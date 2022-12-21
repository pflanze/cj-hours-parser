use anyhow::{Result, bail};
use thiserror::Error;
use kstring::KString;

use super::str_util::{str_ref, str_take, str_start_count, str_is_white};

// https://stackoverflow.com/questions/59869067/does-the-rust-standard-library-have-a-min-max-trait
// but:
// <jbg> bpalmer: pflanze: as is usually the case for number-related traits, the num-traits crate already contains something suitable
// <jbg> num_traits::bounds::* I think

trait PseudoOption {
    fn null() -> Self;
}
impl PseudoOption for u16 {
    fn null() -> u16 {
        u16::MAX
    }
}
impl PseudoOption for u32 {
    fn null() -> u32 {
        u32::MAX
    }
}

// Location without the column:
#[derive(Clone, Copy, Debug)]
pub struct FileLine {
    pub fileno: u16, // 0-based
    pub lineno: u16  // 1-based
}

fn no_fileline() -> FileLine {
    FileLine { fileno: PseudoOption::null(), lineno: PseudoOption::null() }
}

impl FileLine {
    pub fn add_column(self, column: u32) -> Location {
        Location { fileno: self.fileno, lineno: self.lineno, column }
    }
}

#[derive(Clone, Copy)]
pub struct Location {
    fileno: u16, // 0-based
    lineno: u16, // 1-based
    column: u32
}

impl std::fmt::Debug for Location {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        fmt.debug_tuple("L")
            .field(&self.fileno)
            .field(&self.lineno)
            .field(&self.column)
            .finish()
    }
}


#[derive(Error, Debug)]
enum ParseDigitsError {
    #[error("not enough digits")]
    NotEnoughDigits,
    #[error("too many digits")]
    TooManyDigits,
    #[error("number overflow")]
    NumberOverflow
}

// Positions is to map byte indices into character positions (which
// may be non-consecutive, which may be useful e.g. when some input
// string has been stripped of some parts, but still wanting to map
// positions back to the original input positions).
#[derive(Debug)]
pub struct Colstring {
    str: String,
    positions: Vec<u32>,
    fileline: FileLine,
    // The position to report when Colstr.startbyte points to the end
    // of positions (i.e. the position of the thing that comes after);
    // MAX means, not set:
    end_column: u32,
}

// A slice of Colstring.
#[derive(Debug)]
pub struct Colstr<'a> {
    backing: &'a Colstring,
    startbyte: u32,
    lenbytes: u32
}


impl<'a> Colstring {
    pub fn new() -> Colstring {
        Colstring { str: String::new(),
                    positions: Vec::new(),
                    fileline: no_fileline(),
                    end_column: PseudoOption::null() }
    }

    pub fn clear_for_fileline(&mut self, fileline: FileLine) {
        self.str.clear();
        self.positions.clear();
        self.fileline = fileline;
        self.end_column = PseudoOption::null();
    }

    pub fn from_string(str: String, position0: u32)
                       -> Colstring {
        let mut s = Colstring::new();
        let mut ci = position0;
        for c in str.chars() {
            s.push(c, ci);
            ci += 1;
        }
        s.set_end_column(ci);
        s
    }

    pub fn push(&mut self, c: char, position: u32) {
        self.str.push(c);
        self.positions.push(position);
        let c_len = c.len_utf8();
        for _ in 1..c_len {
            self.positions.push(PseudoOption::null());
        }
    }

    // To be called after the last push after clear().
    pub fn set_end_column(&mut self, position: u32) {
        self.end_column = position;
    }

    pub fn byteindex_to_column(&self, byteindex: u32) -> u32 {
        let start = byteindex as usize;
        if start == self.positions.len() {
            // After dropall() or other situations that drop
            // everything to the end.
            self.end_column
        } else {
            let pos = self.positions[start];
            assert!(pos != PseudoOption::null());
            pos
        }
    }

    pub fn colstr(&'a self) -> Colstr<'a> {
        if self.end_column == PseudoOption::null() {
            panic!("Colstring: the end_column has not been set (call set_end_column after the last push call)");
        }
        if self.positions.len() != self.str.len() {
            panic!("BUG: uneven lengths of vectors");
        }
        Colstr {
            backing: self,
            startbyte: 0,
            lenbytes: self.positions.len() as u32 // panic if too large, OK?
        }
    }
}

impl<'a> Colstr<'a> {
    fn with_startbyte_lenbytes(&self, startbyte: u32, lenbytes: u32
    ) -> Colstr<'a> {
        if true {
            let start = startbyte as usize;
            let end = startbyte as usize + lenbytes as usize;
            assert!(end <= self.backing.str.len());
            assert!(start == self.backing.str.len() ||
                    self.backing.positions[start] != PseudoOption::null());
            assert!(end == self.backing.str.len() ||
                    self.backing.positions[end] != PseudoOption::null());
        }
        Colstr { backing: self.backing,
                 startbyte: startbyte,
                 lenbytes: lenbytes }
    }

    // Naming skip vs. drop: skip means go past the match at the start
    // if present, otherwise return the original. drop requires a
    // match, otherwise reports the failure or panics or returns None.
    // XX check if consistent.

    // CAREFUL: only valid when s is guaranteed to start with n
    // characters, and they are all ascii (or at least character boundaries
    // are matched)
    pub fn xdrop_ascii(&self, n: u32) -> Colstr<'a> {
        self.with_startbyte_lenbytes(
            self.startbyte + n,
            self.lenbytes - n)
    }

    // CAREFUL: only valid when s is guaranteed to start with n
    // characters, and they are all ascii (or at least character boundaries
    // are matched)
    pub fn xtake_ascii(&self, n: u32) -> Colstr<'a> {
        self.with_startbyte_lenbytes(
            self.startbyte,
            n)
    }

    pub fn startbyte(&self) -> u32 { self.startbyte }
    pub fn lenbytes(&self) -> u32 { self.lenbytes }
    pub fn clone(&self) -> Colstr<'a> {
        Colstr { backing: self.backing,
                 startbyte: self.startbyte,
                 lenbytes: self.lenbytes }
    }

    pub fn column(&self) -> u32 {
        self.backing.byteindex_to_column(self.startbyte)
    }
    pub fn end_column(&self) -> u32 {
        // self.backing.end_column *no*, of course not!
        self.backing.byteindex_to_column(self.startbyte + self.lenbytes)
    }

    pub fn location(&self) -> Location {
        self.backing.fileline.add_column(self.column())
    }
    pub fn end_location(&self) -> Location {
        self.backing.fileline.add_column(self.end_column())
    }

    pub fn str(&self) -> &'a str {
        &self.backing.str[self.startbyte as usize ..
                          self.startbyte as usize + self.lenbytes as usize]
    }

    pub fn to_string(&self) -> String {
        String::from(self.str())
    }

    pub fn to_kstring(&self) -> KString {
        KString::from_ref(self.str())
    }

    pub fn is_empty(&self) -> bool {
        self.lenbytes == 0
    }

    // char_count() ? -- no, this is actually *not* the char_count of
    // the Colstr; it's (hopefully) the char_count in the original
    // input! If the Colstring was created via Colstring::from_string,
    // then this *is* the char_count as per the slice of the given
    // string.
    pub fn length(&self) -> u32 {
        self.end_column() - self.column()
    }

    pub fn len(&self) -> u32 {
        self.lenbytes
    }

    pub fn dropall(&self) -> Colstr<'a> {
        self.with_startbyte_lenbytes(self.startbyte + self.lenbytes, 0)
    }

    pub fn first(&self) -> Result<char> {
        if self.is_empty() {
            bail!("column {}: premature end of region", self.column())
        } else {
            Ok(str_ref(&self.backing.str, self.startbyte as usize))
        }
    }

    // Only valid if self contains at least 1 character
    // pub fn xrest(&self) -> {
    // }

    pub fn first_opt(&self) -> Option<char> {
        if self.is_empty() {
            None
        } else {
            Some(str_ref(&self.backing.str, self.startbyte as usize))
        }
    }

    pub fn first_and_rest_opt(&self) -> Option<(char, Colstr<'a>)> {
        if self.is_empty() {
            None
        } else {
            let c = str_ref(&self.backing.str, self.startbyte as usize);
            let c_len = c.len_utf8() as u32;
            Some((c,
                  self.xdrop_ascii(c_len)))
        }
    }

    pub fn first_and_rest(&self) -> Result<(char, Colstr<'a>)> {
        if let Some(cr) = self.first_and_rest_opt() {
            Ok(cr)
        } else {
            bail!("column {}: premature end of region", self.column())
        }
    }

    pub fn skip_one_opt<F: Fn(char)->bool>(&self, pred: F)
                                           -> Option<Colstr<'a>> {
        if let Some(c) = self.first_opt() {
            if pred(c) {
                let c_len = c.len_utf8() as u32;
                Some(self.xdrop_ascii(c_len))
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn starts_with_one_or_end_opt<F: Fn(char)->bool>(
        &self, pred: F)
        -> Option<Colstr<'a>> {
        if let Some(c) = self.first_opt() {
            if pred(c) {
                Some(self.xdrop_ascii(c.len_utf8() as u32))
            } else {
                None
            }
        } else {
            Some(self.clone())
        }
    }        

    pub fn starts_with_one_opt<F: Fn(char)->bool>(
        &self, pred: F)
        -> Option<Colstr<'a>> {
        if let Some(c) = self.first_opt() {
            if pred(c) {
                Some(self.xdrop_ascii(c.len_utf8() as u32))
            } else {
                None
            }
        } else {
            None
        }
    }        

    // ah, str has starts_with, already!
    pub fn starts_with(&self, start: &str) -> bool {
        let s = self.str();
        s.len() >= start.len()
            && &s.as_bytes()[0..start.len()] == start.as_bytes()
    }

    // Only valid if start is all ascii
    pub fn skip_ascii_str_opt(&self, start: &str) -> Option<Colstr<'a>> {
        let s = self.str();
        if (s.len() >= start.len()) && (
            &s.as_bytes()[0..start.len()] == start.as_bytes()) {
            let slen = start.len() as u32;
            Some(self.xdrop_ascii(slen))
        } else {
            None
        }
    }

    // Only valid if start is all ascii
    pub fn skip_ascii_str(&self, start: &str) -> Colstr<'a> {
        let s = self.str();
        if (s.len() >= start.len()) && (
            &s.as_bytes()[0..start.len()] == start.as_bytes()) {
            let slen = start.len() as u32;
            self.xdrop_ascii(slen)
        } else {
            self.clone()
        }
    }

    // Returns the substring *before* pat (excluding it), and returns the
    // remainder *after* pat (again excluding it).
    pub fn take_find_opt(&self, pat: &str)
                         -> Option<(Colstr<'a>, Colstr<'a>)> {
        if let Some(i) = self.str().find(pat) {
            let endoffset = (i + pat.len()) as u32;
            Some((self.xtake_ascii(i as u32),
                  self.xdrop_ascii(endoffset)))
        } else {
            None
        }
    }
    
    // CAREFUL: only valid when s is guaranteed to start with n
    // characters, and they are all ascii.
    pub fn xtake_ascii_and_rest(&self, n: u32) -> (Colstr<'a>, Colstr<'a>) {
        (self.xtake_ascii(n),
         self.xdrop_ascii(n))
    }

    pub fn take_while<F: Fn(char)->bool
                      >(&self, pred: F) -> (Colstr<'a>, u32, Colstr<'a>) {
        let mut ci = 0;
        for (i, c) in self.str().char_indices() {
            if !pred(c) {
                return (self.xtake_ascii(i as u32),
                        ci,
                        self.xdrop_ascii(i as u32))
            }
            ci += 1;
        }
        (self.clone(), ci, self.dropall())
    }
    
    // Takes n characters if it can, fewer if reaching EOS before that
    // point. In the first case returns true, in the latter false.
    pub fn take(&self, n: u32) -> (Colstr<'a>, bool) {
        let (s, good) = str_take(self.str(), n as usize);
        (self.xtake_ascii(s.len() as u32),
         good)
    }

    // This is eager, i.e. takes more than nmax chars matching pred if
    // present, and then reports an error if it does.
    pub fn expect_n_to_m<F: Fn(char)->bool>(&self,
                                            nmin: u32,
                                            nmax: u32,
                                            pred: F,
                                            predname: &str)
                                            -> Result<(Colstr<'a>,
                                                       Colstr<'a>)> {
        let (got, gotn, r) = self.take_while(pred);
        let err = ||
            bail!("column {}: expect {}..{} {} chars, got {}: {:?}",
                  self.column(), nmin, nmax, predname, gotn, self.str());
        if gotn >= nmin {
            if gotn <= nmax {
                Ok((got, r))
            } else {
                err()
            }
        } else {
            err()
        }
    }

    // `drop_while` would also return the number of characters dropped?
    pub fn skip_while<F: Fn(char)->bool>(&self, pred: F) -> Colstr<'a> {
        for (i, c) in self.str().char_indices() {
            if !pred(c) {
                return self.xdrop_ascii(i as u32)
            }
        }
        self.dropall()
    }

    // Careful: also drops non-ascii whitespace
    pub fn skip_whitespace(&self) -> Colstr<'a> {
        self.skip_while(|c| c.is_whitespace()) // is_ascii_whitespace
    }

    // Careful: accepts non-ascii whitespace as white, too
    pub fn is_white(&self) -> bool {
        str_is_white(self.str())
    }

    // Skip 1 occurrence of c, if possible; return None if no match or
    // on EOS.
    pub fn skip_char_opt(&self, c: char) -> Option<Colstr<'a>> {
        if let Some(c1) = self.first_opt() {
            if c1 == c {
                let c_len = c.len_utf8() as u32;
                Some(self.xdrop_ascii(c_len))
            } else {
                None
            }
        } else {
            None
        }
    }

    fn _parse_digits(&self, mindigits: u32, maxdigits: u32)
                     -> Result<(u32, Colstr<'a>), ParseDigitsError> {
        let mut ndigits = 0;
        let mut tot : u32 = 0;
        let end = |ndigits, tot|
            if ndigits >= mindigits {
                Ok((tot, self.xdrop_ascii(ndigits)))
            } else {
                Err(ParseDigitsError::NotEnoughDigits)
            };
        for c in self.str().chars() {
            if c.is_ascii_digit() {
                if ndigits < maxdigits {
                    tot = tot.checked_mul(10).ok_or_else(
                        || ParseDigitsError::NumberOverflow)?
                        .checked_add(c.to_digit(10).unwrap()).ok_or_else(
                            || ParseDigitsError::NumberOverflow)?;
                    ndigits += 1;
                } else {
                    return Err(ParseDigitsError::TooManyDigits)
                }
            } else {
                return end(ndigits, tot)
            }
        }
        end(ndigits, tot)
    }

    pub fn parse_digits(&self, mindigits: u32, maxdigits: u32)
                        -> Result<(u32, Colstr<'a>)> {
        let err = |msg| {
            let range =
                if mindigits == maxdigits {
                    format!("exactly {}", mindigits)
                } else {
                    format!("{}-{}", mindigits, maxdigits)
                };
            bail!("column {}: {} digits, need {}",
                          self.column(), msg, range)
        };
        self._parse_digits(mindigits, maxdigits).or_else(
            |e| match e {
                ParseDigitsError::NotEnoughDigits => err("not enough"),
                ParseDigitsError::TooManyDigits => err("too many"),
                ParseDigitsError::NumberOverflow =>
                    bail!("column {}: u32 number overflow",
                          self.column()),
            })
    }

    pub fn parse_u32(&self) -> Result<u32> {
        let (n, s1) = self.parse_digits(1, 10)?;
        if ! s1.is_empty() {
            bail!("column {}: garbage after number: {:?}",
                  s1.column(), s1.str())
        }
        Ok(n)
    }

    pub fn skip_any(&self, c: char) -> (u32, Colstr<'a>) {
        let (n, i) = str_start_count(self.str(), c);
        (n as u32, self.xdrop_ascii(i as u32))
    }
}


impl<'a> std::cmp::PartialEq for Colstr<'a> {
    fn eq(&self, b: &Colstr<'a>) -> bool {
        // could optimize by looking at backing pointer and if equal
        // then also check end_column
        self.str() == b.str() && self.column() == b.column()
    }
}



#[test]
fn t_skip_ascii_str() {
    let colstring = |pos, s| Colstring::from_string(String::from(s), pos);
    let s_ = colstring(0, "hi there");
    let s = s_.colstr();
    assert_eq!(s.skip_ascii_str("hi"),
               colstring(2, " there").colstr());
    assert_eq!(s.skip_ascii_str("Hi"),
               s);
    assert_eq!(s.skip_ascii_str(""),
               s);
    assert_eq!(s.skip_ascii_str("hi there"),
               colstring(8, "").colstr());
    let hi_ = colstring(0, "hi");
    let hi = hi_.colstr();
    assert_eq!(hi.skip_ascii_str("hi there"),
               hi);
}

