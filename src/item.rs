pub mod colstr;
mod char_util;
mod str_util;
mod string_util;

// XX: make Colstr private, offer trait to import instead!
use colstr::{FileLine, Location, Colstring, Colstr};
use char_util::{char_is_ascii_alphabetic, char_is_ascii_alphanumeric,
                char_is_ascii_digit, char_is_word, };
use str_util::{str_is_white, str_skip_any, str_start_count, str_drop, };
use string_util::string_drop_first;

use anyhow::{Result, anyhow, bail, Context};
// use chrono::Weekday;
use chrono::naive::{NaiveTime, // NaiveDate, NaiveDateTime
};
use chrono::offset::FixedOffset;
// use chrono::offset::TimeZone;
use chrono::DateTime;
use std::iter::{Enumerate, Peekable};
use std::fs::File;
use std::io::{Lines, BufReader, // BufRead, BufWriter, stdout, Write, 
};
// use std::option::NoneError;


// // Handle ? on Option as a default error message:
// impl std::error::Error for NoneError {


// }
// XX grrrrr

#[derive(Debug)]
pub struct Category(Vec<String>);

#[derive(Debug)]
pub struct Tasks {
    categories: String, //XX Vec<Category>,
    description: String,
}

#[derive(Debug)]
pub struct Subitem(Location, Si);
#[derive(Debug)]
enum Si {
    Minus,
    About, // ~
    Questionmark,
    Time(Time),
    Rest(String)
}


// A "token" -- the input consists of a sequence of those
#[derive(Debug)]
pub enum Item {
    SingleLineComment(String),      // #
    MultiLineComment(Vec<String>),  // [  ]
    Empty(usize),                   // a number of empty lines
    Todo(String),                   // *
    Other(Vec<Subitem>), // debugging
    ProcessingInstruction { key: String, value: String},  // %, and other
    TimeTo { to: String, tasks: Tasks },
    TimeFromTo { from: String, to: String, tasks: Tasks },
}

impl Item {
    pub fn debug_no_location(&self) -> String {
        match self {
            Item::Other(v) =>
                format!("Other({:?})",
                        v.iter().map(|subitem| &subitem.1)
                                .collect::<Vec<&Si>>()),
            other => format!("{:?}", other)
        }
    }
}


#[derive(Debug)]
// struct Zone([u8, 8]);
pub struct Zone(String);

fn parse_time_zone<'s>(s: &Colstr<'s>) -> Result<(Zone, Colstr<'s>)> {
    // XX  Europe/Zurich, too?
    let (z, r) = s.expect_n_to_m(1, 10,
                                 char_is_ascii_alphabetic, "ascii alphabetic")?;
    // let mut a : [u8, 8] = [0; 8];
    Ok((Zone(z.to_string()), r))
}


#[derive(Debug)]
pub enum Time {
    NT(NaiveTime),
    NTZ(NaiveTime, Zone), // a time with local zone override
    // NDT(NaiveDateTime),
    DT(DateTime<FixedOffset>), // a datetime with local zone override
    Debug(String),
}

// "21:18:04"
fn parse_time_naive<'s>(s: &Colstr<'s>) -> Result<(NaiveTime, Colstr<'s>)> {
    // todo: location tracking for error reporting, sigh ever.
    let (hours, s) = s.parse_digits(1, 2)?;
    let s = s.skip_char_opt(':').ok_or_else(
        || anyhow!("expecting a ':' after the hour"))?;
    let (minutes, s) = s.parse_digits(2, 2)?;
    if let Some(s) = s.skip_char_opt(':') {
        let (seconds, s) = s.parse_digits(2, 2)?;
        Ok((NaiveTime::from_hms_opt(hours, minutes, seconds)
            .ok_or_else(
                || anyhow!("invalid hh:mm:ss values {}, {}, {}",
                           hours, minutes, seconds))?,
            s))
    } else {
        Ok((NaiveTime::from_hms_opt(hours, minutes, 0)
            .ok_or_else(
                || anyhow!("invalid hh:mm values {}, {}",
                           hours, minutes))?,
            s))
    }
}

// "21:18:04", "Mon_31_Oct_200350_CET_2022", "Mon 31 Oct 21:18:04 GMT
// 2022", expected.
fn parse_time<'s>(s: &Colstr<'s>) -> Result<(Time, Colstr<'s>)> {
    let err =
        || bail!("column {}: can't currently parse this as time: {:?}",
                 s.column(), s.str());
    let c = s.first()?;
    if c.is_ascii_digit() {
        // "21:18:04"
        let (t, r) = parse_time_naive(s)?;
        if let Some(_) = r.starts_with_one_opt(char_is_ascii_alphabetic) {
            // There's an optional time zone after the naive time
            let (z, r) = parse_time_zone(&r).with_context(
                || anyhow!("column {}: garbage after time {:?}: {:?}",
                           r.column(), t, r.str()))?;
            Ok((Time::NTZ(t, z), r))
        } else {
            Ok((Time::NT(t), r))
        }
        // or, would I ever use a NaiveDateTime?
    } else if c.is_ascii_alphabetic() {
        // "Mon 31 Oct 21:18:04 GMT 2022" ; XX perhaps sometimes
        // "Mon_31_Oct_200350_CET_2022"? currently
        // parse_baredatetime_opt has the wrong type.
        if let Some((t, r)) = parse_normaldatetime_opt(&s)? {
            Ok((t, r))
        } else {
            err()
        }
    } else {
        err()
    }
}

impl<'s> Colstr<'s> {
    pub fn subitem(&self, si: Si) -> Subitem {
        Subitem(self.location(), si)
    }
}

fn parse_curlydatetime<'s>(s: &Colstr<'s>) -> Result<(Subitem, Colstr<'s>)> {
    let s = s.skip_ascii_str("mtime ");
    let (tim, s1) = s.expect_n_to_m(25, 30, |c| c != '}', "non-'}'")?;
    if let Some(r) = s1.skip_ascii_str_opt("}") {
        let (t, timr) = parse_time(&tim).with_context(
            || anyhow!("between '{{'..'}}'"))?;
        if timr.is_empty() {
            Ok((tim.subitem(Si::Time(t)), r))
        } else {
            bail!("column {}: garbage after date/time between '{{...}}': {:?}",
                  timr.column(), timr.str())
        }
    } else {
        bail!("column {}: missing '}}' after '{{'", s1.column())
    }
}

// A time without date, e.g. 1:34 or 1:34:56
fn parse_baretime<'s>(s: &Colstr<'s>) -> Result<(Subitem, Colstr<'s>)> {
    // Do not figure out delimiter now, since <!-- --> makes it
    // complicated -- OK this is actually obsolete, those are removed
    // now at this point. Anyway, we are where we are, consistency is
    // good, too.
    let (t, r) = parse_time(&s).with_context(
        || {
            let (t, good) = s.take(16);
            anyhow!("column {}: can't parse baretime from: {:?}{}",
                   s.column(), t.str(), if good { "..." } else { "" })})?;
    Ok((s.subitem(Si::Time(t)), r))
}


// E.g. "Mon_31_Oct_200350_CET_2022"
// If we can match a baredate, report errors translating the date,
// otherwise report None.
fn parse_baredatetime_opt<'s>(s: &Colstr<'s>)
                              -> Result<Option<(Subitem, Colstr<'s>)>> {
    let (w, _, s1) = s.take_while(char_is_word);
    if let Some((wday, day, mon, tim, tz, year)) = (|| {
        let take_part = |s: &Colstr<'s>, minlen, maxlen, pred: fn(char) -> bool| {
            let (w, l, s1) = s.take_while(pred);
            if ! (minlen <= l && l <= maxlen) { return None }
            let (_, l, s2) = s1.take_while(|c| c == '_');
            if !(l == 1 || s2.is_empty()) { return None }
            Some((w, s2))
        };
        let (wday, w) = take_part(&w, 2, 10, char_is_ascii_alphabetic)?;
        let (day, w) = take_part(&w, 1, 2, char_is_ascii_digit)?;
        let (mon, w) = take_part(&w, 3, 10, char_is_ascii_alphabetic)?;
        let (tim, w) = take_part(&w, 4, 6, char_is_ascii_digit)?;
        let l = tim.len(); // OK since we're guaranteed to be ascii
        if !(l == 4 || l == 6) { return None }
        let (tz, w) = take_part(&w, 3, 6, char_is_ascii_alphabetic)?;
        // ^ XX optional?
        let (year, w) = take_part(&w, 4, 4, char_is_ascii_digit)?;
        // Have we used up the whole \w+ area? (Note that this is not
        // checking for the remainder after the word area, which is in
        // s1 outside this scope.)
        if ! w.is_empty() { return None }
        Some((wday,
              day.parse_u32().unwrap(),
              mon,
              tim,
              tz,
              year))
    })() {
        let t = {
            let (hh, tim1) = tim.xtake_ascii_and_rest(2);
            let (mm, ss) = tim1.xtake_ascii_and_rest(2);
            NaiveTime::from_hms_opt(hh.parse_u32()?,
                                    mm.parse_u32()?,
                                    ss.parse_u32()?)
                .ok_or_else(
                    || anyhow!("column {}: invalid hh:mm:ss values {}, {}, {}",
                               hh.column(), hh.str(), mm.str(), ss.str()))?
            
        };
        // ç parse tz, derive is_dstime from it;
        // Ok((Subitem::Time(Time::DT(ç)), s1))
        Ok(Some((w.subitem(Si::Rest(w.to_string())), s1)))
    } else {
        Ok(None)
    }
}

// E.g. "Mon 31 Oct 21:18:04 GMT 2022", or "Sun Oct 30 15:43:04 CET
// 2022". If we can match that, report errors translating the date,
// otherwise report None. Partial COPY-PASTE from
// parse_baredatetime_opt (but ":" handling is pretty different, and
// currently different return type).
fn parse_normaldatetime_opt<'s>(s: &Colstr<'s>)
                                -> Result<Option<(Time, Colstr<'s>)>> {
    if let Some((wday, day, mon, tim, tz, year, r)) = (|| {
        let take_part = |s: &Colstr<'s>, minlen, maxlen, pred: fn(char) -> bool| {
            let (w, l, s1) = s.take_while(pred);
            if ! (minlen <= l && l <= maxlen) { return None }
            let (_, l, s2) = s1.take_while(|c| c.is_whitespace());
            if !(l == 1 || l == 2 || s2.is_empty()) { return None }
            Some((w, s2))
        };
        let (wday, w) = take_part(s, 2, 10, char_is_ascii_alphabetic)?;
        let (day, mon, w) =
            if let Some((day, w)) = take_part(&w, 1, 2, char_is_ascii_digit) {
                let (mon, w) = take_part(&w, 3, 10, char_is_ascii_alphabetic)?;
                (day, mon, w)
            } else {
                let (mon, w) = take_part(&w, 3, 10, char_is_ascii_alphabetic)?;
                let (day, w) = take_part(&w, 1, 2, char_is_ascii_digit)?;
                (day, mon, w)
            };
        let (tim, w) = take_part(&w, 4, 8, |c| c.is_ascii_digit() || c == ':')?;
        let (tz, w) = take_part(&w, 3, 6, char_is_ascii_alphabetic)?;
        // ^ XX optional?
        let (year, w) = take_part(&w, 4, 4, char_is_ascii_digit)?;
        Some((wday,
              day.parse_u32().unwrap(),
              mon,
              tim,
              tz,
              year,
              w))
    })() {
        let (naivetime, r) = parse_time_naive(&tim)?;
        if ! r.is_empty() {
            bail!("BUG: column {}", r.column());
        }
        // ç parse tz, derive is_dstime from it;
        // Ok((Subitem::Time(Time::DT(ç)), s1))
        Ok(Some((Time::NT(naivetime), r)))
    } else {
        Ok(None)
    }
}

fn parse_subitem<'s>(s: &Colstr<'s>)
                     -> Result<Option<(Subitem, Colstr<'s>)>> {
    if s.is_empty() {
        return Ok(None)
    }
    let (c, r) = s.first_and_rest()?;
    if c == '-' {
        return Ok(Some((s.subitem(Si::Minus), r)))
    }
    if c == '~' {
        return Ok(Some((s.subitem(Si::About), r)))
    }
    if c == '?' {
        return Ok(Some((s.subitem(Si::Questionmark), r)))
    }
    if c == '{' {
        return Ok(Some(parse_curlydatetime(&r)?))
    }
    if c.is_ascii_digit() {
        // 1:34 or 1:34:56
        return Ok(Some(parse_baretime(s)?))
    }
    if let Some(item_and_rest) = parse_baredatetime_opt(s)? {
        // Mon_31_Oct_200350_CET_2022
        return Ok(Some(item_and_rest))
    }
    let rest =
        if c.is_whitespace() {
            // Here, category and description are expected
            &r
        } else {
            // Also possibility of category and description (after
            // something with a delimiter other than space, like a
            // curlytime), or it could be a line holding a processing
            // instruction. That has to be parsed once other items have
            // been taken, hence, Rest, too.
            s
        };
    Ok(Some((rest.subitem(Si::Rest(rest.to_string())),
             rest.dropall())))
}

fn expect_identifier<'s>(s: &Colstr<'s>) -> Result<(Colstr<'s>, Colstr<'s>)> {
    let s0 = s.skip_whitespace();
    (|| {
        let c = s0.first()?;
        if ! c.is_ascii_alphabetic() {
            bail!("does not start with an ascii alphabetic character");
        }
        s0.expect_n_to_m(1,
                         100,
                         char_is_ascii_alphanumeric, "ascii_alphanumeric")
    })().with_context(
        || anyhow!("column {}: expecting an identifier", s0.column()))
}

fn parse_processinginstruction(s: &Colstr) -> Result<Item> {
    (|| {
        let (key, s1) = expect_identifier(&s)?;
        let s2 = s1.skip_whitespace();
        if let Some((c, s3)) = s2.first_and_rest_opt() {
            if c == '=' {
                Ok(Item::ProcessingInstruction {
                    key: key.to_string(),
                    value: s3.skip_whitespace().to_string() })
            } else if key.str() == "set" {
                // was there whitespace after set?
                if s2.startbyte() > s1.startbyte() {
                    let (key, val0) = expect_identifier(&s2)?;
                    // drop '=' and whitespace if present
                    let (_, val1) = val0.skip_whitespace()
                        .expect_n_to_m(0, 1, |c| c == '=', "'='")?;
                    let val2 = val1.skip_whitespace();
                    // was there either '=' or whitespace after the key?
                    if ! (val2.startbyte() > val0.startbyte()) {
                        bail!("column {}: expecting whitespace \
                               or '=' after the key {:?}",
                              val0.column(), key.str());
                    }
                    Ok(Item::ProcessingInstruction {
                        key: key.to_string(),
                        value: val2.skip_whitespace().to_string() })
                } else {
                    bail!("column {}: expecting whitespace after 'set'",
                          s1.column())
                }
            } else {
                bail!("does not start with `\\w+\\s*=` nor `set \\w+ `")
            }
        } else {
            bail!("missing text after \\w+\\s*")
        }
    })().with_context(
        || anyhow!("can't parse as a processing instruction: {:?}",
                   s.str()))
}

fn parse_other(commentless_line: &Colstr) -> Result<Item> {
    let mut subitems = Vec::new();
    let mut s = commentless_line.clone();
    while let Some((subitem, rest)) = parse_subitem(&s)? {
        subitems.push(subitem);
        s = rest;
    }
    // Now analyze that token stream:
    match &subitems[..] {
        [Subitem(_,Si::Rest(_))] =>
            parse_processinginstruction(&commentless_line),
        _ =>
            Ok(Item::Other(subitems)) //XX
    }
}


// ------------------------------------------------------------------
// Reading line based items, streaming

fn peeking<F: FnOnce(usize, &str) -> Result<bool>>(
    source: &mut Peekable<Enumerate<Lines<BufReader<File>>>>,
    pred: F
) -> Result<bool> {
    if let Some((linenumref, lineref)) = source.peek() {
        match lineref {
            Ok(line) => pred(*linenumref, &line),
            Err(_) => {
                let _ = source.next().unwrap().1?;
                Ok(false) // never happens
            }
        }
    } else {
        Ok(false)
    }
}


// Copy line into stripped_line, while removing <!-- --> comments but
// maintaining location information
fn copy_line_stripping_comments(fileno: u16,
                                linenum: usize,
                                line: &str,
                                stripped_line: &mut Colstring) -> Result<()> {
    stripped_line.clear_for_fileline(
        FileLine { fileno, lineno: linenum as u16 + 1 });
    let mut position = 0;
    let mut current_comment_end : Option<usize> = None;
    for (i, c) in line.char_indices() {
        {
            // Does a comment start here?
            let part = &line[i..];
            if part.starts_with("<!--") {
                let rem = &part[4..];
                if let Some(iend) = rem.find("-->") {
                    current_comment_end = Some(i + 4 + iend + 3);
                } else {
                    bail!("line {}, column {}: missing '-->' \
                           after '<!--'",
                          linenum+1, position)
                }
            }
        }
        if let Some(comment_end) = current_comment_end {
            if i < comment_end {
                // do not push
            } else {
                current_comment_end = None;
                stripped_line.push(c, position);
            }
        } else {
            stripped_line.push(c, position);
        }
        position += 1;
    }
    stripped_line.set_end_column(position);
    Ok(())
}

// Returns None only on EOF.
pub fn read_item<'t, 't1, 't2>(
    fileno: u16,
    source: &mut Peekable<Enumerate<Lines<BufReader<File>>>>,
    tmp: &'t mut Colstring,
    // workaround for pre-Polonius NLL limitation:
    tmp1: &'t1 mut Colstring,
    tmp2: &'t2 mut Colstring)
    -> Result<Option<Item>> {
    if let Some((linenum, line_result)) = source.next() {
        copy_line_stripping_comments(fileno, linenum, &line_result?,
                                     tmp)?;
        let commentless_line = tmp.colstr();
        if commentless_line.is_white() {
            let mut n = 1;
            // while source.peek().is_some_and(str_is_white)
            //   is nightly only.
            while peeking(source, |linenum, line| {
                copy_line_stripping_comments(fileno, linenum, line, tmp1)?;
                Ok(tmp1.colstr().is_white())
            })? {
                source.next().unwrap().1?;
                n += 1;
            }
            Ok(Some(Item::Empty(n)))
        } else {
            // (commentless_line cannot be empty or is_white would have
            // been true above, thus can't fail in first_and_rest here)
            let (c, r) = commentless_line.first_and_rest()?;
            if c == '#' {
                Ok(Some(Item::SingleLineComment(r.to_string())))
            } else if c == '*' {
                Ok(Some(Item::Todo(r.to_string())))
            } else if c == '%' {
                Ok(Some(parse_processinginstruction(&r)?))
            } else if c == '[' {
                // Allow nesting, but only register '[' and ']' at the
                // beginning of the line, although possibly
                // inside/outside another one (i.e. '[[' and ']]' can
                // be stacked); no other text is allowed on the same
                // line after those characters.
                fn check<'t>(rest: &Colstr<'t>, c: char, linenum: usize)
                             ->Result<()> {
                    if ! str_is_white(rest.str()) {
                        bail!("line {} column {}: garbage after '{}': {:?}",
                              linenum+1, rest.column(), c, rest.str());
                    }
                    Ok(())
                }
                let (n, rest) = commentless_line.skip_any('[');
                check(&rest, '[', linenum)?;
                let mut level = n;
                let mut v = Vec::new();
                while peeking(source, |linenum, line| {
                    copy_line_stripping_comments(fileno, linenum, line, tmp2)?;
                    let commentless_line = tmp2.colstr();
                    let (n, rest) = commentless_line.skip_any('[');
                    if n > 0 {
                        level += n;
                        check(&rest, '[', linenum)?;
                    } else {
                        let (n, rest) = commentless_line.skip_any(']');
                        if n > 0 {
                            if n <= level {
                                level -= n;
                                check(&rest, ']', linenum)?;
                            } else {
                                bail!("line {} column {}: more ']' than '['",
                                      linenum+1, n-level)
                            }
                        }
                    }
                    // Retain nested '[' and ']' lines in the comment region
                    // (we count levels only to know when to stop)
                    Ok(
                        if level > 0 {
                            v.push(commentless_line.to_string());
                            true
                        } else {
                            false
                        })
                })? {
                    source.next().unwrap().1?;
                }
                if level > 0 {
                    bail!("premature EOF in a multi-line comment \
                           started on line {}, missing {} ']'",
                          linenum+1, level)
                }
                Ok(Some(Item::MultiLineComment(v)))
            } else {
                let item = parse_other(&commentless_line).with_context(
                    || anyhow!("can't parse line {}, {:?}",
                               linenum+1, commentless_line.str()))?;
                Ok(Some(item))
            }
        }
    } else {
        Ok(None)
    }
}

