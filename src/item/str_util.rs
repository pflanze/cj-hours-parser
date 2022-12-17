
pub fn str_start_count(s: &str, c: char) -> (usize, usize) {
    let mut n = 0;
    for (i, c2) in s.char_indices() {
        if c2 != c {
            return (n, i);
        }
        n += 1;
    }
    (n, s.len())
}

// fn str_starts_with_char(s: &str, c: char) -> bool {
//     if let Some(cc) = s.chars().next() {
//         cc == c
//     } else {
//         false
//     }
// }

pub fn str_skip_any(s: &str, c: char) -> (usize, &str) {
    let (n, i) = str_start_count(s, c);
    (n, &s[i..])
}

pub fn str_drop(s: &str, n: usize) -> &str {
    if n == 0 {
        s
    } else {
        let mut chars = s.chars(); chars.nth(n-1); chars.as_str()
    }
}

#[test]
fn t_str_drop() {
    assert_eq!(str_drop(" Hey there", 0), " Hey there");
    assert_eq!(str_drop(" Hey there", 1), "Hey there");
    assert_eq!(str_drop(" Hey there", 4), " there");
    assert_eq!(str_drop("Hä lü", 2), " lü");
    assert_eq!(str_drop("Hä lü", 5), "");
}


pub fn str_is_white(s: &str) -> bool {
    s.as_bytes().iter().all(u8::is_ascii_whitespace)
}

// Retrieve character at byte position i (which must exist!). This
// looks rather involved, but the iterator appears to be fully
// optimized away (in release mode using LLVM, anyway).
pub fn str_ref(s: &str, i: usize) -> char {
    s[i..].chars().next().unwrap()
}

// Takes n characters if it can, fewer if reaching EOS before that
// point. In the first case returns true, in the latter false.
pub fn str_take(s: &str, n: usize) -> (&str, bool) {
    let mut ci = 0;
    for (i, _) in s.char_indices() {
        if ci == n {
            return (&s[0..i], true)
        }
        ci += 1;
    }
    (s, ci == n)
}

