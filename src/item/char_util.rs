
pub fn char_is_ascii_alphabetic(c: char) -> bool {
    c.is_ascii_alphabetic()
}

pub fn char_is_ascii_alphanumeric(c: char) -> bool {
    c.is_ascii_alphanumeric()
}

pub fn char_is_ascii_digit(c: char) -> bool {
    c.is_ascii_digit()
}

pub fn char_is_word(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

pub fn char_is_whitespace(c: char) -> bool {
    c.is_whitespace() // is_ascii_whitespace ? XX
}

// fn char_is_not_underscore(c: char) -> bool {
//     ! (c == '_')
// }

// fn len_is(s: &Colstr, l: usize) -> bool {
//     s.str.len() == l
// }

// fn len_is_from_to(s: &Colstr, from: usize, to: usize) -> bool {
//     let l = s.str.len();
//     from <= l && l <= to
// }

