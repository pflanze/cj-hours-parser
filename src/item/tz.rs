/// Try to map time zone information abbreviations like "DST" to time
/// offsets. Based on chrono_tz, which doesn't offer that
/// functionality directly--in fact, the mapping can't always be done
/// as there are ambiguities. Currently, just reports an error (which
/// does contain a slow clone of the subtree of the information) for
/// names which are ambiguous at lookup time.

/// Also, currently does not return whether a name signifies daylight
/// savings time or not. There are further ambiguities found there,
/// thus for lookups that request that information, more errors will
/// have to be reported.

// Thanks to Arnavion for the suggestion of the approach!

use thiserror::Error;
// use chrono::offset::TimeZone;
use kstring::KString;
use chrono::naive::{NaiveDate};

use chrono_tz::{Tz, OffsetName, TZ_VARIANTS};
use chrono::{TimeZone, Duration};  // for offset_from_utc_date
use std::collections::HashMap;
use chrono_tz::OffsetComponents;
// use chrono_tz::timezone_impl::TzOffset; // is private

// ------------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TzInfo {
    /// The Tz (like America__New_York) the following is used in
    pub tz: Tz,
    /// The name of this timezone, for example the difference between
    /// `EDT`/`EST`
    pub name: KString,
    /// The base offset from UTC; this usually doesn't change unless
    /// the government changes something
    pub utc_offset: Duration,
    /// The additional offset from UTC for this timespan; typically
    /// for daylight saving time
    pub dst_offset: Duration,
}

impl TzInfo {
    fn from_tzoffset_tz<T: OffsetComponents + OffsetName>(offset: &T, tz: Tz)
                                                          -> TzInfo {
        TzInfo {
            tz,
            name: KString::from_ref(offset.abbreviation()),
            utc_offset: offset.base_utc_offset(),
            dst_offset: offset.dst_offset(),
        }
    }
    fn total_offset(&self) -> Duration {
        self.utc_offset + self.dst_offset
    }
}


/// All information about a particular short name (abbreviation)
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct NameInfo {
    pub total_offset: Duration, // utc_offset + dst_offset
    /// All TzInfo using the same name and same total_offset
    pub tzinfos: Vec<TzInfo>,
}

// ------------------------------------------------------------------

type HashMap_Name_Duration =
    HashMap<KString, HashMap<Duration, NameInfo>>;

#[derive(Debug)]
pub struct TzInfoByName {
    infos: HashMap_Name_Duration
}

#[derive(Error, Debug)]
pub enum TzInfoError {
    #[error("ambiguous short time zone name {0:?} can have multiple \
             offsets: {1:?}")]
    AmbiguousName(KString, HashMap<Duration, NameInfo>),
}


// Since chrono_tz::timezone_impl::TzOffset is private, we have to:
// (XX There's no way for something like `let insert = |o: <T> :: T:
// OffsetComponents + OffsetName| {`, right?)
fn _TzInfoByName_m_insert(m: &mut HashMap_Name_Duration, ti: &TzInfo) {
    let name = ti.name.clone(); // first key
    let off = ti.total_offset(); // second key
    let fresh_ni = || NameInfo { total_offset: off,
                                 tzinfos: vec![ti.clone()] };
    if let Some(ref mut m1) = m.get_mut(&name) {
        if let Some(ref mut ni) = m1.get_mut(&off) {
            assert!(ni.total_offset == off);
            ni.tzinfos.push(ti.clone());
        } else {
            m1.insert(off, fresh_ni());
        }
    } else {
        let mut m1 = HashMap::new();
        m1.insert(off, fresh_ni());
        m.insert(name, m1);
    }
}

impl TzInfoByName {

    pub fn new() -> TzInfoByName {
        let mut m : HashMap_Name_Duration = HashMap::new();
        for tz in &TZ_VARIANTS {
            let ti1 = TzInfo::from_tzoffset_tz(
                &tz.offset_from_utc_date(&NaiveDate::from_ymd(2022, 01, 01)),
                *tz);
            let ti2 = TzInfo::from_tzoffset_tz(
                &tz.offset_from_utc_date(&NaiveDate::from_ymd(2022, 07, 01)),
                *tz);
            _TzInfoByName_m_insert(&mut m, &ti1);
            if ti1 != ti2 {
                _TzInfoByName_m_insert(&mut m, &ti2);
            }
        }
        TzInfoByName { infos: m }
    }

    pub fn lookup(&self, name: &KString) -> Result<Option<&NameInfo>,
                                                   TzInfoError> {
        if let Some(m1) = self.infos.get(name) {
            if m1.len() == 1 {
                Ok(Some(m1.values().next().unwrap()))
            } else {
                Err(TzInfoError::AmbiguousName(name.clone(),
                                               m1.clone()))
            }
        } else {
            Ok(None)
        }
    }
}

