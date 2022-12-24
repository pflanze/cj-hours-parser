// #[macro_use]
// extern crate log;

// #[path = "../rawfdreader.rs"]
mod item;
use item::read_item;
use item::colstr::Colstring;

use structopt::StructOpt;
use anyhow::{Result, anyhow, // bail,
             Context};
use std::env;
// use std::option::Option;
use std::path::{Path, PathBuf};
use std::fs::File;
use std::io::{BufWriter, stdout, Write, BufReader, BufRead};
// use chrono::Weekday;
// use chrono::naive::{NaiveDate, NaiveTime, NaiveDateTime};
// use chrono::offset::FixedOffset;
// use chrono::offset::TimeZone;
// use chrono::DateTime;
use item::tz::TzInfoByName;


#[derive(StructOpt, Debug)]
/// Parsing and summarizing hours files
#[structopt(name = "cj-hours-parser")]
struct Opt {

    /// show debugging output --XX?
    #[structopt(short, long, parse(from_occurrences))]
    debug: u8,

    /// dump TZ database (TzInfoByName)
    #[structopt(long)]
    debug_tzinfo: bool,

    /// show stream of parsed structs
    #[structopt(long)]
    debug_items: bool,

    /// paths to one or more files to be parsed
    #[structopt(name = "files", parse(from_os_str), required(true))]
    file_paths: Vec<PathBuf>,
}


fn parse_file(tzinfobyname: &TzInfoByName,
              fileno: u16,
              path: &Path,
              debug_items: bool) -> Result<usize> {
    let file = File::open(path)?;
    let mut ls =
        BufReader::new(file).lines().enumerate().peekable();
    let mut n = 0;
    {
        let mut out = BufWriter::new(stdout());
        let mut tmp = Colstring::new();
        loop {
            if let Some(item) = read_item(tzinfobyname,
                                          fileno,
                                          &mut ls,
                                          &mut tmp)? {
                if debug_items {
                    // With location information stripped:
                    out.write(format!(
                        "item={}\n", item.debug_no_location()).as_bytes())?;
                    // Including location information:
                    out.write(format!("    ={:?}\n", item).as_bytes())?;
                }
                n += 1;
            } else {
                break;
            }
        }
    }
    // println!("num items: {}", n);
    Ok(n)
}

fn main() -> Result<()> {
    let opt = Opt::from_args();

    let debug = opt.debug;
    if debug > 0 {
        env::set_var("RUST_LOG", "trace");
    }
    env_logger::init();

    let tzbn = TzInfoByName::new();
    if opt.debug_tzinfo {
        println!("{:#?}", tzbn);
    }

    let mut fileno = 0;
    for path in opt.file_paths {
        parse_file(&tzbn, fileno, &path, opt.debug_items).with_context(
            || anyhow!("can't process file {:?}", path))?;
        fileno += 1;
    }
    
    println!("Hello, world!");
    Ok(())
}
