use std::fs;

use clap::Parser;
use rs_matter_idl_parser::Idl;

// Simple program parsing a IDL file
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// IDL file to open
    name: String,

    /// How many time to parse this file
    #[arg(short, long, value_name = "CNT")]
    repeat_count: Option<u32>,
}

fn main() -> miette::Result<()> {
    let args = Args::parse();

    let contents = fs::read_to_string(args.name).expect("Valid input file");

    for _ in 0..args.repeat_count.unwrap_or(1) {
        Idl::parse((&*contents).into())?;
    }
    Ok(())
}
