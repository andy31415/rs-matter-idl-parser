use std::fs;

use clap::Parser;
use rs_matter_idl_parser::Idl;

// Simple program parsing a IDL file
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// IDL file to open
    name: String,
}

fn main() -> miette::Result<()> {
    let args = Args::parse();
    
    let contents = fs::read_to_string(args.name)
        .expect("Valid input file");
    
    Idl::parse((&*contents).into())?;
    Ok(())
}