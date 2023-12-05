use divan::black_box;
use rs_matter_idl_parser::Idl;

fn main() {
    // Run registered benchmarks.
    divan::main();
}

// Define a `fibonacci` function and register it for benchmarking.
#[divan::bench]
fn parse_client_clusters() {
    Idl::parse(black_box(include_str!("../sample-clusters.matter").into())).unwrap();
}
