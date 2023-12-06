use divan::black_box;
use miette::GraphicalReportHandler;
use rs_matter_idl_parser::Idl;

fn main() {
    // Run registered benchmarks.
    divan::main();
}

// Define a `fibonacci` function and register it for benchmarking.
#[divan::bench]
fn parse_client_clusters() {
    if let Err(e) = Idl::parse(black_box(include_str!("../sample-clusters.matter").into())) {
        let mut buf = String::new();
        GraphicalReportHandler::new()
            .render_report(&mut buf, &e)
            .unwrap();
        eprintln!("\n{}", buf);
    }
}
