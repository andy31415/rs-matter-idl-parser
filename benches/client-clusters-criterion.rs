use criterion::{black_box, criterion_group, criterion_main, Criterion};
use miette::GraphicalReportHandler;
use rs_matter_idl_parser::Idl;

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("load example client clusters", |b| {
        b.iter(
            || match Idl::parse(black_box(include_str!("../sample-clusters.matter").into())) {
                Err(e) => {
                    let mut buf = String::new();
                    GraphicalReportHandler::new()
                        .render_report(&mut buf, &e)
                        .unwrap();
                    eprintln!("\n{}", buf);
                }
                _ => {}
            },
        )
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);