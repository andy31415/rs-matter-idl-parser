#!/usr/bin/env bash

# need nightly for -Zprofile
rustup default nightly

export CARGO_INCREMENTAL=0
export RUSTFLAGS="-Zprofile -Ccodegen-units=1 -Copt-level=0 -Clink-dead-code -Coverflow-checks=off -Zpanic_abort_tests -Cpanic=abort"
export RUSTDOCFLAGS="-Cpanic=abort"

cargo build --verbose $CARGO_OPTIONS
cargo test --verbose $CARGO_OPTIONS

# Validate only. Since these are not tests, commented out for now
# cargo run                \
#    --example file_parser \
#    -- /usr/local/google/home/andreilitvin/devel/connectedhomeip/examples/all-clusters-app/all-clusters-common/all-clusters-app.matter


# Actual coverage
mkdir -p target/coverage
grcov . -s . --binary-path ./target/debug/ -t html --branch --ignore-not-existing -o ./target/coverage/

# codecov.io version
#      zip -0 ccov.zip `find . \( -name "YOUR_PROJECT_NAME*.gc*" \) -print`;
#      ./grcov ccov.zip -s . -t lcov --llvm --branch --ignore-not-existing --ignore "/*" -o lcov.info;
#      bash <(curl -s https://codecov.io/bash) -f lcov.info;

