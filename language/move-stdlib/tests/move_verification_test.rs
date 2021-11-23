// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use move_cli::package::prover::ProverTest;

#[test]
fn prove_stdlib() {
    ProverTest::create(".").run()
}

#[test]
#[ignore]
fn prove_stdlib_extended() {
    ProverTest::run_extended_tests_for(".");
}

#[test]
fn prove_nursery() {
    ProverTest::create("nursery").run()
}

#[test]
#[ignore]
fn prove_nursery_extended() {
    ProverTest::run_extended_tests_for("nursery");
}
