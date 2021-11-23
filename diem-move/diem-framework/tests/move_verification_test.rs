// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use move_cli::package::prover::ProverTest;

#[test]
fn prove_core() {
    ProverTest::create("core").run()
}

#[test]
#[ignore]
fn prove_core_extended() {
    ProverTest::run_extended_tests_for("core");
}

#[test]
fn prove_experimental() {
    ProverTest::create("experimental").run()
}

#[test]
#[ignore]
fn prove_experimental_extended() {
    ProverTest::run_extended_tests_for("experimental");
}

#[test]
fn prove_dpn() {
    ProverTest::create("DPN").run()
}

#[test]
#[ignore]
fn prove_dpn_extended() {
    ProverTest::run_extended_tests_for("DPN");
}
