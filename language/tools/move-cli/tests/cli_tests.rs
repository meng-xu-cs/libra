// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use std::{
    path::PathBuf,
    process::{Command, Stdio},
};

pub const CLI_BINARY_PATH: [&str; 6] = ["..", "..", "..", "target", "debug", "move"];
pub const CLI_METATEST_PATH: [&str; 2] = ["tests", "metatests"];

fn get_cli_binary_path() -> String {
    let pb: PathBuf = CLI_BINARY_PATH.iter().collect();
    pb.to_str().unwrap().to_owned()
}

fn get_metatest_path() -> String {
    let pb: PathBuf = CLI_METATEST_PATH.iter().collect();
    pb.to_str().unwrap().to_owned()
}

#[test]
fn run_metatest() {
    let path_cli_binary = get_cli_binary_path();
    let path_metatest = get_metatest_path();

    // with coverage
    assert!(Command::new(&path_cli_binary)
        .arg("sandbox")
        .arg("test")
        .arg("--track-cov")
        .arg(&path_metatest)
        .stdout(Stdio::null())
        .status()
        .is_ok());

    // without coverage
    assert!(Command::new(&path_cli_binary)
        .arg("sandbox")
        .arg("test")
        .arg(&path_metatest)
        .stdout(Stdio::null())
        .status()
        .is_ok());
}
