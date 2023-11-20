use std::{fs, io, path::Path};

use fbx::Version;

fn read_fbx(file_path: &Path) -> fbx::File {
    fbx::File::read_from(io::BufReader::new(
        fs::File::open(file_path).expect("test input not found"),
    ))
    .expect("failed to read fbx")
}

#[test]
fn read_7300() {
    let file = read_fbx("tests/7300_japanese_maple_lowpoly.fbx".as_ref());
    assert_eq!(file.version, Version::V7300);
}

#[test]
fn read_7400() {
    let file = read_fbx("tests/7400_cam_cube_light.fbx".as_ref());
    assert_eq!(file.version, Version::V7400);
}

#[test]
fn read_7500() {
    let file = read_fbx("tests/7500_sun_temple.fbx".as_ref());
    assert_eq!(file.version, Version::V7500);
}
