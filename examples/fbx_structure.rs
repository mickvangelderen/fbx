use clap::Parser;
use fbx::Node;
use std::{fs, io, path::PathBuf};

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Path to the file to read.
    file_path: PathBuf,

    /// Maximum tree depth to print.
    #[arg(long)]
    max_depth: Option<usize>,
}

fn main() {
    let args = Args::parse();

    let mut reader =
        io::BufReader::new(fs::File::open(args.file_path).expect("failed to open file"));
    let file = fbx::File::read_from(&mut reader).expect("failed to parse file");

    println!("version: {}", file.version);

    display_nodes(args.max_depth, 1, &file.children);
}

fn display_nodes<'a>(
    max_depth: Option<usize>,
    depth: usize,
    nodes: impl IntoIterator<Item = &'a Node>,
) {
    if let Some(max_depth) = max_depth {
        if depth > max_depth {
            return;
        }
    }

    for node in nodes {
        let prefix = "  ".repeat(depth.checked_sub(1).unwrap());
        println!("{prefix}- {}", node.name);
        display_nodes(max_depth, depth + 1, &node.children);
    }
}
