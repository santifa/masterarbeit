//! This build script enables literate programming in rust.
//! It takes all *.lrs files within the src folder and transforms
//! them into plain *.rs files.
//!
//! Rules:
//! It converts the first non-code paragraph as module commentary
//! and subsequent non-code paragraphs as documentation commentary.
//! Code paragraphs are either in bird linestyle (>) or within code blocks (#CODE).
//! To get normal commentaries within your code, insert them with bird or code block style.
//!
//! The script doesn't handle indentation.
use std::fs::{self, File};
use std::io::{self, BufRead, BufReader, Write};
use std::path::{Path, PathBuf};

fn main() {
    let lrs = walk_dirs(Path::new("src")).expect("Unable to find literate rust source files.");

    for (lrs, rs) in lrs {
        let file = File::open(lrs).expect("Could not open literate rust file.");
        let reader = BufReader::new(file);
        let converted_rust_code =
            handle_lines(reader).expect("Could not convert literate rust file.");
        let mut output = File::create(rs).expect("Could not write rust file.");
        for code_line in converted_rust_code {
            write!(output, "{}\n", code_line).expect("Write to rust file failed.");
        }
    }
}

/// Define alias types for a literate rust source file and a regular rust source file
type Lrs = PathBuf;
type Rs = PathBuf;

/// walkt through some directory tree and collect all literate rust source paths.
/// Also transform them immidiatly into a rust source path.
fn walk_dirs(dir: &Path) -> io::Result<Vec<(Lrs, Rs)>> {
    let mut literate = vec![];

    if dir.is_dir() {
        for entry in fs::read_dir(dir)? {
            let path = entry?.path();
            if path.is_dir() {
                // collect all lrs path in child directories
                literate.append(&mut walk_dirs(&path)?);
            } else {
                // check if we have an lrs path and convert ist to an rs path
                if let Some("lrs") = path.extension().and_then(std::ffi::OsStr::to_str) {
                    let mut rust_path = path.clone();
                    rust_path.set_extension("rs");
                    literate.push((path.clone(), rust_path))
                }
            }
        }
    }
    Ok(literate)
}

/// Define some basic line types for handling different commentary and code blocks
#[derive(Debug, PartialEq)]
enum LineType {
    Commentary,
    BirdLine,
    CodeBlockStart,
    InBlock,
    CodeBlockEnd,
    EmptyLine,
}

impl LineType {
    fn get_type(line: &str, in_block: bool) -> LineType {
        if line.starts_with(">") {
            LineType::BirdLine
        } else if line.is_empty() {
            LineType::EmptyLine
        } else if line.starts_with("#CODE") && !in_block {
            LineType::CodeBlockStart
        } else if line.starts_with("#CODE") && in_block {
            LineType::CodeBlockEnd
        } else if in_block {
            LineType::InBlock
        } else {
            LineType::Commentary
        }
    }
}

fn handle_lines<T: io::Read>(reader: BufReader<T>) -> io::Result<Vec<String>> {
    let mut converted_rust = vec![];
    let mut in_block = false;
    let mut start = true;

    for line in reader.lines() {
        let mut line = line?;
        if start
            && (LineType::Commentary == LineType::get_type(&line, in_block)
                || LineType::EmptyLine == LineType::get_type(&line, in_block))
        {
            // handle module commentary
            line.insert_str(0, "//!");
            converted_rust.push(line.to_string());
        } else {
            // handle other line types
            start = false;
            match LineType::get_type(&line, in_block) {
                LineType::BirdLine => {
                    converted_rust.push(line.get(1..).unwrap_or("").trim().to_string());
                }
                LineType::Commentary => {
                    line.insert_str(0, "/// ");
                    converted_rust.push(line.to_string());
                }
                LineType::CodeBlockStart => {
                    in_block = true;
                }
                LineType::InBlock => {
                    converted_rust.push(line);
                }
                LineType::CodeBlockEnd => {
                    in_block = false;
                }
                LineType::EmptyLine => {
                    converted_rust.push(line);
                }
            }
        }
    }
    Ok(converted_rust)
}
