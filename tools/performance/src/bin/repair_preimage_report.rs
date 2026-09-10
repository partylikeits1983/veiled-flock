//! Offline correction of derived flamegraphs after the measurement run completes.

fn main() {
    let args = std::env::args_os().skip(1).collect::<Vec<_>>();
    if args.len() == 2 && args[0] == "--validate-xml" {
        match flock_performance::repair::validate_xml(std::path::Path::new(&args[1])) {
            Ok(summary) => println!("{summary:#}"),
            Err(error) => {
                eprintln!("repair_preimage_report: {error}");
                std::process::exit(1);
            }
        }
        return;
    }
    if args.is_empty() {
        eprintln!(
            "usage: repair_preimage_report <evidence-root> --output <publication-root> [--findings <markdown>] | --validate-xml <xml-file>"
        );
        std::process::exit(1);
    }
    if let Err(error) = flock_performance::workflow::report_command(&args) {
        eprintln!("repair_preimage_report: {error}");
        std::process::exit(1);
    }
}
