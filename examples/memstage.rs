//! Peak memory by stage (H61, step 3): `parse`, `eval` (empty plane), `run`
//! (the whole report). Measure outside: `/usr/bin/time -l`.
//!
//!     cargo run --release --example memstage -- parse FILE.agl

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let prog = agl::parse_file(std::path::Path::new(&args[1])).expect("parse");
    match args[0].as_str() {
        "parse" => println!("{} facts", prog.facts.len()),
        "eval" => {
            let out = agl::eval::evaluate(&prog, &agl::model::Plane::new());
            println!("{} atoms", out.db.len());
            if args.len() > 2 {
                // Hold the closure for a heap inspection (`heap PID`).
                std::thread::sleep(std::time::Duration::from_secs(20));
                drop(out);
            }
        }
        _ => println!("{}", agl::render(&agl::run(&prog)).len()),
    }
}
