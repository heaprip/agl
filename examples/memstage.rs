//! Peak memory by stage (H61, step 3): `parse`, `eval` (empty plane), `run`
//! (the whole report), `planes` (each plane of a fact in turn, outcomes
//! held, as the report holds them). A counting allocator reports the heap in use and its
//! peak after each stage; `/usr/bin/time -l` gives the resident peak.
//!
//!     cargo run --release --example memstage -- parse FILE.agl

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

struct Counting;

static NOW: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);
static CALLS: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        let n = NOW.fetch_add(l.size(), Relaxed) + l.size();
        PEAK.fetch_max(n, Relaxed);
        CALLS.fetch_add(1, Relaxed);
        unsafe { System.alloc(l) }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        NOW.fetch_sub(l.size(), Relaxed);
        unsafe { System.dealloc(p, l) }
    }
}

#[global_allocator]
static A: Counting = Counting;

fn stage(name: &str) {
    let mb = |x: usize| x as f64 / 1048576.0;
    eprintln!(
        "{name}: heap {:.1} MB, peak {:.1} MB, {} allocations",
        mb(NOW.load(Relaxed)),
        mb(PEAK.load(Relaxed)),
        CALLS.load(Relaxed)
    );
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let prog = agl::parse_file(std::path::Path::new(&args[1])).expect("parse");
    stage("parse");
    match args[0].as_str() {
        "parse" => println!("{} facts", prog.facts.len()),
        "eval" => {
            let out = agl::eval::evaluate(&prog, &agl::model::Plane::new());
            stage("eval");
            println!("{} atoms", out.db.len());
            if args.len() > 2 {
                // Hold the closure for a heap inspection (`heap PID`).
                std::thread::sleep(std::time::Duration::from_secs(20));
                drop(out);
            }
        }
        "planes" => {
            let planes: std::collections::BTreeSet<agl::model::Plane> =
                prog.facts.iter().map(|f| f.plane.clone()).collect();
            let mut held = Vec::new();
            for p in planes {
                let out = agl::eval::evaluate(&prog, &p);
                stage(&format!("{p:?} ({} atoms)", out.db.len()));
                held.push(out);
            }
        }
        _ => {
            let n = agl::render(&agl::run(&prog)).len();
            stage("run");
            println!("{n}");
        }
    }
}
