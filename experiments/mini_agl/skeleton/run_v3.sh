#!/bin/sh
# v3 pipeline, alarm 1500 s; usage: ./run_v3.sh [OUTDIR] [SEEDS]
cd "$(dirname "$0")" && perl -e 'alarm 1500; exec @ARGV' python3 -B run_v3.py "$@"
