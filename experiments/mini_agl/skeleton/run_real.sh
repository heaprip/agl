#!/bin/sh
# real-data pipeline, alarm 3000 s; usage: ./run_real.sh [OUTDIR] [SEEDS]
cd "$(dirname "$0")" && perl -e 'alarm 3000; exec @ARGV' python3 -B run_real.py "$@"
