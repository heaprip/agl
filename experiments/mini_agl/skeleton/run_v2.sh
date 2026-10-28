#!/bin/sh
# v2 pipeline, alarm 900 s; usage: ./run_v2.sh [OUTDIR] [SEEDS]
cd "$(dirname "$0")" && perl -e 'alarm 900; exec @ARGV' python3 -B run_v2.py "$@"
