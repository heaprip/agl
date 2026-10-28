#!/bin/sh
# whole pipeline, alarm 600 s; usage: ./run.sh [OUTDIR] [SEEDS]
cd "$(dirname "$0")" && perl -e 'alarm 600; exec @ARGV' python3 -B run.py "$@"
