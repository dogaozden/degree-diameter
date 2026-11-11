#!/bin/bash
# usage: check.sh SOLFILE [threads]  -> research/frontier/runs/cloudcheck/<stem>.gen.txt (haarcheck_gen, independent of haar_big0)
S=$1; T=${2:-4}; stem=$(basename $S .txt); out=research/frontier/runs/cloudcheck/$stem.gen.txt
cd /home/user/degree-diameter
{ echo "checker: haarcheck_gen (research/frontier/haarcheck_gen.c, cc -O3 -march=native -fopenmp)"
  echo "command: OMP_NUM_THREADS=$T haarcheck_gen $S"
  echo "start: $(date -u +%FT%TZ)"
  sha256sum /home/user/bin/haarcheck_gen research/frontier/haarcheck_gen.c $S
  t0=$(date +%s); OMP_NUM_THREADS=$T /home/user/bin/haarcheck_gen $S; rc=$?
  echo "exit: $rc"; echo "end: $(date -u +%FT%TZ) ($(( $(date +%s) - t0 )) s)"; } > $out 2>&1
