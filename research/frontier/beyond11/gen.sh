#!/bin/bash
# gen.sh SOL: haarcheck_gen on SOL (CTH threads, default 4), log in runs/<stem>.gen.txt; VALID finds go to sols/
cd "$(dirname "$0")"; f=$1; stem=$(basename $f .out); stem=${stem%.txt}
OMP_NUM_THREADS=${CTH:-4} ./check_one.sh haarcheck_gen runs/$stem.gen.txt ./bin/haarcheck_gen $f
grep -h -E "^VALID|^INVALID" runs/$stem.gen.txt | tail -1
if grep -q "^VALID" runs/$stem.gen.txt; then cp $f sols/$stem.txt; echo "saved sols/$stem.txt"; fi
