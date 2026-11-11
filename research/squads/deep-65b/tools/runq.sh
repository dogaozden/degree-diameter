#!/bin/sh
# usage: tools/runq.sh QUEUEFILE NPAR   (QUEUEFILE: lines "order id"; runs split15 ex on each group, NPAR at a time)
# outputs runs/ex_<order>_<id>.txt (SOL/BEST/DONE lines) and .err (progress)
cd "$(dirname "$0")/.."
grep -v '^#' "$1" | xargs -P "$2" -L 1 sh -c 'f=groups/sg_$0_$1.tab; [ -s runs/ex_$0_$1.txt ] && grep -q DONE runs/ex_$0_$1.txt && exit 0; LMAX=40000000 shared/split15 $f ex > runs/ex_$0_$1.txt 2> runs/ex_$0_$1.err'
