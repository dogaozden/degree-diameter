#!/bin/bash
# Scorer for squad round r1-defect4 (bipartite (k,3,-4)-graphs).
# usage: score.sh path/to/gen.py      (gen.py k out.cnf  must write a DIMACS CNF that is SAT iff a
#                                       bipartite (k,3,-4)-graph exists, possibly with sound symmetry breaking)
# Known: k=5 SAT (unique graph), k=6 UNSAT, k=7 UNSAT (Feria-Puron, Miller, Pineda-Villavicencio 2013).
# Prints one JSON line: {"k5": ..., "k6": ..., "k7": ..., "valid": ..., "score": seconds for k6 (+k7)}
gen=$1
K=/tmp/claude-0/-home-user-degree-diameter/4905f117-080d-5578-b5d8-53a7377d03a3/scratchpad/kissat/build/kissat
tmp=$(mktemp -d)
res() { # k timeout
  python3 "$gen" $1 $tmp/k$1.cnf > /dev/null 2>&1 || { echo "GENFAIL 0"; return; }
  s=$(date +%s.%N)
  timeout $2 nice -n 10 $K -q $tmp/k$1.cnf > $tmp/out$1 2>&1; rc=$?
  e=$(date +%s.%N)
  t=$(echo "$e - $s" | bc)
  case $rc in 10) echo "SAT $t";; 20) echo "UNSAT $t";; *) echo "TIMEOUT $t";; esac
}
r5=$(res 5 300); r6=$(res 6 900)
set -- $r5; a5=$1; t5=$2; set -- $r6; a6=$1; t6=$2
a7=SKIP; t7=0
if [ "$a6" = UNSAT ] && [ $(echo "$t6 < 300" | bc) = 1 ]; then r7=$(res 7 900); set -- $r7; a7=$1; t7=$2; fi
valid=false; [ "$a5" = SAT ] && [ "$a6" = UNSAT ] && valid=true
[ "$a7" = SAT ] && valid=false
score=$t6; [ "$a7" = UNSAT ] && score=$(echo "$t6 + $t7" | bc)
[ "$valid" = true ] || score=99999
echo "{\"k5\": \"$a5 $t5\", \"k6\": \"$a6 $t6\", \"k7\": \"$a7 $t7\", \"valid\": $valid, \"score\": $score}"
rm -rf $tmp
