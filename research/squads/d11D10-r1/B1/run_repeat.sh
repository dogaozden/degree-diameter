#!/bin/bash
# B1 follow-up: repeated-generator copy (generator 4 repeats generator 2), both checkers.
B=/home/user/degree-diameter/research/squads/d11D10-r1/B1
H=/home/user/degree-diameter/research/structured/tools/haarcheck_psl
cd "$B" || exit 2
f=$B/corrupt_repeat_d6D10_psl_23_38.txt
m=$(timeout 300 "$B/pslcheck_b1" "$f" 2>&1); mrc=$?
h=$(timeout 300 "$H" "$f" 2>&1); hrc=$?
echo "[corrupt_repeat] mine rc=$mrc: $(echo "$m" | tail -1)"
echo "[corrupt_repeat] haarcheck_psl rc=$hrc: $(echo "$h" | tail -1)"
echo "repeat done $(date -u +%T)"
