#!/bin/bash
# B1 run, one gate slot: agreement with haarcheck_psl on small PSL solutions, corrupted and reduced-D copies,
# then the 142,235,400-vertex file with both checkers.
B=/home/user/degree-diameter/research/squads/d11D10-r1/B1
S=/home/user/degree-diameter/research/frontier/sols
H=/home/user/degree-diameter/research/structured/tools/haarcheck_psl
C=$B/pslcheck_b1
cd "$B" || exit 2
run() {  # label file
  local lab=$1 f=$2 m h mrc hrc
  m=$(timeout 600 "$C" "$f" 2>&1); mrc=$?
  h=$(timeout 600 "$H" "$f" 2>&1); hrc=$?
  echo "[$lab] mine rc=$mrc: $(echo "$m" | tail -1)"
  echo "[$lab] haarcheck_psl rc=$hrc: $(echo "$h" | tail -1)"
}
run d6D10_psl_23_38 "$S/d6D10_psl_23_38_s1.txt"
run d6D10_psl_29_19 "$S/d6D10_psl_29_19_s1.txt"
run d8D8_psl_31_7 "$S/d8D8_psl_31_7_s1.txt"
run corrupt_entry "$B/corrupt_entry_d6D10_psl_23_38.txt"
run corrupt_repeat "$B/corrupt_repeat_d6D10_psl_23_38.txt"
run dminus1_D9 "$B/dminus1_d6D10_psl_23_38.txt"
echo "=== BIG mine $(date -u +%T)"
timeout 900 "$C" "$B/d11D10_psl_149_43_orb3_s1.txt" > "$B/big_mine.log" 2>&1; echo "rc=$?" >> "$B/big_mine.log"
cat "$B/big_mine.log"; echo "=== done mine $(date -u +%T)"
echo "=== BIG haarcheck_psl $(date -u +%T)"
timeout 900 "$H" "$B/d11D10_psl_149_43_orb3_s1.txt" > "$B/big_haarcheck.log" 2>&1; echo "rc=$?" >> "$B/big_haarcheck.log"
tail -3 "$B/big_haarcheck.log"; echo "=== done haarcheck $(date -u +%T)"
