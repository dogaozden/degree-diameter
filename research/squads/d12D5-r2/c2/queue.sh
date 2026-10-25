#!/bin/bash
# card c2 queue: K33m over Z_25 / Z_27 with fixed backtrack-complete charts; one run at a time.
D=/home/user/degree-diameter/research/d12D5
C=/home/user/degree-diameter/research/squads/d12D5-r2/c2
BASE=$D/base_k33m.txt
Z25=$D/tables/z25.txt
Z27=$D/tables/z27.txt
SUM=$C/summary.txt
DEADLINE=$(date -u -d '2026-10-25 15:42:00' +%s)
# returns 0 normally, 1 if past deadline, 2 if a VALID lift at the top m (z27) was found
run() {  # tag table chart seed
  local tag=$1 tab=$2 ch=$3 seed=$4
  if [ "$(date -u +%s)" -ge "$DEADLINE" ]; then echo "$tag skipped (deadline)" >> $SUM; return 1; fi
  local out=$C/$tag
  WRITEBEST=1 DIAGBT=1 INIT_ECHART=$D/diag/$ch.echart timeout 600 nice -n 10 $D/mlift_ejoint2 $BASE $tab 150 $seed 2 1.0 $out > $out.log 2>&1
  local bc=$(grep -o 'best_cost=[0-9]*' $out.log | head -1)
  echo "$(date -u +%H:%M:%S) $tag chart=$ch seed=$seed $bc" >> $SUM
  if [ "$bc" = "best_cost=0" ]; then
    python3 $D/elift.py $out.edges $out.echart $out.lift.edges >> $out.log 2>&1
    $D/apsp $out.lift.edges 12 5 > $out.apsp.txt 2>&1
    echo "$tag apsp: $(tail -1 $out.apsp.txt)" >> $SUM
    rm -f $out.lift.edges
    if grep -q 'RESULT VALID' $out.apsp.txt && [[ $tag == z27* ]]; then return 2; fi
  fi
  return 0
}
run z27_bt3_s2 $Z27 bt3_k33m_0 2; rc=$?; [ $rc -eq 2 ] && { echo "STOP top m valid" >> $SUM; exit 0; }
run z25_bt3_s2 $Z25 bt3_k33m_0 2; rc=$?
run z27_bt3_s3 $Z27 bt3_k33m_0 3; rc=$?; [ $rc -eq 2 ] && { echo "STOP top m valid" >> $SUM; exit 0; }
run z27_bt_s2  $Z27 bt_k33m_0 2; rc=$?; [ $rc -eq 2 ] && { echo "STOP top m valid" >> $SUM; exit 0; }
run z27_bt2_s2 $Z27 bt2_k33m_0 2; rc=$?; [ $rc -eq 2 ] && { echo "STOP top m valid" >> $SUM; exit 0; }
run z27_bt4_s2 $Z27 bt4_k33m_0 2; rc=$?; [ $rc -eq 2 ] && { echo "STOP top m valid" >> $SUM; exit 0; }
run z27_bt3_1_s2 $Z27 bt3_k33m_1 2; rc=$?; [ $rc -eq 2 ] && { echo "STOP top m valid" >> $SUM; exit 0; }
echo "queue done $(date -u +%H:%M:%S)" >> $SUM
