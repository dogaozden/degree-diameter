#!/bin/bash
# after the fake chain: pick the top-2 (base, N) by fake cost (0 first), then largest m; one real run at a time
C6=/home/user/degree-diameter/research/squads/d12D5-r2/c6
D=/home/user/degree-diameter/research/d12D5
cd $C6
until grep -q "CHAIN DONE" fake_summary.txt 2>/dev/null; do sleep 2; done
python3 -I - > step2_plan.txt <<'PY'
import glob, re
C6 = '/home/user/degree-diameter/research/squads/d12D5-r2/c6'
rows = []
for f in glob.glob(C6 + '/fake_k3_*_z*.log'):
    s = open(f).read()
    m = re.search(r'm=(\d+) best_cost=(\d+)', s)
    mm = re.search(r'fake_k3_(\d+)_z(\d+)\.log$', f)
    if m and mm:
        rows.append((int(m.group(2)), -int(m.group(1)), mm.group(1), int(mm.group(2))))
rows.sort()
for c, negm, X, N in rows[:2]:
    print(X, N, -negm, c)
PY
cat step2_plan.txt >> step2_summary.txt
while read X N m c; do
  BASE=$D/bases3/k3_$X.txt
  TABLE=$D/tables/z$N.txt
  if [ "$X" = 000 ]; then CH=$D/diag/bt_k3_000_0.echart; elif [ "$X" = 002 ]; then CH=$D/diag/bt_k3_002_0.echart; else CH=$C6/bt_k3_${X}_0.echart; fi
  OUT=$C6/real_k3_${X}_z${N}_s2
  s=$(date +%s)
  WRITEBEST=1 DIAGBT=1 INIT_ECHART=$CH timeout 600 nice -n 10 $D/mlift_ejoint2 $BASE $TABLE 120 2 2 1.0 $OUT > $OUT.log 2>&1
  rc=$?
  bc=$(grep -o 'best_cost=[0-9]*' $OUT.log | head -1)
  echo "real k3_$X N=$N m=$m fakecost=$c rc=$rc wall=$(( $(date +%s)-s ))s $bc" >> step2_summary.txt
  if [ "$bc" = "best_cost=0" ] && [ "$m" -ge 70 ]; then
    LIFT=$C6/lift_k3_${X}_z${N}.edges
    python3 -I $D/elift.py $OUT.edges $OUT.echart $LIFT >> step2_summary.txt 2>&1
    $D/apsp $LIFT 12 5 > $C6/apsp_k3_${X}_z${N}.txt 2>&1
    res=$(grep RESULT $C6/apsp_k3_${X}_z${N}.txt)
    echo "apsp k3_$X N=$N: $res" >> step2_summary.txt
    case "$res" in *VALID*) echo "KEPT lift $LIFT" >> step2_summary.txt ;; *) rm -f $LIFT ;; esac
  fi
done < step2_plan.txt
echo "STEP2 DONE" >> step2_summary.txt
