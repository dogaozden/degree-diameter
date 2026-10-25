#!/bin/bash
# variant (myanneal): waits for the baseline, then a short self-check (CHECK=1: incremental state == full evaluation),
# then K33m over Z_23, m=69, 120 s CPU, seeds 1..3. One run at a time.
cd /home/user/degree-diameter/research/squads/d12D5-r1/c6
D=/home/user/degree-diameter/research/d12D5
while ! grep -q "done seed 3" logs/base_progress.txt 2>/dev/null; do sleep 5; done
CHECK=1 THREADS=1 INIT_ECHART=$D/graphs/d12D5_n10692_k33m_z22e_echart.txt \
  timeout 900 nice -n 10 ./myanneal $D/base_k33m.txt $D/tables/z23.txt 6 1 2.0 0.8 > logs/check.log 2>&1 \
  || { echo "CHECK FAILED $(date +%T)" >> logs/var_progress.txt; exit 1; }
echo "check ok $(date +%T) $(tail -2 logs/check.log | tr '\n' ' ')" >> logs/var_progress.txt
for s in 1 2 3; do
  INIT_ECHART=$D/graphs/d12D5_n10692_k33m_z22e_echart.txt THREADS=1 \
    timeout 1500 nice -n 10 ./myanneal $D/base_k33m.txt $D/tables/z23.txt 120 $s 2.0 0.8 out/var_s$s > logs/var_s$s.log 2>&1
  echo "done seed $s $(date +%T)" >> logs/var_progress.txt
done
