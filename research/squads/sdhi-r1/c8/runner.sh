#!/bin/bash
cd /home/user/degree-diameter/research/squads/sdhi-r1/c8
DEADLINE=$(date -d "2026-10-31 07:04:00" +%s)
mkdir -p out
tail -n +2 groups.txt | while read N m k r d inv; do
  now=$(date +%s)
  [ "$now" -ge "$DEADLINE" ] && break
  f=out/g${N}_${m}_${k}_${r}.txt
  if [ -s "$f" ] && grep -q '^DONE' "$f"; then continue; fi
  echo "START $N $m $k $r $(date +%T)" >> out/runner.log
  THREADS=1 ENUM=1 ECAP=3000000 NEAR=30 SECS=20 timeout 300 nice -n 10 ./sdhi 5 7 meta $m $k $r cyc 1 > "$f" 2>&1
  echo "END $N $m $k $r rc=$? $(date +%T)" >> out/runner.log
done
echo ALLDONE $(date +%T) >> out/runner.log
