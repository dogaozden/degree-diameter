#!/bin/bash
# c1 driver: card command on each metacyclic prime-order group (N 4881..5100), in list order, sequential, THREADS=1.
# Stops starting new groups after LIMIT seconds of wall clock.
cd /home/user/degree-diameter || exit 1
OUT=/home/user/degree-diameter/research/squads/sdhi-r1/c1/out
LIST=/home/user/degree-diameter/research/selfdual-hi/logs/K5D8/meta_p_4881_5100.txt
LIMIT=${LIMIT:-600}
START=$(date +%s)
export THREADS=1
while read -r N m k r d inv; do
  now=$(date +%s)
  if [ $((now - START)) -ge "$LIMIT" ]; then echo "STOP_LIMIT after $((now-START)) s at N=$N" >> "$OUT/driver.log"; break; fi
  f="$OUT/N${N}_m${m}_k${k}_r${r}.txt"
  [ -s "$f" ] && continue
  t0=$(date +%s)
  ENUM=1 ECAP=3000000 NEAR=30 SECS=20 TYPES=1+2+2 timeout 300 nice -n 10 research/selfdual-hi/src/sdhi 5 8 meta "$m" "$k" "$r" cyc 1 > "$f" 2>&1
  rc=$?
  echo "N=$N m=$m k=$k r=$r rc=$rc secs=$(( $(date +%s) - t0 ))" >> "$OUT/driver.log"
done < "$LIST"
echo "DRIVER_DONE $(( $(date +%s) - START )) s" >> "$OUT/driver.log"
