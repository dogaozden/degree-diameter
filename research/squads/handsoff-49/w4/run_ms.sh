#!/bin/bash
# multi-start ILS on K44 over Z_622 (45 s each, random restarts); keeps every RESULT line in ms.log
cd /home/user/degree-diameter/research/squads/handsoff-49/w4
END=$(date -d "2026-10-31 23:15:00 UTC" +%s)
for s in $(seq 100 999); do
  [ $(date +%s) -ge $END ] && break
  ILS=1 nice -n 10 ./hgi k44.txt cyc:622 45 $s 1 1 ms/k44_s$s 2>/dev/null | grep RESULT | sed "s/^/seed $s /" >> ms.log
done
echo DONE_MS >> ms.log
