#!/bin/bash
# sequential long ILS runs on K44 over Z_622 with fresh seeds, until 23:28 UTC; wait for the walk run first
cd /home/user/degree-diameter/research/squads/handsoff-49/w4
while ! grep -q RESULT walk_k44_s51.log 2>/dev/null; do sleep 5; done
END=$(date -d "2026-10-31 23:28:00 UTC" +%s)
for s in 61 62 63 64 65 66 67 68; do
  [ $(date +%s) -ge $END ] && break
  ILS=1 nice -n 10 ./hgi k44.txt cyc:622 420 $s 1 1 seq_k44_s$s 2>/dev/null | grep RESULT | sed "s/^/seed $s /" >> seq.log
done
echo DONE_SEQ >> seq.log
