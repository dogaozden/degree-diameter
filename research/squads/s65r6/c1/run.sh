#!/bin/bash
# card c1 driver: export chunks of 40 ids, sweep dcenum (SA), keep best <= 40, stop new chunks at 28 min
cd /home/user/degree-diameter/research/squads/s65r6/c1
DC=/home/user/degree-diameter/research/s65/tools/dcenum
START=$(date +%s); DEADLINE=$((START + 28*60))
: > results.txt
for ch in chunk_*; do
  now=$(date +%s)
  if [ $now -ge $DEADLINE ]; then echo "STOP at $(date +%H:%M:%S): deadline reached before $ch" >> progress.log; break; fi
  ids=$(paste -sd, $ch)
  first=$(head -1 $ch); last=$(tail -1 $ch)
  rm -rf d; mkdir -p d
  t0=$(date +%s)
  gap -q -c "PORD:=256; IDS:=[$ids]; OUTDIR:=\"d\";" c3p_export.g > logs/gap_$ch.log 2>&1
  t1=$(date +%s)
  nfiles=$(ls d/*.dc2 2>/dev/null | wc -l)
  echo "export $ch ($first..$last) files $nfiles gap ${t1}-${t0}s start $(date +%H:%M:%S)" >> progress.log
  for f in d/*.dc2; do
    [ -e "$f" ] || continue
    out="${f%.dc2}.edges"
    res=$(SA=1 SECS=2 SEED=1 timeout 60 nice -n 10 $DC "$f" 6 5 "$out" 2>/dev/null)
    best=$(echo "$res" | sed -n 's/.*best \([0-9]*\) vertices.*/\1/p')
    echo "$(basename $f) ${best:-NA}" >> results.txt
    if [ -n "$best" ] && [ "$best" -eq 0 ]; then echo "RECORD CANDIDATE (cost 0) $(basename $f) $(date +%H:%M:%S)" >> progress.log; fi
    if [ -n "$best" ] && [ "$best" -le 40 ]; then mv "$f" keep/; [ -e "$out" ] && mv "$out" keep/; else rm -f "$f" "$out"; fi
  done
  rm -rf d
  echo "chunk $ch done $(date +%H:%M:%S) kept $(ls keep/*.dc2 2>/dev/null | wc -l) results $(wc -l < results.txt)" >> progress.log
done
echo "DRIVER_DONE $(date +%H:%M:%S)" >> progress.log
