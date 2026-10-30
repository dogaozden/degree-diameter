#!/bin/bash
# card c2: sequential chunk driver. Starts a new chunk only before DEADLINE (epoch seconds).
cd /home/user/degree-diameter/research/squads/s65r6/c2
DC=/home/user/degree-diameter/research/s65/tools/dcenum
DEADLINE=$(date -u -d "2026-10-30 10:17:00" +%s)
touch results.txt
for c in 00 01 02 03 04 05 06 07 08 09; do
  if [ -f done_$c ]; then continue; fi
  if [ "$(date -u +%s)" -gt "$DEADLINE" ]; then echo "deadline reached before chunk $c" >> progress.log; break; fi
  echo "$(date -u +%H:%M:%S) start chunk $c" >> progress.log
  rm -rf d; mkdir -p d
  ids=$(paste -sd, chunk_$c)
  gap -q -c "PORD:=256; IDS:=[$ids]; OUTDIR:=\"d\";" c3p_export.g > export_$c.log 2>&1
  echo "$(date -u +%H:%M:%S) exported chunk $c: $(ls d/*.dc2 2>/dev/null | wc -l) files" >> progress.log
  for f in d/*.dc2; do
    [ -f "$f" ] || continue
    out=$(SA=1 SECS=2 SEED=1 timeout 60 nice -n 10 $DC "$f" 6 5 "$f.edges" 2>/dev/null | grep '^RESULT')
    best=$(echo "$out" | sed -n 's/.* best \([0-9]*\) .*/\1/p')
    [ -z "$best" ] && best=NA
    echo "$f $best" >> results.txt
    if [ "$best" != "NA" ] && [ "$best" -le 40 ]; then
      mv "$f" keep/; mv "$f.edges" keep/ 2>/dev/null
    else
      rm -f "$f" "$f.edges"
    fi
  done
  echo "$(date -u +%H:%M:%S) finished chunk $c" >> progress.log
  touch done_$c
  rm -rf d
done
echo "$(date -u +%H:%M:%S) driver exit" >> progress.log
