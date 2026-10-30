#!/bin/bash
# usage: run_chunks.sh START_CHUNK END_CHUNK_EXCL  (chunks of 50 ids from part_05); stops starting chunks after DEADLINE (epoch secs)
cd /home/user/degree-diameter/research/squads/s65r5/c6
TOOLS=/home/user/degree-diameter/research/s65/tools
IDSFILE=/home/user/degree-diameter/research/s65/c3p256/part_05
START=$1; END=$2; DEADLINE=$3
touch results.txt
for ((c=START; c<END; c++)); do
  now=$(date +%s)
  if [ "$now" -ge "$DEADLINE" ]; then echo "deadline reached before chunk $c" >> progress.txt; break; fi
  ids=$(sed -n "$((c*50+1)),$((c*50+50))p" $IDSFILE | paste -sd, -)
  if [ -z "$ids" ]; then break; fi
  rm -rf d && mkdir -p d
  echo "chunk $c start $(date +%H:%M:%S) ids=$(echo $ids | cut -d, -f1)..$(echo $ids | awk -F, '{print $NF}')" >> progress.txt
  gap -q -c "PORD:=256; IDS:=[$ids]; OUTDIR:=\"d\";" c3p_export.g > gap_chunk_$c.log 2>&1
  nfiles=$(ls d/*.dc2 2>/dev/null | wc -l)
  echo "chunk $c exported $nfiles dc2 files $(date +%H:%M:%S)" >> progress.txt
  for f in d/*.dc2; do
    [ -e "$f" ] || continue
    out=$(SA=1 SECS=3 SEED=1 timeout 60 nice -n 10 $TOOLS/dcenum "$f" 6 5 "$f.edges" 2>&1)
    best=$(echo "$out" | grep RESULT | sed -n 's/.* best \([-0-9]*\).*/\1/p' | head -1)
    [ -z "$best" ] && best=NA
    echo "$f $best" >> results.txt
    if [ "$best" = "0" ]; then
      echo "*** RECORD CANDIDATE (cost 0): $f" >> progress.txt
      cp "$f.edges" "record_$(basename $f .dc2).edges" 2>/dev/null
    fi
    if [ "$best" = "NA" ] || [ "$best" -gt 40 ] 2>/dev/null; then rm -f "$f" "$f.edges"; fi
  done
  echo "chunk $c done $(date +%H:%M:%S)" >> progress.txt
  rm -rf d
done
echo "driver exit $(date +%H:%M:%S)" >> progress.txt
