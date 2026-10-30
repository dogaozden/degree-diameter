#!/bin/bash
# usage: run_chunk.sh NN   (processes ids_NN, one chunk; all work in this card folder)
cd /home/user/degree-diameter/research/squads/s65r5/c5
DCENUM=/home/user/degree-diameter/research/s65/tools/dcenum
SCORE=/home/user/degree-diameter/research/s65/tools/score65
APSP=/home/user/degree-diameter/research/s65/tools/apsp
c=$1
START=$(cat start_epoch.txt)
NOW=$(date +%s)
if [ $((NOW-START)) -gt $((27*60)) ]; then echo "time limit reached, not starting chunk $c"; exit 0; fi
rm -rf d; mkdir -p d
ids=$(paste -sd, ids_$c)
gap -q -c "PORD:=256; IDS:=[$ids]; OUTDIR:=\"d\";" c3p_export.g > gap_$c.log 2>&1
n=0
for f in d/*.dc2; do
  [ -e "$f" ] || continue
  n=$((n+1))
  out=$(SA=1 SECS=3 SEED=1 timeout 60 nice -n 10 $DCENUM $f 6 5 $f.edges 2>&1 | grep '^RESULT')
  best=$(echo "$out" | sed -n 's/.* best \([0-9-]*\) .*/\1/p')
  [ -z "$best" ] && best=ERR
  echo "$f $best" >> results.txt
  if [ "$best" = "0" ]; then
    echo "!!! RECORD CANDIDATE $f cost 0" | tee -a RECORDS.txt
    $SCORE $f.edges | tee -a RECORDS.txt
    $APSP $f.edges 6 5 | tee -a RECORDS.txt
  fi
  if [ "$best" = "ERR" ] || [ "$best" -gt 40 ] 2>/dev/null; then
    rm -f $f $f.edges
  else
    mv $f $f.edges keep/
  fi
done
echo "chunk $c done: $n pairs exported, $(date -u +%H:%M:%S)" | tee -a progress.txt
rm -rf d
