#!/bin/bash
# usage: run_chunk.sh CHUNKIDX ; processes ids in /home/user/degree-diameter/research/s65/c3p256/part_03 lines [50*k+1 .. 50*k+50]
K=$1
cd /home/user/degree-diameter/research/squads/s65r5/c4 || exit 1
IDS=$(sed -n "$((50*K+1)),$((50*K+50))p" /home/user/degree-diameter/research/s65/c3p256/part_03 | paste -sd, -)
[ -z "$IDS" ] && exit 0
mkdir -p d
echo "chunk $K start $(date +%T) ids $IDS" >> progress.txt
gap -q -c "PORD:=256; IDS:=[$IDS]; OUTDIR:=\"d\";" c3p_export.g > gap_$K.log 2>&1
n=0
for f in d/*.dc2; do
  [ -e "$f" ] || continue
  n=$((n+1))
  base=${f%.dc2}
  out=$(SA=1 SECS=3 SEED=1 timeout 60 nice -n 10 /home/user/degree-diameter/research/s65/tools/dcenum "$f" 6 5 "$base.edges" 2>&1 | grep RESULT)
  best=$(echo "$out" | awk '{for(i=1;i<=NF;i++) if($i=="best"){print $(i+1); exit}}')
  [ -z "$best" ] && best=NA
  echo "$(basename $f) $best" >> results.txt
  if [ "$best" = "0" ]; then echo "RECORD CANDIDATE $f" >> records.txt; fi
  if [ "$best" = "NA" ] || [ "$best" -gt 40 ] 2>/dev/null; then rm -f "$f" "$base.edges"; else echo "$(basename $f) $best" >> keep.txt; fi
done
echo "chunk $K done $(date +%T) pairs $n" >> progress.txt
