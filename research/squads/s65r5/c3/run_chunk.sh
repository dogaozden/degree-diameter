#!/bin/bash
# usage: run_chunk.sh NN   (NN = chunk index, file chunks/chunk_NN)
cd /home/user/degree-diameter/research/squads/s65r5/c3 || exit 1
K=$1
IDS=$(paste -sd, chunks/chunk_$K)
D=d_$K; rm -rf $D; mkdir -p $D
echo "chunk $K start $(date +%H:%M:%S)" >> progress.txt
timeout 500 nice -n 10 gap -q -c "PORD:=256; IDS:=[$IDS]; OUTDIR:=\"$D\";" c3p_export.g > gap_$K.log 2>&1
NF=$(ls $D/*.dc2 2>/dev/null | wc -l)
echo "chunk $K exported $NF pairs $(date +%H:%M:%S)" >> progress.txt
for f in $D/*.dc2; do
  [ -e "$f" ] || continue
  b=${f%.dc2}
  out=$(SA=1 SECS=3 SEED=1 timeout 60 nice -n 10 /home/user/degree-diameter/research/s65/tools/dcenum "$f" 6 5 "$b.edges" 2>&1 | grep RESULT)
  best=$(echo "$out" | sed -n 's/.* best \([-0-9]*\) .*/\1/p' | head -1)
  [ -z "$best" ] && best=NA
  echo "$f $best" >> results.txt
  if [ "$best" = "0" ]; then
    echo "!!! RECORD CANDIDATE $f cost 0 !!!" >> progress.txt
    echo "!!! RECORD CANDIDATE $f cost 0 !!!"
  fi
  if [ "$best" = "NA" ] || [ "$best" -gt 40 ] 2>/dev/null; then
    rm -f "$f" "$b.edges"
  fi
done
echo "chunk $K done $(date +%H:%M:%S)" >> progress.txt
