#!/bin/bash
# card c2 driver: chunked GAP export of C3 x SmallGroup(256,id) non-Haar |H|=2 coset pairs, SA scoring by dcenum (6,5).
W=/home/user/degree-diameter/research/squads/s65r5/c2
T=/home/user/degree-diameter/research/s65/tools
cd "$W" || exit 1
mkdir -p d keep re
START=$(date +%s)
LIMIT=$((27*60))
mapfile -t ALL < /home/user/degree-diameter/research/s65/c3p256/part_01
n=${#ALL[@]}
echo "start $(date -u +%H:%M:%S) ids $n" >> progress.txt
for ((i=0; i<n; i+=50)); do
  el=$(( $(date +%s) - START ))
  if [ $el -gt $LIMIT ]; then echo "STOP: not starting chunk at index $i (elapsed ${el}s) $(date -u +%H:%M:%S)" >> progress.txt; break; fi
  chunk=("${ALL[@]:i:50}")
  ids=$(IFS=,; echo "${chunk[*]}")
  rm -f d/*.dc2 d/*.edges
  gap -q -c "PORD:=256; IDS:=[$ids]; OUTDIR:=\"d\";" c3p_export.g > gap_$i.log 2>&1
  for f in d/*.dc2; do
    [ -e "$f" ] || continue
    b=${f%.dc2}
    name=$(basename "$b")
    out=$(SA=1 SECS=3 SEED=1 timeout 60 nice -n 10 "$T/dcenum" "$f" 6 5 "$b.edges" 2>/dev/null)
    best=$(echo "$out" | grep '^RESULT' | sed -E 's/.* best ([0-9]+) .*/\1/')
    [ -z "$best" ] && best=none
    echo "$name $best" >> results.txt
    if [ "$best" = "0" ]; then
      echo "!!! RECORD CANDIDATE (bad 0 coset cost) $name  $(date -u +%H:%M:%S)" >> progress.txt
      cp "$f" "keep/$name.dc2"; cp "$b.edges" "keep/$name.edges"
      { echo "== $name"; "$T/score65" "$b.edges"; "$T/apsp" "$b.edges" 6 5; } >> record.txt 2>&1
      cat record.txt | tail -4 >> progress.txt
    fi
    if [ "$best" != "none" ] && [ "$best" -le 40 ]; then
      cp "$f" "keep/$name.dc2"; [ -e "$b.edges" ] && cp "$b.edges" "keep/$name.edges"
    fi
    rm -f "$f" "$b.edges"
  done
  echo "chunk index $i done $(date -u +%H:%M:%S) elapsed $(( $(date +%s) - START ))s" >> progress.txt
done

# re-anneal the best 3 pairs (SEED=2, then SEED=3 if time allows)
awk '$2 ~ /^[0-9]+$/' results.txt | sort -k2,2n | head -3 > top3.txt
echo "top3: $(cat top3.txt | tr '\n' ';')" >> progress.txt
for seed in 2 3; do
  el=$(( $(date +%s) - START ))
  if [ $seed -eq 3 ] && [ $el -gt $((30*60)) ]; then echo "skip SEED=3 (elapsed ${el}s)" >> progress.txt; break; fi
  while read -r name best; do
    [ -e "keep/$name.dc2" ] || continue
    out=$(SA=1 SECS=60 SEED=$seed timeout 100 nice -n 10 "$T/dcenum" "keep/$name.dc2" 6 5 "re/${name}_s$seed.edges" 2>/dev/null)
    rb=$(echo "$out" | grep '^RESULT' | sed -E 's/.* best ([0-9]+) .*/\1/')
    echo "reanneal SEED=$seed $name prev_best $best new_best ${rb:-none}" >> reanneal.txt
    if [ "$rb" = "0" ]; then echo "!!! RECORD CANDIDATE from reanneal $name seed $seed" >> progress.txt; fi
  done < top3.txt
done
echo "DONE $(date -u +%H:%M:%S) elapsed $(( $(date +%s) - START ))s" >> progress.txt
