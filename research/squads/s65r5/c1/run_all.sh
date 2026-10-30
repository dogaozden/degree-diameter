#!/bin/bash
# card c1: sweep G = C3 x SmallGroup(256,id) non-Haar |H|=2 coset graphs (dcenum SA), chunks of 50 ids.
cd /home/user/degree-diameter/research/squads/s65r5/c1
DEADLINE=$(date -d "2026-10-30 09:46:00 UTC" +%s)
PART=/home/user/degree-diameter/research/s65/c3p256/part_00
DCENUM=/home/user/degree-diameter/research/s65/tools/dcenum
SCORE=/home/user/degree-diameter/research/s65/tools/score65
APSP=/home/user/degree-diameter/research/s65/tools/apsp
touch results.txt progress.txt
N=$(wc -l < $PART)
for ((s=1; s<=N; s+=50)); do
  if [ $(date +%s) -ge $DEADLINE ]; then echo "$(date -u +%T) STOP: deadline reached before chunk starting at line $s" >> progress.txt; break; fi
  ids=$(sed -n "${s},$((s+49))p" $PART | paste -sd, -)
  rm -rf d; mkdir -p d
  echo "$(date -u +%T) chunk lines $s-$((s+49)) start" >> progress.txt
  gap -q -c "PORD:=256; IDS:=[$ids]; OUTDIR:=\"d\";" c3p_export.g > gap_$s.log 2>&1
  for f in d/*.dc2; do
    [ -e "$f" ] || continue
    SA=1 SECS=3 SEED=1 timeout 60 nice -n 10 $DCENUM "$f" 6 5 "$f.edges" > "$f.log" 2>&1
    best=$(grep -o 'best [-0-9]*' "$f.log" | head -1 | awk '{print $2}')
    [ -z "$best" ] && best=NA
    b=$(basename "$f")
    echo "$b $best" >> results.txt
    if [ "$best" = "0" ]; then
      echo "$(date -u +%T) RECORD CANDIDATE $b" >> progress.txt
      cp "$f.edges" keep/$b.edges 2>/dev/null
      $SCORE "$f.edges" >> record.txt 2>&1
      $APSP "$f.edges" 6 5 >> record.txt 2>&1
    fi
    if [ "$best" != "NA" ] && [ "$best" -le 40 ]; then
      mv "$f" keep/; [ -e "$f.edges" ] && mv "$f.edges" keep/
    else
      rm -f "$f" "$f.edges"
    fi
  done
  echo "$(date -u +%T) chunk lines $s-$((s+49)) done ($(grep -c . results.txt) results so far)" >> progress.txt
done
echo "$(date -u +%T) ALL DONE" >> progress.txt
