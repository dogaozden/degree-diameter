#!/bin/bash
# usage: run.sh N1 N2 ...  (per order: generate H-invariant Haar files with GAP, scan each with bicoset)
C=/home/user/degree-diameter/research/squads/f65r1/c14
W=$C/work
cd $C
RES=$C/results.txt
for n in "$@"; do
  printf 'order %s start %s\n' "$n" "$(date +%T)" >> $C/progress.log
  printf 'Read("%s/gen.g");\nDoOrder(%s);\nQUIT;\n' "$C" "$n" > $C/gen_$n.g
  nice -n 10 timeout 900 gap -q $C/gen_$n.g > $C/gen_$n.log 2>&1
  printf 'gap done %s\n' "$(date +%T)" >> $C/progress.log
  [ -f $W/manifest_$n.txt ] || continue
  while read f label hs no nfix; do
    out=$(MAXFIX=3 SAVEBEST=1 timeout 120 nice -n 10 ./bicoset "$f" 6 5 "$W/$label" < /dev/null | grep '^DONE')
    min=$(echo "$out" | sed 's/.* min=\([-0-9]*\).*/\1/')
    echo "$label H=$hs orbits=$no fixedorbits=$nfix min=$min" >> $RES
    if [ "$min" = "0" ] && [ -f "$W/$label.edges" ]; then
      echo "CHECK $label: $(./apsp "$W/$label.edges" 6 5 | tail -1)" >> $C/progress.log
    fi
    rm -f "$f"
  done < $W/manifest_$n.txt
  printf 'order %s scan done %s\n' "$n" "$(date +%T)" >> $C/progress.log
done
echo ALLDONE >> $C/progress.log
