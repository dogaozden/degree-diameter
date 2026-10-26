#!/bin/bash
# usage: run2.sh N:I N:I ... ; per group: GAP generates H-invariant Haar files (timeout 150 s), then bicoset scans each.
C=/home/user/degree-diameter/research/squads/f65r1/c14
W=$C/work
cd $C
RES=$C/results.txt
for pair in "$@"; do
  n=${pair%%:*}; i=${pair##*:}
  printf 'group %s:%s start %s\n' "$n" "$i" "$(date +%T)" >> $C/progress.log
  printf 'Read("%s/gen.g");\nMAN := OutputTextFile("%s/manifest_%s_%s.txt", false);\nSetPrintFormattingStatus(MAN, false);\nDoGroup(%s, %s, MAN);\nCloseStream(MAN);\nQUIT;\n' "$C" "$W" "$n" "$i" "$n" "$i" > $C/gen_${n}_$i.g
  timeout 150 nice -n 10 gap -q $C/gen_${n}_$i.g > $C/gen_${n}_$i.log 2>&1 || echo "gen timeout/fail $n:$i" >> $C/progress.log
  [ -f $W/manifest_${n}_$i.txt ] || continue
  while read f label hs no nfix; do
    out=$(MAXFIX=3 SAVEBEST=1 timeout 120 nice -n 10 ./bicoset "$f" 6 5 "$W/$label" < /dev/null | grep '^DONE')
    min=$(echo "$out" | sed 's/.* min=\([-0-9]*\).*/\1/')
    echo "$label H=$hs orbits=$no fixedorbits=$nfix min=$min" >> $RES
    if [ "$min" = "0" ] && [ -f "$W/$label.edges" ]; then
      echo "CHECK $label: $(./apsp "$W/$label.edges" 6 5 | tail -1)" >> $C/progress.log
    fi
    rm -f "$f"
  done < $W/manifest_${n}_$i.txt
  printf 'group %s:%s scanned %s\n' "$n" "$i" "$(date +%T)" >> $C/progress.log
done
echo ALLDONE >> $C/progress.log
