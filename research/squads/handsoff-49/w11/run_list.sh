#!/bin/bash
# run_list.sh LISTFILE BUDGET_SECS : lines "m k r cs" (cs = screen cost, used as the initial bound).
# Runs the exhaustive search (exh) on each group not yet done, within the budget; records DONE groups in certified.tsv
# and the scoreboard; a cost-0 hit is checked with apsp at once and copied to records/.
W=/home/user/degree-diameter/research/squads/handsoff-49/w11
H=/home/user/degree-diameter/research/squads/handsoff-49
cd $W
BUDGET=${2:-480}
T0=$(date +%s)
while read m k r cs; do
  tag="m${m}_k${k}_r${r}"
  if [ -f state/$tag.txt ] && grep -q "done 1" state/$tag.txt; then continue; fi
  rem=$(( BUDGET - ($(date +%s) - T0) ))
  [ $rem -lt 20 ] && break
  out=$(timeout $((rem + 40)) nice -n 10 ./exh meta $m $k $r $cs $tag $rem 2>&1)
  echo "$out" | grep -E "^(DONE|PAUSED|IMPROVED|WROTE)" | tail -4 >> logs/run_list.log
  if echo "$out" | grep -q "^DONE"; then
    N=$((m*k)); mn=$(echo "$out" | sed -n 's/^DONE.*min=\([0-9]*\).*/\1/p')
    secs=$(sed -n 's/.*secs \([0-9.]*\).*/\1/p' state/$tag.txt)
    echo -e "$tag\t$N\t$mn\t$cs\t$secs" >> certified.tsv
    file=none
    if [ "$mn" -le 4 ] && [ -f out/${tag}_c${mn}.edges ]; then file=$W/out/${tag}_c${mn}.edges; fi
    printf "%s\tw11\texhaustive meta %s %s %s (aut-reduced, all triples, bound %s)\t%d\t%s\tno\t%s\n" "$(date -u +%H:%M)" $m $k $r $cs $((2*N)) $mn "$file" >> $H/scoreboard.tsv
    if [ "$mn" -eq 0 ]; then
      ap=$(../tools/apsp $file 4 9 | tail -1); echo "COST0 $tag: $ap" >> logs/run_list.log
      if echo "$ap" | grep -q "VALID d=4 D=9"; then cp $file $H/records/w11_n$((2*N)).edges; fi
    fi
  fi
done < $1
echo "$(date -u +%H:%M) driver pass ended" >> logs/run_list.log
