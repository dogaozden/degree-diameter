#!/bin/bash
# run_any.sh LISTFILE BUDGET_SECS [BINARY]
# Lines: "meta m k r cs" (split metacyclic) or "ns m k r s cs" (non-split metacyclic, table from w2's nonsplit.py).
# cs = screen cost (initial bound). Resumable: groups with "done 1" in state/ are skipped. Foreground use only.
# certified.tsv gets every DONE group; the scoreboard gets a line only for a new lowest cost at that n.
W=/home/user/degree-diameter/research/squads/handsoff-49/w11
H=/home/user/degree-diameter/research/squads/handsoff-49
EXH=${3:-./exh3}
cd $W
BUDGET=${2:-470}
T0=$(date +%s)
while read kind a b c d e; do
  if [ "$kind" = "meta" ]; then
    m=$a; k=$b; r=$c; cs=$d; tag="m${m}_k${k}_r${r}"; args="meta $m $k $r"
  elif [ "$kind" = "ns" ]; then
    m=$a; k=$b; r=$c; s=$d; cs=$e; tag="ns_m${m}_k${k}_r${r}_s${s}"
    tb=tabs/$tag.bin
    [ -f $tb ] || python3 ../w2/nonsplit.py --table $m $k $r $s $tb
    args="tab $tb"
  else
    continue
  fi
  if [ -f state/$tag.txt ] && grep -q "done 1" state/$tag.txt; then continue; fi
  rem=$(( BUDGET - ($(date +%s) - T0) ))
  [ $rem -lt 20 ] && break
  N=$((m*k))
  out=$(timeout $((rem + 40)) nice -n 10 $EXH $args $cs $tag $rem 2>&1)
  echo "$out" | grep -E "^(DONE|PAUSED|IMPROVED|WROTE|COST0)" | tail -4 >> logs/run_any.log
  if echo "$out" | grep -q "^DONE"; then
    mn=$(echo "$out" | sed -n 's/^DONE.*min=\([0-9]*\).*/\1/p')
    secs=$(sed -n 's/.*secs \([0-9.]*\).*/\1/p' state/$tag.txt)
    echo -e "$tag\t$((2*N))\t$mn\t$cs\t$secs" >> certified.tsv
    file=none
    if [ -f out/${tag}_c${mn}.edges ]; then file=$W/out/${tag}_c${mn}.edges; fi
    if [ "$mn" -eq 0 ] && [ -f "$file" ]; then
      ap=$(../tools/apsp $file 4 9 | tail -1); echo "COST0 $tag: $ap" >> logs/run_any.log
      if echo "$ap" | grep -q "VALID d=4 D=9"; then cp $file $H/records/w11_n$((2*N)).edges; fi
    fi
    low=$(awk -F'\t' -v n=$((2*N)) '$4==n && $5 ~ /^[0-9]+$/ {if (best=="" || $5+0 < best+0) best=$5} END{print best}' $H/scoreboard.tsv)
    if [ -z "$low" ] || [ "$mn" -lt "$low" ]; then
      printf "%s\tw11\texhaustive %s (all triples up to Aut, bound %s)\t%d\t%s\tno\t%s\n" "$(date -u +%H:%M)" "$tag" $cs $((2*N)) $mn "$file" >> $H/scoreboard.tsv
    fi
  fi
done < $1
echo "$(date -u +%H:%M) pass ended ($1)" >> logs/run_any.log
