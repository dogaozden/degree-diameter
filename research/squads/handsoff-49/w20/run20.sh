#!/bin/bash
# run20.sh LIST BUDGET : exhaustive "is there a cost-0 set?" pass over the candidate list (foreground, resumable).
# Search limit 1 (exh3 records costs <= 1; IMPROVED = cost 0, WROTE cost=1 = exact minimum 1).
W=/home/user/degree-diameter/research/squads/handsoff-49/w20
H=/home/user/degree-diameter/research/squads/handsoff-49
W11=$H/w11
cd $W
BUDGET=${2:-480}
T0=$(date +%s)
[ -f certificate.tsv ] || printf "group\tN\tdk\ttype\tstatus\tno_cost0\tmin_seen\tseconds\n" > certificate.tsv
while IFS=$'\t' read dk N m k r s d typ; do
  [ "$dk" = "dk" ] && continue
  if [ "$typ" = "split" ]; then tag="m${m}_k${k}_r${r}"; args="meta $m $k $r"
  else tag="ns_m${m}_k${k}_r${r}_s${s}"; tb=tabs/$tag.bin
       [ -f $tb ] || python3 nonsplit.py --table $m $k $r $s $tb; args="tab $tb"; fi
  if grep -q "done 1" state/$tag.txt 2>/dev/null; then continue; fi
  if grep -q "^$tag	" certificate.tsv 2>/dev/null; then continue; fi
  if grep -q "^$tag	" $W11/certified.tsv 2>/dev/null; then
     w=$(grep "^$tag	" $W11/certified.tsv | head -1 | cut -f3)
     printf "%s\t%d\t%d\t%s\tcovered_by_w11\tno\tmin=%s\t0\n" $tag $((m*k)) $dk $typ "$w" >> certificate.tsv; continue; fi
  rem=$(( BUDGET - ($(date +%s) - T0) ))
  [ $rem -lt 30 ] && break
  out=$(timeout $((rem + 60)) nice -n 10 ./exh3 $args 1 $tag $rem 9 2>&1)
  secs=$(sed -n 's/.*secs \([0-9.]*\).*/\1/p' state/$tag.txt 2>/dev/null)
  if echo "$out" | grep -q "^DONE"; then
    hit=no; grep -q "IMPROVED\|WROTE cost=0" <<< "$out" && hit=YES
    mn=">=2"; grep -q "WROTE cost=1" <<< "$out" && mn=1
    if [ "$hit" = "YES" ]; then
      ap=$(../tools/apsp out/${tag}_c0.edges 4 9 2>/dev/null | tail -1)
      echo "COST0 $tag $ap" >> logs/hits.log; mn=0
    fi
    printf "%s\t%d\t%d\t%s\tDONE\t%s\t%s\t%s\n" $tag $((m*k)) $dk $typ $([ $hit = YES ] && echo HIT || echo yes) "$mn" "$secs" >> certificate.tsv
    echo "$(date -u +%H:%M) DONE $tag hit=$hit min=$mn secs=$secs" >> logs/run20.log
  else
    echo "$(date -u +%H:%M) PAUSED $tag secs=$secs" >> logs/run20.log
    break
  fi
done < "$1"
echo "$(date -u +%H:%M) pass ended ($1)" >> logs/run20.log
