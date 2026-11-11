#!/bin/bash
# run_list.sh LIST SEED : runs salift_s (D=13, p=2, 12 CPU-s) over "N m k r c" lines of LIST, skipping (group, seed)
# pairs already in results.txt; stops starting new groups after ~70 s of wall time (each Bash call < 110 s).
F=/home/user/degree-diameter/research/squads/raise-small/r5/g01
RS=/home/user/degree-diameter/research/frontier/raise_small
L=$1; s=$2; cd $F || exit 1
touch results.txt
T0=$SECONDS
while read N m k r c rest; do
  [ -z "$N" ] && continue
  if awk -v a="$N $m $k $r $c $s" '($1" "$2" "$3" "$4" "$5" "$6)==a {f=1} END{exit !f}' results.txt; then continue; fi
  if [ $((SECONDS - T0)) -gt 76 ]; then echo "STOP-budget"; break; fi
  python3 $RS/tools/gtab.py $F/g.tab $m $k $r $c > /dev/null 2>&1
  rm -f $F/o.sol $F/o.sol.best
  D=13 timeout 100 nice -n 10 $RS/bin/salift_s 2 $F/g.tab 1 $s 12 10 0.3 $F/o.sol > $F/run.log 2>&1
  cost=$(head -1 $F/o.sol.best 2>/dev/null | awk '{print $4}'); [ -z "$cost" ] && cost=NA
  echo "$N $m $k $r $c $s $cost" >> results.txt
  echo "$N $m $k $r $c $s $cost"
  if [ -f $F/o.sol ]; then
    tag="${N}_${m}_${k}_${r}_${c}_s${s}"
    mv $F/o.sol $F/zero_$tag.sol
    python3 $RS/tools/sol2edges.py $F/zero_$tag.sol $m $k $r $c $F/zero_$tag.edges > /dev/null
    echo "CHECK $tag: $($RS/bin/apsp $F/zero_$tag.edges 3 13 | tail -1)"
    echo "CHECK-D12 $tag: $($RS/bin/apsp $F/zero_$tag.edges 3 12 | tail -1)" >/dev/null
  fi
  rm -f $F/g.tab
done < $L
rm -f $F/g.tab
