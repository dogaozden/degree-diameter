#!/bin/bash
# usage: drive.sh ORDER IDX SA_SECS   (h=2, Delta=7, D=5). Exports all (H,K) involution-class pairs of SmallGroup(ORDER,IDX)
# with coset/dc2_lib.g, then dcenum each pair: exhaustive up to 2M unions, then SA for SA_SECS if capped and SA_SECS>0.
# Output: c1/logs/<name>.r2 ; cost-0 graphs copied to c1/logs/HIT_<name>_*.edges
ORDER=$1; IDX=$2; SA=${3:-0}
C1=/home/user/degree-diameter/research/squads/bh5-r4/c1
COSET=/home/user/degree-diameter/research/beyond-haar-d5/coset
name=c1_${ORDER}_${IDX}
cd $COSET || exit 1
gap -q -c "G:=Image(IsomorphismPermGroup(SmallGroup($ORDER,$IDX))); H_ORDER:=2; Read(\"dc2_lib.g\"); ExportPairs(G, H_ORDER, \"$C1/work/$name\"); QUIT;" > $C1/work/$name.gap.log 2>&1
out=$C1/logs/$name.r2; : > $out
for f in $C1/work/${name}_*.dc2; do
  [ -e "$f" ] || continue
  e=${f%.dc2}.edges
  r=$(timeout 200 nice -n 10 ./dcenum $f 7 5 $e 2000000 2>/dev/null | tail -1)
  if [ -z "$r" ]; then r="RESULT $(basename $f) FAILED"; fi
  case "$r" in *"tested 2000000 "*) if [ "$SA" -gt 0 ]; then
      s=$(SA=1 SECS=$SA timeout $((SA+120)) nice -n 10 ./dcenum $f 7 5 $e 2>/dev/null | tail -1)
      r="$r || $s"; fi;;
  esac
  echo "$r" | tee -a $out
  case "$r" in *"best 0 "*) cp $e $C1/logs/HIT_$(basename ${f%.dc2}).edges; echo "HIT $r";; esac
  rm -f $f
done
echo DONE $name >> $out
