#!/bin/bash
# usage: prodh_sweep.sh NAME "GAP expression for G" h DELTA SECS -- bi-coset graphs of a constructed group G with
# core-free H of order h (all pairs of classes): exhaustive up to 2M unions, else SECS of annealing.
# Lines in logs/prodh_d<DELTA>.txt
name=$1; expr=$2; h=$3; delta=$4; secs=$5
dir=tmpq_${name}_$$; mkdir -p $dir logs
gap -q -c "Read(\"dc2_lib.g\"); G:=$expr; G:=Image(IsomorphismPermGroup(G)); G:=Image(SmallerDegreePermutationRepresentation(G)); ExportPairs(G, $h, \"$dir/$name\"); QUIT;" > $dir/gap.log 2>&1
for f in $dir/*.dc2; do
  [ -e "$f" ] || continue
  r=$(timeout 7200 nice -n 5 ./dcenum $f $delta 5 ${f%.dc2}.edges 2000000 2>/dev/null | tail -1)
  case "$r" in *"tested 2000000 "*) r="$r || $(SA=1 SECS=$secs SEED=1 timeout $((secs*8+600)) ./dcenum $f $delta 5 ${f%.dc2}.edges 2>/dev/null | tail -1)";; esac
  echo "$name h$h $r" >> logs/prodh_d${delta}.txt
  case "$r" in *"best 0 "*) cp ${f%.dc2}.edges logs/HIT_$(basename ${f%.dc2}).edges; cp $f logs/; echo "HIT $r";; esac
  rm -f $f ${f%.dc2}.edges
done
[ -z "$(ls $dir/*.dc2 2>/dev/null)" ] && grep -q . $dir/gap.log && echo "$name h$h gap: $(head -c 200 $dir/gap.log)" >> logs/prodh_d${delta}.txt
rm -rf $dir
