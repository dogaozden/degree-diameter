#!/bin/bash
# usage: prod_sweep.sh NAME "GAP expression for G" DELTA SECS SEEDS -- bi-coset graphs of a constructed group G with
# core-free H of order 2 (all pairs of classes), SECS x SEEDS of annealing each; lines in logs/prod_d<DELTA>.txt
name=$1; expr=$2; delta=$3; secs=$4; seeds=${5:-1}
dir=tmpp_${name}_$$; mkdir -p $dir logs
gap -q -c "Read(\"dc2_lib.g\"); G:=$expr; G:=Image(IsomorphismPermGroup(G)); G:=Image(SmallerDegreePermutationRepresentation(G)); ExportPairs(G, 2, \"$dir/$name\"); QUIT;" > $dir/gap.log 2>&1
for f in $dir/*.dc2; do
  [ -e "$f" ] || continue
  for s in $(seq 1 $seeds); do
    r=$(SA=1 SECS=$secs SEED=$s timeout $((secs*8+600)) nice -n 5 ./dcenum $f $delta 5 ${f%.dc2}_s$s.edges 2>/dev/null | tail -1)
    echo "$name $r seed $s" >> logs/prod_d${delta}.txt
    case "$r" in *"best 0 "*) cp ${f%.dc2}_s$s.edges logs/HIT_$(basename ${f%.dc2})_s$s.edges; cp $f logs/; echo "HIT $r";; esac
  done
  rm -f $f ${f%.dc2}_s*.edges
done
rm -rf $dir
