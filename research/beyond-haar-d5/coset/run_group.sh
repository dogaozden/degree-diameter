#!/bin/bash
# usage: run_group.sh NAME "GAP expr" H_ORDER DELTA   -> exports all (H, K) class pairs and enumerates every union
name=$1; expr=$2; h=$3; delta=$4
mkdir -p out logs
gap -q -c "GNAME:=\"$name\"; G:=$expr; H_ORDER:=$h; OUT:=\"out/${name}_h$h\";" dc_export.g 2>&1 | grep -v "Syntax\|^ \|\^" > logs/${name}_h$h.export
for f in out/${name}_h${h}_*.dc; do
  timeout 600 ./dcenum $f $delta 5 ${f%.dc}.best.edges 3000000 | tail -1
done | tee logs/${name}_h${h}_d$delta.result
rm -f out/${name}_h${h}_*.dc
