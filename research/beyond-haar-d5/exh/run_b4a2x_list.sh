#!/bin/bash
# usage: exh/run_b4a2x_list.sh "ids"   exact a=2 search for the listed groups of order 90
for i in $1; do
  r=$(nice -n 5 ./exh/b4a2x exh/grp/g90_$i.txt exh/grp/g90_$i.aut 2>&1 > exh/runs/b4a2x_90_$i.sol | tail -1)
  echo "90 $i :: $r" >> exh/runs/b4a2x_90.txt
done
