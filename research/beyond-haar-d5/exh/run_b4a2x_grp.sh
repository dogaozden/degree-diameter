#!/bin/bash
# usage: exh/run_b4a2x_grp.sh ORDER "ids"   exact search of the base [[2,3],[3,2]] for the listed SmallGroup(ORDER,i)
o=$1
for i in $2; do
  r=$(./exh/b4a2x exh/grp/g${o}_$i.txt exh/grp/g${o}_$i.aut 2>&1 > exh/runs/b4a2x_${o}_$i.sol | tail -1)
  echo "$o $i :: $r" >> exh/runs/b4a2x_$o.txt
done
