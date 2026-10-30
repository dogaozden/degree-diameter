#!/bin/bash
# exact a=2 search over the groups of order 90 (non-abelian first); results in exh/runs/b4a2x_90.txt
for i in 9 3 5 8 1 7 2 6 10 4; do
  [ -f exh/grp/g90_$i.aut ] || gap -q -c "ORDER:=90; ID:=$i; OUT:=\"exh/grp/g90_$i\";" src/gap_tab_aut.g > /dev/null 2>&1
  r=$(nice -n 5 ./exh/b4a2x exh/grp/g90_$i.txt exh/grp/g90_$i.aut 2>&1 > exh/runs/b4a2x_90_$i.sol | tail -1)
  echo "90 $i :: $r" >> exh/runs/b4a2x_90.txt
done
