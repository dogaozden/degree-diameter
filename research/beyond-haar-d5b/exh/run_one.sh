#!/bin/bash
# usage: run_one.sh ORDER ID  -- export SmallGroup(ORDER, ID) (table + Aut generators) and run b4a2y on it;
# one result line in runs/b4a2y_ORDER.txt, solutions in runs/b4a2y_ORDER_ID.sol
o=$1; i=$2
[ -f grp/g${o}_$i.gens ] || gap -q -c "ORDER:=$o; ID:=$i; OUT:=\"grp/g${o}_$i\";" gap_tab_gens.g > /dev/null 2>&1
info=$(cat grp/g${o}_$i.info)
r=$(nice -n 3 ./b4a2y grp/g${o}_$i.txt grp/g${o}_$i.gens 2>&1 > runs/b4a2y_${o}_$i.sol | tail -1)
echo "$info :: $r" >> runs/b4a2y_$o.txt
n=$(grep -c SOL runs/b4a2y_${o}_$i.sol); [ "$n" -gt 0 ] && echo "$o $i HIT $n" >> runs/HITS.txt
rm -f grp/g${o}_$i.txt grp/g${o}_$i.gens
