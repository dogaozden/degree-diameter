#!/bin/bash
# usage: run_one_a1.sh ORDER ID  -- b4a1x (base [[1,4],[4,1]]) on SmallGroup(ORDER, ID); line in runs/b4a1x_ORDER.txt
o=$1; i=$2; p=grp/a1_${o}_$i
gap -q -c "ORDER:=$o; ID:=$i; OUT:=\"$p\";" gap_tab_autlist.g > /dev/null 2>&1
r=$(nice -n 3 ./b4a1x $p.txt $p.aut 2>&1 > runs/b4a1x_${o}_$i.sol | tail -1)
echo "$(cat $p.info) :: $r" >> runs/b4a1x_$o.txt
n=$(grep -c SOL runs/b4a1x_${o}_$i.sol); [ "$n" -gt 0 ] && echo "a1 $o $i HIT $n" >> runs/HITS.txt
rm -f $p.txt $p.aut $p.info
