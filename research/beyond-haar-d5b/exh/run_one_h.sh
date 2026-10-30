#!/bin/bash
# usage: run_one_h.sh ORDER ID  -- haar5x (all Haar graphs of valency 5, diameter 5) on SmallGroup(ORDER, ID)
o=$1; i=$2; p=grp/h_${o}_$i
gap -q -c "ORDER:=$o; ID:=$i; OUT:=\"$p\";" gap_tab_gens.g > /dev/null 2>&1
r=$(nice -n 3 ./haar5x $p.txt $p.gens 2>&1 > runs/haar5x_${o}_$i.sol | tail -1)
echo "$(cat $p.info) :: $r" >> runs/haar5x_$o.txt
n=$(grep -c SOL runs/haar5x_${o}_$i.sol); if [ "$n" -gt 0 ]; then echo "haar $o $i HIT $n" >> runs/HITS.txt; cp $p.txt runs/haar5x_${o}_$i.table; else rm -f runs/haar5x_${o}_$i.sol; fi
rm -f $p.txt $p.gens $p.info
