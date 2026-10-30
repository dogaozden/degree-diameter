#!/bin/bash
# usage: exh/run_b4a1x.sh ORDER   (all SmallGroups of that order; results in exh/runs/b4a1x_<order>.txt)
o=$1; n=$(echo "Print(NrSmallGroups($o),\"\\n\"); QUIT;" | gap -q | tr -d '\r\n ')
for ((i=1; i<=n; i++)); do
  [ -f exh/grp/g${o}_$i.aut ] || gap -q -c "ORDER:=$o; ID:=$i; OUT:=\"exh/grp/g${o}_$i\";" src/gap_tab_aut.g > exh/grp/g${o}_$i.name 2>/dev/null
  r=$(./exh/b4a1x exh/grp/g${o}_$i.txt exh/grp/g${o}_$i.aut 2>&1 > exh/runs/b4a1x_${o}_$i.sol)
  echo "$o $i $(grep -v Syntax exh/grp/g${o}_$i.name | head -1) :: $r" >> exh/runs/b4a1x_$o.txt
done
