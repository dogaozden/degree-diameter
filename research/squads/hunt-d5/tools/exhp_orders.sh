#!/bin/bash
# exhp_orders.sh LO HI OUTLOG : exhaustive Delta=5 Haar search (haar5 exhp) over every group of every order LO..HI
T=$(dirname $0); mkdir -p $T/../tables/exhp
for ((n=$1; n<=$2; n++)); do
  k=$(echo "Print(NrSmallGroups($n),\"\\n\");QUIT;" > /tmp/nr_$n.g; /usr/local/lib/python3.13/dist-packages/sage_wheels/bin/gap -q /tmp/nr_$n.g | tr -d ' \n')
  for ((i=1; i<=k; i++)); do
    f=$T/../tables/exhp/g${n}_$i.bin
    [ -f $f ] || python3 $T/gapgroup.py table $n $i $f
    r=$(timeout 900 $T/haar5 exhp $f 5 0 | tail -1)
    echo "$n $i :: $r" >> $3
    rm -f $f
  done
done
echo DONE >> $3
