#!/bin/bash
# exhaustive cubic Haar (e,x,y) over odd-order Frobenius groups Z_m x|_r Z_k, D=13, N=mk in [1601,2600]
B=/home/user/degree-diameter/research/frontier/beyond13
H=/home/user/degree-diameter/research/squads/beyond13/r5/h15
cd $H
while read N m k r d; do
  f=tab_${m}_${k}_${r}.bin
  nice -n 10 python3 mkfrob.py $m $k $r $f
  echo "== m=$m k=$k r=$r order_r=$d"
  THREADS=1 nice -n 10 $B/bin/exh3 $f 13 $H/sol_${m}_${k}_${r} | grep -E "GROUP|RESULT|WROTE"
  rm -f $f
done < cands.txt
echo DONE
