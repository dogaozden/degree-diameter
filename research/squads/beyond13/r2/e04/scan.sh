#!/bin/bash
# e04: exhaustive S={e,x,y} scan at D=13 over groups of order 1450-2200 (ex = r1/c03 exh tool)
E=/home/user/degree-diameter/research/squads/beyond13/r2/e04
B=/home/user/degree-diameter/research/frontier/beyond13
cd $E
for g in "$@"; do
  s=$(echo "$g" | tr -c 'A-Za-z0-9' '_')
  [ -f tables/$s.bin ] || timeout 300 nice -n 10 python3 /home/user/degree-diameter/research/squads/beyond13/r1/c03/gen.py "$g" tables/$s.bin > runs/gen_$s.log 2>&1 || { echo "GENFAIL $g" >> runs/scan.log; continue; }
  timeout 400 nice -n 10 ./ex tables/$s.bin 13 1 > runs/ex_$s.out 2>&1
  echo "$g :: $(grep SUMMARY runs/ex_$s.out) $(grep -c VALID runs/ex_$s.out)" >> runs/scan.log
  if grep -q '^VALID' runs/ex_$s.out; then
    read x y < <(grep '^VALID' runs/ex_$s.out | head -1 | awk '{print $2, $3}')
    echo "FOUND $g x=$x y=$y" >> runs/scan.log
    timeout 100 nice -n 10 python3 $B/tab2edges.py tables/$s.bin sols/$s.edges 0 $x $y >> runs/scan.log 2>&1
    echo "$s $x $y" >> sols/found.txt

  fi
done
echo SCANDONE >> runs/scan.log
