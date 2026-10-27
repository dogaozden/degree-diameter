#!/bin/bash
# c5: vary the relative position of R (moveR isometries) and the R set; spread fixed (SP0 = L11_spread)
D=/home/user/degree-diameter/research/projects/hexagon-family/ext
W=/home/user/degree-diameter/research/squads/hexfam_r3/c5
cd $W
for v in "m1 1" "m2 2"; do
  set -- $v; name=$1; seed=$2
  timeout 60 nice -n 10 python3 $D/moveR.py 11 R0.txt R_$name.txt $seed 9
  timeout 200 nice -n 10 python3 $D/extend5.py 11 R_$name.txt SP0.txt v_$name.pairs 1 30000 100 1 > v_$name.log 2>&1
  echo "variant $name seed $seed: lines $(wc -l < v_$name.pairs 2>/dev/null)"
done
cp /home/user/degree-diameter/research/squads/hexfam_r2/c3/best_q11_756.txt R_r2.txt
timeout 200 nice -n 10 python3 $D/extend5.py 11 R_r2.txt SP0.txt v_r2.pairs 1 30000 100 1 > v_r2.log 2>&1
echo "variant r2 set: lines $(wc -l < v_r2.pairs 2>/dev/null)"
echo DONE
