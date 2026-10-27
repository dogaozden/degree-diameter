#!/bin/bash
# c5: alternative spread = Hermitian-type spread of Q^-(5,11) inside a random hyperplane (hspread.py), R0 fixed
D=/home/user/degree-diameter/research/projects/hexagon-family/ext
T=/home/user/degree-diameter/research/d10D7/sets
W=/home/user/degree-diameter/research/squads/hexfam_r3/c5
cd $W
while pgrep -f "extend5.py 11 R_r2" > /dev/null; do sleep 2; done
echo "variant r2 set: lines $(wc -l < v_r2.pairs 2>/dev/null)"
timeout 120 nice -n 10 python3 $T/hspread.py /home/user/degree-diameter/research/projects/hexagon-family/hex/hex_q11.bin 11 11 1 1 HS1.txt > hs1.log 2>&1
echo "hspread: $(tail -1 hs1.log)"
timeout 200 nice -n 10 python3 $D/extend5.py 11 R0.txt HS1.txt v_hs1.pairs 1 30000 100 1 > v_hs1.log 2>&1
echo "variant hyperplane spread HS1: lines $(wc -l < v_hs1.pairs 2>/dev/null)"
echo DONE
