#!/bin/bash
# usage: run1.sh fam p n seed   (one 60 s run, c11 card)
D=/home/user/degree-diameter/research/squads/beyond11/r1/c11
name=$1_$2_$3_s$4
cd $D && ORBIT="3 4 1" THREADS=1 timeout 105 nice -n 10 /home/user/degree-diameter/research/frontier/beyond11/bin/haar_big0 13 9 60 $4 4 $D/$name.sol $1 $2 $3 > $D/$name.log 2>&1
echo "exit=$?"; grep RESULT $D/$name.log; grep -m1 start $D/$name.log
