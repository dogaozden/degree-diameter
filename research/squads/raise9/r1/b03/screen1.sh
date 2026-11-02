#!/bin/bash
# usage: screen1.sh fam p n samples
ORBIT="3 4 1" RANDORB=$4 THREADS=1 timeout 105 nice -n 10 /home/user/degree-diameter/research/squads/raise9/bin/haar_big0 13 9 60 1 1 /dev/null $1 $2 $3 2>&1 | grep RANDORB\ d= 
