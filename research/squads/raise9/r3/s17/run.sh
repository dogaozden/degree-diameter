#!/bin/bash
# usage: run.sh "k m f" seed samples sl|psl p n   -> appends the RANDORB summary to raw.log
B=/home/user/degree-diameter/research/squads/raise9/bin
cd /home/user/degree-diameter/research/squads/raise9/r3/s17
out=$(ORBIT="$1" RANDORB=$3 THREADS=1 timeout 105 nice -n 10 $B/haar_big0 17 9 60 $2 1 /dev/null $4 $5 $6 2>&1)
line=$(echo "$out" | grep -E "RANDORB d=" | tail -1)
mem=$(echo "$out" | grep -o "memory [0-9.]* GB" | head -1)
if [ -z "$line" ]; then line="NO SUMMARY (timeout or error): $(echo "$out" | tail -2 | tr '\n' ' ')"; fi
echo "$4 $5 $6 | ORBIT=$1 | seed=$2 | $mem | $line" >> raw.log
echo "$4 $5 $6 | ORBIT=$1 | seed=$2 | $mem | $line"
