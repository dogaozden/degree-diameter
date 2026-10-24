#!/bin/bash
# Card c1: anneal six tied best (min=4, |Fix|=17) choices, 300 s each, one at a time.
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
C=/home/user/degree-diameter/research/squads/r3/c1
cd $C
run() { # $1 = tag, $2 = AR value or "", $3 = alpha index
  if [ -n "$2" ]; then
    AR=$2 ALPHA=$3 ORBIT="3 3 1" timeout 900 nice -n 10 $B/haar_sym 10 5 300 1 8 $C/d10D5_a$1.txt prod psl 3 sl 3 7 > $C/d10D5_a$1.log 2>&1
  else
    ALPHA=$3 ORBIT="3 3 1" timeout 900 nice -n 10 $B/haar_sym 10 5 300 1 8 $C/d10D5_a$1.txt prod psl 3 sl 3 7 > $C/d10D5_a$1.log 2>&1
  fi
  echo "$1 done: $(grep RESULT $C/d10D5_a$1.log)" >> $C/anneal_summary.txt
}
: > $C/anneal_summary.txt
run 32 "" 32
run 60 "" 60
run 146 "" 146
run 201_ar4 4 201
run 227_ar4 4 227
run 257_ar4 4 257
echo ALL_DONE >> $C/anneal_summary.txt
