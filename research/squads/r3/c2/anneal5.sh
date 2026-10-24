#!/bin/bash
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
D=/home/user/degree-diameter/research/squads/r3/c2
cd $D
run(){ tag=$1; alpha=$2; shift 2
  if [ -n "$alpha" ]; then export ALPHA=$alpha; else unset ALPHA; fi
  ORBIT="3 3 1" timeout 900 nice -n 10 $B/haar_sym 10 5 300 1 8 $D/$tag.txt "$@" > $D/$tag.log 2>&1
  echo "$tag $(grep RESULT $D/$tag.log | tail -1)"
}
run pgl3psl3_7_a102 102 prod psl 3 pgl 3 7
run pgl3psl3_7_a28 28 prod psl 3 pgl 3 7
run sl2sl7_a1776 1776 prod sl 2 sl 7 1
run agl13_z13 "" prod agl1 13 cyc 13
run sl3agl4_7_a136 136 prod sl 3 agl1 4 7
echo ALLDONE
