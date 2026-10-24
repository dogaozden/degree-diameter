#!/bin/bash
# Sequential 600 s runs for card c3 (squad r1). One heavy process at a time.
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin/haar_sym
D=/home/user/degree-diameter/research/squads/r1/c3
run() { # tag ORBIT group...
  local tag=$1 orb=$2; shift 2
  echo "START $tag $(date +%T) ORBIT=$orb $*"
  ORBIT="$orb" timeout 900 nice -n 10 $B 12 5 600 1 8 $D/$tag.txt "$@" > $D/$tag.log 2>&1
  echo "END $tag rc=$? $(date +%T) $(grep RESULT $D/$tag.log | tail -1)"
}
run r1_sl7_13_340   "3 4 0" sl 7 13 1
run r1_pgl4_73_340  "3 4 0" pgl 4 73 1
run r1_psl7_25_430  "4 3 0" psl 7 25 1
run r1_psl11_7_620  "6 2 0" psl 11 7 1
echo ALLDONE $(date +%T)
