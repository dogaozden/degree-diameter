#!/bin/bash
# Card c1 queue (directed (10,5)). Runs strictly one at a time; stops at the first solution.
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
DIR=/home/user/degree-diameter/research/squads/r1/c1
cd $DIR
SUM=$DIR/queue_summary.txt
run_one() {
  local tag=$1 secs=$2 seed=$3 orbit=$4 orbw=$5; shift 5
  echo "START $tag $(date +%H:%M:%S) orbit=$orbit orbw=$orbw secs=$secs seed=$seed group=$*" >> $SUM
  if [ -n "$orbw" ]; then
    ORBIT="$orbit" ORBW="$orbw" timeout 900 nice -n 10 $B/haar_sym 10 5 $secs $seed 8 $DIR/$tag.txt "$@" > $DIR/$tag.log 2>&1
  else
    ORBIT="$orbit" timeout 900 nice -n 10 $B/haar_sym 10 5 $secs $seed 8 $DIR/$tag.txt "$@" > $DIR/$tag.log 2>&1
  fi
  echo "END $tag $(date +%H:%M:%S) $(grep RESULT $DIR/$tag.log)" >> $SUM
  if grep -Eq "best=0( |$)" $DIR/$tag.log; then
    echo "SOLVED $tag" >> $SUM
    python3 /home/user/degree-diameter/research/frontier/build_haar2.py $DIR/$tag.txt $DIR/$tag.edges.txt >> $SUM 2>&1
    exit 0
  fi
}
run_one s1_sl13_331        600 1 "3 3 1" ""  sl 13 1
run_one s1_prodA4SL3x7_331 600 1 "3 3 1" ""  prod psl 3 sl 3 7
run_one s1_prodA4PSL7_331  600 1 "3 3 1" ""  prod psl 3 psl 7 1
run_one s2_sl13_331        600 2 "3 3 1" ""  sl 13 1
run_one s3_sl13_331        600 3 "3 3 1" ""  sl 13 1
run_one orbw3_sl13_331     600 1 "3 3 1" 3   sl 13 1
run_one s1_pgl13_331       600 1 "3 3 1" ""  pgl 13 1
run_one s1_psl7x13_331     600 1 "3 3 1" ""  psl 7 13
run_one k2_sl13_250        300 1 "2 5 0" ""  sl 13 1
run_one k2_pgl13_250       300 1 "2 5 0" ""  pgl 13 1
run_one k2_psl7x13_250     300 1 "2 5 0" ""  psl 7 13
run_one s1_sl4x37_331      600 1 "3 3 1" ""  sl 4 37
echo "QUEUE DONE $(date +%H:%M:%S)" >> $SUM
