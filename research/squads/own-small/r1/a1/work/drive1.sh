#!/bin/bash
# one gated run: random-start anneals and requot-seeded anneals over H=110 (index 2) base, logs best cost per run
W=/home/user/degree-diameter/research/squads/own-small/r1/a1/work; cd $W
echo "== random starts H110 T0=1.5"
for s in 1 2 3 4 5 6; do
  r=$(QUIET=1 T0=1.5 ./flift_s rq_110/h110_w0_l0.base rq_110/H110_0.bin 3 10 20 $s 8 $W/d1_rand_$s.sol | tail -1); echo "seed $s: $r"; done
echo "== requot seeds H110 T0=0.5"
for li in 0 20 40 60 80 100; do
  r=$(START=rq110_lines/h110_w0_l${li}.volts QUIET=1 T0=0.5 ./flift_s rq110_lines/h110_w0_l${li}.base rq_110/H110_0.bin 3 10 20 $li 8 $W/d1_req_$li.sol | tail -1); echo "line $li: $r"; done
