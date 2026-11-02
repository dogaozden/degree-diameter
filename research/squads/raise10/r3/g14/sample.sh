#!/bin/bash
# usage: sample.sh D-d-K-label  (runs RANDSAMPLE for the family list below; program-secs irrelevant, sampling only)
BIN=/home/user/degree-diameter/research/squads/raise10/tools/bin/haar_gen3
run() { # d D samples group-args...
  local d=$1 D=$2 m=$3; shift 3
  THREADS=1 RANDSAMPLE=$m timeout -s KILL 110 nice -n 10 $BIN $d $D 1 1 1 /dev/null "$@" 2>&1 | grep RANDSAMPLE
}
if [ "$1" = "510" ]; then
  for m in 20 200; do
  run 5 10 $m prod psl 3 meta 239 17 6 1
  run 5 10 $m prod sl 3 meta 509 4 208 1
  run 5 10 $m prod meta 7 3 2 meta 137 17 16 1
  run 5 10 $m prod psl 7 meta 97 3 35 1
  run 5 10 $m meta 2017 24 122 1
  run 5 10 $m meta 1783 27 255 1
  run 5 10 $m meta 1453 33 11 1
  done
fi
if [ "$1" = "610" ]; then
  for m in 20 200; do
  run 6 10 $m meta 6397 41 503 1
  run 6 10 $m meta 10501 25 608 1
  run 6 10 $m prod psl 3 meta 811 27 7 1
  run 6 10 $m prod sl 3 meta 457 24 70 1
  run 6 10 $m prod psl 7 meta 113 14 4 1
  run 6 10 $m meta 8053 33 190 1
  done
fi
