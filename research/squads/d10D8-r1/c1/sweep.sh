#!/bin/bash
# usage: sweep.sh q rmin rmax iters seeds...   (one process at a time; sequential)
# runs lift3 with GROUP="prod r 5" HSUB=5 MCONST=1 T="1 2" J=2 D=8 for each r, seeds listed
Q=$1; RMIN=$2; RMAX=$3; IT=$4; shift 4
C1=/home/user/degree-diameter/research/squads/d10D8-r1/c1
cd /home/user/degree-diameter/research/d10D8/hex || exit 1
for r in $(seq $RMIN $RMAX); do
  m=$((5*r))
  if [ $m -gt 64 ]; then echo "r=$r m=$m exceeds 64, stop"; break; fi
  for s in "$@"; do
    tag=q${Q}_r${r}_m${m}_s${s}
    GROUP="prod $r 5" HSUB=5 MCONST=1 T="1 2" J=2 D=8 ITERS=$IT SEED=$s \
      OUT=$C1/logs/$tag.sol timeout 900 nice -n 15 ./lift3 $Q > $C1/logs/$tag.out 2> $C1/logs/$tag.err
    echo "$tag $(cat $C1/logs/$tag.out)"
  done
done
