#!/bin/bash
# usage: sweep2.sh q rmin iters seeds...  -- raises r until no seed reaches DIAMETER_OK (stops there), sequential
# GROUP="prod r 5" HSUB=5 MCONST=1 T="1 2" J=2 D=8 ; logs and OUT files go to c1/logs
Q=$1; RMIN=$2; IT=$3; shift 3
C1=/home/user/degree-diameter/research/squads/d10D8-r1/c1
cd /home/user/degree-diameter/research/d10D8/hex || exit 1
r=$RMIN
while [ $((5*r)) -le 64 ]; do
  m=$((5*r)); okany=0
  for s in "$@"; do
    tag=q${Q}_r${r}_m${m}_s${s}
    GROUP="prod $r 5" HSUB=5 MCONST=1 T="1 2" J=2 D=8 ITERS=$IT SEED=$s \
      OUT=$C1/logs/$tag.sol timeout 900 nice -n 15 ./lift3 $Q > $C1/logs/$tag.out 2> $C1/logs/$tag.err
    res=$(cat $C1/logs/$tag.out); echo "$tag $res"
    if echo "$res" | grep -q DIAMETER_OK; then okany=1; fi
  done
  if [ $okany -eq 0 ]; then echo "STOP q=$Q: no seed valid at r=$r (m=$m)"; break; fi
  r=$((r+1))
done
echo "SWEEP_DONE q=$Q"
