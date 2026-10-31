#!/bin/bash
# r3b batch9: parameter variants of symbo on F20 at n=170 (sigma 4,4,2,2,2,2,1), 90 s each, start = the seed-1 SAT start
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
mkdir -p out/b9
run() { # tag K PV PF TEN seed
  local tag=$1 k=$2 pv=$3 pf=$4 ten=$5 seed=$6
  timeout 100 nice -n 10 ./symbo out/f20_170/grp.txt out/f20_170/start.txt 90 $seed out/b9/$tag 40 $ten $pf 1 1000000 $pv 2> out/b9/$tag.log
  echo "$tag K=$k PV=$pv PF=$pf TEN=$ten seed=$seed: $(tail -1 out/b9/$tag.log) $(../bin/score37 out/b9/${tag}_best.edges | tail -1)"
}
run pv08_s31 40 0.8 0.7 10 31
run pv02_s32 40 0.2 0.7 10 32
run pf03_s33 40 0.5 0.3 10 33
run ten30_s34 40 0.5 0.7 30 34
echo BATCH9_DONE
