#!/bin/bash
# r3b batch10: fresh SAT starts. F21 at 196 (M 7, K 14, alpha 2, sigma 1,1,3,3,3,3 both sides; seeds 7, 8),
# F21 at 182 (seed 9, PV 0.8, K 80), D5 at 170 (PV 0.8, seed 9). symbo, 90 s each.
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
mkdir -p out/b10
run() { # tag M K ALPHA SIGA SIGB seed secs K PV
  local tag=$1 m=$2 k=$3 al=$4 sa=$5 sb=$6 seed=$7 secs=$8 kk=$9 pv=${10}
  mkdir -p out/b10/$tag
  python3 mkgroup.py $m $k $al "$sa" "$sb" out/b10/$tag/grp.txt out/b10/$tag/start.txt $seed > out/b10/$tag/mk.log 2>&1 || { echo "mk fail $tag"; return; }
  timeout 100 nice -n 10 ./symbo out/b10/$tag/grp.txt out/b10/$tag/start.txt $secs $seed out/b10/$tag/s$seed $kk 10 0.7 1 1000000 $pv 2> out/b10/$tag/s$seed.log
  echo "$tag n=$((2*k*m)) $(head -1 out/b10/$tag/grp.txt) seed=$seed K=$kk PV=$pv: $(tail -1 out/b10/$tag/s$seed.log) $(../bin/score37 out/b10/$tag/s${seed}_best.edges | tail -1)"
}
run f21_196 7 14 2 "1,1,3,3,3,3" "1,1,3,3,3,3" 7 90 40 0.5
run f21_196b 7 14 2 "1,1,3,3,3,3" "1,1,3,3,3,3" 8 90 40 0.5
D5_SIG=$(python3 -c "print(','.join(['2']*8+['1']))")
run f21_182c 7 13 2 "1,3,3,3,3" "3,3,3,3,1" 9 90 80 0.8
run d5_170c 5 17 4 "$D5_SIG" "$D5_SIG" 9 90 40 0.8
echo BATCH10_DONE
