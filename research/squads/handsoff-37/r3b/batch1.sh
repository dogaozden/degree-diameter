#!/bin/bash
# r3b batch: several symmetric groups, each symbo run in sequence (one heavy process at a time)
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
run() { # name M K ALPHA SIGA SIGB SECS SEED
  local name=$1 m=$2 k=$3 al=$4 sa=$5 sb=$6 secs=$7 seed=$8
  mkdir -p out/$name
  python3 mkgroup.py $m $k $al "$sa" "$sb" out/$name/grp.txt out/$name/start.txt $seed > out/$name/mk.log 2>&1 || { echo "mk fail $name"; return; }
  nice -n 10 timeout 100 ./symbo out/$name/grp.txt out/$name/start.txt $secs $seed out/$name/s$seed 40 10 0.7 1 1000000 0.5 2> out/$name/s$seed.log
  echo "$name $(head -1 out/$name/grp.txt) seed=$seed: $(tail -1 out/$name/s$seed.log)  $(../bin/score37 out/$name/s${seed}_best.edges | tail -1)"
}
F21_4=$(python3 -c "print('1,1,1,1,3,3,3')")
F21_10=$(python3 -c "print(','.join(['1']*10+['3']))")
D5_SIG=$(python3 -c "print(','.join(['2']*8+['1']))")
F20_SIG="4,4,2,2,2,2,1"
run f21_4fix_182 7 13 2 "$F21_4" "$F21_4" 70 1
run f21_10fix_182 7 13 2 "$F21_10" "$F21_10" 70 1
run d5_170 5 17 4 "$D5_SIG" "$D5_SIG" 70 1
run f20_170 5 17 2 "$F20_SIG" "$F20_SIG" 70 1
run d5_170b 5 17 4 "$D5_SIG" "$D5_SIG" 70 2
echo BATCH1_DONE
