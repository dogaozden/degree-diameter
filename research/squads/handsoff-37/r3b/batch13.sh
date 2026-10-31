#!/bin/bash
# r3b batch13: D5 at n=170 (alpha 4, sigma 2^8 1 both sides) with high voltage-move probability PV 0.8 / 0.95, seeds 10-13, 90 s
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
mkdir -p out/b13
D5_SIG=$(python3 -c "print(','.join(['2']*8+['1']))")
for cfg in "10 0.8" "11 0.8" "12 0.95" "13 0.8"; do
  set -- $cfg; seed=$1; pv=$2
  timeout 100 nice -n 10 ./symbo out/b10/d5_170c/grp.txt out/b10/d5_170c/start.txt 90 $seed out/b13/d5_s${seed}_pv$pv 40 10 0.7 1 1000000 $pv 2> out/b13/d5_s${seed}_pv$pv.log
  echo "D5 170 seed=$seed PV=$pv: $(tail -1 out/b13/d5_s${seed}_pv$pv.log) $(../bin/score37 out/b13/d5_s${seed}_pv${pv}_best.edges | tail -1)"
done
echo BATCH13_DONE
