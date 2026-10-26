#!/bin/bash
# d08 batch: flift voltage lifts of small bipartite cubic bases over small groups, D = 12, one process at a time
cd /home/user/degree-diameter/research/squads/beyond/r2/d08
B=/home/user/degree-diameter/research/squads/b48/tools/bases/cubic
G=/home/user/degree-diameter/research/squads/b48/tools/groups.py
mk() { f=$1.bin; [ -s "$f" ] || timeout 900 nice -n 10 python3 $G "$2" "$f" > logs/gen_$1.log 2>&1; }
run() { base=$1; grp=$2; secs=$3; seed=$4; timeout 900 nice -n 10 ./flift $B/$base.txt $grp 3 12 $secs $seed 8 out/${base}_${grp%.bin}_s$seed.sol > logs/${base}_${grp%.bin}_s$seed.log 2>&1; echo "$base $grp seed$seed exit $? $(tail -1 logs/${base}_${grp%.bin}_s$seed.log)" >> logs/status.txt; }
mk pgl2_7 "pgl2 7"; mk sl2_7 "sl2 7"
run heawood psl2_7.bin 60 4
run desargues psl2_7.bin 60 1
run moebius_kantor psl2_7.bin 60 1
run pappus psl2_7.bin 60 1
run heawood pgl2_7.bin 60 1
run k33 pgl2_7.bin 60 1
run b22_cubic sl2_7.bin 60 1
run b22_cubic pgl2_7.bin 60 1
echo BATCH_DONE >> logs/status.txt
