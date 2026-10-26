#!/bin/bash
# c12 batch 1: generate group tables and run the Haar local search (one process at a time, 1 thread)
cd /home/user/degree-diameter/research/squads/beyond/r1/c12
G=/home/user/degree-diameter/research/squads/b48/tools/groups.py
gen() { f=tables/$(echo "$1" | tr ' ' '_').bin; [ -s "$f" ] || timeout 900 nice -n 10 python3 $G "$1" "$f" > logs/gen_$(echo "$1" | tr ' ' '_').log 2>&1; }
run() { t=$1; secs=$2; seed=$3; timeout 900 nice -n 10 ./hsearch tables/$t.bin 12 $secs $seed graphs/${t}_seed$seed.edges > logs/search_${t}_seed$seed.log 2>&1; echo "$t seed$seed exit $?" >> logs/batch1_status.txt; }
gen "psl2 13"; gen "pgl2 11"; gen "sl2 11"; gen "agl1 41"; gen "agl1 37"; gen "psl2 17"; gen "pgl2 13"
run psl2_13 300 2
run pgl2_11 150 1
run sl2_11 150 1
run agl1_41 150 1
run agl1_37 100 1
run psl2_17 600 1
run pgl2_13 600 1
echo BATCH1_DONE >> logs/batch1_status.txt
