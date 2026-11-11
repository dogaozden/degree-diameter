#!/bin/bash
# long ILS runs on the two best bases (sequential, one heavy process at a time)
cd /home/user/degree-diameter/research/squads/handsoff-49/w4
ILS=1 nice -n 10 ./hgi k44.txt cyc:622 420 41 1 1 long_k44_z622_s41 > long_k44_s41.log 2>&1
echo "K44 Z622 s41 $(grep RESULT long_k44_s41.log)" >> run_long.log
ILS=1 nice -n 10 ./hgi pg23.txt cyc:192 420 42 1 1 long_pg_z192_s42 > long_pg_s42.log 2>&1
echo "PG Z192 s42 $(grep RESULT long_pg_s42.log)" >> run_long.log
echo DONE_LONG >> run_long.log
