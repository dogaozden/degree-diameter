#!/bin/bash
# after the group screen: ILS on K44 with several groups of order 622..625, then ILS on PG(2,3) with the best groups
cd /home/user/degree-diameter/research/squads/handsoff-49/w4
while ! grep -q DONE run_groups.log; do sleep 5; done
for spec in "k44.txt groups/k_cyc_622.bin" ; do :; done
ILS=1 nice -n 10 ./hgi k44.txt cyc:622 120 21 1 1 ils_k44_z622 2>&1 | grep -E "ILS sweeps|RESULT" | sed 's/^/K44 Z622 /'
ILS=1 nice -n 10 ./hgi k44.txt groups/k_dih_311.bin 120 22 1 1 ils_k44_d311 2>&1 | grep -E "ILS sweeps|RESULT" | sed 's/^/K44 D311 /'
ILS=1 nice -n 10 ./hgi k44.txt groups/k_cyc_624.bin 120 23 1 1 ils_k44_z624 2>&1 | grep -E "ILS sweeps|RESULT" | sed 's/^/K44 Z624 /'
ILS=1 nice -n 10 ./hgi k44.txt groups/k_meta_13_48_5.bin 120 24 1 1 ils_k44_m624 2>&1 | grep -E "ILS sweeps|RESULT" | sed 's/^/K44 M624 /'
ILS=1 nice -n 10 ./hgi pg23.txt cyc:192 120 25 1 1 ils_pg_z192 2>&1 | grep -E "ILS sweeps|RESULT" | sed 's/^/PG Z192 /'
ILS=1 nice -n 10 ./hgi pg23.txt groups/g2.bin 120 26 1 1 ils_pg_g2 2>&1 | grep -E "ILS sweeps|RESULT" | sed 's/^/PG g2 /'
echo DONE_ILS1
