#!/bin/sh
# Reproduce the card: orbit quotients, ILS (mis2 from r1/c12), expansion, independent check.
E=/home/user/degree-diameter/research/squads/polylev/r2/e07
H=/home/user/degree-diameter/research/theorems/polylev/hex/hex_q7.bin
cd /home/user/degree-diameter/research/theorems/polylev && python3 singer_perms.py $H 3 $E/S19_q7
cd $E && python3 code/quot.py $H /home/user/degree-diameter/research/theorems/polylev/grp/T_q7.pperm $E/T43
python3 code/quot.py $H $E/S19_q7.pperm $E/S19
timeout 300 nice -n 10 /home/user/degree-diameter/research/squads/polylev/r1/c12/mis2 $E/T43 90 1 $E/T43_ils1.txt
timeout 300 nice -n 10 /home/user/degree-diameter/research/squads/polylev/r1/c12/mis2 $E/S19 200 1 $E/S19_ils1.txt
python3 code/expand.py $E/T43 $E/T43_ils1.txt $E/best_T43_K1720_points.txt
python3 code/verify_points.py $E/best_T43_K1720_points.txt
