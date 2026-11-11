#!/bin/bash
# waits for the families2 runner to finish, then runs the K tail sample (A-root only, 800 members, seed 108668)
cd /home/user/degree-diameter/research/squads/handsoff-108/c5b-cosetscreen
while pgrep -f "[r]un_families.sh families2" >/dev/null; do sleep 15; done
AONLY=1 SPLIT=0 SDET=1 DEG=10 TT=8 timeout 3600 nice -n 10 ./cscreen2 229 1 D 10 10 800 108668 > out/K3_psl229_D5_10_tail.out 2> out/K3_psl229_D5_10_tail.err
echo "K3_psl229_D5_10_tail done $(date -u +%H:%M:%S) rc=$?" >> out/progress.log
