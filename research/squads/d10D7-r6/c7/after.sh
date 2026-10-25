#!/bin/bash
# wait for the subsystem job (PID 16760), then count free points of the 756 set and run tabu extension from it
cd /home/user/degree-diameter/research/squads/d10D7-r6/c7
while kill -0 16760 2>/dev/null; do sleep 5; done
echo "subsystem job done $(date -u +%T)"
timeout 600 nice -n 10 python3 free11.py best_756.txt
./tabu_run.sh best_756.txt 1 420 tabu756_s1.txt
echo "tabu done $(date -u +%T)"
[ -f tabu756_s1.txt ] && ./check_all.sh tabu756_s1.txt
