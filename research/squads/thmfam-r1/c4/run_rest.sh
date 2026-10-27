#!/bin/bash
cd /home/user/degree-diameter/research/squads/thmfam-r1/c4
for m in 31 37; do nice -n 10 timeout 900 python3 screen.py $m 23 m${m}_s23.jsonl --sample 200 --seed 1; done
python3 rescore.py m31_s23.jsonl 15 23,31,41 m31_top.jsonl > rescore31.txt 2>&1
python3 rescore.py m37_s23.jsonl 15 23,31,41 m37_top.jsonl > rescore37.txt 2>&1
python3 rescore.py m19_s23.jsonl 0 23 /dev/null >/dev/null 2>&1
echo DONE > run_rest.done
