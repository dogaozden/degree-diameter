#!/bin/bash
# build (file a b) triples: untried files, not in round-3 pass1
cd /home/user/degree-diameter/research/squads/s65r4/c6
grep -v -x -F -f done_files.txt files_all.txt | shuf --random-source=<(yes 65) > untried_shuf.txt
# (3,3) for first 90, (4,2) for next 45, (2,4) for next 45 (distinct files)
head -90 untried_shuf.txt | sed 's/$/ 3 3/' > triples1.txt
sed -n '91,135p' untried_shuf.txt | sed 's/$/ 4 2/' >> triples1.txt
sed -n '136,180p' untried_shuf.txt | sed 's/$/ 2 4/' >> triples1.txt
wc -l triples1.txt
