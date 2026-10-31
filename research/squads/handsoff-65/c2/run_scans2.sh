#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-65/c2
python3 scan.py 6 full 600 10 scan_p6_m58_60.tsv groups/sg_58_*.txt groups/sg_59_*.txt groups/sg_60_*.txt
python3 scan.py 7 kminus 700 10 scan_p7_m49_51.tsv groups/sg_49_*.txt groups/sg_50_*.txt groups/sg_51_*.txt
python3 scan.py 8 kminus 800 10 scan_p8_m43_45.tsv groups/sg_43_*.txt groups/sg_44_*.txt groups/sg_45_*.txt
python3 scan.py 5 full 900 8 scan_p5_m72.tsv groups/sg_72_*.txt
echo ALLDONE2
