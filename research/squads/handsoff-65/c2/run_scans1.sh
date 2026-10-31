#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-65/c2
python3 scan.py 3 full 300 8 scan_p3_m120.tsv groups/sg_120_*.txt
python3 scan.py 4 full 400 15 scan_p4_m86_90.tsv groups/sg_86_*.txt groups/sg_87_*.txt groups/sg_88_*.txt groups/sg_89_*.txt groups/sg_90_*.txt
python3 scan.py 5 full 500 10 scan_p5_m69_71.tsv groups/sg_69_*.txt groups/sg_70_*.txt groups/sg_71_*.txt
echo ALLDONE
