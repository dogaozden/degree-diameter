#!/bin/bash
cd /home/user/degree-diameter/research/frontier/raise_small
tools/scanlift.sh 11 3 runs/g11_p3_odd.txt 20 runs/S11p3 "1 2"
tools/scanlift.sh 11 4 runs/g11_p4_odd.txt 20 runs/S11p4 "1 2"
tools/scanlift.sh 11 2 runs/g11_p2_odd.txt 20 runs/S11p2 "1 2"
