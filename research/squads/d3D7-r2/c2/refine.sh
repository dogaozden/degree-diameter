#!/bin/bash
R=/home/user/degree-diameter
GA=$R/research/squads/d3D7-r1/c9/ga
C=$R/research/squads/d3D7-r2/c2
cd $C
timeout 900 nice -n 10 $GA 6 $R/research/d3D7/groups/g16.txt 1 2 120 30 $C/ref_g16_1_s2.sol > $C/ref_g16_1_s2.log 2>&1
timeout 900 nice -n 10 $GA 6 $R/research/d3D7/groups/g16.txt 5 2 120 30 $C/ref_g16_5_s2.sol > $C/ref_g16_5_s2.log 2>&1
echo DONE
