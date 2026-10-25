#!/bin/bash
C=/home/user/degree-diameter/research/squads/hexfam_r3/c4
R=/home/user/degree-diameter/research/squads/hexfam_r2/c4
cd $C
./runone2.sh t_E7A2p3_s1 $R/A_E7_A2p3_792.txt 1 170
./runone2.sh t_E6A3A1A1_s1 $R/A_E6_A3A1A1_792.txt 1 170
./runone2.sh t_E6D5_s1 $R/A_E6_D5_792.txt 1 170
./runone2.sh t_E7D5A1_s1 $R/A_E7_D5A1_792.txt 1 170
echo BATCH2_DONE
