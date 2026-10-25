#!/bin/bash
cd /home/user/degree-diameter/research/squads/d16D7_r2/c8
S=/home/user/degree-diameter/research/squads/d16D7_r2/run_slot.sh
$S ./wsa wgs_sp.txt wgs_sp_1.sol 120 21 4 0.15 3000000 > wgs_sp.log 2>&1; echo "sp rc=$?" >> wgs_sp.log
$S ./wsa wgs_pt.txt wgs_pt_1.sol 120 22 4 0.15 3000000 > wgs_pt.log 2>&1; echo "pt rc=$?" >> wgs_pt.log
echo chain2-done >> wgs_pt.log
