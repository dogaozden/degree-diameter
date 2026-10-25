#!/bin/bash
cd /home/user/degree-diameter/research/squads/d16D7_r2/c8
S=/home/user/degree-diameter/research/squads/d16D7_r2/run_slot.sh
$S ./wsa wg_sp.txt hsig_sp.sol 90 31 4 0.15 4000000 > hsig_sp.log 2>&1; echo "sp rc=$?" >> hsig_sp.log
$S ./wsa wg_pt.txt hsig_pt.sol 90 32 4 0.15 4000000 > hsig_pt.log 2>&1; echo "pt rc=$?" >> hsig_pt.log
echo chain3-done >> hsig_pt.log
