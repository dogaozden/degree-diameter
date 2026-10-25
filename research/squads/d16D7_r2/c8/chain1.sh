#!/bin/bash
# quotient ILS runs (heavy) through the shared slots, one per graph
cd /home/user/degree-diameter/research/squads/d16D7_r2/c8
S=/home/user/degree-diameter/research/squads/d16D7_r2/run_slot.sh
$S ./ils quot2_sp.txt q2sp.sol 330 11 - > q2sp.log 2>&1; echo "sp rc=$?" >> q2sp.log
$S ./ils quot2_pt.txt q2pt.sol 330 12 - > q2pt.log 2>&1; echo "pt rc=$?" >> q2pt.log
echo chain-done >> q2pt.log
