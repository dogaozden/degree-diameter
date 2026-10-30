#!/bin/bash
# Runs every construction file and every comparison script, saving the real output in logs/.
# Usage:  SAGE=/path/to/sage ./run_all.sh [quick]      (default SAGE=sage; "quick" skips the slowest runs)
cd "$(dirname "$0")"
SAGE=${SAGE:-sage}
mkdir -p logs
run() { name=$1; shift; echo "== $name"; "$@" > "logs/$name.log" 2>&1; echo "   exit $?"; }
run d3_check          $SAGE d3_four_hats.sage
run d3_16_check       $SAGE d3_16_three_gadgets.sage
run d4_theoremA_check $SAGE d4_theoremA_ASq.sage
run d4_propC_check    $SAGE d4_propC_Wq.sage
run d4_7_4_check      $SAGE d4_7_4_359_Q45.sage
run d5_haar_check     $SAGE d5_haar_7_5_1200.sage
run d5_lift360_check  $SAGE d5_lift_5_5_360.sage
run d5_lift384_check  $SAGE d5_lift_5_5_384.sage
run d6_check          $SAGE d6_theoremD_hexagon_doubling.sage
run d4_q7_check       $SAGE -c 'NO_AUTO_CHECK=True
load("d4_theoremA_ASq.sage"); check(7); load("d4_propC_Wq.sage"); check(7)'
run d6_q4_check       $SAGE -c 'NO_AUTO_CHECK=True
load("d6_theoremD_hexagon_doubling.sage"); assert check(4, 2, regular=False)'
run hexagon_selftest  $SAGE hexagon.sage
run d7_check          $SAGE d7_hexagon_copies_hubs.sage
run d8_check          $SAGE d8_gomez_omegaH.sage
for f in compare/compare_d*.sage; do run "$(basename $f .sage)" $SAGE $f; done
