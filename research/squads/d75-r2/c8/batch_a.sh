#!/bin/bash
D=/home/user/degree-diameter/research/squads/d75-r2/c8
A="Read(\"$D/ids_a.g\");;"
$D/run_c8.sh a_664_1 "$A G:=mkMeta(83,2,4)"
$D/run_c8.sh a_666_1 "$A G:=mkMeta(37,6,3)"
$D/run_c8.sh a_668_1 "$A G:=mkMeta(167,2,2)"
$D/run_c8.sh a_678_2 "$A G:=mkMeta(113,2,3)"
$D/run_c8.sh a_711_1 "$A G:=mkMeta(79,3,3)"
$D/run_c8.sh a_712_1 "$A G:=mkMeta(89,2,4)"
$D/run_c8.sh a_716_1 "$A G:=mkMeta(179,2,2)"
echo BATCH_A_DONE >> $D/logs/summary.txt
