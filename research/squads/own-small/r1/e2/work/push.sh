#!/bin/bash
E=/home/user/degree-diameter/research/squads/own-small/r1/e2; F=/home/user/degree-diameter/research/squads/own-small/tools/bin/flift
$F $E/bases/CAT_8.txt $E/groups/g68_0001.bin 3 9 80 7 8 $E/runs/push_cube_g68_1 | grep RESULT
$F $E/bases/CAT_6.txt $E/groups/g90_0007.bin 3 9 80 7 8 $E/runs/push_k33_g90_7 | grep RESULT
$F $E/bases/CAT_8.txt $E/groups/g68_0002.bin 3 9 80 7 8 $E/runs/push_cube_g68_2 | grep RESULT
