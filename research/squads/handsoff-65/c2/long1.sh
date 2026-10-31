#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-65/c2
run() { name=$1; base=$2; grp=$3; seed=$4
  SECS=540 SEED=$seed INIT=random nice -n 10 timeout 600 ../shared/tabu $base $grp long/$name.edges 2> long/$name.err | grep RESULT | sed "s/^/$name /" >> long/results.txt
}
run p3_116_C29C4 bases/p3_full_101.base groups/sg_116_2.txt 1
run p3_120_sg14 bases/p3_full_305.base groups/sg_120_14.txt 1
run p4_88_C11C8 bases/p4_full_403.base groups/sg_88_1.txt 1
echo LONGDONE
