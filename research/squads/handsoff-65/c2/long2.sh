#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-65/c2
run() { name=$1; base=$2; grp=$3; seed=$4
  SECS=540 SEED=$seed INIT=random nice -n 10 timeout 600 ../shared/tabu $base $grp long/$name.edges 2> long/$name.err | grep RESULT | sed "s/^/$name /" >> long/results.txt
}
run cls17_C29C4_s2 bases/class3_17.base groups/sg_116_1.txt 2
run cls17_C116_s3 bases/class3_17.base groups/sg_116_2.txt 3
echo LONG2DONE
