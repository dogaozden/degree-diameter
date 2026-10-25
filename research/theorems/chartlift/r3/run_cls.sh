#!/bin/bash
# usage: r3/run_cls.sh CLASS GROUPNAME ORDERTAG SECONDS  (Haar k=4 base, flags r3/k4q3_diag_cls<CLASS>.flags)
c=$1; g=$2; t=$3; s=$4; W=/tmp/claude-0/-home-user-degree-diameter/8e7a80fa-6b09-58cb-8199-8d05845bbe55/scratchpad/w
timeout $((s+30)) nice -n 5 $W/ctrl_search bases4/k4r1_000.txt r3/gtab/$g.txt r3/k4q3_diag_cls$c.flags $s 1 r3/runs_cls/cls${c}_${t}_$g > r3/runs_cls/cls${c}_${t}_$g.out 2>&1
echo "cls$c $t $g $(tail -n 1 r3/runs_cls/cls${c}_${t}_$g.out | cut -c1-80)"
