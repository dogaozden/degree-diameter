#!/bin/bash
# sequential tabu runs, one process at a time
cd /home/user/degree-diameter/research/squads/gqd5-r2/c2
for s in "$@"; do
  timeout 900 nice -n 10 ./ktabu graph.txt sline.txt $s 400 kt_s$s.txt - > log_kt_s$s.txt 2>&1
done
echo done > tabu_done.flag
