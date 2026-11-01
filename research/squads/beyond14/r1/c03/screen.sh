#!/bin/bash
# usage: screen.sh SECS NAME... ; runs liftg on Pappus base for each group, appends summary to runs/screen.txt
BASE=/home/user/degree-diameter/research/frontier/beyond14/bases/pappus_j13.txt
S=$1; shift
cd /home/user/degree-diameter/research/squads/beyond14/r1/c03
for g in "$@"; do
  r=$(./liftg $BASE groups/$g.grp 14 $S 7 runs/s_$g 2 0.2 500 2>/dev/null | grep RESULT)
  echo "$g $r" >> runs/screen.txt
done
