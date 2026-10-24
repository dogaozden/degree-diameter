#!/bin/bash
# usage: run.sh <q> <group> <iters> <src> <seed> [VAR=val ...]   (group = name in groups/, file written by gen_groups.py)
# Runs lift3 from research/d10D8/hex (it reads hex/hex_q<q>.bin relative to cwd), one process, nice 15, 900 s cap.
q=$1; g=$2; it=$3; src=$4; seed=$5; shift 5
C3=/home/user/degree-diameter/research/squads/d10D8-r1/c3
tag=$(echo "$*" | tr ' =/"' '____' | cut -c1-60)
base=$C3/runs/q${q}_${g}_it${it}_src${src}_s${seed}_${tag}
cd /home/user/degree-diameter/research/d10D8/hex || exit 1
env GROUP="file $C3/groups/$g.txt" J=2 D=8 ITERS=$it SRC=$src SEED=$seed OUT=$base.sol "$@" \
  timeout 900 nice -n 15 ./lift3 $q > $base.log 2>&1
grep -h RESULT $base.log || tail -n 2 $base.log
