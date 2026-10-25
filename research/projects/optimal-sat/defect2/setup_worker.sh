#!/bin/bash
# One-time setup for a cloud worker (about 5 minutes): solvers, checker, python-sat, base CNF and cube list.
# usage: bash setup_worker.sh workdir
set -e
W=$1; mkdir -p $W; cd $W
pip install python-sat > /dev/null 2>&1
[ -x cadical/build/cadical ] || (git clone -q --depth 1 https://github.com/arminbiere/cadical.git && cd cadical && ./configure > /dev/null && make -j4 > /dev/null)
[ -x drat-trim/lrat-check ] || (git clone -q --depth 1 https://github.com/marijnheule/drat-trim.git && cd drat-trim && gcc -O2 -o lrat-check lrat-check.c 2> /dev/null)
D=$(cd "$(dirname "$0")" && pwd)
[ -f abbase11.cnf ] || python3 $D/abcube.py base 11 abbase11.cnf
[ -f ab11.txt ] || python3 $D/ablist.py ab11.txt
echo "setup done in $W: $(wc -l < ab11.txt) cubes"
