#!/bin/bash
# Process the cubes i, i+n, i+2n, ... of ab11.txt with a certified run each (run_abcube.sh), J jobs in parallel.
# usage: bash worker.sh workdir i n [J]      (results: workdir/out/abcubes.log; unsolved cubes are the lines
#        without 'UNSATISFIABLE ... VERIFIED'; rerun them with a larger CUBE_TIMEOUT or split them further)
W=$1; i=$2; n=$3; J=${4:-4}
D=$(cd "$(dirname "$0")" && pwd)
export CADICAL=$W/cadical/build/cadical LRATCHECK=$W/drat-trim/lrat-check
awk -v i=$i -v n=$n 'NR % n == i % n' $W/ab11.txt | xargs -P $J -I{} bash $D/run_abcube.sh $W/abbase11.cnf {} $W/out > /dev/null
echo "worker $i/$n done: $(grep -c VERIFIED $W/out/abcubes.log) verified, $(grep -vc VERIFIED $W/out/abcubes.log) not"
