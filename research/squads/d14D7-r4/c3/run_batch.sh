#!/bin/bash
# run_batch.sh SECONDS SEED name...: orbitclique on perms/NAME.txt, flags to flags/NAME_sSEED.txt, then CHECKONLY score
S=$1; SEED=$2; shift 2
C=/home/user/degree-diameter/research/squads/d14D7-r4/c3
for nm in "$@"; do
  /home/user/degree-diameter/research/squads/bin/heavy.sh $((S+60)) env THREADS=1 /home/user/degree-diameter/research/cell147/units/orbitclique \
     /home/user/degree-diameter/research/cell147/data/E11.map $C/perms/$nm.txt $S $SEED $C/flags/${nm}_s$SEED.txt > $C/logs/${nm}_s$SEED.log 2>&1
  rc=$?
  sc=$(cd $C && CHECKONLY=1 /home/user/degree-diameter/research/cell147/units/pack /home/user/degree-diameter/research/cell147/data/gh_11.txt 0 1 /dev/null $C/flags/${nm}_s$SEED.txt 2>&1 | tail -1)
  echo "$nm seed$SEED rc=$rc :: $sc :: $(tail -1 $C/logs/${nm}_s$SEED.log)"
done
