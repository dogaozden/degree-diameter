#!/bin/bash
# deep.sh TABLE REP COMP SECS SEEDS...   : SA with several seeds on one (table, H rep, composition); prints best C
cd /home/user/degree-diameter/research/squads/handsoff-49/w7
TAB=$1; REP=$2; COMP=$3; SECS=$4; shift 4
for s in "$@"; do
  OUT=tabs/deep_$(basename $TAB .bin)_${REP}_$(echo $COMP | tr -d ,)_s$s.edges
  nice -n 10 timeout 540 ./bicos $TAB sa $REP $COMP $SECS $s $OUT | grep "SA best C" | sed "s/^/seed $s: /"
done
