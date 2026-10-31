#!/bin/bash
# c7 screen: export each non-solvable group of order 1519-1700 (SmallGroups library) and run sdtabu2 on K=9.
D=/home/user/degree-diameter/research/squads/sd5b-r1/c7
export TMPDIR=$D/tmp
T=/home/user/degree-diameter/research/selfdual-d5/src
for pair in "$@"; do
  N=${pair%% *}; ID=${pair##* }; tag=g${N}_${ID}
  timeout 900 nice -n 15 gap -q -o 1500m -c "N:=$N;; ID:=$ID;; NOEXT:=1;; OUT:=\"$D/$tag.ht\";;" $T/export_sd.g < /dev/null > $D/$tag.exp.log 2>&1
  echo "EXPORT $tag rc $? records $(grep -c '^ALPHA' $D/$tag.ht)" >> $D/progress.log
  K=9 SECS=3 NB=48 STALL=1000 TYPES=1,3,5 NOID=1 SEED=1 EDGES=$D/$tag.sol.edges \
    timeout 900 nice -n 15 $T/sdtabu2 $D/$tag.ht all > $D/$tag.out 2>&1
  echo "SDTABU $tag rc $? $(grep -c '^TABU' $D/$tag.out) lines; best: $(grep '^TABU' $D/$tag.out | awk '{for(i=1;i<=NF;i++) if($i=="best") print $(i+1)}' | sort -n | head -1)" >> $D/progress.log
done
echo ALLDONE >> $D/progress.log
