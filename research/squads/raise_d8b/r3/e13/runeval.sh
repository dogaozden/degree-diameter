#!/bin/bash
# name | sl|psl | p | n | ORBIT | d
E=/home/user/degree-diameter/research/squads/raise_d8b/r3/e13
BIN=/home/user/degree-diameter/research/frontier/raise_d8/bin
while IFS='|' read -r name fam p n orb d; do
  name=$(echo $name | xargs); fam=$(echo $fam | xargs); p=$(echo $p | xargs); n=$(echo $n | xargs); orb=$(echo $orb | xargs); d=$(echo $d | xargs)
  EVAL=$E/states/$name UNCPRINT=1 ORBIT="$orb" THREADS=1 OMP_NUM_THREADS=1 nice -n 10 $BIN/haar_big0 $d 8 1 1 8 $E/unused.sol $fam $p $n > $E/eval_$name.txt 2> $E/eval_$name.err
  echo "done $name rc=$?" >> $E/evalrun.log
done <<'LIST'
d01_a.sol.best | sl | 41 | 311 | 5 3 2 | 17
d02_start.sol.best | psl | 89 | 61 | 5 3 2 | 17
d05_a.sol.best | sl | 31 | 1091 | 5 3 3 | 18
d06_d06.sol.best | psl | 97 | 71 | 7 2 4 | 18
d07_a.sol.best | psl | 131 | 41 | 5 3 4 | 19
d09_a.sol.best | psl | 89 | 131 | 5 3 4 | 19
d10_a.sol.best | psl | 59 | 451 | 5 3 4 | 19
d11_a.sol.best.orb | sl | 79 | 131 | 5 4 0 | 20
d12_a.sol.best.orb | psl | 61 | 571 | 5 4 0 | 20
d13_a.sol.best.orb | psl | 109 | 101 | 5 4 0 | 20
LIST
echo ALLDONE >> $E/evalrun.log
