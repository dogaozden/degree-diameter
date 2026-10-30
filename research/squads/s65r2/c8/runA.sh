#!/bin/bash
cd /home/user/degree-diameter/research/squads/s65r2/c8
M=/home/user/degree-diameter/research/s65/groups/mc; T=/home/user/degree-diameter/research/s65/tools
run() { # name group type extra...
  name=$1; grp=$2; typ=$3; shift 3
  env TYPE="$typ" SECS=8 SEED=1 EDGES=edges/$name.edges "$@" timeout 600 nice -n 10 $T/mcos $grp > logs/$name.log 2>&1
  echo "== $name: $(grep -E '^COMB|^SOL|^RESULT' logs/$name.log | tr '\n' ' ')"
}
run A_354_1  $M/sg_354_1.txt  "1|2,2" RANDCOMB=4
run A_360_123 $M/sg_360_123.txt "1|2,2" RANDCOMB=4
run A_360_124 $M/sg_360_124.txt "1|2,2" RANDCOMB=4
run A_360_125 $M/sg_360_125.txt "1|2,2" RANDCOMB=4
run A_360_135 $M/sg_360_135.txt "1|2,2" RANDCOMB=4
run A_360_136 $M/sg_360_136.txt "1|2,2" RANDCOMB=4
run A_360_138 $M/sg_360_138.txt "1|2,2" RANDCOMB=4
run H_354_1  $M/sg_354_1.txt  "1|1"
run H_360_123 $M/sg_360_123.txt "1|1"
run H_360_138 $M/sg_360_138.txt "1|1"
