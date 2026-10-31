#!/bin/bash
# c3 driver: sequential sdhi runs over direct products Q x H at (K,D) = (5,8), one process at a time.
S=/home/user/degree-diameter/research/selfdual-hi/src
L=/home/user/degree-diameter/research/squads/sdhi-r1/c3/logs
run() { # name secs factors...
  local name=$1 secs=$2; shift 2
  env THREADS=1 SECS=$secs TYPES="1+2+2,1+1+1+2" timeout 600 nice -n 10 $S/sdhi 5 8 "$@" > $L/$name.txt 2>&1
  echo "done $name rc=$?" >> $L/progress.txt
}
run psl7_meta5_6_4  3 psl 7 meta 5 6 4
run psl7_meta3_10_2 3 psl 7 meta 3 10 2
run pgl5_meta7_6_2  3 pgl 5 meta 7 6 2
run sl5_meta41_2_40 3 sl 5 meta 41 2 40
run sl3_meta17_12_4 2 sl 3 meta 17 12 4
run pgl3_meta13_16_5 2 pgl 3 meta 13 16 5
run sl4_cyc83       2 sl 4 cyc 83
run sl4_meta3_28_2  2 sl 4 meta 3 28 2
run psl3_meta17_24_4 2 psl 3 meta 17 24 4
run sl7_cyc15       2 sl 7 cyc 15
run psl7_cyc30      2 psl 7 cyc 30
run pgl5_cyc42      3 pgl 5 cyc 42
run sl5_cyc41       3 sl 5 cyc 41
echo ALLDONE >> $L/progress.txt
