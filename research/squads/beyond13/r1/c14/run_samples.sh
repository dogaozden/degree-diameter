#!/bin/bash
# RANDORB cost statistics + hole dumps for random symmetric S at (d,D)=(5,13)
C=/home/user/degree-diameter/research/squads/beyond13/r1/c14
cd $C
mkdir -p holes
for g in "sl 61 7" "sl 113 1" "sl 37 31" "sl 53 13" "sl 29 97" "psl 151 1" "psl 79 7" "psl 47 31" "psl 31 97" "psl 67 13"; do
  set -- $g
  tag="$1_$2_$3"
  rm -f holes/$tag.txt
  ORBIT="3 1 2" THREADS=1 RANDORB=300 HOLESFILE=$C/holes/$tag.txt nice -n 10 timeout 900 $C/anat 5 13 0 1 8 /dev/null $1 $2 $3 > stats_$tag.txt 2> log_$tag.txt
done
echo done > ALLDONE
