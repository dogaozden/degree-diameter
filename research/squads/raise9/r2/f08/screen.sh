#!/bin/bash
# usage: screen.sh LINEFILE SAMPLES  ; each line: N name p k r (name: sl5 | m73 | m133 | m193 | F21_7 | F39_13 | F57_19)
B=/home/user/degree-diameter/research/squads/raise9/bin
cd /home/user/degree-diameter/research/squads/raise9/r2/f08
while read N name p k r; do
  case $name in
    sl5) G="prod sl 5 meta $p $k $r";;
    m73) G="prod meta 7 3 2 meta $p $k $r";;
    m133) G="prod meta 13 3 3 meta $p $k $r";;
    m193) G="prod meta 19 3 7 meta $p $k $r";;
    F21_7) G="prod meta 7 3 2 meta $p $k $r";;
    F39_13) G="prod meta 13 3 3 meta $p $k $r";;
    F57_19) G="prod meta 19 3 7 meta $p $k $r";;
  esac
  RANDSAMPLE=$2 THREADS=1 timeout 100 nice -n 10 $B/haar_gen3s 6 9 100 1 8 /dev/null $G 1 2>&1 | grep RANDSAMPLE | sed "s/^/$N $name $p $k $r : /"
done < $1
