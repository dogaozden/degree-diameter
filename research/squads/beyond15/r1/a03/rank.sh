#!/bin/bash
cd /home/user/degree-diameter/research/squads/beyond15/r1/a03/rank
L=/home/user/degree-diameter/research/frontier/bin/lift
D=15
run() { # name base n
  THREADS=1 timeout 100 nice -n 10 $L $2 $3 $D 35 7 $1 2.0 0.05 1200 > $1.log 2>&1
  echo "$1 n=$3 $(grep -i result $1.log | tail -1)" >> summary.txt
}
run gp8_3 /home/user/degree-diameter/research/frontier/beyond13/lifts/bases/gp8_3.txt 656
run gp12_5 /home/user/degree-diameter/research/frontier/beyond13/lifts/bases/gp12_5.txt 437
run gp16_5 /home/user/degree-diameter/research/frontier/beyond13/lifts/bases/gp16_5.txt 328
run gp24_5 /home/user/degree-diameter/research/frontier/beyond13/lifts/bases/gp24_5.txt 218
run tutte8 /home/user/degree-diameter/research/squads/beyond15/r1/a03/tutte8.txt 350
run pappus18 /home/user/degree-diameter/research/frontier/beyond13/lifts/bases/pappus18.txt 583
run heawood /home/user/degree-diameter/research/frontier/beyond13/lifts/bases/heawood.txt 750
run gp14_3 /home/user/degree-diameter/research/frontier/beyond13/lifts/bases/gp14_3.txt 375
run gp20_3 /home/user/degree-diameter/research/frontier/beyond13/lifts/bases/gp20_3.txt 262
run gp30_7 /home/user/degree-diameter/research/frontier/beyond13/lifts/bases/gp30_7.txt 175
echo DONE >> summary.txt
