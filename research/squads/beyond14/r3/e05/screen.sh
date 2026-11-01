#!/bin/bash
# screen.sh LISTFILE FROM TO SECS SEED: hmeta screen of lines FROM..TO (N m k r), appends to screen.txt
H=/home/user/degree-diameter/research/frontier/beyond14/bin/hmeta
cd /home/user/degree-diameter/research/squads/beyond14/r3/e05
mkdir -p scr
sed -n "$2,$3p" "$1" | while read N m k r f; do
  out=scr/m${m}_k${k}_s$5.sol
  res=$(T0=8 T1=1 REHEAT=400 timeout 105 nice -n 10 env THREADS=1 $H 4 14 $4 $5 16 $out $m $k $r 2>scr/err_m${m}_k${k}.txt | grep RESULT)
  echo "$N $m $k $r | $res" | tee -a screen.txt
done
