#!/bin/bash
# c3 warm-start chain: VALID Z_m design -> same voltages in Z_(m+1) -> active-set repair (symrepair_act)
cd /home/user/degree-diameter/research/squads/d16D8-r3/c3
prev=m17.base; last=17
for m in 18 19 20; do
  sed "1s/^\([0-9]*\) [0-9]* \([0-9]*\)$/\1 $m \2/" $prev > w$m.base
  SRCFILE=r_m16.src NSRC=200 EPOCH=200 K=1 THREADS=1 timeout 1500 nice -n 10 ./symrepair_act w$m.base 8 120 $m m$m.base > m$m.log 2> m$m.err
  if grep -q "RESULT.*best=0 " m$m.log; then echo "m=$m VALID(orbit sources): $(cat m$m.log)"; prev=m$m.base; last=$m;
  else echo "m=$m not repaired: $(cat m$m.log)"; tail -n 3 m$m.err; break; fi
done
echo "last=$last"
