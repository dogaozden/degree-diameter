#!/bin/bash
cd /home/user/degree-diameter/research/d11D5/inc
SECS=400 SEED=1113 T0=3 T1=0.2 PF=0.2 PH=0.7 OUT=wq/run/W11M.in OUT0=wq/run/W11M0.in /tmp/po7 wq/run/W11L.in > wq/run/W11M.log 2>&1
[ -f wq/run/W11M0.in ] && cp wq/run/W11M0.in wq/run/W11M.in
c=$(SCORE=1 /tmp/po7 wq/run/W11M.in | tail -1 | grep -oE "cost=[0-9]+" | cut -d= -f2); echo "cold SA -> $c"
if [ "$c" != "0" ]; then
  [ "$c" -gt 40 ] && { echo "too high for wpo"; exit 1; }
  SECS=300 SEED=5 OUT=wq/run/W11w.in OUT0=wq/run/W11w0.in /tmp/wpo wq/run/W11M.in > wq/run/W11w.log 2>&1
  [ -f wq/run/W11w0.in ] || { echo "wpo did not reach 0"; exit 1; }
  cp wq/run/W11w0.in wq/run/W11M.in
fi
echo "structural 0"
TARGET=1 GCAP=40000000 WMAX=400000 SECS=300 SEED=7 T0=0.5 T1=0.05 PS=0.02 WS=50 NU=wq/run/w11p1.nu OUTNU=wq/run/W11.nu OUT=wq/run/W11.final.in /tmp/nuj9 wq/run/W11M.in > wq/run/W11.nuj.log 2>&1
tail -n 1 wq/run/W11.nuj.log
grep -q "violated=0 " wq/run/W11.nuj.log && ./finish.sh wq/run/W11.final.in wq/run/W11.nu wq/run/W11.lift 14 5
