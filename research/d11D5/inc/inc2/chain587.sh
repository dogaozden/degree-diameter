#!/bin/bash
# long anneal for an n = 587 start, then wpo if low, nu stage from the 7,032 nu, check
cd /home/user/degree-diameter/research/d11D5/inc
s=$1; nu=$2; P=$3; seed=$4
SECS=1100 SEED=$seed T0=20 T1=0.3 PF=0.3 PH=0.7 OUT=$P.L.in OUT0=$P.L0.in /tmp/po7 $s > $P.L.log 2>&1
[ -f $P.L0.in ] && cp $P.L0.in $P.L.in
c=$(SCORE=1 /tmp/po7 $P.L.in | tail -1 | grep -oE "cost=[0-9]+" | cut -d= -f2); echo "long SA -> $c"
if [ "$c" != "0" ]; then
  [ "$c" -gt 30 ] && { echo "too high for wpo"; exit 1; }
  SECS=400 SEED=$seed OUT=$P.w.in OUT0=$P.w0.in /tmp/wpo $P.L.in > $P.w.log 2>&1
  [ -f $P.w0.in ] || { echo "wpo did not reach 0"; exit 1; }
  cp $P.w0.in $P.L.in
fi
echo "structural 0"
TARGET=1 SECS=400 SEED=$seed T0=0.4 T1=0.05 PS=0.02 WS=50 NU=$nu OUTNU=$P.nu OUT=$P.final.in /tmp/nuj9 $P.L.in > $P.nuj.log 2>&1
tail -n 1 $P.nuj.log
grep -q "violated=0 " $P.nuj.log && ./finish.sh $P.final.in $P.nu $P.lift 11 5
