#!/bin/bash
# pipeline.sh start.in start.nu prefix d D : structural stage (po7 annealing, then wpo clause weighting) and nu stage
# (nujoint annealing with targeted sigma swaps), then finish.sh.  Binaries: /tmp/po7 (plus/plusopt7.c),
# /tmp/wpo (squads/r3-d11D5/c2/wpo.c), /tmp/nuj7 (inc/nujoint.c).
s=$1; nu=$2; P=$3; d=$4; D=$5
cost() { SCORE=1 /tmp/po7 $1 | tail -1 | grep -oE "cost=[0-9]+" | cut -d= -f2; }
cp $s $P.s0.in
if [ "$(cost $P.s0.in)" != "0" ]; then
  SECS=${SASECS:-600} SEED=${SEED:-1} T0=20 T1=0.4 PF=0.3 PH=0.7 OUT=$P.sa.in OUT0=$P.sa0.in /tmp/po7 $P.s0.in > $P.sa.log 2>&1
  [ -f $P.sa0.in ] && cp $P.sa0.in $P.sa.in
  echo "SA -> $(cost $P.sa.in)"
  if [ "$(cost $P.sa.in)" -gt 20 ]; then
    SECS=400 SEED=$(( ${SEED:-1} + 100 )) T0=3 T1=0.2 PF=0.3 PH=0.7 OUT=$P.sb.in OUT0=$P.sb0.in /tmp/po7 $P.sa.in > $P.sb.log 2>&1
    [ -f $P.sb0.in ] && cp $P.sb0.in $P.sb.in; cp $P.sb.in $P.sa.in; echo "SA2 -> $(cost $P.sa.in)"
  fi
  if [ "$(cost $P.sa.in)" != "0" ]; then
    SECS=${WSECS:-1200} SEED=${SEED:-1} OUT=$P.w.in OUT0=$P.w0.in /tmp/wpo $P.sa.in > $P.w.log 2>&1
    [ -f $P.w0.in ] || { echo "wpo did not reach 0: $(cost $P.w.in)"; exit 1; }
    cp $P.w0.in $P.struct.in
  else cp $P.sa.in $P.struct.in; fi
else cp $P.s0.in $P.struct.in; fi
echo "structural 0: $P.struct.in"
TARGET=1 SECS=${NSECS:-900} SEED=${SEED:-1} T0=${NT0:-0.4} T1=0.05 PS=0.02 WS=50 NU=$nu OUTNU=$P.nu OUT=$P.final.in /tmp/nuj7 $P.struct.in > $P.nuj.log 2>&1
tail -n 1 $P.nuj.log
grep -q "violated=0 " $P.nuj.log && ./finish.sh $P.final.in $P.nu $P.lift $d $D
