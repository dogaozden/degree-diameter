#!/bin/bash
# endgame.sh base.in nu prefix rounds : alternate SIGFIX (sigma swaps giving violated pairs a sigma route) and a short
# low-temperature nu anneal, until the parity violations reach 0.  Uses /tmp/nuj7 (nujoint.c).
b=$1; nu=$2; P=$3; R=${4:-6}
cp $b $P.in; cp $nu $P.nu
for r in $(seq 1 $R); do
  SIGFIX=1 FIRST=1 SECS=600 NU=$P.nu OUTNU=$P.nu OUT=$P.in /tmp/nuj7 $P.in > $P.sf$r.log 2>&1
  v=$(grep -oE "violated [0-9]+" $P.sf$r.log | tail -1 | cut -d' ' -f2); echo "round $r SIGFIX -> $v"
  [ "$v" = "0" ] && break
  TARGET=1 SECS=150 SEED=$r T0=0.25 T1=0.05 PS=0.02 WS=50 NU=$P.nu OUTNU=$P.nu OUT=$P.in /tmp/nuj7 $P.in > $P.sa$r.log 2>&1
  v=$(grep -oE "violated [0-9]+" $P.sa$r.log | tail -1 | cut -d' ' -f2); echo "round $r SA -> $v"
  [ "$v" = "0" ] && break
done
