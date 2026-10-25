#!/bin/bash
# c0run.sh STATE.sol IN.lift2.sol "FDSET" OUT SEED RELAX ITERS TEMP0 [SWAPP PTARG]: coset-0 by dmfast_fd3 for a FLAGDEL state
X=$1; IN=$2; FS=$3; O=$4; SD=$5; RX=$6; IT=$7; T0=$8; SW=${9:-0.02}; PT=${10:-0.6}
FREE="$(awk '$1=="free"{$1="";print}' "$X")" FDSET="$FS" RELAX=$RX PENW=2 HUBADJ="$(python3 hubadj.py "$X" "$FS")" BASE=gq/gq_q7.bin NPOLY=4 \
  SEED=$SD IN="$IN" OUT="$O.sol" PTARG=$PT SWAPP=$SW ITERS=$IT TEMP0=$T0 TEMP1=0.02 timeout 1200 nice -n 5 ./dmfast_fd3 7 > "$O.log" 2> "$O.err"
cat "$O.log"
