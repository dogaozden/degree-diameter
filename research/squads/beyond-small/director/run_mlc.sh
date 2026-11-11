#!/bin/bash
# usage: run_mlc.sh N secs seed ; tries the 24 colour relabellings of chart_u8 on K3,3 + doubled PM over Z_N
N=$1; S=$2; SEED=$3; P=../../../theorems/squad165/charts
for q in $(seq -w 0 23); do
  r=$(WRITEBEST=1 ./mlift_chart ../../../theorems/squad165/base_k33m.txt z$N.tab $P/pat_u8_q$q.txt $S $SEED 2.0 ctrl_z${N}_q${q}_s$SEED.txt 2>&1 | tail -1)
  echo "N=$N q=$q seed=$SEED $r" >> mlc_z$N.log
done
