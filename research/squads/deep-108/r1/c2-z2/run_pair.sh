#!/bin/bash
# usage: run_pair.sh LNAME RNAME  (names from classes.sh; RNAME may equal LNAME: then R = L, NR = 0)
# writes info_<L>_<R>.txt (census) and samp_<L>_<R>.tsv (scanLR, THR 300, index = 0 mod 200)
cd "$(dirname "$0")"
. ./classes.sh
eval L=\$$1; eval R=\$$2
tag="$1_$2"
if [ "$1" = "$2" ]; then RR=0; else RR="$R"; fi
timeout 100 nice -n 10 ../../cq/cq2 181 1 2 $L $RR info > info_${tag}.txt 2> info_${tag}.err
python3 es.py info_${tag}.txt
timeout 100 nice -n 10 ../../cq/cq2 181 1 2 $L $RR scanLR samp_${tag}.tsv 300 0 200 2> samp_${tag}.err
echo "[$tag] $(tail -1 samp_${tag}.err)"
