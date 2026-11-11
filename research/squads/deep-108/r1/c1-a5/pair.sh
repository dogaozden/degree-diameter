#!/bin/bash
# usage: pair.sh NAME "NL gens..." "NR gens..."  -- info census + 300-member sample (scanLR, THR 300, start 0 step 200)
cd "$(dirname "$0")" || exit 1
. ./env.sh
NAME=$1; LG=$2; RG=$3
timeout 100 nice -n 10 ../../cq/cq3 59 $A $LG $RG info > info_$NAME.txt 2> info_$NAME.err
echo "== $NAME info"; grep -v "^L elt" info_$NAME.txt | tail -4
timeout 100 nice -n 10 ../../cq/cq3 59 $A $LG $RG scanLR samp_$NAME.tsv 300 0 200 2> samp_$NAME.log
echo "exit=$?  $(tail -1 samp_$NAME.log)  lines=$(wc -l < samp_$NAME.tsv)"
