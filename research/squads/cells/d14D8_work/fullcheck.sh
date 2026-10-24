#!/bin/bash
# fullcheck.sh BASEFILE [EVAL] [P]: exact diameter-8 check of a cyclic lift, every source, split over P processes.
# EVAL = lifteval (m <= 64) or liftevalw. Prints per-part COST lines and the total; exit 0 iff total 0.
f=$1; ev=${2:-./liftevalw}; P=${3:-4}
tmp=$(mktemp -d)
for i in $(seq 0 $((P-1))); do nice -n 5 $ev $f 8 s:$i:$P > $tmp/part$i.txt 2> $tmp/err$i.txt & done
wait
cat $tmp/part*.txt
awk '{c+=$2; s+=$4; b+=$6} END {print "TOTAL COST", c, "sources", s, "bad", b; exit (c>0)}' $tmp/part*.txt
