#!/bin/bash
# runq.sh ORD T: qfeas on every exported group of order ORD with threshold T, results in res_ORD.txt
for f in $(ls q$1/hx_$1_*.txt | sort -t_ -k3 -n); do id=$(basename $f .txt); id=${id##*_}; echo "$1 $id $(timeout 1200 /tmp/claude-0/bin/qfeas $f $2)"; done > res_$1.txt
