#!/bin/bash
# (10,14) pipeline: wait for the (9,14) check to end (memory), then search PSL(2,239) x Z1789 with ORBIT "3 3 1" and check.
cd /home/user/degree-diameter/research/frontier/beyond14
echo -12 > /proc/self/autogroup
until grep -q "^exit:" checks/d9D14_psl_241_1429_orb3-3-0_s1.gen.txt 2>/dev/null; do sleep 20; done
S=d10D14_psl_239_1789_orb3-3-1_s1
ORBIT="3 3 1" THREADS=2 ./bin/haar_big0 10 14 1500 1 1 runs/$S.txt psl 239 1789 > runs/$S.out 2>&1
echo "search exit $?" >> runs/$S.out
grep -q "best=0" runs/$S.out || { echo "no cost-0 S"; exit 1; }
cp runs/$S.txt sols/$S.txt
L=checks/$S.gen.txt
{ echo "checker: haarcheck_gen (research/frontier/haarcheck_gen.c, built here as bin/haarcheck_gen)"; echo "command: OMP_NUM_THREADS=2 ./bin/haarcheck_gen sols/$S.txt"; echo "start: $(date -u +%FT%TZ)"; sha256sum bin/haarcheck_gen sols/$S.txt; s=$(date +%s); OMP_NUM_THREADS=2 ./bin/haarcheck_gen sols/$S.txt; echo "exit: $?"; echo "end: $(date -u +%FT%TZ) ($(( $(date +%s) - s )) s)"; } > $L 2>&1
