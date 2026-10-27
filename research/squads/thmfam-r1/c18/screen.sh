#!/bin/bash
# screen subset of primes: $1 = qs list; prints one line per candidate
R=/home/user/degree-diameter/research/squads/thmfam-r1/c18; G=/home/user/degree-diameter/research/theorems/haar_families
QS=$1
FS="python3 $G/family_score.py --group pgl --qs $QS"
summ(){ python3 -c "import sys,json; s=json.loads(sys.stdin.read().split('SUMMARY ')[1]); print(sys.argv[1], 'Delta',s['Delta'],'mean',s['mean_excess'],'n',s['n_q'], {k:round(v['vs_table'],3) for k,v in s['best'].items() if k in ('8','9','10','11') and v['vs_table']})" "$2"; }
nice -n 10 timeout 900 $FS --gen "$G/gen_lps.sh 5 {q}" | tail -1 | summ 'LPS p5' x
for v in f_1pijk f_ipjpk o_far o_1i o_2i o_unip o_u2 o_low o_1p2i o_i2; do
  nice -n 10 timeout 900 $FS --gen "bash -c '($G/gen_lps.sh 5 {q}; python3 $R/repair.py 5 {q} $v)'" | tail -1 | summ "p5 $v" x; done
nice -n 10 timeout 900 $FS --gen "$G/gen_lps.sh 7 {q}" | tail -1 | summ 'LPS p7' x
for v in f_1pijk f_ipjpk o_far o_1i o_2i o_unip; do
  nice -n 10 timeout 900 $FS --gen "bash -c '($G/gen_lps.sh 7 {q}; python3 $R/repair.py 7 {q} $v)'" | tail -1 | summ "p7 $v" x; done
echo DONE
