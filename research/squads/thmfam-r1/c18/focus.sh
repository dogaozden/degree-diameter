#!/bin/bash
R=/home/user/degree-diameter/research/squads/thmfam-r1/c18; G=/home/user/degree-diameter/research/theorems/haar_families
QS=$1; FS="python3 $G/family_score.py --qs $QS"
summ(){ python3 -c "import sys,json; s=json.loads(sys.stdin.read().split('SUMMARY ')[1]); print(sys.argv[1], 'Delta',s['Delta'],'mean',s['mean_excess'],'n',s['n_q'], {k:round(v['vs_table'],3) for k,v in s['best'].items() if k in ('8','9','10') and v['vs_table']})" "$2"; }
nice -n 10 timeout 900 $FS --group pgl --gen "bash -c '($G/gen_lps.sh 5 {q}; python3 $R/repair.py 5 {q} o_unip)'" | tail -1 | summ 'p5 +3 o_unip (D9)' x
nice -n 10 timeout 900 $FS --group pgl --gen "bash -c '($G/gen_lps.sh 5 {q}; python3 $R/repair.py 5 {q} f_ipjpk)'" | tail -1 | summ 'p5 +1 f_ipjpk (D7)' x
for s in 1 2; do nice -n 10 timeout 900 $FS --group psl --gen "python3 $G/gen_random_orb.py {q} 0 3 $s" | tail -1 | summ "rand D9 f0k3 seed$s" x; done
for s in 1 2; do nice -n 10 timeout 900 $FS --group psl --gen "python3 $G/gen_random_orb.py {q} 1 2 $s" | tail -1 | summ "rand D7 f1k2 seed$s" x; done
echo DONE
