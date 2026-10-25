#!/bin/bash
# pipe_fd.sh COV.sol "FDSET" TAG SEED: after a coverage(+D1)-0 state COV.sol (fdrun.sh output, H=3 numbering):
# hub repair if needed -> coset-0 (dmfast_fd3 penalty mode) -> lns2 best-flip repair -> exact check (finish_fd.sh).
X=$1; FS=$2; T=$3; SD=${4:-1}; R=runs/$T
python3 ../hubs/sol2lift2.py "$X" ${R}_l2.sol > /dev/null
hs=$(FREE="$(awk '$1=="free"{$1="";print}' "$X")" H=3 FLAGDEL=1 FDSET="$FS" HUBG_IN="$X" ITERS=0 timeout 300 nice -n 5 ./dmhub2_f gq/gq_q7.bin ${R}_l2.sol ${R}_chk | awk '/final cost/{print $12}' | tr -d ')')
echo "hub-sourced failures: $hs"
ST=$X
if [ "$hs" != "0" ]; then
  timeout 900 nice -n 5 python3 hubfix.py "$X" ${R}_l2.sol "$FS" ${R}_hf.sol | tail -n 1
  c=$(python3 -c "
import lns, d1, numpy as np
S=lns.read_sol('${R}_hf.sol'); FD=set(int(x) for x in '$FS'.split()); F=S['F']
hg=[int(x) for x in S['rows']['hubgraph']]; A=np.zeros((9,9),bool)
for e in range(0,len(hg),2):
    a,b=hg[e],hg[e+1]
    if (a%3<2 or a//3 in FD) and (b%3<2 or b//3 in FD): A[a//3,b//3]=True
print(lns.cover(F,S['sig'],A)+sum(cp+cl for i,(p,l,cp,cl,h) in enumerate(d1.d1(F,S['sig'])) if i in FD))")
  echo "coverage+D1 after hubfix: $c"
  ST=${R}_hf.sol
  python3 ../hubs/sol2lift2.py $ST ${R}_l2.sol > /dev/null
  if [ "$c" != "0" ]; then NOC0=1 KZ=4 SECS=600 STEP=15 SIZE=60 SEED=$SD timeout 700 nice -n 5 python3 lns2.py $ST ${R}_l2.sol "$FS" ${R}_nc.sol | tail -n 1; cp ${R}_nc.sol ${R}_l2.sol; fi
fi
./c0run.sh $ST ${R}_l2.sol "$FS" ${R}_c0a $SD 1 12000000 0.25 0.01 0.5 | tail -n 1
./c0run.sh $ST ${R}_c0a.sol "$FS" ${R}_c0 $((SD + 1)) 2 8000000 0.15 0.03 0.6 | tail -n 1
FLIPS=1 BESTFLIP=1 KZ=4 SECS=${LNSSECS:-2400} STEP=15 SIZE=60 REPAIRS=8 SEED=$SD timeout 2600 nice -n 5 python3 lns2.py $ST ${R}_c0.sol "$FS" ${R}_lns.sol > ${R}_lns.log 2>&1
tail -n 1 ${R}_lns.log
./finish_fd.sh $ST ${R}_lns.sol "$FS" ${R}_fin
echo "STATE $ST"
