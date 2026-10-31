#!/bin/bash
# usage: pipe.sh ORDER IDX SECS_MCOS : Haar floor via mcos, then automorphism-twist scan with each 5-subset of the floor S6
cd /home/user/degree-diameter/research/squads/handsoff-65/c6
O=$1; I=$2; T=$3; G=tabs/sg_${O}_${I}.txt
timeout 300 nice -n 10 env TYPE="1|1" SECS=$T SEED=3 T0=2 T1=0.05 ITERS=30000 EDGES=pf_${O}_${I}.edges ../shared/mcos $G > pf_${O}_${I}.mcos 2>&1
FL=$(grep RESULT pf_${O}_${I}.mcos | awk '{print $3}')
S6=$(python3 -c "
L=open('pf_${O}_${I}.edges').read().split(); n=int(L[0]); E=list(map(int,L[1:])); m=n//2
print(' '.join(str(E[i+1]-m) for i in range(0,len(E),2) if E[i]==0))")
HB=$(../shared/score65 pf_${O}_${I}.edges | grep -o 'bad=[0-9]*')
echo "GROUP ${O}_${I} $(cat tabs/sg_${O}_${I}.name 2>/dev/null) haar_floor_rep=$FL haar_bad=$HB"
[ -f phi/aut_${O}_${I}.txt ] || timeout 200 nice -n 10 gap -q -c "ORDER:=$O; IDS:=[$I];" autos.g >/dev/null 2>&1
BEST=999999999; 
set -- $S6
for drop in 0 1 2 3 4 5; do
  S5=$(echo "$S6" | tr ' ' '\n' | awk -v d=$drop 'NR-1!=d' | paste -sd, -)
  timeout 300 nice -n 10 ./phi_bin $G phi/aut_${O}_${I}.txt 0 1 pscan_${O}_${I}_$drop SCAN=1 S=$S5 MAXK=100000 > pscan_${O}_${I}_$drop.out 2>&1
  R=$(tail -1 pscan_${O}_${I}_$drop.out)
  echo "  drop=$drop $R"
done
