#!/bin/bash
# usage: screen.sh ORDER SECS RANDCOMB i1 i2 ...   (mcos screen, type 1,1,3|1,1,3, a=3,4,5)
ORD=$1; S=$2; RC=$3; shift 3
cd /home/user/degree-diameter/research/squads/deep-65/round1/h3
for i in "$@"; do
  for a in 3 4 5; do
    b=$((5-a))
    NN="$a,$b,1,$b,$a,1,1,1,0"
    out=$(TYPE="1,1,3|1,1,3" N="$NN" SECS=$S RANDCOMB=$RC SEED=$((i*10+a)) EDGES=edges/g${ORD}_${i}_a${a}.edges timeout 60 nice -n 10 ./bin/mcos groups/sg_${ORD}_${i}.txt 2>/dev/null | grep -E '^(COMB|RESULT|SOL)' | tr '\n' ' ')
    best=$(echo "$out" | grep -o 'best [-0-9]*' | tail -1 | awk '{print $2}')
    echo "ORD $ORD grp $i a $a best $best :: $out" | tee -a screen/screen_$ORD.txt | cut -c1-200
  done
done
