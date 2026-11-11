#!/bin/bash
# alpha_sweep.sh TAG ORDER GROUP... n : RANDORB=5000 for every conjugating element index ALPHA=0..ORDER-1 (k=2, m=3, f=0)
# output: alpha_sweep/TAG.tsv  index  min  p1  median  fix  (only valid alpha lines)
TAG=$1; ORD=$2; shift 2
R=/home/user/degree-diameter/research/squads/raise-d6D8
S=/home/user/degree-diameter/research/structured
mkdir -p $R/alpha_sweep
one() {
  i=$1; shift
  out=$(cd $S && ALPHA=$i ORBIT="2 3 0" RANDORB=5000 THREADS=1 ./haar_sym 6 8 1 1 8 /dev/null "$@" 2>&1)
  line=$(echo "$out" | grep "^RANDORB d=" | head -1)
  fix=$(echo "$out" | grep -o "fix=[0-9]*" | head -1)
  [ -n "$line" ] && echo "$i $(echo "$line" | grep -o 'min=[0-9]*') $(echo "$line" | grep -o 'p1=[0-9]*') $(echo "$line" | grep -o 'median=[0-9]*') $fix"
}
export -f one; export S
seq 0 $((ORD-1)) | xargs -P 4 -I{} bash -c "one {} $*" > $R/alpha_sweep/$TAG.tsv
sort -t' ' -k2 $R/alpha_sweep/$TAG.tsv -o $R/alpha_sweep/$TAG.tsv 2>/dev/null
echo SWEEP_DONE $TAG >> $R/runs/wave2.out
