#!/bin/bash
# usage: eval_ctrl.sh CTRLFILE N q   -> exact lift costs: plain (both perm conventions) and with extra vectors on each letter
F=$1; N=$2; q=$3
P=$(sed -n "$((10#$q+1))p" ../../../theorems/squad165/charts/perm_list_u8.txt | tr -d '(),' | cut -d' ' -f2-)
INV=$(python3 -c "p=list(map(int,'$P'.split())); inv=[0]*4
for i,x in enumerate(p): inv[x]=i
print(' '.join(map(str,inv)))")
for pp in "$P" "$INV"; do
  c=$(./rc17c chart_u8.txt $F $N "$pp" 9 1 0 2>/dev/null | grep FINAL | awk '{print $NF}')
  echo "$F perm=($pp) plain cost $c"
done
