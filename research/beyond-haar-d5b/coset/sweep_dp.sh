#!/bin/bash
# usage: sweep_dp.sh K PORD "IDS" DELTA SECS -- bi-coset graphs (H = K of order 2) of C_K x SmallGroup(PORD, j);
# lines in logs/dp_<K>x<PORD>_d<DELTA>.txt
k=$1; po=$2; ids=$3; delta=$4; secs=$5
dir=tmpdp_${k}_${po}_$$; mkdir -p $dir logs
for j in $(echo "$ids" | tr -d '[]' | tr ',' ' '); do
  gap -q -c "K:=$k; PORD:=$po; IDS:=[$j]; OUTDIR:=\"$dir\";" dp_export.g > $dir/gap.log 2>&1
  for f in $dir/*.dc2; do
    [ -e "$f" ] || continue
    b=$(basename $f .dc2); a=$(echo $b | awk -F_ '{print $(NF-1)}'); c=$(echo $b | awk -F_ '{print $NF}')
    if [ "$a" = "$c" ]; then
      r=$(SA=1 SECS=$secs SEED=1 timeout $((secs*8+600)) nice -n 5 ./dcenum $f $delta 5 ${f%.dc2}.edges 2>/dev/null | tail -1)
      echo "$r" >> logs/dp_${k}x${po}_d${delta}.txt
      case "$r" in *"best 0 "*) cp ${f%.dc2}.edges logs/HIT_$b.edges; cp $f logs/; echo "HIT $r";; esac
    fi
    rm -f $f ${f%.dc2}.edges
  done
done
rm -rf $dir
