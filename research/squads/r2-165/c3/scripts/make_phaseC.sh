#!/bin/bash
# pick the best screen line per target (min best_cost over its group tables) and emit one 25 s job per target
SQ=/home/user/degree-diameter/research/theorems/squad165
R=/tmp/claude-0/r2c3/res_screen.txt
: > /tmp/claude-0/r2c3/jobs_phaseC.txt
j=900
for tgt in "5_13_65 T_cyc13.txt 5" "5_14_70 T_cyc14.txt T_dih7.txt 5" "6_11_66 T_cyc11.txt 6" "6_12_72 T_cyc12.txt T_dih6.txt T_meta342.txt 6" "7_10_70 T_cyc10.txt T_dih5.txt 7" "8_9_72 T_cyc9.txt T_c3xc3.txt 8" "13_5_65 T_cyc5.txt 13"; do
  set -- $tgt; name=$1; shift
  kk=$(echo "$@" | awk '{print $NF}')
  tabs=$(echo "$@" | awk '{$NF=""; print}')
  best=""; bc=999
  for tb in $tabs; do
    while read tag base table pat cost; do
      [ "$table" = "$tb" ] || continue
      c=${cost#best_cost=}; [ -n "$c" ] || continue
      if [ "$c" -lt "$bc" ]; then bc=$c; best="$tag $base $table $pat"; fi
    done < $R
  done
  set -- $best
  tag=$1; base=$2; table=$3; pat=$4
  for rep in 1 2; do
    j=$((j+1))
    echo "C_${name}_${tag#s_}_r$rep /tmp/claude-0/r2c3/bases_k$kk/${base} /tmp/claude-0/r2c3/$table $SQ/charts/$pat 20 $j 2.0" >> /tmp/claude-0/r2c3/jobs_phaseC.txt
  done
  echo "target $name: screen best $bc from $tag / $base / $table / $pat"
done
