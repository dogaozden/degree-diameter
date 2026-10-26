#!/bin/bash
# farm_cls.sh DIR CNT SEED0 NSEEDS : haar_cls farm on meta 41 15 10 (= C3 x (Z41 x| Z5)), d=7, D=5, 6 s per seed.
# CNT = counts of S over the C3 factor (j mod 3), e.g. 3,2,2 ; "none" = unconstrained.
dir=$1; cnt=$2; s0=$3; ns=$4
mkdir -p $dir
for ((s=s0; s<s0+ns; s++)); do
  if [ "$cnt" = none ]; then cenv="X=1"; else cenv="CQ=3 CNT=$cnt"; fi
  r=$(env $cenv SAVEBEST=1 THREADS=1 OMP_NUM_THREADS=1 COOL=10 REHEAT=40 timeout 26 nice -n 10 ./haar_cls 7 5 6 $s 16 $dir/s$s.sol meta 41 15 10 1 | grep -E "RESULT|wrote" | tr '\n' ' ')
  echo "seed=$s cnt=$cnt $r" >> $dir/farm.log
done
echo DONE >> $dir/farm.log
