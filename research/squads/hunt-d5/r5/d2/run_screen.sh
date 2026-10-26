#!/bin/bash
# run_screen.sh FIRST LAST : screen lines FIRST..LAST of ../../r3/meta_specs_d6.txt (skipping 71 and 7 3 2 17)
spec=../../r3/meta_specs_d6.txt
first=$1; last=$2
n=0
while read -r mu ord _ p k r c rest; do
  case "$mu" in \#*|"") continue;; esac
  n=$((n+1)); [ $n -lt $first ] && continue; [ $n -gt $last ] && break
  if [ "$p" = 71 ] || { [ "$p" = 7 ] && [ "$k" = 3 ] && [ "$r" = 2 ] && [ "$c" = 17 ]; }; then continue; fi
  dir=$PWD/screen/m_${p}_${k}_${r}_${c}
  mkdir -p $dir
  COOL=10 REHEAT=40 timeout 60 nice -n 10 ../../tools/farm.sh $dir 6 6 16 1 4 meta $p $k $r $c
  best=$(grep -o 'best=[0-9]*' $dir/farm.log | cut -d= -f2 | sort -n | head -1)
  echo "order=$ord mu=$mu meta $p $k $r $c best=$best"
done < $spec
