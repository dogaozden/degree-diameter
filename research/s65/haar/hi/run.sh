#!/bin/bash
# exhaustive haarex2 on the high-involution groups of order 352-360 with the lowest annealing costs (round s65r3 card c8)
for g in 360_61 360_74 352_43 352_61 360_126 360_138 360_59 360_128 360_140 360_146; do
  o=${g%_*}; i=${g#*_}
  gap -q -c "K:=SmallGroup($o,$i);; FN:=\"hx_$g.txt\";;" ../../tools/haarex2.g > exp_$g.log 2>&1
  timeout 1500 nice -n 8 ../../tools/haarex2 hx_$g.txt > h$g.log
  rm -f hx_$g.txt
done
echo ALLDONE > done.txt
