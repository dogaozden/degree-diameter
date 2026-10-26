#!/bin/bash
# one exhaustive orderly Haar job: export SmallGroup(n,i) with Aut generators, run haarex2, keep the log
n=$1; i=$2; D=/home/user/degree-diameter/research/fresh65/hx2; T=/home/user/degree-diameter/research/fresh65/tools
cd $T
[ -f $D/h${n}_$i.log ] && grep -q DONE $D/h${n}_$i.log && exit 0
timeout 3000 gap -q -c "K:=SmallGroup($n,$i);; FN:=\"$D/h${n}_$i.txt\";;" haarex2.g >> $D/export.log 2>&1
timeout 14400 ./haarex2 $D/h${n}_$i.txt > $D/h${n}_$i.log 2>&1
rm -f $D/h${n}_$i.txt
