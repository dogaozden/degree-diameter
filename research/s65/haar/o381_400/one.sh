#!/bin/bash
# one.sh ORDER_ID: export, exhaustive haarex3 (900 s cap), delete the export. Log h<ORDER_ID>.log (run from o381_400/)
g=$1; o=${g%_*}; i=${g#*_}
[ -e h$g.log ] && grep -q DONE h$g.log && exit 0
gap -q -c "K:=SmallGroup($o,$i);; FN:=\"hx_$g.txt\";;" ../../tools/haarex2.g > exp_$g.log 2>&1
timeout 900 nice -n 5 ../../tools/haarex3 hx_$g.txt > h$g.log
rm -f hx_$g.txt
