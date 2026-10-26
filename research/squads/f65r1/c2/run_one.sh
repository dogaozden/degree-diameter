#!/bin/bash
# one argument: h|groupname|groupspec(with _ for spaces)|base|secs|seed
cd /home/user/degree-diameter/research/squads/f65r1/c2
IFS='|' read -r h gname gspec base secs seed <<< "$1"
gspec=${gspec//_/ }
b=$(basename $base .txt)
tag="h${h}_${gname}_${b}_s${seed}"
out=sols/${tag}.txt
# shellcheck disable=SC2086
timeout 600 nice -n 10 ./lift search $base 5 $secs $seed 8 $out $gspec > logs/${tag}.log 2>&1
res=$(grep '^RESULT' logs/${tag}.log | sed 's/.*best=\([0-9-]*\).*/\1/')
echo "$h|$gname|$b|$seed|$res" >> screen_results.txt
