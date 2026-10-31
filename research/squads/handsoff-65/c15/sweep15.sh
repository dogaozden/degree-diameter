#!/bin/bash
# usage: sweep15.sh SECS ORDER ID   -- diagonal bi-coset pairs (H = K, |H| = 2, core-free i.e. non-central) of SmallGroup(ORDER,ID),
# dcenum SA SECS per pair. One line per pair in c15/results.txt. Edges of cost <= 20 kept in c15/best/, cost 0 in c15/HITS/.
SH=/home/user/degree-diameter/research/squads/handsoff-65/shared
C15=/home/user/degree-diameter/research/squads/handsoff-65/c15
SECS=$1; ORDER=$2; ID=$3
dir=$C15/tmp/g${ORDER}_${ID}; rm -rf $dir; mkdir -p $dir $C15/best $C15/HITS
gap -q -c "Read(\"$C15/dc2_diag.g\"); G:=SmallGroup($ORDER,$ID); ExportPairs(G, 2, \"$dir/p\"); QUIT;" </dev/null > $dir/gap.log 2>&1
npairs=0
for f in $dir/p_*.dc2; do
  [ -e "$f" ] || continue
  b=$(basename ${f%.dc2}); [[ $b =~ p_([0-9]+)_([0-9]+) ]]; [ "${BASH_REMATCH[1]}" = "${BASH_REMATCH[2]}" ] || continue; npairs=$((npairs+1))
  out=$dir/$b.edges
  r=$(SA=1 SECS=$SECS SEED=1 timeout $((SECS*3+60)) nice -n 10 $SH/dcenum $f 6 5 $out 2>$dir/err.txt | tail -1)
  nd=$(sed 's/.*double cosets \([0-9]*\);.*/\1/' $dir/err.txt | head -1)
  echo "sa d6 $ORDER $ID $b ndc=$nd | $(echo "$r" | sed 's/set.*//' | sed 's/^RESULT //;s#/home[^ ]*/##')" >> $C15/results.txt
  c=$(echo "$r" | sed -n 's/.*best \([0-9]*\) vertices.*/\1/p')
  if [ "$c" = 0 ]; then cp $out $C15/HITS/g${ORDER}_${ID}_${b}.edges; echo "HIT $ORDER $ID $b" >> $C15/HITS.txt; fi
  if [ -n "$c" ] && [ "$c" -le 20 ]; then cp $out $C15/best/g${ORDER}_${ID}_${b}_c${c}.edges; fi
done
[ $npairs -eq 0 ] && echo "sa d6 $ORDER $ID NOPAIRS" >> $C15/results.txt
rm -rf $dir
