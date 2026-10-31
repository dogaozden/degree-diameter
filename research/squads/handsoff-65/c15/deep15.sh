#!/bin/bash
# usage: deep15.sh ORDER ID PAIR SECS SEED  -- re-export SmallGroup(ORDER,ID) diagonal pairs, anneal pair PAIR (p_PAIR_PAIR) for SECS
# seconds with seed SEED; the best graph goes to c15/best/deep_g<ORDER>_<ID>_p<PAIR>_s<SEED>_c<COST>.edges
SH=/home/user/degree-diameter/research/squads/handsoff-65/shared
C15=/home/user/degree-diameter/research/squads/handsoff-65/c15
ORDER=$1; ID=$2; PAIR=$3; SECS=$4; SEED=$5
dir=$C15/tmp/deep_g${ORDER}_${ID}_s${SEED}; rm -rf $dir; mkdir -p $dir $C15/best
gap -q -c "Read(\"$C15/dc2_diag.g\"); G:=SmallGroup($ORDER,$ID); ExportPairs(G, 2, \"$dir/p\"); QUIT;" </dev/null > $dir/gap.log 2>&1
out=$dir/out.edges
r=$(SA=1 SECS=$SECS SEED=$SEED timeout $((SECS*3+60)) nice -n 10 $SH/dcenum $dir/p_${PAIR}_${PAIR}.dc2 6 5 $out 2>/dev/null | tail -1)
c=$(echo "$r" | sed -n 's/.*best \([0-9]*\) vertices.*/\1/p')
echo "deep g${ORDER}_${ID} p${PAIR} secs $SECS seed $SEED | cost $c" >> $C15/results.txt
[ -n "$c" ] && cp $out $C15/best/deep_g${ORDER}_${ID}_p${PAIR}_s${SEED}_c${c}.edges
[ "$c" = 0 ] && cp $out $C15/HITS/deep_g${ORDER}_${ID}_p${PAIR}_s${SEED}.edges && echo "HIT deep $ORDER $ID $PAIR" >> $C15/HITS.txt
rm -rf $dir
echo "$r" | sed 's/set.*//' | cut -c1-150
