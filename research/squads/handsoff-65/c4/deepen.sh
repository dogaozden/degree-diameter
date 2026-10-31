#!/bin/bash
# usage: deepen.sh ORDER ID PAIR SECS SEED  -- re-export group ORDER,ID (dc2_lib.g), anneal pair p_PAIR_PAIR (diagonal
# class pair, H = K) for SECS seconds with seed SEED; edges of the best graph go to c4/best/g<ORDER>_<ID>_p<PAIR>_s<SEED>.edges
SH=/home/user/degree-diameter/research/squads/handsoff-65/shared
C4=/home/user/degree-diameter/research/squads/handsoff-65/c4
ORDER=$1; ID=$2; PAIR=$3; SECS=$4; SEED=$5
dir=$C4/tmp/deep_g${ORDER}_${ID}; mkdir -p $dir $C4/best
gap -q -c "Read(\"$SH/dc2_lib.g\"); G:=SmallGroup($ORDER,$ID); ExportPairs(G, 2, \"$dir/p\"); QUIT;" </dev/null > $dir/gap.log 2>&1
out=$C4/best/g${ORDER}_${ID}_p${PAIR}_s${SEED}.edges
r=$(SA=1 SECS=$SECS SEED=$SEED timeout $((SECS*3+60)) nice -n 10 $SH/dcenum $dir/p_${PAIR}_${PAIR}.dc2 6 5 $out 2>/dev/null | tail -1)
echo "deep g${ORDER}_${ID} p${PAIR} secs $SECS seed $SEED | $(echo "$r" | sed 's/set.*//')" >> $C4/results.txt
echo "$r" | sed 's/set.*//'
