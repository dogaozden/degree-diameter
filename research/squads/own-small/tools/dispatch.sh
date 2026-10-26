#!/bin/bash
# dispatch.sh: the director's CPU queue for squad cards (own-small round 3). Cards append task lines to
# $Q/tasks.txt (use flock $Q/lock), one task per line:
#   CARD TOOL p N id D secs seed GROUPSFILE [STARTFILE]
# TOOL = salift_s (cubic, joint base+voltage annealing) or salift4 (degree 4). GROUPSFILE = absolute path of a
# gap_export-format table file containing group id. Workers (NW, default 4) take tasks round-robin over cards in
# arrival order, at most CAP tasks per card. Each task writes $Q/out/<CARD>_<k>.{log,sol.best[,sol]} and appends to
# $Q/results.txt: "k CARD p N id D seed best=<c> n=<2pN> state=<file>". A cost-0 state is converted with best2edges.py
# and checked with score48 at once; the check line is appended to $Q/valid.txt.
Q=/home/user/degree-diameter/research/squads/own-small/runs/queue
T=/home/user/degree-diameter/research/squads/own-small/tools
NW=${NW:-4}; CAP=${CAP:-14}
mkdir -p $Q/out; touch $Q/tasks.txt $Q/results.txt $Q/valid.txt $Q/lock
declare -A taken percard
run_task() {
    local k=$1 card=$2 tool=$3 p=$4 N=$5 id=$6 D=$7 secs=$8 seed=$9 gf=${10} st=${11}
    local tag=$Q/out/${card}_$k
    if [ -n "$st" ]; then export START=$st; else unset START; fi
    D=$D $T/bin/$tool $p $gf $id $seed $secs 10 0.3 $tag.sol > $tag.log 2>&1
    local b=$(grep -o 'best [0-9]*' $tag.log | tail -1 | awk '{print $2}')
    [ -z "$b" ] && [ -n "$st" ] && b=$(head -1 $st | awk '{print $4}')
    echo "$k $card p=$p N=$N id=$id D=$D seed=$seed best=$b n=$((2*p*N)) state=$tag.sol.best" >> $Q/results.txt
    if [ -s $tag.sol ]; then
        local d=4; [ $tool = salift_s ] && d=3
        python3 -I $T/best2edges.py $gf $tag.sol $tag.edges > /dev/null 2>&1
        echo "$k $card n=$((2*p*N)) D=$D $($T/bin/score48 $tag.edges $d $D | tail -1) file=$tag.edges" >> $Q/valid.txt
    fi
}
k=0
while true; do
    [ -f $Q/stop ] && break
    mapfile -t L < $Q/tasks.txt
    # pick the next untaken task, round-robin: the card with the fewest tasks taken so far goes first
    best=-1; bestc=999999
    for i in "${!L[@]}"; do
        [ -n "${taken[$i]}" ] && continue
        set -- ${L[$i]}; [ $# -lt 9 ] && { taken[$i]=bad; continue; }
        c=${percard[$1]:-0}
        if [ $c -ge $CAP ]; then taken[$i]=cap; echo "cap $1: ${L[$i]}" >> $Q/skipped.txt; continue; fi
        if [ $c -lt $bestc ]; then best=$i; bestc=$c; fi
    done
    if [ $best -ge 0 ] && [ $(jobs -r | wc -l) -lt $NW ]; then
        taken[$best]=1; set -- ${L[$best]}; percard[$1]=$(( ${percard[$1]:-0} + 1 )); k=$((k+1))
        run_task $k "$@" &
    else
        sleep 2
    fi
done
wait
