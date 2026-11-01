#!/bin/bash
# usage: run.sh TAG SEED K START_OR_dash SPEC...   (SPEC e.g. "meta 677 52 12 1" with d D before it: see below)
# usage: run.sh TAG SEED K START D SPEC_WORDS...  (START "-" = fresh)
B=/home/user/degree-diameter/research/squads/beyond11b/bin
W=/home/user/degree-diameter/research/squads/beyond11b/r5/k14
TAG=$1; SEED=$2; K=$3; ST=$4; DD="$5 $6"; shift 6
SPEC="$*"
ENVS="THREADS=1 SAVEBEST=$W/$TAG.best.txt"
if [ "$ST" != "-" ]; then ENVS="$ENVS START=$ST"; fi
R=$(env $ENVS timeout 105 nice -n 10 $B/haar_gen3s $DD 95 $SEED $K $W/$TAG.sol $SPEC 2>$W/$TAG.err | grep RESULT)
ST0=$(grep 'start cost' $W/$TAG.err 2>/dev/null)
echo "$TAG seed=$SEED K=$K start=$ST shape=($DD) spec=[$SPEC] :: $ST0 :: $R" >> $W/runs.txt
echo "$TAG seed=$SEED K=$K start=$ST :: $ST0 :: $R"
