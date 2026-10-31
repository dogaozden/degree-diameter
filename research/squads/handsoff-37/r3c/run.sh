#!/bin/bash
# usage: run.sh LABEL GROUP K SEED SECS   (env passes engine settings); appends a line to out/runs.tsv
cd /home/user/degree-diameter/research/squads/handsoff-37/r3c
L=$1; G=$2; K=$3; S=$4; SEC=$5
P=out/${L}_s${S}
timeout 100 nice -n 10 ./lift3 groups/$G.txt $K $S $SEC $P > $P.log 2>&1
R=$(grep '^END' $P.log)
N=$(head -1 $P.edges 2>/dev/null)
echo -e "$(date -u +%T)\t$L\t$G\tk=$K\tseed=$S\tsecs=$SEC\t$R" | tee -a out/runs.tsv
