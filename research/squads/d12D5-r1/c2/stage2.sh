#!/bin/bash
# real joint per-edge annealer on one (base, group, seed): usage stage2.sh BASENAME GROUPFILE SEED
D=/home/user/degree-diameter/research/d12D5
C=/home/user/degree-diameter/research/squads/d12D5-r1/c2
cd $C
export THREADS=1
b=$1; g=$2; s=$3; tag=${b}_${g}_s${s}
mkdir -p runs
INIT_CHART=$D/graphs/d12D5_n9720_k33m_z20_chart.txt timeout 500 nice -n 10 $D/mlift_ejoint $D/bases4/$b.txt $g.txt 300 $s 2 0.8 runs/$tag > logs/ej_$tag.log 2>&1
tail -1 logs/ej_$tag.log | cut -c1-200
