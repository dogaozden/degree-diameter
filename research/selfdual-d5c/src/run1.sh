#!/bin/bash
# run1.sh KIND ARGS...: one fsd run (env K, SECS, TYPES, SEED, DEEP, NB, STALL, MAXSOL, REC passed through), full output in
# logs/K$K/out/<tag>.out, one summary line in logs/K$K/runs.txt, edge list of the first solution in cand/.
R0="$(cd "$(dirname "$0")/.." && pwd)"
KV=${K:-12}; L=$R0/logs/K$KV; mkdir -p $L/out $R0/cand
tag=$(echo "$@" | tr ' ' '_')${TAG:+_$TAG}
O=$L/out/$tag.out
t0=$(date +%s)
K=$KV EDGES=$R0/cand/K${KV}_$tag.edges timeout ${TMAX:-36000} nice -n ${NICE:-5} $R0/src/fsd "$@" > $O 2>&1
rc=$?
n=$(awk '/^GROUP/{for(i=1;i<NF;i++) if($i=="n") print $(i+1)}' $O)
nrec=$(awk '/^RECORDS/{print $2}' $O)
best=$(grep "^TABU" $O | awk '{for(i=1;i<NF;i++) if ($i=="best") print $(i+1)}' | sort -n | head -1)
sols=$(grep -c "^SOL" $O)
echo "$tag n $n K $KV records $nrec types $(grep -c '^TABU' $O) best ${best:-NA} sols $sols rc $rc secs $(( $(date +%s) - t0 )) seed ${SEED:-0} secs_per_type ${SECS:-10}" >> $L/runs.txt
[ "$sols" -gt 0 ] && echo "HIT $tag n $n K $KV sols $sols" >> $L/HITS.txt
exit 0
