#!/bin/bash
# exh_one.sh FILE.ht REC F TAG [CAP]: exhaustive sdk on ONE record (0-based) and ONE type (f psi-fixed elements) of an
# export_sd.g file (K = $K, default 9; CAP default 6e9; SAMPLE=0, NEAR=25).  Output logs/K$K/exh/TAG_r<REC>_f<F>.out
# (sdk calls the kept record "rec 0"), one line in logs/K$K/exh/summary.txt.
R0="$(cd "$(dirname "$0")/.." && pwd)"; K=${K:-9}; F=$1; REC=$2; FX=$3; TAG=$4; CAP=${5:-6000000000}
T=${TMPDIR:-/tmp}/deep; mkdir -p $T $R0/logs/K$K/exh; G=$T/${TAG}_rec$REC.ht
python3 - "$F" "$REC" "$G" <<'PY'
import sys
lines = open(sys.argv[1]).read().split('\n'); n = int(lines[0].split()[0]); rest = lines[n + 2:]; recs, i = [], 0
while i < len(rest):
    if rest[i].startswith(('ALPHA', 'EXT')):
        k = int(rest[i + 2].split()[1]); recs.append(rest[i:i + 3 + k]); i += 3 + k
    else: i += 1
open(sys.argv[3], 'w').write('\n'.join(lines[:n + 2] + recs[int(sys.argv[2])]) + '\n')
PY
O=$R0/logs/K$K/exh/${TAG}_r${REC}_f$FX.out; t0=$(date +%s)
K=$K TYPES=$FX MAXEV=$CAP MAXEVF=$CAP SAMPLE=0 NEAR=25 EDGES=$R0/cand/exh${K}_${TAG}_r$REC.edges nice -n 5 $R0/src/sdk $G > $O 2>&1
L=$(grep "^TYPE" $O | head -1)
echo "one $TAG rec $REC f $FX tag ${TAG}_r${REC}_f$FX $L secs $(( $(date +%s) - t0 ))" >> $R0/logs/K$K/exh/summary.txt
grep -q "^SOL" $O && echo "HIT exh $TAG rec $REC f $FX K $K" >> $R0/logs/K$K/HITS.txt
rm -f $G
