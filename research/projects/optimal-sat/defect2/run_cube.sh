#!/bin/bash
# One certified cube job for the k = 11 A-only instance (or any k): builds base CNF + cube units, solves with CaDiCaL
# while lrat-check verifies the streamed LRAT proof (nothing large is stored), writes one log line.
# usage: run_cube.sh cubes.json index outdir        (env: CADICAL, LRATCHECK; python3 with python-sat)
#   cubes.json from:  python3 cube_list.py 11 2 cubes.json --sym --nf2 --ntt --alltr
set -u
here=$(cd "$(dirname "$0")" && pwd)
cubes=$1; i=$2; out=$3; mkdir -p $out
CADICAL=${CADICAL:-cadical}; LRATCHECK=${LRATCHECK:-lrat-check}
cnf=$out/cube$i.cnf
python3 - "$cubes" "$i" "$cnf" "$here" <<'PY'
import sys, json
sys.path.insert(0, sys.argv[4])
from enc_quot import build
d = json.load(open(sys.argv[1])); i = int(sys.argv[2]); o = d['opts']
cnf, pool, a = build(d['k'], sym='--sym' in o, nf2='--nf2' in o, ntt='--ntt' in o, alltr='--alltr' in o,
                     signs='--signs' in o)
assert [abs(l) for l in d['surviving'][i]] == d['cube_vars']
for l in d['surviving'][i]: cnf.append([l])
cnf.to_file(sys.argv[3])
PY
fifo=$out/cube$i.fifo; rm -f $fifo; mkfifo $fifo
"$LRATCHECK" $cnf < $fifo > $out/cube$i.check 2>&1 &
chk=$!
s=$(date +%s)
"$CADICAL" -q --lrat --binary=false $cnf $fifo > $out/cube$i.solve 2>&1; rc=$?
wait $chk; crc=$?
e=$(date +%s)
res=$(grep '^s ' $out/cube$i.solve | tr -d '\r')
ver=$(grep -o -E '(NOT )?VERIFIED' $out/cube$i.check | head -1)
echo "cube $i sha256 $(sha256sum $cnf | cut -c1-16) cadical_rc $rc '$res' lratcheck_rc $crc $ver wall $((e - s)) s" | tee -a $out/cubes.log
rm -f $fifo $cnf
