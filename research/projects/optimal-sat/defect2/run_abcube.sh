#!/bin/bash
# One certified degree-sequence cube (see abcube.py, ablist.py): base CNF + cube clauses, CaDiCaL with an ASCII LRAT
# proof streamed into lrat-check (nothing large stored). One log line per cube.
# usage: run_abcube.sh base.cnf 'a1,..,a9/b1,..,b9' outdir      (env CADICAL, LRATCHECK)
set -u
here=$(cd "$(dirname "$0")" && pwd)
base=$1; spec=$2; out=$3; mkdir -p $out
CADICAL=${CADICAL:-cadical}; LRATCHECK=${LRATCHECK:-lrat-check}
tag=$(echo "$spec" | tr ',/' '._')
cnf=$out/$tag.cnf
t=$(echo "$spec" | cut -d/ -f1 | tr ',' '+' | bc)
mt=""; [ "$t" -le "${MAXT_BELOW:-3}" ] && mt="--maxt"     # cheap and very effective for small t (NOTES item 12)
python3 $here/abcube.py cube $base "$spec" $cnf $mt
fifo=$out/$tag.fifo; rm -f $fifo; mkfifo $fifo
"$LRATCHECK" $cnf < $fifo > $out/$tag.check 2>&1 &
chk=$!
s=$(date +%s)
timeout ${CUBE_TIMEOUT:-3600} "$CADICAL" -q --lrat --binary=false $cnf $fifo > $out/$tag.solve 2>&1; rc=$?
wait $chk; crc=$?
e=$(date +%s)
res=$(grep '^s ' $out/$tag.solve | tr -d '\r')
ver=$(grep -o -E '(NOT )?VERIFIED' $out/$tag.check | head -1)
echo "$spec t=$t $mt cadical_rc $rc '$res' lratcheck_rc $crc $ver wall $((e - s)) s" | tee -a $out/abcubes.log
rm -f $fifo $cnf $out/$tag.check $out/$tag.solve
