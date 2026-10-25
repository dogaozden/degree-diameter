#!/bin/bash
# Certified solve without storing the proof: CaDiCaL writes an ASCII LRAT proof into a named pipe and lrat-check
# (github.com/marijnheule/drat-trim, lrat-check.c) verifies it while it is produced.
# usage: stream_cert.sh file.cnf outprefix      (env CADICAL, LRATCHECK)
set -u
cnf=$1; out=$2
CADICAL=${CADICAL:-cadical}; LRATCHECK=${LRATCHECK:-lrat-check}
fifo=$out.fifo; rm -f $fifo; mkfifo $fifo
echo "cnf $cnf sha256 $(sha256sum $cnf | cut -d' ' -f1)" > $out.log
echo "start $(date -u)" >> $out.log
"$LRATCHECK" "$cnf" < $fifo > $out.check 2>&1 &
chk=$!
s=$(date +%s)
"$CADICAL" -q --lrat --binary=false "$cnf" $fifo > $out.solve 2>&1
rc=$?
wait $chk; crc=$?
e=$(date +%s)
echo "cadical exit $rc ($(grep '^s ' $out.solve)) wall $((e - s)) s" >> $out.log
echo "lrat-check exit $crc: $(grep -E 'VERIFIED|NOT VERIFIED' $out.check | tr -d '\r' | tail -1)" >> $out.log
echo "end $(date -u)" >> $out.log
rm -f $fifo
