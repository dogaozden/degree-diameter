#!/bin/bash
# B8 hunt: random symmetric S on G = Z_P x|_R Z_C (ORBIT "5 2 1", automatic meta scaling alpha), SAMPLES samples.
# haar_sym writes OUT only if a sample has cost 0 and its own full diameter check passes.
# usage: hunt.sh P C R SAMPLES
H=/home/user/degree-diameter/research/structured/haar_sym
D=/home/user/degree-diameter/research/squads/d11D10-r1/B8
unset THREADS
cd "$D" || exit 1
P=$1; C=$2; R=$3; S=$4
OUT="$D/d11D10_meta_${P}_${C}_orb5_B8_s1.txt"
env ORBIT="5 2 1" RANDORB="$S" "$H" 11 10 1 1 8 "$OUT" meta "$P" "$C" "$R" 1
echo "rc=$?"
if [ -s "$OUT" ]; then echo "=== metacheck $OUT"; "$D/metacheck" "$OUT"; echo "metacheck rc=$?"; fi
