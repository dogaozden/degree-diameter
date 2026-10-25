#!/bin/bash
# t2cell.sh NAME GHFILE j DELTA SEED [THREADS] [FLAGSFILE]
# DGQ polygon cover of the hexagon in GHFILE with j matchings over Z_{2j+1}, plus type-2 units (t2design.c) and a
# random hub graph of degree DELTA - (2j+1). QUICK=1 checks only unit endpoints and new vertices (search mode). Writes cells2/NAME.{state,units,x,uhcheck.txt} and prints n.
# With FLAGSFILE (from pack.c) the same flags are used on every matching (BOTH=1); otherwise a random scan packing.
NAME=$1; GH=$2; J=$3; DELTA=$4; SEED=${5:-1}; TH=${6:-1}; FL=$7
M=$((2*J+1)); P=$(head -1 $GH | cut -d' ' -f1); DH=$((DELTA - M))
mkdir -p cells2; OUT=cells2/$NAME
python3 mkunits.py $GH $J $SEED $OUT.rand.state /dev/null 2>/dev/null || exit 1
if [ -n "$FL" ]; then FLAGS=$FL BOTH=1 ./t2design $GH $OUT.rand.state $J 10000000 $OUT.state $OUT.units $SEED 2> $OUT.t2.log
else SCAN=1 ./t2design $GH $OUT.rand.state $J 10000000 $OUT.state $OUT.units $SEED 2> $OUT.t2.log; fi
NU=$(wc -l < $OUT.units)
python3 randhub.py $NU $DH $SEED > $OUT.x 2> $OUT.hub.log || exit 1
if [ -n "$QUICK" ]; then export ONLYUNITS=1; fi
./uhcheck $GH $OUT.state $OUT.units $OUT.x 7 $TH > $OUT.uhcheck.txt 2> $OUT.uhcheck.log
echo "$NAME: q=$(head -1 $GH | cut -d' ' -f2) j=$J m=$M Delta=$DELTA units=$NU n=$((2*P*M + 2*NU)) $(grep -oE 'pairs beyond D = [0-9]+' $OUT.uhcheck.txt) $(cat $OUT.hub.log)"
