#!/bin/bash
# usage: big.sh d D secs seed "k m f" fam p n [VAR=x ...]   (haar_big0 orbit search, 1 thread, log in runs/)
# START=<file> may be passed as VAR to continue from a saved S (.sol.best, or .orb for f = 0)
d=$1; D=$2; secs=$3; seed=$4; orb="$5"; fam=$6; p=$7; n=$8; shift 8
tag="d${d}D${D}_${fam}_${p}_${n}_orb$(echo $orb|tr ' ' '-')_s${seed}w"
cd "$(dirname "$0")"
env "$@" ORBIT="$orb" THREADS=1 ./bin/haar_big0w $d $D $secs $seed 8 runs/$tag.sol $fam $p $n >> runs/$tag.log 2>&1
tail -n 1 runs/$tag.log
