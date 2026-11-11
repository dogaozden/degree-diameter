#!/bin/bash
# usage: run.sh d D secs seed "k m f" fam p n [VAR=x ...]
# runs haar_sym (orbit search) single-threaded; log runs/<tag>.log, solution runs/<tag>.sol
d=$1; D=$2; secs=$3; seed=$4; orb="$5"; fam=$6; p=$7; n=$8; shift 8
tag="d${d}D${D}_${fam}_${p}_${n}_orb$(echo $orb|tr ' ' '-')_s${seed}"
for v in "$@"; do tag="${tag}_${v//=/}"; done
cd "$(dirname "$0")"
env "$@" ORBIT="$orb" THREADS=1 nice -n 5 ./bin/haar_sym $d $D $secs $seed 8 runs/$tag.sol $fam $p $n > runs/$tag.log 2>&1
grep -E "^RESULT" runs/$tag.log | tail -1
