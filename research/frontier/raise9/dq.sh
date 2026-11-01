#!/bin/bash
# dq.sh JOBFILE: director queue for job raise-d9. Each line: d D secs seed K fam p n "k m f" threads [START=file]
# Runs haar_big0 (research/frontier/beyond11/bin) search only; finds are checked separately (chk.sh).
# Lines are read one at a time from JOBFILE (so it can be edited while the queue runs); done lines move to JOBFILE.done.
QF=$(realpath "$1"); cd "$(dirname "$0")"; B=../beyond11/bin; mkdir -p runs
while true; do
  line=$(grep -v "^#" "$QF" | grep . | head -1); [ -z "$line" ] && break
  grep -vxF "$line" "$QF" > "$QF.tmp"; mv "$QF.tmp" "$QF"; echo "$line" >> "$QF.done"
  eval set -- $line
  d=$1 D=$2 secs=$3 seed=$4 K=$5 fam=$6 p=$7 n=$8 orb=$9 th=${10}; st=${11}
  set -- $orb; tag=d${d}D${D}_${fam}_${p}_${n}_orb$1-$2-$3_s${seed}
  echo "$(date -u +%T) start $tag ($secs s, $th threads) $st"
  nice -n ${DNICE:-3} env $st ORBIT="$orb" THREADS=$th $B/haar_big0 $d $D $secs $seed $K runs/$tag.out $fam $p $n > runs/$tag.log 2>&1
  echo "$(date -u +%T) $(grep RESULT runs/$tag.log | tail -1)"
done
echo "QUEUE $QF DONE $(date -u +%T)"
