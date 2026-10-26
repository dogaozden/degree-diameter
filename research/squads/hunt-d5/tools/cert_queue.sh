#!/bin/bash
# cert_queue.sh d OUTLOG "N1 I1" "N2 I2" ... : exact Haar search (haar5 cert) group by group (hunt-d5)
T=$(dirname $0); d=$1; log=$2; shift 2; mkdir -p $T/../tables/cert
for g in "$@"; do set -- $g; n=$1; i=$2; f=$T/../tables/cert/g${n}_$i.bin; o=$T/../tables/cert/orb${n}_$i.txt
  [ -f $f ] || python3 $T/gapgroup.py table $n $i $f
  [ -s $o ] || python3 $T/gapgroup.py orbits $n $i full > $o
  $T/haar5 cert $f $d $o > $T/../tables/cert/cert${d}_${n}_$i.log 2>&1
  echo "$n $i :: $(grep -c '^cost 0' $T/../tables/cert/cert${d}_${n}_$i.log) solutions :: $(tail -n 1 $T/../tables/cert/cert${d}_${n}_$i.log)" >> $log
done
echo DONE >> $log
