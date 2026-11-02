#!/bin/bash
# randloop.sh TAG MAXBATCH d D fam q n  (env ORBIT AFROB FIXORD THREADS BATCH): RANDORB batches until a cost-0 file exists
TAG=$1; MAXB=$2; shift 2; cd /home/user/degree-diameter/research/frontier/raise-d12/runs
for s in $(seq ${SEED0:-101} $((${SEED0:-101}+MAXB-1))); do
  [ -s $TAG.out ] && break
  RANDORB=${BATCH:-150} timeout 600 /home/user/bin/haar_bigq $1 $2 100 $s 4 $TAG.out $3 $4 $5 2>&1 | grep -E "cost 0|^RANDORB d|fixed gen" >> $TAG.randloop.log
done
echo "done $(date -u +%T)" >> $TAG.randloop.log
