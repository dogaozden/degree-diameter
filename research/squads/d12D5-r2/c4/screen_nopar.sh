#!/bin/bash
# FAKE floor over all voltage tuples INCLUDING equal volts on parallel edges (multigraph controllers). One run at a time.
cd /home/user/degree-diameter/research/squads/d12D5-r2/c4
OUT=screen/nopar_fake.txt
: > $OUT
for t in tables/*.txt tables2/*.txt; do
  name=$(echo $t | sed 's#/#_#; s#\.txt##')
  r=$(NOPAR=1 EXH=1 FAKE=1 DIAGBT=1 timeout 60 nice -n 10 ./mlift_exh2 base_k1.txt $t 1 1 2.0 1.0 | sed -n 's/.*min_cost=\([0-9]*\) count_at_min=\([0-9]*\).*volt=\(.*\)/\1 \2 \3/p')
  echo "$name $r" >> $OUT
done
echo DONE >> $OUT
