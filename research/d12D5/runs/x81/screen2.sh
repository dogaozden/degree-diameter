#!/bin/bash
cd /home/user/degree-diameter/research/d12D5
i=0
while read V; do i=$((i+1))
  for f in $(cat runs/x81/var2_list.txt); do c=$(DIAGBT=1 INIT_ECHART=$f INIT_VOLT=$V ./mlift_ejoint2 base_k33m.txt tables/z27.txt 0 1 | head -1 | awk '{print $3}'); echo "$c v$i $f"; done
done < runs/x81/fake_volts.txt | sort -n > runs/x81/screen2_all.txt
