#!/bin/bash
# resumable screen: runs queue entries from progress.txt until ~70 s elapsed; appends to screen.log
cd /home/user/degree-diameter/research/squads/deep-65/round1/h2
start=$(date +%s)
pos=$(cat progress.txt 2>/dev/null || echo 0)
mapfile -t Q < queue.txt
n=${#Q[@]}
while [ "$pos" -lt "$n" ]; do
  now=$(date +%s); if [ $((now-start)) -gt 78 ]; then break; fi
  g=${Q[$pos]}
  out=$(TYPE="1,6,6|1,6,6" N="4,1,1,1,0,0,1,0,0" SECS=4 SEED=1 MAXCOMB=6 timeout 40 nice -n 10 ./mcos groups/sg_$g.txt 2>/dev/null)
  echo "$out" >> screen_full.log
  best=$(echo "$out" | grep '^COMB' | sed -n 's/.*best \(-*[0-9]*\).*/\1/p' | awk '$1>=0' | sort -n | head -1)
  nm=$(cat groups/sg_$g.name | sed 's/ abelian.*//')
  echo "$g [$nm] best=${best:-NA} $(echo "$out" | grep -c '^COMB') combos" >> screen.log
  pos=$((pos+1)); echo $pos > progress.txt
done
echo "progress $pos of $n"
