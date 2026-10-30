#!/bin/bash
# usage: mktable.sh > table.txt  (one line per group that has a log)
C4=/home/user/degree-diameter/research/squads/s65r4/c4
L=/home/user/degree-diameter/research/s65/haar/next_361_380.txt
echo "order_id | structure | |Aut| | pairs covered (a..b of total) | sets | valid | minA | min Bunc"
cd $C4
for log in h*.log; do
  id=${log#h}; id=${id%.log}; o=${id%_*}; i=${id#*_}
  line=$(grep -E "^$id " $L || true)
  aut=$(echo "$line" | awk '{print $5}'); st=$(echo "$line" | sed -E 's/^[^ ]+ inv [0-9]+ aut [0-9]+ //')
  total=$(grep -oE 'pair classes=[0-9]+' $log | head -1 | cut -d= -f2)
  lastp=$(grep -E '^PAIR ' $log | tail -1 | awk '{print $2}')
  done_line=$(grep '^DONE' $log || true)
  if [ -n "$done_line" ]; then
    rng=$(echo "$done_line" | grep -oE 'pairs=[0-9]+\.\.[0-9]+' | cut -d= -f2)
    cov="$rng of $total"
    sets=$(echo "$done_line" | grep -oE 'sets=[0-9]+' | cut -d= -f2)
    val=$(echo "$done_line" | grep -oE 'valid=[0-9]+' | cut -d= -f2)
    mina=$(echo "$done_line" | grep -oE 'minA=[0-9]+' | cut -d= -f2)
    status=""
  else
    cov="0..${lastp:-?} of $total (STOPPED by time box, last PAIR $lastp)"
    sets=$(grep -h '^PAIR ' $log | awk -F'sets=' '{split($2,a," "); s+=a[1]} END{print s+0}')
    val=$(grep -c '^VALID' $log)
    mina=$(grep '^PAIR ' $log | grep -oE 'minA=[0-9]+' | cut -d= -f2 | sort -n | head -1)
  fi
  bunc=$(grep -oE 'Bunc=[0-9]+' $log | cut -d= -f2 | sort -n | head -1)
  echo "$id | $st | $aut | $cov | $sets | $val | ${mina:--} | ${bunc:--}"
done
