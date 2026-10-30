#!/bin/bash
# kopt K=2 (exact 2-opt to cost 0) on the 2+2 lift of every side-A cover of SmallGroup(360,53) (run from research/s65/haar2lift)
i=0
while read S; do i=$((i+1))
  python3 ../tools/haar2lift.py ../haar/h360_53/hx_360_53.txt "$S" a$i.base N53.txt > /dev/null
  python3 ../tools/normlift.py a$i.base N53.txt a${i}n.base
  c=$(D=5 EVAL=1 ../tools/vl a${i}n.base N53.txt 2>&1 | tail -1 | awk '{print $3}')
  nice -n 5 ../tools/kopt a${i}n.base N53.txt 2 5 > a$i.k2 2> a$i.k2err
  echo "$i S $S liftcost $c k2found $(grep -c '^SOL' a$i.k2)" >> k2_summary.txt
done < asides53.txt
