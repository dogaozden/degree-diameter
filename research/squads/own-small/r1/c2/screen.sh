#!/bin/bash
# screen: every non-abelian group x every 4+4 base, 0.5 s flift anneal, D=10, d=3
cd /home/user/degree-diameter/research/squads/own-small/r1/c2
T=/home/user/degree-diameter/research/squads/own-small/tools
: > screen.tsv
for g in $(cat nonabel.txt); do
  for b in 0 1 2 3 4 5; do
    r=$($T/bin/flift bases/b4_$b.txt groups/bin/$g.bin 3 10 0.5 1 2>/dev/null | grep RESULT)
    best=$(echo "$r" | sed -n 's/.*best=\([0-9-]*\).*/\1/p')
    echo -e "$g\t$b\t${best:-NA}" >> screen.tsv
  done
done
