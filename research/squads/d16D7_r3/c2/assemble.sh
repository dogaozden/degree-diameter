#!/bin/bash
# best_X.txt = the larger valid independent set of {expansion of the quotient best, ktabu polish}, both scored by ogscore
cd /home/user/degree-diameter/research/squads/d16D7_r3/c2
R2=/home/user/degree-diameter/research/squads/d16D7_r2
for g in pts lines; do
  best=exp_$g.txt
  if [ -f polish_$g.sol ]; then
    if python3 $R2/ogscore.py $R2/og_$g.txt polish_$g.sol | grep -q '^VALID'; then
      a=$(grep -c . exp_$g.txt); b=$(grep -c . polish_$g.sol)
      [ "$b" -gt "$a" ] && best=polish_$g.sol
    fi
  fi
  cp $best best_$g.txt
  echo "$g: source=$best"; python3 $R2/ogscore.py $R2/og_$g.txt best_$g.txt
done
