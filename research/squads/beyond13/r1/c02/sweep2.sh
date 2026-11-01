#!/bin/bash
# c02: sampled metacyclic sweep at D=14, descending N, k in {2,3,4,5,6,8}; apsp-check every hit.
cd /home/user/degree-diameter/research/squads/beyond13/r1/c02
B=/home/user/degree-diameter/research/frontier/beyond13
mkdir -p hits

while read N m k r; do
  out=$(nice -n 10 timeout 60 ./exh3m $m $k $r 14 hits/h_${m}_${k}_${r} 20 200000 1 2>&1 | grep -E "RESULT|GROUP" | tr '\n' ' ')
  echo "meta $m $k $r N=$N | $out"
  case "$out" in
    *"RESULT FOUND"*)
      f=hits/h_${m}_${k}_${r}_n$((2*N)).edges
      v=$(nice -n 10 timeout 100 $B/bin/apsp $f 3 14 2>&1 | tail -1)
      echo "APSP meta $m $k $r n=$((2*N)) : $v" ;;
  esac
done < specs_sel2.txt
echo DONE
