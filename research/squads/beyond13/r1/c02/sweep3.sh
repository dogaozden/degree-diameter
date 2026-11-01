#!/bin/bash
# c02: sampled (300k random pairs) nonabelian metacyclic sweep at D=14, N in [1500,1900], descending N.
cd /home/user/degree-diameter/research/squads/beyond13/r1/c02
B=/home/user/degree-diameter/research/frontier/beyond13
while read N m k r; do
  out=$(nice -n 10 timeout 80 ./exh3m $m $k $r 14 hits/s3_${m}_${k}_${r} 60 300000 7 2>&1 | grep -E "RESULT|GROUP" | tr '\n' ' ')
  echo "meta $m $k $r N=$N | $out"
  case "$out" in
    *"RESULT FOUND"*)
      f=hits/s3_${m}_${k}_${r}_n$((2*N)).edges
      v=$(nice -n 10 timeout 100 $B/bin/apsp $f 3 14 2>&1 | tail -1)
      echo "APSP meta $m $k $r n=$((2*N)) : $v" ;;
  esac
done < specs_sel3.txt
echo DONE
