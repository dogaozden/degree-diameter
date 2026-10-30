#!/bin/bash
# driver.sh: export odd-order groups (no involutions) of order 1802-1999 and run the bi-coset search on each.
cd /home/user/degree-diameter/research/squads/d75-r1/c7
export TMPDIR=$PWD/tmp
for spec in "1809 3" "1809 7" "1863 4" "1875 5" "1911 7" "1971 6" "1953 5" "1881 3" "1917 2" "1827 4"; do
  set -- $spec; n=$1; i=$2
  f=ht/g${n}_${i}.ht
  timeout 300 gap -q -c "G:=SmallGroup($n,$i);; NOAUT:=true;; OUT:=\"$f\";;" /home/user/degree-diameter/research/d75-raise/src/export.g >/dev/null 2>&1
  res=$(timeout 200 nice -n 10 python3 bic.py $f 30 1 tmp/g${n}_${i}.edges 2>&1 | tail -2 | tr '\n' ' ')
  echo "$n $i $res" >> driver.log
  if echo "$res" | grep -q VALID; then cp tmp/g${n}_${i}.edges hit_${n}_${i}.edges; fi
  rm -f $f
done
echo FINISHED >> driver.log
