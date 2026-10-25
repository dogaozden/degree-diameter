#!/bin/bash
# grid over group patterns, side and port maps for q=3 (alpha=3)
cd /home/user/degree-diameter/research/squads/d12D8_r2/c1
for pat in aaa aab aba baa abb bab bba bbb; do
 for side in P L; do
  for maps in id rand:1 both:1 copy:1; do
    f=grid/q3_${pat}_${side}_$(echo $maps | tr ':' '_').txt
    python3 build.py build 3 $pat $side $maps $f > /dev/null
    d=$(nice -n 10 timeout 600 /home/user/degree-diameter/research/d12D8/r2/apsp $f 12 8 2>&1 | grep -o 'diameter=[0-9]*' | head -1)
    echo "$pat $side $maps $d"
    rm -f $f
  done
 done
done
