#!/bin/bash
# c3 driver: build + export each C_m : H group (GAP), then sdtabu2 screen (K=9, types 1,3,5, 1 s per type).
cd /home/user/degree-diameter/research/squads/sd5b-r1/c3
export TMPDIR=/home/user/degree-diameter/research/squads/sd5b-r1/c3/tmp
SPECS='[[195,"QuaternionGroup(8)",2,"Q8"],[153,"DihedralGroup(10)",2,"D5"],[155,"DihedralGroup(10)",2,"D5"],[111,"DihedralGroup(14)",2,"D7"],[95,"DirectProduct(CyclicGroup(4),CyclicGroup(4))",2,"C4C4"],[169,"DirectProduct(CyclicGroup(3),CyclicGroup(3))",2,"C3C3"],[135,"DicyclicGroup(12)",2,"Dic3"],[65,"DirectProduct(CyclicGroup(3),QuaternionGroup(8))",2,"C3Q8"],[85,"DihedralGroup(18)",2,"D9"],[77,"DirectProduct(DihedralGroup(10),CyclicGroup(2))",2,"D5C2"],[171,"DirectProduct(CyclicGroup(3),CyclicGroup(3))",2,"C3C3b"]]'
timeout 900 nice -n 15 gap -q -c "SPECS:=$SPECS;;" run_spec.g < /dev/null > build.log 2>&1
grep -v "Syntax\|^ \|^\s*\^\|export_sd\|^/" build.log | grep -E "BUILT|EXPORTED|Error" 
while read -r N ID m tagname tag tup; do
  f=x_${tag}.ht
  [ -s "$f" ] || { echo "MISSING $f"; continue; }
  timeout 300 nice -n 15 env K=9 SECS=1 NB=48 STALL=1000 TYPES=1,3,5 NOID=1 SEED=1 EDGES=/home/user/degree-diameter/research/squads/sd5b-r1/c3/sol_${tag}.edges \
    /home/user/degree-diameter/research/selfdual-d5/src/sdtabu2 $f all > out_${tag}.out 2>&1
  echo "SCREENED $tag N=$N ID=$ID $(grep -c '^TABU' out_${tag}.out) lines; best: $(grep '^TABU' out_${tag}.out | sed -E 's/.*best ([0-9]+).*/\1/' | sort -n | head -1)"
done < manifest.txt
echo DRIVER_DONE
