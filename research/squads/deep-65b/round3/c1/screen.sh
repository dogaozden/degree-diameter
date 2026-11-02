#!/bin/bash
# screen.sh TAG TYPE NSPEC ORDER SECS RANDC IDS...   (run from round3/c1; one mcos run per group, seed 1)
cd /home/user/degree-diameter/research/squads/deep-65b/round3/c1 || exit 1
TAG=$1; TYPE=$2; NSPEC=$3; ORD=$4; SECS=$5; RANDC=$6; shift 6
START=$SECONDS
for i in "$@"; do
  el=$((SECONDS-START))
  if [ $el -ge 70 ]; then echo "# stopped before id $i (elapsed $el s)"; break; fi
  to=$((100-el))
  f=tabs/sg_${ORD}_${i}.tab
  name=$(cut -d' ' -f1-40 tabs/sg_${ORD}_${i}.name | tr -d '\n')
  if grep -q 'abelian=true' tabs/sg_${ORD}_${i}.name; then echo "$TAG ord=$ORD id=$i SKIP abelian"; continue; fi
  out=$(timeout $to nice -n 15 env TYPE="$TYPE" N="$NSPEC" SECS=$SECS RANDCOMB=$RANDC SEED=1 EDGES=edges/${TAG}_${ORD}_${i}.edges ./mcos $f 2>/dev/null)
  rc=$?
  best=$(echo "$out" | awk '/^COMB/{for(j=1;j<=NF;j++) if($j=="best"){b=$(j+1); if(b+0>=0 && (min==""||b+0<min+0))min=b}} END{print (min==""?"NA":min)}')
  nc=$(echo "$out" | grep -c '^COMB')
  nsol=$(echo "$out" | grep -c '^SOL')
  line="$TAG ord=$ORD id=$i [$name] combos=$nc best=$best sol=$nsol rc=$rc el=$((SECONDS-START))"
  echo "$line"
  echo "$line" >> results_${TAG}.txt
  if [ "$best" = "0" ]; then echo "ZERO $TAG $ORD $i"; timeout 30 nice -n 15 ../../shared/score65 edges/${TAG}_${ORD}_${i}.edges | tail -1; fi
done
echo "# batch done elapsed $((SECONDS-START)) s"
