#!/bin/bash
# Full family_score (psl, q in [23,113]) for the 8 best integer families per Delta and 4 random baselines per Delta.
C=/home/user/degree-diameter/research/squads/thmfam-r1/c3
H=/home/user/degree-diameter/research/theorems/haar_families
cd $H
python3 - "$C" "$H" <<'PY' > $C/cmds.txt
import json, sys
C = sys.argv[1]; H = sys.argv[2]
top = json.load(open(C + '/top8.json'))
for D in ['8', '10']:
    for i, (sm, e29, e41, e53, toks) in enumerate(top[D]):
        print(f"INT {D} {i} " + f"python3 {C}/gen_int.py {{q}} {{m}} {toks}")
    for s in range(1, 5):
        if D == '8': print(f"BASE {D} {s} python3 {H}/gen_random_orb.py {{q}} 2 2 {s}")
        else: print(f"BASE {D} {s} python3 {H}/gen_random_orb.py {{q}} 1 3 {s}")
PY
while read kind D idx rest; do
  if [ "$kind" = INT ]; then name="int_D${D}_${idx}"; else name="base_D${D}_s${idx}"; fi
  gen="$rest"
  nice -n 10 timeout 900 python3 family_score.py --gen "$gen" --group psl --qrange 23 113 --json > $C/full_${name}.json 2> $C/full_${name}.err
  echo "$name $(python3 -c "import json,sys; print(json.load(open('$C/full_${name}.json'))['summary']['mean_excess'])" 2>/dev/null)" >> $C/full_summary.txt
done < $C/cmds.txt
echo ALLDONE >> $C/full_summary.txt
