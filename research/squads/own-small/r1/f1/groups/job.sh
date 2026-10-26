#!/bin/bash
# one gated job: export group tables (PrintTo format) for the card's 2+2 orders, convert to .bin, then screen
# every non-abelian group (smallest abelianization first) with one 2+2 base (alternating t1/t2), 2 s anneal, d=4 D=8.
G=/home/user/degree-diameter/research/squads/own-small/r1/f1/groups
F=/home/user/degree-diameter/research/squads/own-small/r1/f1
FL=/home/user/degree-diameter/research/squads/own-small/tools/bin/flift
export T0=$(date +%s)
for N in 547 548 549 550 551 552 553 554 555 556 557 558 559 561 562 563 564 565; do
  echo "lo:=$N;; hi:=$N;; dir:=\"$G\";; Read(\"$G/export2.g\");" > $G/e_$N.g
  [ $(( $(date +%s) - T0 )) -gt 60 ] && break
  timeout 60 gap -q -o 2g $G/e_$N.g < /dev/null > /dev/null 2>&1
done
echo "EXPORT_DONE $(date +%T)"
python3 -I $G/convert.py $G/m*.lst
echo "CONVERT_DONE $(date +%T)"
python3 -I - <<'PY'
import glob, os
G = "/home/user/degree-diameter/research/squads/own-small/r1/f1/groups"
rows = []
for fn in glob.glob(G + "/info_*.txt"):
    for line in open(fn):
        p = line.split()
        if len(p) < 4: continue
        N, gid, ab, isab = int(p[0]), int(p[1]), int(p[2]), p[3]
        if isab == "true": continue
        b = f"{G}/g{N}_{gid}.bin"
        if os.path.exists(b): rows.append((ab, N, gid, b))
rows.sort()
with open(G + "/list22.txt", "w") as o:
    for i, (ab, N, gid, b) in enumerate(rows):
        base = "/home/user/degree-diameter/research/squads/own-small/r1/f1/bases/b22_t1.txt" if i % 2 == 0 else "/home/user/degree-diameter/research/squads/own-small/r1/f1/bases/b22_t2.txt"
        o.write(f"{base} {b} N{N}_g{gid}_ab{ab}_t{1 if i%2==0 else 2}\n")
print("list", len(rows))
PY
cd $F && ./screen.sh $F/out_screen22.txt 2 170 1 $G/list22.txt
echo "SCREEN_DONE $(date +%T)"
