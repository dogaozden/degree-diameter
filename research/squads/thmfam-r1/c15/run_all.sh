#!/bin/bash
# c15 experiments. Output: one line per run "TAG | mean_excess n_q Delta | vs_table | connected flags"
FS=/home/user/degree-diameter/research/theorems/haar_families/family_score.py
G=/home/user/degree-diameter/research/squads/thmfam-r1/c15/gen_c15.py
R=/home/user/degree-diameter/research/theorems/haar_families/gen_random_orb.py
Q5=29,31,41,59,61,71,79,89,101,109
Q6=23,37,47,59,61,71,73,83,97,107,109
run(){ # tag qs gen
  out=$(nice -n 10 timeout 900 python3 $FS --gen "$3" --group psl --qs $2 --json 2>&1)
  python3 - "$1" "$out" << 'PY'
import sys, json
tag, out = sys.argv[1], sys.argv[2]
try:
    d = json.loads(out); s = d['summary']; rows = d['rows']
    conn = ''.join('y' if r.get('connected') == 'yes' else 'n' for r in rows if 'excess' in r)
    print(f"{tag} | mean_excess={s['mean_excess']} n_q={s['n_q']} Delta={s['Delta']} | vs_table={ {k:v['vs_table'] for k,v in s['best'].items()} } | connected={conn} | excess={[r.get('excess') for r in rows if 'excess' in r]}", flush=True)
except Exception as e:
    print(f"{tag} | FAILED {e} {out[-300:]}", flush=True)
PY
}
echo "### k=5 uniform, shape 1 (Delta 6)"
for x in u b a c; do run "k5 u1 x=$x" $Q5 "python3 $G {q} 5 1 $x"; done
echo "### k=5 uniform, shape 2 (Delta 10)"
for p in "u b" "u a" "b c" "a c"; do run "k5 u2 x,y=$p" $Q5 "python3 $G {q} 5 2 $p"; done
echo "### k=5 random, shape 1 (Delta 6)"
for s in 1 2 3; do run "k5 r1 seed=$s" $Q5 "python3 $G {q} 5 1 r --seed $s"; done
echo "### k=5 random, shape 2 (Delta 10)"
for s in 1 2 3; do run "k5 r2 seed=$s" $Q5 "python3 $G {q} 5 2 r r --seed $s"; done
echo "### k=3 random baselines on Q5 (Delta 6, 7, 10)"
for s in 1 2 3; do run "k3 D6 seed=$s" $Q5 "python3 $R {q} 0 2 $s"; done
for s in 1 2 3; do run "k3 D10 seed=$s" $Q5 "python3 $R {q} 1 3 $s"; done
echo "### k=6 uniform, shape 1 (Delta 7)"
for x in u b a c; do run "k6 u1 x=$x" $Q6 "python3 $G {q} 6 1 $x"; done
echo "### k=6 uniform, shape 2 (Delta 12)"
for p in "u b" "u a" "b c" "a c"; do run "k6 u2 x,y=$p" $Q6 "python3 $G {q} 6 2 $p"; done
echo "### k=6 random, shape 1 (Delta 7)"
for s in 1 2 3; do run "k6 r1 seed=$s" $Q6 "python3 $G {q} 6 1 r --seed $s"; done
echo "### k=6 random, shape 2 (Delta 12)"
for s in 1 2 3; do run "k6 r2 seed=$s" $Q6 "python3 $G {q} 6 2 r r --seed $s"; done
echo "### k=3 random baselines on Q6 (Delta 6, 7, 12)"
for s in 1 2 3; do run "k3 D6 seed=$s" $Q6 "python3 $R {q} 0 2 $s"; done
for s in 1 2 3; do run "k3 D7 seed=$s" $Q6 "python3 $R {q} 1 2 $s"; done
for s in 1 2; do run "k3 D12 seed=$s" $Q6 "python3 $R {q} 0 4 $s"; done
echo "DONE"
