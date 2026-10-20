import json, random, sys
from pathlib import Path
sys.path.insert(0, '.')
from delorme_q5 import setup
P, lines, N, S, through, adj = setup()
Sset=set(S); v=S[0]
onS=set(p for s in S for p in lines[s])
vlines=set(k for p in lines[v] for k in through[p])
blocked=set(p for k in vlines for p in lines[k])-onS
cand=[k for k in range(len(lines)) if k not in Sset and k not in vlines and not any(p in blocked for p in lines[k])]
random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 0)
random.shuffle(cand)
used=set(); W=[]
for k in cand:
    pts=[p for p in lines[k] if p not in onS]
    if not any(p in used for p in pts):
        W.append(k); used.update(pts)
print(len(cand), 'greedy', len(W))
Path('runs/whiskers_q5_greedy.json').write_text(json.dumps({'whiskers':W}))
