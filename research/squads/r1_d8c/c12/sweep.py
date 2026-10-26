"""c12: smaller deletion sets (prefixes of the seed-1 order of surgery.py, all accepted by its greedy) with hub reps of degree t, both sides.
Usage: python3 sweep.py   (q=3, seed=1 fixed by the exec below)"""
import sys, random
sys.argv = ['x', '3', '1', '1']
src = open('/home/user/degree-diameter/research/squads/r1_d8c/c12/surgery.py').read().split('order = list(range(len(cands)))')[0]
exec(src)
order = list(range(len(cands))); random.Random(seed).shuffle(order)
for k in (10, 20, 45, 90):
    dels = set(order[:k])
    dl = sorted(dels)
    fp = [cands[c][0] for c in dl]; fl = [cands[c][1] for c in dl]
    for t in (q + 3, 3):
        hubs = []
        for typ, pool in (('A', fp), ('B', fl)):
            pool = list(dict.fromkeys(pool))
            hubs += [(typ, pool[j:j+t]) for j in range(0, len(pool) - t + 1, t)]
        if not hubs: continue
        good_nohub, _ = ok(dels, (), tag='nh')
        good, bad = ok(dels, hubs, tag='hb')
        print(f'k={k} t={t} nohub_valid={good_nohub} hubreps={len(hubs)} vertices_gained={10*len(hubs)} valid={good} bad={bad}', flush=True)
