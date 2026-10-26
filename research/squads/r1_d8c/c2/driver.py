"""Enumerate flag-rule configs (no duplicate edges, degree q+3 = 6), score each by exact gcheck over level-0 sources
(exact because the design is Z5-invariant over levels). Log to results.jsonl."""
import sys, random, subprocess, json, itertools, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import flagrule as fr

GC = '/home/user/degree-diameter/research/squads/cells/d10D8_work/gcheck'
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
TRIALS = int(sys.argv[2]) if len(sys.argv) > 2 else 200
perms = list(itertools.permutations(range(4)))
os.makedirs('graphs', exist_ok=True)
best = None
log = open('results.jsonl', 'a')
seen = set()
for trial in range(TRIALS):
    cseed = rng.randrange(5)
    s = [0] + [rng.randrange(5) for _ in range(3)]
    t = [rng.randrange(5), rng.randrange(5)]
    if t[0] == t[1] or t[0] in s or t[1] in s:
        continue  # would create duplicate flag-copy edges (degree < q+3)
    sig = [list(rng.choice(perms)), list(rng.choice(perms))]
    key = (cseed, tuple(s), tuple(t), tuple(sig[0]), tuple(sig[1]))
    if key in seen:
        continue
    seen.add(key)
    out = f'graphs/t{trial}.txt'
    ne, dmax, dmin = fr.build(cseed, s, t, sig, out)
    r = subprocess.run([GC, out, '8', 'range:0:2912'], capture_output=True, text=True, timeout=900)
    parts = r.stdout.split()
    cost = int(parts[1]) if parts and parts[0] == 'GCOST' else -1
    rec = dict(trial=trial, cseed=cseed, s=s, t=t, sig=sig, edges=ne, maxdeg=dmax, mindeg=dmin, cost=cost,
               ecc=parts[parts.index('ecc_max') + 1] if 'ecc_max' in parts else None)
    log.write(json.dumps(rec) + '\n'); log.flush()
    if cost >= 0 and (best is None or cost < best['cost']):
        best = rec
    os.remove(out)
print('BEST', json.dumps(best))
