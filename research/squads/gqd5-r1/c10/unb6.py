import sys, random, os
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c10')
from lib import *
KA, KB, d = 77, 86, 6
found = None
# (i) random maximal, many seeds
for s in range(3000):
    e = random_maximal_bip(KA, KB, d, random.Random(s))
    res = check(KA + KB, e)
    if res.get('valid') == 1 and sorted([res['nA'], res['nB']]) == sorted([KA, KB]):
        found = ('maximal', s, e, res); break
print("maximal tries done; found:", found is not None and found[:2], flush=True)
# (ii) start from a balanced 86+86 6-regular graph and delete 9 A-vertices (keep B side = 86)
if found is None:
    for s in range(300):
        rng = random.Random(10000 + s)
        e = random_regular_bip(86, d, rng)
        if e is None: continue
        dele = set(random.Random(s).sample(range(86), 86 - KA))
        ee = [(a, b) for a, b in e if a not in dele]
        remap = {a: i for i, a in enumerate(sorted(set(range(86)) - dele))}
        ee = [(remap[a], 77 + (b - 86)) for a, b in ee]
        res = check(KA + KB, ee)
        if res.get('valid') == 1 and sorted([res['nA'], res['nB']]) == sorted([KA, KB]):
            found = ('delete-A', s, ee, res); break
    print("deletion tries done; found:", found is not None and found[:2], flush=True)
if found:
    kind, s, e, res = found
    print(kind, res, flush=True)
    fn = '/home/user/degree-diameter/research/squads/gqd5-r1/c10/unbalanced_KB86_KA77_d6.edges'
    with open(fn, 'w') as f:
        f.write(f"# hub graph: colour classes sizes K_B=86 (B-side), K_A=77 (A-side); max degree <= 6; "
                f"vertices 0..76 = A-side, 77..162 = B-side; all same-colour distances <= 4 (verified by hub4)\n")
        f.write(f"{KA + KB} {len(e)}\n")
        f.write("".join(f"{u} {v}\n" for u, v in e))
    body = [l for l in open(fn).read().split('\n')[1:] if l.strip()]
    n, m = map(int, body[0].split())
    ed = [tuple(map(int, l.split())) for l in body[1:]]
    print("reverify", check(n, ed, tag='tmp_reverify6.txt'), flush=True)
    os.remove(os.path.join(HERE, 'tmp_reverify6.txt'))
