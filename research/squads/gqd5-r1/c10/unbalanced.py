import sys, random, os
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c10')
from lib import *
def find(KA, KB, d, seeds=200):
    for s in range(seeds):
        rng = random.Random(s)
        # A side: 0..KA-1, B side: KA..KA+KB-1
        e = random_maximal_bip(KA, KB, d, rng)
        res = check(KA + KB, e)
        if res.get('valid') == 1 and sorted([res['nA'], res['nB']]) == sorted([KA, KB]):
            return s, e, res
    return None
for KA, KB, d in [(115, 126, 8), (77, 86, 6)]:
    r = find(KA, KB, d)
    if r is None:
        print("NOT FOUND", KA, KB, d); continue
    s, e, res = r
    print("FOUND", KA, KB, d, "seed", s, res, flush=True)
    # write edge list, with colour class sizes in the first line comment
    fn = f"/home/user/degree-diameter/research/squads/gqd5-r1/c10/unbalanced_KB{KB}_KA{KA}_d{d}.edges"
    with open(fn, 'w') as f:
        f.write(f"# hub graph: colour classes sizes K_B={KB} (B-side), K_A={KA} (A-side); max degree <= {d}; "
                f"vertices 0..{KA-1} = A-side, {KA}..{KA+KB-1} = B-side; all same-colour distances <= 4 (verified by hub4)\n")
        f.write(f"{KA + KB} {len(e)}\n")
        f.write("".join(f"{u} {v}\n" for u, v in e))
    print("wrote", fn, flush=True)
    # read the file back (skipping the comment line) and re-verify
    lines = open(fn).read().split('\n')[1:]
    body = [l for l in lines if l.strip()]
    n, m = map(int, body[0].split())
    edges = [tuple(map(int, l.split())) for l in body[1:]]
    assert len(edges) == m
    print("reverify", check(n, edges, tag='tmp_reverify.txt'), flush=True)
    os.remove(os.path.join(HERE, 'tmp_reverify.txt'))
