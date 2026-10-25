import numpy as np, sys, os, random, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
t0 = time.time()
H = Hex(SP + 'hex_q11.bin'); N = H.N; q = H.q
print('loaded', N, q, f'{time.time()-t0:.1f}s', flush=True)
def line_pts(u, v):
    """the 12 projective points of <u,v> as hexagon point ids"""
    U = H.X[u]; V = H.X[v]
    vecs = [(U + lam * V) % q for lam in range(q)] + [V]
    return H.index_of(np.array(vecs))
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
for trial in range(4):
    while True:
        u = rng.randrange(N); v = rng.randrange(N)
        if u != v and H.B(u, v) == 0 and v not in H.collinear_points(u): break
    T = line_pts(u, v)
    assert len(set(T.tolist())) == 12
    mids = []
    for i in range(12):
        for j in range(i + 1, 12):
            a, b = int(T[i]), int(T[j])
            mm = H.collinear_points(a) & H.collinear_points(b)
            mids.append(tuple(sorted(mm)))
    cnt = {}
    for mm in mids: cnt[mm] = cnt.get(mm, 0) + 1
    print('trial', trial, 'pairs', len(mids), 'distinct midpoint sets', {k: v for k, v in cnt.items()}, flush=True)
    # collinear pairs inside T?
    print('  any pair collinear:', any(int(T[j]) in H.collinear_points(int(T[i])) for i in range(12) for j in range(i+1, 12)))
