"""Full check (all N^2 pairs) that each generator in an hx .aut file is a bijective automorphism of the table group."""
import sys, struct
import numpy as np
tab, aut = sys.argv[1], sys.argv[2]
with open(tab, 'rb') as f:
    N = struct.unpack('<i', f.read(4))[0]
    M = np.frombuffer(f.read(2 * N * N), dtype='<u2').reshape(N, N).astype(np.int32)
toks = open(aut).read().split()
cnt = int(toks[0]); vals = np.array(list(map(int, toks[1:1 + cnt * N])), dtype=np.int64).reshape(cnt, N)
ok_all = True
for t in range(cnt):
    p = vals[t]
    bij = np.array_equal(np.sort(p), np.arange(N))
    hom = np.array_equal(p[M], M[p[:, None], p[None, :]]) if False else None
    # p(ab) == p(a) p(b) for all a, b: compare p[M[a,b]] with M[p[a], p[b]]
    lhs = p[M]                      # lhs[a,b] = p(a*b)
    rhs = M[np.ix_(p, p)]           # rhs[a,b] = p(a) * p(b)
    hom = np.array_equal(lhs, rhs)
    ok_all &= bij and hom
    if not (bij and hom):
        print("generator", t, "bijective", bij, "homomorphism", hom)
print(f"{tab}: N={N}, {cnt} generators, all bijective automorphisms (full N^2 check): {ok_all}")
