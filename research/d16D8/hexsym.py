# hexsym.py: a semiregular cyclic collineation group of the split Cayley hexagon H(q) (hexgen coordinates).
#
# SL(3,q) sits in G2(q) as x -> (A x[0:3], x[3], A^-T x[4:7]) (V3 = coordinates 0..2, V3* = 4..6, paired 0-4, 1-5, 2-6).
# A = (Singer cycle of GL(3,q))^(q-1) has order q^2+q+1 and det 1; a power of prime order r with r not dividing q-1
# has no eigenvector over F_q, so it fixes no point and no line (no invariant 1- or 2-space). The script checks that the
# map sends every line of hex/hex_q{q}.bin to a line and that the group is semiregular, then writes the permutation.
#
#   python3 hexsym.py q r OUT.json      (r = order of the subgroup to use, a prime dividing q^2+q+1)
# OUT.json: {"q", "r", "pt": point permutation of the generator, "ln": line permutation}
import sys, json, struct, itertools

def load_hex(fn):
    b = open(fn, 'rb').read()
    q, N, L = struct.unpack('<3i', b[:12])
    off = 12 + 4 * L * (q + 1)
    lp = struct.unpack('<%di' % (L * (q + 1)), b[12:off])
    lines = [tuple(lp[i * (q + 1):(i + 1) * (q + 1)]) for i in range(L)]
    coords = [tuple(b[off + 7 * i: off + 7 * i + 7]) for i in range(N)]
    return q, N, lines, coords

def matmul(A, B, q):
    return [[sum(A[i][t] * B[t][j] for t in range(len(B))) % q for j in range(len(B[0]))] for i in range(len(A))]

def matpow(A, e, q):
    R = [[int(i == j) for j in range(3)] for i in range(3)]
    while e:
        if e & 1: R = matmul(R, A, q)
        A = matmul(A, A, q); e >>= 1
    return R

def inv3(A, q):
    a = A
    det = (a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1]) - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
           + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0])) % q
    di = pow(det, q - 2, q)
    C = [[0] * 3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            m = [[a[r][c] for c in range(3) if c != j] for r in range(3) if r != i]
            C[i][j] = ((-1) ** (i + j) * (m[0][0] * m[1][1] - m[0][1] * m[1][0])) % q
    return [[C[j][i] * di % q for j in range(3)] for i in range(3)], det

def singer(q):
    # companion matrix of a primitive cubic over F_q (q prime): search
    for c0, c1, c2 in itertools.product(range(q), repeat=3):
        if c0 == 0: continue
        A = [[0, 0, (-c0) % q], [1, 0, (-c1) % q], [0, 1, (-c2) % q]]   # x^3 + c2 x^2 + c1 x + c0
        # order of A in GL(3,q) must be q^3-1
        n = q ** 3 - 1; ok = True
        I = [[int(i == j) for j in range(3)] for i in range(3)]
        if matpow(A, n, q) != I: continue
        for pr in set(f for f in range(2, n + 1) if n % f == 0 and all(f % g for g in range(2, int(f ** .5) + 1))):
            if matpow(A, n // pr, q) == I: ok = False; break
        if ok: return A
    raise SystemExit('no Singer cycle')

def main():
    q, r, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    assert (q * q + q + 1) % r == 0
    q_, N, lines, coords = load_hex('/home/user/degree-diameter/research/d16D8/hex/hex_q%d.bin' % q)
    assert q_ == q
    A = matpow(singer(q), (q - 1) * ((q * q + q + 1) // r), q)
    Ainv, det = inv3(A, q)
    assert det == 1, det
    AiT = [[Ainv[j][i] for j in range(3)] for i in range(3)]
    idx = {c: i for i, c in enumerate(coords)}
    def norm(v):
        for x in v:
            if x:
                s = pow(x, q - 2, q); return tuple(y * s % q for y in v)
    def act(v):
        a = [sum(A[i][t] * v[t] for t in range(3)) % q for i in range(3)]
        b = [sum(AiT[i][t] * v[4 + t] for t in range(3)) % q for i in range(3)]
        return norm(a + [v[3]] + b)
    pt = [idx[act(c)] for c in coords]
    lidx = {tuple(sorted(L)): i for i, L in enumerate(lines)}
    ln = []
    for L in lines:
        key = tuple(sorted(pt[p] for p in L))
        if key not in lidx: raise SystemExit('generator does not preserve the hexagon')
        ln.append(lidx[key])
    # semiregular: no power 1..r-1 fixes a point or a line (r prime, so checking the generator suffices)
    assert all(pt[i] != i for i in range(N)) and all(ln[i] != i for i in range(N))
    # order check
    x = list(range(N))
    for _ in range(r): x = [pt[i] for i in x]
    assert x == list(range(N))
    json.dump(dict(q=q, r=r, pt=pt, ln=ln), open(out, 'w'))
    print('q=%d r=%d: generator preserves H(q), semiregular, %d point orbits, %d line orbits' % (q, r, N // r, N // r))

main()
