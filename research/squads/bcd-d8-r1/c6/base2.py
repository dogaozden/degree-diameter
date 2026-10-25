"""c6: base' = two layers of H(5) with parity-separated jump edges.

Vertices (x, e): x a point (0..N-1) or line (N..2N-1) of H(5), e in {0,1}; id = e*2N + x.
Edges:
  incidence   (p,e) -- (L,e)            for p on L, both e
  point jump  (p,e) -- (pi p, 1-e)      pi a permutation of points
  line jump   (L,e) -- (rho L, 1-e)     rho a permutation of lines
pi and rho commute with the torus tau (pi(tau x) = tau pi x), so tau acts on base' as (x,e) -> (tau x, e).
Voltages are tau-invariant (one per tau-orbit of base edges), so bcd gets the torus as a base automorphism.
"""
import sys
import numpy as np

sys.path.insert(0, '/home/user/degree-diameter/research/projects/bigcheck-dist/d8')
import hexspec as hs

HEX = '/tmp/bcdt/hex/hex_q5.bin'
SING = '/tmp/bcdt/hex/singer_q5.bin'
H = hs.Hex(HEX, SING)
N, KA = H.N, H.KA
NB = 4 * N
HERE = '/home/user/degree-diameter/research/squads/bcd-d8-r1/c6'


def powers(t):
    P = [np.arange(N)]
    for _ in range(KA - 1):
        P.append(t[P[-1]])
    return np.array(P)


TP = powers(H.tp)          # TP[k][x] = tau^k x on points
TL = powers(H.tl)          # TL[k][l] = tau^k l on lines
TPl = np.array([TP[k] for k in range(KA)])


def equiv_perm(orb, pos, rep, rng, PW):
    """random tau-equivariant permutation of one class of objects (points or lines).
    orb/pos/rep: orbit id, position and representative of each object under tau. PW: powers of tau on the class.
    Returns f with f[tau x] = tau f[x]. Rejects maps with f(f(x)) = x somewhere (duplicate jump edges)."""
    NO = len(rep)
    while True:
        sg = rng.permutation(NO)
        t = rng.integers(0, KA, NO)
        f = PW[(pos + t[orb]) % KA, rep[sg[orb]]]
        if not np.any(f[f] == np.arange(N)):
            return f


def base_tau():
    """tau on base' vertices: layer-wise (points then lines)."""
    perm = np.concatenate([H.tp, N + H.tl])
    return np.concatenate([perm, 2 * N + perm])


def base_orbits():
    T = base_tau()
    orb = -np.ones(NB, dtype=np.int64)
    pos = np.zeros(NB, dtype=np.int64)
    reps = []
    for x in range(NB):
        if orb[x] >= 0:
            continue
        y = x
        for e in range(KA):
            orb[y] = len(reps)
            pos[y] = e
            y = T[y]
        assert y == x
        reps.append(x)
    PWb = np.array([np.arange(NB)] )
    Tk = [np.arange(NB)]
    for _ in range(KA - 1):
        Tk.append(T[Tk[-1]])
    return orb, pos, np.array(reps), np.array(Tk)


BORB, BPOS, BREP, BPW = base_orbits()


def build_edges(pi, rho):
    """list of oriented base edges (u, v) in a fixed order, with types, and their voltage-class keys."""
    E = []
    for e in (0, 1):
        for p in range(N):
            for L in H.plines[p]:
                E.append((e * 2 * N + p, e * 2 * N + N + L))
    for e in (0, 1):
        for p in range(N):
            E.append((e * 2 * N + p, (1 - e) * 2 * N + pi[p]))
        for L in range(N):
            E.append((e * 2 * N + N + L, (1 - e) * 2 * N + N + rho[L]))
    E = np.array(E, dtype=np.int64)
    u, v = E[:, 0], E[:, 1]
    # canonical key of an oriented edge: (orbit of u, tau^{-pos(u)} v)
    vneg = BPW[(KA - BPOS[u]) % KA, v]
    key = BORB[u] * NB + vneg
    uk, inv = np.unique(key, return_inverse=True)
    return E, inv, len(uk)


def write_spec(path, M, E, inv, w):
    a = w[inv]
    with open(path, 'w') as f:
        f.write(f"bcd-lift 1\ngroup cyclic {M}\nvertices {NB}\nedges {len(E)}\n")
        f.write("".join(f"{int(u)} {int(v)} {int(x)}\n" for (u, v), x in zip(E, a)))
        f.write("aut 1\n" + " ".join(map(str, base_tau())) + "\n" + " ".join(["0"] * NB) + "\n")
        f.write("end\n")


def cost(path, M=None, D=8, threads=1):
    import subprocess
    out = subprocess.run(['/tmp/bcd', 'lift', path, '8', str(D), '--cost', '--threads', str(threads)],
                         capture_output=True, text=True, timeout=900)
    for ln in out.stdout.splitlines():
        if ln.startswith('COST'):
            return int(ln.split()[1])
    raise RuntimeError(out.stdout + out.stderr)
