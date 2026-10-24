"""Permutation / group voltage lifts of H(q) + 2 hop matchings (card c8, option B).

A group G of order M acts on the levels by right translations; a dart carrying g gets the permutation h -> h*g.
The lift is then G-invariant (left translations are automorphisms), so gperm mode 1 (sources (v,e)) is exact.
Groups: metacyclic Z_m x| Z_n with action r (order of r divides n, r^n = 1 mod m), which includes Z_M (n=1, r=1)
and non-abelian groups such as D_n (m=n, n=2, r=-1), Z_7 x| Z_3, Z_5 x| Z_4 (= F_20), Z_9 x| Z_3 (order 27).

usage: gperm_lifts.py q m n r seed [model] [holo] [step]   (writes base to scratchpad, runs gperm mode 1, prints result)
"""
import os
import random
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
D8 = '/home/user/degree-diameter/research/theorems/d8'
SCR = '/tmp/claude-0/-home-user-degree-diameter/0ad899b8-ae47-58b5-b704-0795802a53c1/scratchpad'
sys.path.insert(0, D8)
import gh  # noqa: E402
from models import perfect_matching  # noqa: E402


class Group:
    """Metacyclic group Z_m x| Z_n, element (a,b) -> index a*n+b, product (a1,b1)(a2,b2) = (a1 + r^b1 a2, b1+b2)."""

    def __init__(self, m, n, r):
        assert pow(r, n, m) == 1 % m, 'r^n must be 1 mod m'
        self.m, self.n, self.r = m, n, r
        self.order = m * n
        rp = [pow(r, b, m) for b in range(n)]
        self.mul = [[0] * self.order for _ in range(self.order)]
        for a1 in range(m):
            for b1 in range(n):
                for a2 in range(m):
                    for b2 in range(n):
                        a = (a1 + rp[b1] * a2) % m
                        b = (b1 + b2) % n
                        self.mul[a1 * n + b1][a2 * n + b2] = a * n + b
        # right translation permutations: h -> h*g
        self.rperm = [[self.mul[h][g] for h in range(self.order)] for g in range(self.order)]
        self.ident = 0  # (0,0)
        # sanity: associativity on a sample and identity
        rng = random.Random(1)
        for _ in range(2000):
            x, y, z = (rng.randrange(self.order) for _ in range(3))
            assert self.mul[self.mul[x][y]][z] == self.mul[x][self.mul[y][z]]
        assert all(self.mul[self.ident][x] == x and self.mul[x][self.ident] == x for x in range(self.order))

    def abelian(self):
        return all(self.mul[x][y] == self.mul[y][x] for x in range(self.order) for y in range(self.order))


def build_base(q, G, seed, model='free', holo=False, const=None):
    """Return (NB, edges) with edges (u, v, perm_as_list). model 'free': random bijections s1,s2 for the hops;
    'par': two disjoint perfect matchings. holo: random group voltages on the H(q) flags. const: (g1,g2) constant
    hop voltages instead of random ones."""
    rng = random.Random(seed)
    H = gh.load(q)
    N, M = H.N, G.order
    ident = list(range(M))
    edges = []
    for (p, Lv) in gh.flags(H):
        g = rng.randrange(M) if holo else G.ident
        edges.append((p, Lv, G.rperm[g]))
    nbrs = [list(map(int, H.through[p])) for p in range(N)]
    if model == 'par':
        s1 = perfect_matching(N, nbrs, rng)
        s2 = perfect_matching(N, nbrs, rng, forbid=s1)
    else:
        s1 = list(range(N)); rng.shuffle(s1)
        s2 = list(range(N)); rng.shuffle(s2)
    for p in range(N):
        if const is None:
            g1, g2 = rng.randrange(M), rng.randrange(M)
        else:
            g1, g2 = const
        edges.append((p, N + s1[p], G.rperm[g1]))
        edges.append((p, N + s2[p], G.rperm[g2]))
    return 2 * N, M, edges


def write_perm_base(path, NB, M, edges):
    with open(path, 'w') as fh:
        fh.write(f'{NB} {M} {len(edges)}\n')
        for u, v, perm in edges:
            fh.write(f'{u} {v} ' + ' '.join(map(str, perm)) + '\n')


def run_gperm(path, D=8, mode=1, step=1, binary=os.path.join(HERE, 'gperm')):
    out = subprocess.run(['timeout', '900', 'nice', '-n', '10', binary, path, str(D), str(mode), str(step)],
                         capture_output=True, text=True).stdout
    unr = int(out.split('unreached_pairs')[1].split()[0])
    return unr, out


if __name__ == '__main__':
    q, m, n, r, seed = (int(x) for x in sys.argv[1:6])
    model = sys.argv[6] if len(sys.argv) > 6 else 'free'
    holo = (sys.argv[7] == '1') if len(sys.argv) > 7 else False
    step = int(sys.argv[8]) if len(sys.argv) > 8 else 1
    G = Group(m, n, r)
    NB, M, edges = build_base(q, G, seed, model, holo)
    path = f'{SCR}/gp_q{q}_Z{m}x{n}r{r}_{model}_h{int(holo)}_s{seed}.txt'
    write_perm_base(path, NB, M, edges)
    unr, out = run_gperm(path, 8, 1, step)
    print(f'q={q} group=Z{m}x|Z{n}(r={r}) order={M} abelian={G.abelian()} model={model} holo={int(holo)} '
          f'seed={seed} step={step} unreached={unr}', flush=True)
