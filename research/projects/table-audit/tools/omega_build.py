"""Gomez's Omega B_1 (J. Gomez Marti, PhD thesis, UPC Barcelona 1986, Sec. 2.9.3, Fig. 2.21), as read here (table-audit).

B_1: bipartite, sides P and L of equal size, a bijection sigma: P -> L pairs them into positions x = (p_x, l_x).
alpha groups of 5 copies of B_1 (copies U^g_c, c in Z_5) and 10 hub sets n_k, nbar_k (k in Z_5) with one hub per
position.  Group of type 'a' (Fig. 2.21 a): nbar_k(x) ~ (p_x, U_{k+2}), (p_x, U_{k+3}) (the circle arcs) and
n_k(x) ~ (l_x, U_{k-1}), (l_x, U_{k+1}) (the pentagram chords).  Type 'b' (Fig. 2.21 b, the copies drawn with their
sides swapped): n_k(x) ~ (p_x, U_{k+3}), (p_x, U_{k+4}) and nbar_k(x) ~ (l_x, U_{k-1}), (l_x, U_{k+1}).
In a type-b group the copy's points take the colour of the lines of a type-a group, so the graph stays bipartite.
Every copy vertex gains 2, every hub has degree 2*alpha.  Order 5*alpha*N_1 + 5*N_1 = 5(alpha+1)N_1.
Thesis: Delta = Delta_1 + 2 with Delta_1 + 2 = 2 alpha + beta, and diameter <= D_1 + 2 (D_1 even).
Table D = 8 values: Omega H(q): q = 7, 8, 9, 11, 13 (alpha = 5, 5, 6, 7, 8) -> (10,8), (11,8), (12,8), (14,8), (16,8).
Usage: omega_build.py BASE_EDGES TYPES SIGMA OUT [RELABEL]   TYPES e.g. abab; SIGMA = inc (a perfect matching of the
incidence graph: p_x on l_x), shift:s (l_x = line index (x+s) mod N), or rand:seed.  RELABEL (a variant outside the
thesis's notation, to test how much the labelling matters): copy:SEED relabels every copy at random, group:SEED every
group of 5 copies (same relabelling inside a group)."""
import random
import sys

base, types, sig, out = sys.argv[1:5]
with open(base) as f:
    n = int(f.readline())
    E = [tuple(map(int, line.split())) for line in f if line.strip()]
N = n // 2                      # points 0..N-1, lines N..2N-1 (moore_build layout)
alpha = len(types)
if sig == 'inc':
    # greedy augmenting-path perfect matching points -> lines in the incidence graph
    nb = [[] for _ in range(N)]
    for u, v in E:
        nb[u].append(v - N)
    match_l = [-1] * N

    def aug(p, seen):
        for l in nb[p]:
            if not seen[l]:
                seen[l] = True
                if match_l[l] < 0 or aug(match_l[l], seen):
                    match_l[l] = p
                    return True
        return False
    sys.setrecursionlimit(100000)
    for p in range(N):
        assert aug(p, [False] * N)
    sigma = [0] * N
    for l, p in enumerate(match_l):
        sigma[p] = l
elif sig.startswith('shift:'):
    s = int(sig.split(':')[1])
    sigma = [(x + s) % N for x in range(N)]
else:
    rng = random.Random(int(sig.split(':')[1]))
    sigma = list(range(N))
    rng.shuffle(sigma)
B = 2 * N
ncopies = 5 * alpha
H0 = ncopies * B                 # hubs: n_k(x) = H0 + k*N + x, nbar_k(x) = H0 + 5N + k*N + x
tot = H0 + 10 * N


perm = None                      # optional relabelling (variant, not in the thesis)
if len(sys.argv) > 5:
    mode, seed = sys.argv[5].split(':')
    prng = random.Random(int(seed))
    perm = []
    for i in range(ncopies):
        if mode == 'copy' or i % 5 == 0:
            pp, ll = list(range(N)), list(range(N))
            prng.shuffle(pp)
            prng.shuffle(ll)
            cur = pp + [N + y for y in ll]
        perm.append(cur)


def cp(g, c, v):                 # vertex v of B_1 in copy c (mod 5) of group g
    i = 5 * g + c % 5
    return i * B + (perm[i][v] if perm else v)


with open(out, 'w') as f:
    f.write(f'{tot}\n')
    for g in range(ncopies):
        o = g * B
        f.writelines(f'{u + o} {v + o}\n' for u, v in E)
    for g, t in enumerate(types):
        for k in range(5):
            for x in range(N):
                p, l = x, N + sigma[x]
                n_, nb_ = H0 + k * N + x, H0 + 5 * N + k * N + x
                if t == 'a':
                    f.write(f'{nb_} {cp(g, k + 2, p)}\n{nb_} {cp(g, k + 3, p)}\n')
                    f.write(f'{n_} {cp(g, k - 1, l)}\n{n_} {cp(g, k + 1, l)}\n')
                else:
                    f.write(f'{n_} {cp(g, k + 3, p)}\n{n_} {cp(g, k + 4, p)}\n')
                    f.write(f'{nb_} {cp(g, k - 1, l)}\n{nb_} {cp(g, k + 1, l)}\n')
print(out, 'alpha =', alpha, 'types', types, 'sigma', sig, '->', tot, 'vertices')
