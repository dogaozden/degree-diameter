import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley (lift of a 2-vertex base with d darts) search.
#
# Vertices are A_x and B_y for x, y in a finite group G of order N. A_x is
# joined to B_{x*s} for each dart s in a d-subset S of G. Left multiplication
# by g is an automorphism, so the graph is vertex-transitive on each side, and
# its diameter is at most D iff BFS from A_e and from B_e reaches everything
# within D. The engine anneals over the dart set S to minimise the number of
# far pairs. Groups are Z_a x|_r Z_k with r^k = 1 mod a (random choice per
# attempt). Orders are swept downward from the Moore-type limit, and the
# first success above the threshold of the start graph is kept.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 1200

static uint64_t rng_state = 88172645463325252ULL;

static uint64_t rnd64(void) {
    uint64_t z = (rng_state += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static double rndu(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int rndi(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static double budget_s = 10.0;

static int out_of_time(void) {
    return (double)clock() / (double)CLOCKS_PER_SEC > budget_s;
}

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long powmod_i(long base, long e, long m) {
    long r = 1 % m;
    base %= m;
    if (base < 0) base += m;
    while (e > 0) {
        if (e & 1) r = r * base % m;
        base = base * base % m;
        e >>= 1;
    }
    return r;
}

typedef struct {
    int N, d, D;
    int *mul;   /* N*N table, element 0 is the identity */
    int *inv;   /* N */
    int *dist;  /* 2N */
    int *q;     /* 2N */
} Ctx;

/* Semidirect product Z_a x|_r Z_k, element (p, b) coded as p*k + b:
   (p1,b1)(p2,b2) = (p1 + r^b1 p2, b1 + b2). */
static void build_group(int a, int k, int r, int N, int *mul, int *inv) {
    int *pw = (int *)malloc(sizeof(int) * (size_t)k);
    for (int b = 0; b < k; b++) pw[b] = (int)powmod_i(r, b, a);
    for (int x = 0; x < N; x++) {
        int p1 = x / k, b1 = x % k;
        for (int y = 0; y < N; y++) {
            int p2 = y / k, b2 = y % k;
            int p = (int)(((long)p1 + (long)pw[b1] * p2) % a);
            int b = (b1 + b2) % k;
            mul[(size_t)x * N + y] = p * k + b;
        }
    }
    for (int x = 0; x < N; x++) {
        inv[x] = 0;
        for (int y = 0; y < N; y++) {
            if (mul[(size_t)x * N + y] == 0) {
                inv[x] = y;
                break;
            }
        }
    }
    free(pw);
}

static void pick_group(int N, int *pa, int *pk, int *pr) {
    int divs[256];
    int nd = 0;
    for (int k = 1; k <= N && nd < 256; k++)
        if (N % k == 0) divs[nd++] = k;
    int k = divs[rndi(nd)];
    int a = N / k;
    if (a == 1) {
        *pa = 1;
        *pk = k;
        *pr = 0;
        return;
    }
    int cand[NMAX];
    int nc = 0;
    for (int r = 1; r < a; r++) {
        if (gcd_i(r, a) == 1 && powmod_i(r, k, a) == 1) cand[nc++] = r;
    }
    /* r = 1 always qualifies, so nc >= 1. */
    *pa = a;
    *pk = k;
    *pr = cand[rndi(nc)];
}

/* Number of (source, vertex) pairs at distance > D from A_e and from B_e. */
static int cost_of(const Ctx *c, const int *S) {
    const int N = c->N, d = c->d, D = c->D;
    const int n2 = 2 * N;
    int cost = 0;
    for (int s = 0; s < 2; s++) {
        int src = (s == 0) ? 0 : N;
        for (int i = 0; i < n2; i++) c->dist[i] = -1;
        int head = 0, tail = 0;
        c->dist[src] = 0;
        c->q[tail++] = src;
        while (head < tail) {
            int u = c->q[head++];
            int du = c->dist[u];
            if (du >= D) continue;
            if (u < N) {
                const int *row = c->mul + (size_t)u * N;
                for (int j = 0; j < d; j++) {
                    int v = N + row[S[j]];
                    if (c->dist[v] < 0) {
                        c->dist[v] = du + 1;
                        c->q[tail++] = v;
                    }
                }
            } else {
                const int y = u - N;
                const int *row = c->mul + (size_t)y * N;
                for (int j = 0; j < d; j++) {
                    int v = row[c->inv[S[j]]];
                    if (c->dist[v] < 0) {
                        c->dist[v] = du + 1;
                        c->q[tail++] = v;
                    }
                }
            }
        }
        cost += n2 - tail;
    }
    return cost;
}

/* Simulated annealing over d-subsets S of G. Returns 1 with S valid (cost 0). */
static int anneal(Ctx *c, long evals, int *S, unsigned char *inS) {
    const int N = c->N, d = c->d;
    for (int i = 0; i < N; i++) inS[i] = 0;
    for (int j = 0; j < d; j++) {
        int g;
        do {
            g = rndi(N);
        } while (inS[g]);
        S[j] = g;
        inS[g] = 1;
    }
    int cur = cost_of(c, S);
    for (long t = 0; t < evals && cur > 0; t++) {
        if ((t & 255) == 0 && out_of_time()) break;
        double frac = (double)t / (double)evals;
        double T = 1.5 * (1.0 - frac) + 0.05;
        int j = rndi(d);
        int g = rndi(N);
        if (inS[g]) continue;
        int old = S[j];
        S[j] = g;
        int nc = cost_of(c, S);
        int delta = nc - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cur = nc;
            inS[old] = 0;
            inS[g] = 1;
        } else {
            S[j] = old;
        }
    }
    return cur == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    rng_state ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x2545F4914F6CDD1DULL;
    budget_s = atof(argv[4]);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) n0 = 0;
    (void)m0;

    if (d < 3 || D < 2) {
        printf("0 0\n");
        return 0;
    }

    /* Half of the bipartite Moore bound: sum_{i<D} (d-1)^i. */
    long long msum = 0, pw = 1;
    for (int i = 0; i < D; i++) {
        msum += pw;
        pw *= (d - 1);
        if (pw > 1000000000LL) pw = 1000000000LL;
    }
    int Ntop = msum > NMAX ? NMAX : (int)msum;
    int Nlo = n0 / 2 + 1;
    if (Nlo < d) Nlo = d;
    if (Nlo < 1) Nlo = 1;
    if (Ntop < Nlo) {
        printf("0 0\n");
        return 0;
    }

    Ctx c;
    c.d = d;
    c.D = D;
    c.mul = (int *)malloc(sizeof(int) * (size_t)Ntop * (size_t)Ntop);
    c.inv = (int *)malloc(sizeof(int) * (size_t)Ntop);
    c.dist = (int *)malloc(sizeof(int) * 2 * (size_t)Ntop);
    c.q = (int *)malloc(sizeof(int) * 2 * (size_t)Ntop);
    int *S = (int *)malloc(sizeof(int) * (size_t)d);
    unsigned char *inS = (unsigned char *)malloc((size_t)Ntop);

    int *bestE = NULL;
    int bestHalf = 0;
    int Nhi = Ntop;
    long E = 2000;

    while (!out_of_time() && Nlo <= Nhi) {
        for (int N = Nhi; N >= Nlo && !out_of_time(); N--) {
            int a, k, r;
            pick_group(N, &a, &k, &r);
            c.N = N;
            build_group(a, k, r, N, c.mul, c.inv);
            if (anneal(&c, E, S, inS)) {
                int *ne = (int *)malloc(sizeof(int) * 2 * (size_t)N * (size_t)d);
                long idx = 0;
                for (int x = 0; x < N; x++) {
                    for (int j = 0; j < d; j++) {
                        ne[idx++] = x;
                        ne[idx++] = N + c.mul[(size_t)x * N + S[j]];
                    }
                }
                free(bestE);
                bestE = ne;
                bestHalf = N;
                Nlo = N + 1;   /* only larger orders can improve now */
                break;
            }
        }
        if (E < (1L << 40)) E *= 2;
    }

    if (bestHalf > 0) {
        printf("%d %d\n", 2 * bestHalf, bestHalf * d);
        long m = (long)bestHalf * d;
        for (long i = 0; i < m; i++) {
            printf("%d %d\n", bestE[2 * i], bestE[2 * i + 1]);
        }
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are all points of PG(3, q); lines are totally isotropic lines of the
    symplectic form B(x, y) = x0*y1 - x1*y0 + x2*y3 - x3*y2. Degree is q + 1,
    diameter is 4, and the order is 2(q+1)(q^2+1).
    """
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph helpers.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists or sets."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices. Returns list or None."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
    if D < 2:
        return n, edges
    if rng is None:
        rng = random.Random(0)
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order. Returns new edge list."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Twin duplication.
# ----------------------------------------------------------------------------

def _duplicate_twins(n, edges, d, rng):
    """Greedily add twins in random order while neighbours have spare degree."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    changed = True
    while changed:
        changed = False
        order = list(range(len(adj)))
        rng.shuffle(order)
        for v in order:
            nb = adj[v]
            if not nb or len(nb) > d:
                continue
            if any(len(adj[u]) >= d for u in nb):
                continue
            w = len(adj)
            adj.append(set(nb))
            for u in nb:
                adj[u].add(w)
            changed = True
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


def _trial(base_n, base_e, d, D, rng, deadline):
    """One randomized pipeline: mix twin duplication with cover growth and saturation."""
    mode = rng.randrange(3)
    n, e = base_n, list(base_e)
    if mode == 0:
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    return n, e


# ----------------------------------------------------------------------------
# Doubling by cross matching of spare stubs, with annealed repair.
# ----------------------------------------------------------------------------

def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _add_vertex(adj, color, d, D, side, rng):
    """Append a vertex on the opposite side of `side`, joined to a greedy cover of `side`."""
    n = len(adj)
    ball = _balls_radius(n, adj, D - 1)
    covered = 0
    chosen = []
    cands = [s for s in range(n) if color[s] == side]
    for _ in range(d):
        best_s, best_g = None, -1.0
        for s in cands:
            if s in chosen:
                continue
            g = (ball[s] & ~covered).bit_count() + 0.5 * rng.random()
            if g > best_g:
                best_s, best_g = s, g
        if best_s is None:
            break
        chosen.append(best_s)
        covered |= ball[best_s]
    v = n
    adj.append(set())
    color.append(1 - side)
    for s in chosen:
        if len(adj[s]) >= d:
            t = rng.choice(tuple(adj[s]))
            adj[s].discard(t)
            adj[t].discard(s)
        adj[s].add(v)
        adj[v].add(s)
    return v


def _fill(adj, color, d, rng):
    """Add cross-side edges between deficient vertices (only helps the diameter)."""
    n = len(adj)
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _anneal(adj, color, d, D, rng, iters, deadline):
    """Bipartite double-edge switches (degrees unchanged) minimising bad pairs. True if cost reaches 0."""
    cur = _cost(adj, D)
    side0 = [v for v in range(len(adj)) if color[v] == 0]
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        a = rng.choice(side0)
        if not adj[a]:
            continue
        b = rng.choice(tuple(adj[a]))
        c = rng.choice(side0)
        if c == a or not adj[c]:
            continue
        e = rng.choice(tuple(adj[c]))
        if e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _cost(adj, D)
        if new <= cur or (new == cur + 1 and rng.random() < 0.1):
            cur = new
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return cur == 0


def _double_cross(n, edges, d, D, rng, deadline):
    """Try to build a valid 2n-vertex graph from two cross-matched copies of a base graph."""
    N = 2 * n
    if N > lib.moore_bound(d, D):
        return None
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    B = [set() for _ in range(N)]
    for u in range(n):
        for v in adj[u]:
            B[u].add(v)
            B[u + n].add(v + n)
    spare = [d - len(adj[v]) for v in range(n)]
    s0 = [v for v in range(n) if color[v] == 0 for _ in range(spare[v])]
    s1 = [v for v in range(n) if color[v] == 1 for _ in range(spare[v])]
    rng.shuffle(s0)
    rng.shuffle(s1)
    t0 = list(s0)
    t1 = list(s1)
    rng.shuffle(t0)
    rng.shuffle(t1)
    for x, w in zip(s0, s1):
        y = w + n
        if y not in B[x] and len(B[x]) < d and len(B[y]) < d:
            B[x].add(y)
            B[y].add(x)
    for x, w in zip(t1, t0):
        y = w + n
        if y not in B[x] and len(B[x]) < d and len(B[y]) < d:
            B[x].add(y)
            B[y].add(x)
    color2 = color + [1 - c for c in color]
    _fill(B, color2, d, rng)
    if time.monotonic() < deadline:
        if _anneal(B, color2, d, D, rng, 3000, deadline):
            return N, [(u, v) for u in range(N) for v in B[u] if u < v]
    return None


def _try_doubling(n, edges, d, D, deadline, rng, consider):
    """Repeatedly attempt cross-matching doubling of the base until the deadline."""
    while time.monotonic() < deadline:
        res = _double_cross(n, edges, d, D, rng, deadline)
        if res is not None:
            N, e = res
            consider(N, e)
            return True
    return False


# ----------------------------------------------------------------------------
# Kill, repair, regrow large-neighbourhood search.
# ----------------------------------------------------------------------------

def _lns(n, edges, d, D, deadline, rng, consider):
    """Kill-repair-regrow large-neighbourhood search from a valid graph, anchored to its best."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 2, 3, 4))
        if k >= cur_n:
            break
        kill = set(rng.sample(range(cur_n), k))
        keep = [v for v in range(cur_n) if v not in kill]
        remap = {v: i for i, v in enumerate(keep)}
        m = len(keep)
        e2 = [(remap[u], remap[v]) for u, v in cur_e if u not in kill and v not in kill]
        adj = _to_sets(m, e2)
        color = _bipartition(m, adj)
        _fill(adj, color, d, rng)
        if not _anneal(adj, color, d, D, rng, 150, deadline):
            continue
        e3 = [(u, v) for u in range(m) for v in adj[u] if u < v]
        n4, e4 = _grow(m, e3, d, D, deadline, rng)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Redundant-edge pruning, then regrow.
# ----------------------------------------------------------------------------

def _prune_redundant(n, edges, D, rng, deadline, max_tests):
    """Delete random redundant edges (keeping diameter <= D). Returns the pruned edge list."""
    adj = _to_sets(n, edges)
    cand = list(edges)
    rng.shuffle(cand)
    tests = 0
    for u, v in cand:
        if tests >= max_tests or time.monotonic() > deadline:
            break
        if v not in adj[u]:
            continue
        tests += 1
        adj[u].discard(v)
        adj[v].discard(u)
        if _cost(adj, D) != 0:
            adj[u].add(v)
            adj[v].add(u)
    return [(a, b) for a in range(n) for b in adj[a] if a < b]


def _prune_regrow(n, edges, d, D, deadline, rng, consider):
    """Repeatedly prune redundant edges, regrow with cover vertices, keep the best."""
    best_n, best_e = n, list(edges)
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        pe = _prune_redundant(cur_n, cur_e, D, rng, deadline, 160)
        n2, e2 = _grow(cur_n, pe, d, D, deadline, rng)
        consider(n2, e2)
        if n2 > best_n:
            best_n, best_e = n2, list(e2)
        if n2 >= cur_n - 1:
            cur_n, cur_e = n2, list(e2)
        elif n2 < best_n - 2 or rng.random() < 0.3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Vertex splitting with neighbour partition, then annealed repair.
# ----------------------------------------------------------------------------

def _split_repair(n, edges, d, D, deadline, rng, consider):
    """Repeatedly split a random vertex of the current valid graph and repair it."""
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        snap_adj = [set(s) for s in adj]
        snap_color = list(color)
        cur_n = len(adj)
        cands = [v for v in range(cur_n) if len(adj[v]) >= 2]
        if not cands:
            break
        v = rng.choice(cands)
        nb = list(adj[v])
        rng.shuffle(nb)
        k = rng.randint(1, len(nb) - 1)
        S1, S2 = nb[:k], nb[k:]
        w = cur_n
        adj.append(set(S2))
        color.append(color[v])
        adj[v] = set(S1)
        for u in S2:
            adj[u].discard(v)
            adj[u].add(w)
        _fill(adj, color, d, rng)
        if _anneal(adj, color, d, D, rng, 1500, deadline):
            m = len(adj)
            e = [(a, b) for a in range(m) for b in adj[a] if a < b]
            consider(m, e)
        else:
            adj[:] = snap_adj
            color[:] = snap_color


def _prune_then_split(n, edges, d, D, deadline, rng, consider):
    """Prune redundant edges first (frees degree), then run split-repair from the result."""
    if time.monotonic() >= deadline:
        return
    pe = _prune_redundant(n, edges, D, rng, deadline, 160)
    n2, e2 = _grow(n, pe, d, D, deadline, rng)
    consider(n2, e2)
    _split_repair(n2, e2, d, D, deadline, rng, consider)


# ----------------------------------------------------------------------------
# Repair with an added vertex.
# ----------------------------------------------------------------------------

def _repair(d, D, n, edges, deadline, rng, consider):
    """Repeatedly try to add one vertex to the current valid graph, repairing with annealing."""
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        snap_adj = [set(s) for s in adj]
        snap_color = list(color)
        side = rng.randrange(2)
        _add_vertex(adj, color, d, D, side, rng)
        _fill(adj, color, d, rng)
        if _anneal(adj, color, d, D, rng, 1500, deadline):
            m = len(adj)
            e = [(u, v) for u in range(m) for v in adj[u] if u < v]
            consider(m, e)
        else:
            adj[:] = snap_adj
            color[:] = snap_color


# ----------------------------------------------------------------------------
# Glue: parent pipeline and the C bi-Cayley phase.
# ----------------------------------------------------------------------------

def _parent_search(d, D, rng, start, span, st, consider):
    """Structured base, cover growth, randomized pipelines, LNS, pruning, splitting, repair."""

    def at(f):
        return start + f * span

    base_n, base_e = lib.haar_graph(d, range(d))
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            base_n, base_e = base
            consider(base_n, base_e)
            n1, e1 = _grow(base_n, base_e, d, D, at(0.2), rng)
            consider(n1, e1)
    if D >= 2 and 2 * base_n <= lib.moore_bound(d, D):
        _try_doubling(base_n, base_e, d, D, at(0.2), rng, consider)
    if D >= 2:
        while time.monotonic() < at(0.1):
            n, e = _trial(base_n, base_e, d, D, rng, at(0.1))
            consider(n, e)
    if D >= 2:
        _lns(st["n"], st["e"], d, D, at(0.5), rng, consider)
        _prune_regrow(st["n"], st["e"], d, D, at(0.66), rng, consider)
        _prune_then_split(st["n"], st["e"], d, D, at(0.79), rng, consider)
        _repair(d, D, st["n"], st["e"], at(1.0), rng, consider)


def _bicayley_phase(d, D, st, seed, budget, consider):
    """Run the C bi-Cayley engine; it only reports graphs larger than the start graph."""
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                         stdin_graph=(st["n"], st["e"]), timeout=budget + 30.0)
        n, e = lib.parse_graph_text(text)
    except (RuntimeError, ValueError):
        return
    if n > 0:
        consider(n, e)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    T = float(time_limit)
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    st = {"n": 0, "e": []}
    st["n"], st["e"] = lib.haar_graph(d, range(d))  # K_{d,d} fallback

    def consider(n, e):
        if n > st["n"] and lib.is_valid(n, e, d, D):
            st["n"], st["e"] = n, list(e)

    # Phase A: parent pipeline (structured base, growth, LNS, pruning, repair).
    if D >= 2:
        _parent_search(d, D, rng, t0, 0.50 * T, st, consider)

    # Phase B: bi-Cayley search in C, seeded with the best graph so far as threshold.
    if D >= 3 and d >= 3:
        _bicayley_phase(d, D, st, seed, 0.30 * T, consider)

    # Phase C: LNS from the best graph found, until 88% of the budget.
    if D >= 2 and time.monotonic() < t0 + 0.88 * T:
        _lns(st["n"], st["e"], d, D, t0 + 0.88 * T, rng, consider)

    if not lib.is_valid(st["n"], st["e"], d, D):
        return lib.haar_graph(d, range(d))
    return st["n"], list(st["e"])
