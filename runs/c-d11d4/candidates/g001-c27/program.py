import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-lift search over semidirect products Z_m x| Z_kk.
#
# The base graph has K vertices per side and d darts per base vertex (one dart
# per permutation layer). A voltage in G = Z_m x| Z_kk is attached to each dart.
# The lift has 2*K*|G| vertices: (A_i, x) joins (B_b, x*v). Left translation by G
# is an automorphism, so the diameter test only needs BFS from (A_i, e) and
# (B_b, e). Cost = number of (representative, vertex) pairs at distance > D,
# plus a huge penalty for parallel edges. Hill climbing with mild annealing
# runs on voltages and on the base permutations.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

static uint64_t rs_state = 0x9E3779B97F4A7C15ULL;

static uint64_t rnd64(void) {
    rs_state ^= rs_state << 13;
    rs_state ^= rs_state >> 7;
    rs_state ^= rs_state << 17;
    return rs_state;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int dd, DD, KK, GM, GK, GG, NN;
static int *pw, *invt, *P, *Pinv, *V, *stamp, *dist, *qbuf;
static int curstamp = 0;

/* element code x = a*GK + b with a in Z_GM, b in Z_GK; (a,b)(c,e) = (a + r^b c, b+e) */
static inline int gmul(int x, int y) {
    int a = x / GK, b = x - a * GK;
    int c = y / GK, e = y - c * GK;
    long long t = ((long long)a + (long long)pw[b] * (long long)c) % GM;
    int be = b + e;
    if (be >= GK) be -= GK;
    return (int)(t * GK + be);
}

static int reach_from(int src) {
    curstamp++;
    int head = 0, tail = 0;
    int ab = KK * GG;
    qbuf[tail++] = src;
    stamp[src] = curstamp;
    dist[src] = 0;
    while (head < tail) {
        int u = qbuf[head++];
        int du = dist[u];
        if (du >= DD) continue;
        if (u < ab) {
            int i = u / GG, x = u - i * GG;
            for (int j = 0; j < dd; j++) {
                int t = j * KK + i;
                int w = ab + P[t] * GG + gmul(x, V[t]);
                if (stamp[w] != curstamp) {
                    stamp[w] = curstamp;
                    dist[w] = du + 1;
                    qbuf[tail++] = w;
                }
            }
        } else {
            int bb = u - ab;
            int b = bb / GG, y = bb - b * GG;
            for (int j = 0; j < dd; j++) {
                int i = Pinv[j * KK + b];
                int t = j * KK + i;
                int w = i * GG + gmul(y, invt[V[t]]);
                if (stamp[w] != curstamp) {
                    stamp[w] = curstamp;
                    dist[w] = du + 1;
                    qbuf[tail++] = w;
                }
            }
        }
    }
    return tail;
}

static long long eval_cost(void) {
    long long pen = 0;
    for (int i = 0; i < KK; i++)
        for (int j = 0; j < dd; j++)
            for (int j2 = j + 1; j2 < dd; j2++) {
                int t1 = j * KK + i, t2 = j2 * KK + i;
                if (P[t1] == P[t2] && V[t1] == V[t2]) pen++;
            }
    if (pen > 0) return pen * 1000000000LL;
    long long bad = 0;
    for (int i = 0; i < KK; i++) bad += (long long)(NN - reach_from(i * GG));
    for (int b = 0; b < KK; b++) bad += (long long)(NN - reach_from(KK * GG + b * GG));
    return bad;
}

static void swap_perm(int j, int a, int b) {
    int ta = j * KK + a, tb = j * KK + b;
    int pa = P[ta], pb = P[tb];
    P[ta] = pb;
    P[tb] = pa;
    Pinv[j * KK + pb] = a;
    Pinv[j * KK + pa] = b;
}

static void randomize_state(void) {
    int *perm = (int *)malloc(sizeof(int) * (size_t)KK);
    for (int j = 0; j < dd; j++) {
        for (int i = 0; i < KK; i++) perm[i] = i;
        for (int i = KK - 1; i > 0; i--) {
            int k = rndint(i + 1);
            int tmp = perm[i];
            perm[i] = perm[k];
            perm[k] = tmp;
        }
        for (int i = 0; i < KK; i++) {
            P[j * KK + i] = perm[i];
            Pinv[j * KK + perm[i]] = i;
        }
    }
    free(perm);
    for (int t = 0; t < dd * KK; t++) V[t] = rndint(GG);
}

static int search(double budget) {
    randomize_state();
    long long cur = eval_cost();
    long long best_run = cur;
    long stale = 0;
    const double T = 1.0;
    while (cur != 0) {
        if (elapsed() > budget) return 0;
        int kind = 0, t = -1, old = 0, j = -1, a = -1, b = -1;
        if (KK >= 2 && rndint(4) == 0) {
            kind = 1;
            j = rndint(dd);
            a = rndint(KK);
            b = rndint(KK - 1);
            if (b >= a) b++;
            swap_perm(j, a, b);
        } else {
            kind = 0;
            t = rndint(dd * KK);
            old = V[t];
            V[t] = (old + 1 + rndint(GG - 1)) % GG;
        }
        long long nc = eval_cost();
        long long delta = nc - cur;
        int accept = 0;
        if (delta <= 0) accept = 1;
        else if (rnd01() < exp(-(double)delta / T)) accept = 1;
        if (accept) {
            cur = nc;
            if (cur < best_run) {
                best_run = cur;
                stale = 0;
            } else {
                stale++;
            }
        } else {
            if (kind == 0) V[t] = old;
            else swap_perm(j, a, b);
            stale++;
        }
        if (stale > 4000) {
            randomize_state();
            cur = eval_cost();
            best_run = cur;
            stale = 0;
        }
    }
    return 1;
}

static void print_graph(void) {
    int E = KK * GG * dd;
    printf("%d %d\n", NN, E);
    for (int i = 0; i < KK; i++)
        for (int x = 0; x < GG; x++)
            for (int j = 0; j < dd; j++) {
                int t = j * KK + i;
                int u = i * GG + x;
                int w = KK * GG + P[t] * GG + gmul(x, V[t]);
                printf("%d %d\n", u, w);
            }
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int K = atoi(argv[5]), m = atoi(argv[6]), kk = atoi(argv[7]), r = atoi(argv[8]);
    if (d < 2 || D < 2 || K < 1 || m < 1 || kk < 1 || (long long)m * kk < 2 ||
        (long long)K * m * kk > 300000) {
        printf("0 0\n");
        return 0;
    }
    rs_state = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (rs_state == 0) rs_state = 1;

    dd = d;
    DD = D;
    KK = K;
    GM = m;
    GK = kk;
    GG = m * kk;
    NN = 2 * K * GG;
    int rr = r % GM;

    pw = (int *)malloc(sizeof(int) * (size_t)GK);
    pw[0] = 1 % GM;
    for (int b = 1; b < GK; b++) pw[b] = (int)((long long)pw[b - 1] * rr % GM);
    if (GK > 1) {
        if (((long long)pw[GK - 1] * rr) % GM != 1 % GM) {
            printf("0 0\n");
            return 0;
        }
    }

    invt = (int *)malloc(sizeof(int) * (size_t)GG);
    for (int x = 0; x < GG; x++) {
        int a = x / GK, b = x - a * GK;
        int nb = (GK - b) % GK;
        long long v = ((long long)pw[nb] * a) % GM;
        long long an = (GM - v) % GM;
        invt[x] = (int)(an * GK + nb);
    }

    P = (int *)malloc(sizeof(int) * (size_t)(dd * KK));
    Pinv = (int *)malloc(sizeof(int) * (size_t)(dd * KK));
    V = (int *)malloc(sizeof(int) * (size_t)(dd * KK));
    stamp = (int *)calloc((size_t)NN, sizeof(int));
    dist = (int *)malloc(sizeof(int) * (size_t)NN);
    qbuf = (int *)malloc(sizeof(int) * (size_t)NN);

    int found = search(budget);
    if (found) print_graph();
    else printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Base constructions (projective planes and generalized quadrangles).
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
# Cover-based vertex extension (keeps the diameter, adds vertices to deficient sides).
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
    """Two-colouring of a bipartite graph given by adjacency lists."""
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices. Returns the list or None."""
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
    """Extend by cover vertices first, then saturate edges with the remaining spare degree."""
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
# Driver for the C lift search.
# ----------------------------------------------------------------------------

def _pick_group(G, rng):
    """Return (m, kk, r) with m * kk = G giving a semidirect product Z_m x| Z_kk, or None."""
    opts = []
    for kk in range(1, 13):
        if G % kk:
            continue
        m = G // kk
        if m < 1:
            continue
        if kk == 1:
            opts.append((G, 1, 1))
            continue
        if m == 1:
            opts.append((1, kk, 1))
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m]
        if rs:
            opts.append((m, kk, rng.choice(rs)))
    return rng.choice(opts) if opts else None


def _run_lift(d, D, K, m, kk, r, budget, seed):
    """Run the C search for one (K, group) configuration. Returns (n, edges) or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", K, m, kk, r],
                        timeout=budget + 10.0)
        n, edges = lib.parse_graph_text(out)
    except (RuntimeError, ValueError):
        return None
    if n < 2 or not edges:
        return None
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Phase 1: classical base constructions, grown by cover extension (about 25% of budget).
    base_deadline = start + 0.25 * time_limit
    if D == 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:2]
        if pg_qs:
            t0 = time.monotonic()
            span = max(0.0, base_deadline - t0)
            for i, q in enumerate(pg_qs):
                pg_n, pg_e = lib.projective_plane_incidence(q)
                consider(pg_n, pg_e)
                slice_end = t0 + span * (i + 1) / len(pg_qs)
                n2, e2 = _grow(pg_n, pg_e, d, D, slice_end, rng)
                consider(n2, e2)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, base_deadline, rng)
            consider(n2, e2)

    if best_n >= moore:
        return best

    # Phase 2: C bi-lift search over semidirect products, aiming above the current best.
    lift_deadline = start + 0.85 * time_limit - 1.0
    K_choices = [1, 2, 2, 3, 3, 4]
    per_call = max(1.0, min(4.0, 0.04 * time_limit))
    while True:
        now = time.monotonic()
        remaining = lift_deadline - now
        if remaining < 0.5:
            break
        call_budget = min(per_call, remaining)
        K = rng.choice(K_choices)
        Gmin = best_n // (2 * K) + 1
        G = Gmin + rng.randrange(0, max(1, Gmin // 50 + 1))
        grp = _pick_group(G, rng)
        if grp is None:
            continue
        m, kk, r = grp
        res = _run_lift(d, D, K, m, kk, r, call_budget, rng.randrange(1 << 30))
        if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
            best = res
            best_n = res[0]
        if best_n >= moore:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
