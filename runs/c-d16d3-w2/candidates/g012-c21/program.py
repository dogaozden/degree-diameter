import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: tabu search for arc-extended projective plane graphs (diameter 3).
#
# Input: the incidence graph of PG(2, q), points 0..m-1, lines m..2m-1.
# Let s = d - (q+1) be the spare degree of every old vertex. Choose
#   SA: points, each gets a new A-vertex joined to its q+1 lines;
#       each line may hold at most s chosen points.
#   SB: lines, each gets a new B-vertex joined to its q+1 points;
#       each point may lie on at most s chosen lines.
# The two sides are independent. Each side is a "fixed-size overload"
# tabu search: keep a set S, minimise the total overload V = sum_t max(0,
# load_t - s), and grow S whenever V reaches 0. Output: the extended graph.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef struct { int nc, nt; int *off; int *adj; } Side;

typedef struct {
    const Side *S;
    int cap;
    int *inS;
    int *load;
    int V;
    int size;
} St;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static void st_add(St *st, int x) {
    const Side *S = st->S;
    for (int k = S->off[x]; k < S->off[x + 1]; k++) {
        int t = S->adj[k];
        if (st->load[t] >= st->cap) st->V++;
        st->load[t]++;
    }
    st->inS[x] = 1;
    st->size++;
}

static void st_rem(St *st, int x) {
    const Side *S = st->S;
    for (int k = S->off[x]; k < S->off[x + 1]; k++) {
        int t = S->adj[k];
        st->load[t]--;
        if (st->load[t] >= st->cap) st->V--;
    }
    st->inS[x] = 0;
    st->size--;
}

static int st_adddelta(const St *st, int y) {
    const Side *S = st->S;
    int c = 0;
    for (int k = S->off[y]; k < S->off[y + 1]; k++)
        if (st->load[S->adj[k]] >= st->cap) c++;
    return c;
}

static void perturb(St *st, int nc, long *tabu, long it) {
    for (int r = 0; r < 2 && st->size > 0; r++) {
        int x;
        do { x = rndi(nc); } while (!st->inS[x]);
        st_rem(st, x);
        tabu[x] = it + 3;
    }
    for (int r = 0; r < 2 && st->size < nc; r++) {
        int y;
        do { y = rndi(nc); } while (st->inS[y]);
        st_add(st, y);
        tabu[y] = it + 3;
    }
}

static void restore(St *st, const int *best, int nc) {
    for (int x = 0; x < nc; x++) if (st->inS[x]) st_rem(st, x);
    for (int x = 0; x < nc; x++) if (best[x]) st_add(st, x);
}

/* Largest set of candidates with every target hit at most cap times.
   Writes flags into best and returns its size. */
static int search_side(const Side *S, int cap, double deadline, int *best) {
    int nc = S->nc;
    memset(best, 0, nc * sizeof(int));
    if (cap <= 0 || nc == 0) return 0;

    St st;
    st.S = S;
    st.cap = cap;
    st.V = 0;
    st.size = 0;
    st.inS = calloc(nc, sizeof(int));
    st.load = calloc(S->nt, sizeof(int));
    long *tabu = calloc(nc, sizeof(long));
    int *perm = malloc(nc * sizeof(int));

    for (int i = 0; i < nc; i++) perm[i] = i;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int tmp = perm[i];
        perm[i] = perm[j];
        perm[j] = tmp;
    }
    for (int i = 0; i < nc; i++) {
        int x = perm[i], ok = 1;
        for (int k = S->off[x]; k < S->off[x + 1]; k++)
            if (st.load[S->adj[k]] >= cap) { ok = 0; break; }
        if (ok) st_add(&st, x);
    }

    int bestSize = st.size;
    memcpy(best, st.inS, nc * sizeof(int));

    long it = 0, lastImp = 0;
    int bestVseen = INT32_MAX;
    const long STAG = 3000;

    while (1) {
        it++;
        if ((it & 7) == 0 && now() > deadline) break;

        if (st.V == 0) {
            if (st.size > bestSize) {
                bestSize = st.size;
                memcpy(best, st.inS, nc * sizeof(int));
            }
            int bx = -1, bd = INT32_MAX, ties = 0;
            for (int y = 0; y < nc; y++) {
                if (st.inS[y] || tabu[y] > it) continue;
                int dd = st_adddelta(&st, y);
                if (dd < bd) { bd = dd; bx = y; ties = 1; }
                else if (dd == bd) { ties++; if (rndi(ties) == 0) bx = y; }
            }
            if (bx < 0) {
                memset(tabu, 0, nc * sizeof(long));
                continue;
            }
            st_add(&st, bx);
            tabu[bx] = it + 2 + rndi(4);
            bestVseen = INT32_MAX;
            lastImp = it;
            continue;
        }

        /* Repair: best swap (remove x in S, add y outside S) by resulting overload. */
        int bNV = INT32_MAX, bx = -1, by = -1, ties = 0;
        for (int x = 0; x < nc; x++) {
            if (!st.inS[x] || tabu[x] > it) continue;
            st_rem(&st, x);
            int Vr = st.V;
            for (int y = 0; y < nc; y++) {
                if (y == x || st.inS[y] || tabu[y] > it) continue;
                int nv = Vr + st_adddelta(&st, y);
                if (nv < bNV) { bNV = nv; bx = x; by = y; ties = 1; }
                else if (nv == bNV) { ties++; if (rndi(ties) == 0) { bx = x; by = y; } }
            }
            st_add(&st, x);
        }
        if (bx < 0) {
            perturb(&st, nc, tabu, it);
            continue;
        }
        st_rem(&st, bx);
        st_add(&st, by);
        int tt = 3 + rndi(6);
        tabu[bx] = it + tt;
        tabu[by] = it + tt;

        if (st.V < bestVseen) { bestVseen = st.V; lastImp = it; }
        if (it - lastImp > STAG) {
            if (st.V > 0 && bestSize > 0) restore(&st, best, nc);
            perturb(&st, nc, tabu, it);
            bestVseen = INT32_MAX;
            lastImp = it;
        }
    }

    if (st.V == 0 && st.size > bestSize) {
        bestSize = st.size;
        memcpy(best, st.inS, nc * sizeof(int));
    }
    free(st.inS);
    free(st.load);
    free(tabu);
    free(perm);
    return bestSize;
}

static void build_csr(Side *S, int nc, int m, const int *src, const int *dst) {
    S->nc = nc;
    S->nt = nc;
    S->off = calloc(nc + 1, sizeof(int));
    S->adj = malloc((m > 0 ? m : 1) * sizeof(int));
    for (int i = 0; i < m; i++) S->off[src[i] + 1]++;
    for (int i = 0; i < nc; i++) S->off[i + 1] += S->off[i];
    int *pos = malloc((nc + 1) * sizeof(int));
    memcpy(pos, S->off, (nc + 1) * sizeof(int));
    for (int i = 0; i < m; i++) S->adj[pos[src[i]]++] = dst[i];
    free(pos);
}

int main(int argc, char **argv) {
    int d = argc > 1 ? atoi(argv[1]) : 3;
    unsigned long seed = argc > 3 ? strtoul(argv[3], NULL, 10) : 1UL;
    double budget = argc > 4 ? atof(argv[4]) : 5.0;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    int *ea = malloc((m > 0 ? m : 1) * sizeof(int));
    int *eb = malloc((m > 0 ? m : 1) * sizeof(int));
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &ea[i], &eb[i]) != 2) { m = i; break; }
    }

    int mp = n / 2;
    int ok = (n >= 2 && n % 2 == 0);
    int *pa = malloc((m > 0 ? m : 1) * sizeof(int));
    int *pl = malloc((m > 0 ? m : 1) * sizeof(int));
    for (int i = 0; ok && i < m; i++) {
        int a = ea[i] < eb[i] ? ea[i] : eb[i];
        int b = ea[i] < eb[i] ? eb[i] : ea[i];
        if (a < 0 || b >= n || a >= mp || b < mp) ok = 0;
        else { pa[i] = a; pl[i] = b - mp; }
    }
    if (!ok) {
        printf("%d %d\n", n, m);
        for (int i = 0; i < m; i++) printf("%d %d\n", ea[i], eb[i]);
        return 0;
    }

    int *dp = calloc(mp, sizeof(int));
    for (int i = 0; i < m; i++) dp[pa[i]]++;
    int maxdeg = 0;
    for (int i = 0; i < mp; i++) if (dp[i] > maxdeg) maxdeg = dp[i];
    int s = d - maxdeg;
    if (s < 0) s = 0;

    Side A, B;
    build_csr(&A, mp, m, pa, pl);   /* point -> lines */
    build_csr(&B, mp, m, pl, pa);   /* line  -> points */

    int *fA = calloc(mp, sizeof(int));
    int *fB = calloc(mp, sizeof(int));
    double t0 = now();
    search_side(&A, s, t0 + 0.5 * budget, fA);
    search_side(&B, s, t0 + budget, fB);

    int nA = 0, nB = 0;
    for (int i = 0; i < mp; i++) { nA += fA[i]; nB += fB[i]; }
    long E = m;
    for (int P = 0; P < mp; P++) if (fA[P]) E += A.off[P + 1] - A.off[P];
    for (int L = 0; L < mp; L++) if (fB[L]) E += B.off[L + 1] - B.off[L];

    printf("%d %ld\n", n + nA + nB, E);
    for (int i = 0; i < m; i++) printf("%d %d\n", ea[i], eb[i]);
    int t = 0;
    for (int P = 0; P < mp; P++) {
        if (!fA[P]) continue;
        for (int k = A.off[P]; k < A.off[P + 1]; k++)
            printf("%d %d\n", n + t, mp + A.adj[k]);
        t++;
    }
    t = 0;
    for (int L = 0; L < mp; L++) {
        if (!fB[L]) continue;
        for (int k = B.off[L]; k < B.off[L + 1]; k++)
            printf("%d %d\n", n + nA + t, B.adj[k]);
        t++;
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python helpers: plane bounds, greedy fallback for the arc extension.
# ----------------------------------------------------------------------------

def _plane_bound(d, q):
    """Rough upper bound on the order of the arc extension of PG(2, q) for max degree d."""
    s = d - q - 1
    mm = q * q + q + 1
    return 2 * mm + 2 * s * mm // (q + 1)


def _greedy(m, s, nbr, rng, trials):
    """Randomized greedy: choose elements so that every target is hit by at most s chosen ones."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _py_extension(d, q, seed):
    """Python fallback for the C tabu search: greedy arc extension of PG(2, q)."""
    m2, edges = lib.projective_plane_incidence(q)
    m = m2 // 2
    s = d - (q + 1)
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    rng = random.Random(seed)
    SA = _greedy(m, s, point_lines, rng, 30)
    SB = _greedy(m, s, line_points, rng, 30)
    E = list(edges)
    n = m2
    for t, P in enumerate(SA):
        for L in point_lines[P]:
            E.append((n + t, m + L))
    base = n + len(SA)
    for t, j in enumerate(SB):
        for Q in line_points[j]:
            E.append((Q, base + t))
    return base + len(SB), E


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (for D >= 5).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    def left():
        return start + 0.85 * time_limit - time.monotonic()

    # Arc-extended projective plane graphs (diameter 3, valid for all D >= 3).
    # The C tabu search finds the two independent spare-degree sets SA, SB.
    if D >= 3:
        qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]
        qs.sort(key=lambda q: -_plane_bound(d, q))
        shares = (0.8, 0.9)
        for idx, q in enumerate(qs[:2]):
            m2, pe = lib.projective_plane_incidence(q)
            consider(m2, pe)
            if d - (q + 1) <= 0:
                continue
            budget = shares[idx] * max(0.0, left() - 1.0)
            if budget < 1.0:
                continue
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed + idx, round(budget, 2)],
                                stdin_graph=(m2, pe), timeout=budget + 15.0)
                n_c, e_c = lib.parse_graph_text(out)
            except Exception:
                n_c, e_c = _py_extension(d, q, seed + idx)
            consider(n_c, e_c)

    if D >= 4 and left() > 2.0:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed group voltage lifts: only worth the time for larger diameters.
    if D >= 5:
        rng = random.Random(seed)
        ks = [1, 2, 2, 3, 4]
        deadline = start + 0.85 * time_limit
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
