"""Voltage lifts of small bipartite bases for the weakest target (d=4, D=7).

This is a deliberate change of construction. The parent searched explicit group lifts (PSL/PGL(2,p) times Z_k
and semidirect products). This version drops that search and instead takes known algebraic bases (PG(2,3),
W(3), and the split Cayley hexagon H(3)) and searches for cyclic voltage lifts Z_m. A lift of a base with
b vertices and m voltages has b*m vertices and keeps the base degree. Diameter is checked with an
orbit-reduced BFS from one representative per base vertex, since Z_m acts regularly on each fibre.

The C engine takes the bases as one disjoint-union graph on stdin, finds the connected components, fixes a
spanning tree to voltage 0 (a gauge choice), and runs simulated annealing over the non-tree voltages to
drive the count of pairs at distance > D to zero. Tasks are (base, m) pairs with lifted order above the
floor, sorted by order and time-sliced.

Risk: the parent's group-lift search is removed. If no lift of order above the floor is found, this
returns the best verified algebraic base (H(3), 728 vertices), which is below the 840 record. Every returned
graph is checked with lib.is_valid before use.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Cyclic voltage-lift search over a set of bipartite base graphs.
 * Usage:   prog d D seed budget floor   < union_of_bases
 * stdin:   "n m" then m lines "u v"; connected components are the bases.
 * stdout:  "n m" then m lines "u v" for the largest verified lift, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXIN 4096
#define MAXIE 16384
#define MAXV 1024
#define MAXBE 4096
#define MAXDEG 32
#define MAXBASE 8
#define MAXLIFT 8192
#define MAXTASK 64
#define MAXCAND 4096
#define MAXOUTE 65536
#define SPAN 10

static int d, D;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

typedef struct {
    int nb, mb, ok;
    int eu[MAXBE], ev[MAXBE];      /* eu on side 0, ev on side 1 */
    int bd[MAXV];
    int inc[MAXV][MAXDEG];
    int tree[MAXBE];
    int nfree, freeE[MAXBE];
} Base;

static Base B[MAXBASE];
static int nbase = 0;

static int inN = 0, inM = 0;
static int inU[MAXIE], inV[MAXIE];
static int adjn[MAXIN], adjv[MAXIN][MAXDEG];
static int colr[MAXIN], compv[MAXIN], loc[MAXIN], cbad[MAXIN], bidx[MAXIN], que[MAXIN];

static void read_input(void) {
    if (scanf("%d %d", &inN, &inM) != 2 || inN < 0 || inN > MAXIN || inM < 0 || inM > MAXIE) {
        inN = inM = 0;
        return;
    }
    int good = 0;
    for (int e = 0; e < inM; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= inN || v >= inN || u == v) break;
        inU[e] = u;
        inV[e] = v;
        good++;
    }
    inM = good;
}

static void build_bases(void) {
    static int cnt[MAXIN];
    nbase = 0;
    if (inN <= 0 || inM <= 0) return;
    for (int v = 0; v < inN; v++) { adjn[v] = 0; colr[v] = -1; }
    for (int e = 0; e < inM; e++) {
        int u = inU[e], v = inV[e];
        if (adjn[u] >= MAXDEG || adjn[v] >= MAXDEG) return;
        adjv[u][adjn[u]++] = v;
        adjv[v][adjn[v]++] = u;
    }
    int ncomp = 0;
    for (int s = 0; s < inN; s++) {
        if (colr[s] != -1) continue;
        int head = 0, tail = 0;
        colr[s] = 0;
        compv[s] = ncomp;
        cbad[ncomp] = 0;
        que[tail++] = s;
        while (head < tail) {
            int v = que[head++];
            for (int k = 0; k < adjn[v]; k++) {
                int w = adjv[v][k];
                if (colr[w] == -1) {
                    colr[w] = 1 - colr[v];
                    compv[w] = ncomp;
                    que[tail++] = w;
                } else if (colr[w] == colr[v]) {
                    cbad[ncomp] = 1;
                }
            }
        }
        ncomp++;
    }
    for (int c = 0; c < ncomp; c++) cnt[c] = 0;
    for (int v = 0; v < inN; v++) loc[v] = cnt[compv[v]]++;
    for (int c = 0; c < ncomp; c++) {
        bidx[c] = -1;
        if (cbad[c] || cnt[c] < 2 || cnt[c] > MAXV || nbase >= MAXBASE) continue;
        bidx[c] = nbase;
        B[nbase].nb = cnt[c];
        B[nbase].mb = 0;
        B[nbase].ok = 1;
        nbase++;
    }
    for (int e = 0; e < inM; e++) {
        int u = inU[e], v = inV[e], c = compv[u];
        if (bidx[c] < 0) continue;
        Base *b = &B[bidx[c]];
        int x = colr[u] == 0 ? u : v;
        int y = (x == u) ? v : u;
        if (b->mb >= MAXBE) { b->ok = 0; continue; }
        b->eu[b->mb] = loc[x];
        b->ev[b->mb] = loc[y];
        b->mb++;
    }
    for (int i = 0; i < nbase; i++) {
        Base *b = &B[i];
        if (!b->ok) continue;
        int nb = b->nb;
        for (int v = 0; v < nb; v++) b->bd[v] = 0;
        for (int e = 0; e < b->mb && b->ok; e++) {
            int a = b->eu[e], c = b->ev[e];
            if (b->bd[a] >= MAXDEG || b->bd[c] >= MAXDEG) { b->ok = 0; break; }
            b->inc[a][b->bd[a]++] = e;
            b->inc[c][b->bd[c]++] = e;
        }
        if (!b->ok) continue;
        int seen[MAXV], vq[MAXV], head = 0, tail = 0;
        for (int v = 0; v < nb; v++) seen[v] = 0;
        for (int e = 0; e < b->mb; e++) b->tree[e] = 0;
        seen[0] = 1;
        vq[tail++] = 0;
        while (head < tail) {
            int v = vq[head++];
            for (int k = 0; k < b->bd[v]; k++) {
                int e = b->inc[v][k];
                int w = (b->eu[e] == v) ? b->ev[e] : b->eu[e];
                if (!seen[w]) {
                    seen[w] = 1;
                    b->tree[e] = 1;
                    vq[tail++] = w;
                }
            }
        }
        if (tail != nb) { b->ok = 0; continue; }
        b->nfree = 0;
        for (int e = 0; e < b->mb; e++)
            if (!b->tree[e]) b->freeE[b->nfree++] = e;
    }
}

typedef struct { long n; int b, m; } Cand;
static Cand cand[MAXCAND];
static int ncand = 0;

static int cmp_cand(const void *a, const void *b) {
    long x = ((const Cand *)a)->n, y = ((const Cand *)b)->n;
    return (x > y) - (x < y);
}

static void make_tasks(long minN) {
    long moore = moore_bound();
    ncand = 0;
    for (int i = 0; i < nbase; i++) {
        Base *b = &B[i];
        if (!b->ok) continue;
        long nb = b->nb;
        long lo = (minN + nb - 1) / nb;
        if (lo < 2) lo = 2;
        long hi = moore / nb;
        if (hi > lo + SPAN) hi = lo + SPAN;
        if (hi * nb > MAXLIFT) hi = MAXLIFT / nb;
        for (long m = lo; m <= hi && ncand < MAXCAND; m++) {
            cand[ncand].n = nb * m;
            cand[ncand].b = i;
            cand[ncand].m = (int)m;
            ncand++;
        }
    }
    qsort(cand, ncand, sizeof(Cand), cmp_cand);
    if (ncand > MAXTASK) ncand = MAXTASK;
}

/* Voltages on base edges, each in [0, m). Lift vertex (v, x) -> v*m + x. */
static int volt[MAXBE], bestvolt[MAXBE];
static int vis[MAXLIFT], dist_[MAXLIFT], lq[MAXLIFT];
static int stampv = 0;

/* Number of (base vertex s, lift vertex z) pairs with dist((s,0), z) > D. Zero iff diameter <= D. */
static long lift_bad(const Base *b, int m) {
    int nb = b->nb;
    long N = (long)nb * m, bad = 0;
    for (int s = 0; s < nb; s++) {
        stampv++;
        int src = s * m;
        int head = 0, tail = 0;
        lq[tail++] = src;
        vis[src] = stampv;
        dist_[src] = 0;
        while (head < tail) {
            int v = lq[head++];
            int dv = dist_[v];
            if (dv >= D) continue;
            int bv = v / m, x = v - bv * m;
            const int *lst = b->inc[bv];
            int deg = b->bd[bv];
            for (int k = 0; k < deg; k++) {
                int e = lst[k], w, y;
                if (b->eu[e] == bv) {
                    w = b->ev[e];
                    y = x + volt[e];
                    if (y >= m) y -= m;
                } else {
                    w = b->eu[e];
                    y = x - volt[e];
                    if (y < 0) y += m;
                }
                int u = w * m + y;
                if (vis[u] != stampv) {
                    vis[u] = stampv;
                    dist_[u] = dv + 1;
                    lq[tail++] = u;
                }
            }
        }
        bad += N - tail;
    }
    return bad;
}

/* Simulated annealing over the non-tree voltages of one (base, m) task. Returns the best bad count. */
static long run_task(int bi, int m, double until) {
    Base *b = &B[bi];
    for (int e = 0; e < b->mb; e++) volt[e] = 0;
    for (int f = 0; f < b->nfree; f++) volt[b->freeE[f]] = rndint(m);
    long cur = lift_bad(b, m);
    long best = cur;
    memcpy(bestvolt, volt, sizeof(int) * (size_t)b->mb);
    double T = 3.0;
    long it = 0;
    while (best > 0 && b->nfree > 0) {
        if ((it & 15) == 0 && now() > until) break;
        it++;
        int e = b->freeE[rndint(b->nfree)];
        int old = volt[e];
        volt[e] = (old + 1 + rndint(m - 1)) % m;
        long nbad = lift_bad(b, m);
        if (nbad <= cur || rnd01() < exp((double)(cur - nbad) / T)) {
            cur = nbad;
            if (cur < best) {
                best = cur;
                memcpy(bestvolt, volt, sizeof(int) * (size_t)b->mb);
            }
        } else {
            volt[e] = old;
        }
        T *= 0.9995;
        if (T < 0.3) T = 3.0;
    }
    return best;
}

static int bestN = 0, bestM = 0;
static int bestEu[MAXOUTE], bestEv[MAXOUTE];

static void record(const Base *b, int m) {
    long N = (long)b->nb * m;
    long M = (long)b->mb * m;
    if (N <= bestN || M > MAXOUTE) return;
    int k = 0;
    for (int e = 0; e < b->mb; e++)
        for (int x = 0; x < m; x++) {
            bestEu[k] = b->eu[e] * m + x;
            bestEv[k] = b->ev[e] * m + (x + bestvolt[e]) % m;
            k++;
        }
    bestN = (int)N;
    bestM = k;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed budget [floor] < union_of_bases\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    long minN = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    read_input();
    build_bases();
    ncand = 0;
    if (d >= 2 && D >= 2) make_tasks(minN);

    double until_all = t0 + budget;
    for (int t = 0; t < ncand; t++) {
        double left = until_all - now();
        if (left < 0.05) break;
        double slice = left / (ncand - t);
        Cand *c = &cand[t];
        long best = run_task(c->b, c->m, now() + slice);
        if (best == 0) record(&B[c->b], c->m);
    }

    if (bestN > 0) {
        printf("%d %d\n", bestN, bestM);
        for (int k = 0; k < bestM; k++) printf("%d %d\n", bestEu[k], bestEv[k]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''

_KNOWN_RECORD = {(4, 7): 840}


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _gh_h3():
    """Incidence graph of the split Cayley hexagon H(3): 364 + 364 vertices, degree 4, diameter 6.

    Returns None if no sign convention verifies with lib.is_valid.
    """
    q = 3

    def norm(v):
        c = next(x for x in v if x)
        inv = 1 if c == 1 else 2
        return tuple((x * inv) % q for x in v)

    vecs = itertools.product(range(q), repeat=7)
    pts = sorted({norm(v) for v in vecs if any(v) and
                  (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % q == 0})
    P = len(pts)
    index = {p: i for i, p in enumerate(pts)}

    def bil(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] +
                x[2] * y[6] + x[6] * y[2] + x[3] * y[3]) % q

    def pl(x, y, i, j):
        return (x[i] * y[j] - x[j] * y[i]) % q

    conds = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)),
             ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]
    combos = ((1, 0), (0, 1), (1, 1), (1, 2))
    for s in (1, -1):
        lines = set()
        for i in range(P):
            x = pts[i]
            for j in range(i + 1, P):
                y = pts[j]
                if bil(x, y):
                    continue
                if any((pl(x, y, *a) - s * pl(x, y, *b)) % q for a, b in conds):
                    continue
                L = frozenset(index[norm(tuple((a * x[k] + b * y[k]) % q for k in range(7)))]
                              for a, b in combos)
                lines.add(L)
        if len(lines) != P or any(len(L) != 4 for L in lines):
            continue
        ordered = sorted(lines, key=sorted)
        edges = [(p, P + j) for j, L in enumerate(ordered) for p in L]
        n = P + len(ordered)
        if lib.is_valid(n, edges, 4, 6):
            return n, edges
    return None


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidate bases (may be empty). Each is checked before use."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    if d == 4 and D >= 6:
        try:
            gh = _gh_h3()
        except Exception:
            gh = None
        if gh is not None:
            out.append(gh)
    return out


def _union(graphs):
    """Disjoint union of (n, edges) graphs, so the C engine sees each one as a component."""
    total = 0
    edges = []
    for n, e in graphs:
        edges.extend((u + total, v + total) for u, v in e)
        total += n
    return total, edges


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    bases = []
    for n, e in known_starts(d, D):
        if lib.is_valid(n, e, d, D):
            bases.append((n, e))
            if n > best[0]:
                best = (n, e)

    if d > 31 or not bases or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.88 * time_limit - (time.monotonic() - t0) - 3.0
    if budget < 2.0:
        return best

    floor = max(best[0], _KNOWN_RECORD.get((d, D), 0)) + 1
    un, ue = _union(bases)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), floor],
                         stdin_graph=(un, ue), timeout=budget + 8.0)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except Exception:
        pass
    return best
