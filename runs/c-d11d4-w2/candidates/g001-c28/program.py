import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine A (parent): simulated annealing on a fixed vertex set, adding one
# isolated vertex to a start graph and repairing it. Prints "0 0" on failure.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static int N, DEGMAX, DIAM, W, EM, CM, CAP;
static int *eu, *ev, *cu, *cv;
static int *side, *deg, *off, *adj, *cdeg, *coff, *cadj;
static int *pos, *sp0, *sp1, *bfsq;
static u64 *bx, *by;
static u64 rs;

static u64 rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (u64)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int *ialloc(size_t k) {
    int *p = (int *)calloc(k ? k : 1, sizeof(int));
    if (!p) exit(0);
    return p;
}

static void build_csr(int m, const int *a, const int *b, int *dg, int *of, int *ad) {
    int i;
    for (i = 0; i < N; i++) dg[i] = 0;
    for (i = 0; i < m; i++) { dg[a[i]]++; dg[b[i]]++; }
    of[0] = 0;
    for (i = 0; i < N; i++) of[i + 1] = of[i] + dg[i];
    for (i = 0; i < N; i++) pos[i] = of[i];
    for (i = 0; i < m; i++) {
        ad[pos[a[i]]++] = b[i];
        ad[pos[b[i]]++] = a[i];
    }
}

static int isadj(const int *dg, const int *of, const int *ad, int x, int y) {
    int i;
    for (i = of[x]; i < of[x] + dg[x]; i++)
        if (ad[i] == y) return 1;
    return 0;
}

static long long bad_cost(const int *dg, const int *of, const int *ad) {
    u64 *X = bx, *Y = by, *t;
    int v, r, w, i;
    long long cov = 0;
    memset(X, 0, sizeof(u64) * (size_t)N * (size_t)W);
    for (v = 0; v < N; v++) X[(size_t)v * W + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (r = 0; r < DIAM; r++) {
        for (v = 0; v < N; v++) {
            u64 *y = Y + (size_t)v * W;
            const u64 *x = X + (size_t)v * W;
            memcpy(y, x, sizeof(u64) * (size_t)W);
            for (i = of[v]; i < of[v] + dg[v]; i++) {
                const u64 *z = X + (size_t)ad[i] * W;
                for (w = 0; w < W; w++) y[w] |= z[w];
            }
        }
        t = X; X = Y; Y = t;
    }
    for (i = 0; i < N * W; i++) cov += popc(X[i]);
    return ((long long)N * N - cov) / 2;
}

static int collect(int s, int *out) {
    int v, c = 0;
    for (v = 0; v < N; v++)
        if (side[v] == s && deg[v] < DEGMAX) out[c++] = v;
    return c;
}

static int move_add(void) {
    int n0, n1, t, a, b;
    if (CM >= CAP) return 0;
    n0 = collect(0, sp0);
    n1 = collect(1, sp1);
    if (n0 == 0 || n1 == 0) return 0;
    for (t = 0; t < 20; t++) {
        a = sp0[rndint(n0)];
        b = sp1[rndint(n1)];
        if (!isadj(deg, off, adj, a, b)) {
            cu[CM] = a;
            cv[CM] = b;
            CM++;
            return 1;
        }
    }
    return 0;
}

static int move_swap(void) {
    int i, j, a, b, c, e;
    if (CM < 2) return 0;
    i = rndint(CM);
    j = rndint(CM);
    if (i == j) return 0;
    a = cu[i]; b = cv[i];
    c = cu[j]; e = cv[j];
    if (a == c || b == e) return 0;
    if (isadj(deg, off, adj, a, e) || isadj(deg, off, adj, c, b)) return 0;
    cv[i] = e;
    cv[j] = b;
    return 1;
}

static int move_rewire(void) {
    int i, a, b, n, t, c;
    if (CM == 0) return 0;
    i = rndint(CM);
    a = cu[i]; b = cv[i];
    if (rnd() & 1ULL) {
        n = collect(0, sp0);
        for (t = 0; t < 20 && n > 0; t++) {
            c = sp0[rndint(n)];
            if (c != a && !isadj(deg, off, adj, c, b)) { cu[i] = c; return 1; }
        }
    } else {
        n = collect(1, sp1);
        for (t = 0; t < 20 && n > 0; t++) {
            c = sp1[rndint(n)];
            if (c != b && !isadj(deg, off, adj, a, c)) { cv[i] = c; return 1; }
        }
    }
    return 0;
}

static void emit(const int *a, const int *b, int m) {
    int i;
    printf("%d %d\n", N, m);
    for (i = 0; i < m; i++) printf("%d %d\n", a[i], b[i]);
}

int main(int argc, char **argv) {
    int n, m, i, k, s, qh, qt, ok, x, y;
    int *ru, *rv;
    double budget, T, el, frac, r, T0 = 8.0, T1 = 0.25;
    long long cur, cand, delta;
    clock_t c0;

    if (argc < 5) return 1;
    DEGMAX = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    budget = atof(argv[4]);

    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || m < 0) { printf("0 0\n"); return 0; }
    N = n;
    W = (N + 63) / 64;
    CAP = N * DEGMAX + 16;
    if (m > CAP) { printf("0 0\n"); return 0; }

    ru = ialloc(CAP);
    rv = ialloc(CAP);
    for (i = 0; i < m; i++) {
        if (scanf("%d %d", &ru[i], &rv[i]) != 2) { printf("0 0\n"); return 0; }
        if (ru[i] < 0 || ru[i] >= N || rv[i] < 0 || rv[i] >= N || ru[i] == rv[i]) {
            printf("0 0\n");
            return 0;
        }
    }

    side = ialloc(N); deg = ialloc(N); off = ialloc(N + 1); adj = ialloc(2 * CAP);
    cdeg = ialloc(N); coff = ialloc(N + 1); cadj = ialloc(2 * CAP);
    pos = ialloc(N); sp0 = ialloc(N); sp1 = ialloc(N); bfsq = ialloc(N);
    eu = ialloc(CAP); ev = ialloc(CAP); cu = ialloc(CAP); cv = ialloc(CAP);
    bx = (u64 *)calloc((size_t)N * W, sizeof(u64));
    by = (u64 *)calloc((size_t)N * W, sizeof(u64));
    if (!bx || !by) return 0;

    EM = m;
    build_csr(EM, ru, rv, deg, off, adj);
    for (i = 0; i < N; i++) if (deg[i] > DEGMAX) { printf("0 0\n"); return 0; }

    for (i = 0; i < N; i++) side[i] = -1;
    for (s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        qh = 0; qt = 0;
        bfsq[qt++] = s;
        while (qh < qt) {
            x = bfsq[qh++];
            for (k = off[x]; k < off[x] + deg[x]; k++) {
                y = adj[k];
                if (side[y] == -1) {
                    side[y] = 1 - side[x];
                    bfsq[qt++] = y;
                } else if (side[y] == side[x]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    for (i = 0; i < EM; i++) {
        if (side[ru[i]] == 0) { eu[i] = ru[i]; ev[i] = rv[i]; }
        else { eu[i] = rv[i]; ev[i] = ru[i]; }
    }
    build_csr(EM, eu, ev, deg, off, adj);
    cur = bad_cost(deg, off, adj);
    if (cur == 0) { emit(eu, ev, EM); return 0; }

    c0 = clock();
    for (;;) {
        el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= budget) break;
        frac = el / budget;
        T = T0 * pow(T1 / T0, frac);

        memcpy(cu, eu, sizeof(int) * (size_t)EM);
        memcpy(cv, ev, sizeof(int) * (size_t)EM);
        CM = EM;

        r = rnd01();
        if (r < 0.25) ok = move_add();
        else if (r < 0.65) ok = move_swap();
        else ok = move_rewire();
        if (!ok) continue;

        build_csr(CM, cu, cv, cdeg, coff, cadj);
        cand = bad_cost(cdeg, coff, cadj);
        delta = cand - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            int *tp;
            tp = eu; eu = cu; cu = tp;
            tp = ev; ev = cv; cv = tp;
            tp = deg; deg = cdeg; cdeg = tp;
            tp = off; off = coff; coff = tp;
            tp = adj; adj = cadj; cadj = tp;
            EM = CM;
            cur = cand;
            if (cur == 0) { emit(eu, ev, EM); return 0; }
        }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine B (new): subset selection. The host is a larger bipartite graph of
# degree > d (a generalized quadrangle W(q)). The engine anneals over vertex
# subsets S. The cost is bad pairs in the induced subgraph plus degree excess,
# and each kept vertex gives a small reward. Output is the largest feasible
# induced subgraph found, relabelled 0..s-1, or "0 0".
# ----------------------------------------------------------------------------

SUB_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static int N, DEG, DIAM, W;
static int *hoff, *hadj, *dg;
static unsigned char *inS;
static u64 *bx, *by;
static u64 rs;

static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int rndint(int k) { return (int)(rnd() % (u64)k); }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Unordered pairs of kept vertices at distance > DIAM in the induced subgraph. */
static long long eval_bad(int s) {
    u64 *X = bx, *Y = by, *t;
    long long cov = 0;
    int r, v, k, w, u;
    memset(X, 0, sizeof(u64) * (size_t)N * (size_t)W);
    for (v = 0; v < N; v++)
        if (inS[v]) X[(size_t)v * W + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (r = 0; r < DIAM; r++) {
        for (v = 0; v < N; v++) {
            u64 *y = Y + (size_t)v * W;
            if (!inS[v]) { memset(y, 0, sizeof(u64) * (size_t)W); continue; }
            memcpy(y, X + (size_t)v * W, sizeof(u64) * (size_t)W);
            for (k = hoff[v]; k < hoff[v + 1]; k++) {
                u = hadj[k];
                if (!inS[u]) continue;
                {
                    const u64 *z = X + (size_t)u * W;
                    for (w = 0; w < W; w++) y[w] |= z[w];
                }
            }
        }
        t = X; X = Y; Y = t;
    }
    for (k = 0; k < N * W; k++) cov += popc(X[k]);
    return ((long long)s * s - cov) / 2;
}

/* Total excess degree inside S. */
static long long eval_viol(void) {
    long long vi = 0;
    int v;
    for (v = 0; v < N; v++)
        if (inS[v] && dg[v] > DEG) vi += dg[v] - DEG;
    return vi;
}

/* Flip membership of v and update S-neighbour counts of its neighbours. */
static void toggle(int v) {
    int k, delta = inS[v] ? -1 : 1;
    inS[v] ^= 1;
    for (k = hoff[v]; k < hoff[v + 1]; k++) dg[hadj[k]] += delta;
}

int main(int argc, char **argv) {
    int n, m, i, s, v, k, ns;
    int *ea, *eb, *cnt, *fill, *newid;
    unsigned char *bestS;
    double budget, T, el, T0 = 2.0, T1 = 0.05, ALPHA = 0.25, LAM = 1.0;
    long long cur_bad, cur_viol, cb, cv, best_s = -1;
    double cur_f, cand_f, delta;
    clock_t c0;
    int c, me;

    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    budget = atof(argv[4]);

    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || m < 0) { printf("0 0\n"); return 0; }
    N = n;
    W = (N + 63) / 64;
    ea = calloc(m + 1, sizeof(int));
    eb = calloc(m + 1, sizeof(int));
    cnt = calloc(N + 1, sizeof(int));
    if (!ea || !eb || !cnt) return 0;
    for (i = 0; i < m; i++) {
        if (scanf("%d %d", &ea[i], &eb[i]) != 2) { printf("0 0\n"); return 0; }
        if (ea[i] < 0 || ea[i] >= N || eb[i] < 0 || eb[i] >= N || ea[i] == eb[i]) {
            printf("0 0\n");
            return 0;
        }
        cnt[ea[i]]++;
        cnt[eb[i]]++;
    }
    hoff = calloc(N + 1, sizeof(int));
    hadj = calloc(2 * (size_t)m + 1, sizeof(int));
    fill = calloc(N + 1, sizeof(int));
    dg = calloc(N, sizeof(int));
    inS = malloc(N);
    bestS = malloc(N);
    newid = malloc(sizeof(int) * N);
    bx = calloc((size_t)N * W, sizeof(u64));
    by = calloc((size_t)N * W, sizeof(u64));
    if (!hoff || !hadj || !fill || !dg || !inS || !bestS || !newid || !bx || !by) return 0;

    for (v = 0; v < N; v++) hoff[v + 1] = hoff[v] + cnt[v];
    for (v = 0; v < N; v++) fill[v] = hoff[v];
    for (i = 0; i < m; i++) {
        hadj[fill[ea[i]]++] = eb[i];
        hadj[fill[eb[i]]++] = ea[i];
    }
    for (v = 0; v < N; v++) {
        inS[v] = 1;
        dg[v] = cnt[v];
    }

    s = N;
    cur_bad = eval_bad(s);
    cur_viol = eval_viol();
    if (cur_bad == 0 && cur_viol == 0) {
        best_s = s;
        memcpy(bestS, inS, N);
    }

    c0 = clock();
    for (;;) {
        el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= budget) break;
        T = T0 * pow(T1 / T0, el / budget);

        v = rndint(N);
        toggle(v);
        ns = s + (inS[v] ? 1 : -1);
        cb = eval_bad(ns);
        cv = eval_viol();
        cand_f = (double)cb + LAM * (double)cv - ALPHA * (double)ns;
        cur_f = (double)cur_bad + LAM * (double)cur_viol - ALPHA * (double)s;
        delta = cand_f - cur_f;
        if (delta <= 0 || rnd01() < exp(-delta / T)) {
            s = ns;
            cur_bad = cb;
            cur_viol = cv;
            if (cur_bad == 0 && cur_viol == 0 && s > best_s) {
                best_s = s;
                memcpy(bestS, inS, N);
            }
        } else {
            toggle(v);
        }
    }

    if (best_s < 0) { printf("0 0\n"); return 0; }

    c = 0;
    for (v = 0; v < N; v++) newid[v] = bestS[v] ? c++ : -1;
    me = 0;
    for (v = 0; v < N; v++) {
        if (!bestS[v]) continue;
        for (k = hoff[v]; k < hoff[v + 1]; k++)
            if (bestS[hadj[k]] && hadj[k] > v) me++;
    }
    printf("%d %d\n", c, me);
    for (v = 0; v < N; v++) {
        if (!bestS[v]) continue;
        for (k = hoff[v]; k < hoff[v + 1]; k++)
            if (bestS[hadj[k]] && hadj[k] > v)
                printf("%d %d\n", newid[v], newid[hadj[k]]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions
# ----------------------------------------------------------------------------

def _best_gq_q(d):
    """Largest prime power q <= 16 with q + 1 <= d (for the parent's W(q) growth)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return q
    return None


def _host_q(d):
    """Smallest prime power q <= 13 with q + 1 >= d: W(q) has degree q + 1 >= d."""
    for q in range(max(2, d - 1), 14):
        if lib.is_prime_power(q) and q + 1 >= d:
            return q
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
    A = np.array(pts, dtype=np.int64)
    mul, add, neg = F.mul_table, F.add_table, F._neg

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    covered = np.zeros((P, P), dtype=bool)
    lines = []
    for i in range(P):
        x = pts[i]
        # Vectorised symplectic form B(x, y) over all points y.
        t1 = add[mul[x[0], A[:, 1]], neg[mul[x[1], A[:, 0]]]]
        t2 = add[mul[x[2], A[:, 3]], neg[mul[x[3], A[:, 2]]]]
        f = add[t1, t2]
        for j in np.flatnonzero(f == 0):
            j = int(j)
            if j <= i or covered[i, j]:
                continue
            y = pts[j]
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
            idx = np.array(L, dtype=np.int64)
            covered[np.ix_(idx, idx)] = True

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    q = _best_gq_q(d)
    if q is None:
        return None
    return _gq_w(q)


def _prune_stage(d, D, rng, start, end_offset):
    """Anneal a vertex subset of the host W(q) (degree q+1 >= d) into a valid degree-d graph.

    Returns (n, edges) or None. The caller validates the result.
    """
    q = _host_q(d)
    if q is None:
        return None
    host_n, host_e = _gq_w(q)
    if lib.max_degree(host_n, host_e) <= d:
        return host_n, host_e
    remaining = start + end_offset - time.monotonic()
    if remaining < 8.0:
        return None
    budget = remaining - 5.0
    out = lib.run_c(SUB_C, [d, D, rng.randrange(1, 1 << 30), f"{budget:.2f}"],
                    stdin_graph=(host_n, host_e), timeout=remaining - 1.0)
    n, e = lib.parse_graph_text(out)
    if n < 2 or not e:
        return None
    return n, e


# ----------------------------------------------------------------------------
# Twin extension. A twin v of x (same side, N(v) = N(x)) keeps all old distances,
# has dist(v, x) = 2, and preserves bipartiteness. It needs one spare degree on
# each neighbour of x. Twins are added greedily in random passes until none remain.
# ----------------------------------------------------------------------------

def _twin_grow(n, edges, d, rng, deadline):
    """Add twin vertices while every neighbour of the original vertex has spare degree."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
        order = list(range(n))
        rng.shuffle(order)
        for x in order:
            if time.monotonic() >= deadline:
                break
            nb = adj[x]
            if not nb or any(deg[y] >= d for y in nb):
                continue
            v = n
            n += 1
            adj.append(list(nb))
            deg.append(len(nb))
            for y in nb:
                adj[y].append(v)
                deg[y] += 1
                edges.append((y, v))
            changed = True
    return n, edges


def _remove_twins(n, edges, frac, rng):
    """Delete a random fraction of redundant twins; the diameter is preserved."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    classes = {}
    for v in range(n):
        if adj[v]:
            classes.setdefault(frozenset(adj[v]), []).append(v)
    cands = []
    for grp in classes.values():
        if len(grp) >= 2:
            cands.extend(grp[1:])
    if not cands:
        return n, list(edges)
    k = max(1, int(frac * len(cands)))
    drop = set(rng.sample(cands, min(k, len(cands))))
    keep = [v for v in range(n) if v not in drop]
    idx = {v: i for i, v in enumerate(keep)}
    new_e = [(idx[u], idx[v]) for u, v in edges if u not in drop and v not in drop]
    return len(keep), new_e


# ----------------------------------------------------------------------------
# Cover-based vertex extension.
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


def _ball_rows(ball, idx, n):
    """float32 membership matrix: row r is the ball of idx[r] as a 0/1 vector over n vertices."""
    nb = (n + 7) // 8
    out = np.zeros((len(idx), n), dtype=np.float32)
    for r, s in enumerate(idx):
        arr = np.frombuffer(ball[s].to_bytes(nb, "little"), dtype=np.uint8)
        out[r] = np.unpackbits(arr, bitorder="little")[:n]
    return out


def _weighted_cover(sub, cands, n, d, rng, randomize):
    """Rarity-weighted greedy cover of all n vertices by at most d candidate rows of sub."""
    k = sub.shape[0]
    uncovered = np.ones(n, dtype=np.float32)
    avail_b = np.ones(k, dtype=bool)
    chosen = []
    while uncovered.sum() > 0:
        if len(chosen) >= d or not avail_b.any():
            return None
        avail = avail_b.astype(np.float32)
        cnt = avail @ sub
        if np.any((uncovered > 0) & (cnt < 0.5)):
            return None
        w = np.where(uncovered > 0, 1.0 / np.maximum(cnt, 1.0), 0.0).astype(np.float32)
        gain = sub @ w
        gain[~avail_b] = -1.0
        best = float(gain.max())
        if best <= 0:
            return None
        if randomize:
            thr = best * (0.9 if rng.random() < 0.3 else 1.0)
            opts = np.flatnonzero((gain >= thr) & avail_b)
            i = int(opts[rng.randrange(len(opts))])
        else:
            i = int(np.argmax(gain))
        chosen.append(cands[i])
        avail_b[i] = False
        uncovered[sub[i] > 0] = 0.0
    return chosen


def _weighted_cover_search(cands, ball, n, d, rng, tries, deadline):
    """Try several weighted covers (first deterministic, then randomised)."""
    sub = _ball_rows(ball, cands, n)
    for t in range(tries):
        if time.monotonic() >= deadline:
            break
        ch = _weighted_cover(sub, cands, n, d, rng, t > 0)
        if ch:
            return ch
    return None


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
            for attempt in range(40):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if not chosen and time.monotonic() < deadline:
                chosen = _weighted_cover_search(cands, ball, n, d, rng, 15, deadline)
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
    """Extend by cover vertices FIRST, then saturate edges with the remaining spare degree."""
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


def _pipeline(n, edges, d, D, deadline, rng):
    """Alternate twin growth and cover growth until neither adds a vertex."""
    cur_n, cur_e = n, list(edges)
    for _ in range(10):
        if time.monotonic() >= deadline:
            break
        before = cur_n
        cur_n, cur_e = _twin_grow(cur_n, cur_e, d, rng, deadline)
        cur_n, cur_e = _grow(cur_n, cur_e, d, D, deadline, rng)
        if cur_n == before:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Voltage lifts over NON-cyclic groups (semidirect products Z_m x| Z_k2).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(60):
        k2 = rng.randint(1, 12)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 40))
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


def _group_search(d, D, k, G, rng, iters, deadline):
    """Hill-climb dart voltages in a group of order about G over a random d-regular base."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(order)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.group_lift(2 * k, [tuple(x) for x in darts], order, mul)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        if order < 2:
            break
        j = rng.randrange(len(darts))
        old = darts[j][2]
        darts[j][2] = (old + rng.randrange(1, order)) % order
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            darts[j][2] = old
    if c == 0:
        return n, e
    return None


# ----------------------------------------------------------------------------
# Haar and cyclic-lift families, kept for D = 3 and as a secondary family.
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def _search_lift(d, D, k, m, rng, iters, deadline):
    """Hill-climb Z_m voltages on a random d-regular bipartite base with k+k vertices."""
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(m)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.voltage_lift(2 * k, [tuple(x) for x in darts], m)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0:
            break
        if time.monotonic() > deadline:
            break
        touched = [rng.randrange(len(darts))]
        if rng.random() < 0.2:
            touched.append(rng.randrange(len(darts)))
        olds = [(j, darts[j][2]) for j in touched]
        for j in touched:
            if m > 1:
                darts[j][2] = (darts[j][2] + rng.randrange(1, m)) % m
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            for j, old in olds:
                darts[j][2] = old
    if c == 0:
        return n, e
    return None


def _c_grow(d, D, base, seed, remaining):
    """Run the C annealer (engine A) on base plus one isolated vertex. Returns raw (n, edges) or None.

    Results are not trusted here: the caller checks them with lib.is_valid via consider().
    """
    n, edges = base
    budget = max(1.0, (remaining - 3.0) * 0.85)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                        stdin_graph=(n + 1, list(edges)), timeout=remaining - 1.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 <= n or not e2:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    deadline = start + 0.9 * tl
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # D >= 3: projective planes for the few largest prime powers q with q + 1 <= d.
    if D >= 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        if pg_qs:
            ext_deadline = start + (0.15 if D >= 4 else 0.5) * tl
            t0 = time.monotonic()
            span = max(0.0, ext_deadline - t0)
            for i, q in enumerate(pg_qs):
                pg_n, pg_e = lib.projective_plane_incidence(q)
                consider(pg_n, pg_e)
                slice_end = t0 + span * (i + 1) / len(pg_qs)
                n2, e2 = _pipeline(pg_n, pg_e, d, D, slice_end, rng)
                consider(n2, e2)

    # D >= 4 (bold new route): anneal a vertex subset of a larger quadrangle W(q)
    # whose degree is too high, until the induced subgraph has max degree d and
    # diameter <= D. Any failure leaves the fallbacks below in charge.
    sub_graph = None
    if D >= 4:
        try:
            sub_graph = _prune_stage(d, D, rng, start, 0.40 * tl)
        except Exception:
            sub_graph = None
        if sub_graph is not None:
            consider(sub_graph[0], sub_graph[1])

    # D >= 4: growth from the W(q) graph (or the pruned graph if it is larger).
    pipe_end = start + (0.62 if D >= 4 else 0.88) * tl
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if sub_graph is not None and sub_graph[0] > gq[0]:
                base = sub_graph
            else:
                base = gq
            cur = None
            while time.monotonic() < pipe_end:
                if cur is None or rng.random() < 0.2:
                    src_n, src_e = base[0], base[1]
                else:
                    src_n, src_e = _remove_twins(cur[0], cur[1], 0.15, rng)
                pn, pe = _pipeline(src_n, src_e, d, D, pipe_end, rng)
                consider(pn, pe)
                if cur is None or pn >= cur[0]:
                    cur = (pn, pe)

    # D >= 4: single-vertex annealing (engine A) from the current best graph.
    if D >= 4 and best_n > 1:
        c_end = start + 0.80 * tl
        while time.monotonic() < c_end - 6.0:
            before = best_n
            res = _c_grow(d, D, best, rng.randrange(1, 1 << 30), c_end - time.monotonic())
            if res is None:
                break
            consider(res[0], res[1])
            if best_n == before:
                break

    # Main search for the remaining time.
    group_p = 0.85 if D >= 4 else 0.3
    haar_p = 0.35 if D <= 4 else 0.15
    base_sizes = [1, 2, 3, 4, 5, 6]
    group_sizes = [1, 2, 3, 4]
    ladder = {k: 2 for k in base_sizes}
    group_state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
    haar_m, haar_miss = d + 1, 0

    while time.monotonic() < deadline:
        r = rng.random()
        if r < group_p:
            k = rng.choice(group_sizes)
            st = group_state[k]
            floor = best_n // (2 * k) + 1
            G = max(st["G"], floor, 2)
            res = _group_search(d, D, k, G, rng, 200, deadline)
            if res is not None:
                consider(res[0], res[1])
                st["G"] = G + st["step"]
                st["step"] = min(st["step"] * 2, max(1, G // 10))
                st["miss"] = 0
            else:
                st["G"] = G
                st["miss"] += 1
                if st["miss"] >= 3:
                    st["step"] = 1
                    st["miss"] = 0
                    st["G"] = floor
        elif rng.random() < haar_p and haar_miss < 4:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
        else:
            k = rng.choice(base_sizes)
            m = max(ladder[k], best_n // (2 * k) + 1, 2)
            res = _search_lift(d, D, k, m, rng, 250, deadline)
            if res is not None:
                consider(res[0], res[1])
                ladder[k] = m + 1
            else:
                ladder[k] = m

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
