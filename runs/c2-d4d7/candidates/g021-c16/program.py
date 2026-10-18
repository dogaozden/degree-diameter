"""Bold change: voltage-lift an algebraic base graph by simulated annealing over Z_m voltages.

The parent searched explicit group lifts (PSL/PGL(2,p), semidirect products) from scratch. This
version instead takes an algebraic bipartite base graph (for d=4, D>=6 the split Cayley hexagon
H(3) incidence graph, 728 vertices, degree 4) and searches for an m-fold Z_m cover of it with
diameter <= D. Cover order is 728*m, so m=2 gives 1456 vertices against the record 840. The cost is
the orbit-reduced excess distance (BFS from one representative per base vertex). It is zero exactly
when the cover has diameter <= D, and it smooths the landscape. Annealing has elite restarts with
small kicks.

Safety: every returned graph passes lib.is_valid. The fallback is the largest valid algebraic
candidate (K_{d,d}, projective plane, generalized quadrangle, or hexagon). Caveat: the parent's
explicit-group engine was dropped to keep this program compact. If no cover of H(3) reaches diameter
7, the target case returns 728, below the record 840. This is an accepted risk of the experiment.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Voltage-cover search over Z_M for a bipartite base graph.
 * Usage:  prog d D seed budget beat < base
 * stdin:  "n m" then m lines "u v" (simple, bipartite, max degree <= d), or "0 0".
 * stdout: "n m" then the lift, or "0 0" if nothing with order > beat was found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXB 2048
#define MAXE 40000
#define MAXL 8192
#define MAXDEG 32

static int d, D;
static int nb, ne;
static int bdeg[MAXB], bside[MAXB];
static int binc[MAXB][MAXDEG];
static int eu[MAXE], ev[MAXE], volt[MAXE], bestvolt[MAXE], outvolt[MAXE];
static int M, nL;
static int dist[MAXL], qbuf[MAXL];

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long moore_bound(void) {
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000L) break;
    }
    return 2 * s;
}

static int other_end(int e, int u) { return eu[e] == u ? ev[e] : eu[e]; }

static int read_base(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXB || m <= 0 || m > MAXE) return 0;
    nb = n;
    ne = 0;
    for (int v = 0; v < n; v++) bdeg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (bdeg[u] >= d || bdeg[v] >= d) return 0;
        for (int k = 0; k < bdeg[u]; k++)
            if (other_end(binc[u][k], u) == v) return 0;
        eu[ne] = u;
        ev[ne] = v;
        binc[u][bdeg[u]++] = ne;
        binc[v][bdeg[v]++] = ne;
        ne++;
    }
    for (int v = 0; v < nb; v++)
        if (bdeg[v] == 0) return 0;
    for (int v = 0; v < nb; v++) bside[v] = -1;
    static int q[MAXB];
    for (int s = 0; s < nb; s++) {
        if (bside[s] >= 0) continue;
        int head = 0, tail = 0;
        bside[s] = 0;
        q[tail++] = s;
        while (head < tail) {
            int v = q[head++];
            for (int k = 0; k < bdeg[v]; k++) {
                int w = other_end(binc[v][k], v);
                if (bside[w] < 0) {
                    bside[w] = 1 - bside[v];
                    q[tail++] = w;
                } else if (bside[w] == bside[v]) {
                    return 0;
                }
            }
        }
    }
    for (int e = 0; e < ne; e++)
        if (bside[eu[e]] != 0) {
            int t = eu[e];
            eu[e] = ev[e];
            ev[e] = t;
        }
    return 1;
}

/* Orbit-reduced excess distance: BFS from (u,0) for every base vertex u. Unreached vertices
 * cost 2, vertices beyond D cost their excess. Zero iff the cover has diameter <= D. */
static long excess(void) {
    long total = 0;
    for (int u = 0; u < nb; u++) {
        for (int i = 0; i < nL; i++) dist[i] = -1;
        int src = u * M;
        int head = 0, tail = 0;
        dist[src] = 0;
        qbuf[tail++] = src;
        while (head < tail) {
            int v = qbuf[head++];
            int b = v / M, x = v - b * M;
            int dv = dist[v] + 1;
            for (int k = 0; k < bdeg[b]; k++) {
                int e = binc[b][k], w;
                if (bside[b] == 0) w = ev[e] * M + (x + volt[e]) % M;
                else w = eu[e] * M + (x - volt[e] + M) % M;
                if (dist[w] < 0) {
                    dist[w] = dv;
                    qbuf[tail++] = w;
                }
            }
        }
        for (int i = 0; i < nL; i++) {
            if (dist[i] < 0) total += 2;
            else if (dist[i] > D) total += dist[i] - D;
        }
    }
    return total;
}

/* Simulated annealing over the voltages of one cover. Returns 1 with bestvolt set when the
 * cost reaches 0. Each cycle cools geometrically; afterwards the search restarts from the elite
 * with three random voltages changed. */
static int anneal(double until) {
    for (int e = 0; e < ne; e++) volt[e] = rndint(M);
    long cur = excess(), best = cur;
    memcpy(bestvolt, volt, sizeof(int) * (size_t)ne);
    const int CYCLE = 2000;
    while (best > 0) {
        for (int s = 0; s < CYCLE && best > 0; s++) {
            if (now() > until) return 0;
            double T = 3.0 * pow(0.1, (double)s / CYCLE);
            int e = rndint(ne), old = volt[e];
            int nv = rndint(M - 1);
            if (nv >= old) nv++;
            volt[e] = nv;
            long c2 = excess();
            long delta = c2 - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cur = c2;
                if (cur < best) {
                    best = cur;
                    memcpy(bestvolt, volt, sizeof(int) * (size_t)ne);
                }
            } else {
                volt[e] = old;
            }
        }
        if (best == 0) break;
        memcpy(volt, bestvolt, sizeof(int) * (size_t)ne);
        for (int k = 0; k < 3; k++) volt[rndint(ne)] = rndint(M);
        cur = excess();
    }
    return best == 0;
}

static void print_lift(int m) {
    long E = (long)ne * m;
    printf("%d %ld\n", nb * m, E);
    for (int e = 0; e < ne; e++)
        for (int x = 0; x < m; x++)
            printf("%d %d\n", eu[e] * m + x, ev[e] * m + (x + outvolt[e]) % m);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed budget beat < base\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    long beat = atol(argv[5]);
    double deadline = now() + budget * 0.93;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 3 || d > MAXDEG - 1 || D < 2 || !read_base()) {
        printf("0 0\n");
        return 0;
    }
    long moore = moore_bound();
    long Mmax = moore / nb;
    if (Mmax > MAXL / nb) Mmax = MAXL / nb;
    int Mmin = 2;
    while ((long)nb * Mmin <= beat) Mmin++;
    int have = 0, found = 0;
    for (long m = Mmin; m <= Mmax && now() < deadline; m++) {
        M = (int)m;
        nL = nb * M;
        int left = (int)(Mmax - m + 1);
        double until = now() + (deadline - now()) / left;
        if (anneal(until)) {
            have = 1;
            found = M;
            memcpy(outvolt, bestvolt, sizeof(int) * (size_t)ne);
        }
    }
    if (!have) {
        printf("0 0\n");
        return 0;
    }
    print_lift(found);
    return 0;
}
'''


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

    Returns None if no sign convention yields a graph that passes lib.is_valid with diameter 6.
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
    """Algebraic candidate graphs (may be empty). Each has max degree <= d and is bipartite."""
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
        if n <= 0 or not lib.is_bipartite(n, e) or lib.max_degree(n, e) > d:
            continue
        bases.append((n, e))
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D) or not bases:
        return best

    bases.sort(key=lambda g: -g[0])
    moore = lib.moore_bound(d, D)
    end = t0 + 0.85 * time_limit - 2.0
    for i, (n, e) in enumerate(bases):
        if 2 * n > moore:
            continue
        left = end - time.monotonic()
        if left < 2.0:
            break
        frac = 0.7 if (i == 0 and len(bases) > 1) else 1.0 / (len(bases) - i)
        slice_s = round(left * frac, 2)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, slice_s, best[0]],
                             stdin_graph=(n, e), timeout=slice_s + 8)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass
    return best
