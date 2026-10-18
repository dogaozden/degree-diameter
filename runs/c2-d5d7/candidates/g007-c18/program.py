"""Multi-orbit bi-Cayley lift search (replaces the single-orbit grow engine).

Construction: choose p in {1..4} and a semidirect group G = Z_m x|_r Z_k of order N. Base
vertices A_0..A_{p-1} and B_0..B_{p-1}. A circulant base pattern c_s (sum c_s = d) gives c_s darts
from A_i to B_{(i+s) mod p}, each carrying a voltage g in G. Lift: (A_i, x) ~ (B_j, x*g) for every
dart (i -> j, g). Left multiplication by G is an automorphism, so the diameter check needs only
2p BFS runs, from A_i,e and B_j,e. The graph has 2pN vertices and is d-regular and bipartite.

p = 1 is the classic bi-Cayley lift. p >= 2 gives orders that are not single-orbit, which is the
new family. The C engine anneals voltages for random (p, N, G, pattern) windows just above the
current best order. The start graph (hexagon H(4) for d = 5, D = 7, order 2730, or a smaller
algebraic graph) is the fallback, and it is returned unchanged if no lift beats it.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-orbit bi-Cayley lift search over semidirect groups Z_m x|_r Z_k.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0".
 * stdout:  the best valid graph found (a lift if it beats the start, else the start).
 *
 * Vertices: A_i,x = i*N + x (side 0), B_j,y = p*N + j*N + y (side 1), x,y in G, |G| = N.
 * Darts: (i -> j, g) gives edges A_i,x -- B_j,x*g for all x.
 * Base pattern: circulant, from each A_i there are c_s darts to B_{(i+s) mod p}, sum c_s = d.
 * Distinct voltages inside each (i, j) dart group keep the graph simple.
 * Left multiplication by G is an automorphism, transitive on each part-orbit, so diameter <= D
 * is equivalent to BFS from A_i,e and B_j,e (i, j < p) reaching all vertices within D.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXP 4
#define MAXD 16
#define MAXND (MAXP * MAXD)
#define MAXN 8192
#define MAXV 16384
#define MAXE 40000
#define MAXCAND 4096
#define STEPS 6000
#define SPAN 24

typedef struct { int m, k, r; } Grp;

static int d, D;
static double t_end;

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

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

/* Enumerate Z_m x|_r Z_k with m*k = N, gcd(r,m)=1, r^k = 1 mod m. */
static int enum_groups(int N, Grp *out) {
    int cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (cnt < MAXCAND) { out[cnt].m = 1; out[cnt].k = k; out[cnt].r = 0; cnt++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (cnt < MAXCAND) { out[cnt].m = m; out[cnt].k = k; out[cnt].r = r; cnt++; }
        }
    }
    return cnt;
}

static Grp pick_group(const Grp *c, int cnt) {
    for (int tries = 0; tries < 8; tries++) {
        Grp g = c[rndint(cnt)];
        if (g.m > 1 && g.r != 1) return g;
    }
    return c[rndint(cnt)];
}

/* Current group (element (a,b) coded as a*k+b; (a,b)(c,e) = (a + r^b c, b+e)). */
static int GM, GK, GR;
static int NN, NP;
static int RP[MAXN];

static void set_group(Grp G) {
    GM = G.m; GK = G.k; GR = G.r;
    RP[0] = 1 % GM;
    for (int b = 1; b < GK; b++) RP[b] = (int)((long)RP[b - 1] * GR % GM);
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    long t = ((long)a + (long)RP[b] * c) % GM;
    return (int)(t * GK + (b + e) % GK);
}

static inline int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    long t = ((long)RP[nb] * a) % GM;
    t = (GM - t) % GM;
    return (int)(t * GK + nb);
}

/* Darts of the current lift. */
static int nd;
static int DS[MAXND], DD[MAXND], DG[MAXND], DGI[MAXND];
static int OUTL[MAXP][MAXD], INL[MAXP][MAXD];

static void build_lists(void) {
    int co[MAXP] = {0}, ci[MAXP] = {0};
    for (int t = 0; t < nd; t++) {
        OUTL[DS[t]][co[DS[t]]++] = t;
        INL[DD[t]][ci[DD[t]]++] = t;
    }
}

static int dist_[MAXV], seen_[MAXV], q_[MAXV];
static int stamp_ = 0;

/* Number of (source, vertex) pairs at distance > D over sources A_i,e and B_j,e. */
static long eval_bad(void) {
    int N = NN, p = NP, pN = p * N, V = 2 * pN;
    long total = 0;
    for (int s = 0; s < 2 * p; s++) {
        int src = (s < p) ? s * N : pN + (s - p) * N;
        int head = 0, tail = 0;
        stamp_++;
        seen_[src] = stamp_;
        dist_[src] = 0;
        q_[tail++] = src;
        while (head < tail) {
            int v = q_[head++];
            int dv = dist_[v];
            if (dv >= D) continue;
            if (v < pN) {
                int i = v / N, x = v % N;
                for (int z = 0; z < d; z++) {
                    int t = OUTL[i][z];
                    int u = pN + DD[t] * N + gmul(x, DG[t]);
                    if (seen_[u] != stamp_) {
                        seen_[u] = stamp_;
                        dist_[u] = dv + 1;
                        q_[tail++] = u;
                    }
                }
            } else {
                int w = v - pN;
                int j = w / N, y = w % N;
                for (int z = 0; z < d; z++) {
                    int t = INL[j][z];
                    int u = DS[t] * N + gmul(y, DGI[t]);
                    if (seen_[u] != stamp_) {
                        seen_[u] = stamp_;
                        dist_[u] = dv + 1;
                        q_[tail++] = u;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

/* Annealed voltage hill-climb. The dart shape is fixed; only voltages change. */
static long climb(double until) {
    long bad = eval_bad();
    double T = 2.0;
    for (long s = 0; s < STEPS && bad > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = DG[t], oldi = DGI[t];
        int nv = 0, ok = 0;
        for (int tries = 0; tries < 1000 && !ok; tries++) {
            nv = rndint(NN);
            ok = 1;
            for (int u = 0; u < nd; u++)
                if (u != t && DS[u] == DS[t] && DD[u] == DD[t] && DG[u] == nv) { ok = 0; break; }
        }
        if (!ok) continue;
        DG[t] = nv;
        DGI[t] = ginv(nv);
        long nb = eval_bad();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            DG[t] = old;
            DGI[t] = oldi;
        }
        T *= 0.9995;
        if (T < 0.3) T = 0.3;
    }
    return bad;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static int SU[MAXE], SV[MAXE];
    int sn = 0, sm = 0;
    if (scanf("%d %d", &sn, &sm) != 2) { sn = 0; sm = 0; }
    if (sn < 0 || sm < 0 || sm > MAXE) { sn = 0; sm = 0; }
    int got = 0;
    for (int e = 0; e < sm; e++) {
        if (scanf("%d %d", &SU[e], &SV[e]) != 2) break;
        got++;
    }
    if (got != sm) { sn = 0; sm = 0; }

    static int bDS[MAXND], bDD[MAXND], bDG[MAXND];
    static Grp cand[MAXCAND];
    int found = 0, bP = 0, bN = 0, bnd = 0, bGM = 1, bGK = 1, bGR = 0;
    long moore = moore_bound();
    long bestn = sn;

    if (d >= 3 && d <= MAXD && D >= 2) {
        while (now() < t_end) {
            if (bestn >= moore) break;
            int p = 1 + rndint(MAXP);
            long Nlo = bestn / (2L * p) + 1;
            if (Nlo < d + 1) Nlo = d + 1;
            long Nmax = moore / (2L * p);
            if (Nmax > MAXN) Nmax = MAXN;
            if (Nlo > Nmax) continue;
            long span = Nmax - Nlo + 1;
            if (span > SPAN) span = SPAN;
            int N = (int)(Nlo + rndint((int)span));
            int cnt = enum_groups(N, cand);
            if (cnt <= 0) continue;
            Grp G = pick_group(cand, cnt);
            set_group(G);
            NN = N;
            NP = p;

            int c[MAXP] = {0};
            for (int u = 0; u < d; u++) c[rndint(p)]++;
            nd = 0;
            for (int i = 0; i < p; i++)
                for (int s = 0; s < p; s++)
                    for (int u = 0; u < c[s]; u++) {
                        DS[nd] = i;
                        DD[nd] = (i + s) % p;
                        nd++;
                    }
            for (int t = 0; t < nd; t++) {
                int nv, ok;
                do {
                    nv = rndint(N);
                    ok = 1;
                    for (int u = 0; u < t; u++)
                        if (DS[u] == DS[t] && DD[u] == DD[t] && DG[u] == nv) { ok = 0; break; }
                } while (!ok);
                DG[t] = nv;
                DGI[t] = ginv(nv);
            }
            build_lists();
            long bad = climb(t_end);
            if (bad == 0) {
                found = 1;
                bestn = 2L * p * N;
                bP = p; bN = N; bnd = nd;
                bGM = GM; bGK = GK; bGR = GR;
                memcpy(bDS, DS, sizeof(int) * nd);
                memcpy(bDD, DD, sizeof(int) * nd);
                memcpy(bDG, DG, sizeof(int) * nd);
            }
        }
    }

    if (found) {
        Grp g = {bGM, bGK, bGR};
        set_group(g);
        NN = bN;
        NP = bP;
        nd = bnd;
        memcpy(DS, bDS, sizeof(int) * nd);
        memcpy(DD, bDD, sizeof(int) * nd);
        memcpy(DG, bDG, sizeof(int) * nd);
        int n = 2 * bP * bN;
        long ne = (long)nd * bN;
        int pN = bP * bN;
        printf("%d %ld\n", n, ne);
        for (int t = 0; t < nd; t++)
            for (int x = 0; x < bN; x++)
                printf("%d %d\n", DS[t] * bN + x, pN + DD[t] * bN + gmul(x, DG[t]));
    } else {
        printf("%d %d\n", sn, sm);
        for (int e = 0; e < sm; e++) printf("%d %d\n", SU[e], SV[e]);
    }
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


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
    The caller validates the result with lib.is_valid.
    """
    F = lib.GF(q)
    MT, AT = F.mul_table, F.add_table
    pts = []
    for v in itertools.product(range(q), repeat=7):
        if any(v) and next(c for c in v if c) == 1:
            s = AT[AT[MT[v[0], v[4]], MT[v[1], v[5]]], AT[MT[v[2], v[6]], MT[v[3], v[3]]]]
            if s == 0:
                pts.append(tuple(int(c) for c in v))
    N = len(pts)
    index = {v: i for i, v in enumerate(pts)}
    P = np.array(pts, dtype=np.int64)
    lines = set()
    for i in range(N - 1):
        x = P[i]
        Y = P[i + 1:]

        def pp(a, b):
            """Grassmann coordinate p_ab = x_a y_b - x_b y_a, for all y in Y."""
            return AT[MT[x[a], Y[:, b]], MT[x[b], Y[:, a]]]

        s = np.zeros(len(Y), dtype=np.int64)
        for a, b in ((0, 4), (1, 5), (2, 6)):
            s = AT[s, AT[MT[x[a], Y[:, b]], MT[Y[:, a], x[b]]]]
        ok = (s == 0)
        ok &= pp(1, 2) == pp(3, 4)
        ok &= pp(5, 4) == pp(3, 2)
        ok &= pp(2, 0) == pp(3, 5)
        ok &= pp(6, 5) == pp(3, 0)
        ok &= pp(0, 1) == pp(3, 6)
        ok &= pp(4, 6) == pp(3, 1)
        for jj in np.nonzero(ok)[0]:
            y = Y[jj]
            vecs = [tuple(int(c) for c in x)]
            for t in range(q):
                vecs.append(tuple(int(AT[MT[t, x[k]], y[k]]) for k in range(7)))
            idx = []
            for v in vecs:
                c = next(e for e in v if e)
                inv = F.inv(c)
                idx.append(index[tuple(F.mul(inv, e) for e in v)])
            lines.add(tuple(sorted(idx)))
    lines = sorted(lines)
    edges = [(pt, N + k) for k, L in enumerate(lines) for pt in L]
    return 2 * N, edges


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates (may be empty); build() keeps only those that pass lib.is_valid."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 6 and d - 1 in (2, 4):
        try:
            out.append(_hexagon_incidence(d - 1))
        except Exception:
            pass
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            try:
                out.append(_gq_w(q))
            except Exception:
                pass
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
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 16 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.75 * time_limit - (time.monotonic() - t0) - 3.0
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 10)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
