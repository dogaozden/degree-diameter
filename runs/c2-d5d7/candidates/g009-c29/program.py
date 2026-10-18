"""Multi-base voltage-lift search for the weakest cases (d = 5, D = 7 is the target).

Bold change: the parent searched only bi-Cayley graphs (one base vertex per side). This version
searches voltage lifts with S base vertices per side, S = 1..5. A base is a d-regular bipartite
multigraph on S+S vertices. Each dart (i, j, g) joins a_{i,x} to b_{j, x*g} for all x in G, where
G = Z_m x|_r Z_k is a semidirect product. The lift has 2*S*|G| vertices and is d-regular.

Left multiplication by G is an automorphism, so diameter <= D is checked by BFS from a_{i,e} and
b_{j,e} for all i, j (2S sources). Moves change dart voltages or swap the B-ends of two darts. Only
moves that keep the same (A, B, voltage) pairs distinct are accepted, so the lift stays simple.

The start graph (H(q), PG(2,q), or W(q)) is the fallback. If no lift beats it, the start is returned.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-base voltage-lift search over semidirect groups Z_m x|_r Z_k.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0".
 * stdout:  the best valid graph found (a lift if it beats the start, else the start).
 *
 * Lift with S base vertices per side and group G of order N:
 *   A-vertex a_{i,x} = i*N + x,  B-vertex b_{j,y} = S*N + j*N + y.
 *   Darts k = 0..S*d-1: A-end i = k/d, B-end DB[k], voltage DG[k] in G.
 *   Edge a_{i,x} -- b_{DB[k], x*DG[k]} for every dart k with A-end i and every x in G.
 * Pairs (i, j, g) must be distinct, so the lift is simple. Each B-vertex gets exactly d darts.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXD 16
#define MAXS 5
#define MAXDART (MAXS * MAXD)
#define MAXSTART 400000
#define MAXV 12288
#define MAXLE 100000
#define MAXCAND 4096
#define STEPS 3000
#define OFFSET 4

typedef struct { int m, k, r; } Grp;

static int d, D;
static double t_end;
static int S, N, E;
static int DB[MAXDART], DG[MAXDART];
static int MTAB[MAXN * MAXN];
static int INVT[MAXN];
static int RP[MAXN];

static int dist_[MAXV], seen_[MAXV], q_[MAXV];
static int stamp_ = 0;

static int BEU[MAXLE], BEV[MAXLE];
static int BEn = 0;
static int bestV = 0;
static int improved = 0;

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

static int gcd(int a, int b) {
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

/* Enumerate Z_m x|_r Z_k with m*k = n, gcd(r,m)=1, r^k = 1 mod m. */
static int enum_groups(int n, Grp *out) {
    int cnt = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            if (cnt < MAXCAND) { out[cnt].m = 1; out[cnt].k = k; out[cnt].r = 0; cnt++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
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

static void setup_group(int n, Grp G) {
    N = n;
    int m = G.m, k = G.k;
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * G.r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            row[y] = (int)((((long)a + (long)RP[b] * c) % m) * k + (b + e) % k);
        }
    }
    for (int x = 0; x < N; x++) {
        const int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++)
            if (row[y] == 0) { INVT[x] = y; break; }
    }
}

/* True if no dart k2 < k shares (A-end, B-end, voltage) with dart k. */
static int local_ok_prefix(int k) {
    for (int k2 = 0; k2 < k; k2++)
        if (k2 / d == k / d && DB[k2] == DB[k] && DG[k2] == DG[k]) return 0;
    return 1;
}

/* True if all darts are pairwise compatible. */
static int conflict_free(void) {
    for (int k1 = 0; k1 < E; k1++)
        for (int k2 = 0; k2 < k1; k2++)
            if (k1 / d == k2 / d && DB[k1] == DB[k2] && DG[k1] == DG[k2]) return 0;
    return 1;
}

/* Number of (source, vertex) pairs at distance > D over sources a_{i,e} and b_{j,e}. */
static long eval_bad(void) {
    int SN = S * N;
    int V = 2 * SN;
    int BL[MAXDART];
    int cnt[MAXS];
    for (int j = 0; j < S; j++) cnt[j] = 0;
    for (int k = 0; k < E; k++) {
        int j = DB[k];
        BL[j * d + cnt[j]++] = k;
    }
    long total = 0;
    for (int si = 0; si < 2 * S; si++) {
        int src = (si < S) ? si * N : SN + (si - S) * N;
        int head = 0, tail = 0;
        stamp_++;
        seen_[src] = stamp_;
        dist_[src] = 0;
        q_[tail++] = src;
        while (head < tail) {
            int v = q_[head++];
            int dv = dist_[v];
            if (dv >= D) continue;
            if (v < SN) {
                int i = v / N, x = v - i * N;
                const int *row = MTAB + (size_t)x * N;
                for (int t = 0; t < d; t++) {
                    int k = i * d + t;
                    int u = SN + DB[k] * N + row[DG[k]];
                    if (seen_[u] != stamp_) {
                        seen_[u] = stamp_;
                        dist_[u] = dv + 1;
                        q_[tail++] = u;
                    }
                }
            } else {
                int w = v - SN;
                int j = w / N, y = w - j * N;
                const int *row = MTAB + (size_t)y * N;
                for (int c = 0; c < d; c++) {
                    int k = BL[j * d + c];
                    int u = (k / d) * N + row[INVT[DG[k]]];
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

/* Simulated annealing over dart voltages and B-end swaps. */
static long climb(void) {
    long bad = eval_bad();
    double T = 2.0;
    for (long st = 0; st < STEPS && bad > 0; st++) {
        if ((st & 63) == 0 && now() > t_end) break;
        int k = rndint(E);
        int oldB = DB[k], oldG = DG[k];
        int k2 = -1, oldB2 = 0;
        int swapped = 0;
        if (S > 1 && rnd01() < 0.3) {
            k2 = rndint(E);
            if (k2 != k && DB[k2] != oldB) {
                oldB2 = DB[k2];
                DB[k] = oldB2;
                DB[k2] = oldB;
                swapped = 1;
            }
        }
        if (!swapped) DG[k] = rndint(N);
        int ok = conflict_free();
        if (ok) {
            long nb = eval_bad();
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
            else ok = 0;
        }
        if (!ok) {
            if (swapped) { DB[k] = oldB; DB[k2] = oldB2; }
            else DG[k] = oldG;
        }
        T *= 0.999;
        if (T < 0.2) T = 0.2;
    }
    return bad;
}

static void random_init(void) {
    int slot[MAXDART];
    for (int j = 0; j < S; j++)
        for (int c = 0; c < d; c++) slot[j * d + c] = j;
    for (int k = E - 1; k > 0; k--) {
        int r = rndint(k + 1);
        int tmp = slot[k];
        slot[k] = slot[r];
        slot[r] = tmp;
    }
    for (int k = 0; k < E; k++) DB[k] = slot[k];
    for (int k = 0; k < E; k++) {
        int tries = 0;
        do {
            DG[k] = rndint(N);
            tries++;
        } while (!local_ok_prefix(k) && tries < 10000);
    }
}

static void store_best(void) {
    int SN = S * N;
    int ne = 0;
    for (int k = 0; k < E; k++) {
        int i = k / d, j = DB[k];
        for (int x = 0; x < N; x++) {
            BEU[ne] = i * N + x;
            BEV[ne] = SN + j * N + MTAB[(size_t)x * N + DG[k]];
            ne++;
        }
    }
    BEn = ne;
    bestV = 2 * SN;
    improved = 1;
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
    t_end = t0 + limit * 0.93 - 0.3;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static int SU[MAXSTART], SV[MAXSTART];
    int sn = 0, sm = 0;
    if (scanf("%d %d", &sn, &sm) != 2) { sn = 0; sm = 0; }
    if (sn < 0 || sm < 0 || sm > MAXSTART) { sn = 0; sm = 0; }
    int got = 0;
    for (int e = 0; e < sm; e++) {
        if (scanf("%d %d", &SU[e], &SV[e]) != 2) break;
        got++;
    }
    if (got != sm) { sn = 0; sm = 0; }

    bestV = sn;

    if (d >= 3 && d <= MAXD && D >= 2) {
        long moore = moore_bound();
        static Grp cand[MAXCAND];
        while (now() < t_end) {
            if (bestV >= moore) break;
            int s = 1 + rndint(MAXS);
            long Nlo = (long)bestV / (2L * s) + 1;
            if (Nlo < d + 1) Nlo = d + 1;
            long Nl = Nlo + rndint(OFFSET);
            if (Nl > MAXN) continue;
            if (2L * s * Nl > MAXV) continue;
            if (2L * s * Nl > moore) continue;
            int n = (int)Nl;
            int ncand = enum_groups(n, cand);
            if (ncand <= 0) continue;
            Grp G = pick_group(cand, ncand);
            S = s;
            E = S * d;
            setup_group(n, G);
            random_init();
            if (!conflict_free()) continue;
            long bad = climb();
            if (bad == 0) store_best();
        }
    }

    if (improved) {
        printf("%d %d\n", bestV, BEn);
        for (int i = 0; i < BEn; i++) printf("%d %d\n", BEU[i], BEV[i]);
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
    Points: points of the quadric X0X4 + X1X5 + X2X6 = X3^2. Lines: quadric lines whose Grassmann
    coordinates satisfy p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31.
    Characteristic 2, so signs are irrelevant. The caller validates the result with lib.is_valid.
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

        # Collinearity on the quadric: polar form B(x, y) = 0 (char 2 has no 2*x3*y3 term).
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
            # Points of the line: x, and t*x + y for t in GF(q).
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
            out.append(_gq_w(q))
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

    if d > 16 or D < 2 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 6)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
