"""Voltage-lift annealing: bipartite lifts of strong small base graphs over
small semidirect groups, searched by a C annealer, with exact fallbacks."""
import itertools
import time

import lib


C_SOURCE = r'''
/* Voltage-lift annealer for bipartite degree-diameter graphs.
 * Usage: prog d D seed time_limit glo < base_graph
 * base_graph: "n m" + m edges, bipartite, simple, connected, max degree <= d.
 * Lift over group Z_M x| Z_K of order G: vertex (u,x) = u*G + x, and each base
 * edge (u on side 0, v on side 1) with voltage g gives edges (u,x)-(v, x*g).
 * Tree edges get voltage identity (WLOG). Tries G = glo, glo+1, ... while time
 * allows; each level is annealed on the number of unreached (rep, vertex) pairs.
 * Stdout: the largest valid lift found, or the base graph if none.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXB 1024
#define MAXE 8192
#define MAXD 32
#define MAXN 8192
#define MAXG 8192
#define MAXOPT 8192

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

/* ---- base graph ---- */
static int B, E;
static int bdeg[MAXB];
static int bedge[MAXB][MAXD];
static int bside[MAXB];
static int ru[MAXE], rv[MAXE];
static int eu[MAXE], ev[MAXE], eku[MAXE], ekv[MAXE];
static int is_tree[MAXE];
static int nontree[MAXE], NT;

/* ---- group Z_M x|_r Z_K, element a*K+b, (a,b)(c,e) = (a + r^b c, b+e) ---- */
typedef struct { int M, K, r; int rp[MAXG]; } Grp;
static Grp grp, best_grp, triv;
static int G, N;
static int vdeg[MAXN];
static int nbr[MAXN][MAXD];
static int volt[MAXE], best_volt[MAXE], zero_volt[MAXE];
static int stampv[MAXN], distv[MAXN], queuev[MAXN];
static int stampc = 0;
static int nopt, optM[MAXOPT], optK[MAXOPT], optR[MAXOPT];
static int found_G = 0;

static int read_base(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXB || m < 0 || m > MAXE) return 0;
    B = n;
    E = m;
    for (int v = 0; v < n; v++) { bdeg[v] = 0; bside[v] = -1; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (bdeg[u] >= d || bdeg[v] >= d) return 0;
        for (int k = 0; k < bdeg[u]; k++) {
            int f = bedge[u][k];
            if ((ru[f] == u && rv[f] == v) || (ru[f] == v && rv[f] == u)) return 0;
        }
        ru[e] = u;
        rv[e] = v;
        is_tree[e] = 0;
        bedge[u][bdeg[u]++] = e;
        bedge[v][bdeg[v]++] = e;
    }
    static int q[MAXB];
    int head = 0, tail = 0;
    bside[0] = 0;
    q[tail++] = 0;
    while (head < tail) {
        int v = q[head++];
        for (int k = 0; k < bdeg[v]; k++) {
            int e = bedge[v][k];
            int w = (ru[e] == v) ? rv[e] : ru[e];
            if (bside[w] < 0) {
                bside[w] = 1 - bside[v];
                is_tree[e] = 1;
                q[tail++] = w;
            } else if (bside[w] == bside[v]) {
                return 0;
            }
        }
    }
    if (tail != B) return 0;
    NT = 0;
    for (int e = 0; e < E; e++) {
        if (bside[ru[e]] == 0) { eu[e] = ru[e]; ev[e] = rv[e]; }
        else { eu[e] = rv[e]; ev[e] = ru[e]; }
        if (!is_tree[e]) nontree[NT++] = e;
    }
    for (int v = 0; v < B; v++)
        for (int k = 0; k < bdeg[v]; k++) {
            int e = bedge[v][k];
            if (eu[e] == v) eku[e] = k;
            else ekv[e] = k;
        }
    return 1;
}

static void enum_groups(int g) {
    nopt = 0;
    for (int M = 1; M <= g && nopt < MAXOPT; M++) {
        if (g % M) continue;
        int K = g / M;
        if (M == 1) {
            optM[nopt] = 1; optK[nopt] = K; optR[nopt] = 0; nopt++;
            continue;
        }
        for (int r = 1; r < M && nopt < MAXOPT; r++) {
            if (gcd(r, M) != 1) continue;
            if (powmod(r, K, M) != 1) continue;
            optM[nopt] = M; optK[nopt] = K; optR[nopt] = r; nopt++;
        }
    }
}

static void set_group(int i) {
    grp.M = optM[i];
    grp.K = optK[i];
    grp.r = optR[i];
    grp.rp[0] = 1 % grp.M;
    for (int b = 1; b < grp.K; b++)
        grp.rp[b] = (int)((long)grp.rp[b - 1] * grp.r % grp.M);
}

static int gmul(const Grp *g, int x, int y) {
    int K = g->K, M = g->M;
    int a = x / K, b = x % K, c = y / K, e = y % K;
    int aa = (int)((a + (long)g->rp[b] * c) % M);
    return aa * K + (b + e) % K;
}

/* Set voltage of base edge e and rewrite its G lift edges in nbr. */
static void set_volt(int e, int g) {
    volt[e] = g;
    int a0 = eu[e] * G, b0 = ev[e] * G;
    for (int x = 0; x < G; x++) {
        int a = a0 + x;
        int b = b0 + gmul(&grp, x, g);
        nbr[a][eku[e]] = b;
        nbr[b][ekv[e]] = a;
    }
}

/* Sum over base representatives (u, identity) of vertices NOT within distance D.
 * Zero iff the lift has diameter <= D (left translation is an automorphism). */
static long cost_all(void) {
    long total = 0;
    for (int u = 0; u < B; u++) {
        int s = u * G;
        stampc++;
        int head = 0, tail = 0, cnt = 1;
        queuev[tail++] = s;
        stampv[s] = stampc;
        distv[s] = 0;
        while (head < tail) {
            int v = queuev[head++];
            int dv = distv[v];
            if (dv >= D) continue;
            for (int k = 0; k < vdeg[v]; k++) {
                int w = nbr[v][k];
                if (stampv[w] != stampc) {
                    stampv[w] = stampc;
                    distv[w] = dv + 1;
                    queuev[tail++] = w;
                    cnt++;
                }
            }
        }
        total += N - cnt;
    }
    return total;
}

static void save_best(void) {
    found_G = G;
    best_grp = grp;
    memcpy(best_volt, volt, sizeof(int) * (size_t)E);
}

static void print_lift(int g, const Grp *gr, const int *vol) {
    printf("%d %ld\n", B * g, (long)E * g);
    for (int e = 0; e < E; e++)
        for (int x = 0; x < g; x++)
            printf("%d %d\n", eu[e] * g + x, ev[e] * g + gmul(gr, x, vol[e]));
}

/* Anneal for lifts of order G. Returns 1 when a valid lift is saved. */
static int try_level(void) {
    N = B * G;
    if (nopt == 0) return 0;
    for (int v = 0; v < N; v++) vdeg[v] = bdeg[v / G];
    while (now() < t_end) {
        set_group(rndint(nopt));
        for (int e = 0; e < E; e++) volt[e] = is_tree[e] ? 0 : rndint(G);
        for (int e = 0; e < E; e++) set_volt(e, volt[e]);
        long c = cost_all();
        if (c == 0) { save_best(); return 1; }
        if (NT == 0) return 0;
        double start = now();
        double P = start + 4.0;
        if (P > t_end) P = t_end;
        double T0 = 2.0 + 0.02 * (double)c, T1 = 0.3;
        while (now() < P) {
            double frac = (now() - start) / (P - start + 1e-9);
            double T = T0 * pow(T1 / T0, frac);
            int e = nontree[rndint(NT)];
            int g = rndint(G);
            if (g == volt[e]) continue;
            int old = volt[e];
            set_volt(e, g);
            long c2 = cost_all();
            if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) {
                c = c2;
                if (c == 0) { save_best(); return 1; }
            } else {
                set_volt(e, old);
            }
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit glo < base_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int glo = atoi(argv[5]);
    if (d < 1 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (!read_base()) { printf("0 0\n"); return 0; }

    triv.M = 1; triv.K = 1; triv.r = 0; triv.rp[0] = 0;
    if (glo < 2) glo = 2;
    long moore = moore_bound();
    G = glo;
    while (now() < t_end) {
        if ((long)B * G > moore || (long)B * G > MAXN || G > MAXG) break;
        enum_groups(G);
        if (!try_level()) break;
        G++;
    }
    if (found_G > 0) print_lift(found_G, &best_grp, best_volt);
    else print_lift(1, &triv, zero_volt);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact and base constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
# Driver: exact cases, then voltage-lift annealing from strong bases.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = [lib.haar_graph(d, range(d))]

    def consider(n, e):
        if n > best[0][0] and lib.is_valid(n, e, d, D):
            best[0] = (n, e)

    if D == 2:
        return best[0]

    pg = _best_pg(d)
    if pg is not None:
        consider(*pg)
        if D == 3 and lib.is_prime_power(d - 1):
            return best[0]

    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except (ValueError, RuntimeError):
            pass

    gq = None
    if D >= 4 and time.monotonic() < t0 + 0.25 * usable:
        gq = _best_gq(d)
        if gq is not None:
            consider(*gq)
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best[0]

    if d > 31:
        return best[0]

    bases = [b for b in (pg, gq) if b is not None]
    if not bases:
        bases = [lib.haar_graph(d, range(d))]

    for idx, base in enumerate(bases):
        remaining = end - time.monotonic() - 0.5
        if remaining < 1.0:
            break
        share = 0.8 if (len(bases) == 2 and idx == 0) else 1.0
        budget = round(remaining * share, 2)
        if budget < 1.0:
            break
        n0, e0 = base
        glo = max(2, best[0][0] // n0 + 1)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, glo],
                             stdin_graph=(n0, e0), timeout=budget + 5)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0][0], best[0][1], d, D):
        best[0] = lib.haar_graph(d, range(d))
    return best[0]
