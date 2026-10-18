"""Multi-orbit bi-Cayley lifts for the bipartite degree-diameter problem.

Change from the parent: instead of one Haar graph over a single group (r = 1), the C
engine now searches over r left orbits and r right orbits of a group G of order N.
The graph has 2rN vertices. Slot (i, k) of left orbit i points to right orbit
pi_k(i), where pi_0..pi_{d-1} are random permutations of {0..r-1}, so every orbit
has degree d. Each slot carries a voltage s, and L_{i,g} ~ R_{j,g*s}. Voltages on
slots that share the same (i, j) block are kept distinct, so the graph is simple.

Groups are F_q x| H (as in the parent) or cyclic Z_N. Left translations are
automorphisms, so the diameter test is 2r BFS runs, one from L_{i,e} and one from
R_{j,e} for each orbit. The annealing is iterated around the incumbent. Permutations
are re-drawn now and then. Candidates are tried in ascending vertex count, starting
just above the Python fallback. Every output is checked with lib.is_valid, and the
K_{d,d} / projective plane fallbacks are kept.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit lift search.
 * Usage: prog d D seed time_limit vlo vhi     (stdin ignored)
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 256
#define MAXN 2048
#define MAXD 32
#define MAXR 4
#define MAXSL (MAXR * MAXD)
#define MAXV (2 * MAXR * MAXN)
#define MAXCAND 40000
#define ITERS 6000

typedef struct { int r, type, q, p, k, c, N, V; } Cand;

static int DEG, DIAM;
static int NR, NN, NV;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* ------------------------------------------------------------ finite fields */

static int ADDT[MAXQ][MAXQ], MULT[MAXQ][MAXQ], NEGT[MAXQ];
static int built_q = -1;

static int factor_pp(int q, int *p, int *k) {
    int pp = 0;
    for (int f = 2; f * f <= q; f++)
        if (q % f == 0) { pp = f; break; }
    if (!pp) pp = q;
    int r = q, kk = 0;
    while (r % pp == 0) { r /= pp; kk++; }
    if (r != 1 || kk < 1) return 0;
    *p = pp;
    *k = kk;
    return 1;
}

static int polymul(int a, int b, int p, int k, const int *pw, const int *m) {
    int pa[16], pb[16], prod[32];
    for (int i = 0; i < k; i++) {
        pa[i] = (a / pw[i]) % p;
        pb[i] = (b / pw[i]) % p;
    }
    for (int i = 0; i < 2 * k; i++) prod[i] = 0;
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            prod[i + j] = (prod[i + j] + pa[i] * pb[j]) % p;
    for (int deg = 2 * k - 2; deg >= k; deg--) {
        int c = prod[deg];
        if (!c) continue;
        for (int i = 0; i < k; i++) {
            int idx = deg - k + i;
            prod[idx] = ((prod[idx] - c * m[i]) % p + p) % p;
        }
        prod[deg] = 0;
    }
    int r = 0;
    for (int i = 0; i < k; i++) r += prod[i] * pw[i];
    return r;
}

static void build_field(int q, int p, int k) {
    if (built_q == q) return;
    int pw[16];
    pw[0] = 1;
    for (int i = 1; i <= k; i++) pw[i] = pw[i - 1] * p;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            int r = 0;
            for (int i = 0; i < k; i++)
                r += (((a / pw[i]) % p + (b / pw[i]) % p) % p) * pw[i];
            ADDT[a][b] = r;
        }
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            if (ADDT[a][b] == 0) NEGT[a] = b;

    int found = 0;
    for (int code = 0; code < q && !found; code++) {
        int m[16];
        int t = code;
        for (int i = 0; i < k; i++) { m[i] = t % p; t /= p; }
        int ok = 1;
        for (int a = 1; a < q && ok; a++)
            for (int b = 1; b < q && ok; b++)
                if (polymul(a, b, p, k, pw, m) == 0) ok = 0;
        if (ok) {
            found = 1;
            for (int a = 0; a < q; a++)
                for (int b = 0; b < q; b++)
                    MULT[a][b] = polymul(a, b, p, k, pw, m);
        }
    }
    built_q = q;
}

/* ------------------------------------------------------------ groups */

static int Hel[MAXQ], hidx[MAXQ], HM[MAXQ * MAXQ], PWG[MAXQ];
static int GT[MAXN * MAXN];   /* GT[x*NN + y] = x*y, identity = 0 */
static int GI[MAXN];          /* inverses */

/* G = F_q x| H, |H| = c, element (a, h_j) coded a*c + j. */
static void setup_fq(int q, int p, int k, int c) {
    build_field(q, p, k);
    int N = q * c;
    NN = N;
    int g = 1;
    for (int g0 = 2; g0 < q; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) { g = g0; break; }
    }
    PWG[0] = 1;
    for (int i = 1; i < q - 1; i++) PWG[i] = MULT[PWG[i - 1]][g];
    int step = (q - 1) / c;
    for (int j = 0; j < q; j++) hidx[j] = -1;
    for (int t = 0; t < c; t++) {
        Hel[t] = PWG[(t * step) % (q - 1)];
        hidx[Hel[t]] = t;
    }
    for (int j = 0; j < c; j++)
        for (int t = 0; t < c; t++)
            HM[j * c + t] = hidx[MULT[Hel[j]][Hel[t]]];
    for (int x = 0; x < N; x++) {
        int a = x / c, j = x % c;
        for (int y = 0; y < N; y++) {
            int b = y / c, t = y % c;
            int na = ADDT[a][MULT[Hel[j]][b]];
            GT[x * N + y] = na * c + HM[j * c + t];
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (GT[x * N + y] == 0) { GI[x] = y; break; }
}

static void setup_cand(const Cand *cd) {
    if (cd->type == 1) {
        NN = cd->N;
        for (int x = 0; x < NN; x++) {
            for (int y = 0; y < NN; y++) {
                int s = x + y;
                if (s >= NN) s -= NN;
                GT[x * NN + y] = s;
            }
            GI[x] = (NN - x) % NN;
        }
    } else {
        setup_fq(cd->q, cd->p, cd->k, cd->c);
    }
}

/* ------------------------------------------------------------ lift state */

/* Slot e = i*DEG + k: left orbit i, slot k. tgt[e] = right orbit, sv[e] = voltage. */
static int tgt[MAXSL], rin[MAXSL], sv[MAXSL], svi[MAXSL];
static int inc_tgt[MAXSL], inc_rin[MAXSL], inc_sv[MAXSL];
static int vis[MAXV], que[MAXV];
static int have_res = 0;
static Cand res_cand;
static int res_tgt[MAXSL], res_sv[MAXSL];

/* Right orbit j has exactly DEG incoming slots, all in rin[j*DEG .. j*DEG+DEG-1]. */
static void new_perms(void) {
    for (int k = 0; k < DEG; k++) {
        int pm[MAXR];
        for (int i = 0; i < NR; i++) pm[i] = i;
        for (int i = NR - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = pm[i];
            pm[i] = pm[j];
            pm[j] = tmp;
        }
        for (int i = 0; i < NR; i++) tgt[i * DEG + k] = pm[i];
    }
    for (int j = 0; j < NR; j++) {
        int cnt = 0;
        for (int e = 0; e < NR * DEG; e++)
            if (tgt[e] == j && cnt < DEG) rin[j * DEG + cnt++] = e;
    }
}

/* Vertices: L_{i,g} = i*NN + g; R_{j,h} = NR*NN + j*NN + h. */
static int bfs_reach(int src) {
    static int stampc = 0;
    stampc++;
    int rN = NR * NN;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stampc;
    for (int lvl = 0; lvl < DIAM && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < rN) {
                int i = v / NN, g = v - i * NN;
                for (int k = 0; k < DEG; k++) {
                    int e = i * DEG + k;
                    int j = tgt[e];
                    int u = rN + j * NN + GT[g * NN + sv[e]];
                    if (vis[u] != stampc) { vis[u] = stampc; que[tail++] = u; }
                }
            } else {
                int w = v - rN;
                int j = w / NN, h = w - j * NN;
                for (int t = 0; t < DEG; t++) {
                    int e = rin[j * DEG + t];
                    int i = e / DEG;
                    int u = i * NN + GT[h * NN + svi[e]];
                    if (vis[u] != stampc) { vis[u] = stampc; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Cost = number of (root, vertex) pairs at distance > DIAM over the 2*NR roots. */
static long cost_fn(void) {
    int rN = NR * NN;
    long c = 0;
    for (int r = 0; r < 2 * NR; r++) {
        int src = (r < NR) ? r * NN : rN + (r - NR) * NN;
        c += (long)(NV - bfs_reach(src));
    }
    return c;
}

/* Voltages in a block (same left orbit, same right orbit) must be distinct. */
static int conflict_free(int e, int x) {
    int i = e / DEG, j = tgt[e];
    for (int k = 0; k < DEG; k++) {
        int e2 = i * DEG + k;
        if (e2 != e && tgt[e2] == j && sv[e2] >= 0 && sv[e2] == x) return 0;
    }
    return 1;
}

static int pick_volt(int e) {
    int x;
    do { x = rndint(NN); } while (!conflict_free(e, x));
    return x;
}

static void set_volt(int e, int x) {
    sv[e] = x;
    svi[e] = GI[x];
}

static void record_success(const Cand *cd) {
    have_res = 1;
    res_cand = *cd;
    memcpy(res_tgt, tgt, sizeof(int) * (size_t)(NR * DEG));
    memcpy(res_sv, sv, sizeof(int) * (size_t)(NR * DEG));
}

/* Iterated annealing for the current candidate. Returns 1 when cost 0 is reached. */
static int search_cand(const Cand *cd, double until) {
    int have = 0;
    long bestc = 0;
    int L = NR * DEG;
    while (now() < until) {
        int fresh = (!have) || (rndint(3) == 0);
        if (fresh) {
            new_perms();
            for (int e = 0; e < L; e++) sv[e] = -1;
            for (int e = 0; e < L; e++) set_volt(e, pick_volt(e));
        } else {
            memcpy(tgt, inc_tgt, sizeof(int) * (size_t)L);
            memcpy(rin, inc_rin, sizeof(int) * (size_t)L);
            memcpy(sv, inc_sv, sizeof(int) * (size_t)L);
            for (int e = 0; e < L; e++) svi[e] = GI[sv[e]];
            for (int t = 0; t < 2; t++) {
                int e = rndint(L);
                set_volt(e, pick_volt(e));
            }
        }
        long cost = cost_fn();
        if (cost == 0) { record_success(cd); return 1; }
        double c0 = (double)cost;
        double Ts = (fresh ? 0.05 : 0.02) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < ITERS && cost > 0; it++) {
            if ((it & 7) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / ITERS);
            int e = rndint(L);
            int old = sv[e], oldi = svi[e];
            set_volt(e, pick_volt(e));
            long c2 = cost_fn();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                sv[e] = old;
                svi[e] = oldi;
            }
        }
        if (cost == 0) { record_success(cd); return 1; }
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(inc_tgt, tgt, sizeof(int) * (size_t)L);
            memcpy(inc_rin, rin, sizeof(int) * (size_t)L);
            memcpy(inc_sv, sv, sizeof(int) * (size_t)L);
        }
    }
    return 0;
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = (const Cand *)a;
    const Cand *y = (const Cand *)b;
    if (x->V != y->V) return x->V - y->V;
    return x->type - y->type;
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int vlo = atoi(argv[5]), vhi = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    DEG = d;
    DIAM = D;
    if (vhi > MAXV) vhi = MAXV;
    if (vlo < 2 * d) vlo = 2 * d;

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int r = 1; r <= MAXR; r++) {
        int nlo = (vlo + 2 * r - 1) / (2 * r);
        int nhi = vhi / (2 * r);
        if (nlo < d) nlo = d;
        if (nhi > MAXN) nhi = MAXN;
        if (nlo > nhi) continue;
        for (int N = nlo; N <= nhi && nc < MAXCAND; N++) {
            Cand cd = {r, 1, 0, 0, 0, 0, N, 2 * r * N};
            cand[nc++] = cd;
        }
        for (int q = 3; q < MAXQ; q++) {
            int p, k;
            if (!factor_pp(q, &p, &k)) continue;
            for (int c = 1; c <= q - 1; c++) {
                if ((q - 1) % c) continue;
                int N = q * c;
                if (N < nlo || N > nhi) continue;
                if (nc < MAXCAND) {
                    Cand cd = {r, 0, q, p, k, c, N, 2 * r * N};
                    cand[nc++] = cd;
                }
            }
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    int next_min = vlo, fail_V = -1, fails = 0;
    for (int ci = 0; ci < nc; ci++) {
        Cand cd = cand[ci];
        if (cd.V < next_min) continue;
        double rem = t_end - now();
        if (rem < 0.3) break;
        double slice = 0.2 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_cand(&cd);
        NR = cd.r;
        NV = cd.V;
        if (search_cand(&cd, now() + slice)) {
            next_min = cd.V + 1;
            fail_V = -1;
            fails = 0;
        } else {
            if (cd.V != fail_V) { fail_V = cd.V; fails = 0; }
            fails++;
            if (fails >= 2) {
                int step = cd.V / 300;
                if (step < 2) step = 2;
                next_min = cd.V + step;
            }
        }
    }

    if (!have_res) {
        printf("0 0\n");
        return 0;
    }
    setup_cand(&res_cand);
    NR = res_cand.r;
    NV = res_cand.V;
    int rN = NR * NN, L = NR * DEG;
    printf("%d %d\n", 2 * rN, rN * DEG);
    for (int e = 0; e < L; e++) {
        int i = e / DEG, j = res_tgt[e], s = res_sv[e];
        for (int g = 0; g < NN; g++)
            printf("%d %d\n", i * NN + g, rN + j * NN + GT[g * NN + s]);
    }
    return 0;
}
'''


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
    """W(q) for the largest prime power q with q + 1 <= d (kept small for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2 and is the safe fallback.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
        # Exact Moore graph: nothing can beat it.
        if D == 3 and lib.is_prime_power(d - 1) and best[0] > 2 * d:
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    # Search: multi-orbit lifts (r left and r right orbits) over small groups.
    if d >= 3 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        vhi = min(mb, 16384)
        vlo = max(best[0] + 2, mb // 4)
        if budget > 2.0 and vlo <= vhi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), vlo, vhi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
