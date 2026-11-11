"""Multi-base voltage lifts over small groups for the bipartite degree-diameter problem.

Bold change from the parent: instead of only Haar graphs (one base vertex per side), the C engine
searches lifts of a base bipartite multigraph with KB left and KB right vertices (KB = 1, 2, 3).
Each left base vertex has one dart per layer t = 0..d-1, going to right base vertex sig[t][i] with
voltage vol[t][i]. Every right base vertex then also has degree d. Groups are cyclic Z_N, affine
F_q x| C_c, or semidirect Z_m x|_r Z_k. Left translations are automorphisms, so diameter is checked
with BFS from the 2*KB base representatives. Annealing moves change voltages and permute targets
within a layer. The binary search runs over total vertex count, with random group and base choices
at each probe.

The Python baselines (projective planes, Araujo-Lopez, W(q) for D = 4, K_{d,d}) stay as the safe
fallback. Every returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-base voltage lift search.
 * Usage: prog d D seed time_limit lo hi     (lo, hi = bounds on total vertex count)
 * Output: "n m" then m lines "u v" for the best valid graph, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 256
#define MAXD 24
#define MAXK 3
#define MAXN 5000
#define MAXV (2 * MAXK * MAXN)

enum { T_CYC = 0, T_AFF = 1, T_SEMI = 2 };

typedef struct { int type, N, kb, p1, p2, p3; } Cand;

static int d, D;
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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
static long powmod(long a, long e, long m) {
    long r = 1 % m;
    a %= m;
    while (e) {
        if (e & 1) r = r * a % m;
        a = a * a % m;
        e >>= 1;
    }
    return r;
}

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

/* ------------------------------------------------------------ group arithmetic */

static Cand G;
static int Hel[MAXQ], hidx[MAXQ], HM[MAXQ * MAXQ], PWG[MAXQ];
static int PWR[MAXN];

static void setup_group(Cand c) {
    G = c;
    if (c.type == T_AFF) {
        int q = c.p1, cc = c.p2, p, k;
        factor_pp(q, &p, &k);
        build_field(q, p, k);
        int g = -1;
        for (int g0 = 2; g0 < q && g < 0; g0++) {
            int x = 1, ord = 0;
            do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
            if (ord == q - 1) g = g0;
        }
        PWG[0] = 1;
        for (int i = 1; i < q - 1; i++) PWG[i] = MULT[PWG[i - 1]][g];
        int step = (q - 1) / cc;
        for (int j = 0; j < q; j++) hidx[j] = -1;
        for (int t = 0; t < cc; t++) {
            Hel[t] = PWG[(t * step) % (q - 1)];
            hidx[Hel[t]] = t;
        }
        for (int j = 0; j < cc; j++)
            for (int t = 0; t < cc; t++)
                HM[j * cc + t] = hidx[MULT[Hel[j]][Hel[t]]];
    } else if (c.type == T_SEMI) {
        int m = c.p1, k = c.p2, r = c.p3;
        PWR[0] = 1 % m;
        for (int b = 1; b < k; b++) PWR[b] = (PWR[b - 1] * r) % m;
    }
}

static inline int gmul(int x, int y) {
    if (G.type == T_CYC) {
        int s = x + y;
        return s >= G.N ? s - G.N : s;
    }
    if (G.type == T_AFF) {
        int cc = G.p2;
        int a = x / cc, j = x % cc, b = y / cc, t = y % cc;
        int na = ADDT[a][MULT[Hel[j]][b]];
        return na * cc + HM[j * cc + t];
    }
    int m = G.p1, k = G.p2;
    int a = x / k, b = x % k, c2 = y / k, dd = y % k;
    int na = (a + PWR[b] * c2) % m;
    int nb = b + dd;
    if (nb >= k) nb -= k;
    return na * k + nb;
}

static inline int ginv(int x) {
    if (G.type == T_CYC) return x == 0 ? 0 : G.N - x;
    if (G.type == T_AFF) {
        int cc = G.p2;
        int a = x / cc, j = x % cc;
        int jn = (cc - j) % cc;
        int na = NEGT[MULT[Hel[jn]][a]];
        return na * cc + jn;
    }
    int m = G.p1, k = G.p2;
    int a = x / k, b = x % k;
    int nb = (k - b) % k;
    int na = (m - (PWR[nb] * a) % m) % m;
    return na * k + nb;
}

/* ------------------------------------------------------------ lift state */

/* Left base i has one dart per layer t: to right base sig[t][i], voltage vol[t][i].
 * Left vertex (i, g) = i*NN + g, right vertex (j, h) = KB*NN + j*NN + h.
 * Edge (i,g) -- (j, g*v). Right (j,h) reaches (i, h*v^-1). */
static int KB, NN, VV;
static int sig[MAXD][MAXK], sinv[MAXD][MAXK], vol[MAXD][MAXK], vinv[MAXD][MAXK];
static int FW[MAXD][MAXK][MAXN], BW[MAXD][MAXK][MAXN];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;
static int bestSig[MAXD][MAXK], bestVol[MAXD][MAXK];

static void fill_row(int t, int i) {
    for (int g = 0; g < NN; g++) {
        FW[t][i][g] = gmul(g, vol[t][i]);
        BW[t][i][g] = gmul(g, vinv[t][i]);
    }
}

static void set_vol(int t, int i, int v) {
    vol[t][i] = v;
    vinv[t][i] = ginv(v);
    fill_row(t, i);
}

static void rebuild_sinv(int t) {
    for (int i = 0; i < KB; i++) sinv[t][sig[t][i]] = i;
}

static int bfs_count(int src) {
    int LB = KB * NN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int x = que[head++];
            if (x < LB) {
                int i = x / NN, g = x - i * NN;
                for (int t = 0; t < d; t++) {
                    int y = LB + sig[t][i] * NN + FW[t][i][g];
                    if (vis[y] != stamp_) { vis[y] = stamp_; que[tail++] = y; }
                }
            } else {
                int r = x - LB;
                int j = r / NN, h = r - j * NN;
                for (int t = 0; t < d; t++) {
                    int i = sinv[t][j];
                    int y = i * NN + BW[t][i][h];
                    if (vis[y] != stamp_) { vis[y] = stamp_; que[tail++] = y; }
                }
            }
        }
    }
    return tail;
}

/* Zero iff the lift is simple and has diameter <= D. Representatives of every
 * base fiber (left and right) are enough, since translations are automorphisms. */
static long cost_eval(void) {
    long dup = 0;
    for (int i = 0; i < KB; i++)
        for (int t = 0; t < d; t++)
            for (int u = t + 1; u < d; u++)
                if (sig[t][i] == sig[u][i] && vol[t][i] == vol[u][i]) dup++;
    if (dup) return dup * (long)(VV + 1);
    long unr = 0;
    int LB = KB * NN;
    for (int i = 0; i < KB; i++) unr += VV - bfs_count(i * NN);
    for (int j = 0; j < KB; j++) unr += VV - bfs_count(LB + j * NN);
    return unr;
}

static void random_state(void) {
    for (int t = 0; t < d; t++) {
        int perm[MAXK];
        for (int i = 0; i < KB; i++) perm[i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        for (int i = 0; i < KB; i++) sig[t][i] = perm[i];
        rebuild_sinv(t);
        for (int i = 0; i < KB; i++) set_vol(t, i, rndint(NN));
    }
}

static int search_cur(double until) {
    const int iters = 6000;
    while (now() < until) {
        random_state();
        long cost = cost_eval();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            if (KB >= 2 && rnd01() < 0.5) {
                int t = rndint(d), i = rndint(KB), i2 = rndint(KB - 1);
                if (i2 >= i) i2++;
                int tmp = sig[t][i]; sig[t][i] = sig[t][i2]; sig[t][i2] = tmp;
                rebuild_sinv(t);
                long c2 = cost_eval();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    tmp = sig[t][i]; sig[t][i] = sig[t][i2]; sig[t][i2] = tmp;
                    rebuild_sinv(t);
                }
            } else {
                int t = rndint(d), i = rndint(KB);
                int old = vol[t][i];
                int nv = rndint(NN);
                if (nv == old) continue;
                set_vol(t, i, nv);
                long c2 = cost_eval();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    set_vol(t, i, old);
                }
            }
            if (cost == 0) return 1;
        }
    }
    return 0;
}

static int try_cfg(Cand c, double until) {
    setup_group(c);
    KB = c.kb;
    NN = c.N;
    VV = 2 * KB * NN;
    return search_cur(until);
}

static void save_state(void) {
    memcpy(bestSig, sig, sizeof sig);
    memcpy(bestVol, vol, sizeof vol);
}

/* ------------------------------------------------------------ candidates */

static int pplist[64], npp = 0;

/* Random configuration with total 2*h vertices: N*kb = h, base size kb. */
static Cand random_cand(int h) {
    int kbs[MAXK], nk = 0;
    for (int kb = 1; kb <= MAXK; kb++)
        if (h % kb == 0 && h / kb >= d) kbs[nk++] = kb;
    Cand c;
    memset(&c, 0, sizeof c);
    if (nk == 0) { c.type = -1; return c; }
    c.kb = kbs[rndint(nk)];
    c.N = h / c.kb;
    int N = c.N;
    int r = rndint(3);
    if (r == 1 && npp > 0) {
        for (int tries = 0; tries < 100; tries++) {
            int q = pplist[rndint(npp)];
            if (N % q) continue;
            int cc = N / q;
            if (cc >= 2 && (q - 1) % cc == 0) {
                c.type = T_AFF; c.p1 = q; c.p2 = cc;
                return c;
            }
        }
    } else if (r == 2 && N >= 4) {
        for (int tries = 0; tries < 100; tries++) {
            int m = 2 + rndint(N / 2 - 1);
            if (N % m) continue;
            int k = N / m;
            int rr = 1 + rndint(m - 1);
            if (gcd_i(rr, m) != 1) continue;
            if (powmod(rr, k, m) != 1 % m) continue;
            c.type = T_SEMI; c.p1 = m; c.p2 = k; c.p3 = rr;
            return c;
        }
    }
    c.type = T_CYC;
    return c;
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long lo = atol(argv[5]), hi = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (factor_pp(q, &p, &k) && npp < 64) pplist[npp++] = q;
    }

    /* Work in units of h where total vertices = 2h. */
    int ha = (int)((lo + 1) / 2), hb = (int)(hi / 2);
    if (ha < d) ha = d;
    if (hb > MAXN) hb = MAXN;

    int bestH = -1;
    Cand bestC;
    memset(&bestC, 0, sizeof bestC);

    /* Phase 1: binary search over h. Each probe gets an equal share of the
     * remaining time, split over up to three random configurations. */
    int a = ha, b = hb;
    while (a <= b && now() < t_end) {
        int mid = a + (b - a) / 2;
        int span = b - a + 1, probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = t_end - now();
        double slice = rem / (probes + 1);
        int ok = 0;
        for (int tr = 0; tr < 3 && !ok && now() < t_end; tr++) {
            Cand c = random_cand(mid);
            if (c.type < 0) break;
            double until = now() + slice / 3.0;
            if (until > t_end) until = t_end;
            if (try_cfg(c, until)) {
                ok = 1;
                bestC = c;
                bestH = mid;
                save_state();
            }
        }
        if (ok) a = mid + 1;
        else b = mid - 1;
    }

    /* Phase 2: use the leftover time on the next size up. */
    int fails = 0;
    while (bestH >= 0 && fails < 6 && now() < t_end) {
        int h = bestH + 1;
        if (h > hb) break;
        double rem = t_end - now();
        Cand c = random_cand(h);
        if (c.type < 0) break;
        if (try_cfg(c, now() + rem / 3.0)) {
            bestC = c;
            bestH = h;
            save_state();
            fails = 0;
        } else {
            fails++;
        }
    }

    if (bestH < 0) {
        printf("0 0\n");
        return 0;
    }

    /* Restore the best state, verify it, and print. */
    setup_group(bestC);
    KB = bestC.kb;
    NN = bestC.N;
    VV = 2 * KB * NN;
    memcpy(sig, bestSig, sizeof sig);
    for (int t = 0; t < d; t++) {
        rebuild_sinv(t);
        for (int i = 0; i < KB; i++) set_vol(t, i, bestVol[t][i]);
    }
    if (cost_eval() != 0) {
        printf("0 0\n");
        return 0;
    }
    int LB = KB * NN;
    printf("%d %d\n", VV, KB * NN * d);
    for (int i = 0; i < KB; i++)
        for (int g = 0; g < NN; g++)
            for (int t = 0; t < d; t++)
                printf("%d %d\n", i * NN + g, LB + sig[t][i] * NN + FW[t][i][g]);
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

    # Multi-base voltage lifts. Total vertex count lies in [lo, hi].
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, 2 * d)
        hi = mb
        if budget > 2.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass  # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
