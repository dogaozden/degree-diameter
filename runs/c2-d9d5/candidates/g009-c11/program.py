"""Two-orbit bi-Cayley (generalised Haar) lift search for the bipartite degree-diameter problem.

Change from the parent: instead of one Haar graph Cay(G, S) on 2N vertices, the C engine
now also searches graphs with two orbits per side. Left vertices L_i(g) and right vertices
R_j(h), i, j in {0, 1}, have arcs L_i(g) ~ R_j(g*s) for darts (i, j, s). The degree-d
pattern is a 2x2 count matrix [[t, d-t], [d-t, t]] with 1 <= t <= d/2, so the graph has
4N vertices and is d-regular and bipartite. Diameter is checked from one representative
of each of the four vertex classes, since G acts transitively on every class.

Groups: affine F_q x| C_c (q <= 255 prime power, c | q-1, c >= 1) and semidirect
Z_m x|_r Z_k (r^k = 1 mod m, gcd(r, m) = 1), which includes cyclic and dihedral groups.
Candidates with 2*mo*N in [vlo, vhi] are sorted by vertex count, and a binary search over
them uses equal time slices per probe, as in the parent.

Safety: the Python side keeps K_{d,d}, PG(2,q), Araujo-Lopez and W(q) baselines, returns
the exact Moore graph for D = 3 when it exists, and validates every result with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Two-orbit bi-Cayley lift search.
 * Usage: prog d D seed time_limit vlo vhi     (stdin ignored)
 * Output: "V E" then E lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 256
#define MAXC 256
#define MAXN 4096
#define MAXD 32
#define MAXDART 64
#define MAXV 16384
#define MAXCAND 60000

typedef struct {
    int type;   /* 0: affine F_q x| C_c ; 1: semidirect Z_m x| Z_k */
    int a;      /* q (type 0) or m (type 1) */
    int b;      /* c (type 0) or k (type 1) */
    int r;      /* action multiplier (type 1) */
    int p, kf;  /* characteristic and extension degree (type 0) */
    int mo;     /* orbits per side: 1 or 2 */
    int N;      /* group order */
    int V;      /* vertex count 2*mo*N */
} Cand;

static int dd, DD;
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
    int pw[17];
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

static int gtype, GN, GC, GM, GK, GR;
static int Hel[MAXC], HM[MAXC * MAXC], hidx[MAXQ], PWG[MAXQ], PWR[MAXC];

static void setup_group(const Cand *cd) {
    gtype = cd->type;
    if (gtype == 0) {
        int q = cd->a, c = cd->b;
        build_field(q, cd->p, cd->kf);
        GC = c;
        GN = q * c;
        int g = 1;
        for (int g0 = 1; g0 < q; g0++) {
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
    } else {
        GM = cd->a;
        GK = cd->b;
        GR = cd->r;
        GN = GM * GK;
        PWR[0] = 1 % GM;
        for (int b = 1; b < GK; b++) PWR[b] = (PWR[b - 1] * GR) % GM;
    }
}

static inline int gmul(int x, int y) {
    if (gtype == 0) {
        int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
        int na = ADDT[a][MULT[Hel[j]][b]];
        return na * GC + HM[j * GC + t];
    } else {
        int a = x / GK, b = x % GK, c = y / GK, d = y % GK;
        int na = (a + PWR[b] * c) % GM;
        return na * GK + (b + d) % GK;
    }
}

static int ginv(int x) {
    if (gtype == 0) {
        int a = x / GC, j = x % GC;
        int jn = (GC - j) % GC;
        int na = NEGT[MULT[Hel[jn]][a]];
        return na * GC + jn;
    } else {
        int a = x / GK, b = x % GK;
        int nb = (GK - b) % GK;
        int na = (GM - (PWR[nb] * a) % GM) % GM;
        return na * GK + nb;
    }
}

/* ------------------------------------------------------------ bi-Cayley state */

static int mo, NDART, cur_t;
static int dsrc[MAXDART], ddst[MAXDART], dpair[MAXDART];
static int dsh[MAXDART], dshi[MAXDART];
static int fwd[MAXDART][MAXN], bwd[MAXDART][MAXN];
static int ldart[2][MAXD], rdart[2][MAXD], nld[2], nrd[2];
static int vis[MAXV], que[MAXV], stamp_ = 0;

/* Vertex ids: left L_i(g) = i*N + g ; right R_j(h) = mo*N + j*N + h.
 * Arc of dart k from orbit src to orbit dst with shift s: L_src(g) ~ R_dst(g*s). */
static void set_pattern(int t) {
    int nd = 0;
    cur_t = t;
    if (mo == 1) {
        for (int k = 0; k < dd; k++) { dsrc[nd] = 0; ddst[nd] = 0; nd++; }
    } else {
        int pr[4][3] = {{0, 0, t}, {0, 1, dd - t}, {1, 0, dd - t}, {1, 1, t}};
        for (int p = 0; p < 4; p++)
            for (int c = 0; c < pr[p][2]; c++) {
                dsrc[nd] = pr[p][0];
                ddst[nd] = pr[p][1];
                nd++;
            }
    }
    NDART = nd;
    for (int k = 0; k < NDART; k++) dpair[k] = dsrc[k] * 2 + ddst[k];
    nld[0] = nld[1] = nrd[0] = nrd[1] = 0;
    for (int k = 0; k < NDART; k++) {
        ldart[dsrc[k]][nld[dsrc[k]]++] = k;
        rdart[ddst[k]][nrd[ddst[k]]++] = k;
    }
}

static void set_dart(int k, int x) {
    dsh[k] = x;
    dshi[k] = ginv(x);
    for (int g = 0; g < GN; g++) {
        fwd[k][g] = gmul(g, x);
        bwd[k][g] = gmul(g, dshi[k]);
    }
}

/* True if shift x already used by another dart k' < lim in the same orbit pair. */
static int conflict(int k, int x, int lim) {
    for (int j = 0; j < lim; j++)
        if (j != k && dpair[j] == dpair[k] && dsh[j] == x) return 1;
    return 0;
}

static int bfs_count(int src) {
    int N = GN, base = mo * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < DD && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < base) {
                int i = v / N, g = v - i * N;
                for (int q = 0; q < nld[i]; q++) {
                    int k = ldart[i][q];
                    int u = base + ddst[k] * N + fwd[k][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - base;
                int j = w / N, h = w - j * N;
                for (int q = 0; q < nrd[j]; q++) {
                    int k = rdart[j][q];
                    int u = dsrc[k] * N + bwd[k][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Orbit transitivity: one BFS from L_i(e) and one from R_i(e) for each i covers all
 * 2*mo vertex classes, so the cost is zero iff the diameter is at most DD. */
static long cover_cost(void) {
    int N = GN, V = 2 * mo * N;
    long c = 0;
    for (int i = 0; i < mo; i++) {
        c += (long)(V - bfs_count(i * N));
        c += (long)(V - bfs_count(mo * N + i * N));
    }
    return c;
}

static int search_group(double until) {
    int N = GN;
    const int iters = 6000;
    if (N <= dd + 1) return 0;
    while (now() < until) {
        set_pattern(mo == 2 ? 1 + rndint(dd / 2) : 0);
        for (int k = 0; k < NDART; k++) {
            int x;
            do { x = rndint(N); } while (conflict(k, x, k));
            set_dart(k, x);
        }
        long cost = cover_cost();
        double Ts = 0.05 * (double)cost + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int k = rndint(NDART);
            int x;
            do { x = rndint(N); } while (conflict(k, x, NDART));
            int old = dsh[k];
            set_dart(k, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_dart(k, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ candidates */

static Cand bestC;
static int best_t = 0, have_best = 0;
static int best_sh[MAXDART];

static void save_best(const Cand *cd) {
    bestC = *cd;
    best_t = cur_t;
    have_best = 1;
    memcpy(best_sh, dsh, sizeof(int) * (size_t)NDART);
}

static void apply_best(void) {
    setup_group(&bestC);
    set_pattern(best_t);
    for (int k = 0; k < NDART; k++) set_dart(k, best_sh[k]);
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static void add_cand(Cand *cs, int *nc, const Cand *cd) {
    if (*nc < MAXCAND) cs[(*nc)++] = *cd;
}

static void gen_cands(Cand *cs, int *nc, int vlo, int vhi) {
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 1; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            for (int mo_ = 1; mo_ <= 2; mo_++) {
                long N = (long)q * c;
                long V = 2L * mo_ * N;
                if (N > MAXN || V < vlo || V > vhi || V > MAXV) continue;
                Cand cd;
                memset(&cd, 0, sizeof cd);
                cd.type = 0; cd.a = q; cd.b = c; cd.p = p; cd.kf = k;
                cd.mo = mo_; cd.N = (int)N; cd.V = (int)V;
                add_cand(cs, nc, &cd);
            }
        }
    }
    for (int mo_ = 1; mo_ <= 2; mo_++) {
        int Nlo = (vlo + 2 * mo_ - 1) / (2 * mo_);
        int Nhi = vhi / (2 * mo_);
        if (Nhi > MAXN) Nhi = MAXN;
        for (int N = Nlo; N <= Nhi; N++) {
            for (int k = 1; k <= 8 && k <= N; k++) {
                if (N % k) continue;
                int m = N / k;
                if (m < 2) continue;
                for (int r = 1; r < m; r++) {
                    if (gcd_i(r, m) != 1) continue;
                    int rk = 1 % m;
                    for (int i = 0; i < k; i++) rk = rk * r % m;
                    if (rk != 1 % m) continue;
                    Cand cd;
                    memset(&cd, 0, sizeof cd);
                    cd.type = 1; cd.a = m; cd.b = k; cd.r = r;
                    cd.mo = mo_; cd.N = N; cd.V = 2 * mo_ * N;
                    add_cand(cs, nc, &cd);
                }
            }
        }
    }
}

static int cmp_cand(const void *x, const void *y) {
    const Cand *a = (const Cand *)x, *b = (const Cand *)y;
    if (a->V != b->V) return a->V < b->V ? -1 : 1;
    return 0;
}

static void print_result(void) {
    int N = GN, base = mo * N;
    printf("%d %d\n", 2 * mo * N, NDART * N);
    for (int k = 0; k < NDART; k++)
        for (int g = 0; g < N; g++)
            printf("%d %d\n", dsrc[k] * N + g, base + ddst[k] * N + fwd[k][g]);
}

/* ------------------------------------------------------------ main */

static Cand cand[MAXCAND];

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int vlo = atoi(argv[5]), vhi = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (dd < 2 || dd > MAXD || DD < 2) {
        printf("0 0\n");
        return 0;
    }
    if (vlo < 2 * dd) vlo = 2 * dd;
    if (vhi > MAXV) vhi = MAXV;
    if (vlo > vhi) {
        printf("0 0\n");
        return 0;
    }

    int nc = 0;
    gen_cands(cand, &nc, vlo, vhi);
    if (nc == 0) {
        printf("0 0\n");
        return 0;
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Phase 1: binary search over candidates sorted by vertex count. Each probe gets an
     * equal share of the remaining time over the probes still needed. */
    int bestI = -1;
    int a = 0, b = nc - 1;
    while (a <= b && now() < t_end) {
        int mid = (a + b) / 2;
        int span = b - a + 1, probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = t_end - now();
        double slice = rem / (probes + 1);
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        mo = cand[mid].mo;
        setup_group(&cand[mid]);
        NDART = mo * dd;
        if (search_group(now() + slice)) {
            if (bestI < 0 || cand[mid].V > cand[bestI].V) {
                bestI = mid;
                save_best(&cand[mid]);
            }
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }

    /* Phase 2: spend leftover time on the next few candidates above the best. */
    int fails = 0;
    int idx = bestI < 0 ? 0 : bestI + 1;
    while (idx < nc && now() < t_end && fails < 2) {
        if (bestI >= 0 && cand[idx].V <= cand[bestI].V) { idx++; continue; }
        double rem = t_end - now();
        double slice = rem * 0.5;
        if (slice > rem) slice = rem;
        mo = cand[idx].mo;
        setup_group(&cand[idx]);
        NDART = mo * dd;
        if (search_group(now() + slice)) {
            bestI = idx;
            save_best(&cand[idx]);
            fails = 0;
        } else {
            fails++;
        }
        idx++;
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    apply_best();
    print_result();
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

    # Two-orbit bi-Cayley search. Vertex counts are 2*mo*N with mo in {1, 2}.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        vlo = max(2 * d, mb // 5)
        vhi = min(16384, (2 * mb) // 5)
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
