"""Metacyclic and affine group Haar lifts for the bipartite degree-diameter problem.

Change in this version: the C engine now searches two group families, not one.
(1) The affine groups F_q x| H (H the order-c subgroup of F_q^*, |G| = q*c).
(2) Metacyclic groups Z_m x| Z_k, with Z_k acting on Z_m by multiplication by r,
    r^k = 1 mod m, gcd(r, m) = 1. This family includes the cyclic and abelian
    cases (r = 1) and the groups that the earlier semidirect runs missed.
For each group the engine precomputes a full Cayley table, so every multiplication
is a table lookup. A candidate is a d-element connection set S in G, giving the
bipartite Haar graph L_g ~ R_{g s} for s in S. This graph is d-regular, simple and
bipartite. Left translation is transitive on each side, so the diameter check
reduces to two BFS runs from L_e and R_e.

Search: candidate groups are enumerated in ascending order, with a random sample
of at most 12 groups per order N. Each group gets a short slice of time and runs
iterated annealing: each round perturbs the incumbent connection set by two
replacements and anneals from a lower starting temperature. Python keeps the
valid fallbacks (K_{d,d}, projective-plane incidence, Araujo-Lopez) and verifies
every returned graph with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Haar-lift search over affine groups F_q x| H and metacyclic groups Z_m x| Z_k.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
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
#define MAXD 32
#define MAXN 3600
#define MAXCAND 50000
#define PERN 12
#define TMPN 4096

typedef struct { int type, q, p, k, c, m, kk, r, N; } Cand;

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

/* ------------------------------------------------------------ Cayley tables */

static int GN = 0, capN = 0;
static int *MT = NULL;     /* MT[x*GN + y] = x*y */
static int *INVT = NULL;   /* INVT[x] = x^-1 */

static int ensure_group(int N) {
    if (N > capN) {
        free(MT);
        free(INVT);
        MT = malloc(sizeof(int) * (size_t)N * (size_t)N);
        INVT = malloc(sizeof(int) * (size_t)N);
        if (!MT || !INVT) { capN = 0; GN = 0; return 0; }
        capN = N;
    }
    GN = N;
    return 1;
}

static void compute_inv(void) {
    int N = GN;
    for (int x = 0; x < N; x++) {
        INVT[x] = -1;
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INVT[x] = y; break; }
    }
}

/* Affine group: element (a, h_j) coded a*c + j, h_j = g^(j*(q-1)/c).
 * (a, h)(b, h') = (a + h*b, h*h'). */
static int setup_affine(int q, int p, int k, int c) {
    build_field(q, p, k);
    int N = q * c;
    if (!ensure_group(N)) return 0;
    int g = -1;
    for (int g0 = 2; g0 < q && g < 0; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) g = g0;
    }
    if (g < 0) return 0;
    int PW[MAXQ], Hel[MAXQ], hidx[MAXQ];
    PW[0] = 1;
    for (int i = 1; i < q - 1; i++) PW[i] = MULT[PW[i - 1]][g];
    int step = (q - 1) / c;
    for (int j = 0; j < q; j++) hidx[j] = -1;
    for (int t = 0; t < c; t++) {
        Hel[t] = PW[(t * step) % (q - 1)];
        hidx[Hel[t]] = t;
    }
    for (int x = 0; x < N; x++) {
        int a = x / c, j = x % c;
        for (int y = 0; y < N; y++) {
            int b = y / c, t = y % c;
            int na = ADDT[a][MULT[Hel[j]][b]];
            int nt = hidx[MULT[Hel[j]][Hel[t]]];
            MT[x * N + y] = na * c + nt;
        }
    }
    compute_inv();
    return 1;
}

/* Metacyclic group Z_m x| Z_kk: element (a, b) coded a*kk + b.
 * (a, b)(c, d) = (a + r^b * c, b + d). Needs r^kk = 1 mod m. */
static int setup_meta(int m, int kk, int r) {
    int N = m * kk;
    if (!ensure_group(N)) return 0;
    int P[MAXN];
    P[0] = 1 % m;
    for (int b = 1; b < kk; b++) P[b] = (int)((long)P[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / kk, b = x % kk;
        for (int y = 0; y < N; y++) {
            int c = y / kk, dd = y % kk;
            int na = (int)((a + (long)P[b] * c) % m);
            int nb = (b + dd) % kk;
            MT[x * N + y] = na * kk + nb;
        }
    }
    compute_inv();
    return 1;
}

static int setup_cand(const Cand *cd) {
    if (cd->type == 0) return setup_affine(cd->q, cd->p, cd->k, cd->c);
    return setup_meta(cd->m, cd->kk, cd->r);
}

static int powmod(int b, int e, int m) {
    long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* ------------------------------------------------------------ Haar graph state */

static int S[MAXD], Sinv[MAXD], bestS[MAXD];
static int fwd[MAXD][MAXN], bwd[MAXD][MAXN];
static int vis[2 * MAXN], que[2 * MAXN];
static int stamp_ = 0;

/* L_g ~ R_{g s}, so R_h ~ L_{h s^-1}. */
static void set_s(int i, int x) {
    int N = GN;
    S[i] = x;
    Sinv[i] = INVT[x];
    for (int g = 0; g < N; g++) {
        fwd[i][g] = MT[g * N + x];
        bwd[i][g] = MT[g * N + Sinv[i]];
    }
}

static int bfs_count(int src) {
    int N = GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int u = N + fwd[i][v];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int h = v - N;
                for (int i = 0; i < d; i++) {
                    int u = bwd[i][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Vertex-transitivity on each side: two BFS runs decide the diameter. */
static long cover_cost(void) {
    int V = 2 * GN;
    return (long)(V - bfs_count(0)) + (long)(V - bfs_count(GN));
}

static int in_S(int x, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == x) return 1;
    return 0;
}

/* Iterated annealing over the connection set S (size d) in the current group.
 * Round 1 starts random. Later rounds start from the incumbent with two elements
 * replaced, at a lower starting temperature. Returns 1 on cost 0, 0 on timeout. */
static int search_group(double until) {
    int N = GN;
    const int iters = 8000;
    int have = 0;
    long bestc = 0;
    int incS[MAXD];
    while (now() < until) {
        if (!have) {
            for (int i = 0; i < d; i++) {
                int x;
                do { x = rndint(N); } while (in_S(x, i));
                set_s(i, x);
            }
        } else {
            for (int i = 0; i < d; i++) set_s(i, incS[i]);
            for (int t = 0; t < 2; t++) {
                int i = rndint(d), x;
                do { x = rndint(N); } while (in_S(x, d));
                set_s(i, x);
            }
        }
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(d);
            int x;
            do { x = rndint(N); } while (in_S(x, d));
            int old = S[i];
            set_s(i, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_s(i, old);
            }
        }
        if (cost == 0) return 1;
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(incS, S, sizeof(int) * (size_t)d);
        }
    }
    return 0;
}

static void print_result(void) {
    int N = GN;
    printf("%d %d\n", 2 * N, N * d);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + fwd[i][g]);
}

/* ------------------------------------------------------------ main */

static Cand cand[MAXCAND];
static Cand tmp[TMPN];

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    t_end = now() + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (hi > MAXN) hi = MAXN;
    if (lo < 2 * d) lo = 2 * d;
    if (lo > hi) { printf("0 0\n"); return 0; }

    /* Enumerate candidate groups in ascending order of N. For each N, keep a random
     * sample of at most PERN groups from both families. */
    int nc = 0;
    for (int N = lo; N <= hi; N++) {
        int nt = 0;
        /* Affine F_q x| H with |G| = q*c, c | q-1, 2 <= c <= q-1. */
        for (int q = 3; q <= N / 2; q++) {
            if (N % q) continue;
            int p, k;
            if (!factor_pp(q, &p, &k)) continue;
            int c = N / q;
            if (c < 2 || c > q - 1 || (q - 1) % c) continue;
            if (nt < TMPN) {
                Cand cd = {0, q, p, k, c, 0, 0, 0, N};
                tmp[nt++] = cd;
            }
        }
        /* Metacyclic Z_m x| Z_kk with r of order dividing kk mod m. */
        for (int kk = 2; kk <= N / 2; kk++) {
            if (N % kk) continue;
            int m = N / kk;
            for (int r = 1; r < m; r++) {
                if (gcdi(r, m) != 1) continue;
                if (powmod(r, kk, m) != 1 % m) continue;
                if (nt < TMPN) {
                    Cand cd = {1, 0, 0, 0, 0, m, kk, r, N};
                    tmp[nt++] = cd;
                }
            }
        }
        for (int i = nt - 1; i > 0; i--) {
            int j = rndint(i + 1);
            Cand t = tmp[i];
            tmp[i] = tmp[j];
            tmp[j] = t;
        }
        int keep = nt < PERN ? nt : PERN;
        for (int i = 0; i < keep && nc < MAXCAND; i++) cand[nc++] = tmp[i];
    }

    /* Ascending order. Each attempt gets a short slice (about 12% of the remaining
     * time, at least 0.6 s), so many groups get a chance. Groups at or below the
     * current best order are skipped. */
    int best_idx = -1, bestN = 0;
    static int bestS_init = 0;
    (void)bestS_init;
    for (int ci = 0; ci < nc; ci++) {
        double rem = t_end - now();
        if (rem < 0.3) break;
        if (cand[ci].N <= bestN) continue;
        double slice = 0.12 * rem;
        if (slice < 0.6) slice = 0.6;
        if (slice > rem) slice = rem;
        if (!setup_cand(&cand[ci])) continue;
        if (search_group(now() + slice)) {
            bestN = GN;
            best_idx = ci;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
        }
    }

    if (best_idx < 0) {
        printf("0 0\n");
        return 0;
    }
    if (!setup_cand(&cand[best_idx])) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < d; i++) set_s(i, bestS[i]);
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

    # Search: Haar graphs over affine and metacyclic groups in the order range [lo, hi].
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] // 2 + 1, mb // 8)
        hi = min(mb // 3, 3600)
        if budget > 2.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
