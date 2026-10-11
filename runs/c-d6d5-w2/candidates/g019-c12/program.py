import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: Haar-type lifts over arbitrary finite groups.
#
# A graph is built from a group G of order N and a connection set S of DEG
# distinct elements: vertex a_g = g and b_h = N + h, with a_g ~ b_{g s} for
# s in S. Every vertex has degree DEG and the graph is bipartite. Left
# multiplication is an automorphism that is transitive on each side, so the
# diameter is at most D iff BFS of depth D from a_1 and from b_1 reaches all
# 2N vertices.
#
# Groups:
#   - semidirect products Z_m x| Z_k (r^k = 1 mod m), and
#   - matrix groups over small finite fields: SL(2,q), PSL(2,q), PGL(2,q)
#     for q in {5, 7, 8, 9, 11}. These are non-solvable or non-metacyclic.
#
# Search: simulated annealing over S for each sampled group, with restarts.
# Cost = number of uncovered vertices from the two BFS sources. A zero-cost
# set is a valid graph of order 2N. Only graphs with 2N above the current
# best are emitted.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1200
#define ITERS 15000
#define TEMP0 2.0

enum { FAM_SL = 0, FAM_PSL = 1, FAM_PGL = 2 };

static uint64_t rs[2];
static struct timespec TS0;
static double DEADLINE;

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - TS0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - TS0.tv_nsec);
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod(long long b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static int DEG, DIAM;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

/* ---------------- finite fields of order 5, 7, 8, 9, 11 ---------------- */

typedef struct { int q; int add[121]; int mul[121]; int neg[11]; int inv[11]; } Field;
static Field FT[12];

#define FADD(F, x, y) ((F)->add[(x) * (F)->q + (y)])
#define FMUL(F, x, y) ((F)->mul[(x) * (F)->q + (y)])
#define FNEG(F, x) ((F)->neg[(x)])

static void field_init(Field *F, int p, int k, const int *f) {
    int pw[8];
    int q = 1;
    for (int i = 0; i < k; i++) q *= p;
    pw[0] = 1;
    for (int i = 1; i <= k; i++) pw[i] = pw[i - 1] * p;
    F->q = q;
    for (int x = 0; x < q; x++) {
        for (int y = 0; y < q; y++) {
            int s = 0;
            int dx[8], dy[8];
            for (int i = 0; i < k; i++) {
                dx[i] = (x / pw[i]) % p;
                dy[i] = (y / pw[i]) % p;
                s += ((dx[i] + dy[i]) % p) * pw[i];
            }
            F->add[x * q + y] = s;
            int c[16];
            for (int i = 0; i < 16; i++) c[i] = 0;
            for (int i = 0; i < k; i++)
                for (int j = 0; j < k; j++)
                    c[i + j] = (c[i + j] + dx[i] * dy[j]) % p;
            for (int t = 2 * k - 2; t >= k; t--) {
                int co = c[t];
                c[t] = 0;
                for (int j = 0; j < k; j++)
                    c[t - k + j] = ((c[t - k + j] - co * f[j]) % p + p) % p;
            }
            int r = 0;
            for (int i = 0; i < k; i++) r += c[i] * pw[i];
            F->mul[x * q + y] = r;
        }
    }
    for (int x = 0; x < q; x++) {
        F->neg[x] = 0;
        for (int y = 0; y < q; y++)
            if (F->add[x * q + y] == 0) F->neg[x] = y;
        F->inv[x] = 0;
        for (int y = 0; y < q; y++)
            if (x != 0 && F->mul[x * q + y] == 1) F->inv[x] = y;
    }
}

/* ---------------- groups ---------------- */

typedef struct { int N, E; int *mul; int *inv; } Group;
static Group GR;

static void group_free(Group *G) {
    free(G->mul);
    free(G->inv);
    G->mul = NULL;
    G->inv = NULL;
}

static void finish_group(Group *G) {
    int N = G->N;
    G->inv = malloc(sizeof(int) * (size_t)N);
    for (int x = 0; x < N; x++) {
        G->inv[x] = 0;
        for (int y = 0; y < N; y++)
            if (G->mul[x * N + y] == G->E) { G->inv[x] = y; break; }
    }
}

/* (a,b)*(c,e) = (a + r^b c, b + e), element index a*k + b. */
static void build_semidirect(Group *G, int m, int k, int r) {
    int N = m * k;
    G->N = N;
    G->E = 0;
    G->mul = malloc(sizeof(int) * (size_t)N * N);
    int *rp = malloc(sizeof(int) * (size_t)k);
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            int ra = (int)(((long long)a + (long long)rp[b] * c) % m);
            int rb = (b + e) % k;
            G->mul[x * N + y] = ra * k + rb;
        }
    }
    free(rp);
    finish_group(G);
}

static int enc(int q, int a, int b, int c, int d) { return ((a * q + b) * q + c) * q + d; }

static void decode(int code, int q, int *a, int *b, int *c, int *d) {
    *d = code % q; code /= q;
    *c = code % q; code /= q;
    *b = code % q; code /= q;
    *a = code;
}

/* Canonical code of the class of matrix (a b; c d) under the quotient used. */
static int canon(const Field *F, int type, int a, int b, int c, int d) {
    int q = F->q;
    if (type == FAM_SL) return enc(q, a, b, c, d);
    if (type == FAM_PSL) {
        int o = enc(q, FNEG(F, a), FNEG(F, b), FNEG(F, c), FNEG(F, d));
        int s = enc(q, a, b, c, d);
        return s < o ? s : o;
    }
    int best = -1;
    for (int l = 1; l < q; l++) {
        int code = enc(q, FMUL(F, l, a), FMUL(F, l, b), FMUL(F, l, c), FMUL(F, l, d));
        if (best < 0 || code < best) best = code;
    }
    return best;
}

static void build_linear(Group *G, int type, int q) {
    const Field *F = &FT[q];
    int q4 = q * q * q * q;
    int *map = malloc(sizeof(int) * (size_t)q4);
    int *rep = malloc(sizeof(int) * (size_t)q4);
    for (int i = 0; i < q4; i++) map[i] = -1;
    int N = 0;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int d = 0; d < q; d++) {
                    int det = FADD(F, FMUL(F, a, d), FNEG(F, FMUL(F, b, c)));
                    if (type == FAM_PGL ? (det == 0) : (det != 1)) continue;
                    int code = enc(q, a, b, c, d);
                    if (canon(F, type, a, b, c, d) == code) {
                        map[code] = N;
                        rep[N] = code;
                        N++;
                    }
                }
    G->N = N;
    G->mul = malloc(sizeof(int) * (size_t)N * N);
    for (int i = 0; i < N; i++) {
        int a1, b1, c1, d1;
        decode(rep[i], q, &a1, &b1, &c1, &d1);
        for (int j = 0; j < N; j++) {
            int a2, b2, c2, d2;
            decode(rep[j], q, &a2, &b2, &c2, &d2);
            int A = FADD(F, FMUL(F, a1, a2), FMUL(F, b1, c2));
            int B = FADD(F, FMUL(F, a1, b2), FMUL(F, b1, d2));
            int C = FADD(F, FMUL(F, c1, a2), FMUL(F, d1, c2));
            int D = FADD(F, FMUL(F, c1, b2), FMUL(F, d1, d2));
            int idx = map[canon(F, type, A, B, C, D)];
            G->mul[i * N + j] = idx < 0 ? 0 : idx;
        }
    }
    G->E = map[canon(F, type, 1, 0, 0, 1)];
    if (G->E < 0) G->E = 0;
    free(map);
    free(rep);
    finish_group(G);
}

/* ---------------- Haar-lift search ---------------- */

static int S[64], Sbest[64];
static int stamp[2 * MAXN];
static int curst = 0;
static int fbuf[2 * MAXN], hbuf[2 * MAXN];

/* BFS depth DIAM from a_E (side 0) or b_E (side 1); returns number of vertices reached. */
static int bfs_count(int side) {
    const int N = GR.N, E = GR.E;
    const int *mul = GR.mul, *inv = GR.inv;
    if (curst > 2000000000) {
        memset(stamp, 0, sizeof(stamp));
        curst = 0;
    }
    curst++;
    int *f = fbuf, *h = hbuf;
    int fsz = 1, count = 1;
    int src = side ? N + E : E;
    f[0] = src;
    stamp[src] = curst;
    for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
        int nsz = 0;
        for (int q = 0; q < fsz; q++) {
            int v = f[q];
            if (v < N) {
                const int *row = mul + (size_t)v * N;
                for (int i = 0; i < DEG; i++) {
                    int w = N + row[S[i]];
                    if (stamp[w] != curst) { stamp[w] = curst; h[nsz++] = w; }
                }
            } else {
                int hh = v - N;
                const int *row = mul + (size_t)hh * N;
                for (int i = 0; i < DEG; i++) {
                    int w = row[inv[S[i]]];
                    if (stamp[w] != curst) { stamp[w] = curst; h[nsz++] = w; }
                }
            }
        }
        count += nsz;
        int *tmp = f; f = h; h = tmp;
        fsz = nsz;
    }
    return count;
}

static int cost_of(void) {
    int N2 = 2 * GR.N;
    return (N2 - bfs_count(0)) + (N2 - bfs_count(1));
}

static int in_S(int x, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == x) return 1;
    return 0;
}

static void emit_best(void) {
    int N = GR.N;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)N * DEG);
    int idx = 0;
    for (int g = 0; g < N; g++)
        for (int i = 0; i < DEG; i++) {
            best_e[idx++] = g;
            best_e[idx++] = N + GR.mul[g * N + Sbest[i]];
        }
    best_m = N * DEG;
    best_n = 2 * N;
}

/* Returns 1 with Sbest set when a zero-cost connection set is found. */
static int run_sa(void) {
    int N = GR.N;
    if (N < DEG) return 0;
    for (int i = 0; i < DEG; i++) {
        int x;
        do { x = rnd_int(N); } while (in_S(x, i));
        S[i] = x;
    }
    int cur = cost_of();
    if (cur == 0) {
        memcpy(Sbest, S, sizeof(int) * (size_t)DEG);
        return 1;
    }
    if (N == DEG) return 0;
    for (int it = 0; it < ITERS; it++) {
        if ((it & 255) == 0 && elapsed() > DEADLINE) return 0;
        double temp = TEMP0 * (1.0 - (double)it / ITERS) + 0.05;
        int i = rnd_int(DEG);
        int old = S[i];
        int x;
        do { x = rnd_int(N); } while (in_S(x, DEG));
        S[i] = x;
        int c2 = cost_of();
        if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / temp)) {
            cur = c2;
            if (cur == 0) {
                memcpy(Sbest, S, sizeof(int) * (size_t)DEG);
                return 1;
            }
        } else {
            S[i] = old;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n]\n");
        return 1;
    }
    timespec_get(&TS0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    best_n = argc > 5 ? atoi(argv[5]) : 0;
    best_m = 0;
    if (DEG < 2 || DEG > 60 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    field_init(&FT[5], 5, 1, NULL);
    field_init(&FT[7], 7, 1, NULL);
    field_init(&FT[11], 11, 1, NULL);
    static const int f8[3] = {1, 1, 0};   /* x^3 = x + 1 over GF(2) */
    static const int f9[2] = {1, 0};      /* x^2 = -1 over GF(3) */
    field_init(&FT[8], 2, 3, f8);
    field_init(&FT[9], 3, 2, f9);

    /* Upper bound on N: 2N <= Moore bound. */
    int hi;
    if (DEG == 2) {
        hi = DIAM;
    } else {
        double s = 0, pw = 1;
        for (int i = 0; i < DIAM; i++) { s += pw; pw *= (DEG - 1); }
        hi = s > 1100 ? 1100 : (int)s;
    }

    /* Linear group families (orders are fixed, so they are filtered once). */
    int fam_t[16], fam_q[16], fam_n[16], nfam = 0;
    static const int qs[5] = {5, 7, 8, 9, 11};
    for (int qi = 0; qi < 5; qi++) {
        int q = qs[qi];
        int even = (q % 2 == 0);
        for (int t = 0; t < 3; t++) {
            if (t == FAM_PSL && even) continue;
            if (t == FAM_PGL && even) continue;
            int N = q * (q * q - 1);
            if (t == FAM_PSL) N /= 2;
            if (N > 1100) continue;
            fam_t[nfam] = t;
            fam_q[nfam] = q;
            fam_n[nfam] = N;
            nfam++;
        }
    }

    while (elapsed() < DEADLINE) {
        int lo = best_n / 2 + 1;
        if (lo < DEG) lo = DEG;
        if (lo < 2) lo = 2;
        if (lo > hi) break;

        int cand[16], nc = 0;
        for (int f = 0; f < nfam; f++)
            if (fam_n[f] >= lo && fam_n[f] <= hi) cand[nc++] = f;

        if (nc > 0 && rnd_unit() < 0.45) {
            int f = cand[rnd_int(nc)];
            build_linear(&GR, fam_t[f], fam_q[f]);
        } else {
            int N = lo + rnd_int(hi - lo + 1);
            int divs[64], nd = 0;
            for (int k = 1; k <= N && nd < 64; k++)
                if (N % k == 0) divs[nd++] = k;
            int k = divs[rnd_int(nd)];
            int m = N / k;
            int r = 0;
            if (m > 1) {
                r = 1;
                for (int tr = 0; tr < 300; tr++) {
                    int cc = 1 + rnd_int(m - 1);
                    if (gcd_i(cc, m) == 1 && powmod(cc, k, m) == 1 % m) {
                        r = cc;
                        break;
                    }
                }
            }
            build_semidirect(&GR, m, k, r);
        }

        if (run_sa() && 2 * GR.N > best_n) emit_best();
        group_free(&GR);
    }

    if (best_m > 0) {
        printf("%d %d\n", best_n, best_m);
        for (int i = 0; i < best_m; i++)
            printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe Python baselines.
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
# Driver: baselines in Python, then the C Haar-lift search over non-abelian groups.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # One C run gets nearly all of the budget; the margin covers process start,
    # the cached compile step, parsing and validation.
    remaining = 0.9 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
