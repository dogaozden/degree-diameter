import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New construction: bipartite Cayley graphs (K = 1 base vertex) over groups
# that the voltage search cannot reach easily:
#   AGL(1,p)  (order p(p-1)),  PSL(2,p) (order p(p^2-1)/2),  PGL(2,p) (order p(p^2-1)).
#
# Graph: left vertices x in G, right vertices G+y in G. Connection set S has
# DEG distinct non-identity elements, and x ~ G + x*s for each s in S. Each side
# is regular of degree DEG. Left multiplication is an automorphism, so the
# diameter is checked by two BFS runs (from the left identity and from the
# right identity), and the cost is the number of pairs still too far apart.
# Simulated annealing over S finds cost 0 for a group, then the search climbs
# to larger groups.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define CAPG 5000
#define NCANDMAX 256

static uint64_t rs;
static uint64_t rnd64(void) {
    uint64_t x = rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rs = x;
    return x * 2685821657736338717ULL;
}
static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}
static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static int DEG, DIAM;
static double TEND;

/* group state: GT 0 = AGL(1,p), 1 = PSL(2,p), 2 = PGL(2,p) */
static int GT, GP, G, EID;
static int *MA = NULL;      /* 4*G matrix entries (matrix groups) */
static int *IDX4 = NULL;    /* p^4 map from canonical key to element index */
static int *INVP = NULL;    /* inverses mod p */
static uint16_t *MT = NULL; /* MT[u*G + y] = y*u */
static unsigned char *VALID = NULL;

static unsigned char *DIST = NULL;
static int *QU = NULL;
static int *BU = NULL, *BV = NULL;
static int BEST_G = 0, BEDGES = 0;

static int S[MAXD];
static uint16_t *CR[MAXD], *CL[MAXD];

typedef struct {
    int type, p, order, tries;
} Cand;
static Cand CAND[NCANDMAX];
static int NCAND = 0;

static int ipow(int b, int e, int m) {
    int64_t r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static int isprime(int n) {
    if (n < 2) return 0;
    for (int q = 2; q * q <= n; q++)
        if (n % q == 0) return 0;
    return 1;
}

static int keyof(int a, int b, int c, int d) {
    int p = GP;
    return ((a * p + b) * p + c) * p + d;
}

static int canon_key(int a, int b, int c, int d) {
    int p = GP;
    if (GT == 1) {
        int k1 = keyof(a, b, c, d);
        int k2 = keyof((p - a) % p, (p - b) % p, (p - c) % p, (p - d) % p);
        return k1 < k2 ? k1 : k2;
    }
    int f = a ? a : (b ? b : (c ? c : d));
    int iv = INVP[f];
    return keyof(a * iv % p, b * iv % p, c * iv % p, d * iv % p);
}

static void free_group(void) {
    free(MT);   MT = NULL;
    free(VALID); VALID = NULL;
    free(MA);   MA = NULL;
    free(IDX4); IDX4 = NULL;
    free(INVP); INVP = NULL;
}

static int build_group(int type, int p, int order) {
    free_group();
    GT = type;
    GP = p;
    G = order;
    INVP = malloc(sizeof(int) * (size_t)(p + 1));
    if (!INVP) return 0;
    INVP[0] = 0;
    for (int x = 1; x < p; x++) INVP[x] = ipow(x, p - 2, p);
    if (type == 0) {
        EID = 0;
    } else {
        long long P4 = (long long)p * p * p * p;
        IDX4 = malloc(sizeof(int) * (size_t)P4);
        MA = malloc(sizeof(int) * 4 * (size_t)G);
        if (!IDX4 || !MA) return 0;
        for (long long k = 0; k < P4; k++) IDX4[k] = -1;
        int cnt = 0;
        for (int a = 0; a < p; a++)
            for (int b = 0; b < p; b++)
                for (int c = 0; c < p; c++)
                    for (int d = 0; d < p; d++) {
                        int det = ((a * d - b * c) % p + p) % p;
                        int ok = (type == 1) ? (det == 1) : (det != 0);
                        if (!ok) continue;
                        if (canon_key(a, b, c, d) != keyof(a, b, c, d)) continue;
                        if (cnt >= G) return 0;
                        MA[4 * cnt + 0] = a;
                        MA[4 * cnt + 1] = b;
                        MA[4 * cnt + 2] = c;
                        MA[4 * cnt + 3] = d;
                        IDX4[keyof(a, b, c, d)] = cnt;
                        cnt++;
                    }
        if (cnt != G) return 0;
        EID = IDX4[canon_key(1, 0, 0, 1)];
    }
    MT = malloc(sizeof(uint16_t) * (size_t)G * (size_t)G);
    VALID = calloc((size_t)G, 1);
    if (!MT || !VALID) return 0;
    return 1;
}

static int gmul(int x, int y) {
    int p = GP;
    if (GT == 0) {
        int a1 = x / p + 1, b1 = x % p, a2 = y / p + 1, b2 = y % p;
        int a3 = a1 * a2 % p;
        int b3 = (a1 * b2 + b1) % p;
        return (a3 - 1) * p + b3;
    }
    const int *m = MA + 4 * x;
    const int *n = MA + 4 * y;
    int a = (m[0] * n[0] + m[1] * n[2]) % p;
    int b = (m[0] * n[1] + m[1] * n[3]) % p;
    int c = (m[2] * n[0] + m[3] * n[2]) % p;
    int d = (m[2] * n[1] + m[3] * n[3]) % p;
    return IDX4[canon_key(a, b, c, d)];
}

static int ginv(int x) {
    int p = GP;
    if (GT == 0) {
        int a = x / p + 1, b = x % p;
        int ai = INVP[a];
        int bi = (p - (ai * b) % p) % p;
        return (ai - 1) * p + bi;
    }
    const int *m = MA + 4 * x;
    return IDX4[canon_key(m[3], (p - m[1]) % p, (p - m[2]) % p, m[0])];
}

static uint16_t *mtcol(int u) {
    if (!VALID[u]) {
        uint16_t *col = MT + (size_t)u * G;
        for (int y = 0; y < G; y++) col[y] = (uint16_t)gmul(y, u);
        VALID[u] = 1;
    }
    return MT + (size_t)u * G;
}

static void setcol(int i) {
    CR[i] = mtcol(S[i]);
    CL[i] = mtcol(ginv(S[i]));
}

static int in_prefix(int x, int upto) {
    for (int j = 0; j < upto; j++)
        if (S[j] == x) return 1;
    return 0;
}

/* Cost = pairs too far apart: unreached from left identity (all vertices)
   plus unreached right vertices from right identity. Zero iff diameter <= DIAM. */
static int64_t eval_cost(void) {
    int V = 2 * G;
    int64_t cost = 0;
    for (int pass = 0; pass < 2; pass++) {
        int src = (pass == 0) ? EID : G + EID;
        memset(DIST, 255, (size_t)V);
        int head = 0, tail = 0;
        QU[tail++] = src;
        DIST[src] = 0;
        while (head < tail) {
            int v = QU[head++];
            int dv = DIST[v];
            if (dv >= DIAM) continue;
            if (v < G) {
                for (int i = 0; i < DEG; i++) {
                    int w = G + CR[i][v];
                    if (DIST[w] == 255) {
                        DIST[w] = (unsigned char)(dv + 1);
                        QU[tail++] = w;
                    }
                }
            } else {
                int y = v - G;
                for (int i = 0; i < DEG; i++) {
                    int w = CL[i][y];
                    if (DIST[w] == 255) {
                        DIST[w] = (unsigned char)(dv + 1);
                        QU[tail++] = w;
                    }
                }
            }
        }
        if (pass == 0) {
            cost += V - tail;
        } else {
            int rc = 0;
            for (int k = 0; k < tail; k++)
                if (QU[k] >= G) rc++;
            cost += G - rc;
        }
    }
    return cost;
}

static void init_S(void) {
    for (int i = 0; i < DEG; i++) {
        int x;
        do {
            x = rndint(G);
        } while (x == EID || in_prefix(x, i));
        S[i] = x;
    }
    for (int i = 0; i < DEG; i++) setcol(i);
}

static void save_best(void) {
    int k = 0;
    for (int x = 0; x < G; x++) {
        for (int i = 0; i < DEG; i++) {
            BU[k] = x;
            BV[k] = G + (int)CR[i][x];
            k++;
        }
    }
    BEDGES = k;
    BEST_G = G;
}

/* Try to find a valid connection set in the currently built group. */
static int attempt(int ci, double deadline) {
    if (!build_group(CAND[ci].type, CAND[ci].p, CAND[ci].order)) return 0;
    const int ITERS = 20000;
    while (now_s() < deadline) {
        init_S();
        int64_t cur = eval_cost();
        if (cur == 0) {
            save_best();
            return 1;
        }
        double T0 = 0.05 * (double)cur + 1.0;
        for (int t = 0; t < ITERS; t++) {
            if ((t & 127) == 0 && now_s() > deadline) return 0;
            double T = T0 * (1.0 - (double)t / ITERS) + 0.2;
            int i = rndint(DEG);
            int old = S[i];
            int x;
            do {
                x = rndint(G);
            } while (x == EID || in_prefix(x, DEG));
            S[i] = x;
            setcol(i);
            int64_t c2 = eval_cost();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
                if (cur == 0) {
                    save_best();
                    return 1;
                }
            } else {
                S[i] = old;
                setcol(i);
            }
        }
    }
    return 0;
}

static void add_cand(int type, int p, int order) {
    if (NCAND < NCANDMAX) {
        CAND[NCAND].type = type;
        CAND[NCAND].p = p;
        CAND[NCAND].order = order;
        CAND[NCAND].tries = 0;
        NCAND++;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double TL = atof(argv[4]);
    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();
    double t0 = now_s();
    TEND = t0 + TL;

    if (DEG < 3 || DEG > MAXD || DIAM < 3 || DIAM > 200) {
        printf("0 0\n");
        return 0;
    }

    DIST = malloc((size_t)2 * CAPG);
    QU = malloc(sizeof(int) * (size_t)2 * CAPG);
    BU = malloc(sizeof(int) * (size_t)CAPG * MAXD);
    BV = malloc(sizeof(int) * (size_t)CAPG * MAXD);
    if (!DIST || !QU || !BU || !BV) {
        printf("0 0\n");
        return 0;
    }

    double moore = 0.0, pw = 1.0;
    for (int i = 0; i < DIAM; i++) {
        moore += pw;
        pw *= (double)(DEG - 1);
    }
    moore *= 2.0;
    int maxG = CAPG;
    if (moore / 2.0 < (double)maxG) maxG = (int)(moore / 2.0);

    /* candidate groups */
    for (int p = 3; p <= 80; p++) {
        if (!isprime(p)) continue;
        int o = p * (p - 1);
        if (o >= DEG + 1 && o <= maxG) add_cand(0, p, o);
    }
    int psl_p[] = {5, 7, 11, 13, 17, 19};
    for (int i = 0; i < 6; i++) {
        int p = psl_p[i];
        int o = p * (p * p - 1) / 2;
        if (o >= DEG + 1 && o <= maxG) add_cand(1, p, o);
    }
    int pgl_p[] = {3, 5, 7, 11, 13, 17};
    for (int i = 0; i < 6; i++) {
        int p = pgl_p[i];
        int o = p * (p * p - 1);
        if (o >= DEG + 1 && o <= maxG) add_cand(2, p, o);
    }
    for (int a = 1; a < NCAND; a++) {
        Cand t = CAND[a];
        int b = a - 1;
        while (b >= 0 && CAND[b].order > t.order) {
            CAND[b + 1] = CAND[b];
            b--;
        }
        CAND[b + 1] = t;
    }

    int best_order = 0;
    int have = 0;
    while (now_s() < TEND - 0.3) {
        int pool[NCANDMAX];
        int np = 0;
        for (int c = 0; c < NCAND; c++)
            if (CAND[c].order > best_order && CAND[c].tries < 2) pool[np++] = c;
        if (np == 0) break;
        int lim = np < 4 ? np : 4;
        int pick = pool[rndint(lim)];
        double slice = TL / 10.0;
        if (slice < 2.0) slice = 2.0;
        double dl = now_s() + slice;
        if (dl > TEND) dl = TEND;
        if (attempt(pick, dl)) {
            best_order = CAND[pick].order;
            have = 1;
        } else {
            CAND[pick].tries++;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", 2 * BEST_G, BEDGES);
    for (int k = 0; k < BEDGES; k++)
        printf("%d %d\n", BU[k], BV[k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions used as start graphs (kept from the parent).
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
# Main build: exact constructions, then the bi-Cayley search in C.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n:
            try:
                ok = lib.is_valid(n, e, d, D)
            except Exception:
                ok = False
            if ok:
                best = (n, e)
                best_n = n

    if d == 2:
        # Cycle C_{2D} has max degree 2 and diameter D.
        consider(2 * D, [(i, (i + 1) % (2 * D)) for i in range(2 * D)])
        return best
    if d < 3:
        return best

    if D == 3:
        if lib.is_prime_power(d - 1):
            n, e = lib.projective_plane_incidence(d - 1)
            consider(n, e)
            return best
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n, e = lib.araujo_lopez_graph(d - 2)
                consider(n, e)
            except Exception:
                pass

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search, entirely in C.
    elapsed = time.monotonic() - start
    avail = time_limit - elapsed - 6.0
    if avail >= 3.0:
        c_tl = min(avail, 0.8 * time_limit)
        try:
            text = lib.run_c(C_SOURCE,
                             [d, D, int(seed) & 0x7FFFFFFF, round(c_tl, 2)],
                             timeout=c_tl + 8.0)
            n2, e2 = lib.parse_graph_text(text)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
