import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold variant: tabu search over bi-Cayley lifts instead of annealing.
#
# Changes from the parent:
#   - search dynamics: each iteration samples NCAND random moves, applies the
#     best non-tabu one (aspiration if it beats the best cost), and forbids
#     undoing a voltage change for a short tenure. No temperature.
#   - larger base: up to MAXK = 8 vertices per side (uint32 reach masks).
#   - restarts: each trial draws a fresh random layer/voltage state for a new
#     group, so the search explores many small base structures.
#   - moves: voltage change (defect-directed half the time), voltage swap
#     across layers, layer swap.
# Python side: exact constructions (PG(2,q), W(q)) give the fallback, the C
# search runs with the remaining budget, then greedy slack extension. Every
# candidate passes lib.is_valid, and the K_{d,d} fallback is kept otherwise.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXK 8
#define NCHOICE 20
#define PEN 1000
#define NCAND 12
#define TRIAL_IT 1500
#define TRIAL_PAT 350
#define TENURE_MIN 4
#define TENURE_SPAN 8

typedef struct {
    int type;   /* 0 voltage change, 1 voltage swap between layers, 2 layer swap */
    int l, l2, i1, i2, old, nw;
} Move;

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

static const int K2_CHOICES[NCHOICE] = {1,1,2,2,3,4,5,6,7,8,9,10,12,14,16,18,20,24,30,36};

static int DEG, DIAM, CAP;
static int K, K2, M, R, G, N;
static int64_t PWR[64];
static int *AA, *BB;
static int *nbr, *lay, *vol;
static int64_t *tabu;
static int64_t GT = 0;
static uint32_t *cur, *scr, *tmpb;
static uint32_t FULL;
static int timed_out;
static double TL, tstart;
static int *bestnbr;
static int best_stride, best_K, best_G, have_best;

static double elapsed(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
}

static int64_t powmod(int64_t b, int64_t e, int64_t m) {
    int64_t r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int64_t gcd64(int64_t a, int64_t b) {
    while (b) {
        int64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int sample_group(int64_t target) {
    for (int attempt = 0; attempt < 200; attempt++) {
        int k2 = K2_CHOICES[rndint(NCHOICE)];
        int64_t m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int64_t r = -1;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rnd01() < 0.3) {
            r = m - 1;
            if (powmod(r, 2, m) != 1 % m) continue;
        } else {
            for (int tries = 0; tries < 60; tries++) {
                int64_t c = (m > 2) ? 2 + rndint((int)(m - 2)) : 1;
                if (gcd64(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                    r = c;
                    break;
                }
            }
            if (r < 0) continue;
        }
        M = (int)m;
        K2 = k2;
        R = (int)r;
        G = M * K2;
        return 1;
    }
    return 0;
}

static void setup_group(void) {
    for (int t = 0; t < K2; t++) PWR[t] = powmod(R, t, M);
    for (int x = 0; x < G; x++) {
        AA[x] = x / K2;
        BB[x] = x % K2;
    }
}

/* (a,b)(c,e) = (a + r^b c, b + e) */
static inline int gmul(int x, int y) {
    int bx = BB[x];
    int64_t a2 = (AA[x] + PWR[bx] * (int64_t)AA[y]) % M;
    int b2 = (bx + BB[y]) % K2;
    return (int)(a2 * K2 + b2);
}

/* inverse of (a,b) is (-r^{-b} a, -b) */
static inline int ginv(int x) {
    int b = BB[x];
    int nb = (K2 - b) % K2;
    int64_t a2 = (M - (PWR[nb] * (int64_t)AA[x]) % M) % M;
    return (int)(a2 * K2 + nb);
}

/* dart (i, p, s) in layer l: A_i,g ~ B_p,g*s for all g */
static void set_dart(int l, int i, int p, int s) {
    int is = ginv(s);
    int *row = nbr + (size_t)l * N;
    int Ab = i * G, Bb = (K + p) * G;
    for (int g = 0; g < G; g++) {
        row[Ab + g] = Bb + gmul(g, s);
        row[Bb + g] = Ab + gmul(g, is);
    }
}

static inline int pop32(uint32_t x) {
    int c = 0;
    while (x) {
        x &= x - 1;
        c++;
    }
    return c;
}

/* out[v] bit b set iff v is within DIAM of source vertex b*G (orbit representative). */
static void compute_reach(uint32_t *out) {
    int NN = N;
    memset(out, 0, sizeof(uint32_t) * (size_t)NN);
    for (int b = 0; b < 2 * K; b++) out[b * G] = 1u << b;
    for (int t = 0; t < DIAM; t++) {
        int changed = 0;
        for (int v = 0; v < NN; v++) {
            uint32_t x = out[v];
            for (int l = 0; l < DEG; l++) x |= out[nbr[(size_t)l * NN + v]];
            tmpb[v] = x;
            if (x != out[v]) changed = 1;
        }
        if (!changed) break;
        memcpy(out, tmpb, sizeof(uint32_t) * (size_t)NN);
    }
}

static int64_t unreached(const uint32_t *r) {
    int64_t s = 0;
    for (int v = 0; v < N; v++) s += pop32(r[v]);
    return (int64_t)2 * K * N - s;
}

static int dupcount(void) {
    int n = DEG * K, dup = 0;
    for (int e = 0; e < n; e++) {
        int i = e % K;
        for (int f = i; f < e; f += K) {
            if (lay[f] == lay[e] && vol[f] == vol[e]) {
                dup++;
                break;
            }
        }
    }
    return dup;
}

static int64_t total_cost(const uint32_t *r) {
    return unreached(r) + (int64_t)PEN * dupcount();
}

static void apply_move(const Move *m) {
    if (m->type == 0) {
        int e = m->l * K + m->i1;
        vol[e] = m->nw;
        set_dart(m->l, m->i1, lay[e], m->nw);
    } else if (m->type == 1) {
        int e1 = m->l * K + m->i1, e2 = m->l2 * K + m->i1;
        int t = vol[e1];
        vol[e1] = vol[e2];
        vol[e2] = t;
        set_dart(m->l, m->i1, lay[e1], vol[e1]);
        set_dart(m->l2, m->i1, lay[e2], vol[e2]);
    } else {
        int e1 = m->l * K + m->i1, e2 = m->l * K + m->i2;
        int t = lay[e1];
        lay[e1] = lay[e2];
        lay[e2] = t;
        set_dart(m->l, m->i1, lay[e1], vol[e1]);
        set_dart(m->l, m->i2, lay[e2], vol[e2]);
    }
}

static void undo_move(const Move *m) {
    if (m->type == 0) {
        int e = m->l * K + m->i1;
        vol[e] = m->old;
        set_dart(m->l, m->i1, lay[e], m->old);
    } else {
        apply_move(m); /* swaps are involutions */
    }
}

static int gen_move(Move *m, int defu) {
    double r = rnd01();
    if (r < 0.6) {
        m->type = 0;
        m->l = rndint(DEG);
        m->i1 = rndint(K);
        if (defu >= 0 && rnd01() < 0.5) {
            int b = defu / G;
            if (b < K) {
                m->i1 = b;
            } else {
                int p = b - K, f = -1;
                for (int j = 0; j < K; j++) {
                    if (lay[m->l * K + j] == p) {
                        f = j;
                        break;
                    }
                }
                if (f < 0) return 0;
                m->i1 = f;
            }
        }
        int e = m->l * K + m->i1;
        m->old = vol[e];
        m->nw = rndint(G);
        return m->nw != m->old;
    }
    if (r < 0.85) {
        if (DEG < 2) return 0;
        m->type = 1;
        m->l = rndint(DEG);
        m->l2 = rndint(DEG - 1);
        if (m->l2 >= m->l) m->l2++;
        m->i1 = rndint(K);
        return vol[m->l * K + m->i1] != vol[m->l2 * K + m->i1];
    }
    if (K < 2) return 0;
    m->type = 2;
    m->l = rndint(DEG);
    m->i1 = rndint(K);
    m->i2 = rndint(K - 1);
    if (m->i2 >= m->i1) m->i2++;
    return 1;
}

/* Tabu search from the current lift state. Returns 1 iff cost reaches 0. */
static int tabu_search(int maxit, int patience) {
    compute_reach(cur);
    int64_t cost = total_cost(cur);
    int64_t best = cost;
    int last = 0;
    timed_out = 0;
    for (int it = 0; it < maxit && cost != 0; it++) {
        if (it - last > patience) break;
        if ((it & 7) == 0 && elapsed() > TL) {
            timed_out = 1;
            break;
        }
        GT++;
        int defu = -1, cnt = 0;
        for (int v = 0; v < N; v++) {
            if (cur[v] != FULL) {
                cnt++;
                if (rndint(cnt) == 0) defu = v;
            }
        }
        Move bm;
        int64_t bc = 0;
        int have = 0;
        for (int c = 0; c < NCAND; c++) {
            Move m;
            if (!gen_move(&m, defu)) continue;
            apply_move(&m);
            compute_reach(scr);
            int64_t c2 = total_cost(scr);
            undo_move(&m);
            if (m.type == 0 &&
                tabu[(size_t)(m.l * K + m.i1) * CAP + m.nw] > GT && c2 >= best)
                continue;
            if (!have || c2 < bc || (c2 == bc && rnd01() < 0.5)) {
                bc = c2;
                bm = m;
                have = 1;
            }
        }
        if (!have) continue;
        apply_move(&bm);
        if (bm.type == 0) {
            tabu[(size_t)(bm.l * K + bm.i1) * CAP + bm.old] =
                GT + TENURE_MIN + rndint(TENURE_SPAN);
        }
        compute_reach(cur);
        cost = total_cost(cur);
        if (cost < best) {
            best = cost;
            last = it;
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: d D target cap seed time\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    long long best0 = atoll(argv[3]);
    CAP = atoi(argv[4]);
    unsigned long long seed = strtoull(argv[5], NULL, 10);
    TL = atof(argv[6]);
    tstart = (double)clock() / CLOCKS_PER_SEC;

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (DEG < 3 || DIAM < 3 || CAP < 8) {
        printf("0 0\n");
        return 0;
    }

    AA = malloc(sizeof(int) * (size_t)(CAP + 1));
    BB = malloc(sizeof(int) * (size_t)(CAP + 1));
    nbr = malloc(sizeof(int) * (size_t)DEG * CAP);
    bestnbr = malloc(sizeof(int) * (size_t)DEG * CAP);
    lay = malloc(sizeof(int) * (size_t)DEG * MAXK);
    vol = malloc(sizeof(int) * (size_t)DEG * MAXK);
    tabu = calloc((size_t)DEG * MAXK * CAP, sizeof(int64_t));
    cur = malloc(sizeof(uint32_t) * (size_t)CAP);
    scr = malloc(sizeof(uint32_t) * (size_t)CAP);
    tmpb = malloc(sizeof(uint32_t) * (size_t)CAP);
    if (!AA || !BB || !nbr || !bestnbr || !lay || !vol || !tabu || !cur || !scr || !tmpb) {
        printf("0 0\n");
        return 0;
    }

    long long found = best0;
    while (elapsed() < TL) {
        if (found >= CAP) break;
        int k = 1 + rndint(MAXK);
        int64_t base = found / (2 * k);
        int64_t span = base / 10 + 2;
        int64_t target = base + 1 + rndint((int)span);
        if (target < 2) target = 2;
        if (!sample_group(target)) continue;
        long long Nn = 2LL * k * G;
        if (Nn <= found || Nn > CAP) continue;

        K = k;
        N = (int)Nn;
        FULL = (uint32_t)((1u << (2 * K)) - 1);
        setup_group();

        /* fresh random state for this trial */
        for (int l = 0; l < DEG; l++) {
            int perm[MAXK];
            for (int i = 0; i < K; i++) perm[i] = i;
            for (int i = K - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = perm[i];
                perm[i] = perm[j];
                perm[j] = t;
            }
            for (int i = 0; i < K; i++) lay[l * K + i] = perm[i];
        }
        for (int e = 0; e < DEG * K; e++) vol[e] = rndint(G);
        for (int l = 0; l < DEG; l++)
            for (int i = 0; i < K; i++)
                set_dart(l, i, lay[l * K + i], vol[l * K + i]);

        int ok = tabu_search(TRIAL_IT, TRIAL_PAT);
        if (ok) {
            found = N;
            memcpy(bestnbr, nbr, sizeof(int) * (size_t)DEG * N);
            best_stride = N;
            best_K = K;
            best_G = G;
            have_best = 1;
        }
        if (timed_out) break;
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    int KG = best_K * best_G;
    long long m = (long long)KG * DEG;
    printf("%d %lld\n", best_stride, m);
    for (int u = 0; u < KG; u++)
        for (int l = 0; l < DEG; l++)
            printf("%d %d\n", u, bestnbr[(size_t)l * best_stride + u]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions used as the start graph.
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
# Slack extension: add new vertices using spare degree, accepting only
# graphs that pass lib.is_valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Main build: exact constructions first, then the C tabu search, then slack.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 9.0))
    final_deadline = start + max(1.0, time_limit - 3.0)
    rng = random.Random(seed)

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

    # Exact constructions; return immediately on calibration-style cases.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < start + budget:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search, entirely in C.
    if d >= 3 and D >= 3:
        remaining = start + budget - time.monotonic()
        if remaining > 2.0:
            cap = lib.moore_bound(d, D)
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, best_n, cap, int(seed) & 0x7FFFFFFF, round(remaining, 2)],
                                 timeout=remaining + 3.0)
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        try:
            n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
