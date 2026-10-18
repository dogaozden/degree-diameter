import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley lift search, tabu variant.
#
# Model: base graph with K vertices per side and DEG perfect matchings (layers).
# Layer l matches base A_i to base B_{lay[l][i]} with voltage vol[l][i] in
# G = Z_M x| Z_K2. The lift has 2*K*G vertices and is bipartite, G-invariant.
#
# Differences from the annealing engine it replaces:
#   - tabu search: each step samples NCAND moves (voltage, layer swap, voltage
#     exchange), evaluates each exactly, and applies the best non-tabu move even
#     when it is worse (aspiration on new trial-best cost);
#   - defect-directed voltage moves (vertices not yet covering every orbit);
#   - short trials with restarts, a bandit over base size K, and iterated
#     kicks of the best near miss.
#
# Python side: exact constructions as the start graph (PG(2,q), W(q)), the C
# search with the remaining budget, then greedy slack extension. Every candidate
# passes lib.is_valid; a K_{d,d} fallback is kept.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 4
#define MAXDEG 40
#define NCHOICE 20
#define PEN 1000
#define NCAND 8
#define TENURE 5

typedef struct { int type, e1, e2, val; } Move;

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
static int *nbr;                       /* nbr[l*N + v] */
static int lay[MAXDEG * MAXK];         /* lay[l*K + i] = partner base index on B side */
static int vol[MAXDEG * MAXK];         /* voltage of dart (l, i) */
static int64_t tabu_until[MAXDEG * MAXK];
static int64_t tick;
static uint8_t *cur, *scr, *tmpb;
static uint8_t POP[256];
static uint8_t FULL;
static double TL, tstart;
static int timed_out;
static int64_t LASTCOST;

static int have_best;
static int *bestnbr;
static int best_N, best_K, best_G;

static int have_near;
static int nr_K, nr_M, nr_K2, nr_R, nr_G, nr_N;
static int64_t nr_cost;
static int nr_lay[MAXDEG * MAXK], nr_vol[MAXDEG * MAXK];

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

/* Rewrite all darts of slot e = l*K + i from the current lay/vol values. */
static void set_slot(int e) {
    int l = e / K, i = e % K;
    int p = lay[e], s = vol[e];
    int is = ginv(s);
    int *row = nbr + (size_t)l * N;
    int Ab = i * G, Bb = (K + p) * G;
    for (int g = 0; g < G; g++) {
        row[Ab + g] = Bb + gmul(g, s);
        row[Bb + g] = Ab + gmul(g, is);
    }
}

static void compute_reach(uint8_t *out) {
    memset(out, 0, (size_t)N);
    for (int b = 0; b < 2 * K; b++) out[b * G] = (uint8_t)(1u << b);
    for (int t = 0; t < DIAM; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint8_t x = out[v];
            for (int l = 0; l < DEG; l++) x |= out[nbr[(size_t)l * N + v]];
            tmpb[v] = x;
            if (x != out[v]) changed = 1;
        }
        if (!changed) break;
        memcpy(out, tmpb, (size_t)N);
    }
}

static int64_t unreached(const uint8_t *r) {
    int64_t s = 0;
    for (int v = 0; v < N; v++) s += POP[r[v]];
    return (int64_t)2 * K * N - s;
}

static int dupcount(void) {
    int E = DEG * K, dup = 0;
    for (int e = 0; e < E; e++) {
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

/* Cost of the current lay/vol, reach stored in scr (cur untouched). */
static int64_t eval_cost(void) {
    compute_reach(scr);
    return unreached(scr) + (int64_t)PEN * dupcount();
}

/* Cost of the current lay/vol, reach stored in cur. */
static int64_t full_cost(void) {
    compute_reach(cur);
    return unreached(cur) + (int64_t)PEN * dupcount();
}

/* Self-inverse: applying the move twice restores the state. */
static void apply_move(Move *mv) {
    if (mv->type == 0) {
        int t = vol[mv->e1];
        vol[mv->e1] = mv->val;
        mv->val = t;
        set_slot(mv->e1);
    } else if (mv->type == 1) {
        int t = lay[mv->e1];
        lay[mv->e1] = lay[mv->e2];
        lay[mv->e2] = t;
        set_slot(mv->e1);
        set_slot(mv->e2);
    } else {
        int t = vol[mv->e1];
        vol[mv->e1] = vol[mv->e2];
        vol[mv->e2] = t;
        set_slot(mv->e1);
        set_slot(mv->e2);
    }
}

static int gen_volt(Move *mv, int u) {
    int e;
    if (u >= 0 && rnd01() < 0.7) {
        int blk = u / G;
        int l = rndint(DEG);
        if (blk < K) {
            e = l * K + blk;
        } else {
            int p = blk - K, i = 0;
            while (i < K && lay[l * K + i] != p) i++;
            if (i >= K) return 0;
            e = l * K + i;
        }
    } else {
        e = rndint(DEG * K);
    }
    int nw = rndint(G);
    if (nw == vol[e]) nw = (nw + 1) % G;
    mv->type = 0;
    mv->e1 = e;
    mv->e2 = e;
    mv->val = nw;
    return 1;
}

static int gen_swap(Move *mv) {
    int l = rndint(DEG);
    int i1 = rndint(K);
    int i2 = rndint(K - 1);
    if (i2 >= i1) i2++;
    mv->type = 1;
    mv->e1 = l * K + i1;
    mv->e2 = l * K + i2;
    mv->val = 0;
    return 1;
}

static int gen_exch(Move *mv) {
    int i = rndint(K);
    int l1 = rndint(DEG);
    int l2 = rndint(DEG - 1);
    if (l2 >= l1) l2++;
    int e1 = l1 * K + i, e2 = l2 * K + i;
    if (vol[e1] == vol[e2]) return 0;
    mv->type = 2;
    mv->e1 = e1;
    mv->e2 = e2;
    mv->val = 0;
    return 1;
}

static int gen_move(Move *mv, int u) {
    double r = rnd01();
    if (r < 0.5) return gen_volt(mv, u);
    if (r < 0.75 && K >= 2) return gen_swap(mv);
    if (DEG >= 2) return gen_exch(mv);
    return gen_volt(mv, u);
}

/* Uniform random vertex that does not yet reach every orbit; -1 if none. */
static int pick_defect(void) {
    int u = -1, cnt = 0;
    for (int v = 0; v < N; v++) {
        if (cur[v] != FULL) {
            cnt++;
            if (rndint(cnt) == 0) u = v;
        }
    }
    return u;
}

static int run_trial(int max_steps, int patience, int reinit) {
    int E = DEG * K;
    timed_out = 0;
    if (reinit) {
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
        for (int e = 0; e < E; e++) vol[e] = rndint(G);
    }
    for (int e = 0; e < E; e++) set_slot(e);

    int64_t cost = full_cost();
    int64_t best_cost = cost;
    int last_s = 0;

    for (int s = 0; s < max_steps && cost != 0; s++) {
        if ((s & 7) == 0 && elapsed() > TL) {
            timed_out = 1;
            break;
        }
        if (s - last_s > patience) break;

        int u = (rnd01() < 0.7) ? pick_defect() : -1;
        int have = 0;
        int64_t bc = 0;
        Move bm = {0, 0, 0, 0};
        for (int c = 0; c < NCAND; c++) {
            Move mv = {0, 0, 0, 0};
            if (!gen_move(&mv, u)) continue;
            apply_move(&mv);
            int64_t cst = eval_cost();
            apply_move(&mv);             /* revert */
            int tb = (tabu_until[mv.e1] > tick) ||
                     (mv.type != 0 && tabu_until[mv.e2] > tick);
            if (tb && !(cst < best_cost)) continue;
            if (!have || cst < bc || (cst == bc && rnd01() < 0.5)) {
                have = 1;
                bc = cst;
                bm = mv;
            }
        }
        tick++;
        if (!have) continue;

        apply_move(&bm);
        tabu_until[bm.e1] = tick + TENURE + rndint(3);
        if (bm.type != 0) tabu_until[bm.e2] = tick + TENURE + rndint(3);
        cost = full_cost();
        if (cost < best_cost) {
            best_cost = cost;
            last_s = s;
        }
    }
    LASTCOST = cost;
    return cost == 0;
}

static void save_near(void) {
    have_near = 1;
    nr_K = K;
    nr_M = M;
    nr_K2 = K2;
    nr_R = R;
    nr_G = G;
    nr_N = N;
    nr_cost = LASTCOST;
    memcpy(nr_lay, lay, sizeof(lay));
    memcpy(nr_vol, vol, sizeof(vol));
}

static int pick_k(const double *tr, const double *wn) {
    if (rnd01() < 0.2) return 1 + rndint(MAXK);
    int bk = 1;
    double bv = -1.0;
    for (int k = 1; k <= MAXK; k++) {
        double v = (wn[k] + 1.0) / (tr[k] + 2.0) + 0.02 * rnd01();
        if (v > bv) {
            bv = v;
            bk = k;
        }
    }
    return bk;
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
    for (int x = 0; x < 256; x++) {
        int c = 0;
        for (int y = x; y; y >>= 1) c += y & 1;
        POP[x] = (uint8_t)c;
    }

    if (DEG < 3 || DEG > MAXDEG || DIAM < 3 || CAP < 8) {
        printf("0 0\n");
        return 0;
    }

    AA = malloc(sizeof(int) * (size_t)(CAP + 1));
    BB = malloc(sizeof(int) * (size_t)(CAP + 1));
    nbr = malloc(sizeof(int) * (size_t)DEG * CAP);
    cur = malloc((size_t)CAP);
    scr = malloc((size_t)CAP);
    tmpb = malloc((size_t)CAP);
    bestnbr = malloc(sizeof(int) * (size_t)DEG * CAP);
    if (!AA || !BB || !nbr || !cur || !scr || !tmpb || !bestnbr) {
        printf("0 0\n");
        return 0;
    }

    double tr[MAXK + 1] = {0}, wn[MAXK + 1] = {0};
    long long found = best0;

    while (elapsed() < TL) {
        if (found >= CAP) break;
        int ok = 0, k = 1;

        if (have_near && nr_N > found && rnd01() < 0.5) {
            /* iterated local search: kick the saved near miss and re-anneal */
            K = nr_K;
            M = nr_M;
            K2 = nr_K2;
            R = nr_R;
            G = nr_G;
            N = nr_N;
            k = K;
            FULL = (uint8_t)((1u << (2 * K)) - 1);
            setup_group();
            memcpy(lay, nr_lay, sizeof(lay));
            memcpy(vol, nr_vol, sizeof(vol));
            int kicks = 2 + rndint(4);
            for (int q = 0; q < kicks; q++) {
                int e = rndint(DEG * K);
                vol[e] = rndint(G);
            }
            ok = run_trial(2000, 400, 0);
        } else {
            k = pick_k(tr, wn);
            long long base = found / (2 * k);
            long long span = base / 8 + 1;
            if (span < 2) span = 2;
            long long target = base + 1 + rndint((int)span);
            if (target < 2) target = 2;
            if (!sample_group(target)) continue;
            long long Nn = 2LL * k * G;
            if (Nn <= found || Nn > CAP) continue;

            K = k;
            N = (int)Nn;
            FULL = (uint8_t)((1u << (2 * K)) - 1);
            setup_group();
            tr[k] += 1.0;
            ok = run_trial(2500, 400, 1);
        }

        if (!ok && !timed_out && LASTCOST > 0 && LASTCOST <= (int64_t)N / 2) {
            if (!have_near || LASTCOST < nr_cost || nr_N <= found) save_near();
        }

        if (ok) {
            wn[k] += 1.0;
            found = N;
            memcpy(bestnbr, nbr, sizeof(int) * (size_t)DEG * N);
            best_N = N;
            best_K = K;
            best_G = G;
            have_best = 1;
            have_near = 0;
        }
        if (timed_out) break;
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    int KA = best_K * best_G;
    long long m = (long long)KA * DEG;
    printf("%d %lld\n", best_N, m);
    for (int u = 0; u < KA; u++)
        for (int l = 0; l < DEG; l++)
            printf("%d %d\n", u, bestnbr[(size_t)l * best_N + u]);
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
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
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
                                 timeout=remaining + 20.0)
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
