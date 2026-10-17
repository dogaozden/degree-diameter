"""Bi-Cayley lift search, now run in C.

Change: the simulated-annealing search over Z_m x| Z_k2 bi-Cayley lifts, and the
bandit over base sizes k, moved from numpy into a C engine. The C side does the whole
restart loop inside one process, so each move costs roughly one BFS pass over the
lift instead of many numpy calls. Python keeps the exact constructions, the
slack extension and the validation.
"""
import itertools
import random
import time

import lib


C_SOURCE = r"""
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define PEN 1000LL

static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static uint8_t pc8[256];
static double t_end = 1.0;

static int time_up(void) { return (double)clock() / CLOCKS_PER_SEC >= t_end; }

typedef struct { int m, k2, r; int *pw; } Group;

static long long pmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long long ggcd(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static void group_init(Group *g, int m, int k2, int r) {
    g->m = m;
    g->k2 = k2;
    g->r = r;
    g->pw = (int *)malloc(sizeof(int) * (size_t)k2);
    for (int t = 0; t < k2; t++) g->pw[t] = (int)pmod(r, t, m);
}

/* (a,b)(c,e) = (a + r^b c, b + e), element coded as a*k2 + b. */
static int gmul(const Group *g, int x, int y) {
    int a = x / g->k2, b = x % g->k2;
    int c = y / g->k2, e = y % g->k2;
    long long t = (long long)a + (long long)g->pw[b] * (long long)c;
    return (int)(t % g->m) * g->k2 + (b + e) % g->k2;
}

static int sample_group(int target, Group *g) {
    static const int K2[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8,
                               9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    for (int att = 0; att < 200; att++) {
        int k2 = K2[rndint(20)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rnd01() < 0.3) {
            r = m - 1;
            if (ggcd(r, m) != 1 || pmod(r, 2, m) != 1 % m) continue;
        } else {
            r = -1;
            for (int a = 0; a < 60; a++) {
                int c = m > 2 ? 2 + rndint(m - 2) : 1;
                if (ggcd(c, m) == 1 && pmod(c, k2, m) == 1 % m) {
                    r = c;
                    break;
                }
            }
            if (r < 0) continue;
        }
        group_init(g, m, k2, r);
        return 1;
    }
    return 0;
}

typedef struct {
    int d, D, k, G, N;
    int *lay;   /* lay[l*k+i] = B-block that A-block i meets in layer l (a permutation) */
    int *S;     /* S[l*k+i] = voltage */
    int *nbr;   /* nbr[l*N+v] = neighbour of v in layer l */
    uint8_t *reach, *cand, *tmp;
    Group gp;
} Ctx;

/* A_{i,g} ~ B_{j, g*s}, with A block i = [i*G, (i+1)*G) and B block j = [(k+j)*G, ...). */
static void build_nbr(Ctx *c) {
    const int d = c->d, k = c->k, G = c->G, N = c->N;
    for (int l = 0; l < d; l++) {
        int *row = c->nbr + (size_t)l * N;
        for (int i = 0; i < k; i++) {
            int j = c->lay[l * k + i], s = c->S[l * k + i];
            for (int g = 0; g < G; g++) {
                int h = gmul(&c->gp, g, s);
                row[i * G + g] = (k + j) * G + h;
                row[(k + j) * G + h] = i * G + g;
            }
        }
    }
}

static int dupcount(const Ctx *c) {
    const int k = c->k, tot = c->d * c->k;
    int dup = 0;
    for (int a = 0; a < tot; a++) {
        int ia = a % k, ja = c->lay[a], sa = c->S[a];
        for (int b = 0; b < a; b++) {
            if (c->lay[b] == ja && c->S[b] == sa && b % k == ia) {
                dup++;
                break;
            }
        }
    }
    return dup;
}

/* Writes the reach bitmasks into out and returns the cost. */
static long long compute(Ctx *c, uint8_t *out) {
    const int d = c->d, k = c->k, G = c->G, N = c->N, D = c->D;
    build_nbr(c);
    memset(out, 0, (size_t)N);
    for (int b = 0; b < 2 * k; b++) out[b * G] = (uint8_t)(1u << b);
    for (int t = 0; t < D; t++) {
        memcpy(c->tmp, out, (size_t)N);
        for (int l = 0; l < d; l++) {
            const int *row = c->nbr + (size_t)l * N;
            for (int v = 0; v < N; v++) c->tmp[v] |= out[row[v]];
        }
        if (memcmp(c->tmp, out, (size_t)N) == 0) break;
        memcpy(out, c->tmp, (size_t)N);
    }
    long long unr = 2LL * k * N;
    for (int v = 0; v < N; v++) unr -= pc8[out[v]];
    return unr + PEN * (long long)dupcount(c);
}

static int search(Ctx *c, int iters, int patience) {
    const int d = c->d, k = c->k, G = c->G, N = c->N;
    const uint8_t full = (uint8_t)((1u << (2 * k)) - 1u);
    uint8_t *cur = c->reach, *nxt = c->cand;

    for (int l = 0; l < d; l++) {
        int *p = c->lay + (size_t)l * k;
        for (int i = 0; i < k; i++) p[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1), t = p[i];
            p[i] = p[j];
            p[j] = t;
        }
        for (int i = 0; i < k; i++) c->S[l * k + i] = rndint(G);
    }

    long long cost = compute(c, cur);
    const double c0 = (double)(cost > 1 ? cost : 1);
    long long best = cost;
    int last = 0;

    for (int t = 0; t < iters; t++) {
        if (cost == 0 || time_up()) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (k >= 2 && rnd01() < 0.25) {
            /* Layer-swap move: exchange the B-targets of two A-blocks in one layer. */
            int l = rndint(d);
            int i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int *lp = c->lay + (size_t)l * k;
            int tt = lp[i1];
            lp[i1] = lp[i2];
            lp[i2] = tt;
            long long c2 = compute(c, nxt);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                uint8_t *sw = cur;
                cur = nxt;
                nxt = sw;
                if (cost < best) {
                    best = cost;
                    last = t;
                }
            } else {
                tt = lp[i1];
                lp[i1] = lp[i2];
                lp[i2] = tt;
            }
            continue;
        }

        /* Voltage move: defect-targeted with probability 0.4, otherwise uniform. */
        int l = -1, i = -1, picked = 0;
        if (rnd01() < 0.4) {
            int nb = 0;
            for (int v = 0; v < N; v++)
                if (cur[v] != full) nb++;
            if (nb > 0) {
                int pick = rndint(nb), u = -1;
                for (int v = 0; v < N; v++) {
                    if (cur[v] != full) {
                        if (pick == 0) {
                            u = v;
                            break;
                        }
                        pick--;
                    }
                }
                int block = u / G;
                l = rndint(d);
                if (block < k) {
                    i = block;
                } else {
                    for (int ii = 0; ii < k; ii++) {
                        if (c->lay[l * k + ii] == block - k) {
                            i = ii;
                            break;
                        }
                    }
                }
                picked = 1;
            }
        }
        if (!picked) {
            l = rndint(d);
            i = rndint(k);
        }
        int idx = l * k + i;
        int old = c->S[idx];
        int nw = rndint(G);
        if (nw == old) continue;
        c->S[idx] = nw;
        long long c2 = compute(c, nxt);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            uint8_t *sw = cur;
            cur = nxt;
            nxt = sw;
            if (cost < best) {
                best = cost;
                last = t;
            }
        } else {
            c->S[idx] = old;
        }
    }

    c->reach = cur;
    c->cand = nxt;
    if (cost != 0) return 0;
    build_nbr(c);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed budget_seconds [min_n]\n");
        return 1;
    }
    int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    t_end = atof(argv[4]);
    int best_n = argc > 5 ? atoi(argv[5]) : 0;

    rs ^= seed * 0x2545F4914F6CDD1DULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 10; w++) rnd64();
    for (int v = 0; v < 256; v++) {
        int c = 0;
        for (int b = 0; b < 8; b++) c += (v >> b) & 1;
        pc8[v] = (uint8_t)c;
    }

    if (d < 1 || D < 1) {
        printf("0 0\n");
        return 0;
    }

    int have = 0, best_m = 0;
    int *beu = NULL, *bev = NULL;
    int trials[5] = {0, 0, 0, 0, 0}, wins[5] = {0, 0, 0, 0, 0};

    while (!time_up()) {
        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndint(4);
        } else {
            double bv = -1.0;
            k = 1;
            for (int kk = 1; kk <= 4; kk++) {
                double v = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rnd01();
                if (v > bv) {
                    bv = v;
                    k = kk;
                }
            }
        }
        int base = best_n / (2 * k);
        int span = base / 8 + 1;
        if (span < 2) span = 2;
        int target = base + 1 + rndint(span);
        if (target < 2) target = 2;

        Ctx c;
        memset(&c, 0, sizeof c);
        if (!sample_group(target, &c.gp)) continue;
        int G = c.gp.m * c.gp.k2;
        if (2 * k * G <= best_n) {
            free(c.gp.pw);
            continue;
        }
        trials[k]++;
        c.d = d;
        c.D = D;
        c.k = k;
        c.G = G;
        c.N = 2 * k * G;
        c.lay = (int *)malloc(sizeof(int) * (size_t)d * k);
        c.S = (int *)malloc(sizeof(int) * (size_t)d * k);
        c.nbr = (int *)malloc(sizeof(int) * (size_t)d * c.N);
        c.reach = (uint8_t *)malloc((size_t)c.N);
        c.cand = (uint8_t *)malloc((size_t)c.N);
        c.tmp = (uint8_t *)malloc((size_t)c.N);

        if (search(&c, 4000, 1200)) {
            wins[k]++;
            if (c.N > best_n) {
                best_n = c.N;
                int cnt = k * G * d;
                int *nu = (int *)malloc(sizeof(int) * (size_t)cnt);
                int *nv = (int *)malloc(sizeof(int) * (size_t)cnt);
                int q = 0;
                for (int u = 0; u < k * G; u++) {
                    for (int l = 0; l < d; l++) {
                        nu[q] = u;
                        nv[q] = c.nbr[(size_t)l * c.N + u];
                        q++;
                    }
                }
                free(beu);
                free(bev);
                beu = nu;
                bev = nv;
                best_m = cnt;
                have = 1;
            }
        }

        free(c.lay);
        free(c.S);
        free(c.nbr);
        free(c.reach);
        free(c.cand);
        free(c.tmp);
        free(c.gp.pw);
    }

    if (!have) {
        printf("0 0\n");
    } else {
        printf("%d %d\n", best_n, best_m);
        for (int q = 0; q < best_m; q++) printf("%d %d\n", beu[q], bev[q]);
    }
    free(beu);
    free(bev);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
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
# Build: exact constructions, then the C bi-Cayley search, then slack extension.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 6.0))
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

    # Exact constructions: return immediately (calibration-style cases).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search in C: restarts, bandit over base sizes and annealing all run there.
    c_budget = max(1.0, min(0.80 * time_limit, time_limit - 10.0) - (time.monotonic() - start))
    try:
        out = lib.run_c(
            C_SOURCE,
            [d, D, abs(int(seed)), f"{c_budget:.2f}", best_n],
            timeout=max(2.0, time_limit - (time.monotonic() - start) - 3.0),
        )
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except (RuntimeError, ValueError, OSError):
        pass  # keep the exact or Haar fallback

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
