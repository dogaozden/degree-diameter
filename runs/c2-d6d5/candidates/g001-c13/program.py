import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: bi-Cayley lifts over Z_m x| Z_k2, simulated annealing with
# bitmask distance checks, stagnation restarts and a bandit over base sizes k.
# Reads the start graph on stdin and prints the best valid graph found.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PENALTY 1000
#define KMAX 4

static uint64_t rs = 88172645463325252ULL;
static unsigned char pc8[256];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int powmod_i(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return (int)r;
}

typedef struct {
    int d, D, k, G, N, m, k2;
    int *pw;      /* pw[t] = r^t mod m */
    int *layers;  /* d*k: layers[l*k+i] = B-block paired with A-block i in layer l */
    int *S;       /* d*k: voltage of dart (l,i) */
    int *nbr;     /* d*N: nbr[l*N+v] = neighbour of v in layer l */
    int *bad;     /* N scratch */
    uint32_t *reach, *tmp, *ra, *rb;
} St;

static int st_init(St *s, int d, int D, int k, int m, int k2, int r) {
    s->d = d;
    s->D = D;
    s->k = k;
    s->m = m;
    s->k2 = k2;
    s->G = m * k2;
    s->N = 2 * k * s->G;
    s->pw = malloc(sizeof(int) * (size_t)k2);
    s->pw[0] = 1 % m;
    for (int t = 1; t < k2; t++) s->pw[t] = (int)((long long)s->pw[t - 1] * r % m);
    s->layers = malloc(sizeof(int) * (size_t)(d * k));
    s->S = malloc(sizeof(int) * (size_t)(d * k));
    s->nbr = malloc(sizeof(int) * (size_t)d * (size_t)s->N);
    s->bad = malloc(sizeof(int) * (size_t)s->N);
    s->reach = malloc(sizeof(uint32_t) * (size_t)s->N);
    s->tmp = malloc(sizeof(uint32_t) * (size_t)s->N);
    s->ra = malloc(sizeof(uint32_t) * (size_t)s->N);
    s->rb = malloc(sizeof(uint32_t) * (size_t)s->N);
    return 0;
}

static void st_free(St *s) {
    free(s->pw);
    free(s->layers);
    free(s->S);
    free(s->nbr);
    free(s->bad);
    free(s->reach);
    free(s->tmp);
    free(s->ra);
    free(s->rb);
}

/* Group element x = a*k2 + b, product (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(const St *s, int x, int y) {
    int a = x / s->k2, b = x % s->k2;
    int c = y / s->k2, e = y % s->k2;
    return ((a + s->pw[b] * c) % s->m) * s->k2 + (b + e) % s->k2;
}

/* A-vertex i*G+g joined to B-vertex (k+p)*G + g*sv, for all g, in layer l. */
static void set_dart(St *s, int l, int i, int p, int sv) {
    int G = s->G, N = s->N, k = s->k;
    int *nb = s->nbr + (size_t)l * (size_t)N;
    for (int g = 0; g < G; g++) {
        int h = gmul(s, g, sv);
        int A = i * G + g;
        int B = (k + p) * G + h;
        nb[A] = B;
        nb[B] = A;
    }
}

/* Cost = unreached (representative, vertex) pairs + penalty for duplicate darts.
   Result is written to s->tmp. */
static int evaluate(St *s) {
    int N = s->N, d = s->d, k = s->k, G = s->G;
    uint32_t *r = s->ra, *nw = s->rb;
    memset(r, 0, sizeof(uint32_t) * (size_t)N);
    for (int b = 0; b < 2 * k; b++) r[b * G] |= 1u << b;
    for (int t = 0; t < s->D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = r[v];
            for (int l = 0; l < d; l++) x |= r[s->nbr[(size_t)l * N + v]];
            nw[v] = x;
            if (x != r[v]) changed = 1;
        }
        uint32_t *tp = r;
        r = nw;
        nw = tp;
        if (!changed) break;
    }
    memcpy(s->tmp, r, sizeof(uint32_t) * (size_t)N);
    long long total = 0;
    for (int v = 0; v < N; v++) total += pc8[s->tmp[v]];
    long long unreached = 2LL * k * N - total;
    int dup = 0;
    int M = d * k;
    for (int x = 0; x < M; x++) {
        int ix = x % k, px = s->layers[x], sx = s->S[x];
        for (int y = ix; y < x; y += k) {
            if (s->layers[y] == px && s->S[y] == sx) {
                dup++;
                break;
            }
        }
    }
    return (int)unreached + PENALTY * dup;
}

static void accept_state(St *s) {
    uint32_t *t = s->reach;
    s->reach = s->tmp;
    s->tmp = t;
}

static int run_search(St *s, int iters, int patience, double deadline) {
    int d = s->d, k = s->k, G = s->G, N = s->N;
    uint32_t full = (1u << (2 * k)) - 1;
    int *perm = malloc(sizeof(int) * (size_t)k);
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < k; i++) s->layers[l * k + i] = perm[i];
    }
    free(perm);
    for (int x = 0; x < d * k; x++) s->S[x] = rndint(G);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++)
            set_dart(s, l, i, s->layers[l * k + i], s->S[l * k + i]);

    int cost = evaluate(s);
    accept_state(s);
    double c0 = cost > 1 ? (double)cost : 1.0;
    int best_cost = cost, last_improve = 0;

    for (int t = 0; t < iters; t++) {
        if (cost == 0) break;
        if (t - last_improve > patience) break;
        if ((t & 127) == 0 && now_sec() > deadline) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (k >= 2 && rnd01() < 0.25) {
            /* Layer-swap move: exchange the B-targets of two A-blocks in one layer. */
            int l = rndint(d);
            int i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int x1 = l * k + i1, x2 = l * k + i2;
            int t1 = s->layers[x1];
            s->layers[x1] = s->layers[x2];
            s->layers[x2] = t1;
            set_dart(s, l, i1, s->layers[x1], s->S[x1]);
            set_dart(s, l, i2, s->layers[x2], s->S[x2]);
            int c2 = evaluate(s);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                accept_state(s);
                if (cost < best_cost) {
                    best_cost = cost;
                    last_improve = t;
                }
            } else {
                t1 = s->layers[x1];
                s->layers[x1] = s->layers[x2];
                s->layers[x2] = t1;
                set_dart(s, l, i1, s->layers[x1], s->S[x1]);
                set_dart(s, l, i2, s->layers[x2], s->S[x2]);
            }
            continue;
        }

        /* Voltage move: defect-targeted with probability 0.4, otherwise uniform. */
        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            int nbad = 0;
            for (int v = 0; v < N; v++)
                if (s->reach[v] != full) s->bad[nbad++] = v;
            if (nbad > 0) {
                int u = s->bad[rndint(nbad)];
                int block = u / G;
                l = rndint(d);
                if (block < k) {
                    i = block;
                } else {
                    for (int q = 0; q < k; q++) {
                        if (s->layers[l * k + q] == block - k) {
                            i = q;
                            break;
                        }
                    }
                }
            }
        }
        if (i < 0) {
            l = rndint(d);
            i = rndint(k);
        }
        int x = l * k + i;
        int old = s->S[x];
        int nv = rndint(G);
        if (nv == old) continue;
        s->S[x] = nv;
        set_dart(s, l, i, s->layers[x], nv);
        int c2 = evaluate(s);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            accept_state(s);
            if (cost < best_cost) {
                best_cost = cost;
                last_improve = t;
            }
        } else {
            s->S[x] = old;
            set_dart(s, l, i, s->layers[x], old);
        }
    }
    return cost == 0;
}

static const int SK[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit\n");
        return 1;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);

    rs ^= seed * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (rs == 0) rs = 1;
    for (int x = 0; x < 256; x++)
        pc8[x] = (unsigned char)((x & 1) + (x >> 1 ? pc8[x >> 1] : 0));

    double deadline = now_sec() + tl;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        n = 0;
        m = 0;
    }
    if (n < 0 || m < 0) {
        n = 0;
        m = 0;
    }
    int *best_e = malloc(sizeof(int) * 2 * (size_t)(m > 0 ? m : 1));
    int nread = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        best_e[2 * nread] = u;
        best_e[2 * nread + 1] = v;
        nread++;
    }
    int best_n = n, best_m = nread;

    if (d >= 2 && D >= 2) {
        int trials[KMAX + 1], wins[KMAX + 1];
        for (int q = 0; q <= KMAX; q++) {
            trials[q] = 0;
            wins[q] = 0;
        }
        while (now_sec() < deadline) {
            int k;
            if (rnd01() < 0.2) {
                k = 1 + rndint(KMAX);
            } else {
                double bs = -1.0;
                k = 1;
                for (int kk = 1; kk <= KMAX; kk++) {
                    double sc = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rnd01();
                    if (sc > bs) {
                        bs = sc;
                        k = kk;
                    }
                }
            }
            int base = best_n / (2 * k);
            int span = base / 8 + 1;
            if (span < 2) span = 2;
            int target = base + 1 + rndint(span);
            if (target < 2) target = 2;

            int mm = 0, k2 = 1, r = 1, found = 0;
            for (int tries = 0; tries < 200 && !found; tries++) {
                k2 = SK[rndint(20)];
                mm = (target + k2 - 1) / k2;
                if (mm < 2) mm = 2;
                if (k2 == 1) {
                    r = 1 % mm;
                } else if (k2 == 2 && rnd01() < 0.3) {
                    r = mm - 1;
                    if (gcd_i(r, mm) != 1 || powmod_i(r, 2, mm) != 1 % mm) continue;
                } else {
                    r = -1;
                    for (int q = 0; q < 60; q++) {
                        int c = mm > 2 ? 2 + rndint(mm - 2) : 1;
                        if (gcd_i(c, mm) == 1 && powmod_i(c, k2, mm) == 1 % mm) {
                            r = c;
                            break;
                        }
                    }
                    if (r < 0) continue;
                }
                found = 1;
            }
            if (!found) continue;

            int G = mm * k2;
            if (2LL * k * G <= best_n) continue;

            trials[k]++;
            St s;
            memset(&s, 0, sizeof(s));
            st_init(&s, d, D, k, mm, k2, r);
            int ok = run_search(&s, 30000, 4000, deadline);
            if (ok) {
                wins[k]++;
                int N = s.N;
                int cnt = k * G * d;
                int *ne = malloc(sizeof(int) * 2 * (size_t)cnt);
                int q = 0;
                for (int u = 0; u < k * G; u++) {
                    for (int l = 0; l < d; l++) {
                        ne[2 * q] = u;
                        ne[2 * q + 1] = s.nbr[(size_t)l * N + u];
                        q++;
                    }
                }
                free(best_e);
                best_e = ne;
                best_n = N;
                best_m = cnt;
            }
            st_free(&s);
        }
    }

    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
    free(best_e);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    final_deadline = start + max(1.0, time_limit - 3.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < final_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search in C, starting from the best construction found so far.
    if d >= 2 and D >= 2:
        c_budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, c_budget],
                             stdin_graph=best, timeout=time_limit - 3.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
