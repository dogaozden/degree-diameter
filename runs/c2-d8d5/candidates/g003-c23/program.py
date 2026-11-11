import itertools
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PENALTY 1000L
#define MAXK 4
#define MAXK2 40

static uint64_t rs = 0x2545F4914F6CDD1DULL;

static uint64_t rnd64(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_sec(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int popc32(uint32_t x) {
    x = x - ((x >> 1) & 0x55555555u);
    x = (x & 0x33333333u) + ((x >> 2) & 0x33333333u);
    x = (x + (x >> 4)) & 0x0F0F0F0Fu;
    return (int)((x * 0x01010101u) >> 24);
}

/* Group Z_m x| Z_k2, element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e). */
typedef struct {
    long m, k2, G, r;
    long pw[MAXK2];
} Grp;

static long gmul(const Grp *g, long x, long y) {
    long a = x / g->k2, b = x % g->k2;
    long c = y / g->k2, e = y % g->k2;
    long aa = (a + g->pw[b] * c) % g->m;
    long bb = (b + e) % g->k2;
    return aa * g->k2 + bb;
}

static int sample_group(long target, Grp *g) {
    static const int K2[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    for (int tries = 0; tries < 200; tries++) {
        long k2 = K2[rndint(20)];
        long m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        long r = -1;
        if (k2 == 1) {
            r = 1 % m;
        } else if (k2 == 2 && rnd01() < 0.3) {
            r = m - 1;  /* dihedral type, (m-1)^2 = 1 mod m */
        } else if (m > 2) {
            for (int t = 0; t < 60; t++) {
                long c = 2 + rndint((int)(m - 2));
                if (gcd_l(c, m) == 1 && powmod_l(c, k2, m) == 1 % m) { r = c; break; }
            }
        }
        if (r < 0) continue;
        g->m = m;
        g->k2 = k2;
        g->G = m * k2;
        g->r = r;
        g->pw[0] = 1 % m;
        for (long t = 1; t < k2; t++) g->pw[t] = g->pw[t - 1] * r % m;
        return 1;
    }
    return 0;
}

/* Bi-Cayley lift state. A_{i,g} = i*G+g, B_{j,h} = (k+j)*G+h.
   Layer l: A-block i goes to B-block layers[l][i] with voltage S[l][i]:
   A_{i,g} ~ B_{j,g*s}. */
typedef struct {
    int d, D, k;
    long G, N;
    Grp grp;
    int *layers;
    long *S;
    int *nbr;   /* d * N */
} St;

static void set_dart(St *s, int l, int i) {
    long k = s->k, G = s->G, N = s->N;
    int j = s->layers[(long)l * k + i];
    long sv = s->S[(long)l * k + i];
    int *nb = s->nbr + (long)l * N;
    for (long g = 0; g < G; g++) {
        long u = (long)i * G + g;
        long w = (k + j) * G + gmul(&s->grp, g, sv);
        nb[u] = (int)w;
        nb[w] = (int)u;
    }
}

static long dup_count(const St *s) {
    long c = 0;
    int k = s->k, d = s->d;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (s->layers[l * k + i] == s->layers[l2 * k + i] &&
                    s->S[l * k + i] == s->S[l2 * k + i])
                    c++;
    return c;
}

/* R receives the final reach masks, Q is scratch. Returns number of unreached pairs. */
static long compute_reach(const St *s, uint32_t *R, uint32_t *Q) {
    long N = s->N, G = s->G;
    int k = s->k, d = s->d;
    for (long v = 0; v < N; v++) R[v] = 0;
    for (int b = 0; b < 2 * k; b++) R[(long)b * G] = 1u << b;
    for (int t = 0; t < s->D; t++) {
        int changed = 0;
        for (long v = 0; v < N; v++) {
            uint32_t x = R[v];
            for (int l = 0; l < d; l++) x |= R[s->nbr[(long)l * N + v]];
            Q[v] = x;
            if (x != R[v]) changed = 1;
        }
        if (!changed) break;
        memcpy(R, Q, (size_t)N * sizeof(uint32_t));
    }
    long pop = 0;
    for (long v = 0; v < N; v++) pop += popc32(R[v]);
    return 2L * k * N - pop;
}

static int anneal(St *s, double deadline, long iters, long patience) {
    int d = s->d, k = s->k;
    long G = s->G, N = s->N;
    uint32_t full = (1u << (2 * k)) - 1u;

    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) s->layers[l * k + i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int sw = s->layers[l * k + i];
            s->layers[l * k + i] = s->layers[l * k + j];
            s->layers[l * k + j] = sw;
        }
        for (int i = 0; i < k; i++) s->S[l * k + i] = rndint((int)G);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) set_dart(s, l, i);

    uint32_t *cur = malloc((size_t)N * sizeof(uint32_t));
    uint32_t *alt = malloc((size_t)N * sizeof(uint32_t));
    uint32_t *scr = malloc((size_t)N * sizeof(uint32_t));
    long *bad = malloc((size_t)N * sizeof(long));
    if (!cur || !alt || !scr || !bad) {
        free(cur); free(alt); free(scr); free(bad);
        return 0;
    }

    long cost = compute_reach(s, cur, scr) + PENALTY * dup_count(s);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best_cost = cost, last = 0;

    for (long t = 0; t < iters; t++) {
        if (cost == 0) break;
        if ((t & 31) == 0 && now_sec() > deadline) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (k >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(k);
            int i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int sw = s->layers[l * k + i1];
            s->layers[l * k + i1] = s->layers[l * k + i2];
            s->layers[l * k + i2] = sw;
            set_dart(s, l, i1);
            set_dart(s, l, i2);
            long c2 = compute_reach(s, alt, scr) + PENALTY * dup_count(s);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                uint32_t *p = cur; cur = alt; alt = p;
                if (cost < best_cost) { best_cost = cost; last = t; }
            } else {
                sw = s->layers[l * k + i1];
                s->layers[l * k + i1] = s->layers[l * k + i2];
                s->layers[l * k + i2] = sw;
                set_dart(s, l, i1);
                set_dart(s, l, i2);
            }
            continue;
        }

        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            long nb = 0;
            for (long v = 0; v < N; v++)
                if (cur[v] != full) bad[nb++] = v;
            if (nb > 0) {
                long u = bad[rndint((int)nb)];
                long block = u / G;
                l = rndint(d);
                if (block < k) {
                    i = (int)block;
                } else {
                    for (int ii = 0; ii < k; ii++)
                        if (s->layers[l * k + ii] == block - k) { i = ii; break; }
                }
            }
        }
        if (l < 0 || i < 0) {
            l = rndint(d);
            i = rndint(k);
        }

        long old = s->S[l * k + i];
        long nw = rndint((int)G);
        if (nw == old) continue;
        s->S[l * k + i] = nw;
        set_dart(s, l, i);
        long c2 = compute_reach(s, alt, scr) + PENALTY * dup_count(s);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            uint32_t *p = cur; cur = alt; alt = p;
            if (cost < best_cost) { best_cost = cost; last = t; }
        } else {
            s->S[l * k + i] = old;
            set_dart(s, l, i);
        }
    }

    free(cur); free(alt); free(scr); free(bad);
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: d D seed time [best_n]\n");
        return 1;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    long bestN = argc > 5 ? atol(argv[5]) : 0;

    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (d < 2 || D < 1) {
        printf("0 0\n");
        return 0;
    }

    double start = now_sec();
    double deadline = start + tl;

    int *bestE = NULL;
    long bestM = 0, bestNN = 0;
    double wins[MAXK + 1], trials[MAXK + 1];
    for (int i = 0; i <= MAXK; i++) { wins[i] = 0; trials[i] = 0; }

    while (now_sec() < deadline) {
        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bs = -1.0;
            k = 1;
            for (int kk = 1; kk <= MAXK; kk++) {
                double sc = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rnd01();
                if (sc > bs) { bs = sc; k = kk; }
            }
        }

        long base = bestN / (2L * k);
        long span = base / 8 + 1;
        if (span < 2) span = 2;
        long target = base + 1 + rndint((int)span);
        if (target < 2) target = 2;

        Grp g;
        if (!sample_group(target, &g)) continue;
        long N = 2L * k * g.G;
        if (N <= bestN) continue;

        trials[k] += 1.0;

        St st;
        st.d = d;
        st.D = D;
        st.k = k;
        st.G = g.G;
        st.N = N;
        st.grp = g;
        st.layers = malloc(sizeof(int) * (size_t)d * k);
        st.S = malloc(sizeof(long) * (size_t)d * k);
        st.nbr = malloc(sizeof(int) * (size_t)d * (size_t)N);
        if (!st.layers || !st.S || !st.nbr) {
            free(st.layers); free(st.S); free(st.nbr);
            break;
        }

        int ok = anneal(&st, deadline, 150000L, 8000L);
        if (ok) {
            wins[k] += 1.0;
            long M = (long)k * st.G * d;
            if (N > bestN) {
                int *E = malloc(sizeof(int) * 2 * (size_t)M);
                if (E) {
                    long idx = 0;
                    long A = (long)k * st.G;
                    for (long u = 0; u < A; u++)
                        for (int l = 0; l < d; l++) {
                            E[idx++] = (int)u;
                            E[idx++] = st.nbr[(long)l * N + u];
                        }
                    free(bestE);
                    bestE = E;
                    bestM = M;
                    bestNN = N;
                    bestN = N;
                }
            }
        }
        free(st.layers);
        free(st.S);
        free(st.nbr);
    }

    if (bestM == 0 || bestE == NULL) {
        printf("0 0\n");
    } else {
        printf("%ld %ld\n", bestNN, bestM);
        for (long e = 0; e < bestM; e++)
            printf("%d %d\n", bestE[2 * e], bestE[2 * e + 1]);
    }
    free(bestE);
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
# Main build: exact constructions first, then the C bi-Cayley lift annealer
# (which now runs many restarts over groups Z_m x| Z_k2 at native speed),
# then slack extension.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
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

    # Native-speed search for bi-Cayley lifts that beat the current best order.
    remaining = deadline - time.monotonic()
    if d >= 2 and remaining > 0.5:
        try:
            out = lib.run_c(C_SOURCE,
                            [d, D, seed % (2 ** 31), round(remaining, 2), best_n],
                            stdin_graph=None, timeout=remaining + 2.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
