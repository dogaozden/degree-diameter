import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lifts over Z_m x| Z_k2, searched by simulated annealing.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h, G = m*k2.
# Layer l pairs A_i with B_{layer[l][i]} through voltage s: A_{i,g} ~ B_{j,g*s}.
# Each layer is a permutation, so every vertex has degree d exactly.
#
# Cost = number of unreached (block representative, vertex) pairs
#        + PEN * number of duplicate darts.
# Moves: layer swap, voltage move (defect-targeted with prob 0.4), restarts.
# The driver keeps a bandit over k and grows the target order past the best
# found so far. Python validates the output with lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000LL
#define MAXK 4
#define ITERS 20000
#define PATIENCE 2500

static uint64_t rs = 1;

static uint64_t nextr(void) {
    uint64_t z = (rs += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint32_t rnd(uint32_t n) {
    return n ? (uint32_t)(nextr() % n) : 0u;
}

static double rndu(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint8_t POP[256];

static void init_pop(void) {
    for (int i = 0; i < 256; i++) {
        int c = 0;
        for (int b = 0; b < 8; b++) c += (i >> b) & 1;
        POP[i] = (uint8_t)c;
    }
}

typedef struct {
    int d, D, k, G, m, k2, N;
    long long *pw;   /* pw[t] = r^t mod m */
    int *layer;      /* layer[l*k+i] = B-block index j */
    int *S;          /* voltage of dart (l,i) */
    int *nbr;        /* nbr[l*N+v] = neighbour of v in layer l */
} St;

static long long gcdll(long long a, long long b) {
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* (a,b)(c,e) = (a + r^b c, b + e), element code a*k2 + b. */
static int gmul(const St *c, int x, int y) {
    int k2 = c->k2;
    long long m = c->m;
    int a = x / k2, b = x % k2, cc = y / k2, e = y % k2;
    long long aa = ((long long)a + c->pw[b] * (long long)cc) % m;
    return (int)aa * k2 + (b + e) % k2;
}

/* Inverse of (a,b) is (-r^(-b) a, -b). */
static int ginv(const St *c, int x) {
    int k2 = c->k2;
    long long m = c->m;
    int a = x / k2, b = x % k2;
    int nb = (k2 - b) % k2;
    long long na = (m - (c->pw[nb] * (long long)a) % m) % m;
    return (int)na * k2 + nb;
}

static void set_dart(St *c, int l, int i) {
    int k = c->k, G = c->G, N = c->N;
    int j = c->layer[l * k + i], s = c->S[l * k + i];
    int si = ginv(c, s);
    int *nb = c->nbr + (size_t)l * (size_t)N;
    for (int g = 0; g < G; g++) nb[i * G + g] = (k + j) * G + gmul(c, g, s);
    for (int h = 0; h < G; h++) nb[(k + j) * G + h] = i * G + gmul(c, h, si);
}

static int dupcount(const St *c) {
    int k = c->k, n = c->d * c->k, cnt = 0;
    for (int a = 0; a < n; a++) {
        int ia = a % k;
        for (int b = 0; b < a; b++) {
            if (b % k == ia && c->layer[b] == c->layer[a] && c->S[b] == c->S[a]) cnt++;
        }
    }
    return cnt;
}

/* Writes, per vertex, the bitmask of representative blocks within distance D.
   Returns the number of unreached (representative, vertex) pairs. */
static long long evaluate(const St *c, uint32_t *out, uint32_t *scr) {
    int N = c->N, k = c->k, G = c->G, d = c->d, D = c->D;
    memset(out, 0, sizeof(uint32_t) * (size_t)N);
    for (int b = 0; b < 2 * k; b++) out[b * G] = 1u << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = out[v];
            for (int l = 0; l < d; l++) x |= out[c->nbr[(size_t)l * N + v]];
            scr[v] = x;
            changed |= (x != out[v]);
        }
        memcpy(out, scr, sizeof(uint32_t) * (size_t)N);
        if (!changed) break;
    }
    long long unr = 0;
    int full = 2 * k;
    for (int v = 0; v < N; v++) unr += full - POP[out[v] & 255u];
    return unr;
}

static int anneal(St *c, int iters, int patience, double deadline,
                  uint32_t *cur, uint32_t *cand, uint32_t *scr) {
    int d = c->d, k = c->k, G = c->G, N = c->N;
    uint32_t full = (1u << (2 * k)) - 1u;
    long long cost = evaluate(c, cur, scr) + PEN * (long long)dupcount(c);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long long best = cost;
    int last = 0;

    for (int t = 0; t < iters; t++) {
        if (cost == 0) return 1;
        if ((t & 31) == 0 && now() > deadline) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (k >= 2 && rndu() < 0.25) {
            /* Layer-swap move. */
            int l = (int)rnd((uint32_t)d);
            int i1 = (int)rnd((uint32_t)k);
            int i2 = (int)rnd((uint32_t)(k - 1));
            if (i2 >= i1) i2++;
            int *lay = c->layer + l * k;
            int tmp = lay[i1]; lay[i1] = lay[i2]; lay[i2] = tmp;
            set_dart(c, l, i1);
            set_dart(c, l, i2);
            long long c2 = evaluate(c, cand, scr) + PEN * (long long)dupcount(c);
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                uint32_t *tp = cur; cur = cand; cand = tp;
                if (cost < best) { best = cost; last = t; }
            } else {
                tmp = lay[i1]; lay[i1] = lay[i2]; lay[i2] = tmp;
                set_dart(c, l, i1);
                set_dart(c, l, i2);
            }
            continue;
        }

        /* Voltage move: defect-targeted with probability 0.4, else uniform. */
        int l = -1, i = -1;
        long long u = -1;
        if (rndu() < 0.4) {
            int cnt = 0;
            for (int v = 0; v < N; v++) {
                if (cur[v] != full) {
                    cnt++;
                    if (rnd((uint32_t)cnt) == 0) u = v;
                }
            }
        }
        if (u >= 0) {
            int block = (int)(u / G);
            l = (int)rnd((uint32_t)d);
            if (block < k) {
                i = block;
            } else {
                int j = block - k;
                for (int ii = 0; ii < k; ii++) {
                    if (c->layer[l * k + ii] == j) { i = ii; break; }
                }
            }
        }
        if (i < 0) {
            l = (int)rnd((uint32_t)d);
            i = (int)rnd((uint32_t)k);
        }
        int idx = l * k + i;
        int old = c->S[idx];
        int nw = (int)rnd((uint32_t)G);
        if (nw == old) continue;
        c->S[idx] = nw;
        set_dart(c, l, i);
        long long c2 = evaluate(c, cand, scr) + PEN * (long long)dupcount(c);
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            uint32_t *tp = cur; cur = cand; cand = tp;
            if (cost < best) { best = cost; last = t; }
        } else {
            c->S[idx] = old;
            set_dart(c, l, i);
        }
    }
    return cost == 0;
}

/* Random group Z_m x| Z_k2 with m*k2 >= target. r = 1 is always valid (direct product). */
static void sample_group(int target, int *m_out, int *k2_out, long long *r_out) {
    static const int K2S[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    int k2 = K2S[rnd(20)];
    int m = (target + k2 - 1) / k2;
    if (m < 2) m = 2;
    long long r = 1;
    if (k2 >= 2 && rndu() > 0.15) {
        for (int t = 0; t < 60; t++) {
            long long cnd = 1 + (long long)rnd((uint32_t)(m - 1));
            if (gcdll(cnd, m) == 1 && powmod(cnd, k2, m) == 1 % m) {
                r = cnd;
                break;
            }
        }
    }
    *m_out = m;
    *k2_out = k2;
    *r_out = r;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time [min_n]\n");
        return 1;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int best_n = argc > 5 ? atoi(argv[5]) : 0;

    init_pop();
    rs = seed * 0x2545F4914F6CDD1DULL + 0x1234567ULL;
    double deadline = now() + tl;

    int found = 0;
    int best_m = 0;
    int *best_e = NULL;

    if (d < 1 || D < 1) {
        printf("0 0\n");
        return 0;
    }

    long trials[MAXK + 1] = {0};
    long wins[MAXK + 1] = {0};

    while (now() < deadline) {
        int k;
        if (rndu() < 0.2) {
            k = 1 + (int)rnd(MAXK);
        } else {
            double bv = -1.0;
            k = 1;
            for (int kk = 1; kk <= MAXK; kk++) {
                double v = ((double)wins[kk] + 1.0) / ((double)trials[kk] + 2.0) + 0.02 * rndu();
                if (v > bv) { bv = v; k = kk; }
            }
        }
        int base = best_n / (2 * k);
        int target = base + 1 + (int)rnd((uint32_t)(base / 8 + 2));
        if (target < 2) target = 2;
        int m, k2;
        long long r;
        sample_group(target, &m, &k2, &r);
        int G = m * k2;
        int N = 2 * k * G;
        if (N <= best_n) continue;
        trials[k]++;

        St c;
        c.d = d; c.D = D; c.k = k; c.G = G; c.m = m; c.k2 = k2; c.N = N;
        c.pw = malloc(sizeof(long long) * (size_t)k2);
        c.layer = malloc(sizeof(int) * (size_t)(d * k));
        c.S = malloc(sizeof(int) * (size_t)(d * k));
        c.nbr = malloc(sizeof(int) * (size_t)d * (size_t)N);
        uint32_t *cur = malloc(sizeof(uint32_t) * (size_t)N);
        uint32_t *cand = malloc(sizeof(uint32_t) * (size_t)N);
        uint32_t *scr = malloc(sizeof(uint32_t) * (size_t)N);
        if (!c.pw || !c.layer || !c.S || !c.nbr || !cur || !cand || !scr) {
            free(c.pw); free(c.layer); free(c.S); free(c.nbr);
            free(cur); free(cand); free(scr);
            break;
        }

        c.pw[0] = 1 % m;
        for (int t = 1; t < k2; t++) c.pw[t] = c.pw[t - 1] * r % m;

        int arr[MAXK];
        for (int l = 0; l < d; l++) {
            for (int i = 0; i < k; i++) arr[i] = i;
            for (int i = k - 1; i > 0; i--) {
                int j = (int)rnd((uint32_t)(i + 1));
                int tmp = arr[i]; arr[i] = arr[j]; arr[j] = tmp;
            }
            for (int i = 0; i < k; i++) {
                c.layer[l * k + i] = arr[i];
                c.S[l * k + i] = (int)rnd((uint32_t)G);
            }
        }
        for (int l = 0; l < d; l++)
            for (int i = 0; i < k; i++)
                set_dart(&c, l, i);

        int ok = anneal(&c, ITERS, PATIENCE, deadline, cur, cand, scr);
        if (ok) {
            wins[k]++;
            int E = k * G * d;
            int *ne = malloc(sizeof(int) * 2 * (size_t)E);
            if (ne) {
                int idx = 0;
                for (int u = 0; u < k * G; u++)
                    for (int l = 0; l < d; l++) {
                        ne[2 * idx] = u;
                        ne[2 * idx + 1] = c.nbr[(size_t)l * N + u];
                        idx++;
                    }
                free(best_e);
                best_e = ne;
                best_m = E;
                best_n = N;
                found = 1;
            }
        }

        free(c.pw); free(c.layer); free(c.S); free(c.nbr);
        free(cur); free(cand); free(scr);
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int e = 0; e < best_m; e++)
        printf("%d %d\n", best_e[2 * e], best_e[2 * e + 1]);
    free(best_e);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions (exact or structured baselines).
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 6.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
        # Araujo-Pardo & Lopez record for d = q + 2 (q prime power), diameter 3.
        if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search in C (bi-Cayley lifts with annealing and a bandit over k).
    remaining = deadline - time.monotonic()
    if remaining > 2.0:
        seed_int = int(seed) if isinstance(seed, int) else 1
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, seed_int, round(remaining, 2), best_n],
                stdin_graph=None,
                timeout=max(2.0, time_limit - (time.monotonic() - start) - 2.0),
            )
            n, e = lib.parse_graph_text(out)
            if n > best_n:
                consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
