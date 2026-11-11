import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lifts over Z_m x| Z_k2, searched by simulated annealing.
#
# Vertices: A_{i,g} = i*G + g (i < K), B_{p,h} = (K+p)*G + h, with G = m*k2.
# Layer l is a permutation sig_l of the K blocks, plus a voltage s_l,i.
# Edge: A_{i,g} ~ B_{sig_l(i), g*s_l,i}. Every vertex gets degree DEG.
#
# Left multiplication by a group element is an automorphism, so the diameter
# only needs BFS from the 2K block representatives. Cost = unreached
# (representative, vertex) pairs + PEN * duplicate (i, p, s) triples.
#
# New in this version: "sampled best-response voltage move". For a random
# (layer, block) pair, several candidate voltages are scored and the best one
# is proposed to the annealer. The bandit over K also tracks success counts.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#include <limits.h>

#define MAXD 32
#define MAXK 8
#define KMAX 6
#define PEN 1000LL

static int DEG = 0, DIAM = 0, K = 1, M = 2, K2 = 1, G = 2, N = 0;
static int PW[64];
static int *ADJ = NULL, *DIST = NULL, *QUE = NULL;
static int capN = 0;
static int SIG[MAXD * MAXK], SV[MAXD * MAXK];
static uint64_t RS = 88172645463325252ULL;

static int bestN = 0, bK = 0, bG = 0, bM = 0, bK2 = 0;
static int bPW[64], bSIG[MAXD * MAXK], bSV[MAXD * MAXK];

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rnd(void) {
    RS ^= RS >> 12;
    RS ^= RS << 25;
    RS ^= RS >> 27;
    return RS * 2685821657736338717ULL;
}

static int irand(int n) { return (int)(rnd() % (uint64_t)n); }

static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

/* Multiplication in Z_M x| Z_K2: (a,b)(c,e) = (a + r^b c, b + e). */
static inline int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long ra = ((long long)a + (long long)PW[b] * (long long)c) % M;
    int rb = (b + e) % K2;
    return (int)ra * K2 + rb;
}

static void setup_group(long long target) {
    static const int K2S[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    long long m = target, k2 = 1, r = 1;
    int ok = 0;
    for (int tries = 0; tries < 200 && !ok; tries++) {
        k2 = K2S[irand(20)];
        m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        r = 1;
        if (k2 == 1) { ok = 1; break; }
        if (k2 == 2 && m > 2 && urand() < 0.3) { r = m - 1; ok = 1; break; }
        if (m > 2) {
            for (int q = 0; q < 60; q++) {
                long long c = 2 + irand((int)(m - 2));
                if (gcdll(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; ok = 1; break; }
            }
        }
        if (ok) break;
    }
    if (!ok) { k2 = 1; m = target < 2 ? 2 : target; r = 1; }
    M = (int)m;
    K2 = (int)k2;
    G = M * K2;
    for (int b = 0; b < K2; b++) PW[b] = (int)powmod(r, b, m);
}

static void ensure_cap(int need) {
    if (need <= capN) return;
    int *a = realloc(ADJ, sizeof(int) * (size_t)need * (size_t)DEG);
    int *b = realloc(DIST, sizeof(int) * (size_t)need);
    int *c = realloc(QUE, sizeof(int) * (size_t)need);
    if (!a || !b || !c) exit(2);
    ADJ = a;
    DIST = b;
    QUE = c;
    capN = need;
}

/* Write layer l, A-block i (and the B-block it hits) into the adjacency table. */
static void set_block(int l, int i) {
    int p = SIG[l * K + i], s = SV[l * K + i];
    int abase = i * G, bbase = (K + p) * G;
    for (int g = 0; g < G; g++) {
        int a = abase + g;
        int b = bbase + gmul(g, s);
        ADJ[a * DEG + l] = b;
        ADJ[b * DEG + l] = a;
    }
}

static long long dupcount(void) {
    long long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < DEG; l1++)
            for (int l2 = l1 + 1; l2 < DEG; l2++)
                if (SIG[l1 * K + i] == SIG[l2 * K + i] && SV[l1 * K + i] == SV[l2 * K + i]) c++;
    return c;
}

static long long evalcost(void) {
    long long tot = 0;
    for (int b = 0; b < 2 * K; b++) {
        int src = b * G;
        for (int v = 0; v < N; v++) DIST[v] = -1;
        int h = 0, t = 0;
        QUE[t++] = src;
        DIST[src] = 0;
        while (h < t) {
            int u = QUE[h++];
            int du = DIST[u];
            if (du >= DIAM) continue;
            const int *nb = ADJ + (size_t)u * DEG;
            for (int j = 0; j < DEG; j++) {
                int w = nb[j];
                if (DIST[w] < 0) {
                    DIST[w] = du + 1;
                    QUE[t++] = w;
                }
            }
        }
        tot += N - t;
    }
    return tot + PEN * dupcount();
}

static void init_state(void) {
    for (int l = 0; l < DEG; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = irand(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            SIG[l * K + i] = perm[i];
            SV[l * K + i] = irand(G);
        }
    }
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++) set_block(l, i);
}

static long long anneal(long long iters, long long patience, double tend) {
    long long cur = evalcost();
    long long c0 = cur > 0 ? cur : 1;
    double T0 = 0.05 * (double)c0 + 2.0;
    long long last = 0, bestc = cur;
    for (long long t = 0; t < iters && cur > 0; t++) {
        if ((t & 7) == 0 && now_s() > tend) break;
        if (t - last > patience) break;
        double T = T0 * (1.0 - (double)t / (double)iters) + 0.3;

        if (K >= 2 && urand() < 0.2) {
            /* Layer swap: exchange the B-targets of two A-blocks in one layer. */
            int l = irand(DEG), i1 = irand(K), i2 = irand(K);
            if (i1 == i2) continue;
            int tmp = SIG[l * K + i1];
            SIG[l * K + i1] = SIG[l * K + i2];
            SIG[l * K + i2] = tmp;
            set_block(l, i1);
            set_block(l, i2);
            long long c2 = evalcost();
            if (c2 <= cur || urand() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                tmp = SIG[l * K + i1];
                SIG[l * K + i1] = SIG[l * K + i2];
                SIG[l * K + i2] = tmp;
                set_block(l, i1);
                set_block(l, i2);
            }
        } else {
            /* Sampled best-response voltage move. */
            int l = irand(DEG), i = irand(K);
            int idx = l * K + i;
            int old = SV[idx];
            int nsamp = (urand() < 0.5) ? 3 : 1;
            int bestS = -1;
            long long bestC = LLONG_MAX;
            for (int q = 0; q < nsamp; q++) {
                int ns = irand(G);
                if (ns == old) continue;
                SV[idx] = ns;
                set_block(l, i);
                long long c2 = evalcost();
                if (c2 < bestC) {
                    bestC = c2;
                    bestS = ns;
                }
            }
            if (bestS < 0) {
                SV[idx] = old;
                set_block(l, i);
                continue;
            }
            if (bestC <= cur || urand() < exp(-(double)(bestC - cur) / T)) {
                SV[idx] = bestS;
                set_block(l, i);
                cur = bestC;
            } else {
                SV[idx] = old;
                set_block(l, i);
            }
        }
        if (cur < bestc) {
            bestc = cur;
            last = t;
        }
    }
    return cur;
}

static void emit_best(void) {
    if (bestN == 0) {
        printf("0 0\n");
        return;
    }
    K = bK;
    G = bG;
    M = bM;
    K2 = bK2;
    memcpy(PW, bPW, sizeof PW);
    memcpy(SIG, bSIG, sizeof SIG);
    memcpy(SV, bSV, sizeof SV);
    printf("%d %d\n", bestN, K * G * DEG);
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) {
            int p = SIG[l * K + i], s = SV[l * K + i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + p) * G + gmul(g, s);
                printf("%d %d\n", a, b);
            }
        }
    }
}

int main(int argc, char **argv) {
    double t0 = now_s();
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    double tend = t0 + budget;

    {
        char buf[4096];
        while (fread(buf, 1, sizeof buf, stdin) > 0) {
        }
    }

    DEG = d;
    if (DEG < 1 || DEG > MAXD || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    RS = 0x9E3779B97F4A7C15ULL ^ (seed * 0x2545F4914F6CDD1DULL + 1ULL);
    if (RS == 0) RS = 1;
    for (int w = 0; w < 20; w++) rnd();

    long long trials[MAXK + 1], wins[MAXK + 1];
    for (int k = 0; k <= MAXK; k++) {
        trials[k] = 0;
        wins[k] = 0;
    }

    while (now_s() < tend) {
        int k;
        if (urand() < 0.2) {
            k = 1 + irand(KMAX);
        } else {
            double bestv = -1.0;
            k = 1;
            for (int kk = 1; kk <= KMAX; kk++) {
                double v = ((double)wins[kk] + 1.0) / ((double)trials[kk] + 2.0) + 0.05 * urand();
                if (v > bestv) {
                    bestv = v;
                    k = kk;
                }
            }
        }
        long long base = bestN > 0 ? bestN / (2 * k) : DEG;
        long long off = irand((int)(base / 8 + 2));
        long long target = base + 1 + off;
        if (target < 2) target = 2;

        setup_group(target);
        long long nn = 2LL * k * G;
        if (nn <= bestN) continue;

        K = k;
        N = (int)nn;
        ensure_cap(N);
        trials[k]++;
        init_state();
        long long fc = anneal(4000, 1200, tend);
        if (fc == 0) {
            wins[k]++;
            bestN = N;
            bK = K;
            bG = G;
            bM = M;
            bK2 = K2;
            memcpy(bPW, PW, sizeof PW);
            memcpy(bSIG, SIG, sizeof SIG);
            memcpy(bSV, SV, sizeof SV);
        }
    }

    emit_best();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python: exact constructions and glue.
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is the Moore graph for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bi-Cayley annealing in C, using the remaining time budget.
    elapsed = time.monotonic() - start
    budget = min(0.86 * time_limit, time_limit - 6.0) - elapsed
    if budget >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=None, timeout=budget + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except (RuntimeError, ValueError, OSError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
