"""Combined program: a C-native bi-Cayley lift search over semidirect products Z_m x| Z_k2
(many base blocks, non-cyclic groups allowed, simulated annealing on voltages and layer
permutations), with a Python construction fallback. Every returned graph is checked with
lib.is_valid, and K_{d,d} (or a classical construction) is the fallback.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley lift search over semidirect products G = Z_M x| Z_K2 (element (a,b) = a*K2+b,
 * (a,b)(c,e) = (a + r^b c, b+e), r^K2 = 1 mod M).
 *
 * Base graph: k blocks A_0..A_{k-1} and k blocks B_0..B_{k-1}, each block a copy of G.
 * Layer l is a perfect matching of blocks: A_i -> B_{P[l][i]} with voltage S[l][i], so
 * A_{i,g} ~ B_{P[l][i], g*S[l][i]}. Every vertex gets degree d, the graph is bipartite,
 * and it is simple when no two layers share (block, voltage) for the same A block.
 *
 * G acts regularly on every block by left multiplication, so it is enough to BFS from the
 * 2k block identities; the cost is the number of vertices left unreached within distance D.
 * Simulated annealing drives this cost to 0.
 *
 * Usage: prog d D seed time_limit   (stdin ignored). stdout: "n m" + edges of the best graph.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXK 8
#define MAXN 32768
#define MAXR 64

typedef struct {
    int k, K2, M, G, N;
    int RP[MAXR];              /* RP[b] = r^b mod M */
    int P[MAXD][MAXK];         /* P[l][i]: B block hit by A block i in layer l */
    int Pi[MAXD][MAXK];        /* Pi[l][j]: A block hit by B block j in layer l */
    int S[MAXD][MAXK];         /* voltage of dart (l, i) */
    int Si[MAXD][MAXK];        /* inverse voltage */
} Lift;

static int d, D;
static uint64_t rs = 88172645463325252ULL;
static int nbr[MAXN][MAXD];
static int vis[MAXN];
static int qu[MAXN];
static int stamp = 0;
static Lift cur, best, tmp;
static double t_end;

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static inline int gmul(const Lift *L, int x, int y) {
    int K2 = L->K2, M = L->M;
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    int aa = (int)(((long long)a + (long long)L->RP[b] * c) % M);
    int bb = (b + e) % K2;
    return aa * K2 + bb;
}

static inline int ginv(const Lift *L, int x) {
    int K2 = L->K2, M = L->M;
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    int t = (int)((long long)L->RP[nb] * a % M);
    int aa = (M - t) % M;
    return aa * K2 + nb;
}

static int setup_group(Lift *L, int k, int K2, int M, int r) {
    L->k = k;
    L->K2 = K2;
    L->M = M;
    L->G = M * K2;
    L->N = 2 * k * L->G;
    long long p = 1 % M;
    for (int b = 0; b < K2; b++) {
        L->RP[b] = (int)p;
        p = p * r % M;
    }
    return 0;
}

/* Uniformly random r in [1, M) with gcd(r, M) = 1 and r^K2 = 1 mod M; -1 if none. */
static int pick_r(int K2, int M) {
    int chosen = -1, cnt = 0;
    for (int r = 1; r < M; r++) {
        if (gcd_i(r, M) != 1) continue;
        long long p = 1 % M;
        for (int b = 0; b < K2; b++) p = p * r % M;
        if (p != 1 % M) continue;
        cnt++;
        if (rndint(cnt) == 0) chosen = r;
    }
    return chosen;
}

static void build_nbr(const Lift *L) {
    int k = L->k, G = L->G;
    for (int i = 0; i < k; i++)
        for (int g = 0; g < G; g++)
            for (int l = 0; l < d; l++)
                nbr[i * G + g][l] = (k + L->P[l][i]) * G + gmul(L, g, L->S[l][i]);
    for (int j = 0; j < k; j++)
        for (int h = 0; h < G; h++)
            for (int l = 0; l < d; l++) {
                int i = L->Pi[l][j];
                nbr[(k + j) * G + h][l] = i * G + gmul(L, h, L->Si[l][i]);
            }
}

/* Number of vertices not reached within distance D, summed over the 2k block identities. */
static long evaluate(const Lift *L) {
    build_nbr(L);
    int N = L->N, B = 2 * L->k, G = L->G;
    long cost = 0;
    for (int rep = 0; rep < B; rep++) {
        int src = rep * G;
        stamp++;
        int head = 0, tail = 1;
        qu[0] = src;
        vis[src] = stamp;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int v = qu[head++];
                for (int l = 0; l < d; l++) {
                    int u = nbr[v][l];
                    if (vis[u] != stamp) {
                        vis[u] = stamp;
                        qu[tail++] = u;
                    }
                }
            }
        }
        cost += N - tail;
    }
    return cost;
}

/* True if block i has no two layers using the same (target block, voltage). */
static int dup_ok(const Lift *L, int i) {
    for (int l = 0; l < d; l++)
        for (int l2 = 0; l2 < l; l2++)
            if (L->P[l][i] == L->P[l2][i] && L->S[l][i] == L->S[l2][i]) return 0;
    return 1;
}

static int init_random(Lift *L) {
    int k = L->k, G = L->G;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < k; i++) {
            L->P[l][i] = perm[i];
            L->Pi[l][perm[i]] = i;
        }
    }
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++) {
            int ok = 0;
            for (int att = 0; att < 1000 && !ok; att++) {
                int s = rndint(G);
                L->S[l][i] = s;
                ok = 1;
                for (int l2 = 0; l2 < l; l2++)
                    if (L->P[l2][i] == L->P[l][i] && L->S[l2][i] == s) {
                        ok = 0;
                        break;
                    }
            }
            if (!ok) return 0;
            L->Si[l][i] = ginv(L, L->S[l][i]);
        }
    return 1;
}

/* Simulated annealing on voltages and layer permutations. Returns the final cost (0 = valid). */
static long anneal(Lift *L, double deadline, long maxit, long patience) {
    long cost = evaluate(L);
    long c0 = cost > 0 ? cost : 1;
    long bestc = cost, last = 0;
    for (long t = 0; t < maxit && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && now() > deadline) break;
        double frac = (double)t / (double)maxit;
        double T = 0.3 + 0.03 * (double)c0 * (1.0 - frac);
        tmp = *L;
        if (tmp.k >= 2 && rnd01() < 0.3) {
            int l = rndint(d);
            int i1 = rndint(tmp.k);
            int i2 = rndint(tmp.k - 1);
            if (i2 >= i1) i2++;
            int t1 = tmp.P[l][i1];
            tmp.P[l][i1] = tmp.P[l][i2];
            tmp.P[l][i2] = t1;
            tmp.Pi[l][tmp.P[l][i1]] = i1;
            tmp.Pi[l][tmp.P[l][i2]] = i2;
            if (!dup_ok(&tmp, i1) || !dup_ok(&tmp, i2)) continue;
        } else {
            int l = rndint(d);
            int i = rndint(tmp.k);
            int s = rndint(tmp.G);
            if (s == tmp.S[l][i]) continue;
            tmp.S[l][i] = s;
            tmp.Si[l][i] = ginv(&tmp, s);
            if (!dup_ok(&tmp, i)) continue;
        }
        long c2 = evaluate(&tmp);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            *L = tmp;
            cost = c2;
            if (cost < bestc) {
                bestc = cost;
                last = t;
            }
        }
    }
    return cost;
}

static int pick_k(const int *trials, const int *wins) {
    int bestk = 1;
    double bs = -1.0;
    for (int k = 1; k <= MAXK; k++) {
        double s = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.15 * rnd01();
        if (s > bs) {
            bs = s;
            bestk = k;
        }
    }
    return bestk;
}

static const int K2_CHOICES[] = {1, 1, 1, 2, 2, 2, 3, 3, 4, 4, 5, 6, 6, 8, 8, 9, 10, 12, 12, 16, 18, 20, 24};

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    /* Fallback: K_{d,d} as the Haar lift of Z_d with all d voltages. */
    memset(&best, 0, sizeof best);
    setup_group(&best, 1, 1, d, 1);
    for (int l = 0; l < d; l++) {
        best.P[l][0] = 0;
        best.Pi[l][0] = 0;
        best.S[l][0] = l;
        best.Si[l][0] = ginv(&best, l);
    }

    int trials[MAXK + 1] = {0};
    int wins[MAXK + 1] = {0};
    double goal = best.N * 1.02;
    int nK2 = (int)(sizeof(K2_CHOICES) / sizeof(int));

    while (now() < t_end - 0.5) {
        int k = pick_k(trials, wins);
        long target = (long)ceil(goal / (2.0 * k));
        if (target < 2) target = 2;
        int K2 = K2_CHOICES[rndint(nK2)];
        int M = (int)((target + K2 - 1) / K2) + rndint(3);
        if (M < 2) M = 2;
        int r = -1;
        for (int tries = 0; tries < 20; tries++) {
            r = pick_r(K2, M);
            if (r >= 0) break;
            M++;
        }
        if (r < 0) {
            goal = best.N * 1.01 > goal * 0.995 ? best.N * 1.01 : goal * 0.995;
            continue;
        }
        long G = (long)M * K2;
        if (2L * k * G > MAXN) {
            goal = best.N * 1.01 > goal * 0.995 ? best.N * 1.01 : goal * 0.995;
            continue;
        }
        setup_group(&cur, k, K2, M, r);
        if (cur.N <= best.N) {
            goal = best.N * 1.02;
            continue;
        }
        if (!init_random(&cur)) continue;
        trials[k]++;

        double remain = t_end - now();
        double budget = remain / 6.0;
        if (budget < 1.0) budget = 1.0;
        if (budget > 6.0) budget = 6.0;
        double dl = now() + budget;
        if (dl > t_end) dl = t_end;

        long c = anneal(&cur, dl, 400000, 4000);
        if (c == 0) {
            wins[k]++;
            best = cur;
            goal = best.N * 1.03;
        } else {
            double relaxed = goal * 0.995;
            double floor_goal = best.N * 1.01;
            goal = relaxed > floor_goal ? relaxed : floor_goal;
        }
    }

    build_nbr(&best);
    int A = best.k * best.G;
    printf("%d %ld\n", best.N, (long)A * d);
    for (int u = 0; u < A; u++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", u, nbr[u][l]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Classical constructions (exact or record-level for small cases).
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


def _cycle(D):
    """Cycle of length 2D: bipartite, 2-regular, diameter D (optimal for d = 2)."""
    n = 2 * D
    return n, [(i, (i + 1) % n) for i in range(n)]


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # D = 2: K_{d,d} is Moore-optimal.
    if D == 2:
        return best

    # d = 2: the cycle of length 2D is optimal.
    if d == 2:
        try:
            consider(*_cycle(D))
        except Exception:
            pass
        return best

    # Exact or record constructions for D = 3, 4.
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main search: C-native bi-Cayley lift annealing over semidirect products.
    remaining = final - time.monotonic() - 1.0
    if remaining > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=None, timeout=remaining + 10)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
