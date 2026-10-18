import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef unsigned long long u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static long long powmod(long long b, int e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

#define GMAX 400
#define CANDMAX 16384
#define ITERS 12000
#define FAILMAX 3

/* Base graph: B vertices, E edges, regular degree DEG, search depth DEPTH.
   Lift over group G: vertex (u,x) -> u*G+x; base edge (u,v) with voltage s
   gives lift edges (u,x)-(v, x*s). Bipartite and simple if the base is. */
static int B, E, DEG, DEPTH;
static int *eu, *ev, *vo;
static int G, NN;
static int *mul;
static int *nbr, *fillc, *mark, *dd, *qu;
static int stampv = 0;
static int bestNn = 0, bestMm = 0;
static int *bestE = NULL;

/* Group Z_m x| Z_k2 with (a,b)(c,e) = (a + r^b c, b + e); element a*k2+b. */
static int build_group(int m, int k2, int r) {
    int g = m * k2;
    if (g > GMAX) return 0;
    G = g;
    free(mul);
    mul = malloc(sizeof(int) * (size_t)g * (size_t)g);
    int *pw = malloc(sizeof(int) * (size_t)k2);
    pw[0] = 1 % m;
    for (int t = 1; t < k2; t++) pw[t] = (int)((long long)pw[t - 1] * r % m);
    for (int x = 0; x < g; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < g; y++) {
            int c = y / k2, e = y % k2;
            int aa = (int)((a + (long long)pw[b] * c) % m);
            mul[x * g + y] = aa * k2 + (b + e) % k2;
        }
    }
    free(pw);
    return 1;
}

static long long evalcost(void) {
    int N = NN, dg = DEG, g = G;
    memset(fillc, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < E; e++) {
        int u = eu[e], v = ev[e], s = vo[e];
        for (int x = 0; x < g; x++) {
            int a = u * g + x;
            int b = v * g + mul[x * g + s];
            nbr[a * dg + fillc[a]++] = b;
            nbr[b * dg + fillc[b]++] = a;
        }
    }
    long long cost = 0;
    for (int r = 0; r < B; r++) {
        int src = r * g;
        stampv++;
        int head = 0, tail = 0;
        qu[tail++] = src;
        mark[src] = stampv;
        dd[src] = 0;
        while (head < tail) {
            int a = qu[head++];
            if (dd[a] >= DEPTH) continue;
            for (int j = 0; j < dg; j++) {
                int b = nbr[a * dg + j];
                if (mark[b] != stampv) {
                    mark[b] = stampv;
                    dd[b] = dd[a] + 1;
                    qu[tail++] = b;
                }
            }
        }
        cost += (long long)(N - tail);
    }
    return cost;
}

static void record(void) {
    int g = G;
    int n = B * g;
    int m = E * g;
    if (n <= bestNn) return;
    int *ne = malloc(sizeof(int) * 2 * (size_t)m);
    int p = 0;
    for (int e = 0; e < E; e++)
        for (int x = 0; x < g; x++) {
            ne[2 * p] = eu[e] * g + x;
            ne[2 * p + 1] = ev[e] * g + mul[x * g + vo[e]];
            p++;
        }
    free(bestE);
    bestE = ne;
    bestNn = n;
    bestMm = m;
}

/* Simulated annealing on the voltages. Returns 0 when the lift has diameter <= DEPTH. */
static long long search(double tend) {
    long long cur = evalcost();
    if (cur == 0) return 0;
    double T0 = 40.0, T1 = 0.5;
    for (int t = 0; t < ITERS; t++) {
        if ((t & 15) == 0 && now() > tend) break;
        int e = rndi(E);
        int old = vo[e];
        int nw = rndi(G);
        if (nw == old) continue;
        vo[e] = nw;
        long long c2 = evalcost();
        double T = T0 * pow(T1 / T0, (double)t / ITERS);
        if (c2 <= cur || rndu() < exp(-(double)(c2 - cur) / T)) {
            cur = c2;
        } else {
            vo[e] = old;
        }
        if (cur == 0) break;
    }
    return cur;
}

static int cm[CANDMAX], ck[CANDMAX], cr[CANDMAX];

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DEPTH = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int startG = atoi(argv[5]);
    if (DEG < 3 || DEPTH < 1) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || m <= 0) { printf("0 0\n"); return 0; }
    B = n;
    E = m;
    eu = malloc(sizeof(int) * (size_t)E);
    ev = malloc(sizeof(int) * (size_t)E);
    vo = malloc(sizeof(int) * (size_t)E);
    int *deg = calloc((size_t)B, sizeof(int));
    for (int i = 0; i < E; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { printf("0 0\n"); return 0; }
        if (eu[i] < 0 || eu[i] >= B || ev[i] < 0 || ev[i] >= B || eu[i] == ev[i]) {
            printf("0 0\n");
            return 0;
        }
        deg[eu[i]]++;
        deg[ev[i]]++;
    }
    for (int i = 0; i < B; i++)
        if (deg[i] != DEG) { printf("0 0\n"); return 0; }
    free(deg);

    double tend = now() + tl;
    int target = startG < 2 ? 2 : startG;
    int fails = 0;

    while (now() < tend) {
        if (target > GMAX) break;
        int nc = 0;
        for (int k2 = 1; k2 <= target; k2++) {
            if (target % k2) continue;
            int mm = target / k2;
            if (mm < 2) continue;
            for (int r = 1; r < mm; r++) {
                if (gcd_i(r, mm) != 1) continue;
                if (powmod(r, k2, mm) != 1 % mm) continue;
                if (nc < CANDMAX) {
                    cm[nc] = mm;
                    ck[nc] = k2;
                    cr[nc] = r;
                    nc++;
                }
            }
        }
        if (nc == 0) { target++; continue; }
        int pick = rndi(nc);
        if (!build_group(cm[pick], ck[pick], cr[pick])) { target++; continue; }

        NN = B * G;
        free(nbr); free(fillc); free(mark); free(dd); free(qu);
        nbr = malloc(sizeof(int) * (size_t)NN * (size_t)DEG);
        fillc = malloc(sizeof(int) * (size_t)NN);
        mark = calloc((size_t)NN, sizeof(int));
        dd = malloc(sizeof(int) * (size_t)NN);
        qu = malloc(sizeof(int) * (size_t)NN);

        for (int e = 0; e < E; e++) vo[e] = rndi(G);
        long long c = search(tend);
        if (c == 0) {
            record();
            target = G + 1;
            fails = 0;
        } else if (++fails >= FAILMAX) {
            fails = 0;
            if (target > 2) target--;
        }
    }

    if (bestNn == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestNn, bestMm);
    for (int p = 0; p < bestMm; p++)
        printf("%d %d\n", bestE[2 * p], bestE[2 * p + 1]);
    return 0;
}
'''

# Known record orders for the targets (used only to choose the starting group order).
RECORDS = {(6, 5): 684}


def _pg_base(d):
    """Incidence graph of PG(2, d-1) (regular of degree d, diameter 3) if d-1 is a prime power."""
    q = d - 1
    if q < 2 or not lib.is_prime_power(q):
        return None
    return lib.projective_plane_incidence(q)


def build(d, D, seed, time_limit):
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    pg = _pg_base(d)
    if D == 3:
        if pg is not None:
            consider(pg[0], pg[1])
        if d >= 5 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        return best

    # D >= 4: lift the projective-plane incidence graph (a different base from the
    # previous group-lift engine) by groups of growing order, searching voltages.
    if pg is None:
        return best

    B = pg[0]
    budget = max(1.0, time_limit - 10.0)
    target = RECORDS.get((d, D), best_n)
    start_g = (target + 1 + B - 1) // B  # smallest G with B*G > target
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), start_g],
                        stdin_graph=pg, timeout=budget + 5.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
