"""Bi-Cayley seed plus pair-insertion annealing for bipartite d-regular graphs.

Stage 1 (C): scan bi-Cayley graphs over metacyclic groups Z_m x| Z_k, as in the parent.
This gives a d-regular bipartite graph of order 2n with diameter <= D.

Stage 2 (C, new): pair-insertion growth with annealing. From a valid d-regular bipartite
graph on V vertices, pick d edges (a_i, b_i) forming a matching. Delete them, add a new
A-vertex x adjacent to every b_i and a new B-vertex y adjacent to every a_i. Degrees stay
exactly d and bipartiteness is kept. The result has V+2 vertices, but its diameter is
usually too large. Annealing on edge switches (a,b),(c,e) -> (a,e),(c,b) then drives the
number of ordered pairs at distance > D to zero. The cost is computed exactly with
64-bit bitset BFS balls. Bad vertices are targeted with high probability. Each success
grows the graph by 2 vertices, and the best valid graph is printed.

Python keeps the best of the known start and the C result, and checks everything with
lib.is_valid.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1024
#define MAXV 2100
#define MAXW 33
#define MAXDEG 16
#define MAXGRP 4096
#define MAXE (MAXV * MAXDEG / 2 + 64)

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Largest possible order of a bipartite graph with max degree d and diameter D. */
static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* ---------------------------------------------------------- groups Z_m x| Z_k */

typedef struct { int m, k, r; } Grp;
static Grp groups[MAXGRP];
static int ngroups;

static void enum_groups(int n) {
    ngroups = 0;
    for (int pass = 0; pass < 2; pass++) {
        for (int m = 1; m <= n; m++) {
            if (n % m) continue;
            int k = n / m;
            if (m == 1) {
                if (pass == 1 && ngroups < MAXGRP) {
                    groups[ngroups].m = 1;
                    groups[ngroups].k = k;
                    groups[ngroups].r = 0;
                    ngroups++;
                }
                continue;
            }
            for (int r = 1; r < m; r++) {
                if (gcd(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
                int nonab = (r != 1);
                if ((pass == 0) != nonab) continue;
                if (ngroups < MAXGRP) {
                    groups[ngroups].m = m;
                    groups[ngroups].k = k;
                    groups[ngroups].r = r;
                    ngroups++;
                }
            }
        }
    }
}

static int MT[MAXG * MAXG];
static int INV[MAXG];
static int NN;

static void build_group(Grp G) {
    int n = G.m * G.k;
    NN = n;
    static int rp[MAXG];
    rp[0] = 1 % G.m;
    for (int b = 1; b < G.k; b++) rp[b] = (int)((long)rp[b - 1] * G.r % G.m);
    for (int x = 0; x < n; x++) {
        int a = x / G.k, b = x % G.k;
        for (int y = 0; y < n; y++) {
            int c = y / G.k, e = y % G.k;
            MT[x * n + y] = (int)(((long)a + (long)rp[b] * c) % G.m) * G.k + (b + e) % G.k;
        }
    }
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (MT[x * n + y] == 0) { INV[x] = y; break; }
}

/* ---------------------------------------------------------- bi-Cayley check */

static int dist_[MAXV], queue_[MAXV];

/* A_x = x, B_h = NN + h, A_x ~ B_{x s}. Returns 1 iff all vertices are within D of src. */
static int reach_all(const int *S, int src) {
    int n = NN, V2 = 2 * n;
    for (int i = 0; i < V2; i++) dist_[i] = -1;
    int head = 0, tail = 0;
    dist_[src] = 0;
    queue_[tail++] = src;
    while (head < tail) {
        int v = queue_[head++];
        int dv = dist_[v];
        if (dv >= D) continue;
        if (v < n) {
            for (int i = 0; i < d; i++) {
                int u = n + MT[v * n + S[i]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        } else {
            int h = v - n;
            for (int i = 0; i < d; i++) {
                int u = MT[h * n + INV[S[i]]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        }
    }
    return tail == V2;
}

static void pick_set(int n, int *S) {
    S[0] = 0;
    for (int i = 1; i < d; i++) {
        for (;;) {
            int x = 1 + rndint(n - 1);
            int dup = 0;
            for (int j = 0; j < i; j++)
                if (S[j] == x) { dup = 1; break; }
            if (!dup) { S[i] = x; break; }
        }
    }
}

static int bestN = 0;
static Grp bestG;
static int bestS[MAXDEG];

static int search_n(int n, double until) {
    enum_groups(n);
    if (ngroups == 0) return 0;
    int S[MAXDEG];
    while (now() < until) {
        for (int gi = 0; gi < ngroups; gi++) {
            if (now() >= until) break;
            build_group(groups[gi]);
            for (int t = 0; t < 200; t++) {
                pick_set(n, S);
                if (reach_all(S, 0) && reach_all(S, n)) {
                    bestN = n;
                    bestG = groups[gi];
                    memcpy(bestS, S, sizeof(int) * (size_t)d);
                    return 1;
                }
            }
        }
    }
    return 0;
}

/* ---------------------------------------------------------- current graph */

static int V, M;
static int side[MAXV];
static int nb[MAXV * MAXDEG];
static int EU[MAXE], EV[MAXE];   /* edge k joins EU[k] (side 0) and EV[k] (side 1) */
static int degc[MAXV];

typedef struct {
    int V, M;
    int side[MAXV];
    int nb[MAXV * MAXDEG];
    int EU[MAXE];
    int EV[MAXE];
} State;
static State bs;   /* best valid state */

static void save_state(State *s) {
    s->V = V;
    s->M = M;
    memcpy(s->side, side, sizeof(side));
    memcpy(s->nb, nb, sizeof(nb));
    memcpy(s->EU, EU, sizeof(int) * (size_t)M);
    memcpy(s->EV, EV, sizeof(int) * (size_t)M);
}

static void load_state(const State *s) {
    V = s->V;
    M = s->M;
    memcpy(side, s->side, sizeof(side));
    memcpy(nb, s->nb, sizeof(nb));
    memcpy(EU, s->EU, sizeof(int) * (size_t)M);
    memcpy(EV, s->EV, sizeof(int) * (size_t)M);
}

static void add_base(int u, int w) {
    nb[u * MAXDEG + degc[u]++] = w;
    nb[w * MAXDEG + degc[w]++] = u;
    EU[M] = u;
    EV[M] = w;
    M++;
}

static void build_from_bicayley(void) {
    int n = bestN;
    build_group(bestG);
    V = 2 * n;
    M = 0;
    for (int v = 0; v < V; v++) { side[v] = (v < n) ? 0 : 1; degc[v] = 0; }
    for (int x = 0; x < n; x++)
        for (int i = 0; i < d; i++) {
            int y = MT[x * n + bestS[i]];
            add_base(x, n + y);
        }
}

static void build_complete(void) {
    V = 2 * d;
    M = 0;
    for (int v = 0; v < V; v++) { side[v] = (v < d) ? 0 : 1; degc[v] = 0; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_base(a, d + b);
}

static int adjacent(int u, int v) {
    int *p = nb + u * MAXDEG;
    for (int i = 0; i < d; i++) if (p[i] == v) return 1;
    return 0;
}

static void nb_replace(int v, int oldu, int newu) {
    int *p = nb + v * MAXDEG;
    for (int i = 0; i < d; i++) if (p[i] == oldu) { p[i] = newu; return; }
}

/* Edge switch: (a,b),(c,e) -> (a,e),(c,b). Calling it again with the same i, j undoes it. */
static void do_switch(int i, int j) {
    int a = EU[i], b = EV[i], c = EU[j], e = EV[j];
    nb_replace(a, b, e);
    nb_replace(b, a, c);
    nb_replace(c, e, b);
    nb_replace(e, c, a);
    EV[i] = e;
    EV[j] = b;
}

static int valid_switch(int i, int j) {
    if (i == j) return 0;
    int a = EU[i], b = EV[i], c = EU[j], e = EV[j];
    if (a == c || b == e) return 0;
    if (adjacent(a, e) || adjacent(c, b)) return 0;
    return 1;
}

static int find_edge(int v, int u) {
    int a = (side[v] == 0) ? v : u;
    int b = (side[v] == 0) ? u : v;
    for (int k = 0; k < M; k++)
        if (EU[k] == a && EV[k] == b) return k;
    return -1;
}

/* ---------------------------------------------------------- bitset cost */

static uint64_t BA[MAXV * MAXW], BB[MAXV * MAXW];
static int bad[MAXV], badc[MAXV];

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of ordered pairs at distance > D. Per-vertex counts go to bad[]. */
static long cost(void) {
    int W = (V + 63) >> 6;
    uint64_t *cur = BA, *nxt = BB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)V * (size_t)W);
    for (int v = 0; v < V; v++) cur[v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int s = 0; s < D; s++) {
        for (int v = 0; v < V; v++) {
            const int *p = nb + v * MAXDEG;
            for (int k = 0; k < W; k++) {
                uint64_t x = cur[v * W + k];
                for (int i = 0; i < d; i++) x |= cur[p[i] * W + k];
                nxt[v * W + k] = x;
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long tot = 0;
    for (int v = 0; v < V; v++) {
        int c = 0;
        for (int k = 0; k < W; k++) c += popc64(cur[v * W + k]);
        bad[v] = V - c;
        tot += V - c;
    }
    return tot;
}

/* ---------------------------------------------------------- growth move */

/* Insert two vertices x (side 0) and y (side 1) by removing d matching edges (a_i,b_i)
 * and adding x-b_i, y-a_i. Degrees stay d and the graph stays bipartite. */
static int insert_pair(void) {
    if (V + 2 > MAXV - 2) return 0;
    int ch[MAXDEG], cnt = 0;
    long tries = 0;
    while (cnt < d) {
        if (++tries > 200000) return 0;
        int k = rndint(M);
        int a = EU[k], b = EV[k], ok = 1;
        for (int t = 0; t < cnt; t++)
            if (EU[ch[t]] == a || EV[ch[t]] == b) { ok = 0; break; }
        if (ok) ch[cnt++] = k;
    }
    int x = V, y = V + 1;
    side[x] = 0;
    side[y] = 1;
    for (int t = 0; t < d; t++) {
        int k = ch[t];
        int a = EU[k], b = EV[k];
        EV[k] = y;                    /* edge k becomes a-y */
        nb_replace(a, b, y);
        nb_replace(b, a, x);          /* b now joins x instead of a */
        nb[x * MAXDEG + t] = b;
        nb[y * MAXDEG + t] = a;
        EU[M] = x;
        EV[M] = b;
        M++;
    }
    V += 2;
    return 1;
}

/* Simulated annealing on switch moves. Returns 1 when the cost reaches 0 (state kept). */
static int anneal(long iters, double until) {
    long c = cost();
    memcpy(badc, bad, sizeof(int) * (size_t)V);
    if (c == 0) return 1;
    for (long it = 0; it < iters; it++) {
        if ((it & 127) == 0 && now() > until) break;
        double T = 2.5 * (1.0 - (double)it / (double)iters) + 0.25;
        int i = -1, j;
        if (rnd01() < 0.8) {
            int v = -1;
            for (int t = 0; t < 64; t++) {
                int w = rndint(V);
                if (badc[w] > 0) { v = w; break; }
            }
            if (v >= 0) {
                int u = nb[v * MAXDEG + rndint(d)];
                i = find_edge(v, u);
                if (i < 0) continue;
            }
        }
        if (i < 0) i = rndint(M);
        j = rndint(M);
        if (!valid_switch(i, j)) continue;
        do_switch(i, j);
        long c2 = cost();
        long delta = c2 - c;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            c = c2;
            memcpy(badc, bad, sizeof(int) * (size_t)V);
            if (c == 0) return 1;
        } else {
            do_switch(i, j);
        }
    }
    return 0;
}

static void grow(long moore) {
    while (now() < t_end) {
        if ((long)bs.V + 2 > moore || bs.V + 2 > MAXV - 2) break;
        load_state(&bs);
        if (!insert_pair()) break;
        double rem = t_end - now();
        double until = now() + (rem < 4.0 ? rem : 4.0);
        if (anneal(20000, until)) save_state(&bs);
    }
}

/* ---------------------------------------------------------- verify and print */

static int verify_state(void) {
    if ((V * d) % 2 != 0 || M != V * d / 2) return 0;
    for (int v = 0; v < V; v++)
        for (int i = 0; i < d; i++) {
            int u = nb[v * MAXDEG + i];
            if (u < 0 || u >= V) return 0;
            if (side[u] == side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (nb[v * MAXDEG + j] == u) return 0;
        }
    for (int k = 0; k < M; k++) {
        if (EU[k] < 0 || EU[k] >= V || EV[k] < 0 || EV[k] >= V) return 0;
        if (side[EU[k]] != 0 || side[EV[k]] != 1) return 0;
        if (!adjacent(EU[k], EV[k])) return 0;
    }
    return cost() == 0;
}

static void print_state(void) {
    printf("%d %d\n", V, M);
    for (int k = 0; k < M; k++) printf("%d %d\n", EU[k], EV[k]);
}

/* ---------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed budget nlo\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int nlo = atoi(argv[5]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) { printf("0 0\n"); return 0; }

    double t0 = now();
    t_end = t0 + budget * 0.9;

    long moore = moore_bound();
    int nmax = (int)(moore / 2);
    if (nmax > MAXG - 1) nmax = MAXG - 1;
    int nstart = nlo;
    if (nstart < d + 1) nstart = d + 1;

    double slice = budget / 60.0;
    if (slice < 0.4) slice = 0.4;
    if (slice > 2.0) slice = 2.0;

    /* Stage 1: bi-Cayley scan, upward, until half the budget is used. */
    double stage1_end = t0 + 0.5 * budget;
    if (stage1_end > t_end) stage1_end = t_end;
    for (int n = nstart; n <= nmax && now() < stage1_end; n++) {
        double until = now() + slice;
        if (until > stage1_end) until = stage1_end;
        search_n(n, until);
    }

    /* Stage 2: grow from the bi-Cayley graph (or K_{d,d}) by pair insertion + annealing. */
    if (bestN > 0) build_from_bicayley();
    else build_complete();
    if (!verify_state()) build_complete();
    save_state(&bs);

    grow((long)moore);

    load_state(&bs);
    if (verify_state()) {
        print_state();
    } else {
        build_complete();
        if (verify_state()) print_state();
        else printf("0 0\n");
    }
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}
    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d < 2 or D < 2 or d > 16:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best

    nlo = max(d + 1, best[0] // 2 + 1, int(0.45 * moore) // 2)
    if nlo > moore // 2:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), nlo],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
