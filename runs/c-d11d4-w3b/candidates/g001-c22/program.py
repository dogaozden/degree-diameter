import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Lift engine (C): simulated annealing over voltage lifts of a d-regular
# bipartite base on k + k vertices, with lift group Z_m x|_r Z_k2 (order G).
#
# The lift vertex (u, x) joins (v, mul(x, g)) for every dart (u, v, g). Left
# translations are automorphisms, so the whole-graph bad-pair count is
# determined by BFS from the identity of each of the 2k fibres:
#     cost = sum over fibres s of (number of vertices at distance > D from s*G).
# cost == 0 iff the lift has diameter <= D. Moves keep the lift d-regular:
# change one voltage, or swap the right ends (or left ends) of two darts.
# ----------------------------------------------------------------------------

LIFT_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 32
#define MAXK 8
#define MAXDARTS (MAXK * MAXD)
#define MAXG 3000
#define MAXNV 6000

static int d, D, k, m, k2, r, G, nd;
static int U[MAXDARTS], V[MAXDARTS], Gv[MAXDARTS];
static int ed[MAXDARTS][MAXG];
static int pw[64];
static int nbr[MAXNV][MAXD];
static int ndeg[MAXNV];
static int dist_[MAXNV], q_[MAXNV];
static uint64_t rs = 1;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int n) { return (int)(nextr() % (uint64_t)n); }

static double rnd01(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

/* Semidirect product Z_m x| Z_k2, element (a, b) coded as a*k2 + b. */
static int gmul(int x, int y) {
    int a = x / k2, b = x % k2;
    int c = y / k2, e = y % k2;
    int t = (int)(((long long)pw[b] * c + a) % m);
    return t * k2 + (b + e) % k2;
}

static void setg(int j, int g) {
    Gv[j] = g;
    for (int x = 0; x < G; x++) ed[j][x] = gmul(x, g);
}

/* Is there a dart among the first `lim` darts (other than `skip`) equal to (u, v, g)? */
static int dup_in(int lim, int skip, int u, int v, int g) {
    for (int j = 0; j < lim; j++)
        if (j != skip && U[j] == u && V[j] == v && Gv[j] == g) return 1;
    return 0;
}

static void build_adj(void) {
    int n = 2 * k * G;
    for (int i = 0; i < n; i++) ndeg[i] = 0;
    for (int j = 0; j < nd; j++) {
        int u = U[j], v = k + V[j];
        for (int x = 0; x < G; x++) {
            int a = u * G + x;
            int b = v * G + ed[j][x];
            nbr[a][ndeg[a]++] = b;
            nbr[b][ndeg[b]++] = a;
        }
    }
}

/* Sum over fibres of the number of vertices farther than D from the fibre identity.
   Zero iff the lift has diameter <= D (by transitivity of left translations). */
static long long sum_bad(void) {
    int n = 2 * k * G;
    build_adj();
    long long tot = 0;
    for (int s = 0; s < 2 * k; s++) {
        int src = s * G;
        for (int i = 0; i < n; i++) dist_[i] = -1;
        int qh = 0, qt = 0;
        q_[qt++] = src;
        dist_[src] = 0;
        while (qh < qt) {
            int x = q_[qh++];
            if (dist_[x] >= D) continue;
            for (int i = 0; i < ndeg[x]; i++) {
                int y = nbr[x][i];
                if (dist_[y] < 0) {
                    dist_[y] = dist_[x] + 1;
                    q_[qt++] = y;
                }
            }
        }
        tot += n - qt;
    }
    return tot;
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    k = atoi(argv[4]);
    m = atoi(argv[5]);
    k2 = atoi(argv[6]);
    r = atoi(argv[7]);
    double tl = atof(argv[8]);
    if (d < 1 || d > MAXD || D < 1 || k < 1 || k > MAXK || m < 1 || k2 < 1 || k2 > 63 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    G = m * k2;
    if (G > MAXG || 2 * k * G > MAXNV - 1) {
        printf("0 0\n");
        return 0;
    }
    r %= m;
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)(((long long)pw[b - 1] * r) % m);
    if ((((long long)pw[k2 - 1] * r) % m) != (1 % m)) {
        printf("0 0\n");
        return 0;
    }

    rs = seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    nd = k * d;
    int perm[MAXK];
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rnd(i + 1);
            int tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < k; i++) {
            int idx = t * k + i;
            U[idx] = i;
            V[idx] = perm[i];
            int ok = 0;
            for (int tries = 0; tries < 500 && !ok; tries++) {
                setg(idx, rnd(G));
                ok = !dup_in(idx, idx, U[idx], V[idx], Gv[idx]);
            }
            if (!ok) {
                printf("0 0\n");
                return 0;
            }
        }
    }

    long long S = sum_bad();
    const double T0 = 2.0, T1 = 0.1;
    clock_t c0 = clock();
    while (S > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= tl) break;
        double T = T0 * pow(T1 / T0, el / tl);
        double pm = rnd01();
        if (pm < 0.4) {
            int j = rnd(nd);
            int g2 = rnd(G);
            if (g2 == Gv[j] || dup_in(nd, j, U[j], V[j], g2)) continue;
            int old = Gv[j];
            setg(j, g2);
            long long S2 = sum_bad();
            if (S2 <= S || rnd01() < exp(-(double)(S2 - S) / T)) S = S2;
            else setg(j, old);
        } else if (pm < 0.7) {
            int j1 = rnd(nd), j2 = rnd(nd);
            if (j1 == j2 || V[j1] == V[j2]) continue;
            if (dup_in(nd, j1, U[j1], V[j2], Gv[j1]) || dup_in(nd, j2, U[j2], V[j1], Gv[j2])) continue;
            int tmp = V[j1];
            V[j1] = V[j2];
            V[j2] = tmp;
            long long S2 = sum_bad();
            if (S2 <= S || rnd01() < exp(-(double)(S2 - S) / T)) S = S2;
            else {
                tmp = V[j1];
                V[j1] = V[j2];
                V[j2] = tmp;
            }
        } else {
            int j1 = rnd(nd), j2 = rnd(nd);
            if (j1 == j2 || U[j1] == U[j2]) continue;
            if (dup_in(nd, j1, U[j2], V[j1], Gv[j1]) || dup_in(nd, j2, U[j1], V[j2], Gv[j2])) continue;
            int tmp = U[j1];
            U[j1] = U[j2];
            U[j2] = tmp;
            long long S2 = sum_bad();
            if (S2 <= S || rnd01() < exp(-(double)(S2 - S) / T)) S = S2;
            else {
                tmp = U[j1];
                U[j1] = U[j2];
                U[j2] = tmp;
            }
        }
    }

    if (S == 0) {
        int n = 2 * k * G;
        printf("%d %d\n", n, nd * G);
        for (int j = 0; j < nd; j++)
            for (int x = 0; x < G; x++)
                printf("%d %d\n", U[j] * G + x, (k + V[j]) * G + ed[j][x]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Annealing engine (C): grows a valid graph by one vertex whenever it is valid,
# and otherwise anneals rewirings to reduce the number of pairs at distance > D.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 6000
#define WMAX ((MAXN + 63) / 64)
#define DEGMAX 32
#define LOGMAX 1024

static int DEG, DIAM;
static int nv;
static int adjv[MAXN][DEGMAX];
static int deg[MAXN];
static int col[MAXN];
static int bestAdj[MAXN][DEGMAX];
static int bestDeg[MAXN];
static int bestCol[MAXN];
static int bestNv;
static uint64_t RA[MAXN * WMAX];
static uint64_t RB[MAXN * WMAX];
static uint64_t rs = 1;
static int defi[MAXN], fulli[MAXN], stk[MAXN];
static int logOp[LOGMAX], logA[LOGMAX], logB[LOGMAX], logN;
static int stampArr[MAXN], distArr[MAXN], qbuf[MAXN];
static int stampCur = 0;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nextr() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long eval_cost(void) {
    int W = (nv + 63) >> 6;
    uint64_t *cur = RA, *nxt = RB, *tmp;
    memset(RA, 0, sizeof(uint64_t) * (size_t)nv * (size_t)W);
    for (int v = 0; v < nv; v++)
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < nv; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            uint64_t *s = cur + (size_t)v * W;
            memcpy(o, s, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                uint64_t *t = cur + (size_t)adjv[v][i] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < nv; v++) {
        uint64_t *s = cur + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(s[w]);
        bad += nv - cnt;
    }
    return bad / 2;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adjv[a][i] == b) return 1;
    return 0;
}

static void raw_del_half(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adjv[a][i] == b) {
            adjv[a][i] = adjv[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void raw_add(int a, int b) {
    adjv[a][deg[a]++] = b;
    adjv[b][deg[b]++] = a;
}

static void raw_remove(int a, int b) {
    raw_del_half(a, b);
    raw_del_half(b, a);
}

static void log_push(int op, int a, int b) {
    if (logN < LOGMAX) {
        logOp[logN] = op;
        logA[logN] = a;
        logB[logN] = b;
        logN++;
    }
}

static void edit_remove(int a, int b) {
    raw_remove(a, b);
    log_push(0, a, b);
}

static void edit_add(int a, int b) {
    raw_add(a, b);
    log_push(1, a, b);
}

/* Undo the logged edits in reverse order, restoring the previous state. */
static void undo_log(void) {
    for (int i = logN - 1; i >= 0; i--) {
        if (logOp[i] == 0) raw_add(logA[i], logB[i]);
        else raw_remove(logA[i], logB[i]);
    }
    logN = 0;
}

static void shuffle_int(int *x, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

static int swap_move(void) {
    int a = rnd(nv);
    if (deg[a] == 0) return 0;
    int c = -1;
    for (int t = 0; t < 200; t++) {
        int x = rnd(nv);
        if (x != a && col[x] == col[a] && deg[x] > 0) {
            c = x;
            break;
        }
    }
    if (c < 0) return 0;
    int b = adjv[a][rnd(deg[a])];
    int e = adjv[c][rnd(deg[c])];
    if (b == e) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    logN = 0;
    edit_remove(a, b);
    edit_remove(c, e);
    edit_add(a, e);
    edit_add(c, b);
    return 1;
}

static int targeted_move(void) {
    int v = rnd(nv);
    if (deg[v] == 0) return 0;
    stampCur++;
    int qh = 0, qt = 0;
    qbuf[qt++] = v;
    stampArr[v] = stampCur;
    distArr[v] = 0;
    while (qh < qt) {
        int u = qbuf[qh++];
        if (distArr[u] >= DIAM) continue;
        for (int i = 0; i < deg[u]; i++) {
            int x = adjv[u][i];
            if (stampArr[x] != stampCur) {
                stampArr[x] = stampCur;
                distArr[x] = distArr[u] + 1;
                qbuf[qt++] = x;
            }
        }
    }
    int cnt = 0, w = -1;
    for (int x = 0; x < nv; x++) {
        if (col[x] != col[v] || stampArr[x] == stampCur) continue;
        cnt++;
        if (rnd(cnt) == 0) w = x;
    }
    if (w < 0 || deg[w] == 0) return 0;
    int a = adjv[v][rnd(deg[v])];
    int e = adjv[w][rnd(deg[w])];
    if (a == e) return 0;
    if (has_edge(v, e) || has_edge(w, a)) return 0;
    logN = 0;
    edit_remove(v, a);
    edit_remove(w, e);
    edit_add(v, e);
    edit_add(w, a);
    return 1;
}

static int relocate_move(void) {
    int v = rnd(nv);
    int c = col[v];
    logN = 0;
    while (deg[v] > 0) edit_remove(v, adjv[v][deg[v] - 1]);
    int nd = 0, nf = 0;
    for (int w = 0; w < nv; w++) {
        if (w == v || col[w] == c) continue;
        if (deg[w] < DEG) defi[nd++] = w;
        else fulli[nf++] = w;
    }
    shuffle_int(defi, nd);
    shuffle_int(fulli, nf);
    int k = 0;
    for (int i = 0; i < nd && k < DEG; i++) {
        edit_add(v, defi[i]);
        k++;
    }
    for (int i = 0; i < nf && k < DEG; i++) {
        int w = fulli[i];
        int x = adjv[w][rnd(deg[w])];
        edit_remove(w, x);
        edit_add(v, w);
        k++;
    }
    return 1;
}

static void grow(void) {
    int c = rnd(2);
    int v = nv++;
    col[v] = c;
    deg[v] = 0;
    int nd = 0, nf = 0;
    for (int w = 0; w < v; w++) {
        if (col[w] != 1 - c) continue;
        if (deg[w] < DEG) defi[nd++] = w;
        else fulli[nf++] = w;
    }
    shuffle_int(defi, nd);
    shuffle_int(fulli, nf);
    int k = 0;
    for (int i = 0; i < nd && k < DEG; i++) {
        raw_add(v, defi[i]);
        k++;
    }
    for (int i = 0; i < nf && k < DEG; i++) {
        int w = fulli[i];
        int x = adjv[w][rnd(deg[w])];
        raw_remove(w, x);
        raw_add(v, w);
        k++;
    }
}

static void vertex_replace_kick(void) {
    if (nv < 3) return;
    int v = rnd(nv);
    while (deg[v] > 0) raw_remove(v, adjv[v][deg[v] - 1]);
    int L = nv - 1;
    if (v != L) {
        for (int i = 0; i < deg[L]; i++) {
            int w = adjv[L][i];
            for (int j = 0; j < deg[w]; j++)
                if (adjv[w][j] == L) adjv[w][j] = v;
        }
        memcpy(adjv[v], adjv[L], sizeof(int) * DEGMAX);
        deg[v] = deg[L];
        col[v] = col[L];
        deg[L] = 0;
    }
    nv--;
    grow();
}

static void save_best(void) {
    memcpy(bestAdj, adjv, sizeof adjv);
    memcpy(bestDeg, deg, sizeof deg);
    memcpy(bestCol, col, sizeof col);
    bestNv = nv;
}

static void restore_best(void) {
    memcpy(adjv, bestAdj, sizeof adjv);
    memcpy(deg, bestDeg, sizeof deg);
    memcpy(col, bestCol, sizeof col);
    nv = bestNv;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time [stall]\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    long stallLim = 1500;
    if (argc >= 6) stallLim = atol(argv[5]);
    if (stallLim < 50) stallLim = 50;
    rs = seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();
    if (DEG < 1 || DEG > DEGMAX || DIAM < 1 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 0 || n > MAXN - 2) {
        printf("0 0\n");
        return 0;
    }
    nv = n;
    for (int i = 0; i < nv; i++) { deg[i] = 0; col[i] = -1; }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= nv || v >= nv || u == v) continue;
        if (deg[u] >= DEG || deg[v] >= DEG || has_edge(u, v)) continue;
        raw_add(u, v);
    }
    if (nv == 0) {
        printf("0 0\n");
        return 0;
    }

    for (int s = 0; s < nv; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int w = adjv[u][i];
                if (col[w] == -1) {
                    col[w] = 1 - col[u];
                    stk[sp++] = w;
                }
            }
        }
    }

    long long cur_cost = eval_cost();
    save_best();
    int have_valid = (cur_cost == 0);
    double tstart = (double)clock() / CLOCKS_PER_SEC;
    long stall = 0;
    logN = 0;

    while (1) {
        double frac = ((double)clock() / CLOCKS_PER_SEC - tstart) / tl;
        if (frac >= 1.0) break;

        if (cur_cost == 0) {
            if (nv > bestNv || !have_valid) {
                save_best();
                have_valid = 1;
            }
            if (nv + 1 >= MAXN) break;
            grow();
            cur_cost = eval_cost();
            stall = 0;
            continue;
        }

        double T = 0.12 + 0.5 * (1.0 - frac);
        double pm = rnd01();
        int ok;
        if (pm < 0.35) ok = swap_move();
        else if (pm < 0.70) ok = targeted_move();
        else ok = relocate_move();
        if (!ok) {
            logN = 0;
            continue;
        }
        long long c2 = eval_cost();
        double dl = (double)(c2 - cur_cost);
        if (dl <= 0 || rnd01() < exp(-dl / T)) {
            cur_cost = c2;
            logN = 0;
        } else {
            undo_log();
        }

        if (++stall > stallLim) {
            restore_best();
            logN = 0;
            if (rnd01() < 0.5) {
                vertex_replace_kick();
            } else {
                for (int k = 0; k < 2; k++) relocate_move();
            }
            logN = 0;
            cur_cost = eval_cost();
            stall = 0;
        }
    }

    if (cur_cost == 0 && (nv > bestNv || !have_valid)) save_best();

    long long em = 0;
    for (int v = 0; v < bestNv; v++) em += bestDeg[v];
    printf("%d %lld\n", bestNv, em / 2);
    for (int v = 0; v < bestNv; v++)
        for (int i = 0; i < bestDeg[v]; i++)
            if (v < bestAdj[v][i]) printf("%d %d\n", v, bestAdj[v][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: voltage-lift search in C, then annealing growth from the best.
# ----------------------------------------------------------------------------

LIFT_KMAX = 8


def _sample_group(G, rng):
    """Return (m, k2, r) with m * k2 == G describing Z_m x|_r Z_k2 (r = 1 means direct product)."""
    opts = []
    for k2 in range(1, 13):
        if G % k2:
            continue
        m = G // k2
        if k2 == 1:
            opts.append((m, 1, 1))
            continue
        opts.append((m, k2, 1))
        cands = [r for r in range(2, m)
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if cands:
            opts.append((m, k2, rng.choice(cands)))
    return rng.choice(opts)


def _lift_run(d, D, seed, k, m, k2, r, budget):
    """Run the lift engine for one group configuration; return parsed (n, edges), n = 0 on failure."""
    out = lib.run_c(LIFT_SOURCE, [d, D, seed, k, m, k2, r, f"{budget:.2f}"],
                    timeout=budget + 4.0)
    return lib.parse_graph_text(out)


def _anneal(d, D, seed, graph, budget):
    """Run the annealing engine from `graph` for `budget` seconds; return parsed (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", 1500],
                    stdin_graph=graph, timeout=budget + 4.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Calibration: D = 3 with d - 1 a prime power is the Moore-optimal incidence graph.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, e0, d, D):
            return n0, e0

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Phase 1 (bold change): search voltage lifts over non-cyclic groups, all in C.
    # Each call tries one (base size k, group order G, group) configuration with
    # G just above the order needed to beat the current best.
    lift_end = start + 0.70 * tl
    while True:
        budget = min(2.0, lift_end - time.monotonic())
        if budget < 0.6:
            break
        k = rng.randint(1, LIFT_KMAX)
        floor = max(2, best_n // (2 * k) + 1)
        G = floor + rng.randrange(0, 3 + floor // 80)
        G = min(G, 5000 // (2 * k), 3000)
        if G < 2:
            continue
        m, k2, r = _sample_group(G, rng)
        try:
            n2, e2 = _lift_run(d, D, rng.randrange(1 << 30), k, m, k2, r, budget)
        except Exception:
            break
        if n2 > 0:
            consider(n2, e2)

    # Phase 2: C annealer grows the best valid graph (lift or fallback).
    end = start + 0.93 * tl - 1.5
    remaining = end - time.monotonic()
    if remaining > 2.0:
        try:
            n2, e2 = _anneal(d, D, seed, best, remaining)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
