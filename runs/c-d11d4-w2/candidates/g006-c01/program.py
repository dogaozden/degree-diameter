import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over voltage lifts of a bipartite base.
#
# Group G = Z_m x| Z_k (element (a,b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d)).
# Base: KB left and KB right vertices. Slot s (0..DEG-1) is a bijection perm[s]
# from left to right with a voltage volt[s][i] in G. Lift vertices: left (i,x),
# right (j,y), coded i*G+x and (KB+j)*G+y. Edge (i,x)-(perm[s][i], x*volt[s][i]).
# Requirement: for each left i, the pairs (perm[s][i], volt[s][i]) are distinct over s,
# which makes the lift simple, bipartite and DEG-regular.
#
# Left translation by any group element is an automorphism, so vertices in one
# fibre are equivalent. Cost = bad unordered pairs (distance > DIAM) computed
# with one BFS per fibre (2*KB BFS runs), scaled by G.
# Moves: change one voltage, or swap the targets of two left vertices in one slot.
# Stalls trigger a fresh random start. Output: first valid lift found, or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 1024
#define MAXK 8
#define MAXDEG 32
#define MAXN (2 * MAXK * MAXG)
#define STALL 20000

static int G, KB, DEG, DIAM;
static int MUL[MAXG * MAXG];
static int INV[MAXG];
static int PW[MAXG + 1];
static int perm[MAXDEG][MAXK];
static int invp[MAXDEG][MAXK];
static int volt[MAXDEG][MAXK];
static int N;
static int adj[MAXN][MAXDEG];
static int qbuf[MAXN];
static int dist_[MAXN];
static int stamp[MAXN];
static int stampCur = 0;
static uint64_t rs = 1;

static uint64_t nxt(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nxt() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(nxt() >> 11) * (1.0 / 9007199254740992.0);
}

/* True if slot s of left vertex i repeats an earlier slot's (target, voltage). */
static int clash_prev(int s, int i) {
    for (int t = 0; t < s; t++)
        if (perm[t][i] == perm[s][i] && volt[t][i] == volt[s][i]) return 1;
    return 0;
}

static int left_ok(int i) {
    for (int s = 0; s < DEG; s++)
        if (clash_prev(s, i)) return 0;
    return 1;
}

static int all_ok(void) {
    for (int i = 0; i < KB; i++)
        if (!left_ok(i)) return 0;
    return 1;
}

static void init_random(void) {
    for (int s = 0; s < DEG; s++) {
        for (int i = 0; i < KB; i++) perm[s][i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = rnd(i + 1);
            int t = perm[s][i];
            perm[s][i] = perm[s][j];
            perm[s][j] = t;
        }
    }
    for (int s = 0; s < DEG; s++)
        for (int i = 0; i < KB; i++) {
            int tries = 0;
            do {
                volt[s][i] = rnd(G);
                tries++;
            } while (tries < 200 && clash_prev(s, i));
        }
}

static void build_adj(void) {
    N = 2 * KB * G;
    for (int s = 0; s < DEG; s++)
        for (int i = 0; i < KB; i++) invp[s][perm[s][i]] = i;
    for (int i = 0; i < KB; i++)
        for (int x = 0; x < G; x++) {
            int v = i * G + x;
            for (int s = 0; s < DEG; s++) {
                int j = perm[s][i];
                adj[v][s] = (KB + j) * G + MUL[x * G + volt[s][i]];
            }
        }
    for (int j = 0; j < KB; j++)
        for (int y = 0; y < G; y++) {
            int v = (KB + j) * G + y;
            for (int s = 0; s < DEG; s++) {
                int i = invp[s][j];
                adj[v][s] = i * G + MUL[y * G + INV[volt[s][i]]];
            }
        }
}

/* Bad unordered pairs = G * (sum over fibre representatives of unreached counts) / 2. */
static long long cost(void) {
    build_adj();
    long long tot = 0;
    for (int r = 0; r < 2 * KB; r++) {
        int src = r * G;
        stampCur++;
        int qh = 0, qt = 0;
        qbuf[qt++] = src;
        stamp[src] = stampCur;
        dist_[src] = 0;
        while (qh < qt) {
            int u = qbuf[qh++];
            if (dist_[u] >= DIAM) continue;
            for (int s = 0; s < DEG; s++) {
                int w = adj[u][s];
                if (stamp[w] != stampCur) {
                    stamp[w] = stampCur;
                    dist_[w] = dist_[u] + 1;
                    qbuf[qt++] = w;
                }
            }
        }
        tot += N - qt;
    }
    return (long long)G * tot / 2;
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int m = atoi(argv[5]);
    int k = atoi(argv[6]);
    int r = atoi(argv[7]);
    KB = atoi(argv[8]);
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1 || KB < 1 || KB > MAXK ||
        m < 1 || k < 1 || budget <= 0) {
        printf("0 0\n");
        return 0;
    }
    G = m * k;
    if (G > MAXG) {
        printf("0 0\n");
        return 0;
    }
    r = ((r % m) + m) % m;
    PW[0] = 1 % m;
    for (int b = 1; b < k; b++) PW[b] = (PW[b - 1] * r) % m;
    if ((PW[k - 1] * r) % m != 1 % m) {
        printf("0 0\n");
        return 0;
    }
    for (int x = 0; x < G; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < G; y++) {
            int c = y / k, dd = y % k;
            MUL[x * G + y] = ((a + PW[b] * c) % m) * k + (b + dd) % k;
        }
    }
    for (int x = 0; x < G; x++) {
        INV[x] = -1;
        for (int y = 0; y < G; y++)
            if (MUL[x * G + y] == 0) {
                INV[x] = y;
                break;
            }
        if (INV[x] < 0) {
            printf("0 0\n");
            return 0;
        }
    }

    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 16; i++) nxt();

    init_random();
    long long cur = cost();
    long long bestc = cur;
    long long stall = 0;
    clock_t c0 = clock();

    while (cur != 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= budget) break;
        double frac = el / budget;
        double T = (double)G * (0.4 * (1.0 - frac) + 0.01);

        int sp[MAXDEG][MAXK], sv[MAXDEG][MAXK];
        memcpy(sp, perm, sizeof perm);
        memcpy(sv, volt, sizeof volt);
        int ok = 0;
        if (KB >= 2 && rnd01() < 0.3) {
            int s = rnd(DEG);
            int i1 = rnd(KB);
            int i2 = rnd(KB - 1);
            if (i2 >= i1) i2++;
            int t = perm[s][i1];
            perm[s][i1] = perm[s][i2];
            perm[s][i2] = t;
            ok = left_ok(i1) && left_ok(i2);
        } else {
            int s = rnd(DEG), i = rnd(KB);
            int nvv = rnd(G);
            if (nvv != volt[s][i]) {
                volt[s][i] = nvv;
                ok = left_ok(i);
            }
        }
        if (!ok) {
            memcpy(perm, sp, sizeof perm);
            memcpy(volt, sv, sizeof volt);
            continue;
        }

        long long c2 = cost();
        double dl = (double)(c2 - cur);
        if (dl <= 0 || rnd01() < exp(-dl / T)) {
            cur = c2;
        } else {
            memcpy(perm, sp, sizeof perm);
            memcpy(volt, sv, sizeof volt);
        }
        if (cur < bestc) {
            bestc = cur;
            stall = 0;
        } else if (++stall > STALL) {
            init_random();
            cur = cost();
            bestc = cur;
            stall = 0;
        }
    }

    long long fin = cost();
    if (fin != 0 || !all_ok()) {
        printf("0 0\n");
        return 0;
    }
    int nn = 2 * KB * G;
    long long mm = (long long)KB * G * DEG;
    printf("%d %lld\n", nn, mm);
    for (int v = 0; v < KB * G; v++)
        for (int s = 0; s < DEG; s++)
            printf("%d %d\n", v, adj[v][s]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4, order 2(q+1)(q^2+1)."""
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _pg_best(d):
    """PG(2,q) incidence graph for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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
    return color


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order (keeps diameter and bipartiteness)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _group_params(G, rng):
    """Parameters (m, k, r) of semidirect products Z_m x| Z_k with m*k = G (r = 1 gives the direct product)."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m == 1:
            out.append((1, k, 0))
            continue
        cands = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
        out.append((m, k, 1))
        if cands:
            for r in rng.sample(cands, min(3, len(cands))):
                out.append((m, k, r))
    return out


def _c_lift(d, D, seed, m, k, r, kb, budget):
    """Run the C lift annealer; return (n, edges) for a valid lift, or None."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", m, k, r, kb],
                    stdin_graph=None, timeout=budget + 6.0)
    n, edges = lib.parse_graph_text(out)
    return (n, edges) if n > 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        cyc = (n, [(i, (i + 1) % n) for i in range(n)])
        if lib.is_valid(cyc[0], cyc[1], d, D):
            return cyc

    # Calibration: D = 3 with d - 1 a prime power is the Moore-optimal incidence graph.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, e0, d, D):
            return n0, e0

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e, eq=False):
        nonlocal best, best_n
        if (n > best_n or (eq and n == best_n)) and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Construction base: PG(2,q) for D = 3, W(q) for D >= 4, then saturate spare degree.
    base = _pg_best(d) if D == 3 else _best_gq(d)
    if base is not None:
        consider(base[0], base[1])
        sat_edges = _saturate_edges(base[0], base[1], d, rng)
        consider(base[0], sat_edges, eq=True)

    # Main search: voltage lifts over small groups, targeting orders above the best so far.
    # Each candidate order M gives 2M vertices; M = KB * G with KB base pairs and |G| = G.
    deadline = start + 0.85 * tl - 0.5
    M = best_n // 2 + 1
    fails = 0
    exc = 0
    call = 0
    while time.monotonic() < deadline and M <= 8 * 1024:
        remaining = deadline - time.monotonic()
        if remaining < 0.4:
            break
        M = max(M, best_n // 2 + 1)
        kbs = [kb for kb in range(1, 9) if M % kb == 0 and d <= M // kb <= 1024]
        if not kbs:
            M += 1
            continue
        kb = rng.choice(kbs)
        G = M // kb
        m, k, r = rng.choice(_group_params(G, rng))
        budget = min(2.0, remaining - 0.3)
        call += 1
        try:
            res = _c_lift(d, D, seed * 1000 + call, m, k, r, kb, budget)
        except Exception:
            res = None
            exc += 1
            if exc >= 3:
                break
        if res is not None:
            consider(res[0], res[1])
            fails = 0
        else:
            fails += 1
            if fails >= 3:
                M += 1
                fails = 0
        M = max(M, best_n // 2 + 1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
