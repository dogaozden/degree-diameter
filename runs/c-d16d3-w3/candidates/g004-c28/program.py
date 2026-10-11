"""Diameter-3 search: algebraic starts (PG(2,q) incidence, Araujo-Pardo/Lopez, conic blow-up,
arc-extended PG(2,q)), then one C engine that does dominating-set insertion, swap/removal
perturbation, and grow-by-two with annealed repair. Every returned graph is validated."""
import random
import time

import lib

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXW (MAXN / 64)
#define MAXD 40
typedef uint64_t u64;

typedef struct {
    int n;
    int side[MAXN];
    int deg[MAXN];
    int adj[MAXN][MAXD];
} Snap;

static int Dd, DIAM, N;
static int sd[MAXN], dg[MAXN];
static int ad[MAXN][MAXD];
static u64 bufA[MAXN * MAXW], bufB[MAXN * MAXW], ballb[MAXN * MAXW];
static int badv[MAXN];
static Snap best_s, tmp_s;
static u64 rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static u64 rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (u64)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int has(int u, int v) {
    for (int j = 0; j < dg[u]; j++) if (ad[u][j] == v) return 1;
    return 0;
}
static void rep(int u, int old, int nw) {
    for (int j = 0; j < dg[u]; j++) if (ad[u][j] == old) { ad[u][j] = nw; return; }
}
static void drop(int u, int x) {
    for (int j = 0; j < dg[u]; j++)
        if (ad[u][j] == x) { ad[u][j] = ad[u][--dg[u]]; return; }
}
static void link_(int a, int b) {
    ad[a][dg[a]++] = b;
    ad[b][dg[b]++] = a;
}

static void save_state(Snap *s) {
    s->n = N;
    memcpy(s->side, sd, sizeof(int) * N);
    memcpy(s->deg, dg, sizeof(int) * N);
    memcpy(s->adj, ad, sizeof(int) * MAXD * N);
}
static void load_state(const Snap *s) {
    N = s->n;
    memcpy(sd, s->side, sizeof(int) * N);
    memcpy(dg, s->deg, sizeof(int) * N);
    memcpy(ad, s->adj, sizeof(int) * MAXD * N);
}

/* ballb[v] = bit set of vertices within distance k of v (k steps of bit-parallel OR). */
static void reach_all(int k) {
    int W = (N + 63) >> 6;
    u64 *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < k; r++) {
        for (int v = 0; v < N; v++) {
            u64 *dst = nxt + (size_t)v * W;
            memcpy(dst, cur + (size_t)v * W, sizeof(u64) * W);
            for (int j = 0; j < dg[v]; j++) {
                const u64 *s = cur + (size_t)ad[v][j] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        u64 *t = cur; cur = nxt; nxt = t;
    }
    memcpy(ballb, cur, sizeof(u64) * (size_t)N * W);
}

static int diam_ok(void) {
    int W = (N + 63) >> 6;
    reach_all(DIAM);
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(ballb[(size_t)v * W + w]);
        if (c != N) return 0;
    }
    return 1;
}

/* Number of unordered bad pairs; fills badv[]. */
static long bad_count(void) {
    int W = (N + 63) >> 6;
    long tot = 0;
    reach_all(DIAM);
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(ballb[(size_t)v * W + w]);
        badv[v] = N - c;
        tot += N - c;
    }
    return tot / 2;
}

/* Greedy cover of all current vertices by radius-(DIAM-1) balls of vertices with side != X.
   Needs ballb holding radius DIAM-1. Returns number of chosen vertices written to T, or 0. */
static int try_insert(int X, int restarts, int *T) {
    static int cand[MAXN];
    static char used[MAXN];
    static u64 U[MAXW];
    int W = (N + 63) >> 6, nc = 0;
    for (int v = 0; v < N; v++)
        if (sd[v] != X && dg[v] < Dd) cand[nc++] = v;
    if (nc == 0) return 0;
    for (int r = 0; r < restarts; r++) {
        for (int w = 0; w < W; w++) U[w] = ~0ULL;
        if (N & 63) U[W - 1] = (1ULL << (N & 63)) - 1ULL;
        memset(used, 0, (size_t)nc);
        int nt = 0, unc = N;
        while (unc > 0 && nt < Dd) {
            int bi = -1;
            long bk = -1;
            for (int i = 0; i < nc; i++) {
                if (used[i]) continue;
                const u64 *b = ballb + (size_t)cand[i] * W;
                int g = 0;
                for (int w = 0; w < W; w++) g += __builtin_popcountll(b[w] & U[w]);
                if (g == 0) continue;
                long key = (long)g * 4096 + rndint(4096);
                if (key > bk) { bk = key; bi = i; }
            }
            if (bi < 0) break;
            used[bi] = 1;
            T[nt++] = cand[bi];
            const u64 *b = ballb + (size_t)cand[bi] * W;
            unc = 0;
            for (int w = 0; w < W; w++) {
                U[w] &= ~b[w];
                unc += __builtin_popcountll(U[w]);
            }
        }
        if (unc == 0) return nt;
    }
    return 0;
}

static void add_vertex(int X, int nt, const int *T) {
    int x = N++;
    sd[x] = X;
    dg[x] = 0;
    for (int k = 0; k < nt; k++) link_(x, T[k]);
}

static void remove_vertex(int r) {
    int L = N - 1;
    for (int j = 0; j < dg[r]; j++) drop(ad[r][j], r);
    dg[r] = 0;
    if (r != L) {
        for (int j = 0; j < dg[L]; j++) rep(ad[L][j], L, r);
        sd[r] = sd[L];
        dg[r] = dg[L];
        memcpy(ad[r], ad[L], sizeof(int) * dg[L]);
    }
    dg[L] = 0;
    N--;
}

/* Degree-preserving 2-switch on two edges of side 0 (a-b, c-e -> a-e, c-b). */
static int swap_move(void) {
    for (int tries = 0; tries < 50; tries++) {
        int a = rndint(N);
        if (sd[a] != 0 || dg[a] == 0) continue;
        int b = ad[a][rndint(dg[a])];
        int c = rndint(N);
        if (c == a || sd[c] != 0 || dg[c] == 0) continue;
        int e = ad[c][rndint(dg[c])];
        if (e == b || has(a, e) || has(c, b)) continue;
        rep(a, b, e);
        rep(b, a, c);
        rep(c, e, b);
        rep(e, c, a);
        return 1;
    }
    return 0;
}

/* Add two vertices x (side 0), y (side 1) joined, steal up to Dd-1 edges, then anneal
   2-switches until no bad pairs remain. Returns 1 on success (state valid). */
static int grow2(double until) {
    static int used[MAXN];
    static int stamp = 0;
    if (N + 2 >= MAXN) return 0;
    int n0 = N, x = N, y = N + 1;
    stamp++;
    N += 2;
    sd[x] = 0; sd[y] = 1;
    dg[x] = 0; dg[y] = 0;
    link_(x, y);
    used[x] = used[y] = stamp;
    int steals = 0;
    for (int tries = 0; tries < 20000 && steals < Dd - 1; tries++) {
        int a = rndint(n0);
        if (sd[a] != 0 || dg[a] == 0 || used[a] == stamp) continue;
        int b = ad[a][rndint(dg[a])];
        if (used[b] == stamp) continue;
        rep(a, b, y);
        rep(b, a, x);
        ad[x][dg[x]++] = b;
        ad[y][dg[y]++] = a;
        used[a] = used[b] = stamp;
        steals++;
    }
    long cur = bad_count();
    double temp = 1.0;
    long it = 0;
    while (cur > 0) {
        if (((++it) & 7) == 0 && now() > until) return 0;
        int v = rndint(N);
        for (int t = 0; t < 40 && badv[v] == 0; t++) v = rndint(N);
        if (dg[v] == 0) continue;
        int u = ad[v][rndint(dg[v])];
        int s = rndint(N);
        if (s == v || sd[s] != sd[v] || dg[s] == 0) continue;
        int t = ad[s][rndint(dg[s])];
        if (t == u || has(v, t) || has(s, u)) continue;
        rep(v, u, t); rep(u, v, s); rep(s, t, u); rep(t, s, v);
        long nb = bad_count();
        if (nb <= cur || rnd01() < exp((double)(cur - nb) / temp)) {
            cur = nb;
        } else {
            rep(v, t, u); rep(u, s, v); rep(s, u, t); rep(t, v, s);
            bad_count();
        }
        temp *= 0.999;
        if (temp < 0.05) temp = 1.0;
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    Dd = d;
    if (Dd > MAXD) Dd = MAXD;
    rs ^= (u64)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double tend = now() + limit;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    N = (n0 > 0 && n0 <= MAXN - 256) ? n0 : 0;
    if (DIAM < 2 || Dd < 2 || N == 0) { printf("0 0\n"); return 0; }
    for (int v = 0; v < N; v++) { dg[v] = 0; sd[v] = -1; }
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (dg[u] >= Dd || dg[v] >= Dd || has(u, v)) continue;
        link_(u, v);
    }

    static int qu[MAXN];
    int ok = 1;
    for (int s = 0; s < N && ok; s++) {
        if (sd[s] >= 0) continue;
        sd[s] = 0;
        int h = 0, t = 0;
        qu[t++] = s;
        while (h < t) {
            int u = qu[h++];
            for (int j = 0; j < dg[u]; j++) {
                int v = ad[u][j];
                if (sd[v] < 0) { sd[v] = 1 - sd[u]; qu[t++] = v; }
                else if (sd[v] == sd[u]) ok = 0;
            }
        }
    }
    if (!ok || !diam_ok()) { printf("0 0\n"); return 0; }

    save_state(&best_s);
    int bestN = N;
    int stall = 0;
    int T[MAXD];
    while (now() < tend && N + 2 < MAXN) {
        reach_all(DIAM - 1);
        int inserted = 0, first = rndint(2);
        for (int t = 0; t < 2 && !inserted; t++) {
            int X = first ^ t;
            int nt = try_insert(X, 4, T);
            if (nt > 0) { add_vertex(X, nt, T); inserted = 1; }
        }
        if (inserted) {
            if (N > bestN) { bestN = N; save_state(&best_s); }
            stall = 0;
            continue;
        }
        stall++;
        int k = 1 + rndint(3);
        for (int j = 0; j < k; j++) {
            save_state(&tmp_s);
            if (rndint(4) == 0 && N > 4) remove_vertex(rndint(N));
            else swap_move();
            if (!diam_ok()) load_state(&tmp_s);
        }
        if (N < bestN - 2) load_state(&best_s);
        if (stall > 0 && stall % 60 == 0) {
            save_state(&tmp_s);
            double until = now() + 0.7;
            if (until > tend) until = tend;
            if (grow2(until) && diam_ok()) {
                stall = 0;
                if (N > bestN) { bestN = N; save_state(&best_s); }
            } else {
                load_state(&tmp_s);
            }
        }
    }

    load_state(&best_s);
    int M = 0;
    for (int v = 0; v < N; v++)
        for (int j = 0; j < dg[v]; j++)
            if (ad[v][j] > v) M++;
    printf("%d %d\n", N, M);
    for (int v = 0; v < N; v++)
        for (int j = 0; j < dg[v]; j++)
            if (ad[v][j] > v) printf("%d %d\n", v, ad[v][j]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Algebraic starts for diameter 3.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q); lines are indexed 0..m-1."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by at most s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: pick elements so that every target is hit by at most s of them."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, pl, lp, SA, SB):
    """PG(2,q) incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in lp[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """For each prime power q with s = d - q - 1 >= 1, build the arc-extended incidence graph."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if time.monotonic() > deadline:
            break
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 1:
            continue
        m, edges, pl, lp, index = _pg_data(q)
        SA = _greedy_side(m, s, pl, rng, 30, deadline)
        SB = _greedy_side(m, s, lp, rng, 30, deadline)
        if s >= 2 and q >= 3:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, pl):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, lp):
                SB = cs
        if not (_loads_ok(SA, s, m, pl) and _loads_ok(SB, s, m, lp)):
            continue
        out.append(_arc_graph(m, edges, pl, lp, SA, SB))
    return out


def _conic_blowup(d):
    """Twin blow-up of PG(2,q) with q = d-3 odd: conic points and conic lines are duplicated."""
    q = d - 3
    if q < 3 or q % 2 == 0 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {v: i for i, v in enumerate(pts)}
    m = len(pts)
    conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    arc = [index[v] for v in conic]
    n, base = lib.projective_plane_incidence(q)
    pcopy = {i: [i] for i in range(m)}
    lcopy = {j: [m + j] for j in range(m)}
    for i in arc:
        pcopy[i].append(n)
        n += 1
    for j in arc:
        lcopy[j].append(n)
        n += 1
    edges = set()
    for u, v in base:
        i, j = u, v - m
        for a in pcopy[i]:
            for b in lcopy[j]:
                edges.add((a, b) if a < b else (b, a))
    return n, sorted(edges)


def _starts(d, D, deadline, rng):
    """Candidate starting graphs; each is validated by the caller."""
    out = []
    try:
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            out.append(lib.projective_plane_incidence(d - 1))
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            out.append(lib.araujo_lopez_graph(d - 2))
    except Exception:
        pass
    try:
        cb = _conic_blowup(d)
        if cb is not None:
            out.append(cb)
    except Exception:
        pass
    if D >= 3:
        try:
            out.extend(_arc_extensions(d, deadline, rng))
        except Exception:
            pass
    return out


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    fallback = lib.haar_graph(d, range(d))  # K_{d,d}: optimal for D = 2
    if D == 2 or d == 1:
        return fallback

    rng = random.Random(seed * 7919 + 31 * d + D)
    cands = [fallback] + _starts(d, D, t0 + 0.12 * time_limit, rng)
    cands.sort(key=lambda g: -g[0])
    best = None
    for g in cands:
        try:
            if lib.is_valid(g[0], g[1], d, D):
                best = g
                break
        except Exception:
            pass
    if best is None:
        return fallback

    # Already at the Moore bound: nothing to search for.
    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.80 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 1.0:
        return best
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                        stdin_graph=best, timeout=budget + 6.0)
        n2, e2 = lib.parse_graph_text(out)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass
    return best
