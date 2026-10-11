import itertools
import math
import random
import time

import numpy as np

import lib


# C engine: simulated annealing over voltage lifts of a bipartite base graph
# (k + k vertices, d darts per vertex) with group Z_m x| Z_k2 (cyclic when k2 = 1).
# Lifted graph: vertices (base b, group element x), edge (A_i, x) ~ (B_j, x*g) per dart.
# Left multiplication is an automorphism, so BFS from one vertex per fibre
# decides the diameter. Cost = number of unreached (source, vertex) pairs
# plus a large penalty per duplicate lifted edge.
C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <time.h>

#define MAXD 64
#define MAXK 32
#define MAXG 2500

static int d_, D_, k_, m_, k2_, r_, G_, N_;
static int sig[MAXD][MAXK];
static int vol[MAXD][MAXK];
static int incI[MAXD * MAXK];
static int incG[MAXD * MAXK];
static int *MT = NULL, *IV = NULL, *pw = NULL;
static int *mark = NULL, *dep = NULL, *qu = NULL;
static int curstamp = 0;
static uint64_t rs = 88172645463325252ULL;

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_;
    int c = y / k2_, e = y % k2_;
    long t = ((long)a + (long)pw[b] * (long)c) % m_;
    return (int)(t * k2_ + (b + e) % k2_);
}

static int ginv(int x) {
    int a = x / k2_, b = x % k2_;
    int nb = (k2_ - b) % k2_;
    long t = (((long)(m_ - pw[nb])) % m_) * (long)a % m_;
    return (int)(t * k2_ + nb);
}

static void build_tables(void) {
    pw = malloc(sizeof(int) * (size_t)k2_);
    long p = 1 % m_;
    for (int b = 0; b < k2_; b++) {
        pw[b] = (int)p;
        p = (p * r_) % m_;
    }
    MT = malloc(sizeof(int) * (size_t)G_ * (size_t)G_);
    IV = malloc(sizeof(int) * (size_t)G_);
    for (int x = 0; x < G_; x++)
        for (int y = 0; y < G_; y++)
            MT[x * G_ + y] = gmul(x, y);
    for (int x = 0; x < G_; x++)
        IV[x] = ginv(x);
}

static void rebuild_inc(void) {
    int cnt[MAXK];
    memset(cnt, 0, sizeof cnt);
    for (int p = 0; p < d_; p++)
        for (int i = 0; i < k_; i++) {
            int j = sig[p][i];
            int slot = j * d_ + cnt[j]++;
            incI[slot] = i;
            incG[slot] = vol[p][i];
        }
}

static int reach(int src) {
    int cs = ++curstamp;
    int h = 0, t = 0;
    int kG = k_ * G_;
    qu[t++] = src;
    mark[src] = cs;
    dep[src] = 0;
    while (h < t) {
        int v = qu[h++];
        if (dep[v] >= D_) continue;
        int nd = dep[v] + 1;
        if (v < kG) {
            int i = v / G_, x = v % G_;
            for (int p = 0; p < d_; p++) {
                int j = sig[p][i];
                int g = vol[p][i];
                int w = kG + j * G_ + MT[x * G_ + g];
                if (mark[w] != cs) {
                    mark[w] = cs;
                    dep[w] = nd;
                    qu[t++] = w;
                }
            }
        } else {
            int idx = v - kG;
            int j = idx / G_, y = idx % G_;
            for (int s = 0; s < d_; s++) {
                int i = incI[j * d_ + s];
                int g = incG[j * d_ + s];
                int w = i * G_ + MT[y * G_ + IV[g]];
                if (mark[w] != cs) {
                    mark[w] = cs;
                    dep[w] = nd;
                    qu[t++] = w;
                }
            }
        }
    }
    return t;
}

static long evaluate(void) {
    long dup = 0;
    for (int i = 0; i < k_; i++)
        for (int p = 0; p < d_; p++)
            for (int s = p + 1; s < d_; s++)
                if (sig[p][i] == sig[s][i] && vol[p][i] == vol[s][i])
                    dup++;
    rebuild_inc();
    long cost = dup * (long)N_;
    for (int b = 0; b < 2 * k_; b++) {
        int r = reach(b * G_);
        cost += (long)(N_ - r);
    }
    return cost;
}

static int bsig[MAXD][MAXK];
static int bvol[MAXD][MAXK];

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    k_ = atoi(argv[3]);
    m_ = atoi(argv[4]);
    k2_ = atoi(argv[5]);
    r_ = atoi(argv[6]);
    rs = strtoull(argv[7], NULL, 10) * 0x9E3779B97F4A7C15ULL + 1234567ULL;
    if (rs == 0) rs = 1;
    double secs = atof(argv[8]);
    if (d_ < 1 || d_ > MAXD || k_ < 1 || k_ > MAXK || D_ < 1 || m_ < 1 || k2_ < 1) {
        printf("0 0\n");
        return 0;
    }
    G_ = m_ * k2_;
    if (G_ < 2 || G_ > MAXG) {
        printf("0 0\n");
        return 0;
    }
    r_ %= m_;
    build_tables();
    N_ = 2 * k_ * G_;
    mark = calloc((size_t)N_, sizeof(int));
    dep = calloc((size_t)N_, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)N_);

    for (int p = 0; p < d_; p++) {
        int arr[MAXK];
        for (int i = 0; i < k_; i++) arr[i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = arr[i]; arr[i] = arr[j]; arr[j] = tmp;
        }
        for (int i = 0; i < k_; i++) sig[p][i] = arr[i];
    }
    for (int p = 0; p < d_; p++)
        for (int i = 0; i < k_; i++)
            vol[p][i] = rndint(G_);

    long cost = evaluate();
    long cost0 = cost;
    long bestcost = cost;
    memcpy(bsig, sig, sizeof sig);
    memcpy(bvol, vol, sizeof vol);

    double t0 = now_s();
    double T0 = 0.1 * (double)cost0 + 1.0;
    double Tend = 0.5;
    double T = T0;
    long it = 0;
    while (cost > 0) {
        if ((it & 15) == 0) {
            double el = now_s() - t0;
            if (el >= secs) break;
            double f = el / secs;
            T = T0 * pow(Tend / T0, f);
        }
        it++;
        int mtype, p, i, s, oldv = 0;
        if (k_ >= 2 && rnd01() < 0.25) {
            mtype = 1;
            p = rndint(d_);
            i = rndint(k_);
            s = rndint(k_ - 1);
            if (s >= i) s++;
            int tmp = sig[p][i]; sig[p][i] = sig[p][s]; sig[p][s] = tmp;
        } else {
            mtype = 0;
            p = rndint(d_);
            i = rndint(k_);
            oldv = vol[p][i];
            int nv = rndint(G_);
            if (nv == oldv) nv = (nv + 1) % G_;
            vol[p][i] = nv;
        }
        long nc = evaluate();
        int accept = 0;
        if (nc <= cost) accept = 1;
        else if (rnd01() < exp(-(double)(nc - cost) / T)) accept = 1;
        if (accept) {
            cost = nc;
            if (cost < bestcost) {
                bestcost = cost;
                memcpy(bsig, sig, sizeof sig);
                memcpy(bvol, vol, sizeof vol);
            }
        } else {
            if (mtype == 1) {
                int tmp = sig[p][i]; sig[p][i] = sig[p][s]; sig[p][s] = tmp;
            } else {
                vol[p][i] = oldv;
            }
        }
    }

    if (bestcost != 0) {
        printf("0 0\n");
        return 0;
    }
    long M = (long)k_ * G_ * d_;
    printf("%d %ld\n", N_, M);
    for (int i = 0; i < k_; i++)
        for (int x = 0; x < G_; x++)
            for (int p = 0; p < d_; p++) {
                int j = bsig[p][i];
                int g = bvol[p][i];
                int u = i * G_ + x;
                int w = (k_ + j) * G_ + MT[x * G_ + g];
                printf("%d %d\n", u, w);
            }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (degree q+1, diameter 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q); order 2(q+1)(q^2+1)."""
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
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Twin and cover growth (kept from the parent as the safe stage).
# ----------------------------------------------------------------------------

def _twin_grow(n, edges, d, rng, deadline):
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
        order = list(range(n))
        rng.shuffle(order)
        for x in order:
            if time.monotonic() >= deadline:
                break
            nb = adj[x]
            if not nb or any(deg[y] >= d for y in nb):
                continue
            v = n
            n += 1
            adj.append(list(nb))
            deg.append(len(nb))
            for y in nb:
                adj[y].append(v)
                deg[y] += 1
                edges.append((y, v))
            changed = True
    return n, edges


def _balls_radius(n, adj, r):
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
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


def _cand_matrix(cand_balls, n):
    nb = (n + 7) // 8
    buf = b"".join(x.to_bytes(nb, "little") for x in cand_balls)
    arr = np.frombuffer(buf, dtype=np.uint8).reshape(len(cand_balls), nb)
    return np.unpackbits(arr, axis=1, bitorder="little")[:, :n].astype(bool)


def _weighted_cover(B, cand_ids, n, d, nrng, randomize):
    k = B.shape[0]
    uncov = np.ones(n, dtype=bool)
    avail = np.ones(k, dtype=bool)
    chosen = []
    for _ in range(d):
        if not uncov.any():
            break
        sub = B[:, uncov]
        cnt = sub.sum(axis=0)
        if (cnt == 0).any():
            return None
        w = 1.0 / cnt
        score = sub.astype(np.float64) @ w
        if randomize:
            score = score * (1.0 + 0.08 * nrng.random(k))
        score[~avail] = -1.0
        i = int(np.argmax(score))
        if score[i] <= 0:
            break
        avail[i] = False
        chosen.append(cand_ids[i])
        uncov &= ~B[i]
    return chosen if not uncov.any() else None


def _greedy_cover(cands, ball, full, d, rng, randomize):
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _find_cover(cands, ball, n, full, d, rng, deadline):
    B = _cand_matrix([ball[s] for s in cands], n)
    nrng = np.random.default_rng(rng.randrange(1 << 30))
    for attempt in range(12):
        if time.monotonic() >= deadline:
            return None
        chosen = _weighted_cover(B, cands, n, d, nrng, attempt > 0)
        if chosen:
            return chosen
    for attempt in range(60):
        if time.monotonic() >= deadline:
            return None
        chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
        if chosen:
            return chosen
    return None


def _extend_cover(n, edges, d, D, deadline, rng):
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = _find_cover(cands, ball, n, full, d, rng, deadline)
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
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


def _grow(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _pipeline(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(10):
        if time.monotonic() >= deadline:
            break
        before = cur_n
        cur_n, cur_e = _twin_grow(cur_n, cur_e, d, rng, deadline)
        cur_n, cur_e = _grow(cur_n, cur_e, d, D, deadline, rng)
        if cur_n == before:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# New bold stage: annealed voltage lifts over small non-cyclic groups, run in C.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (m, k2, r) with m * k2 == G and Z_m x| Z_k2 a group (r = 1 for cyclic), or None."""
    divs = [k2 for k2 in range(1, min(G, 12) + 1) if G % k2 == 0 and G // k2 >= 2]
    rng.shuffle(divs)
    for k2 in divs:
        m = G // k2
        if k2 == 1:
            return m, 1, 1 % m
        cands = [r for r in rng.sample(range(1, m), min(m - 1, 40))
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if cands:
            return m, k2, rng.choice(cands)
    return None


def _try_lift(d, D, k, G, rng, budget):
    samp = _sample_group(G, rng)
    if samp is None:
        return None
    m, k2, r = samp
    seed = rng.randrange(1, 1 << 30)
    out = lib.run_c(C_SOURCE, [d, D, k, m, k2, r, seed, f"{budget:.2f}"],
                    timeout=budget + 20.0)
    if out.split()[:2] == ["0", "0"]:
        return None
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if best_n >= moore:
        return best

    # Stage 1: structured start plus twin/cover growth (safe baseline).
    stage1_end = start + 0.25 * time_limit
    if D == 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        if qs:
            pg_n, pg_e = lib.projective_plane_incidence(qs[0])
            consider(pg_n, pg_e)
            while time.monotonic() < stage1_end and best_n < moore:
                pn, pe = _pipeline(pg_n, pg_e, d, D, stage1_end, rng)
                consider(pn, pe)
    elif D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            while time.monotonic() < stage1_end and best_n < moore:
                pn, pe = _pipeline(gq[0], gq[1], d, D, stage1_end, rng)
                consider(pn, pe)

    # Stage 2: voltage lifts over small groups, searched in C, aiming above best_n.
    if D >= 3:
        ks = [2, 3, 3, 4, 4, 5, 6]
        while best_n < moore:
            remaining = deadline - time.monotonic()
            if remaining < 2.0:
                break
            budget = max(2.0, min(8.0, remaining - 1.0))
            k = rng.choice(ks)
            G = best_n // (2 * k) + 1
            if rng.random() < 0.5:
                G += rng.randrange(0, 3)
            if G < 2 or G > 2400:
                continue
            try:
                res = _try_lift(d, D, k, G, rng, budget)
            except RuntimeError:
                res = None
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
