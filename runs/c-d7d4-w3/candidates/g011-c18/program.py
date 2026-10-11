import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: annealed voltage lifts over Z_M x| Z_K. Each candidate is a bipartite
# lift with s base vertices per side. Left translation is an automorphism, so the
# diameter test needs BFS only from the 2s representatives. Output is the largest
# valid lift found above the given order, or "0 0". Python re-checks every graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NOPT 8192

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int d_, D_, maxN_;
static int s_, G_, M_, K_, N_, OFF_;
static int pw_[4096];
static int *dI, *dJ, *dG, *sJ, *sG;
static int *adj, *cnt, *seen, *dep, *queue;
static int stamp_ = 0;
static double TL_;
static int oM[NOPT], oK[NOPT], oR[NOPT];

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int powmod_(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static int gmul(int x, int y) {
    int a = x / K_, b = x - a * K_;
    int c = y / K_, e = y - c * K_;
    return (int)(((a + (long long)pw_[b] * c) % M_) * K_ + (b + e) % K_);
}

static void build_adj(void) {
    int d = d_, G = G_, s = s_, off = OFF_;
    memset(cnt, 0, sizeof(int) * (size_t)N_);
    for (int t = 0; t < s * d; t++) {
        int i = dI[t], j = dJ[t], g = dG[t];
        for (int x = 0; x < G; x++) {
            int u = i * G + x;
            int v = off + j * G + gmul(x, g);
            adj[(size_t)u * d + cnt[u]++] = v;
            adj[(size_t)v * d + cnt[v]++] = u;
        }
    }
}

static long cost(void) {
    int d = d_, s = s_, G = G_, N = N_;
    (void)d;
    long total = 0;
    for (int k = 0; k < 2 * s; k++) {
        int src = (k < s) ? k * G : OFF_ + (k - s) * G;
        stamp_++;
        int head = 0, tail = 0;
        queue[tail++] = src;
        seen[src] = stamp_;
        dep[src] = 0;
        while (head < tail) {
            int u = queue[head++];
            if (dep[u] >= D_) continue;
            for (int e = 0; e < cnt[u]; e++) {
                int v = adj[(size_t)u * d_ + e];
                if (seen[v] != stamp_) {
                    seen[v] = stamp_;
                    dep[v] = dep[u] + 1;
                    queue[tail++] = v;
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static void init_darts(void) {
    int s = s_, d = d_, G = G_;
    int n = s * d;
    for (int t = 0; t < n; t++) {
        dI[t] = t / d;
        dJ[t] = t / d;
        dG[t] = rndi(G);
    }
    for (int t = n - 1; t > 0; t--) {
        int r = rndi(t + 1);
        int tmp = dJ[t]; dJ[t] = dJ[r]; dJ[r] = tmp;
    }
}

static long anneal(long cur, int iters) {
    int n = s_ * d_;
    double T = 0.6;
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && elapsed() > TL_) break;
        memcpy(sJ, dJ, sizeof(int) * (size_t)n);
        memcpy(sG, dG, sizeof(int) * (size_t)n);
        if (rndu() < 0.5) {
            int p = rndi(n), q = rndi(n);
            if (p == q) continue;
            int tmp = dJ[p]; dJ[p] = dJ[q]; dJ[q] = tmp;
        } else {
            int p = rndi(n);
            dG[p] = rndi(G_);
        }
        build_adj();
        long nc = cost();
        if (nc <= cur || rndu() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            memcpy(dJ, sJ, sizeof(int) * (size_t)n);
            memcpy(dG, sG, sizeof(int) * (size_t)n);
            build_adj();
        }
        T *= 0.999;
        if (T < 0.05) T = 0.05;
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 7) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], 0, 10);
    double tl = atof(argv[4]);
    int bestN = atoi(argv[5]);
    maxN_ = atoi(argv[6]);
    if (maxN_ > 20000) maxN_ = 20000;
    if (d_ < 2 || D_ < 2 || maxN_ < 4) { printf("0 0\n"); return 0; }

    rs ^= seed * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    TL_ = elapsed() + tl;

    int cap = maxN_ + 8;
    dI = malloc(sizeof(int) * (size_t)(4 * d_ + 8));
    dJ = malloc(sizeof(int) * (size_t)(4 * d_ + 8));
    dG = malloc(sizeof(int) * (size_t)(4 * d_ + 8));
    sJ = malloc(sizeof(int) * (size_t)(4 * d_ + 8));
    sG = malloc(sizeof(int) * (size_t)(4 * d_ + 8));
    adj = malloc(sizeof(int) * (size_t)cap * (size_t)d_);
    cnt = malloc(sizeof(int) * (size_t)cap);
    seen = malloc(sizeof(int) * (size_t)cap);
    dep = malloc(sizeof(int) * (size_t)cap);
    queue = malloc(sizeof(int) * (size_t)cap);
    if (!dI || !dJ || !dG || !sJ || !sG || !adj || !cnt || !seen || !dep || !queue) {
        printf("0 0\n");
        return 0;
    }
    memset(seen, 0, sizeof(int) * (size_t)cap);

    int *bestE = NULL;
    int bestM = 0;
    int found = 0;

    while (elapsed() < TL_) {
        int feas[4], nf = 0;
        for (int s = 1; s <= 4; s++) {
            long lo = bestN / (2 * s) + 1;
            long hi = maxN_ / (2 * s);
            if (lo <= hi) feas[nf++] = s;
        }
        if (nf == 0) break;
        int s = feas[rndi(nf)];
        long lo = bestN / (2 * s) + 1;
        long hi = maxN_ / (2 * s);
        int span = (int)(hi - lo + 1);
        if (span > 4) span = 4;
        int G = (int)lo + rndi(span);

        int nopt = 0;
        for (int k = 1; k <= G; k++) {
            if (G % k) continue;
            if (k > 4096) continue;
            int m = G / k;
            for (int r = 0; r < m; r++) {
                if (gcd_(r, m) != 1) continue;
                if (powmod_(r, k, m) != 1 % m) continue;
                if (nopt < NOPT) {
                    oM[nopt] = m; oK[nopt] = k; oR[nopt] = r;
                    nopt++;
                }
            }
        }
        if (nopt == 0) continue;
        int o = rndi(nopt);

        s_ = s; G_ = G; M_ = oM[o]; K_ = oK[o];
        N_ = 2 * s * G;
        OFF_ = s * G;
        for (int b = 0; b < K_; b++) pw_[b] = powmod_(oR[o], b, M_);

        init_darts();
        build_adj();
        long cur = cost();
        cur = anneal(cur, 2000);

        if (cur == 0) {
            int N = N_, d = d_;
            int *E = malloc(sizeof(int) * 2 * (size_t)N * (size_t)d + 8);
            if (!E) break;
            int M = 0;
            for (int u = 0; u < OFF_; u++) {
                for (int e = 0; e < d; e++) {
                    int v = adj[(size_t)u * d + e];
                    int dup = 0;
                    for (int f = 0; f < e; f++) {
                        if (adj[(size_t)u * d + f] == v) { dup = 1; break; }
                    }
                    if (!dup) {
                        E[2 * M] = u;
                        E[2 * M + 1] = v;
                        M++;
                    }
                }
            }
            free(bestE);
            bestE = E;
            bestM = M;
            bestN = N;
            found = 1;
        }
    }

    if (found) {
        printf("%d %d\n", bestN, bestM);
        for (int i = 0; i < bestM; i++) printf("%d %d\n", bestE[2 * i], bestE[2 * i + 1]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
# Shared graph helpers.
# ----------------------------------------------------------------------------

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


def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


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


def _extend_cover(n, edges, d, D, deadline, rng=None):
    if D < 2:
        return n, edges
    if rng is None:
        rng = random.Random(0)
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
            chosen = None
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
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


# ----------------------------------------------------------------------------
# Twin duplication.
# ----------------------------------------------------------------------------

def _duplicate_twins(n, edges, d, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    changed = True
    while changed:
        changed = False
        order = list(range(len(adj)))
        rng.shuffle(order)
        for v in order:
            nb = adj[v]
            if not nb or len(nb) > d:
                continue
            if any(len(adj[u]) >= d for u in nb):
                continue
            w = len(adj)
            adj.append(set(nb))
            for u in nb:
                adj[u].add(w)
            changed = True
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


def _trial(base_n, base_e, d, D, rng, deadline):
    mode = rng.randrange(3)
    n, e = base_n, list(base_e)
    if mode == 0:
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    return n, e


# ----------------------------------------------------------------------------
# Python fallback for voltage lifts (used only if the C engine fails).
# ----------------------------------------------------------------------------

def _group_options(G):
    """(M, k, r) triples describing groups of order G: Z_M x|_r Z_k with M*k = G."""
    opts = []
    for k in range(1, G + 1):
        if G % k:
            continue
        M = G // k
        for r in range(0, M):
            if math.gcd(r, M) == 1 and pow(r, k, M) == 1 % M:
                opts.append((M, k, r))
    return opts


def _random_darts(s, d, G, rng):
    a = [i for i in range(s) for _ in range(d)]
    b = list(a)
    rng.shuffle(b)
    return [(i, s + j - s, rng.randrange(G)) for i, j in zip(a, b)]


def _lift_search(d, D, s, G, mul, rng, deadline, darts=None, temp=0.6):
    if darts is None:
        darts = _random_darts(s, d, G, rng)
    n, e = lib.group_lift(2 * s, darts, G, mul)
    cur = _cost(_to_sets(n, e), D)
    while cur > 0:
        if time.monotonic() > deadline:
            return None, darts, temp
        old = list(darts)
        k = len(darts)
        if k >= 2 and rng.random() < 0.5:
            p = rng.randrange(k)
            q = rng.randrange(k)
            if p == q:
                continue
            ip, jp, gp = darts[p]
            iq, jq, gq = darts[q]
            darts[p] = (ip, jq, gp)
            darts[q] = (iq, jp, gq)
        else:
            p = rng.randrange(k)
            i, j, _ = darts[p]
            darts[p] = (i, j, rng.randrange(G))
        n2, e2 = lib.group_lift(2 * s, darts, G, mul)
        new = _cost(_to_sets(n2, e2), D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
            n, e = n2, e2
        else:
            darts = old
        temp = max(0.05, temp * 0.999)
    return (n, e), darts, temp


def _lift_phase(d, D, get_best, deadline, rng, consider):
    states = {}
    while time.monotonic() < deadline:
        best_n = get_best()
        states = {key: v for key, v in states.items() if 2 * key[0] * key[1] > best_n}
        if states and rng.random() < 0.7:
            key = rng.choice(list(states))
            darts, temp = states.pop(key)
            s, G, M, k, r = key
        else:
            darts, temp = None, 0.6
            s = rng.choice((1, 2, 2, 3, 3, 4))
            G_min = best_n // (2 * s) + 1
            G = G_min + rng.randrange(4)
            opts = _group_options(G)
            if not opts:
                continue
            M, k, r = rng.choice(opts)
            key = (s, G, M, k, r)
        try:
            _, mul, _ = lib.semidirect_group(M, k, r)
        except ValueError:
            continue
        slice_end = min(deadline, time.monotonic() + 3.0)
        res, darts, temp = _lift_search(d, D, s, G, mul, rng, slice_end, darts, temp)
        if res is None:
            states[key] = (darts, temp)
            if len(states) > 40:
                states.pop(next(iter(states)))
            continue
        n, e = res
        consider(n, e)
        n2, e2 = _grow(n, _saturate_edges(n, e, d, rng), d, D, deadline, rng)
        consider(n2, e2)


# ----------------------------------------------------------------------------
# C voltage-lift search wrapper.
# ----------------------------------------------------------------------------

def _c_lift(d, D, seed, budget, best_n, maxn):
    """Run the C lift search. Returns (n, edges) of a valid lift above best_n, or None."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best_n, maxn],
                     stdin_graph=None, timeout=budget + 15.0)
    n, edges = lib.parse_graph_text(text)
    if n < 1 or not edges:
        return None
    return n, edges


# ----------------------------------------------------------------------------
# Large-neighbourhood search (kill, repair, regrow).
# ----------------------------------------------------------------------------

def _fill(adj, color, d, rng):
    n = len(adj)
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _anneal(adj, color, d, D, rng, iters, deadline):
    cur = _cost(adj, D)
    side0 = [v for v in range(len(adj)) if color[v] == 0]
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        a = rng.choice(side0)
        if not adj[a]:
            continue
        b = rng.choice(tuple(adj[a]))
        c = rng.choice(side0)
        if c == a or not adj[c]:
            continue
        e = rng.choice(tuple(adj[c]))
        if e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _cost(adj, D)
        if new <= cur or (new == cur + 1 and rng.random() < 0.1):
            cur = new
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return cur == 0


def _lns(n, edges, d, D, deadline, rng, consider):
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 2, 3, 4))
        if k >= cur_n:
            break
        kill = set(rng.sample(range(cur_n), k))
        keep = [v for v in range(cur_n) if v not in kill]
        remap = {v: i for i, v in enumerate(keep)}
        m = len(keep)
        e2 = [(remap[u], remap[v]) for u, v in cur_e if u not in kill and v not in kill]
        adj = _to_sets(m, e2)
        color = _bipartition(m, adj)
        _fill(adj, color, d, rng)
        if not _anneal(adj, color, d, D, rng, 150, deadline):
            continue
        e3 = [(u, v) for u in range(m) for v in adj[u] if u < v]
        n4, e4 = _grow(m, e3, d, D, deadline, rng)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Redundant-edge pruning, then regrow.
# ----------------------------------------------------------------------------

def _prune_redundant(n, edges, D, rng, deadline, max_tests):
    adj = _to_sets(n, edges)
    cand = list(edges)
    rng.shuffle(cand)
    tests = 0
    for u, v in cand:
        if tests >= max_tests or time.monotonic() > deadline:
            break
        if v not in adj[u]:
            continue
        tests += 1
        adj[u].discard(v)
        adj[v].discard(u)
        if _cost(adj, D) != 0:
            adj[u].add(v)
            adj[v].add(u)
    return [(a, b) for a in range(n) for b in adj[a] if a < b]


def _prune_regrow(n, edges, d, D, deadline, rng, consider):
    best_n, best_e = n, list(edges)
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        pe = _prune_redundant(cur_n, cur_e, D, rng, deadline, 160)
        n2, e2 = _grow(cur_n, pe, d, D, deadline, rng)
        consider(n2, e2)
        if n2 > best_n:
            best_n, best_e = n2, list(e2)
        if n2 >= cur_n - 1:
            cur_n, cur_e = n2, list(e2)
        elif n2 < best_n - 2 or rng.random() < 0.3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Driver. Budget T = 0.85 * time_limit:
#   base: GQ W(q) or PG(2,q), grown; twin/grow trials
#   lift: C voltage-lift annealing (Python fallback if C fails)
#   LNS from the best valid graph; then pruning and regrowth.
# Every kept graph passes lib.is_valid. The Haar fallback is always valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.85 * time_limit

    def at(f):
        return start + f * T

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    fallback = lib.haar_graph(d, range(d))
    best_n, best_e = fallback
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)
            return True
        return False

    if best_n >= moore:
        return best_n, list(best_e)

    # Structured base.
    base = None
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
    base_n, base_e = best_n, list(best_e)
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        base_n, base_e = n0, list(e0)
        n1, e1 = _grow(n0, e0, d, D, at(0.08), rng)
        consider(n1, e1)
    if D >= 2:
        trial_end = at(0.15)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Voltage lifts: C engine first, Python fallback on failure.
    lift_end = at(0.55)
    if D >= 2 and time.monotonic() < lift_end and best_n < moore:
        got = None
        try:
            got = _c_lift(d, D, seed, lift_end - time.monotonic(), best_n,
                          min(moore, 20000))
        except Exception:
            got = None
            if time.monotonic() < lift_end:
                _lift_phase(d, D, lambda: best_n, lift_end, rng, consider)
        if got is not None:
            n, e = got
            consider(n, e)
            n2, e2 = _grow(n, _saturate_edges(n, e, d, rng), d, D, at(0.62), rng)
            consider(n2, e2)

    if best_n >= moore:
        return best_n, list(best_e)

    # LNS from the best valid graph.
    if D >= 2 and time.monotonic() < at(0.80):
        _lns(best_n, best_e, d, D, at(0.80), rng, consider)

    # Prune redundant edges and regrow.
    if D >= 2 and time.monotonic() < at(1.0):
        _prune_regrow(best_n, best_e, d, D, at(1.0), rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)
