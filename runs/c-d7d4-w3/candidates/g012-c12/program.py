import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: random search for bipartite bi-Cayley lifts over semidirect
# products Z_M x|_r Z_k. Base has s A-vertices and s B-vertices, each A-vertex
# has d darts, each B-vertex receives d darts. Dart (i, j, g) joins A-copy
# (i, x) to B-copy (j, x*g). The graph is d-regular and bipartite. Left
# multiplication by the group acts on the lift, so the diameter is <= D iff a
# BFS from each of the 2s base vertices reaches every vertex within D steps.
# Simulated annealing minimises the number of unreached (source, vertex)
# pairs. Each attempt targets an order above the current best. The engine
# prints the largest valid lift it found (or "0 0").
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXS 4
#define MAXOPT 512

static uint64_t rs_ = 0x9E3779B97F4A7C15ULL;

static uint64_t rnd64(void) {
    rs_ ^= rs_ << 13;
    rs_ ^= rs_ >> 7;
    rs_ ^= rs_ << 17;
    return rs_;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, s_, G_, M_, k_, T_, N_;
static int *pw_ = NULL, *Bd_ = NULL, *Vd_ = NULL, *adj_ = NULL;
static int *fillc_ = NULL, *stamp_ = NULL, *queue_ = NULL;
static int gen_ = 0;

static int gcd_(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static double moore_bound(int d, int D) {
    double sum = 0.0, p = 1.0;
    int i;
    if (D == 0 || d == 0) return 1.0;
    if (d == 1) return D >= 1 ? 2.0 : 1.0;
    if (d == 2) return 2.0 * D;
    for (i = 0; i < D; i++) { sum += p; p *= (d - 1); }
    return 2.0 * sum;
}

static int gopts(int G, int *Mo, int *ko, int *ro, int maxn) {
    int cnt = 0, k, M, r, i;
    for (k = 1; k <= G; k++) {
        if (G % k) continue;
        M = G / k;
        if (M < 2) continue;
        for (r = 1; r < M; r++) {
            long long p = 1;
            if (gcd_(r, M) != 1) continue;
            for (i = 0; i < k; i++) p = p * r % M;
            if (p != 1) continue;
            if (cnt < maxn) { Mo[cnt] = M; ko[cnt] = k; ro[cnt] = r; cnt++; }
        }
    }
    return cnt;
}

static void set_group(int r) {
    int b;
    free(pw_);
    pw_ = malloc(sizeof(int) * (size_t)k_);
    if (!pw_) { printf("0 0\n"); exit(0); }
    pw_[0] = 1 % M_;
    for (b = 1; b < k_; b++) pw_[b] = (int)((long long)pw_[b - 1] * r % M_);
}

static int gmul(int x, int y) {
    int a = x / k_, b = x % k_, c = y / k_, e = y % k_;
    long long na = ((long long)a + (long long)pw_[b] * c) % M_;
    int nb = (b + e) % k_;
    return (int)na * k_ + nb;
}

static void ensure_arrays(void) {
    Bd_ = realloc(Bd_, sizeof(int) * (size_t)T_);
    Vd_ = realloc(Vd_, sizeof(int) * (size_t)T_);
    adj_ = realloc(adj_, sizeof(int) * (size_t)N_ * (size_t)d_);
    fillc_ = realloc(fillc_, sizeof(int) * (size_t)N_);
    stamp_ = realloc(stamp_, sizeof(int) * (size_t)N_);
    queue_ = realloc(queue_, sizeof(int) * (size_t)N_);
    if (!Bd_ || !Vd_ || !adj_ || !fillc_ || !stamp_ || !queue_) {
        printf("0 0\n");
        exit(0);
    }
    memset(stamp_, 0, sizeof(int) * (size_t)N_);
}

static void build_adj(void) {
    int i, x, t, u, w, blockA;
    for (i = 0; i < N_; i++) fillc_[i] = 0;
    for (t = 0; t < T_; t++) {
        blockA = t / d_;
        for (x = 0; x < G_; x++) {
            u = blockA * G_ + x;
            w = (s_ + Bd_[t]) * G_ + gmul(x, Vd_[t]);
            adj_[u * d_ + fillc_[u]++] = w;
            adj_[w * d_ + fillc_[w]++] = u;
        }
    }
}

static long cost_eval(void) {
    long total = 0;
    int si, depth, head, tail, lend, j, v, w;
    for (si = 0; si < 2 * s_; si++) {
        gen_++;
        head = 0;
        tail = 0;
        queue_[tail++] = si * G_;
        stamp_[si * G_] = gen_;
        for (depth = 0; depth < D_ && head < tail; depth++) {
            lend = tail;
            while (head < lend) {
                v = queue_[head++];
                for (j = 0; j < d_; j++) {
                    w = adj_[v * d_ + j];
                    if (stamp_[w] != gen_) {
                        stamp_[w] = gen_;
                        queue_[tail++] = w;
                    }
                }
            }
        }
        total += N_ - tail;
    }
    return total;
}

static long run_anneal(long maxit, clock_t dl) {
    long cur, nc, it;
    int p, q, tmp, old, nv;
    double temp;
    build_adj();
    cur = cost_eval();
    for (it = 0; it < maxit && cur > 0; it++) {
        if ((it & 127) == 0 && clock() > dl) break;
        temp = 2.0 * pow(0.03 / 2.0, (double)it / (double)maxit);
        p = rndint(T_);
        if (rnd01() < 0.6) {
            q = rndint(T_);
            if (q == p || Bd_[q] == Bd_[p]) continue;
            tmp = Bd_[p]; Bd_[p] = Bd_[q]; Bd_[q] = tmp;
            build_adj();
            nc = cost_eval();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / temp)) {
                cur = nc;
            } else {
                tmp = Bd_[p]; Bd_[p] = Bd_[q]; Bd_[q] = tmp;
                build_adj();
            }
        } else {
            old = Vd_[p];
            nv = rndint(G_);
            if (nv == old) continue;
            Vd_[p] = nv;
            build_adj();
            nc = cost_eval();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / temp)) {
                cur = nc;
            } else {
                Vd_[p] = old;
                build_adj();
            }
        }
    }
    return cur;
}

static int emit_edges(int do_print) {
    int m = 0, u, i, j, x, nA = s_ * G_;
    int *tmp = malloc(sizeof(int) * (size_t)d_);
    if (!tmp) return 0;
    for (u = 0; u < nA; u++) {
        memcpy(tmp, adj_ + (size_t)u * d_, sizeof(int) * (size_t)d_);
        for (i = 1; i < d_; i++) {
            x = tmp[i];
            j = i - 1;
            while (j >= 0 && tmp[j] > x) { tmp[j + 1] = tmp[j]; j--; }
            tmp[j + 1] = x;
        }
        for (i = 0; i < d_; i++) {
            if (i > 0 && tmp[i] == tmp[i - 1]) continue;
            m++;
            if (do_print) printf("%d %d\n", u, tmp[i]);
        }
    }
    free(tmp);
    return m;
}

int main(int argc, char **argv) {
    int bs = 0, bG = 0, bM = 0, bk = 0, br = 0, have = 0;
    int *bestB = NULL, *bestV = NULL;
    long bestN, hint, base, G, cur;
    double budget, moore;
    clock_t dl;
    int s, o, t, i, m;
    int Mo[MAXOPT], ko[MAXOPT], ro[MAXOPT];
    int nopt;

    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs_ ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs_ == 0) rs_ = 1;
    for (i = 0; i < 20; i++) rnd64();
    budget = atof(argv[4]);
    hint = atol(argv[5]);
    if (d_ < 2 || D_ < 2) { printf("0 0\n"); return 0; }
    moore = moore_bound(d_, D_);
    if (moore > 60000.0) moore = 60000.0;
    dl = clock() + (clock_t)(budget * CLOCKS_PER_SEC);
    bestN = hint;

    while (clock() < dl) {
        s = 1 + rndint(MAXS);
        base = bestN / (2L * s);
        G = base + 1 + rndint(3);
        if (G < 2) G = 2;
        if (2.0 * s * (double)G > moore) {
            G = (long)(moore / (2.0 * s));
            if (G < base + 1 || G < 2) continue;
        }
        nopt = gopts((int)G, Mo, ko, ro, MAXOPT);
        if (nopt == 0) continue;
        o = rndint(nopt);
        s_ = s;
        G_ = (int)G;
        M_ = Mo[o];
        k_ = ko[o];
        set_group(ro[o]);
        T_ = s_ * d_;
        N_ = 2 * s_ * G_;
        ensure_arrays();
        for (t = 0; t < T_; t++) {
            Bd_[t] = t % s_;
            Vd_[t] = rndint(G_);
        }
        for (t = T_ - 1; t > 0; t--) {
            int j = rndint(t + 1);
            int tmp = Bd_[t]; Bd_[t] = Bd_[j]; Bd_[j] = tmp;
        }
        cur = run_anneal(60000, dl);
        if (cur == 0) {
            bestN = N_;
            have = 1;
            bs = s_; bG = G_; bM = M_; bk = k_; br = ro[o];
            free(bestB);
            free(bestV);
            bestB = malloc(sizeof(int) * (size_t)T_);
            bestV = malloc(sizeof(int) * (size_t)T_);
            if (!bestB || !bestV) { printf("0 0\n"); return 0; }
            memcpy(bestB, Bd_, sizeof(int) * (size_t)T_);
            memcpy(bestV, Vd_, sizeof(int) * (size_t)T_);
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    s_ = bs; G_ = bG; M_ = bM; k_ = bk;
    set_group(br);
    T_ = s_ * d_;
    N_ = 2 * s_ * G_;
    ensure_arrays();
    memcpy(Bd_, bestB, sizeof(int) * (size_t)T_);
    memcpy(Vd_, bestV, sizeof(int) * (size_t)T_);
    build_adj();
    m = emit_edges(0);
    printf("%d %d\n", N_, m);
    emit_edges(1);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases (from the parent).
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
# Shared graph helpers (from the parent).
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
# Python voltage-lift annealer (parent), used as a second, slower search.
# ----------------------------------------------------------------------------

def _group_options(G):
    """(M, k, r) triples describing groups of order G: cyclic plus Z_M x|_r Z_k with M*k = G."""
    opts = [(G, 1, 1)]
    for k in range(2, G + 1):
        if G % k:
            continue
        M = G // k
        if M < 2:
            continue
        for r in range(1, M):
            if math.gcd(r, M) == 1 and pow(r, k, M) == 1 % M:
                opts.append((M, k, r))
    return opts


def _random_darts(s, d, G, rng):
    a = [i for i in range(s) for _ in range(d)]
    b = list(a)
    rng.shuffle(b)
    return [(i, s + j, rng.randrange(G)) for i, j in zip(a, b)]


def _lift_search(d, D, s, G, mul, rng, deadline, darts=None, temp=0.6):
    """Anneal voltages of a bipartite lift.

    Returns (result, darts, temp): result is a valid (n, edges) or None when the
    deadline hit first. darts and temp let the caller resume the run later.
    """
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
    """Anneal lifts that would beat the current best order, resuming parked runs."""
    states = {}  # key (s, G, M, k, r) -> (darts, temp)
    while time.monotonic() < deadline:
        best_n = get_best()
        states = {key: v for key, v in states.items() if 2 * key[0] * key[1] > best_n}
        if states and rng.random() < 0.7:
            key = rng.choice(list(states))
            darts, temp = states.pop(key)
            s, G, M, k, r = key
        else:
            darts, temp = None, 0.6
            s = rng.choice((1, 2, 2, 3, 3, 4, 5, 6))
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
# Large-neighbourhood search and pruning (from the parent).
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
# New: run the C bi-Cayley lift search and keep its output only if valid.
# Any failure (compile error, timeout, bad output) returns None.
# ----------------------------------------------------------------------------

def _c_lift(d, D, hint_n, seed, budget):
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", hint_n],
                         stdin_graph=None, timeout=budget + 8.0)
        n, e = lib.parse_graph_text(text)
    except Exception:
        return None
    if n <= hint_n or not lib.is_valid(n, e, d, D):
        return None
    return n, e


# ----------------------------------------------------------------------------
# Driver. Times are fractions of time_limit:
#   A  structured base (W(q) or PG(2,q)) grown, then twin/grow trials   (to 0.10)
#   C  C bi-Cayley lift search, then grown and saturated                 (to 0.55)
#   L  Python voltage-lift annealer (parent)                             (to 0.70)
#   S  LNS from the best valid graph                                     (to 0.83)
#   P  redundant-edge pruning and regrowth                               (to 0.90)
# Every kept graph passes lib.is_valid. The Haar fallback is always valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    L = float(time_limit)

    def at(f):
        return t0 + f * L

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    fallback = lib.haar_graph(d, range(d))
    if not lib.is_valid(fallback[0], fallback[1], d, D):
        fallback = (1, [])
    best_n, best_e = fallback

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)
            return True
        return False

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase A: structured base, grown; then twin/grow trials.
    base = None
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        n1, e1 = _grow(n0, e0, d, D, at(0.06), rng)
        consider(n1, e1)
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)
    if D >= 2:
        trial_end = at(0.10)
        while time.monotonic() < trial_end:
            n, e = _trial(best_n, list(best_e), d, D, rng, trial_end)
            consider(n, e)
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase C: C bi-Cayley lift search (about 2 s reserved for compiling).
    c_budget = at(0.55) - time.monotonic() - 1.5
    if D >= 2 and c_budget > 3.0:
        res = _c_lift(d, D, best_n, rng.randrange(1, 10 ** 6), c_budget)
        if res is not None:
            n, e = res
            consider(n, e)
            n2, e2 = _grow(n, _saturate_edges(n, e, d, rng), d, D, at(0.70), rng)
            consider(n2, e2)
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase L: Python voltage lifts (parked runs are resumed).
    if D >= 2 and time.monotonic() < at(0.70):
        _lift_phase(d, D, lambda: best_n, at(0.70), rng, consider)
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase S: LNS from the best valid graph.
    if D >= 2 and time.monotonic() < at(0.83):
        _lns(best_n, best_e, d, D, at(0.83), rng, consider)

    # Phase P: prune redundant edges and regrow.
    if D >= 2 and time.monotonic() < at(0.90):
        _prune_regrow(best_n, best_e, d, D, at(0.90), rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)
