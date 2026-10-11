import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: vertex-transitive group-lift search with fast evaluation.
#
# A lift over a semidirect product G = Z_m x| Z_k2 of a d-regular bipartite base
# (k vertices per side, d permutations, voltages in G) is vertex-transitive on each
# side, because left translation by G is an automorphism. So the diameter is
# checked by BFS from only the 2k base vertices. Each evaluation costs tens of
# microseconds, which allows far more hill-climbing than the Python version.
# Duplicate darts are penalized. Every accepted graph is re-verified in full.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAX_G 1500

static uint64_t rs = 0x2545F4914F6CDD1DULL;
static double t_end = 0.0;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) {
    if (n <= 1) return 0;
    return (int)(nextr() % (uint64_t)n);
}

static double cpu_sec(void) {
    return (double)clock() / (double)CLOCKS_PER_SEC;
}

static long long powmod_ll(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long long gcd_ll(long long a, long long b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/* Full check: vertices 0..n-1, m edges, max degree <= d, simple, bipartite, diameter <= D. */
static int verify_graph(int n, int m, const int *eu, const int *ev, int d, int D) {
    int ok = 0;
    int *deg, *off, *pos, *nb, *col, *dist, *q;
    if (n < 1 || m < 0) return 0;
    deg = calloc((size_t)n, sizeof(int));
    off = malloc(((size_t)n + 1) * sizeof(int));
    pos = malloc(((size_t)n + 1) * sizeof(int));
    nb = malloc((2 * (size_t)m + 1) * sizeof(int));
    col = malloc((size_t)n * sizeof(int));
    dist = malloc((size_t)n * sizeof(int));
    q = malloc((size_t)n * sizeof(int));
    if (!deg || !off || !pos || !nb || !col || !dist || !q) goto done;
    for (int e = 0; e < m; e++) {
        int a = eu[e], b = ev[e];
        if (a < 0 || a >= n || b < 0 || b >= n || a == b) goto done;
        deg[a]++;
        deg[b]++;
    }
    for (int v = 0; v < n; v++)
        if (deg[v] > d) goto done;
    off[0] = 0;
    for (int v = 0; v < n; v++) {
        off[v + 1] = off[v] + deg[v];
        pos[v] = off[v];
    }
    for (int e = 0; e < m; e++) {
        nb[pos[eu[e]]++] = ev[e];
        nb[pos[ev[e]]++] = eu[e];
    }
    for (int v = 0; v < n; v++)
        for (int a = off[v]; a < off[v + 1]; a++)
            for (int b = a + 1; b < off[v + 1]; b++)
                if (nb[a] == nb[b]) goto done;
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        int h = 0, t = 0;
        col[s] = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int a = off[u]; a < off[u + 1]; a++) {
                int w = nb[a];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    q[t++] = w;
                } else if (col[w] == col[u]) {
                    goto done;
                }
            }
        }
    }
    for (int s = 0; s < n; s++) {
        int h = 0, t = 0, reached = 1;
        for (int v = 0; v < n; v++) dist[v] = -1;
        dist[s] = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            if (dist[u] >= D) continue;
            for (int a = off[u]; a < off[u + 1]; a++) {
                int w = nb[a];
                if (dist[w] < 0) {
                    dist[w] = dist[u] + 1;
                    reached++;
                    q[t++] = w;
                }
            }
        }
        if (reached != n) goto done;
    }
    ok = 1;
done:
    free(deg);
    free(off);
    free(pos);
    free(nb);
    free(col);
    free(dist);
    free(q);
    return ok;
}

typedef struct {
    int d, D, k, G, m, k2, r;
    int *mt;   /* G*G multiplication table of the group */
    int *P;    /* d*k permutations: P[t*k+i] */
    int *V;    /* d*k voltages */
    int *adj;  /* (2*k*G)*d neighbour slots */
    int *dist, *q;
} Lift;

static void free_lift(Lift *L) {
    free(L->mt);
    free(L->P);
    free(L->V);
    free(L->adj);
    free(L->dist);
    free(L->q);
    L->mt = L->P = L->V = L->adj = L->dist = L->q = NULL;
}

/* Semidirect product Z_m x| Z_k2 with action r: (a,b)*(c,e) = (a + r^b c, b + e). Element (a,b) is coded a*k2+b. */
static int setup_lift(Lift *L, int d, int D, int k, int G, int m, int k2, int r) {
    int n = 2 * k * G;
    L->d = d;
    L->D = D;
    L->k = k;
    L->G = G;
    L->m = m;
    L->k2 = k2;
    L->r = r;
    L->mt = malloc((size_t)G * G * sizeof(int));
    L->P = malloc((size_t)d * k * sizeof(int));
    L->V = malloc((size_t)d * k * sizeof(int));
    L->adj = malloc((size_t)n * d * sizeof(int));
    L->dist = malloc((size_t)n * sizeof(int));
    L->q = malloc((size_t)n * sizeof(int));
    if (!L->mt || !L->P || !L->V || !L->adj || !L->dist || !L->q) return 0;
    int *pw = malloc((size_t)k2 * sizeof(int));
    if (!pw) return 0;
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    for (int x = 0; x < G; x++) {
        for (int y = 0; y < G; y++) {
            int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
            int A = (int)((a + (long long)pw[b] * c) % m);
            int B = (b + e) % k2;
            L->mt[x * G + y] = A * k2 + B;
        }
    }
    free(pw);
    return 1;
}

static int choose_group(int G, int *pm, int *pk2, int *pr) {
    int divs[256], nd = 0;
    for (int q = 1; q <= G && nd < 256; q++)
        if (G % q == 0) divs[nd++] = q;
    for (int tries = 0; tries < 40; tries++) {
        int q = divs[rndint(nd)], m = G / q;
        if (q == 1 || m == 1) {
            *pm = m;
            *pk2 = q;
            *pr = 0;
            return 1;
        }
        for (int tr = 0; tr < 80; tr++) {
            int r = (tr == 79) ? 1 : 1 + rndint(m - 1);
            if (gcd_ll(r, m) == 1 && powmod_ll(r, q, m) == 1 % m) {
                *pm = m;
                *pk2 = q;
                *pr = r;
                return 1;
            }
        }
    }
    return 0;
}

static void randomize_lift(Lift *L) {
    int d = L->d, k = L->k, G = L->G;
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < k; i++) L->P[t * k + i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = L->P[t * k + i];
            L->P[t * k + i] = L->P[t * k + j];
            L->P[t * k + j] = tmp;
        }
        for (int i = 0; i < k; i++) L->V[t * k + i] = rndint(G);
    }
}

/* Cost = pen*n + (unreached pairs from the 2k base vertices). Zero means valid (up to final check). */
static long long eval_lift(Lift *L) {
    int d = L->d, D = L->D, k = L->k, G = L->G, n = 2 * k * G;
    long long pen = 0, bad = 0;
    for (int i = 0; i < k; i++)
        for (int t1 = 0; t1 < d; t1++)
            for (int t2 = t1 + 1; t2 < d; t2++)
                if (L->P[t1 * k + i] == L->P[t2 * k + i] && L->V[t1 * k + i] == L->V[t2 * k + i])
                    pen++;
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < k; i++) {
            int j = k + L->P[t * k + i], g = L->V[t * k + i];
            for (int x = 0; x < G; x++) {
                int u = i * G + x, v = j * G + L->mt[x * G + g];
                L->adj[(size_t)u * d + t] = v;
                L->adj[(size_t)v * d + t] = u;
            }
        }
    }
    for (int s = 0; s < 2 * k; s++) {
        int src = s * G, h = 0, tail = 0, reached = 1;
        for (int v = 0; v < n; v++) L->dist[v] = -1;
        L->dist[src] = 0;
        L->q[tail++] = src;
        while (h < tail) {
            int u = L->q[h++];
            if (L->dist[u] >= D) continue;
            for (int t = 0; t < d; t++) {
                int w = L->adj[(size_t)u * d + t];
                if (L->dist[w] < 0) {
                    L->dist[w] = L->dist[u] + 1;
                    reached++;
                    L->q[tail++] = w;
                }
            }
        }
        bad += n - reached;
    }
    return pen * (long long)n + bad;
}

static long long climb(Lift *L, int iters) {
    int d = L->d, k = L->k, G = L->G;
    long long cur = eval_lift(L);
    for (int it = 0; it < iters && cur > 0; it++) {
        if (cpu_sec() > t_end) break;
        int t = rndint(d), i = rndint(k);
        if (k > 1 && rndint(4) == 0) {
            int i2 = rndint(k);
            if (i2 == i) continue;
            int *p = &L->P[t * k];
            int tmp = p[i];
            p[i] = p[i2];
            p[i2] = tmp;
            long long c = eval_lift(L);
            if (c <= cur) cur = c;
            else {
                tmp = p[i];
                p[i] = p[i2];
                p[i2] = tmp;
            }
        } else {
            if (G < 2) break;
            int idx = t * k + i, old = L->V[idx];
            int nv = rndint(G - 1);
            if (nv >= old) nv++;
            L->V[idx] = nv;
            long long c = eval_lift(L);
            if (c <= cur) cur = c;
            else L->V[idx] = old;
        }
    }
    return cur;
}

static void make_edges(Lift *L, int *eu, int *ev) {
    int d = L->d, k = L->k, G = L->G, idx = 0;
    for (int u = 0; u < k * G; u++)
        for (int t = 0; t < d; t++) {
            eu[idx] = u;
            ev[idx] = L->adj[(size_t)u * d + t];
            idx++;
        }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();
    t_end = 0.9 * tl;

    int n0 = 0, m0 = 0;
    int *bu = NULL, *bv = NULL;
    int best_n = 0, best_m = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    if (n0 > 0 && m0 >= 0) {
        int *su = malloc(((size_t)m0 + 1) * sizeof(int));
        int *sv = malloc(((size_t)m0 + 1) * sizeof(int));
        int good = (su != NULL && sv != NULL);
        for (int e = 0; good && e < m0; e++)
            if (scanf("%d %d", &su[e], &sv[e]) != 2) good = 0;
        if (good && verify_graph(n0, m0, su, sv, d, D)) {
            bu = su;
            bv = sv;
            best_n = n0;
            best_m = m0;
        } else {
            free(su);
            free(sv);
        }
    }

    if (d >= 2 && D >= 2) {
        Lift L;
        memset(&L, 0, sizeof L);
        while (cpu_sec() < t_end) {
            int k = 1 + rndint(6);
            int G = best_n / (2 * k) + 1 + rndint(3);
            if (G > MAX_G) break;
            int m, k2, r;
            if (!choose_group(G, &m, &k2, &r)) continue;
            if (!setup_lift(&L, d, D, k, G, m, k2, r)) {
                free_lift(&L);
                break;
            }
            randomize_lift(&L);
            long long c = climb(&L, 4000);
            if (c == 0) {
                int n = 2 * k * G;
                int me = k * G * d;
                if (n > best_n) {
                    int *cu = malloc(((size_t)me + 1) * sizeof(int));
                    int *cv = malloc(((size_t)me + 1) * sizeof(int));
                    if (cu && cv) {
                        eval_lift(&L);
                        make_edges(&L, cu, cv);
                        if (verify_graph(n, me, cu, cv, d, D)) {
                            free(bu);
                            free(bv);
                            bu = cu;
                            bv = cv;
                            best_n = n;
                            best_m = me;
                            cu = NULL;
                            cv = NULL;
                        }
                    }
                    free(cu);
                    free(cv);
                }
            }
            free_lift(&L);
        }
    }

    printf("%d %d\n", best_n, best_m);
    for (int e = 0; e < best_m; e++) printf("%d %d\n", bu[e], bv[e]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions: projective planes, generalized quadrangles, cover growth.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
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
    """W(q) incidence graph for the largest prime power q <= 16 with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices (optionally randomized)."""
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


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices within D - 1 of spare capacity."""
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
    """Greedily join deficient opposite-side vertices in random order."""
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
    """Extend by cover vertices, then saturate edges with the spare degree."""
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
# Driver: Python builds the base graphs, C searches group lifts for more vertices.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # D >= 3: projective plane, then cover growth in a short Python phase.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, t0 + 0.12 * time_limit, rng)
            consider(n2, e2)

    # D >= 4: generalized quadrangle W(q) with randomized growth restarts.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            ext_deadline = t0 + 0.25 * time_limit
            attempts = 0
            while time.monotonic() < ext_deadline and attempts < 30:
                attempts += 1
                sub = random.Random(rng.randrange(1 << 30))
                n2, e2 = _grow(gq[0], gq[1], d, D, ext_deadline, sub)
                consider(n2, e2)

    # Early exit when the Moore bound is already met (e.g. d=3, D=3 gives 14).
    if best_n >= moore:
        return best

    # C group-lift search, starting from the best graph found so far.
    remaining = time_limit - (time.monotonic() - t0) - 4.0
    if d >= 2 and D >= 2 and remaining > 2.0:
        budget = 0.9 * remaining
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=remaining)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
