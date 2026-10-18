"""Bi-Cayley group-lift search over PSL(2,p) and PGL(2,p), replacing the earlier bi-Cayley search.

Vertices are A_g and B_h for g, h in a finite group G. A connection set S = {s_1..s_d} in G gives
edges A_g ~ B_{g s}. Left multiplication is an automorphism, so the diameter test only needs BFS
from A_e and from B_e. The C engine anneals S for each candidate group, largest expected first.
Fallbacks: K_{d,d}, projective-plane incidence graphs for D = 3, and W(q) for D = 4. Every
returned graph is checked with lib.is_valid.
"""
import itertools
import math
import time

import lib


C_SOURCE = r'''
/* Single-orbit bi-Cayley search over PGL(2,p) or PSL(2,p).
 * Usage:  prog d D seed time_limit p type      (type 0 = PGL, 1 = PSL; p prime 5..37)
 * stdout: "n m" + edges of a valid graph, or "0 0" if none was found in time.
 *
 * Group elements are normalized 2x2 matrices over GF(p). PSL is the subgroup of matrices
 * whose determinant is a square. Vertices 0..G-1 are A_g, G..2G-1 are B_h.
 * A_g ~ B_{g s_j} for j = 0..d-1, with distinct s_j, so the graph is simple and d-regular.
 * Validity: BFS to depth D from A_e and from B_e reaches every vertex.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 16000
#define MAXD 40

static int P, G, DD, DIAM, ident;
static int mat[MAXG][4];
static int inv_el[MAXG];
static int *idx_of;
static int inv_mod[64];
static int S[MAXD];
static int nbA[MAXD][MAXG];   /* A_g -> vertex index of B_{g*s_j} */
static int nbB[MAXD][MAXG];   /* B_h -> vertex index of A_{h*s_j^-1} */
static int bakA[MAXG], bakB[MAXG];
static int vis[2 * MAXG];
static int qa[2 * MAXG], qb[2 * MAXG];
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

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

static int pw_mod(int a, int e, int m) {
    long long r = 1, b = a % m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return (int)r;
}

static int key_of(const int *r) {
    return ((r[0] * P + r[1]) * P + r[2]) * P + r[3];
}

/* Scale a nonzero matrix so its first nonzero entry is 1, then return its element index. */
static int lookup_norm(int *r) {
    int k = 0;
    while (k < 4 && r[k] == 0) k++;
    if (k == 4) return -1;
    int f = inv_mod[r[k]];
    for (int i = 0; i < 4; i++) r[i] = r[i] * f % P;
    return idx_of[key_of(r)];
}

static int mul(int x, int y) {
    const int *A = mat[x], *B = mat[y];
    int r[4];
    r[0] = (A[0] * B[0] + A[1] * B[2]) % P;
    r[1] = (A[0] * B[1] + A[1] * B[3]) % P;
    r[2] = (A[2] * B[0] + A[3] * B[2]) % P;
    r[3] = (A[2] * B[1] + A[3] * B[3]) % P;
    return lookup_norm(r);
}

static int inverse(int x) {
    const int *A = mat[x];
    int r[4] = {A[3], (P - A[1]) % P, (P - A[2]) % P, A[0]};
    return lookup_norm(r);
}

static int build_group(int typ) {
    long total = (long)P * P * P * P;
    idx_of = malloc(sizeof(int) * (size_t)total);
    if (!idx_of) return 0;
    for (long i = 0; i < total; i++) idx_of[i] = -1;
    G = 0;
    for (int a = 0; a < P; a++)
    for (int b = 0; b < P; b++)
    for (int c = 0; c < P; c++)
    for (int e = 0; e < P; e++) {
        int r[4] = {a, b, c, e};
        int k = 0;
        while (k < 4 && r[k] == 0) k++;
        if (k == 4 || r[k] != 1) continue;
        int det = ((a * e - b * c) % P + P) % P;
        if (det == 0) continue;
        if (typ == 1 && pw_mod(det, (P - 1) / 2, P) != 1) continue;
        if (G >= MAXG) return 0;
        mat[G][0] = a;
        mat[G][1] = b;
        mat[G][2] = c;
        mat[G][3] = e;
        idx_of[key_of(r)] = G;
        G++;
    }
    for (int x = 0; x < G; x++) {
        inv_el[x] = inverse(x);
        if (inv_el[x] < 0) return 0;
    }
    int one[4] = {1, 0, 0, 1};
    ident = idx_of[key_of(one)];
    return ident >= 0;
}

static void set_column(int j, int s) {
    int si = inv_el[s];
    S[j] = s;
    for (int g = 0; g < G; g++) {
        nbA[j][g] = G + mul(g, s);
        nbB[j][g] = mul(g, si);
    }
}

static int bfs_count(int src) {
    stamp++;
    int cnt = 1;
    int *cur = qa, *nxt = qb;
    int nc = 1;
    cur[0] = src;
    vis[src] = stamp;
    for (int lev = 0; lev < DIAM; lev++) {
        int nn = 0;
        for (int i = 0; i < nc; i++) {
            int v = cur[i];
            if (v < G) {
                for (int j = 0; j < DD; j++) {
                    int u = nbA[j][v];
                    if (vis[u] != stamp) { vis[u] = stamp; nxt[nn++] = u; }
                }
            } else {
                int h = v - G;
                for (int j = 0; j < DD; j++) {
                    int u = nbB[j][h];
                    if (vis[u] != stamp) { vis[u] = stamp; nxt[nn++] = u; }
                }
            }
        }
        if (nn == 0) break;
        cnt += nn;
        int *t = cur; cur = nxt; nxt = t;
        nc = nn;
    }
    return cnt;
}

static int total_cost(void) {
    return (2 * G - bfs_count(ident)) + (2 * G - bfs_count(G + ident));
}

static int in_set_except(int s, int j) {
    for (int k = 0; k < DD; k++)
        if (k != j && S[k] == s) return 1;
    return 0;
}

static void randomize_all(void) {
    for (int j = 0; j < DD; j++) {
        int s;
        do { s = rndint(G); } while (in_set_except(s, j));
        set_column(j, s);
    }
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: %s d D seed time p type\n", argv[0]);
        return 2;
    }
    int d = atoi(argv[1]), D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int p = atoi(argv[5]), typ = atoi(argv[6]);
    double t0 = now();
    double tend = t0 + limit * 0.9 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2 || p < 5 || p > 37 || (typ != 0 && typ != 1)) {
        printf("0 0\n");
        return 0;
    }
    for (int q = 2; q * q <= p; q++)
        if (p % q == 0) { printf("0 0\n"); return 0; }

    P = p;
    DD = d;
    DIAM = D;
    for (int v = 1; v < P; v++) inv_mod[v] = pw_mod(v, P - 2, P);
    if (!build_group(typ) || G < d + 2) {
        printf("0 0\n");
        return 0;
    }
    for (int j = 0; j < DD; j++) S[j] = -1;
    randomize_all();
    int cost = total_cost();
    int best = cost;
    long it = 0, last_imp = 0;
    double span = tend - t0;
    if (span < 0.05) span = 0.05;
    double T = 3.0;

    while (cost > 0) {
        if ((it & 31) == 0) {
            double tn = now();
            if (tn > tend) break;
            double f = (tn - t0) / span;
            if (f > 1.0) f = 1.0;
            T = 3.0 * pow(0.1, f);
        }
        it++;
        if (it - last_imp > 15000) {
            randomize_all();
            cost = total_cost();
            best = cost;
            last_imp = it;
            continue;
        }
        int j = rndint(DD);
        int s = rndint(G);
        if (s == S[j] || in_set_except(s, j)) continue;
        int old = S[j];
        memcpy(bakA, nbA[j], sizeof(int) * G);
        memcpy(bakB, nbB[j], sizeof(int) * G);
        set_column(j, s);
        int c2 = total_cost();
        if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) {
            cost = c2;
            if (cost < best) { best = cost; last_imp = it; }
        } else {
            S[j] = old;
            memcpy(nbA[j], bakA, sizeof(int) * G);
            memcpy(nbB[j], bakB, sizeof(int) * G);
        }
    }

    if (cost != 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %ld\n", 2 * G, (long)G * DD);
    for (int g = 0; g < G; g++)
        for (int j = 0; j < DD; j++)
            printf("%d %d\n", g, nbA[j][g]);
    return 0;
}
'''


_MAX_D_GROUP = 40
_MAX_GROUP = 15000
# Heuristic cut: a random group lift with about this many expected unreached vertices is hopeless.
_MAX_EXPECTED_UNCOVERED = 300.0


def _is_prime(p):
    return p >= 2 and all(p % r for r in range(2, int(p ** 0.5) + 1))


_PRIMES = [p for p in range(5, 38) if _is_prime(p)]


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


def _expected_uncovered(d, D, G):
    """Poisson-style estimate of unreached vertices for a random single-orbit lift on order G."""
    walks_even = 1 + sum(d * (d - 1) ** (L - 1) for L in range(2, D, 2))
    walks_odd = sum(d * (d - 1) ** (L - 1) for L in range(1, D + 1, 2))
    w = min(walks_even, walks_odd)
    return G * math.exp(-w / G)


def _group_candidates(d, D, lower, cap):
    """PSL(2,p) and PGL(2,p) orders worth trying, largest first, with 2G in (lower, cap]."""
    out = []
    for p in _PRIMES:
        base = p * (p * p - 1)
        for typ, G in ((0, base), (1, base // 2)):
            if G < d + 2 or G > _MAX_GROUP or 2 * G <= lower or 2 * G > cap:
                continue
            if _expected_uncovered(d, D, G) > _MAX_EXPECTED_UNCOVERED:
                continue
            out.append((G, p, typ))
    out.sort(reverse=True)
    return out


def _group_search(d, D, seed, deadline, lower, consider):
    """Try candidate groups in order; stop at the first valid graph that is accepted."""
    if d < 2 or d > _MAX_D_GROUP or D < 3:
        return
    cap = min(lib.moore_bound(d, D), 2 * _MAX_GROUP)
    for idx, (G, p, typ) in enumerate(_group_candidates(d, D, lower, cap)):
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            return
        budget = remaining * 0.5
        budget = min(max(budget, 2.0), remaining - 0.5)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed * 7 + idx, round(budget, 2), p, typ],
                             timeout=budget + 10.0)
            n, edges = lib.parse_graph_text(text)
        except Exception:
            continue
        if n > 1 and consider(n, edges):
            return


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D == 2:
        return best

    # Exact constructions (calibration cases return immediately).
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
    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Group-lift search. Reserve time for the final lib.is_valid check on large outputs.
    total = max(1.0, 0.85 * time_limit - 3.0)
    deadline = t0 + total
    try:
        _group_search(d, D, seed, deadline, best_n, consider)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
