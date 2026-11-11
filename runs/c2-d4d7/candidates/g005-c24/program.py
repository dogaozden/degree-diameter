"""Haar-graph group search for the weakest case (d = 4, D = 7).

Changed in this version: the C engine no longer lifts or grows graphs. It takes a
group G of order N and a connection set S of d elements, and builds the bipartite
Haar graph H(G, S) on 2N vertices: a_x ~ b_{xs} for s in S. Left multiplication is an
automorphism, so the diameter test needs only two BFS runs, from a_e and b_e. Groups
come from two families: semidirect products Z_m x| Z_k, and SL(2,p) (p = 5, 7), SL(2,8)
and their direct products with cyclic groups. The nonabelian families are new here.
S is found by hill climbing. Every result is verified in C by BFS from all vertices,
and again in Python with lib.is_valid. The algebraic starts (H(3) incidence graph,
W(q) incidence graph, projective planes, K_{d,d}) are kept as the fallback.
"""
import time

import itertools

import lib

MAXD = 16

C_SOURCE = r'''
/* Haar-graph search over finite groups.
 * Usage: prog d D seed time_limit min_vertices
 * Output: "n m" then m edges "u v" of the largest verified Haar graph with
 * n > min_vertices, or "0 0" if none was found.
 * Vertices: a_x = x (0 <= x < N), b_y = N + y. Edge a_x ~ b_{x*s} for s in S.
 */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1100
#define MAXD 16

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
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

/* Current group: T[x*N+y] = x*y, INV[x], identity IDEN. */
static int N, IDEN;
static unsigned short T[MAXG * MAXG];
static unsigned short BASE[512 * 512];
static int INV[MAXG];

/* Semidirect Z_m x| Z_k: element a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
static void build_semidirect(int m, int k, int r) {
    static int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    N = m * k;
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            T[x * N + y] = (unsigned short)((((long)a + (long)rp[b] * c) % m) * k + (b + e) % k);
        }
    }
}

/* Field arithmetic for GF(5), GF(7) and GF(8). */
static int Fq, Fc2;
static int fadd(int a, int b) { return Fc2 ? (a ^ b) : (a + b) % Fq; }
static int fneg(int a) { return Fc2 ? a : (Fq - a) % Fq; }
static int fmul(int a, int b) {
    if (!Fc2) return a * b % Fq;
    int r = 0;
    for (int i = 0; i < 3; i++) if ((b >> i) & 1) r ^= a << i;
    for (int i = 4; i >= 3; i--) if ((r >> i) & 1) r ^= 0xB << (i - 3);  /* x^3 + x + 1 */
    return r;
}

static int codeidx[4096];
static int EL[512][4];

/* SL(2,q) x Z_cm with q chosen by kind: 0 -> 5, 1 -> 7, 2 -> 8. */
static void build_sl(int kind, int cm) {
    Fq = kind == 0 ? 5 : kind == 1 ? 7 : 8;
    Fc2 = kind == 2;
    int q = Fq, nb = 0;
    for (int i = 0; i < 4096; i++) codeidx[i] = -1;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int e = 0; e < q; e++) {
                    if (fadd(fmul(a, e), fneg(fmul(b, c))) != 1) continue;
                    codeidx[((a * q + b) * q + c) * q + e] = nb;
                    EL[nb][0] = a; EL[nb][1] = b; EL[nb][2] = c; EL[nb][3] = e;
                    nb++;
                }
    for (int x = 0; x < nb; x++)
        for (int y = 0; y < nb; y++) {
            int a = EL[x][0], b = EL[x][1], c = EL[x][2], e = EL[x][3];
            int f = EL[y][0], g = EL[y][1], h = EL[y][2], k = EL[y][3];
            int p0 = fadd(fmul(a, f), fmul(b, h));
            int p1 = fadd(fmul(a, g), fmul(b, k));
            int p2 = fadd(fmul(c, f), fmul(e, h));
            int p3 = fadd(fmul(c, g), fmul(e, k));
            BASE[x * nb + y] = (unsigned short)codeidx[((p0 * q + p1) * q + p2) * q + p3];
        }
    N = nb * cm;
    for (int x = 0; x < nb; x++)
        for (int i = 0; i < cm; i++)
            for (int y = 0; y < nb; y++)
                for (int j = 0; j < cm; j++)
                    T[(x * cm + i) * N + (y * cm + j)] =
                        (unsigned short)(BASE[x * nb + y] * cm + (i + j) % cm);
}

static int setup_group(void) {
    IDEN = -1;
    for (int e = 0; e < N && IDEN < 0; e++) {
        int ok = 1;
        for (int x = 0; x < N && ok; x++) if (T[e * N + x] != x) ok = 0;
        if (ok) IDEN = e;
    }
    if (IDEN < 0) return 0;
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++)
            if (T[x * N + y] == IDEN) { INV[x] = y; break; }
        if (INV[x] < 0) return 0;
    }
    return 1;
}

/* Choose a random group with order in [lo, hi]. */
static int make_group(int lo, int hi) {
    int kind[32], mult[32], nc = 0;
    static const int base[3] = {120, 336, 504};
    for (int t = 0; t < 3; t++)
        for (int c = 1; c * base[t] <= hi; c++)
            if (c * base[t] >= lo && nc < 32) { kind[nc] = t; mult[nc] = c; nc++; }
    if (nc && rnd01() < 0.6) {
        int t = rndint(nc);
        build_sl(kind[t], mult[t]);
        return 1;
    }
    int span = hi - lo;
    if (rnd01() < 0.5 && span > 60) span = 60;
    int Nn = lo + rndint(span + 1);
    int bm = 1, bk = Nn, br = 0;
    long cnt = 0;
    for (int m = 1; m <= Nn; m++) {
        if (Nn % m) continue;
        int k = Nn / m;
        int r0 = m > 1 ? 1 : 0, r1 = m > 1 ? m : 1;
        for (int r = r0; r < r1; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)(cnt < 2000000000L ? cnt : 2000000000L)) == 0) {
                bm = m; bk = k; br = r;
            }
        }
    }
    build_semidirect(bm, bk, br);
    return 1;
}

static int Sel[MAXD], SI[MAXD];
static int dist_[2 * MAXG], q_[2 * MAXG];

/* BFS from src, limited to distance D. Returns the number of vertices reached. */
static int bfs(int src) {
    int V = 2 * N;
    for (int v = 0; v < V; v++) dist_[v] = -1;
    int head = 0, tail = 0;
    dist_[src] = 0;
    q_[tail++] = src;
    while (head < tail) {
        int v = q_[head++];
        if (dist_[v] >= D) continue;
        if (v < N) {
            for (int i = 0; i < d; i++) {
                int u = N + T[v * N + Sel[i]];
                if (dist_[u] < 0) { dist_[u] = dist_[v] + 1; q_[tail++] = u; }
            }
        } else {
            int y = v - N;
            for (int i = 0; i < d; i++) {
                int u = T[y * N + SI[i]];
                if (dist_[u] < 0) { dist_[u] = dist_[v] + 1; q_[tail++] = u; }
            }
        }
    }
    return tail;
}

/* Unreached pairs from the two orbit representatives. Zero iff the Haar graph has diameter <= D. */
static int evaluate(void) {
    int V = 2 * N;
    for (int i = 0; i < d; i++) SI[i] = INV[Sel[i]];
    return (V - bfs(IDEN)) + (V - bfs(N + IDEN));
}

static int in_sel(int g, int upto) {
    for (int i = 0; i < upto; i++) if (Sel[i] == g) return 1;
    return 0;
}

static void random_sel(void) {
    for (int i = 0; i < d; i++) {
        int g;
        do g = rndint(N); while (in_sel(g, i));
        Sel[i] = g;
    }
}

static int climb(int steps, double until) {
    random_sel();
    int bad = evaluate();
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 127) == 127 && now() > until) break;
        if (s % 1500 == 1499) { random_sel(); bad = evaluate(); continue; }
        int i = rndint(d), old = Sel[i];
        int g;
        do g = rndint(N); while (in_sel(g, d));
        Sel[i] = g;
        int nb = evaluate();
        if (nb <= bad || rnd01() < 0.01) bad = nb;
        else Sel[i] = old;
    }
    return bad == 0;
}

/* Full check: BFS from every vertex. */
static int verify_full(void) {
    int V = 2 * N;
    for (int i = 0; i < d; i++) SI[i] = INV[Sel[i]];
    for (int src = 0; src < V; src++)
        if (bfs(src) != V) return 0;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit min_vertices\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int minn = argc > 5 ? atoi(argv[5]) : 0;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    t_end = now() + limit * 0.92;

    if (d < 1 || d > MAXD || D < 1) { printf("0 0\n"); return 0; }

    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    long moore = d == 1 ? 2 : 2 * s;
    int hi = (int)(moore / 2);
    if (hi > MAXG) hi = MAXG;
    int lo = minn / 2 + 1;
    if (lo < d) lo = d;
    if (lo < 2) lo = 2;

    static unsigned short BESTT[MAXG * MAXG];
    int BESTS[MAXD];
    int bestN = 0;

    while (now() < t_end && lo <= hi) {
        if (!make_group(lo, hi)) break;
        if (!setup_group()) continue;
        double until = now() + 2.5;
        if (until > t_end) until = t_end;
        if (climb(6000, until) && verify_full()) {
            bestN = N;
            memcpy(BESTT, T, sizeof(unsigned short) * (size_t)N * N);
            for (int i = 0; i < d; i++) BESTS[i] = Sel[i];
            lo = N + 1;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %ld\n", 2 * bestN, (long)bestN * d);
    for (int x = 0; x < bestN; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, bestN + BESTT[x * bestN + BESTS[i]]);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _h3_lines(pts, index, s):
    """Lines of H(3) from Tits' description, with the right-hand sign multiplier s (1 or 2 mod 3)."""
    P = len(pts)

    def bil(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1]
                + x[2] * y[6] + x[6] * y[2] - 2 * x[3] * y[3]) % 3

    def norm(v):
        c = next(t for t in v if t)
        inv = 1 if c == 1 else 2
        return tuple((t * inv) % 3 for t in v)

    lines = set()
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            y = pts[j]
            if bil(x, y):
                continue

            def pl(a, b):
                return (x[a] * y[b] - x[b] * y[a]) % 3

            conds = [(pl(1, 2), pl(3, 4)), (pl(5, 4), pl(3, 2)), (pl(2, 0), pl(3, 5)),
                     (pl(6, 5), pl(3, 0)), (pl(0, 1), pl(3, 6)), (pl(4, 6), pl(3, 1))]
            if any((a - s * b) % 3 for a, b in conds):
                continue
            L = set()
            for a in range(3):
                for b in range(3):
                    if a == 0 and b == 0:
                        continue
                    v = tuple((a * x[k] + b * y[k]) % 3 for k in range(7))
                    if any(v):
                        L.add(index[norm(v)])
            if len(L) == 4:
                lines.add(tuple(sorted(L)))
    return lines


def _hexagon_h3():
    """Incidence graph of the split Cayley hexagon H(3): 728 vertices, 4-regular, diameter 6.

    Both sign conventions are tried, and the result is accepted only if lib.is_valid
    confirms it. Returns (n, edges) or None.
    """
    pts = []
    for v in itertools.product(range(3), repeat=7):
        if not any(v):
            continue
        if v[next(i for i, c in enumerate(v) if c)] != 1:
            continue
        if (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % 3:
            continue
        pts.append(v)
    P = len(pts)
    if P != 364:
        return None
    index = {v: i for i, v in enumerate(pts)}
    for s in (1, 2):
        lines = _h3_lines(pts, index, s)
        if len(lines) != P:
            continue
        lines = sorted(lines)
        edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
        if lib.is_valid(2 * P, edges, 4, 6):
            return 2 * P, edges
    return None


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d == 4 and D >= 6:
        try:
            hexg = _hexagon_h3()
        except Exception:
            hexg = None
        if hexg is not None and hexg[0] > best[0] and lib.is_valid(hexg[0], hexg[1], d, D):
            best = hexg

    if d > MAXD or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         stdin_graph=None, timeout=budget + 5)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
