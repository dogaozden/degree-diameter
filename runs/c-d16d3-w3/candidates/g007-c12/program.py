"""Diameter-3 bi-Cayley search: regular bipartite graphs from difference covers in groups.

Construction: for a finite group G of order m and a d-subset S of G, the bipartite graph with
vertices a_g, b_g (g in G) and edges a_g ~ b_{gs} (s in S) is d-regular on 2m vertices. It has
diameter 3 exactly when S S^{-1} = G and S^{-1} S = G, so m <= d(d-1)+1 and the largest orders
come from near-perfect difference sets. Groups are semidirect products Z_a x| Z_k (cyclic when
k = 1 or a = 1). The C engine searches S by simulated annealing, climbing m upward from a lower
bound, and the Python side keeps the best valid graph among the constructions and the C result.
Fallbacks: conic blow-up of PG(2,q) and Araujo-Pardo/Lopez or projective-plane incidence graphs when
they apply, and K_{d,d}, which is always valid for D >= 2.
"""
import itertools
import time

import lib

C_BICAYLEY = r"""
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 256
#define MAXD 32

static int d, m;
static int MT[MAXM][MAXM];
static int INV[MAXM];
static int GA, GK, GR;
static int S[MAXD];
static int nS;
static int inS[MAXM];
static int cntL[MAXM], cntR[MAXM];
static int U;
static double prtab[64];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int gcd(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long powmod(long b, long e, long mod) {
    long r = 1 % mod;
    b %= mod;
    while (e > 0) {
        if (e & 1) r = r * b % mod;
        b = b * b % mod;
        e >>= 1;
    }
    return r;
}

/* Group Z_a semidirect Z_k with action r: element (A,B) coded as A*k+B, (A,B)(C,E) = (A + r^B C, B+E). */
static void build_group(int a, int k, int r) {
    int pw[MAXM];
    GA = a;
    GK = k;
    GR = r;
    pw[0] = 1 % a;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % a);
    for (int x = 0; x < m; x++)
        for (int y = 0; y < m; y++) {
            int A = x / k, B = x % k, C = y / k, E = y % k;
            MT[x][y] = (int)((A + (long)pw[B] * C) % a) * k + (B + E) % k;
        }
    for (int x = 0; x < m; x++)
        for (int y = 0; y < m; y++)
            if (MT[x][y] == 0) {
                INV[x] = y;
                break;
            }
}

static int choose_group(void) {
    static int ca[4096], ck[4096], cr[4096];
    int cnt = 0;
    for (int k = 1; k <= m; k++) {
        if (m % k) continue;
        int a = m / k;
        if (a == 1) {
            if (cnt < 4096) {
                ca[cnt] = 1;
                ck[cnt] = k;
                cr[cnt] = 0;
                cnt++;
            }
            continue;
        }
        for (int r = 1; r < a; r++) {
            if (gcd(r, a) != 1 || powmod(r, k, a) != 1 % a) continue;
            if (cnt < 4096) {
                ca[cnt] = a;
                ck[cnt] = k;
                cr[cnt] = r;
                cnt++;
            }
        }
    }
    if (!cnt) return 0;
    int i = rndint(cnt);
    build_group(ca[i], ck[i], cr[i]);
    return 1;
}

/* Ordered pair (p,q), p != q, covers L = p q^{-1} and R = p^{-1} q. */
static void upd_pair(int p, int q, int sgn) {
    int L = MT[p][INV[q]];
    int R = MT[INV[p]][q];
    if (sgn > 0) {
        if (cntL[L]++ == 0) U--;
        if (cntR[R]++ == 0) U--;
    } else {
        if (--cntL[L] == 0) U++;
        if (--cntR[R] == 0) U++;
    }
}

static void remove_at(int idx) {
    int s = S[idx];
    for (int i = 0; i < nS; i++) {
        if (i == idx) continue;
        int t = S[i];
        upd_pair(s, t, -1);
        upd_pair(t, s, -1);
    }
    inS[s] = 0;
}

static void insert_at(int idx, int x) {
    for (int i = 0; i < nS; i++) {
        if (i == idx) continue;
        int t = S[i];
        upd_pair(x, t, 1);
        upd_pair(t, x, 1);
    }
    S[idx] = x;
    inS[x] = 1;
}

static void init_random(void) {
    memset(cntL, 0, sizeof(int) * m);
    memset(cntR, 0, sizeof(int) * m);
    memset(inS, 0, sizeof(int) * m);
    U = 2 * (m - 1);
    for (int i = 0; i < nS; i++) {
        int x;
        do x = rndint(m);
        while (inS[x]);
        inS[x] = 1;
        for (int j = 0; j < i; j++) {
            upd_pair(x, S[j], 1);
            upd_pair(S[j], x, 1);
        }
        S[i] = x;
    }
}

/* Propose a new element: often one that covers a currently uncovered difference. */
static int pick_x(void) {
    if (rnd01() < 0.8) {
        for (int tries = 0; tries < 24; tries++) {
            int g = 1 + rndint(m - 1);
            if (cntL[g] && cntR[g]) continue;
            int q = S[rndint(nS)];
            int x = cntL[g] == 0 ? MT[g][q] : MT[q][INV[g]];
            if (!inS[x]) return x;
        }
    }
    return rndint(m);
}

static int sa_run(long steps) {
    for (long it = 0; it < steps; it++) {
        if (U == 0) return 1;
        int idx = rndint(nS);
        int x = pick_x();
        if (inS[x]) continue;
        int s = S[idx];
        int before = U;
        remove_at(idx);
        insert_at(idx, x);
        int delta = U - before;
        if (delta <= 0) continue;
        if (delta < 64 && rnd01() < prtab[delta]) continue;
        remove_at(idx);
        insert_at(idx, s);
    }
    return U == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    int D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int lo = atoi(argv[5]);
    if (d < 3 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    for (int i = 0; i < 64; i++) prtab[i] = exp(-i / 0.5);

    nS = d;
    int mmax = d * (d - 1) + 1;
    if (mmax > MAXM - 1) mmax = MAXM - 1;
    int mm = lo;
    if (mm < d) mm = d;
    double t_end = now() + budget;

    int bestm = 0, bS[MAXD], ba = 0, bk = 0, br = 0;
    while (mm <= mmax) {
        m = mm;
        double rem = t_end - now();
        if (rem <= 0) break;
        double cap = now() + 0.5 * rem;
        int ok = 0;
        while (!ok && now() < cap) {
            if (!choose_group()) break;
            init_random();
            ok = sa_run(400000);
            if (ok) {
                bestm = m;
                memcpy(bS, S, sizeof S);
                ba = GA;
                bk = GK;
                br = GR;
            }
        }
        if (!ok) break;
        mm++;
    }

    if (!bestm) {
        printf("0 0\n");
        return 0;
    }
    m = bestm;
    build_group(ba, bk, br);
    long E = (long)m * d;
    printf("%d %ld\n", 2 * m, E);
    for (int g = 0; g < m; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, m + MT[g][bS[i]]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured starts (fallbacks).
# ----------------------------------------------------------------------------

def known_start(d, D):
    """Projective plane or Araujo-Pardo/Lopez graph when they apply to D = 3."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def conic_blowup(d, D):
    """Twin blow-up of PG(2,q), q = d-3 odd, duplicating conic points and dual-conic lines."""
    q = d - 3
    if D != 3 or q < 3 or q % 2 == 0 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {v: i for i, v in enumerate(pts)}
    m = len(pts)
    conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if any(v not in index for v in conic):
        return None
    arc = [index[v] for v in conic]
    n0, base = lib.projective_plane_incidence(q)
    pcopy = {i: [i] for i in range(m)}
    lcopy = {j: [m + j] for j in range(m)}
    n = n0
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


def starts(d, D):
    out = []
    ks = known_start(d, D)
    if ks is not None:
        out.append(ks)
    cb = conic_blowup(d, D)
    if cb is not None:
        out.append(cb)
    return out


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 85% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.85 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    cands = []
    for g in [fallback] + starts(d, D):
        try:
            if lib.is_valid(g[0], g[1], d, D):
                cands.append(g)
        except Exception:
            pass
    if not cands:
        return 1, []
    best = max(cands, key=lambda g: g[0])

    # Bi-Cayley search: only graphs with more than best[0] vertices matter, so m >= best/2 + 1.
    lo = best[0] // 2 + 1
    remaining = hard_end - time.monotonic()
    if D >= 3 and remaining > 4.0:
        budget = remaining - 2.5
        try:
            text = lib.run_c(C_BICAYLEY, [d, D, seed, f"{budget:.2f}", lo],
                             timeout=budget + 8.0)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
