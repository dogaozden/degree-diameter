import time

import lib


# ----------------------------------------------------------------------------
# Strategy: bi-Cayley lifts over semidirect products Z_m x| Z_k2 with a C
# annealer. A lift has 2K blocks of size G (K per side). Dart layer l joins
# A-block i to B-block sig[l][i] with voltage S[l][i], so each vertex gets one
# neighbour per layer. Left multiplication is an automorphism, so it suffices
# to check that every block identity reaches every vertex within D steps. The
# cost counts unreached (vertex, source-block) pairs, updated with bitset
# expansion in C. The C engine keeps restarting with new group orders just
# above the best valid order so far.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define NMAX 100000
#define KMAXL 8

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double T_START = 0.0;
static double now_raw(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}
static double elapsed(void) { return now_raw() - T_START; }

static int DEG, DIA;          /* degree bound, diameter bound */
static int K;                 /* blocks per side */
static int G;                 /* group order */
static int MM, K2, RR;        /* group Z_MM x| Z_K2, r = RR */
static int NN;                /* current vertex count 2*K*G */
static int pw[64];            /* pw[b] = RR^b mod MM */

static int *sig, *isig, *Sv, *Svinv, *nbr;
static unsigned *bufA, *bufB;
static int *bu, *bv;
static int best_n = 0, best_m = 0, have = 0;

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int powmod_(long long b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* Element (a,b) is coded a*K2+b. (a,b)(c,e) = (a + r^b c, b+e). */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    long long t = ((long long)a + (long long)pw[b] * c) % MM;
    return (int)(t * K2 + (b + e) % K2);
}

/* Inverse of (a,b) is (-r^(-b) a, -b). */
static int ginv(int s) {
    int a = s / K2, b = s % K2;
    int nb = (K2 - b) % K2;
    long long t = ((long long)pw[nb] * a) % MM;
    int ia = (int)((MM - t) % MM);
    return ia * K2 + nb;
}

static void set_isig(int l) {
    for (int i = 0; i < K; i++) isig[l * K + sig[l * K + i]] = i;
}

/* Vertex (i,g) for A-block i joins (K+j, g*s); vertex (K+j,h) joins (i, h*s^-1). */
static void rebuild_layer(int l) {
    int *nb = nbr + (size_t)l * NN;
    for (int i = 0; i < K; i++) {
        int j = sig[l * K + i], s = Sv[l * K + i];
        for (int g = 0; g < G; g++) nb[i * G + g] = (K + j) * G + gmul(g, s);
    }
    for (int j = 0; j < K; j++) {
        int i = isig[l * K + j], si = Svinv[l * K + i];
        for (int h = 0; h < G; h++) nb[(K + j) * G + h] = i * G + gmul(h, si);
    }
}

static void random_config(void) {
    for (int l = 0; l < DEG; l++) {
        int *sg = sig + l * K;
        for (int i = 0; i < K; i++) sg[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = sg[i]; sg[i] = sg[j]; sg[j] = t;
        }
        for (int i = 0; i < K; i++) {
            int s = rint_(G);
            Sv[l * K + i] = s;
            Svinv[l * K + i] = ginv(s);
        }
        set_isig(l);
        rebuild_layer(l);
    }
}

/* Sum over vertices of unreached source blocks. Zero means valid. */
static int eval_cost(void) {
    unsigned *a = bufA, *b = bufB;
    for (int v = 0; v < NN; v++) a[v] = 0;
    for (int blk = 0; blk < 2 * K; blk++) a[blk * G] = 1u << blk;
    for (int t = 0; t < DIA; t++) {
        int changed = 0;
        for (int v = 0; v < NN; v++) {
            unsigned x = a[v];
            for (int l = 0; l < DEG; l++) x |= a[nbr[(size_t)l * NN + v]];
            b[v] = x;
            changed |= (x != a[v]);
        }
        unsigned *tmp = a; a = b; b = tmp;
        if (!changed) break;
    }
    long cost = 0;
    for (int v = 0; v < NN; v++) cost += 2 * K - __builtin_popcount(a[v]);
    return (int)cost;
}

static void save_graph(void) {
    int m = 0;
    int A = K * G;
    for (int v = 0; v < A; v++) {
        for (int l = 0; l < DEG; l++) {
            int u = nbr[(size_t)l * NN + v];
            int dup = 0;
            for (int l2 = 0; l2 < l; l2++) {
                if (nbr[(size_t)l2 * NN + v] == u) { dup = 1; break; }
            }
            if (!dup) { bu[m] = v; bv[m] = u; m++; }
        }
    }
    best_n = NN;
    best_m = m;
    have = 1;
}

/* One annealing run for a fixed group. Returns 1 if a valid lift was found. */
static int run_trial(double secs, double global_end) {
    random_config();
    int cost = eval_cost();
    if (cost == 0) { save_graph(); return 1; }
    double t0 = elapsed();
    double tend = t0 + secs;
    if (tend > global_end) tend = global_end;
    double span = tend - t0;
    if (span < 1e-3) span = 1e-3;
    const double T0 = 6.0, T1 = 0.2;

    while (1) {
        double now = elapsed();
        if (now >= tend) break;
        double T = T0 * pow(T1 / T0, (now - t0) / span);
        int l = rint_(DEG);
        if (K >= 2 && rdbl() < 0.25) {
            int *sg = sig + l * K;
            int i1 = rint_(K), i2 = rint_(K - 1);
            if (i2 >= i1) i2++;
            int t = sg[i1]; sg[i1] = sg[i2]; sg[i2] = t;
            set_isig(l);
            rebuild_layer(l);
            int c2 = eval_cost();
            int delta = c2 - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = c2;
            } else {
                t = sg[i1]; sg[i1] = sg[i2]; sg[i2] = t;
                set_isig(l);
                rebuild_layer(l);
            }
        } else {
            int idx = l * K + rint_(K);
            int ns = rint_(G);
            int old = Sv[idx], oldinv = Svinv[idx];
            if (ns == old) continue;
            Sv[idx] = ns;
            Svinv[idx] = ginv(ns);
            rebuild_layer(l);
            int c2 = eval_cost();
            int delta = c2 - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = c2;
            } else {
                Sv[idx] = old;
                Svinv[idx] = oldinv;
                rebuild_layer(l);
            }
        }
        if (cost == 0) { save_graph(); return 1; }
    }
    return 0;
}

int main(int argc, char **argv) {
    T_START = now_raw();
    if (argc < 5) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIA = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    int min_n = argc > 5 ? atoi(argv[5]) : 0;
    if (DEG < 1 || DEG > 64 || DIA < 1) { printf("0 0\n"); return 0; }

    sig = malloc(sizeof(int) * DEG * KMAXL);
    isig = malloc(sizeof(int) * DEG * KMAXL);
    Sv = malloc(sizeof(int) * DEG * KMAXL);
    Svinv = malloc(sizeof(int) * DEG * KMAXL);
    nbr = malloc(sizeof(int) * (size_t)DEG * NMAX);
    bufA = malloc(sizeof(unsigned) * NMAX);
    bufB = malloc(sizeof(unsigned) * NMAX);
    bu = malloc(sizeof(int) * (size_t)NMAX * DEG);
    bv = malloc(sizeof(int) * (size_t)NMAX * DEG);
    if (!sig || !isig || !Sv || !Svinv || !nbr || !bufA || !bufB || !bu || !bv) {
        printf("0 0\n");
        return 0;
    }

    best_n = min_n;
    static const int k2list[15] = {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24};
    int fails = 0;

    while (1) {
        double remaining = limit - elapsed();
        if (remaining < 0.3) break;

        K = 2 + rint_(5);                       /* 2..6 blocks per side */
        int Gmin = best_n / (2 * K) + 1;
        int Gt = Gmin + (int)(Gmin * rdbl() * 0.06);
        K2 = k2list[rint_(15)];
        MM = (Gt + K2 - 1) / K2;
        if (MM < 2) MM = 2;
        RR = 1;
        if (K2 >= 2 && MM >= 3 && rdbl() < 0.7) {
            for (int tr = 0; tr < 200; tr++) {
                int c = 2 + rint_(MM - 2);
                if (gcd_(c, MM) == 1 && powmod_(c, K2, MM) == 1 % MM) { RR = c; break; }
            }
        }
        G = MM * K2;
        NN = 2 * K * G;
        if (NN > NMAX) { fails++; if (fails > 12) fails = 12; continue; }

        pw[0] = 1 % MM;
        for (int b = 1; b < K2; b++) pw[b] = (int)((long long)pw[b - 1] * RR % MM);

        double tl = 3.0 + 0.5 * fails;
        if (tl > remaining) tl = remaining;
        int ok = run_trial(tl, limit);
        if (ok) fails = 0;
        else { fails++; if (fails > 12) fails = 12; }
    }

    if (!have) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bu[i], bv[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    # Main search: C lift annealer over semidirect-product groups.
    budget = max(1.0, min(0.85 * time_limit, time_limit - 7.0))
    remaining = budget - (time.monotonic() - t0)
    if remaining >= 1.0:
        cseed = (seed * 1000003 + 97) % (1 << 31) or 1
        try:
            out = lib.run_c(C_SOURCE, [d, D, cseed, f"{remaining:.2f}", best[0]],
                            stdin_graph=None, timeout=remaining + 15.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
