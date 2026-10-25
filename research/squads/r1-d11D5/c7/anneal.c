/* c7 anneal: base = W(q) incidence graph (points 0..N-1, lines N..N+L-1) plus K parallel copies of one
   non-incident perfect matching sigma: point p -> line sigma(p). Degree = (q+1) + K. Voltages in Z_M.
   Objective F = #(base source x, lift target (u,h)) with no walk of length <= 5 (same as liftcheck far_pairs),
   computed exactly by a bitmask DP over Z_M (bit s set = some walk of that length has voltage sum s).
   usage: anneal gq.bin M K iters T0 T1 seed out.txt [init.txt]
   out.txt is in liftcheck format: "nA nB M" then "a b v" (a point, b line index, v voltage). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

static uint64_t rs0 = 88172645463325252ULL, rs1 = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnext(void) {
    uint64_t s1 = rs0; const uint64_t s0 = rs1; rs0 = s0;
    s1 ^= s1 << 23; rs1 = s1 ^ s0 ^ (s1 >> 17) ^ (s0 >> 26); return rs1 + s0;
}
static inline double runif(void) { return (rnext() >> 11) * (1.0 / 9007199254740992.0); }
static inline int rint_(int n) { return (int)(rnext() % (uint64_t)n); }

static int Q, Q1, N, L, M, K, R, NB, NE, NFLAG;
static int *lin, *sig, *ea, *eb, *ev;
static uint64_t FULL;
static uint64_t *cur, *nxt, *cov;
static int *srcs, NSRC;   /* sampled sources (annealing objective); full check uses all NB */

static inline uint64_t rot(uint64_t m, int v) {
    if (v == 0) return m;
    return ((m << v) | (m >> (M - v))) & FULL;
}

static long compute_far_list(const int *list, int n) {
    long far = 0;
    for (int si = 0; si < n; si++) {
        int x = list[si];
        memset(cur, 0, NB * sizeof(uint64_t));
        memset(cov, 0, NB * sizeof(uint64_t));
        cur[x] = 1; cov[x] = 1;
        for (int l = 1; l <= 5; l++) {
            memset(nxt, 0, NB * sizeof(uint64_t));
            for (int e = 0; e < NE; e++) {
                int a = ea[e], b = eb[e], v = ev[e];
                if (cur[a]) nxt[b] |= rot(cur[a], v);
                if (cur[b]) nxt[a] |= rot(cur[b], (M - v) % M);
            }
            uint64_t *t = cur; cur = nxt; nxt = t;
            for (int u = 0; u < NB; u++) cov[u] |= cur[u];
        }
        for (int u = 0; u < NB; u++) far += __builtin_popcountll(FULL & ~cov[u]);
    }
    return far;
}
static long compute_far(void) { return compute_far_list(srcs, NSRC); }
static long compute_far_all(void) {
    int *all = malloc(sizeof(int) * NB);
    for (int i = 0; i < NB; i++) all[i] = i;
    long f = compute_far_list(all, NB); free(all); return f;
}

/* walk-count first moment: expected uncovered (x,u,h) if sums were independent uniform over Z_M */
static void first_moment(void) {
    double *cnt = malloc(sizeof(double) * 6 * NB), *tot = malloc(sizeof(double) * NB);
    double Ebad = 0, Nmin = 1e300, Nmax = 0;
    for (int x = 0; x < NB; x++) {
        for (int i = 0; i < 6 * NB; i++) cnt[i] = 0;
        cnt[x] = 1;
        for (int u = 0; u < NB; u++) tot[u] = 1.0 * (u == x);
        for (int l = 1; l <= 5; l++) {
            double *pc = cnt + (l - 1) * NB, *c = cnt + l * NB;
            for (int e = 0; e < NE; e++) { c[eb[e]] += pc[ea[e]]; c[ea[e]] += pc[eb[e]]; }
            for (int u = 0; u < NB; u++) tot[u] += c[u];
        }
        for (int u = 0; u < NB; u++) {
            Ebad += M * pow(1.0 - 1.0 / M, tot[u]);
            if (u != x && tot[u] > 0) { if (tot[u] < Nmin) Nmin = tot[u]; if (tot[u] > Nmax) Nmax = tot[u]; }
        }
    }
    double LB = 0; double Wmin_same = 1e300, Wmin_diff = 1e300; long pairs_short = 0;
    for (int x = 0; x < NB; x++) {
        for (int i = 0; i < 6 * NB; i++) cnt[i] = 0;
        cnt[x] = 1;
        for (int u = 0; u < NB; u++) tot[u] = 1.0 * (u == x);
        for (int l = 1; l <= 5; l++) {
            double *pc = cnt + (l - 1) * NB, *c = cnt + l * NB;
            for (int e = 0; e < NE; e++) { c[eb[e]] += pc[ea[e]]; c[ea[e]] += pc[eb[e]]; }
            for (int u = 0; u < NB; u++) tot[u] += c[u];
        }
        for (int u = 0; u < NB; u++) {
            if (tot[u] < M) { LB += M - tot[u]; pairs_short++; }
            if (u != x && tot[u] > 0 && tot[u] < Wmin_diff) Wmin_diff = tot[u];
            if (u == x && tot[u] < Wmin_same) Wmin_same = tot[u];
        }
    }
    printf("WALKLB sum_{x,u} max(0, M - walks_le5(x,u)) = %.0f over %ld pairs; min walks x!=u %.0f; min walks x=u %.0f (M=%d)\n",
           LB, pairs_short, Wmin_diff, Wmin_same, M);
    double Ffree = NE - (NB - 1);
    printf("FIRSTMOMENT walks<=5 per (x,u) pair: min %.0f max %.0f; E[uncovered (x,u,h)] = %.1f; free dims %g, "
           "log(M)*free = %.1f; log E[#solutions] ~ %.1f\n",
           Nmin, Nmax, Ebad, Ffree, Ffree * log((double)M), Ffree * log((double)M) - Ebad);
    free(cnt); free(tot);
}

int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: anneal gq.bin M K R iters T0 T1 seed out.txt [init.txt]\n"); return 1; }
    M = atoi(argv[2]); K = atoi(argv[3]); R = atoi(argv[4]); long iters = atol(argv[5]);
    double T0 = atof(argv[6]), T1 = atof(argv[7]); uint64_t seed = strtoull(argv[8], 0, 10);
    rs0 ^= seed * 0x9E3779B97F4A7C15ULL + 1; rs1 ^= seed * 0xBF58476D1CE4E5B9ULL + 7;
    for (int i = 0; i < 20; i++) rnext();
    FULL = (M >= 64) ? ~0ULL : ((1ULL << M) - 1);

    FILE *f = fopen(argv[1], "rb"); if (!f) { perror("gq"); return 1; }
    int hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1;
    Q = hdr[0]; N = hdr[1]; L = hdr[2]; Q1 = Q + 1;
    lin = malloc(sizeof(int) * (size_t)L * Q1);
    if (fread(lin, 4, (size_t)L * Q1, f) != (size_t)L * Q1) return 1;
    fclose(f);
    if (N != L) { fprintf(stderr, "need N == L\n"); return 1; }
    NB = N + L;

    /* sigma: random bijection points -> lines with no incidence p in sigma(p) (rejection sampling) */
    sig = malloc(sizeof(int) * N);
    int *perm = malloc(sizeof(int) * L);
    for (int i = 0; i < L; i++) perm[i] = i;
    for (;;) {
        for (int i = L - 1; i > 0; i--) { int j = rint_(i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
        int bad = 0;
        for (int p = 0; p < N && !bad; p++) for (int s = 0; s < Q1; s++) if (lin[perm[p] * Q1 + s] == p) { bad = 1; break; }
        if (!bad) break;
    }
    for (int p = 0; p < N; p++) sig[p] = perm[p];

    /* R extra single matchings tau_r: random perfect matchings, tau(p) not incident to p and tau(p) != sigma(p) */
    int *tau = malloc(sizeof(int) * (size_t)(R > 0 ? R : 1) * N);
    for (int r = 0; r < R; r++) {
        for (;;) {
            for (int i = L - 1; i > 0; i--) { int j = rint_(i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
            int bad = 0;
            for (int p = 0; p < N && !bad; p++) { if (perm[p] == sig[p]) bad = 1; for (int s = 0; s < Q1; s++) if (lin[perm[p] * Q1 + s] == p) { bad = 1; break; } }
            if (!bad) break;
        }
        for (int p = 0; p < N; p++) tau[(size_t)r * N + p] = perm[p];
    }
    NFLAG = L * Q1; NE = NFLAG + N * K + R * N;
    ea = malloc(sizeof(int) * NE); eb = malloc(sizeof(int) * NE); ev = malloc(sizeof(int) * NE);
    int e = 0;
    for (int l = 0; l < L; l++) for (int s = 0; s < Q1; s++) { ea[e] = lin[l * Q1 + s]; eb[e] = N + l; e++; }
    for (int p = 0; p < N; p++) for (int a = 0; a < K; a++) { ea[e] = p; eb[e] = N + sig[p]; e++; }
    for (int r = 0; r < R; r++) for (int p = 0; p < N; p++) { ea[e] = p; eb[e] = N + tau[(size_t)r * N + p]; e++; }
    cur = malloc(sizeof(uint64_t) * NB); nxt = malloc(sizeof(uint64_t) * NB); cov = malloc(sizeof(uint64_t) * NB);

    /* initial voltages */
    if (argc >= 11) {
        FILE *g = fopen(argv[10], "r"); int a0, b0, c0, n0, m0, ok = 1;
        if (!g || fscanf(g, "%d %d %d", &n0, &m0, &c0) != 3) ok = 0;
        for (int i = 0; ok && i < NE; i++) {
            if (fscanf(g, "%d %d %d", &a0, &b0, &c0) != 3) ok = 0; else ev[i] = ((c0 % M) + M) % M;
        }
        if (g) fclose(g);
        if (!ok) { fprintf(stderr, "bad init file\n"); return 1; }
    } else {
        for (int i = 0; i < NFLAG + R * N; i++) ev[i] = rint_(M);
        for (int p = 0; p < N; p++) {
            for (int a = 0; a < K; a++) {
                int idx = NFLAG + p * K + a, val, clash;
                do { val = rint_(M); clash = 0; for (int b = 0; b < a; b++) if (ev[NFLAG + p * K + b] == val) clash = 1; } while (clash);
                ev[idx] = val;
            }
        }
    }
    first_moment();

    /* source sample for the objective: NS env var (default all sources) */
    srcs = malloc(sizeof(int) * NB);
    for (int i = 0; i < NB; i++) srcs[i] = i;
    NSRC = NB;
    if (getenv("NS")) {
        int ns = atoi(getenv("NS")); if (ns < NB && ns > 0) {
            for (int i = NB - 1; i > 0; i--) { int j = rint_(i + 1); int t = srcs[i]; srcs[i] = srcs[j]; srcs[j] = t; }
            NSRC = ns;
        }
    }
    long far = compute_far();
    long bestF = far; int *bestv = malloc(sizeof(int) * NE); memcpy(bestv, ev, sizeof(int) * NE);
    printf("init far=%ld (NB=%d NE=%d M=%d K=%d)\n", far, NB, NE, M, K); fflush(stdout);
    long acc = 0;
    for (long it = 0; it < iters && bestF > 0; it++) {
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int ed = rint_(NE);
        int old = ev[ed], val;
        if (ed < NFLAG) {
            do { val = rint_(M); } while (val == old);
        } else {
            int p = ea[ed]; int base = NFLAG + p * K, clash;
            do {
                val = rint_(M); clash = (val == old);
                for (int b = 0; b < K; b++) if (base + b != ed && ev[base + b] == val) clash = 1;
            } while (clash);
        }
        ev[ed] = val;
        long Fn = compute_far();
        long dF = Fn - far;
        if (dF <= 0 || runif() < exp(-(double)dF / T)) {
            far = Fn; acc++;
            if (far < bestF) { bestF = far; memcpy(bestv, ev, sizeof(int) * NE);
                printf("it %ld T %.3f best far=%ld\n", it, T, bestF); fflush(stdout); }
        } else ev[ed] = old;
        if (it % 2000 == 0) { printf("it %ld T %.3f cur far=%ld best=%ld acc=%ld\n", it, T, far, bestF, acc); fflush(stdout); }
    }
    memcpy(ev, bestv, sizeof(int) * NE);
    long chk = compute_far_all();
    printf("FINAL sample-objective far=%ld; full far (all %d sources)=%ld; order=%d\n", bestF, NB, chk, NB * M);
    FILE *o = fopen(argv[9], "w");
    fprintf(o, "%d %d %d\n", N, L, M);
    for (int i = 0; i < NE; i++) fprintf(o, "%d %d %d\n", ea[i], eb[i] - N, ev[i]);
    fclose(o);
    return 0;
}
