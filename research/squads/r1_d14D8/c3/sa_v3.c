/* sa.c (card c3, squad r1_d14D8): simulated annealing for cyclic voltage lifts of H(q) + extra matchings.

   Criterion (lifteval, D = 8): for every point a (source (a,0)) and every line b and level g in Z_m there is a
   walk of length 7 from (a,0) to (b,g). COST of a source = number of uncovered (b,g) pairs; COST = sum over sources.
   Moves: (i) change the voltage of one edge (uniform over the other m-1 values);
          (ii) with prob PM: swap the line targets of two points inside one extra matching (voltages kept).
   The SA cost uses K sampled sources (resampled every RESAMPLE moves); every FULL_EVERY moves the exact cost over
   ALL sources is computed, the best exact state is written to OUT, and the run stops at exact cost 0.

   Usage: sa BASE OUT ITERS T0 T1 K SEED PM NH NMATCH [FULL_EVERY=20000] [RESAMPLE=1000]
     BASE file: first line "N N m", then edge lines "p l v" (p point, l line, v voltage in Z_m).
     Edges 0..NH-1 are the hexagon incidences; then NMATCH blocks of N edges: block j, point p at NH + j*N + p.
   Output file: same format (best exact state). Progress on stderr. Exit code 0 iff exact cost 0 was reached. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

typedef uint64_t u64;
static int N, m, E, NH, NM;
static int *ea, *eb, *ev;               /* edge arrays: point, line, voltage */
static int *Aoff, *Aadj, *Avol, *posA, *Aedge;  /* CSR over points: neighbour line, voltage v, edge id */
static int *Boff, *Badj, *Bvol, *posB, *Bedge;  /* CSR over lines: neighbour point, (m - v) mod m, edge id */
static u64 FULL;
static unsigned char *cnt;              /* cnt[p*N+l]: number of edges between point p and line l */
static u64 *bufA, *bufB;

static u64 rs = 88172645463325252ULL;
static inline u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double rndu(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static inline int rndi(int n) { return (int)(rnd64() % (u64)n); }
static inline u64 rot(u64 x, int v) { return v ? (((x << v) | (x >> (m - v))) & FULL) : x; }

static void build(void) {
    memset(Aoff, 0, sizeof(int) * (N + 1)); memset(Boff, 0, sizeof(int) * (N + 1));
    for (int e = 0; e < E; e++) { Aoff[ea[e] + 1]++; Boff[eb[e] + 1]++; }
    for (int i = 0; i < N; i++) { Aoff[i + 1] += Aoff[i]; Boff[i + 1] += Boff[i]; }
    int *pa = malloc(sizeof(int) * N), *pb = malloc(sizeof(int) * N);
    memcpy(pa, Aoff, sizeof(int) * N); memcpy(pb, Boff, sizeof(int) * N);
    for (int e = 0; e < E; e++) {
        int i = pa[ea[e]]++; Aadj[i] = eb[e]; Avol[i] = ev[e]; posA[e] = i; Aedge[i] = e;
        int j = pb[eb[e]]++; Badj[j] = ea[e]; Bvol[j] = (m - ev[e]) % m; posB[e] = j; Bedge[j] = e;
    }
    free(pa); free(pb);
}
static inline void set_volt(int e, int v) { ev[e] = v; Avol[posA[e]] = v; Bvol[posB[e]] = (m - v) % m; }

/* uncovered (line, level) pairs for source point s: walks of length 7 from (s,0) */
static long long cost_src(int s) {
    memset(bufA, 0, sizeof(u64) * N);
    bufA[s] = 1;
    for (int step = 0; step < 7; step++) {
        if ((step & 1) == 0) { /* points -> lines */
            memset(bufB, 0, sizeof(u64) * N);
            for (int a = 0; a < N; a++) { u64 x = bufA[a]; if (!x) continue;
                for (int k = Aoff[a]; k < Aoff[a + 1]; k++) bufB[Aadj[k]] |= rot(x, Avol[k]); }
        } else {               /* lines -> points */
            memset(bufA, 0, sizeof(u64) * N);
            for (int b = 0; b < N; b++) { u64 x = bufB[b]; if (!x) continue;
                for (int k = Boff[b]; k < Boff[b + 1]; k++) bufA[Badj[k]] |= rot(x, Bvol[k]); }
        }
    }
    long long c = 0;
    for (int b = 0; b < N; b++) c += m - __builtin_popcountll(bufB[b]);
    return c;
}


/* targeted repair move: pick a sampled source a and a missing (b,g) of its reach sets; take a random 7-walk
   a -> b; re-voltage one of its edges with net coefficient +-1 so that the walk sum becomes g.
   Returns the changed edge (old voltage in *oldv) or -1. */
static int targeted_move(const int *S, int K, int *oldv) {
    for (int attempt = 0; attempt < 50; attempt++) {
        int a = S[rndi(K)];
        cost_src(a);                          /* bufB = reach sets of a */
        int nb = 0;
        int *bl = malloc(sizeof(int) * N);
        for (int b = 0; b < N; b++) if (bufB[b] != FULL) bl[nb++] = b;
        if (!nb) { free(bl); continue; }
        int b = bl[rndi(nb)]; free(bl);
        int miss[64], nm2 = 0;
        for (int g = 0; g < m; g++) if (!((bufB[b] >> g) & 1ULL)) miss[nm2++] = g;
        int g = miss[rndi(nm2)];
        for (int tries = 0; tries < 300000; tries++) {
            int pe[7], ps[7]; int pt = a, s = 0, side = 0;
            for (int st = 0; st < 7; st++) {
                if (side == 0) { int k = Aoff[pt] + rndi(Aoff[pt + 1] - Aoff[pt]);
                    pe[st] = Aedge[k]; ps[st] = 1; s += Avol[k]; pt = Aadj[k]; side = 1; }
                else { int k = Boff[pt] + rndi(Boff[pt + 1] - Boff[pt]);
                    pe[st] = Bedge[k]; ps[st] = -1; s -= ev[Bedge[k]]; pt = Badj[k]; side = 0; }
            }
            if (side != 1 || pt != b) continue;
            s = ((s % m) + m) % m;
            int cand[7], nc = 0;
            for (int i = 0; i < 7; i++) {
                int c = 0;
                for (int j = 0; j < 7; j++) if (pe[j] == pe[i]) c += ps[j];
                if (c == 1 || c == -1) {
                    int dup = 0; for (int t = 0; t < nc; t++) if (pe[cand[t]] == pe[i]) dup = 1;
                    if (!dup) cand[nc++] = i;
                }
            }
            if (!nc) continue;
            int i = cand[rndi(nc)], e = pe[i];
            int c = 0; for (int j = 0; j < 7; j++) if (pe[j] == e) c += ps[j];
            int delta = ((c * (g - s)) % m + m) % m;
            if (!delta) continue;
            *oldv = ev[e];
            set_volt(e, (ev[e] + delta) % m);
            return e;
        }
    }
    return -1;
}

static long long cost_set(const int *S, int K) {
    long long c = 0;
    for (int i = 0; i < K; i++) c += cost_src(S[i]);
    return c;
}

static int write_base(const char *fn, const int *el, const int *vol) {
    FILE *f = fopen(fn, "w"); if (!f) { perror(fn); return -1; }
    fprintf(f, "%d %d %d\n", N, N, m);
    for (int e = 0; e < E; e++) fprintf(f, "%d %d %d\n", ea[e], el[e], vol[e]);
    fclose(f); return 0;
}

int main(int argc, char **argv) {
    if (argc < 11) { fprintf(stderr, "usage: sa BASE OUT ITERS T0 T1 K SEED PM NH NMATCH [FULL_EVERY] [RESAMPLE]\n"); return 2; }
    const char *basef = argv[1], *outf = argv[2];
    long long iters = atoll(argv[3]); double T0 = atof(argv[4]), T1 = atof(argv[5]);
    int K = atoi(argv[6]); unsigned long long seed = strtoull(argv[7], NULL, 10);
    double PM = atof(argv[8]); NH = atoi(argv[9]); NM = atoi(argv[10]);
    long long FULL_EVERY = argc > 11 ? atoll(argv[11]) : 20000;
    int RESAMPLE = argc > 12 ? atoi(argv[12]) : 1000;
    double PT = argc > 13 ? atof(argv[13]) : 0.0;
    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd64();

    FILE *f = fopen(basef, "r"); if (!f) { perror(basef); return 2; }
    int n1, n2;
    if (fscanf(f, "%d %d %d", &n1, &n2, &m) != 3 || n1 != n2 || m < 2 || m > 63) { fprintf(stderr, "bad header\n"); return 2; }
    N = n1; FULL = (1ULL << m) - 1;
    int cap = NH + NM * N + 16; if (cap < 1024) cap = 1024;
    ea = malloc(sizeof(int) * cap); eb = malloc(sizeof(int) * cap); ev = malloc(sizeof(int) * cap);
    E = 0; int a, b, v;
    while (fscanf(f, "%d %d %d", &a, &b, &v) == 3) {
        if (E >= cap) { cap *= 2; ea = realloc(ea, sizeof(int) * cap); eb = realloc(eb, sizeof(int) * cap); ev = realloc(ev, sizeof(int) * cap); }
        ea[E] = a; eb[E] = b; ev[E] = ((v % m) + m) % m; E++;
    }
    fclose(f);
    if (E != NH + NM * N) { fprintf(stderr, "edge count %d != NH + NM*N = %d\n", E, NH + NM * N); return 2; }
    for (int j = 0; j < NM; j++) for (int p = 0; p < N; p++) if (ea[NH + j * N + p] != p) { fprintf(stderr, "matching layout mismatch\n"); return 2; }
    cnt = calloc((size_t)N * N, 1);
    for (int e = 0; e < E; e++) cnt[(size_t)ea[e] * N + eb[e]]++;
    long multi = 0; for (size_t i = 0; i < (size_t)N * N; i++) if (cnt[i] > 1) multi++;
    fprintf(stderr, "base N %d m %d edges %d (hex %d, matchings %d x %d); multi-pairs %ld\n", N, m, E, NH, NM, N, multi);
    Aoff = malloc(sizeof(int) * (N + 1)); Boff = malloc(sizeof(int) * (N + 1));
    Aadj = malloc(sizeof(int) * E); Avol = malloc(sizeof(int) * E); posA = malloc(sizeof(int) * E);
    Badj = malloc(sizeof(int) * E); Bvol = malloc(sizeof(int) * E); posB = malloc(sizeof(int) * E);
    Aedge = malloc(sizeof(int) * E); Bedge = malloc(sizeof(int) * E);
    bufA = malloc(sizeof(u64) * N); bufB = malloc(sizeof(u64) * N);
    build();

    int *S = malloc(sizeof(int) * N);
    if (K >= N) { K = N; for (int i = 0; i < N; i++) S[i] = i; RESAMPLE = (int)(iters + 1); }
    else for (int i = 0; i < K; i++) S[i] = rndi(N);
    long long cur = cost_set(S, K);
    long long full = -1, bestfull = -1;
    int *bestvol = malloc(sizeof(int) * E), *bestel = malloc(sizeof(int) * E);
    long long acc = 0, accM = 0, tried = 0, triedM = 0;
    for (long long it = 0; it < iters; it++) {
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        if (it % RESAMPLE == 0 && it && K < N) {
            for (int i = 0; i < K; i++) S[i] = rndi(N);
            cur = cost_set(S, K);
        }
        if (PM > 0 && rndu() < PM && NM > 0) {       /* matching swap move */
            triedM++;
            int j = rndi(NM), p1 = rndi(N), p2 = rndi(N);
            int e1 = NH + j * N + p1, e2 = NH + j * N + p2;
            int l1 = eb[e1], l2 = eb[e2];
            if (p1 != p2 && !cnt[(size_t)p1 * N + l2] && !cnt[(size_t)p2 * N + l1]) {
                cnt[(size_t)p1 * N + l1]--; cnt[(size_t)p2 * N + l2]--;
                cnt[(size_t)p1 * N + l2]++; cnt[(size_t)p2 * N + l1]++;
                eb[e1] = l2; eb[e2] = l1; build();
                long long c = cost_set(S, K);
                long long d = c - cur;
                if (d <= 0 || rndu() < exp(-(double)d / T)) { cur = c; accM++; }
                else {
                    cnt[(size_t)p1 * N + l2]--; cnt[(size_t)p2 * N + l1]--;
                    cnt[(size_t)p1 * N + l1]++; cnt[(size_t)p2 * N + l2]++;
                    eb[e1] = l1; eb[e2] = l2; build();
                }
            }
        } else if (PT > 0 && rndu() < PT) {           /* targeted repair move */
            tried++;
            int oldv = 0;
            int e = targeted_move(S, K, &oldv);
            if (e >= 0) {
                long long c = cost_set(S, K);
                long long d = c - cur;
                if (d <= 0 || rndu() < exp(-(double)d / T)) { cur = c; acc++; }
                else set_volt(e, oldv);
            }
        } else {                                      /* voltage move */
            tried++;
            int e = rndi(E); int old = ev[e];
            int nv = rndi(m - 1); if (nv >= old) nv++;
            set_volt(e, nv);
            long long c = cost_set(S, K);
            long long d = c - cur;
            if (d <= 0 || rndu() < exp(-(double)d / T)) { cur = c; acc++; }
            else set_volt(e, old);
        }
        if (FULL_EVERY > 0 && (it + 1) % FULL_EVERY == 0) {
            for (int i = 0; i < N; i++) S[i] = i;
            full = cost_set(S, N);
            if (bestfull < 0 || full < bestfull) {
                bestfull = full; memcpy(bestvol, ev, sizeof(int) * E); memcpy(bestel, eb, sizeof(int) * E);
                write_base(outf, bestel, bestvol);
            }
            fprintf(stderr, "it %lld T %.3f sample_cost %lld full %lld best_full %lld acc_v %.3f acc_m %.3f\n",
                    it + 1, T, cur, full, bestfull, tried ? (double)acc / tried : 0.0, triedM ? (double)accM / triedM : 0.0);
            if (full == 0) break;
            if (K < N) { for (int i = 0; i < K; i++) S[i] = rndi(N); cur = cost_set(S, K); }
            else cur = full;
        }
    }
    /* final exact evaluation of the current state; keep the better of current and best */
    for (int i = 0; i < N; i++) S[i] = i;
    full = cost_set(S, N);
    if (bestfull < 0 || full < bestfull) {
        bestfull = full; write_base(outf, eb, ev);
    }
    printf("RESULT m %d N %d best_exact_cost %lld\n", m, N, bestfull);
    return bestfull == 0 ? 0 : 1;
}
