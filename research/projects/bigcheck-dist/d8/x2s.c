/* x2s.c: search for diameter-D cyclic lifts of hexagon compounds, with a Singer-torus symmetry.
 *
 * Base X: C copies of the incidence graph of the split Cayley hexagon H(q) (points P, lines L, |P| = |L| = N), plus r
 * bijections sigma_j: P -> L (j = 1..r), joining (p, c) to (sigma_j(p), c + s_j mod C). With C = 2r+1 and s_j = j this
 * is the table's diameter-7 graph X_r (Δ = q+1+r). The lift: (x, c, g) for g in Z_k; every base edge carries a voltage
 * in Z_k. Symmetry imposed: a cyclic group A = <tau> of automorphisms of H(q) acting freely (the torus from singer.py)
 * commutes with each sigma_j and preserves voltages; voltages do not depend on the copy c. So A, the copy rotation and
 * the Z_k translations are automorphisms of the lift, and BFS from (x, 0, 0) for x in a set of A-orbit
 * representatives of P and L gives the exact diameter.
 *
 * Parameters: sigma_j(tau^i p_o) = tau^(i + t_jo) l_(pi_j(o)) for point-orbit reps p_o and line-orbit reps l_o.
 * Voltages: one per A-orbit of flags (point orbit o, slot of the line at p_o), one per (j, point orbit).
 * Cost = number of (source, lift vertex) pairs at distance > D, summed over the sources. Simulated annealing on
 * voltages, offsets t and the orbit matchings pi.
 *
 * Usage: x2s HEX.bin SINGER.bin C r s_1..s_r k D seed iters T0 [init.sol] > log ; writes best to best_<seed>.sol
 * Build: cc -O3 -march=native -fopenmp -o x2s x2s.c */
#include <math.h>
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static int q, N, KA, NO, C, R, S[8], K, D;
static int *lp;           /* lines -> q+1 points */
static int *pl;           /* points -> q+1 lines */
static int *gp, *gl;      /* tau on points, lines */
static int *porb, *ppos, *prep, *lorb, *lpos, *lrep; /* orbit id, position (x = tau^pos rep), reps */
static int *tpow_p, *tpow_l; /* tpow[e * N + x] = tau^e(x) */
/* parameters */
static int *pi_[8], *t_[8], *va_[8];  /* per point orbit */
static int *vf;                        /* flag-class voltage: index o*(q+1)+slot */
/* base graph X: vertex (x, c) -> c*2N + x (points x < N, lines N + l); adjacency fixed degree q+1+r */
static int NBX, DEG; static int *bw; static int *ba;
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static int flag_class(int p, int slot) { /* flag (p, pl[p][slot]) -> class */
    int o = porb[p], e = ppos[p], L = pl[p * (q + 1) + slot];
    int L0 = tpow_l[((KA - e) % KA) * N + L]; /* tau^-e L, a line through the rep */
    int r = prep[o];
    for (int s = 0; s <= q; s++) if (pl[r * (q + 1) + s] == L0) return o * (q + 1) + s;
    fprintf(stderr, "flag class bug\n"); exit(1);
}
static int *fcls; /* fcls[p*(q+1)+slot] */
static int sigma(int j, int p) { int o = porb[p], e = ppos[p]; return tpow_l[((e + t_[j][o]) % KA) * N + lrep[pi_[j][o]]]; }

static void build_base(void) {
    /* slot layout: points: q+1 incidences then r matchings up; lines: q+1 incidences then r matchings down */
    for (int c = 0; c < C; c++) for (int x = 0; x < 2 * N; x++) {
        int v = c * 2 * N + x, *w = bw + (int64_t)v * DEG, *a = ba + (int64_t)v * DEG;
        if (x < N) {
            for (int s = 0; s <= q; s++) { w[s] = c * 2 * N + N + pl[x * (q + 1) + s]; a[s] = vf[fcls[x * (q + 1) + s]]; }
            for (int j = 0; j < R; j++) { w[q + 1 + j] = ((c + S[j]) % C) * 2 * N + N + sigma(j, x); a[q + 1 + j] = va_[j][porb[x]]; }
        }
    }
    /* lines: fill from the points' lists (incidence: reverse voltage; matchings: reverse) */
    static int *fill = NULL; if (!fill) fill = malloc(sizeof(int) * NBX);
    for (int v = 0; v < NBX; v++) fill[v] = 0;
    for (int c = 0; c < C; c++) for (int x = 0; x < N; x++) {
        int v = c * 2 * N + x;
        for (int s = 0; s < DEG; s++) {
            int u = bw[(int64_t)v * DEG + s]; int slot = s <= q ? fill[u]++ : (q + 1 + (s - q - 1));
            bw[(int64_t)u * DEG + slot] = v; ba[(int64_t)u * DEG + slot] = (K - ba[(int64_t)v * DEG + s]) % K;
        }
    }
}

/* BFS cost */
static uint64_t *VIS, *FR, *NX; static int NSRC; static int *SRC; static int64_t NL;
static long long cost_eval(int full_D) {
    long long tot = 0;
    for (int b0 = 0; b0 < NSRC; b0 += 64) {
        int ns = NSRC - b0 < 64 ? NSRC - b0 : 64; uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        memset(VIS, 0, 8 * NL); memset(FR, 0, 8 * NL);
        for (int i = 0; i < ns; i++) { int64_t s = (int64_t)SRC[b0 + i] * K; VIS[s] |= 1ULL << i; FR[s] |= 1ULL << i; }
        for (int lev = 1; lev <= full_D; lev++) {
#pragma omp parallel for schedule(dynamic, 256)
            for (int v = 0; v < NBX; v++) {
                uint64_t *out = NX + (int64_t)v * K; const uint64_t *vis = VIS + (int64_t)v * K;
                for (int g = 0; g < K; g++) out[g] = 0;
                for (int s = 0; s < DEG; s++) {
                    const uint64_t *src = FR + (int64_t)bw[(int64_t)v * DEG + s] * K; int a = ba[(int64_t)v * DEG + s];
                    for (int g = 0; g < K - a; g++) out[g] |= src[g + a];
                    for (int g = K - a; g < K; g++) out[g] |= src[g + a - K];
                }
                for (int g = 0; g < K; g++) out[g] &= ~vis[g];
            }
#pragma omp parallel for schedule(static)
            for (int64_t x = 0; x < NL; x++) VIS[x] |= NX[x];
            uint64_t *t = FR; FR = NX; NX = t;
        }
        long long un = 0;
#pragma omp parallel for schedule(static) reduction(+ : un)
        for (int64_t x = 0; x < NL; x++) un += __builtin_popcountll(~VIS[x] & full);
        tot += un;
    }
    return tot;
}

static void save(const char *path, long long cost) {
    FILE *f = fopen(path, "w");
    fprintf(f, "x2s q %d N %d KA %d C %d r %d s", q, N, KA, C, R); for (int j = 0; j < R; j++) fprintf(f, " %d", S[j]);
    fprintf(f, " k %d D %d cost %lld\n", K, D, cost);
    for (int j = 0; j < R; j++) { fprintf(f, "sigma %d", j); for (int o = 0; o < NO; o++) fprintf(f, " %d %d %d", pi_[j][o], t_[j][o], va_[j][o]); fprintf(f, "\n"); }
    fprintf(f, "flags"); for (int i = 0; i < NO * (q + 1); i++) fprintf(f, " %d", vf[i]); fprintf(f, "\n");
    fclose(f);
}
static int load_sol(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) return 0; char w[64]; int x;
    while (fscanf(f, "%63s", w) == 1 && strcmp(w, "cost")) ;
    long long c; if (fscanf(f, "%lld", &c) != 1) return 0;
    for (int j = 0; j < R; j++) { if (fscanf(f, "%63s %d", w, &x) != 2) return 0; for (int o = 0; o < NO; o++) if (fscanf(f, "%d %d %d", &pi_[j][o], &t_[j][o], &va_[j][o]) != 3) return 0; }
    if (fscanf(f, "%63s", w) != 1) return 0;
    for (int i = 0; i < NO * (q + 1); i++) { if (fscanf(f, "%d", &vf[i]) != 1) return 0; vf[i] %= K; }
    for (int j = 0; j < R; j++) for (int o = 0; o < NO; o++) va_[j][o] %= K;
    fclose(f); return 1;
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: x2s HEX.bin SINGER.bin C r s_1..s_r k D seed iters T0 [init.sol]\n"); return 2; }
    int ai = 1; const char *hexp = argv[ai++], *sgp = argv[ai++]; C = atoi(argv[ai++]); R = atoi(argv[ai++]);
    for (int j = 0; j < R; j++) S[j] = atoi(argv[ai++]);
    K = atoi(argv[ai++]); D = atoi(argv[ai++]); long seed = atol(argv[ai++]); long iters = atol(argv[ai++]); double T0 = atof(argv[ai++]);
    const char *init = ai < argc ? argv[ai++] : NULL;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    FILE *f = fopen(hexp, "rb"); int Lc; if (fread(&q, 4, 1, f) != 1 || fread(&N, 4, 1, f) != 1 || fread(&Lc, 4, 1, f) != 1) return 2;
    lp = malloc(sizeof(int) * N * (q + 1)); if (fread(lp, 4, (size_t)N * (q + 1), f) != (size_t)N * (q + 1)) return 2; fclose(f);
    pl = malloc(sizeof(int) * N * (q + 1)); int *cnt = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int i = 0; i <= q; i++) { int p = lp[l * (q + 1) + i]; pl[p * (q + 1) + cnt[p]++] = l; }
    f = fopen(sgp, "rb"); int n2; if (fread(&n2, 4, 1, f) != 1 || fread(&KA, 4, 1, f) != 1 || n2 != N) return 2;
    gp = malloc(sizeof(int) * N); gl = malloc(sizeof(int) * N);
    if (fread(gp, 4, N, f) != (size_t)N || fread(gl, 4, N, f) != (size_t)N) return 2; fclose(f);
    tpow_p = malloc(sizeof(int) * (size_t)KA * N); tpow_l = malloc(sizeof(int) * (size_t)KA * N);
    for (int x = 0; x < N; x++) { tpow_p[x] = x; tpow_l[x] = x; }
    for (int e = 1; e < KA; e++) for (int x = 0; x < N; x++) { tpow_p[(size_t)e * N + x] = gp[tpow_p[(size_t)(e - 1) * N + x]]; tpow_l[(size_t)e * N + x] = gl[tpow_l[(size_t)(e - 1) * N + x]]; }
    NO = N / KA;
    porb = malloc(sizeof(int) * N); ppos = malloc(sizeof(int) * N); lorb = malloc(sizeof(int) * N); lpos = malloc(sizeof(int) * N);
    prep = malloc(sizeof(int) * NO); lrep = malloc(sizeof(int) * NO);
    for (int x = 0; x < N; x++) porb[x] = lorb[x] = -1;
    int no = 0; for (int x = 0; x < N; x++) if (porb[x] < 0) { prep[no] = x; for (int e = 0; e < KA; e++) { int y = tpow_p[(size_t)e * N + x]; porb[y] = no; ppos[y] = e; } no++; }
    if (no != NO) { fprintf(stderr, "point orbits %d != %d\n", no, NO); return 1; }
    no = 0; for (int x = 0; x < N; x++) if (lorb[x] < 0) { lrep[no] = x; for (int e = 0; e < KA; e++) { int y = tpow_l[(size_t)e * N + x]; lorb[y] = no; lpos[y] = e; } no++; }
    fcls = malloc(sizeof(int) * N * (q + 1));
    for (int p = 0; p < N; p++) for (int s = 0; s <= q; s++) fcls[p * (q + 1) + s] = flag_class(p, s);
    for (int j = 0; j < R; j++) { pi_[j] = malloc(sizeof(int) * NO); t_[j] = malloc(sizeof(int) * NO); va_[j] = malloc(sizeof(int) * NO); }
    vf = malloc(sizeof(int) * NO * (q + 1));
    for (int j = 0; j < R; j++) {
        for (int o = 0; o < NO; o++) pi_[j][o] = o;
        for (int o = NO - 1; o > 0; o--) { int z = rnd() % (o + 1), t = pi_[j][o]; pi_[j][o] = pi_[j][z]; pi_[j][z] = t; }
        for (int o = 0; o < NO; o++) { t_[j][o] = rnd() % KA; va_[j][o] = rnd() % K; }
    }
    for (int i = 0; i < NO * (q + 1); i++) vf[i] = rnd() % K;
    if (init && !load_sol(init)) { fprintf(stderr, "cannot read %s\n", init); return 1; }
    DEG = q + 1 + R; NBX = C * 2 * N; bw = malloc(sizeof(int) * (size_t)NBX * DEG); ba = malloc(sizeof(int) * (size_t)NBX * DEG);
    NL = (int64_t)NBX * K; VIS = malloc(8 * NL); FR = malloc(8 * NL); NX = malloc(8 * NL);
    NSRC = 2 * NO; SRC = malloc(sizeof(int) * NSRC);
    for (int o = 0; o < NO; o++) { SRC[o] = prep[o]; SRC[NO + o] = N + lrep[o]; }
    build_base();
    double t0 = omp_get_wtime();
    long long cur = cost_eval(D), best = cur;
    fprintf(stderr, "q=%d N=%d torus %d orbits %d; C=%d r=%d k=%d D=%d: lift %lld vertices (Δ=%d), %d sources; initial cost %lld [%.2fs/eval]\n",
            q, N, KA, NO, C, R, K, D, (long long)NL, DEG, NSRC, cur, omp_get_wtime() - t0);
    char bestp[256]; snprintf(bestp, sizeof bestp, "best_%ld.sol", seed); save(bestp, best);
    int NF = NO * (q + 1), NM = R * NO;
    for (long it = 1; it <= iters && best > 0; it++) {
        double T = T0 * (1.0 - (double)it / iters) + 1e-9;
        int mv = rnd() % 100; int j = 0, o = 0, o2 = 0, old1 = 0, old2 = 0, idx = 0;
        if (mv < 60) { idx = rnd() % NF; old1 = vf[idx]; vf[idx] = rnd() % K; if (vf[idx] == old1) vf[idx] = (old1 + 1) % K; }
        else if (mv < 80) { idx = rnd() % NM; j = idx / NO; o = idx % NO; old1 = va_[j][o]; va_[j][o] = (old1 + 1 + rnd() % (K - 1)) % K; }
        else if (mv < 92) { j = rnd() % R; o = rnd() % NO; old1 = t_[j][o]; t_[j][o] = rnd() % KA; }
        else { j = rnd() % R; o = rnd() % NO; o2 = rnd() % NO; old1 = pi_[j][o]; old2 = pi_[j][o2]; pi_[j][o] = old2; pi_[j][o2] = old1; }
        build_base();
        long long c = cost_eval(D);
        if (c <= cur || exp((double)(cur - c) / T) * 4294967296.0 > (double)(rnd() & 0xffffffff)) {
            cur = c;
            if (c < best) { best = c; save(bestp, best); fprintf(stderr, "it %ld T %.2f best %lld [%.0fs]\n", it, T, best, omp_get_wtime() - t0); }
        } else {
            if (mv < 60) vf[idx] = old1; else if (mv < 80) va_[j][o] = old1; else if (mv < 92) t_[j][o] = old1; else { pi_[j][o] = old1; pi_[j][o2] = old2; }
        }
        if (it % 200 == 0) fprintf(stderr, "it %ld T %.2f cur %lld best %lld [%.0fs]\n", it, T, cur, best, omp_get_wtime() - t0);
    }
    printf("best %lld\n", best);
    return 0;
}
