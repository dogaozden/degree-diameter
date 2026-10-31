/* hexeval.c (worker c6): voltage lifts of H(q) + J matchings over the cyclic group Z_m (m <= 64).
 * Faster than lift3 for the diameter-8 test: only POINT sources and walks of length 7 are needed (a lift has
 * diameter <= 8 iff every point reaches every line within 7 steps; walks of length 5, 3, 1 are included in
 * length 7 by backtracking, which keeps the voltage). Lanes: LANES = 64/m sources per word.
 * Conventions = lift3.c: flag (pl[l*Q1+k], l) has voltage hv[l*Q1+k] in direction point->line;
 * matching t joins point p to line sig[t*N+p] with voltage mv[t*N+p] (point->line).
 * Solution file = lift3 format ("q J m D cost", gspec line, J sigma lines, J mv lines, hv line), so lift3 can
 * re-check it with IN=file ITERS=0 (full check).
 * env: M (group order), J (default 2), D fixed to 8, ITERS, SEED, TEMP0, TEMP1, IN, OUT, HZERO=1 (hexagon 0),
 *      MCONST (T env "a b"), RESET, PRINT.
 * usage: hexeval q */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

static int q, N, Q1, J = 2, m, V;
static int32_t *pl;
static int *sig, *sinv, *mv, *hv;
static int *inn, *inw;     /* V x Dg: in-neighbour x and voltage w(x->y) */
static int Dg;
static uint64_t Mlo[64], Mhi[64], LaneMask;
static int LANES;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline uint64_t rot(uint64_t R, int g) {
    if (!g) return R;
    return ((R & Mlo[g]) << g) | ((R & Mhi[g]) >> (m - g));
}
static void setup_masks(void) {
    LaneMask = 0; for (int k = 0; k < LANES; k++) for (int h = 0; h < m; h++) LaneMask |= 1ULL << (k * m + h);
    for (int g = 0; g < m; g++) { Mlo[g] = Mhi[g] = 0;
        for (int k = 0; k < LANES; k++) for (int h = 0; h < m; h++) {
            uint64_t b = 1ULL << (k * m + h);
            if (h < m - g) Mlo[g] |= b; else Mhi[g] |= b; } }
}
static void build(void) {       /* in-arcs of all vertices from the current state */
    for (int p = 0; p < N; p++) {
        /* point p: in-arcs from its lines: w(l->p) = -hv */
        int c = 0;
        for (int k = 0; k < Q1; k++) { }
    }
    /* build via point/line lists */
    int *cntp = calloc(V, sizeof(int));
    for (int v = 0; v < V; v++) cntp[v] = 0;
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) {
        int p = pl[l * Q1 + k]; int fl = l * Q1 + k;
        /* in-arc of line N+l from point p: w(p->l) = hv[fl] */
        inn[(N + l) * Dg + cntp[N + l]] = p; inw[(N + l) * Dg + cntp[N + l]] = hv[fl]; cntp[N + l]++;
        /* in-arc of point p from line N+l: w(l->p) = -hv[fl] */
        inn[p * Dg + cntp[p]] = N + l; inw[p * Dg + cntp[p]] = (m - hv[fl]) % m; cntp[p]++;
    }
    for (int t = 0; t < J; t++) for (int p = 0; p < N; p++) {
        int l = sig[t * N + p]; int w = mv[t * N + p];
        inn[(N + l) * Dg + cntp[N + l]] = p; inw[(N + l) * Dg + cntp[N + l]] = w; cntp[N + l]++;
        inn[p * Dg + cntp[p]] = N + l; inw[p * Dg + cntp[p]] = (m - w) % m; cntp[p]++;
    }
    free(cntp);
}
static uint64_t *Wa, *Wb;
static long cost_points(void) {   /* cost over all point sources */
    long c = 0;
    for (int p0 = 0; p0 < N; p0 += LANES) {
        int ns = N - p0 < LANES ? N - p0 : LANES;
        memset(Wa, 0, sizeof(uint64_t) * V);
        for (int k = 0; k < ns; k++) Wa[p0 + k] |= 1ULL << (k * m);
        /* Wa[p] is the set of voltages at vertex p after the current step; lanes = source index */
        for (int step = 1; step <= 7; step++) {
            for (int y = 0; y < V; y++) {
                uint64_t o = 0; const int *a = inn + (size_t)y * Dg, *w = inw + (size_t)y * Dg;
                for (int i = 0; i < Dg; i++) { uint64_t R = Wa[a[i]]; if (R) o |= rot(R, w[i]); }
                Wb[y] = o;
            }
            uint64_t *t = Wa; Wa = Wb; Wb = t;
        }
        uint64_t full = 0;
        for (int l = 0; l < N; l++) { uint64_t R = Wa[N + l]; if (ns < LANES) R &= ((1ULL << (ns * m)) - 1); c += ns * m - __builtin_popcountll(R); }
        (void)full;
        if (c > 1000000000L) return c;
    }
    return c;
}
static void save(const char *fn, long cost) {
    FILE *f = fopen(fn, "w");
    fprintf(f, "%d %d %d %d %ld\ncyc %d\n", q, J, m, 8, cost, m);
    for (int t = 0; t < J; t++) { for (int p = 0; p < N; p++) fprintf(f, "%d ", sig[t * N + p]); fprintf(f, "\n"); }
    for (int t = 0; t < J; t++) { for (int p = 0; p < N; p++) fprintf(f, "%d ", mv[t * N + p]); fprintf(f, "\n"); }
    for (int i = 0; i < N * Q1; i++) fprintf(f, "%d ", hv[i]); fprintf(f, "\n");
    fclose(f);
}
static int load(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) return 0;
    int qq, jj, mm, dd; long c; char line[512];
    if (fscanf(f, "%d %d %d %d %ld\n", &qq, &jj, &mm, &dd, &c) != 5) return 0;
    if (!fgets(line, sizeof line, f)) return 0;
    if (qq != q || jj != J || mm != m) { fprintf(stderr, "solution mismatch\n"); exit(1); }
    for (int t = 0; t < J; t++) for (int p = 0; p < N; p++) if (fscanf(f, "%d", &sig[t * N + p]) != 1) return 0;
    for (int t = 0; t < J; t++) for (int p = 0; p < N; p++) if (fscanf(f, "%d", &mv[t * N + p]) != 1) return 0;
    for (int i = 0; i < N * Q1; i++) if (fscanf(f, "%d", &hv[i]) != 1) return 0;
    fclose(f);
    for (int t = 0; t < J; t++) for (int p = 0; p < N; p++) sinv[t * N + sig[t * N + p]] = p;
    return 1;
}
int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: hexeval q\n"); return 1; }
    q = atoi(argv[1]);
    char fn[64]; sprintf(fn, "hex/hex_q%d.bin", q);
    FILE *f = fopen(fn, "rb"); int32_t h[3]; if (!f || fread(h, 4, 3, f) != 3) { fprintf(stderr, "no %s\n", fn); return 1; }
    N = h[1]; Q1 = q + 1; V = 2 * N;
    pl = malloc(4L * N * Q1); if (fread(pl, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1; fclose(f);
    m = getenv("M") ? atoi(getenv("M")) : 10;
    if (getenv("J")) J = atoi(getenv("J"));
    LANES = 64 / m; setup_masks();
    Dg = Q1 + J;
    sig = malloc(sizeof(int) * J * N); sinv = malloc(sizeof(int) * J * N); mv = malloc(sizeof(int) * J * N);
    hv = malloc(sizeof(int) * N * Q1);
    inn = malloc(sizeof(int) * (size_t)V * Dg); inw = malloc(sizeof(int) * (size_t)V * Dg);
    Wa = malloc(8L * V); Wb = malloc(8L * V);
    if (getenv("SEED")) rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 10; i++) rnd();
    for (int t = 0; t < J; t++) {
        for (int p = 0; p < N; p++) sig[t * N + p] = p;
        for (int p = N - 1; p > 0; p--) { int r = rnd() % (p + 1); int x = sig[t * N + p]; sig[t * N + p] = sig[t * N + r]; sig[t * N + r] = x; }
        for (int p = 0; p < N; p++) sinv[t * N + sig[t * N + p]] = p;
        for (int p = 0; p < N; p++) mv[t * N + p] = (int)(rnd() % m);
    }
    for (int i = 0; i < N * Q1; i++) hv[i] = (int)(rnd() % m);
    int hzero = getenv("HZERO") && atoi(getenv("HZERO"));
    if (hzero) for (int i = 0; i < N * Q1; i++) hv[i] = 0;
    if (getenv("IN") && !load(getenv("IN"))) { fprintf(stderr, "cannot load\n"); return 1; }
    /* check matchings are not on the point's own lines (simple graph) */
    build();
    long cur = cost_points(), best = cur;
    fprintf(stderr, "q=%d m=%d J=%d lift vertices %ld initial cost %ld\n", q, m, J, (long)V * m, cur);
    long iters = getenv("ITERS") ? atol(getenv("ITERS")) : 0;
    double T0 = getenv("TEMP0") ? atof(getenv("TEMP0")) : 3.0, T1 = getenv("TEMP1") ? atof(getenv("TEMP1")) : 0.2;
    char *out = getenv("OUT");
    int nvar_h = hzero ? 0 : N * Q1, nvar_m = J * N, nvar_s = J * N;
    long nv_tot = nvar_h + nvar_m + nvar_s;
    for (long it = 0; it < iters && best > 0; it++) {
        double temp = T0 * pow(T1 / T0, (double)it / iters);
        long r = rnd() % nv_tot;
        int kind, a1 = 0, a2 = 0, old = 0, t = 0;
        if (r < nvar_h) { kind = 0; a1 = r; old = hv[a1]; int nw; do nw = rnd() % m; while (nw == old); hv[a1] = nw; }
        else if (r < nvar_h + nvar_m) { kind = 1; r -= nvar_h; t = r / N; a1 = r % N; old = mv[t * N + a1]; int nw; do nw = rnd() % m; while (nw == old); mv[t * N + a1] = nw; }
        else { kind = 2; r -= nvar_h + nvar_m; t = r / N; a1 = r % N; a2 = rnd() % N; if (a1 == a2) continue;
            int l1 = sig[t * N + a1], l2 = sig[t * N + a2]; sig[t * N + a1] = l2; sig[t * N + a2] = l1; sinv[t * N + l2] = a1; sinv[t * N + l1] = a2;
            int v1 = mv[t * N + a1]; mv[t * N + a1] = mv[t * N + a2]; mv[t * N + a2] = v1; }
        build();
        long nc = cost_points();
        double u = (rnd() >> 11) * (1.0 / 9007199254740992.0);
        long cap = cur + (long)(-temp * log(u + 1e-300));
        if (nc <= cap) {
            cur = nc;
            if (cur < best) { best = cur; if (out) save(out, best); fprintf(stderr, "it %ld temp %.3f best %ld\n", it, temp, best); }
        } else {
            if (kind == 0) hv[a1] = old;
            else if (kind == 1) mv[t * N + a1] = old;
            else { int l1 = sig[t * N + a1], l2 = sig[t * N + a2]; sig[t * N + a1] = l2; sig[t * N + a2] = l1; sinv[t * N + l2] = a1; sinv[t * N + l1] = a2;
                int v1 = mv[t * N + a1]; mv[t * N + a1] = mv[t * N + a2]; mv[t * N + a2] = v1; }
            build();
        }
    }
    if (out && best == cur && iters == 0) save(out, cur);
    printf("RESULT q %d m %d J %d vertices %ld cost %ld\n", q, m, J, (long)V * m, cur);
    return 0;
}
