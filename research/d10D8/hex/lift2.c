/* lift.c: voltage lifts of B = GH(q) + j perfect matchings (points -> lines) by a group G of order m <= 64.
 *
 * Lift vertex (x, h), h in G.  Base edge x->y with voltage g gives (x, h) ~ (y, h*g); y->x carries g^-1.
 * G acts by left multiplication, so the lift's diameter is max over base sources s of ecc((s, e)).
 * Cost of a source s = sum over base vertices y of (m - #sheets of y within distance D of (s,e)).
 * Computed with sheet bitmasks: W_{k+1}(y) = U_{x~y} W_k(x)*g(x->y)  (walks of length exactly k; in a bipartite
 * graph "within D" = W_{D-1} | W_D).
 *
 * Group: GROUP="cyc m" | "prod a b" (Z_a x Z_b) | "dih n" (dihedral of order 2n) | "file path" (m then m*m table,
 * element 0 = identity).
 * Variables: voltage of every hexagon edge (flag), voltage of every matching edge, the matchings themselves.
 * Modes (env): HZERO=1 hexagon voltages fixed to e; MCONST=1 matching t has the constant voltage T_t (env T="1 2"),
 *   NOSWAP=1 matchings fixed; SRC=k evaluate on k random sources (resampled every RESAMPLE steps) instead of all;
 *   ITERS, SEED, TEMP0, TEMP1, D (default 7), J (matchings, default 1), OUT (solution file), IN (start solution).
 * Solution file: "q j m D" line, group spec line, then j lines of sigma_t (point -> line index), then j lines of
 *   matching voltages (per point), then one line of hexagon voltages per flag (line-major, k-th point of line l).
 * usage: lift q   (all settings by env)
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

static int q, N, Q1, J = 1, m, D = 7, V, LANES;
static int32_t *pl;            /* N x Q1: points on line l */
static int *lnp;               /* N x Q1: lines on point p */
static int *flagidx;           /* N x Q1: for point p and its k-th line, the flag index (l*Q1 + pos) */
static int mul[64][64], inv_[64];
static uint64_t ptab[64][8][256];  /* ptab[g][b][byte] = (byte b of mask) * g, as mask */
static int *sig, *sinv;        /* J x N */
static int *mv;                /* J x N voltage of matching edge (p, sig(p)) in direction point->line */
static int *hv;                /* N*Q1 voltage of flag (l, pos) in direction point->line */
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline uint64_t act(uint64_t R, int g) {   /* R * g */
    uint64_t o = 0; int b = 0;
    while (R) { o |= ptab[g][b][R & 255]; R >>= 8; b++; }
    return o;
}

static void make_group(const char *spec) {
    char kind[16]; int a = 0, b = 0;
    sscanf(spec, "%15s %d %d", kind, &a, &b);
    if (!strcmp(kind, "cyc")) { m = a; for (int x = 0; x < m; x++) for (int y = 0; y < m; y++) mul[x][y] = (x + y) % m; }
    else if (!strcmp(kind, "prod")) { m = a * b;
        for (int x = 0; x < m; x++) for (int y = 0; y < m; y++) mul[x][y] = ((x / b + y / b) % a) * b + (x % b + y % b) % b; }
    else if (!strcmp(kind, "dih")) { int n = a; m = 2 * n;   /* element (s, r) = s*n + r : r^r' rotation, s reflection */
        for (int x = 0; x < m; x++) for (int y = 0; y < m; y++) {
            int s1 = x / n, r1 = x % n, s2 = y / n, r2 = y % n;
            int r = s2 ? ((n - r1) + r2) % n : (r1 + r2) % n;   /* (s1 r1)(s2 r2): rho^r1 sigma^s1 rho^r2 sigma^s2 ... */
            /* use x = rho^r1 sigma^s1; sigma rho^r2 = rho^-r2 sigma */
            r = s1 ? (r1 - r2 + n) % n : (r1 + r2) % n;
            mul[x][y] = ((s1 + s2) % 2) * n + r; } }
    else if (!strcmp(kind, "file")) { char path[256]; sscanf(spec, "%*s %255s", path); FILE *f = fopen(path, "r");
        if (!f || fscanf(f, "%d", &m) != 1) { fprintf(stderr, "bad group file\n"); exit(1); }
        for (int x = 0; x < m; x++) for (int y = 0; y < m; y++) if (fscanf(f, "%d", &mul[x][y]) != 1) exit(1); fclose(f); }
    else { fprintf(stderr, "unknown group\n"); exit(1); }
    if (m > 64 || m < 1) { fprintf(stderr, "m out of range\n"); exit(1); }
    for (int x = 0; x < m; x++) { inv_[x] = -1; for (int y = 0; y < m; y++) if (mul[x][y] == 0) inv_[x] = y; if (inv_[x] < 0) { fprintf(stderr, "not a group\n"); exit(1); } }
    for (int x = 0; x < m; x++) for (int y = 0; y < m; y++) for (int z = 0; z < m; z++)
        if (mul[mul[x][y]][z] != mul[x][mul[y][z]]) { fprintf(stderr, "not associative\n"); exit(1); }
    LANES = 64 / m;
    for (int g = 0; g < m; g++) for (int b = 0; b < 8; b++) for (int by = 0; by < 256; by++) {
        uint64_t o = 0; for (int t = 0; t < 8; t++) if (by >> t & 1) { int pos = b * 8 + t, lane = pos / m, h = pos % m;
            if (lane < LANES) o |= 1ULL << (lane * m + mul[h][g]); }
        ptab[g][b][by] = o; }
}

/* adjacency of B with voltages, rebuilt per evaluation from the variable arrays (cheap) */
static int Dg;                 /* degree of B = Q1 + J */
static int *nb; static int *nv;   /* V x Dg neighbour, voltage on the arc from v to nb */
static void build_adj(void) {
    for (int p = 0; p < N; p++) {
        for (int k = 0; k < Q1; k++) { int fi = flagidx[p * Q1 + k]; int l = fi / Q1; nb[p * Dg + k] = N + l; nv[p * Dg + k] = hv[fi]; }
        for (int t = 0; t < J; t++) { nb[p * Dg + Q1 + t] = N + sig[t * N + p]; nv[p * Dg + Q1 + t] = mv[t * N + p]; }
    }
    for (int l = 0; l < N; l++) {
        for (int k = 0; k < Q1; k++) { int p = pl[l * Q1 + k]; nb[(N + l) * Dg + k] = p; nv[(N + l) * Dg + k] = inv_[hv[l * Q1 + k]]; }
        for (int t = 0; t < J; t++) { int p = sinv[t * N + l]; nb[(N + l) * Dg + Q1 + t] = p; nv[(N + l) * Dg + Q1 + t] = inv_[mv[t * N + p]]; }
    }
}
static uint64_t *Wa, *Wb, *Acc;
static uint64_t FULL;
static int *srcs; static int nsrc;
static long group_cost(const int *ss, int ns, long cap) {   /* ns <= LANES sources, one lane each */
    memset(Wa, 0, sizeof(uint64_t) * V); memset(Acc, 0, sizeof(uint64_t) * V);
    for (int k = 0; k < ns; k++) { Wa[ss[k]] |= 1ULL << (k * m); }
    for (int y = 0; y < V; y++) Acc[y] = Wa[y];
    for (int k = 1; k <= D; k++) {
        for (int y = 0; y < V; y++) {
            uint64_t o = 0; const int *a = nb + (size_t)y * Dg, *g = nv + (size_t)y * Dg;
            for (int i = 0; i < Dg; i++) { uint64_t R = Wa[a[i]]; if (R) o |= act(R, inv_[g[i]]); }
            Wb[y] = o;
        }
        uint64_t *t = Wa; Wa = Wb; Wb = t;
        if (k >= D - 1) for (int y = 0; y < V; y++) Acc[y] |= Wa[y];
    }
    uint64_t lm = (ns * m == 64) ? ~0ULL : ((1ULL << (ns * m)) - 1);
    long c = 0, per = (long)ns * m;
    for (int y = 0; y < V; y++) { c += per - __builtin_popcountll(Acc[y] & lm); if (c > cap) return c; }
    return c;
}
static long total_cost(long cap) {
    build_adj();
    long c = 0;
    for (int i = 0; i < nsrc; i += LANES) { int ns = nsrc - i < LANES ? nsrc - i : LANES; c += group_cost(srcs + i, ns, cap - c); if (c > cap) return c; }
    return c;
}

static void save(const char *fn, const char *gspec, long cost) {
    FILE *f = fopen(fn, "w");
    fprintf(f, "%d %d %d %d %ld\n%s\n", q, J, m, D, cost, gspec);
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
    if (argc < 2) { fprintf(stderr, "usage: lift q (env GROUP, J, D, ...)\n"); return 1; }
    q = atoi(argv[1]);
    char fn[64]; sprintf(fn, "hex/hex_q%d.bin", q);
    FILE *f = fopen(fn, "rb"); int32_t h[3]; if (!f || fread(h, 4, 3, f) != 3) { fprintf(stderr, "no %s\n", fn); return 1; }
    N = h[1]; Q1 = q + 1; V = 2 * N;
    pl = malloc(4L * N * Q1); if (fread(pl, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1; fclose(f);
    lnp = malloc(sizeof(int) * N * Q1); flagidx = malloc(sizeof(int) * N * Q1);
    { int *cnt = calloc(N, sizeof(int));
      for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { int p = pl[l * Q1 + k]; lnp[p * Q1 + cnt[p]] = l; flagidx[p * Q1 + cnt[p]] = l * Q1 + k; cnt[p]++; } }
    const char *gspec = getenv("GROUP") ? getenv("GROUP") : "cyc 3";
    make_group(gspec); FULL = (m == 64) ? ~0ULL : ((1ULL << m) - 1);
    if (getenv("J")) J = atoi(getenv("J"));
    if (getenv("D")) D = atoi(getenv("D"));
    long iters = getenv("ITERS") ? atol(getenv("ITERS")) : 0;
    if (getenv("SEED")) rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 10; i++) rnd();
    int hzero = getenv("HZERO") && atoi(getenv("HZERO"));
    int mconst = getenv("MCONST") && atoi(getenv("MCONST"));
    int noswap = getenv("NOSWAP") && atoi(getenv("NOSWAP"));
    int T[16] = {1, 2, 3, 4, 5, 6, 7, 8};
    if (getenv("T")) { char *p = getenv("T"), *e; for (int t = 0; t < J; t++) { T[t] = (int)strtol(p, &e, 10); p = e; } }
    Dg = Q1 + J;
    sig = malloc(sizeof(int) * J * N); sinv = malloc(sizeof(int) * J * N); mv = malloc(sizeof(int) * J * N);
    hv = malloc(sizeof(int) * N * Q1);
    nb = malloc(sizeof(int) * (size_t)V * Dg); nv = malloc(sizeof(int) * (size_t)V * Dg);
    Wa = malloc(8L * V); Wb = malloc(8L * V); Acc = malloc(8L * V);
    /* initial state */
    for (int t = 0; t < J; t++) {
        for (int p = 0; p < N; p++) sig[t * N + p] = p;
        for (int p = N - 1; p > 0; p--) { int r = rnd() % (p + 1); int x = sig[t * N + p]; sig[t * N + p] = sig[t * N + r]; sig[t * N + r] = x; }
        for (int p = 0; p < N; p++) sinv[t * N + sig[t * N + p]] = p;
        for (int p = 0; p < N; p++) mv[t * N + p] = mconst ? T[t] % m : (int)(rnd() % m);
    }
    for (int i = 0; i < N * Q1; i++) hv[i] = hzero ? 0 : (int)(rnd() % m);
    if (getenv("IN") && !load(getenv("IN"))) { fprintf(stderr, "cannot load %s\n", getenv("IN")); return 1; }
    if (hzero) for (int i = 0; i < N * Q1; i++) hv[i] = 0;
    if (mconst) for (int t = 0; t < J; t++) for (int p = 0; p < N; p++) mv[t * N + p] = T[t] % m;
    int SRC = getenv("SRC") ? atoi(getenv("SRC")) : 0;
    long resample = getenv("RESAMPLE") ? atol(getenv("RESAMPLE")) : 1000;
    srcs = malloc(sizeof(int) * V);
    if (SRC <= 0 || SRC >= V) { nsrc = V; for (int i = 0; i < V; i++) srcs[i] = i; }
    else { nsrc = SRC; for (int i = 0; i < nsrc; i++) srcs[i] = rnd() % V; }
    double T0 = getenv("TEMP0") ? atof(getenv("TEMP0")) : 2.0, T1 = getenv("TEMP1") ? atof(getenv("TEMP1")) : 0.05;
    long cur = total_cost(1L << 60), best = cur;
    fprintf(stderr, "q=%d J=%d m=%d D=%d lift vertices %ld, sources %d, initial cost %ld\n", q, J, m, D, (long)V * m, nsrc, cur);
    char *out = getenv("OUT");
    int nvar_h = hzero ? 0 : N * Q1, nvar_m = mconst ? 0 : J * N, nvar_s = noswap ? 0 : J * N;
    long nv_tot = nvar_h + nvar_m + nvar_s;
    for (long it = 0; it < iters && best > 0 && nv_tot > 0; it++) {
        if (SRC > 0 && SRC < V && it % resample == 0 && it) {
            for (int i = 0; i < nsrc; i++) srcs[i] = rnd() % V;
            cur = total_cost(1L << 60);
        }
        double temp = T0 * pow(T1 / T0, (double)it / iters);
        long r = rnd() % nv_tot;
        int kind, a1 = 0, a2 = 0, old = 0, t = 0;
        if (r < nvar_h) { kind = 0; a1 = r; old = hv[a1]; int nwv; do nwv = rnd() % m; while (nwv == old && m > 1); hv[a1] = nwv; }
        else if (r < nvar_h + nvar_m) { kind = 1; r -= nvar_h; t = r / N; a1 = r % N; old = mv[t * N + a1]; int nwv; do nwv = rnd() % m; while (nwv == old && m > 1); mv[t * N + a1] = nwv; }
        else { kind = 2; r -= nvar_h + nvar_m; t = r / N; a1 = r % N; a2 = rnd() % N; if (a1 == a2) continue;
            int l1 = sig[t * N + a1], l2 = sig[t * N + a2]; sig[t * N + a1] = l2; sig[t * N + a2] = l1; sinv[t * N + l2] = a1; sinv[t * N + l1] = a2;
            int v1 = mv[t * N + a1]; mv[t * N + a1] = mv[t * N + a2]; mv[t * N + a2] = v1; }
        double u = (rnd() >> 11) * (1.0 / 9007199254740992.0);
        long cap = cur + (long)(-temp * log(u + 1e-300));
        long nc = total_cost(cap);
        if (nc <= cap) {
            cur = nc;
            if (cur < best) { best = cur; if (out) save(out, gspec, best);
                fprintf(stderr, "it %ld temp %.3f best %ld\n", it, temp, best); }
        } else {
            if (kind == 0) hv[a1] = old;
            else if (kind == 1) mv[t * N + a1] = old;
            else { int l1 = sig[t * N + a1], l2 = sig[t * N + a2]; sig[t * N + a1] = l2; sig[t * N + a2] = l1; sinv[t * N + l2] = a1; sinv[t * N + l1] = a2;
                int v1 = mv[t * N + a1]; mv[t * N + a1] = mv[t * N + a2]; mv[t * N + a2] = v1; }
        }
    }
    /* final full check on all sources */
    nsrc = V; for (int i = 0; i < V; i++) srcs[i] = i;
    long full = total_cost(1L << 60);
    if (out && iters == 0) save(out, gspec, full);
    printf("RESULT q %d J %d m %d D %d vertices %ld best %ld fullcost %ld %s\n", q, J, m, D, (long)V * m, best, full, full == 0 ? "DIAMETER_OK" : "");
    return 0;
}
