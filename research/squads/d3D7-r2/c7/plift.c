/* plift: permutation-voltage lifts of the 2+2 base (edges 0-2, 0-2, 0-3, 1-2, 1-3, 1-3), card r2c7.
   Vertices (u,x), u in 0..3 (whites 0,1; blacks 2,3), x in 0..m-1, n = 4m.
   Edges: e0 (0,x)-(2,x); e1 (0,x)-(2,p1[x]); e2 (0,x)-(3,x); e3 (1,x)-(2,x); e4 (1,x)-(3,p4[x]); e5 (1,x)-(3,p5[x]).
   Modes:
     plift cal GROUPS id v1..v6          regular lift over a group table, voltages as liftedges.py (calibration)
     plift exh agl q OUT                 exhaustive over AGL(1,q) (p1 = x+1 WLOG, p4, p5 over all of AGL)
     plift sa FAM q secs seed T0 T1 OUT  annealing over the three maps in FAM = agl | psl | pgl (m = q or q+1)
   Cost = ordered pairs at distance > 7 (bit-parallel all-pairs, as sa3.c); non-simple lifts get cost 1e6 + clashes. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXN 300
#define W ((MAXN + 63) / 64)
#define MAXM 80
static int n, m, nb[MAXN][3];
static uint64_t ra[MAXN][W], rb[MAXN][W];
static int nw = 0;

static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }

static long cost_graph(void) {
    uint64_t (*cur)[W] = ra, (*nx)[W] = rb;
    for (int x = 0; x < n; x++) { memset(cur[x], 0, nw * 8); cur[x][x >> 6] |= 1ULL << (x & 63); }
    for (int t = 0; t < 7; t++) {
        for (int x = 0; x < n; x++) {
            const uint64_t *a = cur[nb[x][0]], *b = cur[nb[x][1]], *c = cur[nb[x][2]], *s = cur[x];
            for (int w = 0; w < nw; w++) nx[x][w] = s[w] | a[w] | b[w] | c[w];
        }
        uint64_t (*tmp)[W] = cur; cur = nx; nx = tmp;
    }
    long reached = 0;
    for (int x = 0; x < n; x++) for (int w = 0; w < nw; w++) reached += __builtin_popcountll(cur[x][w]);
    return (long)n * n - reached;
}

/* edge list of the lift (also fills nb). returns number of multi-edge clashes */
static int E[MAXN * 3 / 2][2], ne;
static int build(int mm, const int *p1, const int *p4, const int *p5) {
    m = mm; n = 4 * m; nw = (n + 63) / 64; ne = 0;
    int clash = 0;
    for (int x = 0; x < m; x++) {
        E[ne][0] = 0 * m + x; E[ne][1] = 2 * m + x; ne++;
        E[ne][0] = 0 * m + x; E[ne][1] = 2 * m + p1[x]; ne++;
        E[ne][0] = 0 * m + x; E[ne][1] = 3 * m + x; ne++;
        E[ne][0] = 1 * m + x; E[ne][1] = 2 * m + x; ne++;
        E[ne][0] = 1 * m + x; E[ne][1] = 3 * m + p4[x]; ne++;
        E[ne][0] = 1 * m + x; E[ne][1] = 3 * m + p5[x]; ne++;
        if (p1[x] == x) clash++;
        if (p4[x] == p5[x]) clash++;
    }
    int dg[MAXN] = {0};
    for (int i = 0; i < ne; i++) {
        int a = E[i][0], b = E[i][1];
        if (dg[a] >= 3 || dg[b] >= 3) return 1000000;
        nb[a][dg[a]++] = b; nb[b][dg[b]++] = a;
    }
    return clash;
}
static long full_cost(int mm, const int *p1, const int *p4, const int *p5) {
    int c = build(mm, p1, p4, p5);
    if (c) return 1000000L + c;
    return cost_graph();
}
static void save(const char *path) {
    FILE *f = fopen(path, "w"); fprintf(f, "%d\n", n);
    for (int i = 0; i < ne; i++) fprintf(f, "%d %d\n", E[i][0], E[i][1]);
    fclose(f);
}

/* ---- groups as permutation lists on m points ---- */
static int G_N = 0, G_m = 0;
static unsigned char *G_perm = NULL;      /* G_N * G_m */
static void add_perm(const int *p, int mm) { /* store */
    static int cap = 0;
    if (G_N == cap) { cap = cap ? 2 * cap : 1024; G_perm = realloc(G_perm, (size_t)cap * mm); }
    for (int x = 0; x < mm; x++) G_perm[(size_t)G_N * mm + x] = (unsigned char)p[x];
    G_N++;
}
static int inv(int a, int q) { /* a^{-1} mod q */
    int t = 0, nt = 1, r = q, nr = ((a % q) + q) % q;
    while (nr) { int qq = r / nr, tmp; tmp = t - qq * nt; t = nt; nt = tmp; tmp = r - qq * nr; r = nr; nr = tmp; }
    return (t % q + q) % q;
}
static void make_agl(int q) { /* AGL(1,q), m = q */
    int p[MAXM];
    G_m = q; G_N = 0;
    for (int a = 1; a < q; a++) for (int b = 0; b < q; b++) {
        for (int x = 0; x < q; x++) p[x] = (a * x + b) % q;
        add_perm(p, q);
    }
}
static void make_proj(int q, int pgl) { /* PGL(2,q) or PSL(2,q) on q+1 points, point q = infinity */
    int mm = q + 1; int p[MAXM];
    G_m = mm; G_N = 0;
    int isq[MAXM] = {0};
    for (int x = 1; x < q; x++) isq[(x * x) % q] = 1;
    /* enumerate matrices up to scalar: first nonzero entry of (a,b,c,d) equals 1 */
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) for (int c = 0; c < q; c++) for (int d = 0; d < q; d++) {
        int ent[4] = {a, b, c, d}, f = -1;
        for (int i = 0; i < 4; i++) if (ent[i]) { f = i; break; }
        if (f < 0 || ent[f] != 1) continue;
        int det = ((a * d - b * c) % q + q) % q;
        if (det == 0) continue;
        if (!pgl && !isq[det]) continue;
        for (int x = 0; x < q; x++) {
            int num = (a * x + b) % q, den = (c * x + d) % q;
            p[x] = den ? (num * inv(den, q)) % q : q;
        }
        /* infinity */
        p[q] = c ? (a * inv(c, q)) % q : q;
        add_perm(p, mm);
    }
    if (!pgl) { /* PSL: det square; sanity: size q(q^2-1)/2 */ }
    fprintf(stderr, "group size %d on %d points\n", G_N, mm);
}
static inline const int *gp(int i, int *buf) { /* perm i as int array in buf */
    for (int x = 0; x < G_m; x++) buf[x] = G_perm[(size_t)i * G_m + x];
    return buf;
}
static int is_fpf(int i) { for (int x = 0; x < G_m; x++) if (G_perm[(size_t)i * G_m + x] == x) return 0; return 1; }

static void usage(void) { fprintf(stderr,
  "usage: plift cal GROUPS id v1..v6 | plift exh agl q OUT | plift sa agl|psl|pgl q secs seed T0 T1 OUT [sample N]\n"); exit(2); }

/* read a group table block (see liftedges.py) and make the regular right-multiplication perms */
static int read_group_perms(const char *path, int gid, int *N_out, int **mul_out) {
    FILE *f = fopen(path, "r"); if (!f) return 0;
    char tok[64]; int N, g;
    while (fscanf(f, "%63s", tok) == 1) {
        if (strcmp(tok, "G")) continue;
        if (fscanf(f, "%d %d %63s", &N, &g, tok) != 3) break;
        /* skip rest of the header line */
        int c; while ((c = fgetc(f)) != '\n' && c != EOF) {}
        if (g == gid) {
            int *mul = malloc(sizeof(int) * N * N);
            for (int i = 0; i < N * N; i++) if (fscanf(f, "%d", &mul[i]) != 1) return 0;
            *N_out = N; *mul_out = mul; fclose(f); return 1;
        }
        for (int i = 0; i < N * N; i++) { int t; if (fscanf(f, "%d", &t) != 1) break; }
    }
    fclose(f); return 0;
}

int main(int argc, char **argv) {
    if (argc < 2) usage();
    static int p1[MAXM], p4[MAXM], p5[MAXM];
    if (!strcmp(argv[1], "cal")) {
        if (argc < 10) usage();
        int N; int *mul;
        if (!read_group_perms(argv[2], atoi(argv[3]), &N, &mul)) { fprintf(stderr, "group not found\n"); return 2; }
        int v[6]; for (int i = 0; i < 6; i++) v[i] = atoi(argv[4 + i]);
        /* right multiplication x -> x*a = mul[x][a]; edge e lifts with voltage v[e] (liftedges.py convention) */
        for (int x = 0; x < N; x++) { p1[x] = mul[x * N + v[1]]; p4[x] = mul[x * N + v[4]]; p5[x] = mul[x * N + v[5]];
                                      if (mul[x * N + v[0]] != x || mul[x * N + v[2]] != x || mul[x * N + v[3]] != x) { fprintf(stderr, "tree voltages must be 0 here\n"); return 2; } }
        long c = full_cost(N, p1, p4, p5);
        printf("cal N=%d n=%d cost=%ld\n", N, 4 * N, c);
        if (argc > 10) save(argv[10]);
        return 0;
    }
    if (!strcmp(argv[1], "exh")) {
        if (argc < 5) usage();
        int q = atoi(argv[3]);
        make_agl(q);
        int mm = q;
        /* p1 = x+1 (WLOG: conjugating by x -> a x + c moves any translation to +1 with a = 1/b) */
        for (int x = 0; x < mm; x++) p1[x] = (x + 1) % mm;
        long nev = 0, nclash = 0;
        int bi = -1, bj = -1; long bestc = 1L << 60;
        for (int i = 0; i < G_N; i++) {
            gp(i, p4);
            for (int j = 0; j < G_N; j++) {
                gp(j, p5);
                long c = full_cost(mm, p1, p4, p5);
                nev++;
                if (c >= 1000000) { nclash++; continue; }
                if (c < bestc) { bestc = c; bi = i; bj = j; printf("best %ld (p4=%d p5=%d) n=%d\n", c, i, j, 4 * mm); fflush(stdout); }
                if (c == 0) { printf("FOUND i=%d j=%d\n", i, j); break; }
            }
            if (bestc == 0) break;
        }
        printf("exh agl q=%d evals=%ld clashes=%ld best=%ld\n", q, nev, nclash, bestc);
        if (bi >= 0 && argc > 4) {
            gp(bi, p4); gp(bj, p5); full_cost(mm, p1, p4, p5); save(argv[4]);
        }
        return 0;
    }
    if (!strcmp(argv[1], "sa")) {
        if (argc < 9) usage();
        const char *fam = argv[2]; int q = atoi(argv[3]); double secs = atof(argv[4]);
        rng ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; xr(); xr();
        double T0 = atof(argv[6]), T1 = atof(argv[7]); const char *out = argv[8];
        if (!strcmp(fam, "agl")) make_agl(q);
        else make_proj(q, !strcmp(fam, "pgl"));
        int mm = G_m;
        /* p1: fixed-point-free element; p4, p5 arbitrary */
        int *fp = malloc(sizeof(int) * G_N); int nfp = 0; for (int i = 0; i < G_N; i++) if (is_fpf(i)) fp[nfp++] = i;
        fprintf(stderr, "%d fixed-point-free elements\n", nfp);
        if (nfp == 0) { printf("no fpf\n"); return 0; }
        int s1 = fp[xr() % nfp], s4 = xr() % G_N, s5 = xr() % G_N;
        gp(s1, p1); gp(s4, p4); gp(s5, p5);
        long c = full_cost(mm, p1, p4, p5), best = c;
        int bs[3] = {s1, s4, s5};
        clock_t st = clock(); long it = 0; double cyc = 60.0;
        printf("start cost %ld\n", c); fflush(stdout);
        if (c < 1000000) { save(out); }
        for (;;) {
            double el = (double)(clock() - st) / CLOCKS_PER_SEC;
            if (el > secs) break;
            double fr = fmod(el, cyc) / cyc, T = T0 * pow(T1 / T0, fr);
            int k = xr() % 3, cand;
            if (k == 0) cand = fp[xr() % nfp]; else cand = xr() % G_N;
            int old = bs[k]; bs[k] = cand;
            int *pp[3] = {p1, p4, p5};
            gp(bs[0], p1); gp(bs[1], p4); gp(bs[2], p5);
            (void)pp;
            if (k == 0 && !is_fpf(cand)) { bs[k] = old; continue; }
            long c2 = full_cost(mm, p1, p4, p5); it++;
            if (c2 <= c || ur() < exp((double)(c - c2) / T)) {
                c = c2;
                if (c < best) { best = c; save(out); printf("t=%.1f it=%ld best %ld\n", el, it, best); fflush(stdout); if (best == 0) { printf("FOUND\n"); break; } }
            } else bs[k] = old;
        }
        printf("end best %ld its %ld\n", best, it);
        return 0;
    }
    usage();
    return 0;
}
