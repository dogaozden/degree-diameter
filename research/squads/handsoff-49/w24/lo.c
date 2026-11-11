/* w24 lo: voltage-lift optimizer for small bipartite bases over a group table (w24 card, handsoff-49).
   Lift convention (as w16 quot.py / lift_check.py): base edge (u,v) with voltage g gives lift edges (u,x) ~ (v, g*x).
   Left multiplication by h is NOT an automorphism here; right multiplication by G is, so the lift is determined by
   the balls of radius D around (u,e) for the b base roots u. Walk bitsets: S[y][g] has bit x iff a walk of exact length t
   from (x,e) reaches (y,g); ACC = union over t = 0..D is the exact ball. cost = sum_u (b*K - |ball(u)|).
   Gauge: tree voltages are fixed to the identity; the m-b+1 cotree voltages are free.

   Usage: lo BASE GROUP.bin D mode iters seed T0 T1 OUTPREFIX [VOLTFILE]
     BASE: first line 'b m', then m lines 'u v' (bipartite, connected, simple or multi).
     mode sa   : simulated annealing, iters single-voltage moves, geometric T0 -> T1, random start (or VOLTFILE start)
     mode eval : prints cost of the VOLTFILE assignment (m integers, group indices, base edge order; tree entries ignored)
   On cost 0 writes OUTPREFIX.edges (n = b*K) and OUTPREFIX.volt; prints RESULT FOUND iters=... time=...
   Otherwise prints RESULT best=<cost> iters=... time=... and writes OUTPREFIX.best.volt. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXB 64
#define MAXK 2048
#define MAXE 256

static int b, m, K, D;
static uint16_t *MT;
static int *INV;
static int eu[MAXE], ev[MAXE], volt[MAXE], istree[MAXE];
static int cot[MAXE], ncot;
static uint16_t *perm; /* perm[a*K + g] for dart a */
static int asrc[2 * MAXE], adst[2 * MAXE];
static uint64_t *S1, *S2, *ACC;

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double rndu(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static void read_group(const char *fn) {
    FILE *f = fopen(fn, "rb");
    if (!f) { perror(fn); exit(1); }
    int32_t n; if (fread(&n, 4, 1, f) != 1) exit(1);
    if (n > MAXK) { fprintf(stderr, "group order %d > %d\n", n, MAXK); exit(1); }
    K = n;
    MT = malloc(sizeof(uint16_t) * (size_t)K * K);
    INV = malloc(sizeof(int) * K);
    if (fread(MT, 2, (size_t)K * K, f) != (size_t)K * K) { fprintf(stderr, "short group file\n"); exit(1); }
    fclose(f);
    for (int g = 0; g < K; g++) for (int h = 0; h < K; h++) if (MT[g * K + h] == 0) INV[g] = h;
}

static void set_perm(int i) {
    int a = volt[i], ai = INV[a];
    for (int g = 0; g < K; g++) {
        perm[(2 * i) * K + g] = MT[a * K + g];        /* (u,g) -> (v, a g) */
        perm[(2 * i + 1) * K + g] = MT[ai * K + g];   /* (v,g) -> (u, a^-1 g) */
    }
}

/* returns total far pairs: sum over roots of (b*K - ball size) */
static long eval_cost(void) {
    size_t nb = (size_t)b * K;
    memset(ACC, 0, sizeof(uint64_t) * nb);
    memset(S1, 0, sizeof(uint64_t) * nb);
    for (int x = 0; x < b; x++) { S1[x * K + 0] |= 1ULL << x; ACC[x * K + 0] |= 1ULL << x; }
    uint64_t *cur = S1, *nxt = S2;
    for (int t = 1; t <= D; t++) {
        memset(nxt, 0, sizeof(uint64_t) * nb);
        int any = 0;
        for (int a = 0; a < 2 * m; a++) {
            const uint64_t *sb = cur + (size_t)asrc[a] * K;
            uint64_t *db = nxt + (size_t)adst[a] * K;
            const uint16_t *pm = perm + (size_t)a * K;
            for (int g = 0; g < K; g++) {
                uint64_t s = sb[g];
                if (!s) continue;
                db[pm[g]] |= s;
                any = 1;
            }
        }
        if (!any) break;
        for (size_t j = 0; j < nb; j++) ACC[j] |= nxt[j];
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long have = 0;
    for (size_t j = 0; j < nb; j++) have += __builtin_popcountll(ACC[j]);
    return (long)b * (long)b * K - have;
}

static void write_edges(const char *fn) {
    FILE *f = fopen(fn, "w");
    fprintf(f, "%d\n", b * K);
    for (int i = 0; i < m; i++)
        for (int g = 0; g < K; g++) fprintf(f, "%d %d\n", eu[i] * K + g, ev[i] * K + MT[volt[i] * K + g]);
    fclose(f);
}

static void write_volt(const char *fn) {
    FILE *f = fopen(fn, "w");
    for (int i = 0; i < m; i++) fprintf(f, "%d ", volt[i]);
    fprintf(f, "\n");
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: lo BASE GROUP.bin D mode iters seed T0 T1 OUTPREFIX [VOLTFILE]\n"); return 2; }
    FILE *bf = fopen(argv[1], "r");
    if (!bf) { perror(argv[1]); return 2; }
    int n, me; if (fscanf(bf, "%d %d", &n, &me) != 2) return 2;
    b = n; m = 0;
    int a0, a1;
    while (fscanf(bf, "%d %d", &a0, &a1) == 2) { if (m >= MAXE) return 2; eu[m] = a0; ev[m] = a1; m++; }
    fclose(bf);
    if (b > MAXB) { fprintf(stderr, "base too big\n"); return 2; }
    read_group(argv[2]);
    D = atoi(argv[3]);
    const char *mode = argv[4];
    long iters = atol(argv[5]);
    uint64_t seed = (uint64_t)atoll(argv[6]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    double T0 = atof(argv[7]), T1 = atof(argv[8]);
    const char *out = argv[9];

    size_t nb = (size_t)b * K;
    S1 = malloc(sizeof(uint64_t) * nb); S2 = malloc(sizeof(uint64_t) * nb); ACC = malloc(sizeof(uint64_t) * nb);
    perm = malloc(sizeof(uint16_t) * (size_t)2 * m * K);
    for (int a = 0; a < 2 * m; a++) {
        int i = a / 2;
        asrc[a] = (a % 2 == 0) ? eu[i] : ev[i];
        adst[a] = (a % 2 == 0) ? ev[i] : eu[i];
    }
    int seen[MAXB] = {0}, queue[MAXB], qh = 0, qt = 0;
    seen[0] = 1; queue[qt++] = 0;
    while (qh < qt) {
        int u = queue[qh++];
        for (int i = 0; i < m; i++) {
            int w = -1;
            if (eu[i] == u) w = ev[i]; else if (ev[i] == u) w = eu[i];
            if (w >= 0 && !seen[w]) { seen[w] = 1; queue[qt++] = w; istree[i] = 1; }
        }
    }
    if (qt != b) { fprintf(stderr, "base not connected\n"); return 2; }
    ncot = 0;
    for (int i = 0; i < m; i++) { if (!istree[i]) cot[ncot++] = i; volt[i] = 0; }
    if (argc > 10) {
        FILE *vf = fopen(argv[10], "r");
        if (!vf) { perror(argv[10]); return 2; }
        for (int i = 0; i < m; i++) if (fscanf(vf, "%d", &volt[i]) != 1) { fprintf(stderr, "short volt file\n"); return 2; }
        fclose(vf);
    } else {
        for (int j = 0; j < ncot; j++) volt[cot[j]] = (int)(rnd() % K);
    }
    for (int i = 0; i < m; i++) set_perm(i);

    double t0 = now();
    if (!strcmp(mode, "eval")) {
        long c = eval_cost();
        printf("EVAL cost=%ld\n", c);
        return 0;
    }
    long cost = eval_cost(), best = cost;
    int *bestvol = malloc(sizeof(int) * m);
    memcpy(bestvol, volt, sizeof(int) * m);
    long it = 0;
    double lr = log(T1 / T0);
    if (!strcmp(mode, "sa")) {
        for (it = 0; it < iters && cost > 0; it++) {
            double T = T0 * exp(lr * (double)it / (double)iters);
            int c = cot[rnd() % ncot];
            int old = volt[c];
            int nv = (int)(rnd() % (K - 1));
            if (nv >= old) nv++;
            volt[c] = nv; set_perm(c);
            long nc = eval_cost();
            if (nc <= cost || rndu() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
                if (cost < best) { best = cost; memcpy(bestvol, volt, sizeof(int) * m); }
            } else { volt[c] = old; set_perm(c); }
        }
    }
    double el = now() - t0;
    if (best == 0) {
        memcpy(volt, bestvol, sizeof(int) * m); for (int i = 0; i < m; i++) set_perm(i);
        char fn[512]; snprintf(fn, sizeof fn, "%s.edges", out); write_edges(fn);
        snprintf(fn, sizeof fn, "%s.volt", out); write_volt(fn);
        printf("RESULT FOUND iters=%ld time=%.2f\n", it, el);
    } else {
        char fn[512]; snprintf(fn, sizeof fn, "%s.best.volt", out);
        memcpy(volt, bestvol, sizeof(int) * m); write_volt(fn);
        printf("RESULT best=%ld iters=%ld time=%.2f\n", best, it, el);
    }
    return 0;
}
