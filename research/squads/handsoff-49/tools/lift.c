/* lift: simulated annealing over voltage assignments of a base multigraph, for the (Delta, D) problem
   (big-squad-4-8 job). The lift of base vertex u is the fibre {u} x G; an edge (u, v, g) of the base gives the
   lift edges (u, x) ~ (v, x*g) for all x in G. G acts on the lift by left multiplication, transitively on each fibre,
   so the diameter is the largest eccentricity of the b vertices (u, e).

   Usage: lift BASE GROUP d D seconds seed [K] [OUT]
          lift BASE GROUP d D eval < VOLTAGES   (each stdin line: m group indices, one per base edge in file order,
                                                 tree edges included; prints the cost per line, or "invalid" if the
                                                 lift is not simple; env LIMIT=c stops counting above c)
     BASE  text file: "b m", then m lines "u v" (u == v: a loop, contributes 2 to the degree), optionally a third
           token: an integer = fixed voltage (group index) for that edge, or "s" on a loop = semi-edge (the voltage
           must be an involution; contributes 1 to the degree; the lift has edges (u,x) ~ (u,x*g)).
           Edges of a BFS spanning tree get voltage e unless NOTREE=1 (allowed because the base is connected).
     GROUP "cyc:n", "meta:m:k:r" (Z_m x|_r Z_k, (a,j)(b,l) = (a + r^j b, j + l), index a + m*j), or a file:
           text "N" then N rows of N integers (row g is g*h for h = 0..N-1, identity 0), or binary (name ends in .bin):
           int32 N then N*N uint16 (row-major), identity 0.
     K     candidates per move (best of K, default 8).
   Cost = sum over the b roots (u,e) of the number of lift vertices not within distance D, plus b*N*... for a
   non-bipartite lift (when the base is not bipartite, checked every evaluation; when BIP=0 not checked).
   Env: T0 (default 3), T1 (0.05), EPOCH (steps per cooling cycle, 20000), NOTREE, BIP (1), MAXEVALS, QUIET,
   ODDSTRIDE=s (draw only voltages g with floor(g/s) odd: for meta m k r tables, s = m gives odd j; use NOTREE=1 with it,
   since tree edges would otherwise get the identity, which is even).
   Stops at cost 0. If OUT is given, writes the best state found to OUT (solution) and OUT.edges (lift edge list,
   "n" then "u v", vertex (v,x) = v*N + x), cost 0 or not; exit code 0 iff cost 0.
   Always prints "RESULT ... best=<cost> n=<b*N>" at the end. Check OUT.edges with score48. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXB 8192
#define MAXE 16384
static int b, m, N, d, D, K = 8;
static uint16_t *MT; static int *INV;
static int eu[MAXE], ev[MAXE], efix[MAXE], esemi[MAXE], volt[MAXE], bestv[MAXE];
static int nfree, freeidx[MAXE];
static int ndart[MAXB], dto[MAXB][64], dedge[MAXB][64], dinv[MAXB][64];
static int *dist, *queue, *col; static int bip_base = 1, checkbip = 0;
static int *invol, ninvol;
static long long evals = 0;
static char gspec[256];
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void load_group(const char *s) {
    snprintf(gspec, sizeof gspec, "%s", s);
    if (!strncmp(s, "cyc:", 4)) {
        N = atoi(s + 4); MT = malloc((size_t)N * N * 2);
        for (int g = 0; g < N; g++) for (int h = 0; h < N; h++) MT[(size_t)g * N + h] = (g + h) % N;
    } else if (!strncmp(s, "meta:", 5)) {
        int mm, k, r; if (sscanf(s + 5, "%d:%d:%d", &mm, &k, &r) != 3) { fprintf(stderr, "bad meta\n"); exit(2); }
        N = mm * k; MT = malloc((size_t)N * N * 2);
        long *rp = malloc(k * sizeof(long)); rp[0] = 1 % mm; for (int j = 1; j < k; j++) rp[j] = rp[j - 1] * r % mm;
        if (rp[k - 1] * r % mm != 1 % mm) { fprintf(stderr, "r^k != 1 mod m\n"); exit(2); }
        for (int j = 0; j < k; j++) for (int a = 0; a < mm; a++) for (int l = 0; l < k; l++) for (int bb = 0; bb < mm; bb++)
            MT[(size_t)(a + mm * j) * N + bb + mm * l] = (uint16_t)((a + rp[j] * bb) % mm + mm * ((j + l) % k));
        free(rp);
    } else {
        FILE *f = fopen(s, "rb"); if (!f) { fprintf(stderr, "cannot open group %s\n", s); exit(2); }
        size_t L = strlen(s);
        if (L > 4 && !strcmp(s + L - 4, ".bin")) {
            int32_t n32; if (fread(&n32, 4, 1, f) != 1) exit(2); N = n32; MT = malloc((size_t)N * N * 2);
            if (fread(MT, 2, (size_t)N * N, f) != (size_t)N * N) { fprintf(stderr, "short group file\n"); exit(2); }
        } else {
            if (fscanf(f, "%d", &N) != 1) exit(2); MT = malloc((size_t)N * N * 2);
            for (size_t i = 0; i < (size_t)N * N; i++) { int x; if (fscanf(f, "%d", &x) != 1) { fprintf(stderr, "short group file\n"); exit(2); } MT[i] = x; }
        }
        fclose(f);
    }
    if (N > 65535) { fprintf(stderr, "N too large\n"); exit(2); }
    INV = malloc(N * sizeof(int));
    for (int g = 0; g < N; g++) { INV[g] = -1; for (int h = 0; h < N; h++) if (MT[(size_t)g * N + h] == 0) { INV[g] = h; break; } }
    for (int g = 0; g < N; g++) if (INV[g] < 0 || MT[g] != g || MT[(size_t)g * N] != g) { fprintf(stderr, "not a group table (identity/inverse) at %d\n", g); exit(2); }
    invol = malloc(N * sizeof(int)); ninvol = 0;
    for (int g = 1; g < N; g++) if (INV[g] == g) invol[ninvol++] = g;
}

static void load_base(const char *p) {
    FILE *f = fopen(p, "r"); if (!f) { fprintf(stderr, "cannot open base\n"); exit(2); }
    if (fscanf(f, "%d %d", &b, &m) != 2 || b > MAXB || m > MAXE) { fprintf(stderr, "bad base header\n"); exit(2); }
    char line[256]; if (!fgets(line, sizeof line, f)) {}
    for (int i = 0; i < m; i++) {
        if (!fgets(line, sizeof line, f)) { fprintf(stderr, "short base\n"); exit(2); }
        char t3[64] = ""; int n3 = sscanf(line, "%d %d %63s", &eu[i], &ev[i], t3);
        if (n3 < 2) { i--; continue; }
        efix[i] = -1; esemi[i] = 0;
        if (n3 == 3) { if (t3[0] == 's') esemi[i] = 1; else efix[i] = atoi(t3); }
        if (esemi[i] && eu[i] != ev[i]) { fprintf(stderr, "semi-edge must be a loop\n"); exit(2); }
    }
    fclose(f);
    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        dto[u][ndart[u]] = v; dedge[u][ndart[u]] = i; dinv[u][ndart[u]] = 0; ndart[u]++;
        if (!esemi[i]) { dto[v][ndart[v]] = u; dedge[v][ndart[v]] = i; dinv[v][ndart[v]] = 1; ndart[v]++; }
    }
    /* bipartite base? */
    static int c2[MAXB]; for (int u = 0; u < b; u++) c2[u] = -1; c2[0] = 0; static int qq[MAXB]; int h = 0, t = 0; qq[t++] = 0;
    while (h < t) { int u = qq[h++]; for (int j = 0; j < ndart[u]; j++) { int v = dto[u][j];
        if (c2[v] < 0) { c2[v] = 1 - c2[u]; qq[t++] = v; } else if (c2[v] == c2[u]) bip_base = 0; } }
    if (t != b) { fprintf(stderr, "base not connected\n"); exit(2); }
    /* spanning tree */
    static int intree[MAXE];
    if (!getenv("NOTREE") || !atoi(getenv("NOTREE"))) {
        static int seen[MAXB]; seen[0] = 1; h = t = 0; qq[t++] = 0;
        while (h < t) { int u = qq[h++]; for (int j = 0; j < ndart[u]; j++) { int v = dto[u][j], e = dedge[u][j];
            if (!seen[v] && efix[e] < 0) { seen[v] = 1; intree[e] = 1; qq[t++] = v; } } }
    }
    nfree = 0;
    for (int i = 0; i < m; i++) { if (intree[i]) efix[i] = 0; if (efix[i] < 0) freeidx[nfree++] = i; }
}

static inline int dvolt(int u, int j) { int g = volt[dedge[u][j]]; return dinv[u][j] ? INV[g] : g; }

/* simple lift: at every base vertex, darts to the same target have distinct voltages, loops not e, semi-edges involutions */
static int ok_at(int u) {
    for (int j = 0; j < ndart[u]; j++) {
        int g = dvolt(u, j), e = dedge[u][j];
        if (dto[u][j] == u && g == 0) return 0;
        if (esemi[e] && (g == 0 || INV[g] != g)) return 0;
        for (int i = 0; i < j; i++) if (dto[u][i] == dto[u][j] && dvolt(u, i) == g) return 0;
    }
    return 1;
}
static int ok_edge(int e) { return ok_at(eu[e]) && ok_at(ev[e]); }
static int oddstride = 0;   /* env ODDSTRIDE=s: only voltages g with (g / s) odd (meta index a + m*j: s = m, parity j) */
static int draw(int e) {
    for (int t = 0; t < 1000000; t++) {
        int g = esemi[e] ? (ninvol ? invol[rnd() % ninvol] : 0) : (int)(rnd() % N);
        if (!oddstride || ((g / oddstride) & 1)) return g;
    }
    return 0;
}

static int is_bip(void) {
    int n = b * N; for (int i = 0; i < n; i++) col[i] = -1;
    int h = 0, t = 0; col[0] = 0; queue[t++] = 0;
    while (h < t) { int s = queue[h++], u = s / N, x = s % N;
        for (int j = 0; j < ndart[u]; j++) { int y = dto[u][j] * N + MT[(size_t)x * N + dvolt(u, j)];
            if (col[y] < 0) { col[y] = 1 - col[s]; queue[t++] = y; } else if (col[y] == col[s]) return 0; } }
    return 1;
}

static int stampv = 0;
/* cost with abort: returns > lim as soon as partial cost exceeds lim */
static long cost(long lim) {
    evals++;
    long c = 0; int n = b * N;
    if (checkbip && !is_bip()) return (long)n * b + 1;
    for (int r = 0; r < b; r++) {
        stampv++;
        if (stampv == 0x7fffffff) { memset(dist, 0, n * sizeof(int)); stampv = 1; }
        int h = 0, t = 0, s0 = r * N; dist[s0] = stampv; queue[t++] = s0; int lev_end = t, lev = 0;
        while (h < t && lev < D) {
            int s = queue[h++], u = s / N, x = s % N;
            for (int j = 0; j < ndart[u]; j++) { int y = dto[u][j] * N + MT[(size_t)x * N + dvolt(u, j)];
                if (dist[y] != stampv) { dist[y] = stampv; queue[t++] = y; } }
            if (h == lev_end) { lev++; lev_end = t; }
        }
        c += n - t;
        if (c > lim) return c;
    }
    return c;
}

static void write_sol(const char *out, long c) {
    FILE *f = fopen(out, "w");
    fprintf(f, "# lift solution d=%d D=%d n=%d cost=%ld\nbase %d %d\ngroup %s %d\n", d, D, b * N, c, b, m, gspec, N);
    for (int i = 0; i < m; i++) fprintf(f, "e %d %d %d%s\n", eu[i], ev[i], volt[i], esemi[i] ? " s" : "");
    fclose(f);
    char p[1024]; snprintf(p, sizeof p, "%s.edges", out);
    f = fopen(p, "w"); fprintf(f, "%d\n", b * N);
    for (int i = 0; i < m; i++) for (int x = 0; x < N; x++) {
        int y = MT[(size_t)x * N + volt[i]];
        if (esemi[i] && y < x) continue;               /* semi-edge pairs x <-> xg: write once */
        fprintf(f, "%d %d\n", eu[i] * N + x, ev[i] * N + y);
    }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 6 || (argc < 7 && strcmp(argv[5], "eval"))) { fprintf(stderr, "usage: lift BASE GROUP d D seconds seed [K] [OUT] | lift BASE GROUP d D eval\n"); return 2; }
    load_group(argv[2]); load_base(argv[1]);
    d = atoi(argv[3]); D = atoi(argv[4]);
    if (!strcmp(argv[5], "eval")) {   /* batch mode: stdin lines of m voltages (edge order of BASE, all edges) -> cost */
        int n = b * N; dist = calloc(n, sizeof(int)); queue = malloc(n * sizeof(int)); col = malloc(n * sizeof(int));
        checkbip = !bip_base && !(getenv("BIP") && !atoi(getenv("BIP")));
        long lim = getenv("LIMIT") ? atol(getenv("LIMIT")) : (1L << 60);
        char *line = NULL; size_t cap = 0;
        while (getline(&line, &cap, stdin) > 0) {
            char *p = line, *q; int i = 0;
            for (; i < m; i++) { long x = strtol(p, &q, 10); if (q == p) break; volt[i] = (int)(((x % N) + N) % N); p = q; }
            if (i < m) continue;
            int ok = 1; for (int u = 0; u < b; u++) if (!ok_at(u)) ok = 0;
            if (!ok) { printf("invalid\n"); continue; }
            printf("%ld\n", cost(lim));
        }
        return 0;
    }
    double secs = atof(argv[5]); rs ^= (uint64_t)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 20; i++) rnd();
    if (argc > 7) K = atoi(argv[7]);
    const char *out = argc > 8 ? argv[8] : NULL;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 3.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
    long EPOCH = getenv("EPOCH") ? atol(getenv("EPOCH")) : 20000, MAXEV = getenv("MAXEVALS") ? atol(getenv("MAXEVALS")) : -1;
    int quiet = getenv("QUIET") ? atoi(getenv("QUIET")) : 0;
    checkbip = !bip_base && !(getenv("BIP") && !atoi(getenv("BIP")));
    oddstride = getenv("ODDSTRIDE") ? atoi(getenv("ODDSTRIDE")) : 0;
    for (int u = 0; u < b; u++) { int dg = 0; for (int j = 0; j < ndart[u]; j++) dg += 1; if (dg > d) { fprintf(stderr, "base vertex %d has degree %d > d\n", u, dg); return 2; } }
    int n = b * N; dist = calloc(n, sizeof(int)); queue = malloc(n * sizeof(int)); col = malloc(n * sizeof(int));
    /* initial voltages */
    for (int i = 0; i < m; i++) volt[i] = efix[i] >= 0 ? efix[i] : 0;
    for (int f = 0; f < nfree; f++) { int e = freeidx[f], tries = 0;
        do { volt[e] = draw(e); } while (!ok_edge(e) && ++tries < 100000); }
    for (int u = 0; u < b; u++) if (!ok_at(u)) { fprintf(stderr, "cannot make a simple lift (fixed voltages?)\n"); return 2; }
    long cur = cost(1L << 60), best = cur; memcpy(bestv, volt, sizeof volt);
    if (!quiet) printf("group %s N=%d base b=%d m=%d free=%d bip_base=%d n=%d start cost=%ld\n", gspec, N, b, m, nfree, bip_base, n, cur);
    double t0 = now(), tl = t0; long step = 0;
    while (best > 0 && nfree > 0) {
        if ((step & 255) == 0) { double tn = now(); if (tn - t0 > secs) break; if (MAXEV > 0 && evals > MAXEV) break;
            if (!quiet && tn - tl > 10) { printf("t=%.0f evals=%lld cur=%ld best=%ld\n", tn - t0, evals, cur, best); fflush(stdout); tl = tn; } }
        long ph = step % EPOCH;
        if (ph == 0 && step > 0) { memcpy(volt, bestv, sizeof volt); cur = best; }
        double T = T0 * pow(T1 / T0, (double)ph / EPOCH);
        int e = freeidx[rnd() % nfree], old = volt[e], bg = -1; long bc = 1L << 60;
        long lim = cur + (long)(T * 10) + 2;
        for (int k = 0; k < K; k++) {
            int g = draw(e);
            if (g == old) continue;
            volt[e] = g; if (!ok_edge(e)) continue;
            long c = cost(bc < lim ? bc : lim);
            if (c < bc) { bc = c; bg = g; }
        }
        volt[e] = old;
        if (bg >= 0 && (bc <= cur || rnd01() < exp(-(bc - cur) / T))) { volt[e] = bg; cur = bc;
            if (cur < best) { best = cur; memcpy(bestv, volt, sizeof volt);
                if (!quiet) { printf("t=%.1f evals=%lld best=%ld\n", now() - t0, evals, best); fflush(stdout); } } }
        step++;
    }
    memcpy(volt, bestv, sizeof volt);
    if (nfree == 0) best = cost(1L << 60);
    printf("RESULT d=%d D=%d group=%s base=%s n=%d best=%ld evals=%lld time=%.1f\n", d, D, gspec, argv[1], n, best, evals, now() - t0);
    if (out) { write_sol(out, best); printf("wrote %s and %s.edges (cost %ld)\n", out, out, best); }
    return best == 0 ? 0 : 1;
}
