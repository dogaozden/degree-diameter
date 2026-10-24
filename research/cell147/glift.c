/* glift.c: voltage lifts of B = GH(q) incidence graph + j point->line perfect matchings, by a group Gamma of
   order m <= 64, at diameter D (default 7). Cost = number of (source u in V(B), target (w,g)) with
   dist((u,e),(w,g)) > D in the lift (same-colour targets need <= D-1, opposite colour <= D).
   Lift convention: (x,g) ~ (w, g*h) for the dart x->w with voltage h; volt(w->x) = h^-1.
   Reach propagation: R_k(w) = set of g with a walk of length k from (u,e) to (w,g) (walks may backtrack, so
   R_k contains R_{k-2}); bitmask over Gamma.

   Usage: glift GHFILE j D seconds seed OUT
   Environment:
     GROUP   "cyc m" (default cyc 2j+2) | "ab a b ..." (direct product of cyclics) | "dih n" (order 2n) |
             "tab FILE" (m, then m lines of the right-multiplication table g*h, identity = 0)
     GHV     0 (default: polygon voltages identity, fixed) | free (annealed) | z2 (annealed among the
             elements of order <= 2 ... only for cyclic even m: values in {0, m/2})
     HV      dgq (matching t has the fixed voltage HT[t], default t) | free (annealed per edge)
     HT      "h1 h2 ..." voltages for HV=dgq (element indices)
     SIGMA   free (default; annealed by swaps) | fixed
     SAMPLE  sources per evaluation (default 0 = all base vertices)
     RESAMPLE steps between resampling (default 2000)
     T0, TEND temperatures (default 2, 0.05);  THREADS (default 1)
     INIT    file written by a previous run (OUT format) to start from
     EVAL    1: evaluate INIT (or the random start) once with all sources and exit
     EDGES   file: with EVAL=1 write the lift edge list (n, then "u v") for apsp
     TARGET  probability (0..1) that a swap move is targeted: a missed (s,w,g) is turned into a two-hop route
             s ~> u -hop a-> u' -hop b-> v' ~> w by one swap in matching b (j >= 2)
   OUT format: "glift q j m D" then group spec line, then per point p: sigma_1(p) h_1(p) ... sigma_j(p) h_j(p),
   then per flag (in GH file order: line l, k-th point): voltage of the dart point->line.
   Compile: gcc -O3 -march=native -fopenmp -o glift glift.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#ifdef _OPENMP
#include <omp.h>
#endif

typedef uint64_t u64;
static int P, q, J, D, m, NV, deg;
static int *lines;           /* lines[l*(q+1)+k] */
static int *ptl;             /* point -> its q+1 lines (index l), and position k of the point on that line */
static int *ptk;
static int *nbr;             /* nbr[w*deg+s] */
static int *vin;             /* incoming voltage on slot s of w */
static int *sig;             /* sig[t*P+p] = line index of sigma_t(p) */
static int *sinv;            /* sinv[t*P+l] = point with sigma_t = l */
static int *hv;              /* hv[t*P+p] = voltage of dart p -> sigma_t(p) */
static int *fv;              /* fv[l*(q+1)+k] = voltage of dart (point lines[l][k]) -> line l */
static int *mul, *ginv;      /* m x m right multiplication table, inverses */
static int cyclic;
static u64 FULL;
static u64 *ptab;            /* ptab[(h*8+b)*256+byte] */
static int nbytes;
static char groupspec[256];

static u64 rng_s[2];
static u64 rnd(void) { u64 s1 = rng_s[0]; const u64 s0 = rng_s[1]; rng_s[0] = s0; s1 ^= s1 << 23; rng_s[1] = s1 ^ s0 ^ (s1 >> 17) ^ (s0 >> 26); return rng_s[1] + s0; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static inline u64 perm(u64 x, int h) {
    if (cyclic) { if (!h) return x; return ((x << h) | (x >> (m - h))) & FULL; }
    u64 r = 0; for (int b = 0; b < nbytes; b++) r |= ptab[((size_t)h * 8 + b) * 256 + ((x >> (8 * b)) & 255)];
    return r;
}

static void setup_group(const char *spec) {
    strncpy(groupspec, spec, 255);
    char kind[32]; int a[8]; int na = 0;
    if (sscanf(spec, "%31s", kind) != 1) { fprintf(stderr, "bad GROUP\n"); exit(2); }
    if (!strcmp(kind, "tab")) {
        char fn[200]; sscanf(spec, "%*s %199s", fn); FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(2); }
        if (fscanf(f, "%d", &m) != 1) exit(2);
        mul = malloc(sizeof(int) * m * m);
        for (int i = 0; i < m * m; i++) if (fscanf(f, "%d", &mul[i]) != 1) exit(2);
        fclose(f); cyclic = 0;
    } else {
        const char *p = spec + strlen(kind);
        int off; while (na < 8 && sscanf(p, "%d%n", &a[na], &off) == 1) { p += off; na++; }
        if (!strcmp(kind, "cyc")) {
            m = a[0]; mul = malloc(sizeof(int) * m * m);
            for (int g = 0; g < m; g++) for (int h = 0; h < m; h++) mul[g * m + h] = (g + h) % m;
            cyclic = 1;
        } else if (!strcmp(kind, "ab")) {
            m = 1; for (int i = 0; i < na; i++) m *= a[i];
            mul = malloc(sizeof(int) * m * m);
            for (int g = 0; g < m; g++) for (int h = 0; h < m; h++) {
                int x = g, y = h, r = 0, base = 1;
                for (int i = na - 1; i >= 0; i--) { int c = (x % a[i] + y % a[i]) % a[i]; r += c * base; base *= a[i]; x /= a[i]; y /= a[i]; }
                mul[g * m + h] = r;
            }
            cyclic = (na == 1);
        } else if (!strcmp(kind, "dih")) {
            int n = a[0]; m = 2 * n; mul = malloc(sizeof(int) * m * m);
            /* element (r^i s^e) encoded i + n*e; (r^i s^e)(r^k s^f) = r^(i + (-1)^e k) s^(e+f) */
            for (int g = 0; g < m; g++) for (int h = 0; h < m; h++) {
                int i = g % n, e = g / n, k = h % n, f = h / n;
                int ii = ((i + (e ? -k : k)) % n + n) % n; mul[g * m + h] = ii + n * ((e + f) & 1);
            }
            cyclic = 0;
        } else { fprintf(stderr, "unknown group kind %s\n", kind); exit(2); }
    }
    if (m > 64 || m < 1) { fprintf(stderr, "m must be 1..64\n"); exit(2); }
    ginv = malloc(sizeof(int) * m);
    for (int g = 0; g < m; g++) { ginv[g] = -1; for (int h = 0; h < m; h++) if (mul[g * m + h] == 0) ginv[g] = h; if (ginv[g] < 0) { fprintf(stderr, "not a group\n"); exit(2); } }
    FULL = (m == 64) ? ~0ULL : ((1ULL << m) - 1);
    nbytes = (m + 7) / 8;
    ptab = calloc((size_t)m * 8 * 256, sizeof(u64));
    for (int h = 0; h < m; h++) for (int b = 0; b < nbytes; b++) for (int x = 0; x < 256; x++) {
        u64 r = 0; for (int i = 0; i < 8; i++) if (x >> i & 1) { int g = 8 * b + i; if (g < m) r |= 1ULL << mul[g * m + h]; }
        ptab[((size_t)h * 8 + b) * 256 + x] = r;
    }
}

/* rebuild slots of a point p and of the lines touching it */
static void set_point_slots(int p) {
    for (int s = 0; s <= q; s++) { int l = ptl[p * (q + 1) + s], k = ptk[p * (q + 1) + s];
        nbr[(size_t)p * deg + s] = P + l; vin[(size_t)p * deg + s] = ginv[fv[l * (q + 1) + k]]; }
    for (int t = 0; t < J; t++) { int l = sig[t * P + p];
        nbr[(size_t)p * deg + q + 1 + t] = P + l; vin[(size_t)p * deg + q + 1 + t] = ginv[hv[t * P + p]]; }
}
static void set_line_slots(int l) {
    int w = P + l;
    for (int k = 0; k <= q; k++) { nbr[(size_t)w * deg + k] = lines[l * (q + 1) + k]; vin[(size_t)w * deg + k] = fv[l * (q + 1) + k]; }
    for (int t = 0; t < J; t++) { int p = sinv[t * P + l];
        nbr[(size_t)w * deg + q + 1 + t] = p; vin[(size_t)w * deg + q + 1 + t] = hv[t * P + p]; }
}

/* misses from source u; R0/R1 scratch arrays of NV words */
static long long misses_from(int u, u64 *A, u64 *Bv) {
    memset(A, 0, sizeof(u64) * NV);
    A[u] = 1ULL; /* identity = element 0 */
    int side = u < P ? 0 : 1;  /* active side of A */
    long long miss = 0;
    u64 *cur = A, *nxt = Bv;
    for (int k = 1; k <= D; k++) {
        int ns = side ^ (k & 1);   /* side of level k */
        int lo = ns ? P : 0, hi = ns ? NV : P;
        for (int w = lo; w < hi; w++) {
            const int *nb = nbr + (size_t)w * deg; const int *vi = vin + (size_t)w * deg;
            u64 r = 0;
            for (int s = 0; s < deg; s++) { u64 x = cur[nb[s]]; if (x) r |= perm(x, vi[s]); }
            nxt[w] = r;
        }
        u64 *t = cur; cur = nxt; nxt = t;
        if (k >= D - 1) { /* count misses on side ns at its last level */
            for (int w = lo; w < hi; w++) miss += m - __builtin_popcountll(cur[w] & FULL);
        }
    }
    return miss;
}


/* list up to maxk missed targets (w, g) from source u (same propagation as misses_from) */
static int list_misses(int u, u64 *A, u64 *Bv, int *ow, int *og, int maxk, u64 *rs) {
    memset(A, 0, sizeof(u64) * NV); A[u] = 1ULL;
    int side = u < P ? 0 : 1; u64 *cur = A, *nxt = Bv; int k = 0; long long seen = 0;
    for (int lev = 1; lev <= D; lev++) {
        int ns = side ^ (lev & 1); int lo = ns ? P : 0, hi = ns ? NV : P;
        for (int w = lo; w < hi; w++) { const int *nb = nbr + (size_t)w * deg; const int *vi = vin + (size_t)w * deg; u64 r = 0;
            for (int s = 0; s < deg; s++) { u64 x = cur[nb[s]]; if (x) r |= perm(x, vi[s]); } nxt[w] = r; }
        u64 *t = cur; cur = nxt; nxt = t;
        if (lev >= D - 1) for (int w = lo; w < hi; w++) { u64 miss = FULL & ~cur[w];
            while (miss) { int g = __builtin_ctzll(miss); miss &= miss - 1; seen++;
                if (k < maxk) { ow[k] = w; og[k] = g; k++; }
                else { /* reservoir */ *rs = *rs * 6364136223846793005ULL + 1442695040888963407ULL; long long r = (long long)((*rs >> 17) % (u64)seen); if (r < maxk) { ow[r] = w; og[r] = g; } } } }
    }
    return k;
}
/* GH-only BFS distances (no hops), depth <= 5 */
static int *ghd;
static void gh_bfs(int s, int *dist, int *queue) {
    for (int i = 0; i < NV; i++) dist[i] = -1;
    int h = 0, t = 0; dist[s] = 0; queue[t++] = s;
    while (h < t) { int x = queue[h++]; if (dist[x] >= 5) continue;
        if (x < P) { for (int k = 0; k <= q; k++) { int y = P + ptl[x * (q + 1) + k]; if (dist[y] < 0) { dist[y] = dist[x] + 1; queue[t++] = y; } } }
        else { int l = x - P; for (int k = 0; k <= q; k++) { int y = lines[l * (q + 1) + k]; if (dist[y] < 0) { dist[y] = dist[x] + 1; queue[t++] = y; } } } }
}
/* voltage of the GH geodesic from s to x (dist <= 5, unique): product along the path from s */
static int path_volt(int s, int x, const int *dist) {
    /* walk back from x to s along decreasing dist; accumulate voltages in reverse then combine */
    int seq[8], ns = 0; int cur = x;
    while (cur != s) {
        int found = -1, vstep = 0;
        if (cur < P) { for (int k = 0; k <= q; k++) { int l = ptl[cur * (q + 1) + k], y = P + l; if (dist[y] == dist[cur] - 1) { found = y; vstep = fv[l * (q + 1) + ptk[cur * (q + 1) + k]]; break; } } /* dart y(line) -> cur(point) has voltage fv^-1 */ vstep = ginv[vstep]; }
        else { int l = cur - P; for (int k = 0; k <= q; k++) { int y = lines[l * (q + 1) + k]; if (dist[y] == dist[cur] - 1) { found = y; vstep = fv[l * (q + 1) + k]; break; } } }
        seq[ns++] = vstep; cur = found;
    }
    int g = 0; for (int i = ns - 1; i >= 0; i--) g = mul[g * m + seq[i]];
    return g;
}

static int *srcs; static int nsrc; static int nth = 1;
static u64 **bufA, **bufB;
static long long eval_sources_lim(long long lim) {
    long long tot = 0; volatile int stop = 0;
    #pragma omp parallel for reduction(+:tot) schedule(dynamic, 1) num_threads(nth)
    for (int i = 0; i < nsrc; i++) {
        if (stop) continue;
        int tid = 0;
#ifdef _OPENMP
        tid = omp_get_thread_num();
#endif
        long long c = misses_from(srcs[i], bufA[tid], bufB[tid]);
        tot += c;
        if (lim >= 0 && tot > lim) stop = 1;   /* per-thread partial sum exceeds the limit: reject */
    }
    if (stop) return -1;
    return tot;
}
static long long eval_sources(void) { return eval_sources_lim(-1); }
static long long eval_all(long long *worst_src_out) {
    long long tot = 0, worst = -1; int ws = -1;
    #pragma omp parallel for reduction(+:tot) schedule(dynamic, 16) num_threads(nth)
    for (int u = 0; u < NV; u++) {
        int tid = 0;
#ifdef _OPENMP
        tid = omp_get_thread_num();
#endif
        long long c = misses_from(u, bufA[tid], bufB[tid]);
        tot += c;
        if (c > worst) {
            #pragma omp critical
            { if (c > worst) { worst = c; ws = u; } }
        }
    }
    if (worst_src_out) *worst_src_out = ws;
    return tot;
}

static void write_state(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) { perror(fn); return; }
    fprintf(f, "glift %d %d %d %d\n%s\n", q, J, m, D, groupspec);
    for (int p = 0; p < P; p++) { for (int t = 0; t < J; t++) fprintf(f, "%s%d %d", t ? " " : "", sig[t * P + p], hv[t * P + p]); fprintf(f, "\n"); }
    for (int l = 0; l < P; l++) { for (int k = 0; k <= q; k++) fprintf(f, "%s%d", k ? " " : "", fv[l * (q + 1) + k]); fprintf(f, "\n"); }
    fclose(f);
}
static int read_state(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); return 0; }
    int qq, jj, mm, dd; char buf[512];
    if (fscanf(f, "glift %d %d %d %d\n", &qq, &jj, &mm, &dd) != 4 || qq != q || jj != J || mm != m) { fprintf(stderr, "INIT mismatch\n"); exit(2); }
    if (!fgets(buf, sizeof buf, f)) exit(2);
    for (int p = 0; p < P; p++) for (int t = 0; t < J; t++) if (fscanf(f, "%d %d", &sig[t * P + p], &hv[t * P + p]) != 2) exit(2);
    for (int i = 0; i < P * (q + 1); i++) if (fscanf(f, "%d", &fv[i]) != 1) exit(2);
    fclose(f);
    for (int t = 0; t < J; t++) for (int p = 0; p < P; p++) sinv[t * P + sig[t * P + p]] = p;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: glift GHFILE j D seconds seed OUT\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 2; }
    if (fscanf(f, "%d %d", &P, &q) != 2) return 2;
    lines = malloc(sizeof(int) * (size_t)P * (q + 1));
    for (size_t i = 0; i < (size_t)P * (q + 1); i++) if (fscanf(f, "%d", &lines[i]) != 1) return 2;
    fclose(f);
    J = atoi(argv[2]); D = atoi(argv[3]); double secs = atof(argv[4]); u64 seed = strtoull(argv[5], 0, 10); const char *out = argv[6];
    rng_s[0] = seed * 0x9E3779B97F4A7C15ULL + 1; rng_s[1] = seed ^ 0xD1B54A32D192ED03ULL; for (int i = 0; i < 20; i++) rnd();
    char gdef[64]; snprintf(gdef, sizeof gdef, "cyc %d", 2 * J + 2);
    setup_group(getenv("GROUP") ? getenv("GROUP") : gdef);
    const char *ghv = getenv("GHV") ? getenv("GHV") : "0";
    const char *hvm = getenv("HV") ? getenv("HV") : "dgq";
    const char *sgm = getenv("SIGMA") ? getenv("SIGMA") : "free";
    int sample = getenv("SAMPLE") ? atoi(getenv("SAMPLE")) : 0;
    int resample = getenv("RESAMPLE") ? atoi(getenv("RESAMPLE")) : 2000;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 2.0, TEND = getenv("TEND") ? atof(getenv("TEND")) : 0.05;
    nth = getenv("THREADS") ? atoi(getenv("THREADS")) : 1;
    int ht[16]; for (int t = 0; t < 16; t++) ht[t] = (t + 1) % m;
    if (getenv("HT")) { const char *p = getenv("HT"); int off, t = 0; while (t < 16 && sscanf(p, "%d%n", &ht[t], &off) == 1) { p += off; t++; } }
    NV = 2 * P; deg = q + 1 + J;
    ptl = malloc(sizeof(int) * P * (q + 1)); ptk = malloc(sizeof(int) * P * (q + 1));
    { int *c = calloc(P, sizeof(int));
      for (int l = 0; l < P; l++) for (int k = 0; k <= q; k++) { int p = lines[l * (q + 1) + k]; ptl[p * (q + 1) + c[p]] = l; ptk[p * (q + 1) + c[p]] = k; c[p]++; }
      free(c); }
    nbr = malloc(sizeof(int) * (size_t)NV * deg); vin = malloc(sizeof(int) * (size_t)NV * deg);
    sig = malloc(sizeof(int) * (size_t)(J ? J : 1) * P); sinv = malloc(sizeof(int) * (size_t)(J ? J : 1) * P); hv = malloc(sizeof(int) * (size_t)(J ? J : 1) * P);
    fv = calloc((size_t)P * (q + 1), sizeof(int));
    int ghv_free = !strcmp(ghv, "free"), ghv_z2 = !strcmp(ghv, "z2"), hv_free = !strcmp(hvm, "free"), sig_free = !strcmp(sgm, "free");
    /* random start */
    for (int t = 0; t < J; t++) {
        for (int p = 0; p < P; p++) sig[t * P + p] = p;
        for (int p = P - 1; p > 0; p--) { int r = rndi(p + 1); int x = sig[t * P + p]; sig[t * P + p] = sig[t * P + r]; sig[t * P + r] = x; }
        for (int p = 0; p < P; p++) { sinv[t * P + sig[t * P + p]] = p; hv[t * P + p] = hv_free ? rndi(m) : ht[t]; }
    }
    if (ghv_free) for (int i = 0; i < P * (q + 1); i++) fv[i] = rndi(m);
    if (ghv_z2) for (int i = 0; i < P * (q + 1); i++) fv[i] = rndi(2) * (m / 2);
    if (getenv("INIT")) read_state(getenv("INIT"));
    for (int p = 0; p < P; p++) set_point_slots(p);
    for (int l = 0; l < P; l++) set_line_slots(l);
    bufA = malloc(sizeof(u64 *) * nth); bufB = malloc(sizeof(u64 *) * nth);
    for (int i = 0; i < nth; i++) { bufA[i] = malloc(sizeof(u64) * NV); bufB[i] = malloc(sizeof(u64) * NV); }
    double ptarget = getenv("TARGET") ? atof(getenv("TARGET")) : 0.0;
    int *tw = malloc(sizeof(int) * 64), *tg = malloc(sizeof(int) * 64); u64 rs_state = seed * 7 + 3;
    int *ds = malloc(sizeof(int) * NV), *dw = malloc(sizeof(int) * NV), *qu = malloc(sizeof(int) * NV), *du = malloc(sizeof(int) * NV), *qu2 = malloc(sizeof(int) * NV);
    if (getenv("EVAL") && atoi(getenv("EVAL"))) {
        long long ws = -1; double t0 = omp_get_wtime(); long long c;
        if (sample > 0 && sample < NV) { nsrc = sample; srcs = malloc(sizeof(int) * NV); for (int i = 0; i < NV; i++) srcs[i] = i;
            for (int i = 0; i < nsrc; i++) { int r = i + rndi(NV - i); int x = srcs[i]; srcs[i] = srcs[r]; srcs[r] = x; }
            c = eval_sources(); printf("(sampled %d of %d sources; scaled total %.4g)\n", nsrc, NV, (double)c * NV / nsrc); }
        else c = eval_all(&ws);
        printf("EVAL q=%d j=%d m=%d D=%d group=[%s] lift vertices %lld: total misses %lld (worst source %lld) %.1fs\n", q, J, m, D, groupspec, (long long)NV * m, c, ws, omp_get_wtime() - t0);
        if (getenv("EDGES")) {
            FILE *g = fopen(getenv("EDGES"), "w");
            fprintf(g, "%lld\n", (long long)NV * m);
            for (int l = 0; l < P; l++) for (int k = 0; k <= q; k++) { int p = lines[l * (q + 1) + k]; int h = fv[l * (q + 1) + k];
                for (int g0 = 0; g0 < m; g0++) fprintf(g, "%lld %lld\n", (long long)p * m + g0, (long long)(P + l) * m + mul[g0 * m + h]); }
            for (int t = 0; t < J; t++) for (int p = 0; p < P; p++) { int l = sig[t * P + p], h = hv[t * P + p];
                for (int g0 = 0; g0 < m; g0++) fprintf(g, "%lld %lld\n", (long long)p * m + g0, (long long)(P + l) * m + mul[g0 * m + h]); }
            fclose(g);
        }
        return 0;
    }
    if (!sig_free && !hv_free && !ghv_free && !ghv_z2) { fprintf(stderr, "nothing to anneal\n"); return 2; }
    nsrc = sample > 0 && sample < NV ? sample : NV;
    srcs = malloc(sizeof(int) * NV);
    for (int i = 0; i < NV; i++) srcs[i] = i;
    #define RESHUF() do { if (nsrc < NV) for (int i = 0; i < nsrc; i++) { int r = i + rndi(NV - i); int x = srcs[i]; srcs[i] = srcs[r]; srcs[r] = x; } } while (0)
    RESHUF();
    long long cur = eval_sources(), best = cur;
    double t0 = omp_get_wtime(), lastp = t0; long long steps = 0, acc = 0;
    fprintf(stderr, "start q=%d j=%d m=%d D=%d group=[%s] GHV=%s HV=%s SIGMA=%s sample=%d: cost %lld\n", q, J, m, D, groupspec, ghv, hvm, sgm, nsrc, cur);
    write_state(out);
    while (1) {
        double el = omp_get_wtime() - t0; if (el > secs) break;
        double T = T0 * pow(TEND / T0, el / secs);
        if (nsrc < NV && steps % resample == 0 && steps) { RESHUF(); cur = eval_sources(); }
        /* choose move */
        int kinds[3], nk = 0; if (sig_free && J) kinds[nk++] = 0; if (hv_free && J) kinds[nk++] = 1; if (ghv_free || ghv_z2) kinds[nk++] = 2;
        int kind = kinds[rndi(nk)];
        int t = J ? rndi(J) : 0, p1 = 0, p2 = 0, old = 0, idxf = 0;
        int targeted_ok = 0;
        if (kind == 0 && J >= 1 && ptarget > 0 && rndu() < ptarget) {
            /* targeted move: pick a missed (s, w, g) and create a two-hop route
               s ~(l1)~> u -hop a-> u' ~(l2)~> v -hop b-> v' ~(l3)~> w  by one swap in matching b at v */
            int s = srcs[rndi(nsrc)];
            int k = list_misses(s, bufA[0], bufB[0], tw, tg, 64, &rs_state);
            if (k > 0) {
                int i = rndi(k), w = tw[i], g = tg[i];
                gh_bfs(s, ds, qu); gh_bfs(w, dw, qu);
                int L = ((s < P) == (w < P)) ? D - 1 : D;
                for (int tries = 0; tries < 80 && !targeted_ok; tries++) {
                    int l1 = rndi(L - 1), l2 = rndi(L - 1 - l1), l3 = rndi(L - 1 - l1 - l2);
                    if (l1 > 5 || l3 > 5 || l2 > 5) continue;
                    int u = -1, vp = -1;
                    if (l1 == 0) u = s; else for (int z = 0; z < 400 && u < 0; z++) { int x = rndi(NV); if (ds[x] == l1) u = x; }
                    if (l3 == 0) vp = w; else for (int z = 0; z < 400 && vp < 0; z++) { int x = rndi(NV); if (dw[x] == l3) vp = x; }
                    if (u < 0 || vp < 0) continue;
                    int a = rndi(J), b = rndi(J);
                    /* first hop at u */
                    int up, x1;
                    if (u < P) { up = P + sig[a * P + u]; x1 = hv[a * P + u]; }
                    else { int pt = sinv[a * P + (u - P)]; up = pt; x1 = ginv[hv[a * P + pt]]; }
                    /* v at GH distance l2 from up, with type such that hop b at v lands on vp's type */
                    int v = -1;
                    if (l2 == 0) v = up;
                    else { gh_bfs(up, du, qu2); for (int z = 0; z < 400 && v < 0; z++) { int x = rndi(NV); if (du[x] == l2) v = x; } }
                    if (v < 0) continue;
                    if ((v < P) == (vp < P)) continue;          /* hop b must change side */
                    if (l2 == 0 && a == b) continue;            /* immediate backtrack on the same matching */
                    int Vsu = path_volt(s, u, ds), Vvw = ginv[path_volt(w, vp, dw)];
                    int Vuv = 0; if (l2 > 0) Vuv = path_volt(up, v, du);
                    if (v < P) { /* hop P->L at v via sigma_b: set sigma_b(v) = vp */
                        int x2 = hv[b * P + v];
                        int prod = mul[mul[mul[mul[Vsu * m + x1] * m + Vuv] * m + x2] * m + Vvw];
                        if (prod != g) continue;
                        if (b == a && u < P && v == u) continue;
                        int z = sinv[b * P + (vp - P)]; if (z == v) continue;
                        if (b == a && (z == u || v == u || (u >= P && (z == up || v == up)))) continue;
                        t = b; p1 = v; p2 = z; targeted_ok = 1;
                    } else { /* hop L->P at line v via sigma_b^-1: set sigma_b(vp) = v */
                        int x2 = ginv[hv[b * P + vp]];
                        int prod = mul[mul[mul[mul[Vsu * m + x1] * m + Vuv] * m + x2] * m + Vvw];
                        if (prod != g) continue;
                        int z = sinv[b * P + (v - P)]; if (z == vp) continue;
                        if (b == a && (u < P ? (vp == u || z == u) : (vp == up || z == up))) continue;
                        t = b; p1 = vp; p2 = z; targeted_ok = 1;
                    }
                }
            }
        }
        if (kind == 0) {
            if (!targeted_ok) { p1 = rndi(P); p2 = rndi(P); if (p1 == p2) continue; }
            int l1 = sig[t * P + p1], l2 = sig[t * P + p2];
            sig[t * P + p1] = l2; sig[t * P + p2] = l1; sinv[t * P + l2] = p1; sinv[t * P + l1] = p2;
            set_point_slots(p1); set_point_slots(p2); set_line_slots(l1); set_line_slots(l2);
        } else if (kind == 1) {
            p1 = rndi(P); old = hv[t * P + p1]; int nv = rndi(m - 1); if (nv >= old) nv++;
            hv[t * P + p1] = nv; set_point_slots(p1); set_line_slots(sig[t * P + p1]);
        } else {
            idxf = rndi(P * (q + 1)); old = fv[idxf];
            if (ghv_z2) fv[idxf] = old ? 0 : m / 2; else { int nv = rndi(m - 1); if (nv >= old) nv++; fv[idxf] = nv; }
            int l = idxf / (q + 1), k = idxf % (q + 1); set_line_slots(l); set_point_slots(lines[l * (q + 1) + k]);
        }
        double uu = rndu(); long long lim = cur + (long long)floor(-T * log(uu > 1e-300 ? uu : 1e-300));
        long long c = eval_sources_lim(lim); steps++;
        int ok = c >= 0 && c <= lim;
        if (ok) { cur = c; acc++;
            if (c < best) { best = c; write_state(out);
                if (c == 0) {
                    long long ws, full = eval_all(&ws);
                    fprintf(stderr, "sampled cost 0 at step %lld (%.1fs); full cost %lld\n", steps, omp_get_wtime() - t0, full);
                    if (full == 0) { printf("RESULT SOLVED q=%d j=%d m=%d D=%d group=[%s] lift %lld vertices, steps %lld, %.1fs, file %s\n", q, J, m, D, groupspec, (long long)NV * m, steps, omp_get_wtime() - t0, out); return 0; }
                    best = full; cur = full; if (nsrc == NV) best = full;
                }
            }
        } else { /* undo */
            if (kind == 0) { int l1 = sig[t * P + p1], l2 = sig[t * P + p2];
                sig[t * P + p1] = l2; sig[t * P + p2] = l1; sinv[t * P + l2] = p1; sinv[t * P + l1] = p2;
                set_point_slots(p1); set_point_slots(p2); set_line_slots(l1); set_line_slots(l2);
            } else if (kind == 1) { hv[t * P + p1] = old; set_point_slots(p1); set_line_slots(sig[t * P + p1]); }
            else { fv[idxf] = old; int l = idxf / (q + 1), k = idxf % (q + 1); set_line_slots(l); set_point_slots(lines[l * (q + 1) + k]); }
        }
        if (omp_get_wtime() - lastp > 10) { lastp = omp_get_wtime(); fprintf(stderr, "  t=%.0fs steps %lld acc %lld T %.3f cur %lld best %lld\n", lastp - t0, steps, acc, T, cur, best); }
    }
    long long ws; long long full = eval_all(&ws);
    printf("RESULT best_sampled %lld final_full %lld q=%d j=%d m=%d D=%d group=[%s] GHV=%s HV=%s steps %lld file %s\n", best, full, q, J, m, D, groupspec, ghv, hvm, steps, out);
    return 0;
}
