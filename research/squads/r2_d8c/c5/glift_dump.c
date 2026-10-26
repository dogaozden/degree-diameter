/* glift.c: exact diameter-8 test for lifts of a base graph by Z_m (m <= 64) or the dihedral group D_n (2n <= 64).
   (own-d8-compound job, 2026-10-26.)

   Input (text):
     line 1: "Z m" or "D n"
     line 2: V            (number of base vertices)
     line 3: V colours    (0 = point side, 1 = line side of the base)
     then lines "u v a":  a dart u -> v with voltage a; the lift has (u, g) ~ (v, g*a) and (v, h) ~ (u, h*a^-1).
                          u == v is allowed for a semi-edge whose voltage is an involution (one edge per lift vertex).
   Group elements: Z_m: a in 0..m-1.  D_n: a = k + n*t means (k, t), product (k,t)(k',t') = (k + (-1)^t k', t + t').
   Lift colour: col(v, g) = colour(v) + par(g), par = t for D_n, par = g mod 2 for Z_m when MIX=1 (else 0).
   The group acts on the lift by left multiplication, so sources (v, 1) for all base v cover every pair.
   Test: from (s, 1), walks of length exactly 7 (padding by backtracks) reach every vertex of the other colour at
   distance <= 7; diameter <= 8 iff nothing is uncovered from every source (same-colour pairs follow).
   Usage: glift FILE [all | r:K:seed | i:v1,v2,...] [verbose]
   Output: "COST total_uncovered sources n bad b worst_src s worst c lift_vertices N". Exit 0 iff COST 0. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t u64;
static int V, m, n, dih, mix;
static int *col, *off, *adj, *vol;   /* darts out of each vertex, with voltage to apply */
static u64 FULL, LOW;

static inline u64 rotk(u64 x, int a, int len, u64 mask) {
    a %= len; if (a < 0) a += len; if (!a) return x;
    return ((x << a) | (x >> (len - a))) & mask;
}
/* right multiplication of a set of group elements by element a */
static inline u64 rmul(u64 x, int a) {
    if (!dih) return rotk(x, a, m, FULL);
    int k = a % n, t = a / n;
    u64 lo = x & LOW, hi = x >> n;
    if (!t) return rotk(lo, k, n, LOW) | (rotk(hi, -k, n, LOW) << n);
    return rotk(hi, -k, n, LOW) | (rotk(lo, k, n, LOW) << n);
}
static int ginv(int a) {
    if (!dih) return (m - a) % m;
    int k = a % n, t = a / n;
    if (t) return a;
    return (n - k) % n;
}
static u64 rnd_state = 0x9E3779B97F4A7C15ULL;
static u64 rnd(void) { rnd_state ^= rnd_state << 13; rnd_state ^= rnd_state >> 7; rnd_state ^= rnd_state << 17; return rnd_state; }

static long long run_source(int s, u64 *cur, u64 *nxt, int verbose) {
    memset(cur, 0, sizeof(u64) * V);
    cur[s] = 1;
    for (int step = 0; step < 7; step++) {
        memset(nxt, 0, sizeof(u64) * V);
        for (int v = 0; v < V; v++) { u64 x = cur[v]; if (!x) continue;
            for (int k = off[v]; k < off[v + 1]; k++) nxt[adj[k]] |= rmul(x, vol[k]); }
        u64 *t = cur; cur = nxt; nxt = t;
    }
    /* after 7 steps the result is in cur (pointer swapped an odd number of times: copy back semantics handled by caller) */
    long long unc = 0;
    u64 par0, par1;   /* masks of group elements with parity 0 / 1 */
    if (dih) { par0 = LOW; par1 = LOW << n; }
    else if (mix) { par0 = 0; for (int g = 0; g < m; g += 2) par0 |= 1ULL << g; par1 = FULL & ~par0; }
    else { par0 = FULL; par1 = 0; }
    int shown = 0;
    for (int v = 0; v < V; v++) {
        u64 need = (col[v] != col[s]) ? par0 : par1;   /* col(v,g) = col(v)+par(g) must differ from col(s) */
        u64 miss = need & ~cur[v];
        if (miss) { unc += __builtin_popcountll(miss);
            if (verbose >= 2) { fprintf(stderr, "  src %d: v%d (col %d) miss %016llx\n", s, v, col[v], (unsigned long long)miss); shown++; } }
    }
    return unc;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: glift FILE [srcspec] [verbose]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror("open"); return 2; }
    const char *spec = argc > 2 ? argv[2] : "all";
    int verbose = argc > 3 ? atoi(argv[3]) : 0;
    mix = getenv("MIX") ? atoi(getenv("MIX")) : 0;
    char gt[8]; int gp;
    if (fscanf(f, "%7s %d", gt, &gp) != 2) { fprintf(stderr, "bad header\n"); return 2; }
    dih = (gt[0] == 'D');
    if (dih) { n = gp; m = 2 * n; } else { m = gp; n = m; }
    if (m < 1 || m > 64) { fprintf(stderr, "group too large\n"); return 2; }
    FULL = (m == 64) ? ~0ULL : ((1ULL << m) - 1);
    LOW = (n == 64) ? ~0ULL : ((1ULL << n) - 1);
    if (fscanf(f, "%d", &V) != 1) return 2;
    col = malloc(sizeof(int) * V);
    for (int i = 0; i < V; i++) if (fscanf(f, "%d", &col[i]) != 1) return 2;
    int cap = 1 << 20, nd = 0; int *du = malloc(sizeof(int) * cap), *dv = malloc(sizeof(int) * cap), *da = malloc(sizeof(int) * cap);
    int u, v, a; long semi = 0;
    while (fscanf(f, "%d %d %d", &u, &v, &a) == 3) {
        if (u < 0 || u >= V || v < 0 || v >= V || a < 0 || a >= m) { fprintf(stderr, "bad dart %d %d %d\n", u, v, a); return 2; }
        if (nd + 2 >= cap) { cap *= 2; du = realloc(du, sizeof(int) * cap); dv = realloc(dv, sizeof(int) * cap); da = realloc(da, sizeof(int) * cap); }
        if (u == v) {
            if (ginv(a) != a) { fprintf(stderr, "semi-edge at %d with non-involution %d\n", u, a); return 2; }
            du[nd] = u; dv[nd] = u; da[nd] = a; nd++; semi++;
        } else {
            du[nd] = u; dv[nd] = v; da[nd] = a; nd++;
            du[nd] = v; dv[nd] = u; da[nd] = ginv(a); nd++;
        }
    }
    fclose(f);
    off = calloc(V + 1, sizeof(int));
    for (int e = 0; e < nd; e++) off[du[e] + 1]++;
    int maxd = 0, mind = 1 << 30;
    for (int i = 0; i < V; i++) { if (off[i + 1] > maxd) maxd = off[i + 1]; if (off[i + 1] < mind) mind = off[i + 1]; off[i + 1] += off[i]; }
    adj = malloc(sizeof(int) * nd); vol = malloc(sizeof(int) * nd);
    int *pp = malloc(sizeof(int) * V); memcpy(pp, off, sizeof(int) * V);
    for (int e = 0; e < nd; e++) { adj[pp[du[e]]] = dv[e]; vol[pp[du[e]]++] = da[e]; }
    /* bipartite sanity: every dart must change the lift colour */
    for (int e = 0; e < nd; e++) {
        int pa = dih ? (da[e] / n) : (mix ? da[e] % 2 : 0);
        if (((col[du[e]] + col[dv[e]] + pa) & 1) == 0) { fprintf(stderr, "dart %d->%d voltage %d keeps the colour: lift not bipartite\n", du[e], dv[e], da[e]); return 2; }
    }
    fprintf(stderr, "base V %d darts %d (semi %ld) degree %d..%d; group %s of order %d; lift %lld vertices\n",
            V, nd, semi, mind, maxd, dih ? "D" : "Z", m, (long long)V * m);
    int nsrc = 0; int *src = malloc(sizeof(int) * (V + 8));
    if (!strcmp(spec, "all")) { for (int i = 0; i < V; i++) src[nsrc++] = i; }
    else if (spec[0] == 'r') { int K = 0; unsigned long long seed = 2; sscanf(spec, "r:%d:%llu", &K, &seed);
        rnd_state = 0x9E3779B97F4A7C15ULL ^ ((seed + 7) * 0xD1B54A32D192ED03ULL); if (!rnd_state) rnd_state = 1; for (int i = 0; i < 20; i++) rnd();
        for (int i = 0; i < K; i++) src[nsrc++] = (int)(rnd() % (u64)V); }
    else if (spec[0] == 'i') { const char *p = spec + 2; while (*p) { src[nsrc++] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; } }
    long long total = 0; int worst = -1; long long worstc = -1; int bad = 0;
    #pragma omp parallel
    {
        u64 *b1 = malloc(sizeof(u64) * V), *b2 = malloc(sizeof(u64) * V);
        #pragma omp for schedule(dynamic, 16) reduction(+:total, bad)
        for (int s = 0; s < nsrc; s++) {
            long long unc = run_source(src[s], b1, b2, verbose);
            if (unc) bad++;
            total += unc;
            #pragma omp critical
            { if (unc > worstc) { worstc = unc; worst = src[s]; } }
        }
        free(b1); free(b2);
    }
    printf("COST %lld sources %d bad %d worst_src %d worst %lld degree %d lift_vertices %lld\n", total, nsrc, bad, worst,
           worstc, maxd, (long long)V * m);
    return total ? 1 : 0;
}
