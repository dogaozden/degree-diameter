/* hgs.c (w4, handsoff-49): generic symmetric lift search for small bases (<= 64 vertices, <= 256 edges).
   Base file: "b m" then m lines "u v" (simple, 4-regular). Optional automorphism s (permutation line AUTIDX of AUTS,
   fixed-point-free of order m_s): voltages are constant on <s>-edge-orbits, so the lift has the automorphism
   (v,x) -> (s v, x) and only orbit-representative roots are needed (cost = m_s * reps cost = full cost).
   Gauge: edge orbits of a BFS spanning tree of the quotient are fixed to 0.
   Lift over G (cyc:k or file.bin, T[x*k+g] = x*g): lift edges (a,x) ~ (b, x*g) for base edge a->b voltage g.
   Modes: SA (default): simulated annealing for `seconds`. EXH=1: exhaustive over free orbit values, the first free
   value restricted to divisors of k (valid for cyclic G: unit automorphisms of Z_k), cost printed for the best.
   Usage: hgs BASE GROUP AUTS|- AUTIDX seconds seed T0 T1 OUTPREFIX
   Writes OUTPREFIX.best ("e g" per base edge) and OUTPREFIX.edges when full cost is 0 or WRITE_EDGES is set. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXB 64
#define MAXE 256
#define MAXK 1024
#define D 9

static int nb, ne, k;
static uint16_t *T;
static int inv_[MAXK];
static int ea[MAXE], eb[MAXE], ev[MAXE];
static int perm[MAXB], have_perm = 0;
static int vorb[MAXB], nvorb, reps[MAXB], nreps;
static int eorb[MAXE], neorb, eo_first[MAXE], eo_size[MAXE], eo_edges[MAXE][16];
static int tree_o[MAXE], freeo[MAXE], nfree, val[MAXE], m_s = 1;
static int ninc[MAXB], incw[MAXB][8], incg[MAXB][8];
static uint64_t SA_[MAXB][MAXK], SB_[MAXB][MAXK];

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static void load_group(const char *spec) {
    if (strncmp(spec, "cyc:", 4) == 0) {
        k = atoi(spec + 4);
        T = malloc(sizeof(uint16_t) * k * k);
        for (int x = 0; x < k; x++) for (int g = 0; g < k; g++) T[x * k + g] = (uint16_t)((x + g) % k);
    } else {
        FILE *f = fopen(spec, "rb");
        if (!f) { perror("group"); exit(1); }
        int32_t N; if (fread(&N, 4, 1, f) != 1) exit(1);
        k = N; T = malloc(sizeof(uint16_t) * k * k);
        if (fread(T, 2, (size_t)k * k, f) != (size_t)k * k) { fprintf(stderr, "short group\n"); exit(1); }
        fclose(f);
    }
    if (k > MAXK) { fprintf(stderr, "k too big\n"); exit(1); }
    for (int g = 0; g < k; g++) for (int h = 0; h < k; h++) if (T[g * k + h] == 0) { inv_[g] = h; break; }
}

static void load_base(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f || fscanf(f, "%d %d", &nb, &ne) != 2) { fprintf(stderr, "bad base\n"); exit(1); }
    for (int e = 0; e < ne; e++) if (fscanf(f, "%d %d", &ea[e], &eb[e]) != 2) exit(1);
    fclose(f);
}

static void load_aut(const char *path, int idx) {
    FILE *f = fopen(path, "r");
    if (!f) { perror("auts"); exit(1); }
    static char line[8192];
    for (int i = 0; i <= idx; i++) if (!fgets(line, sizeof line, f)) { fprintf(stderr, "no aut line\n"); exit(1); }
    fclose(f);
    char *p = line;
    for (int v = 0; v < nb; v++) perm[v] = (int)strtol(p, &p, 10);
    have_perm = 1;
}

static int find_edge(int u, int v) {
    if (u > v) { int t = u; u = v; v = t; }
    for (int j = 0; j < ne; j++) {
        int a = ea[j], b = eb[j];
        if (a > b) { int t = a; a = b; b = t; }
        if (a == u && b == v) return j;
    }
    return -1;
}

static void build_orbits(void) {
    int ident[MAXB];
    for (int v = 0; v < nb; v++) ident[v] = v;
    if (!have_perm) memcpy(perm, ident, sizeof perm);
    int seen[MAXB]; memset(seen, 0, sizeof seen);
    int o = 1;
    for (int s = 0; s < nb; s++) {
        if (seen[s]) continue;
        int L = 0, x = s;
        while (!seen[x]) { seen[x] = 1; x = perm[x]; L++; }
        int a = o, b = L; while (b) { int t = a % b; a = b; b = t; }
        o = o / a * L;
    }
    m_s = o;
    for (int v = 0; v < nb; v++) vorb[v] = -1;
    nvorb = 0; nreps = 0;
    for (int v = 0; v < nb; v++) {
        if (vorb[v] >= 0) continue;
        int x = v;
        for (int i = 0; i < o; i++) { vorb[x] = nvorb; x = perm[x]; }
        reps[nreps++] = v; nvorb++;
    }
    for (int e = 0; e < ne; e++) eorb[e] = -1;
    neorb = 0;
    for (int e = 0; e < ne; e++) {
        if (eorb[e] >= 0) continue;
        int a = ea[e], b = eb[e], cnt = 0;
        for (int i = 0; i < o; i++) {
            int f = find_edge(a, b);
            if (f < 0) { fprintf(stderr, "aut is not a graph automorphism\n"); exit(1); }
            if (eorb[f] < 0) { eorb[f] = neorb; if (cnt < 16) eo_edges[neorb][cnt] = f; cnt++; }
            a = perm[a]; b = perm[b];
        }
        eo_first[neorb] = e; eo_size[neorb] = cnt < 16 ? cnt : 16; neorb++;
    }
    /* gauge tree on the quotient */
    int qseen[MAXB]; memset(qseen, 0, sizeof qseen);
    for (int i = 0; i < neorb; i++) tree_o[i] = 0;
    int q[MAXB], qh = 0, qt = 0; q[qt++] = vorb[0]; qseen[vorb[0]] = 1;
    while (qh < qt) {
        int c = q[qh++];
        for (int eo = 0; eo < neorb; eo++) {
            int e = eo_first[eo];
            int x = vorb[ea[e]], y = vorb[eb[e]];
            int other = -1;
            if (x == c) other = y; else if (y == c) other = x;
            if (other < 0 || qseen[other]) continue;
            qseen[other] = 1; tree_o[eo] = 1; q[qt++] = other;
        }
    }
    nfree = 0;
    for (int eo = 0; eo < neorb; eo++) if (!tree_o[eo]) freeo[nfree++] = eo;
}

static void set_voltages(void) { for (int e = 0; e < ne; e++) ev[e] = val[eorb[e]]; }

static void build_inc(void) {
    memset(ninc, 0, sizeof ninc);
    for (int e = 0; e < ne; e++) {
        int a = ea[e], b = eb[e], g = ev[e];
        incw[b][ninc[b]] = a; incg[b][ninc[b]] = g; ninc[b]++;
        incw[a][ninc[a]] = b; incg[a][ninc[a]] = inv_[g]; ninc[a]++;
    }
}

/* full cost = m_s * (cost over orbit representatives) */
static int eval_reps(void) {
    build_inc();
    memset(SA_, 0, sizeof SA_);
    for (int i = 0; i < nreps; i++) SA_[reps[i]][0] |= 1ULL << i;
    uint64_t (*cur)[MAXK] = SA_, (*nxt)[MAXK] = SB_;
    for (int step = 1; step <= D; step++) {
        for (int v = 0; v < nb; v++) memcpy(nxt[v], cur[v], sizeof(uint64_t) * k);
        for (int v = 0; v < nb; v++)
            for (int i = 0; i < ninc[v]; i++) {
                int w = incw[v][i], g = incg[v][i];
                for (int x = 0; x < k; x++) nxt[v][T[x * k + g]] |= cur[w][x];
            }
        uint64_t (*t)[MAXK] = cur; cur = nxt; nxt = t;
    }
    int cost = 0;
    for (int v = 0; v < nb; v++)
        for (int x = 0; x < k; x++) cost += nreps - __builtin_popcountll(cur[v][x]);
    return cost;
}

static void write_sol(const char *path) {
    FILE *f = fopen(path, "w");
    for (int e = 0; e < ne; e++) fprintf(f, "%d %d\n", e, ev[e]);
    fclose(f);
}

static void write_edges(const char *path) {
    FILE *f = fopen(path, "w");
    fprintf(f, "%d\n", nb * k);
    for (int e = 0; e < ne; e++)
        for (int x = 0; x < k; x++)
            fprintf(f, "%d %d\n", ea[e] * k + x, eb[e] * k + T[x * k + ev[e]]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: hgs BASE GROUP AUTS|- AUTIDX seconds seed T0 T1 OUTPREFIX\n"); return 1; }
    load_base(argv[1]);
    load_group(argv[2]);
    if (strcmp(argv[3], "-") != 0) load_aut(argv[3], atoi(argv[4]));
    build_orbits();
    double secs = atof(argv[5]);
    rs ^= (uint64_t)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double T0 = atof(argv[7]), T1 = atof(argv[8]);
    const char *outp = argv[9];
    if (nreps > 64) { fprintf(stderr, "too many reps\n"); return 1; }
    for (int eo = 0; eo < neorb; eo++) val[eo] = 0;
    for (int i = 0; i < nfree; i++) val[freeo[i]] = (int)(rnd() % k);
    set_voltages();
    int bestval[MAXE];
    int best;
    char path[512];
    fprintf(stderr, "b=%d m=%d k=%d n=%d aut_order=%d vorbits=%d reps=%d eorbits=%d free=%d\n",
            nb, ne, k, nb * k, m_s, nvorb, nreps, neorb, nfree);
    if (getenv("EXH")) {
        /* exhaustive: first free orbit over divisors of k, the rest over all of G */
        best = 1 << 30; long evals = 0;
        int nd = 0, divs[MAXK];
        for (int d = 1; d <= k; d++) if (k % d == 0) divs[nd++] = d;
        int idx[MAXE];
        if (nfree == 0) { int c = eval_reps(); best = c; memcpy(bestval, val, sizeof val); }
        else {
            int total_first = nd;
            for (int fi = 0; fi < total_first; fi++) {
                /* value of first free orbit: gcd class representative divs[fi] % k */
                int v0 = divs[fi] % k;
                memset(idx, 0, sizeof idx);
                for (int i = 0; i < nfree; i++) val[freeo[i]] = 0;
                val[freeo[0]] = v0;
                /* odometer over remaining free orbits */
                for (int i = 1; i < nfree; i++) val[freeo[i]] = 0;
                while (1) {
                    set_voltages();
                    int c = eval_reps(); evals++;
                    if (c < best) {
                        best = c; memcpy(bestval, val, sizeof val);
                        fprintf(stderr, "EXH best full=%d reps=%d (first=%d)\n", best * m_s, best, v0);
                        if (best == 0) break;
                    }
                    int i = nfree - 1;
                    while (i >= 1) {
                        val[freeo[i]]++;
                        if (val[freeo[i]] < k) break;
                        val[freeo[i]] = 0; i--;
                    }
                    if (i < 1) break;
                }
                if (best == 0) break;
            }
        }
        fprintf(stderr, "evals %ld\n", evals);
    } else {
        set_voltages();
        int cur = eval_reps();
        best = cur;
        memcpy(bestval, val, sizeof val);
        clock_t t0 = clock();
        double T = T0; long it = 0, acc = 0;
        while (nfree > 0) {
            if ((it & 15) == 0) {
                double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
                if (el >= secs) break;
                T = T0 * pow(T1 / T0, el / secs);
                if ((it & 65535) == 0) fprintf(stderr, "P it=%ld t=%.0f T=%.3f cur=%d best=%d\n", it, el, T, cur * m_s, best * m_s);
            }
            it++;
            int eo = freeo[rnd() % nfree];
            int old = val[eo];
            int ng = (int)(rnd() % (k - 1)); if (ng >= old) ng++;
            val[eo] = ng; set_voltages();
            int nc = eval_reps();
            int dlt = nc - cur;
            if (dlt <= 0 || urand() < exp(-dlt / T)) {
                cur = nc; acc++;
                if (cur < best) { best = cur; memcpy(bestval, val, sizeof val); if (best == 0) break; }
            } else val[eo] = old;
        }
        fprintf(stderr, "sa iterations %ld acc %ld\n", it, acc);
    }
    memcpy(val, bestval, sizeof val);
    set_voltages();
    int chk = eval_reps();
    snprintf(path, sizeof path, "%s.best", outp); write_sol(path);
    if (chk == 0 || getenv("WRITE_EDGES")) { snprintf(path, sizeof path, "%s.edges", outp); write_edges(path); }
    printf("RESULT full_cost=%d reps_cost=%d aut_order=%d k=%d n=%d check=%d\n", chk * m_s, chk, m_s, k, nb * k, chk);
    return 0;
}
