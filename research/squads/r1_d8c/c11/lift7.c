/* lift7.c: card c11 (squad r1_d8c). Lift of the D7 level graph G7 (q = 5) by G = Z_5 x Z_K, Z_K voltages on the
   hexagon flags only, matchings with voltages (1,0) and (2,0). Exact cost = number of ordered pairs (s,t) at distance
   > 8 in the lift (bit-parallel BFS, 64 sources per batch, all 2V base sources = all orbits). Anneal the hexagon
   voltages with a sampled version of that cost, then run the exact full check and a breakdown of uncovered targets
   by (level difference = Z_5 coordinate of target, hexagon distance of the base vertices).
   Build: gcc -O2 -o lift7 lift7.c -lm
   Usage: lift7 BASE K MODE STEPS SEED B TLIM T0 T1 OUTPREFIX
     BASE: prep.py output; K: hexagon voltage group Z_K (K >= 2, gcd(K,5)=1 not required; G = Z_5 x Z_K).
     MODE: zero | rand (initial hexagon voltages). STEPS: annealing steps (0 = evaluate initial only).
     B: number of 64-source batches in the annealing sample. TLIM: wall-clock seconds for annealing.
     T0, T1: annealing temperatures (geometric schedule, sampled cost units). OUTPREFIX: output file prefix.
   Output: "COST exact_uncovered sources V G" and breakdown table (rows level 0..4, columns hex distance 0..6).
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;
#define DEG 8
#define LEV 5

static int V, K, G, LV, E;
static int *eu, *ev, *et, *ec, *ev_val, *fpos, *rpos;
static int *nbr;
static int add_t[25 * 25], negt[25];
static u64 *BUF1, *BUF2, *cur;
static unsigned char *hd;   /* V x V hexagon distance table */
static int *hexe, nhex;
static u64 rs = 88172645463325252ULL;

static inline u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static void set_edge(int e, int x) {
    ev_val[e] = x;
    int u = eu[e], v = ev[e];
    int af = x, ar = negt[x];
    for (int g = 0; g < G; g++) {
        nbr[(u * G + g) * DEG + fpos[e]] = v * G + add_t[g * G + af];
        nbr[(v * G + g) * DEG + rpos[e]] = u * G + add_t[g * G + ar];
    }
}

/* bit-parallel BFS from base sources src[0..nb-1] (fibre element 0); returns number of uncovered (source, lift vertex)
   pairs; leaves the reach masks in cur. */
static long long batch(const int *src, int nb) {
    u64 *A = BUF1, *B = BUF2;
    memset(A, 0, sizeof(u64) * LV);
    for (int j = 0; j < nb; j++) A[src[j] * G] |= 1ULL << j;
    for (int r = 0; r < 8; r++) {
        for (int x = 0; x < LV; x++) {
            u64 s = A[x];
            const int *p = &nbr[x * DEG];
            for (int j = 0; j < DEG; j++) s |= A[p[j]];
            B[x] = s;
        }
        u64 *t = A; A = B; B = t;
    }
    cur = A;
    long long reached = 0;
    for (int x = 0; x < LV; x++) reached += __builtin_popcountll(A[x]);
    return (long long)nb * LV - reached;
}

static long long sampled_cost(const int *samp, int ns) {
    long long c = 0;
    for (int i = 0; i < ns; i += 64) {
        int nb = ns - i < 64 ? ns - i : 64;
        c += batch(samp + i, nb);
    }
    return c;
}

static void hex_table(void) {
    /* BFS on hexagon flags only, from every base vertex */
    int *deg = calloc(V, sizeof(int)), *off = calloc(V + 1, sizeof(int));
    for (int e = 0; e < E; e++) if (et[e] == 0) { deg[eu[e]]++; deg[ev[e]]++; }
    for (int u = 0; u < V; u++) off[u + 1] = off[u] + deg[u];
    int *adj = malloc(sizeof(int) * off[V]), *fill = calloc(V, sizeof(int));
    for (int e = 0; e < E; e++) if (et[e] == 0) {
        adj[off[eu[e]] + fill[eu[e]]++] = ev[e];
        adj[off[ev[e]] + fill[ev[e]]++] = eu[e];
    }
    hd = malloc((size_t)V * V);
    int *q = malloc(sizeof(int) * V);
    for (int s = 0; s < V; s++) {
        unsigned char *row = hd + (size_t)s * V;
        memset(row, 255, V);
        int h = 0, t = 0;
        q[t++] = s; row[s] = 0;
        while (h < t) {
            int u = q[h++];
            for (int k = off[u]; k < off[u + 1]; k++) {
                int w = adj[k];
                if (row[w] == 255) { row[w] = row[u] + 1; q[t++] = w; }
            }
        }
    }
    free(deg); free(off); free(adj); free(fill); free(q);
}

int main(int argc, char **argv) {
    if (argc < 11) { fprintf(stderr, "usage: see header\n"); return 1; }
    const char *base = argv[1];
    K = atoi(argv[2]);
    const char *mode = argv[3];
    long steps = atol(argv[4]);
    rs ^= (u64)atol(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    int B = atoi(argv[6]);
    double tlim = atof(argv[7]), T0 = atof(argv[8]), T1 = atof(argv[9]);
    const char *outp = argv[10];
    G = LEV * K; LV = 0;

    FILE *f = fopen(base, "r");
    if (!f) { perror("base"); return 1; }
    if (fscanf(f, "%d", &V) != 1) return 1;
    E = 0;
    int cap = 40000; eu = malloc(sizeof(int) * cap); ev = malloc(sizeof(int) * cap);
    et = malloc(sizeof(int) * cap); ec = malloc(sizeof(int) * cap);
    int t_, u_, v_, c_;
    while (fscanf(f, "%d %d %d %d", &t_, &u_, &v_, &c_) == 4) {
        eu[E] = u_; ev[E] = v_; et[E] = t_; ec[E] = c_; E++;
    }
    fclose(f);
    LV = V * G;

    /* group Z_LEV x Z_K, element index g1*K + g2 */
    for (int x = 0; x < G; x++) for (int y = 0; y < G; y++) {
        int g1 = x / K, g2 = x % K, h1 = y / K, h2 = y % K;
        add_t[x * G + y] = ((g1 + h1) % LEV) * K + (g2 + h2) % K;
    }
    for (int x = 0; x < G; x++) {
        int g1 = x / K, g2 = x % K;
        negt[x] = ((LEV - g1) % LEV) * K + (K - g2) % K;
    }

    fpos = malloc(sizeof(int) * E); rpos = malloc(sizeof(int) * E); ev_val = malloc(sizeof(int) * E);
    int *cnt = calloc(V, sizeof(int));
    nhex = 0; hexe = malloc(sizeof(int) * E);
    for (int e = 0; e < E; e++) {
        fpos[e] = cnt[eu[e]]++;
        rpos[e] = cnt[ev[e]]++;
        if (et[e] == 0) hexe[nhex++] = e;
    }
    for (int u = 0; u < V; u++) if (cnt[u] != DEG) { fprintf(stderr, "degree %d at %d\n", cnt[u], u); return 1; }
    nbr = malloc(sizeof(int) * (size_t)LV * DEG);
    BUF1 = malloc(sizeof(u64) * LV); BUF2 = malloc(sizeof(u64) * LV);

    /* initial voltages */
    for (int e = 0; e < E; e++) {
        int x;
        if (et[e] == 1) x = ec[e] * K;          /* (c mod 5, 0) */
        else if (!strcmp(mode, "zero")) x = 0;
        else x = (int)(rnd() % K);               /* hexagon voltage (0, h) = h */
        set_edge(e, x);
    }
    hex_table();

    /* sample sources for annealing (B batches of 64 random base vertices) */
    int ns = 64 * B;
    int *samp = malloc(sizeof(int) * ns);
    for (int i = 0; i < ns; i++) samp[i] = (int)(rnd() % V);

    long long cur_c = sampled_cost(samp, ns);
    long long best_c = cur_c;
    int *bestv = malloc(sizeof(int) * E);
    for (int e = 0; e < E; e++) bestv[e] = ev_val[e];
    printf("init sampled cost %lld (ns=%d)\n", cur_c, ns); fflush(stdout);

    clock_t t0 = clock();
    long st;
    for (st = 0; st < steps && best_c > 0; st++) {
        double frac = (double)st / (double)steps;
        double T = T0 * pow(T1 / T0, frac);
        int e = hexe[rnd() % nhex];
        int old = ev_val[e];
        int nv = (int)((old + 1 + rnd() % (K - 1)) % K);
        set_edge(e, nv);
        long long c = sampled_cost(samp, ns);
        long long d = c - cur_c;
        double r = (double)(rnd() >> 11) / (double)(1ULL << 53);
        if (d <= 0 || r < exp(-(double)d / T)) {
            cur_c = c;
            if (c < best_c) {
                best_c = c;
                for (int i = 0; i < E; i++) bestv[i] = ev_val[i];
            }
        } else {
            set_edge(e, old);
        }
        if ((st & 255) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > tlim) break;
        }
    }
    printf("anneal steps %ld, best sampled cost %lld, time %.1fs\n", st,
           best_c, (double)(clock() - t0) / CLOCKS_PER_SEC);
    for (int i = 0; i < E; i++) if (et[i] == 0) set_edge(i, bestv[i]);

    /* exact full check: all base sources, batches of 64 */
    long long total = 0;
    long long bd[LEV][8];
    memset(bd, 0, sizeof bd);
    int *srcb = malloc(sizeof(int) * 64);
    for (int i = 0; i < V; i += 64) {
        int nb = V - i < 64 ? V - i : 64;
        for (int j = 0; j < nb; j++) srcb[j] = i + j;
        total += batch(srcb, nb);
        u64 full = nb == 64 ? ~0ULL : ((1ULL << nb) - 1);
        for (int x = 0; x < LV; x++) {
            u64 miss = full & ~cur[x];
            int t = x / G, g1 = (x % G) / K;
            while (miss) {
                int j = __builtin_ctzll(miss); miss &= miss - 1;
                bd[g1][hd[(size_t)(i + j) * V + t]]++;
            }
        }
    }
    printf("COST %lld exact_uncovered sources %d V %d G %d K %d\n", total, V, V, G, K);
    printf("breakdown uncovered (rows: level diff 0..4, cols: hexagon distance 0..6)\n");
    for (int l = 0; l < LEV; l++) {
        printf("L%d:", l);
        for (int h = 0; h <= 6; h++) printf(" %8lld", bd[l][h]);
        printf("\n");
    }
    char fn[512];
    snprintf(fn, sizeof fn, "%s_K%d.txt", outp, K);
    FILE *o = fopen(fn, "w");
    for (int e = 0; e < E; e++) if (et[e] == 0) fprintf(o, "%d %d %d\n", eu[e], ev[e], ev_val[e]);
    fclose(o);
    printf("wrote %s\n", fn);
    return 0;
}
