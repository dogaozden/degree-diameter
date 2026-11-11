/* a03: annealing over voltage lifts of the Heawood graph (14 base vertices, cubic, girth 6)
 * over metacyclic groups G = Z_A x|_R Z_B (element (x,y) = x*B+y, (x1,y1)(x2,y2) = (x1 + R^y1 x2 mod A, y1+y2 mod B)).
 * Lift: vertices (u,g), u in 0..13, g in G; base edge k = (point ea[k], line eb[k]) with voltage c_k:
 * (ea,g) ~ (eb, g c_k). Tree edges (BFS tree from 0) get voltage identity; the 8 cotree edges are free.
 * Left multiplication is an automorphism, so diameter <= D iff every BFS from (u,e) reaches all vertices within D.
 * cost = sum over u of #{x : dist((u,e),x) > D}.
 * usage: lift3 A B R secs seed OUT      (env D=12 default)
 * writes OUT (voltages, text) and OUT.edges (edge list, first line n) when cost 0.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>
#include <math.h>

#define NBASE 14
#define NEDGE 21
#define NPT 7

static int A, B, R, M, N, DIAM = 12;
static int *MUL, *INV;
static int ea[NEDGE], eb[NEDGE];
static int tree_edge[NEDGE];
static int cot[NEDGE], ncot;
static int volt[NEDGE];
static int base_nb[NBASE][3], base_ke[NBASE][3], base_dir[NBASE][3];
static int nv[NBASE][3];
static signed char *dist;
static int *queue;
static uint64_t rng = 88172645463325252ULL;

static inline uint64_t rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static inline double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int build_group(void) {
    M = A * B; N = NBASE * M;
    int *rp = malloc(sizeof(int) * (B + 1));
    for (int y = 0; y < B; y++) { int v = 1 % A; for (int t = 0; t < y; t++) v = (v * R) % A; rp[y] = v; }
    /* well-definedness: R^B == 1 mod A */
    if ((rp[B - 1] * R) % A != 1 % A) { fprintf(stderr, "bad group: R^B != 1 mod A\n"); return 0; }
    MUL = malloc(sizeof(int) * M * M); INV = malloc(sizeof(int) * M);
    for (int g1 = 0; g1 < M; g1++) for (int g2 = 0; g2 < M; g2++) {
        int x1 = g1 / B, y1 = g1 % B, x2 = g2 / B, y2 = g2 % B;
        int x = (x1 + rp[y1] * x2) % A, y = (y1 + y2) % B;
        MUL[g1 * M + g2] = x * B + y;
    }
    for (int g = 0; g < M; g++) for (int h = 0; h < M; h++) if (MUL[g * M + h] == 0) { INV[g] = h; break; }
    free(rp);
    return 1;
}

static void build_base(void) {
    /* Heawood graph: point i ~ line 7 + ((i + d) mod 7), d in {0,1,3} */
    static const int D3[3] = {0, 1, 3};
    for (int i = 0; i < NPT; i++) for (int t = 0; t < 3; t++) {
        int k = 3 * i + t; ea[k] = i; eb[k] = NPT + ((i + D3[t]) % NPT);
    }
    /* BFS spanning tree from base vertex 0 */
    int seen[NBASE] = {0}, qq[NBASE], qh = 0, qt = 0;
    for (int k = 0; k < NEDGE; k++) tree_edge[k] = 0;
    seen[0] = 1; qq[qt++] = 0;
    while (qh < qt) {
        int u = qq[qh++];
        for (int k = 0; k < NEDGE; k++) {
            int w = -1;
            if (ea[k] == u) w = eb[k]; else if (eb[k] == u) w = ea[k];
            if (w >= 0 && !seen[w]) { seen[w] = 1; tree_edge[k] = 1; qq[qt++] = w; }
        }
    }
    ncot = 0;
    for (int k = 0; k < NEDGE; k++) if (!tree_edge[k]) cot[ncot++] = k;
    /* incidence lists */
    int cnt[NBASE] = {0};
    for (int k = 0; k < NEDGE; k++) {
        int p = ea[k], l = eb[k];
        base_nb[p][cnt[p]] = l; base_ke[p][cnt[p]] = k; base_dir[p][cnt[p]] = 0; cnt[p]++;
        base_nb[l][cnt[l]] = p; base_ke[l][cnt[l]] = k; base_dir[l][cnt[l]] = 1; cnt[l]++;
    }
}

static void set_volts(void) {
    for (int k = 0; k < NEDGE; k++) volt[k] = tree_edge[k] ? 0 : volt[k];
    for (int u = 0; u < NBASE; u++) for (int t = 0; t < 3; t++) {
        int c = volt[base_ke[u][t]];
        nv[u][t] = base_dir[u][t] == 0 ? c : INV[c];
    }
}

static long total_bfs = 0;

static int cost_of(void) {
    set_volts();
    int total = 0;
    for (int u = 0; u < NBASE; u++) {
        memset(dist, -1, N);
        int src = u * M; /* (u, identity) */
        int qh = 0, qt = 0;
        dist[src] = 0; queue[qt++] = src;
        int reached = 1;
        while (qh < qt) {
            int x = queue[qh++]; int dx = dist[x];
            if (dx >= DIAM) continue;
            int bu = x / M, g = x % M;
            for (int t = 0; t < 3; t++) {
                int w = base_nb[bu][t];
                int y = w * M + MUL[g * M + nv[bu][t]];
                if (dist[y] < 0) { dist[y] = dx + 1; queue[qt++] = y; }
            }
        }
        reached = qt;
        total += N - reached;
        total_bfs++;
    }
    return total;
}

static void write_result(const char *out, int cost) {
    FILE *f = fopen(out, "w");
    if (!f) return;
    fprintf(f, "# A B R M N cost; volts over the 8 cotree edges (base edge index k, group element)\n");
    fprintf(f, "%d %d %d %d %d %d\n", A, B, R, M, N, cost);
    for (int t = 0; t < ncot; t++) fprintf(f, "%d %d\n", cot[t], volt[cot[t]]);
    fclose(f);
    char fn[1024]; snprintf(fn, sizeof fn, "%s.edges", out);
    FILE *g = fopen(fn, "w");
    if (!g) return;
    fprintf(g, "%d\n", NBASE * M);
    for (int k = 0; k < NEDGE; k++) for (int h = 0; h < M; h++) {
        int u = ea[k] * M + h;
        int v = eb[k] * M + MUL[h * M + volt[k]];
        fprintf(g, "%d %d\n", u, v);
    }
    fclose(g);
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: lift3 A B R secs seed OUT\n"); return 1; }
    A = atoi(argv[1]); B = atoi(argv[2]); R = atoi(argv[3]);
    double secs = atof(argv[4]);
    rng ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    const char *out = argv[6];
    if (getenv("D")) DIAM = atoi(getenv("D"));
    if (!build_group()) return 1;
    build_base();
    dist = malloc(N); queue = malloc(sizeof(int) * N);

    int best_cost = 1 << 30; int bestv[NEDGE];
    int cur_cost; int curv[NEDGE];
    clock_t t0 = clock();
    long iters = 0, restarts = 0;
    /* restart loop: each restart anneals with a cyclic temperature schedule */
    while (1) {
        for (int k = 0; k < NEDGE; k++) volt[k] = 0;
        for (int t = 0; t < ncot; t++) volt[cot[t]] = rndint(M);
        cur_cost = cost_of();
        int restart_best = cur_cost;
        restarts++;
        long period = 4000; long since = 0;
        for (long it = 0; ; it++) {
            iters++;
            if ((iters & 255) == 0) {
                double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
                if (el > secs) goto done;
            }
            double ph = (double)(it % period) / period;
            double T = 0.02 + 1.2 * (1.0 - ph) * (1.0 - ph);
            int k = cot[rndint(ncot)];
            int old = volt[k];
            volt[k] = rndint(M);
            int c = cost_of();
            int d = c - cur_cost;
            if (d <= 0 || rnd01() < exp(-d / T)) {
                cur_cost = c;
                if (c < restart_best) { restart_best = c; since = 0; }
                if (c < best_cost) {
                    best_cost = c; memcpy(bestv, volt, sizeof volt);
                    if (c == 0) break;
                }
            } else {
                volt[k] = old;
            }
            since++;
            if (since > 60000) break;
            if (best_cost == 0) break;
        }
        if (best_cost == 0) break;
    }
done:;
    memcpy(volt, bestv, sizeof volt);
    double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
    int fc = cost_of();
    printf("RESULT A=%d B=%d R=%d M=%d N=%d D=%d best_cost=%d evals=%ld restarts=%ld secs=%.1f\n",
           A, B, R, M, N, DIAM, fc, iters, restarts, el);
    if (fc == 0) write_result(out, fc);
    return 0;
}
