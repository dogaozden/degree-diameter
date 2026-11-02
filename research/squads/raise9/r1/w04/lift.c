/* lift.c: voltage-lift annealer for bipartite Delta-regular diameter search.
   usage: lift BASEFILE GROUP SECS SEED D OUT
   BASEFILE: "bU bV" then one "u v" line per base edge (u in 0..bU-1, v in 0..bV-1; multi-edges allowed).
   GROUP: "cyc m" (Z_m) or "frob p k" (Z_p x| Z_k, k | p-1, action by element of order k).
   Lift vertices: (x,g), x base vertex (U: 0..bU-1, V: bU..), g in G; edge (u,g)~(v,g*a) per base edge (u,v,a).
   Cost = sum over base sources s of #vertices not within distance D of (s,identity)  (+ n per equal parallel voltage).
   Writes OUT (edge list "n" then "u v") on cost 0 and OUT.best (best voltages) at each improvement. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <math.h>
#include <sys/time.h>
static double wall(void){ struct timeval tv; gettimeofday(&tv, 0); return tv.tv_sec + tv.tv_usec * 1e-6; }

static int N, nb, bU, bV, E, DEG, D;
static int *eu, *ev, *vol, *best_vol;
static int *mul, *inv_;
static int *vis, stamp = 0, *qbuf;
static unsigned long long rng;
static inline unsigned long long rnd(void){ rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline double urand(void){ return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int *inc[64]; static int incn[64];   /* incident base edges per base vertex */

static int powmod(int a, long e, int p){ long r = 1; long b = a % p; while (e){ if (e & 1) r = r * b % p; b = b * b % p; e >>= 1; } return (int)r; }

static void build_group(const char *kind, int a1, int a2){
    if (!strcmp(kind, "cyc")) {
        N = a1; mul = malloc(sizeof(int) * N * N); inv_ = malloc(sizeof(int) * N);
        for (int i = 0; i < N; i++) for (int j = 0; j < N; j++) mul[i * N + j] = (i + j) % N;
        for (int i = 0; i < N; i++) inv_[i] = (N - i) % N;
    } else { /* frob p k */
        int p = a1, k = a2; N = p * k;
        if ((p - 1) % k) { fprintf(stderr, "k must divide p-1\n"); exit(1); }
        int g = 2; /* primitive root search */
        for (;; g++) { int ok = 1; int m = p - 1;
            for (int q = 2; q <= m; q++) if (m % q == 0) { int prime = 1; for (int d = 2; d * d <= q; d++) if (q % d == 0) { prime = 0; break; }
                if (prime && powmod(g, (p - 1) / q, p) == 1) { ok = 0; break; } }
            if (ok) break; }
        int r = powmod(g, (p - 1) / k, p);
        int *rp = malloc(sizeof(int) * k); rp[0] = 1; for (int t = 1; t < k; t++) rp[t] = rp[t - 1] * r % p;
        mul = malloc(sizeof(int) * N * N); inv_ = malloc(sizeof(int) * N);
        for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) {
            int a = x / k, t = x % k, b = y / k, s = y % k;
            int aa = (int)((a + (long)rp[t] * b) % p), ss = (t + s) % k;
            mul[x * N + y] = aa * k + ss; }
        for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) if (mul[x * N + y] == 0) inv_[x] = y;
        free(rp);
    }
}

static inline int M(int a, int b){ return mul[a * N + b]; }

/* BFS from (s, identity) to depth D; returns number reached */
static int reach(int s){
    int reached = 0; stamp++;
    int head = 0, tail = 0, lvl_end, depth = 0;
    int start = s * N + 0;
    vis[start] = stamp; qbuf[tail++] = start; reached = 1;
    lvl_end = tail;
    while (depth < D && head < tail) {
        while (head < lvl_end) {
            int id = qbuf[head++]; int x = id / N, g = id % N;
            for (int i = 0; i < incn[x]; i++) {
                int e = inc[x][i]; int y, h;
                if (x == eu[e]) { y = ev[e]; h = M(g, vol[e]); }
                else { y = eu[e]; h = M(g, inv_[vol[e]]); }
                int nid = y * N + h;
                if (vis[nid] != stamp) { vis[nid] = stamp; qbuf[tail++] = nid; }
            }
        }
        reached = tail; lvl_end = tail; depth++;
    }
    return reached;
}

static long cost_of(void){
    int n = nb * N; long c = 0;
    for (int e = 0; e < E; e++) for (int f = e + 1; f < E; f++)
        if (eu[e] == eu[f] && ev[e] == ev[f] && vol[e] == vol[f]) c += n;
    if (c) return c;
    for (int s = 0; s < nb; s++) c += n - reach(s);
    return c;
}

static void write_graph(const char *out){
    int n = nb * N; FILE *f = fopen(out, "w"); fprintf(f, "%d\n", n);
    for (int e = 0; e < E; e++) for (int g = 0; g < N; g++)
        fprintf(f, "%d %d\n", eu[e] * N + g, ev[e] * N + M(g, vol[e]));
    fclose(f);
}


static void rand_vol_all(void){ for (int e = 0; e < E; e++) vol[e] = rnd() % N; }

int main(int argc, char **argv){
    if (argc < 7) { fprintf(stderr, "usage: lift BASEFILE \"cyc m\"|\"frob p k\" SECS SEED D OUT [T0 T1 CYC]\n"); return 1; }
    FILE *bf = fopen(argv[1], "r"); if (!bf) { fprintf(stderr, "no base\n"); return 1; }
    if (fscanf(bf, "%d %d", &bU, &bV) != 2) return 1;
    nb = bU + bV; int cap = 256; eu = malloc(sizeof(int) * cap); ev = malloc(sizeof(int) * cap); E = 0;
    int u, v; while (fscanf(bf, "%d %d", &u, &v) == 2) { if (E == cap) { cap *= 2; eu = realloc(eu, sizeof(int) * cap); ev = realloc(ev, sizeof(int) * cap); }
        eu[E] = u; ev[E] = bU + v; E++; }
    fclose(bf);
    DEG = 0; for (int e = 0; e < E; e++) if (eu[e] == 0) DEG++;
    for (int x = 0; x < nb; x++) { incn[x] = 0; inc[x] = malloc(sizeof(int) * E); }
    for (int e = 0; e < E; e++) { inc[eu[e]][incn[eu[e]]++] = e; inc[ev[e]][incn[ev[e]]++] = e; }
    for (int x = 0; x < nb; x++) if (incn[x] != DEG) { fprintf(stderr, "base not regular\n"); return 1; }
    char kind[16]; int a1 = 0, a2 = 0;
    if (sscanf(argv[2], "%15s %d %d", kind, &a1, &a2) < 2) return 1;
    build_group(kind, a1, a2);
    double secs = atof(argv[3]); rng = strtoull(argv[4], 0, 10) * 2654435761ULL + 88172645463325252ULL;
    D = atoi(argv[5]); const char *out = argv[6];
    double T0 = argc > 7 ? atof(argv[7]) : 3.0, T1 = argc > 8 ? atof(argv[8]) : 0.15;
    long CYC = argc > 9 ? atol(argv[9]) : 20000;
    int n = nb * N;
    vis = calloc(n, sizeof(int)); qbuf = malloc(sizeof(int) * n);
    vol = malloc(sizeof(int) * E); best_vol = malloc(sizeof(int) * E);
    rand_vol_all();
    long cur = cost_of(); long gbest = cur; memcpy(best_vol, vol, sizeof(int) * E);
    int *cur_vol = malloc(sizeof(int) * E); memcpy(cur_vol, vol, sizeof(int) * E);
    fprintf(stderr, "n=%d N=%d E=%d deg=%d init cost %ld\n", n, N, E, DEG, cur);
    double t0 = wall(); long it = 0; long cyc_it = 0; double T = T0; long cycles = 0;
    while (1) {
        if ((it & 255) == 0) { if (wall() - t0 > secs) break; }
        it++;
        /* cycle: cool from T0 to T1 over CYC steps, then restart from best (half) or random */
        if (cyc_it == 0) { T = T0; cycles++; if (cycles & 1) memcpy(vol, best_vol, sizeof(int) * E); else rand_vol_all(); cur = cost_of(); }
        double frac = (double)cyc_it / CYC; T = T0 * pow(T1 / T0, frac);
        int e = rnd() % E; int old = vol[e]; int nv = rnd() % N;
        if (nv == old) continue;
        vol[e] = nv; long c = cost_of();
        if (c <= cur || urand() < exp(-(double)(c - cur) / T)) {
            cur = c;
            if (c < gbest) { gbest = c; memcpy(best_vol, vol, sizeof(int) * E);
                fprintf(stderr, "it %ld cycle %ld best %ld\n", it, cycles, gbest);
                if (gbest == 0) break; }
        } else vol[e] = old;
        if (++cyc_it >= CYC) cyc_it = 0;
    }
    memcpy(vol, best_vol, sizeof(int) * E);
    long fin = cost_of();
    printf("kind=%s base=%s N=%d n=%d best_cost=%ld evals=%ld cycles=%ld secs=%.1f\n", argv[2], argv[1], N, n, fin, it, cycles, wall() - t0);
    if (fin == 0) { write_graph(out); printf("WROTE %s\n", out); }
    printf("VOL");
    for (int e = 0; e < E; e++) printf(" %d", best_vol[e]);
    printf("\n");
    return 0;
}
