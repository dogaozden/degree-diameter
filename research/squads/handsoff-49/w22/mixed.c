/* w22: mixed bi-Cayley graphs. Vertices A = G (ids 0..N-1), B = G (ids N..2N-1).
   Left edges:  (g,A) ~ (s*g, B)  for s in S   (the Haar-type edges of haar_tab)
   Right edges: (g,A) ~ (g*t, B)  for t in T   (right translations; pure right = Haar after inversion)
   |S| + |T| = 4, so the graph is 4-regular bipartite. Mixing left and right moves is NOT a Haar graph in general.
   Cost = unordered pairs at distance > D (bit-parallel BFS from all 2N sources).
   Simulated annealing over the choice of S and T (replace one element at a time, reject non-simple graphs).
   Usage: mixed TABLE.bin a SECONDS SEED T0 T1 OUTPREFIX [SI]   (a = |S|, |T| = 4 - a; SI = fixed start S,T is not used)
   Table format (groups.py): int32 N, then N*N uint16, row g holds g*h, identity 0. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define D 9
static int N, NN;
static uint16_t *MT;
static int a_S, a_T;
static int S[4], T[4];
static int *adj;                 /* 4 per vertex */
static uint64_t *reach, *fra, *nwa;
static uint64_t rng_s;
static uint64_t rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
#define MUL(x, y) ((int)MT[(size_t)(x) * N + (y)])

static int is_simple(void) {
    for (int i = 0; i < a_S; i++) for (int j = i + 1; j < a_S; j++) if (S[i] == S[j]) return 0;
    for (int i = 0; i < a_T; i++) for (int j = i + 1; j < a_T; j++) if (T[i] == T[j]) return 0;
    for (int i = 0; i < a_S; i++) for (int j = 0; j < a_T; j++)
        for (int g = 0; g < N; g++) if (MUL(S[i], g) == MUL(g, T[j])) return 0;
    return 1;
}

static void build(void) {
    int deg[2 * 2600];
    for (int v = 0; v < 2 * N; v++) deg[v] = 0;
    for (int g = 0; g < N; g++) {
        for (int i = 0; i < a_S; i++) { int h = N + MUL(S[i], g); adj[g * 4 + deg[g]++] = h; adj[h * 4 + deg[h]++] = g; }
        for (int j = 0; j < a_T; j++) { int h = N + MUL(g, T[j]); adj[g * 4 + deg[g]++] = h; adj[h * 4 + deg[h]++] = g; }
    }
}

static long cost_full(void) {
    build();
    long far = 0; int V = 2 * N;
    for (int s0 = 0; s0 < V; s0 += 64) {
        int cnt = V - s0 < 64 ? V - s0 : 64;
        uint64_t mask = cnt == 64 ? ~0ULL : ((1ULL << cnt) - 1);
        for (int v = 0; v < V; v++) reach[v] = 0;
        for (int i = 0; i < cnt; i++) reach[s0 + i] |= 1ULL << i;
        memcpy(fra, reach, sizeof(uint64_t) * V);
        uint64_t *fr = fra, *nw = nwa;
        for (int lv = 1; lv <= D; lv++) {
            for (int v = 0; v < V; v++) {
                uint64_t x = fr[adj[v * 4]] | fr[adj[v * 4 + 1]] | fr[adj[v * 4 + 2]] | fr[adj[v * 4 + 3]];
                nw[v] = x & ~reach[v];
            }
            for (int v = 0; v < V; v++) reach[v] |= nw[v];
            uint64_t *tmp = fr; fr = nw; nw = tmp;
        }
        for (int v = 0; v < V; v++) far += __builtin_popcountll(mask & ~reach[v]);
    }
    return far / 2;
}

static void write_edges(const char *fn) {
    build();
    FILE *f = fopen(fn, "w"); int V = 2 * N;
    fprintf(f, "%d\n", V);
    for (int v = 0; v < V; v++) for (int t = 0; t < 4; t++) if (adj[v * 4 + t] > v) fprintf(f, "%d %d\n", v, adj[v * 4 + t]);
    fclose(f);
}

static void random_elem_set(int *arr, int cnt) {
    for (int i = 0; i < cnt; i++) {
        int ok;
        do { arr[i] = 1 + rnd() % (N - 1); ok = 1; for (int j = 0; j < i; j++) if (arr[j] == arr[i]) ok = 0; } while (!ok);
    }
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: mixed TABLE.bin a SECONDS SEED T0 T1 OUTPREFIX\n"); return 2; }
    FILE *f = fopen(argv[1], "rb"); int32_t n32; if (!f || fread(&n32, 4, 1, f) != 1) { fprintf(stderr, "bad table\n"); return 2; }
    N = n32; NN = N * N; MT = malloc(2 * (size_t)NN); if (fread(MT, 2, NN, f) != (size_t)NN) { fprintf(stderr, "short table\n"); return 2; }
    fclose(f);
    a_S = atoi(argv[2]); a_T = 4 - a_S;
    double secs = atof(argv[3]); rng_s = strtoull(argv[4], 0, 10) * 2654435761ULL + 1234567ULL;
    double T0 = atof(argv[5]), T1 = atof(argv[6]); const char *outp = argv[7];
    int V = 2 * N;
    adj = malloc(sizeof(int) * 4 * V); reach = malloc(8 * V); fra = malloc(8 * V); nwa = malloc(8 * V);
    /* initial random simple configuration */
    int tries = 0;
    do { random_elem_set(S, a_S); random_elem_set(T, a_T); tries++; } while (!is_simple() && tries < 100000);
    if (!is_simple()) { fprintf(stderr, "no simple start\n"); return 2; }
    long cur = cost_full(), best = cur;
    char fn[512]; snprintf(fn, sizeof fn, "%s.best.edges", outp);
    fprintf(stderr, "init far=%ld\n", cur);
    write_edges(fn);
    time_t t0 = time(NULL); long it = 0, acc = 0;
    while (difftime(time(NULL), t0) < secs) {
        double frac = difftime(time(NULL), t0) / secs;
        double Tm = T0 * pow(T1 / T0, frac);
        int side = rnd() % 4; int idx, old, nv;
        if (side < a_S) { idx = side; old = S[idx]; } else { if (a_T == 0) continue; idx = (side - a_S) % a_T; old = T[idx]; }
        do { nv = 1 + rnd() % (N - 1); } while (nv == old);
        if (side < a_S) S[idx] = nv; else T[idx] = nv;
        if (!is_simple()) { if (side < a_S) S[idx] = old; else T[idx] = old; continue; }
        long c = cost_full(); it++;
        long d = c - cur;
        if (d <= 0 || urand() < exp(-d / Tm)) {
            cur = c; acc++;
            if (c < best) {
                best = c; write_edges(fn);
                fprintf(stderr, "it=%ld T=%.3f best=%ld\n", it, Tm, best);
                if (best == 0) { fprintf(stderr, "FOUND far=0\n"); break; }
            }
        } else { if (side < a_S) S[idx] = old; else T[idx] = old; }
    }
    printf("RESULT N=%d a=%d best_far=%ld it=%ld acc=%ld S=", N, a_S, best, it, acc);
    for (int i = 0; i < a_S; i++) printf("%d,", S[i]); printf(" T="); for (int i = 0; i < a_T; i++) printf("%d,", T[i]); printf("\n");
    return 0;
}
