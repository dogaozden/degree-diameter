/* polish: exact neighbourhood search around a salift state (own-small job). Tries every single-voltage change, every
   swap of the black endpoints of two base edges, every pair of voltage changes, and every swap combined with a new voltage
   on one of the two edges; writes OUT (salift .sol format "N id p" + 3p lines) and stops at the first cost-0 state.
   Otherwise moves to the best strictly improving neighbour and repeats (steepest descent) until no improvement.
   Usage: polish p GROUPS id START.best OUT.sol   (env D, as salift). Cost as salift: (root, vertex) pairs beyond D. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int p, k, N, D = 7, *mul, *inv, ne;
static int eu[96], ev[96], ea[96];
static uint64_t *R, *R2; static int *nbr;
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }

static long cost(void) {
    for (int e = 0; e < ne; e++) for (int f = e + 1; f < ne; f++)
        if (eu[e] == eu[f] && ev[e] == ev[f] && ea[e] == ea[f]) return 1L << 40;
    int n = k * N, dg[64] = {0};
    static int dv[64][3], da[64][3];
    for (int e = 0; e < ne; e++) { int u = eu[e], v = ev[e];
        dv[u][dg[u]] = v; da[u][dg[u]++] = ea[e]; dv[v][dg[v]] = u; da[v][dg[v]++] = inv[ea[e]]; }
    for (int u = 0; u < k; u++) for (int g = 0; g < N; g++) for (int j = 0; j < 3; j++)
        nbr[(u * N + g) * 3 + j] = dv[u][j] * N + mul[g * N + da[u][j]];
    memset(R, 0, 8L * n);
    for (int u = 0; u < k; u++) R[u * N] = 1ULL << u;
    for (int t = 0; t < D; t++) {
        for (int x = 0; x < n; x++) R2[x] = R[x] | R[nbr[3 * x]] | R[nbr[3 * x + 1]] | R[nbr[3 * x + 2]];
        uint64_t *tmp = R; R = R2; R2 = tmp;
    }
    uint64_t full = k == 64 ? ~0ULL : (1ULL << k) - 1; long c = 0;
    for (int x = 0; x < n; x++) c += __builtin_popcountll(~R[x] & full);
    return c;
}


static void save(const char *out, long c) {
    FILE *f = fopen(out, "w"); fprintf(f, "%d %d %d %ld\n", N, -1, p, c);
    for (int e = 0; e < ne; e++) fprintf(f, "%d %d %d\n", eu[e], ev[e], ea[e]); fclose(f);
}
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: polish p GROUPS id START.best OUT.sol\n"); return 2; }
    p = atoi(argv[1]); k = 2 * p; int want = atoi(argv[3]);
    if (getenv("D")) D = atoi(getenv("D"));
    FILE *fg = fopen(argv[2], "r"); char tag[8], name[256]; int gid, found = 0;
    while (fscanf(fg, "%7s %d %d %255s", tag, &N, &gid, name) == 4) {
        mul = malloc(sizeof(int) * N * N);
        for (int i = 0; i < N * N; i++) if (fscanf(fg, "%d", &mul[i]) != 1) return 3;
        if (gid == want) { found = 1; break; }
        free(mul);
    }
    if (!found) { fprintf(stderr, "group not found\n"); return 2; }
    inv = malloc(sizeof(int) * N);
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) if (mul[a * N + b] == 0) inv[a] = b;
    int n = k * N; R = malloc(8L * n); R2 = malloc(8L * n); nbr = malloc(sizeof(int) * 3 * n);
    ne = 3 * p;
    FILE *fs = fopen(argv[4], "r"); int sN, sg, sp; long sc;
    if (!fs || fscanf(fs, "%d %d %d %ld", &sN, &sg, &sp, &sc) != 4 || sN != N || sp != p) { fprintf(stderr, "bad START\n"); return 2; }
    for (int e = 0; e < ne; e++) if (fscanf(fs, "%d %d %d", &eu[e], &ev[e], &ea[e]) != 3) return 2;
    fclose(fs);
    const char *out = argv[5];
    long cur = cost(); printf("start cost %ld (n=%d)\n", cur, n); fflush(stdout);
    for (int round = 0; ; round++) {
        long best = cur; int bu[96], bv[96], ba[96]; memcpy(bu, eu, sizeof eu); memcpy(bv, ev, sizeof ev); memcpy(ba, ea, sizeof ea);
        long evals = 0;
#define TRY() do { long c_ = cost(); evals++; if (c_ < best) { best = c_; memcpy(bu, eu, sizeof eu); memcpy(bv, ev, sizeof ev); memcpy(ba, ea, sizeof ea); \
            if (c_ == 0) { save(out, 0); printf("FOUND cost 0 (round %d, evals %ld)\n", round, evals); return 0; } } } while (0)
        /* single voltage changes */
        for (int i = 0; i < ne; i++) { int s0 = ea[i]; for (int a = 0; a < N; a++) if (a != s0) { ea[i] = a; TRY(); } ea[i] = s0; }
        /* endpoint swaps, alone and with one new voltage */
        for (int i = 0; i < ne; i++) for (int j = i + 1; j < ne; j++) if (ev[i] != ev[j] && eu[i] != eu[j]) {
            int t = ev[i]; ev[i] = ev[j]; ev[j] = t; TRY();
            for (int w = 0; w < 2; w++) { int e = w ? j : i, s0 = ea[e]; for (int a = 0; a < N; a++) if (a != s0) { ea[e] = a; TRY(); } ea[e] = s0; }
            t = ev[i]; ev[i] = ev[j]; ev[j] = t; }
        printf("round %d: level-1 best %ld (evals %ld)\n", round, best, evals); fflush(stdout);
        if (best >= cur) {
            /* pairs of voltage changes */
            for (int i = 0; i < ne; i++) for (int j = i + 1; j < ne; j++) {
                int si = ea[i], sj = ea[j];
                for (int a = 0; a < N; a++) { if (a == si) continue; ea[i] = a;
                    for (int b = 0; b < N; b++) { if (b == sj) continue; ea[j] = b; TRY(); } }
                ea[i] = si; ea[j] = sj; }
            printf("round %d: level-2 best %ld (evals %ld)\n", round, best, evals); fflush(stdout);
        }
        if (best >= cur) { printf("local minimum %ld\n", cur); save(out, cur); return 1; }
        memcpy(eu, bu, sizeof eu); memcpy(ev, bv, sizeof ev); memcpy(ea, ba, sizeof ea); cur = best; save(out, cur);
    }
}
