/* tabu1: exhaustive 1-move tabu walk from a salift_s state (job raise-small-d, director).
   Neighbourhood of a state (p+p cubic base multigraph, voltages in a group given by a gtab.py table):
     (a) every single voltage change (edge e, new voltage x in G): 3p (N-1) moves;
     (b) every swap of the black endpoints of two base edges (voltages kept): <= C(3p,2) moves.
   Each iteration evaluates the whole neighbourhood exactly (salift_s cost: (base root, vertex) pairs beyond D) and moves
   to the best non-tabu neighbour even if it is worse (edges touched in the last TENURE iterations are tabu unless the
   move beats the best cost so far). Writes OUT.best on every new best ("N id p cost" + 3p lines) and OUT at cost 0.
   Usage: tabu1 p TAB id START.best OUT.sol SECONDS [TENURE]   (env D). Wall-clock limit SECONDS.
   Build: gcc -O3 -march=native -o tabu1 tabu1.c -lm */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int p, k, N, D = 13, *mul, *inv, ne;
static int eu[96], ev[96], ea[96];
static uint64_t *R, *R2; static int *nbr;
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static long cost(void) {
    for (int e = 0; e < ne; e++) for (int f = e + 1; f < ne; f++)
        if (eu[e] == eu[f] && ev[e] == ev[f] && ea[e] == ea[f]) return 1L << 40;
    int n = k * N, dg[64] = {0};
    static int dv[64][3], da[64][3];
    for (int e = 0; e < ne; e++) { int u = eu[e], v = ev[e];
        if (dg[u] >= 3 || dg[v] >= 3) return 1L << 41;
        dv[u][dg[u]] = v; da[u][dg[u]++] = ea[e]; dv[v][dg[v]] = u; da[v][dg[v]++] = inv[ea[e]]; }
    for (int u = 0; u < k; u++) for (int g = 0; g < N; g++) for (int j = 0; j < 3; j++)
        nbr[(u * N + g) * 3 + j] = dv[u][j] * N + mul[(long)g * N + da[u][j]];
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
static void save(const char *fn, int gid, long c) {
    FILE *f = fopen(fn, "w"); fprintf(f, "%d %d %d %ld\n", N, gid, p, c);
    for (int e = 0; e < ne; e++) fprintf(f, "%d %d %d\n", eu[e], ev[e], ea[e]); fclose(f);
}
int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: tabu1 p TAB id START.best OUT.sol SECONDS [TENURE]\n"); return 2; }
    p = atoi(argv[1]); k = 2 * p; int want = atoi(argv[3]); double secs = atof(argv[6]);
    int ten = argc > 7 ? atoi(argv[7]) : 6;
    if (getenv("D")) D = atoi(getenv("D"));
    FILE *fg = fopen(argv[2], "r"); char tag[8], name[256]; int gid, found = 0;
    while (fscanf(fg, "%7s %d %d %255s", tag, &N, &gid, name) == 4) {
        mul = malloc(sizeof(int) * (long)N * N);
        for (long i = 0; i < (long)N * N; i++) if (fscanf(fg, "%d", &mul[i]) != 1) return 3;
        if (gid == want) { found = 1; break; }
        free(mul);
    }
    if (!found) { fprintf(stderr, "group not found\n"); return 2; }
    inv = malloc(sizeof(int) * N);
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) if (mul[(long)a * N + b] == 0) inv[a] = b;
    int n = k * N; R = malloc(8L * n); R2 = malloc(8L * n); nbr = malloc(sizeof(int) * 3 * n);
    ne = 3 * p;
    FILE *fs = fopen(argv[4], "r"); char hl[256]; int sN, sg, sp;
    if (!fs || !fgets(hl, sizeof hl, fs) || sscanf(hl, "%d %d %d", &sN, &sg, &sp) < 3 || sN != N || sp != p) { fprintf(stderr, "bad START\n"); return 2; }
    for (int e = 0; e < ne; e++) if (fscanf(fs, "%d %d %d", &eu[e], &ev[e], &ea[e]) != 3) { fprintf(stderr, "bad START\n"); return 2; }
    fclose(fs);
    char bp[600]; snprintf(bp, sizeof bp, "%s.best", argv[5]);
    long c = cost(), best = c; int tabu[96]; for (int e = 0; e < ne; e++) tabu[e] = -1000;
    double t0 = now(); printf("start cost %ld N=%d p=%d n=%d D=%d\n", c, N, p, n, D); fflush(stdout);
    for (int it = 0; now() - t0 < secs; it++) {
        long bc = 1L << 50; int bt = -1, be = -1, bx = -1, bj = -1;
        for (int e = 0; e < ne && now() - t0 < secs; e++) {
            int old = ea[e];
            for (int x = 0; x < N; x++) { if (x == old) continue;
                ea[e] = x; long c2 = cost();
                int ok = (it - tabu[e] > ten) || c2 < best;
                if (ok && (c2 < bc || (c2 == bc && (rand() & 1)))) { bc = c2; bt = 0; be = e; bx = x; } }
            ea[e] = old;
        }
        for (int i = 0; i < ne; i++) for (int j = i + 1; j < ne; j++) {
            if (ev[i] == ev[j]) continue;
            int t = ev[i]; ev[i] = ev[j]; ev[j] = t; long c2 = cost(); t = ev[i]; ev[i] = ev[j]; ev[j] = t;
            int ok = (it - tabu[i] > ten && it - tabu[j] > ten) || c2 < best;
            if (ok && c2 < bc) { bc = c2; bt = 1; be = i; bj = j; }
        }
        if (be < 0) break;
        if (bt == 0) { ea[be] = bx; tabu[be] = it; }
        else { int t = ev[be]; ev[be] = ev[bj]; ev[bj] = t; tabu[be] = tabu[bj] = it; }
        c = bc;
        printf("it %d t=%.0f cost %ld (best %ld)\n", it, now() - t0, c, best); fflush(stdout);
        if (c < best) { best = c; save(bp, gid, best); }
        if (c == 0) { save(argv[5], gid, 0); printf("FOUND\n"); break; }
    }
    printf("end best %ld\n", best);
    return 0;
}
