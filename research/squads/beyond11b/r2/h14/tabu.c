/* h14: tabu search over the free voltages of cubic bipartite voltage lifts (B+B base, metacyclic G = Z_M x|_R Z_K).
 * Same lift model and cost as r1/g14/lift.c (cost = #(source,vertex) pairs at distance > D + parallel-edge penalty),
 * but: full-neighbourhood tabu on the b+1 non-tree voltages instead of random hill climbing.
 * Validation mode (secs < 0): one random lift, prints its exact diameter (max eccentricity over the 2B identity
 * sources; valid because G acts transitively on each fibre) and writes its edge list OUT for apsp.
 * usage: tabu M K R B D secs seed OUT [maxstall] [sample]      (writes OUT = "N" + "u v" lines on cost 0)              */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
static int M, K, R, n, B, D, NV, N;
static int *MUL, *INV;
static int eu[64], ew[64], ex[64], istree[64], ne, fr[64], nfr;
static int *adj, *dist, *q;
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned long long xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rnd(int k) { return (int)(xr() % (unsigned long long)k); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int gen_base(void) {
    int bl[64], wh[64], i, j, t;
    for (i = 0; i < 3 * B; i++) { bl[i] = i / 3; wh[i] = i / 3; }
    for (i = 3 * B - 1; i > 0; i--) { j = rnd(i + 1); t = wh[i]; wh[i] = wh[j]; wh[j] = t; }
    ne = 3 * B;
    for (i = 0; i < ne; i++) { eu[i] = bl[i]; ew[i] = wh[i]; istree[i] = 0; }
    int seen[128], qq[128], h = 0, tl = 0, cnt = 1;
    memset(seen, 0, sizeof(seen));
    seen[0] = 1; qq[tl++] = 0;
    while (h < tl) {
        int v = qq[h++];
        for (i = 0; i < ne; i++) {
            int a = eu[i], b = B + ew[i], o = -1;
            if (a == v) o = b; else if (b == v) o = a; else continue;
            if (!seen[o]) { seen[o] = 1; qq[tl++] = o; istree[i] = 1; cnt++; }
        }
    }
    nfr = 0;
    for (i = 0; i < ne; i++) if (!istree[i]) fr[nfr++] = i;
    return cnt == 2 * B;
}
/* returns cost; if dmax != NULL stores the exact diameter (or -1 if disconnected) */
static int evalc(int *dmax) {
    int c = 0, s, i, h, tl, j, dm = 0, disc = 0;
    for (i = 0; i < ne; i++) for (j = i + 1; j < ne; j++)
        if (eu[i] == eu[j] && ew[i] == ew[j] && ex[i] == ex[j]) c += N;
    for (int v = 0; v < B; v++) for (int g = 0; g < n; g++) {
        int id = v * n + g, k = 0;
        for (i = 0; i < ne; i++) if (eu[i] == v) adj[id * 3 + k++] = (B + ew[i]) * n + MUL[g * n + ex[i]];
    }
    for (int w = 0; w < B; w++) for (int g = 0; g < n; g++) {
        int id = (B + w) * n + g, k = 0;
        for (i = 0; i < ne; i++) if (ew[i] == w) adj[id * 3 + k++] = eu[i] * n + MUL[g * n + INV[ex[i]]];
    }
    for (s = 0; s < NV; s++) {
        int src = s * n;
        for (i = 0; i < N; i++) dist[i] = -1;
        h = 0; tl = 0; q[tl++] = src; dist[src] = 0;
        while (h < tl) {
            int x = q[h++];
            for (j = 0; j < 3; j++) { int y = adj[x * 3 + j]; if (dist[y] < 0) { dist[y] = dist[x] + 1; q[tl++] = y; } }
        }
        if (tl < N) disc = 1;
        for (i = 0; i < tl; i++) if (dist[q[i]] > dm) dm = dist[q[i]];
        if (dmax == NULL) { /* early exit only in search mode */
            for (i = 0; i < N; i++) if (dist[i] < 0 || dist[i] > D) c++;
            if (c > N * 4) return c;
        } else {
            for (i = 0; i < N; i++) if (dist[i] < 0 || dist[i] > D) c++;
        }
    }
    if (dmax) *dmax = disc ? -1 : dm;
    return c;
}
static void write_out(const char *out) {
    FILE *fo = fopen(out, "w");
    fprintf(fo, "%d\n", N);
    for (int v = 0; v < B; v++) for (int g = 0; g < n; g++) {
        int id = v * n + g;
        for (int j = 0; j < 3; j++) fprintf(fo, "%d %d\n", id, adj[id * 3 + j]);
    }
    fclose(fo);
}
int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: tabu M K R B D secs seed OUT [maxstall] [sample]\n"); return 1; }
    M = atoi(argv[1]); K = atoi(argv[2]); R = atoi(argv[3]); B = atoi(argv[4]); D = atoi(argv[5]);
    double secs = atof(argv[6]); rs ^= (unsigned long long)atoll(argv[7]) * 2654435761ULL + 1;
    const char *out = argv[8];
    int maxstall = argc > 9 ? atoi(argv[9]) : 60;
    int sample = argc > 10 ? atoi(argv[10]) : 0;
    n = M * K; NV = 2 * B; N = NV * n;
    int *RP = malloc(sizeof(int) * (K + 1)); RP[0] = 1 % M;
    for (int b = 1; b <= K; b++) RP[b] = (int)((long long)RP[b - 1] * R % M);
    if ((long long)RP[K] != 1 % M) { fprintf(stderr, "R^K != 1 mod M\n"); return 1; }
    MUL = malloc(sizeof(int) * n * n); INV = malloc(sizeof(int) * n);
    for (int x = 0; x < n; x++) for (int y = 0; y < n; y++) {
        int a = x / K, b = x % K, c = y / K, d = y % K;
        int aa = (int)((a + (long long)RP[b] * c) % M), dd = (b + d) % K;
        MUL[x * n + y] = aa * K + dd;
    }
    for (int x = 0; x < n; x++) for (int y = 0; y < n; y++) if (MUL[x * n + y] == 0) INV[x] = y;
    adj = malloc(sizeof(int) * N * 3); dist = malloc(sizeof(int) * N); q = malloc(sizeof(int) * N);
    if (secs < 0) { /* validation */
        gen_base();
        for (int i = 0; i < ne; i++) ex[i] = istree[i] ? 0 : rnd(n);
        int dm, c = evalc(&dm);
        printf("VALIDATE M=%d K=%d R=%d B=%d N=%d cost=%d lift_diameter=%d\n", M, K, R, B, N, c, dm);
        write_out(out);
        return 0;
    }
    double t0 = now(), tend = t0 + secs;
    int *tabu = malloc(sizeof(int) * 64 * n);
    int best_all = 1 << 30, found = 0, restarts = 0; long evals = 0;
    while (now() < tend && !found) {
        if (!gen_base()) continue;
        restarts++;
        for (int i = 0; i < ne; i++) ex[i] = istree[i] ? 0 : rnd(n);
        if (nfr == 0) break;
        memset(tabu, 0, sizeof(int) * 64 * n);
        int cur = evalc(NULL); evals++;
        int best = cur, stall = 0;
        for (int step = 1; cur > 0 && stall < maxstall && now() < tend; step++) {
            int bc = 1 << 30, bf = -1, bv = -1, nties = 0;
            int nmoves = sample > 0 ? sample : nfr * n;
            for (int mi = 0; mi < nmoves; mi++) {
                int a = sample > 0 ? rnd(nfr) : mi / n;
                int f = fr[a], old = ex[f];
                int v = sample > 0 ? rnd(n) : mi % n;
                {
                    if (v == old) continue;
                    ex[f] = v; int c = evalc(NULL); evals++;
                    int istabu = tabu[f * n + v] > step;
                    if (istabu && c >= best) continue;
                    if (c < bc) { bc = c; bf = f; bv = v; nties = 1; }
                    else if (c == bc && rnd(++nties) == 0) { bf = f; bv = v; }
                }
                ex[f] = old;
            }
            if (bf < 0) break;
            tabu[bf * n + ex[bf]] = step + 5 + rnd(10);   /* forbid returning to the old value */
            ex[bf] = bv; cur = bc;
            if (cur < best) { best = cur; stall = 0; } else stall++;
        }
        if (best < best_all) best_all = best;
        if (cur == 0) {
            int dm; int c = evalc(&dm);
            found = 1;
            printf("FOUND cost=%d diameter=%d N=%d base:", c, dm, N);
            for (int i = 0; i < ne; i++) printf(" (%d,%d,%d)", eu[i], ew[i], ex[i]);
            printf("\n");
            write_out(out);
        }
    }
    printf("M=%d K=%d R=%d n=%d B=%d N=%d D=%d restarts=%d evals=%ld best_cost=%d time=%.1f found=%d\n",
           M, K, R, n, B, N, D, restarts, evals, best_all, now() - t0, found);
    return 0;
}
