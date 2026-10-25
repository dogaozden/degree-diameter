/* clhaar.c: cluster-assisted Haar hub graphs for the (12,7) construction (5-level cover of H(9), freed spread lines).
   Hubs: line-side (g,A) and point-side (g,B), g in Gamma = G1 x Z_n. Hub graph = Haar graph (g,A) ~ (s g, B), s in S,
   |S| = d, s_0 = e. At level i the right cosets of a subgroup H_i (order h <= 20) are the line-side clusters: one coset
   sits on the 10 points of one spread line (2 hubs per point; the pairs are the right cosets of {e, c_i}), so two hubs
   of a cluster are within 4 (2 if they share a point) through the main graph. Point side: subgroups K_i, involutions
   c'_i, clusters on the 10 lines through one ovoid point. Every move is a left multiplication, so hub distances are
   right-invariant: d((g,A),(h,A)) = dA(h g^-1), where dA is the distance from (e,A) in the weighted graph with moves
   (y,A)->(s y,B) and (y,B)->(s^-1 y,A) of weight 1, (y,A)->(a y,A), a in H_i, of weight 4 (2 if a = c_i), and
   (y,B)->(k y,B), k in K_i, of weight 4 (2 if k = c'_i). Cost = #{x : dA(x) > 6} + #{x : dB(x) > 6}.
   (Hubs on opposite sides are always within 7 through the main graph; hub-main and main-main pairs do not use hubs.)
   Usage: clhaar GROUPFILE d L seconds seed OUT [restrictA restrictB]
     L = number of levels with clusters (5); the program anneals over S and over the choice of H_i, K_i among the
     candidate subgroups. Writes OUT when the cost reaches 0: "N n d L", the d generators, then for each level the
     A-side subgroup id and the B-side subgroup id (ids into GROUPFILE's list). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
static int N1, nz, hsz, nsub, N; static int *T1, *inv1;
static int *subc, *sube;   /* subgroup involution and elements */
static inline int mul(int x, int y) { int a = x / nz, z = x % nz, b = y / nz, w = y % nz; return T1[a * N1 + b] * nz + (z + w) % nz; }
static inline int inv(int x) { int a = x / nz, z = x % nz; return inv1[a] * nz + (nz - z) % nz; }
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int d, L; static int S[64], SI[64], HA[8], HB[8];
static int *ltS, *ltSI;  /* left mult tables: ltS[j*N + y] = S[j] y */
static unsigned char *dist; static int *bk[7], bn[7];
static void build_tables(void) {
    for (int j = 0; j < d; j++) { SI[j] = inv(S[j]); for (int y = 0; y < N; y++) { ltS[(long)j * N + y] = mul(S[j], y); ltSI[(long)j * N + y] = mul(SI[j], y); } }
}
static void build_one(int j) { SI[j] = inv(S[j]); for (int y = 0; y < N; y++) { ltS[(long)j * N + y] = mul(S[j], y); ltSI[(long)j * N + y] = mul(SI[j], y); } }
/* side 0 = A, 1 = B; node id = side*N + y */
static int run(int side0, int *missA_out) {
    memset(dist, 255, 2 * N); for (int k = 0; k < 7; k++) bn[k] = 0;
    int s0 = side0 * N; dist[s0] = 0; bk[0][bn[0]++] = s0;
    for (int dd = 0; dd <= 6; dd++) {
        for (int t = 0; t < bn[dd]; t++) {
            int v = bk[dd][t]; if (dist[v] != dd) continue;
            int side = v >= N, y = v - side * N;
            if (dd + 1 <= 6) for (int j = 0; j < d; j++) {
                int w = side ? ltSI[(long)j * N + y] : N + ltS[(long)j * N + y];
                if (dist[w] > dd + 1) { dist[w] = dd + 1; bk[dd + 1][bn[dd + 1]++] = w; }
            }
            if (dd + 2 <= 6) for (int i = 0; i < L; i++) {
                int sg = side ? HB[i] : HA[i]; int c = subc[sg];
                if (dd + 4 <= 6) { for (int k = 0; k < hsz; k++) { int a = sube[sg * hsz + k]; int w = side * N + mul(a, y); int nd = dd + (a == c ? 2 : 4);
                        if (dist[w] > nd) { dist[w] = nd; bk[nd][bn[nd]++] = w; } } }
                else { int w = side * N + mul(c, y); if (dist[w] > dd + 2) { dist[w] = dd + 2; bk[dd + 2][bn[dd + 2]++] = w; } }
            }
        }
    }
    int miss = 0; for (int y = 0; y < N; y++) if (dist[side0 * N + y] > 6) miss++;
    return miss;
}
static int cost(int *ma, int *mb) { *ma = run(0, NULL); *mb = run(1, NULL); return *ma + *mb; }
int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: clhaar GROUPFILE d L seconds seed OUT\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); d = atoi(argv[2]); L = atoi(argv[3]); double secs = atof(argv[4]); rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    if (fscanf(f, "%d %d %d %d", &N1, &nz, &hsz, &nsub) != 4) return 1; N = N1 * nz;
    T1 = malloc(sizeof(int) * N1 * N1); for (long i = 0; i < (long)N1 * N1; i++) if (fscanf(f, "%d", &T1[i]) != 1) return 1;
    int eid = -1; for (int a = 0; a < N1 && eid < 0; a++) { int ok = 1; for (int b = 0; b < N1; b++) if (T1[a * N1 + b] != b) { ok = 0; break; } if (ok) eid = a; }
    inv1 = malloc(sizeof(int) * N1); for (int a = 0; a < N1; a++) for (int b = 0; b < N1; b++) if (T1[a * N1 + b] == eid) { inv1[a] = b; break; }
    subc = malloc(sizeof(int) * nsub); sube = malloc(sizeof(int) * nsub * hsz);
    for (int s = 0; s < nsub; s++) { if (fscanf(f, "%d", &subc[s]) != 1) return 1; for (int k = 0; k < hsz; k++) if (fscanf(f, "%d", &sube[s * hsz + k]) != 1) return 1; }
    fclose(f);
    fprintf(stderr, "N1=%d n=%d N=%d h=%d subgroups=%d identity=%d\n", N1, nz, N, hsz, nsub, eid * nz);
    ltS = malloc(sizeof(int) * (long)d * N); ltSI = malloc(sizeof(int) * (long)d * N); dist = malloc(2 * N);
    for (int k = 0; k < 7; k++) bk[k] = malloc(sizeof(int) * 2 * N * 4);
    S[0] = eid * nz; for (int j = 1; j < d; j++) S[j] = rnd() % N;
    for (int i = 0; i < L; i++) { HA[i] = rnd() % nsub; HB[i] = rnd() % nsub; }
    build_tables();
    int ma, mb, c = cost(&ma, &mb), best = c; double Tm = 2.0; time_t t0 = time(NULL); long evals = 0;
    fprintf(stderr, "start cost=%d (A %d, B %d)\n", c, ma, mb);
    while (c > 0 && difftime(time(NULL), t0) < secs) {
        int kind = rnd() % 10; int j = 0, old = 0, oi = 0, side = 0;
        if (kind < 8) { j = 1 + rnd() % (d - 1); old = S[j]; S[j] = rnd() % N; build_one(j); }
        else { side = rnd() & 1; oi = rnd() % L; old = side ? HB[oi] : HA[oi]; if (side) HB[oi] = rnd() % nsub; else HA[oi] = rnd() % nsub; }
        int na, nb, nc = cost(&na, &nb); evals++;
        if (nc <= c || exp((c - nc) / Tm) > (rnd() % 1000000) / 1e6) { c = nc; ma = na; mb = nb; if (c < best) { best = c; fprintf(stderr, "t=%.0f evals=%ld cost=%d (A %d, B %d) T=%.3f\n", difftime(time(NULL), t0), evals, c, ma, mb, Tm); } }
        else { if (kind < 8) { S[j] = old; build_one(j); } else { if (side) HB[oi] = old; else HA[oi] = old; } }
        Tm *= 0.99995; if (Tm < 0.3) Tm = 2.0;
    }
    printf("RESULT N=%d best=%d final=%d evals=%ld time=%.0f\n", N, best, c, evals, difftime(time(NULL), t0));
    if (c == 0) {
        FILE *o = fopen(argv[6], "w"); fprintf(o, "%d %d %d %d\n", N, nz, d, L);
        for (int j = 0; j < d; j++) fprintf(o, "%d ", S[j]); fprintf(o, "\n");
        for (int i = 0; i < L; i++) fprintf(o, "%d %d\n", HA[i], HB[i]); fclose(o); printf("wrote %s\n", argv[6]);
    }
    return 0;
}
