/* hexlift.h: Z_m-lifts of the split Cayley hexagon H(q) plus t extra point-line matchings.
   Base vertices: points 0..N-1, lines N..2N-1 (hexgen.c numbering, line j has id N+j).
   Lift: vertex (x,i), i in Z_m.  Hexagon flag (p,l): (p,i) ~ (l, i + sig) where sig = sigma of the flag.
   Extra edge k of point p: (p,i) ~ (M[k][p], i + v[k][p]).
   Packed BFS: reach[x] is an m-bit mask (m <= 64) of the levels of x reached so far. */
#ifndef HEXLIFT_H
#define HEXLIFT_H
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t u64;

typedef struct {
    int q, N, V;          /* V = 2N */
    int *lp;              /* line -> q+1 points (L*(q+1)) */
    int *pl;              /* point -> q+1 lines (line index 0..N-1) */
    int *pl_slot;         /* slot of point p in line pl[p][j]'s point list */
} Hex;

static Hex *hex_load(const char *fn) {
    FILE *f = fopen(fn, "rb");
    if (!f) { fprintf(stderr, "cannot open %s\n", fn); exit(1); }
    int32_t hdr[3];
    if (fread(hdr, 4, 3, f) != 3) { fprintf(stderr, "bad header\n"); exit(1); }
    Hex *h = calloc(1, sizeof(Hex));
    h->q = hdr[0]; h->N = hdr[1]; h->V = 2 * h->N;
    int q1 = h->q + 1, N = h->N;
    if (hdr[2] != N) { fprintf(stderr, "L != N\n"); exit(1); }
    h->lp = malloc(sizeof(int) * (size_t)N * q1);
    int32_t *tmp = malloc(4 * (size_t)N * q1);
    if (fread(tmp, 4, (size_t)N * q1, f) != (size_t)N * q1) { fprintf(stderr, "short file\n"); exit(1); }
    for (size_t i = 0; i < (size_t)N * q1; i++) h->lp[i] = tmp[i];
    free(tmp); fclose(f);
    h->pl = malloc(sizeof(int) * (size_t)N * q1);
    h->pl_slot = malloc(sizeof(int) * (size_t)N * q1);
    int *cnt = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int j = 0; j < q1; j++) {
        int p = h->lp[(size_t)l * q1 + j];
        if (cnt[p] >= q1) { fprintf(stderr, "point degree > q+1\n"); exit(1); }
        h->pl[(size_t)p * q1 + cnt[p]] = l;
        h->pl_slot[(size_t)p * q1 + cnt[p]] = j;
        cnt[p]++;
    }
    for (int p = 0; p < N; p++) if (cnt[p] != q1) { fprintf(stderr, "point degree != q+1\n"); exit(1); }
    free(cnt);
    return h;
}

/* adjacency of the base multigraph with level shifts: for base vertex x, deg entries (nbr, shift) where
   moving x -> nbr adds shift to the level (mod m). */
typedef struct {
    int V, deg, m;
    int *nb;      /* V*deg */
    int *sh;      /* V*deg, in 0..m-1 */
} Adj;

/* rotate an m-bit mask by c (0<=c<m): bit i -> bit (i+c) mod m */
static inline u64 rotm(u64 x, int c, int m, u64 full) {
    if (c == 0) return x;
    return ((x << c) | (x >> (m - c))) & full;
}

/* BFS from (src,0) for D steps; returns number of (vertex,level) pairs NOT reached within the distance
   bound (D for same side as src, D-1 for the other side).  reach/front/nxt: scratch arrays of V u64. */
static long bfs_uncovered(const Adj *A, int src, int D, u64 *reach, u64 *front, u64 *nxt, int srcside_is_point) {
    int V = A->V, deg = A->deg, m = A->m;
    u64 full = (m == 64) ? ~0ULL : ((1ULL << m) - 1);
    memset(reach, 0, sizeof(u64) * V);
    memset(front, 0, sizeof(u64) * V);
    reach[src] = 1; front[src] = 1;
    for (int d = 1; d <= D; d++) {
        /* pull: nxt[x] = OR_y rot(front[y], shift(y->x)) ; shift(y->x) = -shift(x->y) */
        for (int x = 0; x < V; x++) {
            u64 acc = 0;
            const int *nb = A->nb + (size_t)x * deg, *sh = A->sh + (size_t)x * deg;
            for (int j = 0; j < deg; j++) {
                u64 f = front[nb[j]];
                if (f) { int c = sh[j] ? m - sh[j] : 0; acc |= rotm(f, c, m, full); }
            }
            nxt[x] = acc & ~reach[x];
        }
        for (int x = 0; x < V; x++) { reach[x] |= nxt[x]; }
        u64 *t = front; front = nxt; nxt = t;
    }
    (void)srcside_is_point;
    long miss = 0;
    for (int x = 0; x < V; x++) miss += m - __builtin_popcountll(reach[x]);
    return miss;
}
#endif
