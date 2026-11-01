/* Exhaustive (4,9) Haar search on Z_P x|_R Z_K (elements (a,j) -> id a*K+j, (a1,j1)(a2,j2) = (a1+R^j1 a2, j1+j2)).
   usage: hsearch PAIRS START END TLIMIT_SECS OUTFILE
          hsearch one a b c            -> prints cost of S={e,a,b,c}
   For each pair line (a,b) (lines START..END-1 of PAIRS, 0-based) every c not in {e,a,b} is tried; S={e,a,b,c}.
   cost = #vertices at distance > 9 from (e,A) + same from (e,B) (Haar graph on 2N vertices, degree 4). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#define P 101
#define K 25
#define R 5
#define N (P*K)
#define D 9
static uint16_t *mul;   /* mul[s*N+g] = s*g */
static uint16_t inv_[N];
static uint32_t stamp[2*N];
static uint32_t cur = 0;
static uint32_t q[2*N], q2[2*N];
static int rp[K];

static int THR = 1 << 30;  /* if cost from (e,A) exceeds THR, return it (lower bound, total > THR) */
static uint64_t vis[(2*N+63)/64];
static uint16_t qa[2*N], qb[2*N];
static inline int tst(uint32_t w){ return (vis[w>>6] >> (w&63)) & 1; }
static inline void setb(uint32_t w){ vis[w>>6] |= 1ULL << (w&63); }
static int cost_of(const int *S) {   /* S[0..3], S[0]=e */
    int total = 0;
    uint16_t sp[4], ip[4];
    for (int t = 0; t < 4; t++) { sp[t] = S[t]; ip[t] = inv_[S[t]]; }
    for (int src = 0; src < 2; src++) {
        if (src == 1 && total > THR) return total;
        memset(vis, 0, sizeof(vis));
        int start = src == 0 ? 0 : N;
        uint16_t *fr = qa, *nx = qb;
        int nf = 0, nn;
        fr[nf++] = start; setb(start);
        int count = 1;
        for (int d = 1; d <= D; d++) {
            nn = 0;
            for (int i = 0; i < nf; i++) {
                uint32_t v = fr[i];
                if (v < N) {
                    const uint16_t *r0 = mul + (size_t)sp[0]*N, *r1 = mul + (size_t)sp[1]*N,
                                   *r2 = mul + (size_t)sp[2]*N, *r3 = mul + (size_t)sp[3]*N;
                    uint32_t ws[4] = { N + r0[v], N + r1[v], N + r2[v], N + r3[v] };
                    for (int t = 0; t < 4; t++) if (!tst(ws[t])) { setb(ws[t]); nx[nn++] = (uint16_t)ws[t]; }
                } else {
                    uint32_t x = v - N;
                    const uint16_t *r0 = mul + (size_t)ip[0]*N, *r1 = mul + (size_t)ip[1]*N,
                                   *r2 = mul + (size_t)ip[2]*N, *r3 = mul + (size_t)ip[3]*N;
                    uint32_t ws[4] = { r0[x], r1[x], r2[x], r3[x] };
                    for (int t = 0; t < 4; t++) if (!tst(ws[t])) { setb(ws[t]); nx[nn++] = (uint16_t)ws[t]; }
                }
            }
            count += nn;
            uint16_t *tmp = fr; fr = nx; nx = tmp; nf = nn;
        }
        total += 2*N - count;
    }
    return total;
}

static void build(void) {
    for (int j = 0; j < K; j++) { rp[j] = 1; for (int i = 0; i < j; i++) rp[j] = rp[j] * R % P; }
    mul = malloc((size_t)N*N*sizeof(uint16_t));
    for (int g = 0; g < N; g++) {
        int a1 = g / K, j1 = g % K;
        for (int h = 0; h < N; h++) {
            int a2 = h / K, j2 = h % K;
            mul[(size_t)g*N + h] = (uint16_t)(((a1 + rp[j1]*a2) % P) * K + (j1 + j2) % K);
        }
    }
    for (int g = 0; g < N; g++) for (int h = 0; h < N; h++) if (mul[(size_t)g*N+h] == 0) { inv_[g] = h; break; }
}

int main(int argc, char **argv) {
    build();
    if (getenv("THR")) THR = atoi(getenv("THR"));
    if (argc == 5 && strcmp(argv[1], "one") == 0) {
        int S[4] = {0, atoi(argv[2]), atoi(argv[3]), atoi(argv[4])};
        printf("cost %d\n", cost_of(S));
        return 0;
    }
    if (argc < 6) { fprintf(stderr, "usage\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); int np; if (fscanf(f, "%d", &np) != 1) return 1;
    int start = atoi(argv[2]), end = atoi(argv[3]); double tl = atof(argv[4]);
    FILE *out = fopen(argv[5], "a");
    int *A = malloc(np*sizeof(int)), *B = malloc(np*sizeof(int));
    for (int i = 0; i < np; i++) if (fscanf(f, "%d %d", &A[i], &B[i]) != 2) return 1;
    fclose(f);
    clock_t t0 = clock();
    int gbest = 1 << 30; long evals = 0; int last = start;
    for (int i = start; i < end && i < np; i++) {
        int a = A[i], b = B[i];
        int best = 1 << 30, bc = -1; int hist[64] = {0};
        for (int c = 1; c < N; c++) {
            if (c == a || c == b) continue;
            int S[4] = {0, a, b, c};
            int cs = cost_of(S); evals++;
            if (cs < best) { best = cs; bc = c; }
            hist[cs < 63 ? cs : 63]++;
            if (cs == 0) fprintf(out, "ZERO a=%d b=%d c=%d\n", a, b, c);
        }
        if (best < gbest) gbest = best;
        fprintf(out, "pair %d a=(%d,%d) b=(%d,%d) minc=%d at c=(%d,%d) count_le10=%d\n", i,
                a/K, a%K, b/K, b%K, best, bc/K, bc%K,
                hist[0]+hist[1]+hist[2]+hist[3]+hist[4]+hist[5]+hist[6]+hist[7]+hist[8]+hist[9]+hist[10]);
        fflush(out);
        last = i + 1;
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > tl) break;
    }
    fprintf(out, "done range %d..%d next=%d evals=%ld gbest=%d time=%.1fs\n", start, end, last, evals, gbest,
            (double)(clock()-t0)/CLOCKS_PER_SEC);
    fclose(out);
    printf("next %d evals %ld gbest %d\n", last, evals, gbest);
    return 0;
}
