/* Anneal an R x C 0/1 matrix for the (16,3) bipartite search.
   Cost = #same-side pairs with no common 1 (rows and cols) . Row/col sums capped at D.
   Moves: degree-preserving 2-switch (most), add a 1 with spare degree, remove a 1.
   Usage: d16_sa start.txt D iters T0 T1 seed out.txt
   start.txt: "R C" then "r c" lines (start may be padded with empty rows/cols).
   Writes out.txt as "R C" + edges when cost reaches 0 (then exits 0), else prints best cost. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAXN 256
int R, C, D;
unsigned char M[MAXN][MAXN];
int OR[MAXN][MAXN], OC[MAXN][MAXN];   /* overlaps of row pairs / col pairs */
int rdeg[MAXN], cdeg[MAXN];
long zero;                             /* zero-overlap pairs, rows + cols */
static unsigned long long rs;
static inline unsigned long long rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double ur(void){ return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* toggle cell (i,j); keeps OR, OC, zero, degrees exact */
static void flip(int i, int j){
    int k, l, d = M[i][j] ? -1 : 1;
    for(k = 0; k < R; k++) if(k != i && M[k][j]){
        int o = OR[i][k];
        OR[i][k] = OR[k][i] = o + d;
        if(d > 0 && o == 0) zero--;
        if(d < 0 && o == 1) zero++;
    }
    for(l = 0; l < C; l++) if(l != j && M[i][l]){
        int o = OC[j][l];
        OC[j][l] = OC[l][j] = o + d;
        if(d > 0 && o == 0) zero--;
        if(d < 0 && o == 1) zero++;
    }
    M[i][j] ^= 1;
    rdeg[i] += d; cdeg[j] += d;
}

static void load(const char *path){
    FILE *f = fopen(path, "r"); int a, b;
    if(!f){ perror(path); exit(1); }
    if(fscanf(f, "%d %d", &R, &C) != 2) exit(2);
    while(fscanf(f, "%d %d", &a, &b) == 2){ M[a][b] = 1; rdeg[a]++; cdeg[b]++; }
    fclose(f);
}

static void init_overlaps(void){
    int i, j, k; zero = 0;
    for(i = 0; i < R; i++) for(k = 0; k < R; k++) if(i != k){
        int o = 0; for(j = 0; j < C; j++) o += M[i][j] & M[k][j];
        OR[i][k] = o; if(i < k && o == 0) zero++;
    }
    for(j = 0; j < C; j++) for(k = 0; k < C; k++) if(j != k){
        int o = 0; for(i = 0; i < R; i++) o += M[i][j] & M[i][k];
        OC[j][k] = o; if(j < k && o == 0) zero++;
    }
}

static void write_out(const char *path){
    FILE *f = fopen(path, "w"); int i, j;
    fprintf(f, "%d %d\n", R, C);
    for(i = 0; i < R; i++) for(j = 0; j < C; j++) if(M[i][j]) fprintf(f, "%d %d\n", i, j);
    fclose(f);
}

int main(int argc, char **argv){
    if(argc < 8){ fprintf(stderr, "usage: d16_sa start.txt D iters T0 T1 seed out.txt\n"); return 1; }
    long iters = atol(argv[3]); double T0 = atof(argv[4]), T1 = atof(argv[5]);
    rs = strtoull(argv[6], 0, 10) * 2654435761ULL + 88172645463325252ULL;
    D = atoi(argv[2]);
    load(argv[1]);
    init_overlaps();
    long best = zero, it; int i, j, k, l;
    fprintf(stderr, "R=%d C=%d D=%d start cost=%ld\n", R, C, D, zero);
    for(it = 0; it < iters && zero > 0; it++){
        double T = T0 * pow(T1 / T0, (double)it / iters);
        long before = zero; int mv = (int)(rnd() % 100);
        int moved[4][2], nm = 0;
        if(mv < 85){
            /* 2-switch: (i,j),(k,l) ones -> (i,l),(k,j) */
            do { i = rnd() % R; j = rnd() % C; } while(!M[i][j]);
            do { k = rnd() % R; l = rnd() % C; } while(!M[k][l]);
            if(i == k || j == l || M[i][l] || M[k][j]) continue;
            flip(i, j); flip(k, l); flip(i, l); flip(k, j);
            moved[0][0]=i; moved[0][1]=j; moved[1][0]=k; moved[1][1]=l; moved[2][0]=i; moved[2][1]=l; moved[3][0]=k; moved[3][1]=j; nm = 4;
        } else if(mv < 93){
            /* add a 1 where both sides have spare degree */
            i = rnd() % R; j = rnd() % C;
            if(M[i][j] || rdeg[i] >= D || cdeg[j] >= D) continue;
            flip(i, j); moved[0][0]=i; moved[0][1]=j; nm = 1;
        } else {
            /* remove a 1 */
            do { i = rnd() % R; j = rnd() % C; } while(!M[i][j]);
            flip(i, j); moved[0][0]=i; moved[0][1]=j; nm = 1;
        }
        long delta = zero - before;
        if(delta <= 0 || ur() < exp(-delta / T)){
            if(zero < best){ best = zero; fprintf(stderr, "it=%ld T=%.4f best=%ld\n", it, T, best); }
        } else {
            for(k = nm - 1; k >= 0; k--) flip(moved[k][0], moved[k][1]);
        }
        if(it % 20000000 == 0 && it) fprintf(stderr, "it=%ld T=%.4f cost=%ld best=%ld\n", it, T, zero, best);
    }
    if(zero == 0){
        int ok = 1;
        for(i = 0; i < R; i++) if(rdeg[i] > D || rdeg[i] == 0) ok = 0;
        for(j = 0; j < C; j++) if(cdeg[j] > D || cdeg[j] == 0) ok = 0;
        fprintf(stderr, "COST 0 at it=%ld, degree check %s\n", it, ok ? "ok" : "FAILED");
        if(ok){ write_out(argv[7]); printf("FOUND R=%d C=%d n=%d\n", R, C, R + C); return 0; }
    }
    printf("NOT FOUND best=%ld final=%ld\n", best, zero);
    return 3;
}
