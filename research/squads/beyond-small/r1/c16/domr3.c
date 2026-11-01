/* Greedy radius-3 domination of side A by balls of B-side vertices in a bipartite graph.
   usage: domr3 edges [R=3]. Prints greedy dominating-set size (number of B-centres needed to cover all A within dist R). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int R = argc > 2 ? atoi(argv[2]) : 3;
    int n; if (fscanf(f, "%d", &n) != 1) return 1;
    int cap = 1 << 22; int *eu = malloc(sizeof(int) * cap), *ev = malloc(sizeof(int) * cap); long m = 0; int a, b;
    while (fscanf(f, "%d %d", &a, &b) == 2) { if (m >= cap) { cap *= 2; eu = realloc(eu, sizeof(int)*cap); ev = realloc(ev, sizeof(int)*cap);} eu[m]=a; ev[m]=b; m++; }
    fclose(f);
    int *deg = calloc(n, sizeof(int)); for (long i = 0; i < m; i++) { deg[eu[i]]++; deg[ev[i]]++; }
    long *off = calloc(n+1, sizeof(long)); for (int v = 0; v < n; v++) off[v+1] = off[v] + deg[v];
    int *adj = malloc(sizeof(int)*off[n]); long *pos = malloc(sizeof(long)*n); for (int v=0;v<n;v++) pos[v]=off[v];
    for (long i = 0; i < m; i++) { adj[pos[eu[i]]++] = ev[i]; adj[pos[ev[i]]++] = eu[i]; }
    int *col = malloc(sizeof(int)*n); for (int v=0;v<n;v++) col[v]=-1;
    int *q = malloc(sizeof(int)*n); int qh=0, qt=0; col[0]=0; q[qt++]=0;
    while (qh < qt) { int x = q[qh++]; for (long j=off[x]; j<off[x+1]; j++) { int y=adj[j]; if (col[y]<0) { col[y]=1-col[x]; q[qt++]=y; } } }
    int nA=0,nB=0; int *idxA = malloc(sizeof(int)*n), *idxB = malloc(sizeof(int)*n);
    int *listA = malloc(sizeof(int)*n), *listB = malloc(sizeof(int)*n);
    for (int v=0; v<n; v++) { if (col[v]==0) { idxA[v]=nA; listA[nA++]=v; } else { idxB[v]=nB; listB[nB++]=v; } }
    int W = (nA + 63) / 64;
    uint64_t *M = calloc((size_t)nB * W, sizeof(uint64_t));   /* M[u] = bitset over A: A-vertices within R of centre u */
    uint64_t *Rr = malloc(sizeof(uint64_t)*n), *Nn = malloc(sizeof(uint64_t)*n);
    for (int base = 0; base < nB; base += 64) {
        int cnt = (nB - base < 64) ? (nB - base) : 64;
        for (int v=0; v<n; v++) Rr[v]=0;
        for (int i=0;i<cnt;i++) Rr[listB[base+i]] |= 1ULL<<i;
        for (int k=0;k<R;k++) {
            for (int v=0; v<n; v++) { uint64_t x = Rr[v]; for (long j=off[v]; j<off[v+1]; j++) x |= Rr[adj[j]]; Nn[v]=x; }
            uint64_t *t=Rr; Rr=Nn; Nn=t;
        }
        for (int v=0; v<n; v++) if (col[v]==0) {
            uint64_t x = Rr[v]; int wa = idxA[v] >> 6; uint64_t bit = 1ULL << (idxA[v] & 63);
            while (x) { int i = __builtin_ctzll(x); x &= x-1; M[(size_t)(base+i)*W + wa] |= bit; }
        }
    }
    /* greedy set cover of A */
    uint64_t *unc = malloc(sizeof(uint64_t)*W); for (int w=0; w<W; w++) unc[w]=~0ULL;
    if (nA % 64) unc[W-1] = (1ULL << (nA%64)) - 1;
    int used = 0; long remaining = nA;
    char *chosen = calloc(nB,1);
    while (remaining > 0) {
        int best=-1, bc=-1;
        for (int u=0; u<nB; u++) { if (chosen[u]) continue; int c=0; for (int w=0; w<W; w++) c += __builtin_popcountll(M[(size_t)u*W+w] & unc[w]); if (c>bc) {bc=c; best=u;} }
        if (bc <= 0) { printf("stuck, remaining %ld\n", remaining); break; }
        chosen[best]=1; used++;
        for (int w=0; w<W; w++) unc[w] &= ~M[(size_t)best*W+w];
        remaining -= bc;
    }
    printf("nA=%d nB=%d R=%d greedy_cover_size=%d (remaining %ld)\n", nA, nB, R, used, remaining);
    /* ball size stats */
    long tot=0; for (int u=0;u<nB;u++) for (int w=0;w<W;w++) tot+=__builtin_popcountll(M[(size_t)u*W+w]);
    printf("avg |B_R(u) cap A| = %.1f\n", (double)tot/nB);
    return 0;
}
