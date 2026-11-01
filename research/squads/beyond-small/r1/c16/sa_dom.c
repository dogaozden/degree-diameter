/* SA for k-set S of B-side vertices dominating all A-side vertices within distance R (R=3).
   usage: sa_dom edges k iters seed R
   On success (uncovered=0) writes S to sol_k<k>_s<seed>.txt (vertex ids of the 33,792 graph). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
static uint64_t rs;
static inline uint64_t rnd(void){ rs ^= rs<<13; rs ^= rs>>7; rs ^= rs<<17; return rs; }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int k = atoi(argv[2]); long iters = atol(argv[3]); rs = 88172645463325252ULL ^ (uint64_t)atol(argv[4]) * 2654435761ULL; int R = argc > 5 ? atoi(argv[5]) : 3;
    int n; if (fscanf(f, "%d", &n) != 1) return 1;
    int cap = 1 << 22; int *eu = malloc(sizeof(int)*cap), *ev = malloc(sizeof(int)*cap); long m = 0; int a, b;
    while (fscanf(f, "%d %d", &a, &b) == 2) { if (m >= cap) { cap*=2; eu=realloc(eu,sizeof(int)*cap); ev=realloc(ev,sizeof(int)*cap);} eu[m]=a; ev[m]=b; m++; }
    fclose(f);
    int *deg = calloc(n,sizeof(int)); for (long i=0;i<m;i++){deg[eu[i]]++;deg[ev[i]]++;}
    long *off = calloc(n+1,sizeof(long)); for (int v=0;v<n;v++) off[v+1]=off[v]+deg[v];
    int *adj = malloc(sizeof(int)*off[n]); long *pos = malloc(sizeof(long)*n); for (int v=0;v<n;v++) pos[v]=off[v];
    for (long i=0;i<m;i++){ adj[pos[eu[i]]++]=ev[i]; adj[pos[ev[i]]++]=eu[i]; }
    int *col = malloc(sizeof(int)*n); for (int v=0;v<n;v++) col[v]=-1;
    int *q = malloc(sizeof(int)*n); int qh=0,qt=0; col[0]=0; q[qt++]=0;
    while (qh<qt){ int x=q[qh++]; for (long j=off[x];j<off[x+1];j++){int y=adj[j]; if(col[y]<0){col[y]=1-col[x]; q[qt++]=y;}} }
    if (argc > 6 && argv[6][0]=='1') for (int v=0;v<n;v++) if (col[v]>=0) col[v]=1-col[v];
    int nA=0,nB=0; int *idxA=malloc(sizeof(int)*n), *idxB=malloc(sizeof(int)*n), *listA=malloc(sizeof(int)*n), *listB=malloc(sizeof(int)*n);
    for (int v=0;v<n;v++){ if(col[v]==0){idxA[v]=nA; listA[nA++]=v;} else {idxB[v]=nB; listB[nB++]=v;} }
    /* ball lists: for centre u in B, list of A-indices within R */
    long *boff = malloc(sizeof(long)*(nB+1)); uint16_t *bl = NULL; long btot = 0;
    /* two passes: count then fill, using per-block bit-parallel BFS */
    int W = 0;
    uint64_t *Rr = malloc(sizeof(uint64_t)*n), *Nn = malloc(sizeof(uint64_t)*n);
    /* first pass: count sizes */
    int *sz = calloc(nB, sizeof(int));
    for (int pass = 0; pass < 2; pass++) {
        if (pass == 1) { for (int u=0;u<nB;u++) boff[u+1]=boff[u]+sz[u]; btot=boff[nB]; bl = malloc(sizeof(uint16_t)*btot); }
        for (int base=0; base<nB; base+=64) {
            int cnt = (nB-base<64)?(nB-base):64;
            for (int v=0;v<n;v++) Rr[v]=0;
            for (int i=0;i<cnt;i++) Rr[listB[base+i]] |= 1ULL<<i;
            for (int kk=0;kk<R;kk++){ for (int v=0;v<n;v++){ uint64_t x=Rr[v]; for (long j=off[v];j<off[v+1];j++) x|=Rr[adj[j]]; Nn[v]=x; } uint64_t *t=Rr; Rr=Nn; Nn=t; }
            for (int v=0;v<n;v++) if (col[v]==0) {
                uint64_t x = Rr[v];
                while (x) { int i = __builtin_ctzll(x); x &= x-1; int u = base+i;
                    if (pass==0) sz[u]++; else bl[boff[u] + 0 + 0] = 0, bl[ boff[u] + (--sz[u]) ] = (uint16_t)idxA[v]; }
            }
        }
    }
    /* sz now zero after decrement pass: recompute fill counts */
    for (int u=0;u<nB;u++) sz[u] = (int)(boff[u+1]-boff[u]);
    /* the fill pass decremented sz; restore sizes is done above (sizes from boff) */
    /* state */
    char *in = calloc(nB,1);
    if (argc > 7) { FILE *ff = fopen(argv[7], "r"); int vv; while (ff && fscanf(ff, "%d", &vv) == 1) { if (col[vv]==1-(argc>6&&argv[6][0]=='1')) { } ; for (int z=0; z<nB; z++) if (listB[z]==vv) in[z]=1; } if (ff) fclose(ff); }
    int *S = malloc(sizeof(int)*k);
    for (int i=0;i<k;i++){ int u; do { u = rnd()%nB; } while(in[u]); in[u]=1; S[i]=u; }
    int *cov = calloc(nA,sizeof(int)); int uncov = nA;
    for (int i=0;i<k;i++) for (long j=boff[S[i]]; j<boff[S[i]+1]; j++){ if (cov[bl[j]]++==0) uncov--; }
    int best = uncov; double T0 = 2.0, T1 = 0.05;
    for (long it=0; it<iters && uncov>0; it++) {
        double T = T0 * pow(T1/T0, (double)it/iters);
        int i = rnd()%k; int u = S[i]; int w; do { w = rnd()%nB; } while (in[w]);
        int before = uncov;
        for (long j=boff[u]; j<boff[u+1]; j++){ if (--cov[bl[j]]==0) uncov++; }
        for (long j=boff[w]; j<boff[w+1]; j++){ if (cov[bl[j]]++==0) uncov--; }
        int delta = uncov - before;
        if (delta <= 0 || (double)(rnd()%1000000)/1e6 < exp(-delta/T)) { in[u]=0; in[w]=1; S[i]=w; if (uncov<best) best=uncov; }
        else { /* revert */
            for (long j=boff[w]; j<boff[w+1]; j++){ if (--cov[bl[j]]==0) uncov++; }
            for (long j=boff[u]; j<boff[u+1]; j++){ if (cov[bl[j]]++==0) uncov--; }
        }
    }
    printf("k=%d R=%d seed=%s final_uncovered=%d best=%d\n", k, R, argv[4], uncov, best);
    if (uncov == 0) {
        char fn[256]; sprintf(fn, "sol_k%d_R%d_s%s.txt", k, R, argv[4]); FILE *o = fopen(fn, "w");
        for (int i=0;i<k;i++) fprintf(o, "%d\n", listB[S[i]]); fclose(o); printf("wrote %s\n", fn);
    }
    return 0;
}
