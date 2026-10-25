/* Direct check of Lemma 4.1 (D7_HEXAGON.md): for a segment set F of points of H(q),
   for all elements u, v: min over points p not in F of d(u,p) + d(p,v) <= 6.
   Hexagon from research/d10D7/hexgen2.c (hex_q{q}.bin). Families of F: spread points (greedy partial spread),
   random maximal segment sets, (R1) sets (each point at most one partner), and a negative control.
   Dual sets: the same check on H^D (swap the roles of points and lines).
   usage: lem41 HEXBIN seed */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int q, N, Q1, V; static int *LP, *PL; /* LP[l*Q1+k] point k of line l; PL[p*Q1+k] line k of point p */
static int *adj; /* adj[v*Q1+k], vertices: points 0..N-1, lines N..2N-1 */
static uint8_t *D; /* all-pairs distances V x V */
static uint64_t rs = 88172645463325252ULL; static uint64_t rnd(void){ rs ^= rs<<13; rs ^= rs>>7; rs ^= rs<<17; return rs; }
static int dual = 0; /* if 1, "points" are the lines (H^D) */
static int pt(int i){ return dual ? N + i : i; }          /* vertex id of "point" i */
static int nb(int v, int k){ return adj[v*Q1+k]; }
static void apsp(void){
    D = malloc((size_t)V*V); int *qq = malloc(sizeof(int)*V);
    for (int s = 0; s < V; s++){ uint8_t *d = D + (size_t)s*V; memset(d, 255, V); d[s]=0; int h=0,t=0; qq[t++]=s;
        while(h<t){ int x=qq[h++]; for(int k=0;k<Q1;k++){ int y=nb(x,k); if(d[y]==255){ d[y]=d[x]+1; qq[t++]=y; } } } }
    free(qq);
}
static int dd(int a, int b){ return D[(size_t)a*V+b]; }
/* segment property for the "point" set F (indexed 0..N-1 as "points") */
static int seg_ok_at(const char *F, int x){ /* x in F: F-neighbours of x on at most one "line" */
    int vx = pt(x), cnt = 0;
    for (int k = 0; k < Q1; k++){ int l = nb(vx,k); int has = 0;
        for (int m = 0; m < Q1; m++){ int y = nb(l,m); if (y != vx && F[dual ? y-N : y]) { has = 1; break; } }
        cnt += has; }
    return cnt <= 1;
}
static int can_add(char *F, int x){ if (F[x]) return 0; F[x] = 1; int ok = seg_ok_at(F,x); int vx = pt(x);
    for (int k = 0; ok && k < Q1; k++){ int l = nb(vx,k); for (int m = 0; ok && m < Q1; m++){ int y = nb(l,m); int yi = dual? y-N : y; if (y != vx && F[yi] && !seg_ok_at(F,yi)) ok = 0; } }
    F[x] = 0; return ok; }
static int partner_ok(char *F, int x){ /* (R1): x and all F-points collinear with it have <= 1 partner after adding */
    if (F[x]) return 0; F[x] = 1; int ok = 1; int vx = pt(x);
    int c = 0; for (int y = 0; y < N; y++) if (F[y] && y != x && dd(vx, pt(y)) == 2) c++; if (c > 1) ok = 0;
    for (int y = 0; ok && y < N; y++) if (F[y] && y != x && dd(vx, pt(y)) == 2){ int c2 = 0; for (int z = 0; z < N; z++) if (F[z] && z != y && dd(pt(y),pt(z)) == 2) c2++; if (c2 > 1) ok = 0; }
    F[x] = 0; return ok; }
/* check Lemma 4.1: for all u, v: exists p notin F with d(u,p)+d(p,v) <= 6. returns number of failing ordered pairs */
static long check(const char *F){
    long bad = 0; int *lab = malloc(sizeof(int)*V);
    for (int u = 0; u < V; u++){
        /* f(v) = min_p notin F d(u,p)+d(p,v): bucket BFS from all p notin F with initial label d(u,p) */
        int *bk[16]; int bn[16]; for (int b=0;b<16;b++){ bk[b]=malloc(sizeof(int)*V*2); bn[b]=0; }
        for (int v=0; v<V; v++) lab[v]=99;
        for (int i=0;i<N;i++) if(!F[i]){ int p=pt(i); int l=dd(u,p); if(l<lab[p]){ lab[p]=l; bk[l][bn[l]++]=p; } }
        for (int b=0;b<16;b++) for(int a=0;a<bn[b];a++){ int x=bk[b][a]; if(lab[x]!=b) continue; if(b+1<16) for(int k=0;k<Q1;k++){ int y=nb(x,k); if(lab[y]>b+1){ lab[y]=b+1; bk[b+1][bn[b+1]++]=y; } } }
        for (int v=0; v<V; v++) if (lab[v] > 6) bad++;
        for (int b=0;b<16;b++) free(bk[b]);
    }
    free(lab); return bad;
}
int main(int argc, char **argv){
    FILE *f = fopen(argv[1],"rb"); int32_t h[3]; if(fread(h,4,3,f)!=3) return 1; q=h[0]; N=h[1]; Q1=q+1; V=2*N;
    LP = malloc(sizeof(int)*N*Q1); if (fread(LP,4,(size_t)N*Q1,f) != (size_t)N*Q1) return 1; fclose(f);
    if (argc > 2) rs += atoi(argv[2])*7919ULL;
    PL = malloc(sizeof(int)*N*Q1); int *c = calloc(N,sizeof(int));
    for (int l=0;l<N;l++) for(int k=0;k<Q1;k++){ int p=LP[l*Q1+k]; PL[p*Q1+c[p]++]=l; }
    adj = malloc(sizeof(int)*V*Q1);
    for (int p=0;p<N;p++) for(int k=0;k<Q1;k++) adj[p*Q1+k]=N+PL[p*Q1+k];
    for (int l=0;l<N;l++) for(int k=0;k<Q1;k++) adj[(N+l)*Q1+k]=LP[l*Q1+k];
    apsp();
    int mx=0; for (size_t i=0;i<(size_t)V*V;i++) if (D[i]>mx) mx=D[i];
    printf("q=%d N=%d diameter=%d\n", q, N, mx);
    char *F = malloc(N);
    for (dual = 0; dual <= 1; dual++){
        const char *nm = dual ? "dual (line sets in H^D)" : "point sets";
        /* 1. spread points: greedy partial spread of "lines" (pairwise opposite), all their "points" */
        { memset(F,0,N); int *ord = malloc(sizeof(int)*N); for(int i=0;i<N;i++) ord[i]=i;
          for(int i=N-1;i>0;i--){ int j=rnd()%(i+1); int t=ord[i]; ord[i]=ord[j]; ord[j]=t; }
          int *S = malloc(sizeof(int)*N), ns=0;
          for (int a=0;a<N;a++){ int lv = dual ? ord[a] : N+ord[a]; /* a "line" vertex */ int ok=1; for(int b=0;b<ns&&ok;b++) if(dd(lv,S[b])<6) ok=0; if(ok) S[ns++]=lv; }
          int nf=0; for(int b=0;b<ns;b++) for(int k=0;k<Q1;k++){ int x=nb(S[b],k); int xi = dual? x-N : x; if(!F[xi]){F[xi]=1;nf++;} }
          int segok=1; for(int i=0;i<N;i++) if(F[i]&&!seg_ok_at(F,i)) segok=0;
          printf("[%s] spread points: %d lines (q^3+1=%d), |F|=%d, segment=%d, failing pairs=%ld\n", nm, ns, q*q*q+1, nf, segok, check(F));
          free(S); free(ord); }
        /* 2. random maximal segment sets */
        for (int rep=0; rep<3; rep++){ memset(F,0,N); int nf=0; int *ord=malloc(sizeof(int)*N); for(int i=0;i<N;i++) ord[i]=i;
          for(int i=N-1;i>0;i--){ int j=rnd()%(i+1); int t=ord[i]; ord[i]=ord[j]; ord[j]=t; }
          for(int a=0;a<N;a++) if(can_add(F,ord[a])){ F[ord[a]]=1; nf++; }
          int pairs=0; for(int i=0;i<N;i++) if(F[i]) for(int j=i+1;j<N;j++) if(F[j]&&dd(pt(i),pt(j))==2) pairs++;
          printf("[%s] random maximal segment set %d: |F|=%d, collinear pairs=%d, failing pairs=%ld\n", nm, rep, nf, pairs, check(F));
          /* negative control: add one point that breaks the segment property (a turning point) */
          int added=-1; for(int a=0;a<N&&added<0;a++){ int x=ord[a]; if(F[x]) continue; F[x]=1; int turn=0; for(int i=0;i<N&&!turn;i++) if(F[i]&&!seg_ok_at(F,i)) turn=1; if(turn) added=x; else F[x]=0; }
          if (added>=0) printf("[%s]   + one turning point: failing pairs=%ld (expected > 0)\n", nm, check(F));
          free(ord); }
        /* 3. (R1) sets: every point at most one partner, random maximal */
        { memset(F,0,N); int nf=0; int *ord=malloc(sizeof(int)*N); for(int i=0;i<N;i++) ord[i]=i;
          for(int i=N-1;i>0;i--){ int j=rnd()%(i+1); int t=ord[i]; ord[i]=ord[j]; ord[j]=t; }
          for(int a=0;a<N;a++) if(partner_ok(F,ord[a])){ F[ord[a]]=1; nf++; }
          int pairs=0; for(int i=0;i<N;i++) if(F[i]) for(int j=i+1;j<N;j++) if(F[j]&&dd(pt(i),pt(j))==2) pairs++;
          printf("[%s] random maximal (R1) set: |F|=%d, partner pairs=%d, failing pairs=%ld\n", nm, nf, pairs, check(F)); free(ord); }
    }
    return 0;
}
