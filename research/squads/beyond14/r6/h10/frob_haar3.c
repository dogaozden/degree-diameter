// Exhaustive cubic Haar graphs H(G,{e,x,y}) over Frobenius groups G = Z_m x| Z_k (m prime, k | m-1).
// Element (u,j) index = u + m*j. (u1,j1)(u2,j2) = (u1 + r^{j1} u2, j1+j2), r of order k mod m.
// Graph: A-vertex g ~ B-vertex g*s, s in S. Cost = #(root,vertex) pairs at distance > D, roots A-e and B-e.
// Usage: frob_haar3 m k D [outprefix]   (x ranges over Aut-orbit reps (1,0) and (0,j); y over all of G)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int m, k, D, N;
static uint16_t *mt;      // mt[a*N+b] = a*b
static int *inv;
static int rpow[256], rinvpow[256];

static long pw(long b, long e, long md){ long r=1; b%=md; while(e){ if(e&1) r=r*b%md; b=b*b%md; e>>=1;} return r; }

static int mulg(int a, int b){
    int u1=a%m, j1=a/m, u2=b%m, j2=b/m;
    int u = (u1 + (long)rpow[j1]*u2) % m;
    int j = (j1+j2) % k;
    return u + m*j;
}

static uint8_t dist[8000];
static int queue_[8000];

// BFS from root (side 0 root = node root), returns number of nodes beyond D (incl. unreached)
static int bfs_cost(int root, int S0, int S1, int S2, int Si1, int Si2){
    // S = {S0,S1,S2} = {e,x,y}; inverses of S1,S2 are Si1, Si2 (S0 = e)
    int V = 2*N;
    memset(dist, 255, V);
    int qh=0, qt=0;
    dist[root]=0; queue_[qt++]=root;
    while(qh<qt){
        int v=queue_[qh++];
        int d=dist[v];
        if(d>=D) continue;
        if(v<N){ // A vertex g -> B vertices g*s
            int g=v;
            int a = N + mt[g*N+S0]; if(dist[a]==255){dist[a]=d+1; queue_[qt++]=a;}
            a = N + mt[g*N+S1]; if(dist[a]==255){dist[a]=d+1; queue_[qt++]=a;}
            a = N + mt[g*N+S2]; if(dist[a]==255){dist[a]=d+1; queue_[qt++]=a;}
        } else {  // B vertex h -> A vertices h*s^{-1}
            int h=v-N;
            int a = mt[h*N+S0]; if(dist[a]==255){dist[a]=d+1; queue_[qt++]=a;}
            a = mt[h*N+Si1]; if(dist[a]==255){dist[a]=d+1; queue_[qt++]=a;}
            a = mt[h*N+Si2]; if(dist[a]==255){dist[a]=d+1; queue_[qt++]=a;}
        }
    }
    int beyond = 0;
    for(int v=0; v<V; v++) if(dist[v]==255 || dist[v]>D) beyond++;
    return beyond;
}

int main(int argc, char **argv){
    if(argc<4){ fprintf(stderr,"usage: m k D [outprefix]\n"); return 1; }
    m=atoi(argv[1]); k=atoi(argv[2]); D=atoi(argv[3]);
    const char *outp = argc>4 ? argv[4] : "h10";
    int xlo = argc>5 ? atoi(argv[5]) : 0, xhi = argc>6 ? atoi(argv[6]) : -1;
    N=m*k; int V=2*N;
    if(V>8000){ fprintf(stderr,"too big\n"); return 1; }
    // primitive root
    int g=2;
    for(; g<m; g++){
        int ok=1;
        // factor m-1
        int n=m-1;
        for(int p=2;p<=n && ok;p++){
            if(n%p==0){ if(pw(g,(m-1)/p,m)==1) ok=0; while(n%p==0) n/=p; }
        }
        if(ok) break;
    }
    long r = pw(g, (m-1)/k, m);
    if(pw(r,k,m)!=1){ fprintf(stderr,"bad r\n"); return 1; }
    rpow[0]=1; for(int j=1;j<k;j++) rpow[j]=(int)(rpow[j-1]*r%m);
    long rinv = pw(r, m-2, m);
    rinvpow[0]=1; for(int j=1;j<k;j++) rinvpow[j]=(int)(rinvpow[j-1]*rinv%m);
    // check order of r is exactly k
    for(int j=1;j<k;j++) if(rpow[j]==1){ fprintf(stderr,"r order<k\n"); return 1; }
    mt = malloc(sizeof(uint16_t)*(size_t)N*N);
    inv = malloc(sizeof(int)*N);
    for(int a=0;a<N;a++) for(int b=0;b<N;b++) mt[(size_t)a*N+b]=(uint16_t)mulg(a,b);
    for(int a=0;a<N;a++){
        int u=a%m, j=a/m;
        int jj=(k-j)%k;
        int v = (int)((m - (long)rinvpow[j]*u % m) % m); // -r^{-j} u
        inv[a] = v + m*jj;
        if(mulg(a,inv[a])!=0){ fprintf(stderr,"inverse bug\n"); return 1; }
    }
    // identity index 0 = (0,0). check
    // x reps: (1,0) = 1, and (0,j) = m*j for j=1..k-1
    int nx = k; int xs[256];
    xs[0]=1; for(int j=1;j<k;j++) xs[j]=m*j;
    int best=1<<30; int bx=-1, by=-1; long n0=0; long evals=0;
    int bestcount=0;
    if(xhi<0 || xhi>nx) xhi=nx;
    for(int xi=xlo; xi<xhi; xi++){
        int x=xs[xi];
        for(int y=1; y<N; y++){
            if(y==x) continue;
            int cost = bfs_cost(0,0,x,y,inv[x],inv[y]) ;
            // second root: B-vertex e (node N)
            cost += bfs_cost(N,0,x,y,inv[x],inv[y]);
            evals++;
            if(cost<best){ best=cost; bx=x; by=y; }
            if(cost==0){
                n0++;
                if(n0==1){
                    char fn[512]; sprintf(fn,"%s_m%d_k%d_cost0.edges",outp,m,k);
                    FILE *f=fopen(fn,"w");
                    fprintf(f,"%d\n",V);
                    // A g (node g) -- B (node N + g*s)
                    int S[3]={0,x,y};
                    for(int gg=0; gg<N; gg++) for(int t=0;t<3;t++) fprintf(f,"%d %d\n", gg, N+mt[(size_t)gg*N+S[t]]);
                    fclose(f);
                    fprintf(stderr,"cost0 at x=%d y=%d written %s\n", x,y,fn);
                }
            }
        }
    }
    printf("RESULT xrange=%d-%d m=%d k=%d N=%d V=%d D=%d best_cost=%d at x=(%d,%d) y=(%d,%d) cost0_count=%ld evals=%ld\n",
           xlo,xhi,m,k,N,V,D,best, bx%m,bx/m, by%m,by/m, n0, evals);
    return 0;
}
