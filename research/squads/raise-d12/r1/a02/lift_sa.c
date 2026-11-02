// Simulated annealing over voltage lifts of the Tutte 8-cage (30 base vertices, cubic, girth 8, diam 4).
// usage: lift_sa GROUPFILE BASEFILE D SECS SEED OUT [START_VOLTAGES]
// GROUPFILE: m, then m*m mult table (row-major), identity = 0.
// BASEFILE: n m, then "u v tree" lines. Tree edges get voltage 0 (identity); cotree edges get free voltages.
// cost = sum over base u of #{x in lift : dist((u,0),x) > D}. Solution (cost 0) written to OUT as
// "m n" then the edge list of the lift (first line n_lift, then "x y" lines), plus voltages.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
static double wall(void){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts); return ts.tv_sec+1e-9*ts.tv_nsec; }
#include <stdint.h>

static int m, nb, ne;
static int *mul, *inv;
static int eu[64], ev[64], et[64];          // base edges
static int ncot, cot[64];                   // cotree edge indices
static int volt[64];                        // voltage per base edge
static int adjn[64], adjv[64][3], adjg[64][3]; // base adjacency with voltages (oriented from u)
static uint32_t *stamp; static uint32_t curstamp = 1;
static int *queue_, *depth_;

static uint64_t rs;
static inline uint64_t rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static void build_adj(void){
    for(int u=0;u<nb;u++) adjn[u]=0;
    for(int e=0;e<ne;e++){
        int u=eu[e], v=ev[e], a=volt[e];
        adjv[u][adjn[u]]=v; adjg[u][adjn[u]]=a; adjn[u]++;
        adjv[v][adjn[v]]=u; adjg[v][adjn[v]]=inv[a]; adjn[v]++;
    }
}

// cost from base vertex u0 with lift vertex (u0,0); returns #far lift vertices
static int far_from(int u0, int D){
    curstamp++;
    int N = nb*m; int head=0, tail=0;
    int src = u0*m + 0;
    stamp[src]=curstamp; queue_[tail++]=src; depth_[src]=0;
    int visited=1;
    while(head<tail){
        int x=queue_[head++]; int d=depth_[x];
        if(d>=D) continue;
        int u=x/m, g=x%m;
        for(int k=0;k<adjn[u];k++){
            int v=adjv[u][k]; int h=mul[g*m+adjg[u][k]];
            int y=v*m+h;
            if(stamp[y]!=curstamp){ stamp[y]=curstamp; depth_[y]=d+1; queue_[tail++]=y; visited++; }
        }
    }
    return N - visited;
}
static int cost_lim(int D, int lim){
    int c=0;
    for(int u=0;u<nb;u++){ c+=far_from(u,D); if(c>lim) return c; }
    return c;
}
static int cost(int D){ return cost_lim(D, 1<<30); }

int main(int argc, char**argv){
    if(argc<7){ fprintf(stderr,"usage\n"); return 1; }
    int D=atoi(argv[3]); double secs=atof(argv[4]); uint64_t seed=strtoull(argv[5],0,10); const char*out=argv[6];
    rs = seed*2654435761ULL + 88172645463325252ULL; for(int i=0;i<10;i++) rnd();
    FILE*f=fopen(argv[1],"r"); if(fscanf(f,"%d",&m)!=1) return 1;
    mul=malloc(sizeof(int)*m*m); for(int i=0;i<m*m;i++) if(fscanf(f,"%d",&mul[i])!=1) return 1; fclose(f);
    inv=malloc(sizeof(int)*m); for(int a=0;a<m;a++) for(int b=0;b<m;b++) if(mul[a*m+b]==0) inv[a]=b;
    f=fopen(argv[2],"r"); if(fscanf(f,"%d %d",&nb,&ne)!=2) return 1;
    for(int e=0;e<ne;e++){ if(fscanf(f,"%d %d %d",&eu[e],&ev[e],&et[e])!=3) return 1; if(!et[e]) cot[ncot++]=e; }
    fclose(f);
    int N=nb*m; stamp=calloc(N,sizeof(uint32_t)); queue_=malloc(sizeof(int)*N); depth_=malloc(sizeof(int)*N);
    for(int e=0;e<ne;e++) volt[e]=0;
    if(argc>7){ // start voltages: ncot ints
        FILE*g=fopen(argv[7],"r"); for(int i=0;i<ncot;i++){ if(fscanf(g,"%d",&volt[cot[i]])!=1) break; } fclose(g);
    } else for(int i=0;i<ncot;i++) volt[cot[i]] = rnd()%m;
    build_adj();
    int cur=cost(D), best=cur; int bestv[64]; for(int i=0;i<ncot;i++) bestv[i]=volt[cot[i]];
    fprintf(stderr,"m=%d N=%d ncot=%d start cost %d\n", m, N, ncot, cur);
    double t0=wall(); long it=0; double T0=3.0, T1=0.05;
    while(best>0){
        double el=wall()-t0; if(el>secs) break;
        double frac=el/secs; double T=T0*pow(T1/T0,frac);
        int i=rnd()%ncot; int e=cot[i]; int old=volt[e];
        int nv=rnd()%m; if(nv==old) continue;
        volt[e]=nv; build_adj();
        double U=((rnd()%1000000)+0.5)/1e6; double thr = cur - T*log(U); // accept iff c <= thr
        int lim=(int)floor(thr);
        int c=cost_lim(D, lim); it++;
        if(c<=lim){ cur=c; if(c<best){ best=c; for(int k=0;k<ncot;k++) bestv[k]=volt[cot[k]]; } }
        else { volt[e]=old; build_adj(); }
    }
    fprintf(stderr,"done it=%ld best=%d cur=%d time=%.1f\n", it, best, cur, wall()-t0);
    printf("RESULT m=%d n=%d best=%d evals=%ld\n", m, N, best, it);
    // write best voltages
    for(int k=0;k<ncot;k++) volt[cot[k]]=bestv[k];
    build_adj();
    FILE*o=fopen(out,"w");
    fprintf(o,"%d %d\n", m, best);
    for(int k=0;k<ncot;k++) fprintf(o,"%d ",bestv[k]); fprintf(o,"\n");
    fclose(o);
    return 0;
}
