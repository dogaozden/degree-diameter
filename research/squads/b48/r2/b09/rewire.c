/* SA over one perfect matching M' (between side A = 0..N-1 and side B = N..2N-1) with 3 fixed matchings.
   Energy = number of unordered pairs at distance > 8 (exact, bitset BFS).
   usage: rewire INPUT SECONDS SEED T0 T1 OUT.edges
   INPUT: "n", then F and F edges (fixed), then V and V edges (variable matching, one per A vertex). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>
#define MAXN 2400
#define W 40
static int n, half;
static int nbr[MAXN][4], deg[MAXN];
static uint64_t cur[MAXN][W], nxt[MAXN][W];
static int mate[MAXN]; static int pfar[MAXN]; static int havep=0; static double PBIAS=0.0;
static int FA[20000], FB[20000]; static int NF;
static uint64_t rs;
static inline uint64_t rnd(void){ rs ^= rs<<13; rs ^= rs>>7; rs ^= rs<<17; return rs; }
static double urand(void){ return (rnd()>>11)*(1.0/9007199254740992.0); }
static double now(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec; }
static int W_;
static uint64_t bufA[MAXN][W], bufB[MAXN][W];
static long eval_far(void){
    int words = (n+63)/64;
    uint64_t (*c)[W] = bufA, (*x)[W] = bufB;
    for(int u=0;u<n;u++){ memset(c[u],0,sizeof(uint64_t)*words); c[u][u>>6] |= 1ULL<<(u&63); }
    for(int step=0; step<8; step++){
        for(int u=0;u<n;u++){
            uint64_t *o=x[u]; const uint64_t *s0=c[u];
            const uint64_t *s1=c[nbr[u][0]], *s2=c[nbr[u][1]], *s3=c[nbr[u][2]], *s4=c[nbr[u][3]];
            for(int w=0;w<words;w++) o[w]=s0[w]|s1[w]|s2[w]|s3[w]|s4[w];
        }
        uint64_t (*t)[W]=c; c=x; x=t;
    }
    long far=0;
    for(int u=0;u<n;u++){
        int cc=0; for(int w=0;w<words;w++) cc+=__builtin_popcountll(c[u][w]);
        far += n - cc;
    }
    return far/2;
}
static int has_nb(int u,int v){ for(int k=0;k<4;k++) if(nbr[u][k]==v) return 1; return 0; }
static void set_mate_slot(int a,int b_old,int b_new){
    /* replace neighbour b_old by b_new in slot 3 of a */
    for(int k=0;k<4;k++) if(nbr[a][k]==b_old){ nbr[a][k]=b_new; return; }
    fprintf(stderr,"slot error\n"); exit(1);
}
int main(int argc,char**argv){
    if(argc<7){ fprintf(stderr,"usage\n"); return 1; }
    FILE*f=fopen(argv[1],"r"); double secs=atof(argv[2]); rs=strtoull(argv[3],0,10)*2654435761ULL+88172645463325252ULL;
    double T0=atof(argv[4]), T1=atof(argv[5]); const char*out=argv[6];
    if(argc>8){ FILE*pf=fopen(argv[7],"r"); int a,b; while(fscanf(pf,"%d %d",&a,&b)==2){ pfar[a]=b; } fclose(pf); havep=1; PBIAS=atof(argv[8]); }
    if(fscanf(f,"%d",&n)!=1) return 1; half=n/2;
    int F; fscanf(f,"%d",&F);
    for(int i=0;i<n;i++) deg[i]=0;
    NF=F; for(int i=0;i<F;i++){ int a,b; fscanf(f,"%d %d",&a,&b); FA[i]=a; FB[i]=b; nbr[a][deg[a]++]=b; nbr[b][deg[b]++]=a; }
    int V; fscanf(f,"%d",&V);
    for(int i=0;i<V;i++){ int a,b; fscanf(f,"%d %d",&a,&b); nbr[a][deg[a]++]=b; nbr[b][deg[b]++]=a; mate[a]=b; }
    fclose(f);
    for(int i=0;i<n;i++) if(deg[i]!=4){ fprintf(stderr,"deg %d = %d\n",i,deg[i]); return 1; }
    long far=eval_far(); long best=far;
    fprintf(stderr,"init far=%ld\n",far);
    double t0=now(), T=T0; long it=0, acc=0;
    int bestmate[MAXN]; memcpy(bestmate,mate,sizeof(int)*half);
    while(1){
        if((it&63)==0){ double el=now()-t0; if(el>secs) break; double fr=el/secs; T=T0*pow(T1/T0,fr); }
        it++;
        int a1 = rnd()%half, a2 = rnd()%half;
        if(havep && urand()<PBIAS){ /* move that makes a1 adjacent to its far partner pfar[a1] */
            int tb=pfar[a1]; a2=-1; for(int a=0;a<half;a++) if(mate[a]==tb){a2=a;break;}
            if(a2<0||a2==a1) continue;
        }
        if(a1==a2) continue;
        int b1=mate[a1], b2=mate[a2];
        if(has_nb(a1,b2) || has_nb(a2,b1)) continue;
        /* apply */
        set_mate_slot(a1,b1,b2); set_mate_slot(b2,a2,a1);
        set_mate_slot(a2,b2,b1); set_mate_slot(b1,a1,a2);
        /* note: set_mate_slot(b2,a2,a1) replaced a2 by a1 in b2 (b2 was matched to a2); then a2 slot b2->b1, b1 a1->a2 */
        mate[a1]=b2; mate[a2]=b1;
        long nf=eval_far();
        long d=nf-far;
        if(getenv("DBG") && it<=40) fprintf(stderr,"DBG it=%ld d=%ld\n",it,d);
        if(d<=0 || urand()<exp(-d/T)){
            far=nf; acc++;
            if(far<best){ best=far; memcpy(bestmate,mate,sizeof(int)*half);
                fprintf(stderr,"it %ld t=%.1f best=%ld\n",it,T,best); if(best==0) break; }
        } else {
            set_mate_slot(a1,b2,b1); set_mate_slot(b1,a2,a1);
            set_mate_slot(a2,b1,b2); set_mate_slot(b2,a1,a2);
            mate[a1]=b1; mate[a2]=b2;
        }
    }
    /* write best graph: fixed edges + best matching */
    FILE*o=fopen(out,"w");
    fprintf(o,"%d\n",n);
    for(int i=0;i<NF;i++) fprintf(o,"%d %d\n",FA[i],FB[i]);
    for(int a=0;a<half;a++) fprintf(o,"%d %d\n",a,bestmate[a]);
    fclose(o);
    fprintf(stderr,"RESULT best=%ld iters=%ld acc=%ld secs=%.1f out=%s\n",best,it,acc,now()-t0,out);
        printf("%ld\n",best);
    return 0;
}
