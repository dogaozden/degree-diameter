/* Voltage lift of the H(2) incidence graph (Tutte 12-cage, 126 vertices, cubic, girth 12, diameter 6) over a group G.
   Cost = number of pairs (base vertex u, lift vertex x) with dist((u,e), x) > 12 (lift BFS, depth-limited).
   Left multiplication is a fibre-preserving automorphism, so cost 0 <=> lift diameter <= 12.
   usage: lift GROUPFILE SECS SEED OUTPREFIX [START_VOLT_FILE]
   Spanning-tree edges have voltage e (index 0); 64 cotree edges get group elements (annealed). Writes OUTPREFIX.volt and,
   if cost 0, OUTPREFIX.edges (first line n, then "u v"). Memory: O(126 m) ints. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <math.h>
#include <sys/time.h>
static double wall(void){ struct timeval tv; gettimeofday(&tv,NULL); return tv.tv_sec + 1e-6*tv.tv_usec; }
#define NB 126
#define NE 189
#define DEP 12
static int m, N;            /* group order, lift vertices NB*m */
static int *G, *INV;        /* G[a*m+b] */
static int ex[NE], ey[NE], tree[NE], cot[NE], ncot;
static int volt[NE];
static int *dist, *queue;
static unsigned *stamp; static unsigned cur_stamp = 1;
static int adjy[NB][3], adja[NB][3];   /* base adjacency with voltage of directed edge */
static int deg[NB];

static unsigned long long rng_s = 88172645463325252ULL;
static unsigned long long rnd(void){ rng_s ^= rng_s<<13; rng_s ^= rng_s>>7; rng_s ^= rng_s<<17; return rng_s; }
static int rndint(int k){ return (int)(rnd() % (unsigned long long)k); }

static void build_adj(void){
    memset(deg,0,sizeof(deg));
    for(int k=0;k<NE;k++){
        int x=ex[k], y=ey[k], a=volt[k];
        adjy[x][deg[x]] = y; adja[x][deg[x]] = a;  /* x->y voltage a  (x point side, y line side) */
        deg[x]++;
        adjy[y][deg[y]] = x; adja[y][deg[y]] = INV[a]; /* y->x voltage a^-1 */
        deg[y]++;
    }
}

/* cost: uncovered pairs over all base sources u */
static long long cost_fn(long long cap){
    long long total = 0;
    int V = NB*m;
    for(int u=0;u<NB;u++){
        cur_stamp++;
        int head=0, tail=0;
        int s = u*m + 0;
        stamp[s]=cur_stamp; dist[s]=0; queue[tail++]=s;
        int seen = 1;
        while(head<tail){
            int z = queue[head++];
            int d = dist[z];
            if(d>=DEP) continue;
            int x = z / m, g = z % m;
            for(int t=0;t<3;t++){
                int y = adjy[x][t], h = G[g*m + adja[x][t]];
                int w = y*m + h;
                if(stamp[w]!=cur_stamp){ stamp[w]=cur_stamp; dist[w]=d+1; queue[tail++]=w; seen++; }
            }
        }
        total += V - seen;
        if(total >= cap) return total;
    }
    return total;
}

int main(int argc, char **argv){
    if(argc<5){ fprintf(stderr,"usage: lift GROUPFILE SECS SEED OUTPREFIX [START]\n"); return 1; }
    FILE *gf = fopen(argv[1],"r"); if(!gf){ perror("group"); return 1; }
    if(fscanf(gf,"%d",&m)!=1) return 1; N = m;
    G = malloc(sizeof(int)*m*m); INV = malloc(sizeof(int)*m);
    for(int i=0;i<m*m;i++) if(fscanf(gf,"%d",&G[i])!=1) return 1;
    fclose(gf);
    for(int a=0;a<m;a++){ int found=-1; for(int b=0;b<m;b++) if(G[a*m+b]==0) found=b; INV[a]=found; }
    double secs = atof(argv[2]); double t0 = wall(); rng_s ^= (unsigned long long)atoll(argv[3]) * 2654435761ULL + 1; for(int i=0;i<10;i++) rnd();
    const char *outp = argv[4];
    FILE *bf = fopen("/home/user/degree-diameter/research/squads/raise-d12/r1/a01/code/base_edges.txt","r");
    int nb, ne; if(fscanf(bf,"%d %d",&nb,&ne)!=2) return 1;
    ncot=0;
    for(int k=0;k<NE;k++){
        int p,l,t; if(fscanf(bf,"%d %d %d",&p,&l,&t)!=3) return 1;
        ex[k]=p; ey[k]=l; tree[k]=t; volt[k]=0;
        if(!t){ cot[ncot++]=k; }
    }
    fclose(bf);
    if(argc>5){ /* start from voltage file: NE lines of group element per edge */
        FILE *sf = fopen(argv[5],"r"); if(sf){ for(int k=0;k<NE;k++){ int v; if(fscanf(sf,"%d",&v)!=1) break; volt[k]=v; } fclose(sf);} 
    } else {
        for(int i=0;i<ncot;i++) volt[cot[i]] = rndint(m);
    }
    /* tree edges stay at 0 (identity) */
    dist = malloc(sizeof(int)*NB*m); queue = malloc(sizeof(int)*NB*m); stamp = calloc(NB*m, sizeof(unsigned));
    build_adj();
    if(getenv("SAMPLE")){ /* statistics of cost over random voltage assignments */
        int K = atoi(getenv("SAMPLE")); long long mn=1LL<<60, sum=0; int zero=0;
        for(int s2=0;s2<K && wall()-t0<secs;s2++){
            for(int i=0;i<ncot;i++) volt[cot[i]] = rndint(m);
            build_adj(); long long c = cost_fn(1LL<<60); sum+=c; if(c<mn) mn=c; if(c==0) zero++;
        }
        printf("SAMPLE m=%d n=%d min=%lld mean=%.1f zeros=%d\n", m, NB*m, mn, (double)sum/K, zero);
        return 0;
    }
    if(getenv("SCAN")){ /* exhaustive single-voltage scan of a start state: cost of every (cotree edge, value) change */
        long long c0 = cost_fn(1LL<<60), bestc = c0; int bk=-1, bv=-1; long long hist[64]={0};
        printf("SCAN start cost %lld\n", c0); fflush(stdout);
        for(int i=0;i<ncot && wall()-t0<secs;i++){
            int k=cot[i]; int old=volt[k];
            for(int v=0;v<m;v++){ if(v==old) continue; volt[k]=v; build_adj(); long long c=cost_fn(1LL<<60);
                if(c<bestc){ bestc=c; bk=k; bv=v; }
                if(c==0){ printf("FOUND cost 0 at edge %d value %d\n",k,v); }
            }
            volt[k]=old; build_adj();
        }
        printf("SCAN done best single change cost %lld (edge %d -> %d)\n", bestc, bk, bv);
        if(bestc==0){ volt[bk]=bv; build_adj(); char fn[512]; sprintf(fn,"%s.volt",outp); FILE *vf=fopen(fn,"w"); for(int k=0;k<NE;k++) fprintf(vf,"%d\n",volt[k]); fclose(vf);} 
        return 0;
    }
    long long cur = cost_fn(1LL<<60), best = cur;
    int *bestv = malloc(sizeof(int)*NE); memcpy(bestv, volt, sizeof(int)*NE);

    double T0 = getenv("T0") ? atof(getenv("T0")) : 3.0, T1 = 0.05;
    long long it = 0, acc = 0;
    double elapsed = 0, T = T0;
    while(best > 0){
        if((it & 63) == 0){
            elapsed = wall()-t0;
            if(elapsed >= secs) break;
            double fr = elapsed/secs; T = T0*pow(T1/T0, fr);
        }
        it++;
        int k = cot[rndint(ncot)];
        int old = volt[k];
        int nv = rndint(m); if(nv==old) continue;
        volt[k] = nv; build_adj();
        long long c = cost_fn(cur + (long long)(10*T) + 1 + 2000000000LL);  /* no early cut beyond need */
        double dc = (double)(c - cur);
        if(dc <= 0 || exp(-dc / T) > (double)(rnd()%1000000)/1e6){
            cur = c; acc++;
            if(cur < best){ best = cur; memcpy(bestv, volt, sizeof(int)*NE); }
        } else { volt[k] = old; build_adj(); }
    }
    memcpy(volt, bestv, sizeof(int)*NE); build_adj();
    printf("m=%d n=%d iters=%lld accepted=%lld best_cost=%lld secs=%.1f\n", m, NB*m, it, acc, best, wall()-t0);
    char fn[512]; sprintf(fn,"%s.volt",outp); FILE *vf=fopen(fn,"w"); for(int k=0;k<NE;k++) fprintf(vf,"%d\n",volt[k]); fclose(vf);
    if(best==0){
        sprintf(fn,"%s.edges",outp); FILE *ef=fopen(fn,"w");
        int n = NB*m; fprintf(ef,"%d\n",n);
        for(int k=0;k<NE;k++) for(int g=0;g<m;g++) fprintf(ef,"%d %d\n", ex[k]*m+g, ey[k]*m + G[g*m+volt[k]]);
        fclose(ef); printf("wrote %s (n=%d)\n", fn, n);
    }
    return 0;
}
