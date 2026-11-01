/* e08: Z11 partial-orbit packer on top of the d06 34,848 hub set (card e08, round 3).
 * A Z11 orbit = base N (<= 17 vertices of side T) with its 11 translates N+u, u in {0,2,...,20} (mod 22).
 * usage: z11 EDGES ORBFILE SECS SEED OUTHUBS CANDFILE...
 *   ORBFILE: 48 full-orbit bases (global ids), first 27 lines = A-hubs (N in B), last 21 = B-hubs (N in A).
 *   OUTHUBS: every hub as one line of global ids (existing 1056 hubs + new Z11 translates).
 * Global ids: A-vertex ((a_i,g),x) local = (22i+g)*256+id(x) in [0,H); B-vertex global = H + local.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#define H 16896
#define W 264
static int nbr[2][H][16];          /* nbr[0][a] = B-locals adjacent to A-local a; nbr[1][b] = A-locals */
static uint64_t *R2[2], *D3[2];    /* R2[T][x]: T-locals at distance 2 from x; D3[T][x]: (1-T)-locals at distance <=3 */
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned rnd(void){ rs ^= rs<<13; rs ^= rs>>7; rs ^= rs<<17; return (unsigned)(rs>>11); }
static double now(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec; }
static inline int shl(int l, int u){ int blk=l>>8; int j=blk/22, h=blk%22; return ((j*22+(h+u)%22)<<8) | (l&255); }
static inline int bit(const uint64_t *a, int l){ return (int)((a[l>>6]>>(l&63))&1); }
static inline void setb(uint64_t *a, int l){ a[l>>6] |= 1ULL<<(l&63); }
typedef struct { int side; int n; int v[17]; } hub_t;   /* side = hub side; v = locals on side 1-side */
static hub_t hubs[4000]; static int nh = 0;
static char used[2][H];

static int self_ok(const int *v, int n){  /* N+u disjoint from N for even u != 0 */
    for (int i=0;i<n;i++) for (int j=0;j<n;j++) if (i!=j){
        int a=v[i], b=v[j]; if ((a&255)!=(b&255)) continue; if ((a>>8)/22 != (b>>8)/22) continue;
        int d=((a>>8)%22 - (b>>8)%22 + 22)%22; if (d%2==0) return 0; }
    return 1;
}
static void b2_of(const int *v, int n, int T, uint64_t *out){   /* out = union R2[T][x] */
    memset(out,0,W*8); for (int i=0;i<n;i++){ uint64_t *r=R2[T]+(size_t)v[i]*W; for(int w=0;w<W;w++) out[w]|=r[w]; } }


static const int MUL4[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static int scal(int l, int a){ int r=0; for(int k=0;k<4;k++) r |= MUL4[l][(a>>(2*k))&3]<<(2*k); return r; }
static inline int keyof(int l){ return ((l>>8)/22)*256 + (l&255); }
/* free-key covers (card e08): 4 lines (each 4 vertices of one controller block, key-distinct) + optional extra,
   all vertices on keys unused by existing hubs. Returns number of covers appended to cov (locals). */
static int gen_covers(int T, int want, double tend, int (*out)[17], int *outn, int maxout){
    int nl=0; static int (*lines)[4]; static int nlines_alloc=0;
    if (!lines){ lines=malloc(sizeof(int[4])*66*85*64); }
    int dirs[85], nd=0; for (int c=1;c<256;c++){ int lead=-1; for(int k=0;k<4;k++) if((c>>(2*k))&3){ lead=(c>>(2*k))&3; break; } if (lead==1) dirs[nd++]=c; }
    for (int cv=0;cv<66;cv++) for (int di=0;di<nd;di++) for (int y=0;y<256;y++){
        int ok=1; int ln[4];
        for (int l=0;l<4;l++){ int z=y^scal(l,dirs[di]); ln[l]=cv*256+z; if (used[T][ln[l]]) { ok=0; break; } }
        if (!ok) continue;
        /* keep each line once: only if y is the minimal member of its line */
        int mn=1; for (int l=0;l<4;l++){ int z=(ln[l]&255); if (z<(y)) { mn=0; break; } }
        if (!mn) continue;
        for (int l=0;l<4;l++) lines[nl][l]=ln[l]; nl++; }
    fprintf(stderr,"T=%d free lines %d\n",T,nl);
    if (nl==0) return 0;
    uint64_t *unc=malloc(W*8), *o=malloc(W*8);
    int nout_=0;
    static char keyused[768];
    long tries=0;
    while (nout_<want && nout_<maxout && now()<tend){
        tries++;
        memset(keyused,0,sizeof keyused); int ch[5], nch=0;
        for (int w=0;w<W;w++) unc[w]=~0ULL;
        int ok=0; int first=-1;
        for (int s=0;s<1000 && first<0;s++){ int i=rnd()%nl; int f=1; for(int l=0;l<4;l++){ if (keyused[keyof(lines[i][l])]) f=0; } if (f) first=i; }
        if (first<0) continue;
        #define ADDL(i) do{ for(int l=0;l<4;l++) keyused[keyof(lines[i][l])]=1; ch[nch++]=(i); \
            for(int l=0;l<4;l++){ uint64_t *dd=D3[T]+(size_t)lines[i][l]*W; for(int w=0;w<W;w++) unc[w]&=~dd[w]; } }while(0)
        ADDL(first);
        for (int step=1; step<4; step++){
            int best=-1, bg=-1;
            for (int s=0;s<400;s++){ int i=rnd()%nl; int f=1; for(int l=0;l<4;l++) if (keyused[keyof(lines[i][l])]) {f=0;break;} if(!f) continue;
                int g=0; for (int l=0;l<4;l++){ uint64_t *dd=D3[T]+(size_t)lines[i][l]*W; for(int w=0;w<W;w++) g+=__builtin_popcountll(unc[w]&dd[w]); }
                if (g>bg){bg=g;best=i;} }
            if (best<0) break;
            ADDL(best);
            { int z=0; for(int w=0;w<W;w++) z+=__builtin_popcountll(unc[w]); if (z==0){ ok=1; break; } }
        }
        int cover[17], m=0;
        if (!ok && nch==4){
            int extra=-1;
            for (int s=0;s<3000 && extra<0;s++){ int t=rnd()%H; if (used[T][t] || keyused[keyof(t)]) continue;
                uint64_t *dd=D3[T]+(size_t)t*W; int cov=1; for(int w=0;w<W;w++) if (unc[w] & ~dd[w]) {cov=0;break;}
                if (cov) extra=t; }
            if (extra>=0){ ok=1; keyused[keyof(extra)]=1; cover[m++]=extra; }
        }
        if (!ok) continue;
        for (int a=0;a<nch;a++) for (int l=0;l<4;l++) cover[m++]=lines[ch[a]][l];
        /* store */
        memcpy(out[nout_], cover, sizeof(int)*m); outn[nout_]=m; nout_++;
    }
    fprintf(stderr,"T=%d covers %d from %ld tries\n",T,nout_,tries);
    return nout_;
}

int main(int argc, char **argv){
    if (argc < 6){ fprintf(stderr,"usage: z11 EDGES ORBFILE SECS SEED OUTHUBS CANDFILE...\n"); return 2; }
    double secs = atof(argv[3]); rs ^= (unsigned long long)atoll(argv[4])*0x9E3779B97F4A7C15ULL; for(int i=0;i<10;i++) rnd();
    static int deg[2][H];
    FILE *f = fopen(argv[1],"r"); long n,u,v; if (fscanf(f,"%ld",&n)!=1 || n!=2*H) return 3;
    while (fscanf(f,"%ld %ld",&u,&v)==2){ if (u>v){long t=u;u=v;v=t;} v-=H; nbr[0][u][deg[0][u]++]=(int)v; nbr[1][v][deg[1][v]++]=(int)u; }
    fclose(f);
    for (int i=0;i<H;i++) if (deg[0][i]!=16||deg[1][i]!=16){ fprintf(stderr,"not regular\n"); return 3; }
    double t0 = now();
    for (int T=0; T<2; T++){
        R2[T]=calloc((size_t)H*W,8); D3[T]=calloc((size_t)H*W,8);
        for (int x=0;x<H;x++){
            uint64_t *r=R2[T]+(size_t)x*W, *d=D3[T]+(size_t)x*W;
            for (int i=0;i<16;i++){ int a=nbr[T][x][i];
                setb(d,a);                                  /* distance 1 (side 1-T) */
                for (int j=0;j<16;j++){ int y=nbr[1-T][a][j]; if (y!=x) setb(r,y); }   /* distance 2 */
                for (int j=0;j<16;j++){ int y=nbr[1-T][a][j]; if (y==x) continue;
                    for (int k=0;k<16;k++) setb(d,nbr[T][y][k]); } }   /* distance 3 */
        }
    }
    fprintf(stderr,"setup %.1fs\n", now()-t0);
    /* existing hubs */
    FILE *of = fopen(argv[2],"r"); char line[4096]; int nb = 0;
    int base[64][17], bn[64], bside[64];
    while (fgets(line,sizeof line,of)){ int x, off, m=0; char *q=line; if (strlen(line)<2) continue;
        while (sscanf(q,"%d%n",&x,&off)==1){ q+=off; base[nb][m++]=x; } bn[nb]=m; bside[nb]=(base[nb][0]>=H); nb++; }
    fclose(of);
    for (int b=0;b<nb;b++){ int sideT = bside[b]; /* neighbours on side sideT; hub side = 1-sideT */
        for (int t=0;t<22;t++){
            hub_t *hb = &hubs[nh++]; hb->side = 1-sideT; hb->n = bn[b];
            for (int i=0;i<bn[b];i++){ int g=base[b][i]; int loc=g-(sideT?H:0); hb->v[i]=shl(loc,t); used[sideT][hb->v[i]]=1; }
        } }
    int nexist = nh;
    /* sanity: existing hubs pairwise disjoint, dims */
    fprintf(stderr,"existing hubs %d (bases %d)\n", nexist, nb);
    static int pside[200000]; static int pv[200000][17]; static int pn[200000]; int NP = 0;
    static int (*gcov)[17]; static int gn[200000]; gcov = malloc(sizeof(int[17])*60000);
    for (int hs=0; hs<2; hs++){
        int T=1-hs; double tend = now() + secs*0.42;
        int ng = gen_covers(T, 60000, tend, gcov, gn, 60000);
        int cnt=0;
        for (int c=0;c<ng;c++){
            int m=gn[c]; int loc[17]; memcpy(loc,gcov[c],sizeof(int)*m);
            int ok=1;
            if (!self_ok(loc,m)) ok=0;
            if (ok){ uint64_t b2[W]; b2_of(loc,m,T,b2);
                for (int s=2;s<=20&&ok;s+=2){ int hit=0; for (int i=0;i<m&&!hit;i++) if (bit(b2,shl(loc[i],s))) hit=1; if(!hit) ok=0; }
                for (int h=0;h<nexist&&ok;h++){ if (hubs[h].side!=hs) continue; int hit=0;
                    for (int i=0;i<hubs[h].n&&!hit;i++) if (bit(b2,hubs[h].v[i])) hit=1; if(!hit) ok=0; } }
            if (ok && NP<200000){ pside[NP]=hs; pn[NP]=m; for(int i=0;i<m;i++) pv[NP][i]=loc[i]; NP++; cnt++; }
        }
        fprintf(stderr,"side %d: %d covers, %d survive self+compat\n", hs, ng, cnt);
    }
    fprintf(stderr,"pool survivors %d (%.1fs)\n", NP, now()-t0);
    if (NP==0){ fprintf(stderr,"no survivors\n"); }

    /* per hub side, clique among survivors with Z11 pair rule */
    int bestTotal=0; int bestSel[200000]; int bestNs=0; int bestSide=-1;
    for (int hs=0; hs<2; hs++){
        int idx[200000], P=0; for (int a=0;a<NP;a++) if (pside[a]==hs) idx[P++]=a;
        if (P==0) continue;
        int CW=(P+63)/64; uint64_t *C=calloc((size_t)P*CW,8);
        long ne=0; int T=1-hs; uint64_t *b2=malloc(W*8), *mk=malloc(W*8);
        for (int a=0;a<P;a++){ int A=idx[a]; b2_of(pv[A],pn[A],T,b2); memset(mk,0,W*8); for(int i=0;i<pn[A];i++) setb(mk,pv[A][i]);
            for (int bb=a+1;bb<P;bb++){ int B=idx[bb]; int ok=1;
                for (int s=0;s<22&&ok;s+=2){ int comp=0, dis=1;
                    for (int i=0;i<pn[B];i++){ int y=shl(pv[B][i],s); if (bit(mk,y)) {dis=0;break;} if (bit(b2,y)) comp=1; }
                    if (!dis || !comp) ok=0; }
                if (ok){ C[(size_t)a*CW+(bb>>6)]|=1ULL<<(bb&63); C[(size_t)bb*CW+(a>>6)]|=1ULL<<(a&63); ne++; } }
        }
        fprintf(stderr,"side %d: P=%d edges=%ld density=%.4f (%.1fs)\n", hs, P, ne, P>1?2.0*ne/((double)P*(P-1)):0.0, now()-t0);
        /* randomized greedy + plateau max clique (as d06), time-limited */
        int *best=malloc(4*(P+1)), nbest=0, *cur=malloc(4*(P+1)), ncur; char *inc=calloc(P+1,1); int *cnt=calloc(P+1,4);
        double tl = now() + 4.0;
        while (now() < tl && P>0){
            ncur=0; memset(inc,0,P); memset(cnt,0,4*P);
            for (int it=0; it<P; it++){ int v2=rnd()%P; if (inc[v2]||cnt[v2]) continue; inc[v2]=1; cur[ncur++]=v2;
                for (int x=0;x<P;x++) if (x!=v2 && !((C[(size_t)v2*CW+(x>>6)]>>(x&63))&1)) cnt[x]++; }
            for (int rounds=0; rounds<20000 && now()<tl; rounds++){
                int added=0;
                for (int x=0;x<P;x++) if (!inc[x]&&cnt[x]==0){ inc[x]=1; cur[ncur++]=x; for (int y=0;y<P;y++) if (y!=x && !((C[(size_t)x*CW+(y>>6)]>>(y&63))&1)) cnt[y]++; added=1; }
                if (ncur>nbest){ nbest=ncur; memcpy(best,cur,4*ncur); fprintf(stderr,"  side %d clique %d (%.1fs)\n",hs,nbest,now()-t0); }
                if (added) continue;
                int x=-1; for (int s=0;s<300;s++){ int y=rnd()%P; if(!inc[y]&&cnt[y]==1){x=y;break;} }
                if (x<0) break;
                int drop=-1; for (int a2=0;a2<ncur;a2++){ int m2=cur[a2]; if (!((C[(size_t)x*CW+(m2>>6)]>>(m2&63))&1)){drop=a2;break;} }
                int m2=cur[drop]; inc[m2]=0; cur[drop]=cur[--ncur];
                for (int y=0;y<P;y++) if (y!=m2 && !((C[(size_t)m2*CW+(y>>6)]>>(y&63))&1)) cnt[y]--;
                inc[x]=1; cur[ncur++]=x;
                for (int y=0;y<P;y++) if (y!=x && !((C[(size_t)x*CW+(y>>6)]>>(y&63))&1)) cnt[y]++;
            }
        }
        if (nbest>0 && nbest*11 > bestTotal){ bestTotal=nbest*11; bestSide=hs; bestNs=nbest; for(int i=0;i<nbest;i++) bestSel[i]=idx[best[i]]; }
        (void)bestSide;
    }
    /* write output: existing hubs + new Z11 translates of the selected bases of the best side (both sides if both chosen) */
    FILE *oh = fopen(argv[5],"w"); int nout=0;
    for (int h=0;h<nexist;h++){ for(int i=0;i<hubs[h].n;i++){ int l=hubs[h].v[i]; int off = (1-hubs[h].side)?H:0; fprintf(oh,"%d ", l+off); } fprintf(oh,"\n"); nout++; }
    int newh=0;
    if (bestNs>0) for (int i=0;i<bestNs;i++){ int A=bestSel[i]; int T=1-pside[A]; int off=T?H:0;
        for (int s=0;s<22;s+=2){ for (int k=0;k<pn[A];k++) fprintf(oh,"%d ", shl(pv[A][k],s)+off); fprintf(oh,"\n"); nout++; newh++; } }
    fclose(oh);
    fprintf(stderr,"wrote %d hubs (%d existing + %d new Z11 hubs from %d bases)\n", nout, nexist, newh, bestNs);
    printf("pool %d best_new_hubs %d bases %d total_hubs %d n %d\n", NP, newh, bestNs, nout, 2*H+nout);
    return 0;
}
