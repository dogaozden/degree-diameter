/* Mixed two-sided Cayley bipartite graphs on G x {A,B}, |G| = 343 (non-abelian).
   A-vertex g ~ B-vertex s*g (s in S1, |S1|=k1)  and  A-vertex g ~ B-vertex g*t (t in T, |T|=k2), k1+k2=6.
   k1=6 is the Haar graph H(G,S1). Cost = ordered same-side pairs at distance > 4 (both sides) + 1000*dups.
   usage: ./mixed GROUP(heis|meta) K1 SECONDS SEED OUTPREFIX */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#define N 343
static int MUL[N][N], INV[N], GT;
static int ginit(const char *name){
  int r8[7]; int p=1; for(int j=0;j<7;j++){ r8[j]=p; p=(p*8)%49; }
  for(int x=0;x<N;x++) for(int y=0;y<N;y++){
    int z;
    if(!strcmp(name,"heis")){
      int a=x/49,b=(x/7)%7,c=x%7,a2=y/49,b2=(y/7)%7,c2=y%7;
      z=((a+a2)%7)*49+((b+b2)%7)*7+((c+c2+a*b2)%7);
    } else {
      int i=x/7,j=x%7,k=y/7,l=y%7;
      z=((i+r8[j]*k)%49)*7+((j+l)%7);
    }
    MUL[x][y]=z;
  }
  for(int x=0;x<N;x++) for(int y=0;y<N;y++) if(MUL[x][y]==0) INV[x]=y;
  /* identity is 0 in both encodings */
  for(int x=0;x<N;x++) if(MUL[0][x]!=x||MUL[x][0]!=x){ fprintf(stderr,"bad identity\n"); return 0; }
  for(int x=0;x<N;x++) for(int y=0;y<N;y++) for(int z=0;z<N;z+=37) if(MUL[MUL[x][y]][z]!=MUL[x][MUL[y][z]]){ fprintf(stderr,"not assoc\n"); return 0;}
  return 1;
}
static int K1,K2; static int S[6]; /* S[0..K1-1]=S1, S[K1..5]=T */
static unsigned stamp_arr[N], stamp=0;
static int nA(int g,int *out){ /* B-neighbours of A-vertex g */
  for(int i=0;i<K1;i++) out[i]=MUL[S[i]][g];
  for(int i=0;i<K2;i++) out[K1+i]=MUL[g][S[K1+i]];
  return 6;
}
static int nB(int h,int *out){ /* A-neighbours of B-vertex h */
  for(int i=0;i<K1;i++) out[i]=MUL[INV[S[i]]][h];
  for(int i=0;i<K2;i++) out[K1+i]=MUL[h][INV[S[K1+i]]];
  return 6;
}
static int dupcheck(void){
  int v[6];
  for(int g=0;g<N;g++){ nA(g,v); for(int i=0;i<6;i++) for(int j=0;j<i;j++) if(v[i]==v[j]) return 1; }
  for(int h=0;h<N;h++){ nB(h,v); for(int i=0;i<6;i++) for(int j=0;j<i;j++) if(v[i]==v[j]) return 1; }
  return 0;
}
/* uncovered same-side ordered pairs from A-sources (side=0) or B-sources (side=1) */
static int uncovered(int side){
  int tot=0;
  static int L1[6],L2[36],L3[216],L4[1296];
  int v[6];
  for(int src=0;src<N;src++){
    stamp++; int reached=0;
    /* level 1: other side, level 2: same side */
    int n1 = 6; 
    if(side==0) nA(src,L1); else nB(src,L1);
    int n2=0;
    for(int i=0;i<n1;i++){ if(side==0) nB(L1[i],v); else nA(L1[i],v); for(int j=0;j<6;j++){ L2[n2++]=v[j]; } }
    int n3=0;
    for(int i=0;i<n2;i++){ if(side==0) nA(L2[i],v); else nB(L2[i],v); for(int j=0;j<6;j++) L3[n3++]=v[j]; }
    int n4=0;
    for(int i=0;i<n3;i++){ if(side==0) nB(L3[i],v); else nA(L3[i],v); for(int j=0;j<6;j++) L4[n4++]=v[j]; }
    stamp_arr[src]=stamp; reached=1;
    for(int i=0;i<n2;i++) if(stamp_arr[L2[i]]!=stamp){ stamp_arr[L2[i]]=stamp; reached++; }
    for(int i=0;i<n4;i++) if(stamp_arr[L4[i]]!=stamp){ stamp_arr[L4[i]]=stamp; reached++; }
    tot += N - reached;
  }
  return tot;
}
static int cost(void){
  if(dupcheck()) return 1000000;
  return uncovered(0)+uncovered(1);
}
static unsigned long long rs;
static unsigned rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return (unsigned)(rs>>11); }
static double urand(void){ return (rnd()%1000000007u)/1000000007.0; }
static void write_edges(const char *fn){
  FILE *f=fopen(fn,"w"); fprintf(f,"%d\n",2*N);
  for(int g=0;g<N;g++){ int v[6]; nA(g,v); for(int i=0;i<6;i++) fprintf(f,"%d %d\n",g,N+v[i]); }
  fclose(f);
}
int main(int argc,char**argv){
  if(argc<6){ fprintf(stderr,"usage: GROUP K1 SECONDS SEED OUTPREFIX\n"); return 1; }
  if(!ginit(argv[1])) return 1;
  K1=atoi(argv[2]); K2=6-K1;
  double secs=atof(argv[3]); rs=strtoull(argv[4],0,10)*2654435761ULL+88172645463325252ULL;
  const char*outp=argv[5];
  /* random initial set of distinct elements */
  for(int i=0;i<6;i++){ int ok; do{ S[i]=1+rnd()%(N-1); ok=1; for(int j=0;j<i;j++) if(S[j]==S[i]) ok=0; }while(!ok); }
  int cur=cost(), best=cur; int bestS[6]; memcpy(bestS,S,sizeof S);
  double T0=atof(getenv("T0")?getenv("T0"):"150"), T1=atof(getenv("T1")?getenv("T1"):"1"); clock_t st=clock(); long it=0;
  while(1){
    it++;
    if((it&255)==0){ double el=(double)(clock()-st)/CLOCKS_PER_SEC; if(el>secs) break; }
    double frac=(double)(clock()-st)/CLOCKS_PER_SEC/secs; if(frac>1) frac=1;
    double T=T0*pow(T1/T0,frac);
    int idx=rnd()%6; int old=S[idx]; int nw;
    do{ nw=1+rnd()%(N-1); }while(0);
    int ok=1; for(int j=0;j<6;j++) if(j!=idx && S[j]==nw) ok=0; if(!ok) continue;
    S[idx]=nw;
    int c=cost();
    if(c<=cur || urand()<exp(-(c-cur)/T)){ cur=c; if(c<best){ best=c; memcpy(bestS,S,sizeof S); if(best==0) break; } }
    else S[idx]=old;
  }
  memcpy(S,bestS,sizeof S);
  printf("group=%s K1=%d best=%d iters=%ld\n",argv[1],K1,best,it);
  printf("S1:"); for(int i=0;i<K1;i++) printf(" %d",S[i]); printf("\nT:"); for(int i=0;i<K2;i++) printf(" %d",S[K1+i]); printf("\n");
  if(best==0){ char fn[512]; sprintf(fn,"%s.edges",outp); write_edges(fn); printf("WROTE %s\n",fn); }
  return 0;
}
