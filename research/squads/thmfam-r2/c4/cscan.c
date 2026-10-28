/* c4 label search for PGL(2,q) x Z_m covers (same convention as haar_ecc.c, PGL mode only).
 * Usage: cscan q m T restarts budget seed < base_lines   (base_lines = the 6 lines "a b c d 0" from
 *        gen_lps_cover.py 5 q 1 zero; the label column is ignored)
 * Labels z0=0, z1=1, z2..z5 in Z_m; hill climbing (accept equal) with random restarts.
 * f = number of vertices of the two components (from (I,A) and from (I,B)) at distance > T; FULL needs both
 * component sizes = q(q^2-1)m. Prints "OK ..." on success (f=0, FULL), else "FAIL ..." with the best labels.
 * Build: cc -O2 -o cscan cscan.c */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll;
static ll q, m, NQ, NI, V; static ll *inv; static int K; static ll M[16][4]; static ll Zg[16];
static ll md(ll a){a%=q;return a<0?a+q:a;}
static ll idx(ll a, ll b, ll c, ll d){
  if(a){ll t=inv[a]; b=b*t%q; c=c*t%q; d=d*t%q; return (b*q+c)*q+d;}
  {ll t=inv[b]; c=c*t%q; d=d*t%q; return q*q*q+c*q+d;}
}
static void unidx(ll i, ll *a, ll *b, ll *c, ll *d){
  if(i<q*q*q){*a=1;*d=i%q;i/=q;*c=i%q;*b=i/q;} else {i-=q*q*q;*a=0;*b=1;*d=i%q;*c=i/q;}
}
static int *stamp, *dist, *queue; static int epoch=0;
static unsigned long long rs=88172645463325252ULL;
static unsigned long long rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
/* BFS from (I, side); fills prof[0..ecc]; returns component size (both sides) */
static ll bfs(int side, ll *prof, int *ecc){
  epoch++; ll e=idx(1,0,0,1)*m; ll head=0, tail=0;
  int v0=(int)(e*2+side);
  stamp[v0]=epoch; dist[v0]=0; queue[tail++]=v0;
  int maxd=0; memset(prof,0,sizeof(ll)*(V+2>2000?2000:2000)); prof[0]=1;
  while(head<tail){
    int v=queue[head++]; int s=v&1; ll gi=v>>1; ll g=gi/m, zz=gi%m; int dv=dist[v];
    ll xa,xb,xc,xd; unidx(g,&xa,&xb,&xc,&xd);
    for(int i=0;i<K;i++){ ll A_,B_,C_,D_,h;
      if(s==0){A_=M[i][0];B_=M[i][1];C_=M[i][2];D_=M[i][3]; h=(zz+Zg[i])%m;}
      else {A_=M[i][3];B_=md(-M[i][1]);C_=md(-M[i][2]);D_=M[i][0]; h=((zz-Zg[i])%m+m)%m;}
      ll t=idx(md(A_*xa+B_*xc),md(A_*xb+B_*xd),md(C_*xa+D_*xc),md(C_*xb+D_*xd))*m+h;
      int w=(int)(t*2+(1-s));
      if(stamp[w]!=epoch){stamp[w]=epoch; dist[w]=dv+1; queue[tail++]=w; prof[dv+1]++; if(dv+1>maxd) maxd=dv+1;}
    }
  }
  *ecc=maxd; return tail;
}
static ll prof2[2][2000]; static int ecc2[2]; static ll comp2[2];
/* returns f (vertices beyond T, both starts); *full = both components have size V; *diam = max ecc */
static ll eval_labels(int *z, int *full, int *diam, int T){
  ll f=0; int dm=0, ok=1;
  for(int i=0;i<K;i++) Zg[i]=z[i];
  for(int s=0;s<2;s++){
    comp2[s]=bfs(s, prof2[s], &ecc2[s]);
    if(comp2[s]!=V) ok=0;
    if(ecc2[s]>dm) dm=ecc2[s];
    for(int d=T+1; d<=ecc2[s]; d++) f+=prof2[s][d];
  }
  *full=ok; *diam=dm; return f;
}
int main(int argc, char **argv){
  if(argc<7){fprintf(stderr,"usage: cscan q m T restarts budget seed < base\n"); return 2;}
  q=atoll(argv[1]); m=atoll(argv[2]); int T=atoi(argv[3]); int restarts=atoi(argv[4]); int budget=atoi(argv[5]);
  rs ^= (unsigned long long)atoll(argv[6])*0x9E3779B97F4A7C15ULL; if(!rs) rs=1;
  K=0; ll a,b,c,d,z; while(K<16 && scanf("%lld %lld %lld %lld %lld",&a,&b,&c,&d,&z)==5){ M[K][0]=md(a);M[K][1]=md(b);M[K][2]=md(c);M[K][3]=md(d); K++; }
  NQ=q*q*q+q*q; NI=NQ*m; V=q*(q*q-1)*m;
  inv=malloc(sizeof(ll)*q); inv[0]=0; for(ll x=1;x<q;x++){ll r=1,bb=x,e=q-2;while(e){if(e&1)r=r*bb%q;bb=bb*bb%q;e>>=1;}inv[x]=r;}
  stamp=calloc(2*NI,sizeof(int)); dist=calloc(2*NI,sizeof(int)); queue=malloc(sizeof(int)*2*NI);
  if(!stamp||!dist||!queue){fprintf(stderr,"oom\n"); return 2;}
  if(!(q*(q*q-1)>0)) return 2;
  int bestz[16]; ll bestf=-1; int bestdiam=0; int bestfull=0;
  for(int rr=0; rr<restarts; rr++){
    int z[16]; z[0]=0; z[1]=1%m; for(int i=2;i<K;i++) z[i]=rnd()%m;
    int full, diam; ll f=eval_labels(z,&full,&diam,T);
    for(int it=0; it<budget && !(full && f==0); it++){
      int zn[16]; memcpy(zn,z,sizeof(zn)); int i=2+rnd()%(K-2);
      if(rnd()%2) zn[i]=rnd()%m; else zn[i]=(int)((zn[i]+(ll)((rnd()%5)+1)*(rnd()%2?1:-1)+m)%m);
      int f2full,d2; ll f2=eval_labels(zn,&f2full,&d2,T);
      int better = (f2full!=full) ? (f2full>full) : (f2<=f);
      if(better){ memcpy(z,zn,sizeof(zn)); f=f2; full=f2full; diam=d2; }
    }
    if(full && (bestf<0 || f<bestf)){ bestf=f; memcpy(bestz,z,sizeof(bestz)); bestfull=full; bestdiam=diam; }
    if(full && f==0){
      printf("OK q=%lld m=%lld T=%d V=%lld diam=%d labels", q,m,T,V,diam);
      for(int i=0;i<K;i++) printf(" %d", z[i]); printf("\n"); return 0;
    }
  }
  printf("FAIL q=%lld m=%lld T=%d V=%lld best_f=%lld full=%d diam=%d labels", q,m,T,V,bestf,bestfull,bestdiam);
  for(int i=0;i<K;i++) printf(" %d", bestz[i]); printf("\n");
  return 1;
}
