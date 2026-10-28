/* haar_dist: BFS in the Haar graph H(PGL(2,q), S), m = 1, S from generator lines "a b c d 0" (stdin).
 * Convention as haar_ecc.c: (g,A) ~ (s g,B).  Usage: haar_dist q targets.txt [lastlayer_out] < gens
 * BFS from (e,A) and from (e,B); prints ecc, component sizes, and for each target T (line "a b c d" in targets.txt)
 * d_A = dist((e,A),(T,A)), d_B = dist((e,A),(T,B)) (-1 = not in the component).  If lastlayer_out is given, writes all
 * vertices at distance ecc_A from (e,A) (both sides) as "side a b c d" lines. Build: cc -O3 -o haar_dist haar_dist.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef long long ll;
static ll q; static ll *inv;
static ll md(ll a){a%=q;return a<0?a+q:a;}
static ll idx(ll a, ll b, ll c, ll d){
  if(a){ll t=inv[a]; b=b*t%q; c=c*t%q; d=d*t%q; return (b*q+c)*q+d;}
  ll t=inv[b]; c=c*t%q; d=d*t%q; return q*q*q+c*q+d; }
static void unidx(ll i, ll *a, ll *b, ll *c, ll *d){
  if(i<q*q*q){*a=1;*d=i%q;i/=q;*c=i%q;*b=i/q;} else {i-=q*q*q;*a=0;*b=1;*d=i%q;*c=i/q;} }
int main(int argc,char**argv){
  if(argc<3){fprintf(stderr,"usage: haar_dist q targets.txt [lastlayer_out] < gens\n");return 2;}
  q=atoll(argv[1]);
  inv=malloc(sizeof(ll)*q); inv[0]=0; for(ll a=1;a<q;a++){ll r=1,b=a,e=q-2;while(e){if(e&1)r=r*b%q;b=b*b%q;e>>=1;}inv[a]=r;}
  ll M[256][4]; int k=0; ll a,b,c,d,z;
  while(k<256 && scanf("%lld %lld %lld %lld %lld",&a,&b,&c,&d,&z)==5){
    a=md(a);b=md(b);c=md(c);d=md(d); if(md(a*d-b*c)==0){fprintf(stderr,"singular generator\n");return 2;}
    M[k][0]=a;M[k][1]=b;M[k][2]=c;M[k][3]=d;k++; }
  for(int i=0;i<k;i++)for(int j=0;j<i;j++) if(idx(M[i][0],M[i][1],M[i][2],M[i][3])==idx(M[j][0],M[j][1],M[j][2],M[j][3])){printf("RESULT REPEATED %d %d\n",j,i);return 1;}
  ll T[64][4]; int nt=0; FILE*f=fopen(argv[2],"r");
  if(f){ while(nt<64 && fscanf(f,"%lld %lld %lld %lld",&T[nt][0],&T[nt][1],&T[nt][2],&T[nt][3])==4) nt++; fclose(f);}
  ll NQ=q*q*q+q*q, W=(NQ+63)/64;
  ll compPGL=q*(q*q-1);
  uint64_t *vis[2],*cur[2],*nxt[2];
  for(int s=0;s<2;s++){vis[s]=calloc(W,8);cur[s]=calloc(W,8);nxt[s]=calloc(W,8);}
  ll tidx[64]; for(int i=0;i<nt;i++) tidx[i]=idx(md(T[i][0]),md(T[i][1]),md(T[i][2]),md(T[i][3]));
  ll tdA[64], tdB[64];
  ll e=idx(1,0,0,1);
  for(int i=0;i<nt;i++){ tdA[i]=(tidx[i]==e)?0:-1; tdB[i]=-1; }
  int ecc[2]; ll comp[2];
  for(int start=0;start<2;start++){
    for(int s=0;s<2;s++){memset(vis[s],0,W*8);memset(cur[s],0,W*8);memset(nxt[s],0,W*8);}
    vis[start][e>>6]|=1ULL<<(e&63); cur[start][e>>6]|=1ULL<<(e&63);
    int side=start, step=0; ll tot=1;
    while(1){ int ns=side^1; ll add=0; memset(nxt[ns],0,W*8);
      for(ll w=0;w<W;w++){uint64_t bits=cur[side][w]; while(bits){int bt=__builtin_ctzll(bits); bits&=bits-1; ll g=w*64+bt;
        ll xa,xb,xc,xd; unidx(g,&xa,&xb,&xc,&xd);
        for(int i=0;i<k;i++){ ll A_,B_,C_,D_;
          if(side==0){A_=M[i][0];B_=M[i][1];C_=M[i][2];D_=M[i][3];}
          else {A_=M[i][3];B_=md(-M[i][1]);C_=md(-M[i][2]);D_=M[i][0];}
          ll t=idx(md(A_*xa+B_*xc),md(A_*xb+B_*xd),md(C_*xa+D_*xc),md(C_*xb+D_*xd));
          uint64_t mk=1ULL<<(t&63); if(!(vis[ns][t>>6]&mk)){vis[ns][t>>6]|=mk; nxt[ns][t>>6]|=mk; add++;} } } }
      if(!add) break;
      memset(cur[side],0,W*8); uint64_t*tt=cur[ns];cur[ns]=nxt[ns];nxt[ns]=tt; side=ns;
      step++; tot+=add;
      if(start==0){ for(int i=0;i<nt;i++){ ll ti=tidx[i];
          if(ns==0 && tdA[i]<0 && (vis[0][ti>>6]&(1ULL<<(ti&63)))) tdA[i]=step;
          if(ns==1 && tdB[i]<0 && (vis[1][ti>>6]&(1ULL<<(ti&63)))) tdB[i]=step; } }
    }
    ecc[start]=step; comp[start]=tot;
    if(start==0 && argc>3){ FILE*o=fopen(argv[3],"w");
      for(ll w=0;w<W;w++){uint64_t bits=cur[side][w]; while(bits){int bt=__builtin_ctzll(bits); bits&=bits-1; ll g=w*64+bt;
        ll xa,xb,xc,xd; unidx(g,&xa,&xb,&xc,&xd); fprintf(o,"%d %lld %lld %lld %lld\n",side,xa,xb,xc,xd);}}
      fclose(o); }
  }
  int dm = ecc[0]>ecc[1]?ecc[0]:ecc[1];
  printf("RESULT q=%lld Delta=%d ecc_A=%d ecc_B=%d compA=%lld compB=%lld compPGL=%lld diam=%d\n",
    q,k,ecc[0],ecc[1],comp[0],comp[1],compPGL,dm);
  for(int i=0;i<nt;i++) printf("TARGET %d (%lld,%lld,%lld,%lld) d_A=%lld d_B=%lld\n",i,T[i][0],T[i][1],T[i][2],T[i][3],tdA[i],tdB[i]);
  return 0;
}
