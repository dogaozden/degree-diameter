/* haar_ecc: eccentricities of (e,A) and (e,B) in the Haar graph H(G,S), G = Q x Z_m with Q = SL(2,q), PSL(2,q) or
 * PGL(2,q), q an odd prime.  Convention of HAAR_D8_10.md: (g,A) ~ (s g, B).  Each BFS stays in its own connected
 * component; the program reports the component orders.  If both components are all of G x {A,B} (connected graph),
 * diameter = max(ecc(e,A), ecc(e,B)) by Cor. 2.3 of HAAR_D8_10.md.  For PGL with S inside one coset of PSL, see
 * HAAR_FAMILIES.md (component argument).
 * Input (stdin): one generator per line: "a b c d z" (integers, reduced mod q and mod m).
 * Usage: haar_ecc sl|psl|pgl q m [-p] [-D Dmax]   (-p prints the distance profiles; -D stops BFS after Dmax steps)
 * Output line: "RESULT group=.. q=.. m=.. Delta=.. ecc_A=.. ecc_B=.. compA=.. compB=.. order=.. connected=yes|no diam=.."
 * Build: cc -O3 -o haar_ecc haar_ecc.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef long long ll;
static ll q, m, NQ, NI; static ll *inv; static int mode; /* 0 sl, 1 psl, 2 pgl */
static ll md(ll a){a%=q;return a<0?a+q:a;}
static ll half;
static ll idx(ll a, ll b, ll c, ll d){
  if(mode==2){ if(a){ll t=inv[a]; b=b*t%q; c=c*t%q; d=d*t%q; return (b*q+c)*q+d;} {ll t=inv[b]; c=c*t%q; d=d*t%q; return q*q*q+c*q+d;} }
  if(mode==1){ /* choose sign so that the first nonzero of (a,b) is in [1,(q-1)/2] */
    ll lead = a? a: b; if(lead>half){a=md(-a);b=md(-b);c=md(-c);d=md(-d);} }
  if(a) return (a-1)*q*q + b*q + c;
  return (mode==1? half: q-1)*q*q + (b-1)*q + d;
}
static void unidx(ll i, ll *a, ll *b, ll *c, ll *d){
  if(mode==2){ if(i<q*q*q){*a=1;*d=i%q;i/=q;*c=i%q;*b=i/q;} else {i-=q*q*q;*a=0;*b=1;*d=i%q;*c=i/q;} return; }
  ll amax = (mode==1? half: q-1);
  if(i < amax*q*q){ *a=i/(q*q)+1; ll r=i%(q*q); *b=r/q; *c=r%q; *d = (1+(*b)*(*c))%q * inv[*a] % q; }
  else { i-=amax*q*q; *a=0; *b=i/q+1; *d=i%q; *c = md(-inv[*b]); }
}
int main(int argc,char**argv){
  if(argc<4){fprintf(stderr,"usage: haar_ecc sl|psl|pgl q m [-p] [-D Dmax] < gens\n");return 2;}
  mode = !strcmp(argv[1],"sl")?0: !strcmp(argv[1],"psl")?1: !strcmp(argv[1],"pgl")?2: -1; if(mode<0) return 2;
  q=atoll(argv[2]); m=atoll(argv[3]); int prof=0, Dmax=1000;
  for(int i=4;i<argc;i++){ if(!strcmp(argv[i],"-p")) prof=1; else if(!strcmp(argv[i],"-D")&&i+1<argc) Dmax=atoi(argv[++i]); }
  for(ll t=2;t*t<=q;t++) if(q%t==0){fprintf(stderr,"q must be prime\n");return 2;}
  if(q<3){fprintf(stderr,"q must be odd\n");return 2;}
  half=(q-1)/2;
  inv=malloc(sizeof(ll)*q); inv[0]=0; for(ll a=1;a<q;a++){ll r=1,b=a,e=q-2;while(e){if(e&1)r=r*b%q;b=b*b%q;e>>=1;}inv[a]=r;}
  NQ = mode==2? q*q*q+q*q : (mode==1? q*(q*q-1)/2 : q*(q*q-1));
  ll order = (mode==1? q*(q*q-1)/2 : q*(q*q-1)) * m;
  ll M[512][4], Z[512]; int k=0; ll a,b,c,d,z;
  while(k<512 && scanf("%lld %lld %lld %lld %lld",&a,&b,&c,&d,&z)==5){
    a=md(a);b=md(b);c=md(c);d=md(d); ll det=md(a*d-b*c);
    if(mode<2 && det!=1){fprintf(stderr,"generator %d has det %lld != 1\n",k,det);return 2;}
    if(mode==2 && det==0){fprintf(stderr,"generator %d singular\n",k);return 2;}
    M[k][0]=a;M[k][1]=b;M[k][2]=c;M[k][3]=d; Z[k]=((z%m)+m)%m; k++; }
  for(int i=0;i<k;i++)for(int j=0;j<i;j++) if(idx(M[i][0],M[i][1],M[i][2],M[i][3])==idx(M[j][0],M[j][1],M[j][2],M[j][3])&&Z[i]==Z[j]){printf("RESULT REPEATED generators %d %d\n",j,i);return 1;}
  NI=NQ*m; ll W=(NI+63)/64;
  uint64_t *vis[2],*cur[2],*nxt[2]; for(int s=0;s<2;s++){vis[s]=calloc(W,8);cur[s]=calloc(W,8);nxt[s]=calloc(W,8); if(!vis[s]||!cur[s]||!nxt[s]){fprintf(stderr,"oom\n");return 2;}}
  ll e=idx(1,0,0,1)*m; int ecc[2]; ll comp[2];
  for(int start=0;start<2;start++){
    for(int s=0;s<2;s++){memset(vis[s],0,W*8);memset(cur[s],0,W*8);}
    vis[start][e>>6]|=1ULL<<(e&63); cur[start][e>>6]|=1ULL<<(e&63);
    int side=start, step=0; ll tot=1; ll pr[1100]; pr[0]=1;
    while(step<Dmax){ int ns=side^1; ll add=0; memset(nxt[ns],0,W*8);
      for(ll w=0;w<W;w++){uint64_t bits=cur[side][w]; while(bits){int bt=__builtin_ctzll(bits); bits&=bits-1; ll gi=w*64+bt, g=gi/m, zz=gi%m;
        ll xa,xb,xc,xd; unidx(g,&xa,&xb,&xc,&xd);
        for(int i=0;i<k;i++){ ll A_,B_,C_,D_,h;
          if(side==0){A_=M[i][0];B_=M[i][1];C_=M[i][2];D_=M[i][3]; h=(zz+Z[i])%m;}
          else {A_=M[i][3];B_=md(-M[i][1]);C_=md(-M[i][2]);D_=M[i][0]; h=(zz-Z[i]+m)%m;
                if(mode==0){ /* adjugate = inverse only for det 1: fine */ } }
          ll t=idx(md(A_*xa+B_*xc),md(A_*xb+B_*xd),md(C_*xa+D_*xc),md(C_*xb+D_*xd))*m+h;
          uint64_t mk=1ULL<<(t&63); if(!(vis[ns][t>>6]&mk)){vis[ns][t>>6]|=mk; nxt[ns][t>>6]|=mk; add++;} } } }
      memset(cur[side],0,W*8); uint64_t*tt=cur[ns];cur[ns]=nxt[ns];nxt[ns]=tt; side=ns;
      if(!add) break; step++; pr[step]=add; tot+=add; }
    ecc[start]=step; comp[start]=tot;
    if(prof){printf("profile (e,%c):",start?'B':'A'); for(int s=0;s<=step;s++) printf(" %lld",pr[s]); printf("\n");}
  }
  int conn = (comp[0]==2*order && comp[1]==2*order);
  int dm = ecc[0]>ecc[1]?ecc[0]:ecc[1];
  printf("RESULT group=%s q=%lld m=%lld Delta=%d ecc_A=%d ecc_B=%d compA=%lld compB=%lld order=%lld connected=%s diam=%d%s\n",
    argv[1],q,m,k,ecc[0],ecc[1],comp[0],comp[1],2*order,conn?"yes":"no",dm, (Dmax<1000 && dm>=Dmax)?" (BFS cut at Dmax)":"");
  return 0;
}
