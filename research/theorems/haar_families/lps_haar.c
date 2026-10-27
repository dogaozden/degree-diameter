/* lps_haar: diameter of the LPS Haar graph H(PGL(2,q) x Z_m, S) restricted to the component of (e,A), where
 * S = { (psi(alpha), c(alpha)) : alpha in S_p } and S_p is the Lubotzky-Phillips-Sarnak set of p+1 integral
 * quaternions of norm p (p odd prime), psi(a0+a1 i+a2 j+a3 k) = [[a0+a1x+a3y, -a1y+a2+a3x],[-a1y-a2+a3x, a0-a1x-a3y]]
 * with x^2+y^2 = -1 mod q (q odd prime, q != p).  Default m = 1 (c = 0).
 * Convention of HAAR_D8_10.md: (g,A) ~ (s g, B).  Elements of PGL(2,q) are normalised matrices: first row (1,b) or (0,1).
 * Output: eccentricities of (e,A) and (e,B) (Cor. 2.3 + the component argument in HAAR_FAMILIES.md), the order of the
 * component, and the distance profile.  Usage: lps_haar p q [m c_0 ... c_p]  (c_i are the Z_m labels in the order the
 * generators are printed with -v).  Build: cc -O3 -o lps_haar lps_haar.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
typedef long long ll;
static ll q, m, NG, NB; static ll *inv;
static ll md(ll a){a%=q;return a<0?a+q:a;}
static ll idx(ll a, ll b, ll c, ll d){ /* normalise and index */
  if(a){ll t=inv[a]; b=b*t%q; c=c*t%q; d=d*t%q; return (b*q+c)*q+d;}
  {ll t=inv[b]; c=c*t%q; d=d*t%q; return q*q*q + c*q + d;}
}
static void unidx(ll i, ll *a, ll *b, ll *c, ll *d){
  if(i<q*q*q){*a=1;*d=i%q;i/=q;*c=i%q;*b=i/q;} else {i-=q*q*q;*a=0;*b=1;*d=i%q;*c=i/q;}
}
int main(int argc,char**argv){
  if(argc<3){fprintf(stderr,"usage: lps_haar p q [m c...] [-v]\n");return 2;}
  ll p=atoll(argv[1]); q=atoll(argv[2]); m=1; int verbose=0;
  ll cc[256]; int nc=0;
  for(int i=3;i<argc;i++){ if(!strcmp(argv[i],"-v")) verbose=1; else if(m==1&&nc==0&&i==3) m=atoll(argv[i]); else cc[nc++]=atoll(argv[i]); }
  inv=malloc(sizeof(ll)*q); inv[0]=0; for(ll a=1;a<q;a++){ll r=1,b=a,e=q-2;while(e){if(e&1)r=r*b%q;b=b*b%q;e>>=1;}inv[a]=r;}
  ll x=-1,y=-1; for(ll a=0;a<q&&x<0;a++)for(ll b=0;b<q;b++) if((a*a+b*b+1)%q==0){x=a;y=b;break;}
  /* LPS set */
  ll G[256][4]; int k=0;
  for(ll a0=-100;a0<=100;a0++)for(ll a1=-100;a1<=100;a1++){ll r=p-a0*a0-a1*a1; if(r<0) continue;
    for(ll a2=-100;a2<=100;a2++){ll r2=r-a2*a2; if(r2<0) continue; ll a3=0; while(a3*a3<r2)a3++; if(a3*a3!=r2) continue;
      for(int sg=0;sg<2;sg++){ ll b3= sg? -a3: a3; if(sg && a3==0) continue;
        int ok;
        if(p%4==1) ok = (a0>0 && (a0&1) && !(a1&1) && !(a2&1) && !(b3&1));
        else ok = (!(a0&1) && (a1&1) && (a2&1) && (b3&1) && (a0>0 || (a0==0 && a1>0)));
        if(ok){ if(k>=256) return 3; G[k][0]=a0;G[k][1]=a1;G[k][2]=a2;G[k][3]=b3;k++; } } } }
  if(k!=p+1){fprintf(stderr,"found %d generators, expected %lld\n",k,p+1);return 2;}
  if(nc && nc!=k){fprintf(stderr,"need %d labels\n",k);return 2;}
  ll M[256][4], Z[256];
  for(int i=0;i<k;i++){ll a0=G[i][0],a1=G[i][1],a2=G[i][2],a3=G[i][3];
    M[i][0]=md(a0+a1*x+a3*y); M[i][1]=md(-a1*y+a2+a3*x); M[i][2]=md(-a1*y-a2+a3*x); M[i][3]=md(a0-a1*x-a3*y);
    Z[i]= nc? ((cc[i]%m)+m)%m : 0;
    if(verbose) printf("gen %d quat (%lld,%lld,%lld,%lld) mat(%lld,%lld,%lld,%lld) z=%lld\n",i,a0,a1,a2,a3,M[i][0],M[i][1],M[i][2],M[i][3],Z[i]); }
  /* distinctness in PGL x Z_m */
  for(int i=0;i<k;i++)for(int j=0;j<i;j++) if(idx(M[i][0],M[i][1],M[i][2],M[i][3])==idx(M[j][0],M[j][1],M[j][2],M[j][3]) && Z[i]==Z[j]){printf("REPEATED generators %d %d\n",j,i);return 1;}
  NG=q*q*q+q*q; NB=NG*m; ll W=(NB+63)/64;
  uint64_t *vis[2],*cur[2],*nxt[2]; for(int s=0;s<2;s++){vis[s]=calloc(W,8);cur[s]=calloc(W,8);nxt[s]=calloc(W,8);}
  ll e=idx(1,0,0,1)*m; ll order=q*(q*q-1)*m; /* |PGL| * m; component has |PSL|*m per side if connected */
  int ecc2[2]; ll tot2[2]; uint8_t *dist=malloc(NB); memset(dist,255,NB); dist[e]=0;
  for(int start=0;start<2;start++){
    for(int s=0;s<2;s++){memset(vis[s],0,W*8);memset(cur[s],0,W*8);}
    vis[start][e>>6]|=1ULL<<(e&63); cur[start][e>>6]|=1ULL<<(e&63);
    int side=start, step=0; ll tot=1; ll prof[200]; prof[0]=1;
    for(;;){ int ns=side^1; ll add=0; memset(nxt[ns],0,W*8);
      for(ll w=0;w<W;w++){uint64_t bits=cur[side][w]; while(bits){int bt=__builtin_ctzll(bits); bits&=bits-1; ll gidx=w*64+bt, g=gidx/m, z=gidx%m;
        ll a,b,c,d; unidx(g,&a,&b,&c,&d);
        for(int i=0;i<k;i++){ ll A_,B_,C_,D_, h;
          if(side==0){A_=M[i][0];B_=M[i][1];C_=M[i][2];D_=M[i][3]; h=(z+Z[i])%m;}
          else {A_=M[i][3];B_=md(-M[i][1]);C_=md(-M[i][2]);D_=M[i][0]; h=(z-Z[i]+m)%m;} /* adjugate = inverse in PGL */
          ll t=idx(md(A_*a+B_*c),md(A_*b+B_*d),md(C_*a+D_*c),md(C_*b+D_*d))*m+h;
          uint64_t mk=1ULL<<(t&63); if(!(vis[ns][t>>6]&mk)){vis[ns][t>>6]|=mk; nxt[ns][t>>6]|=mk; add++; if(start==0) dist[t]=step+1;} } } }
      memset(cur[side],0,W*8); uint64_t*tt=cur[ns];cur[ns]=nxt[ns];nxt[ns]=tt; side=ns;
      if(!add) break; step++; prof[step]=add; tot+=add; if(step>190) break; }
    ecc2[start]=step; tot2[start]=tot;
    if(verbose){printf("profile from (e,%c):",start?'B':'A'); for(int s=0;s<=step;s++) printf(" %lld",prof[s]); printf("\n");}
  }
  { ll ti=idx(md(x),md(-y),md(-y),md(-x))*m, tj=idx(0,1,q-1,0)*m, tk=idx(md(y),md(x),md(x),md(-y))*m; int mx=ecc2[0]; ll nmax=0;
    for(ll i=0;i<NB;i++) if(dist[i]==mx) nmax++;
    double lb = 4*log((double)q)/log((double)p) - 2*log(2.0)/log((double)p);
    printf("targets: d(e,psi(i))=%d d(e,psi(j))=%d d(e,psi(k))=%d  thmB_bound=%.2f  ecc=%d  #at_ecc=%lld  log_p|PSL|=%.2f\n",
      dist[ti]==255?-1:dist[ti], dist[tj]==255?-1:dist[tj], dist[tk]==255?-1:dist[tk], lb, mx, nmax, log((double)q*(q*q-1)/2)/log((double)p)); }
  ll lg=1,bb=p%q,ee=(q-1)/2; while(ee){if(ee&1)lg=lg*bb%q;bb=bb*bb%q;ee>>=1;}
  printf("p=%lld q=%lld m=%lld Delta=%d legendre(p/q)=%s vertices=%lld (2|PSL|m=%lld) ecc(e,A)=%d ecc(e,B)=%d diameter=%d\n",
    p,q,m,k, lg==1?"+1":"-1", tot2[0]+0*order, order, ecc2[0],ecc2[1], ecc2[0]>ecc2[1]?ecc2[0]:ecc2[1]);
  return 0;
}
