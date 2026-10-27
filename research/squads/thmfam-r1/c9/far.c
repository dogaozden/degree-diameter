/* c9: far vertices of the LPS Haar graph H(PGL(2,q), S_p), and the quaternion (least-norm primitive gamma) explanation.
 * Usage: far p q [sample=2000] [seed=1]
 * Same LPS set, (x,y) choice and graph convention as research/theorems/haar_families/lps_haar.c (m = 1).
 * Output: summary line, then one line per listed far A-vertex: "g a b c d Nmin pureAtNmin pureNle50".
 *   Nmin = least N(gamma) over primitive integral gamma with N <= 200 and psi(gamma) = g in PGL (-1 if none);
 *   pureAtNmin = 1 if some pure (a0=0) gamma of norm Nmin maps to g; pureNle50 = 1 if some pure gamma of norm <= 50 maps to g. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef long long ll;
static ll q; static ll *inv; static ll NG;
static ll md(ll a){a%=q; return a<0?a+q:a;}
static ll idx(ll a,ll b,ll c,ll d){ /* normalised projective index; inputs in [0,q) */
  if(a){ll t=inv[a]; b=b*t%q; c=c*t%q; d=d*t%q; return (b*q+c)*q+d;}
  {ll t=inv[b]; c=c*t%q; d=d*t%q; return q*q*q+c*q+d;}
}
static void unidx(ll i,ll*a,ll*b,ll*c,ll*d){
  if(i<q*q*q){*a=1;*d=i%q;i/=q;*c=i%q;*b=i/q;} else {i-=q*q*q;*a=0;*b=1;*d=i%q;*c=i/q;}
}
static ll gcdll(ll a,ll b){if(a<0)a=-a;if(b<0)b=-b;while(b){ll t=a%b;a=b;b=t;}return a;}
int main(int argc,char**argv){
  if(argc<3){fprintf(stderr,"usage: far p q [sample] [seed]\n");return 2;}
  ll p=atoll(argv[1]); q=atoll(argv[2]);
  int sample= argc>3? atoi(argv[3]) : 2000; unsigned seed= argc>4? (unsigned)atoi(argv[4]) : 1;
  inv=malloc(sizeof(ll)*q); inv[0]=0;
  for(ll a=1;a<q;a++){ll r=1,b=a,e=q-2;while(e){if(e&1)r=r*b%q;b=b*b%q;e>>=1;}inv[a]=r;}
  ll x=-1,y=-1; for(ll a=0;a<q&&x<0;a++)for(ll b=0;b<q;b++) if((a*a+b*b+1)%q==0){x=a;y=b;break;}
  /* LPS set (copied from lps_haar.c) */
  ll G[256][4]; int k=0;
  for(ll a0=-100;a0<=100;a0++)for(ll a1=-100;a1<=100;a1++){ll r=p-a0*a0-a1*a1; if(r<0) continue;
    for(ll a2=-100;a2<=100;a2++){ll r2=r-a2*a2; if(r2<0) continue; ll a3=0; while(a3*a3<r2)a3++; if(a3*a3!=r2) continue;
      for(int sg=0;sg<2;sg++){ ll b3= sg? -a3: a3; if(sg && a3==0) continue;
        int ok;
        if(p%4==1) ok = (a0>0 && (a0&1) && !(a1&1) && !(a2&1) && !(b3&1));
        else ok = (!(a0&1) && (a1&1) && (a2&1) && (b3&1) && (a0>0 || (a0==0 && a1>0)));
        if(ok){ if(k>=256) return 3; G[k][0]=a0;G[k][1]=a1;G[k][2]=a2;G[k][3]=b3;k++; } } } }
  if(k!=p+1){fprintf(stderr,"found %d generators, expected %lld\n",k,p+1);return 2;}
  ll M[256][4];
  for(int i=0;i<k;i++){ll a0=G[i][0],a1=G[i][1],a2=G[i][2],a3=G[i][3];
    M[i][0]=md(a0+a1*x+a3*y); M[i][1]=md(-a1*y+a2+a3*x); M[i][2]=md(-a1*y-a2+a3*x); M[i][3]=md(a0-a1*x-a3*y);}
  NG=q*q*q+q*q;

  /* sanity: psi is multiplicative up to scalar (Hamilton product vs matrix product) on random quaternions */
  { int bad=0; srand(7);
    for(int t=0;t<2000;t++){ ll A[4],B[4],C[4]; for(int i=0;i<4;i++){A[i]=rand()%7-3;B[i]=rand()%7-3;}
      C[0]=A[0]*B[0]-A[1]*B[1]-A[2]*B[2]-A[3]*B[3];
      C[1]=A[0]*B[1]+A[1]*B[0]+A[2]*B[3]-A[3]*B[2];
      C[2]=A[0]*B[2]-A[1]*B[3]+A[2]*B[0]+A[3]*B[1];
      C[3]=A[0]*B[3]+A[1]*B[2]-A[2]*B[1]+A[3]*B[0];
      ll P[4],Q[4],R[4];
      ll *Ms[3]={A,B,C}; ll *Outs[3]={P,Q,R};
      for(int w=0;w<3;w++){ ll a0=Ms[w][0],a1=Ms[w][1],a2=Ms[w][2],a3=Ms[w][3];
        Outs[w][0]=md(a0+a1*x+a3*y); Outs[w][1]=md(-a1*y+a2+a3*x); Outs[w][2]=md(-a1*y-a2+a3*x); Outs[w][3]=md(a0-a1*x-a3*y); }
      ll pa[4]={P[0],P[1],P[2],P[3]}, pb[4]={Q[0],Q[1],Q[2],Q[3]}, pc[4]={R[0],R[1],R[2],R[3]};
      ll m0=md(pa[0]*pb[0]+pa[1]*pb[2]), m1=md(pa[0]*pb[1]+pa[1]*pb[3]), m2=md(pa[2]*pb[0]+pa[3]*pb[2]), m3=md(pa[2]*pb[1]+pa[3]*pb[3]);
      /* product as matrices pa*pb */
      ll pr[4]={m0,m1,m2,m3};
      ll ci=idx(pr[0],pr[1],pr[2],pr[3]), cj=idx(pc[0],pc[1],pc[2],pc[3]);
      if(ci!=cj){ bad++; }
    }
    fprintf(stderr,"homomorphism check: %d mismatches of 2000 (0 expected)\n",bad);
  }
  /* quaternion enumeration: primitive gamma with norm <= 200 */
  int *bestN=malloc(sizeof(int)*NG), *bestP=malloc(sizeof(int)*NG), *bestP50=malloc(sizeof(int)*NG);
  for(ll i=0;i<NG;i++){bestN[i]=-1;bestP[i]=-1;bestP50[i]=-1;}
  ll nq=0;
  for(ll a0=-14;a0<=14;a0++)for(ll a1=-14;a1<=14;a1++)for(ll a2=-14;a2<=14;a2++)for(ll a3=-14;a3<=14;a3++){
    ll n=a0*a0+a1*a1+a2*a2+a3*a3; if(n==0||n>200) continue;
    if(gcdll(gcdll(a0,a1),gcdll(a2,a3))!=1) continue;
    if(n%q==0) continue; /* singular: not in PGL */
    ll m0=md(a0+a1*x+a3*y), m1=md(-a1*y+a2+a3*x), m2=md(-a1*y-a2+a3*x), m3=md(a0-a1*x-a3*y);
    ll g=idx(m0,m1,m2,m3); nq++;
    if(bestN[g]<0 || n<bestN[g]) bestN[g]=(int)n;
    if(a0==0 && (bestP[g]<0 || n<bestP[g])) bestP[g]=(int)n;
    if(a0==0 && n<=50 && (bestP50[g]<0 || n<bestP50[g])) bestP50[g]=(int)n;
  }
  /* BFS from (e,A) on states (side, g): state = side*NG + g */
  ll NS=2*NG; unsigned char *dist=malloc(NS); memset(dist,255,NS);
  int *queue=malloc(sizeof(int)*NS);
  ll e=idx(1,0,0,1); ll qh=0,qt=0; dist[e]=0; queue[qt++]=(int)e;
  while(qh<qt){ int u=queue[qh++]; int side=u/NG; ll g=u%NG; ll a,b,c,d; unidx(g,&a,&b,&c,&d);
    int ns=side^1; int du=dist[u];
    for(int i=0;i<k;i++){ ll A_,B_,C_,D_;
      if(side==0){A_=M[i][0];B_=M[i][1];C_=M[i][2];D_=M[i][3];}
      else {A_=M[i][3];B_=md(-M[i][1]);C_=md(-M[i][2]);D_=M[i][0];} /* adjugate = inverse in PGL */
      ll t=idx(md(A_*a+B_*c),md(A_*b+B_*d),md(C_*a+D_*c),md(C_*b+D_*d));
      ll v=ns*NG+t;
      if(dist[v]==255){dist[v]=du+1; queue[qt++]=(int)v;}
    } }
  int ecc=0; ll nA=0;
  for(ll v=0;v<NS;v++) if(dist[v]!=255){ if(dist[v]>ecc) ecc=dist[v]; if(v<NG) nA++; }
  /* far A-vertices: dist >= ecc-1 */
  ll *far=malloc(sizeof(ll)*NG); ll nf=0;
  for(ll g=0;g<NG;g++) if(dist[g]!=255 && dist[g]>=ecc-1) far[nf++]=g;
  /* sample */
  ll nout=nf; if(nf>sample){ srand(seed); for(ll i=nf-1;i>0;i--){ ll j=((ll)rand()*RAND_MAX+rand())%(i+1); ll t=far[i];far[i]=far[j];far[j]=t; } nout=sample; }
  printf("SUMMARY p=%lld q=%lld Delta=%d legendre(p/q)=%s ecc(e,A)=%d A_vertices_in_component=%lld far_A=%lld listed=%lld gamma_norm<=200_classes=%lld\n",
    p,q,k, "-", ecc, nA, nf, nout, nq);
  for(ll s=0;s<nout;s++){ ll g=far[s]; ll a,b,c,d; unidx(g,&a,&b,&c,&d);
    printf("%lld %lld %lld %lld %lld %d %d %d dist=%d\n", a,b,c,d, g, bestN[g], (bestN[g]>=0 && bestP[g]==bestN[g])?1:0,
      bestP50[g]>=0?1:0, dist[g]); }
  return 0;
}
