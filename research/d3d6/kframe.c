/* SA for k gadget frames in a projective plane: loads <= 2 on every point and line (Delta = q+3).
   Frame: A, ell (A not on ell), X[4] on ell. Point-load set: ell and lines A X_s. Line-load set: lines through A or X_s.
   Usage: kframe plane.txt k seconds seed out.txt */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
int n, K1, k; int *lp_, *th; int *LT; int *on;  /* on[p*n+j] incidence */
unsigned long long rs; static inline unsigned long long rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
double ur(void){ return (rnd()>>11)*(1.0/9007199254740992.0); }
typedef struct { int A, ell, m, X[4]; } F;
int MS[16];
int *lp, *ll;
void apply(F *f, int s){
    static int mark[1000]; static int stamp=0; stamp++;
    int i,t;
    /* points */
    if(f->m<=2) mark[f->A]=stamp;  /* small gadgets do not load A */
    for(i=0;i<K1;i++){ int p=lp_[f->ell*K1+i]; if(mark[p]!=stamp){mark[p]=stamp; lp[p]+=s;} }
    for(t=0;t<f->m;t++){ int L=LT[f->A*n+f->X[t]]; for(i=0;i<K1;i++){ int p=lp_[L*K1+i]; if(mark[p]!=stamp){mark[p]=stamp; lp[p]+=s;} } }
    stamp++;
    if(f->m<=2) mark[f->ell]=stamp;  /* small gadgets do not load ell */
    for(i=0;i<K1;i++){ int L=th[f->A*K1+i]; if(mark[L]!=stamp){mark[L]=stamp; ll[L]+=s;} }
    for(t=0;t<f->m;t++) for(i=0;i<K1;i++){ int L=th[f->X[t]*K1+i]; if(mark[L]!=stamp){mark[L]=stamp; ll[L]+=s;} }
}
int cost(F *fr){
    int c=0,i,g,h,t,u;
    for(i=0;i<n;i++){ if(lp[i]>2)c+=lp[i]-2; if(ll[i]>2)c+=ll[i]-2; }
    for(g=0;g<k;g++) for(h=g+1;h<k;h++){
        int a[5]={fr[g].A,fr[g].X[0],fr[g].X[1],fr[g].X[2],fr[g].X[3]}, b[5]={fr[h].A,fr[h].X[0],fr[h].X[1],fr[h].X[2],fr[h].X[3]};
        for(t=0;t<=fr[g].m;t++) for(u=0;u<=fr[h].m;u++) if(a[t]==b[u]) c+=3;
    }
    return c;
}
void randframe(F *f){
    f->ell = rnd()%n; do f->A = rnd()%n; while(on[f->A*n+f->ell]);
    int idx[64], i; for(i=0;i<K1;i++) idx[i]=i;
    for(i=0;i<f->m;i++){ int j=i+rnd()%(K1-i); int t=idx[i]; idx[i]=idx[j]; idx[j]=t; f->X[i]=lp_[f->ell*K1+idx[i]]; }
}
void mutate(F *f){
    double r=ur(); int i;
    if(r<0.5){ int p; again: p=lp_[f->ell*K1+rnd()%K1]; for(i=0;i<f->m;i++) if(f->X[i]==p) goto again; f->X[rnd()%f->m]=p; }
    else if(r<0.8){ do f->A=rnd()%n; while(on[f->A*n+f->ell]); }
    else if(r<0.9){ /* move ell through one X, keep X? re-random */ randframe(f); }
    else { /* rotate: new A on a line through old A */ int L=th[f->A*K1+rnd()%K1]; int p; do p=lp_[L*K1+rnd()%K1]; while(on[p*n+f->ell]); f->A=p; }
}
int main(int argc,char**argv){
    FILE*fp=fopen(argv[1],"r"); fscanf(fp,"%d %d",&n,&K1); { char*q2=argv[2]; k=0; while(*q2){ MS[k++]=*q2-'0'; q2++; if(*q2==',')q2++; } } double secs=atof(argv[3]); rs=0x9E3779B97F4A7C15ULL*(atoll(argv[4])+1);
    lp_=malloc(sizeof(int)*n*K1); th=malloc(sizeof(int)*n*K1); on=calloc(n*n,sizeof(int)); LT=malloc(sizeof(int)*n*n);
    int *cnt=calloc(n,sizeof(int)),i,j,a,b;
    for(i=0;i<n;i++) for(j=0;j<K1;j++){ int p; fscanf(fp,"%d",&p); lp_[i*K1+j]=p; on[p*n+i]=1; th[p*K1+cnt[p]++]=i; }
    for(i=0;i<n;i++) for(a=0;a<K1;a++) for(b=0;b<K1;b++) if(a!=b) LT[lp_[i*K1+a]*n+lp_[i*K1+b]]=i;
    lp=calloc(n,sizeof(int)); ll=calloc(n,sizeof(int));
    F fr[16]; clock_t t0=clock(); int bestc=1<<30; long restarts=0;
    while((double)(clock()-t0)/CLOCKS_PER_SEC < secs){
        memset(lp,0,sizeof(int)*n); memset(ll,0,sizeof(int)*n);
        for(i=0;i<k;i++){ fr[i].m=MS[i]; fr[i].X[3]=-1; randframe(&fr[i]); apply(&fr[i],1); }
        int c=cost(fr); long it, iters=3000000;
        for(it=0;it<iters && c>0;it++){
            double T=1.2*(1.0-(double)it/iters)+0.08;
            int g=rnd()%k; F old=fr[g]; apply(&fr[g],-1); mutate(&fr[g]); apply(&fr[g],1);
            int c2=cost(fr);
            if(c2<=c || ur()<exp((c-c2)/T)) c=c2; else { apply(&fr[g],-1); fr[g]=old; apply(&fr[g],1); }
        }
        restarts++;
        if(c<bestc){ bestc=c; fprintf(stderr,"restart %ld: cost %d\n",restarts,c);
            FILE*o=fopen(argv[5],"w"); for(i=0;i<k;i++){ int t; fprintf(o,"%d %d",fr[i].A,fr[i].ell); for(t=0;t<fr[i].m;t++) fprintf(o," %d",fr[i].X[t]); fprintf(o,"\n"); } fclose(o); }
        if(c==0){
            FILE*o=fopen(argv[5],"w"); for(i=0;i<k;i++) { int t; fprintf(o,"%d %d",fr[i].A,fr[i].ell); for(t=0;t<fr[i].m;t++) fprintf(o," %d",fr[i].X[t]); fprintf(o,"\n"); } fclose(o);
            printf("found\n"); return 0;
        }
    }
    printf("none best %d\n",bestc); return 0;
}
