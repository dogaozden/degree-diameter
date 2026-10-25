/* Independent check: is there S in Z_n, |S|=k, n=k^2-k-1, with S-S covering Z_n\{0}?
   Ordered differences k(k-1) = (n-1)+2, so exactly one pair +-d is covered twice (excess 2).
   1 is in S-S, so translate: 0,1 in S. Elements chosen in increasing order; prune on excess > 2. */
#include <stdio.h>
#include <stdlib.h>
int n,k,S[32],cnt[1024],ex=0; long sols=0,nodes=0;
void rec(int m,int last){
  nodes++;
  if(m==k){ if(ex==2){ sols++; if(sols<=3){for(int i=0;i<k;i++)printf("%d ",S[i]);printf("\n");} } return; }
  for(int s=last+1;s<=n-(k-m);s++){
    int add=0,i;
    for(i=0;i<m;i++){int d=(s-S[i])%n; if(cnt[d]++) add++; if(cnt[n-d]++) add++;}
    if(ex+add<=2){ ex+=add; S[m]=s; rec(m+1,s); ex-=add; }
    for(i=0;i<m;i++){int d=(s-S[i])%n; cnt[d]--; cnt[n-d]--;}
  }
}
int main(int c,char**v){k=atoi(v[1]);n=k*k-k-1;S[0]=0;S[1]=1;cnt[1]=1;cnt[n-1]=1;rec(2,1);
  printf("k=%d n=%d solutions(with 0,1 in S)=%ld nodes=%ld\n",k,n,sols,nodes);}
