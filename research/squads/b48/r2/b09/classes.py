import sys
sys.path.insert(0,'/home/user/degree-diameter/research/squads/b48/r1/c01')
from collections import Counter
N=1100
class Meta:
    def __init__(s,m,k,r):
        s.m,s.k,s.r=m,k,r; s.N=m*k
        s.rp=[pow(r,j,m) for j in range(k)]
    def mul(s,x,y):
        a,j=x%s.m,x//s.m; b,l=y%s.m,y//s.m
        return (a+s.rp[j]*b)%s.m + s.m*((j+l)%s.k)
    def inv(s,x):
        a,j=x%s.m,x//s.m
        ri=pow(s.r,(-j)%s.k,s.m)
        return ((-ri*a)%s.m) + s.m*((-j)%s.k)
G=Meta(55,20,2)
L=open('/home/user/degree-diameter/research/squads/b48/r1/c01/best_cost1_n2200.edges').read().split()
n=int(L[0]); E=[(int(L[i]),int(L[i+1])) for i in range(1,len(L),2)]
def _main():
    cnt=Counter()
    out=[]
    for a,b in E:
        if a>=N: a,b=b,a
        x=a; y=b-N
        g=G.mul(G.inv(x),y)
        out.append((a,b+0,g))
        cnt[g]+=1
    print(len(cnt), cnt.most_common(6))
    # also check the left variant
    cnt2=Counter(G.mul(G.inv(y), x) for (a,b,g) in out for x,y in [(a,b-N)])
    print('left variant', len(cnt2))
if __name__=="__main__": _main()
