import sys, random, math
def groups(n):
    out=[]
    for K in range(2,n+1):
        if n%K: continue
        M=n//K
        if M<2: continue
        for R in range(2,M):
            if math.gcd(R,M)==1 and pow(R,K,M)==1 and R!=1:
                out.append((M,K,R))
    return out
if __name__=="__main__":
    n=int(sys.argv[1])
    for g in groups(n): print(*g)
