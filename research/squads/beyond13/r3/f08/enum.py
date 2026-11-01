import sys
# list odd-order Frobenius factors Z_m x|_r Z_k (m prime, k odd prime | m-1, k>=KMIN), N1=m*k
KMIN=int(sys.argv[1]); LO=int(sys.argv[2]); HI=int(sys.argv[3])
def isp(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
facs=[]
for k in range(KMIN,200):
    if not isp(k) or k%2==0: continue
    m=k+1
    while m*k<=HI:
        if m%2==1 and m*k>=LO//1 and isp(m) and (m-1)%k==0:
            facs.append((m*k,m,k))
        m+=2*k if False else k  # step: need m = 1 mod k
facs.sort()
# need m = 1 mod k: m-1 multiple of k, m prime, m odd -> m = 1 mod 2k
