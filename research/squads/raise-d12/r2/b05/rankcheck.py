import random
# G = D7^5; G/[G,G] = (Z2)^5, the sign of each coordinate. Haar graph H(G,S) connected needs <s^-1 t : s,t in S> = G,
# so the span of the differences of the 5 sign vectors must be all of F2^5.
def span_dim(vecs):
    basis=[]
    for v in vecs:
        for b in basis:
            v=min(v, v^b)
        if v: basis.append(v)
    return len(basis)
random.seed(1)
hist={}
for _ in range(200000):
    S=[random.randrange(32) for _ in range(5)]   # sign vector of each of the 5 chosen elements (uniform over G/G')
    diffs=[S[i]^S[j] for i in range(5) for j in range(i+1,5)]
    d=span_dim(diffs)
    hist[d]=hist.get(d,0)+1
print("span dim of {s^-1 t} in Z2^5 over 200000 random 5-sets:", sorted(hist.items()))
# orbit-closed sets: sign vectors are cyclic shifts of v
hist2={}
for _ in range(200000):
    v=random.randrange(32)
    sh=[((v<<k)|(v>>(5-k)))&31 for k in range(5)]
    d=span_dim([sh[i]^sh[j] for i in range(5) for j in range(i+1,5)])
    hist2[d]=hist2.get(d,0)+1
print("orbit-closed (cyclic shift) span dims:", sorted(hist2.items()))
