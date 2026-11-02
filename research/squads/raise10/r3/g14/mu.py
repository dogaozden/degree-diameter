import math, sys
# size law: W = d * sum_{i<k} (d-1)^(2i) for D = 2k (even D); mu = N exp(-W/N)
def mu(N, d, D):
    k = D // 2
    W = d * sum((d - 1) ** (2 * i) for i in range(k))
    return N * math.exp(-W / N), W
for N, d, D in [(48756,5,10),(48864,5,10),(48909,5,10),(48888,5,10),(48408,5,10),(48141,5,10),(47949,5,10),(262277,6,10),(262525,6,10),(262764,6,10),(263232,6,10),(265776,6,10),(265749,6,10)]:
    m, W = mu(N, d, D); print("N=%d d=%d D=%d W=%d mu=%.1f" % (N, d, D, W, m))
