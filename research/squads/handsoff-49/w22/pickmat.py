import random, sys
p, k = int(sys.argv[1]), int(sys.argv[2]); random.seed(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
def mul(A, B):
    return ((A[0]*B[0]+A[1]*B[2])%p, (A[0]*B[1]+A[1]*B[3])%p, (A[2]*B[0]+A[3]*B[2])%p, (A[2]*B[1]+A[3]*B[3])%p)
def pw(A, e):
    R = (1, 0, 0, 1)
    for _ in range(e): R = mul(R, A)
    return R
def order_div(A, k):
    return pw(A, k) == (1, 0, 0, 1)
found = []
for _ in range(200000):
    A = tuple(random.randrange(p) for _ in range(4))
    det = (A[0]*A[3]-A[1]*A[2]) % p
    if det == 0: continue
    if A[1] == 0 and A[2] == 0 and A[0] == A[3]: continue  # scalar
    if order_div(A, k):
        found.append(A)
        break
print(" ".join(map(str, found[0])) if found else "NONE")
