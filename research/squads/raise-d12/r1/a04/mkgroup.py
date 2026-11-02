# Writes salift_s group tables: "GROUP N gid name" then N*N products mul[a*N+b], identity = index 0.
# Groups: (Z_m x|_r Z_k) x Z_t, element (i,j,s) -> index (i*k + j)*t + s; product (i,j,s)(i',j',s') = (i + r^j i' mod m, j + j' mod k, s + s' mod t).
import sys, itertools, random
def table(m, k, r, t=1):
    N = m*k*t
    rp = [pow(r, j, m) for j in range(k)]
    def idx(i, j, s): return (i*k + j)*t + s
    el = [(i, j, s) for i in range(m) for j in range(k) for s in range(t)]
    mul = [0]*(N*N)
    for a, (i, j, s) in enumerate(el):
        for b, (i2, j2, s2) in enumerate(el):
            mul[a*N + b] = idx((i + rp[j]*i2) % m, (j + j2) % k, (s + s2) % t)
    return N, mul
def check(N, mul, trials=3000):
    assert all(mul[0*N+b] == b and mul[b*N+0] == b for b in range(N))
    for _ in range(trials):
        a, b, c = (random.randrange(N) for _ in range(3))
        assert mul[mul[a*N+b]*N+c] == mul[a*N+mul[b*N+c]], "assoc"
    assert len({mul[a*N+b] for b in range(N)}) == N
def write(path, gid, name, N, mul):
    with open(path, 'w') as f:
        f.write(f"GROUP {N} {gid} {name}\n")
        for a in range(N):
            f.write(" ".join(map(str, mul[a*N:(a+1)*N])) + "\n")
if __name__ == "__main__":
    # usage: mkgroup.py m k r t OUT [gid]
    m, k, r, t = map(int, sys.argv[1:5]); out = sys.argv[5]; gid = int(sys.argv[6]) if len(sys.argv) > 6 else 1
    N, mul = table(m, k, r, t); check(N, mul)
    write(out, gid, f"Z{m}x|{r}Z{k}xZ{t}", N, mul)
    print(N)
