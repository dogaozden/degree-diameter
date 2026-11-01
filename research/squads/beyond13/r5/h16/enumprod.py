import sys, bisect
def isp(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    i = 3
    while i * i <= x:
        if x % i == 0: return False
        i += 2
    return True
lo, hi = float(sys.argv[1]), float(sys.argv[2])
metas = []
for k in [3,5,7,11,13]:
    m = 2*k+1
    while m*k <= hi:
        if isp(m):
            for g in range(2, m):
                r = pow(g, (m-1)//k, m)
                if r != 1: break
            metas.append((m*k, m, k, r))
        m += 2*k
metas.sort()
keys = [x[0] for x in metas]
out = []
for a in metas:
    if a[2] != 3 and False: pass
    blo = max(a[0], lo / a[0]); bhi = hi / a[0]
    i = bisect.bisect_left(keys, blo)
    while i < len(keys) and keys[i] <= bhi:
        b = metas[i]
        if b[0] >= a[0] and (a[2] == 3 or b[2] == 3):
            out.append((a[0]*b[0], a, b))
        i += 1
out.sort()
for N, a, b in out[:80]:
    print(N, f"meta {a[1]} {a[2]} {a[3]}", f"meta {b[1]} {b[2]} {b[3]}")
print(len(out), "candidates", len(metas), "metas")
