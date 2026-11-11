import sys, math
sys.path.insert(0, '/home/user/degree-diameter/research/frontier/beyond13/meta')
def W(d, D):
    return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
def isp(x):
    if x < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if x % p == 0: return x == p
    dd, s = x - 1, 0
    while dd % 2 == 0: dd //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        y = pow(a, dd, x)
        if y in (1, x-1): continue
        for _ in range(s-1):
            y = y*y % x
            if y == x-1: break
        else: return False
    return True
d, D, lo, hi = 4, 14, 245100, 252000
w = W(d, D)
out = []
for k in range(13, 62, 2):
    if not isp(k) and k not in (15,21,25,27,33,35,39,45,49,51,55,57,59,61): pass
    m = lo // k
    while m*k <= hi:
        if m*k >= lo and m % 2 == 1 and isp(m) and (m-1) % k == 0:
            # r of order k
            g = 2
            while True:
                r = pow(g, (m-1)//k, m)
                if r != 1: break
                g += 1
            N = m*k
            out.append((N*math.exp(-w/N), N, m, k, r))
        m += 1
out.sort()
for mu, N, m, k, r in out[:60]:
    print(f"{m} {k} {r} {N} mu={mu:.2f}")
print(len(out), "candidates")
