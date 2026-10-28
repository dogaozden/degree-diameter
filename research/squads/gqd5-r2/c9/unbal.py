import sys
delta = int(sys.argv[1]) if len(sys.argv) > 1 else 8
rects = []
for s in [2,3,4,5,7,8,9]:
    if s+1 <= delta:
        N = s*s+s+1; rects.append((N, N*(delta-s)))
for q in [2,3,4,5]:
    if q+1 <= delta:
        N = (q+1)*(q*q+1); rects.append((N, N+(q+1)*(delta-q-1)))
def covered(a, b):
    lo, hi = min(a,b), max(a,b)
    return any(l <= lo and hi <= h for l, h in rects)
M = 6
while all(covered(a,b) for a in range(7,M+2) for b in range(7,M+2)):
    M += 1
print("delta", delta, "all (KA,KB) with 7<=KA,KB<=%d covered by windows; first failing square size %d" % (M, M+1))
# largest rectangle-covered balanced/unbalanced sample
print("example uncovered pairs:", [(a,b) for a in range(7,M+3) for b in range(7,M+3) if not covered(a,b)][:6])
