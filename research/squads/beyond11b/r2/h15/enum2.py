import bisect
exec(open('enum.py').read().split('for lo,hi')[0])  # reuse F list
lo,hi=5506489,5800000
Ns=[f[0] for f in F]
out=[]
for a in F:
    if a[0] < 1500 or a[0] > hi//1500: continue
    for b in F:
        if b[0] < a[0]: continue
        if b[0] < 1500: continue
        N=a[0]*b[0]
        if N>hi: break
        if lo<=N: out.append((N,a[1:],b[1:]))
print("products",len(out))
for x in out[:80]: print(x)
