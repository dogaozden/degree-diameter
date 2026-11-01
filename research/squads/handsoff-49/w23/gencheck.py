import sys, numpy as np, random
for f in sys.argv[1:]:
    raw = open(f,'rb').read()
    N = int(np.frombuffer(raw[:4], dtype=np.int32)[0])
    T = np.frombuffer(raw[4:], dtype=np.uint16).reshape(N, N).astype(np.int64)
    def closure(gens):
        seen = np.zeros(N, bool); seen[0]=True; fr=[0]
        while fr:
            nf=[]
            for x in fr:
                for g in gens:
                    y=T[x,g]
                    if not seen[y]: seen[y]=True; nf.append(y)
            fr=nf
        return int(seen.sum())
    random.seed(3); found=None
    for t in range(400):
        a,b=random.randrange(1,N),random.randrange(1,N)
        if closure([a,b])==N: found=(a,b); break
    cen = sum(1 for g in range(N) if np.array_equal(T[g],T[:,g]))
    print(f, "N", N, "2-gen pair", found, "centre", cen)
