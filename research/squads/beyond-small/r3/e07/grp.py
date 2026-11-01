import pickle, numpy as np
H=16896; NV=2*H
gens = [np.array(p, dtype=np.int64) for p in pickle.load(open('gens.pkl','rb'))]
ident = np.arange(NV, dtype=np.int64)
G = {ident.tobytes(): ident}
frontier=[ident]
while frontier:
    nf=[]
    for p in frontier:
        for s in gens:
            q = s[p]  # composition
            k = q.tobytes()
            if k not in G:
                G[k]=q; nf.append(q)
    frontier=nf
els = list(G.values())
print('group order', len(els))
pickle.dump(els, open('group.pkl','wb'))
def dec(w):
    side = 'A' if w < H else 'B'
    loc = w % H
    blk, y = divmod(loc, 256)
    j, h = divmod(blk, 22)
    return side, j, h, y
for idx,p in enumerate(els):
    bm = {}
    for w in range(0, NV, 256):  # one vertex per block-fibre sample
        s,j,h,y = dec(w)
        s2,j2,h2,y2 = dec(int(p[w]))
        bm.setdefault((s,j,h),set()).add((s2,j2,h2))
    # block level: is it a shift-only map?
    single = all(len(v)==1 for v in bm.values())
    # identify the (side, j) permutation and g shift
    perm = {}
    for (s,j,h),v in bm.items():
        (s2,j2,h2)=list(v)[0]
        perm.setdefault((s,j),set()).add((s2,j2,(h2-h)%22))
    # summary
    summ = {k: sorted(v) for k,v in perm.items() if k[1]==0}
    fixedfib = sum(1 for w in range(NV) if p[w]==w)
    print(idx, 'blockwise', single, 'fix', fixedfib, 'A-blocks j=0 ->', summ.get(('A',0)), 'B j=0 ->', summ.get(('B',0)))
