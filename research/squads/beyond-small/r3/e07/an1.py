import pickle
H=16896
gens = pickle.load(open('gens.pkl','rb'))
def dec(w):
    side = 'A' if w < H else 'B'
    loc = w % H
    blk, y = divmod(loc, 256)
    j, h = divmod(blk, 22)
    return side, j, h, y
for k, p in enumerate(gens):
    # orders and sample images
    print('gen', k, 'fixed', sum(1 for i,x in enumerate(p) if i==x))
    # check block map: image of block (side,j,h) -> (side',j',h')
    bm = {}
    ok = True
    fib = {}
    for w in range(2*H):
        s,j,h,y = dec(w)
        s2,j2,h2,y2 = dec(p[w])
        bm.setdefault((s,j,h),set()).add((s2,j2,h2))
        fib.setdefault((s,j,h),[]).append((y, y2))
    blocks = {k2: list(v)[0] if len(v)==1 else v for k2,v in bm.items()}
    print(' block images (sample):', [ (kk, blocks[kk]) for kk in list(blocks)[:6]])
    print(' block-level image set sizes', set(len(v) for v in bm.values()))
    # distinct block images of A side
    print(' A(0,0,0) ->', blocks[('A',0,0)] if len(bm[('A',0,0)])==1 else 'multi')
    # fibre map on block 'A',0,0: check y->y2 of 256
    if len(bm[('A',0,0)])==1:
        pairs = fib[('A',0,0)]
        tb = list(bm[('A',0,0)])[0]
        print(' fibre pairs sample', pairs[:8])
