import sys, random
gf, DEL, nsamp, NINV = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
sys.argv = ['x', gf, str(DEL), '1', '1']
exec(open('bicoset.py').read().split("if __name__ == '__main__':")[0])
r = random.Random(11)
res = []
seen_pairs = set()
for a in invols[:NINV]:
    conj = sorted(set(T[T[:, a], INV].tolist()))
    for b in [a] + r.sample(conj, min(2, len(conj))):
        if (a, b) in seen_pairs: continue
        seen_pairs.add((a, b))
        Aid, Bid, Arep, Brep, dcs = setup(a, b)
        p4 = [i for i,d in enumerate(dcs) if len(d)==4]; p2=[i for i,d in enumerate(dcs) if len(d)==2]
        n4, n2 = DEL - 2*(DEL//2) + 0, 0
        best = None
        for n4 in range(0, DEL//2+1):
            n2 = DEL - 2*n4
            if len(p4) < n4 or len(p2) < n2: continue
            bb = 10**9
            for _ in range(nsamp):
                st = r.sample(p4, n4) + r.sample(p2, n2)
                Dl = [e for c in st for e in dcs[c]]
                bb = min(bb, cost(adjacency(Dl, Arep, Bid)))
            res.append((bb, a, b, n4, n2, len(p4), len(p2)))
res.sort()
for x in res[:12]: print('cost', x[0], 'a', x[1], 'b', x[2], 'type', x[3], x[4], 'pools', x[5], x[6])
print('num', len(res))
