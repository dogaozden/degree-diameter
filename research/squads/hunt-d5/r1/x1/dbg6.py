import sys, random, collections
sys.argv = ['x', 'g392_41.bin', '6', '1', '1']
exec(open('bicoset.py').read().split("if __name__ == '__main__':")[0])
r = random.Random(2)
for (a,b) in [(invols[0], invols[5]), (invols[3], invols[9]), (invols[7], invols[20])]:
    conj = set(T[T[:, a], INV].tolist())
    Aid, Bid, Arep, Brep, dcs = setup(a, b)
    p4 = [i for i,d in enumerate(dcs) if len(d)==4]; p2=[i for i,d in enumerate(dcs) if len(d)==2]
    vals=[]
    for t in range(100):
        st = r.sample(p4,3)
        Dl=[e for cc in st for e in dcs[cc]]
        vals.append(cost(adjacency(Dl,Arep,Bid)))
    print('a,b',a,b,'conj' if b in conj else 'nonconj','pools',len(p4),len(p2),'min',min(vals),'median',sorted(vals)[50],'max',max(vals))
