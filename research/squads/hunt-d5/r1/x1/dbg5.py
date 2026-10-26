import sys, random, collections
sys.argv = ['x', 'g392_41.bin', '5', '1', '1']
exec(open('bicoset.py').read().split("if __name__ == '__main__':")[0])
r = random.Random(1)
for (a,b) in [(18,18),(6,40)]:
    Aid, Bid, Arep, Brep, dcs = setup(a, b)
    p4 = [i for i,d in enumerate(dcs) if len(d)==4]; p2=[i for i,d in enumerate(dcs) if len(d)==2]
    c=collections.Counter()
    for t in range(150):
        st = r.sample(p4,2)+r.sample(p2,1)
        Dl=[e for cc in st for e in dcs[cc]]
        c[cost(adjacency(Dl,Arep,Bid))]+=1
    print(a,b,'pools',len(p4),len(p2),'cost distribution (top):', c.most_common(6), 'min', min(c), 'max', max(c))
    print('  centre of a in G? T[a,:]==T[:,a]?', bool((T[a,:]==T[:,a]).all()), 'order of a/b', a, b)
