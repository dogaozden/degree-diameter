import sys, random
sys.argv = ['x', 'g392_5.bin', '5', '1', '1']
exec(open('bicoset.py').read().split("if __name__ == '__main__':")[0])
a = 120; b = 303
Aid, Bid, Arep, Brep, dcs = setup(a, b)
p4 = [i for i,d in enumerate(dcs) if len(d)==4]; p2=[i for i,d in enumerate(dcs) if len(d)==2]
print('p2', p2, [dcs[i] for i in p2])
r = random.Random(7)
vals=[]
for trial in range(300):
    st = r.sample(p4, 5)
    Dl=[e for c in st for e in dcs[c]]
    vals.append(cost(adjacency(Dl, Arep, Bid)))
print('Delta5-ish (5 size4 = 20 elems)', min(vals), sorted(vals)[:10], max(vals))
