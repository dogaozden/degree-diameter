import sys, time, random
sys.argv = ['x', 'g392_5.bin', '5', '1', '1']
exec(open('bicoset.py').read().split("if __name__ == '__main__':")[0])
a = 120; b = 303
Aid, Bid, Arep, Brep, dcs = setup(a, b)
print('n', len(Arep), len(Brep), 'dcs sizes', sorted(set(len(d) for d in dcs)), 'count', [sum(1 for d in dcs if len(d)==k) for k in (2,4)])
# check double cosets sizes and class counts
t=time.time(); D = dcs[0] + dcs[1] + dcs[2]; print('D size', len(D))
M = adjacency(D + [], Arep, Bid) if False else None
import itertools
pool4 = [i for i,d in enumerate(dcs) if len(d)==4]
st = pool4[:2] + [i for i,d in enumerate(dcs) if len(d)==2][:1]
Dl = [e for c in st for e in dcs[c]]
t=time.time(); M = adjacency(Dl, Arep, Bid); print('adj time', time.time()-t)
print('row sums', set(M.sum(1).tolist()), 'col sums', set(M.sum(0).tolist()))
t=time.time(); print('cost', cost(M), 'time', time.time()-t)
