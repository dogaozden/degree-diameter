import sys, random, time
sys.argv = ['x', 'g392_41.bin', '5', '1', '1']
exec(open('bicoset.py').read().split("if __name__ == '__main__':")[0])
a,b = 6,40
Aid, Bid, Arep, Brep, dcs = setup(a, b)
p4 = [i for i,d in enumerate(dcs) if len(d)==4]; p2=[i for i,d in enumerate(dcs) if len(d)==2]
r = random.Random(4)
state = r.sample(p4,2)+r.sample(p2,1)
els=lambda st:[e for c in st for e in dcs[c]]
cur=cost(adjacency(els(state),Arep,Bid)); print('start',cur, 'state', state, 'p2', p2)
t0=time.time(); acc=0; it=0; seen=0
while time.time()-t0<8:
    it+=1
    k=r.randrange(3); pool = p4 if k<2 else p2
    c=r.choice(pool)
    if c in state: continue
    seen+=1
    new=list(state); new[k]=c
    cn=cost(adjacency(els(new),Arep,Bid))
    if cn<=cur: state,cur=new,cn; acc+=1
print('iters',it,'tried',seen,'accepted',acc,'final',cur, 'time/eval', 8/max(seen,1))
