import pickle
HALF=16896; NV=33792
hubs,used=pickle.load(open('state_final.pkl','rb'))
src='/home/user/degree-diameter/research/squads/beyond-small/data/d16D5_n33792.edges'
L=[l for l in open(src).read().split('\n')[1:] if l.strip()]
k=len(hubs); n=NV+k
out=[str(n)]+L
for t,NB in enumerate(hubs):
    h=NV+t
    out += [f"{h} {HALF+b}" for b in NB]
fn=f'best_n{n}.edges'
open(fn,'w').write('\n'.join(out)+'\n')
print('wrote', fn, 'hubs', k)
