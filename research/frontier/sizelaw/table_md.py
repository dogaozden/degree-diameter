import json, math
from data import *
P=json.load(open('pred.json'))
a,b,sd=4.335,-0.123,0.196
def Npred(d,D,shift=0.0):
    w=W(d,D); lo,hi=10.0,float(w)
    for _ in range(200):
        m=(lo+hi)/2
        if math.log(m)-w/m < a+b*math.log(m)+shift: lo=m
        else: hi=m
    return lo
rows=[]
for o in P:
    d,D,t,ours=o['d'],o['D'],o['table'],o['ours']
    nh=Nh(d,D); n=Npred(d,D); lo=Npred(d,D,-2*sd); hi=Npred(d,D,2*sd)
    valid = n < 0.95*nh
    if t is None: verdict='table value unreadable'; gain=None
    else:
        gain=2*n/t-1
        if not valid: verdict='small-N: model not valid'
        elif 2*lo>t: verdict='Haar should beat it'
        elif 2*hi<t: verdict="Haar can't (with current search)"
        else: verdict='marginal'
    if ours and t and ours>t: verdict += '; ours'
    rows.append((d,D,t,ours,2*int(n),2*int(lo),2*int(hi),2*int(nh),gain,verdict, None if t is None else t/(2*nh)))
with open('pred_table.md','w') as f:
    for D in (5,7,8,9,10):
        f.write('\n**D = %d**\n\n| Δ | table | ours | predicted Haar 2N [±2σ] | ceiling 2N_h | pred vs table | table/2N_h | verdict |\n|---|---|---|---|---|---|---|---|\n'%D)
        for r in rows:
            if r[1]!=D: continue
            d,D_,t,ours,n,lo,hi,nh,g,v,tc=r
            f.write('| %d | %s | %s | %s [%s–%s] | %s | %s | %s | %s |\n'%(d,'{:,}'.format(t) if t else 'unreadable','{:,}'.format(ours) if ours else '–','{:,}'.format(n),'{:,}'.format(lo),'{:,}'.format(hi),'{:,}'.format(nh),'–' if g is None else '%+.1f%%'%(100*g),'–' if tc is None else '%.2f'%tc,v))
print(open('pred_table.md').read())
rank=[r for r in rows if r[8] is not None and 'valid' not in r[9]]
rank.sort(key=lambda r:-r[8])
print('RANK'); [print(r[0],r[1],'%+.1f%%'%(100*r[8]),r[9]) for r in rank]
