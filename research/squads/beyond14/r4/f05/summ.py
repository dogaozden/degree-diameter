import sys, statistics as st
def load(fn):
    rows=[]; hdr=None
    for line in open(fn):
        if line.startswith('#'): hdr=line.strip(); continue
        f=line.split()
        rows.append(dict(cost=int(f[1]),b13=float(f[2]),e13=float(f[4]),w=int(f[5]),comp=float(f[6])))
    return hdr,rows
def q(xs,f):
    xs=sorted(xs); i=min(len(xs)-1,int(f*(len(xs)-1)+0.5)); return xs[i]
def line(name,xs): return '%s min %.0f / q25 %.0f / med %.0f / max %.0f' % (name,min(xs),q(xs,.25),q(xs,.5),max(xs))
for fn in sys.argv[1:]:
    hdr,rows=load(fn); n=int(hdr.split('n=')[1].split()[0])
    c=[r['cost'] for r in rows]
    conn=[r for r in rows if r['comp']>=n-0.5]
    print(fn, hdr.split('#')[1].strip(), '| states', len(rows))
    print('  all:', line('cost',c))
    print('  root component / n: median %.3f, fraction of states connected %.3f' % (q([r['comp']/n for r in rows],.5), len(conn)/len(rows)))
    if conn: print('  connected states only: ', line('cost',[r['cost'] for r in conn]), '(count %d)' % len(conn))
    print('  E13/n median %.3f | ball B13/n median %.3f' % (q([r['e13']/n for r in rows],.5), q([r['b13']/n for r in rows],.5)))
