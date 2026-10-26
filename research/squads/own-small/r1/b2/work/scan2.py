import glob, os
src=open('s6scan.py').read().split('out=[]')[0]
exec(src)
res=[]
for f in sorted(glob.glob('/home/user/degree-diameter/research/squads/own-small/r1/b2/cens/Sparse6/*.s6')):
    for li,line in enumerate(open(f)):
        s=line.strip()
        if not s.startswith(':'): continue
        n0=ord(s[1])-63
        if n0>62: continue   # big n: skip (n<=62 only in short form)
        if n0>64: continue
        nn,E=decode(line)
        if nn>64: continue
        bip,diam=info(nn,E)
        base=os.path.basename(f)[:-4]
        res.append((nn,base,li,len(E),bip,diam,s))
for r in sorted(res):
    if r[4]: print(r[0],r[1],r[2],'bip diam',r[5], 'edges',r[3])
print('nonbip count', sum(1 for r in res if not r[4]), 'total <=64', len(res))
