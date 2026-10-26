import glob, os
from collections import deque
src=open('/home/user/degree-diameter/research/squads/own-small/r1/b2/work/s6scan.py').read().split('out=[]')[0]
exec(src)
os.makedirs('/home/user/degree-diameter/research/squads/own-small/r1/b2/bases', exist_ok=True)
for f in sorted(glob.glob('/home/user/degree-diameter/research/squads/own-small/r1/b2/cens/Sparse6/*.s6')):
    for li,line in enumerate(open(f)):
        s=line.strip()
        if not s.startswith(':'): continue
        d=[ord(c)-63 for c in s[1:5]]+[0]*3
        n0=d[0] if d[0]<=62 else (d[1]<<12)|(d[2]<<6)|d[3]
        if n0>64 or n0 in (6,8): continue
        nn,E=decode(line)
        bip,diam=info(nn,E)
        if not bip: continue
        adj=[[] for _ in range(nn)]
        for a,b in E: adj[a].append(b); adj[b].append(a)
        col=[-1]*nn; col[0]=0; q=deque([0])
        while q:
            u=q.popleft()
            for w in adj[u]:
                if col[w]<0: col[w]=1-col[u]; q.append(w)
        Ed=[(a,b) if col[a]==0 else (b,a) for a,b in E]
        nm=f"B{nn}_{os.path.basename(f)[:-4]}_{li}"
        with open(f"/home/user/degree-diameter/research/squads/own-small/r1/b2/bases/{nm}.txt","w") as o:
            o.write(f"{nn} {len(Ed)}\n")
            for a,b in sorted(Ed): o.write(f"{a} {b}\n")
        print(nm, nn, diam)
