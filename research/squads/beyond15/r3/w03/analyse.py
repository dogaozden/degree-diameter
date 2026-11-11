import subprocess, re, sys, collections, os
os.chdir('/home/user/degree-diameter/research/squads/beyond15/r3/w03')
names = ['desargues','pappus','heawood','mobkan','nauru','f26a','dyck','tutte8','gray','foster','gray18','foster18']
def girth_bip(path):
    L = open(path).read().split(); n=int(L[0]); m=int(L[1])
    adj=[[] for _ in range(n)]
    for i in range(m):
        a,b=int(L[2+2*i]),int(L[3+2*i]); adj[a].append(b); adj[b].append(a)
    g=10**9
    for s in range(n):
        dist=[-1]*n; par=[-1]*n; dist[s]=0; q=collections.deque([s])
        while q:
            u=q.popleft()
            for w in adj[u]:
                if dist[w]<0: dist[w]=dist[u]+1; par[w]=u; q.append(w)
                elif par[u]!=w: g=min(g,dist[u]+dist[w]+1)
    # bipartite: 2-colouring
    col=[-1]*n; col[0]=0; q=collections.deque([0]); bip=True
    while q:
        u=q.popleft()
        for w in adj[u]:
            if col[w]<0: col[w]=1-col[u]; q.append(w)
            elif col[w]==col[u]: bip=False
    deg=set(len(a) for a in adj)
    return n, m, g, bip, deg
rows=[]
for nm in names:
    n,m,g,bip,deg=girth_bip(f'{nm}.el')
    rec={'name':nm,'V':n,'girth':g,'bip':bip,'deg':sorted(deg)}
    for D in (15,16):
        out=subprocess.run(['timeout','100','./lb2',f'{nm}.el',str(D),'1'],capture_output=True,text=True).stdout
        open(f'out_{nm}_D{D}.txt','w').write(out)
        res=re.search(r'RESULT D=\d+ nmax=(\d+) .*min_ratio_v=([\d.]+) min_avg_ratio=([\d.]+)',out)
        hdr=re.search(r'nbwalks_per_source=(\d+)',out)
        rec[f'nmax{D}']=int(res.group(1)); rec[f'rmin{D}']=float(res.group(2)); rec[f'ravg{D}']=float(res.group(3))
        rec['walks']=int(float(hdr.group(1)))
        # spread over sources
        mins=[int(x) for x in re.findall(r'minW (\d+)',out)]
        rec[f'srcspread{D}']=(min(mins),max(mins))
    rows.append(rec); print(rec, flush=True)
import json
json.dump(rows,open('table.json','w'),indent=1)
