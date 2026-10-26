import sys, os, collections
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1_d8c/c2')
import flagrule as fr
fr.build(1, [0,1,2,3], [4,4+0] if False else [4,1], [[0,1,2,3],[3,2,1,0]], 'graphs/diag.txt')
lines = open('graphs/diag.txt').read().split()
n = int(lines[0]); E = list(zip(map(int, lines[1::2]), map(int, lines[2::2])))
adj = [[] for _ in range(n)]
for a, b in E: adj[a].append(b); adj[b].append(a)
for src in [0, 1456+5, 2912+3]:
    dist = [-1]*n; dist[src]=0; Q=collections.deque([src])
    while Q:
        u=Q.popleft()
        for v in adj[u]:
            if dist[v]<0: dist[v]=dist[u]+1; Q.append(v)
    print('src', src, 'deg', len(adj[src]), sorted(collections.Counter(dist).items()))
os.remove('graphs/diag.txt')
