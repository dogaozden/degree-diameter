# independent check: hop distance in the full incidence graph (BFS from each point of a sample) for equivariant hops
import sys, runpy, random
sys.argv = ['zlift.py', '4', '8', '1', '/tmp/unused_c8.txt', 'none']
ns = runpy.run_path('/home/user/degree-diameter/research/squads/r3-d8/c8/zlift.py', run_name='zlift_mod')
import collections
N = ns['N']; t1 = ns['t1']; t2 = ns['t2']; adjP = ns['adjP']; adjL = ns['adjL']
def bfs_dist_pt_line(x0):
    dist = {('p', x0): 0}; fr = [('p', x0)]; d = 0
    while fr:
        d += 1; nf = []
        for typ, v in fr:
            nb = [('l', k) for k in adjP[v]] if typ == 'p' else [('p', p) for p in adjL[v]]
            for nd in nb:
                if nd not in dist: dist[nd] = d; nf.append(nd)
        fr = nf
    return dist
rng = random.Random(5)
cnt1 = collections.Counter(); cnt2 = collections.Counter()
for x in rng.sample(range(N), 60):
    dist = bfs_dist_pt_line(x)
    cnt1[dist[('l', int(t1[x]))]] += 1; cnt2[dist[('l', int(t2[x]))]] += 1
print('sampled true distances point->hop line, matching1:', dict(cnt1), 'matching2:', dict(cnt2))
