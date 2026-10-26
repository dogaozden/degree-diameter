import itertools
def write(name, b, edges):
    with open(name, 'w') as f:
        f.write(f"{b} {len(edges)}\n")
        for u, v in edges: f.write(f"{u} {v}\n")
def matching_edges(k, perms, off):
    return [(i, off + p[i]) for p in perms for i in range(k)]
def K(k, off):
    return [(i, off + j) for i in range(k) for j in range(k)]
# 3+3: K33 + 4 perfect matchings (perms of {0,1,2}, A = 0..2, B = 3..5)
idp=(0,1,2); c=(1,2,0); c2=(2,0,1); t1=(1,0,2); t2=(0,2,1); t3=(2,1,0)
write('base33_Q1.txt', 6, K(3,3)+matching_edges(3,[idp,idp,c,c],3))
write('base33_Q2.txt', 6, K(3,3)+matching_edges(3,[idp,c,c2,t1],3))
write('base33_Q3.txt', 6, K(3,3)+matching_edges(3,[t1,t2,t3,idp],3))
# 2+2: m11=m22=a, m12=m21=7-a
for a in (1,2,3):
    e=[(0,2)]*a+[(1,3)]*a+[(0,3)]*(7-a)+[(1,2)]*(7-a)
    write(f'base22_a{a}.txt', 4, e)
# 4+4: K44 + 3 perfect matchings (A=0..3, B=4..7)
i4=(0,1,2,3); k1=(1,0,3,2); k2=(2,3,0,1); cy=(1,2,3,0); cy2=(2,3,0,1); cy3=(3,0,1,2)
write('base44_P1.txt', 8, K(4,4)+matching_edges(4,[i4,k1,k2],4))
write('base44_P2.txt', 8, K(4,4)+matching_edges(4,[cy,cy2,cy3],4))
