import os
D = "/home/user/degree-diameter/research/squads/b48/r5/k04/bases"
def w(name, b, edges):
    with open(os.path.join(D, name + ".txt"), "w") as f:
        f.write(f"{b} {len(edges)}\n")
        for u, v in edges: f.write(f"{u} {v}\n")
w("k4", 4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)])
w("prism3", 6, [(0,1),(1,2),(2,0),(3,4),(4,5),(5,3),(0,3),(1,4),(2,5)])
w("petersen", 10, [(i,(i+1)%5) for i in range(5)] + [(5+i,5+(i+2)%5) for i in range(5)] + [(i,i+5) for i in range(5)])
def circ(n, a):
    E = [(i,(i+a)%n) for i in range(n)] + [(i,i+n//2) for i in range(n//2)]
    return E
for n in range(8,17,2):
    for a in range(1, n//2):
        if a == n//2: continue
        # skip duplicates by a<->n-a only (a < n/2 already); keep all distinct
        if n % 2 == 0 and 2*a == n: continue
        w(f"c{n}_{a}", n, circ(n, a))
