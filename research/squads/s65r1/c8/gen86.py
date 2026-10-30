import sys
# order-86 groups: cyclic C86 and dihedral D43 (element index i + 43*j for r^i s^j)
def cyc(n):
    return n, [[(a+b)%n for b in range(n)] for a in range(n)]
def dih(k):
    m = 2*k
    def idx(a,x): return a + k*x
    T = [[0]*m for _ in range(m)]
    for a in range(k):
        for x in range(2):
            for b in range(k):
                for y in range(2):
                    c = (a + (b if x==0 else -b)) % k
                    z = (x+y) % 2
                    T[idx(a,x)][idx(b,y)] = idx(c,z)
    return m, T
which = sys.argv[1]
m, T = cyc(86) if which == 'C86' else dih(43)
with open(sys.argv[2], 'w') as f:
    f.write(f"{m}\n")
    for row in T:
        f.write(" ".join(map(str,row))+"\n")
