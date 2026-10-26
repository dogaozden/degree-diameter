# abel.py GROUPS N: print "id abelian_flag" for every group of order N in a gap_export text file (flag 1 = abelian)
import sys
f, N = sys.argv[1], int(sys.argv[2])
L = open(f).read().split('\n'); i = 0
while i < len(L):
    if L[i].startswith('G '):
        p = L[i].split(None, 3); n = int(p[1]); gid = int(p[2])
        if n == N:
            R = [list(map(int, L[i + 1 + r].split())) for r in range(n)]
            ab = all(R[a][b] == R[b][a] for a in range(n) for b in range(a + 1, n))
            print(gid, 1 if ab else 0)
        i += 1 + n
    else:
        i += 1
