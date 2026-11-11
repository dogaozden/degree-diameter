import sys
tab = open('D17.tab').read().split()
h = int(tab[0]); M = [[int(tab[1+i*h+j]) for j in range(h)] for i in range(h)]
# group axioms check
ok_assoc = all(M[M[a][b]][c]==M[a][M[b][c]] for a in range(h) for b in range(h) for c in range(h))
ok_latin = all(len(set(M[a]))==h for a in range(h)) and all(len(set(M[i][a] for i in range(h)))==h for a in range(h))
print("assoc", ok_assoc, "latin", ok_latin)
N=h**3
N_ = N
print("h",h,"N",N)
