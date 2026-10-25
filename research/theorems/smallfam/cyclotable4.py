"""Delta=4 version of the fibre bound table: for each k <= KMAX and o | k (o >= 2), B(k, o) = k * max_j min_J |W_J|,
the largest N a Haar graph of any Z_p x|_r Z_k (p prime, ord r = o) of diameter D can have (cyclobound.py, FIBER).
Usage: python3 cyclotable4.py D KMAX"""
import sys
import cyclobound
cyclobound.FIBER = True
D, KMAX = int(sys.argv[1]), int(sys.argv[2])
print(f'# Delta=4 D={D}: k o B(k,o) j_max')
for k in range(2, KMAX + 1):
    for o in range(2, k + 1):
        if k % o == 0:
            B, j = cyclobound.bound(4, D, k, o)
            print(f'{k:3d} {o:3d} {B:7d} {j}', flush=True)
