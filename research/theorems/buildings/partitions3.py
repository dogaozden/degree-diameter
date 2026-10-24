"""§2.1 of BUILDINGS.md pushed to rank 20 for A_n, B_n, D_n (and all exceptional types).
By the reduction lemma of §2.1 a tight splitting J1 | J2 (gap = 0) needs
  (1) a1 = a2 = a, where a_J = number of positive roots supported in J (= length of the longest element of W_J),
  (2) a divides N,
  (3) every node of J1 has a neighbour in J2 and vice versa (else w_J1 w_J2 w_J1 is not reduced).
Splittings passing (1)-(3) get the exact diameter from Demazure products (partitions2.py method) and their gap.
Prints, per type: #splittings, #passing (1)-(3), and the tight ones."""
import sys, itertools
import numpy as np
sys.path.insert(0, '.')
from weyl_dist import cartan
from partitions2 import setup, matmul

def analyse(t, n):
    C, S, pos, act = setup(t, n); N = len(pos)
    supp = np.array([sum(1 << i for i in range(n) if v[i] != 0) for v in pos], dtype=np.int64)
    adj = [sum(1 << j for j in range(n) if j != i and C[i][j] != 0) for i in range(n)]
    full = (1 << n) - 1
    cands = []; total = 0
    for J1 in range(1, full):
        J2 = full ^ J1
        if J1 > J2: continue
        total += 1
        a1 = int(np.count_nonzero((supp & ~J1) == 0)); a2 = int(np.count_nonzero((supp & ~J2) == 0))
        if a1 != a2 or N % a1: continue
        if any((J1 >> i & 1) and not (adj[i] & J2) for i in range(n)): continue
        if any((J2 >> i & 1) and not (adj[i] & J1) for i in range(n)): continue
        cands.append((J1, J2, a1))
    I = [[1 if r == c else 0 for c in range(n)] for r in range(n)]
    def col(M, s): return [M[r][s] for r in range(n)]
    def length(M):
        return sum(1 for v in pos if all(x <= 0 for x in act(M, v)))
    def longest_word(J):
        M = I; word = []
        while True:
            for s in J:
                if all(x >= 0 for x in col(M, s)): M = matmul(M, S[s]); word.append(s); break
            else: return word
    def demazure(M, word):
        for s in word:
            if all(x >= 0 for x in col(M, s)): M = matmul(M, S[s])
        return M
    tight = []
    for J1m, J2m, a in cands:
        J1 = [i for i in range(n) if J1m >> i & 1]; J2 = [i for i in range(n) if J2m >> i & 1]
        words = {0: longest_word(J1), 1: longest_word(J2)}
        ecc = []
        for start in (0, 1):
            M = I; m = 0
            while True:
                m += 1; M = demazure(M, words[(start + m - 1) % 2])
                if length(M) == N: break
            ecc.append(m)
        D = max(ecc); gap = a * (D - 1) - (N - a)
        is_colour = all(C[i][j] == 0 for J in (J1, J2) for i in J for j in J if i != j)
        if gap == 0: tight.append((tuple(J1), tuple(J2), a, D, is_colour))
    return N, total, len(cands), tight

if __name__ == '__main__':
    rmax = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    types = [(t, n) for n in range(2, rmax + 1) for t in 'AB'] + [('D', n) for n in range(4, rmax + 1)] \
            + [('E', 6), ('E', 7), ('E', 8), ('F', 4), ('G', 2)]
    allgood = True
    for t, n in types:
        N, total, nc, tight = analyse(t, n)
        ok = all(c for *_, c in tight)
        allgood &= ok
        print(f"{t}{n}: N={N}; {total} splittings, {nc} pass the necessary conditions (1)-(3); tight: "
              + (", ".join(f"{J1}|{J2} (a={a}, D={D}{', colour classes' if c else ', NOT colour'})" for J1, J2, a, D, c in tight) or "none"),
              flush=True)
    print("only colour classes are tight" if allgood else "A NON-COLOUR TIGHT SPLITTING EXISTS")
