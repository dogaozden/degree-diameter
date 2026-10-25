# c2: greedy extension of a pairwise-opposite id set by any hex points opposite to all members (B != 0 on standard coords)
import numpy as np, sys, struct
HEX = '/home/user/degree-diameter/research/d10D7/hex/hex_q8.bin'
def load_P():
    with open(HEX, 'rb') as f:
        q, N, L = struct.unpack('3i', f.read(12)); f.seek(12 + 4 * N * (q + 1))
        return np.frombuffer(f.read(7 * N), dtype=np.uint8).reshape(N, 7).astype(np.int64)
def B(X, Y):  # X: (a,7), Y: (b,7) -> (a,b) bool, polar form nonzero (char 2, GF(8) mult via table)
    return None
if __name__ == '__main__':
    P = load_P(); N = P.shape[0]
    # GF(8) mult table with x^3 = x+1 (element = a0+2a1+4a2)
    def hm(a, b):
        r = 0
        for i in range(3):
            if (b >> i) & 1: r ^= a << i
        for i in (4, 3):
            if (r >> i) & 1: r ^= 0b1011 << (i - 3)
        return r
    MT = np.array([[hm(a, b) for b in range(8)] for a in range(8)], dtype=np.int64)
    def pairing(i_ids, j_ids):
        a = P[i_ids]; b = P[j_ids]
        return MT[a[:, 0][:, None], b[:, 4][None, :]] ^ MT[a[:, 4][:, None], b[:, 0][None, :]] ^ MT[a[:, 1][:, None], b[:, 5][None, :]] ^ MT[a[:, 5][:, None], b[:, 1][None, :]] ^ MT[a[:, 2][:, None], b[:, 6][None, :]] ^ MT[a[:, 6][:, None], b[:, 2][None, :]]
    ids = [int(x) for x in open(sys.argv[1]).read().split()]
    allids = np.arange(N)
    ok = np.ones(N, dtype=bool)
    M = pairing(allids, np.array(ids)) != 0          # (N, |S|)
    ok = M.all(axis=1)
    ok[ids] = False
    print('members', len(ids), 'candidates opposite to all members:', int(ok.sum()))
    # greedy add (random order) until none left
    rng = np.random.default_rng(int(sys.argv[3]) if len(sys.argv) > 3 else 0)
    S = list(ids)
    cand = np.nonzero(ok)[0]
    while len(cand):
        c = int(rng.choice(cand)); S.append(c)
        cand = cand[(pairing(cand, np.array([c]))[:, 0] != 0) & (cand != c)]
    print('extended size', len(S))
    open(sys.argv[2], 'w').write(' '.join(map(str, sorted(S))) + '\n')
