"""Prop 5.2 construction: given points R, lines F (f(R)), build a bijection sigma points->lines with (H1)-(H3)."""
import numpy as np, sys
rel = np.load('/home/user/degree-diameter/research/squads/conics2-r1/c1/rel_q5.npz')
Pc, Pd4, Lc = rel['Pc'], rel['Pd4'], rel['Lc']
N = Pc.shape[0]

def build_sigma(R, F):
    R = list(map(int, R)); F = list(map(int, F))
    sig = np.full(N, -1, np.int64)
    used_line = np.zeros(N, bool)
    for x, fx in zip(R, F):
        sig[x] = fx; used_line[fx] = True
    # mid-points of distance-4 pairs
    for i in range(len(R)):
        for j in range(i + 1, len(R)):
            x, y = R[i], R[j]
            if Pd4[x, y]:
                mids = np.nonzero(Pc[x] & Pc[y])[0]; assert len(mids) == 1
                fx, fy = F[i], F[j]
                lm = np.nonzero(Lc[fx] & Lc[fy])[0]; assert len(lm) == 1, len(lm)
                z = mids[0]; l = lm[0]
                assert sig[z] == -1 or sig[z] == l
                sig[z] = l; used_line[l] = True
    # private points of each x -> private lines of f(x) (arbitrary bijection)
    for x, fx in zip(R, F):
        pts = [p for p in np.nonzero(Pc[x])[0] if sig[p] == -1]
        lns = [l for l in np.nonzero(Lc[fx])[0] if not used_line[l]]
        assert len(pts) == len(lns), (len(pts), len(lns))
        for p, l in zip(pts, lns):
            sig[p] = l; used_line[l] = True
    # rest: arbitrary bijection
    rest_p = np.nonzero(sig == -1)[0]; rest_l = np.nonzero(~used_line)[0]
    assert len(rest_p) == len(rest_l), (len(rest_p), len(rest_l))
    sig[rest_p] = rest_l
    assert len(set(sig.tolist())) == N
    return sig

if __name__ == '__main__':
    lines = open('/home/user/degree-diameter/research/frontier/sols/d7D7_hex5_mirror81_n23598.sol').read().split('\n')
    R = [int(t) for t in lines[1].split()[1:]]
    sig_rec = np.array([int(t) for s in lines[3:] for t in s.split()], dtype=np.int64)
    F = sig_rec[R]
    sig = build_sigma(R, F)
    np.savetxt('/home/user/degree-diameter/research/squads/conics2-r1/c1/sigma_rebuild81.txt', sig, fmt='%d')
    np.savetxt('/home/user/degree-diameter/research/squads/conics2-r1/c1/R81.txt', np.array(R), fmt='%d')
    print('written; |R|=', len(R))
