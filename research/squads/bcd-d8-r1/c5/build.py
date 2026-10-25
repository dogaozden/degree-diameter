"""A-invariant cyclic lifts of the hexagon base: A = <tau, F> (order 93), sigma_1, sigma_2 A-equivariant,
voltages a(g e) = u^j a(e) for g = tau^i F^j (u^3 = 1 mod M). Writes bcd lift specs with aut lines for tau and F."""
import sys, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import group as G

N, H = G.N, G.H
EP, EL = G.EP, G.EL                      # (93, N) images of points / lines under each element
JEXP = np.array([j for (i, j) in G.ELEM])  # F-exponent of each element
STABP = [tuple(np.nonzero(EP[:, x] == x)[0].tolist()) for x in range(N)]   # point stabilizers
STABL = [tuple(np.nonzero(EL[:, x] == x)[0].tolist()) for x in range(N)]   # line stabilizers
LINES_OF_POINT = [set(H.plines[p].tolist()) for p in range(N)]

def equivariant_sigma(rng, forbid=None, tries=500):
    """A-equivariant bijection points -> lines: orbit of p0 matched to an orbit of l0 with stab(l0) = stab(p0);
    sigma(g p0) = g l0. No point is joined to a line through it."""
    for _ in range(tries):
        sig = -np.ones(N, dtype=np.int64); lorb_used = set(); ok = True
        for po in rng.permutation(len(G.preps)):
            p0 = int(G.preps[po]); S0 = STABP[p0]
            cands = [l for l in range(N) if STABL[l] == S0 and int(G.lorb[l]) not in lorb_used and l not in LINES_OF_POINT[p0]]
            if not cands: ok = False; break
            l0 = cands[rng.integers(len(cands))]
            lorb_used.add(int(G.lorb[l0]))
            sig[EP[:, p0]] = EL[:, l0]
        if not ok or len(set(sig.tolist())) != N: continue
        if forbid is not None and (sig == forbid).any(): continue
        return sig
    raise RuntimeError("no equivariant sigma found")

class Orbits:
    """Edge orbits under A. Edges: incidence (p, l) then sigma_j edges (p, sig_j p) (line index l)."""
    def __init__(self, sig_list):
        P = []; L = []; T = []
        for l in range(N):
            for p in H.lines[l]: P.append(int(p)); L.append(l); T.append(0)
        for jj, sig in enumerate(sig_list):
            P += list(range(N)); L += [int(x) for x in sig]; T += [1 + jj] * N
        self.P = np.array(P); self.L = np.array(L); self.T = np.array(T)
        self.E = len(P)
        key = self.T * N * N + self.P * N + self.L
        self.order = np.argsort(key); self.skey = key[self.order]
        imgP = EP[:, self.P]; imgL = EL[:, self.L]              # (93, E)
        imk = self.T[None, :] * N * N + imgP * N + imgL
        pos = np.searchsorted(self.skey, imk)
        assert (self.skey[pos] == imk).all()
        imid = self.order[pos]                                  # (93, E) edge id of g e
        self.orb = -np.ones(self.E, dtype=np.int64); self.reps = []; self.members = []; self.stabj = []
        for k in range(self.E):
            if self.orb[k] >= 0: continue
            o = len(self.reps); self.reps.append(k)
            mem = {}
            for g in range(93):
                k2 = int(imid[g, k])
                if k2 not in mem: mem[k2] = g          # first group element mapping k to k2
                self.orb[k2] = o
            self.members.append(mem)
            self.stabj.append(sorted({int(JEXP[g]) for g in range(93) if imid[g, k] == k}))
        self.nor = len(self.reps)

def allowed_values(M, u, stabj):
    return [a for a in range(M) if all(((pow(u, j, M) - 1) * a) % M == 0 for j in stabj)]

def spec_text(M, u, O, values):
    """values[o] = a(rep edge of orbit o); a(g e) = u^{j(g)} a(e)."""
    out = []
    for o in range(O.nor):
        a0 = values[o]
        for k2, g in O.members[o].items():
            out.append(f"{O.P[k2]} {N + O.L[k2]} {(pow(u, int(JEXP[g]), M) * a0) % M}")
    base_tau = np.concatenate([G.tp, N + G.tl]); base_F = np.concatenate([G.fp, N + G.fl])
    zeros = ' '.join(['0'] * (2 * N))
    return (f"bcd-lift 1\ngroup cyclic {M}\nvertices {2 * N}\nedges {len(out)}\n" + "\n".join(out) + "\n"
            f"aut 1\n{' '.join(map(str, base_tau))}\n{zeros}\n"
            f"aut {u}\n{' '.join(map(str, base_F))}\n{zeros}\nend\n")
