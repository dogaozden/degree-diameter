#!/usr/bin/env python3
"""hd5_masks.py: pairing masks and protect lists for the relaxed friendly sets of the five-level typed construction
(types HDHDH, research/squads/cells/d16D7.md; relaxed surgery research/d15D7b/RELAXED.md; mirrored surgery on the four
non-friendly transitions, research/theorems/MIRRORED_SURGERY.md). Job d7-family, 2026-10-25.
Friendly sets (state dir files): P01 P23 P41 (points freed at 0->1, 2->3, 4->1), L12 L34 L30 (lines freed at 1->2,
3->4, 3->0); Rp.txt / sigma.txt = the mirrored set R' and the bijection sigma (R' points are A-slots at levels 0, 2, 4 and
B-slots at level 3; sigma(R') lines are B-slots at levels 0, 2, 4 and A-slots at level 1).
A pair {r, x} in set S needs, for each ordered version (r with partner x), a colour-0 cover (B-slot at the source level
on an element incident with x) and a colour-1 cover (A-slot at the target level incident with x):
  set  source->target  colour-0 providers (B-slots at source)   colour-1 providers (A-slots at target)
  P01  0->1            L30, sigma(R')                           L12, sigma(R')
  L12  1->2            P01, P41                                 P23, R'
  P23  2->3            L12, sigma(R')                           L34, L30
  L34  3->4            P23, R'                                  R', P41
  L30  3->0            P23, R'                                  P01, R'
  P41  4->1            L34, sigma(R')                           L12, sigma(R')
usage: hd5_masks.py HEXBIN STATEDIR SET OUT_ALLOW OUT_PROTECT [OUT_FORBID]
  OUT_FORBID: all provider elements of SET (both colours); a pair meeting on one of them would want the same cover
  slot for both of its demands, so dpack (FORBID) never forms such a pair.
  OUT_ALLOW: elements of the set's kind with at least one cover option of each colour (may be paired);
  OUT_PROTECT: elements of SET that are cover options for some paired element of a set it provides for."""
import sys, os, numpy as np
# two demand types share a slot level: colour-1 covers of P01 and P41 (A-slots of level 1), colour-0 covers of L34 and L30
# (B-slots of level 3); a provider element incident with a partner of the competitor is left out of the options
COMP = {('P01', 1): ('P41', 1), ('P41', 1): ('P01', 1), ('L34', 0): ('L30', 0), ('L30', 0): ('L34', 0)}
PROV = {'P01': (('L30', 'S'), ('L12', 'S')), 'L12': (('P01', 'P41'), ('P23', 'R')), 'P23': (('L12', 'S'), ('L34', 'L30')),
        'L34': (('P23', 'R'), ('R', 'P41')), 'L30': (('P23', 'R'), ('P01', 'R')), 'P41': (('L34', 'S'), ('L12', 'S'))}


def load_hex(fn):
    b = open(fn, 'rb').read()
    q, N, Lc = (int(x) for x in np.frombuffer(b[:12], dtype=np.int32)); Q1 = q + 1
    LP = np.frombuffer(b[12:12 + 4 * Lc * Q1], dtype=np.int32).reshape(Lc, Q1).astype(np.int64)
    fp = LP.reshape(-1); fl = np.repeat(np.arange(Lc), Q1); o = np.lexsort((fl, fp))
    return q, N, LP, fl[o].reshape(N, Q1)


def load_state(sd, N):
    st = {k: np.loadtxt(os.path.join(sd, k + '.txt'), dtype=np.int64).reshape(-1) for k in PROV}
    Rp = np.loadtxt(os.path.join(sd, 'Rp.txt'), dtype=np.int64).reshape(-1)
    sig = np.loadtxt(os.path.join(sd, 'sigma.txt'), dtype=np.int64).reshape(-1)
    st['R'] = Rp; st['S'] = sig[Rp]
    return st


def pairs_of(kind, ids, LP, PL, N):
    s = np.zeros(N, bool); s[ids] = True
    inc = LP if kind == 'P' else PL
    c = s[inc].sum(1); assert c.max() <= 2
    out = []
    for r in np.nonzero(c == 2)[0]:
        m = inc[r][s[inc[r]]]; out.append((int(m[0]), int(m[1])))
    return out


def main():
    hexfn, sd, name, oa, op = sys.argv[1:6]; of = sys.argv[6] if len(sys.argv) > 6 else None
    q, N, LP, PL = load_hex(hexfn)
    st = load_state(sd, N)
    kind = name[0]
    # incidence of an element e of this kind: lines through a point (P) or points on a line (L)
    inc = PL if kind == 'P' else LP
    ok = np.ones(N, bool)
    for c, provs in enumerate(PROV[name]):
        m = np.zeros(N, bool)
        for p in provs: m[st[p]] = True                       # provider elements (other kind)
        if (name, c) in COMP:
            cn, cc = COMP[(name, c)]
            partners = np.array([e for pr in pairs_of(cn[0], st[cn], LP, PL, N) for e in pr], dtype=np.int64)
            if len(partners):
                tk = (PL if cn[0] == 'P' else LP)[partners].reshape(-1)
                m[tk] = False
                print(f'  colour {c}: {len(np.unique(tk))} provider elements taken by {cn} partners')
        ok &= m[inc].any(1)
    np.savetxt(oa, np.nonzero(ok)[0], fmt='%d')
    # protect: elements of this set incident with a partner of a client set (any role)
    prot = np.zeros(N, bool); mine = np.zeros(N, bool); mine[st[name]] = True
    for cl, provs in PROV.items():
        if not any(name in p for p in provs): continue
        partners = np.array([e for pr in pairs_of(cl[0], st[cl], LP, PL, N) for e in pr], dtype=np.int64)
        if len(partners) == 0: continue
        inc2 = PL if cl[0] == 'P' else LP                     # elements of my kind incident with the client's partners
        cand = inc2[partners].reshape(-1)
        prot[cand[mine[cand]]] = True
    np.savetxt(op, np.nonzero(prot)[0], fmt='%d')
    if of:
        fb = np.zeros(N, bool)
        for provs in PROV[name]:
            for p in provs: fb[st[p]] = True
        np.savetxt(of, np.nonzero(fb)[0], fmt='%d')
    print(f'{name}: {len(st[name])} elements; {ok.sum()} of {N} may pair; {prot.sum()} protected covers')


if __name__ == '__main__':
    main()
