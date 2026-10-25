#!/usr/bin/env python3
"""c7 (squad r3-d8): SAT search for guaranteed-walk label designs G(M) on the split Cayley hexagon H(q).

Labels: t_k on points and l_k on lines (k = 1..j), one-hot in Z_M.
Multiset: for each k and g, #points with t_k = g equals #lines with l_k = g.
  profile free:    two-sided totalizers on both sides, outputs equated (any profile).
  profile uniform: CardEnc.equals with the near-uniform profile (N//M, +1 on the first N%M values).
Condition G(M): for every point x, line y and g != 0, some term equals g:
  t_k(x) | l_k(y) | -l_k(b) (b through x) | -t_k(a) (a on y) [| t_k(x)+l_m(y) if --sum].
  (g = 0 is always covered by the flag walk.)
Any G(M) solution gives a lift with diameter <= 8 for every label-preserving matching.

usage: g_sat.py q j M [--sum] [--profile free|uniform] [--tag TAG]
writes c7/labels_TAG.json (SAT) and appends one line to c7/results.jsonl (SAT/UNSAT, check results).
"""
import argparse
import collections
import json
import os
import subprocess
import sys
import time

sys.setrecursionlimit(20000)
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d8')
import gh  # noqa: E402
from pysat.solvers import Cadical153  # noqa: E402
from pysat.card import CardEnc, EncType  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
LIFTDIAM = '/home/user/degree-diameter/research/theorems/d8/liftdiam'


class Pool:
    def __init__(self, top=0):
        self.top = top

    def new(self):
        self.top += 1
        return self.top


def totalizer(lits, pool, cls):
    """Two-sided totalizer: returns O with O[k-1] <-> (sum(lits) >= k)."""
    if len(lits) == 1:
        return [lits[0]]
    h = len(lits) // 2
    A = totalizer(lits[:h], pool, cls)
    B = totalizer(lits[h:], pool, cls)
    p, r = len(A), len(B)
    n = p + r
    O = [pool.new() for _ in range(n)]
    for i in range(p + 1):
        for j in range(r + 1):
            if i + j == 0:
                continue
            c = [O[i + j - 1]]
            if i:
                c.append(-A[i - 1])
            if j:
                c.append(-B[j - 1])
            cls.append(c)
    for i in range(p + 1):
        for j in range(r + 1):
            if i + j + 1 > n:
                continue
            c = [-O[i + j]]
            if i + 1 <= p:
                c.append(A[i])
            if j + 1 <= r:
                c.append(B[j])
            cls.append(c)
    return O


def structure(H):
    N = H.N
    through = [[int(k) for k in H.through[p]] for p in range(N)]   # lines (indices) through point p
    pts_of = [[int(p) for p in H.lines[k]] for k in range(N)]      # points on line k
    return N, through, pts_of


def encode(H, j, M, use_sum, profile, sym=True):
    N, through, pts_of = structure(H)

    def T(f, x, g):
        return 1 + (f * 2 * N + x) * M + g

    def L(f, y, g):
        return 1 + (f * 2 * N + N + y) * M + g

    pool = Pool(2 * j * N * M)
    cls = []
    for f in range(j):
        for idx in range(N):
            for fn in (T, L):
                v = [fn(f, idx, g) for g in range(M)]
                cls.append(list(v))
                for a in range(M):
                    for b in range(a + 1, M):
                        cls.append([-v[a], -v[b]])
    if sym:
        # unit symmetry: all labels can be multiplied by a unit of Z_M; t_0(point 0) = a divisor d of M (d = M is 0)
        cls.append([T(0, 0, d % M) for d in range(1, M + 1) if M % d == 0])
    for f in range(j):
        if profile == 'free':
            for g in range(M):
                OP = totalizer([T(f, x, g) for x in range(N)], pool, cls)
                OL = totalizer([L(f, y, g) for y in range(N)], pool, cls)
                for k in range(N):
                    cls.append([-OP[k], OL[k]])
                    cls.append([OP[k], -OL[k]])
        else:
            base_c, rem = divmod(N, M)
            for g in range(M):
                c = base_c + (1 if g < rem else 0)
                for lits in ([T(f, x, g) for x in range(N)], [L(f, y, g) for y in range(N)]):
                    enc = CardEnc.equals(lits=lits, bound=c, top_id=pool.top, encoding=EncType.seqcounter)
                    cls.extend(enc.clauses)
                    pool.top = max(pool.top, enc.nv)
    for x in range(N):
        for y in range(N):
            for g in range(1, M):
                lits = []
                for f in range(j):
                    lits.append(T(f, x, g))
                    lits.append(L(f, y, g))
                    lits += [L(f, b, (-g) % M) for b in through[x]]
                    lits += [T(f, a, (-g) % M) for a in pts_of[y]]
                if use_sum:
                    for k in range(j):
                        for m in range(j):
                            for u in range(M):
                                v = (g - u) % M
                                P = pool.new()          # P -> t_k(x) = u and l_m(y) = v
                                cls.append([-P, T(k, x, u)])
                                cls.append([-P, L(m, y, v)])
                                lits.append(P)
                cls.append(lits)
    return cls, pool


def decode(model_set, H, j, M):
    N = H.N
    pt = [[None] * N for _ in range(j)]
    ln = [[None] * N for _ in range(j)]
    for f in range(j):
        for x in range(N):
            for g in range(M):
                if (1 + (f * 2 * N + x) * M + g) in model_set:
                    pt[f][x] = g
        for y in range(N):
            for g in range(M):
                if (1 + (f * 2 * N + N + y) * M + g) in model_set:
                    ln[f][y] = g
    return pt, ln


def check_labels(H, j, M, pt, ln, use_sum):
    """Independent check: multiset equality, G(M) coverage, regularity."""
    N, through, pts_of = structure(H)
    res = {'multiset_ok': True, 'covered_ok': True, 'bad_pairs': 0, 'regular': True}
    for f in range(j):
        if any(v is None for v in pt[f]) or any(v is None for v in ln[f]):
            return {'error': 'unlabelled'}
        if collections.Counter(pt[f]) != collections.Counter(ln[f]):
            res['multiset_ok'] = False
    for x in range(N):
        for y in range(N):
            S = {0}
            for f in range(j):
                S.add(pt[f][x])
                S.add(ln[f][y])
                S.update((-ln[f][b]) % M for b in through[x])
                S.update((-pt[f][a]) % M for a in pts_of[y])
            if use_sum:
                for k in range(j):
                    for m in range(j):
                        S.add((pt[k][x] + ln[m][y]) % M)
            if len(S) != M:
                res['covered_ok'] = False
                res['bad_pairs'] += 1
    for f in range(j):
        for x in range(N):
            vals = [ln[f][b] for b in through[x]]
            if len(set(vals)) != len(vals):
                res['regular'] = False
        for y in range(N):
            vals = [pt[f][a] for a in pts_of[y]]
            if len(set(vals)) != len(vals):
                res['regular'] = False
    return res


def kuhn(N, allowed):
    matchR = [-1] * N

    def try_(x, seen):
        for y in allowed[x]:
            if not seen[y]:
                seen[y] = True
                if matchR[y] == -1 or try_(matchR[y], seen):
                    matchR[y] = x
                    return True
        return False

    for x in range(N):
        if not try_(x, [False] * N):
            return None
    s = [-1] * N
    for y in range(N):
        s[matchR[y]] = y
    return s


def make_matchings(H, j, pt, ln, flags_ok):
    """Label-preserving bijections s_f: points -> lines (l_f(s_f(x)) = t_f(x)).
    Flags (x on s_f(x)) avoided unless flags_ok; a hop of voltage 0 never sits on a flag; s_1(x) != s_0(x)."""
    N, through, _ = structure(H)
    sets = []
    for f in range(j):
        allowed = []
        for x in range(N):
            fl = set(through[x])
            cand = []
            for y in range(N):
                if ln[f][y] != pt[f][x]:
                    continue
                if y in fl and (not flags_ok or pt[f][x] == 0):
                    continue
                if f > 0 and y == sets[0][x]:
                    continue
                cand.append(y)
            allowed.append(cand)
        s = kuhn(N, allowed)
        if s is None:
            return None
        sets.append(s)
    return sets


def write_lift(path, H, j, M, pt, sets):
    N = H.N
    edges = [(int(p), int(L), 0, 0) for (p, L) in gh.flags(H)]
    for f in range(j):
        for x in range(N):
            edges.append((x, N + sets[f][x], pt[f][x], 0))
    gh.write_base(path, 2 * N, M, 1, edges)
    return len(edges)


def run_liftdiam(path):
    out = subprocess.run([LIFTDIAM, path, '8', '1'], capture_output=True, text=True, timeout=900).stdout
    info = {'raw': out.strip()}
    if 'unreached_pairs' in out:
        info['unreached'] = int(out.split('unreached_pairs')[1].split()[0])
    if 'multi_edges' in out:
        info['multi_edges'] = int(out.split('multi_edges')[1].split()[0])
    return info


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('q', type=int)
    ap.add_argument('j', type=int)
    ap.add_argument('M', type=int)
    ap.add_argument('--sum', action='store_true', help='include the t_k(x)+l_m(y) terms')
    ap.add_argument('--profile', default='free', choices=['free', 'uniform'])
    ap.add_argument('--tag', default=None)
    ap.add_argument('--nosym', action='store_true', help='disable the unit symmetry break')
    a = ap.parse_args()
    tag = a.tag or f"q{a.q}_j{a.j}_M{a.M}_{'sum' if a.sum else 'nosum'}_{a.profile}"
    H = gh.load(a.q)
    t0 = time.time()
    cls, pool = encode(H, a.j, a.M, a.sum, a.profile, sym=not a.nosym)
    t_enc = time.time() - t0
    s = Cadical153(bootstrap_with=cls)
    nclauses, nvars = len(cls), pool.top
    cls = None
    t1 = time.time()
    ok = s.solve()
    t_solve = time.time() - t1
    rec = {'tag': tag, 'q': a.q, 'j': a.j, 'M': a.M, 'sum': a.sum, 'profile': a.profile,
           'status': 'SAT' if ok else 'UNSAT', 'vars': nvars, 'clauses': nclauses,
           't_encode': round(t_enc, 2), 't_solve': round(t_solve, 2)}
    if ok:
        model = set(l for l in s.get_model() if l > 0)
        pt, ln = decode(model, H, a.j, a.M)
        rec['check_labels'] = check_labels(H, a.j, a.M, pt, ln, a.sum)
        rec['regular'] = rec['check_labels'].get('regular')
        with open(os.path.join(HERE, f'labels_{tag}.json'), 'w') as fh:
            json.dump({'q': a.q, 'j': a.j, 'M': a.M, 'pt': pt, 'ln': ln}, fh)
        sets, used = None, None
        for flags_ok in (False, True):
            sets = make_matchings(H, a.j, pt, ln, flags_ok)
            if sets is not None:
                used = 'flags_avoided' if not flags_ok else 'flags_allowed_nonzero_hops'
                break
        if sets is None:
            rec['lift'] = {'error': 'no label-preserving matching'}
        else:
            path = os.path.join(HERE, f'lift_{tag}.txt')
            E = write_lift(path, H, a.j, a.M, pt, sets)
            info = run_liftdiam(path)
            info['E'] = E
            info['matching'] = used
            info['file'] = path
            rec['lift'] = info
            rec['valid'] = (info.get('unreached') == 0 and info.get('multi_edges') == 0)
    s.delete()
    print(json.dumps(rec), flush=True)
    with open(os.path.join(HERE, 'results.jsonl'), 'a') as fh:
        fh.write(json.dumps(rec) + '\n')


if __name__ == '__main__':
    main()
