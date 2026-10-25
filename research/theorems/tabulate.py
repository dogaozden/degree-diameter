"""Item 1: one row per Haar record in research/frontier/sols/, with S in normal form.

Columns: cell, family, q, n, N = |G|, vertices, orbit type, table value (DS14v2), ours/table, N/(Δ-1)^(D-2),
girth (from ball growth around (e,A), up to level LMAX), Q-part traces of S (file normalised so e in S),
orders of the Q-parts of the quotients s_i^-1 s_j (i<j), the Z_n parts.
Output: tabulate_out.txt (human table), records.json (machine-readable, used by later scripts).
"""
import json, sys, os, time
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'frontier'))
from recs import all_records, orbit_type, MatG, ProdG
from heuristic import TABLE, moore

LMAX = 5
WORK = 3_000_000   # max group multiplications per record for the ball growth


def ball_growth(R):
    """distinct elements at BFS levels 1..L around (e,A): level r is on side B for odd r (words s.. ), A for even.
    Returns list of counts and the girth (2r at the first deficient level), or None if no deficiency seen."""
    G, S = R['G'], R['S']
    Sinv = [G.inv(s) for s in S]
    seen = [{G.e}, set()]           # side A, side B
    front, side = [G.e], 0
    counts, girth, work = [], None, 0
    d = len(S)
    for r in range(1, LMAX + 1):
        mult = S if side == 0 else Sinv
        if work + len(front) * d > WORK:
            break
        nxt = set()
        for x in front:
            for s in mult:
                nxt.add(G.mul(s, x))
        work += len(front) * d
        nxt -= seen[1 - side]
        seen[1 - side] |= nxt
        counts.append(len(nxt))
        nb = d * (d - 1) ** (r - 1)
        if girth is None and len(nxt) < nb:
            girth = 2 * r
        front, side = list(nxt), 1 - side
        if girth is not None:
            break
    return counts, girth


def qpart_order(Q, x, cap):
    e, y, k = Q.e, x, 1
    while y != e:
        y = Q.mul(y, x); k += 1
        if k > cap: return None
    return k


def main():
    recs = all_records()
    rows = []
    t0 = time.time()
    for R in recs:
        d, D, Q, n, S = R['d'], R['D'], R['Q'], R['n'], R['S']
        tab = TABLE[d][D - 3]
        verts = 2 * R['N']
        counts, girth = ball_growth(R)
        # quotient invariants
        cap = 2 * (getattr(Q, 'q', 64) + 1) if isinstance(Q, MatG) else 4 * Q.order
        qords, ztot, traces = [], [], []
        for i in range(d):
            for j in range(i + 1, d):
                x = Q.mul(Q.inv(S[i][0]), S[j][0])
                o = qpart_order(Q, x, cap) if (isinstance(Q, MatG) or Q.order < 10**6) else None
                qords.append(o)
                ztot.append((S[j][1] - S[i][1]) % n)
        if isinstance(Q, MatG):
            traces = [Q.trace(s[0]) for s in S]
        e_in_S = Q.e in [s[0] for s in S]
        row = dict(tag=R['tag'], d=d, D=D, spec=R['spec'], n=n, N=R['N'], vertices=verts, orbit=orbit_type(R['tag'], d),
                   table=tab, ratio_table=verts / tab if tab else None, C=R['N'] / (d - 1) ** (D - 2),
                   ratio_moore=verts / moore(d, D), ball=counts, girth=girth,
                   qorders=qords, zparts=[s[1] for s in S], traces=traces,
                   q=getattr(Q, 'q', None), family=type(Q).__name__)
        rows.append(row)
    json.dump(rows, open('records.json', 'w'), indent=0)
    # best per cell
    best = {}
    for r in rows:
        k = (r['d'], r['D'])
        if k not in best or r['vertices'] > best[k]['vertices']:
            best[k] = r
    with open('tabulate_out.txt', 'w') as f:
        f.write(f"{len(rows)} records, {len(best)} cells. Time {time.time()-t0:.0f}s\n\n")
        f.write("cell | group | N | vertices | orbit | table | ours/table | N/(Δ-1)^(D-2) | girth | ball growth (levels 1..) "
                "| min order of Q(s_i^-1 s_j) | #pairs with Q-order<=6 | z-parts\n")
        for r in sorted(rows, key=lambda r: (r['D'], r['d'], -r['vertices'])):
            star = '*' if best[(r['d'], r['D'])] is r else ' '
            qo = [o for o in r['qorders'] if o is not None]
            small = sum(1 for o in qo if o <= 6)
            f.write(f"{star}({r['d']},{r['D']}) | {r['spec']} x Z{r['n']} | {r['N']:,} | {r['vertices']:,} | {r['orbit']} | "
                    f"{r['table']:,} | {r['ratio_table']:.4f} | {r['C']:.3f} | {r['girth']} | {r['ball']} | "
                    f"{min(qo) if qo else None} | {small} | {r['zparts']}\n")
    print(open('tabulate_out.txt').read()[:6000])


if __name__ == '__main__':
    main()
