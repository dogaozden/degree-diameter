"""OMEGA_REPAIR.md Theorem 4.5, step 2 (q = 7).  Six distinct points t, y1..y5 of Q(6,q).  Structure: (A) aligned
classes = the y's on a common totally singular line through t (their sets C_i = y_i^perp & opp(t) are pairwise
disjoint); (B) rich lines = lines of PG(6,q) not through t holding >= 3 of the y's (at most one point per aligned class,
two rich lines share at most one y).  union_bound() bounds |C_1 u ... u C_5| by Bonferroni with: pair overlap 0 inside
an aligned class and >= q^3 - q otherwise; triple overlap 0 if it contains an aligned pair, equal to the line's pair
overlap X_l if it lies on a rich line, <= (q+1)^2 otherwise (Lemma 4.1); exact 5q^4 - 4X_l if all five y's are on one
rich line.  For every structure type: the bound q^5 - union - m2 q^2 on far vertices (m2 = 140, the largest m2 of a
starved pair at q = 7) and the number of pairs among the six points that the structure forces to be perpendicular."""
import itertools
q, m2 = 7, 140
PO = q ** 3 - q; T3 = (q + 1) ** 2
Y = list(range(5))
def partitions(s):
    if not s: yield []; return
    f, rest = s[0], s[1:]
    for p in partitions(rest):
        for i in range(len(p)): yield p[:i] + [[f] + p[i]] + p[i + 1:]
        yield [[f]] + p
def union_bound(part, fam):
    cls = {y: i for i, b in enumerate(part) for y in b}
    if any(len(S) == 5 for S in fam): return 5 * q ** 4 - 4 * PO
    al = lambda i, j: cls[i] == cls[j]
    S2 = sum(PO for i, j in itertools.combinations(Y, 2) if not al(i, j))
    S3 = 0
    for tr in itertools.combinations(Y, 3):
        if any(al(a, b) for a, b in itertools.combinations(tr, 2)): continue
        if not any(set(tr) <= set(S) for S in fam): S3 += T3
    for S in fam:                                   # pairs and triples on a rich line: net -(C(m,2) - C(m,3)) X_l
        m = len(S); c2, c3 = m * (m - 1) // 2, m * (m - 1) * (m - 2) // 6
        S2 += (c2 - c3) * PO - c2 * PO
    return 5 * q ** 4 - S2 + S3
def structures():
    for part in partitions(Y):
        cls = {y: i for i, b in enumerate(part) for y in b}
        cands = [S for k in (3, 4, 5) for S in itertools.combinations(Y, k) if len({cls[y] for y in S}) == k]
        for r in range(0, 4):
            for fam in itertools.combinations(cands, r):
                if any(len(set(a) & set(b)) > 1 for a, b in itertools.combinations(fam, 2)): continue
                # a rich line containing a 3-subset of another chosen line is the same line
                if any(set(a) < set(b) for a in fam for b in fam if a != b): continue
                yield part, fam
def forced_perp(part, fam):
    pts = ['t'] + Y; pr = set()
    for b in part:
        for a, c in itertools.combinations(['t'] + b, 2): pr.add(frozenset((a, c))) if len(b) > 1 else None
    for S in fam:
        for a, c in itertools.combinations(S, 2): pr.add(frozenset((a, c)))
    return len(pr)
if __name__ == '__main__':
    res = {}
    for part, fam in structures():
        far = q ** 5 - union_bound(part, fam) - m2 * q * q
        key = (tuple(sorted(len(b) for b in part)), tuple(sorted(len(S) for S in fam)))
        fp = forced_perp(part, fam)
        old = res.get(key)
        res[key] = (min(far, old[0]) if old else far, min(fp, old[1]) if old else fp)
    print(f"{len(res)} structure types; far vertex forced in {sum(v[0] > 0 for v in res.values())}")
    for k, (v, fp) in sorted(res.items(), key=lambda kv: kv[1][0]):
        print(f"aligned classes {k[0]}, rich lines {k[1]}: far vertices >= {v}{'' if v > 0 else '  (not forced)'}; forced perpendicular pairs >= {fp}")
    print("min forced perpendicular pairs over the types where no far vertex is forced:", min(fp for v, fp in res.values() if v <= 0))
