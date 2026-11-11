# Own enumeration (writer's check) of the configuration types of Lemma 4.3 at q = 7, m2 <= 140.
# A configuration of distinct points y1..y5 (all != t) is recorded by
#   - the partition of {0..4} into aligned classes (points on one totally singular line through t), and
#   - the rich lines: maximal sets of >= 3 points on one line of PG(6,q) not through t;
#     each meets each aligned class at most once, two rich lines share at most one point.
# Bonferroni: |U C_i| <= S1 - S2 + S3 with C_i = y_i^perp cap opp(t), |C_i| = q^4;
#   pair aligned -> 0; pair on a rich line l -> X_l; other pair >= q^3 - q;
#   triple with an aligned pair -> 0; triple inside a rich line -> X_l; other triple <= (q+1)^2;
#   X_l >= q^3 - q; a rich line with all 5 points: exact union 5q^4 - 4 X_l.
from itertools import combinations
q = 7; m2 = 140
P = range(5)
def partitions(s):
    s = list(s)
    if not s: yield []; return
    first, rest = s[0], s[1:]
    for p in partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i+1:]
        yield [[first]] + p
cands = [frozenset(c) for r in (3, 4, 5) for c in combinations(P, r)]
def rich_systems(cls_of):
    ok = [c for c in cands if len({cls_of[i] for i in c}) == len(c)]
    out = []
    def rec(start, chosen):
        out.append(list(chosen))
        for j in range(start, len(ok)):
            c = ok[j]
            if all(len(c & d) <= 1 for d in chosen):
                rec(j + 1, chosen + [c])
    rec(0, [])
    return out
X = q**3 - q
types = {}
nlab = 0
for part in partitions(P):
    cls_of = {i: k for k, c in enumerate(part) for i in c}
    for rich in rich_systems(cls_of):
        nlab += 1
        if any(len(r) == 5 for r in rich):
            U = 5 * q**4 - 4 * X
        else:
            S1 = 5 * q**4
            S2 = 0; S3 = 0
            for a, b in combinations(P, 2):
                if cls_of[a] == cls_of[b]: continue
                S2 += X                      # on a rich line: X_l >= X; otherwise >= q^3 - q
            for tr in combinations(P, 3):
                if len({cls_of[i] for i in tr}) < 3: continue
                if any(set(tr) <= r for r in rich): S3 += 0; continue   # counted below
                S3 += (q + 1)**2
            # rich line with m in {3,4}: pairs contribute -C(m,2) X_l, triples +C(m,3) X_l: net -2 X_l, and X_l >= X
            # above we subtracted C(m,2)*X for its pairs already; add back C(m,3)*X_l <= ... careful: do it exactly
            for r in rich:
                m = len(r)
                c2, c3 = m*(m-1)//2, m*(m-1)*(m-2)//6
                # net contribution of the line's pairs and triples is -(c2 - c3) X_l <= -(c2 - c3) X  (c2 >= c3 for m <= 4)
                # we already counted -c2*X for its pairs; add +c3*X for its triples
                S3 += c3 * X
            U = S1 - S2 + S3
        far = q**5 - U - m2 * q * q
        perp = sum(len(c) + len(c) * (len(c) - 1) // 2 for c in part if len(c) >= 2) + sum(len(r) * (len(r) - 1) // 2 for r in rich)
        key = (tuple(sorted(len(c) for c in part)), tuple(sorted(len(r) for r in rich)))
        types.setdefault(key, set()).add((far, perp))
print("labelled configurations:", nlab, " types:", len(types))
bad = []
for key, vals in sorted(types.items(), key=lambda kv: min(v[0] for v in kv[1])):
    print(key, sorted(vals))
    if min(v[0] for v in vals) <= 0: bad.append(min(v[1] for v in vals))
print("types with no forced far vertex:", len(bad), " min forced perpendicular pairs among them:", min(bad))
