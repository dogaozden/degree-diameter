# Test of Remark 1.5 (why the conic frame is forced): enumerate every labelled four-hat frame
# (labels a,0,c,1 -> distinct points of ell; A = (0,1,0) fixed, theta = conic polarity) and test
# whether theta-hat (with tau induced by theta on the marked set) is a polarity of S.
import sys, itertools
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics-r2/c4')
from check_c4 import run
from collections import Counter
q = int(sys.argv[1]); mode = sys.argv[2] if len(sys.argv) > 2 else '4'
E = run(q)
Z, Zp, ell_pts, build, is_pol = E['Z'], E['Zp'], E['ell_pts'], E['build'], E['is_polarity']
on_conic = E['on_conic']; P = E['P']
if mode == '4':
    labels = ['a', 0, 'c', 1]; T = [0, 'c', 1]; PI = {0: 'c', 'c': 1, 1: 0}; RHO = {0: 'c', 'c': 1, 1: 0}
else:
    labels = ['a', 0, 1]; T = [0, 1]; PI = {0: 1, 1: 0}; RHO = {0: 0, 1: 1}
res = Counter(); passing = []
for perm in itertools.permutations(ell_pts, len(labels)):
    fr = dict(zip(labels, perm))
    r = build(fr, 'a', T, PI, RHO)
    if r is None:
        res['not tau-invariant'] += 1; continue
    I, tau, S = r
    if is_pol(I, tau):
        # which labels sit on the conic (absolute points on ell)?
        absl = tuple(sorted(str(s) for s in labels if on_conic(fr[s])))
        key = ('pol', absl, 'tau=' + str(sorted((str(k), str(v)) for k, v in tau.items() if str(k) != str(v))))
        res[key] += 1
        passing.append((fr, tau))
    else:
        res['not polarity'] += 1
for k, v in sorted(res.items(), key=lambda kv: str(kv[0])):
    print(v, k)
print('total frames', sum(res.values()), 'passing', len(passing))
# check which passing frames have X_c = Z' (Definition 1.2) and which do not
if mode == '4':
    defn = [f for f, t in passing if f['c'] == Zp and f['a'] == Z]
    print('passing frames with X_a=Z, X_c=Z\' (Def 1.2 exactly):', len(defn))
    other = [f for f, t in passing if not (f['c'] == Zp and f['a'] == Z)]
    print('passing frames NOT of Def 1.2 form:', len(other))
    for f in other[:6]:
        print('  ', {str(k): P[v] for k, v in f.items()})
