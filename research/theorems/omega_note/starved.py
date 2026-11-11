# For each alpha and every block pattern: starved pairs (exactly alpha twisted radius-4 words), by bar,
# with the range of m2; uses the referee's route enumerator myroutes.py (copied unchanged from
# claude/referee-omega-repair-qt17fb, research/referee/omega-repair/myroutes.py). Run: python3 starved.py 5 (or 6).
import sys
from myroutes import wiring, routes, summary
alpha = int(sys.argv[1])
glob_max = 0
for na in range(alpha + 1):
    pat = 'a' * na + 'b' * (alpha - na)
    C, meets = wiring(pat)
    st = {'u': [], 'b': []}
    mintw = 99; nonid0 = 0; idr = set()
    for X in C:
        for cp in range(5 * alpha):
            if cp in C[X]: continue
            b = routes(pat, X, cp)
            ident = b.pop((), None); idr.add(ident)
            m, _ = summary(b)
            mintw = min(mintw, m[4]); nonid0 += m.get(0, 0)
            if m[4] == alpha: st[X[0]].append(m[2])
    mx = max(st['u'] + st['b']); glob_max = max(glob_max, mx)
    print(f"alpha={alpha} {pat:<9} identity radius {sorted(idr)}; min twisted r4 over pairs {mintw}; non-identity r0 words {nonid0}; "
          f"starved unbarred {len(st['u'])} (m2 {min(st['u'])}..{max(st['u'])}), barred {len(st['b'])} (m2 {min(st['b'])}..{max(st['b'])})", flush=True)
print("max m2 over all starved pairs:", glob_max)
