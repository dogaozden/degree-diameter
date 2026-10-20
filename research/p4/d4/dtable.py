"""Best GQ-copy constructions at diameter 4 for each Delta, and where the open questions matter."""
import sys
def is_pp(n):
    if n < 2: return False
    for p in range(2, n + 1):
        if n % p == 0:
            while n % p == 0: n //= p
            return n == 1
lo, hi = int(sys.argv[1]), int(sys.argv[2])
print('| Δ | Moore | best known GQ construction | value | % Moore | open lever |')
print('|---|---|---|---|---|---|')
for D in range(lo, hi + 1):
    moore = 2 * D * ((D - 1) ** 2 + 1)
    if is_pp(D - 1):
        print(f'| {D} | {moore} | GQ({D-1},{D-1}) | {moore} | 100 | - |'); continue
    q = max(x for x in range(2, D - 1) if is_pp(x)); j = D - q - 1
    cands = []
    if q % 2 == 0 or j % 2 == 0:
        cands.append((2 * D * (q * q + 1), f'Q(4,{q}), j={j} (B1/C1)', '-'))
    else:
        cands.append((2 * q * q * D, f'AS({q}) (Cor. A1/B2)', ''))
        if j == 1:
            need = q * q - 2 * q - 2
            lever = f'stand-ins: |M| ≥ {need} of ≤ {q*q-q+2} gives up to +{2*(q*q+1)*(q+2) - (q-1) - 2*q*q*D}'
        else:
            lever = f'weighted 3-ovoid of W(3,{q}) gives 2Δ(q²+1) = {2*D*(q*q+1)} (+{2*D})'
        # smaller prime power alternative
        q2 = max(x for x in range(2, q) if is_pp(x)); j2 = D - q2 - 1
        if q2 % 2 == 0 or j2 % 2 == 0:
            cands.append((2 * D * (q2 * q2 + 1), f'Q(4,{q2}), j={j2}', ''))
        cands.sort(reverse=True)
        v, name, _ = cands[0]
        print(f'| {D} | {moore} | {name} | {v} | {100*v/moore:.1f} | {lever} |'); continue
    v, name, lever = cands[0]
    print(f'| {D} | {moore} | {name} | {v} | {100*v/moore:.1f} | {lever} |')
