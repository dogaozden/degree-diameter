import sys
exec(open('octo_g2.py').read().split("closed = all")[0])
Sp = set(S)
changed = True; it = 0
while changed:
    changed = False; it += 1
    rem = [X for X in Sp if any(mul2(X, Y) not in Sp for Y in Sp)]
    if rem:
        for X in rem: Sp.discard(X)
        changed = True
    print('iter', it, 'size', len(Sp), 'removed', len(rem), flush=True)
imag = [X for X in Sp if X[0] == 0]
print('closed subset size', len(Sp), 'imag', len(imag))
print('contains +-e_i:', all(tuple(2*s if t==i else 0 for t in range(8)) in Sp for i in range(1,8) for s in (1,-1)))
