import math
def order_mod(r, m):
    x, o = r % m, 1
    while x != 1 % m:
        x = x * r % m; o += 1
    return o
L = [tuple(map(int, l.split())) for l in open('meta_list.txt') if l.strip()]
def pri(t):
    N, m, k, r = t
    o = order_mod(r, m) if r > 1 else 1
    faithful = (o == k) and r > 1
    return (0 if faithful else 1, N)
L.sort(key=pri)
with open('meta_list2.txt', 'w') as f:
    for t in L: f.write('%d %d %d %d\n' % t)
print(sum(1 for t in L if pri(t)[0] == 0), 'faithful of', len(L))
