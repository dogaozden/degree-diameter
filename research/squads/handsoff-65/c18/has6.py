import sys
# usage: has6.py TABLE...  prints table name, group order, number of elements of order 6, and of order 3, 2 (counts)
for fn in sys.argv[1:]:
    with open(fn) as f:
        m = int(f.readline())
        T = [list(map(int, f.readline().split())) for _ in range(m)]
    cnt = {}
    for g in range(m):
        x, k = g, 1
        while x != 0:
            x = T[x][g]; k += 1
            if k > 60: break
        cnt[k] = cnt.get(k, 0) + 1
    print(fn.split('/')[-1][:-4], m, 'ord6=%d' % cnt.get(6, 0), 'ord3=%d' % cnt.get(3, 0), 'ord2=%d' % cnt.get(2, 0))
