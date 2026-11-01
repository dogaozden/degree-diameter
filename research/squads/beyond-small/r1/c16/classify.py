# classify edges of g18.edges (builder numbering vid=(v*2+a)*5+b, N=2380 points, v>=N lines)
import sys
from collections import Counter
f = open('g18.edges'); n = int(f.readline())
N = 2380
def dec(x):
    b = x % 5; a = (x // 5) % 2; v = x // 10
    return v, a, b
cls = {}
E = []
for l in f:
    if not l.strip(): continue
    x, y = map(int, l.split())
    vx, ax, bx = dec(x); vy, ay, by = dec(y)
    if vx >= N: x, y, vx, ax, bx, vy, ay, by = y, x, vy, ay, by, vx, ax, bx   # x = point
    assert vx < N <= vy, (x, y)
    d = (by - bx) % 5
    c = ax ^ ay
    E.append((x, y, d, c))
print(Counter((d) for _,_,d,_ in E))
print(Counter((d, c) for _,_,d,c in E))
import pickle; pickle.dump(E, open('E18.pkl', 'wb'))
