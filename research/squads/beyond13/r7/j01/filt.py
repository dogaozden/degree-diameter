import sys
def isp(x):
    if x < 2: return False
    i = 2
    while i * i <= x:
        if x % i == 0: return False
        i += 1
    return True
rows = [tuple(map(int, l.split()[:5])) for l in open('all.txt')]
# faithful (order == k), m prime
sel = [r for r in rows if r[4] == r[2] and isp(r[1])]
print(len(sel), "faithful prime-m candidates")
for r in sel[:60]: print(*r)
