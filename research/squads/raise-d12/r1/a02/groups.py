# usage: groups.py meta a b r OUT   -> group Z_a x|_r Z_b (requires r^b = 1 mod a); element (i,j) index i*b+j, identity 0
#        groups.py prod OUT1 IN1 IN2 -> direct product of two group files (index = i*m2 + j)
import sys
def meta(a, b, r):
    assert pow(r, b, a) == 1 % a if a > 1 else True
    m = a * b
    def mul(x, y):
        i1, j1 = divmod(x, b); i2, j2 = divmod(y, b)
        return ((i1 + pow(r, j1, a) * i2) % a) * b + (j1 + j2) % b
    return m, [mul(x, y) for x in range(m) for y in range(m)]
def write(path, m, t):
    with open(path, "w") as f:
        f.write(f"{m}\n")
        for x in range(m):
            f.write(" ".join(str(t[x*m+y]) for y in range(m)) + "\n")
def readg(path):
    with open(path) as f:
        m = int(f.readline()); t = []
        for _ in range(m): t += list(map(int, f.readline().split()))
    return m, t
if __name__ == "__main__":
    if sys.argv[1] == "meta":
        a, b, r = map(int, sys.argv[2:5]); m, t = meta(a, b, r); write(sys.argv[5], m, t)
        print("order", m)
    elif sys.argv[1] == "prod":
        m1, t1 = readg(sys.argv[3]); m2, t2 = readg(sys.argv[4]); m = m1*m2
        def mul(x, y):
            i1, j1 = divmod(x, m2); i2, j2 = divmod(y, m2)
            return t1[i1*m1+i2]*m2 + t2[j1*m2+j2]
        write(sys.argv[2], m, [mul(x, y) for x in range(m) for y in range(m)]); print("order", m)
