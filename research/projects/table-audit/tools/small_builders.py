"""Small table graphs from their papers' parameters (table-audit).
  bye n s F1,F2,..[;G1,..] OUT   Bar-Yehuda--Etzion 1992 (Discrete Appl. Math. 37/38, Sec. 2, Appendix B): two n-cycles
                                 (i,0), (i,1), i in Z_n, plus, for each function F on Z_s (F(i)+i mod s a permutation),
                                 the edges (j,0) ~ (j + F(j mod s), 1).  (3,5) = 56: n = 28, s = 4, F = (12,0,8,20).
  phi m a1,a2,.. OUT             Feria-Puron--Miller--Pineda-Villavicencio 2013 (Discrete Math. 313, Sec. 5):
                                 Phi_m(a_1..a_{d-3}) = Haar graph of Z_m with connection set {0, 1, -1, a_1, ...}:
                                 x_i ~ y_i, y_{i+1}, y_{i-1}, y_{i+a_j}.  (11,3) = 190: m = 95.
Writes apsp.c edge lists ("n" then "u v")."""
import sys


def write(out, n, E):
    with open(out, 'w') as f:
        f.write(f'{n}\n')
        f.writelines(f'{u} {v}\n' for u, v in E)
    print(out, n, len(E))


def bye(n, s, Fs, out):
    E = []
    for i in range(n):
        E.append((i, (i + 1) % n))                  # cycle on (i,0) = i
        E.append((n + i, n + (i + 1) % n))          # cycle on (i,1) = n + i
    for F in Fs:
        assert sorted((F[i] + i) % s for i in range(s)) == list(range(s))
        for j in range(n):
            E.append((j, n + (j + F[j % s]) % n))
    write(out, 2 * n, E)


def phi(m, A, out):
    S = [0, 1, m - 1] + A
    write(out, 2 * m, [(i, m + (i + a) % m) for i in range(m) for a in S])


if __name__ == '__main__':
    if sys.argv[1] == 'bye':
        n, s = int(sys.argv[2]), int(sys.argv[3])
        Fs = [list(map(int, f.split(','))) for f in sys.argv[4].split(';')]
        bye(n, s, Fs, sys.argv[5])
    else:
        phi(int(sys.argv[2]), list(map(int, sys.argv[3].split(','))), sys.argv[4])
