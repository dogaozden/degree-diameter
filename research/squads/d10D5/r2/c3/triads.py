"""triads.py FLAGS...: pair and triad relations of a flag set (p:l tokens): collinear/non-collinear points,
concurrent/disjoint lines, centre counts C (points collinear with all p) and transversal counts T (lines
meeting all l), both excluding the flag points/lines themselves."""
import sys, collections, itertools
sys.path.insert(0, '.')
from obst import Geo
geo = Geo()
fl = [tuple(map(int, t.split(':'))) for t in sys.argv[1:]]
def pc(p, q): return 'col' if ((geo.Pm[p] >> q) & 1 and q != p) else 'non'
def lc(l, m): return 'conc' if set(geo.lines[l]) & set(geo.lines[m]) else 'disj'
for (i, j) in itertools.combinations(range(len(fl)), 2):
    print('pair', i, j, 'points', pc(fl[i][0], fl[j][0]), 'lines', lc(fl[i][1], fl[j][1]),
          'pairwise |A_i&A_j|', bin(geo.flag_sets(*fl[i])[0] & geo.flag_sets(*fl[j])[0]).count('1'),
          '|Ll&Ll|', bin(geo.flag_sets(*fl[i])[1] & geo.flag_sets(*fl[j])[1]).count('1'),
          '|G&G|', bin(geo.flag_sets(*fl[i])[2] & geo.flag_sets(*fl[j])[2]).count('1'),
          '|Pp&Pp|', bin(geo.flag_sets(*fl[i])[3] & geo.flag_sets(*fl[j])[3]).count('1'))
for S in itertools.combinations(range(len(fl)), 3):
    sets = [geo.flag_sets(*fl[s]) for s in S]
    A = sets[0][0] & sets[1][0] & sets[2][0]; Ll = sets[0][1] & sets[1][1] & sets[2][1]
    G = sets[0][2] & sets[1][2] & sets[2][2]; Pp = sets[0][3] & sets[1][3] & sets[2][3]
    pc3 = [pc(fl[S[0]][0], fl[S[1]][0]), pc(fl[S[0]][0], fl[S[2]][0]), pc(fl[S[1]][0], fl[S[2]][0])]
    lc3 = [lc(fl[S[0]][1], fl[S[1]][1]), lc(fl[S[0]][1], fl[S[2]][1]), lc(fl[S[1]][1], fl[S[2]][1])]
    print('triad', S, 'pts', pc3, 'lines', lc3, '|A|', bin(A).count('1'), '|Ll|', bin(Ll).count('1'),
          '|G|', bin(G).count('1'), '|Pp|', bin(Pp).count('1'))
