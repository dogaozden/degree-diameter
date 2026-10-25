import sys
sys.path.insert(0, '.')
from flagmatch import setup, hk
from uncrowd import q, N, lines, lof, P, Lp
for name, s in [('crowded9 (r3 k9_valid)', '266:64 41:289 225:350 65:202 263:330 283:130 398:292 253:247 19:139'),
                ('crowded9 first 8', '266:64 41:289 225:350 65:202 263:330 283:130 398:292 253:247'),
                ('uncrowded5 (s5 set)', '210:336 152:271 188:90 183:296 109:217'),
                ('uncrowded10 (extend)', '210:336 152:271 188:90 183:296 109:217 105:190 56:394 72:311 132:157 116:226')]:
    fl = [tuple(map(int, t.split(':'))) for t in s.split()]
    pc = sum(1 for i in range(len(fl)) for j in range(i+1, len(fl)) if fl[j][0] in P[fl[i][0]])
    lc = sum(1 for i in range(len(fl)) for j in range(i+1, len(fl)) if fl[j][1] in Lp[fl[i][1]])
    size, _ = hk(setup(q, N, lines, lof, fl), N, N)
    print(f'{name}: k={len(fl)} collinear point pairs {pc} concurrent line pairs {lc} matching {size}/400')
