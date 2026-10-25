from base import *
print('sym ok', check_sym(), 'N', N)
S = load_set('/home/user/degree-diameter/research/d10D7/sets/P8_r5c4_217.txt')
print('size', len(S))
r = w_row(P[S[0]])
S_arr = np.array(S)
ok = all(w_pair(P[a], P[b]) != 0 for i, a in enumerate(S) for b in S[i+1:])
print('pairwise nonorth', ok)
