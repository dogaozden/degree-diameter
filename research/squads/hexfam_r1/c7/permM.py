from torus import *
M = pickle.load(open('/home/user/degree-diameter/research/squads/hexfam_r1/c7/M513.pkl','rb'))
pm = perm_of(M)
np.save('/home/user/degree-diameter/research/squads/hexfam_r1/c7/permM.npy', pm)
# check order
x = np.arange(N); k = 0; y = x.copy()
while True:
    y = pm[y]; k += 1
    if (y == x).all(): break
print('order of perm', k)
