"""verify(T): T = iterable of point ids of W(11). Checks: distinct, each point has <= 1 collinear neighbour in T,
and no collinear pair in T has its joining line in S. Returns (ok, msg)."""
import json, sys
S_ = json.load(open('/home/user/degree-diameter/research/squads/gqd5-r2/c2/struct.json'))
plines, lines, S = S_['plines'], S_['lines'], set(S_['S'])
def verify(T):
    T = sorted(set(int(x) for x in T))
    inT = set(T)
    if len(T) != len(list(map(int, T))):
        return False, 'dup'
    for p in T:
        nbr = []
        for l in plines[p]:
            for r in lines[l]:
                if r != p and r in inT:
                    if l in S:
                        return False, f'forbidden pair {p} {r} on S-line {l}'
                    nbr.append(r)
        if len(nbr) > 1:
            return False, f'point {p} has {len(nbr)} T-neighbours'
    return True, f'ok |T|={len(T)}'
if __name__ == '__main__':
    T = json.load(open(sys.argv[1]))
    print(verify(T))
