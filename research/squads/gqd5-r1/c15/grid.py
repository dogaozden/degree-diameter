import numpy as np
REQ = [(82,73,2),(82,73,0),(122,111,2),(122,111,0),(170,157,2),(170,157,0)]
def make_grid():
    pts = set(REQ)
    for b in range(0, 101, 8):
        for c in [0,1,2,3,5,8,12,20,30,40,60,80,100]:
            if c <= b: pts.add((100, b, c))
    pts = sorted(pts, key=lambda t: (-t[0], t[1], t[2]))
    return np.array(pts, dtype=np.float64)
