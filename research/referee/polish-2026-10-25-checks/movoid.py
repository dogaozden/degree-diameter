import sys, io, contextlib
sys.path.insert(0,'.')
with contextlib.redirect_stdout(io.StringIO()):
    import thmA
import highspy, numpy as np
def feasible(q,m):
    with contextlib.redirect_stdout(io.StringIO()):
        F,pts,lines,on,w,sums,e=thmA.build(q)
    h=highspy.Highs(); h.setOptionValue('output_flag',False); h.setOptionValue('time_limit',600.0)
    n=len(pts)
    for i in range(n): h.addVar(0,1)
    h.changeColsIntegrality(n,np.arange(n,dtype=np.int32),np.ones(n,dtype=np.uint8))
    for L in lines:
        idx=np.array(sorted(L),dtype=np.int32); h.addRow(m,m,len(idx),idx,np.ones(len(idx)))
    h.run(); return h.modelStatusToString(h.getModelStatus())
for q,ms in ((3,(1,2)),(5,(1,2,3,4))):
    for m in ms: print("AS(%d) %d-ovoid:"%(q,m),feasible(q,m),flush=True)
