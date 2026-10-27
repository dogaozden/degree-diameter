import itertools, numpy as np
from lib6 import *

def subspace_transvections(basis):
    """all transvections t_a for nonzero a in GF(2)-span of basis (list of 0/1 6-vectors)"""
    B = np.array(basis) % 2
    out = []
    seen = set()
    for coef in itertools.product([0, 1], repeat=len(B)):
        if not any(coef): continue
        a = (np.array(coef) @ B) % 2
        key = tuple(a)
        if key in seen: continue
        seen.add(key); out.append(transvection(a))
    return out

def e(i):
    v = np.zeros(6, dtype=np.int64); v[i] = 1; return v

# standard hyperbolic planes: (e_i, f_i) = (e(i), e(i+3))
def plane(i): return [e(i), e(i + 3)]

def perm_matrix_symp(pi):
    """GF(2) matrix sending standard plane i to plane pi[i] preserving (e,f) order"""
    M = np.zeros((6, 6), dtype=np.int64)
    for i in range(3):
        j = pi[i]
        M[j, i] = 1; M[j + 3, i + 3] = 1
    return M

def fam_S6xS3():
    return subspace_transvections(plane(0)[:0] + [e(0), e(3), e(1), e(4)]) + subspace_transvections(plane(2))

def fam_S3wrS3():
    gens = []
    for i in range(3):
        gens += subspace_transvections(plane(i))
    gens += [perm_matrix_symp([1, 0, 2]), perm_matrix_symp([1, 2, 0])]
    return gens

def fam_S3cube():
    gens = []
    for i in range(3):
        gens += subspace_transvections(plane(i))
    return gens

def fam_S6xS3_2():
    # Sp(4,2) on planes 0,1 with Sp(2,2) on plane 2 - same as S6xS3 but written with the plane split
    return subspace_transvections([e(0), e(3), e(1), e(4)]) + subspace_transvections(plane(2))
