# Row data for rows14.py: (Δ, D) -> (value, construction, check, comparison). Values as checked by the director.
C = 'research/frontier/runs/cloudcheck/'
G = 'research/frontier/beyond/graphs/'
ROWS[(3, 14)] = (7004,
    'regular voltage lift of a 2+2 cubic base (a 4-cycle with two opposite edges doubled) over the Frobenius group '
    'Z103 x\\|_8 Z17 (order 1,751), base and voltages annealed together (salift_s from job own-small; director, '
    'job beyond-d14); not a Haar graph. Earlier the same day: 6,486 (3+3 base over Z47 x\\|_2 Z23, squad r2/d04), 6,328 '
    '(4+4 base over Z113 x\\|_16 Z7, director); the Foster census graph CSS(6272,7) (semisymmetric, Potocnik et al.) has '
    '6,272; beyond-d13: 5,706 (Z317 lift of the Pappus graph)',
    f'apsp VALID, diameter exactly 14 ({G}d3D14_n7004_lift2_meta103_17_8.apsp.txt; graph and .sol next to it)',
    'Haar size law at mu = 5: 2N = 5.23e+03; this lift sits at mu = 33')
ROWS[(4, 14)] = (503014,
    'Haar graph of the metacyclic group Z5849 x\\|_5711 Z43 (m prime, order 251,507), S random (hmeta screen of '
    'prime-m metacyclic groups, then a chain; squad r2/d07); earlier 498,798 (Z3079 x\\|_1863 Z81, r1/c05); '
    'beyond-d13: 497,042',
    f'build_haar2 VALID ({C}d4D14_meta_5849_43_d07.build_haar2.txt)',
    'Haar size law at mu = 5: 2N = 4.47e+05')
ROWS[(5, 14)] = (13105798,
    'Haar graph of the metacyclic group Z152393 x\\|_149882 Z43 (order 6,552,899), S random (hmeta, 4 s; squad '
    'r1/c08); earlier 12,991,752 (PSL(2,163) x Z3 with an order-2 orbit S = {e, x, ax, y, ay}, r1/c11); beyond-d13: '
    '12,795,166',
    f'build_haar2 VALID ({C}d5D14_meta_152393_43_c08.build_haar2.txt)',
    'Haar size law at mu = 5: 2N = 1.27e+07')
ROWS[(6, 14)] = (192314952,
    'Haar graph PSL(2,107) x Z157, S = 2 free orbits of size 3 (ORBIT "3 2 0"; squad r2/d13); earlier 190,269,984 '
    '(SL(2,137) x Z37, first random symmetric S, r1/c12); beyond-d13: 187,990,656',
    f'haarcheck_gen VALID ({C}d6D14_psl_107_157_orb3-2-0_d13.gen.txt)',
    'Haar size law at mu = 5: 2N = 1.83e+08')
ROWS[(7, 14)] = (1709227632,
    'Haar graph PSL(2,167) x Z367, S = {e} + 2 orbits of size 3 (ORBIT "3 2 1"), a random symmetric S (RANDORB '
    'screen, squad r2/d15); earlier 1,694,979,936 (SL(2,233) x Z67, r1/c15); beyond-d13: 1,674,490,944',
    f'haarcheck_gen VALID ({C}d7D14_psl_167_367_orb3-2-1_d15.gen.txt)',
    'Haar size law at mu = 5: 2N = 1.66e+09')
