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
ROWS[(4, 14)] = (504382,
    'Haar graph of the metacyclic group Z6151 x\\|_5694 Z41 (m prime, order 252,191), S random: a cost-2 hmeta state '
    'finished by an exhaustive 1-opt over one generator slot (squad r3/e06, after r2/d07); earlier 503,014 (Z5849 '
    'x\\|_5711 Z43, r2/d07) and 498,798 (Z3079 x\\|_1863 Z81, r1/c05); beyond-d13: 497,042',
    f'build_haar2 VALID ({C}d4D14_meta_6151_41_e06.build_haar2.txt)',
    'Haar size law at mu = 5: 2N = 4.47e+05')
ROWS[(5, 14)] = (13105798,
    'Haar graph of the metacyclic group Z152393 x\\|_149882 Z43 (order 6,552,899), S random (hmeta, 4 s; squad '
    'r1/c08); earlier 12,991,752 (PSL(2,163) x Z3 with an order-2 orbit S = {e, x, ax, y, ay}, r1/c11); beyond-d13: '
    '12,795,166',
    f'build_haar2 VALID ({C}d5D14_meta_152393_43_c08.build_haar2.txt)',
    'Haar size law at mu = 5: 2N = 1.27e+07')
ROWS[(6, 14)] = (193333056,
    'Haar graph SL(2,113) x Z67, S = 2 free orbits of size 3 (ORBIT "3 2 0"), a random symmetric S from a RANDORB screen '
    '(squad r3/e12; the same card also found SL(2,131) x Z43, 193,324,560); earlier 192,314,952 (PSL(2,107) x Z157, r2/d13) and 190,269,984 (SL(2,137) x Z37, r1/c12); '
    'beyond-d13: 187,990,656',
    f'haarcheck_gen VALID ({C}d6D14_sl_113_67_orb3-2-0_e12.gen.txt)',
    'Haar size law at mu = 5: 2N = 1.83e+08')
ROWS[(7, 14)] = (1723572432,
    'Haar graph SL(2,163) x Z199, S = {e} + 2 orbits of size 3 (ORBIT "3 2 1"; 9 evaluations from a random start, squad '
    'r3/e15); earlier 1,709,227,632 (PSL(2,167) x Z367, a random symmetric S, r2/d15) and 1,694,979,936 (SL(2,233) x '
    'Z67, r1/c15); beyond-d13: 1,674,490,944',
    f'haarcheck_gen VALID ({C}d7D14_sl_163_199_orb3-2-1_e15.gen.txt)',
    'Haar size law at mu = 5: 2N = 1.66e+09')
ROWS[(3, 13)] = (4324,
    'regular voltage lift of a 2+2 cubic base over the Frobenius group Z47 x\\|_2 Z23 (order 1,081), base and voltages '
    'annealed together (salift_s, 30 CPU-s; director, job beyond-d14); not a Haar graph. Earlier 3,612 (2+2 base over '
    'Z43 x\\|_9 Z21, beyond-d14) and 3,400 (beyond-d13: Z170 lift of GP(10,3)); Foster census: CSS(2800,3)',
    f'apsp VALID, diameter exactly 13 ({G}d3D13_n4324_lift2_meta47_23_2.apsp.txt)',
    'Haar size law at mu = 5: 2N = 2.89e+03')
ROWS[(9, 14)] = (20002113120,
    'Haar graph PSL(2,241) x Z1429, S = three free alpha-orbits of size 3 (ORBIT "3 3 0", haar_big0 f = 0): the first '
    'random symmetric S at N = 1.0e10 (size-law order for this cell ~2.8e10, so mu ~ 0); director. New cell (nothing was '
    'recorded at Δ = 9, D = 14; the floor from (8,14) was 11,325,238,056)',
    f'haarcheck_gen VALID from (e,A) and (e,B), 2,858 s ({C}d9D14_psl_241_1429_orb3-3-0_s1.gen.txt)',
    'Haar size law at mu = 5: 2N ~ 5.6e+10')
