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
ROWS[(5, 14)] = (13467134,
    'Haar graph of the metacyclic group Z100501 x\\|_52125 Z67 (m prime, order 6,733,567), S random: a cost-1 hmeta state '
    '(r3/e10) moved by the hole-directed finisher and closed by a low-temperature anneal (T0 0.5, T1 0.1, TARGP 90, K 4; '
    'squad r5/g02); earlier 13,156,186 (Z83267 x\\|_31904 Z79, r4/f09), 13,105,798 (Z152393 x\\| Z43, r1/c08) and '
    '12,991,752 (PSL(2,163) x Z3, order-2 orbit S, r1/c11); beyond-d13: 12,795,166',
    f'build_haar2 VALID ({C}d5D14_meta_100501_67_g02.build_haar2.txt)',
    'Haar size law at mu = 5: 2N = 1.27e+07')
ROWS[(6, 14)] = (193539888,
    'Haar graph SL(2,107) x Z79, S = 2 free orbits of size 3 (ORBIT "3 2 0"): best of 60 random symmetric S (cost 4), '
    'then a short anneal (squad r5/g09); earlier 193,333,056 (SL(2,113) x Z67, a random symmetric S, r3/e12), 192,314,952 '
    '(PSL(2,107) x Z157, r2/d13) and 190,269,984 (SL(2,137) x Z37, r1/c12); beyond-d13: 187,990,656',
    f'haarcheck_gen VALID ({C}d6D14_sl_107_79_orb3-2-0_g09.gen.txt)',
    'Haar size law at mu = 5: 2N = 1.83e+08')
ROWS[(7, 14)] = (1732018320,
    'Haar graph SL(2,179) x Z151, S = {e} + 2 orbits of size 3 (ORBIT "3 2 1"): z-filtered random symmetric S, then a '
    'low-temperature anneal from a cost-3 state (squad r4/f15); earlier 1,723,572,432 (SL(2,163) x Z199, r3/e15), '
    '1,709,227,632 (PSL(2,167) x Z367, r2/d15) and 1,694,979,936 (SL(2,233) x Z67, r1/c15); beyond-d13: 1,674,490,944',
    f'haarcheck_gen VALID ({C}d7D14_sl_179_151_orb3-2-1_f15.gen.txt)',
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
ROWS[(3, 12)] = (2436,
    'regular voltage lift of a 2+2 cubic base over Z87 x\\|_7 Z7 (order 609), base and voltages annealed together '
    '(salift_s; squad r5/g14, job beyond-d14); not a Haar graph. The lab record before was 2,368 (4+4 base over '
    'Z37 x\\|_6 Z8, job own-small, research/squads/own-small/records/); earlier rows of this table: 2,176 (metacyclic Haar)',
    f'apsp VALID, diameter exactly 12 ({G}d3D12_n2436_lift2_meta87_7_7.apsp.txt)',
    'Haar size law at mu = 5: 2N = 1.61e+03')
ROWS[(10, 14)] = (20002113120,
    'the (9,14) graph: Haar graph PSL(2,241) x Z1429 (maximum degree 9 <= 10). A 10-regular Haar graph PSL(2,239) x Z1789 '
    'with S = {e} + three alpha-orbits (24,422,855,520 vertices) had cost 0 at the first random S, but its check was stopped '
    'unfinished (sols/d10D14_psl_239_1789_orb3-3-1_s1.txt); director, job beyond-d14. New cell',
    f'haarcheck_gen VALID for the (9,14) graph ({C}d9D14_psl_241_1429_orb3-3-0_s1.gen.txt)',
    'Haar size law at mu = 5: 2N ~ 2.3e+11')
