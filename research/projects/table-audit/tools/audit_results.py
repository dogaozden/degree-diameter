"""Per-cell audit results (table-audit) -> results.json, then cells.csv via gen_cells.py.
Each entry: source (who / where), construction, rebuilt (yes = the table's construction rebuilt at exactly the table
order; order = a graph of exactly the table order built another way; no), check (checker and log), flag, notes.
Logs are in ../checks/ (CHECKS.md lists every command)."""
import json, os, sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
R = {}


def put(d, D, **kw):
    R[f'{d},{D}'] = kw


PRIME_POWERS = {3: 2, 4: 3, 5: 4, 6: 5, 8: 7, 9: 8, 10: 9, 12: 11, 14: 13}
for d, q in PRIME_POWERS.items():
    put(d, 3, source='classical: incidence graph of PG(2,%d)' % q, construction='PG(2,q) incidence graph, q = %d' % q,
        rebuilt='yes', check='apsp.c VALID (checks/moore_pg_w.txt)', notes='bipartite Moore graph, optimal')
    put(d, 4, source='classical: incidence graph of the generalized quadrangle W(%d) (Tits)' % q,
        construction='W(q) incidence graph, q = %d' % q, rebuilt='yes', check='apsp.c VALID (checks/moore_pg_w.txt)',
        notes='bipartite Moore graph, optimal')
    put(d, 6, source='classical: incidence graph of the split Cayley hexagon H(%d) (Tits 1959)' % q,
        construction='H(q) incidence graph from Tits coordinates, q = %d' % q, rebuilt='yes',
        check='apsp%s VALID (checks/%s)' % ('_mt.c' if q >= 9 else '.c', 'h_%d.apsp.txt' % q if q >= 9 else 'moore_h_small.txt'),
        notes='bipartite Moore graph, optimal')

put(3, 5, source='Bar-Yehuda-Etzion, Discrete Appl. Math. 37/38 (1992) 29-43, Appendix B; Bond-Delorme, Ars Combin. 25C (1988)',
    construction='two 28-cycles plus (j,0)~(j+F(j mod 4),1), F = (12,0,8,20)', rebuilt='yes',
    check='apsp.c VALID (checks/small.txt); also an independent annealed graph (graphs/d3D5_n56_anneal.edges.txt)',
    notes='optimal (Jorgensen 1993; also Feria-Puron-Pineda-Villavicencio 2012)')
put(7, 3, source="Hafner (adjacency list on his page https://www.math.auckland.ac.nz/~hafner/bipartite/7.3) and Loz",
    construction="Hafner's graph; also a Haar graph of Z5 x| Z8 found here (graphs/d7D3_n80_meta_5_8_2_x1.sol)",
    rebuilt='yes', check="apsp.c VALID on Hafner's file and on the Haar graph (checks/small.txt)",
    notes='optimal (Feria-Puron-Miller-Pineda-Villavicencio 2013, Thm 4.1)')
put(3, 7, source="Conder-Nedela (census graph C168.1, |Aut| = 504, 1-arc-regular, girth 12); also DGQ, Loz; Conder's file on Hafner's page (mdec3.7)",
    construction='C168.1 from Conder\'s census symmcubicgraphs.tar.gz', rebuilt='yes',
    check="apsp.c VALID on C168.1 and on Hafner's mdec3.7 (checks/small.txt)", notes='unbeaten by the repo')
put(4, 5, source="Hafner (file 4.5, 'Bond-Delorme construction', vertex-transitive, |Aut| = 160) and Loz",
    construction="Hafner's adjacency list", rebuilt='yes', check='apsp.c VALID (checks/small.txt)')
put(4, 7, source="Hafner (file 4.7, 'Bond-Delorme construction', vertex-transitive, |Aut| = 2520) and Loz",
    construction="Hafner's adjacency list", rebuilt='yes', check='apsp.c VALID (checks/small.txt)')

put(11, 3, source='Feria-Puron-Miller-Pineda-Villavicencio, Discrete Math. 313 (2013) (three Haar graphs Phi_95); Araujo-Pardo-Lopez (2022) Thm 1',
    construction='Phi_95(4,7,16,27,38,52,62,81) etc.; AL graph R_9 = PG(2,9) + 8 vertices', rebuilt='yes',
    check='apsp.c VALID on all three Phi_95 and on R_9 (checks/small.txt)')
for d, q in ((13, 11), (15, 13)):
    put(d, 3, source='Araujo-Pardo-Lopez, Graphs Combin. (2022), arXiv:2005.02427, Thm 1 (order 2(q^2+q+5))',
        construction='R_q = PG(2,%d) + 8 vertices, rewired (problems/bipartite_dd/lib.py)' % q, rebuilt='yes',
        check='apsp.c VALID (checks/small.txt)',
        notes='wiki changed 270 -> 274 / 370 -> 374 on 30 Mar 2021; its percentage column was not updated' )
put(16, 3, source='wiki: Delorme-Farhi duplication (no paper names this value; Delorme 1985 JGT not read)',
    construction='PG(2,13) plus copies (Delorme-Farhi 1984) of the 14 points of a conic and of its 14 tangent lines; '
                 'each copy joined to the original neighbours (tools/delorme.py d3)',
    rebuilt='order', check='apsp.c VALID (checks/small.txt)',
    notes='a duplication of exactly this order and degree; whether it is the graph the table had in mind is not documented')
for d, q in ((7, 5), (11, 9), (13, 11), (15, 13)):
    put(d, 4, source='Delorme, Europ. J. Combin. 6 (1985) 291-302, Sec. 8(a) (example q = 5: 312 + 34 = 346)',
        construction='W(%d) + spread {<X,AX>}; doubling of A0 = spread + points of one spread line, A1 = that line' % q,
        rebuilt='yes', check='apsp.c VALID (checks/small.txt)')
put(16, 4, source='Delorme 1985 Sec. 8(a) sets with Sec. 7 tripling, q = 13 (arithmetic matches; not stated in the paper)',
    construction='W(13) + spread, tripling (b = 3)', rebuilt='yes', check='apsp.c VALID (checks/small.txt)')
for d, q in ((7, 5), (11, 9), (13, 11), (15, 13)):
    put(d, 6, source='Delorme 1985 Sec. 8(b) (example q = 5: 7812 + 912 + 2(132) + 4 = 8992)',
        construction='H(%d) + Hermitian spread (Thas 1980); doubling A0 > A1 > A2' % q, rebuilt='yes',
        check='apsp%s VALID (checks/%s)' % ('.c' if q == 5 else '_mt.c', 'small.txt' if q == 5 else 'd6_q%d_b2.apsp.txt' % q))
put(16, 6, source='Delorme 1985 Sec. 8(b) sets with Sec. 7 tripling, q = 13 (arithmetic matches; not stated in the paper)',
    construction='H(13) + Hermitian spread, tripling (b = 3)', rebuilt='yes', check='apsp_mt.c VALID (checks/d6_q13_b3.apsp.txt)')

for d, q, j in ((10, 7, 2), (11, 8, 2), (12, 9, 2), (13, 9, 3), (14, 9, 4), (15, 11, 3)):
    put(d, 5, source='wiki: Delorme-Gomez-Quisquater, "On large bipartite graphs" (submitted; never found)',
        construction='%d copies of W(%d) linked by %d bijections points -> lines (polygon cover, Z_%d voltages 1..%d)' % (2 * j + 1, q, j, 2 * j + 1, j),
        rebuilt='order', check='apsp.c VALID (checks/small.txt)',
        notes='the value is exactly (2j+1)|GQ(q)| with Delta = q+1+j; the cover has diameter <= 5 for any bijections '
              '(proof in tools/xt_build.py); the original paper is unavailable, so this is a construction of the same order, '
              'probably the same family')
put(16, 5, source='wiki: Delorme-Gomez-Quisquater (unpublished)', construction='none traced (27300 = 10*13*14*15 is the only arithmetic fit found)',
    rebuilt='no', check='', flag='no traceable construction',
    notes='superseded: repo record 33,792 (route-chart lift) and the A4(3) flag graph 31,460 (Cames van Batenburg-Korsky 2026)')
for d, q in ((6, 5), (8, 7)):
    put(d, 7, source='Delorme 1985 Sec. 9 (insertion of vertices on edges, then q-1 duplications; order 2q(q^4+q^3+3q^2+q+1)); '
                     'the wiki colours it Delorme-Gomez-Quisquater',
        construction='H(%d), subdivide the 2q^3 edges between distance 2 and 3 from an edge, q copies of the distance <= 2 part' % q,
        rebuilt='yes', check='apsp.c VALID (checks/small.txt)', flag='attribution: the wiki credits DGQ; the construction and order are in Delorme 1985 Sec. 9')
for d, q, j in ((7, 5, 1), (9, 7, 1), (10, 8, 1), (11, 9, 1), (12, 9, 2), (13, 11, 1), (14, 11, 2), (15, 11, 3), (16, 13, 2)):
    put(d, 7, source='wiki: Delorme-Gomez-Quisquater, "On large bipartite graphs" (submitted; never found)',
        construction='%d copies of H(%d) linked by %d bijections points -> lines' % (2 * j + 1, q, j),
        rebuilt='order', check='apsp_orb.c VALID (level shift checked as an automorphism; checks/x7_d%d.apsp.txt)' % d,
        notes='exactly (2j+1)|H(q)|, Delta = q+1+j; diameter <= 7 for any bijections (hexd7 Lemma, tools/xt_build.py)')
D8 = {10: (7, 2, 30), 11: (8, 2, 30), 12: (9, 2, 35), 13: (11, 1, 15), 14: (11, 2, 40), 15: (11, 2, 40), 16: (13, 2, 45)}
GOMEZ = ('J. Gomez Marti, PhD thesis "Diametro y vulnerabilidad en redes de interconexion", UPC Barcelona 1986, '
         'Sec. 2.9.3 (graphs Omega H_q, Fig. 2.21; scan at web.mat.upc.edu/francesc.comellas/delta-d/papers/Gomez1986-PhD-red.pdf, '
         'thesis p. 44-46); wiki: Delorme-Gomez-Quisquater, "On large bipartite graphs" (submitted; never found)')
for d, (q, j, m) in D8.items():
    if d == 13:
        put(d, 8, source='wiki: Delorme-Gomez-Quisquater (unpublished); not in Gomez 1986',
            construction='none traced; value = 15|H(11)| with Delta = q+2', rebuilt='no', check='',
            flag='no traceable construction', notes='superseded by a verified repo record')
        continue
    put(d, 8, source=GOMEZ,
        construction='Omega H(%d): %d copies of H(%d) in groups of 5 plus 10 hubs per point/line pair (degree %d); '
                     'the thesis lists N(%d,8) >= %s' % (q, m - 5, q, d, d if d != 15 else 14, f'{m * 2 * (q ** 6 - 1) // (q - 1):,}'),
        rebuilt='no', check='as read, diameter 9 (checks/omega_D8.txt)',
        flag='does not check out as read: diameter >= 9',
        notes=('the (14,8) value reused (degree 14 <= 15); the thesis also claims N(15,8) >= 14,978,080 (Omega H_11 d); ' if d == 15 else '') +
              ('the thesis claims D <= D_1 + 2 = 8, but under my reading of Fig. 2.21 a hub reaches at most %s of the %s points of a copy it does not touch within 7 steps '
               '(tools/omega_bound.py), and Omega H(7) built at 1,176,480 vertices has eccentricity 9; ' % (
                   {7: '16,249', 8: '26,487', 9: '41,009', 11: '87,297', 13: '165,097'}[q], f'{(q ** 6 - 1) // (q - 1):,}')) +
              ('unbeaten by the repo' if d in (10, 12, 14, 15, 16) else 'superseded by a verified repo record'))
put(3, 8, source='wiki: Delorme-Gomez-Quisquater (unpublished)',
    construction='found here (squad table-audit-r1): a lift of the cube Q3 over Z32 (c3) and a Z32-symmetric annealed graph (c6), '
                 'both 256; also 258 (K33 over Z43)', rebuilt='order', check='apsp.c VALID (checks/small.txt)',
    flag="holder's construction lost; order reproduced",
    notes='not a symmetric cubic graph (Conder census); superseded by the repo record 288')
put(3, 10, source='wiki: Delorme-Gomez-Quisquater (unpublished)',
    construction='found here (lead, after squad table-audit-r2): a Z80-lift of a cubic bipartite base multigraph on 5 + 5 '
                 'vertices (squads/table-audit-r1/c6/sym_anneal.c, b = 10, c = 80, seed 11; graphs/d3D10_n800_symZ80_b10.edges.txt)',
    rebuilt='order', check='apsp.c VALID (checks/small.txt)', flag="holder's construction lost; order reproduced",
    notes='not a symmetric cubic graph; Conder\'s 720 (C720.3) and Bar-Yehuda-Etzion\'s 672 are smaller; unbeaten by the repo')

LOZ = [(3, 9), (4, 8), (4, 9), (4, 10), (5, 5), (5, 7), (5, 8), (5, 9), (5, 10), (6, 5), (6, 8), (6, 9), (6, 10), (7, 5), (7, 8),
       (7, 9), (7, 10), (8, 5), (8, 8), (8, 9), (8, 10), (9, 5), (9, 8), (9, 9), (9, 10)] + \
      [(d, D) for d in range(10, 17) for D in (9, 10)]
for d, D in LOZ:
    put(d, D, source='wiki: Loz, project of Loz, Perez-Roses, Pineda-Villavicencio (voltage lifts; DS14v2 ref. [240]); '
                     'thesis restricted, data page gone', construction='no voltages, groups or base graphs published',
        rebuilt='no', check='', flag='no traceable construction (data lost)', notes='')

OMEGA2 = ('round 2: with a free relabelling of each copy (not in the thesis) Omega H(q) reaches diameter 8 at q = 2 and 3 '
          '(omega/NOTES.md, checks/omega_labelled.txt); at q = 4, 5 no labelling was found (G-equivariant annealing, squad '
          'table-audit-2-r1); a counting bound does not exclude labellings at any q (union bound / n = 4.3 at q = 7, 3.7 at q = 9)')
ROUND2 = {
    '10,8': dict(check='as read, diameter 9 (checks/omega_D8.txt); witness pair d(980400, 20073) = 9 (checks/witness_omega_thesis.txt)',
                 flag='INVALID as read (witness pair saved); no labelling known that gives diameter 8', notes=OMEGA2),
    '13,8': dict(notes='round 2: in the table since the first wiki revision (17 Jan 2012) in DGQ green; not bold in Perez-Roses 2012 '
                       'Table 5.1, so not from Loz\'s voltage search; Perez-Roses cites DGQ "On large bipartite graphs" as an '
                       'unpublished manuscript (2011); 5,314,680 = 5*(13,7) = 15|H(11)|, but Omega H(11) has degree 14 '
                       '(lit/LITERATURE2.md)'),
    '16,5': dict(notes='round 2: in the first wiki revision (2012), DGQ green, not from Loz\'s search (Perez-Roses 2012); '
                       'above every (2j+1)|GQ(q)| at degree 16 (best 26,352); Delorme-Gomez 2002 (EJC) not reachable from here '
                       '(lit/LITERATURE2.md)'),
    '3,7': dict(notes='round 2: optimal among vertex-transitive graphs: every bipartite cubic vertex-transitive graph on 169..248 '
                      'vertices (1,825, census of Potocnik-Spiga-Verret) has diameter >= 8 (checks/cvt_census.txt); upper bound '
                      '248 = Moore - 6 (Feria-Puron-Pineda-Villavicencio 2012); no exhaustive search or later improvement found'),
    '3,9': dict(notes='round 2: the largest bipartite cubic vertex-transitive graph of diameter <= 9 has 506 vertices (census, '
                      'stored diameters <= 11 rechecked, checks/cvt_census.txt); upper bound 1,016 = Moore - 6 (FPV 2012); bold '
                      '(Loz project) in Perez-Roses 2012 Table 5.1; no later improvement found'),
    '4,8': dict(notes='round 2: upper bound 6,554 = Moore - 6 (FPV 2012); bold (Loz project) in Perez-Roses 2012; no exhaustive '
                      'search or later improvement found'),
    '4,9': dict(notes='round 2: upper bound 19,676 = Moore - 6 (FPV 2012); bold (Loz project) in Perez-Roses 2012; no exhaustive '
                      'search or later improvement found'),
    '6,5': dict(notes='round 2: upper bound 1,556 = Moore - 6 (FPV 2012); bold (Loz project) in Perez-Roses 2012; no exhaustive '
                      'search or later improvement found'),
}
for d in (11, 12, 14, 15, 16):
    ROUND2[f'{d},8'] = dict(flag='INVALID as read (diameter >= 9 for every pairing, tools/omega_bound.py; witness pair for '
                                 'q = 7 in checks/witness_omega_thesis.txt, for q = 9 on branch own-12-8); no labelling known '
                                 'that gives diameter 8', notes=OMEGA2)
for k in ('3,9', '4,8', '4,9', '4,10', '5,5', '5,7', '5,8', '5,9', '5,10', '6,5', '6,8', '6,9', '6,10', '7,5', '7,8', '7,9', '7,10',
          '8,5', '8,8', '8,9', '8,10', '9,5', '9,8', '9,9', '9,10') + tuple(f'{d},{D}' for d in range(10, 17) for D in (9, 10)):
    if k not in ROUND2:
        ROUND2[k] = dict(notes='round 2: bold (Loz project) in Perez-Roses 2012 Table 5.1; no groups or voltages survive there')

if __name__ == '__main__':
    extra = json.load(open(sys.argv[1])) if len(sys.argv) > 1 else {}
    for k, v in extra.items():
        cur = R.setdefault(k, {})
        if cur.get('rebuilt') == 'yes' and v.get('rebuilt') == 'order':     # keep the holder's own graph, note ours
            cur['notes'] = (cur.get('notes', '') + '; also ' + v['construction']).lstrip('; ')
            continue
        cur.update(v)
    assert len(R) == 112, len(R)
    # round 2 (table-audit-2, 2026-10-26): notes appended after the merge, flags overridden where stated
    for k, v in ROUND2.items():
        cur = R[k]
        if 'notes' in v:
            cur['notes'] = (cur.get('notes', '') + '; ' + v['notes']).lstrip('; ')
        for f in ('flag', 'check', 'source', 'construction', 'rebuilt'):
            if f in v:
                cur[f] = v[f]
    import re
    for k, v in R.items():          # a check whose log is missing or has no VALID line is not claimed
        for log in re.findall(r'checks/([\w.]+\.txt)', v.get('check', '')):
            path = os.path.join(HERE, 'checks', log)
            if 'VALID' in v['check'] and (not os.path.exists(path) or 'RESULT VALID' not in open(path).read()):
                v['check'] = 'PENDING (log not complete): ' + v['check']
                break
    json.dump(R, open(os.path.join(HERE, 'results.json'), 'w'), indent=1)
    print('results.json', len(R))
