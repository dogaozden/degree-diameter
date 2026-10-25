# uni11: structured partial ovoids of the elliptic section E (cell-14-7, second session, Opus)

Partial ovoids of E = {x4 = -C x0} ∩ Q(6,q) (pairwise non-orthogonal points) as unions of orbits of a group acting on
E, scored with `orbitclique_q` (= ../orbitclique.c with Q from the environment; `Q=q ./orbitclique_q ../../data/Eq.map
PERM SECONDS SEED OUT`). A permutation file lists the image of each point of the map; only its cycles are used, so a
non-cyclic group is passed as a permutation whose cycles are its orbits.

| script | group | best |
|---|---|---|
| sample11.py | random isometries of order 11k (unipotent part), q = 11 | 221 |
| class4.py, recover.py, inv4.py | order-4 classes at q = 11; recovers the isometry behind ../sols/flags_q11_orbit4_240.txt: 1 on A = (x0,x3), J (J^2 = -1) on V4 = (x1,x2,x5,x6) | — |
| permq.py | g = R^k ⊕ J (explicit), prime q | q = 11: 240 (90 s run); q = 7: 88; q = 13: 206–218 |
| permq2.py | similitudes sqrt(nu) on V4 with a similitude of A (q = 1 mod 4) | q = 13: ≤ 212 |
| grpperm.py | subgroups K of SL(2,q) acting by right multiplication on V4 = M2(F_q) | q = 11, K = 2.A5: 2 orbits = 240; q = 5, K = 2.A4: 48; q = 7, K = 2.S4: 48; orders 6–28: q = 7 ≤ 80, q = 11 ≤ 240, q = 13 ≤ 224 |
| permq3.py | twisted cyclic groups R^a ⊕ Y^m (Y elliptic of order q + 1 in SL(2,q)) | see tw*.log |
| stab98.py, hyp49.py | stabilizer (order 336) and centers of the q = 7 98 set | — |
| psl2.py, pgl2.py, psl2sub.py | PSL/PGL(2,q) and subgroups on the quartic model Sym^4 ⊥ <n0> | q = 7: 98 (14 + 84 orbits); q = 11: PSL 12, 2.A5 240; q = 5: 30 |
| hoffman.py | ratio bound inside one square class (q = 7: 300, too weak to help) | — |

Logs: logs/, kbatch1.log, tw*.log, class4_s3.log. Flag files: flags/ (check with `CHECKONLY=1 ../pack ../../data/gh_q.txt 0 1
/dev/null FLAGS`).
