# Handoff: job cell-14-7 (third session 01S9fS5Zi4bymqvTfraD7hJx, branch claude/cell-14-7-record-5d03gb, PR #317)

State at the end of the session (details: research/squads/cells/d14D7.md, research/cell147/typedmirror/README.md,
research/cell147/mirror/README.md, research/theorems/MIRRORED_SURGERY.md):

- (14,7) best **1,789,588**: master's typed five-level graph (cell-16-7 session, 1,788,052) plus this session's mirrored
  surgery (768 elements) on its four non-friendly transitions. Plain all-pairs check (apsp_mt): see
  research/cell147/typedmirror/checks/.
- (15,7) candidate **2,499,748** (master 2,497,075), same combination on nine non-friendly transitions; hypotheses and
  hub graph checked by the builder, BFS from all hubs; no full check (about 8 core-hours without symmetry).
- (13,7) **1,064,472** (master table 1,064,448), apsp_orb VALID: the mirrored set with r = 1. Typed levels do not help
  at three levels, so this one stands on its own.
- Earlier this session, all checked and now superseded or recorded: (14,7) 1,774,588 → 1,774,632 (mirrored surgery
  alone), (7,7) 23,598, (9,7) 118,238, (10,7) 225,152 (on master), (15,7) 2,484,792 (apsp_orb VALID).
- q = 11 plateau: F = 12 extra points from three methods; an exact one-pair extension test shows no F = 12 state extends.
  Partial ovoids: 756 is the W(E7) orbit; every symmetric search returns it.

If resumed, the most promising directions:
1. Bigger non-concurrent line sets of H(11). The (14,7) count is 10·177,156 + 2·(|R_L| + 768) while |R_L| < |R_H|, so
   each extra line is +2 (up to +798 at |R_L| = 8,645), and beyond that both sets must grow. The sets no longer need to
   be orbits of a group, since the combined graph is checked all-pairs anyway (1.8M vertices: about an hour on 4 cores).
   Both of master's sets are maximal already, so this needs exchange-move local search.
2. (16,7): the cell-16-7 graph (4,052,108, q = 13) frees only 2 orbits (122 elements) on its non-friendly transitions; the
   813-point q = 13 mirrored set from this session (research/frontier/sols/d16D7_hex13_mirror813_n4025592.sol) would give
   about +1,382. The obstacle is checking: 4M vertices without symmetry is about 44 core-hours, so it needs a group that
   preserves the friendly sets and the mirrored set, or a big machine.
3. Full check of the (15,7) 2,499,748 candidate (rebuild: tm_build.py build; check: apsp_mt g.edges 15 7 T).
Scratch files are not kept: rebuild hexagons with research/d13D7/hexgen.c / hexgen2.c, graphs from the .sol files.
