# Handoff: job cell-14-7 (third session 01S9fS5Zi4bymqvTfraD7hJx, branch claude/cell-14-7-record-5d03gb, PR #317)

State at the end of the session (details: research/squads/cells/d14D7.md, research/cell147/mirror/README.md,
research/cell147/mirror/RECHECK.md, research/theorems/MIRRORED_SURGERY.md):

- (14,7) best **1,774,632** (master had 1,774,584), apsp_orb VALID. Mirrored surgery with 768 freed points.
- Bonus cells, all-pairs or apsp_orb VALID: (7,7) 23,598, (9,7) 118,238, (10,7) 225,152, (13,7) 1,064,472.
  (15,7) 2,484,792 and (16,7) 4,025,592: built, multi.c checks pass; full-check status in research/cell147/mirror/checks/.
- q = 11 plateau: F = 12 extra points from three methods (squad r6 c1, c2, c3). Partial ovoids: 756 is the W(E7)
  orbit, every symmetric search returns it.

If resumed, the most promising directions:
1. q = 13 / (16,7): the annealer stalls at F = 21 but there is much more room (spread 2,198 lines, extra points at
   distance 4 from 24–48 base points). A better search (c3's two-stage method, ILP on fixed lines) should give more;
   each point is +4 at (16,7). Tools: mirror_sa5.py / mirror_build2.py with --hex hex_q13.bin, R792, S_q13.
2. q = 11 / (14,7): beyond F = 12 needs co-designed structure on both sides. One idea: move R756 by an isometry so
   that its stabiliser meets the hexagon's G2(11) in a large group H (e.g. a G2(2) built from the split octonions),
   fix a Hermitian spread invariant under H, and look for H-orbits of extra points and lines whose cross relations
   match (orbit-level types).
3. The other D = 7 hexagon cells take the same tools in minutes (q = 5, 7, 8: small F; q = 9 uses a true duality).
Scratch files are not kept: rebuild hexagons with research/d13D7/hexgen.c / hexgen2.c, graphs from the .sol files.
