# Remarks on D7_HEXAGON.md for readers of the lab's per-cell notes

Moved out of research/theorems/D7_HEXAGON.md (formerly its Section 12) on 25 October 2026, after the referee report
research/referee/d7-2026-10-25.md (issue 16), so that the note sent outside the lab does not depend on lab-internal terms.
Theorem letters follow the revised note: Theorem B is the automorphic-transition theorem (Section 4, formerly Theorem C)
and Theorem C the local-duality theorem (Section 5, formerly Theorem B). Nothing below is needed for the note's proofs.

*What changed relative to the per-cell notes.* Writing the proofs out gave one simplification: Theorem B replaces the
lab's conditions on freed sets at friendly transitions (non-collinear sets, and the "relaxed sets" with hypotheses (R1),
(R2) of research/d15D7b/RELAXED.md) by the single, weaker condition of being a segment set. The lab's (12,7) notes
(research/squads/cells/d12D7.md §2) state the same condition for transitions matched by a duality and check it by
computer at $q = 9$; Theorem B proves it and transfers it to friendly transitions. The record graphs are unaffected (they
satisfy the stronger hypotheses and were checked by computer in full), but larger sets are now allowed (Remark 9.4 of the note).

*Why the lab's (R2) was not needed.* The lab proof of the relaxed theorem (RELAXED.md, cases 4 and 5) only used paths
whose matching edge sits at a point collinear with the freed point $r$. When $r$ has a partner $x$ and the target is a
line $u$ with $d(r,u) = 5$ and geodesic $r - y - x - y_2 - w_2 - u$, the only such point is $x$ (freed), and (R2) supplies
a hub. The path through $w_2$ (at distance 4 from $r$) avoids this: $w_2$ is collinear with $x$, so it is not freed (else $x$
would have two partners), and $(r,j')\leadsto(w_2,j')\to(w_2,j)\to(u,j)$ has length $4+1+1 = 6$. This is the first step of the proof of Lemma 4.1 (a point and a line at distance 5: three
points in a row on the geodesic).

*Hubs in Theorem C.* The earlier version of Theorem C (research/d13D7/REPORT.md §2, with $R$ pairwise opposite) routed
case 6 through the hub of $x$ in two levels. The route of case 6 in the proof of Theorem C uses no hub, which is what lets hubs take their
slots from different freed elements in different levels (Definition 3.1).

