# Squad round r3-smallfam (thm-smallfamilies resume, 2026-10-25): literature and referee checks

The main session's write-up is `research/theorems/SMALL_DEGREE_FAMILIES.md` (repo /home/user/degree-diameter). This
round does not search for graphs. It checks two things: is our new theory already known, and is it right. The 4 cores
are busy with the main session's searches, so **run nothing heavier than a few seconds of Python**.

## Rules
- No git commands. Do not edit anything outside your card folder `research/squads/r3-smallfam/cX/`; write notes and
  small test scripts there.
- Never contact anyone or post anything; reading web pages and searching is fine. If a site refuses (HTTP 403), say
  so and move on; do not try to get around it.
- Time box: 20 minutes.
- **Quote, don't paraphrase.** For every literature claim give the URL and the exact sentence you read. Mark
  anything you did not read yourself as UNVERIFIED.
- When done, append ONE line of JSON to `research/squads/r3-smallfam/scoreboard.jsonl`:
  `{"card": "cX", "question": "<one line>", "answer": "<one or two lines>", "evidence": "<URLs or file:line>", "confidence": "high|medium|low", "next": "<one line>"}`
- Reply in at most 6 lines.

## Cards
- **c1, literature (metacyclic bounds).** §2.3 of the write-up proves a "fibre bound": for G = Z_p ⋊_r Z_k with
  o = ord r, Haar graphs of diameter D satisfy p ≤ min_J |W_J|, where W_J is a set of walk values in the universal
  group Z[ζ_o]^(Δ−2) ⋊ Z_k. §2.4 proves N ≤ (2D+1)^((o+1)(Δ−1)) for metacyclic groups of action order o.
  - Is either result, or anything equivalent, already published?
  - Start with H. Macbeth, J. Šiagiová, J. Širáň, "Cayley graphs of given degree and diameter for cyclic, Abelian,
    and metacyclic groups", Discrete Math. 312 (2012) 94–99. Its abstract mentions "a result for Cayley graphs of
    metacyclic groups for general degree and diameter". What exactly is that result: an upper bound or a
    construction? Look for an author copy, arXiv version, thesis or slides.
  - Also check Dougherty–Faber (arXiv:math/9412223) and any later work on upper bounds for Cayley graphs of
    metacyclic or virtually abelian groups.
- **c2, literature (who built the open cells).** Find how these were constructed:
  - the bipartite (3,10) table graph on 800 vertices (Delorme, Gómez and Quisquater, "On large bipartite graphs",
    possibly unpublished);
  - the (3,7) 168 graph (Conder–Nedela);
  - any bipartite (Δ, D) result after 2012 that beats the CombinatoricsWiki table at (3,7), (3,9), (3,10), (4,8)
    or (4,9).
  Useful facts go in `c2/notes.md`, with URLs and quotes.
- **c3, referee §2.3 (the fibre bound).** Read §2.2 (normal form) and §2.3 of the write-up and
  `research/theorems/smallfam/cyclobound.py`.
  - Check the proof step by step: the normal form, that φ is a homomorphism, that balls map onto balls, the fibre
    count, and the admissibility and unit-scaling reductions.
  - Check that the code implements exactly that universal group: the product rule, the generators, the inverse
    step for the B side, and the fibre count.
  - You may run `python3 research/theorems/smallfam/cyclocheck.py 3 5 10` (seconds) and small hand examples.
  - Report any real gap or bug, with the exact line.
- **c4, referee §2.4 and the (3,7) theorem.** Read §2.2 ("Lifts and free actions"), §2.4 and the (3,7) bullet of
  §2.5.
  - Check the growth inequality N ≤ (2D+1)^((o+1)(Δ−1)): the universal group, the homomorphism and the counting.
  - Check the logic of "no cubic bipartite graph with more than 168 vertices and diameter 7 has a colour-preserving
    group acting freely with at most 6 vertex orbits".
    - Are all bases with at most 6 vertices covered: the dipole, the 2+2 base, and the three 3+3 bases?
    - Is the claim that every such graph is a lift of its quotient correct?
    - Are the group-order ranges right against the Moore bound 254?
    - Coverage is in `research/theorems/smallfam/runs/completeness_resume.txt`.
  - Report any real gap.
