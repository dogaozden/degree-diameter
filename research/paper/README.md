# Joint paper draft (Araujo-Pardo, López, Özden)

- `joint.tex`: first full draft, assembled from the refereed notes (job paper-joint, branch
  `claude/joint-paper-draft-07dyt1`). Build with `tectonic joint.tex`.
- `joint.pdf`: the compiled draft. The list of points for the co-authors (the `\todo` notes) is at the start.

Sources, each with its referee report applied:

| paper section | source note (branch) | referee |
|---|---|---|
| 2.3, 3, 4, 5, 8.2 | `research/theorems/POLISHED.md` (`claude/thm-polish-2oddll`) | `research/referee/polish-2026-10-25.md` (`claude/referee-polish-2026-10-25-dftm26`) |
| 6 | `research/theorems/D7_HEXAGON.md` (`claude/d7-hexagon-theorems-4w1prt`) | `research/referee/d7-2026-10-25.md` (`claude/referee-d7-hexagon-theorems-hewag2`) |
| 7 | `research/theorems/OMEGA_NOTE.md` (`claude/omega-d8-note-xrbqux`) | omega-dq and omega-repair referees, applied in the note |
| 8.3 | `research/theorems/HAAR_D8_10.md` (`claude/thm-haar-d8-10-sf7f0a`) | `research/referee/haar-2026-10-25.md` (`claude/referee-haar-d8-10-jhckxf`) |
| App. B | `research/lean-maxx/VERIFY*.md` (`claude/leanmaxx-verify-*`), `research/projects/lean-all/STATUS.md` (`claude/lean-all-jvj7b0`) | |

What the draft adds to the notes: the arrangement, connecting text, the note-to-paper numbering map (a todo near the
start), Corollary 6.23 (all levels of type H for every r; suggested by the diameter-7 referee, who built two cases), and
the prior-work paragraphs collected from the notes' literature sections.

## Checks of the draft's text (`checks/`)

Written from the paper's own definitions (not from the lab's builders), to catch transcription errors:

- `hat4.py`: Definition 3.1 and Table 2 (degrees), Theorem 3.2 for q = 5, 7 (all (a, c)) and q = 11: order, maximum
  degree, the filler makes it regular, diameter 3.
- `thmA.py`: AS(q) in the coordinates of Section 4.2, Theorem 4.7 (every line meets the two quadrics in 2 points) and the
  graph of Corollary 4.8 for q = 3, 5, 7: orders 90, 350, 882, regular, diameter 4.
- `singer.py`: the cyclic model of Section 4.3 for q = 3, 5: Proposition 4.10 (exactly the pairs {a, q-a} are 2-ovoids),
  the spread {yK}, Corollary 4.12 and its regular completion (orders 120, 416, diameter 4).
- `thmD.py q c c0 c1`: H(q) from Tits' equations (2.1), Lemma 5.1(d), Theorem 5.5 (the whisker rule is exact) and the
  doubling of Theorem 5.3 with m = 2: q = 3 gives order 1020, maximum degree 5, diameter 6; q = 5 (c = 2, (c0, c1) = (1, 0))
  gives |W| = 600, exact, and the (7,6) graph: order 9592, maximum degree 7, diameter 6 (log `checks.log`).

- `app359.py`: Appendix A parsed from the paper's verbatim block: all 21 rows are lines of Q(4,5), exactly the four
  stated ovoid points lie on two rows, the starred copy is on the second row; the graph has 359 vertices, maximum degree 7,
  diameter 4.
- `cor_r.py`: Corollary 6.23 (the one statement not taken from a refereed note) at q = 5, r = 2: five levels of H(5),
  R the 26 points of an elliptic quadric section, R* 26 lines of a Hermitian spread, sigma built as in Proposition 6.17
  ((H1)-(H3) re-checked), 7 hubs per colour on the Fano plane. `apsp.c` (all pairs): 39,074 vertices, bipartite, maximum
  degree 8, diameter 7. (This cell, (8,7), is not a record; the check is of the corollary.)

Besides these, a script compared every formula of Sections 2-7 with the source notes (all differences are intended
renames or new connective text), and the 34 rows of Table 8 with the Haar note's table (all equal).
