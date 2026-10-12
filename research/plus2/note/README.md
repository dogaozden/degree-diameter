# Note: the four-hat (+2) construction

`fourth-hat.pdf` (source `fourth-hat.tex`) is a short write-up of the +2 theorem for mathematicians: for every
projective plane of order q >= 4, a bipartite graph of order 2(q^2+q+6), maximum degree q+2 and diameter 3.
It restates the construction from `../REPORT.md` section 3 as six rules, gives the proof as four lemmas
(degrees, reduction, points, self-duality), and lists the computer checks in an appendix.

`verify_note.py` is a third independent implementation, written only from the six rules in the note. It checks order,
maximum degree and the two covering properties of the proof on random frames in PG(2,q) for q = 4..13, and runs the
two negative controls (no rotation, no H1-K0 link), which must fail.

Rebuild the PDF: `latexmk -pdf fourth-hat.tex` (in this folder).
