# omega_note: the D = 8 note on Gómez's ΩH_q (job paper-omega)

- `../OMEGA_NOTE.md`: the note (Markdown). `OMEGA_NOTE.tex` / `OMEGA_NOTE.pdf`: typeset version (tectonic).
- Checks re-run for the note (no new searches):
  - `thm2_bound.py` (copied unchanged from the omega-dq referee): Theorem 2 constants A, B, both ways. Log `logs/thm2_bound.txt`.
  - `starved.py` (new) with `myroutes.py` (copied unchanged from the omega-repair referee): starved pairs and m₂ for
    α = 5, 6 (Computer-checked C4). `python3 starved.py 5; python3 starved.py 6`. Log `logs/starved_alpha5_6.txt`.
  - `types43.py` (new, written from scratch): the 17 configuration types of Lemma 5.9 at q = 7. Log `logs/types43_q7.txt`.
  - `typetable.py` (new): the rows (A, T, R₃, U, F, p) printed in Lemma 5.9. Log `logs/typetable_q7.txt`.
