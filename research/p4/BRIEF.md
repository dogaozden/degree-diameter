# Problem 4 overnight (2026-10-19 11 PM → 2026-10-20 6:15 AM)

Araujo-Pardo and López (arXiv 2005.02427, Graphs Combin. 2022; text in research/p4/AL20.txt), Problem 4:
"Generalize our construction to construct bipartite regular graphs of diameters 4 and 6."
Their construction (Section 3, Theorem 1): start from the incidence graph of PG(2,q) (diameter 3, (q+1)-regular),
add 8 vertices ("hats") and a matching, get a (q+2)-regular bipartite graph of diameter 3 on 2(q²+q+5) vertices.
We improved it by 2 with a fourth hat (research/plus2/REPORT.md, research/plus2/note/fourth-hat.tex).

What we already have at diameter 4 (read research/NOTE.md fully): the copy lemma (Delorme–Farhi 1984), Delorme 1985's
ovoid copies (the old table values), our Theorem A (AS(q) + weighted 2-ovoid: 2q²(q+2), records at Δ = 11, 13, 15),
Theorem B (copies with stand-ins), Prop C (2-cover of Q(4,q): 2(q²+1)(q+3)). NOTE.md Section 8 lists open problems.
Diameter 6: research/gh6 (hexagon H(5) copies reached 8820/8890 vs the table's 8992 at Δ7·D6; Feit–Higman rules out an
AS-like hexagon of order (q−1,q+1)). Diameter 5: research/d5/REPORT.md (Haar graphs of groups; lemma
(S⁻¹S)² = G = (SS⁻¹)²; group tables in research/d5/groups.py; fast annealer haar_search3.c) gave 6 records.
Table values: Combinatorics Wiki, "The Degree Diameter Problem for Bipartite Graphs" (README.md and
records/bipartite_dd/CANDIDATES.md have some; look up the D = 4 and D = 6 rows you need and cite them).

## Shared rules (every agent)
- Your folder is research/p4/<your-area>/. Write only there. Do NOT run git; the main session commits your folder.
- Keep research/p4/<your-area>/REPORT.md current: update it at least every hour (results, numbers, what is next),
  so the 6:40 AM summary can use it even if you are still running. Wrap up by 6:15 AM.
- A graph counts only after `python3 scripts/verify_record.py <file.json> <Δ> <D>` prints VALID (same JSON format as
  records/bipartite_dd/*). Never call anything a record; say "beats the table value N" and give the file. The main
  session re-verifies independently.
- Novelty: say what is known (cite) and what you believe is new; do not overclaim.
- CPU: this Mac has 10 cores and a search batch is using 8 until ~1:36 AM. Locally use at most 2 cores, `nice -n 15`.
  For heavy compute you may launch up to 3 cloud sessions each:
  `python3 /Users/dogaozden/AI_Projects/research-lab/tools/launch_cloud.py /Users/dogaozden/AI_Projects/degree-diameter <prompt-file> claude-haiku-5-5 medium`
  The cloud clones GitHub, so code a cloud session needs must be pushed: put it in your folder and ask the main session
  (SendMessage to "main") to commit and push it, then launch. Cloud briefs must include: run `scripts/stop_check.sh`
  before each step and every long command through `scripts/guarded.sh HOURS ...` (max 5 h); push results to a branch
  named p4-<your-area>-<n>. Record each launch (session id) in your REPORT.md.
- Long local commands: run them in the background with nohup + `scripts/guarded.sh`, log to your folder, and poll.
- Final reply to the main session: under 3,500 characters; details go in REPORT.md.
