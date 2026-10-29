# Squad conics-r2 (2026-10-29): second round of independent checks for research/synthetic/CONICS.md

Read first: research/synthetic/CONICS.md (the note being checked; CONICS.pdf is the same text) and, for the hat rules,
research/squads/conics-r1/BRIEF.md (definitions of PG(2,q), the conic x z = y^2, its polarity, the frame, rules
(R1)-(R6), theta). Write your own code; do NOT import from research/synthetic/conics/. You may use
research/plus2/coords/coords.py (class GF) and the python at
/tmp/claude-0/-home-user-degree-diameter/db23ed3e-5ef1-51fa-9a71-0fdc3180aa1f/scratchpad/venv/bin/python
(numpy, python-sat, pynauty, networkx).

Machine rules: about 4 cores shared; THREADS=1; heavy runs as `timeout 900 nice -n 10 <cmd>`; at most 1.5 GB of
memory; no git commits; write only inside research/squads/conics-r2/<card>/; time box about 20 minutes.

Output: append ONE line of JSON to research/squads/conics-r2/scoreboard.jsonl:
{"card": "c1", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <number>, "valid": true|false,
 "next": "<one line>"}
and reply in at most 5 lines (what you checked, the result, anything that failed or looks wrong in the note).
