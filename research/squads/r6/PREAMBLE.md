# Squad round 6 preamble

Same protocol, tools and rules as round 5: read `/home/user/degree-diameter/research/squads/r5/PREAMBLE.md` (and the
Tools / Machine rules sections of r1/PREAMBLE.md it points to). Files only under
`/home/user/degree-diameter/research/squads/r6/<your card>/`. Round 6 retries the round-5 near misses with new seeds.
Keep tool calls few: write one small driver script that runs your whole seed list sequentially, start it with
`nohup ... &`, then check it every few minutes (no busy polling). Do not name a bash variable GROUPS (it is a builtin).
Stop and report within about 50 minutes.
