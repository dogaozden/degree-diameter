---
name: haiku-squad
description: Use when an Opus research session judges that it is stuck, or wants many different strategies tried at once, on a search or construction problem (records, coverings, Haar/Cayley searches, lifts). Opus writes 8 diverse direction cards; 8 Haiku subagents each write and run one strategy, scored by a fast automatic checker, into a shared scoreboard; Opus reads the ranked board, verifies, keeps the best ideas and evolves them. Evolutionary search with Opus as the selector.
---

# Haiku squad: Opus directs, Haikus diversify, a fast scorer judges

Doğa's idea (Oct 23, 2026). Haikus alone are too random: compute that doesn't know where to go is wasted. Opus alone is
bottlenecked on raw compute and gets stuck in its own head. Together, Opus aims, the Haikus explore, and Opus keeps what works.
It's the FunSearch / AlphaEvolve shape: a strong model directs, cheap samplers explore, and an automatic scorer judges.
Kenaznia's refinements are built in below.

## When

Whenever **you** judge it would help: you feel stuck, you want breadth, you want fresh ideas, or you just want more hands.
There's no formula for "stuck". That's your call.

Rules of thumb from earlier runs. They're hints you can use or ignore, not triggers:
- Two ideas in a row that went nowhere is often a sign it's time for fresh eyes.
- A long stretch of solo work on one goal (say 45 minutes) can be worth breaking up with a round, even when things feel fine.
- If two rounds in a row add nothing new, the goal may be exhausted for now; budget is finite (the week was at 86% on Oct 23).

Squads always run in the cloud, as subagents of your cloud session. Never on the coordinator's Mac mini.

## What the Haikus are for: ideas, not randomness

For raw random sampling, our C programs beat a Haiku by orders of magnitude (haar_gen3 tries millions of sets an hour). A
Haiku's value is a **different idea**: another heuristic, group family, construction, mutation rule or code variant. So
each card asks for **one strategy, written as code or a concrete command plan, and scored by the fast checker**. "Guess
some numbers" isn't a card.

## Running a round

1. **Write 8 cards, and make them disagree.** Each card gets a different region or approach, so no two Haikus do the same
   thing:
   - different group families or orders;
   - different orbit types or symmetries;
   - different construction tweaks or mutation rules;
   - and 2–3 wildcards: "find an approach none of the other cards uses", with the list of the other cards attached.
   Every card states:
   - the goal (for example, beat 31,460 at (16,5));
   - the tools and paths;
   - the scorer, meaning the exact check command;
   - the time box (about 15 minutes);
   - the folder to work in: `research/squads/<round>/<card>/`.
2. **Launch all 8 in ONE message** with the Agent tool (8 calls in one turn), each with `model: "haiku"` and a name like
   `squad-r2-c5-haiku`.
3. **Shared machine rules for every card:** about 4 cores and 15 GB are shared with you, so:
   - THREADS=1;
   - `timeout 900 nice -n 10 <cmd>` for anything heavy;
   - at most about 1.5 GB of memory;
   - no git commits;
   - no edits outside the card's folder.
4. **Scoreboard, not reports.** Each Haiku appends ONE line of JSON to `research/squads/<round>/scoreboard.jsonl`:
   `{"card": "c5", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <best size or lowest cost>,
   "valid": true|false, "next": "<one line>"}`, and replies to you in at most 5 lines. You read the board sorted by
   score (one page), not 8 essays. That keeps your context free for judging.
5. **Verify the top lines yourself** with an independent checker: build_haar2.py, the low-memory checkers above 20M
   vertices, or research/lifts/coordinator_check/apsp.c. A Haiku's "valid" is a claim, not proof.
6. **Evolve.** Keep the best 2–3 ideas, mutate or combine them into new cards, add fresh wildcards for the rest, and run
   the next round. Or chase a lead yourself. Or stop. You decide.

## If subagents aren't available

If you can't run Haiku subagents in your session, ask the coordinator for separate cloud Haiku sessions instead. Write
`research/squads/requests/<time>-<goal>.md` with the 8 cards and the scorer, commit and push it. The coordinator checks for
requests every hour, launches them, and points their results to a scoreboard on their own branches.

## Log every round (we are measuring whether this helps)

Append to `research/squads/LOG.md`:
- date and time, your session, the goal, the round number;
- the 8 cards in one line each;
- the best score per card;
- what you kept, and what you did next.

Commit the log, the scoreboards and any verified finds. The coordinator compares Opus + squad, Opus alone and Haikus alone on
the same goals, so an honest "the squad added nothing" is as valuable as a win.
