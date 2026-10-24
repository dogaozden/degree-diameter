---
name: haiku-squad
description: Use when an Opus research session is stuck, out of fresh ideas, or wants to try many variants at once on a search or construction problem (records, coverings, Haar/Cayley searches, lifts). Launches a squad of 8 Haiku subagents in parallel, each exploring one direction, then Opus judges, verifies, keeps the best and steers the next round. Evolutionary search with Opus as the selector.
---

# Haiku squad: Opus directs, Haikus explore

Doğa's idea (Oct 23, 2026): Haikus alone are too random, because compute that doesn't know where to go is wasted. Opus alone is
bottlenecked on raw compute: when it runs out of ideas, it thinks in circles. Together, Opus aims and the Haikus explore.
Opus reads what they found, keeps what works and sends them out again. It's the evolutionary search from our first record
run, with Opus as the selector instead of a fixed score.

## When to call a squad

- **Stuck:** two ideas in a row failed, or you can't name a promising next step.
- **Breadth:** you want to try many variants (groups, parameters, symmetries, construction tweaks) and see what works.
- **Routinely:** after about 45 minutes of solo work on one goal, run a round anyway. Fresh randomness is cheap.

Squads always run in the cloud, as subagents of your cloud session. Never on the coordinator's Mac mini.

## How to run a round

1. **Write 8 direction cards.** Each card is one concrete direction a Haiku can try in about 15 minutes:
   - 5–6 **directed** cards: variations around your best current lead (other groups or orders, another symmetry, a
     parameter window, a tweak to the construction, a different seed strategy).
   - 2–3 **wildcard** cards: "try anything plausible that isn't on this list", with a pointer to the relevant notes. These
     inject the randomness.
   Give every card: the goal (for example "beat 31,460 at (16,5)"), the exact tools and paths to use, how to check a
   result, and what to return.
2. **Launch all 8 in ONE message** with the Agent tool (8 tool calls in one turn, so they run in parallel), each with
   `model: "haiku"` and a name like `squad-r1-c3-haiku`.
3. **Shared machine rules:** the cloud machine has about 4 cores and 15 GB. Put this in every card: one thread per
   experiment (THREADS=1), `timeout 900 nice -n 10 <command>` for anything heavy, at most about 1.5 GB of memory, files only
   under `research/squads/<round>/<card>/`, no git commits, no edits to shared files.
4. **Each Haiku returns** a short report:
   - the idea tried;
   - the exact command;
   - the result (best size or cost reached, and VALID or not);
   - files written;
   - the one thing it would try next.
5. **Judge, then verify.** Read all 8 reports. Re-check any claimed hit yourself with an independent checker:
   build_haar2.py, the low-memory checkers, or an all-pairs BFS (research/lifts/coordinator_check/apsp.c). A Haiku's
   "VALID" is a claim, not proof.
6. **Evolve or take over.** Either chase the best lead yourself, or run the next round: keep the top 2–3 cards, mutate
   them (change one parameter, combine two cards), replace the losers with new directed and wildcard cards. Stop squad
   rounds on a goal after two rounds in a row that produce nothing new, and tell the reader why.

## Keep a log (we are measuring whether this helps)

Append each round to `research/squads/LOG.md`:
- date and time, your session and goal, round number;
- the 8 cards in one line each;
- per card: outcome (better / equal / worse / failed) with the number;
- what you kept, and what you did next.

Commit the log and any verified finds. The coordinator compares squad sessions with solo sessions on the same goals, so an
honest "the squad added nothing" is as useful as a win.
