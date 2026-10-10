# Claude Code handoff: subscription-only evolutionary square-packing research

Prepared October 9, 2026. Intended recipient: Claude Code. This is a build-and-run handoff, not a claim that the system has already been implemented.

## Start here: execution prompt

Build a resumable evolutionary program-search system for packing unit squares into the smallest enclosing square. Use my Claude subscription for model work and Anthropic-hosted Claude Code cloud sessions for numerical execution. Use GitHub for durable code, experimental results, lineage, and checkpoints. Do not require separately billed model APIs, paid external compute, or GitHub Actions compute. Prefer a capable coordinator with Haiku mutation workers.

First verify the capabilities actually available in this account and environment, especially cloud session orchestration, Haiku selection, GitHub access, and runtime limits. Implement the evaluator, independent validator, baseline solver, checkpoint protocol, and worker instructions. Run a small end-to-end pilot, including resuming from a checkpoint. If the pilot passes, continue in bounded, checkpointed batches within subscription limits. A validated working search system is the first milestone; beating a mathematical record is a research objective, not a promised outcome.

Make routine implementation choices autonomously. Ask only for genuinely missing account access, an ambiguous repository destination, or a decision that would incur new charges. Do not replace the subscription-only architecture with API billing. If native cloud orchestration is unavailable, explain the exact gap and implement the best supported fallback below. Do not assume undocumented nested cloud-session launching works.

## User intent and constraints

The user proposed one orchestrator and many evolutionary Haiku agents, with all agents committing their work to GitHub. Cloud execution should let experiments continue with the user's laptop closed. Claude Code is strongly preferred; Codex is a fallback only if Claude cannot support the needed workflow. The user wants an actionable handoff, not more high-level discussion.

No repository has been selected or created in this conversation. No account-specific capability test, code implementation, deployment, or packing experiment has been performed. Codex was not researched because Claude's published features appeared sufficient to pursue first. Do not imply otherwise.

## Inspiration and research objective

Source: Ryan Xu, “Improving 25 square packing upper bounds through evolutionary LLM program search.”
https://slightlysupervised.substack.com/p/improving-25-square-packing-upper

The web page could not be retrieved in the originating conversation; the user pasted its text. The article reports 25 improved records for different numbers of squares, not a new record for packing 25 squares. It reports 128 generations, 7,500 CPU-hours, and $125 in model tokens over two days, using Claude Haiku to mutate search programs. These are the author's reported results, not independently reproduced findings.

The baseline randomly places squares and shrinks their container while L-BFGS resolves overlaps. Human-developed primitives included rounded corners, shaking, directional wind, and fading perturbations. Later mutations used structured initialization, relocating squares into gaps, swapping angles or positions, and fixing portions of a packing during optimization. Candidate roles included refinement, crossover, inventing primitives, and high-risk changes. The author increased runtime allowances and emphasized unbeaten cases as the search progressed.

Our target is the same class of problem: for n unit squares with arbitrary rotations, minimize the enclosing square's side length. A valid packing provides an upper bound. It does not prove optimality. Perfect-square n values already admit exact grid solutions by the area bound and are useful checks, not record targets.

## Product capabilities: evidence versus assumptions

The following official documentation was retrieved on October 9, 2026. Recheck relevant behavior during setup; availability can differ by account and version.

1. Cloud sessions are documented on Pro and Max, use the plan's shared usage allowance, have no separate VM charge, continue with the laptop closed, support simultaneous sessions, and can clone GitHub repositories and push branches. The CLI documents `claude --cloud` for launching a cloud task. This is different from Remote Control, which operates a local machine.
   https://code.claude.com/docs/en/claude-code-on-the-web
2. A new Projects beta coordinates parallel cloud threads from one conversation. It is available to selected Pro/Max Claude Code subscribers during a staged rollout. Do not assume the user has access merely because they subscribe.
   https://support.claude.com/en/articles/9517075-what-are-projects
3. Custom subagents support `model: haiku`. Subagents operate within a session; spawning more subagents is not the same as allocating more cloud VMs.
   https://code.claude.com/docs/en/sub-agents
4. Cloud sessions load committed `.claude/agents/` definitions. Documented approximate per-session ceilings are 4 vCPUs, 16 GB RAM, and 30 GB disk. Command timeouts, background execution limits, and idle VM reclamation apply. The cloud environment supports setup scripts and Python tooling.
   https://code.claude.com/docs/en/cloud-environments

Unverified: the account's simultaneous-session ceiling; sustained numerical throughput; Haiku actually selected in cloud workers; whether the Projects coordinator can autonomously execute every generation without intervention; exact model choices for project threads; and whether a cloud session can itself launch additional cloud sessions using supported subscription authentication. Native custom-agent support and model selection must be tested together, not inferred to work flawlessly from separate documentation pages.

## Architecture and fallback order

Preferred: a native Claude Code Project coordinates several cloud worker threads, each with its own VM. Each worker uses Haiku subagents to propose program mutations, evaluates candidates in its cloud runtime, and pushes results. The coordinator consumes those results and selects the next generation.

Fallback 1: a local Claude Code coordinator dispatches supported cloud sessions from the CLI and tracks their GitHub outputs. Numerical execution still happens in the cloud. Clearly disclose that future generation dispatch may require the coordinator machine to remain awake; this is not an entirely laptop-independent solution.

Fallback 2: one cloud session coordinates Haiku subagents and numerical subprocesses within its own VM. This proves the whole evolutionary loop with limited CPU parallelism. Do not advertise it as a multi-machine cluster.

Only if these are insufficient, investigate Codex's current subscription cloud execution and orchestration from official documentation. Keep the evaluator and checkpoint format platform-independent.

## Repository and coordination protocol

Use a dedicated research repository. If one is already supplied, inspect its instructions and preserve existing work. Otherwise prepare the project locally and resolve the GitHub destination before pushing. Keep it private unless the user chooses publication.

Suggested structure:

```text
CLAUDE.md
.claude/agents/packing-mutator.md
pyproject.toml
src/packing/                 # geometry, evaluator, baseline, selection
tests/                       # meaningful geometry and resume checks
configs/pilot.json
benchmarks/records.json       # dated source-backed reference bounds
experiments/<run-id>/manifest.json
experiments/<run-id>/candidates/<candidate-id>/
experiments/<run-id>/results/<candidate-id>.json
experiments/<run-id>/packings/<candidate-id>/
reports/status.md
```

Each candidate has an immutable ID, parent IDs, mutation role, source hash, generation, configuration, and random seeds. Workers write disjoint files on separate branches. Only the coordinator updates the canonical generation manifest. Avoid multiple agents editing one shared leaderboard. Use immutable task assignments and idempotent result collection so retries cannot double-count candidates. Fetch committed outputs at generation boundaries; do not assume cloud sessions share a live filesystem.

Commit code, compact results, coordinates, seeds, and selected visualizations. Keep huge logs, dependency directories, and temporary binaries out of Git. Checkpoint after every completed candidate or short batch. A restart must identify completed, incomplete, and unclaimed work without relying on chat history. Preserve partial useful results when a candidate times out.

## Evaluator and validation

Represent a packing with n centers and angles plus the enclosing square side length. Fix coordinate conventions explicitly. Require finite values, exactly n unit squares, and no malformed or duplicate IDs. Rotations are allowed; overlapping interiors are not.

Implement an independent geometry validator using square vertices, container containment, and separating-axis checks for every pair. Do not reuse the optimizer's overlap loss as the final validity test. Test edge touching, corner touching, clear overlap, tiny overlap, rotations, containment failures, NaNs, and grid packings. Keep the validator outside candidate-controlled code.

Use identical evaluation budgets and benchmark cases when ranking candidates. Record CPU time and wall time. Control numerical library threading to avoid CPU oversubscription. Evaluate stochastic performance across fixed seeds; reevaluate finalists with fresh seeds. Separate algorithm fitness across cases from the best individual packing ever found. Retain both diversity and elite candidates so selection does not collapse into trivial variants.

Reject invalid packings regardless of claimed score. A grid fallback is a valid baseline, not an improvement. Protect the benchmark table and evaluator from mutation. Record failures and timeouts explicitly. For apparent record improvements, rerun independently, inspect numerical tolerances, and use higher precision or conservative certification before calling a result a validated upper bound. Label floating-point candidates as provisional when appropriate. Obtain current reference records from their actual sources before making a record claim.

## Pilot and evolution plan

1. Check subscription authentication without exposing credentials. Verify available cloud controls, repository permissions, and actual Haiku execution. Record effective CPU/RAM limits and startup time. Use a tiny cloud job that commits a result as the integration test.
2. Build a correct grid baseline and geometry validator. Then implement a random initialization plus local squeeze baseline. Use NumPy/SciPy if available; choose a tractable overlap objective and document its limitations.
3. Start with a small mix of nontrivial n values such as 11, 17, and 51, plus perfect-square sanity cases. Targeting these values does not imply their records are equally approachable. Refresh benchmark data before scaling.
4. Run an initial pilot of roughly 2 generations with 4 candidates per generation, 2 seeds per case, and approximately 10 seconds per candidate/case/seed. These are proposed conservative defaults, not user-imposed limits. Adjust for measured overhead and baseline performance.
5. Prove one checkpoint/resume cycle, reconcile worker branches, verify actual model selection, and compare evolved candidates to baseline under the same budget.
6. Continue in bounded batches if the pilot succeeds. Expand concurrency only to supported account limits. Introduce role diversity, structured initialization, and larger n as evidence warrants. Make evaluator or fitness changes explicit and reevaluate retained parents so comparisons remain meaningful.

Run numerical loops as code, not repeated model calls. Each Haiku receives parent programs, recent scores, a specific mutation role, the immutable candidate interface, and a fixed evaluation budget. Return compact results to the coordinator. Use a stronger coordinator for synthesis and experimental design if available, without prescribing an unverified model ID.

Respect quota exhaustion: persist state and resume when access returns. Do not enable paid overages automatically, bypass limits, or promise unlimited overnight execution. Avoid busy polling; use supported completion signaling or sensible batch collection.

## Completion criteria and final report

Deliver a runnable repository with documented cloud setup, worker definitions, validated scoring, one completed evolutionary pilot, durable GitHub outputs, and a demonstrated resume path. Report which orchestration mode actually worked, actual worker models, measured throughput, best valid packings, comparison to baseline, and any remaining automation gap. Distinguish published product support from tested functionality. Include an exact next action for continuing the search.

The central objective: let subscription agents improve search algorithms, let cloud CPUs evaluate them, and let GitHub preserve the experiment so progress survives sessions.
