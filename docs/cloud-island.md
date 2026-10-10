# Running a cloud island

Start a Claude Code cloud session from the Claude app: **Cloud → Default**, repo **dogaozden/math**, model **Haiku 5.5** (it only babysits). Paste the prompt below with N = 1, 2, 3 or 4. Each island is its own 4-CPU machine and pushes to its own branch `island-N`.

```text
You are babysitting cloud island N of an evolutionary search. Do not edit any code. Do not stop to ask for approval.
1. Run `git remote -v`. If there is no GitHub origin, stop and say so.
2. Run `python3 -m pip install -q numpy networkx pytest` then `python3 -m pytest -q 2>&1 | tail -1`. If tests fail, stop and report.
3. Run `git checkout -b island-N`.
4. Start the run in the background from the repo root:
   `nohup python3 -m evolve run configs/island-N.toml > island-N.log 2>&1; echo "EXIT=$?" >> island-N.log` with `&` so it detaches.
5. Then keep watch: repeatedly run `sleep 540; tail -2 island-N.log; git log --oneline -1` with the Bash timeout set to 600000 ms.
   Keep going until island-N.log contains `EXIT=` or 5 hours have passed.
6. When it ends, reply with the last 5 lines of island-N.log and the output of `git log --oneline -3`.
```
