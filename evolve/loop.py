"""The generation loop: plan, mutate, evaluate, summarize. Every step is resumable from files in the run store."""
from __future__ import annotations

import json
import math
import os
import random
import subprocess
import tempfile
import time
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, as_completed, wait
from dataclasses import asdict
from pathlib import Path
from typing import Callable

from evolve.config import RunConfig
from evolve.mutator import BudgetStop, ClaudeMutator, FakeMutator, MutationTask
from evolve.runner import run_program
from evolve.select import fitness, parent_pool, pick_parents, pick_roles
from evolve.store import RunStore, _atomic_write
from evolve.types import CaseScore, CheckerBug, load_problem

EXIT_DONE, EXIT_BUDGET, EXIT_CHECKER_BUG = 0, 3, 4
SEED_CID = "g000-seed"
COMMIT_TRAILER = ("Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n"
                  "Claude-Session: https://claude.ai/code/session_01BUMdzXMSdYyesowPZnwehe")
GIT_TIMEOUT_S = 120


def make_smoke(problem, cfg: RunConfig) -> Callable[[str], tuple[bool, str]]:
    """Return smoke(code): run the code once on the problem's smoke case and check the output."""
    def smoke(code: str) -> tuple[bool, str]:
        case = problem.smoke_case()
        with tempfile.TemporaryDirectory(prefix="evolve-smoke-") as tmp:
            program = Path(tmp) / "program.py"
            program.write_text(code)
            res = run_program(program, problem.harness_dir, case.params, 0, cfg.smoke_time_limit_s, grace_s=2)
        if res.status != "ok":
            return (False, f"{res.status}: {res.error[-1500:]}")
        try:
            valid, _value, reason = problem.evaluate(case, res.output)
        except CheckerBug:
            return (True, "")   # the full evaluation will hit it again and stop the run
        if not valid:
            return (False, f"invalid output on smoke case {case.id}: {reason}")
        return (True, "")
    return smoke


def _record_prefix(path: Path) -> int | None:
    try:
        return int(path.name.split("-", 1)[0])
    except ValueError:
        return None


def _save_record(records_dir: Path, problem, case, value: float, output, cfg: RunConfig, cid: str, seed: int) -> None:
    folder = records_dir / problem.name / case.id
    top = int(value)
    if any((p := _record_prefix(f)) is not None and p >= top for f in folder.glob("*.json")):
        return
    body = {"case": case.id, "value": value, "run_id": cfg.run_id, "cid": cid, "seed": seed, "output": output}
    _atomic_write(folder / f"{top}-{cfg.run_id}-{cid}.json", json.dumps(body, indent=2, sort_keys=True) + "\n")


def _score_candidate(problem, outcomes: dict, cid: str, cfg: RunConfig, records_dir: Path) -> dict:
    """Best seed per case, second-checker verify, record saving, fitness. Main thread only."""
    cases, scores = {}, {}
    for case in problem.cases:
        seed, res, valid, value, reason = max(outcomes[case.id], key=lambda o: (o[2], o[3]))
        if valid and value >= case.record:
            if not problem.verify(case, res.output):
                valid, value, reason = False, 0.0, "second checker disagreed"
            else:
                _save_record(records_dir, problem, case, value, res.output, cfg, cid, seed)
        score = value / case.record if valid else 0.0
        cases[case.id] = asdict(CaseScore(case.id, res.status, valid, value if valid else 0.0, score,
                                          "" if valid else reason, res.wall_s))
        scores[case.id] = score
    return {"cases": cases, "fitness": fitness(scores, problem.cases)}


def evaluate_candidates(problem, store: RunStore, cids: list[str], cfg: RunConfig,
                        repo_root: Path | None = None) -> dict[str, dict]:
    """Run every candidate on every (case, seed) through one shared pool of cfg.workers threads.

    A candidate is scored, its records saved and its result.json written (all in this thread) as
    soon as its own jobs are done, so a resume keeps every candidate that finished.
    """
    if repo_root is None:   # store.root is repo_root / runs_dir / run_id
        repo_root = store.root.parents[len(Path(cfg.runs_dir).parts)]
    records_dir = repo_root / cfg.records_dir

    def job(program, case, seed):
        res = run_program(program, problem.harness_dir, case.params, seed, cfg.time_limit_s)
        if res.status != "ok":
            return (seed, res, False, 0.0, f"{res.status}: {res.error[-300:]}")
        valid, value, reason = problem.evaluate(case, res.output)   # may raise CheckerBug
        return (seed, res, valid, float(value) if valid else 0.0, reason)

    results: dict[str, dict] = {}
    ex = ThreadPoolExecutor(max(1, cfg.workers))
    try:
        owner, outcomes, left = {}, {}, {}
        for cid in cids:
            program = store.program_path(cid)
            outcomes[cid] = {case.id: [None] * len(cfg.eval_seeds) for case in problem.cases}
            left[cid] = len(problem.cases) * len(cfg.eval_seeds)
            for case in problem.cases:
                for i, seed in enumerate(cfg.eval_seeds):
                    owner[ex.submit(job, program, case, seed)] = (cid, case.id, i)
        for f in as_completed(owner):
            cid, case_id, i = owner[f]
            outcomes[cid][case_id][i] = f.result()
            left[cid] -= 1
            if left[cid] == 0:
                result = _score_candidate(problem, outcomes.pop(cid), cid, cfg, records_dir)
                store.write_result(cid, result)
                results[cid] = result
    except BaseException:
        ex.shutdown(wait=True, cancel_futures=True)
        raise
    ex.shutdown()
    return results


def evaluate_candidate(problem, store: RunStore, cid: str, cfg: RunConfig, repo_root: Path | None = None) -> dict:
    """Run one candidate on every (case, seed), keep the best seed per case, and write result.json."""
    return evaluate_candidates(problem, store, [cid], cfg, repo_root)[cid]


def _best_by_case(store: RunStore, problem) -> dict:
    """Best value per case over all evaluated candidates; the earliest candidate wins ties."""
    best: dict = {}
    for rec in sorted(store.load_candidates(), key=lambda c: (c.generation, c.id)):
        for case in problem.cases:
            v = rec.case_values.get(case.id, 0.0)
            if v > 0 and v > best.get(case.id, {}).get("value", 0.0):
                best[case.id] = {"cid": rec.id, "value": v, "record": case.record}
    return best


def render_status(store: RunStore, problem, cfg: RunConfig) -> str:
    done = [g for g in range(cfg.generations + 1) if store.generation_done(g)]
    best = _best_by_case(store, problem)
    lines = [f"# {cfg.run_id}", "", f"Problem: {problem.name}",
             f"Generations done: {len(done)} of {cfg.generations + 1} (including generation 0)",
             f"Total mutator calls: {store.count_calls()}", "",
             "| case | kind | record | ceiling | best value | best cid |", "|---|---|---|---|---|---|"]
    for case in problem.cases:
        b = best.get(case.id)
        if b is None:
            shown, cid = "-", "-"
        else:
            mark = " NEW" if b["value"] > case.record else (" =" if b["value"] == case.record else "")
            shown, cid = f"{b['value']:g}{mark}", b["cid"]
        lines.append(f"| {case.id} | {case.kind} | {case.record:g} | {case.ceiling:g} | {shown} | {cid} |")
    lines += ["", "| gen | made | failed | best fitness | gen best |", "|---|---|---|---|---|"]
    for g in done[-10:]:
        s = store.read_generation(g)
        gen_best = s.get("gen_best_fitness")
        shown = "-" if gen_best is None else f"{gen_best:.4f}"
        lines.append(f"| {g} | {s['made']} | {s['failed']} | {s['best_fitness']:.4f} | {shown} |")
    return "\n".join(lines) + "\n"


def _git(cfg: RunConfig, repo_root: Path, log, message: str) -> None:
    if not cfg.git.get("enabled"):
        return
    paths = [p for p in (f"{cfg.runs_dir}/{cfg.run_id}", cfg.records_dir) if (repo_root / p).exists()]
    if not paths:
        return
    # Commit only this run's paths, so anything else the user has staged stays staged.
    cmds = [["git", "add", "--", *paths],
            ["git", "commit", "-m", f"{message}\n\n{COMMIT_TRAILER}", "--", *paths]]
    if cfg.git.get("push"):
        cmds.append(["git", "push", "-u", "origin", "HEAD"])
    env = {**os.environ, "GIT_TERMINAL_PROMPT": "0"}
    for cmd in cmds:
        try:
            proc = subprocess.run(cmd, cwd=repo_root, capture_output=True, text=True, env=env, timeout=GIT_TIMEOUT_S)
        except subprocess.TimeoutExpired:
            log(f"git failed: {' '.join(cmd[:2])}: timed out after {GIT_TIMEOUT_S}s")
            return
        except OSError as e:
            log(f"git failed: {' '.join(cmd[:2])}: {e}")
            return
        out = (proc.stderr or "") + (proc.stdout or "")
        if proc.returncode != 0:
            if cmd[1] == "commit" and "nothing to commit" in out:
                continue    # nothing new to record; still push earlier commits
            log(f"git failed: {' '.join(cmd[:2])}: {out.strip()[-500:]}")
            return


def _build_mutator(problem, cfg: RunConfig):
    m = cfg.mutator
    if m["kind"] == "claude":
        return ClaudeMutator(m["model"], problem.prompt_context(), make_smoke(problem, cfg),
                             m.get("timeout_s", 300.0), m.get("stop_at", 0.9))

    def echo_first_parent(task: MutationTask, attempt: int) -> str:
        return "```python\n" + task.parents[0][1] + "\n```"
    return FakeMutator(echo_first_parent, make_smoke(problem, cfg))


def _make_plan(g: int, store: RunStore, problem, cfg: RunConfig) -> dict:
    rng = random.Random(cfg.seed * 1000 + g)
    pool = parent_pool(store.load_candidates(), problem.cases, cfg.selection["elite_k"]) or [SEED_CID]
    roles = pick_roles(cfg.candidates_per_generation, cfg.selection["roles"], rng)
    tasks = [{"cid": f"g{g:03d}-c{i:02d}", "role": r, "parents": pick_parents(pool, r, rng), "status": "pending"}
             for i, r in enumerate(roles)]
    return {"generation": g, "tasks": tasks}


def _mutation_task(task: dict, store: RunStore, problem, time_limit: float | None = None) -> MutationTask:
    parents = []
    for pid in task["parents"]:
        scores: dict = {}
        if store.has_result(pid):
            for k, v in store.read_result(pid)["cases"].items():
                # a zero carries its status and reason so the model can see what went wrong
                scores[k] = v["value"] if v["value"] else {"value": v["value"], "status": v["status"],
                                                           "reason": v["reason"]}
        parents.append((pid, store.read_program(pid), scores))
    return MutationTask(task["cid"], task["role"], parents, problem.cases, time_limit)


def _mutate_generation(g: int, plan: dict, store: RunStore, problem, cfg: RunConfig, mutator, log) -> bool:
    """Mutate every pending task. Returns True if the budget stopped us before all were done."""
    concurrency = max(1, cfg.mutator.get("concurrency", 1))
    max_calls = cfg.mutator.get("max_calls", math.inf)
    for t in plan["tasks"]:
        if t["status"] == "pending" and store.has_candidate(t["cid"]):
            t["status"] = "made"    # crashed between add_candidate and the plan write
    todo = [t for t in plan["tasks"] if t["status"] == "pending"]
    inflight: dict = {}
    stop, first_exc, interrupted = False, None, False
    try:
        with ThreadPoolExecutor(concurrency) as ex:
            while todo or inflight:
                while todo and len(inflight) < concurrency and not stop and first_exc is None and not interrupted:
                    if store.count_calls() >= max_calls:
                        stop = True
                        break
                    t = todo.pop(0)
                    inflight[ex.submit(mutator.mutate, _mutation_task(t, store, problem, cfg.time_limit_s))] = t
                if not inflight:
                    break
                try:
                    done, _ = wait(inflight, return_when=FIRST_COMPLETED)
                except KeyboardInterrupt as e:
                    # Ctrl-C: no new CLI calls, but keep draining so finished work is saved.
                    first_exc = first_exc or e
                    interrupted = True
                    abort = getattr(mutator, "abort", None)
                    if abort is not None:
                        abort()
                    log("interrupted: waiting for in-flight mutations to finish and saving them")
                    continue
                for fut in done:
                    t = inflight.pop(fut)
                    try:
                        res = fut.result()
                    except BudgetStop as e:
                        for call in e.calls:
                            store.append_call(call)
                        log(f"budget stop at {t['cid']}: {e}")
                        stop = True
                        continue
                    except BaseException as e:   # keep draining in-flight work, then re-raise
                        first_exc = first_exc or e
                        continue
                    for call in res.calls:
                        store.append_call(call)
                    if res.code:
                        meta = {"id": t["cid"], "generation": g, "parents": t["parents"], "role": t["role"],
                                "mutator": {"attempts": res.attempts, "error": res.error, "calls": len(res.calls)}}
                        store.add_candidate(t["cid"], res.code, meta)
                        t["status"] = "made"
                    else:
                        t["status"], t["error"] = "failed", res.error
                store.write_plan(g, plan)
    finally:
        store.write_plan(g, plan)
    if first_exc is not None:
        raise first_exc
    return stop


def _summary(g: int, store: RunStore, problem, plan: dict | None, stop: bool, started: float) -> dict:
    cands = store.load_candidates()
    best = _best_by_case(store, problem)
    tasks = plan["tasks"] if plan else []
    gen_best = max((c.fitness for c in cands if c.generation == g and c.fitness is not None), default=0.0)
    return {
        "generation": g, "complete": not stop,
        "candidates": len(store.candidates_in_generation(g)),
        "made": sum(t["status"] == "made" for t in tasks) if plan else 1,
        "failed": sum(t["status"] == "failed" for t in tasks),
        "calls_total": store.count_calls(),
        "best_fitness": max((c.fitness for c in cands if c.fitness is not None), default=0.0),
        "gen_best_fitness": gen_best,
        "best_by_case": best,
        "new_records": [[cid, b["cid"], b["value"]] for cid, b in best.items() if b["value"] > b["record"]],
        "elapsed_s": time.monotonic() - started,
    }


def run(cfg: RunConfig, config_text: str, repo_root: Path, mutator=None, log=print) -> int:
    repo_root = Path(repo_root)
    problem = load_problem(cfg.problem)
    store = RunStore(repo_root / cfg.runs_dir / cfg.run_id)
    imports = [] if store.generation_done(0) else _read_imports(cfg, repo_root)   # fail before anything is written
    store.init(config_text)
    if mutator is None:
        mutator = _build_mutator(problem, cfg)
    try:
        return _run(cfg, repo_root, problem, store, mutator, log, imports)
    except CheckerBug as e:
        log(f"checker bug: {e}")
        store.write_status(f"# CHECKER BUG\n\n{e}\n\nThe run stopped. Fix the checker before resuming.\n\n"
                           + render_status(store, problem, cfg))
        _git(cfg, repo_root, log, f"chore(run): {cfg.run_id} stopped on checker bug")
        return EXIT_CHECKER_BUG


def _finish_generation(g, store, problem, cfg, repo_root, log, plan, stop, started) -> None:
    summary = _summary(g, store, problem, plan, stop, started)
    store.write_generation(g, summary)
    store.write_status(render_status(store, problem, cfg))
    log(f"gen {g}: made {summary['made']} failed {summary['failed']} calls {summary['calls_total']} "
        f"gen-best {summary['gen_best_fitness']:.4f} best {summary['best_fitness']:.4f}")
    for case_id, cid, value in summary["new_records"]:
        if store.read_meta(cid)["generation"] == g:
            log(f"*** NEW RECORD {case_id}: {value:g} > {summary['best_by_case'][case_id]['record']:g} ({cid}) ***")
    _git(cfg, repo_root, log, f"chore(run): {cfg.run_id} generation {g} best {summary['best_fitness']:.4f}")


def _read_imports(cfg: RunConfig, repo_root: Path) -> list[tuple[str, str]]:
    """Read every cfg.seed_programs file as (path string, code); a missing file raises FileNotFoundError."""
    imports = []
    for rel in cfg.seed_programs:
        path = repo_root / rel
        if not path.is_file():
            raise FileNotFoundError(f"seed_programs: no such file: {path}")
        imports.append((rel, path.read_text()))
    return imports


def _run(cfg, repo_root, problem, store, mutator, log, imports=()) -> int:
    if not store.generation_done(0):
        started = time.monotonic()
        if not store.has_candidate(SEED_CID):
            store.add_candidate(SEED_CID, Path(problem.seed_program).read_text(),
                                {"id": SEED_CID, "generation": 0, "parents": [], "role": "seed"})
        for k, (source, code) in enumerate(imports):
            cid = f"g000-i{k:02d}"
            if not store.has_candidate(cid):
                store.add_candidate(cid, code, {"id": cid, "generation": 0, "parents": [], "role": "import",
                                                "source": source})
        pending = [cid for cid in store.candidates_in_generation(0) if not store.has_result(cid)]
        evaluate_candidates(problem, store, pending, cfg, repo_root)
        _finish_generation(0, store, problem, cfg, repo_root, log, None, False, started)

    for g in range(1, cfg.generations + 1):
        if store.generation_done(g):
            continue
        started = time.monotonic()
        plan = store.read_plan(g)
        if plan is None:
            plan = _make_plan(g, store, problem, cfg)
            store.write_plan(g, plan)
        stop = _mutate_generation(g, plan, store, problem, cfg, mutator, log)
        pending = [cid for cid in store.candidates_in_generation(g) if not store.has_result(cid)]
        evaluate_candidates(problem, store, pending, cfg, repo_root)
        _finish_generation(g, store, problem, cfg, repo_root, log, plan, stop, started)
        if stop:
            return EXIT_BUDGET
    return EXIT_DONE
