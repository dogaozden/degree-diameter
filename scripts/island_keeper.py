"""Keep the cloud islands running: relaunch any island that stopped, went quiet, or never started.

Every --every minutes: fetch, find each island's freshest branch (any branch name containing the run id that carries
runs/<id>/status.md), and relaunch a Haiku babysitter session for islands that are
  - stopped (last commit mentions a usage limit, EXIT or final outputs), or
  - quiet (no push for --quiet minutes), or
  - never started (no branch at all),
at most once per --cooldown minutes each, one launch every --gap seconds.
Fresh islands get scratchpad babysit_template.txt; islands with a branch get resume_template.txt.
Launches go through a pseudo-terminal so this can run in the background.
Prints one line per launch and per pass. --once runs a single pass; --dry-run prints what it would launch.
"""
import argparse, json, os, re, subprocess, sys, time
from pathlib import Path

REPO = str(__import__("pathlib").Path(__file__).resolve().parents[1])
SCRATCH = Path(__file__).resolve().parent / "keeper"  # prompt templates; keeper_state.json lives here too
BASE = ["island-1", "spec-d4d5", "spec-d5d5", "spec-d6d5", "spec-d7d5", "spec-d7d4", "spec-d11d4", "spec-d3fam",
        "spec-d16d3", "c-d4d5", "c-d5d5", "c-d6d5", "c-d7d5", "c-d7d4", "c-d11d4", "c-d3fam", "c-d16d3"]
ISLANDS = BASE + [b + s for s in ("-w2", "-w3", "-w3b") for b in BASE]
STOPPED = re.compile(r"usage limit|EXIT=|exit \d|final", re.I)


def git(*a):
    return subprocess.run(["git", "-C", REPO, *a], capture_output=True, text=True).stdout


def freshest(run_id, refs):
    best = None
    for ref, t in refs:
        if run_id in ref and subprocess.run(["git", "-C", REPO, "cat-file", "-e", f"{ref}:runs/{run_id}/status.md"],
                                            capture_output=True).returncode == 0:
            if best is None or t > best[1]:
                best = (ref, t)
    return best


def launch(run_id, template):
    """Start one cloud session through a pseudo-terminal; return the session id or ''."""
    import pty
    prompt = (SCRATCH / template).read_text().replace("RUNID", run_id)
    master, slave = pty.openpty()
    p = subprocess.Popen(["timeout", "60", "claude", "--model", "claude-haiku-5-5", "--effort", "low", "--cloud", prompt],
                         cwd=REPO, stdin=slave, stdout=slave, stderr=slave, close_fds=True)
    os.close(slave)
    out = b""
    while True:
        try:
            chunk = os.read(master, 4096)
        except OSError:
            break
        if not chunk:
            break
        out += chunk
    p.wait(); os.close(master)
    m = re.search(rb"session_[A-Za-z0-9]+", out)
    return m.group(0).decode() if m else ""


def one_pass(a, state):
    subprocess.run(["git", "-C", REPO, "fetch", "--all", "--prune", "-q"], capture_output=True)
    refs = [(l.rsplit(" ", 1)[0], int(l.rsplit(" ", 1)[1])) for l in
            git("for-each-ref", "--format=%(refname:short) %(committerdate:unix)", "refs/remotes/origin/").splitlines()]
    now = time.time(); todo = []
    for run_id in ISLANDS:
        f = freshest(run_id, refs)
        last = state.get(run_id, 0)
        if now - last < a.cooldown * 60:
            continue
        if f is None:
            todo.append((run_id, "babysit_template.txt", "never started"))
            continue
        ref, t = f
        subj = git("log", "-1", "--format=%s", ref).strip()
        age = (now - t) / 60
        if STOPPED.search(subj):
            todo.append((run_id, "resume_template.txt", f"stopped {age:.0f} min ago"))
        elif age > a.quiet:
            todo.append((run_id, "resume_template.txt", f"quiet {age:.0f} min"))
    print(time.strftime("%H:%M"), f"pass: {len(todo)} to launch", flush=True)
    for run_id, template, why in todo:
        if a.dry_run:
            print(f"  would launch {run_id} ({why})", flush=True); continue
        sid = launch(run_id, template)
        state[run_id] = time.time()
        print(f"  {run_id} ({why}): {sid or 'LAUNCH FAILED'}", flush=True)
        time.sleep(a.gap)
    return state


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--every", type=float, default=15)
    ap.add_argument("--quiet", type=float, default=45)
    ap.add_argument("--cooldown", type=float, default=40)
    ap.add_argument("--gap", type=float, default=15)
    ap.add_argument("--once", action="store_true")
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()
    state_file = SCRATCH / "keeper_state.json"
    state = json.loads(state_file.read_text()) if state_file.exists() else {}
    while True:
        state = one_pass(a, state)
        if not a.dry_run:
            state_file.write_text(json.dumps(state))
        if a.once:
            return
        time.sleep(a.every * 60)


if __name__ == "__main__":
    main()
