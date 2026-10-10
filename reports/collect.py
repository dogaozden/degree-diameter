"""Collect run data (generations, per-case bests, calls) into one JSON blob for the HTML report."""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def run_data(run_id):
    root = ROOT / "runs" / run_id
    gens = []
    for f in sorted((root / "generations").glob("[0-9][0-9][0-9].json")):
        s = json.loads(f.read_text())
        gens.append({"g": s["generation"], "best": s.get("best_fitness"), "gen_best": s.get("gen_best_fitness"),
                     "made": s.get("made"), "failed": s.get("failed"), "calls": s.get("calls_total"),
                     "elapsed": s.get("elapsed_s")})
    last = json.loads(sorted((root / "generations").glob("[0-9][0-9][0-9].json"))[-1].read_text())
    cases = {}
    for f in (root / "candidates").glob("*/result.json"):
        cid = f.parent.name
        for case_id, c in json.loads(f.read_text())["cases"].items():
            first = cases.setdefault(case_id, {"history": {}})
            g = int(cid[1:4])
            first["history"][g] = max(first["history"].get(g, 0), c["value"])
    calls = [json.loads(line) for line in (root / "calls.jsonl").read_text().splitlines() if line.strip()] \
        if (root / "calls.jsonl").exists() else []
    out_tokens = sum((c.get("usage") or {}).get("output_tokens", 0) for c in calls)
    in_tokens = sum((c.get("usage") or {}).get("cache_creation_input_tokens", 0) + (c.get("usage") or {}).get("input_tokens", 0)
                    for c in calls)
    limits = next((c["rate_limits"] for c in reversed(calls) if c.get("rate_limits")), {})
    roles = {}
    for m in (root / "candidates").glob("*/meta.json"):
        meta = json.loads(m.read_text())
        roles[meta["role"]] = roles.get(meta["role"], 0) + 1
    return {"run_id": run_id, "generations": gens, "best_by_case": last.get("best_by_case", {}),
            "case_history": {k: sorted(v["history"].items()) for k, v in cases.items()},
            "calls": len(calls), "call_errors": sum(bool(c.get("is_error")) for c in calls),
            "auth": sorted({str(c.get("auth")) for c in calls}), "out_tokens": out_tokens, "in_tokens": in_tokens,
            "cost_usd_api_equiv": round(sum(c.get("cost_usd") or 0 for c in calls), 3),
            "call_wall_s": round(sum(c.get("wall_s") or 0 for c in calls)), "limits": limits, "roles": roles}


if __name__ == "__main__":
    print(json.dumps({r: run_data(r) for r in sys.argv[1:]}, indent=1))
