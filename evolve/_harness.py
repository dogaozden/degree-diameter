"""Runs one candidate program in a child process. Invoked by evolve.runner, not imported.

argv: program harness_dir params_json seed time_limit out_path
Exit codes: 0 ok, 1 import/build exception, 2 output could not be serialized.
"""
import importlib.util
import json
import os
import sys
import traceback


def _default(o):
    if hasattr(o, "tolist"):          # numpy arrays and scalars
        return o.tolist()
    if isinstance(o, (set, frozenset, tuple)):
        return list(o)
    raise TypeError(f"not JSON serializable: {type(o).__name__}")


def main() -> int:
    program, harness_dir, params_json, seed, time_limit, out_path = sys.argv[1:7]
    sys.path.insert(0, harness_dir)
    try:
        spec = importlib.util.spec_from_file_location("candidate", program)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        result = module.build(**json.loads(params_json), seed=int(seed), time_limit=float(time_limit))
    except BaseException:
        traceback.print_exc()
        return 1
    tmp_path = out_path + ".tmp"
    try:
        with open(tmp_path, "w") as f:
            json.dump(result, f, default=_default)
        os.replace(tmp_path, out_path)
    except (TypeError, ValueError, OverflowError):
        traceback.print_exc()
        return 2
    return 0


if __name__ == "__main__":
    code = main()
    sys.stdout.flush()
    sys.stderr.flush()
    os._exit(code)
