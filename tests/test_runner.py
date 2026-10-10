import time
from pathlib import Path
from evolve.runner import run_program

def prog(tmp_path, body, name="p.py"):
    p = tmp_path / name; p.write_text(body); return p

def test_ok(tmp_path):
    r = run_program(prog(tmp_path, "def build(x, seed, time_limit):\n    return [x, [[0, 1]]]\n"), tmp_path, {"x": 2}, 0, 5)
    assert r.status == "ok" and r.output == [2, [[0, 1]]] and r.error == ""

def test_numpy_output_ok(tmp_path):
    body = "import numpy as np\ndef build(seed, time_limit):\n    return (np.int64(3), [(np.int64(0), 1)], {2})\n"
    r = run_program(prog(tmp_path, body), tmp_path, {}, 0, 5)
    assert r.status == "ok" and r.output == [3, [[0, 1]], [2]]

def test_imports_from_harness_dir(tmp_path):
    lib_dir = tmp_path / "libdir"; lib_dir.mkdir(); (lib_dir / "helper.py").write_text("X = 41\n")
    r = run_program(prog(tmp_path, "import helper\ndef build(seed, time_limit):\n    return helper.X + 1\n"), lib_dir, {}, 0, 5)
    assert r.status == "ok" and r.output == 42

def test_crash(tmp_path):
    r = run_program(prog(tmp_path, "def build(seed, time_limit):\n    raise RuntimeError('boom')\n"), tmp_path, {}, 0, 5)
    assert r.status == "crash" and "boom" in r.error and r.output is None

def test_syntax_error_is_crash(tmp_path):
    r = run_program(prog(tmp_path, "def build(:\n"), tmp_path, {}, 0, 5)
    assert r.status == "crash"

def test_bad_output(tmp_path):
    r = run_program(prog(tmp_path, "def build(seed, time_limit):\n    return object()\n"), tmp_path, {}, 0, 5)
    assert r.status == "bad_output"

def test_timeout(tmp_path):
    t = time.monotonic()
    r = run_program(prog(tmp_path, "import time\ndef build(seed, time_limit):\n    time.sleep(60)\n"), tmp_path, {}, 0, 1, grace_s=1)
    assert r.status == "timeout" and time.monotonic() - t < 10

def test_timeout_kills_grandchild(tmp_path):
    marker = tmp_path / "alive"
    child = f"import time,pathlib; time.sleep(4); pathlib.Path({str(marker)!r}).write_text('x')"
    body = f"""import subprocess, sys, time
def build(seed, time_limit):
    subprocess.Popen([sys.executable, '-c', {child!r}])
    time.sleep(60)
"""
    r = run_program(prog(tmp_path, body), tmp_path, {}, 0, 1, grace_s=0.5)
    assert r.status == "timeout"
    time.sleep(5)
    assert not marker.exists()

def test_relative_paths(tmp_path, monkeypatch):
    (tmp_path / "libdir").mkdir()
    (tmp_path / "libdir" / "helper.py").write_text("X = 1\n")
    prog(tmp_path, "import helper\ndef build(seed, time_limit):\n    return helper.X\n")
    monkeypatch.chdir(tmp_path)
    r = run_program(Path("p.py"), Path("libdir"), {}, 0, 5)
    assert r.status == "ok" and r.output == 1

def test_stdin_is_eof(tmp_path):
    body = "def build(seed, time_limit):\n    try:\n        input()\n    except EOFError:\n        return 1\n    return 0\n"
    r = run_program(prog(tmp_path, body), tmp_path, {}, 0, 5)
    assert r.status == "ok" and r.output == 1
