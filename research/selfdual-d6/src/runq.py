#!/usr/bin/env python3
"""Run a file of shell command lines, P at a time (each line through bash, so quotes and env assignments work).
usage: runq.py QUEUE P"""
import subprocess, sys
from concurrent.futures import ThreadPoolExecutor
lines = [l.strip() for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')]
def run(c): subprocess.run(['nice', '-n', '5', 'bash', '-c', c])
with ThreadPoolExecutor(int(sys.argv[2])) as ex: list(ex.map(run, lines))
