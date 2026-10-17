#!/usr/bin/env python3
"""Local server for the Persistence Module Diagram Chaser.

Serves the static site and checks generated Lean files with a local
Lean 4 + Mathlib project:  POST /api/lean  {"code": "..."}.

Usage:
    python3 server.py [--port 8765] [--lean-project /path/to/mathlib/project]

The Lean project must depend on Mathlib and be built (``lake exe cache get``).
It can also be given with the environment variable LEAN_PROJECT.
Standard library only.
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
import threading
import time
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CANDIDATES = [
    ROOT / "lean-project",  # may be a symlink to an existing Mathlib project
]
LEAN_LOCK = threading.Lock()
TIMEOUT = int(os.environ.get("LEAN_TIMEOUT", "600"))


def find_lake():
    for c in [shutil.which("lake"), str(Path.home() / ".elan/bin/lake")]:
        if c and Path(c).exists():
            return c
    return None


def has_mathlib(p):
    p = Path(p)
    return (p / "lakefile.toml").exists() or (p / "lakefile.lean").exists()


def pick_project(arg):
    for c in [arg, os.environ.get("LEAN_PROJECT")] + [str(c) for c in CANDIDATES]:
        if c and has_mathlib(c) and (Path(c) / ".lake/packages/mathlib").exists():
            return str(Path(c).resolve())
    return None


class Handler(SimpleHTTPRequestHandler):
    project = None
    lake = None

    def __init__(self, *a, **kw):
        super().__init__(*a, directory=str(ROOT), **kw)

    def log_message(self, fmt, *args):
        if "/api/" in (args[0] if args else ""):
            sys.stderr.write("%s\n" % (fmt % args))

    def end_headers(self):
        self.send_header("Cache-Control", "no-store")
        super().end_headers()

    def _json(self, code, obj):
        body = json.dumps(obj).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        if self.path.startswith("/api/status"):
            ok = bool(self.project and self.lake)
            msg = "" if ok else "No Lean + Mathlib project found; start with --lean-project PATH."
            return self._json(200, {"lean": ok, "project": self.project, "message": msg})
        return super().do_GET()

    def do_POST(self):
        if not self.path.startswith("/api/lean"):
            return self._json(404, {"error": "not found"})
        if not (self.project and self.lake):
            return self._json(200, {"ok": False, "error": "Lean is not configured on the server."})
        n = int(self.headers.get("Content-Length", "0"))
        if n > 2_000_000:
            return self._json(413, {"ok": False, "error": "file too large"})
        try:
            code = json.loads(self.rfile.read(n) or b"{}").get("code", "")
        except json.JSONDecodeError:
            return self._json(400, {"ok": False, "error": "bad request"})
        if not code.startswith("import Mathlib"):
            return self._json(400, {"ok": False, "error": "expected a generated Lean file"})
        with LEAN_LOCK:
            t0 = time.time()
            with tempfile.TemporaryDirectory(prefix="ktchase") as tmp:
                f = Path(tmp) / "DiagramChase.lean"
                f.write_text(code, encoding="utf-8")
                try:
                    r = subprocess.run([self.lake, "env", "lean", str(f)], cwd=self.project,
                                       capture_output=True, text=True, timeout=TIMEOUT)
                except subprocess.TimeoutExpired:
                    return self._json(200, {"ok": False, "error": f"Lean timed out after {TIMEOUT}s"})
            out = (r.stdout + r.stderr).replace(str(f), "DiagramChase.lean")
            errors = [l for l in out.splitlines() if ": error" in l]
            ok = r.returncode == 0 and not errors
            return self._json(200, {"ok": ok, "output": out.strip()[:20000], "seconds": round(time.time() - t0, 1)})


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--port", type=int, default=int(os.environ.get("PORT", "8765")))
    ap.add_argument("--lean-project", default=None)
    args = ap.parse_args()
    Handler.project = pick_project(args.lean_project)
    Handler.lake = find_lake()
    srv = ThreadingHTTPServer(("127.0.0.1", args.port), Handler)
    print(f"Persistence Module Diagram Chaser on http://127.0.0.1:{args.port}")
    if Handler.project and Handler.lake:
        print(f"Lean checking with project {Handler.project}")
    else:
        print("Lean checking disabled (no Mathlib project found; use --lean-project PATH)")
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
