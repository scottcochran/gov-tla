#!/usr/bin/env python3
"""Generate the gov-tla diagram family (SVG, adaptive light/dark).

Each diagram is a module diagrams/gov-tla/src/d_<id>_<slug>.py exposing ID, SLUG and build() -> Canvas.
Output: diagrams/gov-tla/<ID>-<slug>-<DATE>.svg. Run with no arguments for all, or with ids (e.g. A1 B5).
No dependencies beyond the standard library. Run it under the pinned interpreter, or every coordinate may move:
  uv run --no-project --python 3.9 python diagrams/gen-gov-tla-family.py [IDS]
"""
import importlib
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent / "gov-tla"
sys.path.insert(0, str(HERE / "src"))

from lib import DATE  # noqa: E402


def main(argv):
    want = {a.upper() for a in argv}
    mods = sorted(p.stem for p in (HERE / "src").glob("d_*.py"))
    failed = 0
    for name in mods:
        if want and name.split("_")[1].upper() not in want:
            continue
        try:
            m = importlib.import_module(name)
        except Exception as e:  # report and carry on, so one broken module cannot block the rest
            print(f"ERROR {name}: {e!r}")
            failed += 1
            continue
        out = HERE / f"{m.ID}-{m.SLUG}-{DATE}.svg"
        try:
            canvas = m.build()
        except Exception as e:  # a build-time read that no longer matches (corpus.CorpusError) fails like a gate
            print(f"ERROR {name}: {e!r}")
            failed += 1
            continue
        out.write_text(canvas.svg(), encoding="utf-8")
        print(out.relative_to(HERE.parent.parent))
        for w in canvas.warnings:
            print("  WARNING", w)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
