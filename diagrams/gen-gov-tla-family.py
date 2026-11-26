#!/usr/bin/env python3
"""Generate the gov-tla diagram family (SVG, adaptive light/dark).

Each diagram is a module diagrams/gov-tla/src/d_<id>_<slug>.py exposing ID, SLUG and build() -> Canvas.
Output: diagrams/gov-tla/<ID>-<slug>-<DATE>.svg. Run with no arguments for all, or with ids (e.g. A1 B5).
diagrams/gov-tla/manifest.json is the registry of the links between diagrams: it lists every diagram's anchors, and
a diagram links to another's anchor only when the committed manifest lists it. When a run moves any diagram's
anchors, it updates the manifest, prints a NOTE line and exits 1: run it again, so that the links follow.
No dependencies beyond the standard library. Run it under the pinned interpreter, or every coordinate may move:
  uv run --no-project --python 3.9 python diagrams/gen-gov-tla-family.py [IDS]
"""
import importlib
import json
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent / "gov-tla"
sys.path.insert(0, str(HERE / "src"))

import lib  # noqa: E402
from lib import DATE  # noqa: E402


def main(argv):
    want = {a.upper() for a in argv}
    mods = sorted(p.stem for p in (HERE / "src").glob("d_*.py"))
    failed = 0
    manifest_path = HERE / "manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8")) if manifest_path.exists() else {}
    lib.load_registry(manifest)
    before = {k: (v["file"], v["anchors"]) for k, v in manifest.items()}
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
        manifest[m.ID] = {"file": out.name, "title": canvas.title, "anchors": sorted(canvas.anchors),
                          "links": canvas.links, "links_out": canvas.links_out, "links_ext": canvas.links_ext}
    manifest = {k: manifest[k] for k in sorted(manifest, key=lambda k: (k[0], int(k[1:])))}
    text = json.dumps(manifest, indent=1, ensure_ascii=False) + "\n"
    if not manifest_path.exists() or manifest_path.read_text(encoding="utf-8") != text:
        manifest_path.write_text(text, encoding="utf-8")
    moved = sorted(k for k in manifest if before.get(k) != (manifest[k]["file"], manifest[k]["anchors"]))
    if moved:
        print(f"NOTE the anchors of {', '.join(moved)} moved: the links were resolved against the previous "
              f"manifest, now updated. Run again so that they follow.")
        return 1
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
