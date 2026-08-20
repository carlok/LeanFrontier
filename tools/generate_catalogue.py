#!/usr/bin/env python3
"""Generate the public LeanFrontier theorem catalogue from merged source and claims."""

from __future__ import annotations

import argparse
import html
import json
import re
from pathlib import Path

from frontier_validate import strip_comments


ROOT = Path(__file__).resolve().parents[1]
DESTINATION = Path("docs/catalogue/index.html")
THEOREM = re.compile(r"theorem\s+(?P<name>[A-Za-z_][A-Za-z0-9_']*)\b(?P<statement>.*?)(?=\s*:=)", re.DOTALL)
TRAILING_DOC = re.compile(r"/--(?P<docbody>(?:(?!-/).)*)-/\s*$", re.DOTALL)
NAMESPACE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.']*)\s*$", re.MULTILINE)


def module_for(path: Path, root: Path) -> str:
    return path.relative_to(root).with_suffix("").as_posix().replace("/", ".")


def claims(root: Path) -> dict[str, dict[str, object]]:
    result: dict[str, dict[str, object]] = {}
    for path in sorted((root / "Submissions").glob("*.json")):
        record = json.loads(path.read_text(encoding="utf-8"))
        if isinstance(record, dict):
            for entrypoint in record.get("entrypoints", []):
                if isinstance(entrypoint, str):
                    result[entrypoint] = {"id": record.get("submission_id", path.stem), "producer": record.get("producer", {}), "origin": record.get("origin_mode", "unknown")}
    return result


def observations(root: Path) -> dict[str, dict[str, object]]:
    result: dict[str, dict[str, object]] = {}
    for path in sorted((root / "receiver-observations").glob("*/*.json")):
        record = json.loads(path.read_text(encoding="utf-8"))
        report = record.get("report", {}) if isinstance(record, dict) else {}
        observed = report.get("observed", {}) if isinstance(report, dict) else {}
        if report.get("accepted") is not True or not isinstance(observed, dict):
            continue
        entrypoints = observed.get("entrypoints", {})
        if not isinstance(entrypoints, dict):
            continue
        for entrypoint, details in entrypoints.items():
            if isinstance(entrypoint, str) and isinstance(details, dict):
                result[entrypoint] = {
                    "revision": record.get("accepted_revision", "unknown"),
                    "axioms": details.get("axioms", []),
                    "fingerprint": details.get("statement_sha256", "unknown"),
                    "smoke": observed.get("downstream_import_smoke", "unknown"),
                    "report": path.relative_to(root).as_posix(),
                }
    return result


def entries(root: Path, declared_entrypoints: set[str]) -> list[dict[str, str]]:
    """Return only declarations a submission explicitly exposes as entrypoints.

    Modules naturally contain induction steps and other implementation lemmas.  Those
    declarations are available to Lean, but they are not automatically part of the
    public corpus interface.  The immutable submission record is the authority for
    that boundary.
    """
    result: list[dict[str, str]] = []
    for path in sorted((root / "LeanFrontier").rglob("*.lean")):
        source = path.read_text(encoding="utf-8")
        # Declarations are found in comment-free code, documentation is read back
        # from the original text: `strip_comments` preserves byte offsets, so the
        # two stay aligned. Prose such as "Nicomachus's theorem is ..." would
        # otherwise match as a declaration named `is` and, because `finditer`
        # does not overlap, swallow the next real theorem in the module.
        code = strip_comments(source)
        namespaces = NAMESPACE.findall(code)
        namespace = namespaces[0] if namespaces else "LeanFrontier"
        for match in THEOREM.finditer(code):
            doc_match = TRAILING_DOC.search(source[:match.start()])
            name = f"{namespace}.{match.group('name')}"
            if name not in declared_entrypoints:
                continue
            result.append({
                "name": name,
                "module": module_for(path, root),
                "statement": " ".join(match.group("statement").split()),
                "doc": " ".join((doc_match.group("docbody") if doc_match else "").split()),
                "source": path.relative_to(root).as_posix(),
            })
    return result


def corpus_shape(root: Path) -> dict[str, object]:
    """Facts about how much the corpus depends on itself.

    Two measures, because they are not equally honest. An import edge is one
    line and need not be used, so it can be added to look connected. A corpus
    constant appearing in another submission's *statement* means a theorem
    actually mentions it, which cannot be faked without writing the theorem.
    Both are reported; the second is the one that means something.
    """
    modules = sorted(
        path.relative_to(root).with_suffix("").as_posix().replace("/", ".")
        for path in (root / "LeanFrontier").rglob("*.lean")
    )
    edges: list[tuple[str, str]] = []
    for module in modules:
        source = (root / (module.replace(".", "/") + ".lean")).read_text(encoding="utf-8")
        for line in source.splitlines():
            if line.startswith("import LeanFrontier"):
                edges.append((module, line.split()[1].strip()))
    edges.sort()

    submissions: set[str] = set()
    users: dict[str, set[str]] = {}
    for path in sorted((root / "receiver-observations").glob("*/*.json")):
        record = json.loads(path.read_text(encoding="utf-8"))
        identifier = record.get("submission_id")
        submissions.add(identifier)
        observed = record.get("report", {}).get("observed", {})
        for entry in (observed.get("entrypoints") or {}).values():
            for constant in entry.get("type_dependencies", []):
                if isinstance(constant, str) and constant.startswith("LeanFrontier."):
                    users.setdefault(constant, set()).add(identifier)
    shared = {name: sorted(who) for name, who in sorted(users.items()) if len(who) > 1}
    return {
        "modules": modules,
        "edges": edges,
        "submissions": len(submissions),
        "referenced": len(users),
        "shared": shared,
    }


def shape_svg(shape: dict[str, object]) -> str:
    """A deterministic picture of the import graph.

    Connected modules are drawn first, in the order their edges appear, so the
    clusters that carry the corpus are visible at a glance and the unattached
    remainder is visible as exactly that. Layout is a function of the sorted
    input alone: the catalogue is committed, and a layout that wandered between
    runs would make every regeneration a diff.
    """
    modules: list[str] = shape["modules"]  # type: ignore[assignment]
    edges: list[tuple[str, str]] = shape["edges"]  # type: ignore[assignment]
    attached = {name for edge in edges for name in edge}
    ordered = [m for m in modules if m in attached] + [m for m in modules if m not in attached]
    columns, cell_w, cell_h, radius = 4, 250, 62, 7
    position = {
        name: (60 + (index % columns) * cell_w, 40 + (index // columns) * cell_h)
        for index, name in enumerate(ordered)
    }
    height = 60 + ((len(ordered) + columns - 1) // columns) * cell_h
    parts = [
        f'<svg viewBox="0 0 {60 + columns * cell_w} {height}" width="100%" '
        f'role="img" aria-label="corpus import graph" xmlns="http://www.w3.org/2000/svg">'
    ]
    for tail, head in edges:
        if tail not in position or head not in position:
            continue
        (x1, y1), (x2, y2) = position[tail], position[head]
        mid_x, mid_y = (x1 + x2) / 2, (y1 + y2) / 2 - 26
        parts.append(
            f'<path d="M{x1} {y1} Q{mid_x} {mid_y} {x2} {y2}" fill="none" '
            f'stroke="#0c6d56" stroke-width="1.6"/>'
        )
    for name in ordered:
        x, y = position[name]
        colour = "#0c6d56" if name in attached else "#b8c3bc"
        label = name.replace("LeanFrontier.", "")
        parts.append(f'<circle cx="{x}" cy="{y}" r="{radius}" fill="{colour}"/>')
        parts.append(
            f'<text x="{x + 12}" y="{y + 4}" font-size="12" fill="#17221e" '
            f'font-family="ui-monospace,monospace">{html.escape(label)}</text>'
        )
    parts.append("</svg>")
    return "".join(parts)


def render(root: Path) -> str:
    by_name = claims(root)
    observed_by_name = observations(root)
    cards: list[str] = []
    for item in entries(root, set(by_name)):
        claim = by_name.get(item["name"], {})
        producer = claim.get("producer", {}) if isinstance(claim.get("producer", {}), dict) else {}
        producer_label = str(producer.get("agent", "unrecorded"))
        observation = observed_by_name.get(item["name"])
        audit = ""
        report_link = ""
        if observation:
            audit = (
                f'\n  <dt>Receiver</dt><dd>accepted at <code>{html.escape(str(observation["revision"]))}</code> '
                f'· downstream import {html.escape(str(observation["smoke"]))}</dd>'
                f'\n  <dt>Axioms</dt><dd><code>{html.escape(", ".join(map(str, observation["axioms"])))}</code></dd>'
                f'\n  <dt>Fingerprint</dt><dd><code>{html.escape(str(observation["fingerprint"]))}</code></dd>'
            )
            report_link = (
                f' · <a href="https://github.com/carlok/LeanFrontier/blob/main/'
                f'{html.escape(str(observation["report"]))}">receiver report</a>'
            )
        cards.append(f"""<article>
  <h2><code>{html.escape(item['name'])}</code></h2>
  <p class=\"statement\">{html.escape(item['statement'])}</p>
  <dl><dt>Import</dt><dd><code>import {html.escape(item['module'])}</code></dd>
  <dt>Claim</dt><dd>{html.escape(str(claim.get('id', 'unrecorded')))} · {html.escape(str(claim.get('origin', 'unknown')))} · {html.escape(producer_label)}</dd>{audit}</dl>
  <p>{html.escape(item['doc'])}</p>
  <p><a href=\"https://github.com/carlok/LeanFrontier/blob/main/{html.escape(item['source'])}\">View source</a>{report_link}</p>
</article>""")
    body = "\n".join(cards) or "<p>No public theorems have been catalogued yet.</p>"
    shape = corpus_shape(root)
    modules, edges = shape["modules"], shape["edges"]
    submissions, shared = shape["submissions"], shape["shared"]
    ratio = f"{len(edges) / submissions:.2f}" if submissions else "0"
    shared_rows = "".join(
        f"<li><code>{html.escape(name.replace('LeanFrontier.', ''))}</code> "
        f"— {len(who)} submissions</li>"
        for name, who in shared.items()
    ) or "<li>none yet</li>"
    summary = f"""<section class="shape">
<h2>Corpus shape</h2>
<p>Whether machine-generated mathematics accumulates, or merely piles up, is a
question about the dependency graph rather than the theorem count. These are the
numbers that answer it, regenerated with the catalogue.</p>
<dl><dt>Modules</dt><dd>{len(modules)}</dd>
<dt>Import edges</dt><dd>{len(edges)} internal, {ratio} per accepted submission</dd>
<dt>Referenced</dt><dd>{shape["referenced"]} corpus constants appear in some statement</dd>
<dt>Shared</dt><dd>{len(shared)} of them appear in statements from more than one submission</dd></dl>
<p>The last line is the one that resists gaming. An import costs a line and need
not be used; a constant reaching another submission's statement means a theorem
was written about it.</p>
<ul>{shared_rows}</ul>
{shape_svg(shape)}
<p class="legend">Filled nodes import or are imported by another corpus module; hollow nodes stand alone.</p>
</section>"""
    return f"""<!doctype html>
<html lang=\"en\"><head><meta charset=\"utf-8\"><meta name=\"viewport\" content=\"width=device-width, initial-scale=1\"><title>LeanFrontier theorem catalogue</title>
<style>body{{max-width:72rem;margin:auto;padding:2rem;background:#f4f1e8;color:#17221e;font:1rem/1.55 Georgia,serif}}code{{font:0.88em ui-monospace,monospace}}article{{border-top:1px solid #b8c3bc;padding:1.5rem 0}}h1,h2{{line-height:1.1}}.statement{{font-family:ui-monospace,monospace;overflow-wrap:anywhere}}.shape{{border-top:1px solid #b8c3bc;padding:1.5rem 0}}.shape ul{{columns:2;font:0.9rem ui-monospace,monospace}}.legend{{font-size:0.85rem;color:#4a5b53}}dl{{display:grid;grid-template-columns:6rem 1fr;gap:.35rem 1rem}}dt{{font-weight:bold}}dd{{margin:0}}a{{color:#0c6d56}}</style></head>
<body><p><a href=\"../\">LeanFrontier</a> / corpus</p><h1>Theorem catalogue</h1><p>Generated after merged submissions from Lean source and immutable submission claims. Source and receiver reports remain canonical.</p>{summary}{body}</body></html>
"""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    destination = args.root / DESTINATION
    expected = render(args.root)
    existing = destination.read_text(encoding="utf-8") if destination.exists() else ""
    if expected == existing:
        return 0
    if args.check:
        print(f"{destination} is stale; run tools/generate_catalogue.py")
        return 1
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(expected, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
