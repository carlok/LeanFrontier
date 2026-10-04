#!/usr/bin/env python3
"""Generate the public LeanFrontier theorem catalogue from merged source and claims."""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import re
import shutil
import subprocess
from pathlib import Path

from frontier_validate import CONJECTURE_RE, DECLARATION_NAME, RESOLUTION_RE, STATEMENT_END, strip_comments


ROOT = Path(__file__).resolve().parents[1]
DESTINATION = Path("docs/catalogue/index.html")
THEOREM = re.compile(rf"\b(?:theorem|lemma)\s+(?P<name>{DECLARATION_NAME})(?P<statement>.*?){STATEMENT_END}", re.DOTALL)
TRAILING_DOC = re.compile(r"/--(?P<docbody>(?:(?!-/).)*)-/\s*$", re.DOTALL)
SCOPE = re.compile(r"^(namespace|section|end)\b[ \t]*([A-Za-z_][A-Za-z0-9_.']*)?[ \t]*$", re.MULTILINE)


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
    paths = sorted((root / "LeanFrontier").rglob("*.lean"))
    resolved = {match.group(1).rsplit(".", 1)[-1]
                for path in paths
                for match in RESOLUTION_RE.finditer(strip_comments(path.read_text(encoding="utf-8")))}
    result: list[dict[str, str]] = []
    for path in paths:
        source = path.read_text(encoding="utf-8")
        # Declarations are found in comment-free code, documentation is read back
        # from the original text: `strip_comments` preserves byte offsets, so the
        # two stay aligned. Prose such as "Nicomachus's theorem is ..." would
        # otherwise match as a declaration named `is` and, because `finditer`
        # does not overlap, swallow the next real theorem in the module.
        code = strip_comments(source)
        found = [(match, match.group("name"), match.group("statement"), "theorem")
                 for match in THEOREM.finditer(code)]
        found += [(match, match.group(1), ": " + match.group("body").strip(),
                   "conjecture, resolved" if match.group(1) in resolved else "conjecture, open")
                  for match in CONJECTURE_RE.finditer(code)]
        for match, declared, statement, kind in sorted(found, key=lambda item: item[0].start()):
            doc_match = TRAILING_DOC.search(source[:match.start()])
            name = f"{namespace_at(code, match.start())}.{declared}"
            if name not in declared_entrypoints:
                continue
            result.append({
                "name": name,
                "kind": kind,
                "module": module_for(path, root),
                "statement": " ".join(statement.split()),
                "doc": " ".join((doc_match.group("docbody") if doc_match else "").split()),
                "source": path.relative_to(root).as_posix(),
            })
    return result


def namespace_at(code: str, position: int) -> str:
    """The namespace open at `position`. A module may close one namespace and
    open another, as the curvature-centre bridge does for its Ford-circle half."""
    scopes: list[tuple[str, str]] = []
    for match in SCOPE.finditer(code, 0, position):
        keyword, name = match.group(1), match.group(2) or ""
        if keyword == "end":
            if scopes:
                scopes.pop()
        else:
            scopes.append((keyword, name))
    names = [name for keyword, name in scopes if keyword == "namespace" and name]
    return ".".join(names) if names else "LeanFrontier"


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


def components(modules: list[str], edges: list[tuple[str, str]]) -> list[list[str]]:
    """Modules grouped by import connectivity, largest group first."""
    near: dict[str, set[str]] = {name: set() for name in modules}
    for tail, head in edges:
        if tail in near and head in near:
            near[tail].add(head)
            near[head].add(tail)
    seen: set[str] = set()
    groups: list[list[str]] = []
    for name in modules:
        if name in seen:
            continue
        stack, group = [name], set()
        while stack:
            current = stack.pop()
            if current not in group:
                group.add(current)
                stack.extend(near[current])
        seen |= group
        groups.append(sorted(group))
    return sorted(groups, key=lambda group: (-len(group), group[0]))


def graph_label(name: str, group: list[str]) -> str:
    """The shortest readable name: the last segment, with its parent when that
    segment is short or shared. The full module name is the node's hover title."""
    parts = name.replace("LeanFrontier.", "").split(".")
    last = parts[-1]
    shared = sum(1 for other in group if other.rsplit(".", 1)[-1] == last) > 1
    if len(parts) > 2 and (len(last) < 9 or shared):
        return ".".join(parts[-2:])
    return last


def dot_source(group: list[str], edges: list[tuple[str, str]]) -> str:
    """Graphviz input for one group. Arrows run from a module to its importers.

    Courier is one of the fonts Graphviz measures without looking it up, so box
    sizes do not depend on which fonts the machine drawing it has installed.
    """
    members = set(group)
    lines = [
        'digraph imports {',
        '  rankdir=LR; bgcolor="transparent"; nodesep=0.18; ranksep=0.4;',
        '  node [shape=box style="rounded,filled" fillcolor="#e6efe9" color="#0c6d56" '
        'fontname="Courier" fontsize=10 height=0.28 margin="0.08,0.03"];',
        '  edge [color="#0c6d5699" arrowsize=0.5];',
    ]
    for name in group:
        lines.append(f'  "{name}" [label="{graph_label(name, group)}"];')
    for tail, head in edges:
        if tail in members and head in members:
            lines.append(f'  "{head}" -> "{tail}";')
    lines.append("}")
    return "\n".join(lines) + "\n"


DRAWING = re.compile(r'(<div class="drawing" data-graph="[0-9a-f]+">).*?(</div>)', re.DOTALL)


def draw(source: str, caption: str) -> str:
    """Lay one group out with Graphviz and return the bare SVG element."""
    if shutil.which("dot") is None:
        raise SystemExit("drawing the import graph needs Graphviz: install it (apt-get install graphviz) and rerun")
    svg = subprocess.run(["dot", "-Tsvg"], input=source, capture_output=True, text=True, check=True).stdout
    svg = svg[svg.index("<svg"):]
    svg = re.sub(r"<!--.*?-->", "", svg, flags=re.DOTALL)
    # Several drawings share a page; Graphviz numbers ids from one in each.
    svg = re.sub(r'\sid="[^"]*"', "", svg)
    return svg.replace("<svg ", f'<svg role="img" aria-label="{html.escape(caption)}" ', 1).strip()


def graph_section(shape: dict[str, object], drawn: bool = True) -> str:
    """The import graph, one Graphviz drawing per connected group.

    Each drawing is tagged with a digest of its Graphviz input. Checking the
    catalogue compares digests, not SVG bytes, so a different Graphviz version
    on the machine that checks cannot fail a catalogue whose graph is current.
    """
    modules: list[str] = shape["modules"]  # type: ignore[assignment]
    edges: list[tuple[str, str]] = shape["edges"]  # type: ignore[assignment]
    groups = components(modules, edges)
    figures = []
    for group in (group for group in groups if len(group) > 1):
        source = dot_source(group, edges)
        digest = hashlib.sha256(source.encode("utf-8")).hexdigest()[:16]
        caption = f"{len(group)} modules"
        drawing = draw(source, f"Import graph of {caption}") if drawn else ""
        figures.append(
            f'<figure class="graph"><figcaption>{caption}</figcaption>'
            f'<div class="drawing" data-graph="{digest}">{drawing}</div></figure>'
        )
    alone = [group[0] for group in groups if len(group) == 1]
    alone_items = "".join(
        f"<li><code>{html.escape(name.replace('LeanFrontier.', ''))}</code></li>" for name in alone
    ) or "<li>none</li>"
    return (
        '<p class="legend">Each connected group of modules is drawn on its own. Arrows point from a module '
        "to the modules that import it; hover over a box for its full name.</p>"
        + "".join(figures)
        + f'<h3>Standing alone ({len(alone)})</h3><p class="legend">Modules that neither import another '
        f'corpus module nor are imported by one.</p><ul class="alone">{alone_items}</ul>'
    )


def comparable(page: str) -> str:
    """The page with each drawing reduced to its digest."""
    return DRAWING.sub(r"\1\2", page)


def render(root: Path, drawn: bool = True) -> str:
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
        kind = "" if item["kind"] == "theorem" else f'\n  <dt>Kind</dt><dd>{html.escape(item["kind"])}</dd>'
        cards.append(f"""<article>
  <h2><code>{html.escape(item['name'])}</code></h2>
  <p class=\"statement\">{html.escape(item['statement'])}</p>
  <dl><dt>Import</dt><dd><code>import {html.escape(item['module'])}</code></dd>{kind}
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
{graph_section(shape, drawn)}
</section>"""
    return f"""<!doctype html>
<html lang=\"en\"><head><meta charset=\"utf-8\"><meta name=\"viewport\" content=\"width=device-width, initial-scale=1\"><title>LeanFrontier theorem catalogue</title>
<style>body{{max-width:72rem;margin:auto;padding:2rem;background:#f4f1e8;color:#17221e;font:1rem/1.55 Georgia,serif}}code{{font:0.88em ui-monospace,monospace}}article{{border-top:1px solid #b8c3bc;padding:1.5rem 0}}h1,h2{{line-height:1.1}}h2{{overflow-wrap:anywhere}}.statement{{font-family:ui-monospace,monospace;overflow-wrap:anywhere}}.shape{{border-top:1px solid #b8c3bc;padding:1.5rem 0}}.shape ul{{display:grid;grid-template-columns:repeat(auto-fill,minmax(18rem,1fr));gap:.2rem 1.5rem;padding-left:1rem;font:0.85rem ui-monospace,monospace}}.shape li{{overflow-wrap:anywhere}}.legend{{font-size:0.85rem;color:#4a5b53}}.graph{{margin:1.25rem 0;border-top:1px solid #d9dfd9;padding-top:.4rem}}.graph figcaption{{font:.85rem ui-monospace,monospace;color:#4a5b53}}.drawing{{overflow-x:auto}}.drawing svg{{display:block}}.drawing text{{font-family:ui-monospace,Menlo,Consolas,monospace}}.shape ul.alone{{font-family:inherit}}.alone code{{overflow-wrap:anywhere}}dl{{display:grid;grid-template-columns:6rem minmax(0,1fr);gap:.35rem 1rem}}dt{{font-weight:bold}}dd{{margin:0;overflow-wrap:anywhere}}a{{color:#0c6d56}}</style></head>
<body><p><a href=\"../\">LeanFrontier</a> / corpus</p><h1>Theorem catalogue</h1><p>Generated after merged submissions from Lean source and immutable submission claims. Source and receiver reports remain canonical.</p>{summary}{body}</body></html>
"""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    destination = args.root / DESTINATION
    existing = destination.read_text(encoding="utf-8") if destination.exists() else ""
    # Checking never draws: it needs no Graphviz, and a drawing that differs only
    # because the layout engine changed is not a stale catalogue. For the same
    # reason the writer leaves the file alone unless something it says changed.
    if comparable(render(args.root, drawn=False)) == comparable(existing):
        return 0
    if args.check:
        print(f"{destination} is stale; run tools/generate_catalogue.py")
        return 1
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(render(args.root), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
