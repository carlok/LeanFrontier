#!/usr/bin/env python3
"""Generate the public LeanFrontier theorem catalogue from merged source and claims."""

from __future__ import annotations

import argparse
import html
import json
import re
from pathlib import Path


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


def entries(root: Path) -> list[dict[str, str]]:
    result: list[dict[str, str]] = []
    for path in sorted((root / "LeanFrontier").rglob("*.lean")):
        source = path.read_text(encoding="utf-8")
        namespaces = NAMESPACE.findall(source)
        namespace = namespaces[0] if namespaces else "LeanFrontier"
        for match in THEOREM.finditer(source):
            doc_match = TRAILING_DOC.search(source[:match.start()])
            name = f"{namespace}.{match.group('name')}"
            result.append({
                "name": name,
                "module": module_for(path, root),
                "statement": " ".join(match.group("statement").split()),
                "doc": " ".join((doc_match.group("docbody") if doc_match else "").split()),
                "source": path.relative_to(root).as_posix(),
            })
    return result


def render(root: Path) -> str:
    by_name = claims(root)
    observed_by_name = observations(root)
    cards: list[str] = []
    for item in entries(root):
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
    return f"""<!doctype html>
<html lang=\"en\"><head><meta charset=\"utf-8\"><meta name=\"viewport\" content=\"width=device-width, initial-scale=1\"><title>LeanFrontier theorem catalogue</title>
<style>body{{max-width:72rem;margin:auto;padding:2rem;background:#f4f1e8;color:#17221e;font:1rem/1.55 Georgia,serif}}code{{font:0.88em ui-monospace,monospace}}article{{border-top:1px solid #b8c3bc;padding:1.5rem 0}}h1,h2{{line-height:1.1}}.statement{{font-family:ui-monospace,monospace;overflow-wrap:anywhere}}dl{{display:grid;grid-template-columns:6rem 1fr;gap:.35rem 1rem}}dt{{font-weight:bold}}dd{{margin:0}}a{{color:#0c6d56}}</style></head>
<body><p><a href=\"../website/\">LeanFrontier</a> / corpus</p><h1>Theorem catalogue</h1><p>Generated after merged submissions from Lean source and immutable submission claims. Source and receiver reports remain canonical.</p>{body}</body></html>
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
