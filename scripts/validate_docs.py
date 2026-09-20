#!/usr/bin/env python3
"""Validate BDL_FV's records (docs/project/governance.md).

Checks, without any third-party dependency:

* decisions (`docs/decisions/NNN-*.md`): frontmatter present with the
  required fields, known status, phase and area, id matches the file name
  and the title, ids unique, `supersedes` / `superseded-by` name existing
  records and agree in both directions, a `superseded` record names its
  replacement, `related` names existing records, every id is in the index;
* open items (`docs/issues/NNN-*.md`): known state and area, unique ids, a
  resolved or deferred item has a Resolution section, `resolved-by` names
  an existing record or path, every id is in the index and in the right
  table (Active / Resolved);
* reports (`docs/reports/phase-*.md`) and notes (`docs/notes/*.md`): a
  `kind` / `phase` / `area` / `date` / `status` header whose kind matches
  the folder;
* kernel and project pages: a `kind` / `area` / `status` header whose kind
  matches the folder;
* the front door (`docs/README.md`) links every kernel and project page,
  each index links every record, and no `.md` sits loose at the top of
  `docs/`;
* every relative Markdown link under `docs/` and in `README.md` resolves;
* no current page cites a retired `D-NN` / `OI-NN` id (the migration page and
  each record's `legacy-id` excepted); every `production` entry is an
  `ADR|PRP|ISS-NNNN` with an optional relation; every backticked
  `BDL/….lean` path in `docs/` names an existing file; and the production
  snapshot (`snapshot:` in `docs/project/production-correspondence.md`) is a
  commit hash.

Exit status 1 with one line per problem; 0 and "records: valid" otherwise.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

DECISION_STATUSES = {"accepted", "superseded", "withdrawn"}
ISSUE_STATES = {"open", "deferred", "resolved"}
AREAS = {"core", "validation", "behavior", "surface", "experiments", "paper", "process"}
PHASE = re.compile(r"^(\d+[a-z]?|M)$")
DECISION_FIELDS = {"id", "status", "date", "phase", "area", "supersedes", "superseded-by", "related", "production"}
ISSUE_FIELDS = {"id", "state", "area", "opened", "resolved-by", "related", "production"}
PRODUCTION_RECORD = re.compile(r"^(ADR|PRP|ISS)-\d{4}(/(supports|audits|bears-on))?$")
LEGACY = re.compile(r"\b(D|OI)-\d{1,3}\b")
LEGACY_OK = {"docs/project/decision-id-migration.md", "docs/project/migration-report.md"}
LEAN_REF = re.compile(r"`(BDL/[A-Za-z/]+\.lean)`")
SHA = re.compile(r"^[0-9a-f]{7,40}$")
PHASED_FOLDERS = {"reports": "report", "notes": "note"}
PLAIN_FOLDERS = {"kernel": "kernel", "project": "project"}
PAGE_STATUSES = {"current", "archived"}
DATE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
LINK = re.compile(r"(?<!!)\[[^\]]*\]\(([^)\s]+)\)")
SKIP = {"README.md", "TEMPLATE.md"}


def parse_value(value: str):
    value = value.strip()
    if value.startswith("[") and value.endswith("]"):
        inner = value[1:-1].strip()
        if not inner:
            return []
        return [part.strip().strip("\"'") for part in inner.split(",")]
    return value.strip("\"'")


def parse_frontmatter(text: str) -> dict[str, object] | None:
    lines = text.splitlines()
    if not lines or lines[0].strip() != "---":
        return None
    try:
        end = lines.index("---", 1)
    except ValueError:
        return None
    data: dict[str, object] = {}
    key = None
    for line in lines[1:end]:
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        if line[0] in " \t" and key is not None:
            # Prettier wraps a long inline list onto the next, indented line
            data[key] = parse_value(str(data[key] or "") + " " + line.strip())
            continue
        if ":" not in line:
            continue
        key, value = line.split(":", 1)
        data[key.strip()] = parse_value(value)
        key = key.strip()
    return data


def as_list(value) -> list[str]:
    if isinstance(value, list):
        return value
    if value in (None, ""):
        return []
    return [str(value)]


class Validator:
    def __init__(self, root: Path) -> None:
        self.root = root
        self.errors: list[str] = []
        self.known_ids: set[str] = set()

    def error(self, path: Path | None, message: str) -> None:
        where = f"{path.relative_to(self.root)}: " if path else ""
        self.errors.append(f"{where}{message}")

    # ---- records ---------------------------------------------------------

    def records(self, folder: str) -> list[tuple[Path, dict[str, object], str]]:
        out = []
        for path in sorted((self.root / folder).glob("[0-9][0-9][0-9]-*.md")):
            text = path.read_text(encoding="utf-8")
            meta = parse_frontmatter(text)
            if meta is None:
                self.error(path, "missing or malformed frontmatter")
                continue
            out.append((path, meta, text))
        return out

    def check_common(self, path: Path, meta: dict[str, object], prefix: str, fields: set[str],
                     width: int) -> str:
        missing = sorted(fields - meta.keys())
        if missing:
            self.error(path, f"missing fields {', '.join(missing)}")
        record_id = str(meta.get("id", ""))
        number = int(path.name[:3])
        expected = f"{prefix}-{number:0{width}d}"
        for entry in as_list(meta.get("production")):
            if not PRODUCTION_RECORD.match(entry):
                self.error(path, f"production entry {entry!r} is not ADR|PRP|ISS-NNNN[/relation]")
        if record_id != expected:
            self.error(path, f"id {record_id!r} does not match the file name ({expected})")
        title = re.search(r"^# (\S+):", path.read_text(encoding="utf-8"), re.M)
        if not title or title.group(1) != record_id:
            self.error(path, f"title heading must start with '# {record_id}:'")
        area = str(meta.get("area", ""))
        if area not in AREAS:
            self.error(path, f"unknown area {area!r}")
        for key in ("date", "opened"):
            if key in meta and not DATE.match(str(meta[key])):
                self.error(path, f"{key} must be YYYY-MM-DD")
        if record_id in self.known_ids:
            self.error(path, f"duplicate id {record_id}")
        self.known_ids.add(record_id)
        return record_id

    def check_index(self, index: Path, ids: list[str]) -> str:
        text = index.read_text(encoding="utf-8") if index.exists() else ""
        for record_id in ids:
            if f"[{record_id}]" not in text:
                self.error(index, f"{record_id} is missing from the index")
        return text

    def check_decisions(self) -> None:
        recs = self.records("docs/decisions")
        by_id: dict[str, dict[str, object]] = {}
        paths: dict[str, Path] = {}
        for path, meta, _ in recs:
            record_id = self.check_common(path, meta, "FVD", DECISION_FIELDS, 4)
            if str(meta.get("status")) not in DECISION_STATUSES:
                self.error(path, f"unknown decision status {meta.get('status')!r}")
            if not PHASE.match(str(meta.get("phase", ""))):
                self.error(path, f"phase must be a phase label, not {meta.get('phase')!r}")
            by_id[record_id] = meta
            paths[record_id] = path
        for record_id, meta in by_id.items():
            path = paths[record_id]
            for field in ("supersedes", "superseded-by", "related"):
                for target in as_list(meta.get(field)):
                    if target not in by_id:
                        self.error(path, f"{field} names unknown record {target}")
            for old in as_list(meta.get("supersedes")):
                if old in by_id and record_id not in as_list(by_id[old].get("superseded-by")):
                    self.error(paths[old], f"must list {record_id} in superseded-by")
            for new in as_list(meta.get("superseded-by")):
                if new in by_id and record_id not in as_list(by_id[new].get("supersedes")):
                    self.error(paths[new], f"must list {record_id} in supersedes")
                if str(meta.get("status")) != "superseded":
                    self.error(path, "has superseded-by but status is not 'superseded'")
            if str(meta.get("status")) == "superseded" and not as_list(meta.get("superseded-by")):
                self.error(path, "status 'superseded' needs a superseded-by record")
        self.check_index(self.root / "docs/decisions/README.md", list(by_id))

    def check_issues(self) -> None:
        recs = self.records("docs/issues")
        ids = []
        states: dict[str, str] = {}
        for path, meta, text in recs:
            record_id = self.check_common(path, meta, "FVI", ISSUE_FIELDS, 4)
            ids.append(record_id)
            state = str(meta.get("state"))
            states[record_id] = state
            if state not in ISSUE_STATES:
                self.error(path, f"unknown item state {state!r}")
            resolved_by = as_list(meta.get("resolved-by"))
            if state == "resolved" and not resolved_by:
                self.error(path, "a resolved item must name what resolved it in resolved-by")
            for target in resolved_by:
                if re.match(r"(FVD|FVI)-\d+$", target) and target not in self.known_ids:
                    self.error(path, f"resolved-by names unknown record {target}")
                elif "/" in target and not (self.root / target.split("#")[0]).exists():
                    self.error(path, f"resolved-by path does not exist: {target}")
            if state in ("resolved", "deferred"):
                body = text.split("## Resolution", 1)
                if len(body) < 2 or len(body[1].strip()) < 10:
                    self.error(path, f"a {state} item needs a Resolution section")
        index = self.root / "docs/issues/README.md"
        text = self.check_index(index, ids)
        if "## Active" in text and "## Resolved" in text:
            active, resolved = text.split("## Active", 1)[1].split("## Resolved", 1)
            for record_id, state in states.items():
                in_active, in_resolved = f"[{record_id}]" in active, f"[{record_id}]" in resolved
                if state == "resolved" and (in_active or not in_resolved):
                    self.error(index, f"{record_id} is resolved and belongs in the Resolved table only")
                if state != "resolved" and (in_resolved or not in_active):
                    self.error(index, f"{record_id} is {state} and belongs in the Active table only")

    # ---- pages -------------------------------------------------------------

    def check_pages(self) -> None:
        for folder, kind in {**PHASED_FOLDERS, **PLAIN_FOLDERS}.items():
            for path in sorted((self.root / "docs" / folder).glob("*.md")):
                if path.name in SKIP:
                    continue
                meta = parse_frontmatter(path.read_text(encoding="utf-8"))
                if meta is None:
                    self.error(path, "missing kind/area/status header")
                    continue
                if str(meta.get("kind")) != kind:
                    self.error(path, f"kind must be {kind!r} in docs/{folder}/")
                if str(meta.get("area")) not in AREAS:
                    self.error(path, f"unknown area {meta.get('area')!r}")
                if str(meta.get("status")) not in PAGE_STATUSES:
                    self.error(path, f"unknown status {meta.get('status')!r}")
                if folder in PHASED_FOLDERS:
                    if not PHASE.match(str(meta.get("phase", ""))):
                        self.error(path, f"phase must be a phase label, not {meta.get('phase')!r}")
                    if not DATE.match(str(meta.get("date", ""))):
                        self.error(path, "date must be YYYY-MM-DD")
                if folder == "reports" and not path.name.startswith("phase-"):
                    self.error(path, "report file names are phase-NN-slug.md")

    def check_indexes(self) -> None:
        front = self.root / "docs/README.md"
        text = front.read_text(encoding="utf-8") if front.exists() else ""
        for path in sorted((self.root / "docs").glob("*.md")):
            if path.name != "README.md":
                self.error(path, "loose page at the top of docs/: move it into its kind's folder")
        for folder in PLAIN_FOLDERS:
            for path in sorted((self.root / "docs" / folder).glob("*.md")):
                if path.name in SKIP:
                    continue
                rel = f"{folder}/{path.name}"
                if f"({rel})" not in text and f"({rel}#" not in text:
                    self.error(front, f"{rel} is not registered in the front door")
        for folder in PHASED_FOLDERS:
            index = self.root / "docs" / folder / "README.md"
            itext = index.read_text(encoding="utf-8") if index.exists() else ""
            for path in sorted((self.root / "docs" / folder).glob("*.md")):
                if path.name in SKIP:
                    continue
                if f"({path.name})" not in itext:
                    self.error(index, f"{path.name} is not listed in the index")

    def check_links(self) -> None:
        files = [self.root / "README.md"] + sorted((self.root / "docs").rglob("*.md"))
        for path in files:
            if not path.exists():
                continue
            text = path.read_text(encoding="utf-8")
            for match in LINK.finditer(text):
                target = match.group(1)
                if "://" in target or target.startswith("mailto:") or target.startswith("#"):
                    continue
                target = target.split("#", 1)[0]
                if not target:
                    continue
                resolved = (path.parent / target).resolve()
                if not resolved.exists():
                    self.error(path, f"broken link {match.group(1)}")

    def check_references(self) -> None:
        files = [self.root / "README.md"] + sorted((self.root / "docs").rglob("*.md"))
        for path in files:
            rel = str(path.relative_to(self.root))
            text = path.read_text(encoding="utf-8")
            if rel not in LEGACY_OK:
                body = re.sub(r"(?m)^legacy-id: .*$", "", text)
                for match in LEGACY.finditer(body):
                    self.error(path, f"retired id {match.group(0)}: cite the FVD/FVI record")
            for match in LEAN_REF.finditer(text):
                if not (self.root / match.group(1)).exists():
                    self.error(path, f"Lean file does not exist: {match.group(1)}")
        corr = self.root / "docs/project/production-correspondence.md"
        meta = parse_frontmatter(corr.read_text(encoding="utf-8")) if corr.exists() else None
        if not meta or not SHA.match(str(meta.get("snapshot", ""))):
            self.error(corr, "needs a `snapshot:` commit hash in its frontmatter")

    def run(self) -> list[str]:
        self.check_decisions()
        self.check_issues()
        self.check_pages()
        self.check_indexes()
        self.check_links()
        self.check_references()
        return self.errors


def validate(root: Path) -> list[str]:
    return Validator(root).run()


def main() -> int:
    root = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else Path(__file__).resolve().parents[1]
    errors = validate(root)
    for error in errors:
        print(error)
    if errors:
        print(f"records: {len(errors)} problem(s)")
        return 1
    print("records: valid")
    return 0


if __name__ == "__main__":
    sys.exit(main())
