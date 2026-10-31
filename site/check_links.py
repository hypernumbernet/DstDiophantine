#!/usr/bin/env python3
"""Check internal links under site/. Exit 1 on any broken local link."""
import re
import sys
from pathlib import Path
from urllib.parse import urlparse, unquote

ROOT = Path(__file__).resolve().parent
HTML_FILES = sorted(ROOT.glob("*.html"))
SKIP = {"index.monolith.html"}

pages = {p.name for p in HTML_FILES if p.name not in SKIP}

link_re = re.compile(
    r'(?:href|src)=["\']([^"\']+)["\']',
    re.I,
)

errors = []
checked = 0

for path in HTML_FILES:
    if path.name in SKIP:
        continue
    text = path.read_text(encoding="utf-8")
    for raw in link_re.findall(text):
        if raw.startswith(("http://", "https://", "mailto:", "data:")):
            continue
        if raw.startswith("#"):
            continue
        parsed = urlparse(raw)
        target = unquote(parsed.path)
        if not target or target.endswith("/"):
            continue
        if target.endswith((".css", ".js", ".png", ".svg", ".webp", ".ico")):
            asset = ROOT / target
            if not asset.is_file():
                errors.append(f"{path.name}: missing asset {target}")
            continue
        if "/" in target:
            # repo-relative only
            if target.startswith("/"):
                continue
            errors.append(f"{path.name}: unsupported path {raw}")
            continue
        if target not in pages:
            errors.append(f"{path.name}: missing page {target} (from {raw})")
            continue
        checked += 1
        if parsed.fragment:
            frag = parsed.fragment
            dest = (ROOT / target).read_text(encoding="utf-8")
            if frag not in ("top", "") and f'id="{frag}"' not in dest and f"id='{frag}'" not in dest:
                errors.append(f"{path.name}: fragment #{frag} not in {target}")

print(f"Checked {checked} internal page links across {len(pages)} pages")
if errors:
    for e in errors:
        print("ERROR:", e)
    sys.exit(1)
print("OK: no broken internal links")
