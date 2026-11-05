#!/usr/bin/env python3
"""Check for unused imports in Agda modules using Agda's HTML compiler output.

Agda's `--html` backend (run via `make html`) resolves all names, mixfix operators,
and record projections, embedding exact definition anchors (`href="Module.html#123"`)
for every token.

This script parses the generated HTML to identify:
  1. Symbols imported in `using (...)` whose definition anchors are never referenced
     in the body of the module.
  2. (Optionally) Bare imports `open import M` from which no symbol is referenced.

Usage:
  scripts/unused-imports.py [FILES/MODULES...] [--check] [--html-dir DIR]
"""

import argparse
import glob
import html as html_lib
import os
import re
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
DEFAULT_HTML_DIR = os.path.join(ROOT, "html")


def module_to_paths(mod_or_path, html_dir):
    """Resolve an input (e.g. 'src/QBS/Core.agda' or 'QBS.Core') to (agda_path, html_path)."""
    if mod_or_path.endswith(".agda"):
        agda_path = os.path.abspath(mod_or_path)
        rel = os.path.relpath(agda_path, os.path.join(ROOT, "src"))
        mod_name = rel[:-5].replace(os.sep, ".")
    else:
        mod_name = mod_or_path
        agda_path = os.path.join(ROOT, "src", *mod_name.split(".")) + ".agda"

    html_path = os.path.join(html_dir, f"{mod_name}.html")
    return mod_name, agda_path, html_path


def check_module_html(html_path):
    """Parse an Agda HTML file and find unused imports in using (...) clauses.

    Returns a list of dicts:
      [{'line': int, 'unused': [str], 'module': str, 'raw_import': str}]
    """
    if not os.path.exists(html_path):
        return None

    with open(html_path, "r", encoding="utf-8") as f:
        html = f.read()

    # Extract source content within <pre class="Agda">...</pre>
    if '<pre class="Agda">' not in html:
        return None
    pre_content = html.split('<pre class="Agda">')[1].split('</pre>')[0]

    # Find all using (...) spans in non-public `import` statements
    # Match using\s*</a>\s*<a[^>]*class="Symbol">\(</a>(.*?)<a[^>]*class="Symbol">[^<]*\).*?</a>
    using_spans = []  # list of (start_pos, end_pos)
    using_entries = []  # (line_no, sym_name, target_href, mod_imported)

    for m in re.finditer(
        r'class="Keyword">using</a>\s*<a[^>]*class="Symbol">\(</a>(.*?)<a[^>]*class="Symbol">[^<]*\).*?</a>',
        pre_content,
        re.DOTALL,
    ):
        start_pos = m.start()
        end_pos = m.end()
        # Look back up to 300 chars to check if this is an import statement and not public
        prefix = pre_content[max(0, start_pos - 300) : start_pos]
        if 'class="Keyword">import</a>' not in prefix:
            continue
        if 'class="Keyword">public</a>' in prefix:
            continue

        line_no = pre_content[:start_pos].count("\n") + 1
        using_spans.append((start_pos, end_pos))

        using_content = m.group(1)
        for sym_m in re.finditer(r'href="([^"]+)"[^>]*>([^<]+)</a>', using_content):
            target_href = sym_m.group(1)
            sym_name = html_lib.unescape(sym_m.group(2))
            if not target_href.endswith(".html"):
                using_entries.append((line_no, sym_name, target_href, ""))

    def in_any_using_span(pos):
        for s, e in using_spans:
            if s <= pos < e:
                return True
        return False

    body_hrefs = set()
    body_syms = set()

    for m in re.finditer(r'<a\s+[^>]*href="([^"]+)"[^>]*>([^<]+)</a>', pre_content):
        if not in_any_using_span(m.start()):
            body_hrefs.add(m.group(1))
            body_syms.add(html_lib.unescape(m.group(2)))

    for m in re.finditer(r'<span[^>]*class="([^"]+)"[^>]*>([^<]+)</span>', pre_content):
        if not in_any_using_span(m.start()):
            body_syms.add(html_lib.unescape(m.group(2)))

    # Find unused symbols
    # A symbol is used if:
    #   1. Its exact target_href appears in body_hrefs
    #   2. OR a body token exactly matches sym_name (handles builtin re-exports e.g. `[]`, `_∷_`, `refl`)
    #   3. OR a body token starts with `sym_name.` (qualified projection / module access)
    line_groups = {}
    for line_no, sym_name, target_href, mod in using_entries:
        if target_href in body_hrefs:
            continue
        if sym_name in body_syms:
            continue
        # Check qualified usage, e.g. `OmegaSemiring.Increasing` or `CommutativeSemiring.semiring`
        prefix = f"{sym_name}."
        if any(bs.startswith(prefix) for bs in body_syms):
            continue
        line_groups.setdefault(line_no, []).append(sym_name)

    results = []
    for line_no in sorted(line_groups.keys()):
        results.append({"line": line_no, "unused": line_groups[line_no]})
    return results


def apply_fixes(agda_path, results):
    """Rewrite agda_path to remove unused imports identified in results."""
    if not results or not os.path.exists(agda_path):
        return False
    with open(agda_path, "r", encoding="utf-8") as f:
        content = f.read()

    # Find using (...) spans across newlines
    replacements = []  # (start, end, replacement_str)

    for m in re.finditer(r"using\s*\((.*?)\)", content, re.DOTALL):
        s, e = m.start(), m.end()
        start_line = content[:s].count("\n") + 1
        end_line = content[:e].count("\n") + 1

        # Collect unused symbols relevant to this span
        unused = set()
        for r in results:
            if start_line - 1 <= r["line"] <= end_line + 1:
                unused.update(r["unused"])
        if not unused:
            continue

        inside = m.group(1)
        items = [it.strip() for it in inside.split(";") if it.strip()]

        def is_unused(item):
            it = item.strip()
            if it in unused:
                return True
            if it.startswith("module "):
                return it[7:].strip() in unused
            return False

        remaining = [it for it in items if not is_unused(it)]
        if len(remaining) < len(items):
            line_start = content.rfind("\n", 0, s) + 1
            line_end = content.find("\n", e)
            if line_end == -1:
                line_end = len(content)
            stmt = content[line_start:line_end]

            if not remaining:
                if "renaming" in stmt:
                    replacements.append((s, e, "using ()"))
                else:
                    stripped = stmt.strip()
                    if re.fullmatch(r"(open\s+)?import\s+[\w\.\-]+(\s+using\s*\(.*?\))?", stripped, re.DOTALL):
                        # drop statement / line completely
                        next_nl = content.find("\n", e)
                        if next_nl != -1:
                            replacements.append((line_start, next_nl + 1, ""))
                        else:
                            replacements.append((line_start, len(content), ""))
                    else:
                        replacements.append((s, e, ""))
            else:
                new_inside = "; ".join(remaining)
                replacements.append((s, e, f"using ({new_inside})"))

    if not replacements:
        return False

    # Apply in reverse order to preserve offsets
    replacements.sort(key=lambda x: x[0], reverse=True)
    for s, e, r in replacements:
        content = content[:s] + r + content[e:]

    with open(agda_path, "w", encoding="utf-8") as f:
        f.write(content)
    return True


def main():
    parser = argparse.ArgumentParser(description="Check for unused imports in Agda modules.")
    parser.add_argument("files", nargs="*", help="Agda source files or module names (default: all in src/)")
    parser.add_argument("--check", action="store_true", help="Exit with code 1 if unused imports are found")
    parser.add_argument("--fix", action="store_true", help="Automatically remove unused imports from source files")
    parser.add_argument("--html-dir", default=DEFAULT_HTML_DIR, help="Directory containing Agda HTML files")
    args = parser.parse_args()

    html_dir = os.path.abspath(args.html_dir)
    if not os.path.isdir(html_dir):
        print(f"Error: HTML directory '{html_dir}' not found. Please run 'make html' first.", file=sys.stderr)
        sys.exit(2)

    if args.files:
        targets = args.files
    else:
        # Find all .agda files under src/
        targets = sorted(glob.glob(os.path.join(ROOT, "src", "**", "*.agda"), recursive=True))

    total_unused = 0
    files_with_unused = 0
    missing_html = 0
    fixed_files = 0

    for target in targets:
        mod_name, agda_path, html_path = module_to_paths(target, html_dir)
        results = check_module_html(html_path)

        if results is None:
            missing_html += 1
            continue

        if results:
            files_with_unused += 1
            rel_path = os.path.relpath(agda_path, ROOT)
            for res in results:
                unused_str = ", ".join(f"'{u}'" for u in res["unused"])
                total_unused += len(res["unused"])
                print(f"{rel_path}:{res['line']}: unused import in using: {unused_str}")

            if args.fix:
                if apply_fixes(agda_path, results):
                    fixed_files += 1

    if missing_html > 0:
        print(f"Note: {missing_html} file(s) had no generated HTML in '{html_dir}'. Run 'make html' to generate.", file=sys.stderr)

    if args.fix:
        print(f"\nFixed unused imports in {fixed_files} file(s).")
        sys.exit(0)

    if total_unused == 0:
        print("OK: no unused imports found.")
        sys.exit(0)
    else:
        print(f"\nFound {total_unused} unused import(s) across {files_with_unused} file(s).")
        if args.check:
            sys.exit(1)
        sys.exit(0)


if __name__ == "__main__":
    try:
        main()
    except BrokenPipeError:
        # Silence broken pipe error when piping to head/grep
        sys.stderr.close()
        sys.exit(0)
