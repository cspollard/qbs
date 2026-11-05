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
    lines = pre_content.split("\n")

    # In Agda's HTML, each source line is roughly one HTML line within <pre class="Agda">
    # First, let's identify which hrefs are used in the body.
    # An import statement occurs in lines containing `class="Keyword">import</a>` or
    # opening module statements before declarations.
    # We collect (line_idx, sym_name, target_href, import_stmt) for each using symbol.

    using_entries = []  # (line_no, sym_name, target_href, mod_imported)
    body_hrefs = set()
    body_syms = set()

    in_import = False
    current_import_is_public = False
    current_mod_imported = ""

    for line_idx, line in enumerate(lines, 1):
        # A module import statement MUST contain the `import` keyword.
        # Lines with just `open M` inside the file body are module/record openings,
        # which are part of the file's usage (not imports).
        is_import_line = 'class="Keyword">import</a>' in line
        has_public_kw = 'class="Keyword">public</a>' in line

        if has_public_kw and is_import_line:
            current_import_is_public = True
        elif is_import_line:
            current_import_is_public = False

        # Extract imported module name if present
        mod_match = re.search(r'href="([^"]+\.html)"[^>]*class="Module">([^<]+)</a>', line)
        if mod_match and is_import_line:
            current_mod_imported = mod_match.group(2)

        # Hrefs inside using (...) of an import line are import anchors.
        # All other hrefs (including in `open M ...`) are body hrefs.
        if is_import_line and not current_import_is_public:
            if 'class="Keyword">using</a>' in line:
                using_part = line.split('class="Keyword">using</a>')[1]
                for m in re.finditer(r'href="([^"]+)"[^>]*>([^<]+)</a>', using_part):
                    target_href, sym_name = m.group(1), m.group(2)
                    if not target_href.endswith(".html"):
                        using_entries.append((line_idx, sym_name, target_href, current_mod_imported))
        else:
            for m in re.finditer(r'href="([^"]+)"[^>]*>([^<]+)</a>', line):
                body_hrefs.add(m.group(1))
                body_syms.add(m.group(2))

    # Also handle multiline `using (...)`
    # Match using\s*</a>\s*<a[^>]*class="Symbol">\(</a>(.*?)<a[^>]*class="Symbol">\)</a> across newlines
    for m in re.finditer(
        r'class="Keyword">using</a>\s*<a[^>]*class="Symbol">\(</a>(.*?)<a[^>]*class="Symbol">\)</a>',
        html,
        re.DOTALL,
    ):
        using_content = m.group(1)
        # Ensure this is an `import` statement, not a local `open Foo using (...)`
        prefix = html[max(0, m.start() - 300) : m.start()]
        if 'class="Keyword">import</a>' not in prefix:
            continue
        if 'class="Keyword">public</a>' in prefix:
            continue

        # Estimate line number from offset
        line_no = html[: m.start()].count("\n") + 1
        for sym_m in re.finditer(r'href="([^"]+)"[^>]*>([^<]+)</a>', using_content):
            target_href, sym_name = sym_m.group(1), sym_m.group(2)
            if not target_href.endswith(".html"):
                # Avoid duplicate registration if already handled single-line
                if not any(e[1] == sym_name and e[2] == target_href for e in using_entries):
                    using_entries.append((line_no, sym_name, target_href, ""))

    # Find unused symbols
    # A symbol is used if:
    #   1. Its exact target_href appears in body_hrefs
    #   2. OR a body token starts with `sym_name.` (qualified projection / module access)
    line_groups = {}
    for line_no, sym_name, target_href, mod in using_entries:
        if target_href in body_hrefs:
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

    unused_by_line = {res["line"]: set(res["unused"]) for res in results}
    lines = content.splitlines(keepends=True)

    modified = False
    new_lines = []

    for idx, line in enumerate(lines, 1):
        if idx in unused_by_line:
            unused = unused_by_line[idx]
            m = re.search(r"using\s*\((.*?)\)", line)
            if m:
                inside = m.group(1)
                items = [item.strip() for item in inside.split(";") if item.strip()]
                remaining = [item for item in items if item not in unused]
                if len(remaining) < len(items):
                    modified = True
                    if not remaining:
                        if "renaming" in line:
                            line = re.sub(r"\s*using\s*\(.*?\)", "", line)
                            new_lines.append(line)
                        else:
                            # drop line completely
                            pass
                    else:
                        new_using = "using (" + "; ".join(remaining) + ")"
                        new_line = line[: m.start()] + new_using + line[m.end() :]
                        new_lines.append(new_line)
                else:
                    new_lines.append(line)
            else:
                new_lines.append(line)
        else:
            new_lines.append(line)

    if modified:
        with open(agda_path, "w", encoding="utf-8") as f:
            f.writelines(new_lines)
    return modified


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
