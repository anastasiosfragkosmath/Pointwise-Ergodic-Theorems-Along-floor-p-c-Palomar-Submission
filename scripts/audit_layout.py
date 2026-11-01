#!/usr/bin/env python3
"""Audit package Lean layout; static check, not Lean compilation."""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import sys
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent.parent


def starts_with_module_header(source: str) -> bool:
    """Recognize a module keyword after whitespace and nested Lean comments."""
    source = source.removeprefix('\ufeff')
    i = 0
    while i < len(source):
        if source[i].isspace():
            i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i + 2)
            i = len(source) if end < 0 else end + 1
        elif source.startswith('/-', i):
            depth = 1
            i += 2
            while i < len(source) and depth:
                if source.startswith('/-', i):
                    depth += 1
                    i += 2
                elif source.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError('unterminated leading block comment')
        else:
            break
    end = i + len('module')
    return source.startswith('module', i) and (end == len(source) or source[end].isspace() or source.startswith('--', end) or source.startswith('/-', end))


def main() -> int:
    entries = []
    errors = []
    def onerror(error: OSError) -> None:
        errors.append({'path': str(error.filename), 'error': str(error)})
    for directory, dirs, files in os.walk(ROOT, followlinks=False, onerror=onerror):
        base = Path(directory)
        dirs[:] = [d for d in dirs if d not in {'.lake', '.git'}]
        for name in dirs:
            path = base / name
            if path.is_symlink():
                errors.append({'path': str(path.relative_to(ROOT)), 'error': 'symlinked directory'})
        for name in files:
            if not name.endswith('.lean'):
                continue
            path = base / name
            relative = str(path.relative_to(ROOT))
            if path.is_symlink():
                errors.append({'path': relative, 'error': 'symlinked Lean source'})
                continue
            try:
                data = path.read_bytes()
                source = data.decode('utf-8')
                header = starts_with_module_header(source)
            except (OSError, UnicodeError, ValueError) as error:
                errors.append({'path': relative, 'error': str(error)})
                continue
            # Count physical lines by LF bytes: CRLF is a single line ending;
            # a final unterminated nonempty line counts as one line.
            lines = data.count(b'\n') + (bool(data) and not data.endswith(b'\n'))
            entries.append({'path': relative, 'sha256': hashlib.sha256(data).hexdigest(),
                            'lines': lines, 'module_header': header,
                            'lake_config_exempt': relative == 'lakefile.lean'})
    entries.sort(key=lambda x: x['path'])
    if not entries:
        errors.append({'path': '.', 'error': 'no readable Lean files found'})
    if not any(x['lake_config_exempt'] for x in entries):
        errors.append({'path': 'lakefile.lean', 'error': 'root Lake configuration missing or unreadable'})
    too_long = [e for e in entries if e['lines'] > 10000]
    missing = [e for e in entries if not e['module_header'] and not e['lake_config_exempt']]
    manifest = ''.join(f"{e['sha256']}  {e['path']}\n" for e in entries)
    result = {'generated_at_utc': datetime.now(timezone.utc).isoformat(),
              'scope': 'all local Lean sources outside .lake and .git; only root lakefile.lean exempt from module header',
              'line_count': 'LF-delimited physical lines, including a nonempty final unterminated line',
              'audit_script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'mask_script_sha256': hashlib.sha256((ROOT / 'scripts/lean_source_mask.py').read_bytes()).hexdigest(),
              'lake_manifest_sha256': hashlib.sha256((ROOT / 'lake-manifest.json').read_bytes()).hexdigest(),
              'toolchain_sha256': hashlib.sha256((ROOT / 'lean-toolchain').read_bytes()).hexdigest(),
              'files': len(entries), 'source_sha256': {e['path']: e['sha256'] for e in entries},
              'sha256_manifest': hashlib.sha256(manifest.encode()).hexdigest(),
              'lakefile_sha256': next((e['sha256'] for e in entries if e['lake_config_exempt']), None),
              'over_10000': too_long, 'missing_module_header': missing, 'errors': errors,
              'largest': sorted(entries, key=lambda e: e['lines'], reverse=True)[:10],
              'passed': not (errors or too_long or missing),
              'limitations': 'Static source layout audit; not compilation or proof verification.'}
    (ROOT / 'audits' / 'source_layout.json').write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
    print(json.dumps({'files': len(entries), 'sha256_manifest': result['sha256_manifest'],
                      'lakefile_sha256': result['lakefile_sha256'], 'errors': errors,
                      'over_10000': len(too_long), 'missing_module_header': len(missing), 'passed': result['passed']}))
    return 0 if result['passed'] else 1

if __name__ == '__main__':
    sys.exit(main())
