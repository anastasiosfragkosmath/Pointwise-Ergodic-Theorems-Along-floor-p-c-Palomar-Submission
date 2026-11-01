#!/usr/bin/env python3
"""Audit local Lean source tokens; default forbids all placeholders.

The opt-in flag permits only three standalone `sorry` tactics in Challenge.lean.
The exception is explicitly reported and does not imply a placeholder-free tree.
This lexical audit is not a Lean build or an axiom dependency audit.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import sys

from lean_source_mask import AuditError, FORBIDDEN_PATTERNS, mask_comments_strings_and_quoted_names

ROOT = Path(__file__).resolve().parent.parent
APPROVED_CHALLENGE_SHA256 = "b99baf8751ebabf401a4a21f11d338055836a09a4a43c513383152a20e496285"
# Exact known occurrences: these are bound variables starting continuation lines,
# not declaration commands. Require both the path and the actual line text.
TERM_CONSTANTS = {
    ('OAI/NumberTheory/DirichletL/Eisenstein/InverseCuspCoordinates.lean', 'constant*(p.1:ℂ)^(2/3:ℂ)+coeff.series p := by'),
    ('OAI/NumberTheory/DirichletL/Eisenstein/InverseCuspCoordinates.lean', 'constant*(q.1:ℂ)^(2/3:ℂ)+coeff.series q) p := by'),
    ('OAI/NumberTheory/DirichletL/Eisenstein/PrimePowerGaussSums.lean', 'constant*(hyperbolicHeight w:ℂ)^(2/3:ℂ)+coeff.function w'),
}


def audit(allow: bool) -> dict:
    sources, errors, hits = [], [], []
    def onerror(error: OSError) -> None:
        errors.append({'path': str(error.filename), 'error': str(error)})
    for directory, subdirs, filenames in os.walk(ROOT, followlinks=False, onerror=onerror):
        base = Path(directory)
        subdirs[:] = [x for x in subdirs if x not in {'.git', '.lake'}]
        for name in subdirs:
            path = base / name
            if path.is_symlink():
                errors.append({'path': str(path.relative_to(ROOT)), 'error': 'symlinked directory prevents complete audit'})
        for name in filenames:
            if name.endswith('.lean'):
                sources.append(base / name)
    hashes = {}
    for path in sorted(sources):
        rel = str(path.relative_to(ROOT))
        if path.is_symlink():
            errors.append({'path': rel, 'error': 'symlinked Lean source'})
            continue
        try:
            data = path.read_bytes()
            source = data.decode('utf-8')
            masked = mask_comments_strings_and_quoted_names(source, Path(rel))
        except (OSError, UnicodeError, AuditError) as error:
            errors.append({'path': rel, 'error': str(error)})
            continue
        hashes[rel] = hashlib.sha256(data).hexdigest()
        lines = source.splitlines()
        for token, pattern in FORBIDDEN_PATTERNS.items():
            for match in pattern.finditer(masked):
                pos = match.start('token') if token == 'constant' else match.start()
                line = masked.count('\n', 0, pos) + 1
                text = lines[line - 1].strip()
                item = {'path': rel, 'line': line, 'token': token,
                        'context': lines[max(0, line - 2):min(len(lines), line + 1)]}
                if token == 'constant' and (rel, text) in TERM_CONSTANTS:
                    item['classification'] = 'term occurrence of bound parameter in multiplication, not a declaration'
                elif token == 'sorry' and rel == 'Challenge.lean' and text == 'sorry':
                    item['classification'] = 'Challenge standalone sorry placeholder'
                else:
                    item['classification'] = 'violation'
                hits.append(item)
    challenge = [h for h in hits if h['classification'] == 'Challenge standalone sorry placeholder']
    violations = [h for h in hits if h['classification'] == 'violation']
    if allow:
        if hashes.get("Challenge.lean") != APPROVED_CHALLENGE_SHA256:
            errors.append({"path": "Challenge.lean", "error": "Challenge hash does not match the approved placeholder-bearing file"})
        if len(challenge) != 3:
            errors.append({'path': 'Challenge.lean', 'error': f'expected exactly three standalone sorry placeholders, found {len(challenge)}'})
    else:
        violations += challenge
    if not sources:
        errors.append({'path': '.', 'error': 'no Lean source files found'})
    manifest = ''.join(f'{h}  {p}\n' for p, h in sorted(hashes.items()))
    return {'generated_at_utc': datetime.now(timezone.utc).isoformat(),
            'scope': 'all local Lean files outside .lake and .git',
            'audit_script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'mask_script_sha256': hashlib.sha256((ROOT / 'scripts/lean_source_mask.py').read_bytes()).hexdigest(),
            'lake_manifest_sha256': hashlib.sha256((ROOT / 'lake-manifest.json').read_bytes()).hexdigest(),
            'lakefile_sha256': hashes.get('lakefile.lean'),
            'toolchain_sha256': hashlib.sha256((ROOT / 'lean-toolchain').read_bytes()).hexdigest(),
            'allow_challenge_placeholders': allow,
            'approved_challenge_sha256': APPROVED_CHALLENGE_SHA256,
            'observed_challenge_sha256': hashes.get('Challenge.lean'),
            'source_count': len(sources), 'source_sha256': hashes,
            'sha256_manifest': hashlib.sha256(manifest.encode()).hexdigest(),
            'challenge_placeholders': challenge, 'challenge_placeholder_count': len(challenge),
            'hits': hits, 'violations': violations, 'errors': errors,
            'passed': not violations and not errors,
            'limitations': 'Lexical source audit only; does not check compiled axiom dependencies or mathematical validity.'}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--allow-challenge-placeholders', action='store_true')
    parser.add_argument('--output', type=Path, help='optional JSON output path')
    args = parser.parse_args()
    report = audit(args.allow_challenge_placeholders)
    output = json.dumps(report, indent=2, ensure_ascii=False) + '\n'
    if args.output:
        args.output.write_text(output, encoding='utf-8')
    print(json.dumps({k: report[k] for k in ('source_count','sha256_manifest','allow_challenge_placeholders','challenge_placeholder_count','passed')}, ensure_ascii=False))
    if report['violations'] or report['errors']:
        print(json.dumps({'violations':report['violations'], 'errors':report['errors']}, ensure_ascii=False), file=sys.stderr)
    return 0 if report['passed'] else 1

if __name__ == '__main__':
    raise SystemExit(main())
