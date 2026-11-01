#!/usr/bin/env python3
"""Check the recorded source attribution, licenses and comment-only modifications.

This is a reproducible inventory check, not a legal opinion. Upstream comparisons
are recorded in audits/attribution.json; this offline check verifies their retained
files and notices against that record, without downloading or executing code.
"""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    record = json.loads((ROOT / 'audits/attribution.json').read_text())
    errors = []
    files = record['files']
    paths = [row['path'] for row in files]
    expected = {str(p.relative_to(ROOT)) for family in
                ('OAI', 'PrimeNumberTheoremAnd', 'RellichKondrachov')
                for p in (ROOT / family).rglob('*.lean')}
    expected.update('FractionalPrimes/Literature/JSW/' + name + '.lean'
                    for name in ('SchurKernel', 'SmoothL1Translation'))
    if len(paths) != len(set(paths)) or set(paths) != expected:
        errors.append('registered third-party Lean inventory differs from discovered inventory')
    licenses = {row['path']: row for row in record['license_and_citation_files']}
    for row in files + list(licenses.values()) + record['support_files']:
        path = ROOT / row['path']
        if not path.is_file() or path.is_symlink():
            errors.append('missing/nonregular file: ' + row['path'])
            continue
        data = path.read_bytes()
        if digest(data) != row['sha256']:
            errors.append('content hash differs: ' + row['path'])
        for block in row.get('retained_notice_blocks', []):
            if block.encode() not in data:
                errors.append('original notice not retained: ' + row['path'])
        if 'license_path' in row and row['license_path'] not in licenses:
            errors.append('unregistered license: ' + row['license_path'])
        if 'added_prefix' in row:
            prefix = row['added_prefix'].encode()
            if not data.startswith(prefix) or b'Modified for the Fractional Primes submission' not in prefix:
                errors.append('missing prominent modification notice: ' + row['path'])
            else:
                restored = row.get('replaced_prefix', '').encode() + data[len(prefix):]
                if digest(restored) != row['pre_notice_sha256']:
                    errors.append('edit exceeds recorded comment header: ' + row['path'])
    for name in ('NOTICE', 'THIRD-PARTY.md', 'ACKNOWLEDGMENTS.md', 'CITATIONS.bib'):
        if not (ROOT / name).is_file():
            errors.append('missing attribution entry point: ' + name)
    result = dict(passed=not errors, third_party_lean_files=len(files),
                  license_and_citation_files=len(licenses), errors=errors,
                  attribution_record_sha256=digest((ROOT / 'audits/attribution.json').read_bytes()),
                  checker_sha256=digest(Path(__file__).read_bytes()),
                  limitation='Checks the identified inventory and its recorded notices; not legal clearance.')
    (ROOT / 'audits/attribution_check.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))
    return 0 if result['passed'] else 1


if __name__ == '__main__':
    sys.exit(main())
