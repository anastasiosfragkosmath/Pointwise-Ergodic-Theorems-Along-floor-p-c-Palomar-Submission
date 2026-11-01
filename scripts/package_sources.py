#!/usr/bin/env python3
"""Prepare a deterministic source archive for private transfer."""

import argparse
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parent.parent
EXCLUDED_DIRS = {'.lake', '.git', '__pycache__'}
MANIFEST = 'SOURCE-MANIFEST.json'
SELECTED_AUDITS = {
    'build.json', 'headline_axioms.json', 'source_tokens_challenge_allowed.json',
    'source_tokens_strict.json', 'source_layout.json', 'challenge.json',
    'provenance.json', 'requirements.json', 'policy_review.json',
    'linux_comparator.json', 'linux_headline_axioms.json',
    'linux_source_layout.json', 'linux_challenge.json',
    'provenance_reconciliation.json', 'palomar_mechanical.json',
    'final_revision_checkpoint.json', 'final_headline_axioms.json',
    'final_source_tokens.json', 'final_statement_comparison.json',
    'final_provenance.json', 'challenge_approval_final.json',
    'attribution.json', 'attribution_check.json', 'attribution_checkpoint.json',
}


def inventory():
    files = []
    excluded = 0
    for directory, dirs, names in os.walk(ROOT, followlinks=False):
        base = Path(directory)
        for name in dirs + names:
            if (base / name).is_symlink():
                raise ValueError(f'symlink is not allowed: {(base / name).relative_to(ROOT)}')
        excluded += sum(name in EXCLUDED_DIRS for name in dirs)
        dirs[:] = sorted(name for name in dirs if name not in EXCLUDED_DIRS)
        if base == ROOT / 'audits':
            excluded += len(dirs)
            dirs[:] = []
        for name in sorted(names):
            if (name == '.DS_Store' or name.endswith(('.pyc', '.log', '.tmp', '.swp'))
                    or (base == ROOT / 'audits' and name not in SELECTED_AUDITS)):
                excluded += 1
                continue
            path = base / name
            if not path.is_file():
                raise ValueError(f'not a regular file: {path.relative_to(ROOT)}')
            rel = path.relative_to(ROOT).as_posix()
            if rel == MANIFEST:
                raise ValueError(f'reserved archive name exists in package: {MANIFEST}')
            files.append((rel, path))
    return sorted(files), excluded


def tar_info(name, size, mode):
    entry = tarfile.TarInfo(name)
    entry.size = size
    entry.mode = mode
    entry.mtime = entry.uid = entry.gid = 0
    entry.uname = entry.gname = ''
    return entry


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path,
                        help='archive destination outside the package')
    parser.add_argument('--dry-run', action='store_true')
    args = parser.parse_args()
    output = Path(os.path.abspath(args.output))
    resolved_output = output.resolve()
    if resolved_output == ROOT or ROOT in resolved_output.parents:
        parser.error('output must be outside the package')
    files, excluded = inventory()
    entries = []
    for name, path in files:
        data = path.read_bytes()
        entries.append({'path': name, 'bytes': len(data),
                        'sha256': hashlib.sha256(data).hexdigest(),
                        'executable': bool(path.stat().st_mode & 0o111)})
    manifest = (json.dumps({'files': entries}, indent=2, ensure_ascii=False) + '\n').encode()
    print(json.dumps({'files': len(entries), 'bytes': sum(e['bytes'] for e in entries),
                      'excluded_entries': excluded, 'output': str(output),
                      'manifest_sha256': hashlib.sha256(manifest).hexdigest(),
                      'dry_run': args.dry_run}))
    if args.dry_run:
        return
    # Build in the destination directory, then publish by an exclusive hard
    # link. Unlike rename, link never replaces an existing destination.
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode='wb', dir=output.parent,
                                         prefix='.source-bundle-',
                                         suffix='.tmp', delete=False) as raw:
            temporary = Path(raw.name)
            with gzip.GzipFile(fileobj=raw, mode='wb', filename='', mtime=0) as compressed:
                with tarfile.open(fileobj=compressed, mode='w', format=tarfile.PAX_FORMAT) as archive:
                    by_name = {entry['path']: entry for entry in entries}
                    for name in sorted([*by_name, MANIFEST]):
                        if name == MANIFEST:
                            archive.addfile(tar_info(MANIFEST, len(manifest), 0o644), io.BytesIO(manifest))
                            continue
                        entry = by_name[name]
                        data = (ROOT / entry['path']).read_bytes()
                        if hashlib.sha256(data).hexdigest() != entry['sha256']:
                            raise RuntimeError(f"source changed during packaging: {entry['path']}")
                        mode = 0o755 if entry['executable'] else 0o644
                        archive.addfile(tar_info(entry['path'], len(data), mode), io.BytesIO(data))
        os.link(temporary, output)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


if __name__ == '__main__':
    main()
