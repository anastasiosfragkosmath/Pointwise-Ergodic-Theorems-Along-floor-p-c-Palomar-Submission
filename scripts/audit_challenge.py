#!/usr/bin/env python3
"""Static Challenge size and complete source-import boundary audit; not Comparator."""
from __future__ import annotations
import hashlib, json, os, re, subprocess, sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MODULE = re.compile(r'^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$')

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def command(args, cwd):
    return subprocess.run(args, cwd=cwd, check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout.strip()

def header(path):
    """Read the initial import block, ignoring nested and line comments."""
    s=path.read_text(encoding='utf-8').removeprefix('\ufeff'); i=0; depth=0; clean=[]
    # Only scan until first non-header code line. Preserve line endings in comments.
    lines=[]; curr=[]
    while i < len(s):
        if depth:
            if s.startswith('/-',i): depth+=1; i+=2
            elif s.startswith('-/',i): depth-=1; i+=2
            elif s[i]=='\n': curr.append('\n'); lines.append(''.join(curr)); curr=[]; i+=1
            else: i+=1
        elif s.startswith('/-',i): depth=1; i+=2
        elif s.startswith('--',i):
            j=s.find('\n',i); i=len(s) if j<0 else j
        elif s[i]=='\n':
            curr.append('\n'); lines.append(''.join(curr)); curr=[]; i+=1
            code=lines[-1].strip()
            if code and not (code in ('module','prelude') or re.match(r'^(?:(?:public|meta)\s+)*import\b',code)): break
        else: curr.append(s[i]); i+=1
    if depth: raise ValueError('unterminated comment in header')
    if curr: lines.append(''.join(curr))
    imports=[]; first=None; prelude=False
    for line in lines:
        t=line.strip()
        if not t: continue
        if first is None: first=t
        if t=='prelude': prelude=True; continue
        if t=='module': continue
        m=re.fullmatch(r'(?:(?:public|meta)\s+)*import\s+(.+)',t)
        if not m: break
        names=m.group(1).split()
        if names and names[0]=='all': names=names[1:]
        if not names or any(not MODULE.fullmatch(n) for n in names): raise ValueError('unsupported import header: '+t)
        imports.extend(names)
    return first=='module', prelude, imports

def package_source_manifest(errors):
    """Hash all package Lean sources with the source-token audit convention."""
    hashes = {}
    def onerror(error):
        errors.append(f'package source inventory: {error}')
    for directory, dirs, files in os.walk(ROOT, followlinks=False, onerror=onerror):
        base = Path(directory)
        dirs[:] = [name for name in dirs if name not in {'.git', '.lake'}]
        for name in dirs:
            if (base / name).is_symlink():
                errors.append(f'package source inventory: symlinked directory {(base / name).relative_to(ROOT)}')
        for name in files:
            if not name.endswith('.lean'):
                continue
            path = base / name
            rel = str(path.relative_to(ROOT))
            if path.is_symlink():
                errors.append(f'package source inventory: symlinked Lean file {rel}')
                continue
            try:
                hashes[rel] = sha(path)
            except OSError as error:
                errors.append(f'package source inventory: {rel}: {error}')
    if not hashes:
        errors.append('package source inventory: no Lean sources')
    manifest = ''.join(f'{digest}  {path}\n' for path, digest in sorted(hashes.items()))
    return hashlib.sha256(manifest.encode()).hexdigest(), hashes

def main():
    errors=[]; graph={}; pending=['Challenge']; manifests=json.loads((ROOT/'lake-manifest.json').read_text()); packages={p['name']:p for p in manifests['packages']}
    if 'mathlib' not in packages: errors.append('pinned Mathlib missing from manifest')
    roots=[]; pins={}
    for name,p in packages.items():
        directory=ROOT/'.lake/packages'/name
        try:
            rev=command(['git','rev-parse','HEAD'],directory)
            if rev != p['rev']: errors.append(f'{name}: checkout {rev} differs from pinned {p["rev"]}')
            pins[name]={'manifest_rev':p['rev'],'checkout_rev':rev}
        except (OSError, subprocess.CalledProcessError) as e: errors.append(f'{name}: cannot verify checkout revision: {e}')
        roots.append((f'package:{name}',directory / (p.get('subDir') or '')))
    try:
        prefix=Path(command(['lean','--print-prefix'],ROOT)); lean_version=command(['lean','--version'],ROOT); core=prefix/'src/lean'
        expected_version=(ROOT/'lean-toolchain').read_text().strip().split(':')[-1].removeprefix('v')
        if not lean_version.startswith(f'Lean (version {expected_version},'): errors.append('Lean version does not match lean-toolchain')
        if not core.is_dir(): errors.append('Lean toolchain source directory is missing')
        roots.extend([('lean-core',core),('lean-core-lake',core/'lake')])
    except (OSError, subprocess.CalledProcessError) as e:
        lean_version=None
        errors.append(f'cannot locate pinned Lean toolchain: {e}')
    challenge=ROOT/'Challenge.lean'
    try:
        data=challenge.read_bytes(); lines=len(data.decode('utf-8').splitlines()); has_module,_,direct=header(challenge)
        if len(data)>100*1024: errors.append('Challenge exceeds 100 KiB')
        if lines>1000: errors.append('Challenge exceeds 1000 lines')
        if not has_module: errors.append('Challenge lacks leading module header')
    except (OSError,UnicodeError,ValueError) as e:
        print(f'Challenge read error: {e}',file=sys.stderr); return 1
    while pending:
        name=pending.pop()
        if name in graph: continue
        if name=='Challenge': path=challenge; origin='challenge'
        else:
            rel=Path(*name.split('.')).with_suffix('.lean')
            local=ROOT/rel
            if local.is_file(): errors.append(f'proof-source import forbidden: {name}'); continue
            candidates=[(origin,base/rel) for origin,base in roots if (base/rel).is_file()]
            if len(candidates)!=1:
                errors.append(f'{name}: expected one pinned dependency/core source, found {len(candidates)}'); continue
            origin,path=candidates[0]
        try:
            _, prelude, imports=header(path)
        except (OSError,UnicodeError,ValueError) as e: errors.append(f'{name}: {e}'); continue
        # Lean implicitly imports Init unless a module declares prelude.
        if name != 'Init' and not prelude and 'Init' not in imports: imports=['Init']+imports
        graph[name]={'origin':origin,'sha256':sha(path),'imports':imports}
        pending.extend(imports)
    manifest=''.join(f'{name} {node["origin"]} {node["sha256"]}\n' for name,node in sorted(graph.items()))
    package_manifest, package_hashes = package_source_manifest(errors)
    result={'generated_at_utc':datetime.now(timezone.utc).isoformat(),'scope':'static transitive source-import graph, including implicit Init; local proof sources prohibited',
            'limitations':'Static source audit only, not Comparator, kernel checking, or proof verification; dependency revisions verified against manifest, toolchain source selected using lean --print-prefix.',
            'challenge_sha256':sha(challenge),'challenge_bytes':len(data),'challenge_lines':lines,'challenge_module_header':has_module,'direct_imports':direct,
            'audit_script_sha256':sha(Path(__file__)), 'mask_script_sha256':sha(ROOT/'scripts/lean_source_mask.py'),
            'lake_manifest_sha256':sha(ROOT/'lake-manifest.json'), 'lakefile_sha256':package_hashes.get('lakefile.lean'),
            'package_source_manifest_sha256':package_manifest, 'package_source_count':len(package_hashes), 'lean_version':lean_version, 'manifest_sha256':sha(ROOT/'lake-manifest.json'),'toolchain_sha256':sha(ROOT/'lean-toolchain'),'toolchain':(ROOT/'lean-toolchain').read_text().strip(),
            'dependency_pins':pins,'graph_sha256':hashlib.sha256(manifest.encode()).hexdigest(),'graph':dict(sorted(graph.items())),'errors':errors,'passed':not errors}
    out=ROOT/'audits/challenge.json'; out.parent.mkdir(exist_ok=True); out.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({'passed':result['passed'],'bytes':len(data),'lines':lines,'modules':len(graph),'graph_sha256':result['graph_sha256'],'errors':errors},ensure_ascii=False))
    return 0 if result['passed'] else 1
if __name__=='__main__': sys.exit(main())
