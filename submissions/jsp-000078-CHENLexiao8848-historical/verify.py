#!/usr/bin/env python3
"""Reproduce source, build, type, axiom, and standard Lean replay checks."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / 'evidence'


def checked(command, log_name):
    with (EVIDENCE / log_name).open('w') as log:
        result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        raise SystemExit(f'Failed: {command}; see evidence/{log_name}')
    print('PASS:', ' '.join(command), flush=True)


def main():
    manifest = json.loads((EVIDENCE / 'source-manifest.json').read_text())
    for row in manifest:
        data = (ROOT / row['path']).read_bytes()
        if len(data) != row['bytes'] or hashlib.sha256(data).hexdigest() != row['sha256']:
            raise SystemExit('Source manifest mismatch: ' + row['path'])
    lean_files = sorted((ROOT / 'JSP000078').glob('*.lean'))
    lean_files += [ROOT / 'JSP000078.lean', ROOT / 'Audit.lean']
    words = ['sorry', 'admit', 'unsafe', 'native_decide', 'ofReduceBool',
             'implemented_by', 'extern']
    patterns = ['(?<![A-Za-z0-9_])' + word + '(?![A-Za-z0-9_])' for word in words]
    patterns += ['^[ 	]*axiom(?![A-Za-z0-9_])', 'debug[.]skipKernelTC',
                 'addDeclWithoutChecking']
    for source in lean_files:
        for pattern in patterns:
            if re.search(pattern, source.read_text(), flags=re.MULTILINE):
                raise SystemExit('Forbidden proof-source pattern in ' + source.name)
    print(f'PASS: source manifest and scan ({len(lean_files)} Lean files)', flush=True)
    checked(['lake', 'build'], 'reproduction-build.log')
    checked(['lake', 'env', 'lean', 'JSP000078/Main.lean'], 'reproduction-main.log')
    checked(['lake', 'env', 'lean', 'Audit.lean'], 'reproduction-audit.log')
    audit = (EVIDENCE / 'reproduction-audit.log').read_text()
    lists = re.findall('depends on axioms: ' + re.escape('[') + '([^]]*)' + re.escape(']'), audit, flags=re.DOTALL)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    if len(lists) != 12:
        raise SystemExit('Expected twelve audited theorem declarations')
    for values in lists:
        if {value.strip() for value in values.split(',')} != allowed:
            raise SystemExit('Unexpected theorem axiom dependency')
    modules = sorted('JSP000078.' + p.stem for p in (ROOT / 'JSP000078').glob('*.lean')
                     if p.name != 'AxiomAudit.lean')
    for start in range(0, len(modules), 3):
        checked(['lake', 'env', 'leanchecker', '-v', *modules[start:start + 3]],
                f'reproduction-replay-{start // 3:02d}.log')
    print(f'PASS: all {len(modules)} mathematical modules replayed through the Lean kernel')


if __name__ == '__main__':
    main()
