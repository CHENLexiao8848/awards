#!/usr/bin/env python3
'''Reproduce the frozen complete finite historical-route formalization.'''
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / 'evidence'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def run(command, filename):
    with (EVIDENCE / filename).open('w') as log:
        result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        raise SystemExit('Check failed; inspect evidence/' + filename)
    print('PASS:', ' '.join(command), flush=True)

def check_axioms(filename, expected):
    text = (EVIDENCE / filename).read_text()
    pattern = 'depends on axioms: ' + re.escape('[') + '([^]]*)' + re.escape(']')
    values = re.findall(pattern, text, re.DOTALL)
    if len(values) != expected or any({x.strip() for x in v.split(',')} != ALLOWED for v in values):
        raise SystemExit('Unexpected axiom inventory in ' + filename)

def main():
    records = json.loads((EVIDENCE / 'source-manifest.json').read_text())
    for row in records:
        data = (ROOT / row['path']).read_bytes()
        if len(data) != row['bytes'] or hashlib.sha256(data).hexdigest() != row['sha256']:
            raise SystemExit('Source hash mismatch: ' + row['path'])
    files = sorted((ROOT / 'JSP000078').glob('*.lean')) + [ROOT / 'JSP000078.lean', ROOT / 'Audit.lean']
    words = ['sorry', 'admit', 'unsafe', 'native_decide', 'ofReduceBool', 'implemented_by', 'extern']
    patterns = ['(?<![A-Za-z0-9_])' + w + '(?![A-Za-z0-9_])' for w in words]
    patterns += ['^[ \t]*axiom(?![A-Za-z0-9_])', 'debug[.]skipKernelTC', 'addDeclWithoutChecking']
    for path in files:
        if any(re.search(p, path.read_text(), re.MULTILINE) for p in patterns):
            raise SystemExit('Forbidden construct: ' + str(path.relative_to(ROOT)))
    print('PASS: source hashes and proof-source scan', flush=True)
    run(['lake', 'build'], 'reproduction-build.log')
    run(['lake', 'build', 'JSP000078.Coloring'], 'reproduction-alternative.log')
    run(['lake', 'env', 'lean', 'JSP000078/Main.lean'], 'reproduction-main.log')
    run(['lake', 'env', 'lean', 'JSP000078/Sharpness.lean'], 'reproduction-sharpness.log')
    run(['lake', 'env', 'lean', 'JSP000078/AxiomAudit.lean'], 'reproduction-axioms-full.log')
    check_axioms('reproduction-axioms-full.log', 18)
    run(['lake', 'env', 'lean', 'Audit.lean'], 'reproduction-audit.log')
    check_axioms('reproduction-audit.log', 8)
    prefix = subprocess.check_output(['lake', 'env', 'lean', '--print-prefix'], cwd=ROOT, text=True).strip()
    checker = Path(prefix) / 'src/lean/LeanChecker.lean'
    if not checker.is_file():
        raise SystemExit('Install the source component of the pinned Lean toolchain for kernel replay')
    modules = sorted('JSP000078.' + p.stem for p in (ROOT / 'JSP000078').glob('*.lean') if p.name != 'AxiomAudit.lean')
    for start in range(0, len(modules), 12):
        run(['lake', 'env', 'lean', '-j2', '--run', str(checker), '-v', *modules[start:start+12]],
            f'reproduction-replay-{start//12:02d}.log')
    print(f'PASS: all {len(modules)} mathematical modules replayed by the pinned Lean kernel')

if __name__ == '__main__':
    main()
