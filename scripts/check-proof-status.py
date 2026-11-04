#!/usr/bin/env python3
"""Reject absent advertised declarations or proofs with forbidden axioms.

This is an early readiness check, not a replacement for Palomar Comparator.
It reads the full configuration and never silently restricts to proved results.
"""
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent.parent
config = json.loads((root / 'comparator.json').read_text())
names = config['theorem_names'] + config.get('definition_names', [])
allowed = set(config['permitted_axioms'])
module = config['solution_module']
source = 'module\n\nimport ' + module + '\n\n'
source += '\n'.join('#print axioms ' + name for name in names) + '\n'
(root / '.lake').mkdir(exist_ok=True)
with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', prefix='Readiness',
                                 dir=root / '.lake', delete=False) as f:
    f.write(source)
    path = Path(f.name)
try:
    result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=root,
                            text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
finally:
    path.unlink(missing_ok=True)
print(result.stdout, end='')
forbidden = set()
for group in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', result.stdout,
                        flags=re.DOTALL):
    forbidden |= {a.strip() for a in group.split(',') if a.strip()} - allowed
if result.returncode or forbidden:
    if forbidden:
        print('Forbidden axioms: ' + ', '.join(sorted(forbidden)))
    print('NOT READY: an advertised declaration is missing, failed to load, or has forbidden axioms.')
    sys.exit(1)
print('All advertised declarations exist and use only permitted axioms.')
print('Full independent statement/proof comparison still requires Palomar Comparator.')
