"""Run Palomar's exact pinned metadata validator in an isolated Python venv."""
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REVISION = '14aa8d6b3c2f14a8540605e37144560b9a00e7e7'
POLICY = ROOT / '.lake' / 'palomar-policy'
VENV = ROOT / '.lake' / 'palomar-metadata-venv'


def run(*arguments):
    subprocess.run(arguments, check=True)


POLICY.parent.mkdir(exist_ok=True)
if not POLICY.exists():
    run('git', 'init', '--quiet', str(POLICY))
    run('git', '-C', str(POLICY), 'remote', 'add', 'origin',
        'https://github.com/PalomarRegistry/PalomarSubmission.git')
    run('git', '-C', str(POLICY), 'fetch', '--quiet', '--depth', '1', 'origin', REVISION)
    run('git', '-C', str(POLICY), 'checkout', '--quiet', '--detach', 'FETCH_HEAD')
head = subprocess.check_output(['git', '-C', str(POLICY), 'rev-parse', 'HEAD'], text=True).strip()
if head != REVISION:
    raise SystemExit('The metadata validator checkout does not match its recorded pin.')
python = VENV / 'bin' / 'python'
if not python.exists() or not (VENV / 'bin' / 'pip').exists():
    run(sys.executable, '-m', 'venv', str(VENV))
run(str(python), '-m', 'pip', '--disable-pip-version-check', 'install', '--quiet',
    '--require-hashes', '-r', str(ROOT / 'scripts' / 'requirements-metadata.txt'))
code = '''import json, sys
from pathlib import Path
sys.path.insert(0, sys.argv[1])
from scripts.submission_contract import load_formalization_metadata
result = load_formalization_metadata(Path(sys.argv[2]))
print("PASS: Palomar's pinned formalization.yaml validator accepted the metadata.")
'''
run(str(python), '-c', code, str(POLICY), str(ROOT / 'formalization.yaml'))
