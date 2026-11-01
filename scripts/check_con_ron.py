"""Attempt Palomar's pinned advisory con-ron replay after mandatory checks."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
POLICY = ROOT / '.lake' / 'palomar-policy'
REVISION = '14aa8d6b3c2f14a8540605e37144560b9a00e7e7'
head = subprocess.check_output(['git', '-C', str(POLICY), 'rev-parse', 'HEAD'], text=True).strip()
if head != REVISION:
    raise SystemExit('The advisory checker policy does not match its recorded pin.')
sys.path.insert(0, str(POLICY))
from scripts.checker_updates import materialize_checker, selected_revision
from scripts.kernel_outcomes import con_ron_outcome
from scripts.verify_submission import primitive_targets

toolchain = (ROOT / 'lean-toolchain').read_text().strip()
prefix = Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip())
work = ROOT / 'verification' / 'local'
work.mkdir(parents=True, exist_ok=True)
destination = ROOT / '.lake' / 'advisory-con-ron'
revision = selected_revision(toolchain)
binary = destination / 'con-ron'
if binary.exists():
    if revision is None or hashlib.sha256(binary.read_bytes()).hexdigest() != revision['binary_sha256']:
        raise SystemExit('Existing advisory checker does not match Palomar policy.')
    provenance = {'kind': 'maintainer-pinned-release', 'source_toolchain': toolchain, **revision}
else:
    binary, provenance = materialize_checker(toolchain, prefix / 'bin' / 'con-ron', destination)
export = work / 'solution.export'
targets = list(dict.fromkeys(['Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind',
    'PalomarGradientRanges.theorem_1_1', 'propext', 'Quot.sound', 'Classical.choice',
    *primitive_targets(prefix)]))
with export.open('wb') as output:
    subprocess.run(['lake', 'env', 'leanexport', 'Solution', '--', *targets],
                   cwd=ROOT, stdout=output, check=True)
argv = ['bwrap', '--ro-bind', '/', '/', '--unshare-all', '--die-with-parent',
        '--new-session', '--proc', '/proc', '--dev', '/dev', '--tmpfs', '/tmp',
        '--clearenv', '--setenv', 'LANG', 'C.UTF-8', '--chdir', '/tmp',
        str(binary.resolve()), '--jobs=2', '--verified', str(export.resolve())]
try:
    process = subprocess.run(argv, capture_output=True, text=True, timeout=1800)
    result = con_ron_outcome(process.returncode, process.stdout, process.stderr)
    (work / 'con-ron.log').write_text(process.stdout + process.stderr)
except subprocess.TimeoutExpired:
    (work / 'con-ron.log').write_text('The local 1800-second advisory replay budget expired.\n')
    result = {'name': 'con-ron', 'status': 'declined', 'reason': 'capacity',
              'exit_code': None, 'detail': 'The local 1800-second advisory replay budget expired.'}
with export.open('rb') as source:
    export_digest = hashlib.file_digest(source, 'sha256').hexdigest()
result.update({'policyCommit': REVISION, 'checker': provenance,
               'solutionExportSha256': export_digest})
(work / 'con-ron.json').write_text(json.dumps(result, indent=2) + '\n')
print(f"Advisory con-ron replay: {result['status']} ({result.get('reason', '')}).", flush=True)
if result['status'] not in ('accepted', 'declined'):
    raise SystemExit('The advisory kernel reported a rejection or execution error; inspect con-ron.log.')
