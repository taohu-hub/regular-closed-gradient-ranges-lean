"""Fail-closed checks on this repository's declared submission surface."""
import argparse
import hashlib
import json
import os
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
THEOREM = 'PalomarGradientRanges.theorem_1_1'
STANDARD_AXIOMS = {'propext', 'Quot.sound', 'Classical.choice'}


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def source_files():
    for directory, directories, names in os.walk(ROOT, followlinks=False):
        relative = Path(directory).relative_to(ROOT)
        directories[:] = [name for name in directories if name not in ('.git', '.lake')
                          and (relative / name).as_posix() != 'verification/local']
        for name in directories:
            require(not (Path(directory) / name).is_symlink(), 'Source directory symlink refused.')
        for name in names:
            path = Path(directory) / name
            require(not path.is_symlink(), f'Source symlink refused: {path.relative_to(ROOT)}')
            yield path


def signature(path):
    text = path.read_text()
    declaration = text[text.index('public theorem ' + THEOREM):]
    return declaration.split(' := by\n', 1)[0]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--self-test', action='store_true')
    arguments = parser.parse_args()
    require((ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0',
            'Unexpected Lean toolchain.')
    require((ROOT / 'lakefile.toml').is_file() and not (ROOT / 'lakefile.lean').exists(),
            'Expected one declarative TOML Lakefile.')
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    for package in manifest['packages']:
        require(package['type'] == 'git' and re.fullmatch('[0-9a-f]{40}', package['rev']),
                f'Unpinned dependency: {package["name"]}')
        require(package['url'].startswith('https://github.com/'), 'Non-GitHub dependency.')
    mathlib = next(package for package in manifest['packages'] if package['name'] == 'mathlib')
    require(mathlib['rev'] == '56a005855ea17e0b0958f73ec801ae140b0a1679', 'Unexpected Mathlib pin.')
    config = json.loads((ROOT / 'comparator.json').read_text())
    require(set(config) <= {'challenge_module', 'solution_module', 'theorem_names',
                            'definition_names', 'permitted_axioms', 'enable_nanoda'},
            'Unknown Comparator configuration key.')
    require(config['challenge_module'] == 'Challenge' and config['solution_module'] == 'Solution',
            'Unexpected Comparator modules.')
    require(config['theorem_names'] == [THEOREM] and not config.get('definition_names'),
            'Unexpected compared declarations.')
    require(set(config['permitted_axioms']) == STANDARD_AXIOMS and config.get('enable_nanoda') is True,
            'Unexpected axiom or independent-kernel configuration.')
    total_bytes = 0
    lean_count = 0
    for path in source_files():
        relative = path.relative_to(ROOT).as_posix()
        data = path.read_bytes()
        total_bytes += len(data)
        require(path.suffix != '.tex', f'Manuscript TeX must not be distributed: {relative}')
        if path.suffix != '.lean':
            continue
        lean_count += 1
        text = data.decode('utf-8')
        require(text.splitlines()[0].strip() == 'module', f'Missing module header: {relative}')
        lines = data.count(b'\n') + bool(data and not data.endswith(b'\n'))
        require(lines <= 10000, f'Oversized Lean source: {relative}')
        holes = re.findall(r'\b(?:sorry|admit)\b', text)
        if relative == 'Challenge.lean':
            require(holes == ['sorry'] and lines <= 1000 and len(data) <= 102400,
                    'Unexpected Challenge hole or size.')
        else:
            require(not holes, f'Unauthorized proof hole: {relative}')
        require(not re.search(r'(?m)^\s*(?:(?:public|private|meta|noncomputable)\s+)*axiom\b', text),
                f'Custom axiom declaration: {relative}')
        require(not any(option in text for option in ('debug.skipKernelTC', 'compiler.ignoreErrors')),
                f'Kernel-check bypass: {relative}')
    require(total_bytes <= 500 * 1024 * 1024, 'Submission source tree exceeds 500 MiB.')
    provenance = json.loads((ROOT / 'docs/source-provenance.json').read_text())
    for entry in provenance['modules']:
        path = ROOT / entry['file']
        require(entry['module'] == entry['file'].removesuffix('.lean').replace('/', '.'),
                'Provenance module name does not match its source file.')
        require(hashlib.sha256(path.read_bytes()).hexdigest() == entry['releaseSha256'],
                f'Stale provenance source hash: {entry["file"]}')
    challenge = ROOT / 'Challenge.lean'
    solution = ROOT / 'Solution.lean'
    require(signature(challenge) == signature(solution), 'Challenge/Solution source signatures differ.')
    lock = json.loads((ROOT / 'docs/statement-lock.json').read_text())
    expected = lock['challengeSha256']
    original = challenge.read_bytes()
    require(hashlib.sha256(original).hexdigest() == expected, 'Frozen Challenge identity changed.')
    require(hashlib.sha256(signature(solution).encode()).hexdigest() == lock['signatureSha256'],
            'Frozen Solution signature changed.')
    if arguments.self_test:
        # Identity is a necessary gate after independent source review. These
        # fixtures cannot silently replace that reviewed statement surface.
        text = original.decode()
        extra = ''.join(f' (extra{i} : True)' for i in range(65))
        fixtures = {
            'extra-65-premises': text.replace('(n : ℕ)', '(n : ℕ)' + extra),
            'bundled-extra-premises': text.replace('(n : ℕ)', '(n : ℕ) (gate : True ∧ True)'),
            'zero-fallback-definition': text.replace('public theorem', 'def fakeGradient (_ : ℕ) : ℝ := 0\npublic theorem', 1),
            'deferred-characterization': text.replace('public theorem', 'def chosenObject : ℝ := 0\n-- characterization deferred\npublic theorem', 1),
        }
        require(all(hashlib.sha256(value.encode()).hexdigest() != expected for value in fixtures.values()),
                'A source-replacement regression was accepted.')
        print('PASS: four statement-replacement regressions rejected.')
    print(f'PASS: {lean_count} module sources; canonical statement; pinned dependencies; no production proof holes.')


if __name__ == '__main__':
    main()
