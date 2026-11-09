#!/usr/bin/env python3
"""Compare the archived 19-second bridge prototype with the current tactic in WSL.

Builds isolated copies before timing, retains one warmup per version, then runs
counterbalanced pairs of fresh complete 100x100 proof declarations. Never edits
the working tactic or the prepared native workspace.
"""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import random
import shutil
import statistics
import subprocess
import sys
import tempfile


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pairs', type=int, default=6)
    parser.add_argument('--output', default='benchmarks/evidence/prototype-current')
    parser.add_argument('--environment', default='/tmp/determinant-linux/benchmark-environment.json')
    args = parser.parse_args()
    if args.pairs < 2 or args.pairs % 2:
        parser.error('--pairs must be positive, even, and at least two')
    root = Path(__file__).resolve().parent.parent
    output = Path(args.output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    config = json.loads(Path(args.environment).read_text())
    prepared = Path(config['workspace'])
    evidence = root / 'benchmarks/evidence/checked-bridges'
    historical = json.loads((evidence / 'bridges/environment.json').read_text())
    prototype = evidence / 'exploratory-Modular.lean'
    current = root / 'Determinant/Tactic/Modular.lean'
    key = 'Determinant/Tactic/Modular.lean'
    assert digest(prototype) == historical['project_source_sha256'][key]
    for relative, expected in historical['project_source_sha256'].items():
        if relative != key:
            assert digest(root / relative) == expected, f'other source changed: {relative}'
            assert digest(prepared / relative) == expected, f'prepared source differs: {relative}'

    run_root = Path(tempfile.mkdtemp(prefix='determinant-state-compare-'))
    print('Isolated native workspaces:', run_root, flush=True)
    inputs = run_root / 'source-inputs'
    inputs.mkdir()
    manifest = json.loads((evidence / 'bridges/manifest.json').read_text())
    manifest['cases'] = [case for case in manifest['cases'] if case['dimension'] == 100]
    assert len(manifest['cases']) == 1
    case = manifest['cases'][0]
    filename = case['name'] + '.lean'
    shutil.copy2(evidence / 'bridges/inputs' / filename, inputs / filename)
    assert digest(inputs / filename) == case['source_sha256']
    (inputs / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')

    configurations = {}
    modules = ['Determinant/Tactic/Modular', 'Determinant/Tactic/Bridge',
               'Determinant/Tactic/Dispatch', 'Determinant/Tactic', 'Determinant']
    for label, source in [('prototype', prototype), ('current', current)]:
        shutil.copy2(source, output / (label + '-Modular.lean'))
        workspace = run_root / label
        workspace.mkdir()
        shutil.copytree(root / 'Determinant', workspace / 'Determinant')
        shutil.copy2(root / 'Determinant.lean', workspace / 'Determinant.lean')
        shutil.copytree(root / 'scripts', workspace / 'scripts',
                        ignore=shutil.ignore_patterns('__pycache__'))
        shutil.copy2(source, workspace / key)
        library = workspace / '.lake/build/lib/lean'
        shutil.copytree(Path(config['lean_path'][0]), library)
        variant = dict(config, workspace=str(workspace),
                       lean_path=[str(library), *config['lean_path'][1:]])
        configuration = workspace / 'benchmark-environment.json'
        configuration.write_text(json.dumps(variant, indent=2) + '\n')
        configurations[label] = configuration
        env = dict(os.environ, LEAN_PATH=':'.join(variant['lean_path']))
        print('Building', label, flush=True)
        with (output / (label + '-build.log')).open('w') as log:
            for module in modules:
                subprocess.run([config['lean'], '-R', str(workspace), '-o',
                                str(library / (module + '.olean')),
                                str(workspace / (module + '.lean'))], env=env,
                               cwd=workspace, stdout=log, stderr=log, check=True)

    samples = []

    def bench(label, pair, position):
        name = f'pair{pair:02d}-{label}' if pair else 'warmup-' + label
        results = run_root / 'results' / name
        subprocess.run([sys.executable, str(root / 'benchmarks/run_linux.py'),
                        '--environment', str(configurations[label]), '--input', str(inputs),
                        '--output', str(results), '--repeats', '1', '--deadline', '180'],
                       cwd=root, check=True)
        records = json.loads((results / 'results.json').read_text())
        assert len(records) == 1
        record = records[0]
        assert record['exitCode'] == 0 and not record['timedOut']
        assert record['axiomReport'] == '[propext, Classical.choice, Quot.sound]'
        samples.append(dict(variant=label, pair=pair, position=position,
                            directory=name, record=record))
        (output / 'samples.json').write_text(json.dumps(samples, indent=2) + '\n')
        print(name, record['wallSeconds'], 'seconds', flush=True)

    # Declared in advance: warmups remain visible but are separate from the six
    # measured pairs. Every invocation still launches fresh Lean and Sage.
    for position, label in enumerate(['prototype', 'current']):
        bench(label, 0, position)
    for pair in range(1, args.pairs + 1):
        order = ['prototype', 'current'] if pair % 2 else ['current', 'prototype']
        for position, label in enumerate(order):
            bench(label, pair, position)

    for sample in samples:
        subprocess.run([sys.executable, str(root / 'benchmarks/export_results.py'),
                        '--results', str(run_root / 'results' / sample['directory']),
                        '--output', str(output / sample['directory'])], check=True)

    measured = [sample for sample in samples if sample['pair']]
    aggregates = {}
    for label in ['prototype', 'current']:
        rows = [s['record'] for s in measured if s['variant'] == label]
        aggregates[label] = dict(count=len(rows), wallSeconds=[r['wallSeconds'] for r in rows],
            medianSeconds=statistics.median(r['wallSeconds'] for r in rows),
            worstSeconds=max(r['wallSeconds'] for r in rows),
            medianPhasesMs={p: statistics.median(r['phasesMs'][p] for r in rows)
                            for p in rows[0]['phasesMs']},
            medianKernelMs=statistics.median(r['kernelMs'] for r in rows),
            medianFinalKernelMs=statistics.median(r['finalDeclarationKernelMs'] for r in rows))
    ratios = []
    for pair in range(1, args.pairs + 1):
        times = {s['variant']: s['record']['wallSeconds'] for s in measured if s['pair'] == pair}
        ratios.append(times['current'] / times['prototype'])
    logs = list(map(math.log, ratios))
    rng = random.Random(20261108)
    bootstrap = sorted(math.exp(statistics.mean(rng.choices(logs, k=len(logs))))
                       for _ in range(20000))
    summary = dict(implementations=aggregates, pairedCurrentOverPrototype=ratios,
        pairedGeometricMeanRatio=math.exp(statistics.mean(logs)),
        pairedBootstrap95Interval=[bootstrap[500], bootstrap[19499]],
        bootstrapNote='Descriptive paired bootstrap percentile interval; six pairs by default.',
        warmupsPerVersion=1, alternatingOrder=True, nativeRunRoot=str(run_root),
        sourceHashes={label: digest(output / (label + '-Modular.lean'))
                      for label in ['prototype', 'current']},
        producerSHA256=digest(root / 'scripts/det_certificate.py'))
    assert digest(current) == summary['sourceHashes']['current'], 'working source changed during run'
    (output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == '__main__':
    main()
