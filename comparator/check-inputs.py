#!/usr/bin/env python3
"""Fail closed on changed targets, dependencies, wrappers or pinned proof sources."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, subprocess, sys
from importlib.machinery import SourceFileLoader

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok, message):
    if not ok: raise SystemExit(message)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt-dir', type=Path)
    args = parser.parse_args()
    pins = json.loads((ROOT / 'comparator/pins.json').read_text())
    config = json.loads((ROOT / 'lean/comparator.json').read_text())
    targets = ['SmoothIsometricEmbeddingR4.smooth_isometric_embedding_R4']
    require(config['theorem_names'] == pins['targets'] == targets, 'Target list changed or incomplete')
    require(config['challenge_module'] == 'Challenge' and config['solution_module'] == 'FCSolution', 'Unexpected modules')
    require(sorted(config['permitted_axioms']) == sorted(['propext','Classical.choice','Quot.sound']), 'Unexpected axioms')
    for name, key in [('lean/RELEASE-MANIFEST.json','proof_release_manifest_sha256'),
                      ('comparator/proof-source-lakefile.toml','proof_source_lakefile_sha256'),
                      (pins['fc_draft_path'],'fc_draft_sha256'),
                      ('lean/Challenge.lean','challenge_sha256'),('lean/FCSolution.lean','solution_sha256'),
                      ('lean/FCTargetDefinitions.lean','definitions_sha256')]:
        require(sha(ROOT/name) == pins[key], 'Pinned file changed: ' + name)
    render = SourceFileLoader('r4_render', str(ROOT/'comparator/render-target.py')).load_module()
    for name, content in render.generated().items():
        require((ROOT/name).read_text()==content, 'FC mathematical body differs: ' + name)
    release = json.loads((ROOT/'lean/RELEASE-MANIFEST.json').read_text())
    hashes = {}
    for name, expected in release['files_sha256'].items():
        # The lakefile has only the three declared review libraries appended.
        p = ROOT/'comparator/proof-source-lakefile.toml' if name=='lakefile.toml' else ROOT/'lean'/name
        require(p.is_file() and sha(p)==expected, 'Original proof-release input changed: '+name)
        hashes[name]=expected
    append = '\n\n# Review-only wrappers; original proof modules are unchanged.\n[[lean_lib]]\nname = "Challenge"\n\n[[lean_lib]]\nname = "FCSolution"\n\n[[lean_lib]]\nname = "FCTargetDefinitions"\n'
    require((ROOT/'lean/lakefile.toml').read_text()==(ROOT/'comparator/proof-source-lakefile.toml').read_text()+append, 'Unexpected lakefile changes')
    expected_sources={n for n in hashes if n.endswith('.lean')}
    dirs=['R4Embedding','upstream','models_upstream','analytic','model_atlas','stage07']
    actual={p.relative_to(ROOT/'lean').as_posix() for d in dirs for p in (ROOT/'lean'/d).rglob('*.lean')}
    actual |= {'Verify.lean', 'comparator/Challenge.lean'}
    require(actual==expected_sources, 'Extra or missing proof sources')
    require((ROOT/'lean/lean-toolchain').read_text().strip()==pins['lean_toolchain'], 'Toolchain changed')
    deps={p['name']:p['rev'] for p in json.loads((ROOT/'lean/lake-manifest.json').read_text())['packages']}
    require(deps['mathlib']==pins['mathlib_commit'], 'Mathlib changed')
    git=subprocess.run(['git','-C',str(ROOT),'rev-parse','--show-toplevel'],capture_output=True,text=True)
    commit=None
    if git.returncode==0 and Path(git.stdout.strip()).resolve()==ROOT.resolve():
        commit=subprocess.check_output(['git','-C',str(ROOT),'rev-parse','HEAD'],text=True).strip()
    result={'input_check':'passed','checked_at_utc':datetime.now(timezone.utc).isoformat(),
            'tested_commit':commit,'candidate_only':commit is None,'pins':pins,'config':config,
            'unchanged_proof_release_file_count':len(hashes),'unchanged_proof_release_sha256':hashes,
            'scope':pins['challenge_kind'],'fc_checkout_compatibility':pins['fc_checkout_compatibility']}
    if args.receipt_dir:
        args.receipt_dir.mkdir(parents=True,exist_ok=True)
        (args.receipt_dir/'input-check.json').write_text(json.dumps(result,indent=2)+'\n')
        (args.receipt_dir/'Challenge.lean').write_bytes((ROOT/'lean/Challenge.lean').read_bytes())
    print(f'Input check passed: {len(targets)} target, {len(hashes)} unchanged release inputs; FC checkout compatibility pending.')

if __name__=='__main__': main()
