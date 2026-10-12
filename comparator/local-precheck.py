#!/usr/bin/env python3
"""Run the local draft comparison using an existing built R4 workspace, without claiming CI."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, os, re, shutil, subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--proof-workspace', required=True, type=Path, help='Existing lean/ directory with the pinned R4 build')
    parser.add_argument('--receipt-dir', required=True, type=Path)
    parser.add_argument('--reuse-compiled', action='store_true', help='Reuse byte-identical sources and newer .olean files from a completed local build')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    proof = args.proof_workspace.resolve()
    work = proof/'.fc-review'
    work.mkdir(exist_ok=True)
    receipt = args.receipt_dir.resolve()
    receipt.mkdir(parents=True, exist_ok=True)
    (receipt/'status.txt').write_text('NOT_RUN\n')
    started = datetime.now(timezone.utc).isoformat()
    hashes = {}
    sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    try:
        subprocess.run(['python3', str(root/'comparator/check-inputs.py'), '--receipt-dir', str(receipt/'inputs')], check=True)
        release = json.loads((root/'lean/RELEASE-MANIFEST.json').read_text())
        # Only original proof sources are used from the existing local compilation workspace.
        for name, digest in release['files_sha256'].items():
            if name.endswith('.lean') and name not in {'Verify.lean','comparator/Challenge.lean'}:
                if sha(proof/name)!=digest: raise ValueError('Local proof source differs: '+name)
        lake = shutil.which('lake') or str(Path.home()/'.elan/bin/lake')
        throttle = Path('/private/tmp/r4-lean4341-stage07-throttled/bin/lean')
        lean = str(throttle) if throttle.exists() else str(Path.home()/'.elan/bin/lean')
        paths=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=proof,text=True).strip()
        env=dict(os.environ,LEAN_PATH=str(work)+os.pathsep+paths)
        env['PATH']=str(Path.home()/'.elan/bin')+os.pathsep+env.get('PATH','')
        for module in ['FCTargetDefinitions','Challenge','FCSolution']:
            source = root/'lean'/f'{module}.lean'
            dest = work/source.name
            hashes['lean/'+source.name] = sha(source)
            olean = work/f'{module}.olean'
            reuse = args.reuse_compiled and dest.exists() and dest.read_bytes()==source.read_bytes() and olean.exists() and olean.stat().st_mtime>=dest.stat().st_mtime
            if reuse and module != 'FCTargetDefinitions':
                reuse = olean.stat().st_mtime >= (work/'FCTargetDefinitions.olean').stat().st_mtime
            if not reuse:
                dest.write_bytes(source.read_bytes())
                command=[lean,'-j1','-R',str(work),'-o',str(olean),str(dest)]
                run=subprocess.run(command,cwd=proof,env=env,capture_output=True,text=True)
                (receipt/f'{module}-build.log').write_text(run.stdout+run.stderr)
                if run.returncode!=0: raise ValueError('Local build failed: '+module)
            else:
                (receipt/f'{module}-build.log').write_text('Reused completed local .olean from byte-identical source; source SHA-256: '+sha(source)+'\n')
        compare=root/'comparator/LocalCompare.lean'
        hashes['comparator/LocalCompare.lean']=sha(compare)
        command=[lean,'-j1','--run',str(compare)]
        run=subprocess.run(command,cwd=proof,env=env,capture_output=True,text=True)
        text=run.stdout+run.stderr
        (receipt/'local-comparison.log').write_text(text)
        match=re.search(r'LOCAL_MATCH target=(\S+) declaration_count=(\d+) mismatches=0',text)
        if run.returncode or not match: raise ValueError('Declaration comparison failed; see local-comparison.log')
        (receipt/'axioms.log').write_text(''.join(line+'\n' for line in text.splitlines() if ' depends on axioms: ' in line))
        pins=json.loads((root/'comparator/pins.json').read_text())
        for name in [pins['fc_draft_path'], 'comparator/render-target.py', 'comparator/pins.json']:
            hashes[name] = sha(root/name)
        (receipt/'pins.json').write_bytes((root/'comparator/pins.json').read_bytes())
        (receipt/'Challenge.lean').write_bytes((root/'lean/Challenge.lean').read_bytes())
        (receipt/'FCSolution.lean').write_bytes((root/'lean/FCSolution.lean').read_bytes())
        result={'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),
            'status':'LOCAL_PRECHECK_PASS','target':match.group(1),'compared_declaration_count':int(match.group(2)),
            'mismatches':0,'permitted_axioms':['propext','Classical.choice','Quot.sound'],
            'proof_commit':pins['proof_commit'],'fc_draft_sha256':pins['fc_draft_sha256'],
            'input_sha256':hashes,'tested_commit':None,'linux_sandbox':'NOT_RUN','kernel_replay_for_fc_target':'NOT_RUN',
            'public_ci':'NOT_RUN','fc_checkout_compatibility':pins['fc_checkout_compatibility'],
            'note':'Local declaration comparison of the extracted proposed FC mathematical target and a compiled solution. This is not a full Comparator or an upstream FC checkout validation.'}
        (receipt/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
        (receipt/'status.txt').write_text('LOCAL_PRECHECK_PASS\n')
        print(f'LOCAL_PRECHECK_PASS: {match.group(2)} declarations match; axioms audited. Public Linux CI remains NOT_RUN.')
    except BaseException as error:
        (receipt/'status.txt').write_text('FAIL: '+str(error)+'\n')
        raise
    finally:
        files=sorted(p for p in receipt.rglob('*') if p.is_file() and p.name!='SHA256SUMS')
        (receipt/'SHA256SUMS').write_text(''.join(sha(p)+'  '+p.relative_to(receipt).as_posix()+'\n' for p in files))


if __name__=='__main__': main()
