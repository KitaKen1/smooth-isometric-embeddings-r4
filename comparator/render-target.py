#!/usr/bin/env python3
"""Copy FC definitions and target; normalize answer(True) to True for the external proof."""
from pathlib import Path
import argparse

ROOT = Path(__file__).resolve().parents[1]
PATH = 'FClikelean/SmoothIsometricEmbeddingR4.lean'
IMPORTS = """import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.Sheaf.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Topology.LocallyConstant.Basic"""

def generated():
    text = (ROOT / PATH).read_text()
    if text.count('  sorry\n') != 1:
        raise ValueError('Expected exactly one target theorem hole')
    if text.count('answer(True)') != 1:
        raise ValueError('Expected exactly one affirmative FC answer')
    body = text[text.index('namespace SmoothIsometricEmbeddingR4'):]
    a = body.index('@[category research solved')
    b = body.index('theorem smooth_isometric_embedding_R4', a)
    body = body[:a] + body[b:]
    theorem_start = body.rfind('\n/--', 0, body.index('theorem smooth_isometric_embedding_R4'))
    definitions = IMPORTS + '\n\n' + body[:theorem_start] + '\n\nend SmoothIsometricEmbeddingR4\n'
    namespace_header = body[:body.index('/-- An orientation')]
    statement = body[theorem_start:].replace('answer(True)', 'True', 1)
    challenge = 'import FCTargetDefinitions\n\n' + namespace_header + statement
    solution = challenge.replace('import FCTargetDefinitions', 'import FCTargetDefinitions\nimport R4Initial.FinalTheorem', 1)
    solution = solution.replace('  sorry\n',
        '  constructor\n'
        '  · intro _ M _ _ _ _ _ hOrient g\n'
        '    obtain ⟨o, ho⟩ := hOrient\n'
        '    have hOriginal : R4Embedding.IsOrientableSurface M := ⟨⟨o, ho⟩⟩\n'
        '    obtain ⟨F, hSmooth, hInjective⟩ :=\n'
        '      R4Embedding.closedOrientableSurfaceEmbedding.{0} M hOriginal g\n'
        '    exact ⟨F, hSmooth.1, hInjective, hSmooth.2⟩\n'
        '  · intro _\n'
        '    trivial\n')
    return {'lean/FCTargetDefinitions.lean': definitions, 'lean/Challenge.lean': challenge, 'lean/FCSolution.lean': solution}

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check', action='store_true')
    args = p.parse_args()
    for name, content in generated().items():
        path = ROOT / name
        if args.check:
            if path.read_text() != content:
                raise SystemExit('Generated file differs: ' + name)
        else:
            path.write_text(content)
    print('Mathematical-body extraction checked.' if args.check else 'Challenge and solution generated.')
