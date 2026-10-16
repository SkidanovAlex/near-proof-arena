#!/usr/bin/env python3
"""Native cache bytes versus the proved-equal Lean source evaluator."""
import argparse, hashlib, json, struct, subprocess, sys
from pathlib import Path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--evaluated-results', type=Path, required=True)
    parser.add_argument('--rs-binary', type=Path, required=True)
    parser.add_argument('--native-source', type=Path, required=True)
    parser.add_argument('--reference-directory', type=Path, required=True)
    parser.add_argument('--evaluation-theorem', type=Path, required=True)
    parser.add_argument('--output-directory', type=Path, required=True)
    args = parser.parse_args()
    sys.path.insert(0, str(args.reference_directory))
    from pq384_primitives import merkle_tree, merkle_path, verify_path, field_words
    inputs = args.evaluated_results/'inputs.json'
    outputs = args.evaluated_results/'lean-results.json'
    cases = json.loads(inputs.read_text())
    expected = json.loads(outputs.read_text())
    assert len(cases) == len(expected) and cases
    out = args.output_directory
    out.mkdir(parents=True, exist_ok=True)
    comparisons = []
    for ordinal, (case, model) in enumerate(zip(cases, expected)):
        leaf_count = 2**(case['n']+case['p']+1)
        cache = out/f'{ordinal}-cache'
        assert not cache.exists(), 'Immutable cache directory already exists'
        source = dict(rows=case['rows'], packing=2**case['p'], indices=list(range(leaf_count)),
                      cache_directory=str(cache.resolve()))
        inp, result = out/f'{ordinal}-input.json', out/f'{ordinal}-native.json'
        inp.write_text(json.dumps(source, separators=(',', ':')))
        subprocess.run([str(args.rs_binary), str(inp), str(result)], check=True)
        native = json.loads(result.read_text())
        context = bytes(case['context'])
        root = bytes(model['root'])
        assert native['context_hex'] == context.hex()
        assert native['root'] == list(struct.unpack('<12I', root))
        assert [opening['index'] for opening in native['openings']] == list(range(leaf_count))
        assert [opening['leaf'] for opening in native['openings']] == model['source']
        leaves = [field_words(leaf) for leaf in model['source']]
        reference_root, layers = merkle_tree(leaves, context)
        assert root == reference_root
        assert (cache/'leaves.u32').read_bytes() == b''.join(leaves)
        assert (cache/'coefficients.u32').read_bytes() == b''.join(field_words(lane) for lane in model['coefficients'])
        assert (cache/'tree.sha384').read_bytes() == b''.join(digest for layer in layers for digest in layer)
        for opening in native['openings']:
            path = [struct.pack('<12I', *words) for words in opening['path']]
            assert path == merkle_path(layers, opening['index'])
            assert verify_path(root, context, leaf_count, opening['index'], leaves[opening['index']], path)
        comparisons.append(dict(log_rows=case['n'], packing=2**case['p'], width=case['width'], leaves=leaf_count))
    paths = [Path(__file__), args.rs_binary, args.native_source, args.evaluation_theorem, inputs, outputs,
             args.evaluated_results/'report.json', args.reference_directory/'pq384_primitives.py']
    report = dict(status='PASS', cases=comparisons, leaves=sum(x['leaves'] for x in comparisons),
                  compared=['all coefficients', 'all leaf bytes', 'all tree digests', 'context', 'root', 'all opening paths'],
                  files=[dict(path=str(p), sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in paths],
                  limitations=['Uses Lean evaluation form proved equal to mutable FFT model; original slow direct evaluator did not complete.',
                               'Bounded native executable parity only, not a formal Rust machine execution refinement.',
                               'Fixed computed sources only; unknown-root extraction and cryptographic soundness remain separate.'])
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('files','limitations')}))


if __name__ == '__main__':
    main()
