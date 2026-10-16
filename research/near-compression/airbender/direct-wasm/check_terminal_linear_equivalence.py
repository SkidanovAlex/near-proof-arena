"""Exact symbolic affine normalization, independent of the rewrite algorithm.

Nonlinear products are opaque atoms keyed by their normalized operands. Equal
normal forms imply equal field expressions for every input. This executable
checker is not itself Lean verified and does not establish protocol soundness.
"""
import pq384_ext8_reference as f


class Normalizer:
    def __init__(self):
        self.forms = []
        self.form_ids = {}
        self.atoms = {}
        self.peak_terms = 0

    def intern(self, terms):
        key = tuple(sorted((a, c) for a, c in terms.items() if c != f.ZERO))
        if key not in self.form_ids:
            self.form_ids[key] = len(self.forms)
            self.forms.append(key)
            self.peak_terms = max(self.peak_terms, len(key))
        return self.form_ids[key]

    def atom(self, key):
        if key not in self.atoms:
            self.atoms[key] = len(self.atoms) + 1
        return self.intern({self.atoms[key]: f.ONE})

    def constant(self, expr):
        terms = self.forms[expr]
        if not terms:
            return f.ZERO
        if len(terms) == 1 and terms[0][0] == 0:
            return terms[0][1]
        return None

    def scale(self, expr, coefficient):
        if coefficient == f.ONE:
            return expr
        if coefficient == f.ZERO:
            return self.intern({})
        return self.intern({a: f.mul(c, coefficient) for a, c in self.forms[expr]})

    def operation(self, op, left, right):
        if op == 'mul':
            lc, rc = self.constant(left), self.constant(right)
            if lc is not None:
                return self.scale(right, lc)
            if rc is not None:
                return self.scale(left, rc)
            return self.atom(('mul', min(left, right), max(left, right)))
        terms = dict(self.forms[left])
        combine = f.add if op == 'add' else f.sub
        for atom, coefficient in self.forms[right]:
            terms[atom] = combine(terms.get(atom, f.ZERO), coefficient)
        return self.intern(terms)

    def circuit(self, circuit):
        values = []
        capacity = circuit['private_input_capacity']
        for i, node in enumerate(circuit['nodes']):
            op = node[0]
            if op == 'input':
                if len(node) != 2 or type(node[1]) is not int or not 0 <= node[1] < capacity:
                    raise ValueError('input index')
                result = self.atom(('input', node[1]))
            elif op == 'const':
                result = self.intern({0: f.canonical(node[1:])})
            elif op in ('add', 'sub', 'mul'):
                if len(node) != 3 or any(type(x) is not int or not 0 <= x < i for x in node[1:]):
                    raise ValueError('non-topological gate')
                result = self.operation(op, values[node[1]], values[node[2]])
            else:
                raise ValueError('unknown operation')
            values.append(result)
        root = circuit['root']
        if type(root) is not int or not 0 <= root < len(values):
            raise ValueError('root index')
        return values[root]


def validate(source, target):
    if source['private_input_capacity'] != target['private_input_capacity']:
        raise ValueError('input capacity changed')
    normalizer = Normalizer()
    source_root = normalizer.circuit(source)
    target_root = normalizer.circuit(target)
    if source_root != target_root:
        raise ValueError('different symbolic root expressions')
    return dict(status='PASS', forms=len(normalizer.forms), atoms=len(normalizer.atoms),
                largest_form_terms=normalizer.peak_terms,
                method='Exact affine normalization with opaque normalized nonlinear products',
                scope='Universal input equality checked by Python field arithmetic; checker and field implementation are not Lean-refined')
