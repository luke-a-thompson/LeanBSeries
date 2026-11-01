#!/usr/bin/env python3
"""Exact checks for the iterated-area proof of Williamson order transfer.

Uses only the Python standard library. The general proof is in
papers/williamson_order_transfer.tex; these finite checks are independent
comparisons with chronological exponential expansion, not a proof of all orders.
Run: python3 scripts/check_williamson_transfer.py [maximum_order]
"""

from collections import Counter
from fractions import Fraction as Q
from functools import cache
from itertools import product
from math import factorial, prod
import sys


def add(*terms):
    result = {}
    for scale, term in terms:
        for key, value in term.items():
            result[key] = result.get(key, 0) + scale * value
    return {key: value for key, value in result.items() if value}


@cache
def shuffles(u, v):
    if not u or not v:
        return {u + v: 1}
    return add((1, {(u[0],) + w: n for w, n in shuffles(u[1:], v).items()}),
               (1, {(v[0],) + w: n for w, n in shuffles(u, v[1:]).items()}))


def half_shuffle(u, v):
    result = {}
    for a, x in u.items():
        for b, y in v.items():
            result = add((1, result), (x * y, {w + b[-1:]: n
                         for w, n in shuffles(a, b[:-1]).items()}))
    return result


@cache
def area_words(expr):
    if isinstance(expr, int):
        return {(expr,): 1}
    a, b = map(area_words, expr)
    return add((1, half_shuffle(a, b)), (-1, half_shuffle(b, a)))


@cache
def words(multiset):
    if not multiset:
        return ((),)
    return tuple((a,) + w for a in sorted(set(multiset))
                 for w in words(tuple(x for i, x in enumerate(multiset)
                                      if i != multiset.index(a))))


def splits(multiset):
    counts = Counter(multiset)
    letters = sorted(counts)
    for ns in product(*(range(counts[a] + 1) for a in letters)):
        left = tuple(a for a, n in zip(letters, ns) for _ in range(n))
        right = tuple(a for a, n in zip(letters, ns)
                      for _ in range(counts[a] - n))
        if left and right and left <= right:
            yield left, right


def insert_basis(basis, row, expression=None):
    row = {w: Q(x) for w, x in row.items() if x}
    expression = {} if expression is None else expression
    for pivot, (old, old_expr) in sorted(basis.items()):
        if pivot in row:
            scale = row[pivot]
            row = add((1, row), (-scale, old))
            expression = add((1, expression), (-scale, old_expr))
    if not row:
        return False
    pivot = min(row)
    scale = row[pivot]
    basis[pivot] = ({w: x / scale for w, x in row.items()},
                    {key: x / scale for key, x in expression.items()})
    return True


@cache
def area_basis(multiset):
    if len(multiset) == 1:
        return (multiset[0],)
    basis, expressions = {}, []
    for left, right in splits(multiset):
        for a, b in product(area_basis(left), area_basis(right)):
            if insert_basis(basis, area_words((a, b))):
                expressions.append((a, b))
    return tuple(expressions)


@cache
def word_basis(multiset):
    basis = {}
    for left, right in splits(multiset):
        for a, b in product(words(left), words(right)):
            insert_basis(basis, shuffles(a, b), {("product", a, b): Q(1)})
    for expr in area_basis(multiset):
        insert_basis(basis, area_words(expr), {("area", expr): Q(1)})
    if len(basis) != len(words(multiset)):
        raise AssertionError((multiset, len(basis), len(words(multiset))))
    return basis


@cache
def decompose(word):
    remainder, expression = {word: Q(1)}, {}
    for pivot, (row, rhs) in sorted(word_basis(tuple(sorted(word))).items()):
        if pivot in remainder:
            scale = remainder[pivot]
            remainder = add((1, remainder), (-scale, row))
            expression = add((1, expression), (scale, rhs))
    assert not remainder
    return expression


# An ordinary tree is a sorted tuple of children. A vector is a rational
# linear combination of elementary vectors; a moment monomial is a forest.
def vector_key(v):
    return tuple(sorted(v.items()))


def graft_product(u, v):
    """(A Phi_u) * Phi_v, extended bilinearly."""
    result = {}
    for a, x in u.items():
        for b, y in v.items():
            tree = tuple(sorted(b + (a,)))
            result[tree] = result.get(tree, 0) + x * y
    return result


def bracket(u, v):
    return add((1, graft_product(u, v)), (-1, graft_product(v, u)))


def poly_product(a, b):
    result = {}
    for u, x in a.items():
        for v, y in b.items():
            word = tuple(sorted(u + v))
            result[word] = result.get(word, 0) + x * y
    return {word: x for word, x in result.items() if x}


@cache
def tensor_poly(arguments):
    if not arguments:
        return {(): Q(1)}
    alphabet = tuple(dict.fromkeys(arguments))
    word = tuple(alphabet.index(a) for a in arguments)

    def area_vector(expr):
        if isinstance(expr, int):
            return dict(alphabet[expr])
        return bracket(area_vector(expr[0]), area_vector(expr[1]))

    result = {}
    for key, scale in decompose(word).items():
        if key[0] == "area":
            term = {(tree,): x for tree, x in area_vector(key[1]).items()}
        else:
            term = poly_product(*(tensor_poly(tuple(alphabet[i] for i in w))
                                  for w in key[1:]))
        result = add((1, result), (scale, term))
    return result


@cache
def ordered_poly(tree):
    # Prefix substitution turns a monomial M_t1 ... M_tk into Phi_[t1,...,tk].
    return tensor_poly(tuple(vector_key(ordered_poly(child)) for child in tree))


@cache
def size(tree):
    return 1 + sum(map(size, tree))


@cache
def tree_factorial(tree):
    return size(tree) * prod(map(tree_factorial, tree))


@cache
def exact_ordered(tree):
    partial, denominator = 0, 1
    for child in tree:
        partial += size(child)
        denominator *= partial
    return prod(map(exact_ordered, tree), start=Q(1)) / denominator


@cache
def forests(weight):
    if weight == 0:
        return ((),)
    return tuple((t,) + rest for n in range(1, weight + 1)
                 for t in ordered_trees(n) for rest in forests(weight - n))


@cache
def ordered_trees(n):
    return forests(n - 1)


def tableau(alpha, beta):
    s = len(alpha)
    a, gamma, w, prefix = [], [], [Q(0)] * s, [Q(0)] * s
    for i in range(s):
        a.append(tuple(prefix))
        w = [alpha[i] * x + (i == j) for j, x in enumerate(w)]
        gamma.append(tuple(beta[i] * x for x in w))
        prefix = [x + y for x, y in zip(prefix, gamma[-1])]
    return tuple(a), tuple(prefix), tuple(gamma)


def direct_checker(a, b, gamma):
    s = len(b)

    @cache
    def elementary(tree):
        factors = [tuple(sum(a[i][j] * elementary(child)[j] for j in range(s))
                         for i in range(s)) for child in tree]
        return tuple(prod(factor[i] for factor in factors) for i in range(s))

    @cache
    def moment(tree):
        return sum(x * y for x, y in zip(b, elementary(tree)))

    @cache
    def flow(e, tree):
        if not tree:
            return Q(1)
        if not e:
            return Q(0)
        return sum(flow(e - 1, tree[:k]) / factorial(len(tree) - k)
                   * prod(sum(gamma[e - 1][j] * flow(j, child) for j in range(e))
                          for child in tree[k:]) for k in range(len(tree) + 1))

    def check(tree, polynomial):
        value = sum(coefficient * prod(moment(t) for t in monomial)
                    for monomial, coefficient in polynomial.items())
        assert value == flow(s, tree), (tree, value, flow(s, tree))

    return check


def check_missing_directions():
    # The two patterns responsible for the three seventh-order tests in
    # https://github.com/ipitchford/williamson-order-transfer, Section 6.5.
    cases = [((0, 0, 0, 1, 1), ((0, 1), (0, (0, 1))),
              (0, 1, -1, -3, 4, -1, 2, -3, 1, 0)),
             ((0, 0, 1, 2), ((0, 1), (0, 2)),
              (0, 0, -1, 1, 1, -1, 1, -1, 0, -1, 1, 0))]
    for multiset, expr, null in cases:
        coefficient = sum(area_words(expr).get(w, 0) * n
                          for w, n in zip(words(multiset), null))
        assert coefficient
        print(f"Missing direction {multiset}: iterated-area pairing {coefficient}")


def main():
    maximum = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    # Mixed signs, zeros, one-stage and published rational order-four list.
    lists = [([0], [Q(1)]), ([0, 0, -2, 1], [Q(1, 3), 0, -1, Q(2, 5)]),
             ([0, Q(-2, 3), Q(1, 5), -3, Q(2, 7)],
              [Q(1, 2), -1, Q(3, 4), Q(-1, 6), Q(5, 7)]),
             ([0, -1, -1, -11, Q(1, 10)],
              [Q(1, 2), Q(2, 3), Q(-1, 2), Q(-1, 10), Q(1, 6)])]
    checkers = [direct_checker(*tableau(*ls)) for ls in lists]
    check_missing_directions()
    count = 0
    for degree in range(maximum + 1):
        for tree in ordered_trees(degree + 1):
            polynomial = ordered_poly(tree)
            assert all(sum(map(size, monomial)) == degree for monomial in polynomial)
            exact = sum(c * prod(Q(1, tree_factorial(t)) for t in monomial)
                        for monomial, c in polynomial.items())
            assert exact == exact_ordered(tree), (tree, exact, exact_ordered(tree))
            for check in checkers:
                check(tree, polynomial)
            count += 1
        print(f"Degree {degree}: {len(ordered_trees(degree + 1))} ordered coefficients checked",
              flush=True)
    # A non-Williamson explicit tableau must fail the structural identity.
    a = ((Q(0), Q(0), Q(0)), (Q(1), Q(0), Q(0)), (Q(0), Q(1), Q(0)))
    gamma = ((Q(1), Q(0), Q(0)), (Q(-1), Q(1), Q(0)), (Q(0), Q(-1), Q(1)))
    negative = direct_checker(a, (Q(0), Q(0), Q(1)), gamma)
    rejected = False
    for tree in ordered_trees(4):
        try:
            negative(tree, ordered_poly(tree))
        except AssertionError:
            rejected = True
    assert rejected, "Non-Williamson negative control was not rejected"
    print(f"PASS: {count} exact-flow specialisations; {len(checkers) * count} direct expansions; "
          "non-Williamson negative control rejected")


if __name__ == "__main__":
    main()
