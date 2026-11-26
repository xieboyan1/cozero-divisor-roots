"""Independent exact checks for the cozero-divisor paper. Python standard library."""
from collections import Counter
from fractions import Fraction
from math import gcd


def maximal_clique_sizes(neighbors):
    """Enumerate maximal cliques by Bron--Kerbosch with a pivot."""
    counts = Counter()

    def visit(size, possible, excluded):
        if not possible and not excluded:
            counts[size] += 1
            return
        pivot = max(possible | excluded, key=lambda v: len(possible & neighbors[v]))
        for vertex in sorted(possible - neighbors[pivot]):
            visit(size + 1, possible & neighbors[vertex], excluded & neighbors[vertex])
            possible.remove(vertex)
            excluded.add(vertex)

    visit(0, set(neighbors), set())
    return counts


def check_graph(p, q, m):
    n = p**m * q
    vertices = [x for x in range(1, n) if gcd(x, n) > 1]
    neighbors = {v: set() for v in vertices}
    # Build the complement directly from principal-ideal membership in Z/nZ.
    for i, x in enumerate(vertices):
        for y in vertices[:i]:
            if x % gcd(y, n) == 0 or y % gcd(x, n) == 0:
                neighbors[x].add(y)
                neighbors[y].add(x)
    observed = maximal_clique_sizes(neighbors)
    degree = (q - 1) * p**(m - 1)
    predicted = Counter([degree] + [degree - 1 - (q - p - 1)*p**j for j in range(m)])
    assert observed == predicted, (p, q, m, observed, predicted)
    print(f'p={p}, q={q}, m={m}, nonzero coefficients (exponent, count): {sorted(observed.items())}')


def check_extremal_limit():
    # If r solves sum r^(1+2*2^j)=1, then the extremal limit is -1/r.
    r_lower = Fraction(100_000_000, 124_923_133)
    r_upper = Fraction(100_000_000, 124_923_131)
    exponents = [1 + 2*2**j for j in range(7)]
    next_exponent = 1 + 2*2**7
    partial_lower = sum(r_lower**e for e in exponents)
    tail_bound = r_lower**next_exponent / (1 - r_lower)
    assert partial_lower + tail_bound < 1 < sum(r_upper**e for e in exponents)
    print('p=2, q=5: -1.24923133 < outermost limit < -1.24923131 (exact rational enclosure)')


if __name__ == '__main__':
    for pair, indices in [((2, 3), range(1, 5)), ((2, 5), range(1, 5)),
                          ((3, 5), range(1, 4)), ((3, 7), range(1, 3)),
                          ((5, 7), range(1, 3))]:
        for index in indices:
            check_graph(*pair, index)
    check_extremal_limit()
