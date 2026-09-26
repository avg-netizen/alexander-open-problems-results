"""Exact finite controls; the universal tail bound is a Kraft hand argument."""
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path

rows = ((F(0), F(1), F(1, 4), F(1, 4)),
        (F(1), F(0), F(1, 4), F(1, 4)))
weights = (F(1, 4), F(1, 4))
special_values = [sum(w * row[a] for w, row in zip(weights, rows))
                  for a in range(4)]
selected = [sum(weights[e] * rows[e][pair[e]] for e in range(2))
            for pair in ((0, 1), (2, 3))]
assert special_values == [F(1, 4), F(1, 4), F(1, 8), F(1, 8)]
assert selected == [F(0), F(1, 8)]

branches = ('00', '01', '1111')
assert all(not a.startswith(b) for a in branches for b in branches if a != b)
assert sum(F(1, 2 ** len(a)) for a in branches) <= 1
residual = F(1, 16)
premise_margin = min(special_values[:2]) - max(special_values[2:]) - residual
reversal_margin = selected[1] - selected[0] - residual
assert premise_margin == reversal_margin == F(1, 16)

# An affine inequality reaches its extrema at the corners. These checks use
# independent tail values, a superset of all realizable simultaneous tails.
corners = 0
for tails in product((F(0), residual), repeat=6):
    vals = [a + b for a, b in zip(special_values + selected, tails)]
    assert min(vals[:2]) > max(vals[2:4])
    assert vals[4] < vals[5]
    corners += 1

output = {
    'status': 'passed; all-environment mass uses the separate Kraft proof',
    'special_agent_values': list(map(str, special_values)),
    'special_selected_values': list(map(str, selected)),
    'residual_mass_bound': str(residual),
    'premise_margin_at_least': str(premise_margin),
    'reversal_margin_at_least': str(reversal_margin),
    'residual_box_corners_checked': corners,
    'quantifier': 'one explicit admissible universal machine; not every machine'
}
Path(__file__).with_suffix('.json').write_text(json.dumps(output, indent=2) + '\n')
print(json.dumps(output, indent=2))
