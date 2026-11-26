from fractions import Fraction
import json

def staircase_gap(blocks):
    step = Fraction(1, blocks + 1)
    covered = sum((step * (j * step) for j in range(blocks + 1)), Fraction(0))
    return Fraction(1, 2) - covered

results = []
for blocks in (1, 2, 4, 8, 16, 32, 64, 128):
    gap = staircase_gap(blocks)
    expected = Fraction(1, 2 * (blocks + 1))
    assert gap == expected
    results.append({"blocks": blocks, "gap": str(gap)})
print(json.dumps({"status": "PASS", "cases": results}, indent=2))
