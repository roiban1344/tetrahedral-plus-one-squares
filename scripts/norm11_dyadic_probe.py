#!/usr/bin/env python3
"""Exact exploration of dyadic obstructions, not a completeness proof.

Read the five existing multiplication tables and inspect a full finite unit
period. Also retain the original necessary condition xi[0] = d*r^2.
No output of this script is used as a Lean axiom or certificate.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def read_ring(d):
    source = (ROOT / f"lean/Tetrahedral/Quartic/D{d}Ring.lean").read_text()
    body = source.split("def mul (x y : R) : R :=")[1].split("⟨![")[1].split("]⟩")[0]
    # The source expressions contain only these variables and integer arithmetic.
    forms = []
    for term in body.split(","):
        term = re.sub(r"([xy]) ([0-3])", r"\1[\2]", term).strip()
        if re.search(r"[^xy0-9\[\]()+*\s-]", term):
            raise ValueError("Unexpected multiplication-table syntax")
        forms.append(compile(term, "<multiplication table>", "eval"))
    assert len(forms) == 4

    def mul(x, y, modulus):
        return tuple(eval(f, {"__builtins__": {}, "x": x, "y": y}) % modulus for f in forms)

    return source, mul


def vector(name, source):
    return tuple(map(int, re.search(r"def " + name + r" : R := ⟨!\[([^]]+)\]", source)[1].split(",")))


def main():
    for d, e in [(1, 6), (2, 3), (3, 2), (11, 66), (66, 11)]:
        ring, mul = read_ring(d)
        rho = vector("rho", ring)
        source = (ROOT / f"lean/Tetrahedral/Quartic/D{d}.lean").read_text()
        for initial in (["xi0", "xi1"] if d == 2 else ["xi0"]):
            xi = vector(initial, source)
            for k in [4, 6, 8, 10]:
                modulus = 2**k
                one = (1, 0, 0, 0)
                p = one
                for period in range(1, 8 * modulus + 1):
                    p = mul(p, rho, modulus)
                    if p == one:
                        break
                else:
                    raise ValueError("No period within exploration limit")
                squares = {d * i * i % modulus for i in range(modulus)}
                roots, square_roots = [[], []], [[], []]
                x = tuple(v % modulus for v in xi)
                for m in range(period):
                    for j, sign in enumerate([1, -1]):
                        if ((sign * x[0] - 3)**2 - e * x[1]**2 + 2) % modulus == 0:
                            roots[j].append(m)
                            if sign * x[0] % modulus in squares:
                                square_roots[j].append(m)
                    x = mul(x, rho, modulus)
                compact = lambda rows: rows if sum(map(len, rows)) <= 24 else list(map(len, rows))
                print(d, initial, "mod", modulus, "period", period,
                      "f roots", compact(roots), "+ square", compact(square_roots))


if __name__ == "__main__":
    main()
