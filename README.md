# Erdős–Straus exceptional-set formalization

This repository contains the Lean 4 formalization of an exceptional-set bound
for the Erdős–Straus equation.

The public entry point is `EscAnalytic/Paper.lean`. Its main theorem is:

```lean
theorem erdos_straus_exceptional_set_bound :
    IsMainBound exceptionalCount
```

The theorem has no caller-supplied hypotheses. It uses nine named statements:
cited theorems and the exact specializations proved in the manuscript. Lean
checks every subsequent step to the exceptional-set bound.
`FORMALIZATION.md` lists those statements, describes the exact scope of the
formalization, and gives a reading order.

## Build

The project is pinned to Lean and Mathlib `v4.14.0`.

```bash
lake build
lake build EscAnalytic.TrustBoundary
```

## Source map

- `EscLeanChecks.lean` contains the finite arithmetic certificates.
- `EscAnalytic/Inputs.lean` states the cited theorems and manuscript
  specializations.
- `EscAnalytic/MainTheorem.lean` assembles the concrete family.
- `EscAnalytic/Paper.lean` exposes the main theorem and corollaries.
- `EscAnalytic/TrustBoundary.lean` pins the theorem's exact axiom closure.

The remaining modules contain the intermediate counting, sieve, transfer, and
optimization arguments.
