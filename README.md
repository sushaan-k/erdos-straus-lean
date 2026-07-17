# Erdos--Straus exceptional-set formalization

This repository contains the Lean 4 formalization of an exceptional-set bound
for the Erdos--Straus equation.

The public entry point is `EscAnalytic/Paper.lean`. Its main theorem is:

```lean
theorem erdos_straus_exceptional_set_bound :
    IsMainBound exceptionalCount
```

The theorem has no caller-supplied hypotheses. Its dependency boundary consists
of nine named theorems from analytic number theory; the deduction from those
results to the exceptional-set bound is checked in Lean. `FORMALIZATION.md`
lists the nine results and gives a reading order for the source.

## Build

The project is pinned to Lean and Mathlib `v4.14.0`.

```bash
lake update
lake build EscAnalytic.Paper
lake build EscAnalytic.TrustBoundary
```

## Source map

- `EscLeanChecks.lean` contains the finite arithmetic certificates.
- `EscAnalytic/Inputs.lean` states the external theorem boundary.
- `EscAnalytic/MainTheorem.lean` assembles the concrete family.
- `EscAnalytic/Paper.lean` exposes the main theorem and corollaries.
- `EscAnalytic/TrustBoundary.lean` pins the theorem's exact axiom closure.

The remaining modules contain the intermediate counting, sieve, transfer, and
optimization arguments.
