# Lean formalization guide

## Scope

`EscAnalytic/Paper.lean` is the canonical entry point. Its main theorem is:

```lean
theorem erdos_straus_exceptional_set_bound :
    IsMainBound exceptionalCount
```

The theorem has no caller-supplied hypotheses. Lean checks its derivation from
nine named statements: cited theorems and the exact specializations proved in
the manuscript. The prime, large-prime-factor, and geometric corollaries in
the same file currently have the same dependency set.

The fixed-numerator theorem is not currently a closed Lean result; the
fixed-numerator modules contain a conditional reduction. The growing-numerator
and quartic modules likewise record conditional reductions, matching the
explicit hypotheses in the manuscript.

## Cited theorems and specializations

The closed main theorem uses the following project axioms. There are no other
project axioms on its dependency path, and all remaining proof obligations are
discharged in Lean.

| Lean declaration | Manuscript role |
|---|---|
| `standard_brun_titchmarsh_reciprocal_bound` | reciprocal Brun–Titchmarsh estimate, `lem:BT-recip` |
| `standard_modular_suen_correlation_inequality` | Suen correlation inequality, `thm:CRT-nohit` |
| `standard_ordinary_squarefree_progression_coprime_density_lower_long` | long squarefree progression lower estimate used in the proof of `lem:phi-progression-average` |
| `standard_ordinary_squarefree_progression_coprime_density_upper_yu` | tensor-range squarefree progression estimate used in `thm:tensor-e` |
| `standard_prime_product_log_power_rough_window_count_discrepancy_uniform_normalized_small_bound` | linear-sieve fundamental-lemma estimate in `lem:rough-sqf` |
| `standard_prime_recip_sharp_mertens_nat_defect_eventually_upper_bound` | Mertens upper estimate used by the rough Euler products |
| `standard_prime_recip_window_mertens_lower_bound` | positive reciprocal-prime mass in the fixed prime window |
| `standard_reciprocal_bombieri_vinogradov_weighted_same_carrier` | divisor-weighted reciprocal Bombieri–Vinogradov estimate, `lem:weightedBV` |
| `standard_selberg_upper_long_progressions` | Selberg upper-bound sieve, `lem:selberg-upper` |

The exact manuscript reductions are not all repeated in Lean. In particular,
the weighted reciprocal Bombieri–Vinogradov declaration packages maximal
Bombieri–Vinogradov, dyadic partial summation, and the divisor-weight argument.
The long coprime squarefree lower estimate and the tensor-range squarefree
progression upper estimate are also stated directly in the forms consumed by
the formal proof. The reciprocal Brun–Titchmarsh and long-progression Selberg
statements are exact cited specializations rather than derivations from
Mathlib primitives. These declarations are part of the explicit dependency
boundary, not kernel-derived facts.

Four additional theorem statements are declared for other manuscript routes
but are absent from the closed main theorem's dependency closure: maximal
Bombieri–Vinogradov, weighted Titchmarsh, Selberg–Delange, and the
polylogarithmic-modulus squarefree upper estimate.

The squarefree upper interfaces include the endpoint hypotheses needed for
their statements to be true. The polylogarithmic version requires `0 < a0` and
`0 < c0`; the tensor-range version requires `sigma < a0`.

## Reading order

1. `EscLeanChecks.lean`: finite arithmetic certificates and the elementary
   Erdős--Straus identities.
2. `EscAnalytic/Core.lean`: parameters, scales, and exact-divisor data.
3. `EscAnalytic/Inputs.lean`: finite carriers, cited theorems, and manuscript
   specializations.
4. `EscAnalytic/Family.lean`: the certificate family and the proof that every
   family hit gives an Erdős--Straus representation.
5. `EscAnalytic/MassTensor.lean` and `EscAnalytic/MassEstimates.lean`: mass and
   progression estimates.
6. `EscAnalytic/BrunSuen.lean`, `EscAnalytic/Transfer.lean`, and
   `EscAnalytic/Optimization.lean`: no-hit bounds, finite transfer, and the
   parameter choice.
7. `EscAnalytic/LiftCount.lean` and `EscAnalytic/AbstractMain.lean`: smooth/rough
   lifting and the abstract final assembly.
8. `EscAnalytic/IncrementEstimates.lean`, `EscAnalytic/Assembly.lean`, and
   `EscAnalytic/MainTheorem.lean`: discharge of the concrete paper family
   and the closed theorem.
9. `EscAnalytic/Paper.lean`: stable public theorem names.

`EscAnalytic/Geometry.lean` formalizes the algebraic fan-curve statements. The
fixed-numerator and conditional appendices live in the modules whose names begin
with `FixedNumerator`, `UniformFixedNumerator`, `ReciprocalEH`, and
`QuarticSuen`.

## Verification

Build the project from the repository root:

```bash
lake build
lake build EscAnalytic.TrustBoundary
```

The second command fails if the public theorem's dependency closure differs
from Lean's three foundational axioms and the nine named statements listed
above. A dependency on `sorryAx` therefore fails the same check.
