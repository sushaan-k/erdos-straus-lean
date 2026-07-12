# Lean formalization guide

## Scope

`EscAnalytic/Paper.lean` is the canonical entry point. Its main theorem is:

```lean
theorem erdos_straus_exceptional_set_bound :
    IsMainBound exceptionalCount
```

The theorem has no caller-supplied hypotheses. Lean checks its full derivation
from nine named analytic inputs. The prime, large-prime-factor, and geometric
corollaries in the same file have exactly the same dependency set.

The fixed-numerator theorem and the growing-numerator and quartic variants are
not presented as closed results in this guide. Their current Lean statements
are conditional reductions, matching the explicit hypotheses in those parts of
the development.

## Main theorem trust boundary

The closed main theorem uses the following project axioms. Every other step on
its dependency path is a Lean theorem.

| Lean input | Manuscript role |
|---|---|
| `standard_brun_titchmarsh_reciprocal_bound` | reciprocal Brun--Titchmarsh estimate, `lem:BT-recip` |
| `standard_modular_suen_correlation_inequality` | Suen correlation inequality, `thm:CRT-nohit` |
| `standard_ordinary_squarefree_progression_coprime_density_lower_long` | lower half of `lem:ordinary-sqf` |
| `standard_ordinary_squarefree_progression_coprime_density_upper_yu` | tensor-range squarefree progression estimate used in `thm:tensor-e` |
| `standard_prime_product_log_power_rough_window_count_discrepancy_uniform_normalized_small_bound` | linear-sieve fundamental-lemma estimate in `lem:rough-sqf` |
| `standard_prime_recip_sharp_mertens_nat_defect_eventually_upper_bound` | Mertens upper estimate used by the rough Euler products |
| `standard_prime_recip_window_mertens_lower_bound` | positive reciprocal-prime mass in the fixed prime window |
| `standard_reciprocal_bombieri_vinogradov_weighted_same_carrier` | divisor-weighted reciprocal Bombieri--Vinogradov estimate, `lem:weightedBV` |
| `standard_selberg_upper_long_progressions` | Selberg upper-bound sieve, `lem:selberg-upper` |

The weighted reciprocal Bombieri--Vinogradov declaration is a packaged version
of the maximal Bombieri--Vinogradov, dyadic partial-summation, and divisor-weight
argument written in the manuscript. That reduction has not been reconstructed
inside Lean. Likewise, the tensor-range squarefree progression declaration is
the uniform estimate consumed by the formal tensor proof. These are the two
strongest items at the present trust boundary; they should not be mistaken for
kernel-derived facts.

Four additional analytic axioms are declared for other manuscript routes but
are absent from the closed main theorem's dependency closure: maximal
Bombieri--Vinogradov, weighted Titchmarsh, Selberg--Delange, and the
polylogarithmic-modulus squarefree upper estimate.

The squarefree upper interfaces include the endpoint hypotheses needed for
their statements to be true. The polylogarithmic version requires `0 < a0` and
`0 < c0`; the tensor-range version requires `sigma < a0`.

## Reading order

1. `EscLeanChecks.lean`: finite arithmetic certificates and the elementary
   Erdős--Straus identities.
2. `EscAnalytic/Core.lean`: parameters, scales, and exact-divisor data.
3. `EscAnalytic/Inputs.lean`: finite analytic carriers and named external
   estimates.
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

Build the public entry module from the repository root:

```bash
lake build EscAnalytic.Paper
lake env lean EscAnalytic/TrustBoundary.lean
```

The second command fails if the public theorem's dependency closure differs
from Lean's three foundational axioms and the nine external theorems listed
above. A dependency on `sorryAx` therefore fails the same check.
