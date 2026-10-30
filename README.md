# Erdős–Straus exceptional sets in Lean

A Lean 4 formalization of *An improved bound for the exceptional set of the
Erdős–Straus equation* by Sushaan Kandukoori, Shrikrishna Ramesh and Pranava
Kumar (July 29, 2026). Everything is proved from Mathlib, including the
Bombieri–Vinogradov theorem. The only axioms used are Lean's `propext`,
`Classical.choice` and `Quot.sound`.

## Main results

`ErdosStraus/Paper.lean` states:

- `ErdosStraus.erdos_straus_exceptional_set_bound` (Theorem 1). The number
  `E(N)` of `2 ≤ n ≤ N` for which `4/n = 1/x + 1/y + 1/z` has no solution in
  positive integers satisfies `E(N) ≤ C N exp(-c (log N)^{3/4})` for `N ≥ 3`.
- `ErdosStraus.erdos_straus_fixed_numerator_exceptional_set_bound`
  (Theorem 2). The same bound for `m/n`, for every fixed `m ≥ 4`.
- `ErdosStraus.erdos_straus_prime_exceptional_pi_bound`. The exceptional
  primes up to `N` number at most `C π(N) exp(-c (log N)^{3/4})`.
- `ErdosStraus.example_2521`, the certificate of Example 1.1.

The Bombieri–Vinogradov theorem is `BombieriVinogradov.standard_form`: for
every `A > 0` there is `B` with

    Σ_{q ≤ N^{1/2} (log N)^{-B}} max_{y ≤ N} max_{(a,q)=1} |π(y; q, a) - li(y)/φ(q)| ≪_A N (log N)^{-A}.

`ErdosStraus/MaximalBV.lean` derives from it a maximal form with ϑ,
`ErdosStraus.Estimates.standard_bombieri_vinogradov_maximal_form`, which the
proof of Lemma 3.8 uses:

    Σ_{q ≤ x^{1/2-ε}} sup_{2 ≤ y ≤ x} max_{(a,q)=1} |ϑ(y; q, a) - y/φ(q)| ≪_{A,ε} x (log x)^{-A}.

Theorem 3.7 as printed, `ErdosStraus.PrimeEstimates.bombieri_vinogradov_prime_count`,
follows from that: for `A > 0` and `0 < θ < 1/2`, uniformly for `x ≥ 3`,

    Σ_{q ≤ x^θ} max_{(a,q)=1} |π(x; q, a) - π(x)/φ(q)| ≪_{A,θ} x (log x)^{-A}.

## Building

The toolchain is Lean `v4.33.0-rc1` and the only dependency is Mathlib
(revision `e4c91783`), both pinned.

```bash
lake exe cache get
lake build
```

To check the axioms, compile a file such as

```lean
import ErdosStraus.Paper
#print axioms ErdosStraus.erdos_straus_exceptional_set_bound
#print axioms ErdosStraus.erdos_straus_fixed_numerator_exceptional_set_bound
```

with `lake env lean Axioms.lean`. Each line reports
`[propext, Classical.choice, Quot.sound]`. The CI workflow does the same.

## Layout

| Path | Contents |
|---|---|
| `Paper.lean` | Theorems 1 and 2, the prime corollary, Example 1.1 |
| `Basic.lean` | The parameters of (4), the scales, the counting function `E(N)`, the prime product `P(z)` and the notation `f ≍ g` |
| `Congruences/` | Representability, Type II solutions and the fan certificates (Section 2) |
| `Estimates/` | Chebyshev and Mertens bounds, squarefree and totient sums in progressions, rough sums, Brun–Hooley sieve, reciprocal sums over primes (Section 3) |
| `MaximalBV.lean` | Bombieri–Vinogradov in the maximal ϑ-form used for Lemma 3.8 |
| `CubicSums/` | Divisor sums of cubic size, local restrictions, Titchmarsh bound, coprime barrier (Section 4) |
| `Counting/` | Binomial moments, the no-hit bound, finite transfer, lifting (Section 5) |
| `Family/` | The selected family for a fixed numerator: masses, divisor sums, overlaps and the final assembly (Section 6) |
| `BombieriVinogradov/` | The proof of the Bombieri–Vinogradov theorem |

## Paper results

| Paper | Lean |
|---|---|
| Theorem 1 | `erdos_straus_exceptional_set_bound` |
| Theorem 2 | `erdos_straus_fixed_numerator_exceptional_set_bound` |
| Exceptional primes (after Theorem 1) | `erdos_straus_prime_exceptional_pi_bound` |
| Example 1.1 | `example_2521` |
| Remark 1.2 | `finite_level_condition_of_log`, `FixedNumeratorMain.level_budget`, `CommonScale.log_scale_cube`, `CommonScale.log_scale_fourth` |
| Theorem 2.1 | `FixedNumeratorTypeII.cross_of_linear`, `FixedNumeratorTypeII.normal_form_of_representation`, `FixedNumeratorTypeII.cross_iff_unit_fractions` |
| Theorem 2.2 | `FixedNumeratorTypeII.completeFan_congruence_iff_typeII_unit_fractions`, `Arithmetic.completeFan_decomposition_of_dvd_square`, `FixedNumeratorTypeII.congruence_iff_linear`, `FixedNumeratorTypeII.not_all_denominators_multiples` |
| Lemma 2.3 | `Arithmetic.fixedFan_positive_unit_fractions`, `fixed_numerator_representable_of_fixed_fan` |
| Lemma 3.1 | `PrimeEstimates.Mertens.prime_estimates`, `PrimeEstimates.Mertens.prime_reciprocal_window` |
| Lemma 3.2 | `ProgressionEstimates.squarefree_reciprocal_asymp`, `ProgressionEstimates.squarefree_coprime_reciprocal_asymp`, `Estimates.progressionRecip_le_log_plus_inv` |
| Lemma 3.3 | `FixedNumeratorFamily.conductor_weights` |
| Lemma 3.4 | `RoughReciprocal.initial_two_sided` |
| Lemma 3.5 | `BrunHooley.prime_progression_count_upper` |
| Lemma 3.6 | `BrunHooley.prime_reciprocal_power_window_bound` |
| Theorem 3.7 | `PrimeEstimates.bombieri_vinogradov_prime_count` |
| Lemma 3.8 | `PrimeEstimates.reciprocalBV_explicit`, `PrimeEstimates.reciprocalBV_weighted` |
| Lemma 4.1 | `DivisorEstimates.tau_square_moebius`, `Estimates.tauSqSum_cubic_remainder` |
| Proposition 4.2 | `DivisorEstimates.interiorDivisors_sum_asymptotic`, `DivisorEstimates.lowerDivisors_sum_asymptotic` |
| Proposition 4.3 | `Estimates.localObstrInteriorMass_cubic_remainder`, `Estimates.singularSeries_pos`, `DivisorEstimates.localObstrInteriorMass_prime_pow_cubic_order`, `DivisorEstimates.exists_two_adic_class` |
| Lemma 4.4 | `DivisorEstimates.weighted_titchmarsh_divisor_bound_of_three_le` |
| Proposition 4.5 | `Estimates.pairwiseSubfanMass_le_log_square`, `DivisorEstimates.coprime_barrier_relative` |
| Lemma 5.1 | `ModularFamily.coefficient_factorial_bound` |
| Theorem 5.2 | `ModularFamily.noHit_uniform_near_leading`, `Conditioning.noHit_le_exp_conditioning` |
| Lemma 5.3 | `ModularFamily.positiveRankCount_abs_sub_main` |
| Theorem 5.4 | `ModularFamily.positive_finite_transfer_uniform_near_leading` |
| Lemma 5.5 | `Counting.lifting` |
| Lemma 6.1 | `FixedNumeratorFamily.reciprocalTotient_asymp_printed` |
| Proposition 6.2 | `FixedNumeratorFamily.numerator_quadratic_masses` |
| Theorem 6.3 | `FixedNumeratorFamily.numerator_residue_masses_normalized` |
| Lemma 6.4 | `FixedNumeratorFamily.numeratorSmallDivisorAverage_two_sided` |
| Lemma 6.5 | `FixedNumeratorFamily.saturationMass_two_sided` |
| Proposition 6.6 | `FixedNumeratorFamily.indexMass_two_sided` |
| Proposition 6.7 | `FixedNumeratorFamily.mass_and_distribution` |
| Lemma 6.8 | `FixedNumeratorFamily.StaticMem.eq_of_compatible_same_prime`, `DirectPrimeCount.fixed_prime_fiber_reciprocal_le`, `DirectPrimeCount.conductor_div_prime_le_power`, `DirectPrimeCount.prime_power_tendsto_zero` |
| Lemma 6.9 | `FixedNumeratorFamily.modularDelta_eventually_small`, `FixedNumeratorFamily.modularDependencyMass_eventually_small`, `FixedNumeratorFamily.increment_eventually_le_one_add_mul_mass` |

Names are relative to the namespace `ErdosStraus`. When a result has several
parts, the names follow the order of the parts. Theorem 5.2 is proved by the
paper's conditioning argument, so Suen's inequality is not needed.

## Credits and license

The files in `ErdosStraus/BombieriVinogradov/` are adapted from
[goldbach-lean](https://github.com/subfish-zhou/goldbach-lean) (commit
`9d4c3a4`, Copyright 2026 UyNewNas, Apache License 2.0), reduced to the proof
of the Bombieri–Vinogradov theorem. The files in
`ErdosStraus/BombieriVinogradov/PNT/` come, through goldbach-lean, from
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
(Apache License 2.0). Each adapted file names its source and says that it was
modified.

This project is released under the Apache License 2.0 (`LICENSE`).
