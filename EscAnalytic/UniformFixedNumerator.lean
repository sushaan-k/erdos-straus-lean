import EscAnalytic.Assembly

/-!
# Uniform fixed-numerator bridges

This file contains small wrappers around the uniform fixed-numerator assembly
surface.  The goal is to keep the finite exact reduced carrier
`fixedNumeratorReducedSumCount` visible at the public boundary, so callers do
not have to provide the raw reduced summatory inequality separately.
-/

namespace EscAnalytic

open Classical
open scoped BigOperators

/-- Uniform exact reduced-count saving from fixed-`m` analytic cores with
common large-range constants.

This is the uniformized form of
`fixedNumeratorReducedSumCount_large_saving_of_paper_suen_analytic_core_exact_reduced_carrier`.
The important point is that the bound is taken only on the common large range:
no finite-initial constant depending on `m` is introduced. -/
theorem uniform_exact_reduced_sum_count_of_uniform_paper_suen_analytic_core_exact_reduced_carrier
    {ι : Type*} {A c : ℝ} {T : ℕ}
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreInputs m ι)
    (hc_core : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_core : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T)
    (hEred_sum_exact : ∀ m : ℕ, 2 ≤ m → ∀ N : ℕ, 3 ≤ N →
      (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
        ∑ b ∈ (H m).cls N, (H m).Mb N b) :
    ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ (Real.log N) ^ A →
        (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
          1 * ((N : ℝ) * saving c N) := by
  intro N m hN hTN hm _hm_log
  have hlarge :=
    fixedNumeratorReducedSumCount_large_saving_of_paper_suen_analytic_core_exact_reduced_carrier
      (H m) (hEred_sum_exact m hm) N hN (le_trans (hT_core m hm) hTN)
  rw [hc_core m hm] at hlarge
  simpa [one_mul] using hlarge

/-- Uniform exact reduced-count saving from fixed-`m` analytic cores whose
analytic reduced carrier is the concrete finite carrier.

This replaces the broad exact-carrier mass-domination hypothesis in
`uniform_exact_reduced_sum_count_of_uniform_paper_suen_analytic_core_exact_reduced_carrier`
with the carrier identity for `Ered`, and delegates the finite mass comparison
to the existing named carrier-equality theorem. -/
theorem uniform_exact_reduced_sum_count_of_uniform_paper_suen_analytic_core_carrier_eq
    {ι : Type*} {A c : ℝ} {T : ℕ}
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreInputs m ι)
    (hc_core : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_core : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T)
    (hEred_eq : ∀ m : ℕ, 2 ≤ m → ∀ N : ℕ, 3 ≤ N →
      (H m).Ered N = fixedNumeratorReducedSumCount m (zNatScale N) N) :
    ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ (Real.log N) ^ A →
        (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
          1 * ((N : ℝ) * saving c N) :=
  uniform_exact_reduced_sum_count_of_uniform_paper_suen_analytic_core_exact_reduced_carrier
    (A := A) (c := c) (T := T) H hc_core hT_core
    (by
      intro m hm
      exact fixedNumeratorPaperSuenAnalyticCoreInputs_exact_reduced_carrier_mass_of_carrier_eq
        (H m) (hEred_eq m hm))

/-- Uniform final assembly from a common-constant fixed-`m` analytic core
family and the exact reduced carrier.

The smooth range, Euler loss, finite lifting, finite-initial absorption, and
denominator loss are all discharged by the existing Rankin/smoothPsi exact
reduced-count assembly.  The remaining caller obligations are precisely the
large-range fixed-`m` Suen cores with constants uniform over the displayed
logarithmic numerator range, plus the concrete reduced-carrier mass domination
for each numerator. -/
noncomputable def UniformNumeratorLargeRangeInputs.of_uniform_paper_suen_analytic_core_exact_reduced_carrier_rankin_smoothPsi
    {ι : Type*} {A c B : ℝ} {T : ℕ}
    (hc : 0 < c) (hB : 0 < B)
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreInputs m ι)
    (hc_core : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_core : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T)
    (hEred_sum_exact : ∀ m : ℕ, 2 ≤ m → ∀ N : ℕ, 3 ≤ N →
      (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
        ∑ b ∈ (H m).cls N, (H m).Mb N b) :
    UniformNumeratorLargeRangeInputs A :=
  UniformNumeratorLargeRangeInputs.of_uniform_final_assembly_rankin_smoothPsi_exact_reduced_sum_count
    (T := T) (Ered_c₁ := c) (Ered_C₁ := 1) (B := B)
    hc zero_lt_one hB
    (uniform_exact_reduced_sum_count_of_uniform_paper_suen_analytic_core_exact_reduced_carrier
      (A := A) (c := c) (T := T) H hc_core hT_core hEred_sum_exact)

/-- Uniform final assembly from common-constant fixed-`m` analytic cores whose
reduced carrier is already the concrete finite carrier. -/
noncomputable def UniformNumeratorLargeRangeInputs.of_uniform_paper_suen_analytic_core_carrier_eq_rankin_smoothPsi
    {ι : Type*} {A c B : ℝ} {T : ℕ}
    (hc : 0 < c) (hB : 0 < B)
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreInputs m ι)
    (hc_core : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_core : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T)
    (hEred_eq : ∀ m : ℕ, 2 ≤ m → ∀ N : ℕ, 3 ≤ N →
      (H m).Ered N = fixedNumeratorReducedSumCount m (zNatScale N) N) :
    UniformNumeratorLargeRangeInputs A :=
  UniformNumeratorLargeRangeInputs.of_uniform_final_assembly_rankin_smoothPsi_exact_reduced_sum_count
    (T := T) (Ered_c₁ := c) (Ered_C₁ := 1) (B := B)
    hc zero_lt_one hB
    (uniform_exact_reduced_sum_count_of_uniform_paper_suen_analytic_core_carrier_eq
      (A := A) (c := c) (T := T) H hc_core hT_core hEred_eq)

/-- Uniform exact reduced-count saving from the paper optimization inputs, with
common large-range constants.

This pushes the preceding bridge one layer closer to the manuscript: the
finite-level condition, saving inequality, Suen-tail inequality, decomposition
bound, class-count bound, and top-coefficient tail are all derived from
`FixedNumeratorPaperSuenAnalyticCoreOptimizationInputs`.  The remaining
large-range assumptions are the genuinely uniform family data and the exact
reduced-carrier mass domination. -/
theorem uniform_exact_reduced_sum_count_of_uniform_paper_suen_analytic_core_optimization_exact_reduced_carrier
    {ι : Type*} {A c : ℝ} {T : ℕ}
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationInputs m ι)
    (hc_opt : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_opt : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T)
    (hEred_sum_exact : ∀ m : ℕ, 2 ≤ m → ∀ N : ℕ, 3 ≤ N →
      (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
        ∑ b ∈ (H m).cls N, (H m).Mb N b) :
    ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ (Real.log N) ^ A →
        (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
          1 * ((N : ℝ) * saving c N) := by
  exact
    uniform_exact_reduced_sum_count_of_uniform_paper_suen_analytic_core_exact_reduced_carrier
      (A := A) (c := c) (T := T)
      (fun m => fixedNumeratorPaperSuenAnalyticCoreInputs_of_optimization (H m))
      (by
        intro m hm
        simpa [fixedNumeratorPaperSuenAnalyticCoreInputs_of_optimization] using
          hc_opt m hm)
      (by
        intro m hm
        simpa [fixedNumeratorPaperSuenAnalyticCoreInputs_of_optimization] using
          hT_opt m hm)
      (by
        intro m hm N hN
        simpa [fixedNumeratorPaperSuenAnalyticCoreInputs_of_optimization] using
          hEred_sum_exact m hm N hN)

/-- Uniform final assembly from common-constant fixed-`m` paper optimization
inputs and the exact reduced carrier.

This is the paper-facing uniform route below the analytic-core wrapper: all
fixed-`m` Suen finite-transfer ingredients are obtained from the optimization
record before the Rankin/smoothPsi uniform assembly is applied. -/
noncomputable def UniformNumeratorLargeRangeInputs.of_uniform_paper_suen_analytic_core_optimization_exact_reduced_carrier_rankin_smoothPsi
    {ι : Type*} {A c B : ℝ} {T : ℕ}
    (hc : 0 < c) (hB : 0 < B)
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationInputs m ι)
    (hc_opt : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_opt : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T)
    (hEred_sum_exact : ∀ m : ℕ, 2 ≤ m → ∀ N : ℕ, 3 ≤ N →
      (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
        ∑ b ∈ (H m).cls N, (H m).Mb N b) :
    UniformNumeratorLargeRangeInputs A :=
  UniformNumeratorLargeRangeInputs.of_uniform_final_assembly_rankin_smoothPsi_exact_reduced_sum_count
    (T := T) (Ered_c₁ := c) (Ered_C₁ := 1) (B := B)
    hc zero_lt_one hB
    (uniform_exact_reduced_sum_count_of_uniform_paper_suen_analytic_core_optimization_exact_reduced_carrier
      (A := A) (c := c) (T := T) H hc_opt hT_opt hEred_sum_exact)

/-- Uniform exact reduced-count saving from paper optimization inputs whose
analytic reduced carrier is the concrete finite carrier.

This removes the caller-supplied exact-carrier mass domination from
`uniform_exact_reduced_sum_count_of_uniform_paper_suen_analytic_core_optimization_exact_reduced_carrier`.
Once `(H m).Ered` is identified with
`fixedNumeratorReducedSumCount m (zNatScale N) N`, the existing `Ered_sum`
field of the optimization record supplies the required comparison to
`∑_b Mb`. -/
theorem uniform_exact_reduced_sum_count_of_uniform_paper_suen_analytic_core_optimization_carrier_eq
    {ι : Type*} {A c : ℝ} {T : ℕ}
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationInputs m ι)
    (hc_opt : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_opt : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T)
    (hEred_eq : ∀ m : ℕ, 2 ≤ m → ∀ N : ℕ, 3 ≤ N →
      (H m).Ered N = fixedNumeratorReducedSumCount m (zNatScale N) N) :
    ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ (Real.log N) ^ A →
        (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
          1 * ((N : ℝ) * saving c N) :=
  uniform_exact_reduced_sum_count_of_uniform_paper_suen_analytic_core_carrier_eq
    (A := A) (c := c) (T := T)
    (fun m => fixedNumeratorPaperSuenAnalyticCoreInputs_of_optimization (H m))
    (by
      intro m hm
      simpa [fixedNumeratorPaperSuenAnalyticCoreInputs_of_optimization] using
        hc_opt m hm)
    (by
      intro m hm
      simpa [fixedNumeratorPaperSuenAnalyticCoreInputs_of_optimization] using
        hT_opt m hm)
    (by
      intro m hm N hN
      simpa [fixedNumeratorPaperSuenAnalyticCoreInputs_of_optimization] using
        hEred_eq m hm N hN)

/-- Uniform final assembly from paper optimization inputs whose reduced carrier
is already the concrete finite carrier.

This is the narrowest optimization-record route before proving the actual
uniform exact reduced summatory estimate: optimization side conditions,
finite-transfer packaging, Rankin smooth range, Euler loss, denominator loss,
and exact-carrier mass domination are internal.  The remaining caller-side
content is the uniform family of optimization records, common constants, and
the carrier identity for `Ered`. -/
noncomputable def UniformNumeratorLargeRangeInputs.of_uniform_paper_suen_analytic_core_optimization_carrier_eq_rankin_smoothPsi
    {ι : Type*} {A c B : ℝ} {T : ℕ}
    (hc : 0 < c) (hB : 0 < B)
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationInputs m ι)
    (hc_opt : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_opt : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T)
    (hEred_eq : ∀ m : ℕ, 2 ≤ m → ∀ N : ℕ, 3 ≤ N →
      (H m).Ered N = fixedNumeratorReducedSumCount m (zNatScale N) N) :
    UniformNumeratorLargeRangeInputs A :=
  UniformNumeratorLargeRangeInputs.of_uniform_final_assembly_rankin_smoothPsi_exact_reduced_sum_count
    (T := T) (Ered_c₁ := c) (Ered_C₁ := 1) (B := B)
    hc zero_lt_one hB
    (uniform_exact_reduced_sum_count_of_uniform_paper_suen_analytic_core_optimization_carrier_eq
      (A := A) (c := c) (T := T) H hc_opt hT_opt hEred_eq)

/-- Convert the exact-direct optimization record into the legacy optimization
record, keeping the concrete reduced summatory carrier definitionally. -/
noncomputable abbrev fixedNumeratorPaperSuenAnalyticCoreOptimizationInputs_of_exact_direct
    {ι : Type*} {m : ℕ}
    (H : FixedNumeratorPaperSuenAnalyticCoreOptimizationExactDirectInputs m ι) :
    FixedNumeratorPaperSuenAnalyticCoreOptimizationInputs m ι :=
  fixedNumeratorPaperSuenAnalyticCoreOptimizationInputs_of_power
    (fixedNumeratorPaperSuenAnalyticCoreOptimizationPowerInputs_of_direct H.toDirect)

/-- Uniform exact reduced-count saving from exact-direct paper optimization
inputs.

This wrapper removes the broad `hEred_sum_exact`/mass-domination argument from
the uniform optimization route.  The caller supplies the standard exact-direct
input record, whose reduced carrier is definitionally
`fixedNumeratorReducedSumCount m (zNatScale N) N`; the existing carrier-equality
wrapper then turns the record's `Ered_sum` field into the exact reduced-carrier
comparison. -/
theorem uniform_exact_reduced_sum_count_of_uniform_paper_suen_analytic_core_optimization_exact_direct
    {ι : Type*} {A c : ℝ} {T : ℕ}
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationExactDirectInputs m ι)
    (hc_exact : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_exact : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T) :
    ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ (Real.log N) ^ A →
        (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
          1 * ((N : ℝ) * saving c N) :=
  uniform_exact_reduced_sum_count_of_uniform_paper_suen_analytic_core_optimization_carrier_eq
    (A := A) (c := c) (T := T)
    (fun m => fixedNumeratorPaperSuenAnalyticCoreOptimizationInputs_of_exact_direct (H m))
    (by
      intro m hm
      simpa [fixedNumeratorPaperSuenAnalyticCoreOptimizationInputs_of_exact_direct,
        fixedNumeratorPaperSuenAnalyticCoreOptimizationInputs_of_power,
        fixedNumeratorPaperSuenAnalyticCoreOptimizationPowerInputs_of_direct,
        FixedNumeratorPaperSuenAnalyticCoreOptimizationExactDirectInputs.toDirect] using
        hc_exact m hm)
    (by
      intro m hm
      simpa [fixedNumeratorPaperSuenAnalyticCoreOptimizationInputs_of_exact_direct,
        fixedNumeratorPaperSuenAnalyticCoreOptimizationInputs_of_power,
        fixedNumeratorPaperSuenAnalyticCoreOptimizationPowerInputs_of_direct,
        FixedNumeratorPaperSuenAnalyticCoreOptimizationExactDirectInputs.toDirect] using
        hT_exact m hm)
    (by
      intro m _hm N _hN
      rfl)

/-- Uniform exact reduced-count saving from exact-direct paper optimization
inputs, with no numerator-size side condition.

The fixed-`m` analytic core supplies its large-range reduced-count estimate
without using a logarithmic restriction on `m`; only the family constants and
cutoffs have to be uniform over `m`. -/
theorem uniform_exact_reduced_sum_count_large_of_uniform_paper_suen_analytic_core_optimization_exact_direct
    {ι : Type*} {c : ℝ} {T : ℕ}
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationExactDirectInputs m ι)
    (hc_exact : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_exact : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T) :
    ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
        1 * ((N : ℝ) * saving c N) := by
  intro N m hN hTN hm
  have hlarge :=
    fixedNumeratorReducedSumCount_large_saving_of_paper_suen_analytic_core_exact_reduced_carrier
      (fixedNumeratorPaperSuenAnalyticCoreInputs_of_optimization
        (fixedNumeratorPaperSuenAnalyticCoreOptimizationInputs_of_exact_direct (H m)))
      (by
        intro N hN
        simpa [fixedNumeratorPaperSuenAnalyticCoreInputs_of_optimization,
          fixedNumeratorPaperSuenAnalyticCoreOptimizationInputs_of_exact_direct,
          fixedNumeratorPaperSuenAnalyticCoreOptimizationInputs_of_power,
          fixedNumeratorPaperSuenAnalyticCoreOptimizationPowerInputs_of_direct,
          FixedNumeratorPaperSuenAnalyticCoreOptimizationExactDirectInputs.toDirect]
          using (H m).Ered_sum N hN)
      N hN
      (by
        exact le_trans (by
          simp [fixedNumeratorPaperSuenAnalyticCoreInputs_of_optimization,
            fixedNumeratorPaperSuenAnalyticCoreOptimizationInputs_of_exact_direct,
            fixedNumeratorPaperSuenAnalyticCoreOptimizationInputs_of_power,
            fixedNumeratorPaperSuenAnalyticCoreOptimizationPowerInputs_of_direct,
            FixedNumeratorPaperSuenAnalyticCoreOptimizationExactDirectInputs.toDirect]
          ) (le_trans (hT_exact m hm) hTN))
  rw [show (fixedNumeratorPaperSuenAnalyticCoreInputs_of_optimization
      (fixedNumeratorPaperSuenAnalyticCoreOptimizationInputs_of_exact_direct (H m))).c = c by
        simpa [fixedNumeratorPaperSuenAnalyticCoreInputs_of_optimization,
          fixedNumeratorPaperSuenAnalyticCoreOptimizationInputs_of_exact_direct,
          fixedNumeratorPaperSuenAnalyticCoreOptimizationInputs_of_power,
          fixedNumeratorPaperSuenAnalyticCoreOptimizationPowerInputs_of_direct,
          FixedNumeratorPaperSuenAnalyticCoreOptimizationExactDirectInputs.toDirect]
          using hc_exact m hm] at hlarge
  simpa [one_mul] using hlarge

/-- Uniform final assembly from exact-direct paper optimization inputs.

All reduced-carrier mass comparison is routed through the exact-direct input's
definitional carrier, so no separate `hEred_sum_exact`-style hypothesis is
exposed at the uniform boundary. -/
noncomputable def UniformNumeratorLargeRangeInputs.of_uniform_paper_suen_analytic_core_optimization_exact_direct_rankin_smoothPsi
    {ι : Type*} {A c B : ℝ} {T : ℕ}
    (hc : 0 < c) (hB : 0 < B)
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationExactDirectInputs m ι)
    (hc_exact : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_exact : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T) :
    UniformNumeratorLargeRangeInputs A :=
  UniformNumeratorLargeRangeInputs.of_uniform_final_assembly_rankin_smoothPsi_exact_reduced_sum_count
    (T := T) (Ered_c₁ := c) (Ered_C₁ := 1) (B := B)
    hc zero_lt_one hB
    (uniform_exact_reduced_sum_count_of_uniform_paper_suen_analytic_core_optimization_exact_direct
      (A := A) (c := c) (T := T) H hc_exact hT_exact)

/-- `thm:uniform-m` directly from exact-direct paper optimization inputs.

This composes the exact-direct reduced-carrier route with the existing
large-range-to-uniform theorem, so callers do not have to build
`UniformNumeratorLargeRangeInputs` by hand.  The remaining input is still the
uniform family of exact-direct fixed-`m` optimization records with common
large-range constants for each logarithmic range `A`. -/
theorem thm_uniform_m_of_uniform_paper_suen_analytic_core_optimization_exact_direct_rankin_smoothPsi
    {ι : Type*}
    (T : ℝ → ℕ) (c B : ℝ → ℝ)
    (hc : ∀ A : ℝ, 0 < A → 0 < c A)
    (hB : ∀ A : ℝ, 0 < A → 0 < B A)
    (H : ∀ A : ℝ, 0 < A → ∀ m : ℕ,
      FixedNumeratorPaperSuenAnalyticCoreOptimizationExactDirectInputs m ι)
    (hc_exact : ∀ A : ℝ, (hA : 0 < A) → ∀ m : ℕ, 2 ≤ m →
      (H A hA m).c = c A)
    (hT_exact : ∀ A : ℝ, (hA : 0 < A) → ∀ m : ℕ, 2 ≤ m →
      (H A hA m).T ≤ T A) :
    ∀ A : ℝ, 0 < A →
      ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∃ Bden > (0 : ℝ),
        ∀ N m : ℕ, 3 ≤ N → 2 ≤ m → (m : ℝ) ≤ (Real.log N) ^ A →
          (fixedNumeratorExceptionalCount m N : ℝ) ≤
            C * (N : ℝ) * uniformNumeratorSaving c Bden m N :=
  thm_uniform_m_of_largeRangeInputs (fun A hA =>
    UniformNumeratorLargeRangeInputs.of_uniform_paper_suen_analytic_core_optimization_exact_direct_rankin_smoothPsi
      (A := A) (c := c A) (B := B A) (T := T A)
      (hc A hA) (hB A hA) (H A hA) (hc_exact A hA) (hT_exact A hA))

/-- Uniform exact reduced-count saving from paper optimization inputs and
reduced-class majorants.

This discharges the exact-carrier mass domination in the previous optimization
bridge by finite reduced-class bookkeeping: membership of the reduced residue
fibers, their per-class majorants, and a comparison from the reduced-class mass
to the global analytic mass `Mb`. -/
theorem uniform_exact_reduced_sum_count_of_uniform_paper_suen_analytic_core_optimization_reduced_class_majorants
    {ι κ : Type*} [DecidableEq κ] {A c : ℝ} {T : ℕ}
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationInputs m ι)
    (hc_opt : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_opt : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T)
    (clsRed : ℕ → ℕ → ℕ → Finset κ)
    (classOfRed : ℕ → ℕ → ℕ → ℕ → κ)
    (Mred : ℕ → ℕ → ℕ → κ → ℝ)
    (hred_class_mem : ∀ m : ℕ, 2 ≤ m → ∀ N : ℕ, 3 ≤ N →
      ∀ s ∈ Finset.Icc 1 N,
        ∀ r ∈ ((Finset.Icc 1 (N / s)).filter
          (fun r => IsRough (zNatScale N) r ∧ ¬ fixedNumeratorRepresentable m r)),
            classOfRed m N s r ∈ clsRed m N s)
    (hred_class_bound : ∀ m : ℕ, 2 ≤ m → ∀ N : ℕ, 3 ≤ N →
      ∀ s ∈ Finset.Icc 1 N, ∀ b ∈ clsRed m N s,
        ((((Finset.Icc 1 (N / s)).filter
          (fun r => (IsRough (zNatScale N) r ∧ ¬ fixedNumeratorRepresentable m r) ∧
            classOfRed m N s r = b)).card : ℕ) : ℝ) ≤ Mred m N s b)
    (hred_mass_to_global : ∀ m : ℕ, 2 ≤ m → ∀ N : ℕ, 3 ≤ N →
      (∑ s ∈ Finset.Icc 1 N, ∑ b ∈ clsRed m N s, Mred m N s b) ≤
        ∑ b ∈ (H m).cls N, (H m).Mb N b) :
    ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ (Real.log N) ^ A →
        (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
          1 * ((N : ℝ) * saving c N) :=
  uniform_exact_reduced_sum_count_of_uniform_paper_suen_analytic_core_optimization_exact_reduced_carrier
    (A := A) (c := c) (T := T) H hc_opt hT_opt
    (by
      intro m hm
      exact
        fixedNumeratorPaperSuenAnalyticCoreOptimizationInputs_exact_reduced_carrier_mass_of_reduced_class_majorants
          (H m) (clsRed m) (classOfRed m) (Mred m)
          (hred_class_mem m hm) (hred_class_bound m hm)
          (hred_mass_to_global m hm))

/-- Uniform final assembly from paper optimization inputs and reduced-class
majorants.

Compared with the exact-carrier optimization route, this no longer asks for the
exact reduced summatory carrier to be dominated by `∑ Mb` as a primitive
assumption.  It proves that domination from reduced-class fiber majorants and the
global reduced-to-analytic mass comparison. -/
noncomputable def UniformNumeratorLargeRangeInputs.of_uniform_paper_suen_analytic_core_optimization_reduced_class_majorants_rankin_smoothPsi
    {ι κ : Type*} [DecidableEq κ] {A c B : ℝ} {T : ℕ}
    (hc : 0 < c) (hB : 0 < B)
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationInputs m ι)
    (hc_opt : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_opt : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T)
    (clsRed : ℕ → ℕ → ℕ → Finset κ)
    (classOfRed : ℕ → ℕ → ℕ → ℕ → κ)
    (Mred : ℕ → ℕ → ℕ → κ → ℝ)
    (hred_class_mem : ∀ m : ℕ, 2 ≤ m → ∀ N : ℕ, 3 ≤ N →
      ∀ s ∈ Finset.Icc 1 N,
        ∀ r ∈ ((Finset.Icc 1 (N / s)).filter
          (fun r => IsRough (zNatScale N) r ∧ ¬ fixedNumeratorRepresentable m r)),
            classOfRed m N s r ∈ clsRed m N s)
    (hred_class_bound : ∀ m : ℕ, 2 ≤ m → ∀ N : ℕ, 3 ≤ N →
      ∀ s ∈ Finset.Icc 1 N, ∀ b ∈ clsRed m N s,
        ((((Finset.Icc 1 (N / s)).filter
          (fun r => (IsRough (zNatScale N) r ∧ ¬ fixedNumeratorRepresentable m r) ∧
            classOfRed m N s r = b)).card : ℕ) : ℝ) ≤ Mred m N s b)
    (hred_mass_to_global : ∀ m : ℕ, 2 ≤ m → ∀ N : ℕ, 3 ≤ N →
      (∑ s ∈ Finset.Icc 1 N, ∑ b ∈ clsRed m N s, Mred m N s b) ≤
        ∑ b ∈ (H m).cls N, (H m).Mb N b) :
    UniformNumeratorLargeRangeInputs A :=
  UniformNumeratorLargeRangeInputs.of_uniform_final_assembly_rankin_smoothPsi_exact_reduced_sum_count
    (T := T) (Ered_c₁ := c) (Ered_C₁ := 1) (B := B)
    hc zero_lt_one hB
    (uniform_exact_reduced_sum_count_of_uniform_paper_suen_analytic_core_optimization_reduced_class_majorants
      (A := A) (c := c) (T := T) H hc_opt hT_opt clsRed classOfRed Mred
      hred_class_mem hred_class_bound hred_mass_to_global)

/-- Uniform exact reduced-count saving from canonical reduced-class global mass.

The finite membership and fiber-majorant parts of the reduced-class comparison
are discharged by the canonical reduced-class image; the remaining assumption is
only the comparison from that canonical class-counted reduced mass to the global
analytic mass `Mb`. -/
theorem uniform_exact_reduced_sum_count_of_uniform_paper_suen_analytic_core_optimization_canonical_reduced_class_global_mass
    {ι κ : Type*} [DecidableEq κ] {A c : ℝ} {T : ℕ}
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationInputs m ι)
    (hc_opt : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_opt : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T)
    (classOfRed : ℕ → ℕ → ℕ → ℕ → κ)
    (hcanonical_mass_to_global : ∀ m : ℕ, 2 ≤ m → ∀ N : ℕ, 3 ≤ N →
      (∑ s ∈ Finset.Icc 1 N,
        ((fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)).card : ℝ) *
          (fixedNumeratorReducedExceptionalCount m (zNatScale N) (N / s) : ℝ)) ≤
        ∑ b ∈ (H m).cls N, (H m).Mb N b) :
    ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ (Real.log N) ^ A →
        (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
          1 * ((N : ℝ) * saving c N) :=
  uniform_exact_reduced_sum_count_of_uniform_paper_suen_analytic_core_optimization_exact_reduced_carrier
    (A := A) (c := c) (T := T) H hc_opt hT_opt
    (by
      intro m hm
      exact
        fixedNumeratorPaperSuenAnalyticCoreOptimizationInputs_exact_reduced_carrier_mass_of_canonical_reduced_class_global_mass
          (H m) (classOfRed m) (hcanonical_mass_to_global m hm))

/-- Uniform final assembly from paper optimization inputs and canonical
reduced-class global mass.

This is the narrowest current uniform fixed-numerator route: the analytic-core
conversion, exact reduced-carrier finite bookkeeping, Rankin smooth range, Euler
loss, and finite initial absorption are all internal.  The remaining
reduced-side content is the canonical reduced-mass comparison to `∑ Mb`, with
constants uniform in the logarithmic numerator range. -/
noncomputable def UniformNumeratorLargeRangeInputs.of_uniform_paper_suen_analytic_core_optimization_canonical_reduced_class_global_mass_rankin_smoothPsi
    {ι κ : Type*} [DecidableEq κ] {A c B : ℝ} {T : ℕ}
    (hc : 0 < c) (hB : 0 < B)
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationInputs m ι)
    (hc_opt : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_opt : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T)
    (classOfRed : ℕ → ℕ → ℕ → ℕ → κ)
    (hcanonical_mass_to_global : ∀ m : ℕ, 2 ≤ m → ∀ N : ℕ, 3 ≤ N →
      (∑ s ∈ Finset.Icc 1 N,
        ((fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)).card : ℝ) *
          (fixedNumeratorReducedExceptionalCount m (zNatScale N) (N / s) : ℝ)) ≤
        ∑ b ∈ (H m).cls N, (H m).Mb N b) :
    UniformNumeratorLargeRangeInputs A :=
  UniformNumeratorLargeRangeInputs.of_uniform_final_assembly_rankin_smoothPsi_exact_reduced_sum_count
    (T := T) (Ered_c₁ := c) (Ered_C₁ := 1) (B := B)
    hc zero_lt_one hB
    (uniform_exact_reduced_sum_count_of_uniform_paper_suen_analytic_core_optimization_canonical_reduced_class_global_mass
      (A := A) (c := c) (T := T) H hc_opt hT_opt classOfRed
      hcanonical_mass_to_global)

/-- Uniform final assembly from the exact fixed-numerator reduced summatory
carrier.

This is the exact-reduced-count variant of
`UniformNumeratorLargeRangeInputs.of_uniform_final_assembly_reduced_sum_lift`.
The raw reduced-sum hypothesis is discharged by taking
`Ered m N = fixedNumeratorReducedSumCount m (z m N) N`; the only remaining
reduced-count input is the large-range bound for this exact finite carrier. -/
noncomputable def UniformNumeratorLargeRangeInputs.of_uniform_final_assembly_exact_reduced_sum_count
    {A Ered_c₁ Ered_C₁ smoothExp smoothC eulerC B : ℝ} (T : ℕ)
    (hEred_c₁ : 0 < Ered_c₁) (hEred_C₁ : 0 < Ered_C₁)
    (hsmoothExp_pos : 0 < smoothExp) (hsmoothExp_lt_one : smoothExp < 1)
    (hsmoothC_pos : 0 < smoothC) (heulerC_pos : 0 < eulerC)
    (hB : 0 < B)
    (smooth euler : ℕ → ℕ → ℝ)
    (z : ℕ → ℕ → ℕ)
    (hEred_exact : ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ (Real.log N) ^ A →
        (fixedNumeratorReducedSumCount m (z m N) N : ℝ) ≤
          Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N))
    (hsmooth : ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ (Real.log N) ^ A →
        smooth m N ≤ smoothC * (N : ℝ) ^ smoothExp)
    (heuler : ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ (Real.log N) ^ A →
        euler m N ≤ eulerC * (Real.log N) ^ (4 : ℕ))
    (heuler_ge_one : ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ (Real.log N) ^ A →
        1 ≤ euler m N)
    (hsmooth_count : ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ (Real.log N) ^ A →
        (fixedNumeratorSmoothRangeCount m (z m N) N : ℝ) ≤ smooth m N) :
    UniformNumeratorLargeRangeInputs A :=
  UniformNumeratorLargeRangeInputs.of_uniform_final_assembly_reduced_sum_lift
    (T := T)
    (Ered := fun m N => fixedNumeratorReducedSumCount m (z m N) N)
    (smooth := smooth) (euler := euler) (z := z)
    hEred_c₁ hEred_C₁ hsmoothExp_pos hsmoothExp_lt_one hsmoothC_pos
    heulerC_pos hB hEred_exact hsmooth heuler hsmooth_count
    (by
      intro N m hN hTN hm hm_log
      exact fixedNumeratorReduced_sum_le_euler_mul_self
        (m := m) (z := z m N) (N := N) (euler := euler m N)
        (heuler_ge_one N m hN hTN hm hm_log))

/-- Global saturation package from the exact fixed-numerator reduced summatory
carrier.

This composes
`UniformNumeratorLargeRangeInputs.of_uniform_final_assembly_exact_reduced_sum_count`
with the existing finite-initial absorption step, so `hyp:uniform-m-saturation`
can be supplied from the exact reduced-count large-range estimate directly. -/
noncomputable def UniformNumeratorSaturationInputs.of_uniform_final_assembly_exact_reduced_sum_count
    {A Ered_c₁ Ered_C₁ smoothExp smoothC eulerC B : ℝ} (T : ℕ)
    (hEred_c₁ : 0 < Ered_c₁) (hEred_C₁ : 0 < Ered_C₁)
    (hsmoothExp_pos : 0 < smoothExp) (hsmoothExp_lt_one : smoothExp < 1)
    (hsmoothC_pos : 0 < smoothC) (heulerC_pos : 0 < eulerC)
    (hB : 0 < B)
    (smooth euler : ℕ → ℕ → ℝ)
    (z : ℕ → ℕ → ℕ)
    (hEred_exact : ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ (Real.log N) ^ A →
        (fixedNumeratorReducedSumCount m (z m N) N : ℝ) ≤
          Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N))
    (hsmooth : ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ (Real.log N) ^ A →
        smooth m N ≤ smoothC * (N : ℝ) ^ smoothExp)
    (heuler : ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ (Real.log N) ^ A →
        euler m N ≤ eulerC * (Real.log N) ^ (4 : ℕ))
    (heuler_ge_one : ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ (Real.log N) ^ A →
        1 ≤ euler m N)
    (hsmooth_count : ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ (Real.log N) ^ A →
        (fixedNumeratorSmoothRangeCount m (z m N) N : ℝ) ≤ smooth m N) :
    UniformNumeratorSaturationInputs A :=
  (UniformNumeratorLargeRangeInputs.of_uniform_final_assembly_exact_reduced_sum_count
    (T := T) hEred_c₁ hEred_C₁ hsmoothExp_pos hsmoothExp_lt_one hsmoothC_pos
    heulerC_pos hB smooth euler z hEred_exact hsmooth heuler heuler_ge_one
    hsmooth_count).toSaturationInputs

/-- Global saturation from the exact reduced summatory carrier, with the
smooth and Euler sides fixed to the checked Rankin/smoothPsi and concrete
Euler-product machinery.

Compared with
`UniformNumeratorSaturationInputs.of_uniform_final_assembly_exact_reduced_sum_count`,
this removes the auxiliary smooth carrier, Euler carrier, smooth-count bound,
and Euler lower-bound fields.  The only remaining analytic input is the
large-range saving estimate for the exact finite carrier
`fixedNumeratorReducedSumCount m (zNatScale N) N`, uniformly over the displayed
logarithmic numerator range. -/
noncomputable def UniformNumeratorSaturationInputs.of_uniform_rankin_smoothPsi_exact_reduced_sum_count
    {A Ered_c₁ Ered_C₁ B : ℝ} (T : ℕ)
    (hEred_c₁ : 0 < Ered_c₁) (hEred_C₁ : 0 < Ered_C₁)
    (hB : 0 < B)
    (hEred_exact : ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ (Real.log N) ^ A →
        (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
          Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N)) :
    UniformNumeratorSaturationInputs A :=
  (UniformNumeratorLargeRangeInputs.of_uniform_final_assembly_rankin_smoothPsi_exact_reduced_sum_count
    (T := T) (Ered_c₁ := Ered_c₁) (Ered_C₁ := Ered_C₁) (B := B)
    hEred_c₁ hEred_C₁ hB hEred_exact).toSaturationInputs

/-- Same as
`UniformNumeratorSaturationInputs.of_uniform_rankin_smoothPsi_exact_reduced_sum_count`,
with the denominator-loss exponent fixed to `1`.  This removes a purely
auxiliary parameter from callers: the hard input remains exactly the uniform
large-range saving estimate for
`fixedNumeratorReducedSumCount m (zNatScale N) N`. -/
noncomputable def UniformNumeratorSaturationInputs.of_uniform_rankin_smoothPsi_exact_reduced_sum_count_one
    {A Ered_c₁ Ered_C₁ : ℝ} (T : ℕ)
    (hEred_c₁ : 0 < Ered_c₁) (hEred_C₁ : 0 < Ered_C₁)
    (hEred_exact : ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ (Real.log N) ^ A →
        (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
          Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N)) :
    UniformNumeratorSaturationInputs A :=
  UniformNumeratorSaturationInputs.of_uniform_rankin_smoothPsi_exact_reduced_sum_count
    (T := T) (Ered_c₁ := Ered_c₁) (Ered_C₁ := Ered_C₁) (B := 1)
    hEred_c₁ hEred_C₁ (by norm_num) hEred_exact

/-- `thm:uniform-m` from uniform exact reduced summatory estimates.

This is the direct paper-hypothesis bridge for the fixed-numerator lane: for
each fixed logarithmic range `A`, a single large-range bound for
`fixedNumeratorReducedSumCount m (zNatScale N) N` supplies the full
`hyp:uniform-m-saturation` package and hence the published uniform-numerator
conclusion. -/
theorem thm_uniform_m_of_uniform_rankin_smoothPsi_exact_reduced_sum_count
    (T : ℝ → ℕ) (Ered_c₁ Ered_C₁ B : ℝ → ℝ)
    (hEred_c₁ : ∀ A : ℝ, 0 < A → 0 < Ered_c₁ A)
    (hEred_C₁ : ∀ A : ℝ, 0 < A → 0 < Ered_C₁ A)
    (hB : ∀ A : ℝ, 0 < A → 0 < B A)
    (hEred_exact : ∀ A : ℝ, 0 < A → ∀ N m : ℕ,
      3 ≤ N → T A ≤ N → 2 ≤ m →
        (m : ℝ) ≤ (Real.log N) ^ A →
          (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
            Ered_C₁ A * ((N : ℝ) * saving (Ered_c₁ A) N)) :
    ∀ A : ℝ, 0 < A →
      ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∃ Bden > (0 : ℝ),
        ∀ N m : ℕ, 3 ≤ N → 2 ≤ m → (m : ℝ) ≤ (Real.log N) ^ A →
          (fixedNumeratorExceptionalCount m N : ℝ) ≤
            C * (N : ℝ) * uniformNumeratorSaving c Bden m N :=
  thm_uniform_m_of_largeRangeInputs (fun A hA =>
    UniformNumeratorLargeRangeInputs.of_uniform_final_assembly_rankin_smoothPsi_exact_reduced_sum_count
      (T := T A) (Ered_c₁ := Ered_c₁ A) (Ered_C₁ := Ered_C₁ A) (B := B A)
      (hEred_c₁ A hA) (hEred_C₁ A hA) (hB A hA) (hEred_exact A hA))

/-- `thm:uniform-m` from uniform exact reduced summatory estimates, with the
denominator-loss exponent fixed internally to `1`. -/
theorem thm_uniform_m_of_uniform_rankin_smoothPsi_exact_reduced_sum_count_one
    (T : ℝ → ℕ) (Ered_c₁ Ered_C₁ : ℝ → ℝ)
    (hEred_c₁ : ∀ A : ℝ, 0 < A → 0 < Ered_c₁ A)
    (hEred_C₁ : ∀ A : ℝ, 0 < A → 0 < Ered_C₁ A)
    (hEred_exact : ∀ A : ℝ, 0 < A → ∀ N m : ℕ,
      3 ≤ N → T A ≤ N → 2 ≤ m →
        (m : ℝ) ≤ (Real.log N) ^ A →
          (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
            Ered_C₁ A * ((N : ℝ) * saving (Ered_c₁ A) N)) :
    ∀ A : ℝ, 0 < A →
      ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∃ Bden > (0 : ℝ),
        ∀ N m : ℕ, 3 ≤ N → 2 ≤ m → (m : ℝ) ≤ (Real.log N) ^ A →
          (fixedNumeratorExceptionalCount m N : ℝ) ≤
            C * (N : ℝ) * uniformNumeratorSaving c Bden m N :=
  thm_uniform_m_of_largeRangeInputs (fun A hA =>
    UniformNumeratorLargeRangeInputs.of_uniform_final_assembly_rankin_smoothPsi_exact_reduced_sum_count
      (T := T A) (Ered_c₁ := Ered_c₁ A) (Ered_C₁ := Ered_C₁ A) (B := 1)
      (hEred_c₁ A hA) (hEred_C₁ A hA) (by norm_num) (hEred_exact A hA))

/-- `thm:uniform-m` from an existential exact reduced summatory estimate.

This is the narrowest theorem-level form of the remaining uniform fixed-
numerator hard core currently exposed by the project: for each logarithmic
numerator range, it asks only for eventual saving of the exact reduced carrier
`fixedNumeratorReducedSumCount m (zNatScale N) N`, with all finite-initial,
smooth, Euler, lifting, and denominator-loss bookkeeping supplied internally. -/
theorem thm_uniform_m_of_exists_uniform_rankin_smoothPsi_exact_reduced_sum_count
    (hEred : ∀ A : ℝ, 0 < A →
      ∃ T : ℕ, ∃ c > (0 : ℝ), ∃ C > (0 : ℝ),
        ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
          (m : ℝ) ≤ (Real.log N) ^ A →
            (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
              C * ((N : ℝ) * saving c N)) :
    ∀ A : ℝ, 0 < A →
      ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∃ Bden > (0 : ℝ),
        ∀ N m : ℕ, 3 ≤ N → 2 ≤ m → (m : ℝ) ≤ (Real.log N) ^ A →
          (fixedNumeratorExceptionalCount m N : ℝ) ≤
            C * (N : ℝ) * uniformNumeratorSaving c Bden m N := by
  apply thm_uniform_m_of_largeRangeInputs
  intro A hA
  let T : ℕ := Classical.choose (hEred A hA)
  have hT :
      ∃ c > (0 : ℝ), ∃ C > (0 : ℝ),
        ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
          (m : ℝ) ≤ (Real.log N) ^ A →
            (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
              C * ((N : ℝ) * saving c N) :=
    Classical.choose_spec (hEred A hA)
  let c : ℝ := Classical.choose hT
  have hc :
      c > (0 : ℝ) ∧
        ∃ C > (0 : ℝ),
          ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
            (m : ℝ) ≤ (Real.log N) ^ A →
              (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
                C * ((N : ℝ) * saving c N) :=
    Classical.choose_spec hT
  let C : ℝ := Classical.choose hc.2
  have hC :
      C > (0 : ℝ) ∧
        ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
          (m : ℝ) ≤ (Real.log N) ^ A →
            (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
              C * ((N : ℝ) * saving c N) :=
    Classical.choose_spec hc.2
  exact
    UniformNumeratorLargeRangeInputs.of_uniform_final_assembly_rankin_smoothPsi_exact_reduced_sum_count
      (T := T) (Ered_c₁ := c) (Ered_C₁ := C) (B := 1)
      hc.1 hC.1 (by norm_num) hC.2

/-- EH numerator package from the exact reduced summatory carrier.

This is the EH-range analogue of
`UniformNumeratorLargeRangeInputs.of_uniform_final_assembly_rankin_smoothPsi_exact_reduced_sum_count`.
It fixes the smooth side to the Rankin/de Bruijn envelope, fixes the Euler loss
to the concrete log-fourth Euler-product bound, performs the finite
smooth/rough lift, and then applies the EH denominator-loss conversion.  Thus
the caller supplies only the exact reduced-count saving over the exponential
numerator range, not an already assembled exceptional-count estimate. -/
noncomputable def EHUniformNumeratorInputs.of_rankin_smoothPsi_exact_reduced_sum_count
    {κ Ered_c₁ Ered_C₁ B : ℝ} (T : ℕ)
    (hκ : 0 < κ) (hEred_c₁ : 0 < Ered_c₁) (hEred_C₁ : 0 < Ered_C₁)
    (hB : 0 < B)
    (hEred : ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ Real.exp (κ * (Real.log N) ^ ((1 : ℝ) / 4)) →
        (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
          Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N)) :
    EHUniformNumeratorInputs := by
  let smoothExp : ℝ := Classical.choose rankin_smoothRankinEnvelope_zNatScale_bound
  let smoothC : ℝ :=
    Classical.choose (Classical.choose_spec rankin_smoothRankinEnvelope_zNatScale_bound)
  have hsmooth_spec :
      0 < smoothExp ∧ smoothExp < 1 ∧ 0 < smoothC ∧
        ∀ N : ℕ, 3 ≤ N → smoothRankinEnvelope N ≤ smoothC * (N : ℝ) ^ smoothExp := by
    simpa [smoothExp, smoothC] using
      Classical.choose_spec
        (Classical.choose_spec rankin_smoothRankinEnvelope_zNatScale_bound)
  let eulerC : ℝ := Classical.choose eulerProductFactorAtNat_log_fourth_bound
  have heuler_spec :
      0 < eulerC ∧ ∀ N : ℕ, 3 ≤ N →
        eulerProductFactorAtNat N ≤ eulerC * (Real.log N) ^ (4 : ℕ) := by
    simpa [eulerC] using Classical.choose_spec eulerProductFactorAtNat_log_fourth_bound
  let cs : ℝ :=
    Classical.choose
      (poly_absorb hsmooth_spec.1 hsmooth_spec.2.1 hsmooth_spec.2.2.1)
  have hpoly_cs :
      cs > (0 : ℝ) ∧ ∃ C > (0 : ℝ),
        ∀ N : ℕ, 3 ≤ N →
          smoothC * (N : ℝ) ^ smoothExp ≤ C * ((N : ℝ) * saving cs N) :=
    Classical.choose_spec
      (poly_absorb hsmooth_spec.1 hsmooth_spec.2.1 hsmooth_spec.2.2.1)
  let Cs : ℝ := Classical.choose hpoly_cs.2
  have hpoly_Cs :
      Cs > (0 : ℝ) ∧
        ∀ N : ℕ, 3 ≤ N →
          smoothC * (N : ℝ) ^ smoothExp ≤ Cs * ((N : ℝ) * saving cs N) :=
    Classical.choose_spec hpoly_cs.2
  let ce : ℝ :=
    Classical.choose (log_pow_four_absorb hEred_c₁ heuler_spec.1 hEred_C₁)
  have hlog_ce :
      ce > (0 : ℝ) ∧ ∃ C > (0 : ℝ),
        ∀ N : ℕ, 3 ≤ N →
          eulerC * (Real.log N) ^ (4 : ℕ) *
              (Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N))
            ≤ C * ((N : ℝ) * saving ce N) :=
    Classical.choose_spec (log_pow_four_absorb hEred_c₁ heuler_spec.1 hEred_C₁)
  let Ce : ℝ := Classical.choose hlog_ce.2
  have hlog_Ce :
      Ce > (0 : ℝ) ∧
        ∀ N : ℕ, 3 ≤ N →
          eulerC * (Real.log N) ^ (4 : ℕ) *
              (Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N))
            ≤ Ce * ((N : ℝ) * saving ce N) :=
    Classical.choose_spec hlog_ce.2
  have hcs : 0 < cs := hpoly_cs.1
  have hCs : 0 < Cs := hpoly_Cs.1
  have hce : 0 < ce := hlog_ce.1
  have hCe : 0 < Ce := hlog_Ce.1
  set c : ℝ := min cs ce with hcdef
  have hc : 0 < c := lt_min hcs hce
  have hC : 0 < Cs + Ce := add_pos hCs hCe
  have sav_mono : ∀ (c' : ℝ), c ≤ c' → ∀ N : ℕ, 3 ≤ N →
      (N : ℝ) * saving c' N ≤ (N : ℝ) * saving c N := by
    intro c' hcc' N hN
    have hLpos : 0 < Real.log N := log_pos_of_three_le hN
    have hL34 : 0 ≤ (Real.log N) ^ ((3 : ℝ) / 4) :=
      (Real.rpow_pos_of_pos hLpos _).le
    have hNpos : (0 : ℝ) ≤ N := by positivity
    apply mul_le_mul_of_nonneg_left _ hNpos
    unfold saving
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by linarith : -c' ≤ -c) hL34
  refine
    EHUniformNumeratorInputs.of_uniform_base_saving_bound
      (T := T) (κ := κ) (c := c) (C := Cs + Ce) (B := B)
      hκ hc hC hB ?_
  intro N m hN hTN hm hm_range
  have hlift :
      (fixedNumeratorExceptionalCount m N : ℝ) ≤
        smoothRankinEnvelope N +
          eulerProductFactorAtNat N *
            (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) :=
    fixedNumerator_lift_of_smooth_and_reduced_sum_bounds
      (m := m) (z := zNatScale N) (N := N)
      (smooth := smoothRankinEnvelope N) (euler := eulerProductFactorAtNat N)
      (Ered := (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ))
      (by
        simpa [smoothRankinEnvelope] using
          fixedNumeratorSmoothRangeCount_le_sum_smoothPsi m (zNatScale N) N)
      (fixedNumeratorReduced_sum_le_euler_mul_self
        (m := m) (z := zNatScale N) (N := N) (euler := eulerProductFactorAtNat N)
        (eulerProductFactorAtNat_one_le N))
  have hsmooth_le :
      smoothRankinEnvelope N ≤ Cs * ((N : ℝ) * saving c N) := by
    have h1 := hsmooth_spec.2.2.2 N hN
    have h2 := hpoly_Cs.2 N hN
    have h3 : (N : ℝ) * saving cs N ≤ (N : ℝ) * saving c N :=
      sav_mono cs (by rw [hcdef]; exact min_le_left _ _) N hN
    calc
      smoothRankinEnvelope N ≤ smoothC * (N : ℝ) ^ smoothExp := h1
      _ ≤ Cs * ((N : ℝ) * saving cs N) := h2
      _ ≤ Cs * ((N : ℝ) * saving c N) :=
        mul_le_mul_of_nonneg_left h3 hCs.le
  have hreduced_le :
      eulerProductFactorAtNat N *
          (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
        Ce * ((N : ℝ) * saving c N) := by
    have heu := heuler_spec.2 N hN
    have hEr := hEred N m hN hTN hm hm_range
    have hEr0 : 0 ≤ (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) := by
      positivity
    have hlog_nonneg : 0 ≤ Real.log N := (log_pos_of_three_le hN).le
    have step1 :
        eulerProductFactorAtNat N *
            (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ)
          ≤ (eulerC * (Real.log N) ^ (4 : ℕ)) *
              (Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N)) := by
      apply mul_le_mul heu hEr hEr0
      exact mul_nonneg heuler_spec.1.le (pow_nonneg hlog_nonneg 4)
    have step2 :
        (eulerC * (Real.log N) ^ (4 : ℕ)) *
            (Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N))
          ≤ Ce * ((N : ℝ) * saving ce N) := by
      simpa [mul_assoc] using hlog_Ce.2 N hN
    have step3 : (N : ℝ) * saving ce N ≤ (N : ℝ) * saving c N :=
      sav_mono ce (by rw [hcdef]; exact min_le_right _ _) N hN
    calc
      eulerProductFactorAtNat N *
          (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ)
          ≤ (eulerC * (Real.log N) ^ (4 : ℕ)) *
              (Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N)) := step1
      _ ≤ Ce * ((N : ℝ) * saving ce N) := step2
      _ ≤ Ce * ((N : ℝ) * saving c N) :=
        mul_le_mul_of_nonneg_left step3 hCe.le
  calc
    (fixedNumeratorExceptionalCount m N : ℝ)
        ≤ smoothRankinEnvelope N +
            eulerProductFactorAtNat N *
              (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) := hlift
    _ ≤ Cs * ((N : ℝ) * saving c N) + Ce * ((N : ℝ) * saving c N) :=
      add_le_add hsmooth_le hreduced_le
    _ = (Cs + Ce) * ((N : ℝ) * saving c N) := by ring
    _ = (Cs + Ce) * (N : ℝ) * saving c N := by ring

/-- EH numerator package directly from exact-direct paper optimization inputs.

The exact-direct fixed-`m` inputs give the reduced-count saving with no
numerator-size side condition, so they can feed the exponential EH range after
the Rankin/smoothPsi lift. -/
noncomputable def EHUniformNumeratorInputs.of_uniform_paper_suen_analytic_core_optimization_exact_direct_rankin_smoothPsi
    {ι : Type*} {κ c B : ℝ} (T : ℕ)
    (hκ : 0 < κ) (hc : 0 < c) (hB : 0 < B)
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationExactDirectInputs m ι)
    (hc_exact : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_exact : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T) :
    EHUniformNumeratorInputs :=
  EHUniformNumeratorInputs.of_rankin_smoothPsi_exact_reduced_sum_count
    (T := T) (κ := κ) (Ered_c₁ := c) (Ered_C₁ := 1) (B := B)
    hκ hc zero_lt_one hB
    (by
      intro N m hN hTN hm _hm_range
      exact
        uniform_exact_reduced_sum_count_large_of_uniform_paper_suen_analytic_core_optimization_exact_direct
          (c := c) (T := T) H hc_exact hT_exact N m hN hTN hm)

/-- `thm:EH-uniform-m` directly from exact-direct paper optimization inputs. -/
theorem thm_EH_uniform_m_of_uniform_paper_suen_analytic_core_optimization_exact_direct_rankin_smoothPsi
    {ι : Type*} {κ c B : ℝ} (T : ℕ)
    (hκ : 0 < κ) (hc : 0 < c) (hB : 0 < B)
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationExactDirectInputs m ι)
    (hc_exact : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_exact : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T) :
    (∃ κ > (0 : ℝ), ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∃ B > (0 : ℝ),
      (∀ N m : ℕ, 3 ≤ N → 2 ≤ m →
        (m : ℝ) ≤ Real.exp (κ * (Real.log N) ^ ((1 : ℝ) / 4)) →
          (fixedNumeratorExceptionalCount m N : ℝ) ≤
            C * (N : ℝ) * uniformNumeratorSaving c B m N) ∧
      (∀ η : ℝ, 0 < η →
        ∃ cη > (0 : ℝ), ∃ Cη > (0 : ℝ), ∀ N m : ℕ, 3 ≤ N → 2 ≤ m →
          (m : ℝ) ≤ Real.exp (κ * (Real.log N) ^ ((1 : ℝ) / 4)) →
          uniformNumeratorDenominator B m ≤ (Real.log N) ^ ((3 : ℝ) / 4 - η) →
            (fixedNumeratorExceptionalCount m N : ℝ) ≤
              Cη * (N : ℝ) * logPowerSaving cη η N)) :=
  thm_EH_uniform_m
    (EHUniformNumeratorInputs.of_uniform_paper_suen_analytic_core_optimization_exact_direct_rankin_smoothPsi
      (T := T) (κ := κ) (c := c) (B := B)
      hκ hc hB H hc_exact hT_exact)

/-- Uniform exact reduced-count saving from exact concrete-alpha optimization
inputs, with no numerator-size side condition.

Compared with the exact-direct wrapper, the optimization scale is no longer a
caller-supplied field: it is the canonical `optimizationSmallAlpha Cp` scale
inside `FixedNumeratorPaperSuenAnalyticCoreOptimizationExactConcreteAlphaInputs`. -/
theorem uniform_exact_reduced_sum_count_large_of_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha
    {ι : Type*} {c : ℝ} {T : ℕ}
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationExactConcreteAlphaInputs m ι)
    (hc_exact : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_exact : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T) :
    ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
        1 * ((N : ℝ) * saving c N) :=
  uniform_exact_reduced_sum_count_large_of_uniform_paper_suen_analytic_core_optimization_exact_direct
    (c := c) (T := T) (fun m => (H m).toExactDirect)
    (by
      intro m hm
      simpa [FixedNumeratorPaperSuenAnalyticCoreOptimizationExactConcreteAlphaInputs.toExactDirect]
        using hc_exact m hm)
    (by
      intro m hm
      simpa [FixedNumeratorPaperSuenAnalyticCoreOptimizationExactConcreteAlphaInputs.toExactDirect]
        using hT_exact m hm)

/-- Uniform exact reduced-count saving directly from the canonical scalar-two-mu
fixed-`m` Suen data.

This exposes the upstream reduced-sum estimate itself, rather than only the
assembled numerator exceptional-set consequence.  The common large-range cutoff
is `max T Tdef`, because the Suen decomposition and the relaxed defect estimate
may become valid at different finite thresholds. -/
theorem uniform_exact_reduced_sum_count_large_of_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
    {κcls : Type*} [DecidableEq κcls]
    (T Tdef : ℕ) (Cp cμ η : ℝ)
    (cμ_pos : 0 < cμ)
    (eta_lt_one : η < 1)
    (classOfRed : ℕ → ℕ → ℕ → ℕ → κcls)
    (μ εb : ℕ → ℕ → ℝ)
    (δb Δb : ℕ → ℕ → (Σ _s : ℕ, κcls) → NNReal)
    (weights : ℕ → ℕ → (Σ _s : ℕ, κcls) → List {q : ℚ // 0 ≤ q})
    (R : ℕ → ℕ → (Σ _s : ℕ, κcls) → ℕ)
    (hweights_sum_le_two_mu : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        ((((weights m N b).map Subtype.val).sum : ℚ) : ℝ) ≤ 2 * μ m N)
    (mertens_Pz : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        Real.log (max (1 : ℝ)
          (((Finset.Icc 1 N).sigma (fun s =>
            fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
              (classOfRed m N s))).card : ℝ)) ≤
            2 * zScale
              (Real.exp (optimizationSmallAlpha Cp *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))))
    (level_budget : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        2 * (R m N b : ℝ) *
            (optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) +
            6 * μ m N
          ≤ Cp * ((optimizationSmallAlpha Cp) ^ 4 * Real.log (N : ℝ)))
    (hmass_logcube_lower : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ m N)
    (hdefect : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Tdef ≤ N →
      εb m N + Real.log 3 / μ m N ≤ η)
    (hsuen_tail : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        Inputs.suenTailConstant * (Δb m N b : ℝ) *
            Real.exp (2 * (δb m N b : ℝ))
          ≤ εb m N * μ m N)
    (hdecomp : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        (fixedNumeratorReducedExceptionalCount m (zNatScale N) (N / b.1) : ℝ)
          ≤
            ((N : ℝ) / max (1 : ℝ)
              (((Finset.Icc 1 N).sigma (fun s =>
                fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
                  (classOfRed m N s))).card : ℝ)) *
              (Inputs.suenProb (μ m N) (δb m N b : ℝ) (Δb m N b : ℝ) +
                (EscLeanChecks.elemSymmList
                  ((weights m N b).map Subtype.val) (2 * R m N b) : ℝ)) +
            ∑ r ∈ Finset.range (2 * R m N b + 1),
              (Real.exp (optimizationSmallAlpha Cp *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))) ^ r *
                (EscLeanChecks.elemSymmList
                  ((weights m N b).map Subtype.val) r : ℝ))
    (hF2R_tail_two_mu : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        (2 * μ m N) ^ (2 * R m N b) /
            (Nat.factorial (2 * R m N b) : ℝ)
          ≤ Real.exp (-3 * μ m N)) :
    ∀ N m : ℕ, 3 ≤ N → max T Tdef ≤ N → 2 ≤ m →
      (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
        1 * ((N : ℝ) * saving (((1 - η) * cμ) / 2) N) :=
  uniform_exact_reduced_sum_count_large_of_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha
    (c := ((1 - η) * cμ) / 2) (T := max T Tdef)
    (fun m =>
      FixedNumeratorPaperSuenAnalyticCoreOptimizationExactConcreteAlphaInputs.of_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_auto_constants_auto_mu
        m (classOfRed m) (μ m) (εb m) (δb m) (Δb m) (weights m) (R m)
        Cp cμ η (max T Tdef) cμ_pos eta_lt_one
        (by
          intro N hN hTN b hb
          exact hweights_sum_le_two_mu m N hN
            (le_trans (Nat.le_max_left T Tdef) hTN) b hb)
        (by
          intro N hN hTN b hb
          exact mertens_Pz m N hN
            (le_trans (Nat.le_max_left T Tdef) hTN) b hb)
        (by
          intro N hN hTN b hb
          exact level_budget m N hN
            (le_trans (Nat.le_max_left T Tdef) hTN) b hb)
        (by
          intro N hN hTN
          exact (mu_lower_saving_of_logCube_lower_nat cμ_pos
            (by
              intro N hN hTN
              exact hmass_logcube_lower m N hN
                (le_trans (Nat.le_max_left T Tdef) hTN))) N hN hTN)
        (by
          intro N hN hTN
          exact hdefect m N hN
            (le_trans (Nat.le_max_right T Tdef) hTN))
        (by
          intro N hN hTN b hb
          exact hsuen_tail m N hN
            (le_trans (Nat.le_max_left T Tdef) hTN) b hb)
        (by
          intro N hN hTN b hb
          exact hdecomp m N hN
            (le_trans (Nat.le_max_left T Tdef) hTN) b hb)
        (by
          intro N hN hTN b hb
          exact hF2R_tail_two_mu m N hN
            (le_trans (Nat.le_max_left T Tdef) hTN) b hb))
    (by
      intro m hm
      rfl)
    (by
      intro m hm
      rfl)

/-- Uniform exact reduced-count theorem from canonical fixed-numerator data when
the scalar two-mu top tail is discharged by the rank choice `24 * μ ≤ 2R`. -/
theorem uniform_exact_reduced_sum_count_large_of_sigma_canonical_nn_rat_weights_nn_defects_rank_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
    {κcls : Type*} [DecidableEq κcls]
    (T Tdef : ℕ) (Cp cμ η : ℝ)
    (cμ_pos : 0 < cμ)
    (eta_lt_one : η < 1)
    (classOfRed : ℕ → ℕ → ℕ → ℕ → κcls)
    (μ εb : ℕ → ℕ → ℝ)
    (δb Δb : ℕ → ℕ → (Σ _s : ℕ, κcls) → NNReal)
    (weights : ℕ → ℕ → (Σ _s : ℕ, κcls) → List {q : ℚ // 0 ≤ q})
    (R : ℕ → ℕ → (Σ _s : ℕ, κcls) → ℕ)
    (hweights_sum_le_two_mu : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        ((((weights m N b).map Subtype.val).sum : ℚ) : ℝ) ≤ 2 * μ m N)
    (mertens_Pz : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        Real.log (max (1 : ℝ)
          (((Finset.Icc 1 N).sigma (fun s =>
            fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
              (classOfRed m N s))).card : ℝ)) ≤
            2 * zScale
              (Real.exp (optimizationSmallAlpha Cp *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))))
    (level_budget : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        2 * (R m N b : ℝ) *
            (optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) +
            6 * μ m N
          ≤ Cp * ((optimizationSmallAlpha Cp) ^ 4 * Real.log (N : ℝ)))
    (hmass_logcube_lower : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ m N)
    (hdefect : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Tdef ≤ N →
      εb m N + Real.log 3 / μ m N ≤ η)
    (hsuen_tail : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        Inputs.suenTailConstant * (Δb m N b : ℝ) *
            Real.exp (2 * (δb m N b : ℝ))
          ≤ εb m N * μ m N)
    (hdecomp : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        (fixedNumeratorReducedExceptionalCount m (zNatScale N) (N / b.1) : ℝ)
          ≤
            ((N : ℝ) / max (1 : ℝ)
              (((Finset.Icc 1 N).sigma (fun s =>
                fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
                  (classOfRed m N s))).card : ℝ)) *
              (Inputs.suenProb (μ m N) (δb m N b : ℝ) (Δb m N b : ℝ) +
                (EscLeanChecks.elemSymmList
                  ((weights m N b).map Subtype.val) (2 * R m N b) : ℝ)) +
            ∑ r ∈ Finset.range (2 * R m N b + 1),
              (Real.exp (optimizationSmallAlpha Cp *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))) ^ r *
                (EscLeanChecks.elemSymmList
                  ((weights m N b).map Subtype.val) r : ℝ))
    (hrank_tail : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        24 * μ m N ≤ (2 * R m N b : ℝ)) :
    ∀ N m : ℕ, 3 ≤ N → max T Tdef ≤ N → 2 ≤ m →
      (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
        1 * ((N : ℝ) * saving (((1 - η) * cμ) / 2) N) :=
  uniform_exact_reduced_sum_count_large_of_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
    T Tdef Cp cμ η cμ_pos eta_lt_one classOfRed μ εb δb Δb weights R
    hweights_sum_le_two_mu mertens_Pz level_budget hmass_logcube_lower hdefect
    hsuen_tail hdecomp
    (by
      intro m N hN hTN b hb
      exact scalar_two_mu_factorial_tail_of_rank_ge
        ((mu_nonneg_of_logCube_lower_nat cμ_pos
          (fun N hN hTN => hmass_logcube_lower m N hN hTN)) N hN hTN)
        (hrank_tail m N hN hTN b hb))

/-- Uniform final assembly from exact concrete-alpha optimization inputs. -/
noncomputable def UniformNumeratorLargeRangeInputs.of_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha_rankin_smoothPsi
    {ι : Type*} {A c B : ℝ} {T : ℕ}
    (hc : 0 < c) (hB : 0 < B)
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationExactConcreteAlphaInputs m ι)
    (hc_exact : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_exact : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T) :
    UniformNumeratorLargeRangeInputs A :=
  UniformNumeratorLargeRangeInputs.of_uniform_paper_suen_analytic_core_optimization_exact_direct_rankin_smoothPsi
    (A := A) (c := c) (B := B) (T := T)
    hc hB (fun m => (H m).toExactDirect)
    (by
      intro m hm
      simpa [FixedNumeratorPaperSuenAnalyticCoreOptimizationExactConcreteAlphaInputs.toExactDirect]
        using hc_exact m hm)
    (by
      intro m hm
      simpa [FixedNumeratorPaperSuenAnalyticCoreOptimizationExactConcreteAlphaInputs.toExactDirect]
        using hT_exact m hm)

/-- `thm:uniform-m` directly from exact concrete-alpha optimization inputs. -/
theorem thm_uniform_m_of_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha_rankin_smoothPsi
    {ι : Type*}
    (T : ℝ → ℕ) (c B : ℝ → ℝ)
    (hc : ∀ A : ℝ, 0 < A → 0 < c A)
    (hB : ∀ A : ℝ, 0 < A → 0 < B A)
    (H : ∀ A : ℝ, 0 < A → ∀ m : ℕ,
      FixedNumeratorPaperSuenAnalyticCoreOptimizationExactConcreteAlphaInputs m ι)
    (hc_exact : ∀ A : ℝ, (hA : 0 < A) → ∀ m : ℕ, 2 ≤ m →
      (H A hA m).c = c A)
    (hT_exact : ∀ A : ℝ, (hA : 0 < A) → ∀ m : ℕ, 2 ≤ m →
      (H A hA m).T ≤ T A) :
    ∀ A : ℝ, 0 < A →
      ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∃ Bden > (0 : ℝ),
        ∀ N m : ℕ, 3 ≤ N → 2 ≤ m → (m : ℝ) ≤ (Real.log N) ^ A →
          (fixedNumeratorExceptionalCount m N : ℝ) ≤
            C * (N : ℝ) * uniformNumeratorSaving c Bden m N :=
  thm_uniform_m_of_uniform_paper_suen_analytic_core_optimization_exact_direct_rankin_smoothPsi
    T c B hc hB
    (fun A hA m => (H A hA m).toExactDirect)
    (by
      intro A hA m hm
      simpa [FixedNumeratorPaperSuenAnalyticCoreOptimizationExactConcreteAlphaInputs.toExactDirect]
        using hc_exact A hA m hm)
    (by
      intro A hA m hm
      simpa [FixedNumeratorPaperSuenAnalyticCoreOptimizationExactConcreteAlphaInputs.toExactDirect]
        using hT_exact A hA m hm)

/-- EH numerator package directly from exact concrete-alpha optimization inputs. -/
noncomputable def EHUniformNumeratorInputs.of_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha_rankin_smoothPsi
    {ι : Type*} {κ c B : ℝ} (T : ℕ)
    (hκ : 0 < κ) (hc : 0 < c) (hB : 0 < B)
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationExactConcreteAlphaInputs m ι)
    (hc_exact : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_exact : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T) :
    EHUniformNumeratorInputs :=
  EHUniformNumeratorInputs.of_uniform_paper_suen_analytic_core_optimization_exact_direct_rankin_smoothPsi
    (T := T) (κ := κ) (c := c) (B := B)
    hκ hc hB (fun m => (H m).toExactDirect)
    (by
      intro m hm
      simpa [FixedNumeratorPaperSuenAnalyticCoreOptimizationExactConcreteAlphaInputs.toExactDirect]
        using hc_exact m hm)
    (by
      intro m hm
      simpa [FixedNumeratorPaperSuenAnalyticCoreOptimizationExactConcreteAlphaInputs.toExactDirect]
        using hT_exact m hm)

/-- EH numerator package from the canonical scalar-two-mu fixed-`m` Suen data.

This is the uniform-level version of the exact concrete-alpha record constructor
in `Assembly`: instead of taking a prebuilt family of exact concrete-alpha
records, it constructs that family from the paper's canonical reduced classes,
nonnegative rational weights, nonnegative defects, direct finite-transfer
decomposition, and scalar two-mu top-tail estimate.

The relaxed defect cutoff is supplied uniformly in `m`; this is necessary for
the growing-numerator theorem, whose fixed-`m` inputs must share one large-range
cutoff. -/
noncomputable def EHUniformNumeratorInputs.of_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
    {κcls : Type*} [DecidableEq κcls] {κeh B : ℝ}
    (T Tdef : ℕ) (Cp cμ η : ℝ)
    (hκ : 0 < κeh) (hB : 0 < B)
    (cμ_pos : 0 < cμ)
    (eta_lt_one : η < 1)
    (classOfRed : ℕ → ℕ → ℕ → ℕ → κcls)
    (μ εb : ℕ → ℕ → ℝ)
    (δb Δb : ℕ → ℕ → (Σ _s : ℕ, κcls) → NNReal)
    (weights : ℕ → ℕ → (Σ _s : ℕ, κcls) → List {q : ℚ // 0 ≤ q})
    (R : ℕ → ℕ → (Σ _s : ℕ, κcls) → ℕ)
    (hweights_sum_le_two_mu : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        ((((weights m N b).map Subtype.val).sum : ℚ) : ℝ) ≤ 2 * μ m N)
    (mertens_Pz : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        Real.log (max (1 : ℝ)
          (((Finset.Icc 1 N).sigma (fun s =>
            fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
              (classOfRed m N s))).card : ℝ)) ≤
            2 * zScale
              (Real.exp (optimizationSmallAlpha Cp *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))))
    (level_budget : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        2 * (R m N b : ℝ) *
            (optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) +
            6 * μ m N
          ≤ Cp * ((optimizationSmallAlpha Cp) ^ 4 * Real.log (N : ℝ)))
    (hmass_logcube_lower : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ m N)
    (hdefect : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Tdef ≤ N →
      εb m N + Real.log 3 / μ m N ≤ η)
    (hsuen_tail : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        Inputs.suenTailConstant * (Δb m N b : ℝ) *
            Real.exp (2 * (δb m N b : ℝ))
          ≤ εb m N * μ m N)
    (hdecomp : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        (fixedNumeratorReducedExceptionalCount m (zNatScale N) (N / b.1) : ℝ)
          ≤
            ((N : ℝ) / max (1 : ℝ)
              (((Finset.Icc 1 N).sigma (fun s =>
                fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
                  (classOfRed m N s))).card : ℝ)) *
              (Inputs.suenProb (μ m N) (δb m N b : ℝ) (Δb m N b : ℝ) +
                (EscLeanChecks.elemSymmList
                  ((weights m N b).map Subtype.val) (2 * R m N b) : ℝ)) +
            ∑ r ∈ Finset.range (2 * R m N b + 1),
              (Real.exp (optimizationSmallAlpha Cp *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))) ^ r *
                (EscLeanChecks.elemSymmList
                  ((weights m N b).map Subtype.val) r : ℝ))
    (hF2R_tail_two_mu : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        (2 * μ m N) ^ (2 * R m N b) /
            (Nat.factorial (2 * R m N b) : ℝ)
          ≤ Real.exp (-3 * μ m N)) :
    EHUniformNumeratorInputs :=
  EHUniformNumeratorInputs.of_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha_rankin_smoothPsi
    (T := max T Tdef) (κ := κeh) (c := ((1 - η) * cμ) / 2) (B := B)
    hκ
    (by
      have hone_minus_eta_pos : 0 < 1 - η := by linarith
      exact div_pos (mul_pos hone_minus_eta_pos cμ_pos) (by norm_num))
    hB
    (fun m =>
      FixedNumeratorPaperSuenAnalyticCoreOptimizationExactConcreteAlphaInputs.of_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_auto_constants_auto_mu
        m (classOfRed m) (μ m) (εb m) (δb m) (Δb m) (weights m) (R m)
        Cp cμ η (max T Tdef) cμ_pos eta_lt_one
        (by
          intro N hN hTN b hb
          exact hweights_sum_le_two_mu m N hN
            (le_trans (Nat.le_max_left T Tdef) hTN) b hb)
        (by
          intro N hN hTN b hb
          exact mertens_Pz m N hN
            (le_trans (Nat.le_max_left T Tdef) hTN) b hb)
        (by
          intro N hN hTN b hb
          exact level_budget m N hN
            (le_trans (Nat.le_max_left T Tdef) hTN) b hb)
        (by
          intro N hN hTN
          exact (mu_lower_saving_of_logCube_lower_nat cμ_pos
            (by
              intro N hN hTN
              exact hmass_logcube_lower m N hN
                (le_trans (Nat.le_max_left T Tdef) hTN))) N hN hTN)
        (by
          intro N hN hTN
          exact hdefect m N hN
            (le_trans (Nat.le_max_right T Tdef) hTN))
        (by
          intro N hN hTN b hb
          exact hsuen_tail m N hN
            (le_trans (Nat.le_max_left T Tdef) hTN) b hb)
        (by
          intro N hN hTN b hb
          exact hdecomp m N hN
            (le_trans (Nat.le_max_left T Tdef) hTN) b hb)
        (by
          intro N hN hTN b hb
          exact hF2R_tail_two_mu m N hN
            (le_trans (Nat.le_max_left T Tdef) hTN) b hb))
    (by
      intro m hm
      rfl)
    (by
      intro m hm
      rfl)

/-- Uniform EH numerator input from canonical fixed-numerator data when the
scalar two-mu top tail is discharged by the rank choice `24 * μ ≤ 2R`. -/
noncomputable def EHUniformNumeratorInputs.of_sigma_canonical_nn_rat_weights_nn_defects_rank_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
    {κcls : Type*} [DecidableEq κcls] {κeh B : ℝ}
    (T Tdef : ℕ) (Cp cμ η : ℝ)
    (hκ : 0 < κeh) (hB : 0 < B)
    (cμ_pos : 0 < cμ)
    (eta_lt_one : η < 1)
    (classOfRed : ℕ → ℕ → ℕ → ℕ → κcls)
    (μ εb : ℕ → ℕ → ℝ)
    (δb Δb : ℕ → ℕ → (Σ _s : ℕ, κcls) → NNReal)
    (weights : ℕ → ℕ → (Σ _s : ℕ, κcls) → List {q : ℚ // 0 ≤ q})
    (R : ℕ → ℕ → (Σ _s : ℕ, κcls) → ℕ)
    (hweights_sum_le_two_mu : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        ((((weights m N b).map Subtype.val).sum : ℚ) : ℝ) ≤ 2 * μ m N)
    (mertens_Pz : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        Real.log (max (1 : ℝ)
          (((Finset.Icc 1 N).sigma (fun s =>
            fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
              (classOfRed m N s))).card : ℝ)) ≤
            2 * zScale
              (Real.exp (optimizationSmallAlpha Cp *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))))
    (level_budget : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        2 * (R m N b : ℝ) *
            (optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) +
            6 * μ m N
          ≤ Cp * ((optimizationSmallAlpha Cp) ^ 4 * Real.log (N : ℝ)))
    (hmass_logcube_lower : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ m N)
    (hdefect : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Tdef ≤ N →
      εb m N + Real.log 3 / μ m N ≤ η)
    (hsuen_tail : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        Inputs.suenTailConstant * (Δb m N b : ℝ) *
            Real.exp (2 * (δb m N b : ℝ))
          ≤ εb m N * μ m N)
    (hdecomp : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        (fixedNumeratorReducedExceptionalCount m (zNatScale N) (N / b.1) : ℝ)
          ≤
            ((N : ℝ) / max (1 : ℝ)
              (((Finset.Icc 1 N).sigma (fun s =>
                fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
                  (classOfRed m N s))).card : ℝ)) *
              (Inputs.suenProb (μ m N) (δb m N b : ℝ) (Δb m N b : ℝ) +
                (EscLeanChecks.elemSymmList
                  ((weights m N b).map Subtype.val) (2 * R m N b) : ℝ)) +
            ∑ r ∈ Finset.range (2 * R m N b + 1),
              (Real.exp (optimizationSmallAlpha Cp *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))) ^ r *
                (EscLeanChecks.elemSymmList
                  ((weights m N b).map Subtype.val) r : ℝ))
    (hrank_tail : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        24 * μ m N ≤ (2 * R m N b : ℝ)) :
    EHUniformNumeratorInputs :=
  EHUniformNumeratorInputs.of_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
    (κeh := κeh) (B := B) T Tdef Cp cμ η hκ hB cμ_pos eta_lt_one
    classOfRed μ εb δb Δb weights R hweights_sum_le_two_mu
    mertens_Pz level_budget hmass_logcube_lower hdefect hsuen_tail hdecomp
    (by
      intro m N hN hTN b hb
      exact scalar_two_mu_factorial_tail_of_rank_ge
        ((mu_nonneg_of_logCube_lower_nat cμ_pos
          (fun N hN hTN => hmass_logcube_lower m N hN hTN)) N hN hTN)
        (hrank_tail m N hN hTN b hb))

/-- Uniform final assembly for a fixed logarithmic numerator range from the
canonical scalar-two-mu fixed-`m` Suen data.

This is the fixed-logarithmic companion to
`EHUniformNumeratorInputs.of_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi`:
the raw canonical fixed-numerator data first gives the EH numerator package,
then the already-formalized growth comparison places any fixed logarithmic
range inside the EH range. -/
noncomputable def UniformNumeratorLargeRangeInputs.of_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
    {κcls : Type*} [DecidableEq κcls] {κeh B : ℝ}
    (A : ℝ) (hA : 0 < A)
    (T Tdef : ℕ) (Cp cμ η : ℝ)
    (hκ : 0 < κeh) (hB : 0 < B)
    (cμ_pos : 0 < cμ)
    (eta_lt_one : η < 1)
    (classOfRed : ℕ → ℕ → ℕ → ℕ → κcls)
    (μ εb : ℕ → ℕ → ℝ)
    (δb Δb : ℕ → ℕ → (Σ _s : ℕ, κcls) → NNReal)
    (weights : ℕ → ℕ → (Σ _s : ℕ, κcls) → List {q : ℚ // 0 ≤ q})
    (R : ℕ → ℕ → (Σ _s : ℕ, κcls) → ℕ)
    (hweights_sum_le_two_mu : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        ((((weights m N b).map Subtype.val).sum : ℚ) : ℝ) ≤ 2 * μ m N)
    (mertens_Pz : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        Real.log (max (1 : ℝ)
          (((Finset.Icc 1 N).sigma (fun s =>
            fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
              (classOfRed m N s))).card : ℝ)) ≤
            2 * zScale
              (Real.exp (optimizationSmallAlpha Cp *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))))
    (level_budget : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        2 * (R m N b : ℝ) *
            (optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) +
            6 * μ m N
          ≤ Cp * ((optimizationSmallAlpha Cp) ^ 4 * Real.log (N : ℝ)))
    (hmass_logcube_lower : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ m N)
    (hdefect : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Tdef ≤ N →
      εb m N + Real.log 3 / μ m N ≤ η)
    (hsuen_tail : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        Inputs.suenTailConstant * (Δb m N b : ℝ) *
            Real.exp (2 * (δb m N b : ℝ))
          ≤ εb m N * μ m N)
    (hdecomp : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        (fixedNumeratorReducedExceptionalCount m (zNatScale N) (N / b.1) : ℝ)
          ≤
            ((N : ℝ) / max (1 : ℝ)
              (((Finset.Icc 1 N).sigma (fun s =>
                fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
                  (classOfRed m N s))).card : ℝ)) *
              (Inputs.suenProb (μ m N) (δb m N b : ℝ) (Δb m N b : ℝ) +
                (EscLeanChecks.elemSymmList
                  ((weights m N b).map Subtype.val) (2 * R m N b) : ℝ)) +
            ∑ r ∈ Finset.range (2 * R m N b + 1),
              (Real.exp (optimizationSmallAlpha Cp *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))) ^ r *
                (EscLeanChecks.elemSymmList
                  ((weights m N b).map Subtype.val) r : ℝ))
    (hF2R_tail_two_mu : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        (2 * μ m N) ^ (2 * R m N b) /
            (Nat.factorial (2 * R m N b) : ℝ)
          ≤ Real.exp (-3 * μ m N)) :
    UniformNumeratorLargeRangeInputs A :=
  UniformNumeratorLargeRangeInputs.of_EHUniformNumeratorInputs
    (EHUniformNumeratorInputs.of_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
      (κeh := κeh) (B := B) T Tdef Cp cμ η hκ hB cμ_pos eta_lt_one
      classOfRed μ εb δb Δb weights R hweights_sum_le_two_mu
      mertens_Pz level_budget hmass_logcube_lower hdefect hsuen_tail
      hdecomp hF2R_tail_two_mu)
    A hA

/-- Uniform final assembly for a fixed logarithmic numerator range from
canonical fixed-numerator data when the scalar two-mu top tail is discharged by
the rank choice `24 * μ ≤ 2R`. -/
noncomputable def UniformNumeratorLargeRangeInputs.of_sigma_canonical_nn_rat_weights_nn_defects_rank_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
    {κcls : Type*} [DecidableEq κcls] {κeh B : ℝ}
    (A : ℝ) (hA : 0 < A)
    (T Tdef : ℕ) (Cp cμ η : ℝ)
    (hκ : 0 < κeh) (hB : 0 < B)
    (cμ_pos : 0 < cμ)
    (eta_lt_one : η < 1)
    (classOfRed : ℕ → ℕ → ℕ → ℕ → κcls)
    (μ εb : ℕ → ℕ → ℝ)
    (δb Δb : ℕ → ℕ → (Σ _s : ℕ, κcls) → NNReal)
    (weights : ℕ → ℕ → (Σ _s : ℕ, κcls) → List {q : ℚ // 0 ≤ q})
    (R : ℕ → ℕ → (Σ _s : ℕ, κcls) → ℕ)
    (hweights_sum_le_two_mu : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        ((((weights m N b).map Subtype.val).sum : ℚ) : ℝ) ≤ 2 * μ m N)
    (mertens_Pz : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        Real.log (max (1 : ℝ)
          (((Finset.Icc 1 N).sigma (fun s =>
            fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
              (classOfRed m N s))).card : ℝ)) ≤
            2 * zScale
              (Real.exp (optimizationSmallAlpha Cp *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))))
    (level_budget : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        2 * (R m N b : ℝ) *
            (optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) +
            6 * μ m N
          ≤ Cp * ((optimizationSmallAlpha Cp) ^ 4 * Real.log (N : ℝ)))
    (hmass_logcube_lower : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ m N)
    (hdefect : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Tdef ≤ N →
      εb m N + Real.log 3 / μ m N ≤ η)
    (hsuen_tail : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        Inputs.suenTailConstant * (Δb m N b : ℝ) *
            Real.exp (2 * (δb m N b : ℝ))
          ≤ εb m N * μ m N)
    (hdecomp : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        (fixedNumeratorReducedExceptionalCount m (zNatScale N) (N / b.1) : ℝ)
          ≤
            ((N : ℝ) / max (1 : ℝ)
              (((Finset.Icc 1 N).sigma (fun s =>
                fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
                  (classOfRed m N s))).card : ℝ)) *
              (Inputs.suenProb (μ m N) (δb m N b : ℝ) (Δb m N b : ℝ) +
                (EscLeanChecks.elemSymmList
                  ((weights m N b).map Subtype.val) (2 * R m N b) : ℝ)) +
            ∑ r ∈ Finset.range (2 * R m N b + 1),
              (Real.exp (optimizationSmallAlpha Cp *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))) ^ r *
                (EscLeanChecks.elemSymmList
                  ((weights m N b).map Subtype.val) r : ℝ))
    (hrank_tail : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        24 * μ m N ≤ (2 * R m N b : ℝ)) :
    UniformNumeratorLargeRangeInputs A :=
  UniformNumeratorLargeRangeInputs.of_EHUniformNumeratorInputs
    (EHUniformNumeratorInputs.of_sigma_canonical_nn_rat_weights_nn_defects_rank_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
      (κeh := κeh) (B := B) T Tdef Cp cμ η hκ hB cμ_pos eta_lt_one
      classOfRed μ εb δb Δb weights R hweights_sum_le_two_mu
      mertens_Pz level_budget hmass_logcube_lower hdefect hsuen_tail
      hdecomp hrank_tail)
    A hA

/-- `thm:uniform-m` from the canonical scalar-two-mu fixed-`m` Suen data.

This exposes the same raw fixed-numerator canonical data used by the EH route,
with no prebuilt exact concrete-alpha record family at the theorem boundary. -/
theorem thm_uniform_m_of_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
    {κcls : Type*} [DecidableEq κcls] {κeh B : ℝ}
    (T Tdef : ℕ) (Cp cμ η : ℝ)
    (hκ : 0 < κeh) (hB : 0 < B)
    (cμ_pos : 0 < cμ)
    (eta_lt_one : η < 1)
    (classOfRed : ℕ → ℕ → ℕ → ℕ → κcls)
    (μ εb : ℕ → ℕ → ℝ)
    (δb Δb : ℕ → ℕ → (Σ _s : ℕ, κcls) → NNReal)
    (weights : ℕ → ℕ → (Σ _s : ℕ, κcls) → List {q : ℚ // 0 ≤ q})
    (R : ℕ → ℕ → (Σ _s : ℕ, κcls) → ℕ)
    (hweights_sum_le_two_mu : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        ((((weights m N b).map Subtype.val).sum : ℚ) : ℝ) ≤ 2 * μ m N)
    (mertens_Pz : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        Real.log (max (1 : ℝ)
          (((Finset.Icc 1 N).sigma (fun s =>
            fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
              (classOfRed m N s))).card : ℝ)) ≤
            2 * zScale
              (Real.exp (optimizationSmallAlpha Cp *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))))
    (level_budget : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        2 * (R m N b : ℝ) *
            (optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) +
            6 * μ m N
          ≤ Cp * ((optimizationSmallAlpha Cp) ^ 4 * Real.log (N : ℝ)))
    (hmass_logcube_lower : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ m N)
    (hdefect : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Tdef ≤ N →
      εb m N + Real.log 3 / μ m N ≤ η)
    (hsuen_tail : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        Inputs.suenTailConstant * (Δb m N b : ℝ) *
            Real.exp (2 * (δb m N b : ℝ))
          ≤ εb m N * μ m N)
    (hdecomp : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        (fixedNumeratorReducedExceptionalCount m (zNatScale N) (N / b.1) : ℝ)
          ≤
            ((N : ℝ) / max (1 : ℝ)
              (((Finset.Icc 1 N).sigma (fun s =>
                fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
                  (classOfRed m N s))).card : ℝ)) *
              (Inputs.suenProb (μ m N) (δb m N b : ℝ) (Δb m N b : ℝ) +
                (EscLeanChecks.elemSymmList
                  ((weights m N b).map Subtype.val) (2 * R m N b) : ℝ)) +
            ∑ r ∈ Finset.range (2 * R m N b + 1),
              (Real.exp (optimizationSmallAlpha Cp *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))) ^ r *
                (EscLeanChecks.elemSymmList
                  ((weights m N b).map Subtype.val) r : ℝ))
    (hF2R_tail_two_mu : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        (2 * μ m N) ^ (2 * R m N b) /
            (Nat.factorial (2 * R m N b) : ℝ)
          ≤ Real.exp (-3 * μ m N)) :
    ∀ A : ℝ, 0 < A →
      ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∃ Bden > (0 : ℝ),
        ∀ N m : ℕ, 3 ≤ N → 2 ≤ m → (m : ℝ) ≤ (Real.log N) ^ A →
          (fixedNumeratorExceptionalCount m N : ℝ) ≤
            C * (N : ℝ) * uniformNumeratorSaving c Bden m N :=
  thm_uniform_m_of_EHUniformNumeratorInputs
    (EHUniformNumeratorInputs.of_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
      (κeh := κeh) (B := B) T Tdef Cp cμ η hκ hB cμ_pos eta_lt_one
      classOfRed μ εb δb Δb weights R hweights_sum_le_two_mu
      mertens_Pz level_budget hmass_logcube_lower hdefect hsuen_tail
      hdecomp hF2R_tail_two_mu)

/-- `thm:uniform-m` from canonical fixed-numerator data when the scalar two-mu
top tail is discharged by the rank choice `24 * μ ≤ 2R`. -/
theorem thm_uniform_m_of_sigma_canonical_nn_rat_weights_nn_defects_rank_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
    {κcls : Type*} [DecidableEq κcls] {κeh B : ℝ}
    (T Tdef : ℕ) (Cp cμ η : ℝ)
    (hκ : 0 < κeh) (hB : 0 < B)
    (cμ_pos : 0 < cμ)
    (eta_lt_one : η < 1)
    (classOfRed : ℕ → ℕ → ℕ → ℕ → κcls)
    (μ εb : ℕ → ℕ → ℝ)
    (δb Δb : ℕ → ℕ → (Σ _s : ℕ, κcls) → NNReal)
    (weights : ℕ → ℕ → (Σ _s : ℕ, κcls) → List {q : ℚ // 0 ≤ q})
    (R : ℕ → ℕ → (Σ _s : ℕ, κcls) → ℕ)
    (hweights_sum_le_two_mu : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        ((((weights m N b).map Subtype.val).sum : ℚ) : ℝ) ≤ 2 * μ m N)
    (mertens_Pz : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        Real.log (max (1 : ℝ)
          (((Finset.Icc 1 N).sigma (fun s =>
            fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
              (classOfRed m N s))).card : ℝ)) ≤
            2 * zScale
              (Real.exp (optimizationSmallAlpha Cp *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))))
    (level_budget : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        2 * (R m N b : ℝ) *
            (optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) +
            6 * μ m N
          ≤ Cp * ((optimizationSmallAlpha Cp) ^ 4 * Real.log (N : ℝ)))
    (hmass_logcube_lower : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ m N)
    (hdefect : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Tdef ≤ N →
      εb m N + Real.log 3 / μ m N ≤ η)
    (hsuen_tail : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        Inputs.suenTailConstant * (Δb m N b : ℝ) *
            Real.exp (2 * (δb m N b : ℝ))
          ≤ εb m N * μ m N)
    (hdecomp : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        (fixedNumeratorReducedExceptionalCount m (zNatScale N) (N / b.1) : ℝ)
          ≤
            ((N : ℝ) / max (1 : ℝ)
              (((Finset.Icc 1 N).sigma (fun s =>
                fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
                  (classOfRed m N s))).card : ℝ)) *
              (Inputs.suenProb (μ m N) (δb m N b : ℝ) (Δb m N b : ℝ) +
                (EscLeanChecks.elemSymmList
                  ((weights m N b).map Subtype.val) (2 * R m N b) : ℝ)) +
            ∑ r ∈ Finset.range (2 * R m N b + 1),
              (Real.exp (optimizationSmallAlpha Cp *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))) ^ r *
                (EscLeanChecks.elemSymmList
                  ((weights m N b).map Subtype.val) r : ℝ))
    (hrank_tail : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRed m N s)),
        24 * μ m N ≤ (2 * R m N b : ℝ)) :
    ∀ A : ℝ, 0 < A →
      ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∃ Bden > (0 : ℝ),
        ∀ N m : ℕ, 3 ≤ N → 2 ≤ m → (m : ℝ) ≤ (Real.log N) ^ A →
          (fixedNumeratorExceptionalCount m N : ℝ) ≤
            C * (N : ℝ) * uniformNumeratorSaving c Bden m N :=
  thm_uniform_m_of_EHUniformNumeratorInputs
    (EHUniformNumeratorInputs.of_sigma_canonical_nn_rat_weights_nn_defects_rank_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
      (κeh := κeh) (B := B) T Tdef Cp cμ η hκ hB cμ_pos eta_lt_one
      classOfRed μ εb δb Δb weights R hweights_sum_le_two_mu
      mertens_Pz level_budget hmass_logcube_lower hdefect hsuen_tail
      hdecomp hrank_tail)

/-- `thm:EH-uniform-m` directly from exact concrete-alpha optimization inputs. -/
theorem thm_EH_uniform_m_of_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha_rankin_smoothPsi
    {ι : Type*} {κ c B : ℝ} (T : ℕ)
    (hκ : 0 < κ) (hc : 0 < c) (hB : 0 < B)
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationExactConcreteAlphaInputs m ι)
    (hc_exact : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_exact : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T) :
    (∃ κ > (0 : ℝ), ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∃ B > (0 : ℝ),
      (∀ N m : ℕ, 3 ≤ N → 2 ≤ m →
        (m : ℝ) ≤ Real.exp (κ * (Real.log N) ^ ((1 : ℝ) / 4)) →
          (fixedNumeratorExceptionalCount m N : ℝ) ≤
            C * (N : ℝ) * uniformNumeratorSaving c B m N) ∧
      (∀ η : ℝ, 0 < η →
        ∃ cη > (0 : ℝ), ∃ Cη > (0 : ℝ), ∀ N m : ℕ, 3 ≤ N → 2 ≤ m →
          (m : ℝ) ≤ Real.exp (κ * (Real.log N) ^ ((1 : ℝ) / 4)) →
          uniformNumeratorDenominator B m ≤ (Real.log N) ^ ((3 : ℝ) / 4 - η) →
            (fixedNumeratorExceptionalCount m N : ℝ) ≤
              Cη * (N : ℝ) * logPowerSaving cη η N)) :=
  thm_EH_uniform_m
    (EHUniformNumeratorInputs.of_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha_rankin_smoothPsi
      (T := T) (κ := κ) (c := c) (B := B)
      hκ hc hB H hc_exact hT_exact)

end EscAnalytic
