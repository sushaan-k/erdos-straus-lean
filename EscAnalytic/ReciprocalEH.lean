import EscAnalytic.Assembly
import EscAnalytic.QuarticSuen
import EscAnalytic.UniformFixedNumerator

/-!
# Reciprocal Elliott--Halberstam interface

This file records the definitional equivalence between the paper-facing
`ReciprocalElliottHalberstamInput` in `Assembly` and the same-carrier
`weightedBVSum` proposition in `Inputs`.  It intentionally does not introduce a
new axiom: the theorem shape needed for `hyp:reciprocal-EH` is exactly the
same-carrier weighted reciprocal-prime distribution statement.
-/

namespace EscAnalytic

/-- The `Assembly` paper-facing reciprocal-EH input is exactly the same
same-carrier weighted-BV proposition tracked in `Inputs`. -/
theorem reciprocalElliottHalberstamInput_iff_inputs_sameCarrier :
    ReciprocalElliottHalberstamInput ↔
      Inputs.ReciprocalElliottHalberstamWeightedBVSameCarrier :=
  Iff.rfl

/-- The standard external weighted-BV/EH input has the exact same carrier as the
paper-facing reciprocal-EH hypothesis. -/
theorem reciprocalElliottHalberstamInput_iff_weightedBVExternalInput :
    ReciprocalElliottHalberstamInput ↔
      Inputs.ReciprocalElliottHalberstamWeightedBVExternalInput :=
  Iff.rfl

/-- Package the `Inputs` same-carrier reciprocal-EH theorem as the current
paper-facing `hyp:reciprocal-EH` input. -/
theorem reciprocalElliottHalberstamInput_of_inputs_sameCarrier
    (h : Inputs.ReciprocalElliottHalberstamWeightedBVSameCarrier) :
    ReciprocalElliottHalberstamInput :=
  h

/-- Unpack the current paper-facing `hyp:reciprocal-EH` input to the
same-carrier `Inputs.weightedBVSum` statement. -/
theorem inputs_sameCarrier_of_reciprocalElliottHalberstamInput
    (h : ReciprocalElliottHalberstamInput) :
    Inputs.ReciprocalElliottHalberstamWeightedBVSameCarrier :=
  h

/-- Bridge from the cited external weighted-BV/EH theorem shape to the
paper-facing `hyp:reciprocal-EH` carrier. -/
theorem reciprocalElliottHalberstamInput_of_weightedBVExternalInput
    (h : Inputs.ReciprocalElliottHalberstamWeightedBVExternalInput) :
    ReciprocalElliottHalberstamInput :=
  h

/-- The paper-facing reciprocal-EH carrier supplies the cited external
same-carrier weighted-BV/EH shape. -/
theorem weightedBVExternalInput_of_reciprocalElliottHalberstamInput
    (h : ReciprocalElliottHalberstamInput) :
    Inputs.ReciprocalElliottHalberstamWeightedBVExternalInput :=
  h

/- EH-only declarations below are conditional on the paper's explicit
reciprocal Elliott--Halberstam hypothesis, not on a global axiom. -/
variable [reciprocalEHFact : Fact Inputs.ReciprocalElliottHalberstamWeightedBVExternalInput]

/-- Paper-facing `hyp:reciprocal-EH` discharged by the named cited external
weighted-BV/EH input.  The proof deliberately goes through the standard external
input, not through the weaker Brun--Titchmarsh/BV fallback routes. -/
theorem reciprocalElliottHalberstamInput_of_standard_weightedBVExternalInput :
    ReciprocalElliottHalberstamInput :=
  reciprocalElliottHalberstamInput_of_weightedBVExternalInput
    reciprocalEHFact.out

/-- Build the paper EH package from the named cited reciprocal-EH input and an
eventual exponential-range numerator estimate.

This removes the caller-supplied `hEH : ReciprocalElliottHalberstamInput`
argument from the package constructor: the reciprocal-EH field is discharged by
the standard weighted-BV/EH input recorded in `EscAnalytic.Inputs`. -/
noncomputable def EHUniformNumeratorHypotheses.of_standard_reciprocalEH_eventual_bound
    {κ c C B : ℝ} (T : ℕ)
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C) (hB : 0 < B)
    (hlarge : ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ Real.exp (κ * (Real.log N) ^ ((1 : ℝ) / 4)) →
        (fixedNumeratorExceptionalCount m N : ℝ) ≤
          C * (N : ℝ) * uniformNumeratorSaving c B m N) :
    EHUniformNumeratorHypotheses :=
  EHUniformNumeratorHypotheses.of_reciprocalEH_eventual_bound
    reciprocalElliottHalberstamInput_of_standard_weightedBVExternalInput
    T hκ hc hC hB hlarge

/-- Build the paper EH package from the named cited reciprocal-EH input and an
exponential-range base-saving estimate.

The cited reciprocal-EH field, denominator-loss conversion, and finite initial
range are all discharged internally.  The remaining nonstandard input is the
uniform base fixed-numerator saving estimate in the displayed EH numerator
range. -/
noncomputable def EHUniformNumeratorHypotheses.of_standard_reciprocalEH_uniform_base_saving_bound
    {κ c C : ℝ} (T : ℕ)
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hlarge : ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ Real.exp (κ * (Real.log N) ^ ((1 : ℝ) / 4)) →
        (fixedNumeratorExceptionalCount m N : ℝ) ≤
          C * (N : ℝ) * saving c N) :
    EHUniformNumeratorHypotheses :=
  EHUniformNumeratorHypotheses.of_reciprocalEH_uniform_base_saving_bound
    reciprocalElliottHalberstamInput_of_standard_weightedBVExternalInput
    (B := 1) T hκ hc hC (by norm_num) hlarge

/-- Build the paper EH package from the named cited reciprocal-EH input and an
exact reduced-count estimate over the exponential numerator range.

This opens the uniform-saturation side one step further than
`of_standard_reciprocalEH_uniform_base_saving_bound`: the smooth envelope,
Euler loss, finite lift, denominator-loss conversion, and finite initial range
are all internal.  The remaining nonstandard input is the exact reduced
summatory saving for
`fixedNumeratorReducedSumCount m (zNatScale N) N` in the displayed EH range. -/
noncomputable def EHUniformNumeratorHypotheses.of_standard_reciprocalEH_rankin_smoothPsi_exact_reduced_sum_count
    {κ Ered_c₁ Ered_C₁ : ℝ} (T : ℕ)
    (hκ : 0 < κ) (hEred_c₁ : 0 < Ered_c₁) (hEred_C₁ : 0 < Ered_C₁)
    (hEred : ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ Real.exp (κ * (Real.log N) ^ ((1 : ℝ) / 4)) →
        (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
          Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N)) :
    EHUniformNumeratorHypotheses :=
  { reciprocal_EH := reciprocalElliottHalberstamInput_of_standard_weightedBVExternalInput
    assembled_bound :=
      EHUniformNumeratorInputs.of_rankin_smoothPsi_exact_reduced_sum_count
        (T := T) (κ := κ) (Ered_c₁ := Ered_c₁) (Ered_C₁ := Ered_C₁)
        (B := 1) hκ hEred_c₁ hEred_C₁ (by norm_num) hEred }

/-- Build the paper EH package directly from the standard cited reciprocal-EH
input and exact-direct fixed-numerator optimization inputs.

This removes the separate EH-range reduced-count hypothesis from
`of_standard_reciprocalEH_rankin_smoothPsi_exact_reduced_sum_count`: the
exact-direct fixed-`m` optimization records supply the reduced-count saving
uniformly over the exponential numerator range. -/
noncomputable def EHUniformNumeratorHypotheses.of_standard_reciprocalEH_uniform_paper_suen_analytic_core_optimization_exact_direct_rankin_smoothPsi
    {ι : Type*} {κ c B : ℝ} (T : ℕ)
    (hκ : 0 < κ) (hc : 0 < c) (hB : 0 < B)
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationExactDirectInputs m ι)
    (hc_exact : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_exact : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T) :
    EHUniformNumeratorHypotheses :=
  { reciprocal_EH := reciprocalElliottHalberstamInput_of_standard_weightedBVExternalInput
    assembled_bound :=
      EHUniformNumeratorInputs.of_uniform_paper_suen_analytic_core_optimization_exact_direct_rankin_smoothPsi
        (T := T) (κ := κ) (c := c) (B := B)
        hκ hc hB H hc_exact hT_exact }

/-- Build the paper EH package directly from the standard cited reciprocal-EH
input and exact concrete-alpha fixed-numerator optimization inputs.

This is the narrower version of
`of_standard_reciprocalEH_uniform_paper_suen_analytic_core_optimization_exact_direct_rankin_smoothPsi`:
the optimization scale is chosen internally as `optimizationSmallAlpha Cp`. -/
noncomputable def EHUniformNumeratorHypotheses.of_standard_reciprocalEH_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha_rankin_smoothPsi
    {ι : Type*} {κ c B : ℝ} (T : ℕ)
    (hκ : 0 < κ) (hc : 0 < c) (hB : 0 < B)
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationExactConcreteAlphaInputs m ι)
    (hc_exact : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_exact : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T) :
    EHUniformNumeratorHypotheses :=
  { reciprocal_EH := reciprocalElliottHalberstamInput_of_standard_weightedBVExternalInput
    assembled_bound :=
      EHUniformNumeratorInputs.of_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha_rankin_smoothPsi
        (T := T) (κ := κ) (c := c) (B := B)
        hκ hc hB H hc_exact hT_exact }

/-- Build the paper EH package from the standard cited reciprocal-EH input and
canonical scalar-two-mu fixed-numerator data.

This removes the prebuilt family
`FixedNumeratorPaperSuenAnalyticCoreOptimizationExactConcreteAlphaInputs m ι`
from the reciprocal-EH interface.  The remaining hypotheses are the canonical
class decomposition, nonnegative rational weights/defects, direct finite
transfer decomposition, scalar two-mu top-tail estimate, and one uniform defect
cutoff for all numerators. -/
noncomputable def EHUniformNumeratorHypotheses.of_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
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
    EHUniformNumeratorHypotheses :=
  { reciprocal_EH := reciprocalElliottHalberstamInput_of_standard_weightedBVExternalInput
    assembled_bound :=
      EHUniformNumeratorInputs.of_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
        (κeh := κeh) (B := B) T Tdef Cp cμ η hκ hB cμ_pos eta_lt_one
        classOfRed μ εb δb Δb weights R hweights_sum_le_two_mu mertens_Pz
        level_budget hmass_logcube_lower hdefect hsuen_tail hdecomp hF2R_tail_two_mu }

/-- Build the paper EH package from the standard cited reciprocal-EH input and
canonical fixed-numerator data when the scalar two-mu top tail is discharged by
the rank choice `24 * μ ≤ 2R`. -/
noncomputable def EHUniformNumeratorHypotheses.of_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_rank_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
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
    EHUniformNumeratorHypotheses :=
  { reciprocal_EH := reciprocalElliottHalberstamInput_of_standard_weightedBVExternalInput
    assembled_bound :=
      EHUniformNumeratorInputs.of_sigma_canonical_nn_rat_weights_nn_defects_rank_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
        (κeh := κeh) (B := B) T Tdef Cp cμ η hκ hB cμ_pos eta_lt_one
        classOfRed μ εb δb Δb weights R hweights_sum_le_two_mu mertens_Pz
        level_budget hmass_logcube_lower hdefect hsuen_tail hdecomp hrank_tail }

/-- Geometric/uniform endpoint with the reciprocal-EH hypothesis discharged by
the named cited weighted-BV/EH input.

The remaining exponential-range base-saving hypothesis is deliberately left as
an argument: it is fixed-numerator content, not part of the reciprocal-EH
external theorem. -/
noncomputable def geometric_uniform_paper_outputs_from_exact_reduced_sum_concrete_euler_mertens_canonical_smooth_canonical_quartic_logcube_mu_lower_relaxed_defect_auto_card_budget_standard_reciprocalEH_base_saving
    {κ : Type*} [DecidableEq κ]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (Ered_c₁ Ered_C₁ cμ : ℝ) (T : ℕ)
    (hc₁ : 0 < Ered_c₁) (hC₁ : 0 < Ered_C₁)
    (hcμ : 0 < cμ)
    (hEred : ∀ N : ℕ, 3 ≤ N →
      (reducedSumCountFor zNatScale N : ℝ) ≤
        Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N))
    (htransfer_local : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ s ∈ Finset.Icc 1 N,
        ∀ b ∈ reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s),
          (reducedExceptionalCount (zNatScale N) (N / s) : ℝ) ≤
            ((N : ℝ) / canonicalQuarticPz classOfRed N) *
              Real.exp (-(1 - (εb N + Real.log 3 / μ N)) * μ N))
    (hmass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N)
    (hεb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    {κeh ceh Ceh : ℝ} (Teh : ℕ)
    (hκeh : 0 < κeh) (hceh : 0 < ceh) (hCeh : 0 < Ceh)
    (hEH_base : ∀ N m : ℕ, 3 ≤ N → Teh ≤ N → 2 ≤ m →
      (m : ℝ) ≤ Real.exp (κeh * (Real.log N) ^ ((1 : ℝ) / 4)) →
        (fixedNumeratorExceptionalCount m N : ℝ) ≤
          Ceh * (N : ℝ) * saving ceh N) :=
  geometric_uniform_paper_outputs_from_exact_reduced_sum_concrete_euler_mertens_canonical_smooth_canonical_quartic_logcube_mu_lower_relaxed_defect_auto_card_budget_reciprocalEH_base_saving
    classOfRed μ εb Ered_c₁ Ered_C₁ cμ T hc₁ hC₁ hcμ hEred
    htransfer_local hmass_logcube_lower hεb_zero
    reciprocalElliottHalberstamInput_of_standard_weightedBVExternalInput
    (Beh := 1) Teh hκeh hceh hCeh (by norm_num) hEH_base

/-- Geometric/uniform endpoint with the reciprocal-EH hypothesis discharged by
the named cited weighted-BV/EH input and the EH-range base-saving estimate
opened to the exact fixed-numerator reduced-count carrier.

This is the explicit discharge below
`..._standard_reciprocalEH_base_saving`: the cited weighted-BV input supplies
only `ReciprocalElliottHalberstamInput`.  The remaining fixed-numerator content
is the exponential-range saving estimate for
`fixedNumeratorReducedSumCount m (zNatScale N) N`, from which the Rankin/smoothPsi
assembly constructs the EH numerator package. -/
noncomputable def geometric_uniform_paper_outputs_from_exact_reduced_sum_concrete_euler_mertens_canonical_smooth_canonical_quartic_logcube_mu_lower_relaxed_defect_auto_card_budget_standard_reciprocalEH_rankin_smoothPsi_exact_reduced_sum_count
    {κ : Type*} [DecidableEq κ]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (Ered_c₁ Ered_C₁ cμ : ℝ) (T : ℕ)
    (hc₁ : 0 < Ered_c₁) (hC₁ : 0 < Ered_C₁)
    (hcμ : 0 < cμ)
    (hEred : ∀ N : ℕ, 3 ≤ N →
      (reducedSumCountFor zNatScale N : ℝ) ≤
        Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N))
    (htransfer_local : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ s ∈ Finset.Icc 1 N,
        ∀ b ∈ reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s),
          (reducedExceptionalCount (zNatScale N) (N / s) : ℝ) ≤
            ((N : ℝ) / canonicalQuarticPz classOfRed N) *
              Real.exp (-(1 - (εb N + Real.log 3 / μ N)) * μ N))
    (hmass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N)
    (hεb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    {κeh EredEH_c₁ EredEH_C₁ : ℝ} (Teh : ℕ)
    (hκeh : 0 < κeh) (hEredEH_c₁ : 0 < EredEH_c₁)
    (hEredEH_C₁ : 0 < EredEH_C₁)
    (hEH_Ered : ∀ N m : ℕ, 3 ≤ N → Teh ≤ N → 2 ≤ m →
      (m : ℝ) ≤ Real.exp (κeh * (Real.log N) ^ ((1 : ℝ) / 4)) →
        (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
          EredEH_C₁ * ((N : ℝ) * saving EredEH_c₁ N)) :=
  geometric_uniform_paper_outputs_from_exact_reduced_sum_concrete_euler_mertens_canonical_smooth_canonical_quartic_logcube_mu_lower_relaxed_defect_auto_card_budget
    classOfRed μ εb Ered_c₁ Ered_C₁ cμ T hc₁ hC₁ hcμ hEred
    htransfer_local hmass_logcube_lower hεb_zero
    (EHUniformNumeratorHypotheses.of_standard_reciprocalEH_rankin_smoothPsi_exact_reduced_sum_count
      (κ := κeh) (Ered_c₁ := EredEH_c₁) (Ered_C₁ := EredEH_C₁)
      Teh hκeh hEredEH_c₁ hEredEH_C₁ hEH_Ered).toInputs

/-- Geometric/uniform endpoint with the standard reciprocal-EH input and the
EH-range fixed-numerator content supplied by exact-direct paper optimization
records.

This removes the separate exponential-range `hEH_Ered` hypothesis from the
previous wrapper.  The remaining geometric hypotheses are the global reduced
summatory estimate and the local transfer/mass inputs; the EH numerator package
is supplied by exact-direct fixed-`m` analytic-core records with uniform
constants. -/
noncomputable def geometric_uniform_paper_outputs_from_exact_reduced_sum_concrete_euler_mertens_canonical_smooth_canonical_quartic_logcube_mu_lower_relaxed_defect_auto_card_budget_standard_reciprocalEH_uniform_paper_suen_analytic_core_optimization_exact_direct_rankin_smoothPsi
    {κ ι : Type*} [DecidableEq κ]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (Ered_c₁ Ered_C₁ cμ : ℝ) (T : ℕ)
    (hc₁ : 0 < Ered_c₁) (hC₁ : 0 < Ered_C₁)
    (hcμ : 0 < cμ)
    (hEred : ∀ N : ℕ, 3 ≤ N →
      (reducedSumCountFor zNatScale N : ℝ) ≤
        Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N))
    (htransfer_local : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ s ∈ Finset.Icc 1 N,
        ∀ b ∈ reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s),
          (reducedExceptionalCount (zNatScale N) (N / s) : ℝ) ≤
            ((N : ℝ) / canonicalQuarticPz classOfRed N) *
              Real.exp (-(1 - (εb N + Real.log 3 / μ N)) * μ N))
    (hmass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N)
    (hεb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    {κeh ceh Beh : ℝ} (Teh : ℕ)
    (hκeh : 0 < κeh) (hceh : 0 < ceh) (hBeh : 0 < Beh)
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationExactDirectInputs m ι)
    (hc_exact : ∀ m : ℕ, 2 ≤ m → (H m).c = ceh)
    (hT_exact : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ Teh) :=
  geometric_uniform_paper_outputs_from_exact_reduced_sum_concrete_euler_mertens_canonical_smooth_canonical_quartic_logcube_mu_lower_relaxed_defect_auto_card_budget
    classOfRed μ εb Ered_c₁ Ered_C₁ cμ T hc₁ hC₁ hcμ hEred
    htransfer_local hmass_logcube_lower hεb_zero
    (EHUniformNumeratorHypotheses.of_standard_reciprocalEH_uniform_paper_suen_analytic_core_optimization_exact_direct_rankin_smoothPsi
      (T := Teh) (κ := κeh) (c := ceh) (B := Beh)
      hκeh hceh hBeh H hc_exact hT_exact).toInputs

/-- Geometric/uniform endpoint with the standard reciprocal-EH input and the
EH-range fixed-numerator content supplied by exact concrete-alpha optimization
records. -/
noncomputable def geometric_uniform_paper_outputs_from_exact_reduced_sum_concrete_euler_mertens_canonical_smooth_canonical_quartic_logcube_mu_lower_relaxed_defect_auto_card_budget_standard_reciprocalEH_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha_rankin_smoothPsi
    {κ ι : Type*} [DecidableEq κ]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (Ered_c₁ Ered_C₁ cμ : ℝ) (T : ℕ)
    (hc₁ : 0 < Ered_c₁) (hC₁ : 0 < Ered_C₁)
    (hcμ : 0 < cμ)
    (hEred : ∀ N : ℕ, 3 ≤ N →
      (reducedSumCountFor zNatScale N : ℝ) ≤
        Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N))
    (htransfer_local : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ s ∈ Finset.Icc 1 N,
        ∀ b ∈ reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s),
          (reducedExceptionalCount (zNatScale N) (N / s) : ℝ) ≤
            ((N : ℝ) / canonicalQuarticPz classOfRed N) *
              Real.exp (-(1 - (εb N + Real.log 3 / μ N)) * μ N))
    (hmass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N)
    (hεb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    {κeh ceh Beh : ℝ} (Teh : ℕ)
    (hκeh : 0 < κeh) (hceh : 0 < ceh) (hBeh : 0 < Beh)
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationExactConcreteAlphaInputs m ι)
    (hc_exact : ∀ m : ℕ, 2 ≤ m → (H m).c = ceh)
    (hT_exact : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ Teh) :=
  geometric_uniform_paper_outputs_from_exact_reduced_sum_concrete_euler_mertens_canonical_smooth_canonical_quartic_logcube_mu_lower_relaxed_defect_auto_card_budget
    classOfRed μ εb Ered_c₁ Ered_C₁ cμ T hc₁ hC₁ hcμ hEred
    htransfer_local hmass_logcube_lower hεb_zero
    (EHUniformNumeratorHypotheses.of_standard_reciprocalEH_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha_rankin_smoothPsi
      (T := Teh) (κ := κeh) (c := ceh) (B := Beh)
      hκeh hceh hBeh H hc_exact hT_exact).toInputs

/-- Geometric/uniform endpoint with the standard reciprocal-EH input and the
EH-range fixed-numerator content supplied directly by canonical scalar-two-mu
fixed-numerator data.

This is the raw-data version of
`..._exact_concrete_alpha_rankin_smoothPsi`: the caller no longer supplies a
prebuilt family of exact concrete-alpha fixed-`m` records. -/
noncomputable def geometric_uniform_paper_outputs_from_exact_reduced_sum_concrete_euler_mertens_canonical_smooth_canonical_quartic_logcube_mu_lower_relaxed_defect_auto_card_budget_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
    {κ κfix : Type*} [DecidableEq κ] [DecidableEq κfix]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (Ered_c₁ Ered_C₁ cμ : ℝ) (T : ℕ)
    (hc₁ : 0 < Ered_c₁) (hC₁ : 0 < Ered_C₁)
    (hcμ : 0 < cμ)
    (hEred : ∀ N : ℕ, 3 ≤ N →
      (reducedSumCountFor zNatScale N : ℝ) ≤
        Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N))
    (htransfer_local : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ s ∈ Finset.Icc 1 N,
        ∀ b ∈ reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s),
          (reducedExceptionalCount (zNatScale N) (N / s) : ℝ) ≤
            ((N : ℝ) / canonicalQuarticPz classOfRed N) *
              Real.exp (-(1 - (εb N + Real.log 3 / μ N)) * μ N))
    (hmass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N)
    (hεb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    {κeh Beh : ℝ} (Teh Tdef : ℕ) (Cpfix cμfix ηfix : ℝ)
    (hκeh : 0 < κeh) (hBeh : 0 < Beh)
    (cμfix_pos : 0 < cμfix)
    (etafix_lt_one : ηfix < 1)
    (classOfRedFix : ℕ → ℕ → ℕ → ℕ → κfix)
    (μfix εbfix : ℕ → ℕ → ℝ)
    (δbfix Δbfix : ℕ → ℕ → (Σ _s : ℕ, κfix) → NNReal)
    (weightsFix : ℕ → ℕ → (Σ _s : ℕ, κfix) → List {q : ℚ // 0 ≤ q})
    (Rfix : ℕ → ℕ → (Σ _s : ℕ, κfix) → ℕ)
    (hweights_sum_le_two_mu_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        ((((weightsFix m N b).map Subtype.val).sum : ℚ) : ℝ) ≤ 2 * μfix m N)
    (mertens_Pz_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        Real.log (max (1 : ℝ)
          (((Finset.Icc 1 N).sigma (fun s =>
            fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
              (classOfRedFix m N s))).card : ℝ)) ≤
            2 * zScale
              (Real.exp (optimizationSmallAlpha Cpfix *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))))
    (level_budget_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        2 * (Rfix m N b : ℝ) *
            (optimizationSmallAlpha Cpfix * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) +
            6 * μfix m N
          ≤ Cpfix * ((optimizationSmallAlpha Cpfix) ^ 4 * Real.log (N : ℝ)))
    (hmass_logcube_lower_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      cμfix * logCube (N : ℝ) ≤ μfix m N)
    (hdefect_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Tdef ≤ N →
      εbfix m N + Real.log 3 / μfix m N ≤ ηfix)
    (hsuen_tail_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        Inputs.suenTailConstant * (Δbfix m N b : ℝ) *
            Real.exp (2 * (δbfix m N b : ℝ))
          ≤ εbfix m N * μfix m N)
    (hdecomp_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        (fixedNumeratorReducedExceptionalCount m (zNatScale N) (N / b.1) : ℝ)
          ≤
            ((N : ℝ) / max (1 : ℝ)
              (((Finset.Icc 1 N).sigma (fun s =>
                fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
                  (classOfRedFix m N s))).card : ℝ)) *
              (Inputs.suenProb (μfix m N) (δbfix m N b : ℝ) (Δbfix m N b : ℝ) +
                (EscLeanChecks.elemSymmList
                  ((weightsFix m N b).map Subtype.val) (2 * Rfix m N b) : ℝ)) +
            ∑ r ∈ Finset.range (2 * Rfix m N b + 1),
              (Real.exp (optimizationSmallAlpha Cpfix *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))) ^ r *
                (EscLeanChecks.elemSymmList
                  ((weightsFix m N b).map Subtype.val) r : ℝ))
    (hF2R_tail_two_mu_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        (2 * μfix m N) ^ (2 * Rfix m N b) /
            (Nat.factorial (2 * Rfix m N b) : ℝ)
          ≤ Real.exp (-3 * μfix m N)) :=
  geometric_uniform_paper_outputs_from_exact_reduced_sum_concrete_euler_mertens_canonical_smooth_canonical_quartic_logcube_mu_lower_relaxed_defect_auto_card_budget
    classOfRed μ εb Ered_c₁ Ered_C₁ cμ T hc₁ hC₁ hcμ hEred
    htransfer_local hmass_logcube_lower hεb_zero
    (EHUniformNumeratorHypotheses.of_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
      (κeh := κeh) (B := Beh) Teh Tdef Cpfix cμfix ηfix hκeh hBeh
      cμfix_pos etafix_lt_one classOfRedFix μfix εbfix δbfix Δbfix
      weightsFix Rfix hweights_sum_le_two_mu_fix mertens_Pz_fix
      level_budget_fix hmass_logcube_lower_fix hdefect_fix hsuen_tail_fix
      hdecomp_fix hF2R_tail_two_mu_fix).toInputs

/-- Exact-reduced geometric/uniform endpoint with the fixed-side scalar two-mu
tail discharged from the rank choice `24 * μ ≤ 2R`. -/
noncomputable def geometric_uniform_paper_outputs_from_exact_reduced_sum_concrete_euler_mertens_canonical_smooth_canonical_quartic_logcube_mu_lower_relaxed_defect_auto_card_budget_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_rank_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
    {κ κfix : Type*} [DecidableEq κ] [DecidableEq κfix]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (Ered_c₁ Ered_C₁ cμ : ℝ) (T : ℕ)
    (hc₁ : 0 < Ered_c₁) (hC₁ : 0 < Ered_C₁)
    (hcμ : 0 < cμ)
    (hEred : ∀ N : ℕ, 3 ≤ N →
      (reducedSumCountFor zNatScale N : ℝ) ≤
        Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N))
    (htransfer_local : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ s ∈ Finset.Icc 1 N,
        ∀ b ∈ reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s),
          (reducedExceptionalCount (zNatScale N) (N / s) : ℝ) ≤
            ((N : ℝ) / canonicalQuarticPz classOfRed N) *
              Real.exp (-(1 - (εb N + Real.log 3 / μ N)) * μ N))
    (hmass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N)
    (hεb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    {κeh Beh : ℝ} (Teh Tdef : ℕ) (Cpfix cμfix ηfix : ℝ)
    (hκeh : 0 < κeh) (hBeh : 0 < Beh)
    (cμfix_pos : 0 < cμfix)
    (etafix_lt_one : ηfix < 1)
    (classOfRedFix : ℕ → ℕ → ℕ → ℕ → κfix)
    (μfix εbfix : ℕ → ℕ → ℝ)
    (δbfix Δbfix : ℕ → ℕ → (Σ _s : ℕ, κfix) → NNReal)
    (weightsFix : ℕ → ℕ → (Σ _s : ℕ, κfix) → List {q : ℚ // 0 ≤ q})
    (Rfix : ℕ → ℕ → (Σ _s : ℕ, κfix) → ℕ)
    (hweights_sum_le_two_mu_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        ((((weightsFix m N b).map Subtype.val).sum : ℚ) : ℝ) ≤ 2 * μfix m N)
    (mertens_Pz_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        Real.log (max (1 : ℝ)
          (((Finset.Icc 1 N).sigma (fun s =>
            fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
              (classOfRedFix m N s))).card : ℝ)) ≤
            2 * zScale
              (Real.exp (optimizationSmallAlpha Cpfix *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))))
    (level_budget_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        2 * (Rfix m N b : ℝ) *
            (optimizationSmallAlpha Cpfix * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) +
            6 * μfix m N
          ≤ Cpfix * ((optimizationSmallAlpha Cpfix) ^ 4 * Real.log (N : ℝ)))
    (hmass_logcube_lower_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      cμfix * logCube (N : ℝ) ≤ μfix m N)
    (hdefect_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Tdef ≤ N →
      εbfix m N + Real.log 3 / μfix m N ≤ ηfix)
    (hsuen_tail_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        Inputs.suenTailConstant * (Δbfix m N b : ℝ) *
            Real.exp (2 * (δbfix m N b : ℝ))
          ≤ εbfix m N * μfix m N)
    (hdecomp_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        (fixedNumeratorReducedExceptionalCount m (zNatScale N) (N / b.1) : ℝ)
          ≤
            ((N : ℝ) / max (1 : ℝ)
              (((Finset.Icc 1 N).sigma (fun s =>
                fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
                  (classOfRedFix m N s))).card : ℝ)) *
              (Inputs.suenProb (μfix m N) (δbfix m N b : ℝ) (Δbfix m N b : ℝ) +
                (EscLeanChecks.elemSymmList
                  ((weightsFix m N b).map Subtype.val) (2 * Rfix m N b) : ℝ)) +
            ∑ r ∈ Finset.range (2 * Rfix m N b + 1),
              (Real.exp (optimizationSmallAlpha Cpfix *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))) ^ r *
                (EscLeanChecks.elemSymmList
                  ((weightsFix m N b).map Subtype.val) r : ℝ))
    (hrank_tail_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        24 * μfix m N ≤ (2 * Rfix m N b : ℝ)) :=
  geometric_uniform_paper_outputs_from_exact_reduced_sum_concrete_euler_mertens_canonical_smooth_canonical_quartic_logcube_mu_lower_relaxed_defect_auto_card_budget_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
    classOfRed μ εb Ered_c₁ Ered_C₁ cμ T hc₁ hC₁ hcμ hEred
    htransfer_local hmass_logcube_lower hεb_zero Teh Tdef Cpfix cμfix ηfix
    hκeh hBeh cμfix_pos etafix_lt_one classOfRedFix μfix εbfix
    δbfix Δbfix weightsFix Rfix hweights_sum_le_two_mu_fix
    mertens_Pz_fix level_budget_fix hmass_logcube_lower_fix hdefect_fix
    hsuen_tail_fix hdecomp_fix
    (by
      intro m N hN hTN b hb
      exact scalar_two_mu_factorial_tail_of_rank_ge
        ((mu_nonneg_of_logCube_lower_nat cμfix_pos
          (fun N hN hTN => hmass_logcube_lower_fix m N hN hTN)) N hN hTN)
        (hrank_tail_fix m N hN hTN b hb))

/-- Canonical Suen geometric/uniform endpoint with the standard reciprocal-EH
input and the EH numerator package supplied by exact concrete-alpha fixed-m
optimization records.

Unlike the exact-reduced capstone, this route does not expose a separate global
`reducedSumCountFor` saving hypothesis or a separate quartic local-transfer
hypothesis: both are already consequences of the canonical Suen finite-transfer
data in `Assembly`. -/
noncomputable def geometric_uniform_paper_outputs_of_suen_canonical_reduced_classes_rank_tail_canonical_quartic_relaxed_defect_standard_reciprocalEH_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha_rankin_smoothPsi_pos_xq
    {κ ι : Type*} [DecidableEq κ]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (δb Δb : ℕ → (Σ _s : ℕ, κ) → NNReal)
    (weights : ℕ → (Σ _s : ℕ, κ) → List {q : ℚ // 0 ≤ q})
    (Xq : ℕ → (Σ _s : ℕ, κ) → {q : ℚ // 1 ≤ q})
    (R : ℕ → (Σ _s : ℕ, κ) → ℕ)
    (Cp cμ : ℝ) (T : ℕ)
    (cμ_pos : 0 < cμ)
    (hεb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    (hweights_sum_le_two_mu : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (((weights N b).map Subtype.val).sum : ℝ) ≤ 2 * μ N)
    (hsuen_tail : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Inputs.suenTailConstant * (Δb N b : ℝ) *
            Real.exp (2 * (δb N b : ℝ)) ≤ εb N * μ N)
    (hdecomp : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (reducedExceptionalCount (zNatScale N) (N / b.1) : ℝ) ≤
          ((N : ℝ) /
            max (1 : ℝ)
              (((Finset.Icc 1 N).sigma (fun s =>
                reducedCanonicalClasses (zNatScale N) (N / s)
                  (classOfRed N s))).card : ℝ)) *
          (Inputs.suenProb (μ N) (δb N b : ℝ) (Δb N b : ℝ) +
            (EscLeanChecks.elemSymmList
              ((weights N b).map Subtype.val) (2 * R N b) : ℝ)) +
          ∑ r ∈ Finset.range (2 * R N b + 1),
            ((Xq N b : ℚ) : ℝ) ^ r *
              (EscLeanChecks.elemSymmList
                ((weights N b).map Subtype.val) r : ℝ))
    (hscale : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log ((Xq N b : ℚ) : ℝ) =
          optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))
    (hmertens : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log
          (max (1 : ℝ)
            (((Finset.Icc 1 N).sigma (fun s =>
              reducedCanonicalClasses (zNatScale N) (N / s)
                (classOfRed N s))).card : ℝ))
          ≤ 2 * zScale ((Xq N b : ℚ) : ℝ))
    (hbudget : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        2 * (R N b : ℝ) * Real.log ((Xq N b : ℚ) : ℝ) + 6 * μ N
          ≤ Cp * ((optimizationSmallAlpha Cp) ^ 4 * Real.log (N : ℝ)))
    (hmass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N)
    (hrank_tail : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        24 * μ N ≤ (2 * R N b : ℝ))
    {κeh ceh Beh : ℝ} (Teh : ℕ)
    (hκeh : 0 < κeh) (hceh : 0 < ceh) (hBeh : 0 < Beh)
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationExactConcreteAlphaInputs m ι)
    (hc_exact : ∀ m : ℕ, 2 ≤ m → (H m).c = ceh)
    (hT_exact : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ Teh) :=
  let hXq_cast :
      ∀ N : ℕ, 3 ≤ N → T ≤ N →
        ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
          reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
          1 ≤ (Xq N b : ℚ) := by
    intro N _hN _hTN b _hb
    exact (Xq N b).property
  let hF2R_tail_sum_mass :
      ∀ N : ℕ, 3 ≤ N → T ≤ N →
        ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
          reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
          ((((weights N b).map Subtype.val).sum : ℝ) ^ (2 * R N b)) /
              (Nat.factorial (2 * R N b) : ℝ)
            ≤ Real.exp (-3 * μ N) := by
    intro N hN hTN b hb
    exact rational_weight_self_tail_of_two_mu_tail
      ((weights N b).map Subtype.val) (R N b) (μ N)
      (by
        intro w hw
        rcases List.mem_map.1 hw with ⟨q, _hq, rfl⟩
        exact q.property)
      (hweights_sum_le_two_mu N hN hTN b hb)
      (scalar_two_mu_factorial_tail_of_rank_ge
        ((mu_nonneg_of_logCube_lower_nat cμ_pos hmass_logcube_lower)
          N hN hTN)
        (hrank_tail N hN hTN b hb))
  geometric_uniform_paper_outputs_of_suen_sigma_class_sum_mass_canonical_quartic_relaxed_defect
    (fun N s => reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s))
    classOfRed
    (fun N s _b => (reducedExceptionalCount (zNatScale N) (N / s) : ℝ))
    μ εb δb Δb weights (fun N b => (Xq N b : ℚ)) R Cp cμ T
    cμ_pos hεb_zero
    (by
      intro N _hN s _hs r hr
      exact reducedCanonicalClasses_mem (zNatScale N) (N / s)
        (classOfRed N s) r hr)
    (by
      intro N _hN s _hs b _hb
      exact reducedCanonicalClassFiber_le_total (zNatScale N) (N / s)
        (classOfRed N s) b)
    hweights_sum_le_two_mu hXq_cast hsuen_tail hdecomp hscale hmertens
    hbudget hF2R_tail_sum_mass hmass_logcube_lower
    (canonical_quartic_local_transfer_of_suen_elemSymm_sum_mass_standard_tail
      classOfRed μ εb δb Δb weights (fun N b => (Xq N b : ℚ)) R Cp cμ T
      cμ_pos hweights_sum_le_two_mu hXq_cast hsuen_tail hdecomp hscale
      hmertens hbudget hF2R_tail_sum_mass hmass_logcube_lower)
    (EHUniformNumeratorHypotheses.of_standard_reciprocalEH_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha_rankin_smoothPsi
      (T := Teh) (κ := κeh) (c := ceh) (B := Beh)
      hκeh hceh hBeh H hc_exact hT_exact).toInputs

/-- Canonical Suen geometric/uniform endpoint with the standard reciprocal-EH
input and the EH numerator side opened to canonical fixed-numerator raw data.

Compared with
`geometric_uniform_paper_outputs_of_suen_canonical_reduced_classes_rank_tail_canonical_quartic_relaxed_defect_standard_reciprocalEH_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha_rankin_smoothPsi_pos_xq`,
this removes the prebuilt fixed-`m` exact concrete-alpha record family from the
non-packet canonical-Suen interface. -/
noncomputable def geometric_uniform_paper_outputs_of_suen_canonical_reduced_classes_rank_tail_canonical_quartic_relaxed_defect_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi_pos_xq
    {κ κfix : Type*} [DecidableEq κ] [DecidableEq κfix]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (δb Δb : ℕ → (Σ _s : ℕ, κ) → NNReal)
    (weights : ℕ → (Σ _s : ℕ, κ) → List {q : ℚ // 0 ≤ q})
    (Xq : ℕ → (Σ _s : ℕ, κ) → {q : ℚ // 1 ≤ q})
    (R : ℕ → (Σ _s : ℕ, κ) → ℕ)
    (Cp cμ : ℝ) (T : ℕ)
    (cμ_pos : 0 < cμ)
    (hεb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    (hweights_sum_le_two_mu : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (((weights N b).map Subtype.val).sum : ℝ) ≤ 2 * μ N)
    (hsuen_tail : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Inputs.suenTailConstant * (Δb N b : ℝ) *
            Real.exp (2 * (δb N b : ℝ)) ≤ εb N * μ N)
    (hdecomp : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (reducedExceptionalCount (zNatScale N) (N / b.1) : ℝ) ≤
          ((N : ℝ) /
            max (1 : ℝ)
              (((Finset.Icc 1 N).sigma (fun s =>
                reducedCanonicalClasses (zNatScale N) (N / s)
                  (classOfRed N s))).card : ℝ)) *
          (Inputs.suenProb (μ N) (δb N b : ℝ) (Δb N b : ℝ) +
            (EscLeanChecks.elemSymmList
              ((weights N b).map Subtype.val) (2 * R N b) : ℝ)) +
          ∑ r ∈ Finset.range (2 * R N b + 1),
            ((Xq N b : ℚ) : ℝ) ^ r *
              (EscLeanChecks.elemSymmList
                ((weights N b).map Subtype.val) r : ℝ))
    (hscale : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log ((Xq N b : ℚ) : ℝ) =
          optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))
    (hmertens : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log
          (max (1 : ℝ)
            (((Finset.Icc 1 N).sigma (fun s =>
              reducedCanonicalClasses (zNatScale N) (N / s)
                (classOfRed N s))).card : ℝ))
          ≤ 2 * zScale ((Xq N b : ℚ) : ℝ))
    (hbudget : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        2 * (R N b : ℝ) * Real.log ((Xq N b : ℚ) : ℝ) + 6 * μ N
          ≤ Cp * ((optimizationSmallAlpha Cp) ^ 4 * Real.log (N : ℝ)))
    (hmass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N)
    (hrank_tail : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        24 * μ N ≤ (2 * R N b : ℝ))
    {κeh Beh : ℝ} (Teh Tdef : ℕ) (Cpfix cμfix ηfix : ℝ)
    (hκeh : 0 < κeh) (hBeh : 0 < Beh)
    (cμfix_pos : 0 < cμfix)
    (etafix_lt_one : ηfix < 1)
    (classOfRedFix : ℕ → ℕ → ℕ → ℕ → κfix)
    (μfix εbfix : ℕ → ℕ → ℝ)
    (δbfix Δbfix : ℕ → ℕ → (Σ _s : ℕ, κfix) → NNReal)
    (weightsFix : ℕ → ℕ → (Σ _s : ℕ, κfix) → List {q : ℚ // 0 ≤ q})
    (Rfix : ℕ → ℕ → (Σ _s : ℕ, κfix) → ℕ)
    (hweights_sum_le_two_mu_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        ((((weightsFix m N b).map Subtype.val).sum : ℚ) : ℝ) ≤ 2 * μfix m N)
    (mertens_Pz_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        Real.log (max (1 : ℝ)
          (((Finset.Icc 1 N).sigma (fun s =>
            fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
              (classOfRedFix m N s))).card : ℝ)) ≤
            2 * zScale
              (Real.exp (optimizationSmallAlpha Cpfix *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))))
    (level_budget_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        2 * (Rfix m N b : ℝ) *
            (optimizationSmallAlpha Cpfix * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) +
            6 * μfix m N
          ≤ Cpfix * ((optimizationSmallAlpha Cpfix) ^ 4 * Real.log (N : ℝ)))
    (hmass_logcube_lower_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      cμfix * logCube (N : ℝ) ≤ μfix m N)
    (hdefect_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Tdef ≤ N →
      εbfix m N + Real.log 3 / μfix m N ≤ ηfix)
    (hsuen_tail_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        Inputs.suenTailConstant * (Δbfix m N b : ℝ) *
            Real.exp (2 * (δbfix m N b : ℝ))
          ≤ εbfix m N * μfix m N)
    (hdecomp_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        (fixedNumeratorReducedExceptionalCount m (zNatScale N) (N / b.1) : ℝ)
          ≤
            ((N : ℝ) / max (1 : ℝ)
              (((Finset.Icc 1 N).sigma (fun s =>
                fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
                  (classOfRedFix m N s))).card : ℝ)) *
              (Inputs.suenProb (μfix m N) (δbfix m N b : ℝ) (Δbfix m N b : ℝ) +
                (EscLeanChecks.elemSymmList
                  ((weightsFix m N b).map Subtype.val) (2 * Rfix m N b) : ℝ)) +
            ∑ r ∈ Finset.range (2 * Rfix m N b + 1),
              (Real.exp (optimizationSmallAlpha Cpfix *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))) ^ r *
                (EscLeanChecks.elemSymmList
                  ((weightsFix m N b).map Subtype.val) r : ℝ))
    (hF2R_tail_two_mu_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        (2 * μfix m N) ^ (2 * Rfix m N b) /
            (Nat.factorial (2 * Rfix m N b) : ℝ)
          ≤ Real.exp (-3 * μfix m N)) :=
  let hXq_cast :
      ∀ N : ℕ, 3 ≤ N → T ≤ N →
        ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
          reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
          1 ≤ (Xq N b : ℚ) := by
    intro N _hN _hTN b _hb
    exact (Xq N b).property
  let hF2R_tail_sum_mass :
      ∀ N : ℕ, 3 ≤ N → T ≤ N →
        ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
          reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
          ((((weights N b).map Subtype.val).sum : ℝ) ^ (2 * R N b)) /
              (Nat.factorial (2 * R N b) : ℝ)
            ≤ Real.exp (-3 * μ N) := by
    intro N hN hTN b hb
    exact rational_weight_self_tail_of_two_mu_tail
      ((weights N b).map Subtype.val) (R N b) (μ N)
      (by
        intro w hw
        rcases List.mem_map.1 hw with ⟨q, _hq, rfl⟩
        exact q.property)
      (hweights_sum_le_two_mu N hN hTN b hb)
      (scalar_two_mu_factorial_tail_of_rank_ge
        ((mu_nonneg_of_logCube_lower_nat cμ_pos hmass_logcube_lower)
          N hN hTN)
        (hrank_tail N hN hTN b hb))
  geometric_uniform_paper_outputs_of_suen_sigma_class_sum_mass_canonical_quartic_relaxed_defect
    (fun N s => reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s))
    classOfRed
    (fun N s _b => (reducedExceptionalCount (zNatScale N) (N / s) : ℝ))
    μ εb δb Δb weights (fun N b => (Xq N b : ℚ)) R Cp cμ T
    cμ_pos hεb_zero
    (by
      intro N _hN s _hs r hr
      exact reducedCanonicalClasses_mem (zNatScale N) (N / s)
        (classOfRed N s) r hr)
    (by
      intro N _hN s _hs b _hb
      exact reducedCanonicalClassFiber_le_total (zNatScale N) (N / s)
        (classOfRed N s) b)
    hweights_sum_le_two_mu hXq_cast hsuen_tail hdecomp hscale hmertens
    hbudget hF2R_tail_sum_mass hmass_logcube_lower
    (canonical_quartic_local_transfer_of_suen_elemSymm_sum_mass_standard_tail
      classOfRed μ εb δb Δb weights (fun N b => (Xq N b : ℚ)) R Cp cμ T
      cμ_pos hweights_sum_le_two_mu hXq_cast hsuen_tail hdecomp hscale
      hmertens hbudget hF2R_tail_sum_mass hmass_logcube_lower)
    (EHUniformNumeratorHypotheses.of_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
      (κeh := κeh) (B := Beh) Teh Tdef Cpfix cμfix ηfix hκeh hBeh
      cμfix_pos etafix_lt_one classOfRedFix μfix εbfix δbfix Δbfix
      weightsFix Rfix hweights_sum_le_two_mu_fix mertens_Pz_fix
      level_budget_fix hmass_logcube_lower_fix hdefect_fix hsuen_tail_fix
      hdecomp_fix hF2R_tail_two_mu_fix).toInputs

/-- Non-packet canonical Suen reciprocal-EH capstone with the EH numerator
fixed-side scalar two-mu tail discharged from the rank choice `24 * μ ≤ 2R`. -/
noncomputable def geometric_uniform_paper_outputs_of_suen_canonical_reduced_classes_rank_tail_canonical_quartic_relaxed_defect_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_rank_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi_pos_xq
    {κ κfix : Type*} [DecidableEq κ] [DecidableEq κfix]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (δb Δb : ℕ → (Σ _s : ℕ, κ) → NNReal)
    (weights : ℕ → (Σ _s : ℕ, κ) → List {q : ℚ // 0 ≤ q})
    (Xq : ℕ → (Σ _s : ℕ, κ) → {q : ℚ // 1 ≤ q})
    (R : ℕ → (Σ _s : ℕ, κ) → ℕ)
    (Cp cμ : ℝ) (T : ℕ)
    (cμ_pos : 0 < cμ)
    (hεb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    (hweights_sum_le_two_mu : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (((weights N b).map Subtype.val).sum : ℝ) ≤ 2 * μ N)
    (hsuen_tail : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Inputs.suenTailConstant * (Δb N b : ℝ) *
            Real.exp (2 * (δb N b : ℝ)) ≤ εb N * μ N)
    (hdecomp : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (reducedExceptionalCount (zNatScale N) (N / b.1) : ℝ) ≤
          ((N : ℝ) /
            max (1 : ℝ)
              (((Finset.Icc 1 N).sigma (fun s =>
                reducedCanonicalClasses (zNatScale N) (N / s)
                  (classOfRed N s))).card : ℝ)) *
          (Inputs.suenProb (μ N) (δb N b : ℝ) (Δb N b : ℝ) +
            (EscLeanChecks.elemSymmList
              ((weights N b).map Subtype.val) (2 * R N b) : ℝ)) +
          ∑ r ∈ Finset.range (2 * R N b + 1),
            ((Xq N b : ℚ) : ℝ) ^ r *
              (EscLeanChecks.elemSymmList
                ((weights N b).map Subtype.val) r : ℝ))
    (hscale : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log ((Xq N b : ℚ) : ℝ) =
          optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))
    (hmertens : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log
          (max (1 : ℝ)
            (((Finset.Icc 1 N).sigma (fun s =>
              reducedCanonicalClasses (zNatScale N) (N / s)
                (classOfRed N s))).card : ℝ))
          ≤ 2 * zScale ((Xq N b : ℚ) : ℝ))
    (hbudget : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        2 * (R N b : ℝ) * Real.log ((Xq N b : ℚ) : ℝ) + 6 * μ N
          ≤ Cp * ((optimizationSmallAlpha Cp) ^ 4 * Real.log (N : ℝ)))
    (hmass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N)
    (hrank_tail : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        24 * μ N ≤ (2 * R N b : ℝ))
    {κeh Beh : ℝ} (Teh Tdef : ℕ) (Cpfix cμfix ηfix : ℝ)
    (hκeh : 0 < κeh) (hBeh : 0 < Beh)
    (cμfix_pos : 0 < cμfix)
    (etafix_lt_one : ηfix < 1)
    (classOfRedFix : ℕ → ℕ → ℕ → ℕ → κfix)
    (μfix εbfix : ℕ → ℕ → ℝ)
    (δbfix Δbfix : ℕ → ℕ → (Σ _s : ℕ, κfix) → NNReal)
    (weightsFix : ℕ → ℕ → (Σ _s : ℕ, κfix) → List {q : ℚ // 0 ≤ q})
    (Rfix : ℕ → ℕ → (Σ _s : ℕ, κfix) → ℕ)
    (hweights_sum_le_two_mu_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        ((((weightsFix m N b).map Subtype.val).sum : ℚ) : ℝ) ≤ 2 * μfix m N)
    (mertens_Pz_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        Real.log (max (1 : ℝ)
          (((Finset.Icc 1 N).sigma (fun s =>
            fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
              (classOfRedFix m N s))).card : ℝ)) ≤
            2 * zScale
              (Real.exp (optimizationSmallAlpha Cpfix *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))))
    (level_budget_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        2 * (Rfix m N b : ℝ) *
            (optimizationSmallAlpha Cpfix * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) +
            6 * μfix m N
          ≤ Cpfix * ((optimizationSmallAlpha Cpfix) ^ 4 * Real.log (N : ℝ)))
    (hmass_logcube_lower_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      cμfix * logCube (N : ℝ) ≤ μfix m N)
    (hdefect_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Tdef ≤ N →
      εbfix m N + Real.log 3 / μfix m N ≤ ηfix)
    (hsuen_tail_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        Inputs.suenTailConstant * (Δbfix m N b : ℝ) *
            Real.exp (2 * (δbfix m N b : ℝ))
          ≤ εbfix m N * μfix m N)
    (hdecomp_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        (fixedNumeratorReducedExceptionalCount m (zNatScale N) (N / b.1) : ℝ)
          ≤
            ((N : ℝ) / max (1 : ℝ)
              (((Finset.Icc 1 N).sigma (fun s =>
                fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
                  (classOfRedFix m N s))).card : ℝ)) *
              (Inputs.suenProb (μfix m N) (δbfix m N b : ℝ) (Δbfix m N b : ℝ) +
                (EscLeanChecks.elemSymmList
                  ((weightsFix m N b).map Subtype.val) (2 * Rfix m N b) : ℝ)) +
            ∑ r ∈ Finset.range (2 * Rfix m N b + 1),
              (Real.exp (optimizationSmallAlpha Cpfix *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))) ^ r *
                (EscLeanChecks.elemSymmList
                  ((weightsFix m N b).map Subtype.val) r : ℝ))
    (hrank_tail_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        24 * μfix m N ≤ (2 * Rfix m N b : ℝ)) :=
  geometric_uniform_paper_outputs_of_suen_canonical_reduced_classes_rank_tail_canonical_quartic_relaxed_defect_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi_pos_xq
    classOfRed μ εb δb Δb weights Xq R Cp cμ T cμ_pos hεb_zero
    hweights_sum_le_two_mu hsuen_tail hdecomp hscale hmertens hbudget
    hmass_logcube_lower hrank_tail Teh Tdef Cpfix cμfix ηfix hκeh hBeh
    cμfix_pos etafix_lt_one classOfRedFix μfix εbfix δbfix Δbfix
    weightsFix Rfix hweights_sum_le_two_mu_fix mertens_Pz_fix
    level_budget_fix hmass_logcube_lower_fix hdefect_fix hsuen_tail_fix
    hdecomp_fix
    (by
      intro m N hN hTN b hb
      exact scalar_two_mu_factorial_tail_of_rank_ge
        ((mu_nonneg_of_logCube_lower_nat cμfix_pos
          (fun N hN hTN => hmass_logcube_lower_fix m N hN hTN)) N hN hTN)
        (hrank_tail_fix m N hN hTN b hb))

/-- Packet-level version of the canonical Suen reciprocal-EH capstone.

This keeps the quartic side as the named canonical Suen packet already used by
the quartic bridge.  The only extra datum is the identification of the packet's
real scale with the rational scale needed by the reciprocal local construction. -/
noncomputable def geometric_uniform_paper_outputs_of_quarticCanonicalSuenPacket_rank_tail_standard_reciprocalEH_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha_rankin_smoothPsi_pos_xq
    {κ ι : Type*} [DecidableEq κ]
    (HQ : QuarticCanonicalSuenPacketInputs κ)
    (Xq : ℕ → (Σ _s : ℕ, κ) → {q : ℚ // 1 ≤ q})
    (hXq : ∀ N b, HQ.X N b = ((Xq N b : ℚ) : ℝ))
    {κeh ceh Beh : ℝ} (Teh : ℕ)
    (hκeh : 0 < κeh) (hceh : 0 < ceh) (hBeh : 0 < Beh)
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationExactConcreteAlphaInputs m ι)
    (hc_exact : ∀ m : ℕ, 2 ≤ m → (H m).c = ceh)
    (hT_exact : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ Teh) :=
  geometric_uniform_paper_outputs_of_suen_canonical_reduced_classes_rank_tail_canonical_quartic_relaxed_defect_standard_reciprocalEH_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha_rankin_smoothPsi_pos_xq
    HQ.classOfRed HQ.μ HQ.εb HQ.δb HQ.Δb HQ.weights Xq HQ.R
    HQ.Cp HQ.cμ HQ.T HQ.cμ_pos HQ.εb_zero HQ.weights_sum_le_two_mu
    HQ.suen_tail
    (by
      intro N hN hTN b hb
      simpa [hXq N b] using HQ.decomp N hN hTN b hb)
    (by
      intro N hN hTN b hb
      simpa [hXq N b] using HQ.scale N hN hTN b hb)
    (by
      intro N hN hTN b hb
      simpa [hXq N b] using HQ.mertens_budget N hN hTN b hb)
    (by
      intro N hN hTN b hb
      simpa [hXq N b] using HQ.level_budget N hN hTN b hb)
    HQ.mass_logcube_lower HQ.rank_tail Teh hκeh hceh hBeh H hc_exact hT_exact

/-- Packet-level canonical Suen reciprocal-EH capstone with the EH numerator
side opened to canonical fixed-numerator raw data. -/
noncomputable def geometric_uniform_paper_outputs_of_quarticCanonicalSuenPacket_rank_tail_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi_pos_xq
    {κ κfix : Type*} [DecidableEq κ] [DecidableEq κfix]
    (HQ : QuarticCanonicalSuenPacketInputs κ)
    (Xq : ℕ → (Σ _s : ℕ, κ) → {q : ℚ // 1 ≤ q})
    (hXq : ∀ N b, HQ.X N b = ((Xq N b : ℚ) : ℝ))
    {κeh Beh : ℝ} (Teh Tdef : ℕ) (Cpfix cμfix ηfix : ℝ)
    (hκeh : 0 < κeh) (hBeh : 0 < Beh)
    (cμfix_pos : 0 < cμfix)
    (etafix_lt_one : ηfix < 1)
    (classOfRedFix : ℕ → ℕ → ℕ → ℕ → κfix)
    (μfix εbfix : ℕ → ℕ → ℝ)
    (δbfix Δbfix : ℕ → ℕ → (Σ _s : ℕ, κfix) → NNReal)
    (weightsFix : ℕ → ℕ → (Σ _s : ℕ, κfix) → List {q : ℚ // 0 ≤ q})
    (Rfix : ℕ → ℕ → (Σ _s : ℕ, κfix) → ℕ)
    (hweights_sum_le_two_mu_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        ((((weightsFix m N b).map Subtype.val).sum : ℚ) : ℝ) ≤ 2 * μfix m N)
    (mertens_Pz_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        Real.log (max (1 : ℝ)
          (((Finset.Icc 1 N).sigma (fun s =>
            fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
              (classOfRedFix m N s))).card : ℝ)) ≤
            2 * zScale
              (Real.exp (optimizationSmallAlpha Cpfix *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))))
    (level_budget_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        2 * (Rfix m N b : ℝ) *
            (optimizationSmallAlpha Cpfix * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) +
            6 * μfix m N
          ≤ Cpfix * ((optimizationSmallAlpha Cpfix) ^ 4 * Real.log (N : ℝ)))
    (hmass_logcube_lower_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      cμfix * logCube (N : ℝ) ≤ μfix m N)
    (hdefect_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Tdef ≤ N →
      εbfix m N + Real.log 3 / μfix m N ≤ ηfix)
    (hsuen_tail_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        Inputs.suenTailConstant * (Δbfix m N b : ℝ) *
            Real.exp (2 * (δbfix m N b : ℝ))
          ≤ εbfix m N * μfix m N)
    (hdecomp_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        (fixedNumeratorReducedExceptionalCount m (zNatScale N) (N / b.1) : ℝ)
          ≤
            ((N : ℝ) / max (1 : ℝ)
              (((Finset.Icc 1 N).sigma (fun s =>
                fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
                  (classOfRedFix m N s))).card : ℝ)) *
              (Inputs.suenProb (μfix m N) (δbfix m N b : ℝ) (Δbfix m N b : ℝ) +
                (EscLeanChecks.elemSymmList
                  ((weightsFix m N b).map Subtype.val) (2 * Rfix m N b) : ℝ)) +
            ∑ r ∈ Finset.range (2 * Rfix m N b + 1),
              (Real.exp (optimizationSmallAlpha Cpfix *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))) ^ r *
                (EscLeanChecks.elemSymmList
                  ((weightsFix m N b).map Subtype.val) r : ℝ))
    (hF2R_tail_two_mu_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        (2 * μfix m N) ^ (2 * Rfix m N b) /
            (Nat.factorial (2 * Rfix m N b) : ℝ)
          ≤ Real.exp (-3 * μfix m N)) :=
  geometric_uniform_paper_outputs_of_suen_canonical_reduced_classes_rank_tail_canonical_quartic_relaxed_defect_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi_pos_xq
    HQ.classOfRed HQ.μ HQ.εb HQ.δb HQ.Δb HQ.weights Xq HQ.R
    HQ.Cp HQ.cμ HQ.T HQ.cμ_pos HQ.εb_zero HQ.weights_sum_le_two_mu
    HQ.suen_tail
    (by
      intro N hN hTN b hb
      simpa [hXq N b] using HQ.decomp N hN hTN b hb)
    (by
      intro N hN hTN b hb
      simpa [hXq N b] using HQ.scale N hN hTN b hb)
    (by
      intro N hN hTN b hb
      simpa [hXq N b] using HQ.mertens_budget N hN hTN b hb)
    (by
      intro N hN hTN b hb
      simpa [hXq N b] using HQ.level_budget N hN hTN b hb)
    HQ.mass_logcube_lower HQ.rank_tail Teh Tdef Cpfix cμfix ηfix
    hκeh hBeh cμfix_pos etafix_lt_one classOfRedFix μfix εbfix
    δbfix Δbfix weightsFix Rfix hweights_sum_le_two_mu_fix
    mertens_Pz_fix level_budget_fix hmass_logcube_lower_fix hdefect_fix
    hsuen_tail_fix hdecomp_fix hF2R_tail_two_mu_fix

/-- Packet-level canonical Suen reciprocal-EH capstone with the EH numerator
fixed-side scalar two-mu tail discharged from the rank choice `24 * μ ≤ 2R`. -/
noncomputable def geometric_uniform_paper_outputs_of_quarticCanonicalSuenPacket_rank_tail_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_rank_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi_pos_xq
    {κ κfix : Type*} [DecidableEq κ] [DecidableEq κfix]
    (HQ : QuarticCanonicalSuenPacketInputs κ)
    (Xq : ℕ → (Σ _s : ℕ, κ) → {q : ℚ // 1 ≤ q})
    (hXq : ∀ N b, HQ.X N b = ((Xq N b : ℚ) : ℝ))
    {κeh Beh : ℝ} (Teh Tdef : ℕ) (Cpfix cμfix ηfix : ℝ)
    (hκeh : 0 < κeh) (hBeh : 0 < Beh)
    (cμfix_pos : 0 < cμfix)
    (etafix_lt_one : ηfix < 1)
    (classOfRedFix : ℕ → ℕ → ℕ → ℕ → κfix)
    (μfix εbfix : ℕ → ℕ → ℝ)
    (δbfix Δbfix : ℕ → ℕ → (Σ _s : ℕ, κfix) → NNReal)
    (weightsFix : ℕ → ℕ → (Σ _s : ℕ, κfix) → List {q : ℚ // 0 ≤ q})
    (Rfix : ℕ → ℕ → (Σ _s : ℕ, κfix) → ℕ)
    (hweights_sum_le_two_mu_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        ((((weightsFix m N b).map Subtype.val).sum : ℚ) : ℝ) ≤ 2 * μfix m N)
    (mertens_Pz_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        Real.log (max (1 : ℝ)
          (((Finset.Icc 1 N).sigma (fun s =>
            fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
              (classOfRedFix m N s))).card : ℝ)) ≤
            2 * zScale
              (Real.exp (optimizationSmallAlpha Cpfix *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))))
    (level_budget_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        2 * (Rfix m N b : ℝ) *
            (optimizationSmallAlpha Cpfix * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) +
            6 * μfix m N
          ≤ Cpfix * ((optimizationSmallAlpha Cpfix) ^ 4 * Real.log (N : ℝ)))
    (hmass_logcube_lower_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      cμfix * logCube (N : ℝ) ≤ μfix m N)
    (hdefect_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Tdef ≤ N →
      εbfix m N + Real.log 3 / μfix m N ≤ ηfix)
    (hsuen_tail_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        Inputs.suenTailConstant * (Δbfix m N b : ℝ) *
            Real.exp (2 * (δbfix m N b : ℝ))
          ≤ εbfix m N * μfix m N)
    (hdecomp_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        (fixedNumeratorReducedExceptionalCount m (zNatScale N) (N / b.1) : ℝ)
          ≤
            ((N : ℝ) / max (1 : ℝ)
              (((Finset.Icc 1 N).sigma (fun s =>
                fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
                  (classOfRedFix m N s))).card : ℝ)) *
              (Inputs.suenProb (μfix m N) (δbfix m N b : ℝ) (Δbfix m N b : ℝ) +
                (EscLeanChecks.elemSymmList
                  ((weightsFix m N b).map Subtype.val) (2 * Rfix m N b) : ℝ)) +
            ∑ r ∈ Finset.range (2 * Rfix m N b + 1),
              (Real.exp (optimizationSmallAlpha Cpfix *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))) ^ r *
                (EscLeanChecks.elemSymmList
                  ((weightsFix m N b).map Subtype.val) r : ℝ))
    (hrank_tail_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        24 * μfix m N ≤ (2 * Rfix m N b : ℝ)) :=
  geometric_uniform_paper_outputs_of_suen_canonical_reduced_classes_rank_tail_canonical_quartic_relaxed_defect_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_rank_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi_pos_xq
    HQ.classOfRed HQ.μ HQ.εb HQ.δb HQ.Δb HQ.weights Xq HQ.R
    HQ.Cp HQ.cμ HQ.T HQ.cμ_pos HQ.εb_zero HQ.weights_sum_le_two_mu
    HQ.suen_tail
    (by
      intro N hN hTN b hb
      simpa [hXq N b] using HQ.decomp N hN hTN b hb)
    (by
      intro N hN hTN b hb
      simpa [hXq N b] using HQ.scale N hN hTN b hb)
    (by
      intro N hN hTN b hb
      simpa [hXq N b] using HQ.mertens_budget N hN hTN b hb)
    (by
      intro N hN hTN b hb
      simpa [hXq N b] using HQ.level_budget N hN hTN b hb)
    HQ.mass_logcube_lower HQ.rank_tail Teh Tdef Cpfix cμfix ηfix
    hκeh hBeh cμfix_pos etafix_lt_one classOfRedFix μfix εbfix
    δbfix Δbfix weightsFix Rfix hweights_sum_le_two_mu_fix
    mertens_Pz_fix level_budget_fix hmass_logcube_lower_fix hdefect_fix
    hsuen_tail_fix hdecomp_fix hrank_tail_fix

/-- Packet-level canonical Suen reciprocal-EH capstone using the scalar
`2 * μ` tail packet rather than the stronger pointwise rank-tail packet. -/
noncomputable def geometric_uniform_paper_outputs_of_quarticCanonicalSuenTwoMuPacket_standard_reciprocalEH_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha_rankin_smoothPsi_pos_xq
    {κ ι : Type*} [DecidableEq κ]
    (HQ : QuarticCanonicalSuenTwoMuPacketInputs κ)
    (Xq : ℕ → (Σ _s : ℕ, κ) → {q : ℚ // 1 ≤ q})
    (hXq : ∀ N b, HQ.X N b = ((Xq N b : ℚ) : ℝ))
    {κeh ceh Beh : ℝ} (Teh : ℕ)
    (hκeh : 0 < κeh) (hceh : 0 < ceh) (hBeh : 0 < Beh)
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationExactConcreteAlphaInputs m ι)
    (hc_exact : ∀ m : ℕ, 2 ≤ m → (H m).c = ceh)
    (hT_exact : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ Teh) :=
  let hXq_cast :
      ∀ N : ℕ, 3 ≤ N → HQ.T ≤ N →
        ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
          reducedCanonicalClasses (zNatScale N) (N / s) (HQ.classOfRed N s)),
          1 ≤ (Xq N b : ℚ) := by
    intro N _hN _hTN b _hb
    exact (Xq N b).property
  let hF2R_tail_sum_mass :
      ∀ N : ℕ, 3 ≤ N → HQ.T ≤ N →
        ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
          reducedCanonicalClasses (zNatScale N) (N / s) (HQ.classOfRed N s)),
          ((((HQ.weights N b).map Subtype.val).sum : ℝ) ^ (2 * HQ.R N b)) /
              (Nat.factorial (2 * HQ.R N b) : ℝ)
            ≤ Real.exp (-3 * HQ.μ N) := by
    intro N hN hTN b hb
    exact rational_weight_self_tail_of_two_mu_tail
      ((HQ.weights N b).map Subtype.val) (HQ.R N b) (HQ.μ N)
      (by
        intro w hw
        rcases List.mem_map.1 hw with ⟨q, _hq, rfl⟩
        exact q.property)
      (HQ.weights_sum_le_two_mu N hN hTN b hb)
      (HQ.two_mu_tail N hN hTN b hb)
  geometric_uniform_paper_outputs_of_suen_sigma_class_sum_mass_canonical_quartic_relaxed_defect
    (fun N s => reducedCanonicalClasses (zNatScale N) (N / s) (HQ.classOfRed N s))
    HQ.classOfRed
    (fun N s _b => (reducedExceptionalCount (zNatScale N) (N / s) : ℝ))
    HQ.μ HQ.εb HQ.δb HQ.Δb HQ.weights (fun N b => (Xq N b : ℚ)) HQ.R
    HQ.Cp HQ.cμ HQ.T HQ.cμ_pos HQ.εb_zero
    (by
      intro N _hN s _hs r hr
      exact reducedCanonicalClasses_mem (zNatScale N) (N / s)
        (HQ.classOfRed N s) r hr)
    (by
      intro N _hN s _hs b _hb
      exact reducedCanonicalClassFiber_le_total (zNatScale N) (N / s)
        (HQ.classOfRed N s) b)
    HQ.weights_sum_le_two_mu hXq_cast HQ.suen_tail
    (by
      intro N hN hTN b hb
      simpa [hXq N b] using HQ.decomp N hN hTN b hb)
    (by
      intro N hN hTN b hb
      simpa [hXq N b] using HQ.scale N hN hTN b hb)
    (by
      intro N hN hTN b hb
      simpa [hXq N b] using HQ.mertens_budget N hN hTN b hb)
    (by
      intro N hN hTN b hb
      simpa [hXq N b] using HQ.level_budget N hN hTN b hb)
    hF2R_tail_sum_mass HQ.mass_logcube_lower
    (canonical_quartic_local_transfer_of_suen_elemSymm_sum_mass_standard_tail
      HQ.classOfRed HQ.μ HQ.εb HQ.δb HQ.Δb HQ.weights
      (fun N b => (Xq N b : ℚ)) HQ.R HQ.Cp HQ.cμ HQ.T
      HQ.cμ_pos HQ.weights_sum_le_two_mu hXq_cast HQ.suen_tail
      (by
        intro N hN hTN b hb
        simpa [hXq N b] using HQ.decomp N hN hTN b hb)
      (by
        intro N hN hTN b hb
        simpa [hXq N b] using HQ.scale N hN hTN b hb)
      (by
        intro N hN hTN b hb
        simpa [hXq N b] using HQ.mertens_budget N hN hTN b hb)
      (by
        intro N hN hTN b hb
        simpa [hXq N b] using HQ.level_budget N hN hTN b hb)
      hF2R_tail_sum_mass HQ.mass_logcube_lower)
    (EHUniformNumeratorHypotheses.of_standard_reciprocalEH_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha_rankin_smoothPsi
      (T := Teh) (κ := κeh) (c := ceh) (B := Beh)
      hκeh hceh hBeh H hc_exact hT_exact).toInputs

/-- Packet-level scalar-two-mu canonical Suen capstone with the EH numerator
side opened to canonical fixed-numerator raw data.

Compared with
`geometric_uniform_paper_outputs_of_quarticCanonicalSuenTwoMuPacket_standard_reciprocalEH_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha_rankin_smoothPsi_pos_xq`,
this removes the prebuilt fixed-`m` exact concrete-alpha record family from the
packet interface. -/
noncomputable def geometric_uniform_paper_outputs_of_quarticCanonicalSuenTwoMuPacket_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi_pos_xq
    {κ κfix : Type*} [DecidableEq κ] [DecidableEq κfix]
    (HQ : QuarticCanonicalSuenTwoMuPacketInputs κ)
    (Xq : ℕ → (Σ _s : ℕ, κ) → {q : ℚ // 1 ≤ q})
    (hXq : ∀ N b, HQ.X N b = ((Xq N b : ℚ) : ℝ))
    {κeh Beh : ℝ} (Teh Tdef : ℕ) (Cpfix cμfix ηfix : ℝ)
    (hκeh : 0 < κeh) (hBeh : 0 < Beh)
    (cμfix_pos : 0 < cμfix)
    (etafix_lt_one : ηfix < 1)
    (classOfRedFix : ℕ → ℕ → ℕ → ℕ → κfix)
    (μfix εbfix : ℕ → ℕ → ℝ)
    (δbfix Δbfix : ℕ → ℕ → (Σ _s : ℕ, κfix) → NNReal)
    (weightsFix : ℕ → ℕ → (Σ _s : ℕ, κfix) → List {q : ℚ // 0 ≤ q})
    (Rfix : ℕ → ℕ → (Σ _s : ℕ, κfix) → ℕ)
    (hweights_sum_le_two_mu_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        ((((weightsFix m N b).map Subtype.val).sum : ℚ) : ℝ) ≤ 2 * μfix m N)
    (mertens_Pz_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        Real.log (max (1 : ℝ)
          (((Finset.Icc 1 N).sigma (fun s =>
            fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
              (classOfRedFix m N s))).card : ℝ)) ≤
            2 * zScale
              (Real.exp (optimizationSmallAlpha Cpfix *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))))
    (level_budget_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        2 * (Rfix m N b : ℝ) *
            (optimizationSmallAlpha Cpfix * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) +
            6 * μfix m N
          ≤ Cpfix * ((optimizationSmallAlpha Cpfix) ^ 4 * Real.log (N : ℝ)))
    (hmass_logcube_lower_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      cμfix * logCube (N : ℝ) ≤ μfix m N)
    (hdefect_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Tdef ≤ N →
      εbfix m N + Real.log 3 / μfix m N ≤ ηfix)
    (hsuen_tail_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        Inputs.suenTailConstant * (Δbfix m N b : ℝ) *
            Real.exp (2 * (δbfix m N b : ℝ))
          ≤ εbfix m N * μfix m N)
    (hdecomp_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        (fixedNumeratorReducedExceptionalCount m (zNatScale N) (N / b.1) : ℝ)
          ≤
            ((N : ℝ) / max (1 : ℝ)
              (((Finset.Icc 1 N).sigma (fun s =>
                fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
                  (classOfRedFix m N s))).card : ℝ)) *
              (Inputs.suenProb (μfix m N) (δbfix m N b : ℝ) (Δbfix m N b : ℝ) +
                (EscLeanChecks.elemSymmList
                  ((weightsFix m N b).map Subtype.val) (2 * Rfix m N b) : ℝ)) +
            ∑ r ∈ Finset.range (2 * Rfix m N b + 1),
              (Real.exp (optimizationSmallAlpha Cpfix *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))) ^ r *
                (EscLeanChecks.elemSymmList
                  ((weightsFix m N b).map Subtype.val) r : ℝ))
    (hF2R_tail_two_mu_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        (2 * μfix m N) ^ (2 * Rfix m N b) /
            (Nat.factorial (2 * Rfix m N b) : ℝ)
          ≤ Real.exp (-3 * μfix m N)) :=
  let hXq_cast :
      ∀ N : ℕ, 3 ≤ N → HQ.T ≤ N →
        ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
          reducedCanonicalClasses (zNatScale N) (N / s) (HQ.classOfRed N s)),
          1 ≤ (Xq N b : ℚ) := by
    intro N _hN _hTN b _hb
    exact (Xq N b).property
  let hF2R_tail_sum_mass :
      ∀ N : ℕ, 3 ≤ N → HQ.T ≤ N →
        ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
          reducedCanonicalClasses (zNatScale N) (N / s) (HQ.classOfRed N s)),
          ((((HQ.weights N b).map Subtype.val).sum : ℝ) ^ (2 * HQ.R N b)) /
              (Nat.factorial (2 * HQ.R N b) : ℝ)
            ≤ Real.exp (-3 * HQ.μ N) := by
    intro N hN hTN b hb
    exact rational_weight_self_tail_of_two_mu_tail
      ((HQ.weights N b).map Subtype.val) (HQ.R N b) (HQ.μ N)
      (by
        intro w hw
        rcases List.mem_map.1 hw with ⟨q, _hq, rfl⟩
        exact q.property)
      (HQ.weights_sum_le_two_mu N hN hTN b hb)
      (HQ.two_mu_tail N hN hTN b hb)
  geometric_uniform_paper_outputs_of_suen_sigma_class_sum_mass_canonical_quartic_relaxed_defect
    (fun N s => reducedCanonicalClasses (zNatScale N) (N / s) (HQ.classOfRed N s))
    HQ.classOfRed
    (fun N s _b => (reducedExceptionalCount (zNatScale N) (N / s) : ℝ))
    HQ.μ HQ.εb HQ.δb HQ.Δb HQ.weights (fun N b => (Xq N b : ℚ)) HQ.R
    HQ.Cp HQ.cμ HQ.T HQ.cμ_pos HQ.εb_zero
    (by
      intro N _hN s _hs r hr
      exact reducedCanonicalClasses_mem (zNatScale N) (N / s)
        (HQ.classOfRed N s) r hr)
    (by
      intro N _hN s _hs b _hb
      exact reducedCanonicalClassFiber_le_total (zNatScale N) (N / s)
        (HQ.classOfRed N s) b)
    HQ.weights_sum_le_two_mu hXq_cast HQ.suen_tail
    (by
      intro N hN hTN b hb
      simpa [hXq N b] using HQ.decomp N hN hTN b hb)
    (by
      intro N hN hTN b hb
      simpa [hXq N b] using HQ.scale N hN hTN b hb)
    (by
      intro N hN hTN b hb
      simpa [hXq N b] using HQ.mertens_budget N hN hTN b hb)
    (by
      intro N hN hTN b hb
      simpa [hXq N b] using HQ.level_budget N hN hTN b hb)
    hF2R_tail_sum_mass HQ.mass_logcube_lower
    (canonical_quartic_local_transfer_of_suen_elemSymm_sum_mass_standard_tail
      HQ.classOfRed HQ.μ HQ.εb HQ.δb HQ.Δb HQ.weights
      (fun N b => (Xq N b : ℚ)) HQ.R HQ.Cp HQ.cμ HQ.T
      HQ.cμ_pos HQ.weights_sum_le_two_mu hXq_cast HQ.suen_tail
      (by
        intro N hN hTN b hb
        simpa [hXq N b] using HQ.decomp N hN hTN b hb)
      (by
        intro N hN hTN b hb
        simpa [hXq N b] using HQ.scale N hN hTN b hb)
      (by
        intro N hN hTN b hb
        simpa [hXq N b] using HQ.mertens_budget N hN hTN b hb)
      (by
        intro N hN hTN b hb
        simpa [hXq N b] using HQ.level_budget N hN hTN b hb)
      hF2R_tail_sum_mass HQ.mass_logcube_lower)
    (EHUniformNumeratorHypotheses.of_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
      (κeh := κeh) (B := Beh) Teh Tdef Cpfix cμfix ηfix hκeh hBeh
      cμfix_pos etafix_lt_one classOfRedFix μfix εbfix δbfix Δbfix
      weightsFix Rfix hweights_sum_le_two_mu_fix mertens_Pz_fix
      level_budget_fix hmass_logcube_lower_fix hdefect_fix hsuen_tail_fix
      hdecomp_fix hF2R_tail_two_mu_fix).toInputs

/-- Packet-level scalar-two-mu canonical Suen capstone with the EH numerator
side opened to canonical fixed-numerator raw data, discharging the fixed-side
scalar two-mu top tail from the rank choice `24 * μ ≤ 2R`. -/
noncomputable def geometric_uniform_paper_outputs_of_quarticCanonicalSuenTwoMuPacket_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_rank_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi_pos_xq
    {κ κfix : Type*} [DecidableEq κ] [DecidableEq κfix]
    (HQ : QuarticCanonicalSuenTwoMuPacketInputs κ)
    (Xq : ℕ → (Σ _s : ℕ, κ) → {q : ℚ // 1 ≤ q})
    (hXq : ∀ N b, HQ.X N b = ((Xq N b : ℚ) : ℝ))
    {κeh Beh : ℝ} (Teh Tdef : ℕ) (Cpfix cμfix ηfix : ℝ)
    (hκeh : 0 < κeh) (hBeh : 0 < Beh)
    (cμfix_pos : 0 < cμfix)
    (etafix_lt_one : ηfix < 1)
    (classOfRedFix : ℕ → ℕ → ℕ → ℕ → κfix)
    (μfix εbfix : ℕ → ℕ → ℝ)
    (δbfix Δbfix : ℕ → ℕ → (Σ _s : ℕ, κfix) → NNReal)
    (weightsFix : ℕ → ℕ → (Σ _s : ℕ, κfix) → List {q : ℚ // 0 ≤ q})
    (Rfix : ℕ → ℕ → (Σ _s : ℕ, κfix) → ℕ)
    (hweights_sum_le_two_mu_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        ((((weightsFix m N b).map Subtype.val).sum : ℚ) : ℝ) ≤ 2 * μfix m N)
    (mertens_Pz_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        Real.log (max (1 : ℝ)
          (((Finset.Icc 1 N).sigma (fun s =>
            fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
              (classOfRedFix m N s))).card : ℝ)) ≤
            2 * zScale
              (Real.exp (optimizationSmallAlpha Cpfix *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))))
    (level_budget_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        2 * (Rfix m N b : ℝ) *
            (optimizationSmallAlpha Cpfix * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) +
            6 * μfix m N
          ≤ Cpfix * ((optimizationSmallAlpha Cpfix) ^ 4 * Real.log (N : ℝ)))
    (hmass_logcube_lower_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      cμfix * logCube (N : ℝ) ≤ μfix m N)
    (hdefect_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Tdef ≤ N →
      εbfix m N + Real.log 3 / μfix m N ≤ ηfix)
    (hsuen_tail_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        Inputs.suenTailConstant * (Δbfix m N b : ℝ) *
            Real.exp (2 * (δbfix m N b : ℝ))
          ≤ εbfix m N * μfix m N)
    (hdecomp_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        (fixedNumeratorReducedExceptionalCount m (zNatScale N) (N / b.1) : ℝ)
          ≤
            ((N : ℝ) / max (1 : ℝ)
              (((Finset.Icc 1 N).sigma (fun s =>
                fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
                  (classOfRedFix m N s))).card : ℝ)) *
              (Inputs.suenProb (μfix m N) (δbfix m N b : ℝ) (Δbfix m N b : ℝ) +
                (EscLeanChecks.elemSymmList
                  ((weightsFix m N b).map Subtype.val) (2 * Rfix m N b) : ℝ)) +
            ∑ r ∈ Finset.range (2 * Rfix m N b + 1),
              (Real.exp (optimizationSmallAlpha Cpfix *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))) ^ r *
                (EscLeanChecks.elemSymmList
                  ((weightsFix m N b).map Subtype.val) r : ℝ))
    (hrank_tail_fix : ∀ m : ℕ, ∀ N : ℕ, 3 ≤ N → Teh ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        fixedNumeratorReducedCanonicalClasses m (zNatScale N) (N / s)
          (classOfRedFix m N s)),
        24 * μfix m N ≤ (2 * Rfix m N b : ℝ)) :=
  geometric_uniform_paper_outputs_of_quarticCanonicalSuenTwoMuPacket_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi_pos_xq
    HQ Xq hXq Teh Tdef Cpfix cμfix ηfix hκeh hBeh cμfix_pos
    etafix_lt_one classOfRedFix μfix εbfix δbfix Δbfix weightsFix Rfix
    hweights_sum_le_two_mu_fix mertens_Pz_fix level_budget_fix
    hmass_logcube_lower_fix hdefect_fix hsuen_tail_fix hdecomp_fix
    (by
      intro m N hN hTN b hb
      exact scalar_two_mu_factorial_tail_of_rank_ge
        ((mu_nonneg_of_logCube_lower_nat cμfix_pos
          (fun N hN hTN => hmass_logcube_lower_fix m N hN hTN)) N hN hTN)
        (hrank_tail_fix m N hN hTN b hb))

/-- EH growing-numerator theorem from the standard cited reciprocal-EH input and
an eventual exponential-range numerator estimate. -/
theorem thm_EH_uniform_m_of_standard_reciprocalEH_and_eventual_bound
    {κ c C B : ℝ} (T : ℕ)
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C) (hB : 0 < B)
    (hlarge : ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ Real.exp (κ * (Real.log N) ^ ((1 : ℝ) / 4)) →
        (fixedNumeratorExceptionalCount m N : ℝ) ≤
          C * (N : ℝ) * uniformNumeratorSaving c B m N) :
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
  thm_EH_uniform_m_of_reciprocalEH_and_uniformSaturation
    (EHUniformNumeratorHypotheses.of_standard_reciprocalEH_eventual_bound
      T hκ hc hC hB hlarge)

/-- Fixed-logarithmic uniform theorem from the standard cited reciprocal-EH
input and an eventual exponential-range numerator estimate. -/
theorem thm_uniform_m_of_standard_reciprocalEH_and_eventual_bound
    {κ c C B : ℝ} (T : ℕ)
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C) (hB : 0 < B)
    (hlarge : ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ Real.exp (κ * (Real.log N) ^ ((1 : ℝ) / 4)) →
        (fixedNumeratorExceptionalCount m N : ℝ) ≤
          C * (N : ℝ) * uniformNumeratorSaving c B m N) :
    ∀ A : ℝ, 0 < A →
      ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∃ B > (0 : ℝ),
        ∀ N m : ℕ, 3 ≤ N → 2 ≤ m → (m : ℝ) ≤ (Real.log N) ^ A →
          (fixedNumeratorExceptionalCount m N : ℝ) ≤
            C * (N : ℝ) * uniformNumeratorSaving c B m N :=
  thm_uniform_m_of_reciprocalEH_and_uniformSaturation
    (EHUniformNumeratorHypotheses.of_standard_reciprocalEH_eventual_bound
      T hκ hc hC hB hlarge)

/-- EH growing-numerator theorem from the standard cited reciprocal-EH input and
an exponential-range base-saving estimate. -/
theorem thm_EH_uniform_m_of_standard_reciprocalEH_and_uniform_base_saving_bound
    {κ c C : ℝ} (T : ℕ)
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hlarge : ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ Real.exp (κ * (Real.log N) ^ ((1 : ℝ) / 4)) →
        (fixedNumeratorExceptionalCount m N : ℝ) ≤
          C * (N : ℝ) * saving c N) :
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
  thm_EH_uniform_m_of_reciprocalEH_and_uniformSaturation
    (EHUniformNumeratorHypotheses.of_standard_reciprocalEH_uniform_base_saving_bound
      T hκ hc hC hlarge)

/-- Fixed-logarithmic uniform theorem from the standard cited reciprocal-EH
input and an exponential-range base-saving estimate. -/
theorem thm_uniform_m_of_standard_reciprocalEH_and_uniform_base_saving_bound
    {κ c C : ℝ} (T : ℕ)
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hlarge : ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ Real.exp (κ * (Real.log N) ^ ((1 : ℝ) / 4)) →
        (fixedNumeratorExceptionalCount m N : ℝ) ≤
          C * (N : ℝ) * saving c N) :
    ∀ A : ℝ, 0 < A →
      ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∃ B > (0 : ℝ),
        ∀ N m : ℕ, 3 ≤ N → 2 ≤ m → (m : ℝ) ≤ (Real.log N) ^ A →
          (fixedNumeratorExceptionalCount m N : ℝ) ≤
            C * (N : ℝ) * uniformNumeratorSaving c B m N :=
  thm_uniform_m_of_reciprocalEH_and_uniformSaturation
    (EHUniformNumeratorHypotheses.of_standard_reciprocalEH_uniform_base_saving_bound
      T hκ hc hC hlarge)

/-- EH growing-numerator theorem from the standard cited reciprocal-EH input and
the exact reduced summatory estimate over the exponential numerator range. -/
theorem thm_EH_uniform_m_of_standard_reciprocalEH_and_rankin_smoothPsi_exact_reduced_sum_count
    {κ Ered_c₁ Ered_C₁ : ℝ} (T : ℕ)
    (hκ : 0 < κ) (hEred_c₁ : 0 < Ered_c₁) (hEred_C₁ : 0 < Ered_C₁)
    (hEred : ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ Real.exp (κ * (Real.log N) ^ ((1 : ℝ) / 4)) →
        (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
          Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N)) :
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
  thm_EH_uniform_m_of_reciprocalEH_and_uniformSaturation
    (EHUniformNumeratorHypotheses.of_standard_reciprocalEH_rankin_smoothPsi_exact_reduced_sum_count
      T hκ hEred_c₁ hEred_C₁ hEred)

/-- Fixed-logarithmic uniform theorem from the standard cited reciprocal-EH input
and the exact reduced summatory estimate over the exponential numerator range. -/
theorem thm_uniform_m_of_standard_reciprocalEH_and_rankin_smoothPsi_exact_reduced_sum_count
    {κ Ered_c₁ Ered_C₁ : ℝ} (T : ℕ)
    (hκ : 0 < κ) (hEred_c₁ : 0 < Ered_c₁) (hEred_C₁ : 0 < Ered_C₁)
    (hEred : ∀ N m : ℕ, 3 ≤ N → T ≤ N → 2 ≤ m →
      (m : ℝ) ≤ Real.exp (κ * (Real.log N) ^ ((1 : ℝ) / 4)) →
        (fixedNumeratorReducedSumCount m (zNatScale N) N : ℝ) ≤
          Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N)) :
    ∀ A : ℝ, 0 < A →
      ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∃ B > (0 : ℝ),
        ∀ N m : ℕ, 3 ≤ N → 2 ≤ m → (m : ℝ) ≤ (Real.log N) ^ A →
          (fixedNumeratorExceptionalCount m N : ℝ) ≤
            C * (N : ℝ) * uniformNumeratorSaving c B m N :=
  thm_uniform_m_of_reciprocalEH_and_uniformSaturation
    (EHUniformNumeratorHypotheses.of_standard_reciprocalEH_rankin_smoothPsi_exact_reduced_sum_count
      T hκ hEred_c₁ hEred_C₁ hEred)

/-- EH growing-numerator theorem from the standard cited reciprocal-EH input and
exact-direct fixed-numerator optimization inputs. -/
theorem thm_EH_uniform_m_of_standard_reciprocalEH_and_uniform_paper_suen_analytic_core_optimization_exact_direct_rankin_smoothPsi
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
  thm_EH_uniform_m_of_reciprocalEH_and_uniformSaturation
    (EHUniformNumeratorHypotheses.of_standard_reciprocalEH_uniform_paper_suen_analytic_core_optimization_exact_direct_rankin_smoothPsi
      (T := T) (κ := κ) (c := c) (B := B)
      hκ hc hB H hc_exact hT_exact)

/-- Fixed-logarithmic uniform theorem from the standard cited reciprocal-EH input
and exact-direct fixed-numerator optimization inputs. -/
theorem thm_uniform_m_of_standard_reciprocalEH_and_uniform_paper_suen_analytic_core_optimization_exact_direct_rankin_smoothPsi
    {ι : Type*} {κ c B : ℝ} (T : ℕ)
    (hκ : 0 < κ) (hc : 0 < c) (hB : 0 < B)
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationExactDirectInputs m ι)
    (hc_exact : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_exact : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T) :
    ∀ A : ℝ, 0 < A →
      ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∃ B > (0 : ℝ),
        ∀ N m : ℕ, 3 ≤ N → 2 ≤ m → (m : ℝ) ≤ (Real.log N) ^ A →
          (fixedNumeratorExceptionalCount m N : ℝ) ≤
            C * (N : ℝ) * uniformNumeratorSaving c B m N :=
  thm_uniform_m_of_reciprocalEH_and_uniformSaturation
    (EHUniformNumeratorHypotheses.of_standard_reciprocalEH_uniform_paper_suen_analytic_core_optimization_exact_direct_rankin_smoothPsi
      (T := T) (κ := κ) (c := c) (B := B)
      hκ hc hB H hc_exact hT_exact)

/-- EH growing-numerator theorem from the standard cited reciprocal-EH input and
exact concrete-alpha fixed-numerator optimization inputs. -/
theorem thm_EH_uniform_m_of_standard_reciprocalEH_and_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha_rankin_smoothPsi
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
  thm_EH_uniform_m_of_reciprocalEH_and_uniformSaturation
    (EHUniformNumeratorHypotheses.of_standard_reciprocalEH_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha_rankin_smoothPsi
      (T := T) (κ := κ) (c := c) (B := B)
      hκ hc hB H hc_exact hT_exact)

/-- Fixed-logarithmic uniform theorem from the standard cited reciprocal-EH input
and exact concrete-alpha fixed-numerator optimization inputs. -/
theorem thm_uniform_m_of_standard_reciprocalEH_and_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha_rankin_smoothPsi
    {ι : Type*} {κ c B : ℝ} (T : ℕ)
    (hκ : 0 < κ) (hc : 0 < c) (hB : 0 < B)
    (H : ∀ m : ℕ, FixedNumeratorPaperSuenAnalyticCoreOptimizationExactConcreteAlphaInputs m ι)
    (hc_exact : ∀ m : ℕ, 2 ≤ m → (H m).c = c)
    (hT_exact : ∀ m : ℕ, 2 ≤ m → (H m).T ≤ T) :
    ∀ A : ℝ, 0 < A →
      ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∃ B > (0 : ℝ),
        ∀ N m : ℕ, 3 ≤ N → 2 ≤ m → (m : ℝ) ≤ (Real.log N) ^ A →
          (fixedNumeratorExceptionalCount m N : ℝ) ≤
            C * (N : ℝ) * uniformNumeratorSaving c B m N :=
  thm_uniform_m_of_reciprocalEH_and_uniformSaturation
    (EHUniformNumeratorHypotheses.of_standard_reciprocalEH_uniform_paper_suen_analytic_core_optimization_exact_concrete_alpha_rankin_smoothPsi
      (T := T) (κ := κ) (c := c) (B := B)
      hκ hc hB H hc_exact hT_exact)

/-- EH growing-numerator theorem from the standard cited reciprocal-EH input and
canonical scalar-two-mu fixed-numerator data. -/
theorem thm_EH_uniform_m_of_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
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
  thm_EH_uniform_m_of_reciprocalEH_and_uniformSaturation
    (EHUniformNumeratorHypotheses.of_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
      (κeh := κeh) (B := B) T Tdef Cp cμ η hκ hB cμ_pos eta_lt_one
      classOfRed μ εb δb Δb weights R hweights_sum_le_two_mu mertens_Pz
      level_budget hmass_logcube_lower hdefect hsuen_tail hdecomp hF2R_tail_two_mu)

/-- Fixed-logarithmic uniform theorem from the standard cited reciprocal-EH
input and canonical scalar-two-mu fixed-numerator data. -/
theorem thm_uniform_m_of_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
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
      ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∃ B > (0 : ℝ),
        ∀ N m : ℕ, 3 ≤ N → 2 ≤ m → (m : ℝ) ≤ (Real.log N) ^ A →
          (fixedNumeratorExceptionalCount m N : ℝ) ≤
            C * (N : ℝ) * uniformNumeratorSaving c B m N :=
  thm_uniform_m_of_reciprocalEH_and_uniformSaturation
    (EHUniformNumeratorHypotheses.of_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_two_mu_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
      (κeh := κeh) (B := B) T Tdef Cp cμ η hκ hB cμ_pos eta_lt_one
      classOfRed μ εb δb Δb weights R hweights_sum_le_two_mu mertens_Pz
      level_budget hmass_logcube_lower hdefect hsuen_tail hdecomp hF2R_tail_two_mu)

/-- EH growing-numerator theorem from the standard cited reciprocal-EH input and
canonical fixed-numerator data, with the scalar two-mu top tail discharged by
the rank choice `24 * μ ≤ 2R`. -/
theorem thm_EH_uniform_m_of_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_rank_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
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
  thm_EH_uniform_m_of_reciprocalEH_and_uniformSaturation
    (EHUniformNumeratorHypotheses.of_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_rank_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
      (κeh := κeh) (B := B) T Tdef Cp cμ η hκ hB cμ_pos eta_lt_one
      classOfRed μ εb δb Δb weights R hweights_sum_le_two_mu mertens_Pz
      level_budget hmass_logcube_lower hdefect hsuen_tail hdecomp hrank_tail)

/-- Fixed-logarithmic uniform theorem from the standard cited reciprocal-EH
input and canonical fixed-numerator data, with the scalar two-mu top tail
discharged by the rank choice `24 * μ ≤ 2R`. -/
theorem thm_uniform_m_of_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_rank_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
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
      ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∃ B > (0 : ℝ),
        ∀ N m : ℕ, 3 ≤ N → 2 ≤ m → (m : ℝ) ≤ (Real.log N) ^ A →
          (fixedNumeratorExceptionalCount m N : ℝ) ≤
            C * (N : ℝ) * uniformNumeratorSaving c B m N :=
  thm_uniform_m_of_reciprocalEH_and_uniformSaturation
    (EHUniformNumeratorHypotheses.of_standard_reciprocalEH_sigma_canonical_nn_rat_weights_nn_defects_rank_tail_direct_decomp_uniform_defect_logcube_mass_lower_exact_concrete_alpha_rankin_smoothPsi
      (κeh := κeh) (B := B) T Tdef Cp cμ η hκ hB cμ_pos eta_lt_one
      classOfRed μ εb δb Δb weights R hweights_sum_le_two_mu mertens_Pz
      level_budget hmass_logcube_lower hdefect hsuen_tail hdecomp hrank_tail)

end EscAnalytic
