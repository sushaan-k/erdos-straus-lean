import EscAnalytic.Assembly

/-!
# Quartic Suen reductions

This file keeps the quartic-hypothesis attack separate from `Assembly.lean`.
It records direct constructors from the already-checked canonical Suen transfer
surface to the exact large-range quartic package and to the paper-facing
certificate proposition.
-/

namespace EscAnalytic

/-- The manuscript's auxiliary family scale at ambient size `N`. -/
noncomputable def canonicalPaperFamilyScale (Cp : ℝ) (N : ℕ) : ℝ :=
  Real.exp (optimizationSmallAlpha Cp *
    (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))

/-- The auxiliary family scale tends to infinity. -/
theorem canonicalPaperFamilyScale_tendsto_atTop (Cp : ℝ) :
    Filter.Tendsto (canonicalPaperFamilyScale Cp)
      Filter.atTop Filter.atTop := by
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hquarter : Filter.Tendsto
      (fun N : ℕ => (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 4)).comp hlog
  have hexponent : Filter.Tendsto
      (fun N : ℕ => optimizationSmallAlpha Cp *
        (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (optimizationSmallAlpha_pos Cp) hquarter
  exact Real.tendsto_exp_atTop.comp hexponent

/-- Cubing the logarithm of the auxiliary scale gives exactly the intended
`(log N)^(3/4)` saving scale. -/
theorem logCube_canonicalPaperFamilyScale
    (Cp : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    logCube (canonicalPaperFamilyScale Cp N) =
      (optimizationSmallAlpha Cp) ^ 3 *
        (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4) := by
  unfold logCube canonicalPaperFamilyScale
  rw [Real.log_exp]
  apply logX_cube_eq
  exact Real.log_nonneg (by exact_mod_cast hN)
  rfl

/-- Correct scale transfer for the concrete actual-family mass.  Unlike the
old ambient-`N` bridge, both bounds are on the manuscript's
`(log N)^(3/4)` scale. -/
theorem actualPaperFamilyMass_canonicalScale_two_sided
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)]
    (Cp : ℝ) (bres : ℕ → ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ T : ℕ, ∀ N : ℕ,
      3 ≤ N → T ≤ N →
      Nat.Coprime (bres N)
        (Inputs.roughModulus (canonicalPaperFamilyScale Cp N)) →
      c * (optimizationSmallAlpha Cp) ^ 3 *
          (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4) ≤
        actualPaperFamilyMassAtScaleNat P
          (canonicalPaperFamilyScale Cp) bres N ∧
        actualPaperFamilyMassAtScaleNat P
          (canonicalPaperFamilyScale Cp) bres N ≤
      C * (optimizationSmallAlpha Cp) ^ 3 *
          (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4) := by
  rcases actualPaperFamilyMassAtScaleNat_logCube_lower P
      (canonicalPaperFamilyScale Cp) bres with ⟨c, Xc, hc, hlower⟩
  rcases actualPaperFamilyMassAtScaleNat_logCube_upper P
      (canonicalPaperFamilyScale Cp) bres with ⟨C, XC, hC, hupper⟩
  have hscale := canonicalPaperFamilyScale_tendsto_atTop Cp
  have hevent : ∀ᶠ N : ℕ in Filter.atTop,
      max (max Xc XC) 1 < canonicalPaperFamilyScale Cp N :=
    hscale.eventually (Filter.eventually_gt_atTop _)
  rcases Filter.eventually_atTop.mp hevent with ⟨T, hT⟩
  refine ⟨c, C, hc, hC, T, ?_⟩
  intro N hN hTN hcop
  have hs := hT N hTN
  have hXc : Xc ≤ canonicalPaperFamilyScale Cp N :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hs.le)
  have hXC : XC ≤ canonicalPaperFamilyScale Cp N :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hs.le)
  have hone : 1 < canonicalPaperFamilyScale Cp N :=
    lt_of_le_of_lt (le_max_right (max Xc XC) 1) hs
  have hcube := logCube_canonicalPaperFamilyScale Cp
    (N := N) (by omega : 1 ≤ N)
  constructor
  · simpa [hcube, mul_assoc] using hlower N hXc hone hcop
  · simpa [hcube, mul_assoc] using hupper N hXC hone hcop

/-- Nonnegative event weights of the actual paper family at the canonical
auxiliary scale. -/
noncomputable def actualPaperFamilyWeightsCanonicalScale
    (P : Params) (Cp : ℝ) (bres : ℕ → ℕ) (N : ℕ) :
    List {q : ℚ // 0 ≤ q} :=
  let indices := Family.familyIndexFinset P (canonicalPaperFamilyScale Cp N)
    (Inputs.roughModulus (canonicalPaperFamilyScale Cp N)) (bres N)
  (Family.familyEventWeightsRat indices).attach.map fun q =>
    ⟨q.1, Family.familyEventWeightsRat_nonneg indices q.1 q.2⟩

/-- Forgetting nonnegativity proofs recovers exactly the family event-weight
list, not a surrogate carrier. -/
theorem actualPaperFamilyWeightsCanonicalScale_values
    (P : Params) (Cp : ℝ) (bres : ℕ → ℕ) (N : ℕ) :
    (actualPaperFamilyWeightsCanonicalScale P Cp bres N).map Subtype.val =
      Family.familyEventWeightsRat
        (Family.familyIndexFinset P (canonicalPaperFamilyScale Cp N)
          (Inputs.roughModulus (canonicalPaperFamilyScale Cp N)) (bres N)) := by
  classical
  unfold actualPaperFamilyWeightsCanonicalScale
  simp

/-- The canonical-scale weight list has exactly the actual-family mass. -/
theorem actualPaperFamilyWeightsCanonicalScale_sum_eq_mass
    (P : Params) (Cp : ℝ) (bres : ℕ → ℕ) {N : ℕ}
    (hscale : 1 < canonicalPaperFamilyScale Cp N) :
    (((actualPaperFamilyWeightsCanonicalScale P Cp bres N).map
        Subtype.val).sum : ℝ) =
      actualPaperFamilyMassAtScaleNat P
        (canonicalPaperFamilyScale Cp) bres N := by
  rw [actualPaperFamilyWeightsCanonicalScale_values]
  rw [Family.actualPaperFamily_eventWeights_sum_eq_indexMass
    P (canonicalPaperFamilyScale Cp N)
      (Inputs.roughModulus (canonicalPaperFamilyScale Cp N)) (bres N) hscale]
  rfl

/-- Consequently the packet's coarse `sum weights ≤ 2 μ` field is automatic
when `μ` is the actual family mass. -/
theorem actualPaperFamilyWeightsCanonicalScale_sum_le_two_mass
    (P : Params) (Cp : ℝ) (bres : ℕ → ℕ) {N : ℕ}
    (hscale : 1 < canonicalPaperFamilyScale Cp N) :
    (((actualPaperFamilyWeightsCanonicalScale P Cp bres N).map
        Subtype.val).sum : ℝ) ≤
      2 * actualPaperFamilyMassAtScaleNat P
        (canonicalPaperFamilyScale Cp) bres N := by
  rw [actualPaperFamilyWeightsCanonicalScale_sum_eq_mass P Cp bres hscale]
  have hmass : 0 ≤ actualPaperFamilyMassAtScaleNat P
      (canonicalPaperFamilyScale Cp) bres N := by
    unfold actualPaperFamilyMassAtScaleNat Family.familyIndexMassRat
    exact_mod_cast (Finset.sum_nonneg fun i hi => by
      unfold Family.FamilyIndex.wRat
      positivity)
  linarith

/-- The manuscript's actual compatible reciprocal-LCM coefficient at the
canonical auxiliary scale. -/
noncomputable def actualPaperFamilyLcmCoefficientCanonicalScale
    (P : Params) (Cp : ℝ) (bres : ℕ → ℕ) (N r : ℕ) : ℝ :=
  (Family.familyCompatibleLcmMassRat
    (Family.familyIndexFinset P (canonicalPaperFamilyScale Cp N)
      (Inputs.roughModulus (canonicalPaperFamilyScale Cp N)) (bres N)) r : ℝ)

/-- Actual compatible reciprocal-LCM coefficients are nonnegative. -/
theorem actualPaperFamilyLcmCoefficientCanonicalScale_nonneg
    (P : Params) (Cp : ℝ) (bres : ℕ → ℕ) (N r : ℕ) :
    0 ≤ actualPaperFamilyLcmCoefficientCanonicalScale P Cp bres N r := by
  unfold actualPaperFamilyLcmCoefficientCanonicalScale
    Family.familyCompatibleLcmMassRat
  exact_mod_cast (Finset.sum_nonneg fun events hevents => by positivity)

/-- Concrete bounded-rank factorial estimate for the actual compatible-LCM
coefficients at the canonical scale. -/
theorem actualPaperFamilyLcmCoefficientCanonicalScale_factorial_up_to
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ K : ℚ, ∃ X₀ : ℝ, 0 < K ∧
      ∀ Cp : ℝ, ∀ bres : ℕ → ℕ, ∀ N : ℕ,
      X₀ ≤ canonicalPaperFamilyScale Cp N →
      Real.exp 2 ≤ canonicalPaperFamilyScale Cp N →
      Nat.Coprime (bres N)
        (Inputs.roughModulus (canonicalPaperFamilyScale Cp N)) →
      ∀ ε : ℚ, 0 ≤ ε → ∀ R : ℕ,
      (K : ℝ) *
        (Real.exp ((R : ℝ) * paperIncrementFloorScale P
          (canonicalPaperFamilyScale Cp N)) - 1) ≤ (ε : ℝ) →
      ∀ r : ℕ, r ≤ R →
        actualPaperFamilyLcmCoefficientCanonicalScale P Cp bres N r ≤
          (((Family.familyIndexMassRat
              (Family.familyIndexFinset P (canonicalPaperFamilyScale Cp N)
                (Inputs.roughModulus (canonicalPaperFamilyScale Cp N))
                (bres N)) * (1 + ε)) ^ r /
            (Nat.factorial r : ℚ) : ℚ) : ℝ) := by
  rcases actualPaperFamily_compatibleLcmMassRat_le_up_to_of_rank_scale P with
    ⟨K, X₀, hK, hbound⟩
  refine ⟨K, X₀, hK, ?_⟩
  intro Cp bres N hX hXexp hcop ε hε R hscalar r hr
  unfold actualPaperFamilyLcmCoefficientCanonicalScale
  exact_mod_cast hbound (canonicalPaperFamilyScale Cp N) hX hXexp
    (bres N) hcop ε hε R hscalar r hr

/-- The manuscript's finite Brun error sum, now using the actual compatible
reciprocal-LCM coefficients rather than elementary-symmetric surrogates. -/
theorem actualPaperFamilyLcmCoefficientCanonicalScale_brun_envelope
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ K : ℚ, ∃ X₀ : ℝ, 0 < K ∧
      ∀ Cp : ℝ, ∀ bres : ℕ → ℕ, ∀ N : ℕ,
      X₀ ≤ canonicalPaperFamilyScale Cp N →
      Real.exp 2 ≤ canonicalPaperFamilyScale Cp N →
      Nat.Coprime (bres N)
        (Inputs.roughModulus (canonicalPaperFamilyScale Cp N)) →
      ∀ ε : ℚ, 0 ≤ ε → ∀ R : ℕ,
      (K : ℝ) *
        (Real.exp ((R : ℝ) * paperIncrementFloorScale P
          (canonicalPaperFamilyScale Cp N)) - 1) ≤ (ε : ℝ) →
      ∀ A : ℝ, 1 ≤ A →
        (∑ r ∈ Finset.range (R + 1), A ^ r *
          actualPaperFamilyLcmCoefficientCanonicalScale P Cp bres N r) ≤
        A ^ R * Real.exp
          ((Family.familyIndexMassRat
            (Family.familyIndexFinset P (canonicalPaperFamilyScale Cp N)
              (Inputs.roughModulus (canonicalPaperFamilyScale Cp N))
              (bres N)) * (1 + ε) : ℚ) : ℝ) := by
  rcases actualPaperFamilyLcmCoefficientCanonicalScale_factorial_up_to P with
    ⟨K, X₀, hK, hfactor⟩
  refine ⟨K, X₀, hK, ?_⟩
  intro Cp bres N hX hXexp hcop ε hε R hscalar A hA
  let indices := Family.familyIndexFinset P (canonicalPaperFamilyScale Cp N)
    (Inputs.roughModulus (canonicalPaperFamilyScale Cp N)) (bres N)
  let Mq : ℚ := Family.familyIndexMassRat indices * (1 + ε)
  have hmassQ : 0 ≤ Family.familyIndexMassRat indices := by
    unfold Family.familyIndexMassRat
    exact Finset.sum_nonneg fun i hi => by
      unfold Family.FamilyIndex.wRat
      positivity
  have hMq : 0 ≤ Mq :=
    mul_nonneg hmassQ (by linarith)
  apply brun_envelope_of_factorial_bound_up_to
    (actualPaperFamilyLcmCoefficientCanonicalScale P Cp bres N)
    (Mq : ℝ) A R (by exact_mod_cast hMq) hA
  intro r hr
  simpa [indices, Mq] using
    hfactor Cp bres N hX hXexp hcop ε hε R hscalar r hr

/-- Paper-facing relaxed canonical quartic fan hypothesis.

This record names the non-rank quartic hypothesis surface directly.  It does
not add a new axiom or a new mathematical route: `toLargeRangeInputs` below
immediately feeds the existing canonical relaxed-defect constructor.  The point
is to make the remaining paper-facing quartic hard core first-class instead of
burying it as an anonymous argument list. -/
structure QuarticCanonicalRelaxedEHFanHypotheses
    (κ : Type*) [DecidableEq κ] where
  classOfRed : ℕ → ℕ → ℕ → κ
  μ : ℕ → ℝ
  εb : ℕ → ℝ
  cμ : ℝ
  T : ℕ
  cμ_pos : 0 < cμ
  local_transfer : ∀ N : ℕ, 3 ≤ N → T ≤ N →
    ∀ s ∈ Finset.Icc 1 N,
      ∀ b ∈ reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s),
        (reducedExceptionalCount (zNatScale N) (N / s) : ℝ) ≤
          ((N : ℝ) / canonicalQuarticPz classOfRed N) *
            Real.exp (-(1 - (εb N + Real.log 3 / μ N)) * μ N)
  mass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
    cμ * logCube (N : ℝ) ≤ μ N
  defect_tendsto_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ))

/-- Build the named quartic Suen hypothesis package with `mu` equal to the
mass of the actual manuscript family.  The cubic mass field is discharged by
`actualPaperFamilyMassNat_eventual_logCube_lower`; callers retain only the
genuinely separate local-transfer and defect estimates. -/
noncomputable def QuarticCanonicalRelaxedEHFanHypotheses.of_actualPaperFamilyMass
    {κ : Type*} [DecidableEq κ]
    (P : Params) (bres : ℕ → ℕ)
    (classOfRed : ℕ → ℕ → ℕ → κ) (εb : ℕ → ℝ) (Tdata : ℕ)
    (hcop : ∀ N : ℕ, 3 ≤ N → Tdata ≤ N →
      Nat.Coprime (bres N) (Inputs.roughModulus (N : ℝ)))
    (hlocal : ∀ N : ℕ, 3 ≤ N → Tdata ≤ N →
      ∀ s ∈ Finset.Icc 1 N,
        ∀ b ∈ reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s),
          (reducedExceptionalCount (zNatScale N) (N / s) : ℝ) ≤
            ((N : ℝ) / canonicalQuarticPz classOfRed N) *
              Real.exp (-(1 - (εb N + Real.log 3 /
                actualPaperFamilyMassNat P bres N)) *
                  actualPaperFamilyMassNat P bres N))
    (hdefect : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ))) :
    QuarticCanonicalRelaxedEHFanHypotheses κ := by
  let hmassEvent := actualPaperFamilyMassNat_eventual_logCube_lower P bres
  let cμ : ℝ := Classical.choose hmassEvent
  have hcμSpec : ∃ X₀ : ℝ, 0 < cμ ∧ ∀ N : ℕ, X₀ ≤ (N : ℝ) → 3 ≤ N →
      Nat.Coprime (bres N) (Inputs.roughModulus (N : ℝ)) →
        cμ * logCube (N : ℝ) ≤ actualPaperFamilyMassNat P bres N :=
    Classical.choose_spec hmassEvent
  let Xμ : ℝ := Classical.choose hcμSpec
  have hmassSpec : 0 < cμ ∧ ∀ N : ℕ, Xμ ≤ (N : ℝ) → 3 ≤ N →
      Nat.Coprime (bres N) (Inputs.roughModulus (N : ℝ)) →
        cμ * logCube (N : ℝ) ≤ actualPaperFamilyMassNat P bres N :=
    Classical.choose_spec hcμSpec
  let T : ℕ := max Tdata (Nat.ceil Xμ)
  refine
    { classOfRed := classOfRed
      μ := actualPaperFamilyMassNat P bres
      εb := εb
      cμ := cμ
      T := T
      cμ_pos := hmassSpec.1
      local_transfer := ?_
      mass_logcube_lower := ?_
      defect_tendsto_zero := hdefect }
  · intro N hN hTN s hs b hb
    exact hlocal N hN
      (le_trans (Nat.le_max_left Tdata (Nat.ceil Xμ)) hTN) s hs b hb
  · intro N hN hTN
    have hceil : Nat.ceil Xμ ≤ N :=
      le_trans (Nat.le_max_right Tdata (Nat.ceil Xμ)) hTN
    have hXμ : Xμ ≤ (N : ℝ) :=
      (Nat.le_ceil Xμ).trans (by exact_mod_cast hceil)
    exact hmassSpec.2 N hXμ hN
      (hcop N hN (le_trans (Nat.le_max_left Tdata (Nat.ceil Xμ)) hTN))

/-- The named paper-facing relaxed canonical quartic hypothesis supplies the
existing large-range quartic input package. -/
noncomputable def QuarticCanonicalRelaxedEHFanHypotheses.toLargeRangeInputs
    {κ : Type*} [DecidableEq κ]
    (H : QuarticCanonicalRelaxedEHFanHypotheses κ) :
    QuarticLargeRangeInputs :=
  QuarticLargeRangeInputs.of_canonical_sigma_classes_logcube_mu_lower_relaxed_defect_auto_card_budget_concrete_lift
    H.classOfRed H.μ H.εb H.cμ H.T H.cμ_pos
    H.local_transfer H.mass_logcube_lower H.defect_tendsto_zero

/-- The named paper-facing relaxed canonical quartic hypothesis supplies the
paper-facing quartic EH fan package after finite-initial absorption. -/
noncomputable def QuarticCanonicalRelaxedEHFanHypotheses.toEHFanInputs
    {κ : Type*} [DecidableEq κ]
    (H : QuarticCanonicalRelaxedEHFanHypotheses κ) :
    QuarticEHFanInputs :=
  H.toLargeRangeInputs.toEHFanInputs

/-- The named paper-facing relaxed canonical quartic hypothesis supplies the
quartic certificate-family proposition used by the geometric capstones. -/
noncomputable def QuarticCertificateFamilyInput.of_canonicalRelaxedEHFanHypotheses
    {κ : Type*} [DecidableEq κ]
    (H : QuarticCanonicalRelaxedEHFanHypotheses κ) :
    QuarticCertificateFamilyInput :=
  QuarticCertificateFamilyInput.of_largeRangeInputs H.toLargeRangeInputs

/-- The standard canonical Suen bridge supplies the named relaxed quartic fan
hypothesis. -/
noncomputable def QuarticCanonicalRelaxedEHFanHypotheses.of_canonical_suen_elemSymm_sum_mass_real_scale_standard_tail
    {κ : Type*} [DecidableEq κ]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (δb Δb : ℕ → (Σ _s : ℕ, κ) → NNReal)
    (weights : ℕ → (Σ _s : ℕ, κ) → List {q : ℚ // 0 ≤ q})
    (X : ℕ → (Σ _s : ℕ, κ) → ℝ)
    (R : ℕ → (Σ _s : ℕ, κ) → ℕ)
    (Cp cμ : ℝ) (T : ℕ)
    (cμ_pos : 0 < cμ)
    (hεb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    (hweights_sum_le_two_mu : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (((weights N b).map Subtype.val).sum : ℝ) ≤ 2 * μ N)
    (hX : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        1 ≤ X N b)
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
            (X N b) ^ r *
              (EscLeanChecks.elemSymmList
                ((weights N b).map Subtype.val) r : ℝ))
    (hscale : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log (X N b) =
          optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))
    (hmertens : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log
          (max (1 : ℝ)
            (((Finset.Icc 1 N).sigma (fun s =>
              reducedCanonicalClasses (zNatScale N) (N / s)
                (classOfRed N s))).card : ℝ))
          ≤ 2 * zScale (X N b))
    (hbudget : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        2 * (R N b : ℝ) * Real.log (X N b) + 6 * μ N
          ≤ Cp * ((optimizationSmallAlpha Cp) ^ 4 * Real.log (N : ℝ)))
    (hF2R_tail_sum_mass : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        ((((weights N b).map Subtype.val).sum : ℝ) ^ (2 * R N b)) /
            (Nat.factorial (2 * R N b) : ℝ)
          ≤ Real.exp (-3 * μ N))
    (hmass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N) :
    QuarticCanonicalRelaxedEHFanHypotheses κ where
  classOfRed := classOfRed
  μ := μ
  εb := εb
  cμ := cμ
  T := T
  cμ_pos := cμ_pos
  local_transfer :=
    canonical_quartic_local_transfer_of_suen_elemSymm_sum_mass_standard_tail_real_X
      classOfRed μ εb δb Δb weights X R Cp cμ T cμ_pos
      hweights_sum_le_two_mu hX hsuen_tail hdecomp hscale hmertens hbudget
      hF2R_tail_sum_mass
      (fun N hN hTN =>
        mu_pos_of_logCube_lower_nat cμ_pos hmass_logcube_lower N hN hTN)
  mass_logcube_lower := hmass_logcube_lower
  defect_tendsto_zero := hεb_zero

/-- The canonical Suen bridge with scalar `2 * μ` top tail supplies the named
relaxed quartic fan hypothesis. -/
noncomputable def QuarticCanonicalRelaxedEHFanHypotheses.of_canonical_suen_elemSymm_sum_mass_two_mu_tail_real_scale_standard_tail
    {κ : Type*} [DecidableEq κ]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (δb Δb : ℕ → (Σ _s : ℕ, κ) → NNReal)
    (weights : ℕ → (Σ _s : ℕ, κ) → List {q : ℚ // 0 ≤ q})
    (X : ℕ → (Σ _s : ℕ, κ) → ℝ)
    (R : ℕ → (Σ _s : ℕ, κ) → ℕ)
    (Cp cμ : ℝ) (T : ℕ)
    (cμ_pos : 0 < cμ)
    (hεb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    (hweights_sum_le_two_mu : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (((weights N b).map Subtype.val).sum : ℝ) ≤ 2 * μ N)
    (hX : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        1 ≤ X N b)
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
            (X N b) ^ r *
              (EscLeanChecks.elemSymmList
                ((weights N b).map Subtype.val) r : ℝ))
    (hscale : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log (X N b) =
          optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))
    (hmertens : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log
          (max (1 : ℝ)
            (((Finset.Icc 1 N).sigma (fun s =>
              reducedCanonicalClasses (zNatScale N) (N / s)
                (classOfRed N s))).card : ℝ))
          ≤ 2 * zScale (X N b))
    (hbudget : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        2 * (R N b : ℝ) * Real.log (X N b) + 6 * μ N
          ≤ Cp * ((optimizationSmallAlpha Cp) ^ 4 * Real.log (N : ℝ)))
    (hF2R_tail_two_mu : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (2 * μ N) ^ (2 * R N b) / (Nat.factorial (2 * R N b) : ℝ)
          ≤ Real.exp (-3 * μ N))
    (hmass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N) :
    QuarticCanonicalRelaxedEHFanHypotheses κ :=
  QuarticCanonicalRelaxedEHFanHypotheses.of_canonical_suen_elemSymm_sum_mass_real_scale_standard_tail
    classOfRed μ εb δb Δb weights X R Cp cμ T cμ_pos hεb_zero
    hweights_sum_le_two_mu hX hsuen_tail hdecomp hscale hmertens hbudget
    (by
      intro N hN hTN b hb
      exact rational_weight_self_tail_of_two_mu_tail
        ((weights N b).map Subtype.val) (R N b) (μ N)
        (by
          intro w hw
          rcases List.mem_map.1 hw with ⟨q, _hq, rfl⟩
          exact q.property)
        (hweights_sum_le_two_mu N hN hTN b hb)
        (hF2R_tail_two_mu N hN hTN b hb))
    hmass_logcube_lower

/-- The canonical Suen bridge with the scalar top-tail discharged from the rank
choice `24 * μ ≤ 2R` supplies the named relaxed quartic fan hypothesis. -/
noncomputable def QuarticCanonicalRelaxedEHFanHypotheses.of_canonical_suen_elemSymm_sum_mass_rank_tail_real_scale_standard_tail
    {κ : Type*} [DecidableEq κ]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (δb Δb : ℕ → (Σ _s : ℕ, κ) → NNReal)
    (weights : ℕ → (Σ _s : ℕ, κ) → List {q : ℚ // 0 ≤ q})
    (X : ℕ → (Σ _s : ℕ, κ) → ℝ)
    (R : ℕ → (Σ _s : ℕ, κ) → ℕ)
    (Cp cμ : ℝ) (T : ℕ)
    (cμ_pos : 0 < cμ)
    (hεb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    (hweights_sum_le_two_mu : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (((weights N b).map Subtype.val).sum : ℝ) ≤ 2 * μ N)
    (hX : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        1 ≤ X N b)
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
            (X N b) ^ r *
              (EscLeanChecks.elemSymmList
                ((weights N b).map Subtype.val) r : ℝ))
    (hscale : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log (X N b) =
          optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))
    (hmertens : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log
          (max (1 : ℝ)
            (((Finset.Icc 1 N).sigma (fun s =>
              reducedCanonicalClasses (zNatScale N) (N / s)
                (classOfRed N s))).card : ℝ))
          ≤ 2 * zScale (X N b))
    (hbudget : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        2 * (R N b : ℝ) * Real.log (X N b) + 6 * μ N
          ≤ Cp * ((optimizationSmallAlpha Cp) ^ 4 * Real.log (N : ℝ)))
    (hrank_tail : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        24 * μ N ≤ (2 * R N b : ℝ))
    (hmass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N) :
    QuarticCanonicalRelaxedEHFanHypotheses κ :=
  QuarticCanonicalRelaxedEHFanHypotheses.of_canonical_suen_elemSymm_sum_mass_two_mu_tail_real_scale_standard_tail
    classOfRed μ εb δb Δb weights X R Cp cμ T cμ_pos hεb_zero
    hweights_sum_le_two_mu hX hsuen_tail hdecomp hscale hmertens hbudget
    (by
      intro N hN hTN b hb
      exact scalar_two_mu_factorial_tail_of_rank_ge
        (mu_nonneg_of_logCube_lower_nat cμ_pos hmass_logcube_lower N hN hTN)
        (hrank_tail N hN hTN b hb))
    hmass_logcube_lower

/-- Exact large-range quartic input from canonical Suen finite-transfer data at
a real Brun scale.

This is the large-range analogue of
`quarticEHFanInputs_of_canonical_suen_elemSymm_sum_mass_real_scale_standard_tail`:
instead of first building `QuarticEHFanInputs`, it feeds the Suen-derived local
canonical transfer directly into the large-range quartic constructor. -/
noncomputable def QuarticLargeRangeInputs.of_canonical_suen_elemSymm_sum_mass_real_scale_standard_tail
    {κ : Type*} [DecidableEq κ]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (δb Δb : ℕ → (Σ _s : ℕ, κ) → NNReal)
    (weights : ℕ → (Σ _s : ℕ, κ) → List {q : ℚ // 0 ≤ q})
    (X : ℕ → (Σ _s : ℕ, κ) → ℝ)
    (R : ℕ → (Σ _s : ℕ, κ) → ℕ)
    (Cp cμ : ℝ) (T : ℕ)
    (cμ_pos : 0 < cμ)
    (hεb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    (hweights_sum_le_two_mu : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (((weights N b).map Subtype.val).sum : ℝ) ≤ 2 * μ N)
    (hX : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        1 ≤ X N b)
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
            (X N b) ^ r *
              (EscLeanChecks.elemSymmList
                ((weights N b).map Subtype.val) r : ℝ))
    (hscale : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log (X N b) =
          optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))
    (hmertens : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log
          (max (1 : ℝ)
            (((Finset.Icc 1 N).sigma (fun s =>
              reducedCanonicalClasses (zNatScale N) (N / s)
                (classOfRed N s))).card : ℝ))
          ≤ 2 * zScale (X N b))
    (hbudget : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        2 * (R N b : ℝ) * Real.log (X N b) + 6 * μ N
          ≤ Cp * ((optimizationSmallAlpha Cp) ^ 4 * Real.log (N : ℝ)))
    (hF2R_tail_sum_mass : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        ((((weights N b).map Subtype.val).sum : ℝ) ^ (2 * R N b)) /
            (Nat.factorial (2 * R N b) : ℝ)
          ≤ Real.exp (-3 * μ N))
    (hmass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N) :
    QuarticLargeRangeInputs :=
  (QuarticCanonicalRelaxedEHFanHypotheses.of_canonical_suen_elemSymm_sum_mass_real_scale_standard_tail
    classOfRed μ εb δb Δb weights X R Cp cμ T cμ_pos hεb_zero
    hweights_sum_le_two_mu hX hsuen_tail hdecomp hscale hmertens hbudget
    hF2R_tail_sum_mass hmass_logcube_lower).toLargeRangeInputs

/-- Paper-facing quartic certificate from the standard canonical Suen bridge. -/
noncomputable def QuarticCertificateFamilyInput.of_canonical_suen_elemSymm_sum_mass_real_scale_standard_tail
    {κ : Type*} [DecidableEq κ]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (δb Δb : ℕ → (Σ _s : ℕ, κ) → NNReal)
    (weights : ℕ → (Σ _s : ℕ, κ) → List {q : ℚ // 0 ≤ q})
    (X : ℕ → (Σ _s : ℕ, κ) → ℝ)
    (R : ℕ → (Σ _s : ℕ, κ) → ℕ)
    (Cp cμ : ℝ) (T : ℕ)
    (cμ_pos : 0 < cμ)
    (hεb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    (hweights_sum_le_two_mu : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (((weights N b).map Subtype.val).sum : ℝ) ≤ 2 * μ N)
    (hX : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        1 ≤ X N b)
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
            (X N b) ^ r *
              (EscLeanChecks.elemSymmList
                ((weights N b).map Subtype.val) r : ℝ))
    (hscale : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log (X N b) =
          optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))
    (hmertens : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log
          (max (1 : ℝ)
            (((Finset.Icc 1 N).sigma (fun s =>
              reducedCanonicalClasses (zNatScale N) (N / s)
                (classOfRed N s))).card : ℝ))
          ≤ 2 * zScale (X N b))
    (hbudget : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        2 * (R N b : ℝ) * Real.log (X N b) + 6 * μ N
          ≤ Cp * ((optimizationSmallAlpha Cp) ^ 4 * Real.log (N : ℝ)))
    (hF2R_tail_sum_mass : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        ((((weights N b).map Subtype.val).sum : ℝ) ^ (2 * R N b)) /
            (Nat.factorial (2 * R N b) : ℝ)
          ≤ Real.exp (-3 * μ N))
    (hmass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N) :
    QuarticCertificateFamilyInput :=
  QuarticCertificateFamilyInput.of_largeRangeInputs
    (QuarticLargeRangeInputs.of_canonical_suen_elemSymm_sum_mass_real_scale_standard_tail
      classOfRed μ εb δb Δb weights X R Cp cμ T cμ_pos hεb_zero
      hweights_sum_le_two_mu hX hsuen_tail hdecomp hscale hmertens hbudget
      hF2R_tail_sum_mass hmass_logcube_lower)

/-- Exact large-range quartic input from canonical Suen data when the top tail
is supplied at the scalar `2 * μ` budget.  This removes the classwise
finite-weight factorial-tail assumption from the large-range quartic surface. -/
noncomputable def QuarticLargeRangeInputs.of_canonical_suen_elemSymm_sum_mass_two_mu_tail_real_scale_standard_tail
    {κ : Type*} [DecidableEq κ]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (δb Δb : ℕ → (Σ _s : ℕ, κ) → NNReal)
    (weights : ℕ → (Σ _s : ℕ, κ) → List {q : ℚ // 0 ≤ q})
    (X : ℕ → (Σ _s : ℕ, κ) → ℝ)
    (R : ℕ → (Σ _s : ℕ, κ) → ℕ)
    (Cp cμ : ℝ) (T : ℕ)
    (cμ_pos : 0 < cμ)
    (hεb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    (hweights_sum_le_two_mu : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (((weights N b).map Subtype.val).sum : ℝ) ≤ 2 * μ N)
    (hX : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        1 ≤ X N b)
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
            (X N b) ^ r *
              (EscLeanChecks.elemSymmList
                ((weights N b).map Subtype.val) r : ℝ))
    (hscale : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log (X N b) =
          optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))
    (hmertens : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log
          (max (1 : ℝ)
            (((Finset.Icc 1 N).sigma (fun s =>
              reducedCanonicalClasses (zNatScale N) (N / s)
                (classOfRed N s))).card : ℝ))
          ≤ 2 * zScale (X N b))
    (hbudget : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        2 * (R N b : ℝ) * Real.log (X N b) + 6 * μ N
          ≤ Cp * ((optimizationSmallAlpha Cp) ^ 4 * Real.log (N : ℝ)))
    (hF2R_tail_two_mu : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (2 * μ N) ^ (2 * R N b) / (Nat.factorial (2 * R N b) : ℝ)
          ≤ Real.exp (-3 * μ N))
    (hmass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N) :
    QuarticLargeRangeInputs :=
  (QuarticCanonicalRelaxedEHFanHypotheses.of_canonical_suen_elemSymm_sum_mass_two_mu_tail_real_scale_standard_tail
    classOfRed μ εb δb Δb weights X R Cp cμ T cμ_pos hεb_zero
    hweights_sum_le_two_mu hX hsuen_tail hdecomp hscale hmertens hbudget
    hF2R_tail_two_mu hmass_logcube_lower).toLargeRangeInputs

/-- Paper-facing quartic certificate from canonical Suen data with scalar
`2 * μ` top-tail input. -/
noncomputable def QuarticCertificateFamilyInput.of_canonical_suen_elemSymm_sum_mass_two_mu_tail_real_scale_standard_tail
    {κ : Type*} [DecidableEq κ]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (δb Δb : ℕ → (Σ _s : ℕ, κ) → NNReal)
    (weights : ℕ → (Σ _s : ℕ, κ) → List {q : ℚ // 0 ≤ q})
    (X : ℕ → (Σ _s : ℕ, κ) → ℝ)
    (R : ℕ → (Σ _s : ℕ, κ) → ℕ)
    (Cp cμ : ℝ) (T : ℕ)
    (cμ_pos : 0 < cμ)
    (hεb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    (hweights_sum_le_two_mu : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (((weights N b).map Subtype.val).sum : ℝ) ≤ 2 * μ N)
    (hX : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        1 ≤ X N b)
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
            (X N b) ^ r *
              (EscLeanChecks.elemSymmList
                ((weights N b).map Subtype.val) r : ℝ))
    (hscale : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log (X N b) =
          optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))
    (hmertens : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log
          (max (1 : ℝ)
            (((Finset.Icc 1 N).sigma (fun s =>
              reducedCanonicalClasses (zNatScale N) (N / s)
                (classOfRed N s))).card : ℝ))
          ≤ 2 * zScale (X N b))
    (hbudget : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        2 * (R N b : ℝ) * Real.log (X N b) + 6 * μ N
          ≤ Cp * ((optimizationSmallAlpha Cp) ^ 4 * Real.log (N : ℝ)))
    (hF2R_tail_two_mu : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (2 * μ N) ^ (2 * R N b) / (Nat.factorial (2 * R N b) : ℝ)
          ≤ Real.exp (-3 * μ N))
    (hmass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N) :
    QuarticCertificateFamilyInput :=
  QuarticCertificateFamilyInput.of_largeRangeInputs
    (QuarticLargeRangeInputs.of_canonical_suen_elemSymm_sum_mass_two_mu_tail_real_scale_standard_tail
      classOfRed μ εb δb Δb weights X R Cp cμ T cμ_pos hεb_zero
      hweights_sum_le_two_mu hX hsuen_tail hdecomp hscale hmertens hbudget
      hF2R_tail_two_mu hmass_logcube_lower)

/-- Exact large-range quartic input from canonical Suen data when the scalar
top-tail is discharged by the rank choice `24 * μ ≤ 2R`.

The log-cube mass lower bound supplies the required nonnegativity of `μ`; the
only remaining scalar top-tail input is the pointwise truncation-rank lower
bound. -/
noncomputable def QuarticLargeRangeInputs.of_canonical_suen_elemSymm_sum_mass_rank_tail_real_scale_standard_tail
    {κ : Type*} [DecidableEq κ]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (δb Δb : ℕ → (Σ _s : ℕ, κ) → NNReal)
    (weights : ℕ → (Σ _s : ℕ, κ) → List {q : ℚ // 0 ≤ q})
    (X : ℕ → (Σ _s : ℕ, κ) → ℝ)
    (R : ℕ → (Σ _s : ℕ, κ) → ℕ)
    (Cp cμ : ℝ) (T : ℕ)
    (cμ_pos : 0 < cμ)
    (hεb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    (hweights_sum_le_two_mu : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (((weights N b).map Subtype.val).sum : ℝ) ≤ 2 * μ N)
    (hX : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        1 ≤ X N b)
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
            (X N b) ^ r *
              (EscLeanChecks.elemSymmList
                ((weights N b).map Subtype.val) r : ℝ))
    (hscale : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log (X N b) =
          optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))
    (hmertens : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log
          (max (1 : ℝ)
            (((Finset.Icc 1 N).sigma (fun s =>
              reducedCanonicalClasses (zNatScale N) (N / s)
                (classOfRed N s))).card : ℝ))
          ≤ 2 * zScale (X N b))
    (hbudget : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        2 * (R N b : ℝ) * Real.log (X N b) + 6 * μ N
          ≤ Cp * ((optimizationSmallAlpha Cp) ^ 4 * Real.log (N : ℝ)))
    (hrank_tail : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        24 * μ N ≤ (2 * R N b : ℝ))
    (hmass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N) :
    QuarticLargeRangeInputs :=
  QuarticLargeRangeInputs.of_canonical_suen_elemSymm_sum_mass_two_mu_tail_real_scale_standard_tail
    classOfRed μ εb δb Δb weights X R Cp cμ T cμ_pos hεb_zero
    hweights_sum_le_two_mu hX hsuen_tail hdecomp hscale hmertens hbudget
    (by
      intro N hN hTN b hb
      exact scalar_two_mu_factorial_tail_of_rank_ge
        (mu_nonneg_of_logCube_lower_nat cμ_pos hmass_logcube_lower N hN hTN)
        (hrank_tail N hN hTN b hb))
    hmass_logcube_lower

/-- Paper-facing quartic certificate from canonical Suen data when the scalar
top-tail is discharged by the rank choice `24 * μ ≤ 2R`. -/
noncomputable def QuarticCertificateFamilyInput.of_canonical_suen_elemSymm_sum_mass_rank_tail_real_scale_standard_tail
    {κ : Type*} [DecidableEq κ]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (δb Δb : ℕ → (Σ _s : ℕ, κ) → NNReal)
    (weights : ℕ → (Σ _s : ℕ, κ) → List {q : ℚ // 0 ≤ q})
    (X : ℕ → (Σ _s : ℕ, κ) → ℝ)
    (R : ℕ → (Σ _s : ℕ, κ) → ℕ)
    (Cp cμ : ℝ) (T : ℕ)
    (cμ_pos : 0 < cμ)
    (hεb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    (hweights_sum_le_two_mu : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (((weights N b).map Subtype.val).sum : ℝ) ≤ 2 * μ N)
    (hX : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        1 ≤ X N b)
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
            (X N b) ^ r *
              (EscLeanChecks.elemSymmList
                ((weights N b).map Subtype.val) r : ℝ))
    (hscale : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log (X N b) =
          optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))
    (hmertens : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log
          (max (1 : ℝ)
            (((Finset.Icc 1 N).sigma (fun s =>
              reducedCanonicalClasses (zNatScale N) (N / s)
                (classOfRed N s))).card : ℝ))
          ≤ 2 * zScale (X N b))
    (hbudget : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        2 * (R N b : ℝ) * Real.log (X N b) + 6 * μ N
          ≤ Cp * ((optimizationSmallAlpha Cp) ^ 4 * Real.log (N : ℝ)))
    (hrank_tail : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        24 * μ N ≤ (2 * R N b : ℝ))
    (hmass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N) :
    QuarticCertificateFamilyInput :=
  QuarticCertificateFamilyInput.of_largeRangeInputs
    (QuarticLargeRangeInputs.of_canonical_suen_elemSymm_sum_mass_rank_tail_real_scale_standard_tail
      classOfRed μ εb δb Δb weights X R Cp cμ T cμ_pos hεb_zero
      hweights_sum_le_two_mu hX hsuen_tail hdecomp hscale hmertens hbudget
      hrank_tail hmass_logcube_lower)

/-- Overstrong rank-tail packet interface for the canonical Suen route.

This record spells out the finite canonical classes, the weighted increment
majorants, the Suen tail, the local decomposition, the real-scale optimization
budget, and the rank choice needed for the top elementary-symmetric tail.  The
rank choice is intentionally separated from the scalar-two-mu packet below,
because the rank-tail route is known to be too strong for the current log-cube
mass and level-budget architecture under the usual eventual-nonempty condition.
It does not contain the final quartic exceptional-set bound as a field; the
conversions below prove that bound from these packet data. -/
structure QuarticCanonicalSuenPacketInputs (κ : Type*) [DecidableEq κ] where
  classOfRed : ℕ → ℕ → ℕ → κ
  μ : ℕ → ℝ
  εb : ℕ → ℝ
  δb : ℕ → (Σ _s : ℕ, κ) → NNReal
  Δb : ℕ → (Σ _s : ℕ, κ) → NNReal
  weights : ℕ → (Σ _s : ℕ, κ) → List {q : ℚ // 0 ≤ q}
  X : ℕ → (Σ _s : ℕ, κ) → ℝ
  R : ℕ → (Σ _s : ℕ, κ) → ℕ
  Cp : ℝ
  cμ : ℝ
  T : ℕ
  cμ_pos : 0 < cμ
  εb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ))
  weights_sum_le_two_mu : ∀ N : ℕ, 3 ≤ N → T ≤ N →
    ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
      reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
      (((weights N b).map Subtype.val).sum : ℝ) ≤ 2 * μ N
  X_ge_one : ∀ N : ℕ, 3 ≤ N → T ≤ N →
    ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
      reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
      1 ≤ X N b
  suen_tail : ∀ N : ℕ, 3 ≤ N → T ≤ N →
    ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
      reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
      Inputs.suenTailConstant * (Δb N b : ℝ) *
          Real.exp (2 * (δb N b : ℝ)) ≤ εb N * μ N
  decomp : ∀ N : ℕ, 3 ≤ N → T ≤ N →
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
          (X N b) ^ r *
            (EscLeanChecks.elemSymmList
              ((weights N b).map Subtype.val) r : ℝ)
  scale : ∀ N : ℕ, 3 ≤ N → T ≤ N →
    ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
      reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
      Real.log (X N b) =
        optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)
  mertens_budget : ∀ N : ℕ, 3 ≤ N → T ≤ N →
    ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
      reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
      Real.log
        (max (1 : ℝ)
          (((Finset.Icc 1 N).sigma (fun s =>
            reducedCanonicalClasses (zNatScale N) (N / s)
              (classOfRed N s))).card : ℝ))
        ≤ 2 * zScale (X N b)
  level_budget : ∀ N : ℕ, 3 ≤ N → T ≤ N →
    ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
      reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
      2 * (R N b : ℝ) * Real.log (X N b) + 6 * μ N
        ≤ Cp * ((optimizationSmallAlpha Cp) ^ 4 * Real.log (N : ℝ))
  rank_tail : ∀ N : ℕ, 3 ≤ N → T ≤ N →
    ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
      reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
      24 * μ N ≤ (2 * R N b : ℝ)
  mass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
    cμ * logCube (N : ℝ) ≤ μ N

/-- Narrow quartic packet interface for the canonical Suen route, stopping at
the scalar `2 * μ` top-tail estimate.

This is the non-rank-tail version of `QuarticCanonicalSuenPacketInputs`.  It
keeps the remaining analytic obligation at the scalar factorial-tail level and
does not package the separate pointwise rank inequality, which is known to be
too strong for the current log-cube mass and level-budget architecture. -/
structure QuarticCanonicalSuenTwoMuPacketInputs (κ : Type*) [DecidableEq κ] where
  classOfRed : ℕ → ℕ → ℕ → κ
  μ : ℕ → ℝ
  εb : ℕ → ℝ
  δb : ℕ → (Σ _s : ℕ, κ) → NNReal
  Δb : ℕ → (Σ _s : ℕ, κ) → NNReal
  weights : ℕ → (Σ _s : ℕ, κ) → List {q : ℚ // 0 ≤ q}
  X : ℕ → (Σ _s : ℕ, κ) → ℝ
  R : ℕ → (Σ _s : ℕ, κ) → ℕ
  Cp : ℝ
  cμ : ℝ
  T : ℕ
  cμ_pos : 0 < cμ
  εb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ))
  weights_sum_le_two_mu : ∀ N : ℕ, 3 ≤ N → T ≤ N →
    ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
      reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
      (((weights N b).map Subtype.val).sum : ℝ) ≤ 2 * μ N
  X_ge_one : ∀ N : ℕ, 3 ≤ N → T ≤ N →
    ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
      reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
      1 ≤ X N b
  suen_tail : ∀ N : ℕ, 3 ≤ N → T ≤ N →
    ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
      reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
      Inputs.suenTailConstant * (Δb N b : ℝ) *
          Real.exp (2 * (δb N b : ℝ)) ≤ εb N * μ N
  decomp : ∀ N : ℕ, 3 ≤ N → T ≤ N →
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
          (X N b) ^ r *
            (EscLeanChecks.elemSymmList
              ((weights N b).map Subtype.val) r : ℝ)
  scale : ∀ N : ℕ, 3 ≤ N → T ≤ N →
    ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
      reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
      Real.log (X N b) =
        optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)
  mertens_budget : ∀ N : ℕ, 3 ≤ N → T ≤ N →
    ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
      reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
      Real.log
        (max (1 : ℝ)
          (((Finset.Icc 1 N).sigma (fun s =>
            reducedCanonicalClasses (zNatScale N) (N / s)
              (classOfRed N s))).card : ℝ))
        ≤ 2 * zScale (X N b)
  level_budget : ∀ N : ℕ, 3 ≤ N → T ≤ N →
    ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
      reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
      2 * (R N b : ℝ) * Real.log (X N b) + 6 * μ N
        ≤ Cp * ((optimizationSmallAlpha Cp) ^ 4 * Real.log (N : ℝ))
  two_mu_tail : ∀ N : ℕ, 3 ≤ N → T ≤ N →
    ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
      reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
      (2 * μ N) ^ (2 * R N b) / (Nat.factorial (2 * R N b) : ℝ)
        ≤ Real.exp (-3 * μ N)
  mass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
    cμ * logCube (N : ℝ) ≤ μ N

/-- Build the scalar-two-mu canonical Suen packet with the level budget derived
from lower-level rank and mass estimates.

The output cutoff is enlarged once so that
`optimizationSmallAlpha Cp * (log N)^(1/4) ≥ 1`.  On that range the existing
scalar algebra lemma `level_budget_of_rank_mu_upper_logX_cube_scalar` converts
`2R ≤ KR μ`, `μ ≤ cM(log X)^3`, and `(KR + 6)cM ≤ Cp` into the packet's
`level_budget` field. -/
noncomputable def QuarticCanonicalSuenTwoMuPacketInputs.of_level_budget_from_rank_mass
    {κ : Type*} [DecidableEq κ]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (δb Δb : ℕ → (Σ _s : ℕ, κ) → NNReal)
    (weights : ℕ → (Σ _s : ℕ, κ) → List {q : ℚ // 0 ≤ q})
    (X : ℕ → (Σ _s : ℕ, κ) → ℝ)
    (R : ℕ → (Σ _s : ℕ, κ) → ℕ)
    (Cp cμ KR cM : ℝ) (T : ℕ)
    (cμ_pos : 0 < cμ)
    (hKR_nonneg : 0 ≤ KR)
    (hlevel_constants : (KR + 6) * cM ≤ Cp)
    (εb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    (weights_sum_le_two_mu : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (((weights N b).map Subtype.val).sum : ℝ) ≤ 2 * μ N)
    (X_ge_one : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        1 ≤ X N b)
    (suen_tail : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Inputs.suenTailConstant * (Δb N b : ℝ) *
            Real.exp (2 * (δb N b : ℝ)) ≤ εb N * μ N)
    (decomp : ∀ N : ℕ, 3 ≤ N → T ≤ N →
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
            (X N b) ^ r *
              (EscLeanChecks.elemSymmList
                ((weights N b).map Subtype.val) r : ℝ))
    (scale : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log (X N b) =
          optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))
    (mertens_budget : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log
          (max (1 : ℝ)
            (((Finset.Icc 1 N).sigma (fun s =>
              reducedCanonicalClasses (zNatScale N) (N / s)
                (classOfRed N s))).card : ℝ))
          ≤ 2 * zScale (X N b))
    (rank_level_upper : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        2 * (R N b : ℝ) ≤ KR * μ N)
    (mass_logX_upper : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      μ N ≤ cM *
        (optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) ^ 3)
    (two_mu_tail : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (2 * μ N) ^ (2 * R N b) / (Nat.factorial (2 * R N b) : ℝ)
          ≤ Real.exp (-3 * μ N))
    (mass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N) :
    QuarticCanonicalSuenTwoMuPacketInputs κ := by
  classical
  let Tlog : ℕ :=
    Classical.choose
      (Filter.eventually_atTop.mp
        (eventually_one_le_optimizationSmallAlpha_log_quarter Cp))
  have hlog : ∀ N ≥ Tlog,
      1 ≤ optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4) :=
    Classical.choose_spec
      (Filter.eventually_atTop.mp
        (eventually_one_le_optimizationSmallAlpha_log_quarter Cp))
  refine
    { classOfRed := classOfRed
      μ := μ
      εb := εb
      δb := δb
      Δb := Δb
      weights := weights
      X := X
      R := R
      Cp := Cp
      cμ := cμ
      T := max T Tlog
      cμ_pos := cμ_pos
      εb_zero := εb_zero
      weights_sum_le_two_mu := ?_
      X_ge_one := ?_
      suen_tail := ?_
      decomp := ?_
      scale := ?_
      mertens_budget := ?_
      level_budget := ?_
      two_mu_tail := ?_
      mass_logcube_lower := ?_ }
  · intro N hN hTN b hb
    exact weights_sum_le_two_mu N hN
      (le_trans (Nat.le_max_left T Tlog) hTN) b hb
  · intro N hN hTN b hb
    exact X_ge_one N hN (le_trans (Nat.le_max_left T Tlog) hTN) b hb
  · intro N hN hTN b hb
    exact suen_tail N hN (le_trans (Nat.le_max_left T Tlog) hTN) b hb
  · intro N hN hTN b hb
    exact decomp N hN (le_trans (Nat.le_max_left T Tlog) hTN) b hb
  · intro N hN hTN b hb
    exact scale N hN (le_trans (Nat.le_max_left T Tlog) hTN) b hb
  · intro N hN hTN b hb
    exact mertens_budget N hN (le_trans (Nat.le_max_left T Tlog) hTN) b hb
  · intro N hN hTN b hb
    have hT : T ≤ N := le_trans (Nat.le_max_left T Tlog) hTN
    have hTlog : Tlog ≤ N := le_trans (Nat.le_max_right T Tlog) hTN
    have hNge_one : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ N)
    rw [scale N hN hT b hb]
    exact
      level_budget_of_rank_mu_upper_logX_cube_scalar
        (R := R N b) (μ := μ N) (Cp := Cp) (KR := KR) (cM := cM)
        (a := optimizationSmallAlpha Cp) (L := Real.log (N : ℝ))
        (Real.log_nonneg hNge_one)
        (hlog N hTlog)
        ((mu_nonneg_of_logCube_lower_nat cμ_pos mass_logcube_lower) N hN hT)
        hKR_nonneg
        (rank_level_upper N hN hT b hb)
        (mass_logX_upper N hN hT)
        hlevel_constants
  · intro N hN hTN b hb
    exact two_mu_tail N hN (le_trans (Nat.le_max_left T Tlog) hTN) b hb
  · intro N hN hTN
    exact mass_logcube_lower N hN (le_trans (Nat.le_max_left T Tlog) hTN)

/-- Build the scalar-two-mu canonical Suen packet at the canonical exponential
scale.

This refines `of_level_budget_from_rank_mass` by fixing
`X = exp(optimizationSmallAlpha Cp * (log N)^(1/4))`.  The scale identity is then
`Real.log_exp`, and `X ≥ 1` follows from nonnegativity of the displayed
exponent on `N ≥ 3`. -/
noncomputable def QuarticCanonicalSuenTwoMuPacketInputs.of_exp_scale_level_budget_from_rank_mass
    {κ : Type*} [DecidableEq κ]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (δb Δb : ℕ → (Σ _s : ℕ, κ) → NNReal)
    (weights : ℕ → (Σ _s : ℕ, κ) → List {q : ℚ // 0 ≤ q})
    (R : ℕ → (Σ _s : ℕ, κ) → ℕ)
    (Cp cμ KR cM : ℝ) (T : ℕ)
    (cμ_pos : 0 < cμ)
    (hKR_nonneg : 0 ≤ KR)
    (hlevel_constants : (KR + 6) * cM ≤ Cp)
    (εb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    (weights_sum_le_two_mu : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (((weights N b).map Subtype.val).sum : ℝ) ≤ 2 * μ N)
    (suen_tail : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Inputs.suenTailConstant * (Δb N b : ℝ) *
            Real.exp (2 * (δb N b : ℝ)) ≤ εb N * μ N)
    (decomp : ∀ N : ℕ, 3 ≤ N → T ≤ N →
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
            (Real.exp
              (optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))) ^ r *
              (EscLeanChecks.elemSymmList
                ((weights N b).map Subtype.val) r : ℝ))
    (mertens_budget : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log
          (max (1 : ℝ)
            (((Finset.Icc 1 N).sigma (fun s =>
              reducedCanonicalClasses (zNatScale N) (N / s)
                (classOfRed N s))).card : ℝ))
          ≤ 2 * zScale
            (Real.exp
              (optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))))
    (rank_level_upper : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        2 * (R N b : ℝ) ≤ KR * μ N)
    (mass_logX_upper : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      μ N ≤ cM *
        (optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) ^ 3)
    (two_mu_tail : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (2 * μ N) ^ (2 * R N b) / (Nat.factorial (2 * R N b) : ℝ)
          ≤ Real.exp (-3 * μ N))
    (mass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N) :
    QuarticCanonicalSuenTwoMuPacketInputs κ :=
  QuarticCanonicalSuenTwoMuPacketInputs.of_level_budget_from_rank_mass
    classOfRed μ εb δb Δb weights
    (fun N _b =>
      Real.exp (optimizationSmallAlpha Cp * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)))
    R Cp cμ KR cM T cμ_pos hKR_nonneg hlevel_constants εb_zero
    weights_sum_le_two_mu
    (by
      intro N hN _hTN b _hb
      have hNge_one : (1 : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (by omega : 1 ≤ N)
      have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNge_one
      have hpow_nonneg :
          0 ≤ (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4) :=
        Real.rpow_nonneg hlog_nonneg _
      exact Real.one_le_exp
        (mul_nonneg (optimizationSmallAlpha_pos Cp).le hpow_nonneg))
    suen_tail decomp
    (by
      intro N _hN _hTN b _hb
      simp [Real.log_exp])
    mertens_budget rank_level_upper mass_logX_upper two_mu_tail mass_logcube_lower

/-- Build the scalar-two-mu packet at canonical exponential scale and canonical
Brun rank.

This removes the explicit rank function, the rank upper bound, and the scalar
two-mu tail hypothesis from the preceding constructor.  The rank is fixed to
`floor(12 μ(N)) + 1`; after enlarging the large-`N` cutoff until `μ ≥ 1`,
`brun_floor_rank_upper_of_one_le` gives the level-budget rank upper bound and
`brun_floor_rank_tail` feeds `scalar_two_mu_factorial_tail_of_rank_ge`. -/
noncomputable def QuarticCanonicalSuenTwoMuPacketInputs.of_exp_scale_brun_rank_floor
    {κ : Type*} [DecidableEq κ]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (δb Δb : ℕ → (Σ _s : ℕ, κ) → NNReal)
    (weights : ℕ → (Σ _s : ℕ, κ) → List {q : ℚ // 0 ≤ q})
    (cμ cM : ℝ) (T : ℕ)
    (cμ_pos : 0 < cμ)
    (εb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    (weights_sum_le_two_mu : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (((weights N b).map Subtype.val).sum : ℝ) ≤ 2 * μ N)
    (suen_tail : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Inputs.suenTailConstant * (Δb N b : ℝ) *
            Real.exp (2 * (δb N b : ℝ)) ≤ εb N * μ N)
    (decomp : ∀ N : ℕ, 3 ≤ N → T ≤ N →
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
              ((weights N b).map Subtype.val)
                (2 * (⌊12 * μ N⌋₊ + 1)) : ℝ)) +
          ∑ r ∈ Finset.range (2 * (⌊12 * μ N⌋₊ + 1) + 1),
            (Real.exp
              (optimizationSmallAlpha (((26 : ℝ) + 6) * cM) *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))) ^ r *
              (EscLeanChecks.elemSymmList
                ((weights N b).map Subtype.val) r : ℝ))
    (mertens_budget : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log
          (max (1 : ℝ)
            (((Finset.Icc 1 N).sigma (fun s =>
              reducedCanonicalClasses (zNatScale N) (N / s)
                (classOfRed N s))).card : ℝ))
          ≤ 2 * zScale
            (Real.exp
              (optimizationSmallAlpha (((26 : ℝ) + 6) * cM) *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))))
    (mass_logX_upper : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      μ N ≤ cM *
        (optimizationSmallAlpha (((26 : ℝ) + 6) * cM) *
          (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) ^ 3)
    (mass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N) :
    QuarticCanonicalSuenTwoMuPacketInputs κ := by
  classical
  let hev :=
    Filter.eventually_atTop.mp
      ((mu_tendsto_atTop_of_logCube_lower_nat cμ_pos mass_logcube_lower).eventually
        (Filter.eventually_ge_atTop (1 : ℝ)))
  let Tmu : ℕ := Classical.choose hev
  have hmu_ge_one : ∀ N ≥ Tmu, (1 : ℝ) ≤ μ N :=
    Classical.choose_spec hev
  exact
    QuarticCanonicalSuenTwoMuPacketInputs.of_exp_scale_level_budget_from_rank_mass
      classOfRed μ εb δb Δb weights
      (fun N _b => ⌊12 * μ N⌋₊ + 1)
      (((26 : ℝ) + 6) * cM) cμ (26 : ℝ) cM (max T Tmu)
      cμ_pos (by norm_num)
      le_rfl εb_zero
      (by
        intro N hN hTN b hb
        exact weights_sum_le_two_mu N hN
          (le_trans (Nat.le_max_left T Tmu) hTN) b hb)
      (by
        intro N hN hTN b hb
        exact suen_tail N hN (le_trans (Nat.le_max_left T Tmu) hTN) b hb)
      (by
        intro N hN hTN b hb
        exact decomp N hN (le_trans (Nat.le_max_left T Tmu) hTN) b hb)
      (by
        intro N hN hTN b hb
        exact mertens_budget N hN (le_trans (Nat.le_max_left T Tmu) hTN) b hb)
      (by
        intro N _hN hTN b _hb
        exact brun_floor_rank_upper_of_one_le
          (μ := μ N)
          (hmu_ge_one N (le_trans (Nat.le_max_right T Tmu) hTN)))
      (by
        intro N hN hTN
        exact mass_logX_upper N hN (le_trans (Nat.le_max_left T Tmu) hTN))
      (by
        intro N hN hTN b hb
        exact scalar_two_mu_factorial_tail_of_rank_ge
          ((mu_nonneg_of_logCube_lower_nat cμ_pos mass_logcube_lower)
            N hN (le_trans (Nat.le_max_left T Tmu) hTN))
          (by simpa using brun_floor_rank_tail (μ N)))
      (by
        intro N hN hTN
        exact mass_logcube_lower N hN (le_trans (Nat.le_max_left T Tmu) hTN))

/-- The scalar-two-mu canonical Suen packet supplies the named relaxed quartic
fan hypothesis directly. -/
noncomputable def QuarticCanonicalSuenTwoMuPacketInputs.toRelaxedEHFanHypotheses
    {κ : Type*} [DecidableEq κ] (H : QuarticCanonicalSuenTwoMuPacketInputs κ) :
    QuarticCanonicalRelaxedEHFanHypotheses κ :=
  QuarticCanonicalRelaxedEHFanHypotheses.of_canonical_suen_elemSymm_sum_mass_two_mu_tail_real_scale_standard_tail
    H.classOfRed H.μ H.εb H.δb H.Δb H.weights H.X H.R H.Cp H.cμ H.T
    H.cμ_pos H.εb_zero H.weights_sum_le_two_mu H.X_ge_one H.suen_tail
    H.decomp H.scale H.mertens_budget H.level_budget H.two_mu_tail
    H.mass_logcube_lower

/-- The overstrong rank-tail canonical Suen packet also supplies the named
relaxed quartic fan hypothesis, by first deriving the scalar two-mu tail. -/
noncomputable def QuarticCanonicalSuenPacketInputs.toRelaxedEHFanHypotheses
    {κ : Type*} [DecidableEq κ] (H : QuarticCanonicalSuenPacketInputs κ) :
    QuarticCanonicalRelaxedEHFanHypotheses κ :=
  QuarticCanonicalRelaxedEHFanHypotheses.of_canonical_suen_elemSymm_sum_mass_two_mu_tail_real_scale_standard_tail
    H.classOfRed H.μ H.εb H.δb H.Δb H.weights H.X H.R H.Cp H.cμ H.T
    H.cμ_pos H.εb_zero H.weights_sum_le_two_mu H.X_ge_one H.suen_tail
    H.decomp H.scale H.mertens_budget H.level_budget
      (by
        intro N hN hTN b hb
        exact scalar_two_mu_factorial_tail_of_rank_ge
          (mu_nonneg_of_logCube_lower_nat H.cμ_pos H.mass_logcube_lower N hN hTN)
          (H.rank_tail N hN hTN b hb))
    H.mass_logcube_lower

/-- The scalar-two-mu canonical Suen packet implies the exact large-range
quartic hard core. -/
noncomputable def QuarticCanonicalSuenTwoMuPacketInputs.toLargeRangeInputs
    {κ : Type*} [DecidableEq κ] (H : QuarticCanonicalSuenTwoMuPacketInputs κ) :
    QuarticLargeRangeInputs :=
  H.toRelaxedEHFanHypotheses.toLargeRangeInputs

/-- The scalar-two-mu canonical Suen packet implies the paper-facing quartic
certificate. -/
noncomputable def QuarticCanonicalSuenTwoMuPacketInputs.toCertificateFamilyInput
    {κ : Type*} [DecidableEq κ] (H : QuarticCanonicalSuenTwoMuPacketInputs κ) :
    QuarticCertificateFamilyInput :=
  QuarticCertificateFamilyInput.of_canonicalRelaxedEHFanHypotheses
    H.toRelaxedEHFanHypotheses

/-- Quartic optimization theorem from the scalar-two-mu canonical Suen packet
interface. -/
theorem thm_EH_quartic_of_canonicalSuenTwoMuPacket
    {κ : Type*} [DecidableEq κ] (H : QuarticCanonicalSuenTwoMuPacketInputs κ) :
    ∃ c₄ > (0 : ℝ), ∃ C₄ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      (exceptionalCount N : ℝ) ≤ C₄ * (N : ℝ) * quarticSaving c₄ N :=
  thm_EH_quartic_of_largeRangeInputs H.toLargeRangeInputs

/-- Exact large-range quartic input from canonical Suen data at the canonical
exponential scale and canonical Brun rank.

This is the rank-floor surface for the canonical Suen route.  The caller no
longer supplies an explicit rank function, rank upper bound, scalar two-mu tail,
or level budget; those are discharged by
`QuarticCanonicalSuenTwoMuPacketInputs.of_exp_scale_brun_rank_floor`. -/
noncomputable def QuarticLargeRangeInputs.of_canonical_suen_exp_scale_brun_rank_floor_standard_tail
    {κ : Type*} [DecidableEq κ]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (δb Δb : ℕ → (Σ _s : ℕ, κ) → NNReal)
    (weights : ℕ → (Σ _s : ℕ, κ) → List {q : ℚ // 0 ≤ q})
    (cμ cM : ℝ) (T : ℕ)
    (cμ_pos : 0 < cμ)
    (εb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    (weights_sum_le_two_mu : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (((weights N b).map Subtype.val).sum : ℝ) ≤ 2 * μ N)
    (suen_tail : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Inputs.suenTailConstant * (Δb N b : ℝ) *
            Real.exp (2 * (δb N b : ℝ)) ≤ εb N * μ N)
    (decomp : ∀ N : ℕ, 3 ≤ N → T ≤ N →
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
              ((weights N b).map Subtype.val)
                (2 * (⌊12 * μ N⌋₊ + 1)) : ℝ)) +
          ∑ r ∈ Finset.range (2 * (⌊12 * μ N⌋₊ + 1) + 1),
            (Real.exp
              (optimizationSmallAlpha (((26 : ℝ) + 6) * cM) *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))) ^ r *
              (EscLeanChecks.elemSymmList
                ((weights N b).map Subtype.val) r : ℝ))
    (mertens_budget : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log
          (max (1 : ℝ)
            (((Finset.Icc 1 N).sigma (fun s =>
              reducedCanonicalClasses (zNatScale N) (N / s)
                (classOfRed N s))).card : ℝ))
          ≤ 2 * zScale
            (Real.exp
              (optimizationSmallAlpha (((26 : ℝ) + 6) * cM) *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))))
    (mass_logX_upper : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      μ N ≤ cM *
        (optimizationSmallAlpha (((26 : ℝ) + 6) * cM) *
          (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) ^ 3)
    (mass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N) :
    QuarticLargeRangeInputs :=
  (QuarticCanonicalSuenTwoMuPacketInputs.of_exp_scale_brun_rank_floor
    classOfRed μ εb δb Δb weights cμ cM T cμ_pos εb_zero
    weights_sum_le_two_mu suen_tail decomp mertens_budget mass_logX_upper
    mass_logcube_lower).toLargeRangeInputs

/-- Paper-facing quartic certificate from canonical Suen data at the canonical
exponential scale and canonical Brun rank. -/
noncomputable def QuarticCertificateFamilyInput.of_canonical_suen_exp_scale_brun_rank_floor_standard_tail
    {κ : Type*} [DecidableEq κ]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (δb Δb : ℕ → (Σ _s : ℕ, κ) → NNReal)
    (weights : ℕ → (Σ _s : ℕ, κ) → List {q : ℚ // 0 ≤ q})
    (cμ cM : ℝ) (T : ℕ)
    (cμ_pos : 0 < cμ)
    (εb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    (weights_sum_le_two_mu : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (((weights N b).map Subtype.val).sum : ℝ) ≤ 2 * μ N)
    (suen_tail : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Inputs.suenTailConstant * (Δb N b : ℝ) *
            Real.exp (2 * (δb N b : ℝ)) ≤ εb N * μ N)
    (decomp : ∀ N : ℕ, 3 ≤ N → T ≤ N →
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
              ((weights N b).map Subtype.val)
                (2 * (⌊12 * μ N⌋₊ + 1)) : ℝ)) +
          ∑ r ∈ Finset.range (2 * (⌊12 * μ N⌋₊ + 1) + 1),
            (Real.exp
              (optimizationSmallAlpha (((26 : ℝ) + 6) * cM) *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))) ^ r *
              (EscLeanChecks.elemSymmList
                ((weights N b).map Subtype.val) r : ℝ))
    (mertens_budget : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log
          (max (1 : ℝ)
            (((Finset.Icc 1 N).sigma (fun s =>
              reducedCanonicalClasses (zNatScale N) (N / s)
                (classOfRed N s))).card : ℝ))
          ≤ 2 * zScale
            (Real.exp
              (optimizationSmallAlpha (((26 : ℝ) + 6) * cM) *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))))
    (mass_logX_upper : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      μ N ≤ cM *
        (optimizationSmallAlpha (((26 : ℝ) + 6) * cM) *
          (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) ^ 3)
    (mass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N) :
    QuarticCertificateFamilyInput :=
  QuarticCertificateFamilyInput.of_largeRangeInputs
    (QuarticLargeRangeInputs.of_canonical_suen_exp_scale_brun_rank_floor_standard_tail
      classOfRed μ εb δb Δb weights cμ cM T cμ_pos εb_zero
      weights_sum_le_two_mu suen_tail decomp mertens_budget mass_logX_upper
      mass_logcube_lower)

/-- Quartic optimization theorem from canonical Suen data at the canonical
exponential scale and canonical Brun rank. -/
theorem thm_EH_quartic_of_canonical_suen_exp_scale_brun_rank_floor_standard_tail
    {κ : Type*} [DecidableEq κ]
    (classOfRed : ℕ → ℕ → ℕ → κ)
    (μ εb : ℕ → ℝ)
    (δb Δb : ℕ → (Σ _s : ℕ, κ) → NNReal)
    (weights : ℕ → (Σ _s : ℕ, κ) → List {q : ℚ // 0 ≤ q})
    (cμ cM : ℝ) (T : ℕ)
    (cμ_pos : 0 < cμ)
    (εb_zero : Filter.Tendsto εb Filter.atTop (nhds (0 : ℝ)))
    (weights_sum_le_two_mu : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        (((weights N b).map Subtype.val).sum : ℝ) ≤ 2 * μ N)
    (suen_tail : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Inputs.suenTailConstant * (Δb N b : ℝ) *
            Real.exp (2 * (δb N b : ℝ)) ≤ εb N * μ N)
    (decomp : ∀ N : ℕ, 3 ≤ N → T ≤ N →
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
              ((weights N b).map Subtype.val)
                (2 * (⌊12 * μ N⌋₊ + 1)) : ℝ)) +
          ∑ r ∈ Finset.range (2 * (⌊12 * μ N⌋₊ + 1) + 1),
            (Real.exp
              (optimizationSmallAlpha (((26 : ℝ) + 6) * cM) *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))) ^ r *
              (EscLeanChecks.elemSymmList
                ((weights N b).map Subtype.val) r : ℝ))
    (mertens_budget : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b ∈ (Finset.Icc 1 N).sigma (fun s =>
        reducedCanonicalClasses (zNatScale N) (N / s) (classOfRed N s)),
        Real.log
          (max (1 : ℝ)
            (((Finset.Icc 1 N).sigma (fun s =>
              reducedCanonicalClasses (zNatScale N) (N / s)
                (classOfRed N s))).card : ℝ))
          ≤ 2 * zScale
            (Real.exp
              (optimizationSmallAlpha (((26 : ℝ) + 6) * cM) *
                (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))))
    (mass_logX_upper : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      μ N ≤ cM *
        (optimizationSmallAlpha (((26 : ℝ) + 6) * cM) *
          (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) ^ 3)
    (mass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N) :
    ∃ c₄ > (0 : ℝ), ∃ C₄ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      (exceptionalCount N : ℝ) ≤ C₄ * (N : ℝ) * quarticSaving c₄ N :=
  thm_EH_quartic_of_largeRangeInputs
    (QuarticLargeRangeInputs.of_canonical_suen_exp_scale_brun_rank_floor_standard_tail
      classOfRed μ εb δb Δb weights cμ cM T cμ_pos εb_zero
      weights_sum_le_two_mu suen_tail decomp mertens_budget mass_logX_upper
      mass_logcube_lower)

/-- The remaining mass hypotheses in the canonical rank-floor route are
eventually incompatible.

This is the exp-scale form before specializing the quartic Brun-rank constant:
the quarter-log upper mass law cannot coexist eventually with a positive
log-cube lower mass law. -/
theorem canonical_suen_exp_scale_mass_logX_upper_logCube_lower_incompatible
    {μ : ℕ → ℝ} {Cp cμ cM : ℝ} {T : ℕ}
    (cμ_pos : 0 < cμ)
    (mass_logX_upper : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      μ N ≤ cM *
        (optimizationSmallAlpha Cp *
          (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) ^ 3)
    (mass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N) :
    False :=
  mass_logCube_lower_and_quarter_upper_eventually_incompatible
    (μ := μ) (cμ := cμ) (cM := cM) (a := optimizationSmallAlpha Cp) (T := T)
    cμ_pos mass_logX_upper mass_logcube_lower

/-- The remaining mass hypotheses in the canonical rank-floor route are
eventually incompatible.

After the rank, scalar two-mu tail, and level budget are discharged by the
rank-floor constructor, the exposed upper mass law is still a quarter-log scale
bound.  It cannot coexist eventually with a positive log-cube lower mass law. -/
theorem canonical_suen_exp_scale_brun_rank_floor_mass_logX_upper_logCube_lower_incompatible
    {μ : ℕ → ℝ} {cμ cM : ℝ} {T : ℕ}
    (cμ_pos : 0 < cμ)
    (mass_logX_upper : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      μ N ≤ cM *
        (optimizationSmallAlpha (((26 : ℝ) + 6) * cM) *
          (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4)) ^ 3)
    (mass_logcube_lower : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      cμ * logCube (N : ℝ) ≤ μ N) :
    False :=
  canonical_suen_exp_scale_mass_logX_upper_logCube_lower_incompatible
    (Cp := ((26 : ℝ) + 6) * cM)
    cμ_pos mass_logX_upper mass_logcube_lower

/-- The overstrong rank-tail canonical Suen packet implies the exact
large-range quartic hard core. -/
noncomputable def QuarticCanonicalSuenPacketInputs.toLargeRangeInputs
    {κ : Type*} [DecidableEq κ] (H : QuarticCanonicalSuenPacketInputs κ) :
    QuarticLargeRangeInputs :=
  H.toRelaxedEHFanHypotheses.toLargeRangeInputs

/-- The overstrong rank-tail canonical Suen packet implies the final-bound
quartic certificate carrier. -/
noncomputable def QuarticCanonicalSuenPacketInputs.toCertificateFamilyInput
    {κ : Type*} [DecidableEq κ] (H : QuarticCanonicalSuenPacketInputs κ) :
    QuarticCertificateFamilyInput :=
  QuarticCertificateFamilyInput.of_canonicalRelaxedEHFanHypotheses
    H.toRelaxedEHFanHypotheses

/-- Quartic optimization theorem from the overstrong rank-tail canonical Suen
packet interface, rather than from a final-bound carrier. -/
theorem thm_EH_quartic_of_canonicalSuenPacket
    {κ : Type*} [DecidableEq κ] (H : QuarticCanonicalSuenPacketInputs κ) :
    ∃ c₄ > (0 : ℝ), ∃ C₄ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      (exceptionalCount N : ℝ) ≤ C₄ * (N : ℝ) * quarticSaving c₄ N :=
  thm_EH_quartic_of_largeRangeInputs H.toLargeRangeInputs

end EscAnalytic
