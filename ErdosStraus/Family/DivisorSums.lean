import ErdosStraus.Estimates.WeightedSums
import ErdosStraus.Family.TotientExpansion
import ErdosStraus.Family.TotientAverage
import ErdosStraus.Family.Definition
import ErdosStraus.Family.Scales

/-!
# Theorem 6.3: divisor sums in residue classes

For the set `E_lin` of divisors `e = r s²` in (12), the sums of `1/rad(e)` and
`1/φ(rad(e))` over `e ≡ c (mod D)` are `≪ M₁/D` and `≪ M_φ/D`, uniformly for `D ≤ Y U` and
`(c, D) = 1`, where `M₁ ≍ M_φ ≍ (log X)²` (Proposition 6.2). Both statements are proved first
without and then with the condition `(rs, m) = 1` in the definition of `E_lin`. For the index
set `I_b`, the exact divisors with a given `d₋`, `D ∣ d₊` and `e ≡ c (mod D)` lie in one
reduced class modulo `D d₋`, so their `1/φ(rad(e))` sum is `≪ M_φ/(D d₋)`.
-/

/-! ## Sums without the condition `(rs, m) = 1` -/

namespace ErdosStraus
namespace ProgressionEstimates

open scoped BigOperators

/-- `∑ 1/φ(rs)` over `e = r s² ≡ c (mod D)` as in (12), without the condition `(rs, m) = 1`. -/
noncomputable def totientResidueMass (P : Params) (X : ℝ) (D c : ℕ) : ℝ := by
  classical
  exact ∑ x ∈ (exactDivisorMassSupport P X).filter
    (fun x => Estimates.congMod (x.2 * x.1 ^ 2) c D),
    (1 : ℝ) / Nat.totient (x.2 * x.1)

/-- `∑ 1/(rs)` over `e = r s² ≡ c (mod D)` as in (12), without the condition `(rs, m) = 1`. -/
noncomputable def reciprocalResidueMass (P : Params) (X : ℝ) (D c : ℕ) : ℝ := by
  classical
  exact ∑ x ∈ (exactDivisorMassSupport P X).filter
    (fun x => Estimates.congMod (x.2 * x.1 ^ 2) c D),
    (1 : ℝ) / ((x.2 * x.1 : ℕ) : ℝ)

theorem coprime_conductor_of_linearized_congruence {r s D c : ℕ}
    (hc : Nat.Coprime c D) (h : Estimates.congMod (r * s ^ 2) c D) :
    Nat.Coprime s D := by
  have hrs : Nat.Coprime (r * s ^ 2) D := Estimates.coprime_of_congMod_left h hc
  apply hrs.coprime_dvd_left
  rw [pow_two]
  exact dvd_mul_of_dvd_right (dvd_mul_right s s) r

theorem quotient_congruence_of_linearized_congruence {r s D c : ℕ}
    (hD : 0 < D) (hs : Nat.Coprime s D)
    (h : Estimates.congMod (r * s ^ 2) c D) :
    Estimates.congMod r (c * exactDivisorInverseSquareResidue D s) D := by
  have hinv := (modInverseChoice_coprime hD hs).pow 2
  have hleft : (r * s ^ 2) * (modInverseChoice D s) ^ 2 ≡ r [MOD D] := by
    have hi := hinv.mul_left r
    simpa [mul_pow, Nat.mul_assoc] using hi
  have hright := (show r * s ^ 2 ≡ c [MOD D] from h).mul_right
    ((modInverseChoice D s) ^ 2)
  show r ≡ c * exactDivisorInverseSquareResidue D s [MOD D]
  simpa [exactDivisorInverseSquareResidue, Nat.ne_of_gt hD] using hleft.symm.trans hright

/-- For fixed `s`, the class `r s² ≡ c (mod D)` is empty unless `(s, D) = 1`, and
then it is the class `r ≡ c s⁻² (mod D)`. Hence the sum of `1/φ(rs)` is at most
`∑_{(s, D) = 1} φ(s)⁻¹ ∑_{r ≡ c s⁻²} φ(r)⁻¹`. -/
theorem totientResidueMass_le_tensor (P : Params) (X : ℝ) {D c : ℕ}
    (hD : 0 < D) (hc : Nat.Coprime c D) :
    totientResidueMass P X D c ≤ exactDivisorMPhiTensorFiberCoprime P X D
      (fun s => c * exactDivisorInverseSquareResidue D s) := by
  classical
  unfold totientResidueMass exactDivisorMassSupport
  rw [Finset.sum_filter, Finset.sum_sigma]
  unfold exactDivisorMPhiTensorFiberCoprime
  apply Finset.sum_le_sum
  intro s hs
  by_cases hsD : Nat.Coprime s D
  · rw [if_pos hsD]
    rw [← Finset.sum_filter]
    unfold phiProgressionAverage
    rw [Finset.mul_sum]
    let R := (phiProgressionSupport P X 1 0 s).filter
      (fun r => Estimates.congMod (r * s ^ 2) c D)
    let T := (Estimates.natWindow (phiProgressionU0 P s X) (phiProgressionU1 P s X)).filter
      (fun r => Squarefree r ∧ Nat.Coprime r s ∧
        Estimates.congMod r (c * exactDivisorInverseSquareResidue D s) D)
    have hsub : R ⊆ T := by
      intro r hr
      obtain ⟨hrS, hrCong⟩ := Finset.mem_filter.mp hr
      obtain ⟨hrW, hrSq, hrCop, _⟩ := Finset.mem_filter.mp hrS
      exact Finset.mem_filter.mpr ⟨hrW, hrSq, hrCop,
        quotient_congruence_of_linearized_congruence hD hsD hrCong⟩
    change (∑ r ∈ R, (1 : ℝ) / Nat.totient (r * s)) ≤
      ∑ r ∈ T, ((1 : ℝ) / Nat.totient s) * ((1 : ℝ) / Nat.totient r)
    calc
      _ = ∑ r ∈ R, ((1 : ℝ) / Nat.totient s) * ((1 : ℝ) / Nat.totient r) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrCop := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.2.1
        rw [Nat.totient_mul hrCop, Nat.cast_mul]
        ring
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro r _ _
        positivity)
  · rw [if_neg hsD]
    have hzero : ∀ r ∈ phiProgressionSupport P X 1 0 s,
        ¬ Estimates.congMod (r * s ^ 2) c D := by
      intro r _ hr
      exact hsD (coprime_conductor_of_linearized_congruence hc hr)
    have hz : (∑ r ∈ phiProgressionSupport P X 1 0 s,
        if Estimates.congMod (r * s ^ 2) c D then (1 : ℝ) / Nat.totient (r * s) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      simp [hzero r hr]
    exact hz.le

theorem reciprocalResidueMass_le_totientResidueMass (P : Params) (X : ℝ) (D c : ℕ) :
    reciprocalResidueMass P X D c ≤ totientResidueMass P X D c := by
  classical
  unfold reciprocalResidueMass totientResidueMass
  apply Finset.sum_le_sum
  intro x hx
  obtain ⟨hxS, _⟩ := Finset.mem_filter.mp hx
  obtain ⟨hs, hr⟩ := Finset.mem_sigma.mp hxS
  have hsN : 0 < x.1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
  have hrN : 0 < x.2 :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1).1
  exact one_div_nat_le_one_div_totient (Nat.mul_pos hrN hsN)

/-- Both residue-class sums are `≪ (log X)²/D`, uniformly for `D ≤ Y U` and `(c, D) = 1`. -/
theorem linearized_residue_masses_wide_upper (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D c : ℕ, 0 < D → Nat.Coprime c D →
        (D : ℝ) ≤ YScale P X * UScale X →
        reciprocalResidueMass P X D c ≤ (C / (D : ℝ)) * (Real.log X) ^ 2 ∧
        totientResidueMass P X D c ≤ (C / (D : ℝ)) * (Real.log X) ^ 2 := by
  obtain ⟨C, X₀, hC, hupper⟩ := exactDivisorMPhiTensorFiberCoprime_wide_upper P
  refine ⟨C, X₀, hC, ?_⟩
  intro X hX D c hD hc hDW
  have htot := (totientResidueMass_le_tensor P X hD hc).trans
    (hupper X hX D hD hDW _ (by
      intro s _ hsD
      exact Nat.Coprime.mul_left hc (exactDivisorInverseSquareResidue_coprime hsD)))
  exact ⟨(reciprocalResidueMass_le_totientResidueMass P X D c).trans htot, htot⟩

/-- Lemma 6.1 for `phiProgressionAverage`. -/
theorem phiProgressionAverage_two_sided (P : Params) :
    PhiProgressionAverageTwoSided P := by
  obtain ⟨c, XL, hc, hl⟩ := PhiProgressionBareLower_of_sqfRecipLower
    (phiProgressionSqfRecipLower P)
  obtain ⟨C, XU, hC, hu⟩ := phiProgressionAverage_small_upper P
  refine ⟨c, C, max XL XU, hc, hC, ?_⟩
  intro X hX d a s hd hdSq hdOdd hdU ha hs hsSq hsd hsS
  exact ⟨phiProgressionAverage_lower_of_bare_lower
    (hl X ((le_max_left _ _).trans hX) d a s hd hdSq hdOdd hdU ha hs hsSq hsd hsS),
    hu X ((le_max_right _ _).trans hX) d a s hd hdU ha hs hsd hsS⟩

theorem exactDivisorM1MassRaw_lower (P : Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      c * (Real.log X) ^ 2 ≤ exactDivisorM1MassRaw P X := by
  obtain ⟨a, XL, ha, hl⟩ := exactDivisorM1MassFiber_lower_of_sqfRecipLower
    (phiProgressionSqfRecipLower P)
  obtain ⟨c, _, XS, hc, _, hs⟩ := exactDivisorM1MassShape_logSq P
  refine ⟨a * c, max XL XS, mul_pos ha hc, ?_⟩
  intro X hX
  rw [exactDivisorM1MassRaw_eq_fiber]
  calc
    (a * c) * (Real.log X) ^ 2 = a * (c * logSq X) := by
      simp only [logSq]
      ring
    _ ≤ a * exactDivisorM1MassShape P X :=
      mul_le_mul_of_nonneg_left (hs X ((le_max_right _ _).trans hX)).1 ha.le
    _ ≤ exactDivisorM1MassFiber P X := hl X ((le_max_left _ _).trans hX)

/-- Proposition 6.2 without the condition `(rs, m) = 1`: `M₁ ≍ M_φ ≍ (log X)²`. -/
theorem quadratic_masses (P : Params) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      (c * (Real.log X) ^ 2 ≤ exactDivisorM1MassRaw P X ∧
        exactDivisorM1MassRaw P X ≤ C * (Real.log X) ^ 2) ∧
      (c * (Real.log X) ^ 2 ≤ exactDivisorMPhiMassRaw P X ∧
        exactDivisorMPhiMassRaw P X ≤ C * (Real.log X) ^ 2) := by
  obtain ⟨c, XL, hc, hl⟩ := exactDivisorM1MassRaw_lower P
  obtain ⟨_, C, Xφ, _, hC, hφ⟩ :=
    exactDivisorMPhiMassRaw_logSq_of_fiberAverageTwoSided
      (exactDivisorMPhiFiber_of_phiProgression
        (phiProgressionAverage_two_sided P))
  refine ⟨c, C, max XL Xφ, hc, hC, ?_⟩
  intro X hX
  have h1 := hl X ((le_max_left _ _).trans hX)
  have h2 : exactDivisorMPhiMassRaw P X ≤ C * (Real.log X) ^ 2 :=
    (hφ X ((le_max_right _ _).trans hX)).2
  have hle := exactDivisorM1MassRaw_le_MPhiMassRaw P X
  exact ⟨⟨h1, hle.trans h2⟩, ⟨h1.trans hle, h2⟩⟩

/-- Theorem 6.3 without the condition `(rs, m) = 1`. -/
theorem linearized_residue_masses_normalized (P : Params) :
    ∃ K X₀ : ℝ, 0 < K ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D c : ℕ, 0 < D → Nat.Coprime c D →
        (D : ℝ) ≤ YScale P X * UScale X →
        reciprocalResidueMass P X D c ≤
          (K / (D : ℝ)) * exactDivisorM1MassRaw P X ∧
        totientResidueMass P X D c ≤
          (K / (D : ℝ)) * exactDivisorMPhiMassRaw P X := by
  obtain ⟨a, _, XM, ha, _, hm⟩ := quadratic_masses P
  obtain ⟨C, XU, hC, hu⟩ := linearized_residue_masses_wide_upper P
  refine ⟨C / a, max XM XU, div_pos hC ha, ?_⟩
  intro X hX D c hD hc hDU
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hmass := hm X ((le_max_left _ _).trans hX)
  have hupper := hu X ((le_max_right _ _).trans hX) D c hD hc hDU
  have hK : 0 ≤ C / a / (D : ℝ) := by positivity
  constructor
  · calc
      reciprocalResidueMass P X D c ≤ (C / (D : ℝ)) * (Real.log X) ^ 2 := hupper.1
      _ = (C / a / (D : ℝ)) * (a * (Real.log X) ^ 2) := by
        field_simp [ne_of_gt ha, ne_of_gt hDR]
      _ ≤ (C / a / (D : ℝ)) * exactDivisorM1MassRaw P X :=
        mul_le_mul_of_nonneg_left hmass.1.1 hK
  · calc
      totientResidueMass P X D c ≤ (C / (D : ℝ)) * (Real.log X) ^ 2 := hupper.2
      _ = (C / a / (D : ℝ)) * (a * (Real.log X) ^ 2) := by
        field_simp [ne_of_gt ha, ne_of_gt hDR]
      _ ≤ (C / a / (D : ℝ)) * exactDivisorMPhiMassRaw P X :=
        mul_le_mul_of_nonneg_left hmass.2.1 hK

end ProgressionEstimates
end ErdosStraus

/-! ## Sums over the family `E_lin` -/

namespace ErdosStraus.FixedNumeratorFamily

open Classical
open scoped BigOperators

/-- `∑_{s ≤ S₀, (s, m) = 1} μ²(s) φ(s)/s²`. -/
noncomputable def coprimeConductorWeight (m : ℕ) (P : Params) (X : ℝ) : ℝ :=
  ∑ s ∈ (Finset.Icc 1 ⌊SScale P X⌋₊).filter
    (fun s => Squarefree s ∧ Nat.Coprime s m), (Nat.totient s : ℝ) / (s : ℝ) ^ 2

theorem coprimeConductorWeight_nonneg (m : ℕ) (P : Params) (X : ℝ) :
    0 ≤ coprimeConductorWeight m P X := by
  exact Finset.sum_nonneg (by intro s _; positivity)

/-- Cauchy–Schwarz over `s ≤ S₀`, as in the proof of Lemma 3.3:
`(∑_{(s, m) = 1} μ²(s)/s)² ≤ (∑_{(s, m) = 1} μ²(s) φ(s)/s²) ∑_s μ²(s)/φ(s)`. -/
theorem conductor_cauchy (m : ℕ) (P : Params) (X : ℝ) :
    Estimates.sAvgRecipCoprime P X m ^ 2 ≤ coprimeConductorWeight m P X *
      ∑ s ∈ exactDivisorSRange P X, (1 : ℝ) / Nat.totient s := by
  let A := (Finset.Icc 1 ⌊SScale P X⌋₊).filter
    (fun s => Squarefree s ∧ Nat.Coprime s m)
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul A
    (r := fun s => (1 : ℝ) / s)
    (f := fun s => (Nat.totient s : ℝ) / (s : ℝ) ^ 2)
    (g := fun s => (1 : ℝ) / Nat.totient s)
    (by intro s _; positivity) (by intro s _; positivity) (by
      intro s hs
      have hspos := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
      have hφ : (Nat.totient s : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hspos).ne'
      exact le_of_eq (by field_simp))
  apply hc.trans
  apply mul_le_mul_of_nonneg_left _ (coprimeConductorWeight_nonneg m P X)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    obtain ⟨hsI, hsq, _⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_filter.mpr ⟨hsI, hsq⟩
  · intro s _ _; positivity

/-- Lemma 3.3 at `T = S₀`: `∑_{(s, m) = 1} μ²(s) φ(s)/s² ≍ log S₀`. -/
theorem coprime_conductor_weight (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * Real.log (SScale P X) ≤ coprimeConductorWeight m P X ∧
      coprimeConductorWeight m P X ≤ C * Real.log (SScale P X) := by
  obtain ⟨a, C, XR, ha, hC, hR⟩ := coprime_conductor_mass m hm P
  obtain ⟨B, hB, hφ⟩ := ProgressionEstimates.exactDivisorSRange_reciprocal_totient_upper P
  refine ⟨a ^ 2 * P.η / B, C, max XR (Real.exp 1),
    div_pos (mul_pos (sq_pos_of_pos ha) P.η_pos) hB, hC, ?_⟩
  intro X hX
  have hXe := (le_max_right XR (Real.exp 1)).trans hX
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hXe
  have hlog : 0 < Real.log X :=
    (by norm_num : (0 : ℝ) < 1).trans_le ((Real.le_log_iff_exp_le hXp).mpr hXe)
  have hlogs : Real.log (SScale P X) = P.η * Real.log X := log_SScale P hXp
  have hR' := hR X ((le_max_left _ _).trans hX)
  have hw := coprimeConductorWeight_nonneg m P X
  have hcs := (conductor_cauchy m P X).trans
    (mul_le_mul_of_nonneg_left (hφ X hXe) hw)
  have hsquare : (a * Real.log (SScale P X)) ^ 2 ≤
      Estimates.sAvgRecipCoprime P X m ^ 2 :=
    pow_le_pow_left₀ (by rw [hlogs]; exact mul_nonneg ha.le (mul_nonneg P.η_pos.le hlog.le)) hR'.1 2
  constructor
  · rw [hlogs] at hsquare ⊢
    have hmul : (a ^ 2 * P.η / B * (P.η * Real.log X)) *
        (B * Real.log X) ≤ coprimeConductorWeight m P X * (B * Real.log X) := by
      calc
        _ = (a * (P.η * Real.log X)) ^ 2 := by field_simp
        _ ≤ _ := hsquare.trans hcs
    exact (mul_le_mul_iff_left₀ (mul_pos hB hlog)).mp hmul
  · apply le_trans _ hR'.2
    apply Finset.sum_le_sum
    intro s hs
    have hspos := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
    have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hspos
    apply (div_le_iff₀ (sq_pos_of_pos hsR)).mpr
    calc
      (Nat.totient s : ℝ) ≤ s := Nat.cast_le.mpr (Nat.totient_le s)
      _ = (1 / (s : ℝ)) * (s : ℝ) ^ 2 := by field_simp

/-- Lemma 3.3: both sums over squarefree `s ≤ T` coprime to `m` are `≍ log T`. -/
theorem conductor_weights (m : ℕ) (hm : 0 < m) :
    ∃ c C T₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ T : ℝ, T₀ ≤ T →
      let A := (Finset.Icc 1 ⌊T⌋₊).filter (fun s => Squarefree s ∧ Nat.Coprime s m)
      (c * Real.log T ≤ ∑ s ∈ A, (Nat.totient s : ℝ) / (s : ℝ) ^ 2 ∧
        (∑ s ∈ A, (Nat.totient s : ℝ) / (s : ℝ) ^ 2) ≤ C * Real.log T) ∧
      (c * Real.log T ≤ ∑ s ∈ A, (1 : ℝ) / s ∧
        (∑ s ∈ A, (1 : ℝ) / s) ≤ C * Real.log T) := by
  let P := Params.explicit
  obtain ⟨c₁, C₁, X₁, hc₁, hC₁, h₁⟩ := coprime_conductor_weight m hm P
  obtain ⟨c₂, C₂, X₂, hc₂, hC₂, h₂⟩ := coprime_conductor_mass m hm P
  let B := max 1 (max X₁ X₂)
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨min c₁ c₂, max C₁ C₂, max 1 (B ^ P.η), lt_min hc₁ hc₂,
    lt_max_of_lt_left hC₁, ?_⟩
  intro T hT
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  have hTp : 0 < T := zero_lt_one.trans_le hT1
  let X := T ^ (1 / P.η)
  have hη : P.η ≠ 0 := P.η_pos.ne'
  have hBX : B ≤ X := by
    have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hB.le P.η)
      ((le_max_right 1 (B ^ P.η)).trans hT)
      (div_nonneg zero_le_one P.η_pos.le)
    rw [← Real.rpow_mul hB.le, show P.η * (1 / P.η) = 1 by field_simp,
      Real.rpow_one] at hpow
    exact hpow
  have hS : SScale P X = T := by
    unfold SScale X
    rw [← Real.rpow_mul hTp.le, show 1 / P.η * P.η = 1 by field_simp,
      Real.rpow_one]
  have h₁' := h₁ X (((le_max_left X₁ X₂).trans (le_max_right 1 _)).trans hBX)
  have h₂' := h₂ X (((le_max_right X₁ X₂).trans (le_max_right 1 _)).trans hBX)
  simp only [coprimeConductorWeight, Estimates.sAvgRecipCoprime, hS] at h₁' h₂'
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
  exact ⟨⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) hlog).trans h₁'.1,
      h₁'.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog)⟩,
    ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _) hlog).trans h₂'.1,
      h₂'.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hlog)⟩⟩

/-- The pairs `(s, r)` with `e = r s² ∈ E_lin`. -/
noncomputable def numeratorDivisorSupport (m : ℕ) (P : Params) (X : ℝ) :
    Finset ((_s : ℕ) × ℕ) :=
  ((exactDivisorSRange P X).filter (fun s => Nat.Coprime s m)).sigma
    (fun s => numeratorRRange m P X 1 0 s)

theorem numeratorDivisorSupport_eq_filter (m : ℕ) (P : Params) (X : ℝ) :
    numeratorDivisorSupport m P X =
      (exactDivisorMassSupport P X).filter (fun x => Nat.Coprime (x.2 * x.1) m) := by
  ext x
  simp only [numeratorDivisorSupport, Finset.mem_sigma, Finset.mem_filter,
    numeratorRRange, exactDivisorMassSupport, phiProgressionSupport,
    Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right]
  tauto

/-- `M₁ = ∑_{e ∈ E_lin} 1/rad(e)`. -/
noncomputable def numeratorM1 (m : ℕ) (P : Params) (X : ℝ) : ℝ :=
  ∑ x ∈ numeratorDivisorSupport m P X, (1 : ℝ) / ((x.2 * x.1 : ℕ) : ℝ)

/-- `M_φ = ∑_{e ∈ E_lin} 1/φ(rad(e))`. -/
noncomputable def numeratorMPhi (m : ℕ) (P : Params) (X : ℝ) : ℝ :=
  ∑ x ∈ numeratorDivisorSupport m P X, (1 : ℝ) / Nat.totient (x.2 * x.1)

theorem numeratorM1_le_MPhi (m : ℕ) (P : Params) (X : ℝ) :
    numeratorM1 m P X ≤ numeratorMPhi m P X := by
  apply Finset.sum_le_sum
  intro x hx
  have hsup : x ∈ exactDivisorMassSupport P X := by
    rw [numeratorDivisorSupport_eq_filter] at hx
    exact (Finset.mem_filter.mp hx).1
  obtain ⟨hs, hr⟩ := Finset.mem_sigma.mp hsup
  have hsp : 0 < x.1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
  have hrp : 0 < x.2 := Nat.pos_of_ne_zero (Finset.mem_filter.mp hr).2.1.ne_zero
  apply one_div_le_one_div_of_le
    (by exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hrp hsp))
  exact_mod_cast Nat.totient_le (x.2 * x.1)

theorem numeratorMPhi_le_ordinary (m : ℕ) (P : Params) (X : ℝ) :
    numeratorMPhi m P X ≤ exactDivisorMPhiMassRaw P X := by
  unfold numeratorMPhi exactDivisorMPhiMassRaw
  rw [numeratorDivisorSupport_eq_filter]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (by intro x _ _; positivity)

theorem numeratorM1_lower (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      c * (Real.log X) ^ 2 ≤ numeratorM1 m P X := by
  obtain ⟨a, XR, ha, hR⟩ := numeratorReciprocalAverage_lower m hm P
  obtain ⟨cL, CL, XL, hcL, hCL, hL⟩ := slantLogLength_uniform_bounds P
  obtain ⟨cW, CW, XW, hcW, hCW, hW⟩ := coprime_conductor_weight m hm P
  refine ⟨a * cL * cW * P.η, max (max XR XL) (max XW (Real.exp 1)),
    mul_pos (mul_pos (mul_pos ha hcL) hcW) P.η_pos, ?_⟩
  intro X hX
  have hXR := (le_max_left XR XL).trans ((le_max_left _ _).trans hX)
  have hXL := (le_max_right XR XL).trans ((le_max_left _ _).trans hX)
  have hXW := (le_max_left XW (Real.exp 1)).trans ((le_max_right _ _).trans hX)
  have hXe := (le_max_right XW (Real.exp 1)).trans ((le_max_right _ _).trans hX)
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hXe
  have hlog : 0 ≤ Real.log X :=
    (by norm_num : (0 : ℝ) ≤ 1).trans ((Real.le_log_iff_exp_le hXp).mpr hXe)
  have hfiber : a * cL * Real.log X * coprimeConductorWeight m P X ≤ numeratorM1 m P X := by
    unfold numeratorM1 numeratorDivisorSupport
    rw [Finset.sum_sigma]
    unfold coprimeConductorWeight
    have hset : (Finset.Icc 1 ⌊SScale P X⌋₊).filter
        (fun s => Squarefree s ∧ Nat.Coprime s m) =
        (exactDivisorSRange P X).filter (fun s => Nat.Coprime s m) := by
      ext s; simp [exactDivisorSRange, and_assoc]
    rw [hset, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    obtain ⟨hsS, hsm⟩ := Finset.mem_filter.mp hs
    obtain ⟨hsI, hsq⟩ := Finset.mem_filter.mp hsS
    obtain ⟨hsp, hsmax⟩ := Finset.mem_Icc.mp hsI
    have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hsp
    have hsScale : (s : ℝ) ≤ SScale P X :=
      (Nat.cast_le.mpr hsmax).trans (Nat.floor_le (Real.rpow_nonneg hXp.le _))
    have hr := hR X hXR s hsp hsq hsScale hsm
    have hlen := (hL X hXL s hsp hsScale).1
    have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ (1 : ℝ) / s by positivity)
    calc
      _ = (1 / (s : ℝ)) * (a * ((Nat.totient s : ℝ) / s) * (cL * Real.log X)) := by ring
      _ ≤ (1 / (s : ℝ)) * (a * ((Nat.totient s : ℝ) / s) * slantLogLength P s X) := by
        gcongr
        exact hlen
      _ ≤ (1 / (s : ℝ)) * (∑ r ∈ numeratorRRange m P X 1 0 s, (1 : ℝ) / r) := hh
      _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r hr; push_cast; ring
  calc
    _ = (a * cL * Real.log X) * (cW * Real.log (SScale P X)) := by
      rw [log_SScale P hXp]; ring
    _ ≤ (a * cL * Real.log X) * coprimeConductorWeight m P X :=
      mul_le_mul_of_nonneg_left (hW X hXW).1 (by positivity)
    _ ≤ _ := hfiber

/-- Proposition 6.2: `M₁ ≍ M_φ ≍ (log X)²`. -/
theorem numerator_quadratic_masses (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      (c * (Real.log X) ^ 2 ≤ numeratorM1 m P X ∧
        numeratorM1 m P X ≤ C * (Real.log X) ^ 2) ∧
      (c * (Real.log X) ^ 2 ≤ numeratorMPhi m P X ∧
        numeratorMPhi m P X ≤ C * (Real.log X) ^ 2) := by
  obtain ⟨c, XL, hc, hl⟩ := numeratorM1_lower m hm P
  obtain ⟨_, C, XU, _, hC, hu⟩ := ProgressionEstimates.quadratic_masses P
  refine ⟨c, C, max XL XU, hc, hC, ?_⟩
  intro X hX
  have hl' := hl X ((le_max_left _ _).trans hX)
  have hu' := (numeratorMPhi_le_ordinary m P X).trans
    (hu X ((le_max_right _ _).trans hX)).2.2
  have hle := numeratorM1_le_MPhi m P X
  exact ⟨⟨hl', hle.trans hu'⟩, ⟨hl'.trans hle, hu'⟩⟩

/-- `∑ 1/rad(e)` over `e ∈ E_lin` with `e ≡ c (mod D)`. -/
noncomputable def numeratorResidueM1 (m : ℕ) (P : Params) (X : ℝ) (D c : ℕ) : ℝ :=
  ∑ x ∈ (numeratorDivisorSupport m P X).filter
    (fun x => Estimates.congMod (x.2 * x.1 ^ 2) c D),
    (1 : ℝ) / ((x.2 * x.1 : ℕ) : ℝ)

/-- `∑ 1/φ(rad(e))` over `e ∈ E_lin` with `e ≡ c (mod D)`. -/
noncomputable def numeratorResidueMPhi (m : ℕ) (P : Params) (X : ℝ) (D c : ℕ) : ℝ :=
  ∑ x ∈ (numeratorDivisorSupport m P X).filter
    (fun x => Estimates.congMod (x.2 * x.1 ^ 2) c D),
    (1 : ℝ) / Nat.totient (x.2 * x.1)

theorem numerator_residue_le_ordinary (m : ℕ) (P : Params) (X : ℝ) (D c : ℕ) :
    numeratorResidueM1 m P X D c ≤ ProgressionEstimates.reciprocalResidueMass P X D c ∧
    numeratorResidueMPhi m P X D c ≤ ProgressionEstimates.totientResidueMass P X D c := by
  have hsub : (numeratorDivisorSupport m P X).filter
      (fun x => Estimates.congMod (x.2 * x.1 ^ 2) c D) ⊆
      (exactDivisorMassSupport P X).filter
        (fun x => Estimates.congMod (x.2 * x.1 ^ 2) c D) := by
    apply Finset.filter_subset_filter
    rw [numeratorDivisorSupport_eq_filter]
    exact Finset.filter_subset _ _
  constructor
  · exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro x _ _; positivity)
  · exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro x _ _; positivity)

/-- Theorem 6.3: the sums over `e ≡ c (mod D)` are `≪ M₁/D` and `≪ M_φ/D`, uniformly for
`D ≤ Y U` and `(c, D) = 1`. -/
theorem numerator_residue_masses_normalized (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ K X₀ : ℝ, 0 < K ∧ ∀ X : ℝ, X₀ ≤ X → ∀ D c : ℕ,
      0 < D → Nat.Coprime c D → (D : ℝ) ≤ YScale P X * UScale X →
      numeratorResidueM1 m P X D c ≤ (K / (D : ℝ)) * numeratorM1 m P X ∧
      numeratorResidueMPhi m P X D c ≤ (K / (D : ℝ)) * numeratorMPhi m P X := by
  obtain ⟨a, _, XM, ha, _, hmass⟩ := numerator_quadratic_masses m hm P
  obtain ⟨C, XU, hC, hu⟩ := ProgressionEstimates.linearized_residue_masses_wide_upper P
  refine ⟨C / a, max XM XU, div_pos hC ha, ?_⟩
  intro X hX D c hD hc hDU
  have hDR : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hM := hmass X ((le_max_left _ _).trans hX)
  have hU := hu X ((le_max_right _ _).trans hX) D c hD hc hDU
  have hsub := numerator_residue_le_ordinary m P X D c
  have hK : 0 ≤ C / a / (D : ℝ) := by positivity
  constructor
  · calc
      _ ≤ (C / (D : ℝ)) * (Real.log X) ^ 2 := hsub.1.trans hU.1
      _ = (C / a / (D : ℝ)) * (a * (Real.log X) ^ 2) := by
        field_simp [ha.ne', hDR.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hM.1.1 hK
  · calc
      _ ≤ (C / (D : ℝ)) * (Real.log X) ^ 2 := hsub.2.trans hU.2
      _ = (C / a / (D : ℝ)) * (a * (Real.log X) ^ 2) := by
        field_simp [ha.ne', hDR.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hM.2.1 hK

end ErdosStraus.FixedNumeratorFamily

/-! ## Exact divisors of `I_b` in residue classes -/

namespace ErdosStraus.FixedNumeratorFamily

open Classical Family
open scoped BigOperators

theorem StaticMem.exactDivisor_mem_support
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (hX : 1 < X) (h : StaticMem m P X Pz b i) :
    (⟨i.E.s, i.E.r⟩ : (_s : ℕ) × ℕ) ∈ exactDivisorMassSupport P X := by
  have hs : (0 : ℝ) < i.E.s := by exact_mod_cast h.s_pos
  have hr : 0 < i.E.r := by
    have hnonneg : 0 ≤ Y0Scale P X / (i.E.s : ℝ) := by
      unfold Y0Scale
      positivity
    exact_mod_cast hnonneg.trans_lt h.r_gt
  apply Finset.mem_sigma.mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨h.s_pos, Nat.le_floor h.s_le_S⟩, i.E.s_squarefree⟩, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨hr, Nat.le_floor h.r_le⟩, h.r_gt⟩, i.E.r_squarefree, i.E.coprime_rs, ?_⟩
  simp [Estimates.congMod, Nat.mod_one]

theorem StaticMem.e_coprime_tensor_modulus
    {m D dminus : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (h : StaticMem m P X Pz b i) (hminus : i.dminus = dminus) (hD : D ∣ i.dplus) :
    Nat.Coprime i.e (D * dminus) := by
  have hdiv : D * dminus ∣ i.dminus * i.dplus := by
    rw [hminus, mul_comm D dminus]
    exact Nat.mul_dvd_mul_left dminus hD
  have hρ : Nat.Coprime (D * dminus) i.rho :=
    (h.dd_coprime_mrho.coprime_dvd_left hdiv).coprime_dvd_right (dvd_mul_left i.rho m)
  exact (hρ.symm.pow_left 2).coprime_dvd_left
    (i.E.e_dvd_sq_of_rho_dvd (dvd_refl i.E.rho))

theorem StaticMem.base_e_congr
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ} {i j : FamilyIndex}
    (hi : StaticMem m P X Pz b i) (hj : StaticMem m P X Pz b j)
    (hdminus : i.dminus = j.dminus) : i.e ≡ j.e [MOD i.dminus] := by
  have hdm := hi.dd_coprime_mrho.coprime_dvd_left (dvd_mul_right i.dminus i.dplus)
  have hmcop : Nat.Coprime m i.dminus :=
    (hdm.coprime_dvd_right (dvd_mul_right m i.rho)).symm
  have hjbase : b + m * j.e ≡ 0 [MOD i.dminus] := by rw [hdminus]; exact hj.base_cong
  exact Nat.ModEq.cancel_left_of_coprime hmcop.symm.gcd_eq_one
    (Nat.ModEq.add_left_cancel' b (hi.base_cong.trans hjbase.symm))

/-- The exact divisors of the indices with a given `d₋`, `D ∣ d₊` and `e ≡ c (mod D)` lie in
one reduced class modulo `D d₋`, the class of any one of them, so their `1/φ(rad(e))` sum is
at most the residue sum of that class. -/
theorem exactValues_recipTotient_le_residueMass
    (m : ℕ) (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X) (hmem : ∀ i ∈ indices, StaticMem m P X Pz b i)
    (D c dminus : ℕ) (hDcop : Nat.Coprime D Pz) :
    ∃ a : ℕ, Nat.Coprime a (D * dminus) ∧
      (∑ E ∈ familyExactValuesAtDminus indices D c dminus,
        (1 : ℝ) / Nat.totient E.rho) ≤
          ProgressionEstimates.totientResidueMass P X (D * dminus) a := by
  classical
  let S := familyExactValuesAtDminus indices D c dminus
  have hpre : ∀ E ∈ S, ∃ i ∈ indices,
      i.E = E ∧ i.dminus = dminus ∧ D ∣ i.dplus ∧ i.e % D = c := by
    intro E hE
    obtain ⟨i, hi, hiE⟩ := Finset.mem_image.mp hE
    obtain ⟨hiI, himinus, hiD, hic⟩ := Finset.mem_filter.mp hi
    exact ⟨i, hiI, hiE, himinus, hiD, hic⟩
  by_cases hS : S.Nonempty
  · obtain ⟨E₀, hE₀⟩ := hS
    obtain ⟨i₀, hi₀, hi₀E, hi₀minus, hi₀D, hi₀c⟩ := hpre E₀ hE₀
    have h₀ := hmem i₀ hi₀
    have ha : Nat.Coprime E₀.e (D * dminus) := by
      simpa only [FamilyIndex.e, hi₀E] using h₀.e_coprime_tensor_modulus hi₀minus hi₀D
    refine ⟨E₀.e, ha, ?_⟩
    let f : ExactDivisor → (_s : ℕ) × ℕ := fun E => ⟨E.s, E.r⟩
    have hinj : Set.InjOn f (S : Set _) := by
      intro E _hE F _hF hEF
      have hs := congrArg Sigma.fst hEF
      have hr := congrArg (fun x : (_s : ℕ) × ℕ => x.2) hEF
      cases E
      cases F
      simp_all [f]
    have hsubset : S.image f ⊆ (exactDivisorMassSupport P X).filter
        (fun x => Estimates.congMod (x.2 * x.1 ^ 2) E₀.e (D * dminus)) := by
      intro x hx
      obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨i, hi, hiE, himinus, hiD, hic⟩ := hpre E hE
      have h := hmem i hi
      have hsupport := h.exactDivisor_mem_support hX
      have hresD : i.e ≡ i₀.e [MOD D] := by
        change i.e % D = i₀.e % D
        exact hic.trans hi₀c.symm
      have hresminus : i.e ≡ i₀.e [MOD dminus] := by
        simpa only [himinus] using h.base_e_congr h₀ (himinus.trans hi₀minus.symm)
      have hDminus : Nat.Coprime D dminus := by
        simpa only [himinus] using hDcop.coprime_dvd_right h.dminus_dvd_Pz
      have hres := (Nat.modEq_and_modEq_iff_modEq_mul hDminus).mp ⟨hresD, hresminus⟩
      apply Finset.mem_filter.mpr
      refine ⟨by simpa only [f, hiE] using hsupport, ?_⟩
      simpa only [f, Estimates.congMod, FamilyIndex.e, ExactDivisor.e, hiE, hi₀E, Nat.ModEq] using hres
    have heq : (∑ E ∈ S, (1 : ℝ) / Nat.totient E.rho) =
        ∑ x ∈ S.image f, (1 : ℝ) / Nat.totient (x.2 * x.1) := by
      rw [Finset.sum_image hinj]
      rfl
    change (∑ E ∈ S, (1 : ℝ) / Nat.totient E.rho) ≤ _
    rw [heq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by intro x _hx _hnot; positivity)
  · refine ⟨1, Nat.coprime_one_left _, ?_⟩
    change (∑ E ∈ S, (1 : ℝ) / Nat.totient E.rho) ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.sum_empty]
    unfold ProgressionEstimates.totientResidueMass
    exact Finset.sum_nonneg (fun _ _ => by positivity)

/-- The sum of `1/φ(rad(e))` over the exact divisors of the indices with a given `d₋ ≤ U`,
`D ∣ d₊` and `e ≡ c (mod D)` is `≪ M_φ/(D d₋)`, for `D ≤ Y` coprime to `P(z)`; here `M_φ`
is taken without the condition `(rs, m) = 1`. -/
theorem exactValues_recipTotient_upper (m : ℕ) (P : Params) :
    ∃ K X₀ : ℝ, 0 < K ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X →
      ∀ Pz b : ℕ, ∀ indices : Finset FamilyIndex,
        (∀ i ∈ indices, StaticMem m P X Pz b i) →
        ∀ D c dminus : ℕ, 0 < D → Nat.Coprime D Pz →
          0 < dminus → (D : ℝ) ≤ YScale P X → (dminus : ℝ) ≤ UScale X →
          (∑ E ∈ familyExactValuesAtDminus indices D c dminus,
            (1 : ℝ) / Nat.totient E.rho) ≤
              (K / ((D : ℝ) * dminus)) * exactDivisorMPhiMassRaw P X := by
  obtain ⟨K, X₀, hK, hu⟩ := ProgressionEstimates.linearized_residue_masses_normalized P
  refine ⟨K, X₀, hK, ?_⟩
  intro X hX hX1 Pz b indices hmem D c dminus hD hDcop hminus hDY hminusU
  obtain ⟨a, ha, hfiber⟩ := exactValues_recipTotient_le_residueMass m P X Pz b indices
    hX1 hmem D c dminus hDcop
  have hrange : ((D * dminus : ℕ) : ℝ) ≤ YScale P X * UScale X := by
    push_cast
    exact mul_le_mul hDY hminusU (Nat.cast_nonneg _) (by unfold YScale; positivity)
  have hh := (hu X hX (D * dminus) a (Nat.mul_pos hD hminus) ha hrange).2
  simpa only [Nat.cast_mul] using hfiber.trans hh

end ErdosStraus.FixedNumeratorFamily
