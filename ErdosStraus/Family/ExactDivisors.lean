import ErdosStraus.Estimates.WeightedSums
import ErdosStraus.Basic

/-!
# Quadratic divisor sums

Sums over the divisors `e = r s²` of (12), without the condition `(rs, m) = 1`: `r` and `s` are
squarefree and coprime, `1 ≤ s ≤ S₀ = X^η` and `U₀ = Y₀/s < r ≤ U₁ = H/s²`. The masses
`M₁ = ∑ 1/(rs)` and `M_φ = ∑ 1/φ(rs)` of Proposition 6.2 are written as sums over `s` of the
progression sums of Lemma 6.1, and compared with `log X ∑_s μ²(s) φ(s)/s²` and
`log X ∑_s μ²(s)/s`, both `≍ (log X)²` by Lemma 3.3. The ingredients for Lemma 6.1 are the
expansion `1/φ(r) = r⁻¹ ∑_{k ∣ r} γ(k)`, the bound `∑_{k ≤ K} γ(k)/k ≤ C_γ` from the Euler
product, and the reduction of the lower bound to Lemma 3.2 through `1/r ≤ 1/φ(r)`.
-/

namespace ErdosStraus

open Filter
open scoped BigOperators

/-! ## Logarithmic scales and the window `(U₀, U₁]` -/

/-- The scale function `X ↦ log X`. -/
noncomputable def logX (X : ℝ) : ℝ := Real.log X

theorem log_SScale (P : Params) {X : ℝ} (hX : 0 < X) :
    Real.log (SScale P X) = P.η * Real.log X := by
  unfold SScale
  rw [Real.log_rpow hX]

theorem log_Y0Scale (P : Params) {X : ℝ} (hX : 0 < X) :
    Real.log (Y0Scale P X) = P.lam * Real.log X := by
  unfold Y0Scale
  rw [Real.log_rpow hX]

theorem log_HScale (P : Params) {X : ℝ} (hX : 0 < X) :
    Real.log (HScale P X) = P.θ * Real.log X := by
  unfold HScale
  rw [Real.log_rpow hX]

/-- `L_s = log(H/(Y₀ s)) = log(U₁/U₀)`, the logarithmic length of the `r`-window of
Lemma 6.1. -/
noncomputable def slantLogLength (P : Params) (s : ℕ) (X : ℝ) : ℝ :=
  Real.log (HScale P X / (Y0Scale P X * (s : ℝ)))

theorem slantLogLength_eq_theta_sub_lam_mul_log_sub_log_nat
    (P : Params) {X : ℝ} {s : ℕ} (hX : 0 < X) (hs : 0 < s) :
    slantLogLength P s X =
      (P.θ - P.lam) * Real.log X - Real.log (s : ℝ) := by
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hHne : HScale P X ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hX P.θ)
  have hYne : Y0Scale P X ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hX P.lam)
  have hsne : (s : ℝ) ≠ 0 := ne_of_gt hsR
  have hden_ne : Y0Scale P X * (s : ℝ) ≠ 0 := mul_ne_zero hYne hsne
  unfold slantLogLength
  rw [Real.log_div hHne hden_ne, Real.log_mul hYne hsne]
  rw [log_HScale P hX, log_Y0Scale P hX]
  ring

/-- `L_s ≥ (θ - λ - η) log X` for `1 ≤ s ≤ S₀`. -/
theorem slantLogLength_ge_theta_sub_lam_sub_eta_mul_log
    (P : Params) {X : ℝ} {s : ℕ} (hX : 1 ≤ X) (hs : 1 ≤ s)
    (hsS : (s : ℝ) ≤ SScale P X) :
    (P.θ - P.lam - P.η) * Real.log X ≤ slantLogLength P s X := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hs_pos : 0 < (s : ℝ) := by exact_mod_cast hs_pos_nat
  have hlogs : Real.log (s : ℝ) ≤ P.η * Real.log X := by
    calc
      Real.log (s : ℝ) ≤ Real.log (SScale P X) :=
        Real.log_le_log hs_pos hsS
      _ = P.η * Real.log X := log_SScale P hXpos
  rw [slantLogLength_eq_theta_sub_lam_mul_log_sub_log_nat P hXpos hs_pos_nat]
  nlinarith

/-- `L_s ≤ (θ - λ) log X` for `s ≥ 1`. -/
theorem slantLogLength_le_theta_sub_lam_mul_log
    (P : Params) {X : ℝ} {s : ℕ} (hX : 1 ≤ X) (hs : 1 ≤ s) :
    slantLogLength P s X ≤ (P.θ - P.lam) * Real.log X := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hs_ge_one : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hlog_s_nonneg : 0 ≤ Real.log (s : ℝ) := Real.log_nonneg hs_ge_one
  rw [slantLogLength_eq_theta_sub_lam_mul_log_sub_log_nat P hXpos hs_pos_nat]
  nlinarith

/-- The lower end `U₀ = Y₀/s` of the `r`-window of Lemma 6.1. -/
noncomputable def phiProgressionU0 (P : Params) (s : ℕ) (X : ℝ) : ℝ :=
  Y0Scale P X / (s : ℝ)

/-- The upper end `U₁ = H/s²` of the `r`-window of Lemma 6.1. -/
noncomputable def phiProgressionU1 (P : Params) (s : ℕ) (X : ℝ) : ℝ :=
  HScale P X / (s : ℝ) ^ (2 : ℕ)

/-- For `1 ≤ s ≤ S₀` the window is long: `U₁/U₀ ≥ X^{θ-λ-η}`, as Lemma 3.2 requires. -/
theorem phiProgression_ratio_ge_rpow_theta_sub_lam_sub_eta
    (P : Params) {X : ℝ} {s : ℕ} (hX : 1 ≤ X) (hs : 1 ≤ s)
    (hsS : (s : ℝ) ≤ SScale P X) :
    X ^ (P.θ - P.lam - P.η) ≤
      phiProgressionU1 P s X / phiProgressionU0 P s X := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hs_pos : 0 < (s : ℝ) := by exact_mod_cast hs_pos_nat
  have hYpos : 0 < Y0Scale P X := Real.rpow_pos_of_pos hXpos P.lam
  have hHpos : 0 < HScale P X := Real.rpow_pos_of_pos hXpos P.θ
  have hSpos : 0 < SScale P X := Real.rpow_pos_of_pos hXpos P.η
  have hU0pos : 0 < phiProgressionU0 P s X := by
    unfold phiProgressionU0
    exact div_pos hYpos hs_pos
  have hsS_pos : 0 < SScale P X := hSpos
  calc
    X ^ (P.θ - P.lam - P.η)
        = X ^ P.θ / (X ^ P.lam * X ^ P.η) := by
          rw [← Real.rpow_add hXpos, ← Real.rpow_sub hXpos]
          ring_nf
    _ = HScale P X / (Y0Scale P X * SScale P X) := by
          unfold HScale Y0Scale SScale
          rfl
    _ ≤ HScale P X / (Y0Scale P X * (s : ℝ)) := by
          exact div_le_div_of_nonneg_left hHpos.le
            (mul_pos hYpos hs_pos) (mul_le_mul_of_nonneg_left hsS hYpos.le)
    _ = phiProgressionU1 P s X / phiProgressionU0 P s X := by
          unfold phiProgressionU1 phiProgressionU0
          field_simp [ne_of_gt hs_pos, ne_of_gt hYpos, ne_of_gt hU0pos,
            ne_of_gt hsS_pos]

/-- `U₀ ≥ X^{λ-η}` for `1 ≤ s ≤ S₀`. -/
theorem phiProgressionU0_ge_rpow_lam_sub_eta
    (P : Params) {X : ℝ} {s : ℕ} (hX : 1 ≤ X) (hs : 1 ≤ s)
    (hsS : (s : ℝ) ≤ SScale P X) :
    X ^ (P.lam - P.η) ≤ phiProgressionU0 P s X := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hs_pos : 0 < (s : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hs
  have hYpos : 0 ≤ Y0Scale P X := (Real.rpow_pos_of_pos hXpos P.lam).le
  unfold phiProgressionU0 Y0Scale SScale at *
  calc
    X ^ (P.lam - P.η) = X ^ P.lam / X ^ P.η := by
      rw [Real.rpow_sub hXpos]
    _ ≤ X ^ P.lam / (s : ℝ) := by
      exact div_le_div_of_nonneg_left hYpos hs_pos hsS

/-- For large `X`, `Y U ≤ X^{λ-η}`, since `η + σ < λ` and `U = (log X)^8 = o(X^δ)` for
every `δ > 0`. This bounds the moduli `D ≤ Y U` of Theorem 6.3. -/
theorem YScale_mul_UScale_le_rpow_lam_sub_eta_eventually (P : Params) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      YScale P X * UScale X ≤ X ^ (P.lam - P.η) := by
  let δ : ℝ := P.lam - P.η - P.σ
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith [P.η_add_σ_lt_lam]
  rcases Estimates.eventually_UScale_le_rpow hδ with ⟨XU, hU⟩
  refine ⟨max XU (Real.exp 1), ?_⟩
  intro X hX
  have hXU : XU ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hY_nonneg : 0 ≤ YScale P X :=
    (Real.rpow_pos_of_pos hXpos P.σ).le
  calc
    YScale P X * UScale X
        ≤ YScale P X * X ^ δ :=
          mul_le_mul_of_nonneg_left (hU X hXU) hY_nonneg
    _ = X ^ (P.lam - P.η) := by
          unfold YScale
          dsimp [δ]
          rw [← Real.rpow_add hXpos]
          ring_nf

/-- For large `X`, every `D ≤ Y U` satisfies `D ≤ U₀ = Y₀/s` for all `1 ≤ s ≤ S₀`. -/
theorem wideModulus_le_phiProgressionU0_eventually (P : Params) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ s D : ℕ, 1 ≤ s → (s : ℝ) ≤ SScale P X →
        (D : ℝ) ≤ YScale P X * UScale X →
          (D : ℝ) ≤ phiProgressionU0 P s X := by
  rcases YScale_mul_UScale_le_rpow_lam_sub_eta_eventually P with
    ⟨XYU, hYU⟩
  refine ⟨max XYU (Real.exp 1), ?_⟩
  intro X hX s D hs hsS hDwide
  have hXYU : XYU ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe
  exact hDwide.trans ((hYU X hXYU).trans
    (phiProgressionU0_ge_rpow_lam_sub_eta P hXone hs hsS))

theorem one_le_phiProgressionU0
    (P : Params) {X : ℝ} {s : ℕ}
    (hXone : 1 ≤ X) (hs : 1 ≤ s) (hsS : (s : ℝ) ≤ SScale P X) :
    1 ≤ phiProgressionU0 P s X := by
  have hexp : 0 ≤ P.lam - P.η := by
    linarith [P.η_add_σ_lt_lam, P.σ_pos]
  exact (Real.one_le_rpow hXone hexp).trans
    (phiProgressionU0_ge_rpow_lam_sub_eta P hXone hs hsS)

theorem phiProgressionU1_le_rpow_theta
    (P : Params) {X : ℝ} {s : ℕ} (hX : 0 < X) (hs : 1 ≤ s) :
    phiProgressionU1 P s X ≤ X ^ P.θ := by
  have hs_ge_one : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hs_sq_ge_one : (1 : ℝ) ≤ (s : ℝ) ^ (2 : ℕ) :=
    one_le_pow₀ hs_ge_one
  have hH_nonneg : 0 ≤ HScale P X :=
    (Real.rpow_pos_of_pos hX P.θ).le
  unfold phiProgressionU1 HScale
  calc
    X ^ P.θ / (s : ℝ) ^ (2 : ℕ)
        ≤ X ^ P.θ / 1 :=
          div_le_div_of_nonneg_left hH_nonneg (by norm_num) hs_sq_ge_one
    _ = X ^ P.θ := by ring

/-- `U₀ < U₁` for `1 ≤ s ≤ S₀` and `X > 1`, since `λ + η < θ`. -/
theorem phiProgressionU0_lt_U1_of_s_le_SScale
    (P : Params) {X : ℝ} {s : ℕ}
    (hX : 1 < X) (hs : 1 ≤ s) (hsS : (s : ℝ) ≤ SScale P X) :
    phiProgressionU0 P s X < phiProgressionU1 P s X := by
  have hXpos : 0 < X := lt_trans zero_lt_one hX
  have hspos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hspos_nat
  have hY0pos : 0 < Y0Scale P X := Real.rpow_pos_of_pos hXpos P.lam
  have hY0S_lt_H : Y0Scale P X * SScale P X < HScale P X := by
    unfold Y0Scale SScale HScale
    calc
      X ^ P.lam * X ^ P.η = X ^ (P.lam + P.η) := by
        rw [← Real.rpow_add hXpos]
      _ < X ^ P.θ :=
        Real.rpow_lt_rpow_of_exponent_lt hX P.lam_add_η_lt_θ
  have hY0s_lt_H : Y0Scale P X * (s : ℝ) < HScale P X :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hsS hY0pos.le) hY0S_lt_H
  have hs_sq_pos : 0 < (s : ℝ) ^ (2 : ℕ) := sq_pos_of_pos hspos
  unfold phiProgressionU0 phiProgressionU1
  calc
    Y0Scale P X / (s : ℝ)
        = (Y0Scale P X * (s : ℝ)) / (s : ℝ) ^ (2 : ℕ) := by
          field_simp [ne_of_gt hspos]
    _ < HScale P X / (s : ℝ) ^ (2 : ℕ) :=
        div_lt_div_of_pos_right hY0s_lt_H hs_sq_pos

/-! ## The progression sums of Lemma 6.1 -/

/-- The squarefree `r ∈ (U₀, U₁]` with `(r, s) = 1` and `r ≡ a (mod d)`. -/
noncomputable def phiProgressionSupport
    (P : Params) (X : ℝ) (d a s : ℕ) : Finset ℕ := by
  classical
  exact
    (Estimates.natWindow (phiProgressionU0 P s X)
      (phiProgressionU1 P s X)).filter
      (fun r => Squarefree r ∧ Nat.Coprime r s ∧ Estimates.congMod r a d)

/-- `∑_{U₀<r≤U₁, r squarefree, (r,s)=1, r≡a (mod d)} 1/r`, a lower bound for the sum of
Lemma 6.1. -/
noncomputable def phiProgressionBareAverage
    (P : Params) (X : ℝ) (d a s : ℕ) : ℝ := by
  classical
  exact
    ∑ r ∈ (Estimates.natWindow (phiProgressionU0 P s X)
        (phiProgressionU1 P s X)).filter
        (fun r => Squarefree r ∧ Nat.Coprime r s ∧ Estimates.congMod r a d),
      (1 : ℝ) / (r : ℝ)

/-- The weight `γ(k) = ∏_{p ∣ k} 1/(p-1)` in the expansion of `1/φ(r)`; it equals
`μ²(k)/φ(k)` for squarefree `k`. -/
noncomputable def phiGammaAF : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p : ℕ => (1 : ℝ) / ((p : ℝ) - 1))

/-- `γ(k)` as a function on `ℕ`. -/
noncomputable def phiGamma (k : ℕ) : ℝ :=
  phiGammaAF k

/-- The partial sum `∑_{1 ≤ k ≤ K} γ(k)/k`; the coefficient sum in (18) is a sub-sum of it. -/
noncomputable def phiGammaDivSum (K : ℕ) : ℝ := by
  classical
  exact ∑ k ∈ Finset.Icc (1 : ℕ) K, phiGamma k / (k : ℝ)

/-- The sum of Lemma 6.1, with `(r, s) = 1` in place of `(r, sm) = 1`:
`∑_{U₀<r≤U₁, r squarefree, (r,s)=1, r≡a (mod d)} 1/φ(r)`. -/
noncomputable def phiProgressionAverage
    (P : Params) (X : ℝ) (d a s : ℕ) : ℝ := by
  classical
  exact
    ∑ r ∈ (Estimates.natWindow (phiProgressionU0 P s X)
        (phiProgressionU1 P s X)).filter
        (fun r => Squarefree r ∧ Nat.Coprime r s ∧ Estimates.congMod r a d),
      (1 : ℝ) / (Nat.totient r : ℝ)

/-- The main term `(1/d) (φ(s)/s) L_s` of Lemma 6.1. -/
noncomputable def phiProgressionAverageShape
    (P : Params) (X : ℝ) (d s : ℕ) : ℝ :=
  ((1 : ℝ) / (d : ℝ)) * ((Nat.totient s : ℝ) / (s : ℝ)) *
    slantLogLength P s X

/-- Lemma 6.1 for `phiProgressionAverage`: uniformly for squarefree odd `d ≤ U`, `(a, d) = 1`
and squarefree `s ≤ S₀` with `(s, d) = 1`, the sum is `≍ (1/d) (φ(s)/s) L_s`. It is proved in
`ProgressionEstimates.phiProgressionAverage_two_sided`. -/
def PhiProgressionAverageTwoSided (P : Params) : Prop :=
  ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ d a s : ℕ,
      0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
      Nat.Coprime a d →
      1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
        c * phiProgressionAverageShape P X d s ≤
            phiProgressionAverage P X d a s ∧
          phiProgressionAverage P X d a s ≤
            C * phiProgressionAverageShape P X d s

/-- The lower bound `≫ (1/d) (φ(s)/s) log(U₁/U₀)` for the sum of `1/r` over the squarefree
`r` of Lemma 6.1. With `1/r ≤ 1/φ(r)` it gives the lower bound of that lemma. -/
def PhiProgressionSqfRecipLower (P : Params) : Prop :=
  ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ d a s : ℕ,
      0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
      Nat.Coprime a d →
      1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
        c * (((1 : ℝ) / (d : ℝ)) * ((Nat.totient s : ℝ) / (s : ℝ)) *
          Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X))
          ≤ Estimates.sqfRecip X s d a
            (phiProgressionU0 P s X) (phiProgressionU1 P s X)

theorem phiProgressionBareAverage_nonneg
    (P : Params) (X : ℝ) (d a s : ℕ) :
    0 ≤ phiProgressionBareAverage P X d a s := by
  classical
  unfold phiProgressionBareAverage
  apply Finset.sum_nonneg
  intro r hr
  have hr_window :
      r ∈ Estimates.natWindow (phiProgressionU0 P s X)
        (phiProgressionU1 P s X) :=
    (Finset.mem_filter.mp hr).1
  have hr_pos_nat : 0 < r := by
    unfold Estimates.natWindow at hr_window
    exact lt_of_lt_of_le Nat.zero_lt_one
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hr_window).1).1
  exact div_nonneg zero_le_one (by exact_mod_cast hr_pos_nat.le)

/-! ## The masses `M₁` and `M_φ`

The divisors are `e = r s²` with `r, s` squarefree and coprime, `s ≤ S₀` and
`Y₀/s < r ≤ H/s²`, so that `ρ(e) = rad(e) = rs`. As in the proof of Proposition 6.2, the sums
of `1/rad(e)` and `1/φ(rad(e))` are written as sums over `s` of `r`-fibres. -/

/-- The squarefree `s ≤ S₀`. -/
noncomputable def exactDivisorSRange (P : Params) (X : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊).filter (fun s => Squarefree s)

/-- The pairs `(s, r)` with `e = r s²` as in (12), without the condition `(rs, m) = 1`. -/
noncomputable def exactDivisorMassSupport
    (P : Params) (X : ℝ) : Finset (Sigma fun _s : ℕ => ℕ) := by
  classical
  exact (exactDivisorSRange P X).sigma
    (fun s => phiProgressionSupport P X 1 0 s)

/-- `M₁ = ∑ 1/rad(e) = ∑ 1/(rs)`. -/
noncomputable def exactDivisorM1MassRaw (P : Params) (X : ℝ) : ℝ := by
  classical
  exact
    ∑ x ∈ exactDivisorMassSupport P X,
      (1 : ℝ) / ((x.2 * x.1 : ℕ) : ℝ)

/-- `M₁` as a sum over `s`: `∑_s (1/s) ∑_r 1/r`. -/
noncomputable def exactDivisorM1MassFiber (P : Params) (X : ℝ) : ℝ := by
  classical
  exact
    ∑ s ∈ exactDivisorSRange P X,
      ((1 : ℝ) / (s : ℝ)) * phiProgressionBareAverage P X 1 0 s

/-- `M_φ = ∑ 1/φ(rad(e)) = ∑ 1/φ(rs)`. -/
noncomputable def exactDivisorMPhiMassRaw (P : Params) (X : ℝ) : ℝ := by
  classical
  exact
    ∑ x ∈ exactDivisorMassSupport P X,
      (1 : ℝ) / (Nat.totient (x.2 * x.1) : ℝ)

/-- `M_φ` as a sum over `s`: `∑_s (1/φ(s)) ∑_r 1/φ(r)`. -/
noncomputable def exactDivisorMPhiMassFiber (P : Params) (X : ℝ) : ℝ := by
  classical
  exact
    ∑ s ∈ exactDivisorSRange P X,
      ((1 : ℝ) / (Nat.totient s : ℝ)) * phiProgressionAverage P X 1 0 s

/-- The main term `∑_s L_s/s` of `M_φ`, obtained by replacing each `r`-fibre by
`(φ(s)/s) L_s`. -/
noncomputable def exactDivisorMPhiMassShape (P : Params) (X : ℝ) : ℝ := by
  classical
  exact
    ∑ s ∈ exactDivisorSRange P X,
      ((1 : ℝ) / (s : ℝ)) * slantLogLength P s X

/-- The main term `∑_s φ(s) L_s/s²` of `M₁`, obtained by replacing each `r`-fibre by
`(φ(s)/s) L_s`. -/
noncomputable def exactDivisorM1MassShape (P : Params) (X : ℝ) : ℝ := by
  classical
  exact
    ∑ s ∈ exactDivisorSRange P X,
      ((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) * slantLogLength P s X

theorem exactDivisorM1MassRaw_eq_fiber (P : Params) (X : ℝ) :
    exactDivisorM1MassRaw P X = exactDivisorM1MassFiber P X := by
  classical
  unfold exactDivisorM1MassRaw exactDivisorM1MassFiber exactDivisorMassSupport
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro s hs
  unfold phiProgressionBareAverage phiProgressionSupport
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hspos : 0 < s :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
  have hssqf : Squarefree s := (Finset.mem_filter.mp hs).2
  have hwin :
      r ∈ Estimates.natWindow (phiProgressionU0 P s X)
        (phiProgressionU1 P s X) :=
    (Finset.mem_filter.mp hr).1
  have hdata := (Finset.mem_filter.mp hr).2
  have hrsqf : Squarefree r := hdata.1
  have hcop : Nat.Coprime r s := hdata.2.1
  have hrpos : 0 < r := by
    unfold Estimates.natWindow at hwin
    exact lt_of_lt_of_le Nat.zero_lt_one
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hwin).1).1
  let E : ExactDivisor :=
    { r := r
      s := s
      r_squarefree := hrsqf
      s_squarefree := hssqf
      coprime_rs := hcop }
  have hfactor := ExactDivisor.one_div_rho_cast_eq E hrpos hspos
  have hfactor' :
      (1 : ℝ) / ((r * s : ℕ) : ℝ) =
        ((1 : ℝ) / (r : ℝ)) * ((1 : ℝ) / (s : ℝ)) := by
    simpa [E, ExactDivisor.rho] using hfactor
  change (1 : ℝ) / ((r * s : ℕ) : ℝ) =
    ((1 : ℝ) / (s : ℝ)) * ((1 : ℝ) / (r : ℝ))
  rw [hfactor']
  ring

theorem exactDivisorMPhiMassRaw_eq_fiber (P : Params) (X : ℝ) :
    exactDivisorMPhiMassRaw P X = exactDivisorMPhiMassFiber P X := by
  classical
  unfold exactDivisorMPhiMassRaw exactDivisorMPhiMassFiber exactDivisorMassSupport
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro s hs
  unfold phiProgressionAverage phiProgressionSupport
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hspos : 0 < s :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
  have hssqf : Squarefree s := (Finset.mem_filter.mp hs).2
  have hwin :
      r ∈ Estimates.natWindow (phiProgressionU0 P s X)
        (phiProgressionU1 P s X) :=
    (Finset.mem_filter.mp hr).1
  have hdata := (Finset.mem_filter.mp hr).2
  have hrsqf : Squarefree r := hdata.1
  have hcop : Nat.Coprime r s := hdata.2.1
  have hrpos : 0 < r := by
    unfold Estimates.natWindow at hwin
    exact lt_of_lt_of_le Nat.zero_lt_one
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hwin).1).1
  let E : ExactDivisor :=
    { r := r
      s := s
      r_squarefree := hrsqf
      s_squarefree := hssqf
      coprime_rs := hcop }
  have hfactor := ExactDivisor.one_div_totient_rho_cast_eq E hrpos hspos
  have hfactor' :
      (1 : ℝ) / (Nat.totient (r * s) : ℝ) =
        ((1 : ℝ) / (Nat.totient r : ℝ)) *
          ((1 : ℝ) / (Nat.totient s : ℝ)) := by
    simpa [E, ExactDivisor.rho] using hfactor
  change (1 : ℝ) / (Nat.totient (r * s) : ℝ) =
    ((1 : ℝ) / (Nat.totient s : ℝ)) *
      ((1 : ℝ) / (Nat.totient r : ℝ))
  rw [hfactor']
  ring

theorem exactDivisorMPhiMassShape_nonneg
    (P : Params) {X : ℝ} (hX : Real.exp 1 ≤ X) :
    0 ≤ exactDivisorMPhiMassShape P X := by
  classical
  unfold exactDivisorMPhiMassShape
  apply Finset.sum_nonneg
  intro s hs
  have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
    (Finset.mem_filter.mp hs).1
  have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
  have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hX
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hS_nonneg : 0 ≤ SScale P X := (Real.rpow_pos_of_pos hXpos P.η).le
  have hsS : (s : ℝ) ≤ SScale P X :=
    le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
  have hslant_nonneg :
      0 ≤ slantLogLength P s X := by
    have hlog_nonneg : 0 ≤ Real.log X := Real.log_nonneg hXone
    have hlower :=
      slantLogLength_ge_theta_sub_lam_sub_eta_mul_log P hXone hs_one hsS
    have hcoef_pos : 0 < P.θ - P.lam - P.η := by
      linarith [P.lam_add_η_lt_θ]
    nlinarith
  exact mul_nonneg (div_nonneg zero_le_one (by exact_mod_cast (Nat.zero_le s)))
    hslant_nonneg

theorem exactDivisorMPhiMassShape_lower_logX_sAvgRecip
    (P : Params) {X : ℝ} (hX : Real.exp 1 ≤ X) :
    (P.θ - P.lam - P.η) * logX X * Estimates.sAvgRecip P X
      ≤ exactDivisorMPhiMassShape P X := by
  classical
  unfold exactDivisorMPhiMassShape Estimates.sAvgRecip exactDivisorSRange
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
    (Finset.mem_filter.mp hs).1
  have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
  have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hX
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hS_nonneg : 0 ≤ SScale P X := (Real.rpow_pos_of_pos hXpos P.η).le
  have hsS : (s : ℝ) ≤ SScale P X :=
    le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
  have hslant :=
    slantLogLength_ge_theta_sub_lam_sub_eta_mul_log P hXone hs_one hsS
  have hs_nonneg : 0 ≤ (1 : ℝ) / (s : ℝ) :=
    div_nonneg zero_le_one (by exact_mod_cast (Nat.zero_le s))
  unfold logX
  calc
    ((P.θ - P.lam - P.η) * Real.log X) * ((1 : ℝ) / (s : ℝ))
        = ((1 : ℝ) / (s : ℝ)) * ((P.θ - P.lam - P.η) * Real.log X) := by ring
    _ ≤ ((1 : ℝ) / (s : ℝ)) * slantLogLength P s X :=
        mul_le_mul_of_nonneg_left hslant hs_nonneg

theorem exactDivisorMPhiMassShape_upper_logX_sAvgRecip
    (P : Params) {X : ℝ} (hX : Real.exp 1 ≤ X) :
    exactDivisorMPhiMassShape P X
      ≤ (P.θ - P.lam) * logX X * Estimates.sAvgRecip P X := by
  classical
  unfold exactDivisorMPhiMassShape Estimates.sAvgRecip exactDivisorSRange
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
    (Finset.mem_filter.mp hs).1
  have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hX
  have hslant :=
    slantLogLength_le_theta_sub_lam_mul_log P hXone hs_one
  have hs_nonneg : 0 ≤ (1 : ℝ) / (s : ℝ) :=
    div_nonneg zero_le_one (by exact_mod_cast (Nat.zero_le s))
  unfold logX
  calc
    ((1 : ℝ) / (s : ℝ)) * slantLogLength P s X
        ≤ ((1 : ℝ) / (s : ℝ)) * ((P.θ - P.lam) * Real.log X) :=
          mul_le_mul_of_nonneg_left hslant hs_nonneg
    _ = ((P.θ - P.lam) * Real.log X) * ((1 : ℝ) / (s : ℝ)) := by ring

theorem exactDivisorM1MassShape_nonneg
    (P : Params) {X : ℝ} (hX : Real.exp 1 ≤ X) :
    0 ≤ exactDivisorM1MassShape P X := by
  classical
  unfold exactDivisorM1MassShape
  apply Finset.sum_nonneg
  intro s hs
  have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
    (Finset.mem_filter.mp hs).1
  have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
  have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hX
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hS_nonneg : 0 ≤ SScale P X := (Real.rpow_pos_of_pos hXpos P.η).le
  have hsS : (s : ℝ) ≤ SScale P X :=
    le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
  have hslant_nonneg :
      0 ≤ slantLogLength P s X := by
    have hlog_nonneg : 0 ≤ Real.log X := Real.log_nonneg hXone
    have hlower :=
      slantLogLength_ge_theta_sub_lam_sub_eta_mul_log P hXone hs_one hsS
    have hcoef_pos : 0 < P.θ - P.lam - P.η := by
      linarith [P.lam_add_η_lt_θ]
    nlinarith
  have hcoef_nonneg :
      0 ≤ (Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ) :=
    div_nonneg (by exact_mod_cast Nat.zero_le (Nat.totient s))
      (sq_nonneg (s : ℝ))
  exact mul_nonneg hcoef_nonneg hslant_nonneg

theorem exactDivisorM1MassShape_lower_logX_sAvgPhi
    (P : Params) {X : ℝ} (hX : Real.exp 1 ≤ X) :
    (P.θ - P.lam - P.η) * logX X * Estimates.sAvgPhi P X
      ≤ exactDivisorM1MassShape P X := by
  classical
  unfold exactDivisorM1MassShape Estimates.sAvgPhi exactDivisorSRange
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
    (Finset.mem_filter.mp hs).1
  have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
  have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hX
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hS_nonneg : 0 ≤ SScale P X := (Real.rpow_pos_of_pos hXpos P.η).le
  have hsS : (s : ℝ) ≤ SScale P X :=
    le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
  have hslant :=
    slantLogLength_ge_theta_sub_lam_sub_eta_mul_log P hXone hs_one hsS
  have hcoef_nonneg :
      0 ≤ (Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ) :=
    div_nonneg (by exact_mod_cast Nat.zero_le (Nat.totient s))
      (sq_nonneg (s : ℝ))
  unfold logX
  calc
    ((P.θ - P.lam - P.η) * Real.log X) *
        ((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ))
        =
        ((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) *
          ((P.θ - P.lam - P.η) * Real.log X) := by ring
    _ ≤ ((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) *
          slantLogLength P s X :=
        mul_le_mul_of_nonneg_left hslant hcoef_nonneg

theorem exactDivisorM1MassShape_upper_logX_sAvgPhi
    (P : Params) {X : ℝ} (hX : Real.exp 1 ≤ X) :
    exactDivisorM1MassShape P X
      ≤ (P.θ - P.lam) * logX X * Estimates.sAvgPhi P X := by
  classical
  unfold exactDivisorM1MassShape Estimates.sAvgPhi exactDivisorSRange
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
    (Finset.mem_filter.mp hs).1
  have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hX
  have hslant :=
    slantLogLength_le_theta_sub_lam_mul_log P hXone hs_one
  have hcoef_nonneg :
      0 ≤ (Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ) :=
    div_nonneg (by exact_mod_cast Nat.zero_le (Nat.totient s))
      (sq_nonneg (s : ℝ))
  unfold logX
  calc
    ((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) *
        slantLogLength P s X
        ≤ ((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) *
          ((P.θ - P.lam) * Real.log X) :=
          mul_le_mul_of_nonneg_left hslant hcoef_nonneg
    _ = ((P.θ - P.lam) * Real.log X) *
          ((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) := by ring

/-! ## The weights `γ(k)` -/

theorem phiGammaAF_multiplicative :
    phiGammaAF.IsMultiplicative := by
  unfold phiGammaAF
  exact ArithmeticFunction.IsMultiplicative.prodPrimeFactors
    (R := ℝ) (fun p : ℕ => (1 : ℝ) / ((p : ℝ) - 1))

theorem phiGammaAF_apply_prime {p : ℕ} (hp : Nat.Prime p) :
    phiGammaAF p = (1 : ℝ) / ((p : ℝ) - 1) := by
  unfold phiGammaAF
  rw [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors]
  simp

theorem phiGamma_eq_primeFactorProduct {k : ℕ} (hk : k ≠ 0) :
    phiGamma k = ∏ p ∈ k.primeFactors, (1 : ℝ) / ((p : ℝ) - 1) := by
  unfold phiGamma phiGammaAF
  exact ArithmeticFunction.prodPrimeFactors_apply (R := ℝ)
    (f := fun p : ℕ => (1 : ℝ) / ((p : ℝ) - 1)) hk

theorem phiGamma_nonneg (k : ℕ) :
    0 ≤ phiGamma k := by
  by_cases hk : k = 0
  · simp [phiGamma, phiGammaAF, hk]
  · rw [phiGamma_eq_primeFactorProduct hk]
    apply Finset.prod_nonneg
    intro p hp
    have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hp_gt_one : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.one_lt
    exact div_nonneg zero_le_one (sub_nonneg.mpr hp_gt_one.le)

/-- The partial sums of `∑_k γ(k)/k` are bounded. -/
def PhiGammaDivSummableBound : Prop :=
  ∃ Cgamma : ℝ, 0 < Cgamma ∧ ∀ K : ℕ, phiGammaDivSum K ≤ Cgamma

theorem phiGamma_prime_pow_succ {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    phiGamma (p ^ (e + 1)) = (1 : ℝ) / ((p : ℝ) - 1) := by
  rw [phiGamma_eq_primeFactorProduct (pow_ne_zero (e + 1) hp.ne_zero)]
  rw [Nat.primeFactors_pow p (Nat.succ_ne_zero e)]
  simp [hp.primeFactors]

/-- The local factor of `∑ γ(k)/k` at `p`, without its constant term:
`∑_{e ≥ 1} γ(p^e)/p^e = 1/(p-1)²`. -/
theorem phiGamma_primePowerDiv_positive_tsum {p : ℕ} (hp : Nat.Prime p) :
    (∑' e : ℕ, phiGamma (p ^ (e + 1)) / ((p ^ (e + 1) : ℕ) : ℝ)) =
      (1 : ℝ) / (((p : ℝ) - 1) ^ 2) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_one_lt : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp_pred_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp_inv_nonneg : 0 ≤ (1 : ℝ) / (p : ℝ) :=
    div_nonneg zero_le_one hp_pos.le
  have hp_inv_lt_one : (1 : ℝ) / (p : ℝ) < 1 := by
    rw [div_lt_one hp_pos]
    exact hp_one_lt
  calc
    (∑' e : ℕ, phiGamma (p ^ (e + 1)) / ((p ^ (e + 1) : ℕ) : ℝ))
        = ∑' e : ℕ,
            ((1 : ℝ) / ((p : ℝ) - 1)) * ((1 : ℝ) / (p : ℝ)) ^ (e + 1) := by
          apply tsum_congr
          intro e
          rw [phiGamma_prime_pow_succ hp e]
          rw [Nat.cast_pow]
          field_simp [ne_of_gt hp_pos, ne_of_gt hp_pred_pos]
          rw [← mul_pow, mul_one_div_cancel (ne_of_gt hp_pos), one_pow]
    _ = ((1 : ℝ) / ((p : ℝ) - 1)) *
          ∑' e : ℕ, ((1 : ℝ) / (p : ℝ)) ^ (e + 1) := by
          rw [tsum_mul_left]
    _ = ((1 : ℝ) / ((p : ℝ) - 1)) *
          (((1 : ℝ) / (p : ℝ)) * ∑' e : ℕ, ((1 : ℝ) / (p : ℝ)) ^ e) := by
          congr 1
          rw [← tsum_mul_left]
          apply tsum_congr
          intro e
          rw [pow_succ']
    _ = ((1 : ℝ) / ((p : ℝ) - 1)) *
          (((1 : ℝ) / (p : ℝ)) * (1 - (1 : ℝ) / (p : ℝ))⁻¹) := by
          rw [tsum_geometric_of_lt_one hp_inv_nonneg hp_inv_lt_one]
    _ = (1 : ℝ) / (((p : ℝ) - 1) ^ 2) := by
          field_simp [ne_of_gt hp_pos, ne_of_gt hp_pred_pos]

theorem phiGamma_primePowerDiv_positive_summable {p : ℕ} (hp : Nat.Prime p) :
    Summable (fun e : ℕ =>
      phiGamma (p ^ (e + 1)) / ((p ^ (e + 1) : ℕ) : ℝ)) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_one_lt : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp_pred_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp_inv_nonneg : 0 ≤ (1 : ℝ) / (p : ℝ) :=
    div_nonneg zero_le_one hp_pos.le
  have hp_inv_lt_one : (1 : ℝ) / (p : ℝ) < 1 := by
    rw [div_lt_one hp_pos]
    exact hp_one_lt
  have hgeom : Summable (fun e : ℕ => ((1 : ℝ) / (p : ℝ)) ^ e) :=
    summable_geometric_of_lt_one hp_inv_nonneg hp_inv_lt_one
  have hshift :
      Summable (fun e : ℕ => ((1 : ℝ) / (p : ℝ)) ^ (e + 1)) := by
    simpa [pow_succ'] using hgeom.mul_left ((1 : ℝ) / (p : ℝ))
  refine hshift.mul_left ((1 : ℝ) / ((p : ℝ) - 1)) |>.congr ?_
  intro e
  rw [phiGamma_prime_pow_succ hp e]
  rw [Nat.cast_pow]
  field_simp [ne_of_gt hp_pos, ne_of_gt hp_pred_pos]
  rw [← mul_pow, one_div_mul_cancel (ne_of_gt hp_pos), one_pow]

theorem phiGamma_primePowerDiv_positive_norm_summable {p : ℕ} (hp : Nat.Prime p) :
    Summable (fun e : ℕ =>
      ‖phiGamma (p ^ (e + 1)) / ((p ^ (e + 1) : ℕ) : ℝ)‖) := by
  simpa only [Real.norm_eq_abs] using
    (phiGamma_primePowerDiv_positive_summable hp).abs

theorem phiGamma_primePowerDiv_norm_summable {p : ℕ} (hp : Nat.Prime p) :
    Summable (fun e : ℕ =>
      ‖phiGamma (p ^ e) / ((p ^ e : ℕ) : ℝ)‖) := by
  have htail := phiGamma_primePowerDiv_positive_norm_summable hp
  exact (_root_.summable_nat_add_iff
    (f := fun e : ℕ => ‖phiGamma (p ^ e) / ((p ^ e : ℕ) : ℝ)‖) 1).1 htail

/-- The coefficient `γ(k)/k` of (18). -/
noncomputable def phiGammaDivCoeff (k : ℕ) : ℝ :=
  phiGamma k / (k : ℝ)

theorem phiGammaDivCoeff_one :
    phiGammaDivCoeff 1 = 1 := by
  unfold phiGammaDivCoeff
  rw [phiGamma_eq_primeFactorProduct (by norm_num : (1 : ℕ) ≠ 0)]
  simp

theorem phiGammaDivCoeff_mul_of_coprime {m n : ℕ}
    (h : Nat.Coprime m n) :
    phiGammaDivCoeff (m * n) =
      phiGammaDivCoeff m * phiGammaDivCoeff n := by
  unfold phiGammaDivCoeff
  rw [show phiGamma (m * n) = phiGamma m * phiGamma n by
    exact phiGammaAF_multiplicative.map_mul_of_coprime h]
  rw [Nat.cast_mul]
  by_cases hm : (m : ℝ) = 0
  · have hmnat : m = 0 := by exact_mod_cast hm
    subst m
    simp
  · by_cases hn : (n : ℝ) = 0
    · have hnnat : n = 0 := by exact_mod_cast hn
      subst n
      simp
    · field_simp [hm, hn]

theorem phiGammaDivCoeff_primePower_norm_summable {p : ℕ} (hp : Nat.Prime p) :
    Summable (fun e : ℕ => ‖phiGammaDivCoeff (p ^ e)‖) := by
  simpa [phiGammaDivCoeff] using phiGamma_primePowerDiv_norm_summable hp

/-- The Euler factor `1 + 1/(p-1)²` of `∑ γ(k)/k` at `p`. -/
noncomputable def phiGammaDivCoeffLocalFactor (p : ℕ) : ℝ :=
  (1 : ℝ) + (1 : ℝ) / (((p : ℝ) - 1) ^ 2)

theorem phiGammaDivCoeff_primePower_tsum {p : ℕ} (hp : Nat.Prime p) :
    (∑' e : ℕ, phiGammaDivCoeff (p ^ e)) = phiGammaDivCoeffLocalFactor p := by
  have hsum : Summable (fun e : ℕ => phiGammaDivCoeff (p ^ e)) :=
    (phiGammaDivCoeff_primePower_norm_summable hp).of_norm
  rw [hsum.tsum_eq_zero_add]
  simp only [pow_zero]
  rw [phiGammaDivCoeff_one]
  have htail :
      (∑' e : ℕ, phiGammaDivCoeff (p ^ (e + 1))) =
        (1 : ℝ) / (((p : ℝ) - 1) ^ 2) := by
    simpa [phiGammaDivCoeff] using phiGamma_primePowerDiv_positive_tsum hp
  rw [htail]
  rfl

/-- The Euler product of `∑ γ(k)/k` over the integers whose prime factors lie in `s`. -/
theorem phiGammaDivCoeff_finiteEulerProduct (s : Finset ℕ) :
    Summable (fun m : Nat.factoredNumbers s => ‖phiGammaDivCoeff m‖) ∧
      HasSum (fun m : Nat.factoredNumbers s => phiGammaDivCoeff m)
        (∏ p ∈ s with p.Prime, ∑' e : ℕ, phiGammaDivCoeff (p ^ e)) := by
  exact EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := phiGammaDivCoeff)
    phiGammaDivCoeff_one
    (fun {m n} h => phiGammaDivCoeff_mul_of_coprime h)
    (fun {p} hp => phiGammaDivCoeff_primePower_norm_summable hp)
    s

/-- The same Euler product, with the local factors `1 + 1/(p-1)²`. -/
theorem phiGammaDivCoeff_finiteEulerProduct_localFactors (s : Finset ℕ) :
    Summable (fun m : Nat.factoredNumbers s => ‖phiGammaDivCoeff m‖) ∧
      HasSum (fun m : Nat.factoredNumbers s => phiGammaDivCoeff m)
        (∏ p ∈ Finset.filter (fun p : ℕ => Nat.Prime p) s,
          phiGammaDivCoeffLocalFactor p) := by
  rcases phiGammaDivCoeff_finiteEulerProduct s with ⟨hsum, hhas⟩
  refine ⟨hsum, ?_⟩
  have hprod :
      (∏ p ∈ Finset.filter (fun p : ℕ => Nat.Prime p) s,
          ∑' e : ℕ, phiGammaDivCoeff (p ^ e)) =
        (∏ p ∈ Finset.filter (fun p : ℕ => Nat.Prime p) s,
          phiGammaDivCoeffLocalFactor p) := by
    exact Finset.prod_congr rfl (by
      intro p hp
      exact phiGammaDivCoeff_primePower_tsum (Finset.mem_filter.mp hp).2)
  rw [← hprod]
  exact hhas

theorem phiGammaDivCoeff_nonneg (k : ℕ) :
    0 ≤ phiGammaDivCoeff k := by
  unfold phiGammaDivCoeff
  exact div_nonneg (phiGamma_nonneg k) (Nat.cast_nonneg k)

theorem mem_factoredNumbers_primesBelow_succ_of_pos_le
    {K k : ℕ} (hk_pos : 1 ≤ k) (hk_le : k ≤ K) :
    k ∈ Nat.factoredNumbers ((K + 1).primesBelow) := by
  rw [Nat.mem_factoredNumbers']
  intro p hp hpdvd
  rw [Nat.mem_primesBelow]
  have hp_le_k : p ≤ k := Nat.le_of_dvd (Nat.succ_le_iff.mp hk_pos) hpdvd
  exact ⟨lt_of_le_of_lt (le_trans hp_le_k hk_le) (Nat.lt_succ_self K), hp⟩

/-- `∑_{k ≤ K} γ(k)/k ≤ ∏_{p ≤ K} (1 + 1/(p-1)²)`. -/
theorem phiGammaDivSum_le_finiteEulerProduct (K : ℕ) :
    phiGammaDivSum K ≤
      ∏ p ∈ Finset.filter (fun p : ℕ => Nat.Prime p) ((K + 1).primesBelow),
        phiGammaDivCoeffLocalFactor p := by
  classical
  let primes : Finset ℕ := (K + 1).primesBelow
  let S : Finset {k : ℕ // k ∈ Finset.Icc (1 : ℕ) K} := (Finset.Icc (1 : ℕ) K).attach
  let f : {k : ℕ // k ∈ Finset.Icc (1 : ℕ) K} → Nat.factoredNumbers primes :=
    fun k => ⟨k.1, by
      have hk := Finset.mem_Icc.mp k.2
      exact mem_factoredNumbers_primesBelow_succ_of_pos_le
        (K := K) (k := k.1) hk.1 hk.2⟩
  have hinj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y := by
    intro x _hx y _hy hxy
    apply Subtype.ext
    exact congrArg (fun z : Nat.factoredNumbers primes => (z : ℕ)) hxy
  have hsum_image :
      (∑ x ∈ S, phiGammaDivCoeff (f x)) =
        ∑ m ∈ S.image f, phiGammaDivCoeff m := by
    rw [Finset.sum_image]
    exact hinj
  have hattach :
      phiGammaDivSum K = ∑ x ∈ S, phiGammaDivCoeff (f x) := by
    unfold phiGammaDivSum phiGammaDivCoeff
    change (∑ k ∈ Finset.Icc (1 : ℕ) K, phiGamma k / (k : ℝ)) =
      ∑ x ∈ (Finset.Icc (1 : ℕ) K).attach, phiGamma x.1 / ((x.1 : ℕ) : ℝ)
    rw [← Finset.sum_attach]
  rcases phiGammaDivCoeff_finiteEulerProduct_localFactors primes with ⟨hsum_norm, hhas⟩
  have hsum : Summable (fun m : Nat.factoredNumbers primes => phiGammaDivCoeff m) :=
    hsum_norm.of_norm
  have hpartial :
      (∑ m ∈ S.image f, phiGammaDivCoeff m) ≤
        ∑' m : Nat.factoredNumbers primes, phiGammaDivCoeff m :=
    Summable.sum_le_tsum (S.image f)
      (fun m _hm => phiGammaDivCoeff_nonneg m)
      hsum
  calc
    phiGammaDivSum K = ∑ x ∈ S, phiGammaDivCoeff (f x) := hattach
    _ = ∑ m ∈ S.image f, phiGammaDivCoeff m := hsum_image
    _ ≤ ∑' m : Nat.factoredNumbers primes, phiGammaDivCoeff m := hpartial
    _ = ∏ p ∈ Finset.filter (fun p : ℕ => Nat.Prime p) primes,
        phiGammaDivCoeffLocalFactor p := hhas.tsum_eq
    _ = ∏ p ∈ Finset.filter (fun p : ℕ => Nat.Prime p) ((K + 1).primesBelow),
        phiGammaDivCoeffLocalFactor p := by rfl

theorem phiGammaDivCoeffLocalFactor_nonneg (p : ℕ) :
    0 ≤ phiGammaDivCoeffLocalFactor p := by
  unfold phiGammaDivCoeffLocalFactor
  positivity

/-- `∏_p (1 + 1/(p-1)²) ≤ exp(∑_p 1/(p-1)²)` over the primes of `s`. -/
theorem finiteEulerProduct_le_exp_primePredSqSum (s : Finset ℕ) :
    (∏ p ∈ Finset.filter (fun p : ℕ => Nat.Prime p) s,
        phiGammaDivCoeffLocalFactor p) ≤
      Real.exp
        (∑ p ∈ Finset.filter (fun p : ℕ => Nat.Prime p) s,
          (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) := by
  classical
  calc
    (∏ p ∈ Finset.filter (fun p : ℕ => Nat.Prime p) s,
        phiGammaDivCoeffLocalFactor p)
        ≤ ∏ p ∈ Finset.filter (fun p : ℕ => Nat.Prime p) s,
            Real.exp ((1 : ℝ) / (((p : ℝ) - 1) ^ 2)) := by
          apply Finset.prod_le_prod
          · intro p _hp
            exact phiGammaDivCoeffLocalFactor_nonneg p
          · intro p _hp
            unfold phiGammaDivCoeffLocalFactor
            simpa [one_div, add_comm] using
              Real.add_one_le_exp ((((p : ℝ) - 1) ^ 2)⁻¹)
    _ = Real.exp
        (∑ p ∈ Finset.filter (fun p : ℕ => Nat.Prime p) s,
          (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) := by
          rw [Real.exp_sum]

/-- The series `∑_p 1/(p-1)²` converges. -/
def PhiGammaPrimePredSqSummable : Prop :=
  Summable (fun p : Nat.Primes => (1 : ℝ) / (((p : ℝ) - 1) ^ 2))

/-- `∑_p 1/(p-1)²` converges, by comparison with `4 ∑_p p⁻²`. -/
theorem phiGamma_primePredSqSummable :
    PhiGammaPrimePredSqSummable := by
  have hsq : Summable (fun p : Nat.Primes => (1 : ℝ) / ((p : ℝ) ^ 2)) := by
    have hsq' : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-2 : ℝ)) :=
      Nat.Primes.summable_rpow.mpr (by norm_num)
    convert hsq' using 1
    ext p
    rw [Real.rpow_neg (by positivity)]
    norm_num
  refine (hsq.mul_left 4).of_nonneg_of_le ?_ ?_
  · intro p
    positivity
  · intro p
    have hp_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
    have hpred_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hmain :
        (1 : ℝ) / (((p : ℝ) - 1) ^ 2) ≤ 4 / ((p : ℝ) ^ 2) := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hpred_pos) (sq_pos_of_pos hp_pos)]
      nlinarith [sq_nonneg ((p : ℝ) - 2)]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmain

theorem primePredSqFiniteSum_le_tsum (s : Finset ℕ) :
    (∑ p ∈ Finset.filter (fun p : ℕ => Nat.Prime p) s,
          (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) ≤
      ∑' p : Nat.Primes, (1 : ℝ) / (((p : ℝ) - 1) ^ 2) := by
  classical
  let S : Finset ℕ := Finset.filter (fun p : ℕ => Nat.Prime p) s
  let f : {p : ℕ // p ∈ S} → Nat.Primes :=
    fun p => ⟨p.1, (Finset.mem_filter.mp p.2).2⟩
  have hinj : ∀ x ∈ S.attach, ∀ y ∈ S.attach, f x = f y → x = y := by
    intro x _hx y _hy hxy
    apply Subtype.ext
    exact congrArg (fun z : Nat.Primes => (z : ℕ)) hxy
  have hsum_image :
      (∑ x ∈ S.attach, (1 : ℝ) / (((f x : ℕ) : ℝ) - 1) ^ 2) =
        ∑ p ∈ S.attach.image f, (1 : ℝ) / ((((p : ℕ) : ℝ) - 1) ^ 2) := by
    rw [Finset.sum_image]
    exact hinj
  have hattach :
      (∑ p ∈ S, (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) =
        ∑ x ∈ S.attach, (1 : ℝ) / (((f x : ℕ) : ℝ) - 1) ^ 2 := by
    change (∑ p ∈ S, (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) =
      ∑ x ∈ S.attach, (1 : ℝ) / (((x.1 : ℝ) - 1) ^ 2)
    rw [← Finset.sum_attach]
  have hpartial :
      (∑ p ∈ S.attach.image f, (1 : ℝ) / ((((p : ℕ) : ℝ) - 1) ^ 2)) ≤
        ∑' p : Nat.Primes, (1 : ℝ) / (((p : ℝ) - 1) ^ 2) := by
    exact Summable.sum_le_tsum (S.attach.image f)
      (fun p _hp => by positivity)
      phiGamma_primePredSqSummable
  calc
    (∑ p ∈ Finset.filter (fun p : ℕ => Nat.Prime p) s,
          (1 : ℝ) / (((p : ℝ) - 1) ^ 2))
        = ∑ p ∈ S, (1 : ℝ) / (((p : ℝ) - 1) ^ 2) := by rfl
    _ = ∑ x ∈ S.attach, (1 : ℝ) / (((f x : ℕ) : ℝ) - 1) ^ 2 := hattach
    _ = ∑ p ∈ S.attach.image f, (1 : ℝ) / ((((p : ℕ) : ℝ) - 1) ^ 2) := hsum_image
    _ ≤ ∑' p : Nat.Primes, (1 : ℝ) / (((p : ℝ) - 1) ^ 2) := hpartial

theorem finiteEulerProduct_le_exp_primePredSqTsum (s : Finset ℕ) :
    (∏ p ∈ Finset.filter (fun p : ℕ => Nat.Prime p) s,
        phiGammaDivCoeffLocalFactor p) ≤
      Real.exp (∑' p : Nat.Primes, (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) := by
  calc
    (∏ p ∈ Finset.filter (fun p : ℕ => Nat.Prime p) s,
        phiGammaDivCoeffLocalFactor p)
        ≤ Real.exp
            (∑ p ∈ Finset.filter (fun p : ℕ => Nat.Prime p) s,
              (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) :=
          finiteEulerProduct_le_exp_primePredSqSum s
    _ ≤ Real.exp (∑' p : Nat.Primes, (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) :=
          Real.exp_le_exp.mpr (primePredSqFiniteSum_le_tsum s)

/-- `∑_{k ≤ K} γ(k)/k ≤ exp(∑_p 1/(p-1)²)` for every `K`. -/
theorem phiGammaDivSum_le_exp_primePredSqTsum (K : ℕ) :
    phiGammaDivSum K ≤
      Real.exp (∑' p : Nat.Primes, (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) := by
  calc
    phiGammaDivSum K
        ≤ ∏ p ∈ Finset.filter (fun p : ℕ => Nat.Prime p) ((K + 1).primesBelow),
            phiGammaDivCoeffLocalFactor p :=
          phiGammaDivSum_le_finiteEulerProduct K
    _ ≤ Real.exp (∑' p : Nat.Primes, (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) :=
          finiteEulerProduct_le_exp_primePredSqTsum ((K + 1).primesBelow)

/-- The partial sums of `∑ γ(k)/k` are bounded, by the finite Euler product and
the summability of `∑_p 1/(p-1)²`. -/
theorem PhiGammaDivSummableBound_concrete :
    PhiGammaDivSummableBound := by
  refine ⟨Real.exp (∑' p : Nat.Primes,
    (1 : ℝ) / (((p : ℝ) - 1) ^ 2)), Real.exp_pos _, ?_⟩
  intro K
  exact phiGammaDivSum_le_exp_primePredSqTsum K

/-- For squarefree `r`, `∑_{k ∣ r} γ(k) = ∏_{p ∣ r} (1 + 1/(p-1))`. -/
theorem phiGamma_divisor_sum_eq_prime_product {r : ℕ} (hr : Squarefree r) :
    ∑ k ∈ r.divisors, phiGamma k =
      ∏ p ∈ r.primeFactors, (1 + (1 : ℝ) / ((p : ℝ) - 1)) := by
  have h :=
    phiGammaAF_multiplicative.prodPrimeFactors_one_add_of_squarefree
      (n := r) hr
  unfold phiGamma
  rw [← h]
  apply Finset.prod_congr rfl
  intro p hp
  rw [phiGammaAF_apply_prime (Nat.prime_of_mem_primeFactors hp)]

theorem one_div_totient_eq_one_div_nat_mul_prime_product {r : ℕ} (hr : 0 < r) :
    (1 : ℝ) / (Nat.totient r : ℝ) =
      (1 / (r : ℝ)) *
        ∏ p ∈ r.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hprod := Estimates.totient_div_eq_totientPrimeFactorProduct (n := r) hr
  have hprod_unfold :
      (Nat.totient r : ℝ) / (r : ℝ) =
        ∏ p ∈ r.primeFactors, (1 - (p : ℝ)⁻¹) := by
    simpa [Estimates.totientPrimeFactorProduct] using hprod
  have hr_ne : (r : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  have hphi_pos : (0 : ℝ) < (Nat.totient r : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hr
  have hprod_ne : (∏ p ∈ r.primeFactors, (1 - (p : ℝ)⁻¹)) ≠ 0 := by
    rw [← hprod_unfold]
    exact div_ne_zero (ne_of_gt hphi_pos) hr_ne
  calc
    (1 : ℝ) / (Nat.totient r : ℝ)
        = (1 / (r : ℝ)) *
            ((Nat.totient r : ℝ) / (r : ℝ))⁻¹ := by
              field_simp [hr_ne, ne_of_gt hphi_pos]
    _ = (1 / (r : ℝ)) *
          (∏ p ∈ r.primeFactors, (1 - (p : ℝ)⁻¹))⁻¹ := by
              rw [hprod_unfold]
    _ = (1 / (r : ℝ)) *
          ∏ p ∈ r.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
              rw [Finset.prod_inv_distrib]

theorem primeFactor_one_sub_inv_inv_eq_one_add_inv_pred
    {r p : ℕ} (hp : p ∈ r.primeFactors) :
    (1 - (p : ℝ)⁻¹)⁻¹ = 1 + (1 : ℝ) / ((p : ℝ) - 1) := by
  have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_gt_one : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.one_lt
  have hp_ne : (p : ℝ) ≠ 0 := by positivity
  have hp_pred_ne : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp_gt_one.ne'
  field_simp [hp_ne, hp_pred_ne]
  ring

/-- The expansion `1/φ(r) = r⁻¹ ∑_{k ∣ r} γ(k)` for squarefree `r`, which gives (18). -/
theorem one_div_totient_eq_one_div_nat_mul_phiGamma_sum
    {r : ℕ} (hr : Squarefree r) :
    (1 : ℝ) / (Nat.totient r : ℝ) =
      (1 / (r : ℝ)) * ∑ k ∈ r.divisors, phiGamma k := by
  have hr_pos : 0 < r := Nat.pos_of_ne_zero hr.ne_zero
  rw [one_div_totient_eq_one_div_nat_mul_prime_product hr_pos]
  congr 1
  calc
    (∏ p ∈ r.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹)
        = ∏ p ∈ r.primeFactors, (1 + (1 : ℝ) / ((p : ℝ) - 1)) := by
            apply Finset.prod_congr rfl
            intro p hp
            exact primeFactor_one_sub_inv_inv_eq_one_add_inv_pred hp
    _ = ∑ k ∈ r.divisors, phiGamma k :=
            (phiGamma_divisor_sum_eq_prime_product hr).symm

/-! ## The lower bound of Lemma 6.1 -/

theorem one_div_nat_le_one_div_totient {r : ℕ} (hr : 0 < r) :
    (1 : ℝ) / (r : ℝ) ≤ (1 : ℝ) / (Nat.totient r : ℝ) := by
  have htot_pos_nat : 0 < Nat.totient r := Nat.totient_pos.mpr hr
  have htot_pos : (0 : ℝ) < (Nat.totient r : ℝ) := by exact_mod_cast htot_pos_nat
  have htot_le_nat : Nat.totient r ≤ r := Nat.totient_le r
  have htot_le : (Nat.totient r : ℝ) ≤ (r : ℝ) := by exact_mod_cast htot_le_nat
  exact one_div_le_one_div_of_le htot_pos htot_le

theorem phiProgressionBareAverage_le_phiProgressionAverage
    (P : Params) (X : ℝ) (d a s : ℕ) :
    phiProgressionBareAverage P X d a s ≤
      phiProgressionAverage P X d a s := by
  classical
  unfold phiProgressionBareAverage phiProgressionAverage
  apply Finset.sum_le_sum
  intro r hr
  have hr_window :
      r ∈ Estimates.natWindow (phiProgressionU0 P s X)
        (phiProgressionU1 P s X) :=
    (Finset.mem_filter.mp hr).1
  have hr_pos_nat : 0 < r := by
    unfold Estimates.natWindow at hr_window
    exact lt_of_lt_of_le Nat.zero_lt_one
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hr_window).1).1
  exact one_div_nat_le_one_div_totient hr_pos_nat

/-- The sum of `1/r` is the squarefree reciprocal sum `Estimates.sqfRecip` with coprimality
modulus `s`. -/
theorem phiProgressionBareAverage_eq_sqfRecip
    (P : Params) (X : ℝ) (d a s : ℕ) :
    phiProgressionBareAverage P X d a s =
      Estimates.sqfRecip X s d a
        (phiProgressionU0 P s X) (phiProgressionU1 P s X) := by
  rfl

theorem log_phiProgressionU1_div_U0_eq_slantLogLength
    (P : Params) {X : ℝ} {s : ℕ} (hX : 0 < X) (hs : 0 < s) :
    Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) =
      slantLogLength P s X := by
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hs)
  have hY0_pos : 0 < Y0Scale P X := Real.rpow_pos_of_pos hX P.lam
  have hY0_ne : Y0Scale P X ≠ 0 := ne_of_gt hY0_pos
  unfold phiProgressionU1 phiProgressionU0 slantLogLength
  congr 1
  field_simp [hsR, hY0_ne]

theorem phiProgressionAverage_lower_of_bare_lower
    {P : Params} {X : ℝ} {d a s : ℕ} {c : ℝ}
    (hbare : c * phiProgressionAverageShape P X d s ≤
      phiProgressionBareAverage P X d a s) :
    c * phiProgressionAverageShape P X d s ≤
      phiProgressionAverage P X d a s :=
  le_trans hbare (phiProgressionBareAverage_le_phiProgressionAverage P X d a s)

/-- The lower bound of Lemma 6.1 for the sum of `1/r`. -/
def PhiProgressionBareLower (P : Params) : Prop :=
  ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ d a s : ℕ,
      0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
      Nat.Coprime a d →
      1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
        c * phiProgressionAverageShape P X d s ≤
          phiProgressionBareAverage P X d a s

/-- The lower bound of Lemma 6.1 for the sum of `1/r`, from the squarefree reciprocal lower
bound and `log(U₁/U₀) = L_s`. -/
theorem PhiProgressionBareLower_of_sqfRecipLower
    {P : Params} (h : PhiProgressionSqfRecipLower P) :
    PhiProgressionBareLower P := by
  rcases h with ⟨c, Xbase, hc, hlower⟩
  refine ⟨c, max Xbase 1, hc, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  have hXbase : Xbase ≤ X := le_trans (le_max_left Xbase 1) hX
  have hXone : (1 : ℝ) ≤ X := le_trans (le_max_right Xbase 1) hX
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hsqf :
      c * (((1 : ℝ) / (d : ℝ)) * ((Nat.totient s : ℝ) / (s : ℝ)) *
          Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X))
        ≤ Estimates.sqfRecip X s d a
          (phiProgressionU0 P s X) (phiProgressionU1 P s X) :=
    hlower X hXbase d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS
  simpa [phiProgressionBareAverage_eq_sqfRecip,
    phiProgressionAverageShape,
    log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos] using hsqf

/-- Lower bound `≫ (1/D)(φ(M)/M) log(U₁/U₀)` for the sum of `1/n` over
squarefree `n` with `(n,M)=1` and `n ≡ b (mod D)`, on windows
`X^a₀ ≤ U₀ < U₁ ≤ X^b₀` with `U₁/U₀ ≥ X^c₀`; this is the Möbius calculation in
the proof of Lemma 3.2. -/
def OrdinarySquarefreeProgressionCoprimeDensityLowerLong
    (a₀ b₀ c₀ C₀ : ℝ) : Prop :=
  ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ M D b : ℕ, 0 < D → Squarefree M → Squarefree D →
      Nat.Coprime M D → Nat.Coprime b D →
      (M : ℝ) ≤ X ^ C₀ → (D : ℝ) ≤ UScale X →
      ∀ U₀ U₁ : ℝ, X ^ a₀ ≤ U₀ → U₀ < U₁ → 1 ≤ U₁ → U₁ ≤ X ^ b₀ →
        X ^ c₀ ≤ U₁ / U₀ →
        c * (((1 : ℝ) / (D : ℝ)) *
          ((Nat.totient M : ℝ) / (M : ℝ)) * Real.log (U₁ / U₀)) ≤
          Estimates.sqfRecip X M D b U₀ U₁

/-- The long-window squarefree lower bound implies
`PhiProgressionSqfRecipLower`; the window condition `U₁/U₀ ≥ X^c₀` holds with
`c₀ = θ-λ-η`. -/
theorem PhiProgressionSqfRecipLower_of_ordinary_long
    {P : Params}
    (hordinary :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η) :
    PhiProgressionSqfRecipLower P := by
  rcases hordinary with ⟨c, Xbase, hc, hbound⟩
  refine ⟨c, max Xbase (Real.exp 1), hc, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  have hXbase : Xbase ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXexp
  have hXgtone : (1 : ℝ) < X :=
    lt_of_lt_of_le (by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)) hXexp
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hM_scale : (s : ℝ) ≤ X ^ P.η := by
    simpa [SScale] using hsS
  have hU0_scale :
      X ^ (P.lam - P.η) ≤ phiProgressionU0 P s X :=
    phiProgressionU0_ge_rpow_lam_sub_eta P hXone hs_one hsS
  have hU1_scale :
      phiProgressionU1 P s X ≤ X ^ P.θ :=
    phiProgressionU1_le_rpow_theta P hXpos hs_one
  have hU01 :
      phiProgressionU0 P s X < phiProgressionU1 P s X :=
    phiProgressionU0_lt_U1_of_s_le_SScale P hXgtone hs_one hsS
  have hU0_one : (1 : ℝ) ≤ phiProgressionU0 P s X :=
    one_le_phiProgressionU0 P hXone hs_one hsS
  have hratio :
      X ^ (P.θ - P.lam - P.η) ≤
        phiProgressionU1 P s X / phiProgressionU0 P s X :=
    phiProgression_ratio_ge_rpow_theta_sub_lam_sub_eta P hXone hs_one hsS
  exact
    hbound X hXbase s d a hd_pos hs_sqf hd_sqf hs_coprime ha_coprime
      hM_scale hdU
      (phiProgressionU0 P s X) (phiProgressionU1 P s X)
      hU0_scale hU01 (hU0_one.trans hU01.le) hU1_scale hratio

/-- The long-window squarefree lower bound of Lemma 3.2. -/
theorem sqfRecip_lower_long
    (a₀ b₀ c₀ C₀ : ℝ) (ha₀ : 0 < a₀) (hc₀ : 0 < c₀) :
    OrdinarySquarefreeProgressionCoprimeDensityLowerLong a₀ b₀ c₀ C₀ := by
  simpa [OrdinarySquarefreeProgressionCoprimeDensityLowerLong,
    Estimates.OrdinarySquarefreeProgressionCoprimeDensityLowerLong] using
    Estimates.ordinary_squarefree_progression_coprime_density_lower_long a₀ b₀ c₀ C₀ ha₀ hc₀

/-- `PhiProgressionSqfRecipLower` holds, with window exponents `a₀ = λ-η`,
`b₀ = θ`, `c₀ = θ-λ-η` and conductor exponent `C₀ = η`. -/
theorem phiProgressionSqfRecipLower
    (P : Params) :
    PhiProgressionSqfRecipLower P :=
  PhiProgressionSqfRecipLower_of_ordinary_long
    (sqfRecip_lower_long
      (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η
      (by linarith [P.η_add_σ_lt_lam, P.σ_pos])
      (by linarith [P.lam_add_η_lt_θ]))

/-! ## Comparison with the main terms -/

theorem phiProgressionAverage_bounds_of_twoSided
    {P : Params} (hφ : PhiProgressionAverageTwoSided P) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          c * phiProgressionAverageShape P X d s ≤
              phiProgressionAverage P X d a s ∧
            phiProgressionAverage P X d a s ≤
              C * phiProgressionAverageShape P X d s :=
  hφ

/-- The case `d = 1` of Lemma 6.1: for squarefree `1 ≤ s ≤ S₀`, the `r`-fibre of `M_φ` is
`≍ (φ(s)/s) L_s`. This is the estimate for `M_φ` in Proposition 6.2. -/
def ExactDivisorMPhiFiberAverageTwoSided (P : Params) : Prop :=
  ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ s : ℕ, 1 ≤ s → Squarefree s → (s : ℝ) ≤ SScale P X →
      c * (((Nat.totient s : ℝ) / (s : ℝ)) * slantLogLength P s X) ≤
          phiProgressionAverage P X 1 0 s ∧
        phiProgressionAverage P X 1 0 s ≤
          C * (((Nat.totient s : ℝ) / (s : ℝ)) * slantLogLength P s X)

/-- A fixed `d` satisfies `d ≤ U = (log X)^8` for large `X`. -/
theorem fixedNat_le_UScale_eventually (d : ℕ) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → (d : ℝ) ≤ UScale X := by
  have hU : Tendsto (fun X : ℝ => UScale X) atTop atTop := by
    unfold UScale
    exact (tendsto_pow_atTop (by norm_num : (8 : ℕ) ≠ 0)).comp
      Real.tendsto_log_atTop
  rcases Filter.eventually_atTop.mp
      (hU.eventually (Filter.eventually_ge_atTop (d : ℝ))) with
    ⟨X₀, hX₀⟩
  exact ⟨X₀, fun X hX => hX₀ X hX⟩

/-- Lemma 6.1 with `d = 1` gives `ExactDivisorMPhiFiberAverageTwoSided`. -/
theorem exactDivisorMPhiFiber_of_phiProgression
    {P : Params} (hφ : PhiProgressionAverageTwoSided P) :
    ExactDivisorMPhiFiberAverageTwoSided P := by
  rcases phiProgressionAverage_bounds_of_twoSided hφ with
    ⟨c, C, Xφ, hc, hC, hbounds⟩
  rcases fixedNat_le_UScale_eventually 1 with ⟨XU, hU⟩
  refine ⟨c, C, max (max Xφ XU) (Real.exp 1), hc, hC, ?_⟩
  intro X hX s hs_one hs_sqf hsS
  have hXφ : Xφ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXU : XU ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hU1 : ((1 : ℕ) : ℝ) ≤ UScale X := hU X hXU
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hbounds_s :=
    hbounds X hXφ 1 0 s (by norm_num) squarefree_one
      (by exact ⟨0, by norm_num⟩) hU1 (by norm_num)
      hs_one hs_sqf (Nat.coprime_one_right s) hsS
  simpa [phiProgressionAverageShape,
    log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos] using hbounds_s

/-- Given the `d = 1` fibre estimate, `M_φ` is comparable to its main term
`∑_s μ²(s) L_s/s`. -/
theorem exactDivisorMPhiMassFiber_asymp_shape
    {P : Params} (hφ : ExactDivisorMPhiFiberAverageTwoSided P) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X ∧
        exactDivisorMPhiMassFiber P X ≤ C * exactDivisorMPhiMassShape P X := by
  classical
  rcases hφ with ⟨c, C, Xφ, hc, hC, hbounds⟩
  refine ⟨c, C, max Xφ (Real.exp 1), hc, hC, ?_⟩
  intro X hX
  have hXφ : Xφ ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hS_nonneg : 0 ≤ SScale P X := (Real.rpow_pos_of_pos hXpos P.η).le
  constructor
  · unfold exactDivisorMPhiMassShape exactDivisorMPhiMassFiber exactDivisorSRange
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
      (Finset.mem_filter.mp hs).1
    have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
    have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
    have hssqf : Squarefree s := (Finset.mem_filter.mp hs).2
    have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
    have hsS : (s : ℝ) ≤ SScale P X :=
      le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
    have hbounds_s := hbounds X hXφ s hs_one hssqf hsS
    have htot_pos_nat : 0 < Nat.totient s := Nat.totient_pos.mpr hs_pos_nat
    have htot_pos : 0 < (Nat.totient s : ℝ) := by exact_mod_cast htot_pos_nat
    have hscale_nonneg : 0 ≤ (1 : ℝ) / (Nat.totient s : ℝ) :=
      div_nonneg zero_le_one htot_pos.le
    calc
      c * ((1 : ℝ) / (s : ℝ) * slantLogLength P s X)
          = ((1 : ℝ) / (Nat.totient s : ℝ)) *
              (c * (((Nat.totient s : ℝ) / (s : ℝ)) *
                slantLogLength P s X)) := by
            field_simp [ne_of_gt htot_pos,
              ne_of_gt (by exact_mod_cast hs_pos_nat : (0 : ℝ) < s)]
      _ ≤ ((1 : ℝ) / (Nat.totient s : ℝ)) *
            phiProgressionAverage P X 1 0 s :=
          mul_le_mul_of_nonneg_left hbounds_s.1 hscale_nonneg
  · unfold exactDivisorMPhiMassShape exactDivisorMPhiMassFiber exactDivisorSRange
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
      (Finset.mem_filter.mp hs).1
    have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
    have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
    have hssqf : Squarefree s := (Finset.mem_filter.mp hs).2
    have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
    have hsS : (s : ℝ) ≤ SScale P X :=
      le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
    have hbounds_s := hbounds X hXφ s hs_one hssqf hsS
    have htot_pos_nat : 0 < Nat.totient s := Nat.totient_pos.mpr hs_pos_nat
    have htot_pos : 0 < (Nat.totient s : ℝ) := by exact_mod_cast htot_pos_nat
    have hscale_nonneg : 0 ≤ (1 : ℝ) / (Nat.totient s : ℝ) :=
      div_nonneg zero_le_one htot_pos.le
    calc
      ((1 : ℝ) / (Nat.totient s : ℝ)) *
          phiProgressionAverage P X 1 0 s
          ≤ ((1 : ℝ) / (Nat.totient s : ℝ)) *
              (C * (((Nat.totient s : ℝ) / (s : ℝ)) *
                slantLogLength P s X)) :=
            mul_le_mul_of_nonneg_left hbounds_s.2 hscale_nonneg
      _ = C * ((1 : ℝ) / (s : ℝ) * slantLogLength P s X) := by
            field_simp [ne_of_gt htot_pos,
              ne_of_gt (by exact_mod_cast hs_pos_nat : (0 : ℝ) < s)]

/-- Uniformly for `1 ≤ s ≤ S₀`, `(θ - λ - η) log X ≤ L_s ≤ (θ - λ) log X`, as in the proof
of Proposition 6.2; the lower constant is positive since `λ + η < θ`. This is the comparison
`L_s ≍ log X` used in Lemma 6.5. -/
theorem slantLogLength_uniform_bounds (P : Params) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → ∀ s : ℕ,
      1 ≤ s → (s : ℝ) ≤ SScale P X →
        c * logX X ≤ slantLogLength P s X ∧ slantLogLength P s X ≤ C * logX X := by
  refine ⟨P.θ - P.lam - P.η, P.θ - P.lam, Real.exp 1, ?_, ?_, ?_⟩
  · linarith [P.lam_add_η_lt_θ]
  · linarith [P.lam_add_η_lt_θ, P.η_pos]
  intro X hX s hs hsS
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hlogX_nonneg : 0 ≤ Real.log X := by
    have hXge1 : (1 : ℝ) ≤ X := by
      exact le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hX
    exact Real.log_nonneg hXge1
  have hspos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hspos_nat
  have hs_ge_one_real : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hlog_s_nonneg : 0 ≤ Real.log (s : ℝ) := Real.log_nonneg hs_ge_one_real
  have hSpos : 0 < SScale P X := Real.rpow_pos_of_pos hXpos P.η
  have hlog_s_le_logS : Real.log (s : ℝ) ≤ Real.log (SScale P X) :=
    Real.log_le_log hspos hsS
  have hlog_s_le_eta : Real.log (s : ℝ) ≤ P.η * Real.log X := by
    simpa [log_SScale P hXpos] using hlog_s_le_logS
  have hY0pos : 0 < Y0Scale P X := Real.rpow_pos_of_pos hXpos P.lam
  have hHpos : 0 < HScale P X := Real.rpow_pos_of_pos hXpos P.θ
  have hdenpos : 0 < Y0Scale P X * (s : ℝ) := mul_pos hY0pos hspos
  have hlen_eq :
      slantLogLength P s X = (P.θ - P.lam) * Real.log X - Real.log (s : ℝ) := by
    unfold slantLogLength
    rw [Real.log_div (ne_of_gt hHpos) (ne_of_gt hdenpos)]
    rw [Real.log_mul (ne_of_gt hY0pos) (ne_of_gt hspos)]
    rw [log_HScale P hXpos, log_Y0Scale P hXpos]
    ring
  unfold logX
  rw [hlen_eq]
  constructor
  · nlinarith [hlog_s_le_eta]
  · nlinarith [hlog_s_nonneg]

/-- `∑_{s ≤ S₀} μ²(s)/s ≍ log S₀ = η log X` (Lemma 3.3). The factor `η` is absorbed into the
constants, and the threshold is at least `e`, so that `log X > 0`. -/
noncomputable def sAvgRecip_asymp (P : Params) :
    FactorAsymp (fun X => Estimates.sAvgRecip P X) logX where
  c := P.η * (Estimates.s_average_recip P).choose
  C := P.η * (Estimates.s_average_recip P).choose_spec.choose
  X₀ := max (Estimates.s_average_recip P).choose_spec.choose_spec.choose (Real.exp 1)
  c_pos := mul_pos P.η_pos (Estimates.s_average_recip P).choose_spec.choose_spec.choose_spec.1
  C_pos := mul_pos P.η_pos (Estimates.s_average_recip P).choose_spec.choose_spec.choose_spec.2.1
  f_nonneg := fun X _ => Estimates.sAvgRecip_nonneg P X
  sandwich := fun X hX => by
    have hX0' : (Estimates.s_average_recip P).choose_spec.choose_spec.choose ≤ X :=
      le_trans (le_max_left _ _) hX
    have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
    have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
    have hsand :=
      (Estimates.s_average_recip P).choose_spec.choose_spec.choose_spec.2.2 X hX0'
    rw [log_SScale P hXpos] at hsand
    obtain ⟨hlo, hhi⟩ := hsand
    refine ⟨?_, ?_⟩
    · have : (Estimates.s_average_recip P).choose * (P.η * Real.log X)
              ≤ Estimates.sAvgRecip P X := hlo
      unfold logX
      linarith [this]
    · have : Estimates.sAvgRecip P X
              ≤ (Estimates.s_average_recip P).choose_spec.choose * (P.η * Real.log X) := hhi
      unfold logX
      linarith [this]

/-- `∑_{s ≤ S₀} μ²(s) φ(s)/s² ≍ log S₀ = η log X` (Lemma 3.3). -/
noncomputable def sAvgPhi_asymp (P : Params) :
    FactorAsymp (fun X => Estimates.sAvgPhi P X) logX where
  c := P.η * (Estimates.s_average_phi P).choose
  C := P.η * (Estimates.s_average_phi P).choose_spec.choose
  X₀ := max (Estimates.s_average_phi P).choose_spec.choose_spec.choose (Real.exp 1)
  c_pos := mul_pos P.η_pos
    (Estimates.s_average_phi P).choose_spec.choose_spec.choose_spec.1
  C_pos := mul_pos P.η_pos
    (Estimates.s_average_phi P).choose_spec.choose_spec.choose_spec.2.1
  f_nonneg := fun X _ => Estimates.sAvgPhi_nonneg P X
  sandwich := fun X hX => by
    have hX0' : (Estimates.s_average_phi P).choose_spec.choose_spec.choose ≤ X :=
      le_trans (le_max_left _ _) hX
    have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
    have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
    have hsand :=
      (Estimates.s_average_phi P).choose_spec.choose_spec.choose_spec.2.2 X hX0'
    rw [log_SScale P hXpos] at hsand
    obtain ⟨hlo, hhi⟩ := hsand
    refine ⟨?_, ?_⟩
    · have : (Estimates.s_average_phi P).choose * (P.η * Real.log X)
              ≤ Estimates.sAvgPhi P X := hlo
      unfold logX
      linarith [this]
    · have : Estimates.sAvgPhi P X
              ≤ (Estimates.s_average_phi P).choose_spec.choose *
                (P.η * Real.log X) := hhi
      unfold logX
      linarith [this]

/-- The main term of `M_φ` is `≍ (log X)²`. -/
noncomputable def exactDivisorMPhiMassShape_factor_asymp
    (P : Params) :
    FactorAsymp (fun X => exactDivisorMPhiMassShape P X) logSq where
  c := (P.θ - P.lam - P.η) * (sAvgRecip_asymp P).c
  C := (P.θ - P.lam) * (sAvgRecip_asymp P).C
  X₀ := max (sAvgRecip_asymp P).X₀ (Real.exp 1)
  c_pos := by
    have hcoef : 0 < P.θ - P.lam - P.η := by
      linarith [P.lam_add_η_lt_θ]
    exact mul_pos hcoef (sAvgRecip_asymp P).c_pos
  C_pos := by
    have hcoef : 0 < P.θ - P.lam := by
      linarith [P.lam_add_η_lt_θ, P.η_pos]
    exact mul_pos hcoef (sAvgRecip_asymp P).C_pos
  f_nonneg := by
    intro X hX
    have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
    exact exactDivisorMPhiMassShape_nonneg P hXe
  sandwich := by
    intro X hX
    have hXs : (sAvgRecip_asymp P).X₀ ≤ X := le_trans (le_max_left _ _) hX
    have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
    have hlog_nonneg : 0 ≤ logX X := by
      unfold logX
      exact Real.log_nonneg
        (le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe)
    have hsavg_lower := (sAvgRecip_asymp P).lower hXs
    have hsavg_upper := (sAvgRecip_asymp P).upper hXs
    have hshape_lower :=
      exactDivisorMPhiMassShape_lower_logX_sAvgRecip P hXe
    have hshape_upper :=
      exactDivisorMPhiMassShape_upper_logX_sAvgRecip P hXe
    have hcoef_lower : 0 ≤ P.θ - P.lam - P.η := by
      have : 0 < P.θ - P.lam - P.η := by
        linarith [P.lam_add_η_lt_θ]
      exact this.le
    have hcoef_upper : 0 ≤ P.θ - P.lam := by
      have : 0 < P.θ - P.lam := by
        linarith [P.lam_add_η_lt_θ, P.η_pos]
      exact this.le
    constructor
    · calc
        ((P.θ - P.lam - P.η) * (sAvgRecip_asymp P).c) * logSq X
            = (P.θ - P.lam - P.η) * ((sAvgRecip_asymp P).c * logX X) * logX X := by
              unfold logSq logX
              ring
        _ ≤ (P.θ - P.lam - P.η) * Estimates.sAvgRecip P X * logX X := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hsavg_lower hcoef_lower) hlog_nonneg
        _ = (P.θ - P.lam - P.η) * logX X * Estimates.sAvgRecip P X := by ring
        _ ≤ exactDivisorMPhiMassShape P X := hshape_lower
    · calc
        exactDivisorMPhiMassShape P X
            ≤ (P.θ - P.lam) * logX X * Estimates.sAvgRecip P X := hshape_upper
        _ ≤ (P.θ - P.lam) * logX X * ((sAvgRecip_asymp P).C * logX X) := by
              exact mul_le_mul_of_nonneg_left hsavg_upper
                (mul_nonneg hcoef_upper hlog_nonneg)
        _ = ((P.θ - P.lam) * (sAvgRecip_asymp P).C) * logSq X := by
              unfold logSq logX
              ring

theorem exactDivisorMPhiMassShape_logSq
    (P : Params) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassShape P X ∧
        exactDivisorMPhiMassShape P X ≤ C * logSq X := by
  let h := exactDivisorMPhiMassShape_factor_asymp P
  exact ⟨h.c, h.C, h.X₀, h.c_pos, h.C_pos, fun X hX => h.sandwich X hX⟩

/-- The main term of `M₁` is `≍ (log X)²`. -/
noncomputable def exactDivisorM1MassShape_factor_asymp
    (P : Params) :
    FactorAsymp (fun X => exactDivisorM1MassShape P X) logSq where
  c := (P.θ - P.lam - P.η) * (sAvgPhi_asymp P).c
  C := (P.θ - P.lam) * (sAvgPhi_asymp P).C
  X₀ := max (sAvgPhi_asymp P).X₀ (Real.exp 1)
  c_pos := by
    have hcoef : 0 < P.θ - P.lam - P.η := by
      linarith [P.lam_add_η_lt_θ]
    exact mul_pos hcoef (sAvgPhi_asymp P).c_pos
  C_pos := by
    have hcoef : 0 < P.θ - P.lam := by
      linarith [P.lam_add_η_lt_θ, P.η_pos]
    exact mul_pos hcoef (sAvgPhi_asymp P).C_pos
  f_nonneg := by
    intro X hX
    have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
    exact exactDivisorM1MassShape_nonneg P hXe
  sandwich := by
    intro X hX
    have hXs : (sAvgPhi_asymp P).X₀ ≤ X := le_trans (le_max_left _ _) hX
    have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
    have hlog_nonneg : 0 ≤ logX X := by
      unfold logX
      exact Real.log_nonneg
        (le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe)
    have hsavg_lower := (sAvgPhi_asymp P).lower hXs
    have hsavg_upper := (sAvgPhi_asymp P).upper hXs
    have hshape_lower :=
      exactDivisorM1MassShape_lower_logX_sAvgPhi P hXe
    have hshape_upper :=
      exactDivisorM1MassShape_upper_logX_sAvgPhi P hXe
    have hcoef_lower : 0 ≤ P.θ - P.lam - P.η := by
      have : 0 < P.θ - P.lam - P.η := by
        linarith [P.lam_add_η_lt_θ]
      exact this.le
    have hcoef_upper : 0 ≤ P.θ - P.lam := by
      have : 0 < P.θ - P.lam := by
        linarith [P.lam_add_η_lt_θ, P.η_pos]
      exact this.le
    constructor
    · calc
        ((P.θ - P.lam - P.η) * (sAvgPhi_asymp P).c) * logSq X
            = (P.θ - P.lam - P.η) * ((sAvgPhi_asymp P).c * logX X) * logX X := by
              unfold logSq logX
              ring
        _ ≤ (P.θ - P.lam - P.η) * Estimates.sAvgPhi P X * logX X := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hsavg_lower hcoef_lower) hlog_nonneg
        _ = (P.θ - P.lam - P.η) * logX X * Estimates.sAvgPhi P X := by ring
        _ ≤ exactDivisorM1MassShape P X := hshape_lower
    · calc
        exactDivisorM1MassShape P X
            ≤ (P.θ - P.lam) * logX X * Estimates.sAvgPhi P X := hshape_upper
        _ ≤ (P.θ - P.lam) * logX X * ((sAvgPhi_asymp P).C * logX X) := by
              exact mul_le_mul_of_nonneg_left hsavg_upper
                (mul_nonneg hcoef_upper hlog_nonneg)
        _ = ((P.θ - P.lam) * (sAvgPhi_asymp P).C) * logSq X := by
              unfold logSq logX
              ring

theorem exactDivisorM1MassShape_logSq
    (P : Params) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorM1MassShape P X ∧
        exactDivisorM1MassShape P X ≤ C * logSq X := by
  let h := exactDivisorM1MassShape_factor_asymp P
  exact ⟨h.c, h.C, h.X₀, h.c_pos, h.C_pos, fun X hX => h.sandwich X hX⟩

/-! ## Bounds for `M₁` and `M_φ` -/

/-- Given the `d = 1` fibre estimate, `M_φ ≍ (log X)²`. -/
theorem exactDivisorMPhiMassRaw_logSq_of_fiberAverageTwoSided
    {P : Params}
    (hφ : ExactDivisorMPhiFiberAverageTwoSided P) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
        exactDivisorMPhiMassRaw P X ≤ C * logSq X := by
  rcases exactDivisorMPhiMassFiber_asymp_shape hφ with
    ⟨a, A, Xcmp, ha, hA, hcmp⟩
  rcases exactDivisorMPhiMassShape_logSq P with
    ⟨c, C, Xshape, hc, hC, hshape⟩
  refine ⟨a * c, A * C, max Xcmp Xshape, mul_pos ha hc, mul_pos hA hC, ?_⟩
  intro X hX
  have hXcmp : Xcmp ≤ X := le_trans (le_max_left _ _) hX
  have hXshape : Xshape ≤ X := le_trans (le_max_right _ _) hX
  have hcmpX := hcmp X hXcmp
  have hshapeX := hshape X hXshape
  constructor
  · calc
      (a * c) * logSq X = a * (c * logSq X) := by ring
      _ ≤ a * exactDivisorMPhiMassShape P X :=
          mul_le_mul_of_nonneg_left hshapeX.1 ha.le
      _ ≤ exactDivisorMPhiMassFiber P X := hcmpX.1
      _ = exactDivisorMPhiMassRaw P X := by
          rw [← exactDivisorMPhiMassRaw_eq_fiber P X]
  · calc
      exactDivisorMPhiMassRaw P X = exactDivisorMPhiMassFiber P X := by
          rw [exactDivisorMPhiMassRaw_eq_fiber P X]
      _ ≤ A * exactDivisorMPhiMassShape P X := hcmpX.2
      _ ≤ A * (C * logSq X) := mul_le_mul_of_nonneg_left hshapeX.2 hA.le
      _ = (A * C) * logSq X := by ring

/-- Given `PhiProgressionSqfRecipLower`, `M₁` is at least a constant times its main term. -/
theorem exactDivisorM1MassFiber_lower_of_sqfRecipLower
    {P : Params} (hlower : PhiProgressionSqfRecipLower P) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      c * exactDivisorM1MassShape P X ≤ exactDivisorM1MassFiber P X := by
  classical
  rcases hlower with ⟨c, Xlo, hc, hlo⟩
  rcases fixedNat_le_UScale_eventually 1 with ⟨XU, hU⟩
  refine ⟨c, max (max Xlo XU) (Real.exp 1), hc, ?_⟩
  intro X hX
  have hXlo : Xlo ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXU : XU ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hS_nonneg : 0 ≤ SScale P X :=
    (Real.rpow_pos_of_pos hXpos P.η).le
  have hU1 : ((1 : ℕ) : ℝ) ≤ UScale X := hU X hXU
  unfold exactDivisorM1MassShape exactDivisorM1MassFiber exactDivisorSRange
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
    (Finset.mem_filter.mp hs).1
  have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
  have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
  have hs_sqf : Squarefree s := (Finset.mem_filter.mp hs).2
  have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos_nat
  have hsS : (s : ℝ) ≤ SScale P X :=
    le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
  have hbare :
      c * phiProgressionAverageShape P X 1 s ≤
        phiProgressionBareAverage P X 1 0 s := by
    have hraw := hlo X hXlo 1 0 s (by norm_num) squarefree_one
      (by norm_num) hU1 (by norm_num) hs_one hs_sqf
      (Nat.coprime_one_right s) hsS
    simpa [phiProgressionBareAverage_eq_sqfRecip,
      phiProgressionAverageShape,
      log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos_nat]
      using hraw
  have hscale_nonneg : 0 ≤ (1 : ℝ) / (s : ℝ) := by positivity
  calc
    c * (((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) *
          slantLogLength P s X) =
        ((1 : ℝ) / (s : ℝ)) *
          (c * phiProgressionAverageShape P X 1 s) := by
            unfold phiProgressionAverageShape
            ring_nf
    _ ≤ ((1 : ℝ) / (s : ℝ)) *
          phiProgressionBareAverage P X 1 0 s :=
      mul_le_mul_of_nonneg_left hbare hscale_nonneg

/-- `M₁ ≤ M_φ`, since `1/n ≤ 1/φ(n)` termwise on the same support. -/
theorem exactDivisorM1MassRaw_le_MPhiMassRaw (P : Params) (X : ℝ) :
    exactDivisorM1MassRaw P X ≤ exactDivisorMPhiMassRaw P X := by
  rw [exactDivisorM1MassRaw_eq_fiber, exactDivisorMPhiMassRaw_eq_fiber]
  unfold exactDivisorM1MassFiber exactDivisorMPhiMassFiber
  apply Finset.sum_le_sum
  intro s hs
  have hs_one : 1 ≤ s :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hcoeff : (1 : ℝ) / (s : ℝ) ≤
      (1 : ℝ) / (Nat.totient s : ℝ) :=
    one_div_nat_le_one_div_totient hs_pos
  have hfiber := phiProgressionBareAverage_le_phiProgressionAverage P X 1 0 s
  exact mul_le_mul hcoeff hfiber
    (phiProgressionBareAverage_nonneg P X 1 0 s) (by positivity)

/-! ## Residue classes

For `(s, D) = 1` the condition `e ≡ c (mod D)` is the reduced progression
`r ≡ c s⁻² (mod D)`, as in the proof of Theorem 6.3. -/

/-- A residue `k⁻¹ mod d`: some `b` with `k b ≡ 1 (mod d)` if there is one, and `0`
otherwise. -/
noncomputable def modInverseChoice (d k : ℕ) : ℕ := by
  classical
  exact if h : ∃ b : ℕ, k * b ≡ 1 [MOD d] then Classical.choose h else 0

theorem modInverseChoice_spec {d k : ℕ}
    (h : ∃ b : ℕ, k * b ≡ 1 [MOD d]) :
    k * modInverseChoice d k ≡ 1 [MOD d] := by
  classical
  unfold modInverseChoice
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem exists_mul_modEq_one_of_coprime
    {d k : ℕ} (hd : 0 < d) (hk : Nat.Coprime k d) :
    ∃ b : ℕ, k * b ≡ 1 [MOD d] := by
  classical
  by_cases hd_one : d = 1
  · subst d
    exact ⟨0, by simp [Nat.ModEq]⟩
  · have hd_gt_one : 1 < d :=
      lt_of_le_of_ne (Nat.succ_le_of_lt hd) (Ne.symm hd_one)
    obtain ⟨b, -, hb⟩ := Nat.exists_mul_mod_eq_one_of_coprime
      (k := d) (n := k) hk hd_gt_one
    refine ⟨b, ?_⟩
    rw [Nat.ModEq, hb, Nat.mod_eq_of_lt hd_gt_one]

theorem modInverseChoice_coprime {d k : ℕ}
    (hd : 0 < d) (hk : Nat.Coprime k d) :
    k * modInverseChoice d k ≡ 1 [MOD d] :=
  modInverseChoice_spec (exists_mul_modEq_one_of_coprime hd hk)

theorem modInverseChoice_value_coprime {d k : ℕ}
    (hd : 0 < d) (hk : Nat.Coprime k d) :
    Nat.Coprime (modInverseChoice d k) d := by
  have hcong : k * modInverseChoice d k ≡ 1 [MOD d] :=
    modInverseChoice_coprime hd hk
  have hprod : Nat.Coprime (k * modInverseChoice d k) d := by
    rw [Nat.coprime_iff_gcd_eq_one]
    rw [hcong.gcd_eq]
    simp
  exact hprod.coprime_dvd_left (dvd_mul_left _ _)

/-- The residue `s⁻² mod D` for `D > 0` and `(s, D) = 1`; it is `1` when `D = 0`. -/
noncomputable def exactDivisorInverseSquareResidue (D s : ℕ) : ℕ :=
  if D = 0 then 1 else (modInverseChoice D s) ^ (2 : ℕ)

theorem exactDivisorInverseSquareResidue_coprime {D s : ℕ}
    (hsD : Nat.Coprime s D) :
    Nat.Coprime (exactDivisorInverseSquareResidue D s) D := by
  by_cases hD0 : D = 0
  · subst D
    simp [exactDivisorInverseSquareResidue]
  · have hDpos : 0 < D := Nat.pos_of_ne_zero hD0
    have hinv : Nat.Coprime (modInverseChoice D s) D :=
      modInverseChoice_value_coprime hDpos hsD
    simpa [exactDivisorInverseSquareResidue, hD0] using hinv

/-- `∑_{(s, D) = 1} φ(s)⁻¹ ∑_{r ≡ a(s) (mod D)} 1/φ(r)`, which bounds the `M_φ` sum over
`e ≡ c (mod D)` when `a(s) = c s⁻²`. Only `(s, D) = 1` occurs, since `r s² ≡ c (mod D)` has no
solution otherwise when `(c, D) = 1`. -/
noncomputable def exactDivisorMPhiTensorFiberCoprime
    (P : Params) (X : ℝ) (D : ℕ) (a : ℕ → ℕ) : ℝ := by
  classical
  exact
    ∑ s ∈ exactDivisorSRange P X,
      if Nat.Coprime s D then
        ((1 : ℝ) / (Nat.totient s : ℝ)) * phiProgressionAverage P X D (a s) s
      else 0

end ErdosStraus
