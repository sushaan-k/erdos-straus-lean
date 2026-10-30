import ErdosStraus.BombieriVinogradov.DirichletL.Bounds
import ErdosStraus.BombieriVinogradov.Reduction.Orthogonality

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

/-!
# Smoothed Perron formula for twisted Chebyshev sums

For a Dirichlet character `χ` and the smoothed cutoff `Smooth1 ν ε`, the sum
`∑ₙ Λ(n) χ(n) Smooth1 ν ε (n / X)` equals
`(2πi)⁻¹ ∫_{(σ)} -L'/L(s, χ) 𝓜(Smooth1 ν ε)(s) X^s ds` for `1 < σ ≤ 2`.
On the line `re s = 1 + δ` the parts of this integral with `|t| ≥ T` are
`O(X^{1+δ} (1 + δ⁻²) / (ε T))`, and the smoothed sum is within `O(ε X log X)` of
`∑_{n ≤ X} Λ(n) χ(n)`.
-/

section

open Set Function Filter Complex Real MeasureTheory
open ArithmeticFunction (vonMangoldt)
open scoped LSeries.notation

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

local notation "𝓜" => mellin
local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- `Λ(n) χ(n)`, the coefficients of the Dirichlet series of `-L'/L(s, χ)`. -/
noncomputable def twistedVonMangoldtCoeff (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  (Λ n : ℂ) * χ n

/-- The smoothed twisted Chebyshev sum `∑ₙ Λ(n) χ(n) Smooth1 ν ε (n / X)`. -/
noncomputable def twistedSmoothedPsi (χ : DirichletCharacter ℂ q)
    (ν : ℝ → ℝ) (ε X : ℝ) : ℂ :=
  ∑' n : ℕ, twistedVonMangoldtCoeff χ n * Smooth1 ν ε (n / X)

/-- The Perron integrand `-L'/L(s, χ) · 𝓜(Smooth1 ν ε)(s) · X^s`. -/
noncomputable def twistedSmoothedPerronIntegrand (χ : DirichletCharacter ℂ q)
    (ν : ℝ → ℝ) (ε X : ℝ) (s : ℂ) : ℂ :=
  (-deriv (LFunction χ) s / LFunction χ s) *
    𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s * (X : ℂ) ^ s

lemma neg_logDeriv_LFunction_eq_tsum_twistedVonMangoldtCoeff
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    -deriv (LFunction χ) s / LFunction χ s =
      ∑' n : ℕ, twistedVonMangoldtCoeff χ n / (n : ℂ) ^ s := by
  rw [← LSeries_twist_vonMangoldt_eq_neg_logDeriv_LFunction χ hs]
  dsimp [LSeries, LSeries.term]
  nth_rewrite 2 [Summable.tsum_eq_add_tsum_ite (b := 0) ?_]
  · simp [twistedVonMangoldtCoeff, mul_comm]
  · have h := LSeriesSummable_twist_vonMangoldt χ hs
    dsimp [LSeriesSummable] at h
    convert! h
    rename ℕ => n
    by_cases hn : n = 0 <;> simp [LSeries.term, twistedVonMangoldtCoeff, hn, mul_comm]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero q] in
lemma twistedSmoothedPerron_aux_tsum_integral
    (χ : DirichletCharacter ℂ q) {ν : ℝ → ℝ}
    (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {X : ℝ} (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1)
    {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    ∫ t : ℝ, ∑' n : ℕ,
      twistedVonMangoldtCoeff χ n / (n : ℂ) ^ (σ + t * I) *
        𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
          (X : ℂ) ^ (σ + t * I) =
    ∑' n : ℕ, ∫ t : ℝ,
      twistedVonMangoldtCoeff χ n / (n : ℂ) ^ (σ + t * I) *
        𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
          (X : ℂ) ^ (σ + t * I) := by
  have cont_mellin_smooth : Continuous fun a : ℝ ↦
      𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + a * I) := by
    rw [← continuousOn_univ]
    refine ContinuousOn.comp' ?_ ?_ ?_ (t := {z : ℂ | 0 < z.re})
    · refine continuousOn_of_forall_continuousAt ?_
      intro z hz
      exact (Smooth1MellinDifferentiable diffν suppν ⟨εpos, ε_lt_one⟩
        νpos mass_one hz).continuousAt
    · fun_prop
    · simp only [mapsTo_univ_iff, mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re,
        mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, forall_const]
      linarith
  have norm_nat_cpow_vertical : ∀ a : ℝ, ∀ n : ℕ,
      ‖(n : ℂ) ^ ((σ : ℂ) + a * I)‖₊ = n ^ σ := by
    intro a n
    simp_rw [← norm_toNNReal]
    rw [norm_natCast_cpow_of_re_ne_zero _ (by
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero, ne_eq]
      linarith)]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero,
      Real.toNNReal_of_nonneg <| rpow_nonneg (y := σ) (x := n) (by linarith)]
    norm_cast
  -- The absolute bound factors as `∑ₙ Λ(n) / n^σ` times `∫ |𝓜(Smooth1 ν ε)(σ + it)| dt`.
  rw [MeasureTheory.integral_tsum]
  · have X_ne : X ≠ 0 := ne_of_gt X_pos
    intro n
    by_cases hn : n = 0
    · simpa [hn, twistedVonMangoldtCoeff] using aestronglyMeasurable_const
    · apply Continuous.aestronglyMeasurable
      fun_prop (disch := simp [hn, X_ne])
  · rw [← lt_top_iff_ne_top]
    simp_rw [enorm_mul, enorm_eq_nnnorm, nnnorm_div, ← norm_toNNReal,
      Complex.norm_cpow_eq_rpow_re_of_pos X_pos, norm_toNNReal, norm_nat_cpow_vertical]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
      I_im, mul_one, sub_self, add_zero]
    simp_rw [MeasureTheory.lintegral_mul_const' (r := ↑(X ^ σ).toNNReal) (hr := by simp),
      ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top ?_ ENNReal.coe_lt_top
    conv =>
      arg 1
      arg 1
      intro n
      rw [MeasureTheory.lintegral_const_mul' (hr := by simp)]
    rw [ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top
    · rw [WithTop.lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable_coe]
      push_cast
      refine Summable.of_nonneg_of_le (fun _ ↦ div_nonneg (norm_nonneg _) (by positivity))
        (fun n ↦ ?_)
        (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := σ)
          (by simp only [ofReal_re]; linarith)).norm
      rw [LSeries.term_def]
      split_ifs with hn
      · simp [hn, twistedVonMangoldtCoeff]
      · dsimp [twistedVonMangoldtCoeff]
        rw [norm_div, norm_mul]
        calc
          ‖(Λ n : ℂ)‖ * ‖χ n‖ / (n : ℝ) ^ σ ≤
              ‖(Λ n : ℂ)‖ / (n : ℝ) ^ σ :=
            div_le_div_of_nonneg_right
              (mul_le_of_le_one_right (norm_nonneg _) (norm_le_one χ n)) (by positivity)
          _ = ‖(Λ n : ℂ)‖ / ‖(n : ℂ) ^ (σ : ℂ)‖ := by
            rw [Complex.norm_natCast_cpow_of_re_ne_zero n]
            · simp
            · simp only [ofReal_re]
              linarith
    · simp_rw [← enorm_eq_nnnorm]
      rw [← MeasureTheory.hasFiniteIntegral_iff_enorm]
      exact SmoothedChebyshevDirichlet_aux_integrable diffν νpos suppν mass_one
        εpos ε_lt_one σ_gt σ_le |>.hasFiniteIntegral

set_option backward.isDefEq.respectTransparency false in
/-- Smoothed Perron formula: for `1 < σ ≤ 2`, the smoothed sum
`∑ₙ Λ(n) χ(n) Smooth1 ν ε (n / X)` equals `(2πi)⁻¹` times the integral of the Perron
integrand over `re s = σ`. It holds for every Dirichlet character `χ`, principal or not. -/
theorem twistedSmoothedPerron
    (χ : DirichletCharacter ℂ q) {ν : ℝ → ℝ}
    (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {X : ℝ} (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1)
    {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    twistedSmoothedPsi χ ν ε X =
      VerticalIntegral' (twistedSmoothedPerronIntegrand χ ν ε X) σ := by
  symm
  dsimp [twistedSmoothedPsi, twistedSmoothedPerronIntegrand,
    VerticalIntegral', VerticalIntegral]
  calc
    _ = 1 / (2 * π * I) * (I * ∫ t : ℝ, ∑' n : ℕ,
        twistedVonMangoldtCoeff χ n / (n : ℂ) ^ (σ + t * I) *
          𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
            (X : ℂ) ^ (σ + t * I)) := by
      congr
      ext t
      rw [neg_logDeriv_LFunction_eq_tsum_twistedVonMangoldtCoeff χ]
      · rw [← tsum_mul_right, ← tsum_mul_right]
      · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
          mul_one, sub_self, add_zero]
        exact σ_gt
    _ = 1 / (2 * π * I) * (I * ∑' n : ℕ, ∫ t : ℝ,
        twistedVonMangoldtCoeff χ n / (n : ℂ) ^ (σ + t * I) *
          𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
            (X : ℂ) ^ (σ + t * I)) := by
      congr 2
      exact twistedSmoothedPerron_aux_tsum_integral χ diffν νpos suppν mass_one
        X_pos εpos ε_lt_one σ_gt σ_le
    _ = 1 / (2 * π * I) * (I * ∑' n : ℕ, twistedVonMangoldtCoeff χ n *
        ∫ t : ℝ, 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
          (X / (n : ℂ)) ^ (σ + t * I)) := by
      field_simp
      congr 1
      ext n
      rw [← MeasureTheory.integral_const_mul]
      congr 1
      ext t
      by_cases hn : n = 0
      · simp [hn, twistedVonMangoldtCoeff]
      rw [mul_div_assoc, mul_assoc]
      congr 1
      rw [(div_eq_iff (by simp [hn])).mpr]
      · have hmul := @mul_cpow_ofReal_nonneg (a := X / (n : ℝ)) (b := (n : ℝ))
          (r := σ + I * t) (div_nonneg X_pos.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
        push_cast at hmul ⊢
        rw [← hmul, div_mul_cancel₀]
        simp [hn]
    _ = 1 / (2 * π) * (∑' n : ℕ, twistedVonMangoldtCoeff χ n *
        ∫ t : ℝ, 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
          (X / (n : ℂ)) ^ (σ + t * I)) := by
      rw [← mul_assoc]
      congr 1
      field_simp
    _ = ∑' n : ℕ, twistedVonMangoldtCoeff χ n *
        (1 / (2 * π) * ∫ t : ℝ,
          𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
            (X / (n : ℂ)) ^ (σ + t * I)) := by
      simp_rw [← tsum_mul_left, ← mul_assoc, mul_comm]
    _ = ∑' n : ℕ, twistedVonMangoldtCoeff χ n *
        (1 / (2 * π) * ∫ t : ℝ,
          𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
            ((n : ℂ) / X) ^ (-(σ + t * I))) := by
      have ht (t : ℝ) : -(σ + t * I) = (-1) * (σ + t * I) := by simp
      have hninv (n : ℂ) : (n / X) ^ (-1 : ℂ) = X / n := by simp [cpow_neg_one]
      have him (n : ℕ) : (log ((n : ℂ) / (X : ℂ)) * -1).im = 0 := by
        simp [Complex.log_im, arg_eq_zero_iff,
          div_nonneg (Nat.cast_nonneg _) X_pos.le]
      have hpow (n : ℕ) (t : ℝ) :
          ((n : ℂ) / X) ^ ((-1 : ℂ) * (σ + t * I)) =
            (((n : ℂ) / X) ^ (-1 : ℂ)) ^ (σ + t * I) := by
        rw [cpow_mul] <;> rw [him n] <;> simp [Real.pi_pos, Real.pi_nonneg]
      simp_rw [ht, hpow, hninv]
    _ = _ := by
      congr 1
      ext n
      by_cases hn : n = 0
      · simp [hn, twistedVonMangoldtCoeff]
      have n_pos : 0 < n := Nat.pos_of_ne_zero hn
      congr 1
      have h := mellinInv_mellin_eq σ
        (f := fun x ↦ (Smooth1 ν ε x : ℂ)) (x := n / X) ?_ ?_ ?_ ?_
      · beta_reduce at h
        dsimp [mellinInv, VerticalIntegral] at h
        convert! h using 4
        · norm_cast
        · rw [mul_comm]
          norm_cast
      · exact div_pos (by exact_mod_cast n_pos) X_pos
      · apply Smooth1MellinConvergent diffν suppν ⟨εpos, ε_lt_one⟩ νpos mass_one
        simp only [ofReal_re]
        linarith
      · dsimp [VerticalIntegrable]
        exact SmoothedChebyshevDirichlet_aux_integrable diffν νpos suppν mass_one
          εpos ε_lt_one σ_gt σ_le
      · refine ContinuousAt.comp (g := ofReal) RCLike.continuous_ofReal.continuousAt ?_
        exact Smooth1ContinuousAt diffν νpos suppν εpos (by positivity)

end DirichletCharacter

end

/-! ## Integrability and tail bounds on vertical lines -/

section

open Set Function Filter Complex Real MeasureTheory
open ArithmeticFunction (vonMangoldt)

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

local notation "𝓜" => mellin
local notation "Λ" => ArithmeticFunction.vonMangoldt

set_option backward.isDefEq.respectTransparency false in
/-- For `1 < σ ≤ 2` the Perron integrand is integrable along `re s = σ`, since the
Dirichlet series of `-L'/L` converges absolutely there and `𝓜(Smooth1 ν ε)` is
integrable on vertical lines. -/
theorem twistedSmoothedPerronIntegrand_integrable_right
    (χ : DirichletCharacter ℂ q) {ν : ℝ → ℝ}
    (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {X : ℝ} (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1)
    {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    Integrable (fun t : ℝ =>
      twistedSmoothedPerronIntegrand χ ν ε X (σ + t * I)) := by
  have right_re (t : ℝ) : ((σ : ℂ) + t * I).re = σ := by simp
  have σ_pos : 0 < σ := zero_lt_one.trans σ_gt
  let term : ℕ → ℝ → ℂ := fun n t =>
    twistedVonMangoldtCoeff χ n / (n : ℂ) ^ (σ + t * I) *
      𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
        (X : ℂ) ^ (σ + t * I)
  have nnnorm_natCast_cpow_right : ∀ t : ℝ, ∀ n : ℕ,
      ‖(n : ℂ) ^ ((σ : ℂ) + t * I)‖₊ = n ^ σ := by
    intro t n
    simp_rw [← norm_toNNReal]
    rw [norm_natCast_cpow_of_re_ne_zero _ (by
      rw [right_re]
      exact σ_pos.ne'), right_re,
      Real.toNNReal_of_nonneg (rpow_nonneg (Nat.cast_nonneg n) σ)]
    norm_cast
  have cont_mellin_smooth : Continuous fun a : ℝ ↦
      𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + a * I) := by
    rw [← continuousOn_univ]
    refine ContinuousOn.comp' ?_ ?_ ?_ (t := {z : ℂ | 0 < z.re})
    · refine continuousOn_of_forall_continuousAt ?_
      intro z hz
      exact (Smooth1MellinDifferentiable diffν suppν ⟨εpos, ε_lt_one⟩
        νpos mass_one hz).continuousAt
    · fun_prop
    · intro t _
      change 0 < ((σ : ℂ) + t * I).re
      rw [right_re]
      exact σ_pos
  have X_ne : X ≠ 0 := ne_of_gt X_pos
  have hmeas : AEStronglyMeasurable (fun t : ℝ => ∑' n : ℕ, term n t) := by
    apply AEStronglyMeasurable.tsum
    intro n
    by_cases hn : n = 0
    · simpa [term, hn, twistedVonMangoldtCoeff] using aestronglyMeasurable_const
    · apply Continuous.aestronglyMeasurable
      dsimp [term]
      fun_prop (disch := simp [hn, X_ne])
  have hmajor :
      ∫⁻ t : ℝ, ∑' n : ℕ, ‖term n t‖ₑ < ⊤ := by
    simp_rw [term, enorm_mul, enorm_eq_nnnorm, nnnorm_div, ← norm_toNNReal,
      Complex.norm_cpow_eq_rpow_re_of_pos X_pos, norm_toNNReal, nnnorm_natCast_cpow_right]
    simp only [right_re]
    simp_rw [ENNReal.tsum_mul_right]
    rw [MeasureTheory.lintegral_mul_const'
      (r := ↑(X ^ σ).toNNReal) (hr := ENNReal.coe_ne_top)]
    apply WithTop.mul_lt_top ?_ ENNReal.coe_lt_top
    have hCne :
        (∑' n : ℕ, (↑(‖twistedVonMangoldtCoeff χ n‖₊ /
          (n : NNReal) ^ σ) : ENNReal)) ≠ ⊤ := by
      rw [ENNReal.tsum_coe_ne_top_iff_summable_coe]
      push_cast
      refine Summable.of_nonneg_of_le (fun _ ↦ div_nonneg (norm_nonneg _) (by positivity))
        (fun n ↦ ?_)
        (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := σ)
          (by simp only [ofReal_re]; linarith)).norm
      rw [LSeries.term_def]
      split_ifs with hn
      · simp [hn, twistedVonMangoldtCoeff]
      · dsimp [twistedVonMangoldtCoeff]
        rw [norm_div, norm_mul]
        calc
          ‖(Λ n : ℂ)‖ * ‖χ n‖ / (n : ℝ) ^ σ ≤
              ‖(Λ n : ℂ)‖ / (n : ℝ) ^ σ :=
            div_le_div_of_nonneg_right
              (mul_le_of_le_one_right (norm_nonneg _) (norm_le_one χ n)) (by positivity)
          _ = ‖(Λ n : ℂ)‖ / ‖(n : ℂ) ^ (σ : ℂ)‖ := by
            rw [Complex.norm_natCast_cpow_of_re_ne_zero n]
            · simp
            · simp only [ofReal_re]
              linarith
    rw [MeasureTheory.lintegral_const_mul' (hr := hCne)]
    apply WithTop.mul_lt_top (lt_top_iff_ne_top.mpr hCne)
    simp_rw [← enorm_eq_nnnorm]
    rw [← MeasureTheory.hasFiniteIntegral_iff_enorm]
    exact SmoothedChebyshevDirichlet_aux_integrable diffν νpos suppν mass_one
      εpos ε_lt_one σ_gt σ_le |>.hasFiniteIntegral
  have hseries : Integrable (fun t : ℝ => ∑' n : ℕ, term n t) := by
    refine ⟨hmeas, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
    exact lt_of_le_of_lt
      (MeasureTheory.lintegral_mono fun t => enorm_tsum_le_tsum_enorm) hmajor
  convert hseries using 1
  funext t
  dsimp [twistedSmoothedPerronIntegrand, term]
  rw [neg_logDeriv_LFunction_eq_tsum_twistedVonMangoldtCoeff χ]
  · rw [← tsum_mul_right, ← tsum_mul_right]
  · simpa only [right_re] using σ_gt

end DirichletCharacter

end

section

open Set Function Filter Complex Real MeasureTheory
open ArithmeticFunction (vonMangoldt)

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

local notation "𝓜" => mellin
local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- `∑ₙ |Λ(n) χ(n) / n^s|` at `s = 1 + δ + it`. -/
noncomputable def twistedVonMangoldtRightMajorant
    (χ : DirichletCharacter ℂ q) (δ t : ℝ) : ℝ :=
  ∑' n : ℕ,
    ‖twistedVonMangoldtCoeff χ n /
      (n : ℂ) ^ ((1 + δ : ℝ) + t * I)‖

omit [NeZero q] in
/-- For `0 < δ ≤ 1`, `∑ₙ Λ(n) |χ(n)| / n^{1+δ} ≤ 6 (1 + δ⁻²)`, uniformly in `χ` and `t`.
The proof uses `log n ≤ (2/δ) n^{δ/2}`. -/
theorem twistedVonMangoldtRightMajorant_le
    (χ : DirichletCharacter ℂ q) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (t : ℝ) :
    twistedVonMangoldtRightMajorant χ δ t ≤ 6 * (1 + δ⁻¹ ^ 2) := by
  let s : ℂ := (1 + δ : ℝ) + t * I
  have hs : 1 < s.re := by simp [s]; linarith
  have hright : Summable (fun n : ℕ =>
      (2 / δ) * (n : ℝ) ^ (-(1 + δ / 2))) := by
    apply Summable.mul_left
    exact Real.summable_nat_rpow.mpr (by linarith)
  have hterm (n : ℕ) :
      ‖twistedVonMangoldtCoeff χ n / (n : ℂ) ^ s‖ ≤
        (2 / δ) * (n : ℝ) ^ (-(1 + δ / 2)) := by
    by_cases hn : n = 0
    · subst n
      rw [show twistedVonMangoldtCoeff χ 0 = 0 by
        simp [twistedVonMangoldtCoeff]]
      simp only [zero_div, norm_zero]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hlog := Real.log_natCast_le_rpow_div n (show 0 < δ / 2 by positivity)
    have hΛlog : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    have hpow :
        (n : ℝ) ^ (δ / 2) / (δ / 2) / (n : ℝ) ^ (1 + δ) =
          (2 / δ) * (n : ℝ) ^ (-(1 + δ / 2)) := by
      calc
        (n : ℝ) ^ (δ / 2) / (δ / 2) / (n : ℝ) ^ (1 + δ) =
            (2 / δ) * ((n : ℝ) ^ (δ / 2) / (n : ℝ) ^ (1 + δ)) := by
              field_simp [hδ.ne']
        _ = (2 / δ) * (n : ℝ) ^ (δ / 2 - (1 + δ)) := by
              rw [Real.rpow_sub hnpos]
        _ = _ := by congr 2; ring
    rw [norm_div, twistedVonMangoldtCoeff, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Complex.norm_natCast_cpow_of_re_ne_zero n]
    · simp only [s, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero]
      calc
        Λ n * ‖χ n‖ / (n : ℝ) ^ (1 + δ) ≤
            Λ n / (n : ℝ) ^ (1 + δ) := by
              exact div_le_div_of_nonneg_right
                (mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
                  (norm_le_one χ n)) (Real.rpow_nonneg hnpos.le _)
        _ ≤ Real.log n / (n : ℝ) ^ (1 + δ) := by gcongr
        _ ≤ ((n : ℝ) ^ (δ / 2) / (δ / 2)) / (n : ℝ) ^ (1 + δ) := by
              gcongr
        _ = _ := hpow
    · simp [s]
      linarith
  have hleft : Summable (fun n : ℕ =>
      ‖twistedVonMangoldtCoeff χ n / (n : ℂ) ^ s‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hright
  have hseries : twistedVonMangoldtRightMajorant χ δ t ≤
      (2 / δ) * (1 + 1 / ((1 + δ / 2) - 1)) := by
    unfold twistedVonMangoldtRightMajorant
    change (∑' n : ℕ, ‖twistedVonMangoldtCoeff χ n / (n : ℂ) ^ s‖) ≤ _
    calc
      _ ≤ ∑' n : ℕ, (2 / δ) * (n : ℝ) ^ (-(1 + δ / 2)) :=
        hleft.tsum_le_tsum hterm hright
      _ = (2 / δ) * ∑' n : ℕ, (n : ℝ) ^ (-(1 + δ / 2)) :=
        tsum_mul_left
      _ ≤ (2 / δ) * (1 + 1 / ((1 + δ / 2) - 1)) := by
        gcongr
        exact BombieriVinogradov.tsum_nat_rpow_neg_le
          (1 + δ / 2) (by linarith)
  calc
    twistedVonMangoldtRightMajorant χ δ t
        ≤ (2 / δ) * (1 + 1 / ((1 + δ / 2) - 1)) := hseries
    _ = 2 / δ + 4 / δ ^ 2 := by field_simp [hδ.ne']; ring
    _ ≤ 6 * (1 + δ⁻¹ ^ 2) := by
      have hinv : 1 ≤ δ⁻¹ := by
        rw [inv_eq_one_div, le_div_iff₀ hδ]
        simpa using hδ1
      have hinv0 : 0 ≤ δ⁻¹ := le_of_lt (inv_pos.mpr hδ)
      have hdivsq : 4 / δ ^ 2 = 4 * δ⁻¹ ^ 2 := by
        field_simp [hδ.ne']
      rw [div_eq_mul_inv, hdivsq]
      nlinarith [sq_nonneg (δ⁻¹ - 1)]

private theorem integral_right_inv_one_add_sq_le_inv
    {T : ℝ} (hT : 1 ≤ T) :
    ∫ t in Ici T, (1 + t ^ 2)⁻¹ ≤ T⁻¹ := by
  rw [integral_Ici_eq_integral_Ioi]
  have hmono : ∀ᵐ t ∂volume.restrict (Ioi T),
      (1 + t ^ 2)⁻¹ ≤ t ^ (-2 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := (lt_of_lt_of_le zero_lt_one hT).trans ht
    rw [Real.rpow_neg (le_of_lt ht0), Real.rpow_two]
    exact inv_anti₀ (sq_pos_of_pos ht0) (by nlinarith)
  calc
    ∫ t in Ioi T, (1 + t ^ 2)⁻¹ ≤ ∫ t in Ioi T, t ^ (-2 : ℝ) := by
      refine integral_mono_ae integrable_inv_one_add_sq.integrableOn
        (integrableOn_Ioi_rpow_of_lt (by norm_num) (lt_of_lt_of_le zero_lt_one hT)) hmono
    _ = T⁻¹ := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) (lt_of_lt_of_le zero_lt_one hT)]
      norm_num [Real.rpow_neg_one]

private theorem integral_left_inv_one_add_sq_le_inv
    {T : ℝ} (hT : 1 ≤ T) :
    ∫ t in Iic (-T), (1 + t ^ 2)⁻¹ ≤ T⁻¹ := by
  calc
    ∫ t in Iic (-T), (1 + t ^ 2)⁻¹ =
        ∫ t in Ioi T, (1 + t ^ 2)⁻¹ := by
          rw [integral_Iic_inv_one_add_sq, integral_Ioi_inv_one_add_sq,
            Real.arctan_neg]
          ring
    _ ≤ T⁻¹ := by
      simpa [integral_Ici_eq_integral_Ioi] using
        integral_right_inv_one_add_sq_le_inv hT

set_option maxHeartbeats 3000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Tail bounds on `re s = 1 + δ`: for `0 < δ ≤ 1`, `0 < ε < 1` and `T ≥ 1`, the integrals
of the Perron integrand over `t ≤ -T` and over `t ≥ T` have norm at most
`c X^{1+δ} (1 + δ⁻²) / (ε T)`, where `c` depends only on `ν`. -/
theorem twistedSmoothedPerron_right_tails_quantitative
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1) :
    ∃ c > 0, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
      {δ ε X T : ℝ}, 0 < δ → δ ≤ 1 → 0 < ε → ε < 1 → 0 < X → 1 ≤ T →
      ‖∫ t in Iic (-T),
          twistedSmoothedPerronIntegrand χ ν ε X (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤
          c * X ^ (1 + δ) * (1 + δ⁻¹ ^ 2) / (ε * T) ∧
      ‖∫ t in Ici T,
          twistedSmoothedPerronIntegrand χ ν ε X (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤
          c * X ^ (1 + δ) * (1 + δ⁻¹ ^ 2) / (ε * T) := by
  obtain ⟨C, Cpos, hC⟩ := MellinOfSmooth1b diffν suppν
  refine ⟨6 * C, by positivity, ?_⟩
  intro q _ χ δ ε X T hδ hδ1 hε hε1 hX hT
  have hσ : 1 < 1 + δ := by linarith
  have hσ2 : 1 + δ ≤ 2 := by linarith
  let f : ℝ → ℂ := fun t =>
    twistedSmoothedPerronIntegrand χ ν ε X (((1 + δ : ℝ) : ℂ) + t * I)
  let g : ℝ → ℝ := fun t =>
    6 * (1 + δ⁻¹ ^ 2) * C / ε * X ^ (1 + δ) * (1 + t ^ 2)⁻¹
  have hf : Integrable f := by
    simpa only [f] using
      (twistedSmoothedPerronIntegrand_integrable_right (q := q) (σ := 1 + δ)
        (X := X) (ε := ε) χ diffν νpos suppν mass_one hX hε hε1 hσ hσ2)
  have hg : Integrable g := by
    dsimp [g]
    exact integrable_inv_one_add_sq.const_mul _
  have hpoint (t : ℝ) : ‖f t‖ ≤ g t := by
    have hsre : 1 < (((1 + δ : ℝ) : ℂ) + t * I).re := by simp; linarith
    have hsum : Summable (fun n : ℕ =>
        twistedVonMangoldtCoeff χ n /
          (n : ℂ) ^ (((1 + δ : ℝ) : ℂ) + t * I)) := by
      have h := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hsre
      rw [LSeriesSummable] at h
      convert h using 1
      ext n
      by_cases hn : n = 0
      · simp [LSeries.term, twistedVonMangoldtCoeff, hn]
      · simp [LSeries.term, twistedVonMangoldtCoeff, hn, mul_comm]
    have hseries := norm_tsum_le_tsum_norm hsum.norm
    have hmellin := hC ((1 + δ) / 2) (by positivity)
      (((1 + δ : ℝ) : ℂ) + t * I) (by simp; linarith) (by simp; linarith)
      ε hε hε1
    have hmaj := twistedVonMangoldtRightMajorant_le χ hδ hδ1 t
    dsimp [f, g, twistedSmoothedPerronIntegrand]
    rw [neg_logDeriv_LFunction_eq_tsum_twistedVonMangoldtCoeff χ hsre,
      norm_mul, norm_mul]
    have hseries' :
        ‖∑' n : ℕ, twistedVonMangoldtCoeff χ n /
          (n : ℂ) ^ (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤
          twistedVonMangoldtRightMajorant χ δ t := by
      simpa [twistedVonMangoldtRightMajorant] using hseries
    have hmajor0 : 0 ≤ twistedVonMangoldtRightMajorant χ δ t :=
      tsum_nonneg fun _ => norm_nonneg _
    have hmellinR0 :
        0 ≤ C * (ε * ‖(((1 + δ : ℝ) : ℂ) + t * I)‖ ^ 2)⁻¹ := by positivity
    have hXnorm :
        ‖(X : ℂ) ^ (((1 + δ : ℝ) : ℂ) + t * I)‖ = X ^ (1 + δ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
      simp
    have hXpow0 : 0 ≤ X ^ (1 + δ) := Real.rpow_nonneg hX.le _
    have hfirst :
        ‖∑' n : ℕ, twistedVonMangoldtCoeff χ n /
          (n : ℂ) ^ (((1 + δ : ℝ) : ℂ) + t * I)‖ *
            ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤
          twistedVonMangoldtRightMajorant χ δ t *
            (C * (ε * ‖(((1 + δ : ℝ) : ℂ) + t * I)‖ ^ 2)⁻¹) := by
      calc
        _ ≤ twistedVonMangoldtRightMajorant χ δ t *
            ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (((1 + δ : ℝ) : ℂ) + t * I)‖ :=
          mul_le_mul_of_nonneg_right hseries' (norm_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left hmellin hmajor0
    have hnormsq : 1 + t ^ 2 ≤ ‖(((1 + δ : ℝ) : ℂ) + t * I)‖ ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
      nlinarith
    have hinvnorm :
        (ε * ‖(((1 + δ : ℝ) : ℂ) + t * I)‖ ^ 2)⁻¹ ≤
          ε⁻¹ * (1 + t ^ 2)⁻¹ := by
      rw [mul_inv_rev]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right
        (inv_anti₀ (by nlinarith [sq_nonneg t]) hnormsq) (inv_nonneg.mpr hε.le)
    calc
      ‖∑' n : ℕ, twistedVonMangoldtCoeff χ n /
          (n : ℂ) ^ (((1 + δ : ℝ) : ℂ) + t * I)‖ *
            ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (((1 + δ : ℝ) : ℂ) + t * I)‖ *
              ‖(X : ℂ) ^ (((1 + δ : ℝ) : ℂ) + t * I)‖
          ≤ (twistedVonMangoldtRightMajorant χ δ t *
            (C * (ε * ‖(((1 + δ : ℝ) : ℂ) + t * I)‖ ^ 2)⁻¹)) *
              X ^ (1 + δ) := by rw [← hXnorm]; gcongr
      _ ≤ (6 * (1 + δ⁻¹ ^ 2) *
            (C * (ε * ‖(((1 + δ : ℝ) : ℂ) + t * I)‖ ^ 2)⁻¹)) *
              X ^ (1 + δ) := by
                gcongr
      _ ≤ (6 * (1 + δ⁻¹ ^ 2) * (C * (ε⁻¹ * (1 + t ^ 2)⁻¹))) *
              X ^ (1 + δ) := by
                gcongr
      _ = 6 * (1 + δ⁻¹ ^ 2) * C / ε * X ^ (1 + δ) * (1 + t ^ 2)⁻¹ := by
        ring
  have htail (s : Set ℝ)
      (hdecay : ∫ t in s, (1 + t ^ 2)⁻¹ ≤ T⁻¹) :
      ‖∫ t in s, f t‖ ≤ 6 * C * X ^ (1 + δ) * (1 + δ⁻¹ ^ 2) / (ε * T) := by
    calc
      ‖∫ t in s, f t‖ ≤ ∫ t in s, ‖f t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in s, g t :=
        integral_mono_ae hf.norm.integrableOn hg.integrableOn (Filter.Eventually.of_forall hpoint)
      _ = (6 * (1 + δ⁻¹ ^ 2) * C / ε * X ^ (1 + δ)) *
          ∫ t in s, (1 + t ^ 2)⁻¹ := by
        dsimp only [g]
        rw [integral_const_mul]
      _ ≤ (6 * (1 + δ⁻¹ ^ 2) * C / ε * X ^ (1 + δ)) * T⁻¹ :=
        mul_le_mul_of_nonneg_left hdecay (by positivity)
      _ = _ := by ring
  exact ⟨htail (Iic (-T)) (integral_left_inv_one_add_sq_le_inv hT),
    htail (Ici T) (integral_right_inv_one_add_sq_le_inv hT)⟩

end DirichletCharacter

end

/-! ## Comparison with the sharp sum -/

section

open Set Function Filter Complex Real MeasureTheory
open scoped BigOperators ArithmeticFunction

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]
local notation "λχ" => BombieriVinogradov.lambdaCharacterPrefix

omit [NeZero q] in
/-- Let the cutoff `w(n) = Smooth1 SmoothingF ε (n / X)` lie in `[0, 1]`, equal `1` for
`n ≤ X(1 - c₁ε)` and `0` for `n ≥ X(1 + c₂ε)`. Then
`|∑ₙ Λ(n) χ(n) w(n) - ∑_{n ≤ X} Λ(n) χ(n)| ≤ 2 C ε X log X`. Since `|χ(n)| ≤ 1`, the error
is bounded termwise by the untwisted errors for a lower and an upper cutoff. -/
theorem twistedSmoothedPsiClose_aux
    (SmoothingF : ℝ → ℝ)
    (c₁ : ℝ) (c₁_pos : 0 < c₁) (c₁_lt : c₁ < 1)
    (c₂ : ℝ) (c₂_pos : 0 < c₂) (c₂_lt : c₂ < 2)
    (hc₂ : ∀ (ε x : ℝ), ε ∈ Ioo 0 1 → 1 + c₂ * ε ≤ x → Smooth1 SmoothingF ε x = 0)
    (C : ℝ) (C_eq : C = 6 * (3 * c₁ + c₂))
    (ε : ℝ) (ε_pos : 0 < ε) (ε_lt_one : ε < 1)
    (X : ℝ) (X_pos : 0 < X) (X_gt_three : 3 < X)
    (X_bound_1 : 1 ≤ X * ε * c₁) (X_bound_2 : 1 ≤ X * ε * c₂)
    (smooth1BddAbove : ∀ n : ℕ, 0 < n → Smooth1 SmoothingF ε (n / X) ≤ 1)
    (smooth1BddBelow : ∀ n : ℕ, 0 < n → 0 ≤ Smooth1 SmoothingF ε (n / X))
    (smoothIs1 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ X * (1 - c₁ * ε) →
      Smooth1 SmoothingF ε (n / X) = 1)
    (smoothIs0 : ∀ n : ℕ, 1 + c₂ * ε ≤ (n : ℝ) / X →
      Smooth1 SmoothingF ε (n / X) = 0)
    (χ : DirichletCharacter ℂ q) :
    ‖twistedSmoothedPsi χ SmoothingF ε X - λχ ⌊X⌋₊ q χ‖ ≤
      2 * C * ε * X * Real.log X := by
  let Lower : (ℝ → ℝ) → ℝ → ℝ → ℝ :=
    fun ν e x => if x ≤ 1 then Smooth1 ν e x else 0
  let Upper : (ℝ → ℝ) → ℝ → ℝ → ℝ :=
    fun ν e x => if x ≤ 1 then 1 else Smooth1 ν e x

  have h_outer_gt_one : 1 < 1 + c₂ * ε := by nlinarith [mul_pos c₂_pos ε_pos]
  have h_inner_le_one : 1 - c₁ * ε ≤ 1 := by nlinarith [mul_pos c₁_pos ε_pos]

  have hLowerZero (e x : ℝ) (he : e ∈ Ioo 0 1) (hx : 1 + c₂ * e ≤ x) :
      Lower SmoothingF e x = 0 := by
    have hx1 : ¬ x ≤ 1 := by nlinarith [mul_pos c₂_pos he.1]
    simp [Lower, hx1]
  have hUpperZero (e x : ℝ) (he : e ∈ Ioo 0 1) (hx : 1 + c₂ * e ≤ x) :
      Upper SmoothingF e x = 0 := by
    have hx1 : ¬ x ≤ 1 := by nlinarith [mul_pos c₂_pos he.1]
    simp [Upper, hx1, hc₂ e x he hx]

  have hLowerAbove (n : ℕ) (hn : 0 < n) : Lower SmoothingF ε (n / X) ≤ 1 := by
    by_cases h : (n : ℝ) / X ≤ 1
    · simpa [Lower, h] using smooth1BddAbove n hn
    · simp [Lower, h]
  have hLowerBelow (n : ℕ) (hn : 0 < n) : 0 ≤ Lower SmoothingF ε (n / X) := by
    by_cases h : (n : ℝ) / X ≤ 1
    · simpa [Lower, h] using smooth1BddBelow n hn
    · simp [Lower, h]
  have hUpperAbove (n : ℕ) (hn : 0 < n) : Upper SmoothingF ε (n / X) ≤ 1 := by
    by_cases h : (n : ℝ) / X ≤ 1
    · simp [Upper, h]
    · simpa [Upper, h] using smooth1BddAbove n hn
  have hUpperBelow (n : ℕ) (hn : 0 < n) : 0 ≤ Upper SmoothingF ε (n / X) := by
    by_cases h : (n : ℝ) / X ≤ 1
    · simp [Upper, h]
    · simpa [Upper, h] using smooth1BddBelow n hn

  have hInnerCutoff (n : ℕ) (hnin : (n : ℝ) ≤ X * (1 - c₁ * ε)) :
      (n : ℝ) / X ≤ 1 := by
    rw [div_le_one X_pos]
    exact hnin.trans (mul_le_of_le_one_right X_pos.le h_inner_le_one)
  have hLowerOne (n : ℕ) (hn : 0 < n)
      (hnin : (n : ℝ) ≤ X * (1 - c₁ * ε)) : Lower SmoothingF ε (n / X) = 1 := by
    have hnx := hInnerCutoff n hnin
    simp [Lower, hnx, smoothIs1 n hn hnin]
  have hUpperOne (n : ℕ) (_hn : 0 < n)
      (hnin : (n : ℝ) ≤ X * (1 - c₁ * ε)) : Upper SmoothingF ε (n / X) = 1 := by
    have hnx := hInnerCutoff n hnin
    simp [Upper, hnx]
  have hLowerOuter (n : ℕ) (hn : 1 + c₂ * ε ≤ (n : ℝ) / X) :
      Lower SmoothingF ε (n / X) = 0 := by
    have hnx : ¬ (n : ℝ) / X ≤ 1 := by linarith
    simp [Lower, hnx]
  have hUpperOuter (n : ℕ) (hn : 1 + c₂ * ε ≤ (n : ℝ) / X) :
      Upper SmoothingF ε (n / X) = 0 := by
    have hnx : ¬ (n : ℝ) / X ≤ 1 := by linarith
    simp [Upper, hnx, smoothIs0 n hn]

  have hL := SmoothedChebyshevClose_aux SmoothingF c₁ c₁_pos c₁_lt c₂ c₂_pos c₂_lt
    hLowerZero C C_eq ε ε_pos ε_lt_one X X_pos X_gt_three X_bound_1 X_bound_2
    hLowerAbove hLowerBelow hLowerOne hLowerOuter
  have hU := SmoothedChebyshevClose_aux SmoothingF c₁ c₁_pos c₁_lt c₂ c₂_pos c₂_lt
    hUpperZero C C_eq ε ε_pos ε_lt_one X X_pos X_gt_three X_bound_1 X_bound_2
    hUpperAbove hUpperBelow hUpperOne hUpperOuter

  let Y := ⌊X⌋₊
  let N := ⌊X * (1 + c₂ * ε)⌋₊ + 1
  have hXN : X < (N : ℝ) := by
    have ho : X < X * (1 + c₂ * ε) := by nlinarith
    exact ho.trans (by simpa [N] using Nat.lt_floor_add_one (X * (1 + c₂ * ε)))
  have hYN : Y + 1 ≤ N := by
    have hYlt : Y < N := by
      change ⌊X⌋₊ < N
      exact (Nat.floor_lt X_pos.le).2 hXN
    omega

  have hFzero (n : ℕ) (hn : n ∉ Finset.range N) :
      Smooth1 SmoothingF ε ((n : ℝ) / X) = 0 := by
    have hnN : N ≤ n := by simpa [Finset.mem_range] using hn
    apply smoothIs0
    rw [le_div_iff₀ X_pos]
    have houtN : X * (1 + c₂ * ε) < (N : ℝ) := by
      simpa [N] using Nat.lt_floor_add_one (X * (1 + c₂ * ε))
    have hnNr : (N : ℝ) ≤ n := by exact_mod_cast hnN
    simpa [mul_comm] using houtN.le.trans hnNr
  have hfilt : (Finset.range N).filter (fun n => n ≤ Y) = Finset.range (Y + 1) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hOutsideCutoff (n : ℕ) (hn : n ∉ Finset.range N) : ¬ (n : ℝ) / X ≤ 1 := by
    rw [not_le, one_lt_div X_pos]
    have hnN : N ≤ n := by simpa [Finset.mem_range] using hn
    have hnNr : (N : ℝ) ≤ n := by exact_mod_cast hnN
    exact hXN.trans_le hnNr

  have htwistedFinite : twistedSmoothedPsi χ SmoothingF ε X =
      ∑ n ∈ Finset.range N, twistedVonMangoldtCoeff χ n * Smooth1 SmoothingF ε (n / X) := by
    unfold twistedSmoothedPsi
    apply tsum_eq_sum (s := Finset.range N)
    intro n hn
    simp [hFzero n hn]
  have hprefixFinite : λχ Y q χ =
      ∑ n ∈ Finset.range N,
        twistedVonMangoldtCoeff χ n * (if n ≤ Y then (1 : ℝ) else 0) := by
    rw [BombieriVinogradov.lambdaCharacterPrefix]
    rw [← hfilt, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs with h
    · simp [twistedVonMangoldtCoeff, BombieriVinogradov.lambdaNatCoeff]
    · simp

  have hLowerFinite : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Lower SmoothingF ε (n / X)) =
      ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n * Lower SmoothingF ε (n / X) := by
    apply tsum_eq_sum (s := Finset.range N)
    intro n hn
    have hnx := hOutsideCutoff n hn
    simp [Lower, hnx]
  have hUpperFinite : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Upper SmoothingF ε (n / X)) =
      ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n * Upper SmoothingF ε (n / X) := by
    apply tsum_eq_sum (s := Finset.range N)
    intro n hn
    have hnx := hOutsideCutoff n hn
    simp [Upper, hnx, hFzero n hn]

  have hpsi : Chebyshev.psi X = ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n * (if n ≤ Y then (1 : ℝ) else 0) := by
    rw [Chebyshev.psi_eq_sum_range]
    rw [← hfilt, Finset.sum_filter]
    simp

  have hfloor (n : ℕ) : n ≤ Y ↔ (n : ℝ) / X ≤ 1 := by
    rw [div_le_one X_pos]
    exact Nat.le_floor_iff X_pos.le

  have hpoint (n : ℕ) (hn : n ∈ Finset.range N) :
      ‖twistedVonMangoldtCoeff χ n *
          (Smooth1 SmoothingF ε (n / X) - (if n ≤ Y then (1 : ℝ) else 0))‖ ≤
        ArithmeticFunction.vonMangoldt n * ((if n ≤ Y then (1 : ℝ) else 0) - Lower SmoothingF ε (n / X) +
          (Upper SmoothingF ε (n / X) - (if n ≤ Y then (1 : ℝ) else 0))) := by
    by_cases hn0 : n = 0
    · simp [hn0, twistedVonMangoldtCoeff]
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hchar : ‖χ n‖ ≤ 1 := norm_le_one χ n
    have hF0 := smooth1BddBelow n hnpos
    have hF1 := smooth1BddAbove n hnpos
    rw [norm_mul]
    rw [twistedVonMangoldtCoeff, norm_mul]
    rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hcoeff : ArithmeticFunction.vonMangoldt n * ‖χ n‖ ≤
        ArithmeticFunction.vonMangoldt n :=
      mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg hchar
    apply (mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _)).trans
    apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
    by_cases hny : n ≤ Y
    · have hnx : (n : ℝ) / X ≤ 1 := (hfloor n).mp hny
      simp [hny, Lower, Upper, hnx, abs_of_nonpos (sub_nonpos.mpr hF1)]
    · have hnx : ¬ (n : ℝ) / X ≤ 1 := fun h => hny ((hfloor n).mpr h)
      simp [hny, Lower, Upper, hnx, abs_of_nonneg hF0]

  rw [htwistedFinite, hprefixFinite, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    ‖∑ n ∈ Finset.range N, twistedVonMangoldtCoeff χ n *
        (Smooth1 SmoothingF ε (n / X) - (if n ≤ Y then (1 : ℝ) else 0))‖
        ≤ ∑ n ∈ Finset.range N, ‖twistedVonMangoldtCoeff χ n *
          (Smooth1 SmoothingF ε (n / X) - (if n ≤ Y then (1 : ℝ) else 0))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n *
        ((if n ≤ Y then (1 : ℝ) else 0) - Lower SmoothingF ε (n / X) +
          (Upper SmoothingF ε (n / X) - (if n ≤ Y then (1 : ℝ) else 0))) :=
      Finset.sum_le_sum hpoint
    _ = ‖((∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Lower SmoothingF ε (n / X) : ℝ) : ℂ) - Chebyshev.psi X‖ +
        ‖((∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Upper SmoothingF ε (n / X) : ℝ) : ℂ) - Chebyshev.psi X‖ := by
      rw [hLowerFinite, hUpperFinite, hpsi]
      have hLle : (∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n * Lower SmoothingF ε (n / X)) ≤
          ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n * (if n ≤ Y then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases hn0 : n = 0
        · simp [hn0]
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
        by_cases hny : n ≤ Y
        · have hnx : (n : ℝ) / X ≤ 1 := (hfloor n).mp hny
          simpa [hny, Lower, hnx] using smooth1BddAbove n hnpos
        · have hnx : ¬ (n : ℝ) / X ≤ 1 := fun h => hny ((hfloor n).mpr h)
          simp [hny, Lower, hnx]
      have hIleU : (∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n * (if n ≤ Y then (1 : ℝ) else 0)) ≤
          ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n * Upper SmoothingF ε (n / X) := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases hn0 : n = 0
        · simp [hn0, Upper]
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
        by_cases hny : n ≤ Y
        · have hnx : (n : ℝ) / X ≤ 1 := (hfloor n).mp hny
          simp [hny, Upper, hnx]
        · have hnx : ¬ (n : ℝ) / X ≤ 1 := fun h => hny ((hfloor n).mpr h)
          simpa [hny, Upper, hnx] using smooth1BddBelow n hnpos
      rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr hLle),
        abs_of_nonneg (sub_nonneg.mpr hIleU)]
      simp_rw [mul_add, mul_sub]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      ring
    _ ≤ C * ε * X * Real.log X + C * ε * X * Real.log X := add_le_add hL hU
    _ = 2 * C * ε * X * Real.log X := by ring

end DirichletCharacter

end
