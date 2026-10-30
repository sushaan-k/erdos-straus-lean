

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic
import ErdosStraus.BombieriVinogradov.PNT.ResidueCalcOnRectangles

section

/-!
# An exponentially damped Perron kernel

For `ε > 0` the step kernel `K_ε(x) = 1/2 + arctan (x / ε) / π` satisfies
`K_ε(x) = 1/2 + (1/π) ∫_0^∞ e^{-ε t} sin (t x) / t dt` and `|1_{x > 0} - K_ε(x)| ≤ ε / (π |x|)`
for `x ≠ 0`. At `x = log ((Y + 1/2) / n)` with `n, M ≥ 1` and `Y ≤ M` the error is at most
`8 ε M / π`. We also show `∫_0^∞ e^{-ε t} min (1, L t) / t dt ≤ L + log (1/ε) + 1` for `0 < ε ≤ 1`.
-/

noncomputable section

open MeasureTheory
open scoped Interval

namespace BombieriVinogradov

/-- The function `t ↦ sin (t x) / t`, extended by its limit `x` at `t = 0`. -/
def truncatedPerronIntegrand (x t : ℝ) : ℝ :=
  if t = 0 then x else Real.sin (t * x) / t

theorem truncatedPerronIntegrand_eq_mul_sinc (x t : ℝ) :
    truncatedPerronIntegrand x t = x * Real.sinc (t * x) := by
  by_cases ht : t = 0
  · simp [truncatedPerronIntegrand, ht]
  by_cases hx : x = 0
  · simp [truncatedPerronIntegrand, ht, hx]
  · rw [truncatedPerronIntegrand, if_neg ht, Real.sinc_of_ne_zero (mul_ne_zero ht hx)]
    field_simp

@[simp]
theorem truncatedPerronIntegrand_zero_left (t : ℝ) :
    truncatedPerronIntegrand 0 t = 0 := by
  rw [truncatedPerronIntegrand_eq_mul_sinc]
  simp

@[simp]
theorem truncatedPerronIntegrand_neg_left (x t : ℝ) :
    truncatedPerronIntegrand (-x) t = -truncatedPerronIntegrand x t := by
  simp only [truncatedPerronIntegrand_eq_mul_sinc]
  rw [mul_neg, Real.sinc_neg]
  ring

theorem continuous_truncatedPerronIntegrand_right (x : ℝ) :
    Continuous (truncatedPerronIntegrand x) := by
  change Continuous (fun t ↦ truncatedPerronIntegrand x t)
  simp_rw [truncatedPerronIntegrand_eq_mul_sinc]
  fun_prop

theorem abs_truncatedPerronIntegrand_le (x t : ℝ) :
    |truncatedPerronIntegrand x t| ≤ |x| := by
  rw [truncatedPerronIntegrand_eq_mul_sinc, abs_mul]
  simpa using mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one (t * x)) (abs_nonneg x)

end BombieriVinogradov

end
end

section

/-! ## The half-integer cutoff and the Laplace transform of sinc -/

open scoped BigOperators Interval

namespace BombieriVinogradov

open Finset
open Topology Filter Set Asymptotics

/-- The half-integer cutoff `Y + 1/2`. -/
noncomputable def perronHalfStep (Y : ℕ) : ℝ :=
  Y + 1 / 2

theorem natCast_lt_perronHalfStep_iff {n Y : ℕ} :
    (n : ℝ) < perronHalfStep Y ↔ n ≤ Y := by
  unfold perronHalfStep
  constructor
  · intro h
    by_contra hnY
    have hYn : Y + 1 ≤ n := by omega
    have hYnR : (Y : ℝ) + 1 ≤ n := by exact_mod_cast hYn
    norm_num at h
    linarith
  · intro hnY
    have hnYR : (n : ℝ) ≤ Y := by exact_mod_cast hnY
    norm_num
    linarith

theorem perronHalfStep_div_natCast_pos {n Y : ℕ} (hn : n ≠ 0) :
    0 < perronHalfStep Y / (n : ℝ) := by
  apply div_pos
  · unfold perronHalfStep
    positivity
  · exact_mod_cast Nat.pos_of_ne_zero hn

private theorem one_div_four_mul_le_one_sub_inv_div_of_half_gap
    {x n M : ℝ} (hx : 0 < x) (hM : 1 ≤ M)
    (hgap : 1 / 2 ≤ x - n) (hxM : x ≤ 2 * M) :
    1 / (4 * M) ≤ 1 - (x / n)⁻¹ := by
  have hMp : 0 < M := lt_of_lt_of_le (by norm_num) hM
  rw [inv_div, div_eq_mul_inv]
  apply (le_sub_iff_add_le).2
  field_simp
  nlinarith

/-- `|log ((Y + 1/2) / n)| ≥ 1 / (4 M)` for `1 ≤ n ≤ M` and `Y ≤ M`, since `n` is at
distance at least `1/2` from the cutoff and `log u ≥ 1 - 1/u`. -/
theorem one_div_four_mul_le_abs_log_perronHalfStep_div
    {n Y M : ℕ} (hn : n ≠ 0) (hM : 1 ≤ M)
    (hYM : Y ≤ M) (hnM : n ≤ M) :
    1 / (4 * (M : ℝ)) ≤
      |Real.log (perronHalfStep Y / (n : ℝ))| := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hYMR : (Y : ℝ) ≤ M := by exact_mod_cast hYM
  have hnMR : (n : ℝ) ≤ M := by exact_mod_cast hnM
  have hx : 0 < perronHalfStep Y := by
    unfold perronHalfStep
    positivity
  have hratio : 0 < perronHalfStep Y / (n : ℝ) :=
    div_pos hx hnR
  by_cases h : n ≤ Y
  · have hnY : (n : ℝ) ≤ Y := by exact_mod_cast h
    have hgap : (1 / 2 : ℝ) ≤ perronHalfStep Y - n := by
      unfold perronHalfStep
      norm_num
      linarith
    have hxM : perronHalfStep Y ≤ 2 * (M : ℝ) := by
      unfold perronHalfStep
      norm_num
      linarith
    have hlow :=
      one_div_four_mul_le_one_sub_inv_div_of_half_gap hx hMR hgap hxM
    have hone : (1 : ℝ) ≤ perronHalfStep Y / (n : ℝ) := by
      rw [one_le_div₀ hnR]
      linarith
    rw [abs_of_nonneg (Real.log_nonneg hone)]
    exact hlow.trans (Real.one_sub_inv_le_log_of_pos hratio)
  · have hYn : Y + 1 ≤ n := by omega
    have hYnR : (Y : ℝ) + 1 ≤ n := by exact_mod_cast hYn
    have hgap : (1 / 2 : ℝ) ≤
        (n : ℝ) - perronHalfStep Y := by
      unfold perronHalfStep
      norm_num
      linarith
    have hn2M : (n : ℝ) ≤ 2 * (M : ℝ) := by nlinarith
    have hrevpos : 0 < (n : ℝ) / perronHalfStep Y :=
      div_pos hnR hx
    have hlow :=
      one_div_four_mul_le_one_sub_inv_div_of_half_gap hnR hMR hgap hn2M
    have hle : perronHalfStep Y / (n : ℝ) ≤ 1 := by
      rw [div_le_one hnR]
      linarith
    rw [abs_of_nonpos (Real.log_nonpos hratio.le hle)]
    calc
      1 / (4 * (M : ℝ)) ≤
          1 - (((n : ℝ) / perronHalfStep Y)⁻¹) := hlow
      _ ≤ Real.log ((n : ℝ) / perronHalfStep Y) :=
        Real.one_sub_inv_le_log_of_pos hrevpos
      _ = -Real.log (perronHalfStep Y / (n : ℝ)) := by
        rw [← Real.log_inv, inv_div]

private theorem integral_Ioi_exp_neg_mul_sin
    (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sin x =
      1 / (a ^ 2 + 1) := by
  let z : ℂ := (-(a : ℂ)) + Complex.I
  have hzre : z.re < 0 := by
    simp [z, ha]
  have hint : MeasureTheory.Integrable
      (fun x : ℝ => Complex.exp (z * x))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    integrableOn_exp_mul_complex_Ioi (a := z) hzre 0
  have him := integral_im
    (μ := MeasureTheory.volume.restrict (Set.Ioi 0)) hint
  have hpoint :
      (fun x : ℝ => Real.exp (-a * x) * Real.sin x) =
        fun x : ℝ => (Complex.exp (z * x)).im := by
    funext x
    simp [z, Complex.exp_im, mul_add, mul_comm]
  calc
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sin x =
        ∫ x : ℝ in Set.Ioi 0, (Complex.exp (z * x)).im := by
      rw [hpoint]
    _ = (∫ x : ℝ in Set.Ioi 0, Complex.exp (z * x)).im := by
      simpa using him
    _ = (-Complex.exp (z * (0 : ℝ)) / z).im := by
      rw [integral_exp_mul_complex_Ioi (a := z) hzre 0]
    _ = 1 / (a ^ 2 + 1) := by
      simp [z, Complex.div_im, Complex.normSq]
      ring

private theorem integral_Ioi_one_div_one_add_sq
    (a : ℝ) (ha : 0 < a) :
    ∫ u : ℝ in Set.Ioi a, (1 / (u ^ 2 + 1) : ℝ) =
      Real.arctan a⁻¹ := by
  have h :
      ∫ u : ℝ in Set.Ioi a, (1 / (u ^ 2 + 1) : ℝ) =
        Real.pi / 2 - Real.arctan a := by
    simpa [one_div, add_comm] using
      integral_Ioi_inv_one_add_sq (i := a)
  rw [h]
  exact (Real.arctan_inv_of_pos ha).symm

private theorem integral_Ioi_exp_neg_mul
    (a x : ℝ) (hx : 0 < x) :
    ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x) =
      Real.exp (-a * x) / x := by
  have h := integral_exp_mul_Ioi (a := -x) (by linarith : -x < 0) a
  calc
    ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x) =
        ∫ u : ℝ in Set.Ioi a, Real.exp ((-x) * u) := by
      congr with u
      ring_nf
    _ = Real.exp (-a * x) / x := by
      rw [h]
      field_simp [hx.ne']

private theorem integral_Ioi_exp_neg_mul_mul_sin
    (a x : ℝ) (hx : 0 < x) :
    ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x) * Real.sin x =
      Real.exp (-a * x) * Real.sinc x := by
  rw [MeasureTheory.integral_mul_const]
  rw [integral_Ioi_exp_neg_mul a x hx]
  rw [Real.sinc_of_ne_zero hx.ne']
  field_simp [hx.ne']

private theorem integrable_exp_neg_mul_sin_prod_Ioi
    (a : ℝ) (ha : 0 < a) :
    MeasureTheory.Integrable
      (Function.uncurry
        (fun x u : ℝ => Real.exp (-u * x) * Real.sin x))
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict (Set.Ioi a))) := by
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  let ν := MeasureTheory.volume.restrict (Set.Ioi a)
  change MeasureTheory.Integrable
    (Function.uncurry
      (fun x u : ℝ => Real.exp (-u * x) * Real.sin x)) (μ.prod ν)
  have hsm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry
        (fun x u : ℝ => Real.exp (-u * x) * Real.sin x))
      (μ.prod ν) := by
    exact (by fun_prop : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry
        (fun x u : ℝ => Real.exp (-u * x) * Real.sin x))
      (μ.prod ν))
  rw [MeasureTheory.integrable_prod_iff hsm]
  constructor
  · dsimp [μ]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    change MeasureTheory.Integrable
      (fun u : ℝ => Real.exp (-u * x) * Real.sin x) ν
    have h_exp : MeasureTheory.Integrable
        (fun u : ℝ => Real.exp (-u * x)) ν := by
      dsimp [ν]
      change MeasureTheory.IntegrableOn
        (fun u : ℝ => Real.exp (-u * x)) (Set.Ioi a)
      simpa [mul_comm] using
        integrableOn_exp_mul_Ioi (a := -x) (neg_lt_zero.mpr hx) a
    exact h_exp.mul_const (Real.sin x)
  · have h_exp_a : MeasureTheory.Integrable
        (fun x : ℝ => Real.exp (-a * x)) μ := by
      dsimp [μ]
      change MeasureTheory.IntegrableOn
        (fun x : ℝ => Real.exp (-a * x)) (Set.Ioi 0)
      simpa [mul_comm] using
        exp_neg_integrableOn_Ioi (0 : ℝ) (b := a) ha
    refine h_exp_a.mono ?_ ?_
    · exact hsm.norm.integral_prod_right'
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hx
      have h_exp_x : MeasureTheory.Integrable
          (fun y : ℝ => Real.exp (-y * x)) ν := by
        dsimp [ν]
        change MeasureTheory.IntegrableOn
          (fun y : ℝ => Real.exp (-y * x)) (Set.Ioi a)
        simpa [mul_comm] using
          integrableOn_exp_mul_Ioi (a := -x) (neg_lt_zero.mpr hx0) a
      have h_lhs : MeasureTheory.Integrable
          (fun y : ℝ =>
            ‖Function.uncurry
              (fun x u : ℝ => Real.exp (-u * x) * Real.sin x)
              (x, y)‖) ν := by
        simpa [Function.uncurry] using
          (h_exp_x.mul_const (Real.sin x)).norm
      have h_rhs : MeasureTheory.Integrable
          (fun y : ℝ => Real.exp (-y * x) * x) ν :=
        h_exp_x.mul_const x
      calc
        ‖∫ y : ℝ, ‖Function.uncurry
            (fun x u : ℝ => Real.exp (-u * x) * Real.sin x)
            (x, y)‖ ∂ν‖ =
            ∫ y : ℝ, ‖Function.uncurry
              (fun x u : ℝ => Real.exp (-u * x) * Real.sin x)
              (x, y)‖ ∂ν := by
          rw [Real.norm_eq_abs, abs_of_nonneg]
          exact MeasureTheory.integral_nonneg fun y => norm_nonneg _
        _ ≤ ∫ y : ℝ, Real.exp (-y * x) * x ∂ν := by
          refine MeasureTheory.integral_mono_ae h_lhs h_rhs ?_
          filter_upwards with y
          rw [Function.uncurry, Real.norm_eq_abs, abs_mul,
            abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul_of_nonneg_left
            (by simpa [abs_of_pos hx0] using
              (Real.abs_sin_le_abs (x := x)))
            (Real.exp_pos _).le
        _ = Real.exp (-a * x) := by
          dsimp [ν]
          rw [MeasureTheory.integral_mul_const]
          rw [integral_Ioi_exp_neg_mul a x hx0]
          field_simp [hx0.ne']
        _ = ‖Real.exp (-a * x)‖ := by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- `∫_0^∞ e^{-a x} sinc x dx = arctan (1/a)` for `a > 0`, by writing
`e^{-a x} sinc x = ∫_a^∞ e^{-u x} sin x du` and exchanging the integrals. -/
theorem integral_exp_neg_mul_sinc_eq_arctan_inv
    (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sinc x =
      Real.arctan a⁻¹ := by
  have hswap :
      (∫ x : ℝ in Set.Ioi 0,
        ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x) * Real.sin x) =
      ∫ u : ℝ in Set.Ioi a,
        ∫ x : ℝ in Set.Ioi 0, Real.exp (-u * x) * Real.sin x := by
    simpa [Function.uncurry] using
      MeasureTheory.integral_integral_swap
        (integrable_exp_neg_mul_sin_prod_Ioi a ha)
  calc
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sinc x =
        ∫ x : ℝ in Set.Ioi 0,
          ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x) * Real.sin x := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards
        [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      exact (integral_Ioi_exp_neg_mul_mul_sin a x hx).symm
    _ = ∫ u : ℝ in Set.Ioi a,
        ∫ x : ℝ in Set.Ioi 0,
          Real.exp (-u * x) * Real.sin x := hswap
    _ = ∫ u : ℝ in Set.Ioi a, (1 / (u ^ 2 + 1) : ℝ) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards
        [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      exact integral_Ioi_exp_neg_mul_sin u (lt_trans ha hu)
    _ = Real.arctan a⁻¹ :=
      integral_Ioi_one_div_one_add_sq a ha

/-- `|log ((Y + 1/2) / n)| ≥ 1 / (8 M)` for every `n ≥ 1`, not only for `n ≤ M`. -/
theorem one_div_eight_mul_le_abs_log_perronHalfStep_div
    {n Y M : ℕ} (hn : n ≠ 0) (hM : 1 ≤ M) (hYM : Y ≤ M) :
    1 / (8 * (M : ℝ)) ≤
      |Real.log (perronHalfStep Y / (n : ℝ))| := by
  by_cases hnM : n ≤ M
  · calc
      1 / (8 * (M : ℝ)) ≤ 1 / (4 * (M : ℝ)) := by
        have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
        gcongr
        norm_num
      _ ≤ |Real.log (perronHalfStep Y / (n : ℝ))| :=
        one_div_four_mul_le_abs_log_perronHalfStep_div
          hn hM hYM hnM
  · have hnlow : M + 1 ≤ n := by omega
    have hnR : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hMR : (0 : ℝ) < M := by
      exact_mod_cast (show 0 < M by omega)
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hx : 0 < perronHalfStep Y := by
      unfold perronHalfStep
      positivity
    have hxM :
        perronHalfStep Y ≤ (M : ℝ) + 1 / 2 := by
      unfold perronHalfStep
      have hYR : (Y : ℝ) ≤ M := by exact_mod_cast hYM
      linarith
    have hnMR : (M : ℝ) + 1 ≤ n := by
      exact_mod_cast hnlow
    have hratio :
        perronHalfStep Y / (n : ℝ) < 1 := by
      rw [div_lt_one hnR]
      linarith
    rw [abs_of_neg (Real.log_neg
      (perronHalfStep_div_natCast_pos hn) hratio)]
    rw [← Real.log_inv, inv_div]
    have hrev : 0 < (n : ℝ) / perronHalfStep Y :=
      div_pos hnR hx
    have hratioBound :
        perronHalfStep Y / (n : ℝ) ≤
          ((M : ℝ) + 1 / 2) / ((M : ℝ) + 1) := by
      exact div_le_div₀ (by positivity) hxM (by positivity) hnMR
    calc
      1 / (8 * (M : ℝ)) ≤
          1 - (perronHalfStep Y / (n : ℝ)) := by
        calc
          1 / (8 * (M : ℝ)) ≤
              1 - (((M : ℝ) + 1 / 2) / ((M : ℝ) + 1)) := by
            field_simp
            ring_nf
            nlinarith
          _ ≤ 1 - (perronHalfStep Y / (n : ℝ)) :=
            sub_le_sub_left hratioBound 1
      _ = 1 - (((n : ℝ) / perronHalfStep Y)⁻¹) := by
        rw [inv_div]
      _ ≤ Real.log ((n : ℝ) / perronHalfStep Y) :=
        Real.one_sub_inv_le_log_of_pos hrev

end BombieriVinogradov

end

section

/-! ## The damped step kernel -/

noncomputable section

open MeasureTheory
open scoped Interval

namespace BombieriVinogradov

/-- The step kernel `K_ε(x) = 1/2 + arctan (x / ε) / π`. -/
def dampedArctanPerronKernel (ε x : ℝ) : ℝ :=
  1 / 2 + Real.arctan (x / ε) / Real.pi

/-- The case `x > 0`, by the substitution `u = x t`. -/
private theorem integral_exp_neg_mul_truncatedPerronIntegrand_of_pos
    {ε x : ℝ} (hε : 0 < ε) (hx : 0 < x) :
    ∫ t : ℝ in Set.Ioi 0,
        Real.exp (-ε * t) * truncatedPerronIntegrand x t =
      Real.arctan (x / ε) := by
  let g : ℝ → ℝ := fun u => Real.exp (-(ε / x) * u) * Real.sinc u
  have hscale := MeasureTheory.integral_comp_mul_left_Ioi g 0 hx
  have hbase :=
    BombieriVinogradov.integral_exp_neg_mul_sinc_eq_arctan_inv
      (ε / x) (div_pos hε hx)
  rw [mul_zero] at hscale
  calc
    (∫ t : ℝ in Set.Ioi 0,
        Real.exp (-ε * t) * truncatedPerronIntegrand x t) =
        ∫ t : ℝ in Set.Ioi 0, x * g (x * t) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t
          rw [truncatedPerronIntegrand_eq_mul_sinc]
          dsimp only [g]
          have hexpArg : -(ε / x) * (x * t) = -ε * t := by
            field_simp [hx.ne']
          rw [hexpArg]
          ring_nf
    _ = x * ∫ t : ℝ in Set.Ioi 0, g (x * t) := by
          rw [MeasureTheory.integral_const_mul]
    _ = x * (x⁻¹ * ∫ u : ℝ in Set.Ioi 0, g u) := by
          rw [hscale]
          rfl
    _ = ∫ u : ℝ in Set.Ioi 0, g u := by field_simp [hx.ne']
    _ = Real.arctan ((ε / x)⁻¹) := hbase
    _ = Real.arctan (x / ε) := by
          congr 1
          field_simp [hε.ne', hx.ne']

/-- `∫_0^∞ e^{-ε t} sin (t x) / t dt = arctan (x / ε)` for `ε > 0`. -/
theorem integral_exp_neg_mul_truncatedPerronIntegrand_eq_arctan_div
    (ε x : ℝ) (hε : 0 < ε) :
    ∫ t : ℝ in Set.Ioi 0,
        Real.exp (-ε * t) * truncatedPerronIntegrand x t =
      Real.arctan (x / ε) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hpos : 0 < -x := neg_pos.mpr hx
    have h := integral_exp_neg_mul_truncatedPerronIntegrand_of_pos hε hpos
    calc
      (∫ t : ℝ in Set.Ioi 0,
          Real.exp (-ε * t) * truncatedPerronIntegrand x t) =
          -(∫ t : ℝ in Set.Ioi 0,
            Real.exp (-ε * t) * truncatedPerronIntegrand (-x) t) := by
              rw [← MeasureTheory.integral_neg]
              apply MeasureTheory.integral_congr_ae
              filter_upwards with t
              rw [truncatedPerronIntegrand_neg_left]
              ring
      _ = -Real.arctan ((-x) / ε) := by rw [h]
      _ = Real.arctan (x / ε) := by
            rw [show (-x) / ε = -(x / ε) by ring, Real.arctan_neg]
            ring
  · subst x
    simp
  · exact integral_exp_neg_mul_truncatedPerronIntegrand_of_pos hε hx

/-- `K_ε(x) = 1/2 + (1/π) ∫_0^∞ e^{-ε t} sin (t x) / t dt` for `ε > 0`. -/
theorem dampedArctanPerronKernel_eq_half_add_integral
    (ε x : ℝ) (hε : 0 < ε) :
    dampedArctanPerronKernel ε x =
      1 / 2 + (1 / Real.pi) *
        ∫ t : ℝ in Set.Ioi 0,
          Real.exp (-ε * t) * truncatedPerronIntegrand x t := by
  rw [integral_exp_neg_mul_truncatedPerronIntegrand_eq_arctan_div ε x hε]
  unfold dampedArctanPerronKernel
  ring

theorem arctan_le_self_of_nonneg {z : ℝ} (hz : 0 ≤ z) :
    Real.arctan z ≤ z := by
  simpa only [Real.tan_arctan] using
    Real.le_tan (Real.arctan_nonneg.mpr hz) (Real.arctan_lt_pi_div_two z)

theorem dampedArctanPerronKernel_neg (ε x : ℝ) :
    dampedArctanPerronKernel ε (-x) = 1 - dampedArctanPerronKernel ε x := by
  unfold dampedArctanPerronKernel
  rw [neg_div, Real.arctan_neg]
  ring

private theorem abs_one_sub_dampedArctanPerronKernel_le
    {ε x : ℝ} (hε : 0 < ε) (hx : 0 < x) :
    |1 - dampedArctanPerronKernel ε x| ≤ ε / (Real.pi * |x|) := by
  let z := x / ε
  have hz : 0 < z := div_pos hx hε
  have hnonneg : 0 ≤ 1 - dampedArctanPerronKernel ε x := by
    rw [sub_nonneg]
    have hdiv : Real.arctan z / Real.pi < 1 / 2 := by
      rw [div_lt_iff₀ Real.pi_pos]
      nlinarith [Real.arctan_lt_pi_div_two z]
    unfold dampedArctanPerronKernel
    rw [show x / ε = z by rfl]
    linarith
  rw [abs_of_nonneg hnonneg]
  calc
    1 - dampedArctanPerronKernel ε x = Real.arctan z⁻¹ / Real.pi := by
      rw [Real.arctan_inv_of_pos hz]
      unfold dampedArctanPerronKernel
      rw [show x / ε = z by rfl]
      field_simp [Real.pi_ne_zero]
      ring
    _ ≤ z⁻¹ / Real.pi := by
      exact (div_le_div_iff_of_pos_right Real.pi_pos).2
        (arctan_le_self_of_nonneg (inv_nonneg.mpr hz.le))
    _ = ε / (Real.pi * |x|) := by
      rw [abs_of_pos hx]
      dsimp only [z]
      field_simp [hε.ne', hx.ne', Real.pi_ne_zero]

/-- `|1_{x > 0} - K_ε(x)| ≤ ε / (π |x|)` for `x ≠ 0`, since
`π/2 - arctan z = arctan (1/z) ≤ 1/z` for `z > 0`. -/
theorem abs_indicator_sub_dampedArctanPerronKernel_le
    {ε x : ℝ} (hε : 0 < ε) (hx : x ≠ 0) :
    |(if 0 < x then 1 else 0 : ℝ) - dampedArctanPerronKernel ε x| ≤
      ε / (Real.pi * |x|) := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have hpos : 0 < -x := neg_pos.mpr hxneg
    have hbound := abs_one_sub_dampedArctanPerronKernel_le hε hpos
    rw [dampedArctanPerronKernel_neg] at hbound
    simpa [if_neg (not_lt.mpr hxneg.le), abs_neg] using hbound
  · simpa [if_pos hxpos] using
      (abs_one_sub_dampedArctanPerronKernel_le hε hxpos)

/-- `|1_{n ≤ Y} - K_ε(log ((Y + 1/2) / n))| ≤ 8 ε M / π` for `n, M ≥ 1` and `Y ≤ M`,
using `|log ((Y + 1/2) / n)| ≥ 1 / (8 M)`. -/
theorem abs_halfStepIndicator_sub_dampedArctanPerronKernel_le
    {ε : ℝ} {n Y M : ℕ} (hε : 0 < ε) (hn : n ≠ 0)
    (hM : 1 ≤ M) (hYM : Y ≤ M) :
    |(if n ≤ Y then 1 else 0 : ℝ) -
        dampedArctanPerronKernel ε
          (Real.log
            (BombieriVinogradov.perronHalfStep Y / (n : ℝ)))| ≤
      8 * ε * (M : ℝ) / Real.pi := by
  let r := BombieriVinogradov.perronHalfStep Y / (n : ℝ)
  let x := Real.log r
  have hr : 0 < r :=
    BombieriVinogradov.perronHalfStep_div_natCast_pos hn
  have hcut : 0 < x ↔ n ≤ Y := by
    dsimp only [x]
    rw [Real.log_pos_iff hr.le]
    dsimp only [r]
    rw [one_lt_div₀ (by exact_mod_cast Nat.pos_of_ne_zero hn)]
    exact BombieriVinogradov.natCast_lt_perronHalfStep_iff
  have hsep : 1 / (8 * (M : ℝ)) ≤ |x| := by
    exact BombieriVinogradov.one_div_eight_mul_le_abs_log_perronHalfStep_div
      hn hM hYM
  have hMpos : (0 : ℝ) < M := by
    exact_mod_cast (show 0 < M by omega)
  have hxabs : 0 < |x| :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (8 * (M : ℝ))) hsep
  have hx : x ≠ 0 := fun hx0 => by simp [hx0] at hxabs
  have hbound := abs_indicator_sub_dampedArctanPerronKernel_le hε hx
  simp only [hcut] at hbound
  have hinv : 1 / |x| ≤ 8 * (M : ℝ) := by
    rw [div_le_iff₀ hxabs]
    rw [div_le_iff₀ (mul_pos (by norm_num) hMpos)] at hsep
    nlinarith
  calc
    |(if n ≤ Y then 1 else 0 : ℝ) -
        dampedArctanPerronKernel ε
          (Real.log
            (BombieriVinogradov.perronHalfStep Y / (n : ℝ)))| =
        |(if n ≤ Y then 1 else 0 : ℝ) - dampedArctanPerronKernel ε x| := by rfl
    _ ≤ ε / (Real.pi * |x|) := hbound
    _ = (ε / Real.pi) * (1 / |x|) := by field_simp [Real.pi_ne_zero, hxabs.ne']
    _ ≤ (ε / Real.pi) * (8 * (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hinv (div_nonneg hε.le Real.pi_pos.le)
    _ = 8 * ε * (M : ℝ) / Real.pi := by ring

end BombieriVinogradov

end
end

section

/-! ## The damped majorant integral -/

open Real Set MeasureTheory intervalIntegral

namespace BombieriVinogradov

/-- The integrand `e^{-ε t} min (1, L t) / t`, set to `0` at `t = 0`. -/
noncomputable def dampedPerronMajorantIntegrand (ε L t : ℝ) : ℝ :=
  if t = 0 then 0 else Real.exp (-ε * t) * min 1 (L * t) / t

lemma dampedPerronMajorantIntegrand_measurable (ε L : ℝ) : Measurable (dampedPerronMajorantIntegrand ε L) := by
  unfold dampedPerronMajorantIntegrand
  apply Measurable.ite (by simpa only [Set.ofPred_eq_eq_singleton] using measurableSet_singleton (0 : ℝ))
  · fun_prop
  · fun_prop

lemma dampedPerronMajorantIntegrand_nonneg {ε L t : ℝ} (hL : 0 ≤ L) (ht : 0 ≤ t) :
    0 ≤ dampedPerronMajorantIntegrand ε L t := by
  by_cases h0 : t = 0
  · simp [dampedPerronMajorantIntegrand, h0]
  · rw [dampedPerronMajorantIntegrand, if_neg h0]
    positivity

lemma dampedPerronMajorantIntegrand_le_head {ε L t : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (ht : t ∈ Ioc (0 : ℝ) 1) : dampedPerronMajorantIntegrand ε L t ≤ L := by
  rw [dampedPerronMajorantIntegrand, if_neg ht.1.ne']
  have he : Real.exp (-ε * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1.le])
  have hm0 : 0 ≤ min 1 (L * t) := le_min zero_le_one (mul_nonneg hL ht.1.le)
  have hm : min 1 (L * t) ≤ L * t := min_le_right _ _
  rw [div_le_iff₀ ht.1]
  nlinarith [Real.exp_pos (-ε * t)]

lemma dampedPerronMajorantIntegrand_le_inv {ε L t : ℝ} (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (ht : 1 ≤ t) : dampedPerronMajorantIntegrand ε L t ≤ t⁻¹ := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  rw [dampedPerronMajorantIntegrand, if_neg ht0.ne']
  have he : Real.exp (-ε * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hm0 : 0 ≤ min 1 (L * t) := le_min zero_le_one (mul_nonneg hL ht0.le)
  have hm : min 1 (L * t) ≤ 1 := min_le_left _ _
  rw [div_eq_mul_inv]
  have hi : 0 ≤ t⁻¹ := inv_nonneg.mpr ht0.le
  have hp : Real.exp (-ε * t) * min 1 (L * t) ≤ 1 := by
    nlinarith [Real.exp_pos (-ε * t)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hp hi

lemma dampedPerronMajorantIntegrand_le_tail {ε L t : ℝ} (hε : 0 < ε) (_hL : 0 ≤ L)
    (ht : ε⁻¹ ≤ t) : dampedPerronMajorantIntegrand ε L t ≤ ε * Real.exp (-ε * t) := by
  have ht0 : 0 < t := (inv_pos.mpr hε).trans_le ht
  have hi : t⁻¹ ≤ ε := by
    rw [inv_le_comm₀ ht0 hε]
    simpa [one_div] using ht
  calc
    dampedPerronMajorantIntegrand ε L t ≤ t⁻¹ * Real.exp (-ε * t) := by
      rw [dampedPerronMajorantIntegrand, if_neg ht0.ne', div_eq_mul_inv]
      have hm : min 1 (L * t) ≤ 1 := min_le_left _ _
      have he0 : 0 ≤ Real.exp (-ε * t) := (Real.exp_pos _).le
      have hi0 : 0 ≤ t⁻¹ := inv_nonneg.mpr ht0.le
      nlinarith [mul_le_mul_of_nonneg_left hm he0]
    _ ≤ ε * Real.exp (-ε * t) := by
      gcongr

lemma dampedPerronMajorant_integrableOn_head {ε L : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε) :
    IntegrableOn (dampedPerronMajorantIntegrand ε L) (Ioc (0 : ℝ) 1) := by
  apply (integrableOn_const (μ := volume) (C := L)
    ((measure_Ioc_lt_top (μ := volume) : volume (Ioc (0 : ℝ) 1) < ⊤).ne)).mono'
  · exact (dampedPerronMajorantIntegrand_measurable ε L).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (dampedPerronMajorantIntegrand_nonneg hL ht.1.le)]
    exact dampedPerronMajorantIntegrand_le_head hL hε ht

lemma dampedPerronMajorant_integrableOn_tail {ε L : ℝ} (hε : 0 < ε) (hL : 0 ≤ L) :
    IntegrableOn (dampedPerronMajorantIntegrand ε L) (Ioi (1 : ℝ)) := by
  apply (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hε) 1).mono'
  · exact (dampedPerronMajorantIntegrand_measurable ε L).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (dampedPerronMajorantIntegrand_nonneg hL (zero_lt_one.trans ht).le)]
    rw [dampedPerronMajorantIntegrand, if_neg (zero_lt_one.trans ht).ne', div_eq_mul_inv]
    have hm : min 1 (L * t) ≤ 1 := min_le_left _ _
    have hi : t⁻¹ ≤ 1 := (inv_le_one₀ (zero_lt_one.trans ht)).mpr ht.le
    have he0 : 0 ≤ Real.exp (-ε * t) := (Real.exp_pos _).le
    have hm0 : 0 ≤ min 1 (L * t) :=
      le_min zero_le_one (mul_nonneg hL (zero_lt_one.trans ht).le)
    nlinarith [mul_le_mul_of_nonneg_left hm he0,
      mul_le_mul_of_nonneg_left hi (mul_nonneg he0 hm0)]

theorem dampedPerronMajorant_integrableOn_Ioi {ε L : ℝ} (hε : 0 < ε) (hL : 0 ≤ L) :
    IntegrableOn (dampedPerronMajorantIntegrand ε L) (Ioi (0 : ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  exact (dampedPerronMajorant_integrableOn_head hL hε.le).union (dampedPerronMajorant_integrableOn_tail hε hL)

theorem dampedPerronMajorant_integral_head_le {ε L : ℝ} (hε : 0 < ε) (hL : 0 ≤ L) :
    (∫ t in Ioc (0 : ℝ) 1, dampedPerronMajorantIntegrand ε L t) ≤ L := by
  calc
    (∫ t in Ioc (0 : ℝ) 1, dampedPerronMajorantIntegrand ε L t) ≤ ∫ _t in Ioc (0 : ℝ) 1, L := by
      apply MeasureTheory.integral_mono_ae
      · exact dampedPerronMajorant_integrableOn_head hL hε.le
      · exact integrableOn_const (μ := volume)
          ((measure_Ioc_lt_top (μ := volume) : volume (Ioc (0 : ℝ) 1) < ⊤).ne)
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact dampedPerronMajorantIntegrand_le_head hL hε.le ht
    _ = L := by norm_num

theorem dampedPerronMajorant_integral_middle_le {ε L : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hL : 0 ≤ L) :
    (∫ t in Ioc (1 : ℝ) ε⁻¹, dampedPerronMajorantIntegrand ε L t) ≤ Real.log (ε⁻¹) := by
  have hb : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε1
  calc
    (∫ t in Ioc (1 : ℝ) ε⁻¹, dampedPerronMajorantIntegrand ε L t) ≤ ∫ t in Ioc (1 : ℝ) ε⁻¹, t⁻¹ := by
      apply MeasureTheory.integral_mono_ae
      · exact (dampedPerronMajorant_integrableOn_Ioi hε hL).mono (fun t ht => zero_lt_one.trans ht.1) le_rfl
      · exact ((continuousOn_inv₀.mono (by
          intro t ht
          simp only [mem_compl_iff, mem_singleton_iff]
          linarith [ht.1])).integrableOn_Icc (μ := volume)).mono Ioc_subset_Icc_self le_rfl
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact dampedPerronMajorantIntegrand_le_inv hε.le hL ht.1.le
    _ = Real.log (ε⁻¹) := by
      rw [← intervalIntegral.integral_of_le hb, integral_inv_of_pos zero_lt_one (inv_pos.mpr hε)]
      simp

theorem dampedPerronMajorant_integral_tail_le_one {ε L : ℝ} (hε : 0 < ε) (hL : 0 ≤ L) :
    (∫ t in Ioi ε⁻¹, dampedPerronMajorantIntegrand ε L t) ≤ 1 := by
  calc
    (∫ t in Ioi ε⁻¹, dampedPerronMajorantIntegrand ε L t) ≤
        ∫ t in Ioi ε⁻¹, ε * Real.exp (-ε * t) := by
      apply MeasureTheory.integral_mono_ae
      · exact (dampedPerronMajorant_integrableOn_Ioi hε hL).mono (Ioi_subset_Ioi (inv_pos.mpr hε).le) le_rfl
      · exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hε) ε⁻¹).const_mul ε
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact dampedPerronMajorantIntegrand_le_tail hε hL ht.le
    _ = Real.exp (-1) := by
      rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hε)]
      rw [show -ε * ε⁻¹ = -1 by field_simp]
      field_simp
    _ ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)

/-- `∫_0^∞ e^{-ε t} min (1, L t) / t dt ≤ L + log (1/ε) + 1` for `0 < ε ≤ 1` and `L ≥ 0`. -/
theorem dampedPerronMajorant_integral_Ioi_le {ε L : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hL : 0 ≤ L) :
    (∫ t in Ioi (0 : ℝ), dampedPerronMajorantIntegrand ε L t) ≤ L + Real.log (1 / ε) + 1 := by
  have hb : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε1
  have hi := dampedPerronMajorant_integrableOn_Ioi hε hL
  have hi₁ := hi.mono_set (Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))
  have hi₂ := hi.mono_set (Ioi_subset_Ioi (inv_pos.mpr hε).le)
  -- Split at `1` and `1/ε`; the integrand is at most `L`, then `1/t`, then `ε e^{-ε t}`.
  have hsplit :
      (∫ t in Ioi (0 : ℝ), dampedPerronMajorantIntegrand ε L t) =
        (∫ t in Ioc (0 : ℝ) 1, dampedPerronMajorantIntegrand ε L t) +
          (∫ t in Ioc (1 : ℝ) ε⁻¹, dampedPerronMajorantIntegrand ε L t) +
            (∫ t in Ioi ε⁻¹, dampedPerronMajorantIntegrand ε L t) := by
    rw [← integral_interval_add_Ioi hi hi₁, ← integral_interval_add_Ioi hi₁ hi₂,
      integral_of_le zero_le_one, integral_of_le hb, add_assoc]
  rw [hsplit, one_div]
  exact add_le_add (add_le_add (dampedPerronMajorant_integral_head_le hε hL)
    (dampedPerronMajorant_integral_middle_le hε hε1 hL))
    (dampedPerronMajorant_integral_tail_le_one hε hL)

end BombieriVinogradov

end
