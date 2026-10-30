import ErdosStraus.BombieriVinogradov.DirichletL.ValueAtOne
import ErdosStraus.BombieriVinogradov.DirichletL.NonQuadraticZeroFree

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

section

/-!
# Zero-free regions for quadratic Dirichlet L-functions

Let `χ` be a nonprincipal character mod `q` with `χ² = 1` and `c q^(-η) ≤ Re L(1, χ)`.
Then `L(β + it, χ) ≠ 0` for `1 - A q^(-2η) / H(q, t)^12 ≤ β < 1`, with `A > 0` depending only
on `c` and `η`. Near `t = 0` this follows by comparing `L(β + it, χ)` with `L(1, χ)`, and
elsewhere from the `(3,4,1)` inequality. We deduce a zero-free rectangle
`[1 - w, 2] × [-T, T]` and explicit bounds for `L'/L` on it.
-/

open Complex Set

namespace BombieriVinogradov

open BombieriVinogradov.LValueBound
open BombieriVinogradov.LDerivBound
variable {q : ℕ} [NeZero q]

/-- On a horizontal segment with `1 - 1 / log N ≤ σ₁ ≤ σ₂ ≤ 2`, where `N = q (⌊|t|⌋ + 1)`,
`‖L(σ₂ + it, χ) - L(σ₁ + it, χ)‖ ≤ 64 (1 + log N)² (σ₂ - σ₁)`. -/
theorem norm_LFunction_sub_le_sixtyfour_mul_conductorHeightLogSq
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {σ₁ σ₂ t : ℝ}
    (hσ₁half : 1 / 2 ≤ σ₁)
    (hσ₁lower :
      1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ σ₁)
    (hσ₁σ₂ : σ₁ ≤ σ₂) (hσ₂upper : σ₂ ≤ 2) :
    ‖χ.LFunction (σ₂ + t * I) - χ.LFunction (σ₁ + t * I)‖ ≤
      64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 *
        (σ₂ - σ₁) := by
  rw [← BombieriVinogradov.WeakStripDifference.integral_deriv_LFunction_eq_sub
    χ hχ σ₁ σ₂ t]
  convert intervalIntegral.norm_integral_le_of_norm_le_const ?_ using 1
  · congr
    rw [_root_.abs_of_nonneg (sub_nonneg.mpr hσ₁σ₂)]
  · intro σ hσ
    rw [uIoc_of_le hσ₁σ₂, mem_Ioc] at hσ
    convert norm_deriv_LFunction_le_one_add_log_sq
      χ hχ (hσ₁half.trans hσ.1.le) (hσ.2.trans hσ₂upper)
      (hσ₁lower.trans hσ.1.le) using 1; ring_nf

/-- The scale `H(q, t) = 1 + log N + (1 + log (|2t| + 2) + 1 / |2t|)`, where
`N = q (⌊|t|⌋ + 1)` and the bracket is omitted at `t = 0`. It bounds both `1 + log N` and
the size of `ζ` near `1 + 2it`. -/
noncomputable def dirichletLQuadraticConditionalPowerZeroFreeH
    (q : ℕ) (t : ℝ) : ℝ :=
  1 + Real.log (dirichletLConductorHeightCutoff q t) +
    if _ht : t = 0 then 0
    else 1 + Real.log (|2 * t| + 2) + 1 / |2 * t|

/-- On the vertical segment from `1` to `1 + it`,
`‖L(1 + it, χ) - L(1, χ)‖ ≤ 64 (1 + log N)² |t|` with `N = q (⌊|t|⌋ + 1)`. -/
theorem norm_LFunction_vertical_sub_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    ‖χ.LFunction (1 + t * I) - χ.LFunction 1‖ ≤
      64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 * |t| := by
  let C : ℝ := 64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2
  have hmain : ‖χ.LFunction (1 + t * I) - χ.LFunction 1‖ ≤
      C * ‖(1 + t * I : ℂ) - 1‖ :=
    (convex_segment (𝕜 := ℝ) (1 : ℂ) (1 + t * I)).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℂ) (f := χ.LFunction) (C := C)
      (fun z _ => χ.differentiable_LFunction hχ z) (fun z hz => by
        rw [segment_eq_image_lineMap] at hz
        obtain ⟨u, hu, rfl⟩ := hz
        have hu0 : 0 ≤ u := hu.1
        have hu1 : u ≤ 1 := hu.2
        have hline : AffineMap.lineMap (1 : ℂ) (1 + t * I) u = 1 + (u * t) * I := by
          apply Complex.ext <;> simp [AffineMap.lineMap_apply]
        have him : |(AffineMap.lineMap (1 : ℂ) (1 + t * I) u).im| ≤ |t| := by
          rw [hline]
          simp only [add_im, one_im, mul_im, mul_re, ofReal_re, ofReal_im, I_re,
            I_im, mul_one, mul_zero, zero_mul, add_zero, zero_add]
          rw [sub_zero, abs_mul, abs_of_nonneg hu0]
          exact mul_le_of_le_one_left (abs_nonneg t) hu1
        have hcut : dirichletLConductorHeightCutoff q
            (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).im ≤
            dirichletLConductorHeightCutoff q t := by
          unfold dirichletLConductorHeightCutoff dirichletLHeightBlock
          exact Nat.mul_le_mul_left q (Nat.add_le_add_right (Nat.floor_mono him) 1)
        have hcutpos : (0 : ℝ) < dirichletLConductorHeightCutoff q
            (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).im := by
          exact_mod_cast Nat.mul_pos (NeZero.pos q) (by simp [dirichletLHeightBlock])
        have hcutR : (dirichletLConductorHeightCutoff q
            (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).im : ℝ) ≤
            dirichletLConductorHeightCutoff q t := by exact_mod_cast hcut
        have hlog : Real.log (dirichletLConductorHeightCutoff q
            (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).im) ≤
            Real.log (dirichletLConductorHeightCutoff q t) :=
          Real.log_le_log hcutpos hcutR
        have hd := norm_deriv_LFunction_le_one_add_log_sq
          χ hχ (σ := (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).re)
            (t := (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).im)
            (by rw [hline]; norm_num) (by rw [hline]; norm_num)
            (by
              have hp := log_conductorHeightCutoff_pos χ hχ
                (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).im
              rw [show (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).re = 1 by
                rw [hline]; simp]
              exact sub_le_self 1 (one_div_nonneg.mpr hp.le))
        rw [show (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).re +
            I * (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).im =
            AffineMap.lineMap (1 : ℂ) (1 + t * I) u by
              rw [mul_comm I]; exact Complex.re_add_im _] at hd
        dsimp only [C]
        calc
          ‖fderiv ℂ χ.LFunction (AffineMap.lineMap (1 : ℂ) (1 + t * I) u)‖ ≤
              64 * (1 + Real.log (dirichletLConductorHeightCutoff q
                (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).im)) ^ 2 := by
                  rw [← norm_deriv_eq_norm_fderiv]
                  exact hd
          _ ≤ 64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            have hp := log_conductorHeightCutoff_pos χ hχ
              (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).im
            exact pow_le_pow_left₀ (by linarith [hp]) (by linarith [hlog]) 2)
      (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  have hnorm : ‖(1 + t * I : ℂ) - 1‖ = |t| := by
    rw [show (1 + t * I : ℂ) - 1 = t * I by ring, norm_mul, norm_I, mul_one,
      norm_real, Real.norm_eq_abs]
  simpa only [C, hnorm] using hmain

/-- If `L` changes by at most `Bh` from `β + it` to `1 + it` and by at most `Bv` from
`1 + it` to `1`, and `Bh + Bv < L(1, χ)`, then `L(β + it, χ) ≠ 0`. For quadratic `χ`,
`L(1, χ)` is real and positive, so it equals its norm. -/
theorem LFunction_ne_zero_lowHeight_of_twoSegmentBudgets
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1)
    {β t Bh Bv : ℝ}
    (hhorizontal :
      ‖χ.LFunction (1 + t * I) - χ.LFunction (β + t * I)‖ ≤ Bh)
    (hvertical : ‖χ.LFunction (1 + t * I) - χ.LFunction 1‖ ≤ Bv)
    (hbudget : Bh + Bv < (χ.LFunction 1).re) :
    χ.LFunction (β + I * t) ≠ 0 := by
  intro hz
  have hz' : χ.LFunction (β + t * I) = 0 := by convert hz using 1; ring_nf
  have hre := DirichletCharacter.LFunction_apply_one_re_pos_of_sq_eq_one hquad hχ
  have him := DirichletCharacter.LFunction_apply_one_im_eq_zero_of_sq_eq_one hquad hχ
  have hnormone : ‖χ.LFunction 1‖ = (χ.LFunction 1).re := by
    rw [Complex.norm_def, Complex.normSq_apply, him]
    simp only [mul_zero, add_zero]
    rw [← pow_two, Real.sqrt_sq_eq_abs, abs_of_pos hre]
  have htri : ‖χ.LFunction 1‖ ≤
      ‖χ.LFunction (1 + t * I) - χ.LFunction 1‖ +
        ‖χ.LFunction (1 + t * I) - χ.LFunction (β + t * I)‖ := by
    rw [hz', sub_zero]
    calc
      ‖χ.LFunction 1‖ = ‖χ.LFunction 1 - χ.LFunction (1 + t * I) +
          χ.LFunction (1 + t * I)‖ := by rw [sub_add_cancel]
      _ ≤ ‖χ.LFunction 1 - χ.LFunction (1 + t * I)‖ +
          ‖χ.LFunction (1 + t * I)‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev]
  rw [hnormone] at htri
  linarith

/-- Since `χ²` is principal, `L(s, χ²)` is `ζ(s)` times an Euler factor of size at most
`1 + log q`. With the bound `hzeta` for `ζ` this gives
`‖L(1 + x + 2it, χ²)‖ ≤ (1 + log q) Z (1 + log (|2t| + 2) + 1 / |2t|)`. -/
theorem norm_quadraticSquare_LFunction_le_principalPolePlusLog
    (Z : ℝ)
    (hzeta : ∀ (x u : ℝ), 0 < x → x ≤ 1 → u ≠ 0 →
      ‖riemannZeta (1 + x + I * u)‖ ≤
        Z * (1 + Real.log (|u| + 2) + 1 / |u|))
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1)
    {x t : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (ht : t ≠ 0) :
    ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖ ≤
      (1 + Real.log q) *
        (Z * (1 + Real.log (|2 * t| + 2) + 1 / |2 * t|)) := by
  have hu : 2 * t ≠ 0 := mul_ne_zero (by norm_num) ht
  have he := DirichletCharacter.norm_LFunction_sq_le_one_add_log_mul_riemannZeta
    χ hquad (s := 1 + x + I * (2 * t)) (by simp; linarith) (by
      intro h
      have hh := congrArg Complex.im h
      simp at hh
      exact ht hh)
  calc
    _ ≤ (1 + Real.log q) * ‖riemannZeta (1 + x + I * (2 * t))‖ := he
    _ ≤ (1 + Real.log q) *
        (Z * (1 + Real.log (|2 * t| + 2) + 1 / |2 * t|)) := by
      gcongr
      simpa only [ofReal_mul, ofReal_ofNat] using hzeta x (2 * t) hx hx1 hu

/-- The `(3,4,1)` inequality
`1 ≤ ‖L(1 + x, χ₀)‖³ ‖L(1 + x + it, χ)‖⁴ ‖L(1 + x + 2it, χ²)‖` is incompatible with the
bounds `htriv`, `hright` and `hpay`, so the conclusion holds for every `β`. In applications
`hright` is derived from a zero at `β + it`. -/
theorem LFunction_ne_zero_highHeight_of_valueProduct
    (Z : ℝ) (hZ : 0 < Z)
    (hzeta : ∀ (x u : ℝ), 0 < x → x ≤ 1 → u ≠ 0 →
      ‖riemannZeta (1 + x + I * u)‖ ≤
        Z * (1 + Real.log (|u| + 2) + 1 / |u|))
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) (_hχ : χ ≠ 1)
    {β t x D : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (ht : t ≠ 0)
    (htriv : ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ≤ 2 / x)
    (hright : ‖χ.LFunction (1 + x + I * t)‖ ≤ D * x)
    (hpay : 8 * (1 + Real.log q) *
        (Z * (1 + Real.log (|2 * t| + 2) + 1 / |2 * t|)) * (D * x) ^ 4 < x ^ 3) :
    χ.LFunction (β + I * t) ≠ 0 := by
  have hsquare := norm_quadraticSquare_LFunction_le_principalPolePlusLog
    Z hzeta χ hquad hx hx1 ht
  have hp := χ.norm_LFunction_product_ge_one hx t
  have hprod : 1 ≤
      ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ^ 3 *
        ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
        ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖ := by
    convert (show 1 ≤
        ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ^ 3 *
          ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
          ‖(χ ^ 2).LFunction (1 + x + 2 * I * t)‖ by
      simpa only [norm_mul, norm_pow] using hp) using 1; ring_nf
  have hmajor : 1 ≤ (2 / x) ^ 3 * (D * x) ^ 4 *
      ((1 + Real.log q) *
        (Z * (1 + Real.log (|2 * t| + 2) + 1 / |2 * t|))) := by
    calc
      1 ≤ ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ^ 3 *
          ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
          ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖ := hprod
      _ ≤ _ := by gcongr
  have hm := mul_le_mul_of_nonneg_left hmajor (pow_nonneg hx.le 3)
  have hcontr : x ^ 3 ≤ 8 * (1 + Real.log q) *
      (Z * (1 + Real.log (|2 * t| + 2) + 1 / |2 * t|)) * (D * x) ^ 4 := by
    calc
      x ^ 3 = x ^ 3 * 1 := by ring
      _ ≤ x ^ 3 * ((2 / x) ^ 3 * (D * x) ^ 4 *
          ((1 + Real.log q) *
            (Z * (1 + Real.log (|2 * t| + 2) + 1 / |2 * t|)))) := hm
      _ = _ := by field_simp [ne_of_gt hx]; ring
  exact False.elim ((not_lt_of_ge hcontr) hpay)

theorem one_le_dirichletLQuadraticConditionalPowerZeroFreeH
    (q : ℕ) [NeZero q] (t : ℝ) :
    1 ≤ dirichletLQuadraticConditionalPowerZeroFreeH q t := by
  have hcut : (1 : ℝ) ≤ dirichletLConductorHeightCutoff q t := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
      exact Nat.mul_ne_zero (NeZero.ne q) (by simp [dirichletLHeightBlock]))
  have hlog : 0 ≤ Real.log (dirichletLConductorHeightCutoff q t) :=
    Real.log_nonneg hcut
  by_cases ht : t = 0
  · subst t
    simpa [dirichletLQuadraticConditionalPowerZeroFreeH] using
      (show (1 : ℝ) ≤ 1 + Real.log (dirichletLConductorHeightCutoff q 0) by linarith)
  · have habs : 0 < |2 * t| := abs_pos.mpr (mul_ne_zero (by norm_num) ht)
    have hlogtwo : 0 ≤ Real.log (|2 * t| + 2) :=
      Real.log_nonneg (by linarith [abs_nonneg (2 * t)])
    have hinv : 0 < 1 / |2 * t| := one_div_pos.mpr habs
    simp only [dirichletLQuadraticConditionalPowerZeroFreeH, dif_neg ht]
    linarith

theorem one_add_log_conductorHeightCutoff_le_quadraticH
    (q : ℕ) [NeZero q] (t : ℝ) :
    1 + Real.log (dirichletLConductorHeightCutoff q t) ≤
      dirichletLQuadraticConditionalPowerZeroFreeH q t := by
  by_cases ht : t = 0
  · simp [dirichletLQuadraticConditionalPowerZeroFreeH, ht]
  · have habs : 0 < |2 * t| := abs_pos.mpr (mul_ne_zero (by norm_num) ht)
    have hlogtwo : 0 ≤ Real.log (|2 * t| + 2) :=
      Real.log_nonneg (by linarith [abs_nonneg (2 * t)])
    have hinv : 0 < 1 / |2 * t| := one_div_pos.mpr habs
    simp only [dirichletLQuadraticConditionalPowerZeroFreeH, dif_neg ht]
    linarith

theorem one_add_log_twoHeight_add_inv_le_quadraticH
    (q : ℕ) [NeZero q] {t : ℝ} (ht : t ≠ 0) :
    1 + Real.log (|2 * t| + 2) + 1 / |2 * t| ≤
      dirichletLQuadraticConditionalPowerZeroFreeH q t := by
  have hcut : (1 : ℝ) ≤ dirichletLConductorHeightCutoff q t := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
      exact Nat.mul_ne_zero (NeZero.ne q) (by simp [dirichletLHeightBlock]))
  have hlog : 0 ≤ Real.log (dirichletLConductorHeightCutoff q t) :=
    Real.log_nonneg hcut
  simp only [dirichletLQuadraticConditionalPowerZeroFreeH, dif_neg ht]
  linarith

/-- Zero-free region for quadratic characters. If `c q^(-η) ≤ Re L(1, χ)`, then
`L(β + it, χ) ≠ 0` for `1 - A q^(-2η) / H(q, t)^12 ≤ β < 1`, with `A` depending only on `c`
and `η`. For `|t|` at most the width we compare with `L(1, χ)` along two segments; for
larger `|t|` we use the `(3,4,1)` inequality. -/
theorem exists_dirichletL_quadratic_conditional_powerZeroFree
    (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (β t : ℝ),
        χ ^ 2 = 1 → χ ≠ 1 →
        c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re →
        β ∈ Set.Ico
          (1 - A * (q : ℝ) ^ (-2 * η) /
            (dirichletLQuadraticConditionalPowerZeroFreeH q t) ^ 12) 1 →
        χ.LFunction (β + I * t) ≠ 0 := by
  obtain ⟨Z, hZ, hzeta⟩ := zeta_pole_plus_log_bound
  let A : ℝ := min (1 / 2) (min (c / 256) (1 / (16 * Z * 128 ^ 4)))
  have hA : 0 < A := by
    dsimp only [A]
    exact lt_min (by norm_num) (lt_min (div_pos hc (by norm_num)) (by positivity))
  refine ⟨A, hA, ?_⟩
  intro q _ χ β t hquad hχ hSiegel hβ
  let H : ℝ := dirichletLQuadraticConditionalPowerZeroFreeH q t
  let p : ℝ := (q : ℝ) ^ (-2 * η)
  let r : ℝ := (q : ℝ) ^ (-η)
  let x : ℝ := A * p / H ^ 12
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hH1 : 1 ≤ H := one_le_dirichletLQuadraticConditionalPowerZeroFreeH q t
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  have hp : 0 < p := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hq1) _
  have hr : 0 < r := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hq1) _
  have hpr : p ≤ r := by
    dsimp only [p, r]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hp1 : p ≤ 1 := by
    dsimp only [p]
    simpa using Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : -2 * η ≤ 0)
  have hHpow : 1 ≤ H ^ 12 := one_le_pow₀ hH1
  have hx : 0 < x := div_pos (mul_pos hA hp) (pow_pos hH 12)
  have hAhalf : A ≤ 1 / 2 := by exact min_le_left _ _
  have hA1 : A ≤ 1 := hAhalf.trans (by norm_num)
  have hx1 : x ≤ 1 := by
    dsimp only [x]
    exact (div_le_one (pow_pos hH 12)).2
      (((mul_le_of_le_one_right hA.le hp1).trans hA1).trans hHpow)
  have hβleft : 1 - x ≤ β := by simpa only [x, p, H] using hβ.1
  have hβhalf : 1 / 2 ≤ β := by
    have hxhalf : x ≤ 1 / 2 := by
      have hsmall : A ≤ 1 / 2 := hAhalf
      dsimp only [x]
      calc
        A * p / H ^ 12 ≤ A := by
          rw [div_le_iff₀ (pow_pos hH 12)]
          nlinarith [hHpow, mul_le_of_le_one_right hA.le hp1]
        _ ≤ 1 / 2 := hsmall
    linarith
  -- In both cases `β` lies in the strip where the derivative bound holds.
  have hnear :
      1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ β := by
    have hlogpos := log_conductorHeightCutoff_pos χ hχ t
    have hone : x ≤ 1 / Real.log (dirichletLConductorHeightCutoff q t) := by
      have hlogle : Real.log (dirichletLConductorHeightCutoff q t) ≤ H := by
        have := one_add_log_conductorHeightCutoff_le_quadraticH q t
        linarith
      apply (le_div_iff₀ hlogpos).2
      calc
        x * Real.log (dirichletLConductorHeightCutoff q t) ≤ x * H :=
          mul_le_mul_of_nonneg_left hlogle hx.le
        _ ≤ 1 := by
          dsimp only [x]
          rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hH 12)]
          nlinarith [hHpow, one_le_pow₀ hH1 (n := 11),
            mul_le_of_le_one_right hA.le hp1]
    linarith
  have hlogH := one_add_log_conductorHeightCutoff_le_quadraticH q t
  by_cases htlow : |t| ≤ x
  · have hhorizontal := norm_LFunction_sub_le_sixtyfour_mul_conductorHeightLogSq
      χ hχ hβhalf hnear hβ.2.le (by norm_num : (1 : ℝ) ≤ 2)
    have hvertical :=
      norm_LFunction_vertical_sub_le χ hχ t
    have hBh : ‖χ.LFunction (1 + t * I) - χ.LFunction (β + t * I)‖ ≤
        64 * H ^ 2 * x := by
      calc
        _ ≤ 64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 *
            (1 - β) := by simpa using hhorizontal
        _ ≤ 64 * H ^ 2 * x := by
          have hwidth : 1 - β ≤ x := by linarith
          have hnonneg : 0 ≤ 1 - β := sub_nonneg.mpr hβ.2.le
          gcongr
    have hBv : ‖χ.LFunction (1 + t * I) - χ.LFunction 1‖ ≤
        64 * H ^ 2 * x := by
      calc
        _ ≤ 64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 * |t| :=
          hvertical
        _ ≤ 64 * H ^ 2 * x := by
          gcongr
    have hAlow : A ≤ c / 256 :=
      (min_le_right (1 / 2) _).trans (min_le_left _ _)
    have hbudget : 64 * H ^ 2 * x + 64 * H ^ 2 * x < (χ.LFunction 1).re := by
      have hpow10 : 1 ≤ H ^ 10 := one_le_pow₀ hH1
      have hcalc : 128 * H ^ 2 * x ≤ (c / 2) * r := by
        dsimp only [x]
        have heq : 128 * H ^ 2 * (A * p / H ^ 12) = 128 * A * p / H ^ 10 := by
          field_simp [ne_of_gt hH]
        rw [heq, div_le_iff₀ (pow_pos hH 10)]
        have hAp : A * p ≤ (c / 256) * r :=
          mul_le_mul hAlow hpr hp.le (by positivity)
        have hscale : (c / 2) * r ≤ (c / 2) * r * H ^ 10 :=
          le_mul_of_one_le_right (by positivity) hpow10
        nlinarith
      have : (c / 2) * r < c * r :=
        mul_lt_mul_of_pos_right (by linarith) hr
      linarith
    exact LFunction_ne_zero_lowHeight_of_twoSegmentBudgets χ hquad hχ hBh hBv hbudget
  · have ht : t ≠ 0 := by
      intro h
      subst t
      simp only [abs_zero] at htlow
      exact htlow hx.le
    have hright0 := norm_LFunction_sub_le_sixtyfour_mul_conductorHeightLogSq
      χ hχ (σ₁ := β) (σ₂ := 1 + x) (t := t) hβhalf
      hnear
      (by linarith [hβ.2]) (by linarith [hx1] : 1 + x ≤ 2)
    have htriv : ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ≤ 2 / x := by
      rw [DirichletCharacter.LFunctionTrivChar]
      calc
        ‖(1 : DirichletCharacter ℂ q).LFunction (1 + x)‖ ≤ 1 + 1 / x := by
          convert norm_dirichletLFunction_le
            (1 : DirichletCharacter ℂ q) (1 + x) 0 (by linarith) using 1 <;> norm_num
        _ ≤ 2 / x := by
          rw [le_div_iff₀ hx]
          field_simp [ne_of_gt hx]
          linarith
    intro hz
    have hz' : χ.LFunction (β + t * I) = 0 := by
      convert hz using 1; ring_nf
    have hright : ‖χ.LFunction (1 + x + I * t)‖ ≤ (128 * H ^ 2) * x := by
      calc
        ‖χ.LFunction (1 + x + I * t)‖ =
            ‖χ.LFunction (1 + x + t * I) - χ.LFunction (β + t * I)‖ := by
              rw [hz', sub_zero]
              congr 2
              ring
        _ ≤ 64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 *
            ((1 + x) - β) := by
              convert hright0 using 1; push_cast; ring
        _ ≤ (128 * H ^ 2) * x := by
          have hwidth : 1 - β ≤ x := by linarith
          have hdiff : (1 + x) - β ≤ 2 * x := by linarith
          have hdiff0 : 0 ≤ (1 + x) - β := by linarith [hβ.2]
          have hlogH' :
              1 + Real.log (dirichletLConductorHeightCutoff q t) ≤ H := by
            simpa only [H] using hlogH
          calc
            64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 *
                ((1 + x) - β) ≤ 64 * H ^ 2 * ((1 + x) - β) := by gcongr
            _ ≤ 64 * H ^ 2 * (2 * x) := by gcongr
            _ = (128 * H ^ 2) * x := by ring
    have hqcut : q ≤ dirichletLConductorHeightCutoff q t := by
      unfold dirichletLConductorHeightCutoff
      exact Nat.le_mul_of_pos_right q (by simp [dirichletLHeightBlock])
    have hlogq : 1 + Real.log q ≤ H := by
      have hqpos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq1
      have hcast : (q : ℝ) ≤ dirichletLConductorHeightCutoff q t := by
        exact_mod_cast hqcut
      have hl := Real.log_le_log hqpos hcast
      have hh := one_add_log_conductorHeightCutoff_le_quadraticH q t
      linarith
    let S : ℝ := 1 + Real.log (|2 * t| + 2) + 1 / |2 * t|
    have hSpos : 0 < S := by
      dsimp only [S]
      have habs : 0 < |2 * t| := abs_pos.mpr (mul_ne_zero (by norm_num) ht)
      have hlogtwo : 0 ≤ Real.log (|2 * t| + 2) :=
        Real.log_nonneg (by linarith [abs_nonneg (2 * t)])
      positivity
    have hSH : S ≤ H := by
      simpa only [S] using one_add_log_twoHeight_add_inv_le_quadraticH q ht
    have hmajor :
        8 * (1 + Real.log q) * (Z * S) * ((128 * H ^ 2) * x) ^ 4 ≤
          8 * H * (Z * H) * ((128 * H ^ 2) * x) ^ 4 := by
      gcongr
    have hAhigh : A ≤ 1 / (16 * Z * 128 ^ 4) :=
      (min_le_right (1 / 2) _).trans (min_le_right _ _)
    have hdenpos : 0 < 16 * Z * 128 ^ 4 := by positivity
    have hZA : 16 * Z * 128 ^ 4 * A ≤ 1 := by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using
        (le_div_iff₀ hdenpos).mp hAhigh
    have hZAp : 16 * Z * 128 ^ 4 * A * p ≤ 1 :=
      (mul_le_of_le_one_right (by positivity) hp1).trans hZA
    have hfactor : 8 * Z * 128 ^ 4 * A * p / H ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ (pow_pos hH 2)]
      have hHsq : 1 ≤ H ^ 2 := one_le_pow₀ hH1
      nlinarith
    have hid :
        8 * H * (Z * H) * ((128 * H ^ 2) * x) ^ 4 =
          (8 * Z * 128 ^ 4 * A * p / H ^ 2) * x ^ 3 := by
      dsimp only [x]
      field_simp [ne_of_gt hH]
    have hpay :
        8 * (1 + Real.log q) * (Z * S) * ((128 * H ^ 2) * x) ^ 4 < x ^ 3 := by
      calc
        _ ≤ 8 * H * (Z * H) * ((128 * H ^ 2) * x) ^ 4 := hmajor
        _ = (8 * Z * 128 ^ 4 * A * p / H ^ 2) * x ^ 3 := hid
        _ ≤ (1 / 2) * x ^ 3 := mul_le_mul_of_nonneg_right hfactor (pow_nonneg hx.le 3)
        _ < x ^ 3 := by nlinarith [pow_pos hx 3]
    have hne := LFunction_ne_zero_highHeight_of_valueProduct Z hZ hzeta χ hquad hχ
      (β := β) (t := t) (x := x) (D := 128 * H ^ 2)
      hx hx1 ht htriv hright (by simpa only [S] using hpay)
    exact hne hz

end BombieriVinogradov

end

section

open Complex Set

namespace BombieriVinogradov

open BombieriVinogradov.LValueBound
open BombieriVinogradov.LDerivBound

/-!
## Rectangles away from height zero

Since `H(q, t)` contains `1 / |2t|`, the width of the zero-free region above tends to `0`
as `t → 0`. On the heights `τ ≤ |t| ≤ T` it contains two rectangles of fixed width.
-/

/-- An upper bound for `H(q, t)` that is uniform in `τ ≤ |t| ≤ T`. -/
noncomputable def dirichletLQuadraticConditionalFixedH
    (q : ℕ) (τ T : ℝ) : ℝ :=
  1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T) +
    (1 + Real.log (2 * T + 2) + 1 / (2 * τ))

/-- The left edge `σ₀ = 1 - A q^(-2η) / H^12`, where `H` is the uniform bound for `H(q, t)`
on `τ ≤ |t| ≤ T`. -/
noncomputable def dirichletLQuadraticConditionalFixedLeft
    (A η : ℝ) (q : ℕ) (τ T : ℝ) : ℝ :=
  1 - A * (q : ℝ) ^ (-2 * η) /
    (dirichletLQuadraticConditionalFixedH q τ T) ^ 12

/-- The rectangle `[σ₀, 2] × [τ, T]`. -/
def dirichletLQuadraticConditionalUpperRectangle
    (A η : ℝ) (q : ℕ) (τ T : ℝ) : Set ℂ :=
  ((dirichletLQuadraticConditionalFixedLeft A η q τ T : ℂ) + I * τ).Rectangle
    (2 + I * T)

/-- The rectangle `[σ₀, 2] × [-T, -τ]`. -/
def dirichletLQuadraticConditionalLowerRectangle
    (A η : ℝ) (q : ℕ) (τ T : ℝ) : Set ℂ :=
  ((dirichletLQuadraticConditionalFixedLeft A η q τ T : ℂ) - I * T).Rectangle
    (2 - I * τ)

theorem dirichletLQuadraticConditionalPowerZeroFreeH_le_fixedH
    {q : ℕ} [NeZero q] {τ T t : ℝ}
    (hτ : 0 < τ) (_hT : τ ≤ T) (htlow : τ ≤ |t|) (hthigh : |t| ≤ T) :
    dirichletLQuadraticConditionalPowerZeroFreeH q t ≤
      dirichletLQuadraticConditionalFixedH q τ T := by
  have ht : t ≠ 0 := by
    intro ht
    subst t
    simp only [abs_zero] at htlow
    linarith
  have hcut := dirichletLConductorHeightCutoff_le_fixedHeightCutoff (q := q) hthigh
  have hcutpos : (0 : ℝ) < dirichletLConductorHeightCutoff q t := by
    exact_mod_cast Nat.mul_pos (NeZero.pos q) (by simp [dirichletLHeightBlock])
  have hcutR : (dirichletLConductorHeightCutoff q t : ℝ) ≤
      dirichletLNonquadraticConductorLogCutoff q T := by exact_mod_cast hcut
  have hlogcut := Real.log_le_log hcutpos hcutR
  have habs : |2 * t| = 2 * |t| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have harg : |2 * t| + 2 ≤ 2 * T + 2 := by rw [habs]; linarith
  have hargpos : 0 < |2 * t| + 2 := by linarith [abs_nonneg (2 * t)]
  have hlogarg := Real.log_le_log hargpos harg
  have hden : 0 < 2 * τ := by positivity
  have habsden : 2 * τ ≤ |2 * t| := by rw [habs]; linarith
  have hinv : 1 / |2 * t| ≤ 1 / (2 * τ) :=
    one_div_le_one_div_of_le hden habsden
  simp only [dirichletLQuadraticConditionalPowerZeroFreeH, dif_neg ht,
    dirichletLQuadraticConditionalFixedH]
  linarith

private theorem quadratic_fixed_parameters
    {q : ℕ} [NeZero q] {A η τ T : ℝ}
    (hA : 0 < A) (hτ : 0 < τ) (hT : τ ≤ T) :
    0 < dirichletLQuadraticConditionalFixedH q τ T ∧
      dirichletLQuadraticConditionalFixedLeft A η q τ T < 1 ∧
      dirichletLQuadraticConditionalFixedLeft A η q τ T ≤ 2 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hcut : (1 : ℝ) ≤ dirichletLNonquadraticConductorLogCutoff q T := by
    exact_mod_cast (show 1 ≤ dirichletLNonquadraticConductorLogCutoff q T by
      unfold dirichletLNonquadraticConductorLogCutoff
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne q) (by
        unfold dirichletLNonquadraticConductorLogHeightBlock
        omega)))
  have hlogcut : 0 ≤ Real.log (dirichletLNonquadraticConductorLogCutoff q T : ℝ) :=
    Real.log_nonneg hcut
  have hT0 : 0 < T := lt_of_lt_of_le hτ hT
  have hlogarg : 0 ≤ Real.log (2 * T + 2) := Real.log_nonneg (by linarith)
  have hH : 0 < dirichletLQuadraticConditionalFixedH q τ T := by
    dsimp only [dirichletLQuadraticConditionalFixedH]
    positivity
  have hp : 0 < (q : ℝ) ^ (-2 * η) := Real.rpow_pos_of_pos hq _
  have hw : 0 < A * (q : ℝ) ^ (-2 * η) /
      (dirichletLQuadraticConditionalFixedH q τ T) ^ 12 := by positivity
  have hleft : dirichletLQuadraticConditionalFixedLeft A η q τ T < 1 := by
    dsimp only [dirichletLQuadraticConditionalFixedLeft]
    linarith only [hw]
  exact ⟨hH, hleft, hleft.le.trans (by norm_num)⟩

private theorem LFunction_ne_zero_on_quadraticConditionalRectangle_aux
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A η τ T : ℝ} (hA : 0 < A) (hτ : 0 < τ) (hT : τ ≤ T)
    (hzero : ∀ (β t : ℝ),
      β ∈ Ico
        (1 - A * (q : ℝ) ^ (-2 * η) /
          (dirichletLQuadraticConditionalPowerZeroFreeH q t) ^ 12) 1 →
      χ.LFunction (β + I * t) ≠ 0)
    {s : ℂ} (hre : dirichletLQuadraticConditionalFixedLeft A η q τ T ≤ s.re)
    (_hre2 : s.re ≤ 2) (htlow : τ ≤ |s.im|) (hthigh : |s.im| ≤ T) :
    χ.LFunction s ≠ 0 := by
  by_cases hsre : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) hsre
  · have hsrelt : s.re < 1 := lt_of_not_ge hsre
    have hHF := dirichletLQuadraticConditionalPowerZeroFreeH_le_fixedH (q := q)
      hτ hT htlow hthigh
    have hHlocal := one_le_dirichletLQuadraticConditionalPowerZeroFreeH q s.im
    have hHfixed : 0 < dirichletLQuadraticConditionalFixedH q τ T :=
      (quadratic_fixed_parameters (q := q) (η := η) hA hτ hT).1
    have hp : 0 ≤ A * (q : ℝ) ^ (-2 * η) := by positivity
    have hpow : (dirichletLQuadraticConditionalPowerZeroFreeH q s.im) ^ 12 ≤
        (dirichletLQuadraticConditionalFixedH q τ T) ^ 12 := by
      exact pow_le_pow_left₀ (zero_le_one.trans hHlocal) hHF 12
    have hwidth : A * (q : ℝ) ^ (-2 * η) /
          (dirichletLQuadraticConditionalFixedH q τ T) ^ 12 ≤
        A * (q : ℝ) ^ (-2 * η) /
          (dirichletLQuadraticConditionalPowerZeroFreeH q s.im) ^ 12 := by
      exact div_le_div_of_nonneg_left hp (pow_pos (by linarith) 12) hpow
    have hβ : s.re ∈ Ico
        (1 - A * (q : ℝ) ^ (-2 * η) /
          (dirichletLQuadraticConditionalPowerZeroFreeH q s.im) ^ 12) 1 := by
      refine ⟨?_, hsrelt⟩
      dsimp only [dirichletLQuadraticConditionalFixedLeft] at hre
      linarith
    have hz := hzero s.re s.im hβ
    have hsrepr : ((s.re : ℂ) + I * s.im) = s := by
      apply Complex.ext <;> simp
    simpa only [hsrepr] using hz

/-- If `L(β + it, χ) ≠ 0` for all `1 - A q^(-2η) / H(q, t)^12 ≤ β < 1`, then `L(s, χ) ≠ 0`
on the rectangle `[σ₀, 2] × [τ, T]`. -/
theorem LFunction_ne_zero_on_quadraticConditionalUpperRectangle
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A η τ T : ℝ} (hA : 0 < A) (hτ : 0 < τ) (hT : τ ≤ T)
    (hzero : ∀ (β t : ℝ),
      β ∈ Ico
        (1 - A * (q : ℝ) ^ (-2 * η) /
          (dirichletLQuadraticConditionalPowerZeroFreeH q t) ^ 12) 1 →
      χ.LFunction (β + I * t) ≠ 0) :
    ∀ s ∈ dirichletLQuadraticConditionalUpperRectangle A η q τ T,
      χ.LFunction s ≠ 0 := by
  intro s hs
  rw [dirichletLQuadraticConditionalUpperRectangle, Complex.Rectangle,
    Complex.mem_reProdIm] at hs
  norm_num at hs
  have hp := quadratic_fixed_parameters (q := q) (η := η) hA hτ hT
  rw [Set.uIcc_of_le hp.2.2, Set.uIcc_of_le hT] at hs
  rcases hs with ⟨⟨hreL, hreR⟩, ⟨himL, himR⟩⟩
  have habsim : |s.im| = s.im := abs_of_nonneg (hτ.le.trans himL)
  exact LFunction_ne_zero_on_quadraticConditionalRectangle_aux (q := q) χ hχ hA hτ hT hzero
    hreL hreR (by simpa only [habsim] using himL) (by simpa only [habsim] using himR)

/-- The same statement for the rectangle `[σ₀, 2] × [-T, -τ]`. -/
theorem LFunction_ne_zero_on_quadraticConditionalLowerRectangle
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A η τ T : ℝ} (hA : 0 < A) (hτ : 0 < τ) (hT : τ ≤ T)
    (hzero : ∀ (β t : ℝ),
      β ∈ Ico
        (1 - A * (q : ℝ) ^ (-2 * η) /
          (dirichletLQuadraticConditionalPowerZeroFreeH q t) ^ 12) 1 →
      χ.LFunction (β + I * t) ≠ 0) :
    ∀ s ∈ dirichletLQuadraticConditionalLowerRectangle A η q τ T,
      χ.LFunction s ≠ 0 := by
  intro s hs
  rw [dirichletLQuadraticConditionalLowerRectangle, Complex.Rectangle,
    Complex.mem_reProdIm] at hs
  norm_num at hs
  have hp := quadratic_fixed_parameters (q := q) (η := η) hA hτ hT
  rw [Set.uIcc_of_le hp.2.2, Set.uIcc_of_le (by linarith : -T ≤ -τ)] at hs
  rcases hs with ⟨⟨hreL, hreR⟩, ⟨himL, himR⟩⟩
  have him_nonpos : s.im ≤ 0 := by linarith
  have habsim : |s.im| = -s.im := abs_of_nonpos him_nonpos
  apply LFunction_ne_zero_on_quadraticConditionalRectangle_aux (q := q) χ hχ hA hτ hT hzero
    hreL hreR
  · rw [habsim]
    linarith
  · rw [habsim]
    linarith

/-!
## A rectangle crossing height zero

On the central band `|t| ≤ τ` we compare `L(β + it, χ)` with `L(1, χ)` directly, using the
conductor cutoff `q (⌊T⌋ + 1)` at height `T`. The rectangles on `τ ≤ |t| ≤ T` cover the
rest, giving one zero-free rectangle `[1 - w, 2] × [-T, T]`.
-/

/-- The scale `H₀ = 1 + log (q (⌊T⌋ + 1))` for the central band. -/
noncomputable def dirichletLQuadraticConditionalCentralH (q : ℕ) (T : ℝ) : ℝ :=
  1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)

/-- The half-height `τ = min(T, c q^(-η) / (256 H₀²))` of the central band, chosen so that
`L` changes by at most `c q^(-η) / 4` between `1` and `1 + it` for `|t| ≤ τ`. -/
noncomputable def dirichletLQuadraticConditionalCentralHeight
    (c η : ℝ) (q : ℕ) (T : ℝ) : ℝ :=
  min T (c * (q : ℝ) ^ (-η) /
    (256 * (dirichletLQuadraticConditionalCentralH q T) ^ 2))

/-- The width `w = A q^(-2η) / H^12`, where `H` is the uniform bound for `H(q, t)` on
`τ ≤ |t| ≤ T`. -/
noncomputable def dirichletLQuadraticConditionalCrossZeroWidth
    (A c η : ℝ) (q : ℕ) (T : ℝ) : ℝ :=
  A * (q : ℝ) ^ (-2 * η) /
    (dirichletLQuadraticConditionalFixedH q
      (dirichletLQuadraticConditionalCentralHeight c η q T) T) ^ 12

/-- The rectangle `[1 - w, 2] × [-T, T]`. -/
def dirichletLQuadraticConditionalCrossZeroRectangle
    (A c η : ℝ) (q : ℕ) (T : ℝ) : Set ℂ :=
  (((1 - dirichletLQuadraticConditionalCrossZeroWidth A c η q T : ℝ) : ℂ) - I * T).Rectangle
    (2 + I * T)

private theorem central_parameters
    {q : ℕ} [NeZero q] {A c η T : ℝ}
    (hA : 0 < A) (hAc : A ≤ c / 256) (hAhalf : A ≤ 1 / 2)
    (hc : 0 < c) (hη : 0 < η) (hT : 0 < T) :
    let H₀ := dirichletLQuadraticConditionalCentralH q T
    let τ := dirichletLQuadraticConditionalCentralHeight c η q T
    let H := dirichletLQuadraticConditionalFixedH q τ T
    let w := dirichletLQuadraticConditionalCrossZeroWidth A c η q T
    1 ≤ H₀ ∧ 0 < τ ∧ τ ≤ T ∧ H₀ ≤ H ∧ 1 ≤ H ∧ 0 < w ∧
      w ≤ c * (q : ℝ) ^ (-η) / (256 * H₀ ^ 2) ∧ w ≤ 1 / H₀ := by
  dsimp only
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hcut : (1 : ℝ) ≤ dirichletLNonquadraticConductorLogCutoff q T := by
    exact_mod_cast (show 1 ≤ dirichletLNonquadraticConductorLogCutoff q T by
      unfold dirichletLNonquadraticConductorLogCutoff
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne q) (by
        unfold dirichletLNonquadraticConductorLogHeightBlock
        omega)))
  have hH₀ : 1 ≤ 1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T) := by
    linarith [Real.log_nonneg hcut]
  have hr : 0 < (q : ℝ) ^ (-η) := Real.rpow_pos_of_pos hq _
  have hp : 0 < (q : ℝ) ^ (-2 * η) := Real.rpow_pos_of_pos hq _
  have hpr : (q : ℝ) ^ (-2 * η) ≤ (q : ℝ) ^ (-η) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  let τ : ℝ := min T (c * (q : ℝ) ^ (-η) /
    (256 * (1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)) ^ 2))
  have hτ : 0 < τ := lt_min hT (by positivity)
  have hτT : τ ≤ T := min_le_left _ _
  have hlogarg : 0 ≤ Real.log (2 * T + 2) := Real.log_nonneg (by linarith)
  let H : ℝ := dirichletLQuadraticConditionalFixedH q τ T
  have hH₀H : 1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T) ≤ H := by
    dsimp only [H, dirichletLQuadraticConditionalFixedH]
    have hinv : 0 < 1 / (2 * τ) := by positivity
    linarith
  have hH : 1 ≤ H := hH₀.trans hH₀H
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  let w : ℝ := A * (q : ℝ) ^ (-2 * η) / H ^ 12
  have hw : 0 < w := by dsimp only [w]; positivity
  have hHpow2 :
      (1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)) ^ 2 ≤ H ^ 12 := by
    calc
      _ ≤ H ^ 2 := pow_le_pow_left₀ (zero_le_one.trans hH₀) hH₀H 2
      _ ≤ H ^ 12 := by exact pow_le_pow_right₀ hH (by omega)
  have hwbudget : w ≤ c * (q : ℝ) ^ (-η) /
      (256 * (1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)) ^ 2) := by
    rw [div_le_div_iff₀ (pow_pos hHpos 12) (by positivity)]
    have hAp : A * (q : ℝ) ^ (-2 * η) ≤ (c / 256) * (q : ℝ) ^ (-η) :=
      mul_le_mul hAc hpr hp.le (by positivity)
    calc
      A * (q : ℝ) ^ (-2 * η) *
          (256 * (1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)) ^ 2) ≤
          ((c / 256) * (q : ℝ) ^ (-η)) *
            (256 * (1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)) ^ 2) := by
              gcongr
      _ = c * (q : ℝ) ^ (-η) *
          (1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)) ^ 2 := by ring
      _ ≤ c * (q : ℝ) ^ (-η) * H ^ 12 := by gcongr
  have hwlog : w ≤ 1 / (1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)) := by
    apply (le_div_iff₀ (lt_of_lt_of_le zero_lt_one hH₀)).2
    dsimp only [w]
    rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hHpos 12)]
    have hAp1 : A * (q : ℝ) ^ (-2 * η) ≤ 1 := by
      have hp1 : (q : ℝ) ^ (-2 * η) ≤ 1 := by
        simpa using Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : -2 * η ≤ 0)
      calc
        A * (q : ℝ) ^ (-2 * η) ≤ (1 / 2 : ℝ) * 1 :=
          mul_le_mul hAhalf hp1 hp.le (by norm_num)
        _ ≤ 1 := by norm_num
    calc
      A * (q : ℝ) ^ (-2 * η) *
          (1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)) ≤
          1 * (1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)) :=
            mul_le_mul_of_nonneg_right hAp1 (zero_le_one.trans hH₀)
      _ ≤ H ^ 12 := by
        have hHpow : H ≤ H ^ 12 := by
          simpa only [pow_one] using (pow_le_pow_right₀ hH (by norm_num : 1 ≤ 12))
        simpa only [one_mul] using hH₀H.trans hHpow
      _ = 1 * H ^ 12 := by ring
  simpa only [dirichletLQuadraticConditionalCentralH,
    dirichletLQuadraticConditionalCentralHeight,
    dirichletLQuadraticConditionalCrossZeroWidth, τ, H, w] using
    And.intro hH₀ (And.intro hτ (And.intro hτT (And.intro hH₀H
      (And.intro hH (And.intro hw (And.intro hwbudget hwlog))))))

private theorem LFunction_ne_zero_centralBand
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1)
    {A c η T β t : ℝ}
    (hA : 0 < A) (hAc : A ≤ c / 256) (hAhalf : A ≤ 1 / 2)
    (hc : 0 < c) (hη : 0 < η) (hT : 0 < T)
    (hSiegel : c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re)
    (hβ : 1 - dirichletLQuadraticConditionalCrossZeroWidth A c η q T ≤ β)
    (hβone : β < 1)
    (ht : |t| ≤ dirichletLQuadraticConditionalCentralHeight c η q T) :
    χ.LFunction (β + I * t) ≠ 0 := by
  let H₀ := dirichletLQuadraticConditionalCentralH q T
  let τ := dirichletLQuadraticConditionalCentralHeight c η q T
  let w := dirichletLQuadraticConditionalCrossZeroWidth A c η q T
  have hp := central_parameters (q := q) hA hAc hAhalf hc hη hT
  dsimp only at hp
  have htT : |t| ≤ T := ht.trans hp.2.2.1
  have hcut := dirichletLConductorHeightCutoff_le_fixedHeightCutoff (q := q) htT
  have hcutpos : (0 : ℝ) < dirichletLConductorHeightCutoff q t := by
    exact_mod_cast Nat.mul_pos (NeZero.pos q) (by simp [dirichletLHeightBlock])
  have hcutR : (dirichletLConductorHeightCutoff q t : ℝ) ≤
      dirichletLNonquadraticConductorLogCutoff q T := by exact_mod_cast hcut
  have hlog : 1 + Real.log (dirichletLConductorHeightCutoff q t) ≤ H₀ := by
    dsimp only [H₀, dirichletLQuadraticConditionalCentralH]
    linarith [Real.log_le_log hcutpos hcutR]
  have hβhalf : 1 / 2 ≤ β := by
    have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hpq : 0 < (q : ℝ) ^ (-2 * η) := Real.rpow_pos_of_pos hq _
    have hpq1 : (q : ℝ) ^ (-2 * η) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : -2 * η ≤ 0)
    have hH : 1 ≤ dirichletLQuadraticConditionalFixedH q τ T := hp.2.2.2.2.1
    have hHpow : 1 ≤ (dirichletLQuadraticConditionalFixedH q τ T) ^ 12 :=
      one_le_pow₀ hH
    have hw_half : w ≤ 1 / 2 := by
      dsimp only [w, dirichletLQuadraticConditionalCrossZeroWidth]
      exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hHpow)).2
        ((mul_le_mul_of_nonneg_left hpq1 hA.le).trans (by nlinarith))
    dsimp only [w] at hw_half ⊢
    linarith
  have hnear : 1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ β := by
    have hlogpos := log_conductorHeightCutoff_pos χ hχ t
    have hw_invlog : w ≤ 1 / Real.log (dirichletLConductorHeightCutoff q t) := by
      apply (le_div_iff₀ hlogpos).2
      have hwH₀ : w * H₀ ≤ 1 := by
        apply (le_div_iff₀ (lt_of_lt_of_le zero_lt_one hp.1)).mp
        exact hp.2.2.2.2.2.2.2
      calc
        w * Real.log (dirichletLConductorHeightCutoff q t) ≤ w * H₀ := by
          have hlog' : Real.log (dirichletLConductorHeightCutoff q t) ≤ H₀ := by linarith [hlog]
          exact mul_le_mul_of_nonneg_left hlog' hp.2.2.2.2.2.1.le
        _ ≤ 1 := hwH₀
    linarith
  have hhorizontal := norm_LFunction_sub_le_sixtyfour_mul_conductorHeightLogSq
    χ hχ hβhalf hnear hβone.le (by norm_num : (1 : ℝ) ≤ 2)
  have hvertical := norm_LFunction_vertical_sub_le χ hχ t
  have hBh : ‖χ.LFunction (1 + t * I) - χ.LFunction (β + t * I)‖ ≤ 64 * H₀ ^ 2 * w := by
    calc
      _ ≤ 64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 * (1 - β) := by
        simpa using hhorizontal
      _ ≤ 64 * H₀ ^ 2 * w := by
        have hwidth : 1 - β ≤ w := by dsimp only [w] at hβ ⊢; linarith
        have hnonneg : 0 ≤ 1 - β := sub_nonneg.mpr hβone.le
        gcongr
  have hBv : ‖χ.LFunction (1 + t * I) - χ.LFunction 1‖ ≤ 64 * H₀ ^ 2 * τ := by
    calc
      _ ≤ 64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 * |t| := hvertical
      _ ≤ 64 * H₀ ^ 2 * τ := by gcongr
  have hwpay : 64 * H₀ ^ 2 * w ≤ c * (q : ℝ) ^ (-η) / 4 := by
    have hwraw := hp.2.2.2.2.2.2.1
    have hden : 0 < 256 * H₀ ^ 2 := by
      have : 0 < H₀ := lt_of_lt_of_le zero_lt_one hp.1
      positivity
    have hmul : 256 * H₀ ^ 2 * w ≤ c * (q : ℝ) ^ (-η) := by
      have hx := (le_div_iff₀ hden).mp (by simpa only [H₀, w] using hwraw)
      simpa only [mul_comm] using hx
    calc
      64 * H₀ ^ 2 * w = (1 / 4 : ℝ) * (256 * H₀ ^ 2 * w) := by ring
      _ ≤ (1 / 4 : ℝ) * (c * (q : ℝ) ^ (-η)) := by gcongr
      _ = c * (q : ℝ) ^ (-η) / 4 := by ring
  have hτpay : 64 * H₀ ^ 2 * τ ≤ c * (q : ℝ) ^ (-η) / 4 := by
    have hτbound : τ ≤ c * (q : ℝ) ^ (-η) / (256 * H₀ ^ 2) := by
      dsimp only [τ, dirichletLQuadraticConditionalCentralHeight]
      exact min_le_right _ _
    have hH₀pos : 0 < H₀ := lt_of_lt_of_le zero_lt_one hp.1
    have hden : 0 < 256 * H₀ ^ 2 := by positivity
    have hmul : 256 * H₀ ^ 2 * τ ≤ c * (q : ℝ) ^ (-η) := by
      have hx := (le_div_iff₀ hden).mp hτbound
      simpa only [mul_comm] using hx
    calc
      64 * H₀ ^ 2 * τ = (1 / 4 : ℝ) * (256 * H₀ ^ 2 * τ) := by ring
      _ ≤ (1 / 4 : ℝ) * (c * (q : ℝ) ^ (-η)) := by gcongr
      _ = c * (q : ℝ) ^ (-η) / 4 := by ring
  have hbudget : 64 * H₀ ^ 2 * w + 64 * H₀ ^ 2 * τ < (χ.LFunction 1).re := by
    have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    have hr : 0 < (q : ℝ) ^ (-η) := Real.rpow_pos_of_pos hq _
    have hhalf : 64 * H₀ ^ 2 * w + 64 * H₀ ^ 2 * τ ≤
        c * (q : ℝ) ^ (-η) / 2 := by linarith
    have hcr : 0 < c * (q : ℝ) ^ (-η) := mul_pos hc hr
    have hstrict : c * (q : ℝ) ^ (-η) / 2 < c * (q : ℝ) ^ (-η) := by linarith
    exact hhalf.trans_lt (hstrict.trans_le hSiegel)
  exact LFunction_ne_zero_lowHeight_of_twoSegmentBudgets χ hquad hχ hBh hBv hbudget

/-- If `c q^(-η) ≤ Re L(1, χ)` for a quadratic character `χ`, then `L(s, χ) ≠ 0` on the
rectangle `[1 - w, 2] × [-T, T]`, with `A > 0` depending only on `c` and `η`. -/
theorem exists_LFunction_ne_zero_quadratic
    (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ),
        χ ^ 2 = 1 → χ ≠ 1 → 0 < T →
        c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re →
        ∀ s ∈ dirichletLQuadraticConditionalCrossZeroRectangle A c η q T,
          χ.LFunction s ≠ 0 := by
  obtain ⟨A₀, hA₀, hzero₀⟩ :=
    exists_dirichletL_quadratic_conditional_powerZeroFree c η hc hη
  let A : ℝ := min A₀ (min (c / 256) (1 / 2))
  have hA : 0 < A := lt_min hA₀ (lt_min (div_pos hc (by norm_num)) (by norm_num))
  have hAA₀ : A ≤ A₀ := min_le_left _ _
  have hAc : A ≤ c / 256 := (min_le_right _ _).trans (min_le_left _ _)
  have hAhalf : A ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨A, hA, ?_⟩
  intro q _ χ T hquad hχ hT hSiegel s hs
  let τ := dirichletLQuadraticConditionalCentralHeight c η q T
  let w := dirichletLQuadraticConditionalCrossZeroWidth A c η q T
  have hp := central_parameters (q := q) hA hAc hAhalf hc hη hT
  dsimp only at hp
  have hrect : (1 - w ≤ s.re ∧ s.re ≤ 2) ∧ (-T ≤ s.im ∧ s.im ≤ T) := by
    rw [dirichletLQuadraticConditionalCrossZeroRectangle, Complex.Rectangle,
      Complex.mem_reProdIm] at hs
    norm_num at hs
    rw [Set.uIcc_of_le (by
      have hw : 0 < w := hp.2.2.2.2.2.1
      linarith), Set.uIcc_of_le (by linarith : -T ≤ T)] at hs
    exact ⟨⟨hs.1.1, hs.1.2⟩, ⟨hs.2.1, hs.2.2⟩⟩
  by_cases hre : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) hre
  have hrelt : s.re < 1 := lt_of_not_ge hre
  by_cases hcentral : |s.im| ≤ τ
  · have hz := LFunction_ne_zero_centralBand χ hquad hχ hA hAc hAhalf hc hη hT hSiegel
      hrect.1.1 hrelt (by simpa only [τ] using hcentral)
    simpa only [mul_comm I, Complex.re_add_im] using hz
  · have hτabs : τ ≤ |s.im| := le_of_not_ge hcentral
    have hzero : ∀ (β t : ℝ),
        β ∈ Ico
          (1 - A * (q : ℝ) ^ (-2 * η) /
            (dirichletLQuadraticConditionalPowerZeroFreeH q t) ^ 12) 1 →
        χ.LFunction (β + I * t) ≠ 0 := by
      intro β t hβ
      apply hzero₀ q χ β t hquad hχ hSiegel
      refine ⟨?_, hβ.2⟩
      have hHpos : 0 < dirichletLQuadraticConditionalPowerZeroFreeH q t :=
        lt_of_lt_of_le zero_lt_one (one_le_dirichletLQuadraticConditionalPowerZeroFreeH q t)
      have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
      have hpq : 0 < (q : ℝ) ^ (-2 * η) := Real.rpow_pos_of_pos hq _
      have hwidth : A * (q : ℝ) ^ (-2 * η) /
          (dirichletLQuadraticConditionalPowerZeroFreeH q t) ^ 12 ≤
          A₀ * (q : ℝ) ^ (-2 * η) /
          (dirichletLQuadraticConditionalPowerZeroFreeH q t) ^ 12 := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hAA₀ hpq.le)
          (pow_nonneg hHpos.le 12)
      exact (sub_le_sub_left hwidth 1).trans hβ.1
    by_cases him : 0 ≤ s.im
    · apply LFunction_ne_zero_on_quadraticConditionalUpperRectangle χ hχ hA hp.2.1 hp.2.2.1 hzero
      rw [dirichletLQuadraticConditionalUpperRectangle, Complex.Rectangle,
        Complex.mem_reProdIm]
      norm_num
      rw [Set.uIcc_of_le (by
        change 1 - w ≤ 2
        linarith [hp.2.2.2.2.2.1]), Set.uIcc_of_le hp.2.2.1]
      refine ⟨⟨?_, hrect.1.2⟩, ?_, hrect.2.2⟩
      · simpa only [dirichletLQuadraticConditionalFixedLeft, w,
          dirichletLQuadraticConditionalCrossZeroWidth] using hrect.1.1
      · rw [abs_of_nonneg him] at hτabs
        exact hτabs
    · have him' : s.im ≤ 0 := le_of_not_ge him
      apply LFunction_ne_zero_on_quadraticConditionalLowerRectangle χ hχ hA hp.2.1 hp.2.2.1 hzero
      rw [dirichletLQuadraticConditionalLowerRectangle, Complex.Rectangle,
        Complex.mem_reProdIm]
      norm_num
      rw [Set.uIcc_of_le (by
        change 1 - w ≤ 2
        linarith [hp.2.2.2.2.2.1]), Set.uIcc_of_le (by linarith : -T ≤ -τ)]
      refine ⟨⟨?_, hrect.1.2⟩, hrect.2.1, ?_⟩
      · simpa only [dirichletLQuadraticConditionalFixedLeft, w,
          dirichletLQuadraticConditionalCrossZeroWidth] using hrect.1.1
      · rw [abs_of_nonpos him'] at hτabs
        linarith

/-!
## `L'/L` on the central band

The lower bound `c q^(-η) ≤ L(1, χ)` gives `‖L(s, χ)‖ ≥ c q^(-η) / 2` on the part of the
rectangle with `|t| ≤ τ`, and hence `‖L'/L(s, χ)‖ ≪ H₀² q^η / c` there.
-/

private theorem central_band_parameter_bounds
    {q : ℕ} [NeZero q] {A c η T : ℝ}
    (hA : 0 < A) (hAc : A ≤ c / 256) (hAhalf : A ≤ 1 / 2)
    (hc : 0 < c) (hη : 0 < η) (hT : 0 < T) :
    let H₀ := dirichletLQuadraticConditionalCentralH q T
    let H := dirichletLQuadraticConditionalFixedH q
      (dirichletLQuadraticConditionalCentralHeight c η q T) T
    let w := dirichletLQuadraticConditionalCrossZeroWidth A c η q T
    1 ≤ H₀ ∧ H₀ ≤ H ∧ 0 < w ∧
      64 * H₀ ^ 2 * w ≤ c * (q : ℝ) ^ (-η) / 4 ∧
      w ≤ 1 / H₀ := by
  dsimp only
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hq1 : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hcut : (1 : ℝ) ≤ dirichletLNonquadraticConductorLogCutoff q T := by
    exact_mod_cast (show 1 ≤ dirichletLNonquadraticConductorLogCutoff q T by
      unfold dirichletLNonquadraticConductorLogCutoff
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne q) (by
        unfold dirichletLNonquadraticConductorLogHeightBlock
        omega)))
  let H₀ : ℝ := dirichletLQuadraticConditionalCentralH q T
  let τ : ℝ := dirichletLQuadraticConditionalCentralHeight c η q T
  let H : ℝ := dirichletLQuadraticConditionalFixedH q τ T
  let w : ℝ := dirichletLQuadraticConditionalCrossZeroWidth A c η q T
  have hH₀ : 1 ≤ H₀ := by
    dsimp only [H₀, dirichletLQuadraticConditionalCentralH]
    linarith [Real.log_nonneg hcut]
  have hτ : 0 < τ := by
    dsimp only [τ, dirichletLQuadraticConditionalCentralHeight]
    exact lt_min hT (by positivity)
  have hH₀H : H₀ ≤ H := by
    dsimp only [H₀, H, dirichletLQuadraticConditionalCentralH,
      dirichletLQuadraticConditionalFixedH]
    have hlogarg : 0 ≤ Real.log (2 * T + 2) := Real.log_nonneg (by linarith)
    have hinv : 0 < 1 / (2 * τ) := by positivity
    linarith
  have hH : 1 ≤ H := hH₀.trans hH₀H
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hp : 0 < (q : ℝ) ^ (-2 * η) := Real.rpow_pos_of_pos hq _
  have hpr : (q : ℝ) ^ (-2 * η) ≤ (q : ℝ) ^ (-η) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hw : 0 < w := by
    dsimp only [w, dirichletLQuadraticConditionalCrossZeroWidth]
    positivity
  have hHpow2 : H₀ ^ 2 ≤ H ^ 12 := by
    calc
      H₀ ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ (zero_le_one.trans hH₀) hH₀H 2
      _ ≤ H ^ 12 := pow_le_pow_right₀ hH (by omega)
  have hwpay : 64 * H₀ ^ 2 * w ≤ c * (q : ℝ) ^ (-η) / 4 := by
    have hwbudget : w ≤ c * (q : ℝ) ^ (-η) / (256 * H₀ ^ 2) := by
      dsimp only [w, dirichletLQuadraticConditionalCrossZeroWidth]
      rw [div_le_div_iff₀ (pow_pos hHpos 12) (by positivity)]
      have hAp : A * (q : ℝ) ^ (-2 * η) ≤ (c / 256) * (q : ℝ) ^ (-η) :=
        mul_le_mul hAc hpr hp.le (by positivity)
      calc
        A * (q : ℝ) ^ (-2 * η) * (256 * H₀ ^ 2) ≤
            ((c / 256) * (q : ℝ) ^ (-η)) * (256 * H₀ ^ 2) := by gcongr
        _ = c * (q : ℝ) ^ (-η) * H₀ ^ 2 := by ring
        _ ≤ c * (q : ℝ) ^ (-η) * H ^ 12 := by gcongr
    have hmul : 256 * H₀ ^ 2 * w ≤ c * (q : ℝ) ^ (-η) := by
      have hx := (le_div_iff₀ (by positivity : 0 < 256 * H₀ ^ 2)).mp hwbudget
      simpa only [mul_comm] using hx
    calc
      64 * H₀ ^ 2 * w = (1 / 4 : ℝ) * (256 * H₀ ^ 2 * w) := by ring
      _ ≤ (1 / 4 : ℝ) * (c * (q : ℝ) ^ (-η)) := by gcongr
      _ = c * (q : ℝ) ^ (-η) / 4 := by ring
  have hp1 : (q : ℝ) ^ (-2 * η) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : -2 * η ≤ 0)
  have hwH₀ : w * H₀ ≤ 1 := by
    dsimp only [w, dirichletLQuadraticConditionalCrossZeroWidth]
    rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hHpos 12)]
    calc
      A * (q : ℝ) ^ (-2 * η) * H₀ ≤ H₀ := by
        have hprod : A * (q : ℝ) ^ (-2 * η) ≤ 1 := by
          calc
            A * (q : ℝ) ^ (-2 * η) ≤ (1 / 2 : ℝ) * 1 :=
              mul_le_mul hAhalf hp1 hp.le (by norm_num)
            _ ≤ 1 := by norm_num
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hprod (zero_le_one.trans hH₀)
      _ ≤ H ^ 12 := hH₀H.trans (by
        simpa only [pow_one] using (pow_le_pow_right₀ hH (by norm_num : 1 ≤ 12)))
      _ = 1 * H ^ 12 := by ring
  have hwInv : w ≤ 1 / H₀ := (le_div_iff₀ (lt_of_lt_of_le zero_lt_one hH₀)).2
    (by simpa [mul_comm] using hwH₀)
  simpa only [H₀, H, w, τ] using ⟨hH₀, hH₀H, hw, hwpay, hwInv⟩

/-- A point `β + it` of the central band satisfies the hypotheses of the derivative bound. -/
private theorem central_band_point_bounds
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A c η T β t : ℝ}
    (hA : 0 < A) (hAc : A ≤ c / 256) (hAhalf : A ≤ 1 / 2)
    (hc : 0 < c) (hη : 0 < η) (hT : 0 < T)
    (hβ : 1 - dirichletLQuadraticConditionalCrossZeroWidth A c η q T ≤ β)
    (ht : |t| ≤ dirichletLQuadraticConditionalCentralHeight c η q T) :
    1 / 2 ≤ β ∧
      1 + Real.log (dirichletLConductorHeightCutoff q t) ≤
        dirichletLQuadraticConditionalCentralH q T ∧
      1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ β := by
  let H₀ := dirichletLQuadraticConditionalCentralH q T
  let τ := dirichletLQuadraticConditionalCentralHeight c η q T
  let w := dirichletLQuadraticConditionalCrossZeroWidth A c η q T
  have hp := central_band_parameter_bounds (q := q) hA hAc hAhalf hc hη hT
  dsimp only at hp
  have htT : |t| ≤ T := ht.trans (by
    dsimp only [τ, dirichletLQuadraticConditionalCentralHeight]
    exact min_le_left _ _)
  have hcut := dirichletLConductorHeightCutoff_le_fixedHeightCutoff (q := q) htT
  have hcutpos : (0 : ℝ) < dirichletLConductorHeightCutoff q t := by
    exact_mod_cast Nat.mul_pos (NeZero.pos q) (by simp [dirichletLHeightBlock])
  have hcutR : (dirichletLConductorHeightCutoff q t : ℝ) ≤
      dirichletLNonquadraticConductorLogCutoff q T := by exact_mod_cast hcut
  have hlog : 1 + Real.log (dirichletLConductorHeightCutoff q t) ≤ H₀ := by
    dsimp only [H₀, dirichletLQuadraticConditionalCentralH]
    linarith [Real.log_le_log hcutpos hcutR]
  have hβhalf : 1 / 2 ≤ β := by
    have hq1 : (1 : ℝ) ≤ q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hpq1 : (q : ℝ) ^ (-2 * η) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : -2 * η ≤ 0)
    have Hge : 1 ≤ dirichletLQuadraticConditionalFixedH q τ T := hp.1.trans hp.2.1
    have hw_half : w ≤ 1 / 2 := by
      dsimp only [w, dirichletLQuadraticConditionalCrossZeroWidth]
      rw [div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one Hge) 12)]
      calc
        A * (q : ℝ) ^ (-2 * η) ≤ 1 / 2 := by
          calc
            A * (q : ℝ) ^ (-2 * η) ≤ (1 / 2 : ℝ) * 1 :=
              mul_le_mul hAhalf hpq1 (Real.rpow_nonneg (by positivity) _) (by norm_num)
            _ = 1 / 2 := by ring
        _ ≤ (1 / 2) * (dirichletLQuadraticConditionalFixedH q τ T) ^ 12 := by
          simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left (one_le_pow₀ Hge) (by norm_num : (0 : ℝ) ≤ 1 / 2))
    dsimp only [w] at hw_half hβ
    linarith
  have hnear : 1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ β := by
    have hlogpos := log_conductorHeightCutoff_pos χ hχ t
    have hwlog : w ≤ 1 / Real.log (dirichletLConductorHeightCutoff q t) := by
      apply (le_div_iff₀ hlogpos).2
      calc
        w * Real.log (dirichletLConductorHeightCutoff q t) ≤ w * H₀ := by
          exact mul_le_mul_of_nonneg_left (by linarith [hlog]) hp.2.2.1.le
        _ ≤ 1 := by
          exact (le_div_iff₀ (lt_of_lt_of_le zero_lt_one hp.1)).mp hp.2.2.2.2
    dsimp only [w] at hwlog hβ
    linarith
  exact ⟨hβhalf, hlog, hnear⟩

/-- On the central band `‖L(β + it, χ)‖ ≥ c q^(-η) / 2`, since `L` changes by at most
`c q^(-η) / 4` along each of the segments from `1` to `1 + it` and from `1 + it` to
`β + it`. -/
theorem norm_LFunction_ge_half_on_centralBand
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A c η T β t : ℝ}
    (hA : 0 < A) (hAc : A ≤ c / 256) (hAhalf : A ≤ 1 / 2)
    (hc : 0 < c) (hη : 0 < η) (hT : 0 < T)
    (hSiegel : c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re)
    (hβ : 1 - dirichletLQuadraticConditionalCrossZeroWidth A c η q T ≤ β)
    (hβone : β ≤ 1)
    (ht : |t| ≤ dirichletLQuadraticConditionalCentralHeight c η q T) :
    c * (q : ℝ) ^ (-η) / 2 ≤ ‖χ.LFunction (β + I * t)‖ := by
  let H₀ := dirichletLQuadraticConditionalCentralH q T
  let τ := dirichletLQuadraticConditionalCentralHeight c η q T
  let w := dirichletLQuadraticConditionalCrossZeroWidth A c η q T
  have hp := central_band_parameter_bounds (q := q) hA hAc hAhalf hc hη hT
  dsimp only at hp
  obtain ⟨hβhalf, hlog, hnear⟩ :=
    central_band_point_bounds χ hχ hA hAc hAhalf hc hη hT hβ ht
  have hhorizontal := norm_LFunction_sub_le_sixtyfour_mul_conductorHeightLogSq
    χ hχ hβhalf hnear hβone (by norm_num : (1 : ℝ) ≤ 2)
  have hvertical := norm_LFunction_vertical_sub_le χ hχ t
  have hBh : ‖χ.LFunction (1 + t * I) - χ.LFunction (β + t * I)‖ ≤
      64 * H₀ ^ 2 * w := by
    calc
      _ ≤ 64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 * (1 - β) := by
        simpa using hhorizontal
      _ ≤ 64 * H₀ ^ 2 * w := by
        have hwidth : 1 - β ≤ w := by dsimp only [w] at hβ ⊢; linarith
        gcongr
  have hτpay : 64 * H₀ ^ 2 * τ ≤ c * (q : ℝ) ^ (-η) / 4 := by
    have hτbound : τ ≤ c * (q : ℝ) ^ (-η) / (256 * H₀ ^ 2) := by
      dsimp only [τ, H₀, dirichletLQuadraticConditionalCentralHeight]
      exact min_le_right _ _
    have hH₀pos : 0 < H₀ := lt_of_lt_of_le zero_lt_one hp.1
    have hmul : 256 * H₀ ^ 2 * τ ≤ c * (q : ℝ) ^ (-η) := by
      have hx := (le_div_iff₀ (by positivity : 0 < 256 * H₀ ^ 2)).mp hτbound
      simpa only [mul_comm] using hx
    calc
      64 * H₀ ^ 2 * τ = (1 / 4 : ℝ) * (256 * H₀ ^ 2 * τ) := by ring
      _ ≤ (1 / 4 : ℝ) * (c * (q : ℝ) ^ (-η)) := by gcongr
      _ = c * (q : ℝ) ^ (-η) / 4 := by ring
  have hBv : ‖χ.LFunction (1 + t * I) - χ.LFunction 1‖ ≤
      c * (q : ℝ) ^ (-η) / 4 := by
    calc
      _ ≤ 64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 * |t| := hvertical
      _ ≤ 64 * H₀ ^ 2 * τ := by gcongr
      _ ≤ _ := hτpay
  have hclose : ‖χ.LFunction (β + I * t) - χ.LFunction 1‖ ≤
      c * (q : ℝ) ^ (-η) / 2 := by
    calc
      _ ≤ ‖χ.LFunction (β + I * t) - χ.LFunction (1 + I * t)‖ +
          ‖χ.LFunction (1 + I * t) - χ.LFunction 1‖ := by
            simpa only [sub_add_sub_cancel] using norm_add_le
              (χ.LFunction (β + I * t) - χ.LFunction (1 + I * t))
              (χ.LFunction (1 + I * t) - χ.LFunction 1)
      _ ≤ 64 * H₀ ^ 2 * w + c * (q : ℝ) ^ (-η) / 4 := by
        gcongr
        · rw [norm_sub_rev]
          simpa [mul_comm] using hBh
        · simpa [mul_comm] using hBv
      _ ≤ c * (q : ℝ) ^ (-η) / 2 := by linarith [hp.2.2.2.1]
  have hLone : c * (q : ℝ) ^ (-η) ≤ ‖χ.LFunction 1‖ :=
    hSiegel.trans (Complex.re_le_norm _)
  calc
    c * (q : ℝ) ^ (-η) / 2
        ≤ ‖χ.LFunction 1‖ - ‖χ.LFunction (β + I * t) - χ.LFunction 1‖ := by linarith
    _ ≤ ‖χ.LFunction (β + I * t)‖ := by
      have htri := norm_add_le
        (χ.LFunction 1 - χ.LFunction (β + I * t)) (χ.LFunction (β + I * t))
      rw [sub_add_cancel] at htri
      have hrev : ‖χ.LFunction 1 - χ.LFunction (β + I * t)‖ =
          ‖χ.LFunction (β + I * t) - χ.LFunction 1‖ := norm_sub_rev _ _
      rw [hrev] at htri
      linarith

/-- On the central band `‖L'/L(β + it, χ)‖ ≤ 128 H₀² / (c q^(-η))`. -/
theorem norm_logDerivative_le_on_quadraticConditionalCentralBand
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A c η T β t : ℝ}
    (hA : 0 < A) (hAc : A ≤ c / 256) (hAhalf : A ≤ 1 / 2)
    (hc : 0 < c) (hη : 0 < η) (hT : 0 < T)
    (hSiegel : c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re)
    (hβ : 1 - dirichletLQuadraticConditionalCrossZeroWidth A c η q T ≤ β)
    (hβone : β ≤ 1)
    (ht : |t| ≤ dirichletLQuadraticConditionalCentralHeight c η q T) :
    ‖deriv χ.LFunction (β + I * t) / χ.LFunction (β + I * t)‖ ≤
      (128 * (dirichletLQuadraticConditionalCentralH q T) ^ 2) /
        (c * (q : ℝ) ^ (-η)) := by
  have hlower := norm_LFunction_ge_half_on_centralBand
    χ hχ hA hAc hAhalf hc hη hT hSiegel hβ hβone ht
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hden : 0 < c * (q : ℝ) ^ (-η) := mul_pos hc (Real.rpow_pos_of_pos hq _)
  obtain ⟨hβhalf, hlog, hnear⟩ :=
    central_band_point_bounds χ hχ hA hAc hAhalf hc hη hT hβ ht
  have hderiv := norm_deriv_LFunction_le_one_add_log_sq
    χ hχ hβhalf (by linarith) hnear
  rw [norm_div]
  calc
    ‖deriv χ.LFunction (β + I * t)‖ / ‖χ.LFunction (β + I * t)‖
        ≤ ‖deriv χ.LFunction (β + I * t)‖ /
            (c * (q : ℝ) ^ (-η) / 2) := by
          exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hlower
    _ ≤ (64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2) /
            (c * (q : ℝ) ^ (-η) / 2) := by
          exact div_le_div_of_nonneg_right hderiv (by positivity)
    _ ≤ (64 * (dirichletLQuadraticConditionalCentralH q T) ^ 2) /
            (c * (q : ℝ) ^ (-η) / 2) := by
          gcongr
    _ = (128 * (dirichletLQuadraticConditionalCentralH q T) ^ 2) /
            (c * (q : ℝ) ^ (-η)) := by field_simp; ring

end BombieriVinogradov

end

section

/-!
## `L'/L` on the annulus and on the whole rectangle

On `τ ≤ |t| ≤ T` the `(3,4,1)` inequality gives an explicit lower bound for `‖L(s, χ)‖`,
and hence a bound for `L'/L`. Together with the central band this bounds `L'/L` on
`[1 - w, 1] × [-T, T]`.
-/

set_option maxHeartbeats 800000
open Complex Set

namespace BombieriVinogradov

open BombieriVinogradov.LValueBound
open BombieriVinogradov.LDerivBound

private theorem fixedH_annular_bounds
    {q : ℕ} [NeZero q] {τ T t : ℝ}
    (hτ : 0 < τ) (hτT : τ ≤ T) (htlow : τ ≤ |t|) (htT : |t| ≤ T) :
    let H := dirichletLQuadraticConditionalFixedH q τ T
    1 ≤ H ∧
      1 + Real.log q ≤ H ∧
      1 + Real.log (|2 * t| + 2) + 1 / |2 * t| ≤ H ∧
      1 + Real.log (dirichletLConductorHeightCutoff q t) ≤ H := by
  dsimp only
  have hHt := dirichletLQuadraticConditionalPowerZeroFreeH_le_fixedH
    (q := q) hτ hτT htlow htT
  have hHone := one_le_dirichletLQuadraticConditionalPowerZeroFreeH q t
  have hcond := one_add_log_conductorHeightCutoff_le_quadraticH q t
  have ht : t ≠ 0 := by
    intro ht
    subst t
    simp only [abs_zero] at htlow
    linarith
  have hpole := one_add_log_twoHeight_add_inv_le_quadraticH q ht
  have hqcut : q ≤ dirichletLConductorHeightCutoff q t := by
    unfold dirichletLConductorHeightCutoff
    exact Nat.le_mul_of_pos_right q (by simp [dirichletLHeightBlock])
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hcast : (q : ℝ) ≤ dirichletLConductorHeightCutoff q t := by exact_mod_cast hqcut
  have hlogq := Real.log_le_log hqpos hcast
  exact ⟨hHone.trans hHt, (by linarith [hcond.trans hHt]),
    hpole.trans hHt, hcond.trans hHt⟩

private theorem powerWidth_le_half_and_inv_log
    {A p H L : ℝ} (hA : 0 < A) (hAhalf : A ≤ 1 / 2)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hH1 : 1 ≤ H)
    (hL : 0 < L) (hLH : L ≤ H) :
    let x := A * p / H ^ 12
    x ≤ 1 / 2 ∧ x ≤ 1 / L := by
  dsimp only
  have hH : 0 < H := zero_lt_one.trans_le hH1
  have hAp : A * p ≤ A := mul_le_of_le_one_right hA.le hp1
  have hHpow : 1 ≤ H ^ 12 := one_le_pow₀ hH1
  have hhalf : A * p / H ^ 12 ≤ 1 / 2 := by
    calc
      A * p / H ^ 12 ≤ A := by
        rw [div_le_iff₀ (pow_pos hH 12)]
        exact hAp.trans (le_mul_of_one_le_right hA.le hHpow)
      _ ≤ 1 / 2 := hAhalf
  refine ⟨hhalf, (le_div_iff₀ hL).2 ?_⟩
  calc
    A * p / H ^ 12 * L ≤ A * p / H ^ 12 * H :=
      mul_le_mul_of_nonneg_left hLH (by positivity)
    _ ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hH 12), one_mul]
      have hAp1 : A * p ≤ 1 := hAp.trans (hAhalf.trans (by norm_num))
      have hHle : H ≤ H ^ 12 := by
        calc
          H = H * 1 := (mul_one H).symm
          _ ≤ H * H ^ 11 := mul_le_mul_of_nonneg_left (one_le_pow₀ hH1) hH.le
          _ = H ^ 12 := by ring
      exact (mul_le_of_le_one_left hH.le hAp1).trans hHle

/-- On `τ ≤ |t| ≤ T`, `‖L(β + it, χ)‖ ≥ 64 H² x` with `x = A q^(-2η) / H^12`. Otherwise
`‖L(1 + x + it, χ)‖ < 192 H² x`, which contradicts the `(3,4,1)` inequality. -/
theorem norm_LFunction_ge_on_quadraticConditionalAnnulus
    (Z : ℝ) (hZ : 0 < Z)
    (hzeta : ∀ (x u : ℝ), 0 < x → x ≤ 1 → u ≠ 0 →
      ‖riemannZeta (1 + x + I * u)‖ ≤
        Z * (1 + Real.log (|u| + 2) + 1 / |u|))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1)
    {A η τ T β t : ℝ}
    (hA : 0 < A) (hAhalf : A ≤ 1 / 2)
    (hAsmall : A ≤ 1 / (16 * Z * 192 ^ 4))
    (hη : 0 < η) (hτ : 0 < τ) (hτT : τ ≤ T)
    (hβ : dirichletLQuadraticConditionalFixedLeft A η q τ T ≤ β)
    (hβone : β ≤ 1) (htlow : τ ≤ |t|) (htT : |t| ≤ T) :
    let H := dirichletLQuadraticConditionalFixedH q τ T
    let x := A * (q : ℝ) ^ (-2 * η) / H ^ 12
    64 * H ^ 2 * x ≤ ‖χ.LFunction (β + I * t)‖ := by
  dsimp only
  let H : ℝ := dirichletLQuadraticConditionalFixedH q τ T
  let p : ℝ := (q : ℝ) ^ (-2 * η)
  let x : ℝ := A * p / H ^ 12
  change 64 * H ^ 2 * x ≤ ‖χ.LFunction (β + I * t)‖
  have hb := fixedH_annular_bounds (q := q) hτ hτT htlow htT
  dsimp only at hb
  have hH1 : 1 ≤ H := by simpa only [H] using hb.1
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  have hq1 : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hp : 0 < p := by
    dsimp only [p]
    exact Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hq1) _
  have hp1 : p ≤ 1 := by
    dsimp only [p]
    simpa using Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : -2 * η ≤ 0)
  have hx : 0 < x := by dsimp only [x]; positivity
  have hlogH : 1 + Real.log (dirichletLConductorHeightCutoff q t) ≤ H := by
    simpa only [H] using hb.2.2.2
  obtain ⟨hxhalf, hxlog⟩ := powerWidth_le_half_and_inv_log
    hA hAhalf hp.le hp1 hH1 (log_conductorHeightCutoff_pos χ hχ t)
      (by linarith only [hlogH])
  have hx1 : x ≤ 1 := hxhalf.trans (by norm_num)
  have hβleft : 1 - x ≤ β := by
    simpa only [dirichletLQuadraticConditionalFixedLeft, x, p, H] using hβ
  have hβhalf : 1 / 2 ≤ β := by linarith only [hβleft, hxhalf]
  have hnear : 1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ β := by
    linarith only [hβleft, hxlog]
  have hdiff0 := norm_LFunction_sub_le_sixtyfour_mul_conductorHeightLogSq
    χ hχ (σ₁ := β) (σ₂ := 1 + x) (t := t) hβhalf hnear
      (by linarith) (by linarith [hx1] : 1 + x ≤ 2)
  have hdiff :
      ‖χ.LFunction (1 + x + I * t) - χ.LFunction (β + I * t)‖ ≤
        128 * H ^ 2 * x := by
    calc
      _ ≤ 64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 *
          ((1 + x) - β) := by
            convert hdiff0 using 1; push_cast; ring_nf
      _ ≤ 64 * H ^ 2 * (2 * x) := by
        have hwidth : 1 - β ≤ x := by linarith
        have hinterval : 0 ≤ (1 + x) - β := by linarith
        have htwo : (1 + x) - β ≤ 2 * x := by linarith
        gcongr
      _ = 128 * H ^ 2 * x := by ring
  have ht : t ≠ 0 := by
    intro ht
    subst t
    simp only [abs_zero] at htlow
    linarith
  have htriv : ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ≤ 2 / x := by
    rw [DirichletCharacter.LFunctionTrivChar]
    calc
      ‖(1 : DirichletCharacter ℂ q).LFunction (1 + x)‖ ≤ 1 + 1 / x := by
        convert norm_dirichletLFunction_le
          (1 : DirichletCharacter ℂ q) (1 + x) 0 (by linarith) using 1 <;> norm_num
      _ ≤ 2 / x := by
        rw [le_div_iff₀ hx]
        field_simp [ne_of_gt hx]
        linarith
  have hsquare := norm_quadraticSquare_LFunction_le_principalPolePlusLog
    Z hzeta χ hquad hx hx1 ht
  have hprod : 1 ≤
      ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ^ 3 *
        ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
        ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖ := by
    have hpv := χ.norm_LFunction_product_ge_one hx t
    convert (show 1 ≤
        ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ^ 3 *
          ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
          ‖(χ ^ 2).LFunction (1 + x + 2 * I * t)‖ by
      simpa only [norm_mul, norm_pow] using hpv) using 1; ring_nf
  by_contra! hlow
  have hright : ‖χ.LFunction (1 + x + I * t)‖ < 192 * H ^ 2 * x := by
    have htri := norm_add_le
      (χ.LFunction (1 + x + I * t) - χ.LFunction (β + I * t))
      (χ.LFunction (β + I * t))
    rw [sub_add_cancel] at htri
    nlinarith
  have hSpos : 0 < 1 + Real.log (|2 * t| + 2) + 1 / |2 * t| := by
    have habs : 0 < |2 * t| := abs_pos.mpr (mul_ne_zero (by norm_num) ht)
    have hlogtwo : 0 ≤ Real.log (|2 * t| + 2) :=
      Real.log_nonneg (by linarith [abs_nonneg (2 * t)])
    positivity
  have hmajor : 1 < (2 / x) ^ 3 * (192 * H ^ 2 * x) ^ 4 *
      ((1 + Real.log q) *
        (Z * (1 + Real.log (|2 * t| + 2) + 1 / |2 * t|))) := by
    calc
      1 ≤ ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ^ 3 *
          ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
          ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖ := hprod
      _ ≤ (2 / x) ^ 3 * ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
          ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖ := by gcongr
      _ ≤ (2 / x) ^ 3 * ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
          ((1 + Real.log q) *
            (Z * (1 + Real.log (|2 * t| + 2) + 1 / |2 * t|))) := by gcongr
      _ < _ := by gcongr
  have hmajorH : 1 < (2 / x) ^ 3 * (192 * H ^ 2 * x) ^ 4 *
      (H * (Z * H)) := by
    have hqH : 1 + Real.log q ≤ H := by simpa only [H] using hb.2.1
    have hSH : 1 + Real.log (|2 * t| + 2) + 1 / |2 * t| ≤ H := by
      simpa only [H] using hb.2.2.1
    have hfactorUpper :
        (1 + Real.log q) *
            (Z * (1 + Real.log (|2 * t| + 2) + 1 / |2 * t|)) ≤ H * (Z * H) := by
      gcongr
    exact hmajor.trans_le
      (mul_le_mul_of_nonneg_left hfactorUpper (by positivity))
  have hmul := mul_lt_mul_of_pos_left hmajorH (pow_pos hx 3)
  have hcontr : x ^ 3 < 8 * Z * 192 ^ 4 * H ^ 10 * x ^ 4 := by
    calc
      x ^ 3 = x ^ 3 * 1 := by ring
      _ < x ^ 3 * ((2 / x) ^ 3 * (192 * H ^ 2 * x) ^ 4 *
          (H * (Z * H))) := hmul
      _ = 8 * Z * 192 ^ 4 * H ^ 10 * x ^ 4 := by
        field_simp [ne_of_gt hx]
        ring
  have hdenpos : 0 < 16 * Z * 192 ^ 4 := by positivity
  have hZA : 16 * Z * 192 ^ 4 * A ≤ 1 := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      (le_div_iff₀ hdenpos).mp hAsmall
  have hZAp : 16 * Z * 192 ^ 4 * A * p ≤ 1 :=
    (mul_le_of_le_one_right (by positivity) hp1).trans hZA
  have hfactor : 8 * Z * 192 ^ 4 * A * p / H ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ (pow_pos hH 2)]
    nlinarith [one_le_pow₀ hH1 (n := 2)]
  have hid : 8 * Z * 192 ^ 4 * H ^ 10 * x ^ 4 =
      (8 * Z * 192 ^ 4 * A * p / H ^ 2) * x ^ 3 := by
    dsimp only [x]
    field_simp [ne_of_gt hH]
  rw [hid] at hcontr
  have hhalf :
      (8 * Z * 192 ^ 4 * A * p / H ^ 2) * x ^ 3 ≤ (1 / 2) * x ^ 3 :=
    mul_le_mul_of_nonneg_right hfactor (pow_nonneg hx.le 3)
  nlinarith [pow_pos hx 3]

/-- On `τ ≤ |t| ≤ T`, `‖L'/L(β + it, χ)‖ ≤ H^12 / (A q^(-2η))`. -/
theorem norm_logDerivative_le_on_quadraticConditionalAnnulus
    (Z : ℝ) (hZ : 0 < Z)
    (hzeta : ∀ (x u : ℝ), 0 < x → x ≤ 1 → u ≠ 0 →
      ‖riemannZeta (1 + x + I * u)‖ ≤
        Z * (1 + Real.log (|u| + 2) + 1 / |u|))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1)
    {A η τ T β t : ℝ}
    (hA : 0 < A) (hAhalf : A ≤ 1 / 2)
    (hAsmall : A ≤ 1 / (16 * Z * 192 ^ 4))
    (hη : 0 < η) (hτ : 0 < τ) (hτT : τ ≤ T)
    (hβ : dirichletLQuadraticConditionalFixedLeft A η q τ T ≤ β)
    (hβone : β ≤ 1) (htlow : τ ≤ |t|) (htT : |t| ≤ T) :
    ‖deriv χ.LFunction (β + I * t) / χ.LFunction (β + I * t)‖ ≤
      (dirichletLQuadraticConditionalFixedH q τ T) ^ 12 /
        (A * (q : ℝ) ^ (-2 * η)) := by
  let H : ℝ := dirichletLQuadraticConditionalFixedH q τ T
  let p : ℝ := (q : ℝ) ^ (-2 * η)
  let x : ℝ := A * p / H ^ 12
  change ‖deriv χ.LFunction (β + I * t) / χ.LFunction (β + I * t)‖ ≤
    H ^ 12 / (A * p)
  have hb := fixedH_annular_bounds (q := q) hτ hτT htlow htT
  dsimp only at hb
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one (by simpa only [H] using hb.1)
  have hp : 0 < p := by
    dsimp only [p]
    exact Real.rpow_pos_of_pos (by exact_mod_cast NeZero.pos q) _
  have hx : 0 < x := by dsimp only [x]; positivity
  have hlower := norm_LFunction_ge_on_quadraticConditionalAnnulus
    Z hZ hzeta χ hquad hχ hA hAhalf hAsmall hη hτ hτT hβ hβone htlow htT
  dsimp only at hlower
  have hH1 : 1 ≤ H := by simpa only [H] using hb.1
  have hq1 : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hp1 : p ≤ 1 := by
    dsimp only [p]
    simpa using Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : -2 * η ≤ 0)
  have hlogH : 1 + Real.log (dirichletLConductorHeightCutoff q t) ≤ H := by
    simpa only [H] using hb.2.2.2
  obtain ⟨hxhalf, hxlog⟩ := powerWidth_le_half_and_inv_log
    hA hAhalf hp.le hp1 hH1 (log_conductorHeightCutoff_pos χ hχ t)
      (by linarith only [hlogH])
  have hβleft : 1 - x ≤ β := by
    simpa only [dirichletLQuadraticConditionalFixedLeft, x, p, H] using hβ
  have hβhalf : 1 / 2 ≤ β := by linarith only [hβleft, hxhalf]
  have hnear : 1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ β := by
    linarith only [hβleft, hxlog]
  have hderiv := norm_deriv_LFunction_le_one_add_log_sq
    χ hχ hβhalf (hβone.trans (by norm_num)) hnear
  rw [norm_div]
  calc
    ‖deriv χ.LFunction (β + I * t)‖ / ‖χ.LFunction (β + I * t)‖
        ≤ (64 * H ^ 2) / ‖χ.LFunction (β + I * t)‖ := by
          exact div_le_div_of_nonneg_right (hderiv.trans (by gcongr)) (norm_nonneg _)
    _ ≤ (64 * H ^ 2) / (64 * H ^ 2 * x) := by
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hlower
    _ = H ^ 12 / (A * p) := by
      dsimp only [x, p]
      field_simp [ne_of_gt hH, ne_of_gt hA, ne_of_gt hp]

/-- On `[1 - w, 1] × [-T, T]`, `‖L'/L(β + it, χ)‖` is at most the sum of the bounds for the
central band and for `τ ≤ |t| ≤ T`. -/
theorem norm_logDerivative_le_on_quadraticConditionalWholeBand
    (Z : ℝ) (hZ : 0 < Z)
    (hzeta : ∀ (x u : ℝ), 0 < x → x ≤ 1 → u ≠ 0 →
      ‖riemannZeta (1 + x + I * u)‖ ≤
        Z * (1 + Real.log (|u| + 2) + 1 / |u|))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1)
    {A c η T β t : ℝ}
    (hA : 0 < A) (hAc : A ≤ c / 256) (hAhalf : A ≤ 1 / 2)
    (hAsmall : A ≤ 1 / (16 * Z * 192 ^ 4))
    (hc : 0 < c) (hη : 0 < η) (hT : 0 < T)
    (hSiegel : c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re)
    (hβ : 1 - dirichletLQuadraticConditionalCrossZeroWidth A c η q T ≤ β)
    (hβone : β ≤ 1) (htT : |t| ≤ T) :
    ‖deriv χ.LFunction (β + I * t) / χ.LFunction (β + I * t)‖ ≤
      (128 * (dirichletLQuadraticConditionalCentralH q T) ^ 2) /
          (c * (q : ℝ) ^ (-η)) +
        (dirichletLQuadraticConditionalFixedH q
          (dirichletLQuadraticConditionalCentralHeight c η q T) T) ^ 12 /
          (A * (q : ℝ) ^ (-2 * η)) := by
  let τ := dirichletLQuadraticConditionalCentralHeight c η q T
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hcut : (1 : ℝ) ≤ dirichletLNonquadraticConductorLogCutoff q T := by
    exact_mod_cast (show 1 ≤ dirichletLNonquadraticConductorLogCutoff q T by
      unfold dirichletLNonquadraticConductorLogCutoff
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne q) (by
        unfold dirichletLNonquadraticConductorLogHeightBlock
        omega)))
  have hH₀ : 0 < dirichletLQuadraticConditionalCentralH q T := by
    dsimp only [dirichletLQuadraticConditionalCentralH]
    linarith [Real.log_nonneg hcut]
  have hτ : 0 < τ := by
    dsimp only [τ, dirichletLQuadraticConditionalCentralHeight]
    exact lt_min hT (by positivity)
  have hτT : τ ≤ T := by
    dsimp only [τ, dirichletLQuadraticConditionalCentralHeight]
    exact min_le_left _ _
  have hcentralNonneg : 0 ≤
      (128 * (dirichletLQuadraticConditionalCentralH q T) ^ 2) /
        (c * (q : ℝ) ^ (-η)) := by positivity
  have hannularNonneg : 0 ≤
      (dirichletLQuadraticConditionalFixedH q τ T) ^ 12 /
        (A * (q : ℝ) ^ (-2 * η)) := by positivity
  by_cases htcentral : |t| ≤ τ
  · have hcbd := norm_logDerivative_le_on_quadraticConditionalCentralBand
      χ hχ hA hAc hAhalf hc hη hT hSiegel hβ hβone
        (by simpa only [τ] using htcentral)
    exact hcbd.trans (le_add_of_nonneg_right (by simpa only [τ] using hannularNonneg))
  · have htlow : τ ≤ |t| := le_of_not_ge htcentral
    have habd := norm_logDerivative_le_on_quadraticConditionalAnnulus
      Z hZ hzeta χ hquad hχ hA hAhalf hAsmall hη hτ hτT
        (by simpa only [dirichletLQuadraticConditionalFixedLeft,
          dirichletLQuadraticConditionalCrossZeroWidth, τ] using hβ)
        hβone htlow htT
    exact habd.trans (by
      simpa only [τ] using le_add_of_nonneg_left hcentralNonneg)

end BombieriVinogradov

end
