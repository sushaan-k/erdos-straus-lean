import ErdosStraus.BombieriVinogradov.DirichletL.ConditionalSeries
import ErdosStraus.BombieriVinogradov.LargeSieve.PrimitiveCharacters

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

/-!
# Quadratic Dirichlet L-functions at `s = 1`

Let `χ` be a nonprincipal Dirichlet character modulo `q`. If `χ` is quadratic, then
`L(conj s, χ) = conj L(s, χ)` for `re s > 0`, so `L(β, χ)` is real for real `β > 0`.
For any nonprincipal `χ` and `m ≥ 1`, `‖L(1, χ) - ∑_{n < m} χ(n)/n‖ ≤ 2q/m`.
Finally, for quadratic `χ`, `L(1, χ)` is real and positive.
-/

section

/-! ## Conjugation symmetry -/

open Complex Finset Filter Set
open scoped Topology

namespace DirichletCharacter

open BombieriVinogradov.AbelWeight BombieriVinogradov.LValueSeries

local notation "conj" => starRingEnd ℂ

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
/-- Complex conjugation fixes a quadratic Dirichlet character. -/
lemma star_eq_self_of_sq_eq_one (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) :
    star χ = χ := by
  rw [MulChar.star_eq_inv, (MulChar.isQuadratic_iff_sq_eq_one.mpr hquad).inv]

omit [NeZero q] in
private lemma conj_character_apply_of_sq_eq_one
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) (k : ℕ) :
    conj (χ k) = χ k := by
  have h := congrArg (fun ψ : DirichletCharacter ℂ q => ψ k)
    (star_eq_self_of_sq_eq_one χ hquad)
  simpa using h

private lemma conj_cpowWeight (s : ℂ) (k : ℕ) :
    conj (cpowWeight s k) = cpowWeight (conj s) k := by
  unfold cpowWeight
  have harg : ((k : ℂ)).arg ≠ Real.pi := by
    change (((k : ℝ) : ℂ)).arg ≠ Real.pi
    rw [Complex.arg_ofReal_of_nonneg (by positivity)]
    exact ne_of_lt Real.pi_pos
  simpa using (Complex.cpow_conj (k : ℂ) (-s) harg).symm

omit [NeZero q] in
/-- For quadratic `χ`, conjugating the partial sum `∑_{k < n} χ(k) k^{-s}` replaces `s` by
`conj s`. -/
lemma conj_sum_range_cpowWeight_character_of_sq_eq_one
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) (s : ℂ) (n : ℕ) :
    conj (∑ k ∈ range n, cpowWeight s k * χ k) =
      ∑ k ∈ range n, cpowWeight (conj s) k * χ k := by
  rw [map_sum]
  apply sum_congr rfl
  intro k hk
  rw [map_mul, conj_cpowWeight, conj_character_apply_of_sq_eq_one χ hquad k]

/-- For a nonprincipal quadratic character `χ` and `re s > 0`,
`L(conj s, χ) = conj L(s, χ)`. Both sides are limits of the partial sums
`∑_{k < n} χ(k) k^{-s}`, which conjugate term by term. -/
theorem LFunction_conj_eq_conj_LFunction_of_sq_eq_one
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hquad : χ ^ 2 = 1)
    (s : ℂ) (hs : 0 < s.re) :
    χ.LFunction (conj s) = conj (χ.LFunction s) := by
  have hsc : 0 < (conj s).re := by simpa using hs
  have hleft := tendsto_sum_range_orderedValueSeries χ hχ (conj s) hsc
  have hright0 := tendsto_sum_range_orderedValueSeries χ hχ s hs
  have hright :
      Tendsto (fun n : ℕ => conj (∑ k ∈ range n, cpowWeight s k * χ k)) atTop
        (𝓝 (conj (orderedValueSeries χ hχ s hs))) :=
    (Complex.continuous_conj.tendsto (orderedValueSeries χ hχ s hs)).comp hright0
  have hright' :
      Tendsto (fun n : ℕ => ∑ k ∈ range n, cpowWeight (conj s) k * χ k) atTop
        (𝓝 (conj (orderedValueSeries χ hχ s hs))) := by
    refine (tendsto_congr' (Eventually.of_forall fun n => ?_)).mp hright
    exact conj_sum_range_cpowWeight_character_of_sq_eq_one χ hquad s n
  have hordered :
      orderedValueSeries χ hχ (conj s) hsc =
        conj (orderedValueSeries χ hχ s hs) :=
    tendsto_nhds_unique hleft hright'
  rw [orderedValueSeries_eq_LFunction_of_re_pos χ hχ (conj s) hsc,
    orderedValueSeries_eq_LFunction_of_re_pos χ hχ s hs] at hordered
  exact hordered

/-- For a nonprincipal quadratic character `χ`, `L(β, χ)` is real for every real
`β > 0`. -/
theorem LFunction_ofReal_im_eq_zero_of_sq_eq_one
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hquad : χ ^ 2 = 1)
    (β : ℝ) (hβ : 0 < β) :
    (χ.LFunction (β : ℂ)).im = 0 := by
  have hs : 0 < ((β : ℂ).re) := by simpa using hβ
  have h := LFunction_conj_eq_conj_LFunction_of_sq_eq_one χ hχ hquad (β : ℂ) hs
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

end DirichletCharacter

end

section

/-! ## Partial sums at `s = 1` -/

open Complex Finset

namespace DirichletCharacter

open BombieriVinogradov.AbelWeight BombieriVinogradov.LValueSeries
variable {q : ℕ} [NeZero q]

/-- The real part of the partial sum `∑_{n < m} χ(n)/n`. -/
noncomputable def quadraticHarmonicTruncation
    (χ : DirichletCharacter ℂ q) (m : ℕ) : ℝ :=
  (∑ n ∈ range m, cpowWeight (1 : ℂ) n * χ n).re

/-- For a nonprincipal character `χ` modulo `q` and `m ≥ 1`,
`‖L(1, χ) - ∑_{n < m} χ(n)/n‖ ≤ 2q/m`. -/
theorem norm_LFunction_one_sub_harmonic_sum_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {m : ℕ} (hm : 1 ≤ m) :
    ‖χ.LFunction 1 - ∑ n ∈ range m, cpowWeight (1 : ℂ) n * χ n‖ ≤
      2 * (q : ℝ) / (m : ℝ) := by
  have htail := norm_orderedValueSeries_sub_sum_range_le
    χ hχ (1 : ℂ) (by norm_num) hm
  rw [orderedValueSeries_eq_LFunction_of_re_pos χ hχ (1 : ℂ) (by norm_num)] at htail
  calc
    _ ≤ (q : ℝ) * ((m : ℝ)⁻¹ + (m : ℝ)⁻¹) := by
      simpa [Real.rpow_neg_one] using htail
    _ = 2 * (q : ℝ) / (m : ℝ) := by
      rw [div_eq_mul_inv]
      ring

/-- For a nonprincipal character `χ` modulo `q` and `m ≥ 1`,
`|Re L(1, χ) - Re ∑_{n < m} χ(n)/n| ≤ 2q/m`. -/
theorem abs_LFunction_one_re_sub_quadraticHarmonicTruncation_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {m : ℕ} (hm : 1 ≤ m) :
    |(χ.LFunction 1).re - quadraticHarmonicTruncation χ m| ≤
      2 * (q : ℝ) / (m : ℝ) := by
  have hnorm := norm_LFunction_one_sub_harmonic_sum_le χ hχ hm
  have hre := Complex.abs_re_le_norm
    (χ.LFunction 1 - ∑ n ∈ range m, cpowWeight (1 : ℂ) n * χ n)
  have hre' :
      |(χ.LFunction 1).re - quadraticHarmonicTruncation χ m| ≤
        ‖χ.LFunction 1 - ∑ n ∈ range m, cpowWeight (1 : ℂ) n * χ n‖ := by
    simpa [quadraticHarmonicTruncation] using hre
  exact hre'.trans hnorm

end DirichletCharacter

end

section

/-! ## Positivity at `s = 1` -/

open Complex Filter Topology
open ArithmeticFunction hiding log
open scoped ComplexOrder LSeries.notation

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- For `re s > 1`, `ζ(s) L(s, χ)` is the L-series of the Dirichlet convolution
`1 * χ`. -/
lemma riemannZeta_mul_LFunction_eq_LSeries_zetaMul
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * χ.LFunction s = LSeries χ.zetaMul s := by
  rw [zetaMul, ← coe_mul, LSeries_convolution']
  · rw [χ.LFunction_eq_LSeries hs]
    congr 1
    · simp_rw [← LSeries_zeta_eq_riemannZeta hs, ← natCoe_apply]
    · exact LSeries_congr χ.apply_eq_toArithmeticFunction_apply s
  · exact LSeriesSummable_zeta_iff.mpr hs
  · exact (LSeriesSummable_congr _ fun h ↦ (χ.apply_eq_toArithmeticFunction_apply h).symm).mpr <|
      ZMod.LSeriesSummable_of_one_lt_re χ hs

/-- For a nonprincipal quadratic character `χ`, `L(1, χ) ≥ 0` in the complex
order, so `L(1, χ)` is real and nonnegative. It is the limit as `x → 1⁺` of
`(x - 1) ζ(x) L(x, χ)`, which is positive because `ζ(s) L(s, χ)` has nonnegative
Dirichlet coefficients. -/
theorem LFunction_apply_one_nonneg_of_sq_eq_one
    {χ : DirichletCharacter ℂ N} (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    0 ≤ χ.LFunction 1 := by
  have habs : LSeries.abscissaOfAbsConv χ.zetaMul ≤ 1 :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      fun _ hy ↦ χ.LSeriesSummable_zetaMul hy
  have hseries_pos {x : ℝ} (hx : 1 < x) : 0 < LSeries χ.zetaMul x := by
    apply LSeries.positive (zetaMul_nonneg hquad)
      (χ.isMultiplicative_zetaMul.map_one ▸ zero_lt_one)
    exact habs.trans_lt (by exact_mod_cast hx)
  have hprod_pos {x : ℝ} (hx : 1 < x) :
      0 < ((x : ℂ) - 1) * riemannZeta x * χ.LFunction x := by
    rw [mul_assoc, riemannZeta_mul_LFunction_eq_LSeries_zetaMul χ (by simpa using hx)]
    exact mul_pos (by exact_mod_cast sub_pos.mpr hx) (hseries_pos hx)
  have hcoe_nhds : Tendsto (fun x : ℝ ↦ (x : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hcoe_punctured :
      Tendsto (fun x : ℝ ↦ (x : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hcoe_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxne : (x : ℂ) ≠ 1 := by
      exact_mod_cast ne_of_gt hx
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxne
  have hlim :
      Tendsto (fun x : ℝ ↦ ((x : ℂ) - 1) * riemannZeta x * χ.LFunction x)
        (𝓝[>] (1 : ℝ)) (𝓝 (χ.LFunction 1)) := by
    simpa only [Function.comp_apply, one_mul] using
      (riemannZeta_residue_one.comp hcoe_punctured).mul
        ((χ.differentiableAt_LFunction 1 (.inr hχ)).continuousAt.tendsto.comp hcoe_nhds)
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (hprod_pos hx).le

/-- For a nonprincipal quadratic character `χ`, `L(1, χ)` is real. -/
theorem LFunction_apply_one_im_eq_zero_of_sq_eq_one
    {χ : DirichletCharacter ℂ N} (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    (χ.LFunction 1).im = 0 :=
  (Complex.nonneg_iff.mp (LFunction_apply_one_nonneg_of_sq_eq_one hquad hχ)).2.symm

/-- For a nonprincipal quadratic character `χ`, `Re L(1, χ) > 0`. This combines
`L(1, χ) ≥ 0` with `L(1, χ) ≠ 0`. -/
theorem LFunction_apply_one_re_pos_of_sq_eq_one
    {χ : DirichletCharacter ℂ N} (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    0 < (χ.LFunction 1).re := by
  have hnonneg := Complex.nonneg_iff.mp
    (LFunction_apply_one_nonneg_of_sq_eq_one hquad hχ)
  have him : (χ.LFunction 1).im = 0 := hnonneg.2.symm
  have hre_ne : (χ.LFunction 1).re ≠ 0 := by
    intro hre
    apply χ.LFunction_apply_one_ne_zero hχ
    apply Complex.ext
    · simpa only [zero_re] using hre
    · simpa only [zero_im] using him
  exact lt_of_le_of_ne hnonneg.1 (Ne.symm hre_ne)

end DirichletCharacter

end
