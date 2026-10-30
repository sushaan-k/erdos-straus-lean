import ErdosStraus.BombieriVinogradov.Siegel.Fourfold

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

/-!
# Siegel's lower bound for `L(1, χ)`

For every `η > 0` there is `c > 0` such that `c q^{-η} ≤ L(1, χ)` for every primitive
quadratic character `χ ≠ 1` of conductor `q`. If some primitive quadratic `ψ` mod `r` has a
real zero `β` close to `1`, comparing each `χ` with this fixed `ψ` at level `q r` gives the
bound. Otherwise a small value of `L(1, χ)` would force such a zero for `χ` itself.
The constant `c` is not effective.
-/

section

/-! ## Comparison with a fixed real zero -/

open Complex Finset Filter
open scoped Topology

namespace DirichletCharacter

/-- `L(1, χ)` is the sum of the convergent series `∑ χ(n) / n`, so two characters of
possibly different levels that agree on `ℕ` have the same value at `1`. -/
theorem LFunction_one_eq_of_nat_values_eq {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (heq : ∀ n : ℕ, χ n = ψ n) :
    χ.LFunction 1 = ψ.LFunction 1 := by
  have hχlim := BombieriVinogradov.LValueSeries.tendsto_sum_range_orderedValueSeries
    χ hχ 1 (by norm_num)
  have hψlim := BombieriVinogradov.LValueSeries.tendsto_sum_range_orderedValueSeries
    ψ hψ 1 (by norm_num)
  rw [BombieriVinogradov.LValueSeries.orderedValueSeries_eq_LFunction_of_re_pos] at hχlim hψlim
  simp only [heq] at hχlim
  exact tendsto_nhds_unique hχlim hψlim

end DirichletCharacter

namespace BombieriVinogradov.Siegel

open DirichletCharacter

/-- Let `χ` mod `q` and `ψ` mod `Q` be quadratic characters `≠ 1` with `q ∣ Q` and `χ ≠ ψ`
at level `Q`. If `L(β, ψ) = 0` with `7/8 ≤ β < 1`, then for `a > 0`
`L(1, χ) ≥ (1 - β) / (2 · 5000^{8(1-β)} (3 + 1/a)³) · Q^{-(24(1-β) + 3a)}`.
This compares the lower bound `(1 - β) / (2 ((5000 Q³)^8)^{1-β})` for
`L(1, χ) L(1, ψ) L(1, χψ)` with the upper bound `L(1, χ) (3 + 1/a)³ Q^{3a}`. -/
theorem original_value_lower_bound_of_common_level_real_zero
    {q Q : ℕ} [NeZero q] [NeZero Q] (hq : q ∣ Q)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ Q)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχquad : χ ^ 2 = 1) (hψquad : ψ ^ 2 = 1)
    (hne : changeLevel hq χ ≠ ψ) {β a : ℝ}
    (hβ : 7 / 8 ≤ β) (hβ1 : β < 1) (hzero : ψ.LFunction (β : ℂ) = 0)
    (ha : 0 < a) :
    ((1 - β) / (2 * (5000 : ℝ) ^ (8 * (1 - β)) * (3 + 1 / a) ^ 3)) *
        (Q : ℝ) ^ (-(24 * (1 - β) + 3 * a)) ≤ (χ.LFunction 1).re := by
  have hχQ : changeLevel hq χ ≠ 1 :=
    fun h => hχ ((changeLevel_eq_one_iff hq).mp h)
  have hχQquad := sq_changeLevel_eq_one hq hχquad
  have hprod := mul_ne_one_of_quadratic_ne hψquad hne
  have hlower := twoCharacterResidue_re_lower_bound_of_real_zero
    (changeLevel hq χ) ψ hχQ hψ hχQquad hψquad hne hβ hβ1
    (Or.inr (Or.inl hzero))
  have hupper := twoCharacterResidue_re_le_original_value_mul_subpower
    hq χ ψ hχ hχquad hψ hprod ha
  have hQ : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hendpoint :
      ((5000 * (Q : ℝ) ^ 3) ^ 8) ^ (1 - β) =
        (5000 : ℝ) ^ (8 * (1 - β)) * (Q : ℝ) ^ (24 * (1 - β)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      Real.mul_rpow (by norm_num) (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul hQ.le]
    congr 2
    ring
  have hpow :
      (Q : ℝ) ^ (3 * a) * (Q : ℝ) ^ (24 * (1 - β)) =
        (Q : ℝ) ^ (24 * (1 - β) + 3 * a) := by
    rw [← Real.rpow_add hQ, add_comm]
  have h := (div_le_iff₀ (by positivity :
      0 < 2 * ((5000 * (Q : ℝ) ^ 3) ^ 8) ^ (1 - β))).mp
    (hlower.trans hupper)
  rw [hendpoint] at h
  have h' :
      1 - β ≤ (χ.LFunction 1).re *
        (2 * (5000 : ℝ) ^ (8 * (1 - β)) * (3 + 1 / a) ^ 3) *
        (Q : ℝ) ^ (24 * (1 - β) + 3 * a) := by
    calc
      _ ≤ _ := h
      _ = _ := by rw [← hpow]; ring
  rw [Real.rpow_neg hQ.le, ← div_eq_mul_inv, div_div]
  apply (div_le_iff₀ (by positivity)).mpr
  simpa only [mul_assoc] using h'

/-- Fix a primitive quadratic `ψ ≠ 1` mod `r` with `L(β, ψ) = 0`, `7/8 ≤ β < 1`, and let
`a > 0`. There is `c > 0` with `c q^{-(24(1-β) + 3a)} ≤ L(1, χ)` for every primitive
quadratic `χ ≠ 1` mod `q` whose values differ from those of `ψ`. The proof works at
level `q r`, and the factor `r^{-(24(1-β) + 3a)}` goes into `c`. -/
theorem exists_fixed_witness_distinct_lower_bound
    {r : ℕ} [NeZero r] (ψ : DirichletCharacter ℂ r)
    (hψprim : ψ.IsPrimitive) (hψ : ψ ≠ 1) (hψquad : ψ ^ 2 = 1)
    {β a : ℝ} (hβ : 7 / 8 ≤ β) (hβ1 : β < 1)
    (hzero : ψ.LFunction (β : ℂ) = 0) (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 → (∃ n : ℕ, χ n ≠ ψ n) →
        c * (q : ℝ) ^ (-(24 * (1 - β) + 3 * a)) ≤ (χ.LFunction 1).re := by
  let e : ℝ := 24 * (1 - β) + 3 * a
  let k : ℝ := (1 - β) /
    (2 * (5000 : ℝ) ^ (8 * (1 - β)) * (3 + 1 / a) ^ 3)
  have hk : 0 < k := by dsimp [k]; positivity
  have hr : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  refine ⟨k * (r : ℝ) ^ (-e), mul_pos hk (Real.rpow_pos_of_pos hr _), ?_⟩
  intro q _ χ hχprim hχ hχquad hne
  let hqQ : q ∣ q * r := dvd_mul_right q r
  let hrQ : r ∣ q * r := dvd_mul_left r q
  have hψQ : changeLevel hrQ ψ ≠ 1 :=
    fun h => hψ ((changeLevel_eq_one_iff hrQ).mp h)
  have hneQ := changeLevel_ne_of_primitive_values hqQ hrQ χ ψ hχprim hψprim hne
  have hzeroQ := (LFunction_changeLevel_real_eq_zero_iff hrQ ψ
    (by linarith : 0 < β) (Or.inl hψ)).mpr hzero
  have h := original_value_lower_bound_of_common_level_real_zero hqQ χ
    (changeLevel hrQ ψ) hχ hψQ hχquad (sq_changeLevel_eq_one hrQ hψquad)
    hneQ hβ hβ1 hzeroQ ha
  change k * ((q * r : ℕ) : ℝ) ^ (-e) ≤ _ at h
  rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg q) hr.le] at h
  calc
    _ = _ := by ring
    _ ≤ _ := h

/-- The previous bound for all primitive quadratic `χ ≠ 1`. If `χ` and `ψ` agree on `ℕ`, then
`L(1, χ) = L(1, ψ) > 0`, which is handled by taking `c ≤ L(1, ψ)`. -/
theorem exists_fixed_witness_lower_bound
    {r : ℕ} [NeZero r] (ψ : DirichletCharacter ℂ r)
    (hψprim : ψ.IsPrimitive) (hψ : ψ ≠ 1) (hψquad : ψ ^ 2 = 1)
    {β a : ℝ} (hβ : 7 / 8 ≤ β) (hβ1 : β < 1)
    (hzero : ψ.LFunction (β : ℂ) = 0) (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 →
        c * (q : ℝ) ^ (-(24 * (1 - β) + 3 * a)) ≤ (χ.LFunction 1).re := by
  obtain ⟨c, hc, hcomp⟩ := exists_fixed_witness_distinct_lower_bound
    ψ hψprim hψ hψquad hβ hβ1 hzero ha
  have hL := LFunction_apply_one_re_pos_of_sq_eq_one hψquad hψ
  refine ⟨min c (ψ.LFunction 1).re, lt_min hc hL, ?_⟩
  intro q _ χ hχprim hχ hχquad
  by_cases hne : ∃ n : ℕ, χ n ≠ ψ n
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (Real.rpow_nonneg (Nat.cast_nonneg q) _)).trans
        (hcomp q χ hχprim hχ hχquad hne)
  · have heq : ∀ n : ℕ, χ n = ψ n := by simpa only [not_exists, not_not] using hne
    rw [LFunction_one_eq_of_nat_values_eq χ ψ hχ hψ heq]
    have hp : (q : ℝ) ^ (-(24 * (1 - β) + 3 * a)) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
      · linarith
    calc
      _ ≤ (ψ.LFunction 1).re * (q : ℝ) ^ (-(24 * (1 - β) + 3 * a)) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg q) _)
      _ ≤ (ψ.LFunction 1).re := mul_le_of_le_one_right hL.le hp

end BombieriVinogradov.Siegel

end

section

/-! ## Siegel's theorem -/

open Complex

namespace BombieriVinogradov.Siegel

open DirichletCharacter

/-- Siegel's theorem: for every `η > 0` there is `c > 0` with `c q^{-η} ≤ L(1, χ)` for every
primitive quadratic character `χ ≠ 1` of conductor `q`. The proof splits on whether some
primitive quadratic character has a real zero in `(1 - ε, 1)`, where `ε ≤ η / 100`. -/
theorem exists_uniform_quadratic_LFunction_one_lower_bound
    (η : ℝ) (hη : 0 < η) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 →
        c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re := by
  obtain ⟨ε₀, hε₀, _hε₀4, hsmall⟩ :=
    exists_uniform_small_value_real_zero_neighborhood
  let ε : ℝ := min ε₀ (min (1 / 8) (η / 100))
  have hε : 0 < ε := lt_min hε₀ (lt_min (by norm_num) (by positivity))
  have hε₀bound : ε ≤ ε₀ := min_le_left _ _
  have hε8 : ε ≤ 1 / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hεη : ε ≤ η / 100 := (min_le_right _ _).trans (min_le_right _ _)
  by_cases hw : ∃ (r : ℕ) (_ : NeZero r) (ψ : DirichletCharacter ℂ r) (β : ℝ),
      ψ.IsPrimitive ∧ ψ ≠ 1 ∧ ψ ^ 2 = 1 ∧
        β ∈ Set.Ioo (1 - ε) 1 ∧ ψ.LFunction (β : ℂ) = 0
  · obtain ⟨r, hr, ψ, β, hψprim, hψ, hψquad, hβ, hzero⟩ := hw
    obtain ⟨c, hc, hcomp⟩ := exists_fixed_witness_lower_bound
      ψ hψprim hψ hψquad (by linarith [hβ.1] : 7 / 8 ≤ β)
      hβ.2 hzero (by positivity : 0 < η / 6)
    refine ⟨c, hc, ?_⟩
    intro q _ χ hχprim hχ hχquad
    have hq : (1 : ℝ) ≤ q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hp : (q : ℝ) ^ (-η) ≤
        (q : ℝ) ^ (-(24 * (1 - β) + 3 * (η / 6))) :=
      Real.rpow_le_rpow_of_exponent_le hq (by linarith [hβ.1])
    exact (mul_le_mul_of_nonneg_left hp hc.le).trans (hcomp q χ hχprim hχ hχquad)
  · let c : ℝ := ε / (4 * (648 : ℝ) ^ (4 * ε))
    have hc : 0 < c := by dsimp [c]; positivity
    refine ⟨c, hc, ?_⟩
    intro q hqinst χ hχprim hχ hχquad
    have hq : (1 : ℝ) ≤ q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
    have hlarge : ε / (4 * (648 * (q : ℝ)) ^ (4 * ε)) <
        (χ.LFunction 1).re := by
      by_contra h
      obtain ⟨β, hβ, hzero⟩ := hsmall ε hε hε₀bound q χ hχprim hχ hχquad (not_lt.mp h)
      exact hw ⟨q, hqinst, χ, β, hχprim, hχ, hχquad, hβ, hzero⟩
    have hthreshold :
        c * (q : ℝ) ^ (-(4 * ε)) = ε / (4 * (648 * (q : ℝ)) ^ (4 * ε)) := by
      dsimp [c]
      simp only [Real.rpow_neg hq0.le,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 648) hq0.le,
        div_eq_mul_inv, mul_inv_rev]
      ring
    calc
      c * (q : ℝ) ^ (-η) ≤ c * (q : ℝ) ^ (-(4 * ε)) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hq (by linarith)) hc.le
      _ = _ := hthreshold
      _ ≤ _ := hlarge.le

end BombieriVinogradov.Siegel

end
