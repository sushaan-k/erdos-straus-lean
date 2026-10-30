import ErdosStraus.BombieriVinogradov.SiegelWalfisz.Quadratic
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import ErdosStraus.BombieriVinogradov.Siegel.LowerBound

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

/-!
# Proof of the Bombieri–Vinogradov theorem

For every `A > 0` there are `B ≥ 0` and `C > 0` such that for all large `N`,
`∑_{q ≤ N^{1/2} / (log N)^B} max_{y ≤ N} max_{(l,q)=1} |E(y; q, l)| ≤ C N / (log N)^A`,
where `E(y; q, l) = π(y; q, l) - li(y) / φ(q)`. Siegel's lower bound for `L(1, χ)` gives the Siegel–Walfisz bound for primitive characters
of conductor at most a power of `log N`, and this bound implies the theorem. The
Siegel–Walfisz argument uses a smooth weight `ν ≥ 0` supported in `[1/2, 2]` with
`∫_0^∞ ν(x) dx / x = 1`, built here from a bump function.
-/

section

/-! ## A smooth weight on `[1/2, 2]` -/

open Set Function Filter Complex Real MeasureTheory Metric

namespace BombieriVinogradov

noncomputable section

/-- A smooth bump `b` equal to `1` on `[1, 3/2]` and with support `(1/2, 2)`. -/
def smoothingBump : ContDiffBump (5 / 4 : ℝ) :=
  ⟨1 / 4, 3 / 4, by norm_num, by norm_num⟩

/-- The function `b(x) / max(x, 1/2)`. It is continuous on `ℝ` and equals `b(x) / x` on the
support of `b`. -/
def smoothingBumpWeight (x : ℝ) : ℝ :=
  smoothingBump x / max x (1 / 2)

/-- The normalizing constant `∫_0^∞ b(x) dx / x`. -/
def smoothingBumpMass : ℝ :=
  ∫ x : ℝ, smoothingBumpWeight x

theorem smoothingBumpWeight_continuous : Continuous smoothingBumpWeight := by
  apply smoothingBump.continuous.div
  · fun_prop
  · intro x
    have h : 0 < max x (1 / 2) :=
      lt_of_lt_of_le (by norm_num) (le_max_right x (1 / 2))
    exact h.ne'

theorem smoothingBumpWeight_hasCompactSupport :
    HasCompactSupport smoothingBumpWeight := by
  exact smoothingBump.hasCompactSupport.mul_right

theorem smoothingBumpWeight_nonneg : 0 ≤ smoothingBumpWeight := by
  intro x
  exact div_nonneg smoothingBump.nonneg (by positivity)

private lemma smoothingBumpWeight_at_center :
    smoothingBumpWeight (5 / 4) ≠ 0 := by
  have hone : smoothingBump (5 / 4) = 1 :=
    smoothingBump.one_of_mem_closedBall
      (mem_closedBall_self smoothingBump.rIn_pos.le)
  rw [smoothingBumpWeight, hone]
  norm_num

theorem smoothingBumpMass_pos : 0 < smoothingBumpMass := by
  exact smoothingBumpWeight_continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    smoothingBumpWeight_hasCompactSupport smoothingBumpWeight_nonneg
    smoothingBumpWeight_at_center

/-- The weight `ν(x) = b(x) / ∫_0^∞ b(t) dt / t`, so that `∫_0^∞ ν(x) dx / x = 1`. -/
def smoothingWeight (x : ℝ) : ℝ :=
  smoothingBump x / smoothingBumpMass

theorem smoothingWeight_contDiff :
    ContDiff ℝ 1 smoothingWeight := by
  exact smoothingBump.contDiff.div_const smoothingBumpMass

theorem smoothingWeight_nonneg_all (x : ℝ) :
    0 ≤ smoothingWeight x := by
  exact div_nonneg smoothingBump.nonneg
    smoothingBumpMass_pos.le

/-- Nonnegativity on `(0, ∞)`, the form of the hypothesis in the Siegel–Walfisz bound. -/
theorem smoothingWeight_nonneg (x : ℝ) (_hx : 0 < x) :
    0 ≤ smoothingWeight x :=
  smoothingWeight_nonneg_all x

private theorem smoothingBump_support :
    support smoothingBump ⊆ Icc (1 / 2) 2 := by
  rw [smoothingBump.support_eq, Real.ball_eq_Ioo]
  intro x hx
  norm_num [smoothingBump] at hx ⊢
  exact ⟨hx.1.le, hx.2.le⟩

theorem smoothingWeight_support :
    support smoothingWeight ⊆ Icc (1 / 2) 2 := by
  intro x hx
  apply smoothingBump_support
  exact fun hzero => hx (by simp [smoothingWeight, hzero])

private lemma smoothingBumpWeight_eq_div (x : ℝ) (_hx : x ∈ Ioi (0 : ℝ)) :
    smoothingBumpWeight x = smoothingBump x / x := by
  by_cases hs : x ∈ support smoothingBump
  · rw [smoothingBumpWeight,
      max_eq_left (smoothingBump_support hs).1]
  · simp [smoothingBumpWeight, notMem_support.mp hs]

private lemma smoothingBumpWeight_zero_of_nonpos {x : ℝ}
    (hx : x ∉ Ioi (0 : ℝ)) : smoothingBumpWeight x = 0 := by
  have hout : x ∉ support smoothingBump := by
    intro hs
    apply hx
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (smoothingBump_support hs).1
  simp [smoothingBumpWeight, notMem_support.mp hout]

theorem smoothingWeight_mass_one :
    ∫ x in Ioi (0 : ℝ), smoothingWeight x / x = 1 := by
  calc
    ∫ x in Ioi (0 : ℝ), smoothingWeight x / x =
        ∫ x in Ioi (0 : ℝ),
          smoothingBumpWeight x / smoothingBumpMass := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          change smoothingWeight x / x =
            smoothingBumpWeight x / smoothingBumpMass
          rw [smoothingBumpWeight_eq_div x hx, smoothingWeight,
            div_right_comm]
    _ = ∫ x : ℝ,
          smoothingBumpWeight x / smoothingBumpMass := by
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro x hx
          simp [smoothingBumpWeight_zero_of_nonpos hx]
    _ = smoothingBumpMass / smoothingBumpMass :=
      integral_div _ _
    _ = 1 := div_self smoothingBumpMass_pos.ne'

end

end BombieriVinogradov

end

/-! ## From Siegel's bound to the theorem -/

namespace BombieriVinogradov

/-- Siegel's theorem: for every `η > 0` there is `c > 0` with `Re L(1, χ) ≥ c q^{-η}` for every
primitive quadratic character `χ ≠ 1` mod `q`. -/
theorem rawLandauSiegelLowerBound : RawLandauSiegelLowerBound := by
  intro η hη
  obtain ⟨c, hc, hbound⟩ :=
    Siegel.exists_uniform_quadratic_LFunction_one_lower_bound η hη
  exact ⟨c, hc, fun q _ χ hprim hquad hχ => hbound q χ hprim hχ hquad⟩

/-- The Siegel–Walfisz bound: for all `C` and `D` there is `K` such that for large `N`,
`max_{y ≤ N} |∑_{n ≤ y} Λ(n) ψ(n)| ≤ K N / (log N)^D` for every nonprincipal primitive
character `ψ` of conductor `2 ≤ d ≤ (log N)^C`. -/
theorem primitiveSiegelWalfisz :
    PrimitiveSiegelWalfisz :=
  primitiveSiegelWalfisz_of_siegel
    rawLandauSiegelLowerBound smoothingWeight_contDiff
    smoothingWeight_nonneg smoothingWeight_support
    smoothingWeight_mass_one

/-- **The Bombieri–Vinogradov theorem.** For every `A > 0` there are `B ≥ 0` and `C > 0` such
that for all large `N`,
`∑_{1 ≤ q ≤ N^{1/2} / (log N)^B} max_{y ≤ N} max_{(l,q)=1} |E(y; q, l)| ≤ C N / (log N)^A`. -/
theorem standard_form :
    BombieriVinogradov.StandardForm :=
  standard_form_of_nonprincipalPrimitivePsi
    primitiveSiegelWalfisz

end BombieriVinogradov
