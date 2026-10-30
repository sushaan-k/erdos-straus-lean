import ErdosStraus.BombieriVinogradov.DirichletL.PolyaVinogradov
import Mathlib.NumberTheory.LSeries.SumCoeff

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

/-!
# A real zero of `L(s, χ)` near `1` when `L(1, χ)` is small

Let `χ` be a primitive quadratic character mod `q` and `a(n) = ∑_{d ∣ n} Re χ(d)` the
coefficients of `ζ(s) L(s, χ)`, so that `a(n) ≥ 0` and `a(1) = 1`. Pólya–Vinogradov gives
`∑_{n ≤ X} a(n) = X L(1, χ) + O(q √X)`, which continues `ζ(s) L(s, χ)` to `Re s > 1/2` and
gives an asymptotic for `∑_{n ≤ x} a(n) n^{-β}`. Taking `x = (648 q)^4` and `β = 1 - ε`,
the bound `L(1, χ) ≤ ε / (4 (648 q)^{4ε})` forces `ζ(β) L(β, χ) > 0`, and since `ζ(β) < 0`
for small `ε` and `L(1, χ) > 0`, `L(s, χ)` has a zero in `(1 - ε, 1)`.
-/

section

open Complex Finset
open ArithmeticFunction hiding log
open scoped BigOperators ComplexOrder Real

namespace DirichletCharacter

variable {q : ℕ}

/-- `a(n) = ∑_{d ∣ n} Re χ(d)`, the real part of the `n`-th coefficient of `ζ(s) L(s, χ)`. -/
noncomputable def quadraticSiegelConvolution
    (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  (χ.zetaMul n).re

theorem quadraticSiegelConvolution_eq_divisorSum
    (χ : DirichletCharacter ℂ q) (n : ℕ) :
    quadraticSiegelConvolution χ n = ∑ d ∈ n.divisors, (χ d).re := by
  rw [quadraticSiegelConvolution, zetaMul, coe_zeta_mul_apply]
  calc
    (∑ d ∈ n.divisors, (toArithmeticFunction fun x => χ x) d).re =
        (∑ d ∈ n.divisors, χ d).re := by
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
      simp [toArithmeticFunction, hd0]
    _ = ∑ d ∈ n.divisors, (χ d).re := Complex.re_sum _ _

/-- For quadratic `χ` the coefficients of `ζ(s) L(s, χ)` are real. -/
theorem zetaMul_im_eq_zero_of_sq_eq_one
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) (n : ℕ) :
    (χ.zetaMul n).im = 0 := by
  have h := zetaMul_nonneg hquad n
  rw [RCLike.le_iff_re_im] at h
  simpa using h.2.symm

/-- For quadratic `χ`, `a(n) ≥ 0`. -/
theorem quadraticSiegelConvolution_nonneg
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ quadraticSiegelConvolution χ n := by
  have h := zetaMul_nonneg hquad n
  rw [RCLike.le_iff_re_im] at h
  exact h.1

/-- The summatory function `A(X) = ∑_{1 ≤ n ≤ X} a(n)`. -/
noncomputable def quadraticSiegelConvolutionSummatory
    (χ : DirichletCharacter ℂ q) (X : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 X, quadraticSiegelConvolution χ n

theorem quadraticSiegelConvolutionSummatory_eq_divisorDoubleSum
    (χ : DirichletCharacter ℂ q) (X : ℕ) :
    quadraticSiegelConvolutionSummatory χ X =
      ∑ n ∈ Icc 1 X, ∑ d ∈ n.divisors, (χ d).re := by
  unfold quadraticSiegelConvolutionSummatory
  apply Finset.sum_congr rfl
  intro n hn
  exact quadraticSiegelConvolution_eq_divisorSum χ n

/-- The discrepancy `A(X) - X ∑_{1 ≤ d < m} Re χ(d)/d`. -/
noncomputable def quadraticSiegelConvolutionDiscrepancy
    (χ : DirichletCharacter ℂ q) (X m : ℕ) : ℝ :=
  quadraticSiegelConvolutionSummatory χ X -
    (X : ℝ) * quadraticHarmonicTruncation χ m

end DirichletCharacter

end

section

/-!
## Bounding the discrepancy

The discrepancy equals `∑_{d ≤ X} ⌊X/d⌋ Re χ(d) - X ∑_{1 ≤ d < m} Re χ(d)/d`. The terms
`d < m` contribute at most `m`, and the terms `d ≥ m` are bounded by Abel summation and
Pólya–Vinogradov.
-/

open Complex Finset
open BombieriVinogradov.AbelWeight
open scoped BigOperators

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

/-- Abel summation: if all prefix sums of `f` are at most `B` in absolute value and `w` is
nonnegative and decreasing, then `|∑_{i < n} w(i) f(i)| ≤ B w(0)`. -/
lemma abs_sum_range_mul_le_of_prefix
    (f w : ℕ → ℝ) (n : ℕ) (B : ℝ)
    (hB : 0 ≤ B)
    (hpref : ∀ k ≤ n, |∑ i ∈ range k, f i| ≤ B)
    (hw0 : ∀ i, 0 ≤ w i)
    (hwmono : ∀ i, i + 1 < n → w (i + 1) ≤ w i) :
    |∑ i ∈ range n, w i * f i| ≤ B * w 0 := by
  cases n with
  | zero => simpa using mul_nonneg hB (hw0 0)
  | succ k =>
      rw [show (∑ i ∈ range (k + 1), w i * f i) =
          ∑ i ∈ range (k + 1), w i • f i by simp]
      rw [Finset.sum_range_by_parts]
      simp only [Nat.add_sub_cancel, smul_eq_mul]
      calc
        |w k * (∑ i ∈ range (k + 1), f i) -
            ∑ i ∈ range k, (w (i + 1) - w i) * ∑ j ∈ range (i + 1), f j| ≤
            |w k * (∑ i ∈ range (k + 1), f i)| +
              |∑ i ∈ range k, (w (i + 1) - w i) * ∑ j ∈ range (i + 1), f j| :=
          abs_sub _ _
        _ ≤ B * w k +
            ∑ i ∈ range k, B * (w i - w (i + 1)) := by
          gcongr
          · rw [abs_mul, abs_of_nonneg (hw0 k)]
            simpa [mul_comm] using
              mul_le_mul_of_nonneg_left (hpref (k + 1) (by omega)) (hw0 k)
          · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            apply sum_le_sum
            intro i hi
            rw [mem_range] at hi
            have hmono := hwmono i (by omega)
            rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hmono), neg_sub]
            simpa [mul_comm] using
              mul_le_mul_of_nonneg_left (hpref (i + 1) (by omega))
                (sub_nonneg.mpr hmono)
        _ = B * w 0 := by
          rw [← Finset.mul_sum, Finset.sum_range_sub']
          ring

 omit [NeZero q] in
/-- Each `d ≤ X` divides exactly `⌊X/d⌋` integers `n ≤ X`. -/
theorem quadraticDivisorDoubleSum_eq_floorSum
    (χ : DirichletCharacter ℂ q) (X : ℕ) :
    (∑ n ∈ Icc 1 X, ∑ d ∈ n.divisors, (χ d).re) =
      ∑ d ∈ Icc 1 X, ((X / d : ℕ) : ℝ) * (χ d).re := by
  classical
  calc
    (∑ n ∈ Icc 1 X, ∑ d ∈ n.divisors, (χ d).re) =
        ∑ n ∈ Icc 1 X, ∑ d ∈ Icc 1 X, if d ∣ n then (χ d).re else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [mem_Icc] at hn
      rw [← sum_filter]
      apply sum_congr
      · ext d
        simp only [Nat.mem_divisors, mem_filter, mem_Icc]
        constructor
        · rintro ⟨hdn, hn0⟩
          exact ⟨⟨Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨hdn, hn0⟩),
            (Nat.le_of_dvd hn.1 hdn).trans hn.2⟩, hdn⟩
        · rintro ⟨⟨hd1, hdX⟩, hdn⟩
          exact ⟨hdn, by omega⟩
      · intro d hd
        simp only [mem_filter] at hd
        simp []
    _ = ∑ d ∈ Icc 1 X, ∑ n ∈ Icc 1 X, if d ∣ n then (χ d).re else 0 := by
      rw [sum_comm]
    _ = ∑ d ∈ Icc 1 X, ((X / d : ℕ) : ℝ) * (χ d).re := by
      apply sum_congr rfl
      intro d hd
      rw [mem_Icc] at hd
      rw [← sum_filter]
      have hcard : ((Icc 1 X).filter fun n => d ∣ n).card = X / d := by
        rw [← Nat.card_multiples' X d]
        congr 1
        ext n
        constructor
        · simp only [mem_filter, mem_Icc]
          rintro ⟨⟨hn1, hnX⟩, hdn⟩
          simp only [mem_range]
          exact ⟨Nat.lt_succ_of_le hnX, by omega, hdn⟩
        · simp only [mem_filter, mem_range]
          rintro ⟨hnX, hn0, hdn⟩
          simp only [mem_Icc]
          exact ⟨⟨Nat.pos_of_ne_zero hn0, Nat.le_of_lt_succ hnX⟩, hdn⟩
      simp [hcard]

omit [NeZero q] in
/-- The real part of the truncated harmonic sum is `∑_{1 ≤ d < m} Re χ(d)/d`. -/
theorem quadraticHarmonicTruncation_eq_Ico
    (χ : DirichletCharacter ℂ q) (m : ℕ) :
    quadraticHarmonicTruncation χ m =
      ∑ d ∈ Ico 1 m, (χ d).re / (d : ℝ) := by
  classical
  unfold quadraticHarmonicTruncation
  rw [Complex.re_sum]
  have hsub : Ico 1 m ⊆ range m := by
    intro d hd
    exact mem_range.mpr (mem_Ico.mp hd).2
  rw [← Finset.sum_subset hsub]
  · apply sum_congr rfl
    intro d hd
    rw [mem_Ico] at hd
    have hdpos : 0 < d := by omega
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
    simp [cpowWeight, Complex.cpow_neg_one, div_eq_mul_inv]
    field_simp [hd0]
  · intro d hdRange hdIco
    rw [mem_range] at hdRange
    have hd0 : d = 0 := by
      simp only [mem_Ico, not_and_or, not_le] at hdIco
      omega
    subst d
    simp [cpowWeight]

/-- Pólya–Vinogradov on intervals: `|∑_{a ≤ n < b} Re χ(n)| ≤ 8 √q (1 + log q)`. -/
theorem IsPrimitive.abs_sum_Ico_character_re_le_eight_mul_sqrt_q_mul_one_add_log
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 1 < q)
    (a b : ℕ) :
    |∑ n ∈ Ico a b, (χ n).re| ≤ 8 * Real.sqrt q * (1 + Real.log q) := by
  by_cases hab : a ≤ b
  · rw [← Complex.re_sum]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [Finset.sum_Ico_eq_sub (f := fun n => χ n) hab]
    calc
      ‖(∑ n ∈ range b, χ n) - ∑ n ∈ range a, χ n‖ ≤
          ‖∑ n ∈ range b, χ n‖ + ‖∑ n ∈ range a, χ n‖ := norm_sub_le _ _
      _ ≤ 4 * Real.sqrt q * (1 + Real.log q) +
          4 * Real.sqrt q * (1 + Real.log q) := by
        gcongr
        · simpa using hχ.norm_sum_range_le_four_mul_sqrt_q_mul_one_add_log hq b
        · simpa using hχ.norm_sum_range_le_four_mul_sqrt_q_mul_one_add_log hq a
      _ = 8 * Real.sqrt q * (1 + Real.log q) := by ring
  · rw [Finset.Ico_eq_empty (by omega)]
    simp
    positivity

/-- Abel summation against the decreasing weight `⌊X/d⌋` gives
`|∑_{m ≤ d ≤ X} ⌊X/d⌋ Re χ(d)| ≤ 8 √q (1 + log q) ⌊X/m⌋`. -/
theorem IsPrimitive.abs_floorWeighted_character_tail_le
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 1 < q)
    {m X : ℕ} (hm : 1 ≤ m) (_hmX : m ≤ X) :
    |∑ d ∈ Icc m X, ((X / d : ℕ) : ℝ) * (χ d).re| ≤
      (8 * Real.sqrt q * (1 + Real.log q)) * ((X / m : ℕ) : ℝ) := by
  let L := X + 1 - m
  let f : ℕ → ℝ := fun i => (χ (m + i)).re
  let w : ℕ → ℝ := fun i => ((X / (m + i) : ℕ) : ℝ)
  have hset : Icc m X = Ico m (X + 1) := by
    ext d
    simp only [mem_Icc, mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  have hB : 0 ≤ 8 * Real.sqrt q * (1 + Real.log q) := by
    have : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt hq)
    positivity
  have hab := abs_sum_range_mul_le_of_prefix f w L
    (8 * Real.sqrt q * (1 + Real.log q)) hB (by
      intro k hk
      rw [show (∑ i ∈ range k, f i) = ∑ n ∈ Ico m (m + k), (χ n).re by
        simpa [f] using
          (Finset.sum_Ico_eq_sum_range (fun n => (χ n).re) m (m + k)).symm]
      exact hχ.abs_sum_Ico_character_re_le_eight_mul_sqrt_q_mul_one_add_log
        hq m (m + k)) (by
      intro i
      dsimp only [w]
      exact_mod_cast Nat.zero_le (X / (m + i))) (by
      intro i hi
      dsimp only [w]
      exact_mod_cast Nat.div_le_div_left (Nat.le_succ (m + i))
        (by omega : 0 < m + i))
  simpa only [L, f, w, Nat.cast_add, Nat.add_zero, zero_add] using hab

omit [NeZero q] in
theorem quadraticSiegelConvolutionDiscrepancy_eq_floorSum_sub
    (χ : DirichletCharacter ℂ q) (X m : ℕ) :
    quadraticSiegelConvolutionDiscrepancy χ X m =
      (∑ d ∈ Icc 1 X, ((X / d : ℕ) : ℝ) * (χ d).re) -
        (X : ℝ) * ∑ d ∈ Ico 1 m, (χ d).re / (d : ℝ) := by
  rw [quadraticSiegelConvolutionDiscrepancy,
    quadraticSiegelConvolutionSummatory_eq_divisorDoubleSum,
    quadraticDivisorDoubleSum_eq_floorSum,
    quadraticHarmonicTruncation_eq_Ico]

end DirichletCharacter

end

section

open Complex Finset
open scoped BigOperators Real

namespace DirichletCharacter

lemma abs_natDiv_cast_sub_div_le_one (X d : ℕ) (hd : 1 ≤ d) :
    |((X / d : ℕ) : ℝ) - (X : ℝ) / (d : ℝ)| ≤ 1 := by
  have hdpos : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hdecomp :
      (X : ℝ) = (d : ℝ) * ((X / d : ℕ) : ℝ) + ((X % d : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod X d).symm
  have hquot :
      (X : ℝ) / (d : ℝ) =
        ((X / d : ℕ) : ℝ) + ((X % d : ℕ) : ℝ) / (d : ℝ) := by
    rw [div_eq_iff hdR.ne', add_mul, div_mul_cancel₀ _ hdR.ne']
    simpa [mul_comm] using hdecomp
  have hrnonneg : 0 ≤ ((X % d : ℕ) : ℝ) / (d : ℝ) := by positivity
  have hrle : ((X % d : ℕ) : ℝ) / (d : ℝ) ≤ 1 := by
    rw [div_le_one hdR]
    exact_mod_cast (Nat.mod_lt X hdpos).le
  rw [hquot]
  rw [show ((X / d : ℕ) : ℝ) -
      (((X / d : ℕ) : ℝ) + ((X % d : ℕ) : ℝ) / (d : ℝ)) =
        -(((X % d : ℕ) : ℝ) / (d : ℝ)) by ring,
      abs_neg, abs_of_nonneg hrnonneg]
  exact hrle

/-- The terms `d < m` contribute at most `m`, since `|⌊X/d⌋ - X/d| ≤ 1` and
`|Re χ(d)| ≤ 1`. -/
lemma abs_quadratic_shortFloorError_le
    {q : ℕ} (χ : DirichletCharacter ℂ q) (X m : ℕ) :
    |∑ d ∈ Ico 1 m,
        (((X / d : ℕ) : ℝ) * (χ d).re -
          (X : ℝ) * ((χ d).re / (d : ℝ)))| ≤ (m : ℝ) := by
  calc
    |∑ d ∈ Ico 1 m,
        (((X / d : ℕ) : ℝ) * (χ d).re -
          (X : ℝ) * ((χ d).re / (d : ℝ)))|
        ≤ ∑ d ∈ Ico 1 m,
            |((X / d : ℕ) : ℝ) * (χ d).re -
              (X : ℝ) * ((χ d).re / (d : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Ico 1 m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [mem_Ico] at hd
      have hfloor := abs_natDiv_cast_sub_div_le_one X d hd.1
      have hchi : |(χ d).re| ≤ 1 :=
        (Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one χ d)
      have heq :
          ((X / d : ℕ) : ℝ) * (χ d).re -
              (X : ℝ) * ((χ d).re / (d : ℝ)) =
            (((X / d : ℕ) : ℝ) - (X : ℝ) / (d : ℝ)) * (χ d).re := by
        ring
      rw [heq, abs_mul]
      exact mul_le_one₀ hfloor (abs_nonneg _) hchi
    _ = ((Ico 1 m).card : ℝ) := by simp
    _ ≤ (m : ℝ) := by
      rw [Nat.card_Ico]
      exact_mod_cast (Nat.sub_le m 1)

/-- For `1 ≤ m ≤ X`, the discrepancy is at most `m + 8 √q (1 + log q) ⌊X/m⌋`. -/
theorem IsPrimitive.abs_quadraticSiegelConvolutionDiscrepancy_le
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : 1 < q) {m X : ℕ} (hm : 1 ≤ m) (hmX : m ≤ X) :
    |quadraticSiegelConvolutionDiscrepancy χ X m| ≤
      (m : ℝ) +
        (8 * Real.sqrt q * (1 + Real.log q)) * ((X / m : ℕ) : ℝ) := by
  have hunion : Icc 1 X = Ico 1 m ∪ Icc m X := by
    ext d
    simp only [mem_Icc, mem_union, mem_Ico]
    omega
  have hdisj : Disjoint (Ico 1 m) (Icc m X) := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    rw [mem_Ico] at hd1
    rw [mem_Icc] at hd2
    omega
  have hD :
      quadraticSiegelConvolutionDiscrepancy χ X m =
        (∑ d ∈ Ico 1 m,
          (((X / d : ℕ) : ℝ) * (χ d).re -
            (X : ℝ) * ((χ d).re / (d : ℝ)))) +
        ∑ d ∈ Icc m X, ((X / d : ℕ) : ℝ) * (χ d).re := by
    rw [quadraticSiegelConvolutionDiscrepancy_eq_floorSum_sub, hunion,
      Finset.sum_union hdisj, Finset.mul_sum]
    rw [Finset.sum_sub_distrib]
    ring
  rw [hD]
  calc
    |(∑ d ∈ Ico 1 m,
          (((X / d : ℕ) : ℝ) * (χ d).re -
            (X : ℝ) * ((χ d).re / (d : ℝ)))) +
        ∑ d ∈ Icc m X, ((X / d : ℕ) : ℝ) * (χ d).re| ≤
      |∑ d ∈ Ico 1 m,
          (((X / d : ℕ) : ℝ) * (χ d).re -
            (X : ℝ) * ((χ d).re / (d : ℝ)))| +
        |∑ d ∈ Icc m X, ((X / d : ℕ) : ℝ) * (χ d).re| := abs_add_le _ _
    _ ≤ (m : ℝ) +
        (8 * Real.sqrt q * (1 + Real.log q)) * ((X / m : ℕ) : ℝ) := by
      gcongr
      · exact abs_quadratic_shortFloorError_le χ X m
      · exact hχ.abs_floorWeighted_character_tail_le hq hm hmX

end DirichletCharacter

end

/-!
## The summatory function

Taking `m = ⌊√X⌋` in the discrepancy bound and using `|L(1, χ) - ∑_{d < m} χ(d)/d| ≤ 2q/m`
gives `A(X) = X L(1, χ) + O(q √X)`.
-/

namespace BombieriVinogradov.Siegel

open Complex Finset DirichletCharacter

private theorem polyaVinogradov_budget_le_twentyfour_mul (q : ℕ) (hq : 1 ≤ q) :
    8 * Real.sqrt q * (1 + Real.log q) ≤ 24 * q := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hs : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hlogs := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt (by positivity)] at hlogs
  have hsle : Real.sqrt (q : ℝ) ≤ q :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hsq := Real.sq_sqrt (Nat.cast_nonneg q)
  have hprod := mul_le_mul_of_nonneg_left
    (show 1 + Real.log (q : ℝ) ≤ 1 + 2 * Real.sqrt q by linarith) hs.le
  nlinarith

private theorem div_natSqrt_le_three_mul_sqrt {X : ℕ} (hX : 1 ≤ X) :
    (X : ℝ) / (X.sqrt : ℝ) ≤ 3 * Real.sqrt X := by
  have hm : 1 ≤ X.sqrt := Nat.sqrt_pos.mpr (by omega)
  have hmR : (1 : ℝ) ≤ X.sqrt := by exact_mod_cast hm
  have hmsq : (X.sqrt : ℝ) ^ 2 ≤ X := by exact_mod_cast Nat.sqrt_le' X
  have hmlt : (X : ℝ) ≤ (X.sqrt : ℝ) * X.sqrt + X.sqrt + X.sqrt := by
    exact_mod_cast Nat.sqrt_le_add X
  have hmle : (X.sqrt : ℝ) ≤ Real.sqrt X :=
    (Real.le_sqrt (by positivity) (by positivity)).mpr hmsq
  have hdiv : (X : ℝ) / (X.sqrt : ℝ) ≤ (X.sqrt : ℝ) + 2 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < X.sqrt)]
    nlinarith
  exact hdiv.trans (by nlinarith)

/-- `|A(X) - X Re L(1, χ)| ≤ 79 q √X` for every primitive `χ ≠ 1`; `χ` need not be
quadratic here. -/
theorem IsPrimitive.abs_quadratic_convolution_sub_LValue_main_le
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (X : ℕ) :
    |quadraticSiegelConvolutionSummatory χ X - (X : ℝ) * (χ.LFunction 1).re| ≤
      79 * q * Real.sqrt X := by
  have hq : 1 < q := by
    have hq0 := NeZero.ne q
    have hq1 : q ≠ 1 := by
      rintro rfl
      exact hχ (Subsingleton.elim _ _)
    omega
  rcases X.eq_zero_or_pos with rfl | hX
  · simp [quadraticSiegelConvolutionSummatory]
  have hm : 1 ≤ X.sqrt := Nat.sqrt_pos.mpr hX
  have hdisc := hprim.abs_quadraticSiegelConvolutionDiscrepancy_le
    hq hm (Nat.sqrt_le_self X)
  have htail := abs_LFunction_one_re_sub_quadraticHarmonicTruncation_le χ hχ hm
  have hPV := polyaVinogradov_budget_le_twentyfour_mul q (by omega)
  have hdiv := div_natSqrt_le_three_mul_sqrt (show 1 ≤ X by omega)
  have hmle : (X.sqrt : ℝ) ≤ Real.sqrt X :=
    (Real.le_sqrt (by positivity) (by positivity)).mpr (by
      exact_mod_cast Nat.sqrt_le' X)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  calc
    _ = |quadraticSiegelConvolutionDiscrepancy χ X X.sqrt +
        (X : ℝ) * (quadraticHarmonicTruncation χ X.sqrt - (χ.LFunction 1).re)| := by
      congr 1
      unfold quadraticSiegelConvolutionDiscrepancy
      ring
    _ ≤ |quadraticSiegelConvolutionDiscrepancy χ X X.sqrt| +
        (X : ℝ) * |quadraticHarmonicTruncation χ X.sqrt - (χ.LFunction 1).re| := by
      simpa only [abs_mul, abs_of_nonneg (Nat.cast_nonneg X : (0 : ℝ) ≤ X)] using
        abs_add_le (quadraticSiegelConvolutionDiscrepancy χ X X.sqrt)
          ((X : ℝ) * (quadraticHarmonicTruncation χ X.sqrt - (χ.LFunction 1).re))
    _ ≤ (X.sqrt : ℝ) +
        (8 * Real.sqrt q * (1 + Real.log q)) * ((X / X.sqrt : ℕ) : ℝ) +
        (X : ℝ) * (2 * (q : ℝ) / (X.sqrt : ℝ)) := by
      exact add_le_add hdisc (mul_le_mul_of_nonneg_left
        (by simpa only [abs_sub_comm] using htail) (Nat.cast_nonneg X))
    _ ≤ Real.sqrt X + (24 * q) * ((X : ℝ) / (X.sqrt : ℝ)) +
        (X : ℝ) * (2 * (q : ℝ) / (X.sqrt : ℝ)) := by
      gcongr
      exact Nat.cast_div_le
    _ = Real.sqrt X + (26 * q) * ((X : ℝ) / (X.sqrt : ℝ)) := by ring
    _ ≤ Real.sqrt X + (26 * q) * (3 * Real.sqrt X) := by gcongr
    -- Use `q ≥ 1` to absorb the term `√X`.
    _ ≤ q * Real.sqrt X + (26 * q) * (3 * Real.sqrt X) :=
      add_le_add (le_mul_of_one_le_left (Real.sqrt_nonneg _) hqR) le_rfl
    _ = 79 * q * Real.sqrt X := by ring

/-- For real `x ≥ 1`, `|A(⌊x⌋) - x Re L(1, χ)| ≤ 81 q √x`, using `|L(1, χ)| ≤ 2q`. -/
theorem IsPrimitive.abs_quadratic_convolution_floor_sub_LValue_main_le
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    |quadraticSiegelConvolutionSummatory χ ⌊x⌋₊ - x * (χ.LFunction 1).re| ≤
      81 * q * Real.sqrt x := by
  have hmain := IsPrimitive.abs_quadratic_convolution_sub_LValue_main_le χ hprim hχ ⌊x⌋₊
  have htail := norm_LFunction_one_sub_harmonic_sum_le χ hχ (m := 1) (by norm_num)
  have hnorm : ‖χ.LFunction 1‖ ≤ 2 * q := by
    simpa [BombieriVinogradov.AbelWeight.cpowWeight] using htail
  have hL : |(χ.LFunction 1).re| ≤ 2 * q := (Complex.abs_re_le_norm _).trans hnorm
  have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have herror : |(⌊x⌋₊ : ℝ) - x| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hfloor)]
    linarith only [Nat.lt_floor_add_one x]
  have hsqrt : Real.sqrt (⌊x⌋₊ : ℝ) ≤ Real.sqrt x := Real.sqrt_le_sqrt hfloor
  have hsqrt1 : 1 ≤ Real.sqrt x :=
    (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hx)
  calc
    _ = |(quadraticSiegelConvolutionSummatory χ ⌊x⌋₊ -
          (⌊x⌋₊ : ℝ) * (χ.LFunction 1).re) +
        ((⌊x⌋₊ : ℝ) - x) * (χ.LFunction 1).re| := by congr 1; ring
    _ ≤ |quadraticSiegelConvolutionSummatory χ ⌊x⌋₊ -
          (⌊x⌋₊ : ℝ) * (χ.LFunction 1).re| +
        |(⌊x⌋₊ : ℝ) - x| * |(χ.LFunction 1).re| := by
      simpa only [abs_mul] using
        abs_add_le (quadraticSiegelConvolutionSummatory χ ⌊x⌋₊ -
          (⌊x⌋₊ : ℝ) * (χ.LFunction 1).re)
          (((⌊x⌋₊ : ℝ) - x) * (χ.LFunction 1).re)
    _ ≤ 79 * q * Real.sqrt (⌊x⌋₊ : ℝ) + 1 * (2 * q) := by gcongr
    _ ≤ 79 * q * Real.sqrt x + 1 * (2 * q) := by gcongr
    -- Since `x ≥ 1`, `2q ≤ 2q √x`.
    _ ≤ 79 * q * Real.sqrt x + (2 * q) * Real.sqrt x := by
      exact add_le_add le_rfl (by
        simpa only [one_mul] using
          le_mul_of_one_le_right (by positivity : 0 ≤ 2 * (q : ℝ)) hsqrt1)
    _ = 81 * q * Real.sqrt x := by ring

end BombieriVinogradov.Siegel

section

/-!
## Continuation of `ζ(s) L(s, χ)` to `Re s > 1/2`

With `E(t) = A(⌊t⌋) - t Re L(1, χ)`, partial summation gives, for `Re s > 1`,
`ζ(s) L(s, χ) = Re L(1, χ) s/(s - 1) + s ∫_1^∞ E(t) t^{-s-1} dt`. Since `E(t) = O(q √t)`, the
integral is holomorphic for `Re s > 1/2`, and the identity theorem extends the formula there.
-/

open Complex Finset Filter MeasureTheory Set Asymptotics
open scoped Topology

namespace BombieriVinogradov.Siegel

open DirichletCharacter
variable {q : ℕ} [NeZero q]

/-- The error term `E(t) = A(⌊t⌋) - t Re L(1, χ)`. -/
noncomputable def quadraticConvolutionError (χ : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  quadraticSiegelConvolutionSummatory χ ⌊t⌋₊ - t * (χ.LFunction 1).re

/-- The integrand `E(t) t^{-s-1}`. -/
noncomputable def quadraticConvolutionErrorKernel
    (χ : DirichletCharacter ℂ q) (s : ℂ) (t : ℝ) : ℂ :=
  (quadraticConvolutionError χ t : ℂ) * (t : ℂ) ^ (-(s + 1))

/-- The error integral `∫_1^∞ E(t) t^{-s-1} dt`. -/
noncomputable def quadraticConvolutionErrorIntegral
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), quadraticConvolutionErrorKernel χ s t

/-- `E(t)` for `t > 1` and `0` otherwise; its Mellin transform at `-s` is the error
integral. -/
noncomputable def quadraticConvolutionCutoffError
    (χ : DirichletCharacter ℂ q) : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator fun t => (quadraticConvolutionError χ t : ℂ)

theorem measurable_quadraticConvolutionError (χ : DirichletCharacter ℂ q) :
    Measurable (quadraticConvolutionError χ) := by
  exact ((StronglyMeasurable.of_discrete (f := quadraticSiegelConvolutionSummatory χ)).measurable.comp
    measurable_id.nat_floor).sub (measurable_id.mul_const _)

theorem measurable_quadraticConvolutionCutoffError (χ : DirichletCharacter ℂ q) :
    Measurable (quadraticConvolutionCutoffError χ) :=
  (Complex.measurable_ofReal.comp (measurable_quadraticConvolutionError χ)).indicator
    measurableSet_Ioi

theorem IsPrimitive.abs_quadraticConvolutionError_le
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {t : ℝ} (ht : 1 ≤ t) :
    |quadraticConvolutionError χ t| ≤ 81 * q * Real.sqrt t :=
  IsPrimitive.abs_quadratic_convolution_floor_sub_LValue_main_le χ hprim hχ ht

theorem IsPrimitive.norm_quadraticConvolutionCutoffError_le
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (t : ℝ) :
    ‖quadraticConvolutionCutoffError χ t‖ ≤ 81 * q * Real.sqrt t := by
  by_cases ht : 1 < t
  · simpa [quadraticConvolutionCutoffError, ht] using
      IsPrimitive.abs_quadraticConvolutionError_le χ hprim hχ ht.le
  · simp [quadraticConvolutionCutoffError, ht]
    positivity

theorem IsPrimitive.locallyIntegrable_quadraticConvolutionCutoffError
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    LocallyIntegrable (quadraticConvolutionCutoffError χ) := by
  refine (show Continuous (fun t : ℝ => 81 * (q : ℝ) * Real.sqrt t) by
    fun_prop).locallyIntegrable.mono
      (measurable_quadraticConvolutionCutoffError χ).aestronglyMeasurable ?_
  filter_upwards [] with t
  exact (IsPrimitive.norm_quadraticConvolutionCutoffError_le χ hprim hχ t).trans
    (Real.le_norm_self _)

theorem IsPrimitive.quadraticConvolutionCutoffError_isBigO_atTop
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    quadraticConvolutionCutoffError χ =O[atTop] (fun t : ℝ => t ^ (1 / 2 : ℝ)) := by
  refine isBigO_iff.mpr ⟨81 * q, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simpa [Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht _)]
    using IsPrimitive.norm_quadraticConvolutionCutoffError_le χ hprim hχ t

theorem quadraticConvolutionCutoffError_isBigO_zero
    (χ : DirichletCharacter ℂ q) (b : ℝ) :
    quadraticConvolutionCutoffError χ =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ b) := by
  refine isBigO_iff.mpr ⟨0, ?_⟩
  filter_upwards [((eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
    nhdsWithin_le_nhds)] with t ht
  simp [quadraticConvolutionCutoffError, not_lt.mpr ht.le]

private theorem cutoff_mellin_kernel (χ : DirichletCharacter ℂ q) (s : ℂ) :
    (fun t : ℝ => (t : ℂ) ^ (-s - 1) • quadraticConvolutionCutoffError χ t) =
      (Ioi (1 : ℝ)).indicator (quadraticConvolutionErrorKernel χ s) := by
  funext t
  by_cases ht : 1 < t
  · simp [quadraticConvolutionCutoffError, quadraticConvolutionErrorKernel, ht,
      smul_eq_mul, sub_eq_add_neg, mul_comm, add_comm]
  · simp [quadraticConvolutionCutoffError, ht]

theorem mellin_quadraticConvolutionCutoffError
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    mellin (quadraticConvolutionCutoffError χ) (-s) =
      quadraticConvolutionErrorIntegral χ s := by
  rw [mellin, cutoff_mellin_kernel, setIntegral_indicator measurableSet_Ioi]
  simp only [Ioi_inter_Ioi, max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)]
  rfl

theorem IsPrimitive.mellinConvergent_quadraticConvolutionCutoffError
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    MellinConvergent (quadraticConvolutionCutoffError χ) (-s) := by
  apply mellinConvergent_of_isBigO_rpow
    ((IsPrimitive.locallyIntegrable_quadraticConvolutionCutoffError χ hprim hχ).locallyIntegrableOn _)
    (a := -(1 / 2)) (b := -s.re - 1)
  · simpa using IsPrimitive.quadraticConvolutionCutoffError_isBigO_atTop χ hprim hχ
  · simp only [neg_re]; linarith
  · exact quadraticConvolutionCutoffError_isBigO_zero χ _
  · simp only [neg_re]; linarith

/-- The error integral converges absolutely for `Re s > 1/2`. -/
theorem IsPrimitive.integrableOn_quadraticConvolutionErrorKernel
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    IntegrableOn (quadraticConvolutionErrorKernel χ s) (Ioi (1 : ℝ)) := by
  have h := IsPrimitive.mellinConvergent_quadraticConvolutionCutoffError χ hprim hχ hs
  rw [MellinConvergent, cutoff_mellin_kernel,
    integrableOn_indicator_iff measurableSet_Ioi] at h
  simpa only [Ioi_inter_Ioi, max_eq_left (show (0 : ℝ) ≤ 1 by norm_num)] using h

/-- The error integral is holomorphic for `Re s > 1/2`, being a Mellin transform of a
function that is `O(√t)` at infinity and vanishes near `0`. -/
theorem IsPrimitive.differentiableAt_quadraticConvolutionErrorIntegral
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (quadraticConvolutionErrorIntegral χ) s := by
  have hm : DifferentiableAt ℂ (mellin (quadraticConvolutionCutoffError χ)) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow
      ((IsPrimitive.locallyIntegrable_quadraticConvolutionCutoffError χ hprim hχ).locallyIntegrableOn _)
      (a := -(1 / 2)) (b := -s.re - 1)
    · simpa using IsPrimitive.quadraticConvolutionCutoffError_isBigO_atTop χ hprim hχ
    · simp only [neg_re]; linarith
    · exact quadraticConvolutionCutoffError_isBigO_zero χ _
    · simp only [neg_re]; linarith
  simpa only [Function.comp_def, mellin_quadraticConvolutionCutoffError] using
    hm.comp s differentiableAt_id.neg

omit [NeZero q] in
theorem quadraticSiegelConvolution_ofReal_eq_zetaMul
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) (n : ℕ) :
    (quadraticSiegelConvolution χ n : ℂ) = χ.zetaMul n := by
  apply Complex.ext
  · rfl
  · exact (zetaMul_im_eq_zero_of_sq_eq_one χ hquad n).symm

omit [NeZero q] in
theorem quadraticSiegelConvolutionSummatory_ofReal_eq_sum_zetaMul
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) (n : ℕ) :
    (quadraticSiegelConvolutionSummatory χ n : ℂ) =
      ∑ k ∈ Finset.Icc 1 n, χ.zetaMul k := by
  simp only [quadraticSiegelConvolutionSummatory, ofReal_sum,
    quadraticSiegelConvolution_ofReal_eq_zetaMul χ hquad]

theorem IsPrimitive.quadraticSiegelConvolutionSummatory_isBigO
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    quadraticSiegelConvolutionSummatory χ =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
  refine isBigO_iff.mpr ⟨79 * q + |(χ.LFunction 1).re|, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : Real.sqrt (n : ℝ) ≤ n := Real.sqrt_le_self_iff.mpr (Or.inr hnR)
  simp only [Real.norm_eq_abs, Real.rpow_one,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  calc
    _ ≤ |quadraticSiegelConvolutionSummatory χ n - (n : ℝ) * (χ.LFunction 1).re| +
        (n : ℝ) * |(χ.LFunction 1).re| := by
      simpa only [sub_add_cancel, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] using
        abs_add_le
          (quadraticSiegelConvolutionSummatory χ n - (n : ℝ) * (χ.LFunction 1).re)
          ((n : ℝ) * (χ.LFunction 1).re)
    _ ≤ 79 * q * Real.sqrt n + (n : ℝ) * |(χ.LFunction 1).re| :=
      add_le_add
        (IsPrimitive.abs_quadratic_convolution_sub_LValue_main_le χ hprim hχ n) le_rfl
    _ ≤ 79 * q * n + (n : ℝ) * |(χ.LFunction 1).re| :=
      add_le_add
        (mul_le_mul_of_nonneg_left hsqrt (show (0 : ℝ) ≤ 79 * q by positivity)) le_rfl
    _ = _ := by ring

theorem IsPrimitive.sum_zetaMul_isBigO
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ.zetaMul k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
  have h := IsPrimitive.quadraticSiegelConvolutionSummatory_isBigO χ hprim hχ
  rw [isBigO_iff] at h ⊢
  obtain ⟨C, hC⟩ := h
  refine ⟨C, hC.mono fun n hn => ?_⟩
  simpa only [← quadraticSiegelConvolutionSummatory_ofReal_eq_sum_zetaMul χ hquad,
    Complex.norm_real] using hn

private theorem mul_error_cpow (t : ℝ) (ht : 0 < t) (s : ℂ) :
    (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (-s) := by
  simpa only [cpow_one, neg_add_rev, add_neg_cancel_left] using
    (cpow_add (1 : ℂ) (-(s + 1)) (ofReal_ne_zero.mpr ht.ne')).symm

private theorem summatory_kernel_split
    (χ : DirichletCharacter ℂ q) (s : ℂ) {t : ℝ} (ht : 1 < t) :
    (quadraticSiegelConvolutionSummatory χ ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      quadraticConvolutionErrorKernel χ s t +
        ((χ.LFunction 1).re : ℂ) * (t : ℂ) ^ (-s) := by
  rw [quadraticConvolutionErrorKernel, quadraticConvolutionError, ofReal_sub, ofReal_mul,
    sub_mul, ← mul_error_cpow t (by linarith) s]
  ring

/-- For `Re s > 1`, partial summation of the Dirichlet series of `ζ(s) L(s, χ)` gives
`ζ(s) L(s, χ) = Re L(1, χ) s/(s - 1) + s ∫_1^∞ E(t) t^{-s-1} dt`. -/
theorem IsPrimitive.riemannZeta_mul_LFunction_eq_errorIntegral_of_one_lt_re
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * χ.LFunction s =
      ((χ.LFunction 1).re : ℂ) * s / (s - 1) +
        s * quadraticConvolutionErrorIntegral χ s := by
  have hid := LSeries_eq_mul_integral (fun n => χ.zetaMul n)
    (r := 1) (by norm_num) hs (χ.LSeriesSummable_zetaMul hs)
    (IsPrimitive.sum_zetaMul_isBigO χ hprim hχ hquad)
  rw [← riemannZeta_mul_LFunction_eq_LSeries_zetaMul χ hs] at hid
  simp only [← quadraticSiegelConvolutionSummatory_ofReal_eq_sum_zetaMul χ hquad] at hid
  have hsplit :
      (∫ t in Ioi (1 : ℝ),
        (quadraticSiegelConvolutionSummatory χ ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) =
        quadraticConvolutionErrorIntegral χ s +
          ((χ.LFunction 1).re : ℂ) * (-(1 : ℂ) / (-s + 1)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => summatory_kernel_split χ s ht)]
    rw [integral_add
      (IsPrimitive.integrableOn_quadraticConvolutionErrorKernel χ hprim hχ (by linarith))
      ((integrableOn_Ioi_cpow_of_lt (by simpa using (neg_lt_neg hs))
        (by norm_num : (0 : ℝ) < 1)).const_mul ((χ.LFunction 1).re : ℂ)),
      integral_const_mul, integral_Ioi_cpow_of_lt (by simpa using (neg_lt_neg hs))
        (by norm_num : (0 : ℝ) < 1)]
    simp only [ofReal_one, one_cpow]
    rfl
  rw [hid, hsplit]
  have hm : -s + 1 = -(s - 1) := by ring
  rw [hm, div_neg, neg_div, neg_neg]
  ring

/-- With the entire function `ζ₁(s) = (s - 1) ζ(s)`, the identity
`ζ₁(s) L(s, χ) = Re L(1, χ) s + (s - 1) s ∫_1^∞ E(t) t^{-s-1} dt` extends from `Re s > 1` to
`Re s > 1/2` by the identity theorem. -/
theorem IsPrimitive.riemannZeta₁_mul_LFunction_eq_errorIntegral
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    riemannZeta₁ s * χ.LFunction s =
      ((χ.LFunction 1).re : ℂ) * s +
        (s - 1) * s * quadraticConvolutionErrorIntegral χ s := by
  let U : Set ℂ := {z | 1 / 2 < z.re}
  let F : ℂ → ℂ := fun z => ((χ.LFunction 1).re : ℂ) * z +
    (z - 1) * z * quadraticConvolutionErrorIntegral χ z
  let G : ℂ → ℂ := fun z => riemannZeta₁ z * χ.LFunction z
  have hUopen : IsOpen U := continuous_re.isOpen_preimage _ isOpen_Ioi
  have hFdiff : DifferentiableOn ℂ F U := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have hE := IsPrimitive.differentiableAt_quadraticConvolutionErrorIntegral χ hprim hχ hz
    dsimp [F]
    fun_prop
  have hF : AnalyticOnNhd ℂ F U := hFdiff.analyticOnNhd hUopen
  have hG : AnalyticOnNhd ℂ G U :=
    (differentiable_riemannZeta₁.mul (χ.differentiable_LFunction hχ)).differentiableOn.analyticOnNhd
      isOpen_univ |>.mono (subset_univ U)
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have htwo : (2 : ℂ) ∈ U := by norm_num [U]
  have hevent : G =ᶠ[𝓝 (2 : ℂ)] F := by
    filter_upwards [eventually_of_mem
      ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
        (by norm_num : (1 : ℝ) < (2 : ℂ).re)) (fun z hz => hz)] with z hz
    have hz1 : z ≠ 1 := by
      intro h
      rw [h] at hz
      norm_num at hz
    have hzeta : riemannZeta₁ z = (z - 1) * riemannZeta z := by
      rw [riemannZeta_eq_inv_sub_mul hz1, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hz1),
        one_mul]
    dsimp [F, G]
    rw [hzeta, mul_assoc,
      IsPrimitive.riemannZeta_mul_LFunction_eq_errorIntegral_of_one_lt_re χ hprim hχ hquad hz]
    field_simp
  exact hG.eqOn_of_preconnected_of_eventuallyEq hF hpre htwo hevent hs

/-- The formula `ζ(s) L(s, χ) = Re L(1, χ) s/(s - 1) + s ∫_1^∞ E(t) t^{-s-1} dt` holds for
`Re s > 1/2`, `s ≠ 1`. -/
theorem IsPrimitive.riemannZeta_mul_LFunction_eq_errorIntegral
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s * χ.LFunction s =
      ((χ.LFunction 1).re : ℂ) * s / (s - 1) +
        s * quadraticConvolutionErrorIntegral χ s := by
  rw [riemannZeta_eq_inv_sub_mul hs1, mul_assoc,
    IsPrimitive.riemannZeta₁_mul_LFunction_eq_errorIntegral χ hprim hχ hquad hs]
  field_simp

end BombieriVinogradov.Siegel

end

section

/-!
## Weighted sums

For `β > 1/2`, `β ≠ 1`, partial summation gives
`∑_{n ≤ x} a(n) n^{-β} = Re L(1, χ) x^{1-β}/(1 - β) + ζ(β) L(β, χ) + O(q x^{1/2-β})`.
-/

open Complex Finset Filter MeasureTheory
open scoped Topology

namespace BombieriVinogradov.Siegel

open DirichletCharacter
variable {q : ℕ} [NeZero q]

/-- The weighted sum `∑_{1 ≤ n ≤ x} a(n) n^{-β}`. -/
noncomputable def quadraticConvolutionWeightedSum
    (χ : DirichletCharacter ℂ q) (β x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, quadraticSiegelConvolution χ n * (n : ℝ) ^ (-β)

omit [NeZero q] in
private theorem convolution_sum_from_zero (χ : DirichletCharacter ℂ q) (N : ℕ) :
    ∑ n ∈ Icc 0 N, quadraticSiegelConvolution χ n =
      quadraticSiegelConvolutionSummatory χ N := by
  rw [← insert_Icc_add_one_left_eq_Icc (Nat.zero_le N), sum_insert (by simp)]
  simp [quadraticSiegelConvolution, quadraticSiegelConvolutionSummatory]

private theorem rpow_continuousOn (β x : ℝ) :
    ContinuousOn (fun t : ℝ => t ^ β) (Set.Icc 1 x) := by
  intro t ht
  exact (Real.continuousAt_rpow_const _ _
    (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))).continuousWithinAt

omit [NeZero q] in
/-- Abel summation for the weighted sum, valid for every real `β`. -/
theorem quadraticConvolutionWeightedSum_eq_abel
    (χ : DirichletCharacter ℂ q) (β x : ℝ) :
    quadraticConvolutionWeightedSum χ β x =
      x ^ (-β) * quadraticSiegelConvolutionSummatory χ ⌊x⌋₊ +
        β * ∫ t in Set.Ioc (1 : ℝ) x,
          quadraticSiegelConvolutionSummatory χ ⌊t⌋₊ * t ^ (-β - 1) := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc 1 x) :
      HasDerivAt (fun t : ℝ => t ^ (-β)) (-β * t ^ (-β - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))
  have hint : IntegrableOn (deriv (fun t : ℝ => t ^ (-β))) (Set.Icc 1 x) :=
    (((rpow_continuousOn (-β - 1) x).const_mul (-β)).integrableOn_Icc).congr_fun
      (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have h := sum_mul_eq_sub_integral_mul₀ (quadraticSiegelConvolution χ)
    (by simp [quadraticSiegelConvolution]) x (fun t ht => (hd t ht).differentiableAt) hint
  have hs :
      (∑ n ∈ Icc 0 ⌊x⌋₊, (n : ℝ) ^ (-β) * quadraticSiegelConvolution χ n) =
        quadraticConvolutionWeightedSum χ β x := by
    rw [← insert_Icc_add_one_left_eq_Icc (Nat.zero_le ⌊x⌋₊),
      sum_insert (by simp)]
    simp [quadraticSiegelConvolution, quadraticConvolutionWeightedSum, mul_comm]
  rw [hs, convolution_sum_from_zero] at h
  have hi :
      (∫ t in Set.Ioc (1 : ℝ) x,
        deriv (fun t : ℝ => t ^ (-β)) t *
          ∑ n ∈ Icc 0 ⌊t⌋₊, quadraticSiegelConvolution χ n) =
      -β * ∫ t in Set.Ioc (1 : ℝ) x,
        quadraticSiegelConvolutionSummatory χ ⌊t⌋₊ * t ^ (-β - 1) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hd t ⟨ht.1.le, ht.2⟩).deriv, convolution_sum_from_zero]
    ring
  rw [hi] at h
  linarith

theorem quadraticConvolutionErrorKernel_ofReal
    (χ : DirichletCharacter ℂ q) (β : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    quadraticConvolutionErrorKernel χ (β : ℂ) t =
      ((quadraticConvolutionError χ t * t ^ (-β - 1) : ℝ) : ℂ) := by
  rw [quadraticConvolutionErrorKernel, ofReal_mul, Complex.ofReal_cpow ht]
  congr 2
  push_cast
  ring

theorem IsPrimitive.integrableOn_real_quadraticConvolutionErrorKernel
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {β : ℝ} (hβ : 1 / 2 < β) :
    IntegrableOn (fun t : ℝ => quadraticConvolutionError χ t * t ^ (-β - 1))
      (Set.Ioi (1 : ℝ)) := by
  have h := (IsPrimitive.integrableOn_quadraticConvolutionErrorKernel χ hprim hχ
    (s := (β : ℂ)) hβ).re
  exact IntegrableOn.congr_fun h (fun t ht => by
    rw [quadraticConvolutionErrorKernel_ofReal χ β (le_of_lt (lt_trans zero_lt_one ht))]
    rfl) measurableSet_Ioi

/-- The continuation formula at real `β > 1/2`, `β ≠ 1`. -/
theorem IsPrimitive.re_riemannZeta_mul_LFunction_eq_real_errorIntegral
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) {β : ℝ} (hβ : 1 / 2 < β) (hβ1 : β ≠ 1) :
    (riemannZeta (β : ℂ) * χ.LFunction (β : ℂ)).re =
      (χ.LFunction 1).re * β / (β - 1) +
        β * ∫ t in Set.Ioi (1 : ℝ),
          quadraticConvolutionError χ t * t ^ (-β - 1) := by
  have h := IsPrimitive.riemannZeta_mul_LFunction_eq_errorIntegral χ hprim hχ hquad
    (s := (β : ℂ)) hβ (by exact_mod_cast hβ1)
  have hI :
      (quadraticConvolutionErrorIntegral χ (β : ℂ)).re =
        ∫ t in Set.Ioi (1 : ℝ),
          quadraticConvolutionError χ t * t ^ (-β - 1) := by
    calc
      _ = ∫ t in Set.Ioi (1 : ℝ),
          (quadraticConvolutionErrorKernel χ (β : ℂ) t).re :=
        (integral_re (IsPrimitive.integrableOn_quadraticConvolutionErrorKernel
          χ hprim hχ (s := (β : ℂ)) hβ)).symm
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [quadraticConvolutionErrorKernel_ofReal χ β
          (le_of_lt (lt_trans zero_lt_one ht))]
        rfl
  have hmain :
      ((χ.LFunction 1).re : ℂ) * (β : ℂ) / ((β : ℂ) - 1) =
        (((χ.LFunction 1).re * β / (β - 1) : ℝ) : ℂ) := by push_cast; rfl
  rw [h, add_re, hmain, ofReal_re, re_ofReal_mul, hI]

private theorem sqrt_mul_weight {t : ℝ} (ht : 0 < t) (β : ℝ) :
    Real.sqrt t * t ^ (-β - 1) = t ^ (-β - 1 / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]
  congr 1
  ring

/-- Tail bound for the error integral, from `|E(t)| ≤ 81 q √t`. -/
theorem IsPrimitive.abs_quadraticConvolutionError_tail_le
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {β x : ℝ} (hβ : 1 / 2 < β) (hx : 1 ≤ x) :
    |∫ t in Set.Ioi x, quadraticConvolutionError χ t * t ^ (-β - 1)| ≤
      81 * q * x ^ (1 / 2 - β) / (β - 1 / 2) := by
  have hp : -β - 1 / 2 < -1 := by linarith
  have hx0 : 0 < x := by linarith
  have hg := (integrableOn_Ioi_rpow_of_lt hp hx0).const_mul (81 * (q : ℝ))
  have hbound :
      ∀ᵐ t ∂volume.restrict (Set.Ioi x),
        ‖quadraticConvolutionError χ t * t ^ (-β - 1)‖ ≤
          81 * q * t ^ (-β - 1 / 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hx0 ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    calc
      _ ≤ (81 * q * Real.sqrt t) * t ^ (-β - 1) :=
        mul_le_mul_of_nonneg_right
          (IsPrimitive.abs_quadraticConvolutionError_le χ hprim hχ (hx.trans ht.le))
          (Real.rpow_nonneg ht0.le _)
      _ = _ := by rw [mul_assoc, sqrt_mul_weight ht0]
  have h := norm_integral_le_of_norm_le hg hbound
  rw [Real.norm_eq_abs, integral_const_mul, integral_Ioi_rpow_of_lt hp hx0] at h
  rw [show -β - 1 / 2 + 1 = -(β - 1 / 2) by ring,
    div_neg, neg_div, neg_neg] at h
  convert h using 1
  ring_nf

private theorem mul_weight {t : ℝ} (ht : 0 < t) (β : ℝ) :
    t * t ^ (-β - 1) = t ^ (-β) := by
  calc
    _ = t ^ (1 : ℝ) * t ^ (-β - 1) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add ht]; congr 1; ring

private theorem mul_weight_main {t : ℝ} (ht : 0 < t) (β : ℝ) :
    t ^ (-β) * t = t ^ (1 - β) := by
  calc
    _ = t ^ (-β) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add ht]; congr 1; ring

/-- The weighted sum equals the main term `Re L(1, χ) x^{1-β}/(1 - β)`, plus the constant
`ζ(β) L(β, χ)`, plus the endpoint term `E(x) x^{-β}`, minus the tail
`β ∫_x^∞ E(t) t^{-β-1} dt`. -/
theorem IsPrimitive.quadraticConvolutionWeightedSum_eq_product_add_tail
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) {β x : ℝ}
    (hβ : 1 / 2 < β) (hβ1 : β ≠ 1) (hx : 1 ≤ x) :
    quadraticConvolutionWeightedSum χ β x =
      (χ.LFunction 1).re * x ^ (1 - β) / (1 - β) +
        (riemannZeta (β : ℂ) * χ.LFunction (β : ℂ)).re +
        quadraticConvolutionError χ x * x ^ (-β) -
        β * ∫ t in Set.Ioi x, quadraticConvolutionError χ t * t ^ (-β - 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hE := IsPrimitive.integrableOn_real_quadraticConvolutionErrorKernel χ hprim hχ hβ
  have hEI : IntegrableOn
      (fun t : ℝ => quadraticConvolutionError χ t * t ^ (-β - 1))
      (Set.Ioc 1 x) := hE.mono_set Set.Ioc_subset_Ioi_self
  have hP : IntegrableOn (fun t : ℝ => (χ.LFunction 1).re * t ^ (-β))
      (Set.Ioc 1 x) :=
    ((rpow_continuousOn (-β) x).const_mul _).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hsplit :
      (∫ t in Set.Ioc (1 : ℝ) x,
        quadraticSiegelConvolutionSummatory χ ⌊t⌋₊ * t ^ (-β - 1)) =
      (∫ t in Set.Ioc (1 : ℝ) x,
        quadraticConvolutionError χ t * t ^ (-β - 1)) +
      (χ.LFunction 1).re * ∫ t in Set.Ioc (1 : ℝ) x, t ^ (-β) := by
    rw [← integral_const_mul, ← integral_add hEI hP]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    unfold quadraticConvolutionError
    rw [sub_mul, mul_assoc t _ _, mul_comm (χ.LFunction 1).re,
      ← mul_assoc t, mul_weight (lt_trans zero_lt_one ht.1)]
    ring
  have hpow :
      (∫ t in Set.Ioc (1 : ℝ) x, t ^ (-β)) =
        (x ^ (1 - β) - 1) / (1 - β) := by
    rw [← intervalIntegral.integral_of_le hx]
    rw [integral_rpow (Or.inr ⟨fun h => hβ1 (by linarith), by
      rw [Set.uIcc_of_le hx]
      simp⟩)]
    simp only [Real.one_rpow]
    rw [show -β + 1 = 1 - β by ring]
  have htail := intervalIntegral.integral_Ioi_sub_Ioi hE hx
  rw [intervalIntegral.integral_of_le hx] at htail
  have hend :
      x ^ (-β) * quadraticSiegelConvolutionSummatory χ ⌊x⌋₊ =
        quadraticConvolutionError χ x * x ^ (-β) +
          (χ.LFunction 1).re * x ^ (1 - β) := by
    unfold quadraticConvolutionError
    rw [sub_mul, mul_assoc x _ _, mul_comm (χ.LFunction 1).re,
      ← mul_assoc x, mul_comm x (x ^ (-β)), mul_weight_main hx0]
    ring
  rw [quadraticConvolutionWeightedSum_eq_abel, hsplit, hpow, hend,
    IsPrimitive.re_riemannZeta_mul_LFunction_eq_real_errorIntegral χ hprim hχ hquad hβ hβ1,
    ← htail]
  have hden : 1 - β ≠ 0 := sub_ne_zero.mpr hβ1.symm
  have hden' : β - 1 ≠ 0 := sub_ne_zero.mpr hβ1
  field_simp
  ring

/-- For `β > 1/2`, `β ≠ 1` and `x ≥ 1`, the weighted sum equals
`Re L(1, χ) x^{1-β}/(1 - β) + ζ(β) L(β, χ)` up to `81 q (1 + β/(β - 1/2)) x^{1/2-β}`. -/
theorem IsPrimitive.abs_quadraticConvolutionWeightedSum_sub_main_sub_product_le
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) {β x : ℝ}
    (hβ : 1 / 2 < β) (hβ1 : β ≠ 1) (hx : 1 ≤ x) :
    |quadraticConvolutionWeightedSum χ β x -
        (χ.LFunction 1).re * x ^ (1 - β) / (1 - β) -
        (riemannZeta (β : ℂ) * χ.LFunction (β : ℂ)).re| ≤
      81 * q * (1 + β / (β - 1 / 2)) * x ^ (1 / 2 - β) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hβ0 : 0 ≤ β := by linarith
  have hend :
      |quadraticConvolutionError χ x * x ^ (-β)| ≤
        81 * q * x ^ (1 / 2 - β) := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    calc
      _ ≤ (81 * q * Real.sqrt x) * x ^ (-β) :=
        mul_le_mul_of_nonneg_right
          (IsPrimitive.abs_quadraticConvolutionError_le χ hprim hχ hx)
          (Real.rpow_nonneg hx0.le _)
      _ = _ := by
        rw [mul_assoc, Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
        congr 2
  have htail :
      |β * ∫ t in Set.Ioi x, quadraticConvolutionError χ t * t ^ (-β - 1)| ≤
        β * (81 * q * x ^ (1 / 2 - β) / (β - 1 / 2)) := by
    rw [abs_mul, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left
      (IsPrimitive.abs_quadraticConvolutionError_tail_le χ hprim hχ hβ hx) hβ0
  rw [IsPrimitive.quadraticConvolutionWeightedSum_eq_product_add_tail χ hprim hχ
    hquad hβ hβ1 hx]
  calc
    _ = |quadraticConvolutionError χ x * x ^ (-β) -
        β * ∫ t in Set.Ioi x, quadraticConvolutionError χ t * t ^ (-β - 1)| := by
      congr 1
      ring
    _ ≤ |quadraticConvolutionError χ x * x ^ (-β)| +
        |β * ∫ t in Set.Ioi x, quadraticConvolutionError χ t * t ^ (-β - 1)| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le (quadraticConvolutionError χ x * x ^ (-β)) 0
          (β * ∫ t in Set.Ioi x, quadraticConvolutionError χ t * t ^ (-β - 1))
    _ ≤ 81 * q * x ^ (1 / 2 - β) +
        β * (81 * q * x ^ (1 / 2 - β) / (β - 1 / 2)) := add_le_add hend htail
    _ = _ := by ring

end BombieriVinogradov.Siegel

end

section

/-!
## The real zero
-/

open Complex Finset Filter
open scoped Topology

namespace BombieriVinogradov.Siegel

open DirichletCharacter
variable {q : ℕ} [NeZero q]

omit [NeZero q] in
/-- Since `a(1) = 1` and `a(n) ≥ 0`, the weighted sum is at least `1` for `x ≥ 1`. -/
theorem one_le_quadraticConvolutionWeightedSum
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1)
    (β : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ quadraticConvolutionWeightedSum χ β x := by
  have hcoeff : quadraticSiegelConvolution χ 1 = 1 := by
    unfold quadraticSiegelConvolution
    rw [χ.isMultiplicative_zetaMul.map_one]
    rfl
  calc
    (1 : ℝ) = quadraticSiegelConvolution χ 1 * (1 : ℝ) ^ (-β) := by
      rw [hcoeff, Real.one_rpow, mul_one]
    _ ≤ quadraticConvolutionWeightedSum χ β x := by
      unfold quadraticConvolutionWeightedSum
      simpa only [Nat.cast_one] using Finset.single_le_sum
        (f := fun n : ℕ => quadraticSiegelConvolution χ n * (n : ℝ) ^ (-β))
        (fun n _ => mul_nonneg (quadraticSiegelConvolution_nonneg χ hquad n)
          (Real.rpow_nonneg (Nat.cast_nonneg n) _))
        (mem_Icc.mpr ⟨le_rfl, (Nat.one_le_floor_iff _).mpr hx⟩)

private theorem conductor_cutoff_one_le (q : ℕ) [NeZero q] :
    1 ≤ (648 * (q : ℝ)) ^ (4 : ℕ) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  exact one_le_pow₀ (by linarith : (1 : ℝ) ≤ 648 * q)

/-- At `x = (648 q)^4` the error in the weighted asymptotic is at most `1/2` for all
`β ≥ 3/4`. -/
theorem quadraticConvolution_weighted_error_at_cutoff_le
    {β : ℝ} (hβ : 3 / 4 ≤ β) :
    81 * q * (1 + β / (β - 1 / 2)) *
        ((648 * (q : ℝ)) ^ (4 : ℕ)) ^ (1 / 2 - β) ≤ 1 / 2 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have ha : (0 : ℝ) < 648 * q := by positivity
  have hratio : β / (β - 1 / 2) ≤ 3 :=
    (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hpow :
      ((648 * (q : ℝ)) ^ (4 : ℕ)) ^ (1 / 2 - β) ≤ (648 * (q : ℝ))⁻¹ := by
    calc
      _ ≤ ((648 * (q : ℝ)) ^ (4 : ℕ)) ^ (-1 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (conductor_cutoff_one_le q) (by linarith)
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
        norm_num [Real.rpow_neg_one]
  calc
    _ ≤ (81 * (q : ℝ) * 4) * (648 * (q : ℝ))⁻¹ := by gcongr; linarith
    _ = 1 / 2 := by field_simp; ring

/-- If `0 < ε ≤ 1/4` and `Re L(1, χ) ≤ ε / (4 (648 q)^{4ε})`, then
`Re(ζ(1 - ε) L(1 - ε, χ)) > 0`. -/
theorem IsPrimitive.re_zeta_mul_LFunction_pos_of_small_value
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) {ε : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4)
    (hsmall : (χ.LFunction 1).re ≤
      ε / (4 * (648 * (q : ℝ)) ^ (4 * ε))) :
    0 < (riemannZeta ((1 - ε : ℝ) : ℂ) * χ.LFunction ((1 - ε : ℝ) : ℂ)).re := by
  let x : ℝ := (648 * (q : ℝ)) ^ (4 : ℕ)
  have hx : 1 ≤ x := conductor_cutoff_one_le q
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hpower : x ^ ε = (648 * (q : ℝ)) ^ (4 * ε) := by
    rw [Real.rpow_mul (by positivity)]
    norm_num [x]
  have hmain :
      (χ.LFunction 1).re * x ^ ε / ε ≤ 1 / 4 := by
    have hp : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 ε
    rw [← hpower, le_div_iff₀ (by positivity : 0 < 4 * x ^ ε)] at hsmall
    rw [div_le_iff₀ hε]
    nlinarith only [hsmall]
  have hweight := one_le_quadraticConvolutionWeightedSum χ hquad (1 - ε) hx
  have herr := IsPrimitive.abs_quadraticConvolutionWeightedSum_sub_main_sub_product_le
    χ hprim hχ hquad (β := 1 - ε) (by linarith) (by linarith) hx
  have hpay := quadraticConvolution_weighted_error_at_cutoff_le (q := q)
    (β := 1 - ε) (by linarith)
  have hupper := (le_abs_self _).trans (herr.trans hpay)
  rw [show 1 - (1 - ε) = ε by ring] at hupper
  linarith

/-- `Re ζ(1 - ε) < 0` for all small `ε > 0`, since `(s - 1) ζ(s)` is continuous and equals
`1` at `s = 1`. -/
theorem exists_zeta_negative_left_neighborhood :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 4 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        (riemannZeta ((1 - ε : ℝ) : ℂ)).re < 0 := by
  have hc : Continuous (fun t : ℝ => (riemannZeta₁ (t : ℂ)).re) :=
    Complex.continuous_re.comp (differentiable_riemannZeta₁.continuous.comp
      Complex.continuous_ofReal)
  have he : ∀ᶠ t : ℝ in 𝓝 1, 0 < (riemannZeta₁ (t : ℂ)).re :=
    continuousAt_const.eventually_lt hc.continuousAt (by simp [riemannZeta₁_one])
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨min (r / 2) (1 / 4), lt_min (by positivity) (by norm_num),
    min_le_right _ _, ?_⟩
  intro ε hε hε₀
  have hεr : ε < r := by
    have := hε₀.trans (min_le_left _ _)
    linarith
  have hpos : 0 < (riemannZeta₁ ((1 - ε : ℝ) : ℂ)).re := by
    apply hball
    simpa [Real.dist_eq, abs_of_pos hε] using hεr
  have hs : ((1 - ε : ℝ) : ℂ) ≠ 1 := by
    exact_mod_cast (show 1 - ε ≠ 1 by linarith)
  have hform :
      (riemannZeta ((1 - ε : ℝ) : ℂ)).re =
        (1 - ε - 1)⁻¹ * (riemannZeta₁ ((1 - ε : ℝ) : ℂ)).re := by
    rw [riemannZeta_eq_inv_sub_mul hs]
    have hsub : ((1 - ε : ℝ) : ℂ) - 1 = ((1 - ε - 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [hsub, ← ofReal_inv, re_ofReal_mul]
  rw [hform]
  rw [show 1 - ε - 1 = -ε by ring, inv_neg]
  exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr (inv_pos.mpr hε)) hpos

/-- There is `ε₀ > 0` such that for `0 < ε ≤ ε₀`, every modulus `q` and every primitive
quadratic character `χ ≠ 1` mod `q`, if `Re L(1, χ) ≤ ε / (4 (648 q)^{4ε})` then
`L(β, χ) = 0` for some `β ∈ (1 - ε, 1)`. -/
theorem exists_uniform_small_value_real_zero_neighborhood :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 4 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 →
        (χ.LFunction 1).re ≤ ε / (4 * (648 * (q : ℝ)) ^ (4 * ε)) →
        ∃ β : ℝ, β ∈ Set.Ioo (1 - ε) 1 ∧ χ.LFunction (β : ℂ) = 0 := by
  obtain ⟨ε₀, hε₀, hε₀4, hzeta⟩ := exists_zeta_negative_left_neighborhood
  refine ⟨ε₀, hε₀, hε₀4, ?_⟩
  intro ε hε hεbound q _ χ hprim hχ hquad hsmall
  have hε4 := hεbound.trans hε₀4
  have hLpos := LFunction_apply_one_re_pos_of_sq_eq_one hquad hχ
  have hprod := IsPrimitive.re_zeta_mul_LFunction_pos_of_small_value
    χ hprim hχ hquad hε hε4 hsmall
  have hreal := LFunction_ofReal_im_eq_zero_of_sq_eq_one χ hχ hquad (1 - ε)
    (by linarith)
  rw [mul_re, hreal, mul_zero, sub_zero] at hprod
  have hLneg : (χ.LFunction ((1 - ε : ℝ) : ℂ)).re < 0 :=
    neg_of_mul_pos_right hprod (hzeta ε hε hεbound).le
  have hc : Continuous (fun t : ℝ => (χ.LFunction (t : ℂ)).re) :=
    Complex.continuous_re.comp ((χ.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal)
  obtain ⟨β, hβ, hzero⟩ := intermediate_value_Icc (show 1 - ε ≤ 1 by linarith)
    hc.continuousOn ⟨hLneg.le, by simpa using hLpos.le⟩
  have hβleft : 1 - ε < β := by
    rcases hβ.1.eq_or_lt with h | h
    · rw [← h] at hzero
      linarith
    · exact h
  have hβright : β < 1 := by
    rcases hβ.2.eq_or_lt with h | h
    · rw [h] at hzero
      simp only [ofReal_one] at hzero
      linarith
    · exact h
  refine ⟨β, ⟨hβleft, hβright⟩, ?_⟩
  apply Complex.ext
  · exact hzero
  · exact LFunction_ofReal_im_eq_zero_of_sq_eq_one χ hχ hquad β (by linarith)

end BombieriVinogradov.Siegel

end
