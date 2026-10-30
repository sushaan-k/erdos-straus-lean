import ErdosStraus.BombieriVinogradov.DirichletL.ConditionalSeries
import Mathlib.NumberTheory.LSeries.SumCoeff

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

/-!
# Convolutions of two Dirichlet characters

For quadratic characters `χ, ψ` modulo `q`, the coefficients of
`ζ(s) L(s, χ) L(s, ψ) L(s, χψ)` are nonnegative. For nonprincipal characters `ψ, η` modulo `q`,
the hyperbola method gives `|∑_{n ≤ N} (ψ * η)(n)| ≤ 3 q √N`. By partial summation this
continues `L(s, ψ) L(s, η)` to `Re s > 1/2` as a Mellin integral of the summatory function, and
gives `|L(1, ψ) L(1, η) - ∑_{n ≤ m} (ψ * η)(n) / n| ≤ 9 q / √m`.
-/

section

/-! ## Nonnegative coefficients of `ζ(s) L(s, χ) L(s, ψ) L(s, χψ)` -/

open Complex Finset
open ArithmeticFunction hiding log
open scoped BigOperators ComplexOrder

namespace DirichletCharacter

variable {q : ℕ}

/-- The arithmetic function `1 * χ * ψ * χψ`, with Dirichlet series
`ζ(s) L(s, χ) L(s, ψ) L(s, χψ)`. -/
noncomputable def twoCharacterConvolution
    (χ ψ : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  χ.zetaMul * toArithmeticFunction (ψ ·) * toArithmeticFunction ((χ * ψ) ·)

theorem isMultiplicative_twoCharacterConvolution
    (χ ψ : DirichletCharacter ℂ q) :
    (twoCharacterConvolution χ ψ).IsMultiplicative :=
  (χ.isMultiplicative_zetaMul.mul (isMultiplicative_toArithmeticFunction ψ)).mul
    (isMultiplicative_toArithmeticFunction (χ * ψ))

theorem twoCharacterConvolution_one (χ ψ : DirichletCharacter ℂ q) :
    twoCharacterConvolution χ ψ 1 = 1 :=
  (isMultiplicative_twoCharacterConvolution χ ψ).map_one

theorem twoCharacterConvolution_comm (χ ψ : DirichletCharacter ℂ q) :
    twoCharacterConvolution χ ψ = twoCharacterConvolution ψ χ := by
  unfold twoCharacterConvolution zetaMul
  rw [mul_comm ψ χ]
  ac_rfl

/-- `(ψ * χψ)(n) = ψ(n) (1 * χ)(n)`. -/
theorem character_mul_product_apply
    (χ ψ : DirichletCharacter ℂ q) (n : ℕ) :
    (toArithmeticFunction (ψ ·) * toArithmeticFunction ((χ * ψ) ·)) n =
      ψ n * χ.zetaMul n := by
  rw [zetaMul, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hxprod := (Nat.mem_divisorsAntidiagonal.mp hx).1
  obtain ⟨hx1, hx2⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hx
  simp only [toArithmeticFunction, coe_mk, hx1, hx2, ↓reduceIte,
    natCoe_apply, zeta_apply_ne hx1, Nat.cast_one, one_mul, MulChar.mul_apply]
  rw [← hxprod, Nat.cast_mul, map_mul]
  ring

private lemma twist_zetaMul_prime_pow_nonneg
    {χ ψ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1)
    {p : ℕ} (hψp : 0 ≤ ψ p) (k : ℕ) :
    0 ≤ ψ (p ^ k : ℕ) * χ.zetaMul (p ^ k) := by
  rw [Nat.cast_pow, map_pow]
  exact mul_nonneg (pow_nonneg hψp _) (zetaMul_nonneg hχ _)

set_option backward.isDefEq.respectTransparency.types false in
private lemma twist_zetaMul_prime_pow_nonneg_of_neg_one
    {χ ψ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1)
    {p : ℕ} (hp : p.Prime) (hχp : χ p = -1) (hψp : ψ p = -1)
    (k : ℕ) :
    0 ≤ ψ (p ^ k : ℕ) * χ.zetaMul (p ^ k) := by
  rw [Nat.cast_pow, map_pow, hψp]
  by_cases hk : _root_.Even k
  · rw [hk.neg_one_pow, one_mul]
    exact zetaMul_nonneg hχ _
  · have hk' : _root_.Even (k + 1) := (Nat.not_even_iff_odd.mp hk).add_odd odd_one
    have hz : χ.zetaMul (p ^ k) = 0 := by
      simp only [zetaMul, toArithmeticFunction, coe_zeta_mul_apply, coe_mk,
        Nat.sum_divisors_prime_pow hp, pow_eq_zero_iff', hp.ne_zero, ne_eq,
        false_and, ↓reduceIte, Nat.cast_pow, map_pow, hχp, neg_one_geom_sum,
        if_pos hk']
    rw [hz, mul_zero]

private lemma twoCharacterConvolution_prime_pow_nonneg_of_twist
    {χ ψ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1)
    {p : ℕ} (hp : p.Prime)
    (htwist : ∀ k, 0 ≤ ψ (p ^ k : ℕ) * χ.zetaMul (p ^ k)) (k : ℕ) :
    0 ≤ twoCharacterConvolution χ ψ (p ^ k) := by
  rw [twoCharacterConvolution, mul_assoc, ArithmeticFunction.mul_apply]
  apply Finset.sum_nonneg
  intro x hx
  rw [character_mul_product_apply]
  apply mul_nonneg (zetaMul_nonneg hχ _)
  have hxdvd : x.2 ∣ p ^ k :=
    Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp hxdvd
  rw [hj]
  exact htwist j

/-- Nonnegativity at prime powers. The coefficient at `p^k` is
`∑_{i + j = k} (1 * χ)(p^i) ψ(p^j) (1 * χ)(p^j)`. Each term is nonnegative when `ψ(p) ≥ 0`,
and also when `χ(p) = ψ(p) = -1`, since then `(1 * χ)(p^j) = 0` for odd `j`. The remaining
case follows by exchanging `χ` and `ψ`. -/
theorem twoCharacterConvolution_prime_pow_nonneg
    {χ ψ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 ≤ twoCharacterConvolution χ ψ (p ^ k) := by
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with hχp | hχp | hχp
  · rw [twoCharacterConvolution_comm]
    exact twoCharacterConvolution_prime_pow_nonneg_of_twist hψ hp
      (twist_zetaMul_prime_pow_nonneg hψ (by simp [hχp])) k
  · rw [twoCharacterConvolution_comm]
    exact twoCharacterConvolution_prime_pow_nonneg_of_twist hψ hp
      (twist_zetaMul_prime_pow_nonneg hψ (by simp [hχp])) k
  · apply twoCharacterConvolution_prime_pow_nonneg_of_twist hχ hp
    intro j
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hψ p with hψp | hψp | hψp
    · exact twist_zetaMul_prime_pow_nonneg hχ (by simp [hψp]) j
    · exact twist_zetaMul_prime_pow_nonneg hχ (by simp [hψp]) j
    · exact twist_zetaMul_prime_pow_nonneg_of_neg_one hχ hp hχp hψp j

/-- For quadratic `χ, ψ`, every coefficient of `ζ(s) L(s, χ) L(s, ψ) L(s, χψ)` is a
nonnegative real number, in the order on `ℂ`. -/
theorem twoCharacterConvolution_nonneg
    {χ ψ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (n : ℕ) :
    0 ≤ twoCharacterConvolution χ ψ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, le_refl]
  · simpa only [(isMultiplicative_twoCharacterConvolution χ ψ).multiplicative_factorization
        _ hn] using!
      Finset.prod_nonneg fun p hp =>
        twoCharacterConvolution_prime_pow_nonneg hχ hψ
          (Nat.prime_of_mem_primeFactors hp) _

theorem twoCharacterConvolution_re_nonneg
    {χ ψ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (n : ℕ) :
    0 ≤ (twoCharacterConvolution χ ψ n).re := by
  have h := twoCharacterConvolution_nonneg hχ hψ n
  rw [RCLike.le_iff_re_im] at h
  exact h.1

lemma characterArithmeticFunction_LSeriesSummable
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (toArithmeticFunction (χ ·)) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
  intro n hn
  simpa only [toArithmeticFunction, coe_mk, hn, ↓reduceIte] using norm_le_one χ n

theorem LSeriesSummable_twoCharacterConvolution
    (χ ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (twoCharacterConvolution χ ψ) s :=
  ArithmeticFunction.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_mul (χ.LSeriesSummable_zetaMul hs)
      (characterArithmeticFunction_LSeriesSummable ψ hs))
    (characterArithmeticFunction_LSeriesSummable (χ * ψ) hs)

private lemma characterArithmeticFunction_LSeries
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    LSeries (toArithmeticFunction (χ ·)) s = LSeries (fun n : ℕ => χ n) s :=
  LSeries_congr (fun hn => (χ.apply_eq_toArithmeticFunction_apply hn).symm) s

/-- For `Re s > 1`, the L-series of `1 * χ * ψ * χψ` is `ζ(s)` times the Dirichlet series
of `χ`, `ψ` and `χψ`. This holds for every modulus, including `q = 0`. -/
theorem LSeries_twoCharacterConvolution
    (χ ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (twoCharacterConvolution χ ψ) s =
      riemannZeta s * LSeries (fun n : ℕ => χ n) s *
        LSeries (fun n : ℕ => ψ n) s * LSeries (fun n : ℕ => (χ * ψ) n) s := by
  have hχ := characterArithmeticFunction_LSeriesSummable χ hs
  have hψ := characterArithmeticFunction_LSeriesSummable ψ hs
  have hχψ := characterArithmeticFunction_LSeriesSummable (χ * ψ) hs
  have hζχ := χ.LSeriesSummable_zetaMul hs
  have hζ : LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s :=
    LSeriesSummable_zeta_iff.mpr hs
  have hζvalue : LSeries (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s =
      riemannZeta s := LSeries_zeta_eq_riemannZeta hs
  have hζχvalue : LSeries χ.zetaMul s =
      riemannZeta s * LSeries (fun n : ℕ => χ n) s :=
    (ArithmeticFunction.LSeries_mul' hζ hχ).trans
      (congrArg₂ (· * ·) hζvalue (characterArithmeticFunction_LSeries χ s))
  have hpair : LSeries (χ.zetaMul * toArithmeticFunction (ψ ·) : ArithmeticFunction ℂ) s =
      riemannZeta s * LSeries (fun n : ℕ => χ n) s *
        LSeries (fun n : ℕ => ψ n) s :=
    (ArithmeticFunction.LSeries_mul' hζχ hψ).trans
      (congrArg₂ (· * ·) hζχvalue (characterArithmeticFunction_LSeries ψ s))
  exact (ArithmeticFunction.LSeries_mul'
    (ArithmeticFunction.LSeriesSummable_mul hζχ hψ) hχψ).trans
      (congrArg₂ (· * ·) hpair (characterArithmeticFunction_LSeries (χ * ψ) s))

/-- For `Re s > 1`, the L-series of `1 * χ * ψ * χψ` is
`ζ(s) L(s, χ) L(s, ψ) L(s, χψ)`. -/
theorem LSeries_twoCharacterConvolution_eq_LFunction_product
    [NeZero q] (χ ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (twoCharacterConvolution χ ψ) s =
      riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ * ψ).LFunction s := by
  rw [LSeries_twoCharacterConvolution χ ψ hs, χ.LFunction_eq_LSeries hs,
    ψ.LFunction_eq_LSeries hs, (χ * ψ).LFunction_eq_LSeries hs]

end DirichletCharacter

end

section

/-! ## Partial sums of `ψ * η` by the hyperbola method -/

open Complex Finset
open ArithmeticFunction hiding log
open scoped BigOperators

namespace DirichletCharacter

private lemma sum_Ioc_cutoff_eq_sum_ite {A : Type*} [AddCommMonoid A]
    (F : ℕ → A) {m N : ℕ} (hm : m ≤ N) :
    (∑ a ∈ Ioc 0 m, F a) = ∑ a ∈ Ioc 0 N, if a ≤ m then F a else 0 := by
  classical
  rw [← sum_filter]
  congr 1
  ext a
  simp only [mem_filter, mem_Ioc]
  omega

private lemma hyperbola_arm_eq_sum_ite (f g : ℕ → ℂ)
    {m N : ℕ} (hm : m ≤ N) :
    (∑ a ∈ Ioc 0 m, f a * ∑ b ∈ Ioc 0 (N / a), g b) =
      ∑ a ∈ Ioc 0 N, ∑ b ∈ Ioc 0 N,
        if a ≤ m ∧ a * b ≤ N then f a * g b else 0 := by
  rw [sum_Ioc_cutoff_eq_sum_ite _ hm]
  apply sum_congr rfl
  intro a ha
  have ha0 := (mem_Ioc.mp ha).1
  rw [sum_Ioc_cutoff_eq_sum_ite g (Nat.div_le_self N a)]
  by_cases ham : a ≤ m
  · simp only [ham, true_and, ↓reduceIte, mul_sum]
    apply sum_congr rfl
    intro b _
    have hdiv : b ≤ N / a ↔ a * b ≤ N := by
      rw [Nat.le_div_iff_mul_le ha0, Nat.mul_comm]
    by_cases hab : a * b ≤ N <;> simp [hdiv, hab]
  · simp [ham]

private lemma hyperbola_square_eq_sum_ite (f g : ℕ → ℂ)
    {m N : ℕ} (hm : m ≤ N) :
    (∑ a ∈ Ioc 0 m, f a) * (∑ b ∈ Ioc 0 m, g b) =
      ∑ a ∈ Ioc 0 N, ∑ b ∈ Ioc 0 N,
        if a ≤ m ∧ b ≤ m then f a * g b else 0 := by
  rw [sum_Ioc_cutoff_eq_sum_ite f hm, sum_Ioc_cutoff_eq_sum_ite g hm,
    sum_mul]
  apply sum_congr rfl
  intro a _
  rw [mul_sum]
  apply sum_congr rfl
  intro b _
  by_cases ha : a ≤ m <;> by_cases hb : b ≤ m <;> simp [ha, hb]

/-- Dirichlet's hyperbola identity for `∑_{n ≤ N} (f * g)(n)`, split at `⌊√N⌋`. -/
theorem sum_Ioc_convolution_eq_sqrt_hyperbola
    (f g : ArithmeticFunction ℂ) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (f * g) n) =
      (∑ a ∈ Ioc 0 N.sqrt, f a * ∑ b ∈ Ioc 0 (N / a), g b) +
      (∑ b ∈ Ioc 0 N.sqrt, g b * ∑ a ∈ Ioc 0 (N / b), f a) -
      (∑ a ∈ Ioc 0 N.sqrt, f a) * (∑ b ∈ Ioc 0 N.sqrt, g b) := by
  rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter, sum_filter, sum_product,
    hyperbola_arm_eq_sum_ite f g (Nat.sqrt_le_self N),
    hyperbola_arm_eq_sum_ite g f (Nat.sqrt_le_self N),
    hyperbola_square_eq_sum_ite f g (Nat.sqrt_le_self N)]
  rw [sum_comm (f := fun b a =>
    if b ≤ N.sqrt ∧ b * a ≤ N then g b * f a else 0)]
  rw [← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro a _
  rw [← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro b _
  have hsmall : a ≤ N.sqrt → b ≤ N.sqrt → a * b ≤ N := by
    intro ha hb
    exact (Nat.mul_le_mul ha hb).trans (Nat.sqrt_le N)
  have hlarge : ¬a ≤ N.sqrt → ¬b ≤ N.sqrt → ¬a * b ≤ N := by
    intro ha hb hab
    have h := Nat.mul_le_mul (by omega : N.sqrt.succ ≤ a)
      (by omega : N.sqrt.succ ≤ b)
    exact (Nat.not_le_of_gt (Nat.lt_succ_sqrt N)) (h.trans hab)
  by_cases ha : a ≤ N.sqrt <;> by_cases hb : b ≤ N.sqrt <;>
    by_cases hab : a * b ≤ N <;>
    simp [ha, hb, hab, mul_comm] <;> aesop

variable {q : ℕ}

/-- For nonprincipal `χ` modulo `q`, `|∑_{n ≤ N} χ(n)| ≤ min(N, q)`. -/
theorem norm_sum_Ioc_character_le_min [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Ioc 0 N, χ n‖ ≤ min (N : ℝ) q := by
  apply le_min
  · calc
      ‖∑ n ∈ Ioc 0 N, χ n‖ ≤ ∑ n ∈ Ioc 0 N, ‖χ n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Ioc 0 N, (1 : ℝ) :=
        sum_le_sum fun n _ => norm_le_one χ n
      _ = N := by simp
  · have hz : χ (0 : ZMod q) = 0 :=
      χ.map_zero' (fun hq => hχ (χ.level_one' hq))
    have hsum : (∑ n ∈ Ioc 0 N, χ n) = ∑ n ∈ range (N + 1), χ n := by
      simpa only [Nat.range_succ_eq_Icc_zero, Nat.cast_zero, hz, add_zero] using
        (sum_Ioc_add_eq_sum_Icc (f := fun n : ℕ => χ n) (Nat.zero_le N))
    rw [hsum]
    exact BombieriVinogradov.WeakStrip.norm_sum_range_character_le_modulus χ hχ (N + 1)

lemma sum_Ioc_characterArithmeticFunction
    (χ : DirichletCharacter ℂ q) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, toArithmeticFunction (χ ·) n) =
      ∑ n ∈ Ioc 0 N, χ n :=
  sum_congr rfl fun _n hn =>
    (χ.apply_eq_toArithmeticFunction_apply (Nat.ne_of_gt (mem_Ioc.mp hn).1)).symm

private lemma norm_character_hyperbola_arm_le [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (N m : ℕ) :
    ‖∑ a ∈ Ioc 0 m, toArithmeticFunction (χ ·) a *
        ∑ b ∈ Ioc 0 (N / a), toArithmeticFunction (ψ ·) b‖ ≤ (m : ℝ) * q := by
  calc
    _ ≤ ∑ a ∈ Ioc 0 m, ‖toArithmeticFunction (χ ·) a *
        ∑ b ∈ Ioc 0 (N / a), toArithmeticFunction (ψ ·) b‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ Ioc 0 m, (q : ℝ) := by
      apply sum_le_sum
      intro a ha
      rw [norm_mul, sum_Ioc_characterArithmeticFunction,
        ← χ.apply_eq_toArithmeticFunction_apply (Nat.ne_of_gt (mem_Ioc.mp ha).1)]
      calc
        ‖χ a‖ * ‖∑ b ∈ Ioc 0 (N / a), ψ b‖ ≤ 1 * (q : ℝ) :=
          mul_le_mul (norm_le_one χ a)
            ((norm_sum_Ioc_character_le_min ψ hψ _).trans (min_le_right _ _))
            (norm_nonneg _) (by norm_num)
        _ = q := one_mul _
    _ = (m : ℝ) * q := by simp

/-- For nonprincipal `ψ, η` modulo `q`, `|∑_{n ≤ N} (ψ * η)(n)| ≤ 3 q ⌊√N⌋`. Each of the
three terms of the hyperbola identity is at most `q ⌊√N⌋`; in the product term one factor
is bounded by its length and the other by `q`. -/
theorem norm_sum_Ioc_pair_convolution_le [NeZero q]
    (ψ η : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hη : η ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Ioc 0 N,
      (toArithmeticFunction (ψ ·) * toArithmeticFunction (η ·)) n‖ ≤
      3 * (q : ℝ) * N.sqrt := by
  rw [sum_Ioc_convolution_eq_sqrt_hyperbola]
  have hoverlap :
      ‖(∑ a ∈ Ioc 0 N.sqrt, toArithmeticFunction (ψ ·) a) *
        (∑ b ∈ Ioc 0 N.sqrt, toArithmeticFunction (η ·) b)‖ ≤
        (N.sqrt : ℝ) * q := by
    rw [norm_mul, sum_Ioc_characterArithmeticFunction, sum_Ioc_characterArithmeticFunction]
    exact mul_le_mul
      ((norm_sum_Ioc_character_le_min ψ hψ _).trans (min_le_left _ _))
      ((norm_sum_Ioc_character_le_min η hη _).trans (min_le_right _ _))
      (norm_nonneg _) (by positivity)
  calc
    _ ≤ ‖∑ a ∈ Ioc 0 N.sqrt, toArithmeticFunction (ψ ·) a *
          ∑ b ∈ Ioc 0 (N / a), toArithmeticFunction (η ·) b‖ +
        ‖∑ b ∈ Ioc 0 N.sqrt, toArithmeticFunction (η ·) b *
          ∑ a ∈ Ioc 0 (N / b), toArithmeticFunction (ψ ·) a‖ +
        ‖(∑ a ∈ Ioc 0 N.sqrt, toArithmeticFunction (ψ ·) a) *
          (∑ b ∈ Ioc 0 N.sqrt, toArithmeticFunction (η ·) b)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (N.sqrt : ℝ) * q + (N.sqrt : ℝ) * q + (N.sqrt : ℝ) * q :=
      add_le_add
        (add_le_add (norm_character_hyperbola_arm_le ψ η hη _ _)
          (norm_character_hyperbola_arm_le η ψ hψ _ _)) hoverlap
    _ = 3 * (q : ℝ) * N.sqrt := by ring

/-- The same bound with `√N` in place of `⌊√N⌋`. -/
theorem norm_sum_Icc_character_pair_convolution_le_three_mul_sqrt [NeZero q]
    (ψ η : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hη : η ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N,
      (toArithmeticFunction (ψ ·) * toArithmeticFunction (η ·)) n‖ ≤
      3 * (q : ℝ) * Real.sqrt N := by
  rw [show Icc 1 N = Ioc 0 N from Icc_succ_left_eq_Ioc _ _]
  refine (norm_sum_Ioc_pair_convolution_le
    ψ η hψ hη N).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.le_sqrt_of_sq_le
  exact_mod_cast (show N.sqrt ^ 2 ≤ N by simpa only [pow_two] using Nat.sqrt_le N)

/-- The same bound at a real endpoint: `|∑_{n ≤ X} (ψ * η)(n)| ≤ 3 q √X` for `X ≥ 0`. -/
theorem norm_sum_Icc_floor_pair_convolution_le [NeZero q]
    (ψ η : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hη : η ≠ 1)
    {X : ℝ} (hX : 0 ≤ X) :
    ‖∑ n ∈ Icc 1 ⌊X⌋₊,
      (toArithmeticFunction (ψ ·) * toArithmeticFunction (η ·)) n‖ ≤
      3 * (q : ℝ) * Real.sqrt X := by
  refine (norm_sum_Icc_character_pair_convolution_le_three_mul_sqrt
    ψ η hψ hη ⌊X⌋₊).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.floor_le hX)) (by positivity)

end DirichletCharacter

end

section

/-! ## Continuation of `L(s, ψ) L(s, η)` to `Re s > 1/2` -/

open Complex Finset Filter MeasureTheory Set Asymptotics
open scoped Topology

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

/-- The summatory function `S(t) = ∑_{n ≤ t} (ψ * η)(n)`. -/
noncomputable def characterPairSummatory (ψ η : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊t⌋₊,
    (toArithmeticFunction (ψ ·) * toArithmeticFunction (η ·)) n

/-- The integrand `S(t) t^{-s-1}`. -/
noncomputable def characterPairKernel
    (ψ η : DirichletCharacter ℂ q) (s : ℂ) (t : ℝ) : ℂ :=
  characterPairSummatory ψ η t * (t : ℂ) ^ (-(s + 1))

/-- `∫_1^∞ S(t) t^{-s-1} dt`, which converges for `Re s > 1/2`. -/
noncomputable def characterPairIntegral
    (ψ η : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), characterPairKernel ψ η s t

/-- `S(t)` for `t > 1` and `0` otherwise; its Mellin transform at `-s` is
`∫_1^∞ S(t) t^{-s-1} dt`. -/
noncomputable def characterPairCutoff (ψ η : DirichletCharacter ℂ q) : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator (characterPairSummatory ψ η)

omit [NeZero q] in
theorem measurable_characterPairSummatory (ψ η : DirichletCharacter ℂ q) :
    Measurable (characterPairSummatory ψ η) :=
  (StronglyMeasurable.of_discrete (f := fun N : ℕ =>
    ∑ n ∈ Finset.Icc 1 N,
      (toArithmeticFunction (ψ ·) * toArithmeticFunction (η ·)) n)).measurable.comp
        measurable_id.nat_floor

omit [NeZero q] in
theorem measurable_characterPairCutoff (ψ η : DirichletCharacter ℂ q) :
    Measurable (characterPairCutoff ψ η) :=
  (measurable_characterPairSummatory ψ η).indicator measurableSet_Ioi

theorem norm_characterPairCutoff_le (ψ η : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (hη : η ≠ 1) (t : ℝ) :
    ‖characterPairCutoff ψ η t‖ ≤ 3 * q * Real.sqrt t := by
  by_cases ht : 1 < t
  · simpa [characterPairCutoff, characterPairSummatory, ht] using
      norm_sum_Icc_floor_pair_convolution_le ψ η hψ hη
        (show 0 ≤ t by linarith)
  · simp [characterPairCutoff, ht]
    positivity

theorem locallyIntegrable_characterPairCutoff (ψ η : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (hη : η ≠ 1) :
    LocallyIntegrable (characterPairCutoff ψ η) := by
  refine (show Continuous (fun t : ℝ => 3 * (q : ℝ) * Real.sqrt t) by
    fun_prop).locallyIntegrable.mono
      (measurable_characterPairCutoff ψ η).aestronglyMeasurable ?_
  filter_upwards [] with t
  exact (norm_characterPairCutoff_le ψ η hψ hη t).trans (Real.le_norm_self _)

theorem characterPairCutoff_isBigO_atTop (ψ η : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (hη : η ≠ 1) :
    characterPairCutoff ψ η =O[atTop] (fun t : ℝ => t ^ (1 / 2 : ℝ)) := by
  refine isBigO_iff.mpr ⟨3 * q, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simpa [Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht _)]
    using norm_characterPairCutoff_le ψ η hψ hη t

omit [NeZero q] in
theorem characterPairCutoff_isBigO_zero (ψ η : DirichletCharacter ℂ q) (b : ℝ) :
    characterPairCutoff ψ η =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ b) := by
  refine isBigO_iff.mpr ⟨0, ?_⟩
  filter_upwards [((eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
    nhdsWithin_le_nhds)] with t ht
  simp [characterPairCutoff, not_lt.mpr ht.le]

omit [NeZero q] in
private theorem characterPair_cutoff_mellin_kernel
    (ψ η : DirichletCharacter ℂ q) (s : ℂ) :
    (fun t : ℝ => (t : ℂ) ^ (-s - 1) • characterPairCutoff ψ η t) =
      (Ioi (1 : ℝ)).indicator (characterPairKernel ψ η s) := by
  funext t
  by_cases ht : 1 < t
  · simp [characterPairCutoff, characterPairKernel, ht,
      smul_eq_mul, sub_eq_add_neg, mul_comm, add_comm]
  · simp [characterPairCutoff, ht]

omit [NeZero q] in
theorem mellin_characterPairCutoff (ψ η : DirichletCharacter ℂ q) (s : ℂ) :
    mellin (characterPairCutoff ψ η) (-s) = characterPairIntegral ψ η s := by
  rw [mellin, characterPair_cutoff_mellin_kernel, setIntegral_indicator measurableSet_Ioi]
  simp only [Ioi_inter_Ioi, max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)]
  rfl

theorem mellinConvergent_characterPairCutoff (ψ η : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (hη : η ≠ 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    MellinConvergent (characterPairCutoff ψ η) (-s) := by
  apply mellinConvergent_of_isBigO_rpow
    ((locallyIntegrable_characterPairCutoff ψ η hψ hη).locallyIntegrableOn _)
    (a := -(1 / 2)) (b := -s.re - 1)
  · simpa using characterPairCutoff_isBigO_atTop ψ η hψ hη
  · simp only [neg_re]; linarith
  · exact characterPairCutoff_isBigO_zero ψ η _
  · simp only [neg_re]; linarith

theorem integrableOn_characterPairKernel (ψ η : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (hη : η ≠ 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    IntegrableOn (characterPairKernel ψ η s) (Ioi (1 : ℝ)) := by
  have h := mellinConvergent_characterPairCutoff ψ η hψ hη hs
  rw [MellinConvergent, characterPair_cutoff_mellin_kernel,
    integrableOn_indicator_iff measurableSet_Ioi] at h
  simpa only [Ioi_inter_Ioi, max_eq_left (show (0 : ℝ) ≤ 1 by norm_num)] using h

theorem differentiableAt_characterPairIntegral (ψ η : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (hη : η ≠ 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (characterPairIntegral ψ η) s := by
  have hm : DifferentiableAt ℂ (mellin (characterPairCutoff ψ η)) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow
      ((locallyIntegrable_characterPairCutoff ψ η hψ hη).locallyIntegrableOn _)
      (a := -(1 / 2)) (b := -s.re - 1)
    · simpa using characterPairCutoff_isBigO_atTop ψ η hψ hη
    · simp only [neg_re]; linarith
    · exact characterPairCutoff_isBigO_zero ψ η _
    · simp only [neg_re]; linarith
  simpa only [Function.comp_def, mellin_characterPairCutoff] using
    hm.comp s differentiableAt_id.neg

private theorem characterPair_sum_isBigO (ψ η : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (hη : η ≠ 1) :
    (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N,
      (toArithmeticFunction (ψ ·) * toArithmeticFunction (η ·)) n) =O[atTop]
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ)) := by
  refine isBigO_iff.mpr ⟨3 * q, Eventually.of_forall fun N => ?_⟩
  simpa [Real.sqrt_eq_rpow, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)] using
      norm_sum_Icc_character_pair_convolution_le_three_mul_sqrt ψ η hψ hη N

omit [NeZero q] in
private theorem characterPair_factor_summable (ψ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (toArithmeticFunction (ψ ·)) s := by
  exact DirichletCharacter.characterArithmeticFunction_LSeriesSummable ψ hs

private theorem characterPair_factor_LSeries (ψ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (toArithmeticFunction (ψ ·)) s = ψ.LFunction s := by
  rw [ψ.LFunction_eq_LSeries hs]
  exact LSeries_congr (fun hn => (ψ.apply_eq_toArithmeticFunction_apply hn).symm) s

set_option maxHeartbeats 800000 in
/-- For `Re s > 1`, `L(s, ψ) L(s, η) = s ∫_1^∞ S(t) t^{-s-1} dt` by partial summation. -/
theorem LFunction_mul_eq_characterPairIntegral_of_one_lt_re
    (ψ η : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hη : η ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    ψ.LFunction s * η.LFunction s = s * characterPairIntegral ψ η s := by
  have hψs := characterPair_factor_summable ψ hs
  have hηs := characterPair_factor_summable η hs
  have hid := LSeries_eq_mul_integral
    (toArithmeticFunction (ψ ·) * toArithmeticFunction (η ·) : ArithmeticFunction ℂ)
    (r := 1 / 2) (by norm_num) (by linarith : 1 / 2 < s.re)
    (ArithmeticFunction.LSeriesSummable_mul hψs hηs)
    (characterPair_sum_isBigO ψ η hψ hη)
  rw [ArithmeticFunction.LSeries_mul' hψs hηs,
    characterPair_factor_LSeries ψ hs, characterPair_factor_LSeries η hs] at hid
  exact hid

/-- For nonprincipal `ψ, η` and `Re s > 1/2`, `L(s, ψ) L(s, η) = s ∫_1^∞ S(t) t^{-s-1} dt`.
Both sides are holomorphic on `Re s > 1/2` and agree for `Re s > 1`. -/
theorem LFunction_mul_eq_characterPairIntegral
    (ψ η : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hη : η ≠ 1)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    ψ.LFunction s * η.LFunction s = s * characterPairIntegral ψ η s := by
  let U : Set ℂ := {z | 1 / 2 < z.re}
  let F : ℂ → ℂ := fun z => z * characterPairIntegral ψ η z
  let G : ℂ → ℂ := fun z => ψ.LFunction z * η.LFunction z
  have hUopen : IsOpen U := continuous_re.isOpen_preimage _ isOpen_Ioi
  have hFdiff : DifferentiableOn ℂ F U := by
    intro z hz
    exact (differentiableAt_id.mul
      (differentiableAt_characterPairIntegral ψ η hψ hη hz)).differentiableWithinAt
  have hF : AnalyticOnNhd ℂ F U := hFdiff.analyticOnNhd hUopen
  have hG : AnalyticOnNhd ℂ G U :=
    ((ψ.differentiable_LFunction hψ).mul (η.differentiable_LFunction hη)).differentiableOn
      |>.analyticOnNhd hUopen
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have htwo : (2 : ℂ) ∈ U := by norm_num [U]
  have hevent : G =ᶠ[𝓝 (2 : ℂ)] F := by
    have hone : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
    filter_upwards [hone] with z hz
    exact LFunction_mul_eq_characterPairIntegral_of_one_lt_re ψ η hψ hη hz
  exact hG.eqOn_of_preconnected_of_eventuallyEq hF hpre htwo hevent hs

/-- `L(1, ψ) L(1, η) = ∫_1^∞ S(t) t^{-2} dt`. -/
theorem LFunction_one_mul_eq_characterPairIntegral
    (ψ η : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hη : η ≠ 1) :
    ψ.LFunction 1 * η.LFunction 1 = characterPairIntegral ψ η 1 := by
  simpa using LFunction_mul_eq_characterPairIntegral ψ η hψ hη
    (s := 1) (by norm_num)

end DirichletCharacter

end

section

/-! ## Partial sums of `(ψ * η)(n) / n` -/

open Complex Finset Filter MeasureTheory Set
open scoped Topology

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
private theorem sum_Icc_zero_eq_sum_Icc_one (f : ArithmeticFunction ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 0 N, f n) = ∑ n ∈ Finset.Icc 1 N, f n := by
  rw [← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le N), Finset.sum_insert]
  · simp
  · simp

omit [NeZero q] in
private theorem characterPair_abel (ψ η : DirichletCharacter ℂ q) (m : ℕ) :
    (∑ n ∈ Finset.Icc 1 m,
      (toArithmeticFunction (ψ ·) * toArithmeticFunction (η ·)) n / (n : ℂ)) =
      characterPairSummatory ψ η m / (m : ℂ) +
        ∫ t in Ioc (1 : ℝ) m, characterPairKernel ψ η 1 t := by
  let c : ArithmeticFunction ℂ :=
    toArithmeticFunction (ψ ·) * toArithmeticFunction (η ·)
  let f : ℝ → ℂ := fun t => (t : ℂ) ^ (-1 : ℂ)
  have hderiv (t : ℝ) (ht : 0 < t) :
      deriv f t = -((t : ℂ) ^ (-(1 + 1 : ℂ))) := by
    rw [show deriv f t = deriv (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ)) t from rfl,
      deriv_ofReal_cpow_const ht.ne' (by norm_num)]
    norm_num
  have hdiff (t : ℝ) (ht : t ∈ Set.Icc 1 (m : ℝ)) :
      DifferentiableAt ℝ f t :=
    differentiableAt_id.ofReal_cpow_const (by dsimp; linarith [ht.1]) (by norm_num)
  have hint : IntegrableOn (deriv f) (Set.Icc 1 (m : ℝ)) := by
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.congr
      (f := fun t : ℝ => -((t : ℂ) ^ (-(1 + 1 : ℂ))))
    · intro t ht
      exact (continuousAt_ofReal_cpow_const _ _ (Or.inr (by linarith [ht.1]))).neg.continuousWithinAt
    · intro t ht
      exact hderiv t (by linarith [ht.1])
  have h := sum_mul_eq_sub_integral_mul₀' (c := (c : ℕ → ℂ))
    c.map_zero m hdiff hint
  have hsum :
      (∑ n ∈ Finset.Icc 0 m, f n * c n) =
        ∑ n ∈ Finset.Icc 1 m, c n / (n : ℂ) := by
    rw [← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le m), Finset.sum_insert]
    · simp only [ArithmeticFunction.map_zero, mul_zero, zero_add]
      apply sum_congr rfl
      intro n _
      simp [f, cpow_neg_one, div_eq_mul_inv, mul_comm]
    · simp
  have hint_eq :
      (∫ t in Ioc (1 : ℝ) m, deriv f t * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) =
        -(∫ t in Ioc (1 : ℝ) m, characterPairKernel ψ η 1 t) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [hderiv t (by linarith [ht.1]), sum_Icc_zero_eq_sum_Icc_one]
    simp [characterPairKernel, characterPairSummatory, c, mul_comm]
  rw [hsum, sum_Icc_zero_eq_sum_Icc_one, hint_eq, sub_neg_eq_add] at h
  simpa only [f, cpow_neg_one, characterPairSummatory, Nat.floor_natCast, ofReal_natCast,
    div_eq_mul_inv, mul_comm, c] using h

/-- `L(1, ψ) L(1, η) - ∑_{n ≤ m} (ψ * η)(n) / n = ∫_m^∞ S(t) t^{-2} dt - S(m) / m`, by
partial summation. -/
theorem LFunction_one_mul_sub_characterPair_harmonic_eq
    (ψ η : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hη : η ≠ 1)
    {m : ℕ} (hm : 1 ≤ m) :
    ψ.LFunction 1 * η.LFunction 1 -
      (∑ n ∈ Finset.Icc 1 m,
        (toArithmeticFunction (ψ ·) * toArithmeticFunction (η ·)) n / (n : ℂ)) =
      (∫ t in Ioi (m : ℝ), characterPairKernel ψ η 1 t) -
        characterPairSummatory ψ η m / (m : ℂ) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hi := integrableOn_characterPairKernel ψ η hψ hη (s := 1) (by norm_num)
  have hsplit : characterPairIntegral ψ η 1 =
      (∫ t in Ioc (1 : ℝ) m, characterPairKernel ψ η 1 t) +
        ∫ t in Ioi (m : ℝ), characterPairKernel ψ η 1 t := by
    have hunion : Ioc (1 : ℝ) m ∪ Ioi (m : ℝ) = Ioi (1 : ℝ) :=
      Ioc_union_Ioi_eq_Ioi hmR
    have hdisj : Disjoint (Ioc (1 : ℝ) m) (Ioi (m : ℝ)) :=
      Ioc_disjoint_Ioi_same
    unfold characterPairIntegral
    rw [← hunion]
    exact setIntegral_union hdisj measurableSet_Ioi
      (hi.mono_set fun _ ht => ht.1) (hi.mono_set (Ioi_subset_Ioi hmR))
  rw [LFunction_one_mul_eq_characterPairIntegral ψ η hψ hη,
    characterPair_abel ψ η, hsplit]
  ring

theorem norm_characterPairKernel_one_le (ψ η : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (hη : η ≠ 1) {t : ℝ} (ht : 0 < t) :
    ‖characterPairKernel ψ η 1 t‖ ≤ 3 * q * t ^ (-3 / 2 : ℝ) := by
  rw [characterPairKernel, norm_mul, norm_cpow_eq_rpow_re_of_pos ht]
  have hb := norm_sum_Icc_floor_pair_convolution_le
    ψ η hψ hη ht.le
  calc
    _ ≤ (3 * q * Real.sqrt t) * t ^ (-(1 + 1 : ℂ)).re :=
      mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg ht.le _)
    _ = _ := by
      rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add ht]
      norm_num

/-- `|∫_x^∞ S(t) t^{-2} dt| ≤ 6 q / √x`, from `|S(t)| ≤ 3 q √t`. -/
theorem norm_integral_Ioi_characterPairKernel_one_le
    (ψ η : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hη : η ≠ 1)
    {x : ℝ} (hx : 0 < x) :
    ‖∫ t in Ioi x, characterPairKernel ψ η 1 t‖ ≤ 6 * q / Real.sqrt x := by
  calc
    _ ≤ ∫ t in Ioi x, 3 * (q : ℝ) * t ^ (-3 / 2 : ℝ) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) hx).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact norm_characterPairKernel_one_le ψ η hψ hη (hx.trans ht)
    _ = 6 * q / Real.sqrt x := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hx]
      norm_num
      rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
      ring

/-- For nonprincipal `ψ, η` modulo `q` and `m ≥ 1`,
`|L(1, ψ) L(1, η) - ∑_{n ≤ m} (ψ * η)(n) / n| ≤ 9 q / √m`. -/
theorem norm_LFunction_one_mul_sub_characterPair_harmonic_le
    (ψ η : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hη : η ≠ 1)
    {m : ℕ} (hm : 1 ≤ m) :
    ‖ψ.LFunction 1 * η.LFunction 1 -
      (∑ n ∈ Finset.Icc 1 m,
        (toArithmeticFunction (ψ ·) * toArithmeticFunction (η ·)) n / (n : ℂ))‖ ≤
      9 * q / Real.sqrt m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
  have hb : ‖characterPairSummatory ψ η m / (m : ℂ)‖ ≤ 3 * q / Real.sqrt m := by
    rw [norm_div, Complex.norm_natCast]
    calc
      _ ≤ (3 * q * Real.sqrt m) / m := by
        apply div_le_div_of_nonneg_right _ hmR.le
        simpa [characterPairSummatory] using
          norm_sum_Icc_character_pair_convolution_le_three_mul_sqrt ψ η hψ hη m
      _ = 3 * q / Real.sqrt m := by
        rw [div_eq_div_iff (ne_of_gt hmR) (ne_of_gt hs)]
        nlinarith [Real.sq_sqrt hmR.le]
  rw [LFunction_one_mul_sub_characterPair_harmonic_eq ψ η hψ hη hm]
  calc
    _ ≤ ‖∫ t in Ioi (m : ℝ), characterPairKernel ψ η 1 t‖ +
        ‖characterPairSummatory ψ η m / (m : ℂ)‖ := norm_sub_le _ _
    _ ≤ 6 * q / Real.sqrt m + 3 * q / Real.sqrt m :=
      add_le_add (norm_integral_Ioi_characterPairKernel_one_le ψ η hψ hη hmR) hb
    _ = 9 * q / Real.sqrt m := by ring

end DirichletCharacter

end
