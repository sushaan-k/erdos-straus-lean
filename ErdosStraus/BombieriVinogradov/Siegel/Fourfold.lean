import ErdosStraus.BombieriVinogradov.Siegel.CharacterPair
import ErdosStraus.BombieriVinogradov.Siegel.RealZero
import ErdosStraus.BombieriVinogradov.DirichletL.Bounds

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

/-!
# The product `ζ(s) L(s, χ) L(s, ψ) L(s, χψ)` and a lower bound for its residue

For nonprincipal characters `χ`, `ψ` modulo `q` with `χ` quadratic and `χψ` nonprincipal, let
`a(n)` be the coefficients of `ζ(s) L(s, χ) L(s, ψ) L(s, χψ)`. The hyperbola method gives
`∑_{n ≤ N} a(n) = N L(1, χ) L(1, ψ) L(1, χψ) + O(q² N^{3/4})`, which continues the product to
`Re s > 3/4`. When `ψ` is also quadratic and one of the three L-functions vanishes at a real
`β ∈ [7/8, 1)`, positivity of `a(n)` gives
`Re (L(1, χ) L(1, ψ) L(1, χψ)) ≥ (1 - β) / (2 x^{1-β})` with `x = (5000 q³)^8`.
-/

section

/-! ## Partial sums of `1 * χ` -/

open Complex Finset
open scoped ComplexOrder

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
private theorem sum_Ioc_characterAF (χ : DirichletCharacter ℂ q) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, toArithmeticFunction (χ ·) n) = ∑ n ∈ Ioc 0 N, χ n :=
  DirichletCharacter.sum_Ioc_characterArithmeticFunction χ N

private theorem sum_Ioc_zeta (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) = N := by
  calc
    _ = ∑ _n ∈ Ioc 0 N, (1 : ℂ) := by
      apply sum_congr rfl
      intro n hn
      simp [ArithmeticFunction.zeta_apply_ne (Nat.ne_of_gt (mem_Ioc.mp hn).1)]
    _ = N := by simp

omit [NeZero q] in
/-- The hyperbola identity for `∑_{n ≤ N} (1 * χ)(n)`, split at `√N`. -/
theorem sum_Ioc_zetaMul_eq_sqrt_hyperbola (χ : DirichletCharacter ℂ q) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, χ.zetaMul n) =
      (∑ a ∈ Ioc 0 N.sqrt, χ a * ((N / a : ℕ) : ℂ)) +
      (∑ b ∈ Ioc 0 N.sqrt, ∑ a ∈ Ioc 0 (N / b), χ a) -
      (N.sqrt : ℂ) * (∑ a ∈ Ioc 0 N.sqrt, χ a) := by
  rw [zetaMul, sum_Ioc_convolution_eq_sqrt_hyperbola]
  simp_rw [sum_Ioc_characterAF, sum_Ioc_zeta]
  have hζ : (∑ a ∈ Ioc 0 N.sqrt,
      (ArithmeticFunction.zeta : ArithmeticFunction ℂ) a * ∑ b ∈ Ioc 0 (N / a), χ b) =
      ∑ a ∈ Ioc 0 N.sqrt, ∑ b ∈ Ioc 0 (N / a), χ b := by
    apply sum_congr rfl
    intro a ha
    simp [ArithmeticFunction.zeta_apply_ne (Nat.ne_of_gt (mem_Ioc.mp ha).1)]
  rw [hζ]
  have hχ : (∑ b ∈ Ioc 0 N.sqrt,
      toArithmeticFunction (χ ·) b * ((N / b : ℕ) : ℂ)) =
      ∑ b ∈ Ioc 0 N.sqrt, χ b * ((N / b : ℕ) : ℂ) := by
    apply sum_congr rfl
    intro b hb
    rw [← χ.apply_eq_toArithmeticFunction_apply (Nat.ne_of_gt (mem_Ioc.mp hb).1)]
  rw [hχ, add_comm]

theorem norm_LFunction_one_sub_sum_Ioc_div_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (m : ℕ) :
    ‖χ.LFunction 1 - ∑ n ∈ Ioc 0 m, χ n / (n : ℂ)‖ ≤
      2 * q / (m + 1 : ℝ) := by
  have h := norm_LFunction_one_sub_harmonic_sum_le χ hχ (m := m + 1) (by omega)
  have hsum : (∑ n ∈ range (m + 1),
      BombieriVinogradov.AbelWeight.cpowWeight (1 : ℂ) n * χ n) =
      ∑ n ∈ Ioc 0 m, χ n / (n : ℂ) := by
    rw [Nat.range_succ_eq_Icc_zero, ← insert_Icc_add_one_left_eq_Icc (Nat.zero_le m),
      sum_insert (by simp)]
    simp only [BombieriVinogradov.AbelWeight.cpowWeight, cpow_neg_one,
      Nat.cast_zero, ofReal_zero, inv_zero, zero_mul, zero_add, ofReal_natCast]
    rw [show Icc 1 m = Ioc 0 m from Icc_succ_left_eq_Ioc _ _]
    apply sum_congr rfl
    intro n _
    simp [div_eq_mul_inv, mul_comm]
  rw [hsum] at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- In the hyperbola identity each character sum is at most `q` in absolute value and each
floor error is at most `1`. -/
theorem norm_sum_Ioc_zetaMul_sub_harmonic_main_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖(∑ n ∈ Ioc 0 N, χ.zetaMul n) -
      (N : ℂ) * ∑ n ∈ Ioc 0 N.sqrt, χ n / (n : ℂ)‖ ≤
      3 * q * (N.sqrt : ℝ) := by
  have hfloor :
      ‖∑ a ∈ Ioc 0 N.sqrt,
        (χ a * ((N / a : ℕ) : ℂ) - (N : ℂ) * (χ a / (a : ℂ)))‖ ≤ N.sqrt := by
    calc
      _ ≤ ∑ a ∈ Ioc 0 N.sqrt,
          ‖χ a * ((N / a : ℕ) : ℂ) - (N : ℂ) * (χ a / (a : ℂ))‖ := norm_sum_le _ _
      _ ≤ ∑ _a ∈ Ioc 0 N.sqrt, (1 : ℝ) := by
        apply sum_le_sum
        intro a ha
        have heq : χ a * ((N / a : ℕ) : ℂ) - (N : ℂ) * (χ a / (a : ℂ)) =
            χ a * ((((N / a : ℕ) : ℝ) - (N : ℝ) / (a : ℝ) : ℝ) : ℂ) := by
          push_cast
          ring
        rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact (mul_le_mul (norm_le_one χ a)
          (abs_natDiv_cast_sub_div_le_one N a (Nat.succ_le_of_lt (mem_Ioc.mp ha).1))
          (abs_nonneg _) (by norm_num)).trans (by norm_num)
      _ = N.sqrt := by simp
  have harm :
      ‖∑ b ∈ Ioc 0 N.sqrt, ∑ a ∈ Ioc 0 (N / b), χ a‖ ≤
        (N.sqrt : ℝ) * q := by
    calc
      _ ≤ ∑ b ∈ Ioc 0 N.sqrt, ‖∑ a ∈ Ioc 0 (N / b), χ a‖ := norm_sum_le _ _
      _ ≤ ∑ _b ∈ Ioc 0 N.sqrt, (q : ℝ) := sum_le_sum fun _ _ =>
        (norm_sum_Ioc_character_le_min χ hχ _).trans (min_le_right _ _)
      _ = (N.sqrt : ℝ) * q := by simp
  have hoverlap : ‖(N.sqrt : ℂ) * ∑ a ∈ Ioc 0 N.sqrt, χ a‖ ≤
      (N.sqrt : ℝ) * q := by
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left
      ((norm_sum_Ioc_character_le_min χ hχ _).trans (min_le_right _ _)) (by positivity)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  rw [sum_Ioc_zetaMul_eq_sqrt_hyperbola]
  have heq :
      (∑ a ∈ Ioc 0 N.sqrt, χ a * ((N / a : ℕ) : ℂ)) +
        (∑ b ∈ Ioc 0 N.sqrt, ∑ a ∈ Ioc 0 (N / b), χ a) -
        (N.sqrt : ℂ) * (∑ a ∈ Ioc 0 N.sqrt, χ a) -
        (N : ℂ) * (∑ n ∈ Ioc 0 N.sqrt, χ n / (n : ℂ)) =
      (∑ a ∈ Ioc 0 N.sqrt,
        (χ a * ((N / a : ℕ) : ℂ) - (N : ℂ) * (χ a / (a : ℂ)))) +
        (∑ b ∈ Ioc 0 N.sqrt, ∑ a ∈ Ioc 0 (N / b), χ a) -
        (N.sqrt : ℂ) * (∑ a ∈ Ioc 0 N.sqrt, χ a) := by
    rw [sum_sub_distrib, ← mul_sum]
    ring
  rw [heq]
  calc
    _ ≤ _ := (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (N.sqrt : ℝ) + (N.sqrt : ℝ) * q + (N.sqrt : ℝ) * q :=
      add_le_add (add_le_add hfloor harm) hoverlap
    _ ≤ 3 * q * (N.sqrt : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hq) (Nat.cast_nonneg N.sqrt : (0 : ℝ) ≤ _)]

/-- `∑_{n ≤ N} (1 * χ)(n) = N L(1, χ) + O(q √N)` for every nonprincipal `χ` mod `q`,
primitive or not. -/
theorem norm_sum_Ioc_zetaMul_sub_LFunction_main_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖(∑ n ∈ Ioc 0 N, χ.zetaMul n) - (N : ℂ) * χ.LFunction 1‖ ≤
      7 * q * Real.sqrt N := by
  have hdisc := norm_sum_Ioc_zetaMul_sub_harmonic_main_le χ hχ N
  have htail := norm_LFunction_one_sub_sum_Ioc_div_le χ hχ N.sqrt
  have hmsq : (N.sqrt : ℝ) ^ 2 ≤ N := by exact_mod_cast Nat.sqrt_le' N
  have hmle : (N.sqrt : ℝ) ≤ Real.sqrt N :=
    Real.le_sqrt_of_sq_le hmsq
  have hN : (N : ℝ) ≤ (N.sqrt : ℝ) * N.sqrt + N.sqrt + N.sqrt := by
    exact_mod_cast Nat.sqrt_le_add N
  have hdiv : (N : ℝ) / ((N.sqrt : ℝ) + 1) ≤ 2 * Real.sqrt N := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hmle)
      (show (0 : ℝ) ≤ (N.sqrt : ℝ) + 1 by positivity)]
  calc
    _ ≤ ‖(∑ n ∈ Ioc 0 N, χ.zetaMul n) -
        (N : ℂ) * ∑ n ∈ Ioc 0 N.sqrt, χ n / (n : ℂ)‖ +
        (N : ℝ) * ‖χ.LFunction 1 - ∑ n ∈ Ioc 0 N.sqrt, χ n / (n : ℂ)‖ := by
      simpa only [← mul_sub, norm_mul, Complex.norm_natCast, norm_sub_rev] using
        norm_sub_le_norm_sub_add_norm_sub
          (∑ n ∈ Ioc 0 N, χ.zetaMul n)
          ((N : ℂ) * ∑ n ∈ Ioc 0 N.sqrt, χ n / (n : ℂ))
          ((N : ℂ) * χ.LFunction 1)
    _ ≤ 3 * q * (N.sqrt : ℝ) + (N : ℝ) * (2 * q / (N.sqrt + 1 : ℝ)) :=
      add_le_add hdisc (mul_le_mul_of_nonneg_left htail (by positivity))
    _ = 3 * q * (N.sqrt : ℝ) + 2 * q * ((N : ℝ) / (N.sqrt + 1 : ℝ)) := by ring
    _ ≤ 3 * q * Real.sqrt N + 2 * q * (2 * Real.sqrt N) := by gcongr
    _ = 7 * q * Real.sqrt N := by ring

theorem norm_LFunction_one_le_two_mul_modulus
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ‖χ.LFunction 1‖ ≤ 2 * q := by
  simpa [BombieriVinogradov.AbelWeight.cpowWeight] using
    norm_LFunction_one_sub_harmonic_sum_le χ hχ (m := 1) (by norm_num)

/-- For quadratic `χ` the coefficients `(1 * χ)(n)` are nonnegative, so this follows from
the asymptotic `N L(1, χ) + O(q √N)`. -/
theorem sum_Ioc_norm_zetaMul_le_nine_mul_modulus
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hquad : χ ^ 2 = 1) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, ‖χ.zetaMul n‖) ≤ 9 * q * N := by
  have hn (n : ℕ) : ‖χ.zetaMul n‖ = (χ.zetaMul n).re := by
    exact (Complex.re_eq_norm.mpr (zetaMul_nonneg hquad n)).symm
  have hsum : (∑ n ∈ Ioc 0 N, ‖χ.zetaMul n‖) =
      ((∑ n ∈ Ioc 0 N, χ.zetaMul n) : ℂ).re := by simp only [hn, re_sum]
  rw [hsum]
  have h := norm_sum_Ioc_zetaMul_sub_LFunction_main_le χ hχ N
  have hL := norm_LFunction_one_le_two_mul_modulus χ hχ
  have hsqrt : Real.sqrt (N : ℝ) ≤ N := by
    by_cases hN : N = 0
    · simp [hN]
    · have hN' : (1 : ℝ) ≤ N := by exact_mod_cast Nat.pos_of_ne_zero hN
      exact Real.sqrt_le_self_iff.mpr (Or.inr hN')
  calc
    _ ≤ ‖∑ n ∈ Ioc 0 N, χ.zetaMul n‖ := Complex.re_le_norm _
    _ ≤ ‖(∑ n ∈ Ioc 0 N, χ.zetaMul n) - (N : ℂ) * χ.LFunction 1‖ +
        ‖(N : ℂ) * χ.LFunction 1‖ := by
      simpa only [add_comm] using norm_le_insert'
        (∑ n ∈ Ioc 0 N, χ.zetaMul n) ((N : ℂ) * χ.LFunction 1)
    _ ≤ 7 * q * Real.sqrt N + (N : ℝ) * (2 * q) := by
      rw [norm_mul, Complex.norm_natCast]
      exact add_le_add h (mul_le_mul_of_nonneg_left hL (by positivity))
    _ ≤ 7 * q * N + (N : ℝ) * (2 * q) := by gcongr
    _ = 9 * q * N := by ring

end DirichletCharacter

end

section

/-! ## Lifting characters to a common modulus -/

open Complex Finset

namespace DirichletCharacter

variable {q r Q : ℕ}

/-- `∏_{p ∣ Q} (1 - χ(p) p^{-s})`, the Euler factor relating `L(s, χ)` to the L-function
of `χ` lifted to modulus `Q`. -/
noncomputable def inductionEulerProduct
    (χ : DirichletCharacter ℂ q) (Q : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ Q.primeFactors, (1 - χ p * (p : ℂ) ^ (-s))

theorem sq_changeLevel_eq_one {q Q : ℕ} (h : q ∣ Q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) :
    (changeLevel h χ) ^ 2 = 1 := by
  rw [← map_pow, hχ, map_one]

theorem mul_ne_one_of_quadratic_ne {χ ψ : DirichletCharacter ℂ Q}
    (hψ : ψ ^ 2 = 1) (hne : χ ≠ ψ) : χ * ψ ≠ 1 := by
  intro h
  apply hne
  calc
    χ = χ * (ψ * ψ) := by rw [← pow_two, hψ, mul_one]
    _ = ψ := by rw [← mul_assoc, h, one_mul]

/-- Primitive characters of possibly different moduli that differ at some `n` stay distinct
after both are lifted to a common multiple `Q` of their moduli. -/
theorem changeLevel_ne_of_primitive_values [NeZero Q]
    (hq : q ∣ Q) (hr : r ∣ Q) (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    (hne : ∃ n : ℕ, χ n ≠ ψ n) :
    changeLevel hq χ ≠ changeLevel hr ψ := by
  intro heq
  have hqr : q = r := by
    have hc := congrArg conductor heq
    change χ.conductor = q at hχ
    change ψ.conductor = r at hψ
    simpa only [conductor_changeLevel, hχ, hψ] using hc
  subst r
  have hchars : χ = ψ := changeLevel_injective hq heq
  obtain ⟨n, hn⟩ := hne
  exact hn (congrArg (fun η : DirichletCharacter ℂ q => η n) hchars)

private theorem norm_character_prime_cpow_le
    (χ : DirichletCharacter ℂ q) (p : ℕ) (β : ℝ) :
    ‖χ p * (p : ℂ) ^ (-(β : ℂ))‖ ≤ (p : ℝ) ^ (-β) := by
  rw [norm_mul, ← ofReal_neg, norm_cpow_real, Complex.norm_natCast]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    (norm_le_one χ p)

theorem norm_inductionEulerProduct_le
    (χ : DirichletCharacter ℂ q) (Q : ℕ) (β : ℝ) :
    ‖inductionEulerProduct χ Q (β : ℂ)‖ ≤
      ∏ p ∈ Q.primeFactors, (1 + (p : ℝ) ^ (-β)) := by
  rw [inductionEulerProduct, norm_prod]
  apply prod_le_prod (fun _ _ => norm_nonneg _)
  intro p _
  exact (norm_sub_le _ _).trans (by
    simpa using add_le_add_left (norm_character_prime_cpow_le χ p β) 1)

private theorem prime_rpow_neg_lt_one {p : ℕ} (hp : p.Prime)
    {β : ℝ} (hβ : 0 < β) : (p : ℝ) ^ (-β) < 1 :=
  (Real.rpow_lt_one_iff_of_pos (by exact_mod_cast hp.pos)).mpr
    (Or.inl ⟨by exact_mod_cast hp.one_lt, neg_neg_of_pos hβ⟩)

theorem prod_one_sub_rpow_le_norm_inductionEulerProduct
    (χ : DirichletCharacter ℂ q) (Q : ℕ) {β : ℝ} (hβ : 0 < β) :
    (∏ p ∈ Q.primeFactors, (1 - (p : ℝ) ^ (-β))) ≤
      ‖inductionEulerProduct χ Q (β : ℂ)‖ := by
  rw [inductionEulerProduct, norm_prod]
  apply prod_le_prod
    (fun p hp => sub_nonneg.mpr
      (prime_rpow_neg_lt_one (Nat.prime_of_mem_primeFactors hp) hβ).le)
  intro p _
  have h := norm_add_le (1 - χ p * (p : ℂ) ^ (-(β : ℂ)))
    (χ p * (p : ℂ) ^ (-(β : ℂ)))
  rw [sub_add_cancel, norm_one] at h
  linarith [norm_character_prime_cpow_le χ p β]

theorem inductionEulerProduct_ne_zero
    (χ : DirichletCharacter ℂ q) (Q : ℕ) {β : ℝ} (hβ : 0 < β) :
    inductionEulerProduct χ Q (β : ℂ) ≠ 0 := by
  apply norm_pos_iff.mp
  refine lt_of_lt_of_le ?_
    (prod_one_sub_rpow_le_norm_inductionEulerProduct χ Q hβ)
  exact prod_pos fun p hp => sub_pos.mpr
    (prime_rpow_neg_lt_one (Nat.prime_of_mem_primeFactors hp) hβ)

/-- For real `β > 0`, lifting `χ` to modulus `Q` neither creates nor removes a zero of
`L(β, χ)`, since the extra Euler factors do not vanish there. -/
theorem LFunction_changeLevel_real_eq_zero_iff
    [NeZero q] [NeZero Q] (hq : q ∣ Q) (χ : DirichletCharacter ℂ q)
    {β : ℝ} (hβ : 0 < β) (hχ : χ ≠ 1 ∨ β ≠ 1) :
    (changeLevel hq χ).LFunction (β : ℂ) = 0 ↔ χ.LFunction (β : ℂ) = 0 := by
  rw [LFunction_changeLevel hq χ
    (hχ.imp id (fun h => by exact_mod_cast h))]
  exact mul_eq_zero_iff_right (inductionEulerProduct_ne_zero χ Q hβ)

/-- `L(1, χ) L(1, ψ) L(1, χψ)`, the residue at `s = 1` of
`ζ(s) L(s, χ) L(s, ψ) L(s, χψ)`. -/
noncomputable def twoCharacterResidue [NeZero Q]
    (χ ψ : DirichletCharacter ℂ Q) : ℂ :=
  χ.LFunction 1 * ψ.LFunction 1 * (χ * ψ).LFunction 1

open Filter
open scoped Topology ComplexOrder

end DirichletCharacter

end

section

/-! ## Upper bounds for `L(1, χ)` and the residue -/

open Complex Finset

namespace DirichletCharacter

variable {q Q : ℕ}

/-- Truncate the series for `L(1, χ)` at `n = q` and bound the tail by `2`. -/
theorem norm_LFunction_one_le_log_add_three [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ‖χ.LFunction 1‖ ≤ Real.log q + 3 := by
  have hsum : ‖∑ n ∈ Ioc 0 q, χ n / (n : ℂ)‖ ≤ 1 + Real.log q := by
    calc
      _ ≤ ∑ n ∈ Ioc 0 q, ‖χ n / (n : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Ioc 0 q, (n : ℝ)⁻¹ := by
        apply sum_le_sum
        intro n _
        rw [norm_div, Complex.norm_natCast, ← one_div]
        exact div_le_div_of_nonneg_right (norm_le_one χ n) (Nat.cast_nonneg n)
      _ = (harmonic q : ℝ) := by
        have hI : Ioc 0 q = Icc 1 q := by ext n; simp; omega
        rw [hI]
        simpa only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
          congrArg (fun x : ℚ => (x : ℝ)) (harmonic_eq_sum_Icc (n := q)).symm
      _ ≤ 1 + Real.log q := by exact_mod_cast harmonic_le_one_add_log q
  have htail : ‖χ.LFunction 1 - ∑ n ∈ Ioc 0 q, χ n / (n : ℂ)‖ ≤ 2 :=
    (norm_LFunction_one_sub_sum_Ioc_div_le χ hχ q).trans
      ((div_le_iff₀ (by positivity)).mpr (by linarith))
  calc
    ‖χ.LFunction 1‖ ≤
        ‖χ.LFunction 1 - ∑ n ∈ Ioc 0 q, χ n / (n : ℂ)‖ +
          ‖∑ n ∈ Ioc 0 q, χ n / (n : ℂ)‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (χ.LFunction 1 - ∑ n ∈ Ioc 0 q, χ n / (n : ℂ))
        (∑ n ∈ Ioc 0 q, χ n / (n : ℂ))
    _ ≤ 2 + (1 + Real.log q) := add_le_add htail hsum
    _ = Real.log q + 3 := by ring

/-- Uses `∏_{p ∣ Q} (1 + 1/p) ≤ 1 + log Q`. -/
theorem norm_inductionEulerProduct_one_le_one_add_log
    (χ : DirichletCharacter ℂ q) (Q : ℕ) [NeZero Q] :
    ‖inductionEulerProduct χ Q 1‖ ≤ 1 + Real.log Q := by
  have h := norm_inductionEulerProduct_le χ Q 1
  simp only [ofReal_one, Real.rpow_neg_one] at h
  exact h.trans (prod_one_add_inv_primeFactors_le_one_add_log Q
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne Q)))

theorem log_add_three_le_subpower {a x : ℝ} (ha : 0 < a) (hx : 1 ≤ x) :
    Real.log x + 3 ≤ (3 + 1 / a) * x ^ a := by
  have hp : 1 ≤ x ^ a := Real.one_le_rpow hx ha.le
  have hl := Real.log_le_rpow_div (by linarith : 0 ≤ x) ha
  calc
    Real.log x + 3 ≤ x ^ a / a + 3 * x ^ a := by linarith
    _ = (3 + 1 / a) * x ^ a := by ring

theorem norm_LFunction_one_le_subpower [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {a : ℝ} (ha : 0 < a) :
    ‖χ.LFunction 1‖ ≤ (3 + 1 / a) * (q : ℝ) ^ a :=
  (norm_LFunction_one_le_log_add_three χ hχ).trans
    (log_add_three_le_subpower ha (by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)))

theorem norm_inductionEulerProduct_one_le_subpower
    (χ : DirichletCharacter ℂ q) (Q : ℕ) [NeZero Q] {a : ℝ} (ha : 0 < a) :
    ‖inductionEulerProduct χ Q 1‖ ≤ (3 + 1 / a) * (Q : ℝ) ^ a := by
  have h := norm_inductionEulerProduct_one_le_one_add_log χ Q
  exact (h.trans (by linarith : 1 + Real.log Q ≤ Real.log Q + 3)).trans
    (log_add_three_le_subpower ha (by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne Q)))

/-- For quadratic nonprincipal `χ`, `L(1, χ)` is real and positive. -/
theorem norm_LFunction_one_eq_re_of_quadratic [NeZero q]
    {χ : DirichletCharacter ℂ q} (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    ‖χ.LFunction 1‖ = (χ.LFunction 1).re := by
  have hr : χ.LFunction 1 = ((χ.LFunction 1).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using LFunction_apply_one_im_eq_zero_of_sq_eq_one hquad hχ
  calc
    _ = ‖((χ.LFunction 1).re : ℂ)‖ := congrArg norm hr
    _ = _ := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (LFunction_apply_one_re_pos_of_sq_eq_one hquad hχ)]

/-- Upper bound for the residue of `χ` lifted to modulus `Q` and `ψ` mod `Q`. The factor
`L(1, χ)` is kept at the modulus `q` of `χ`; the Euler factor and the other two L-values are
each at most `(3 + 1/a) Q^a`. -/
theorem twoCharacterResidue_re_le_original_value_mul_subpower
    [NeZero q] [NeZero Q] (hq : q ∣ Q)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ Q)
    (hχ : χ ≠ 1) (hquad : χ ^ 2 = 1) (hψ : ψ ≠ 1)
    (hprod : changeLevel hq χ * ψ ≠ 1) {a : ℝ} (ha : 0 < a) :
    (twoCharacterResidue (changeLevel hq χ) ψ).re ≤
      (χ.LFunction 1).re * ((3 + 1 / a) ^ 3 * (Q : ℝ) ^ (3 * a)) := by
  have hE := norm_inductionEulerProduct_one_le_subpower χ Q ha
  have hψB := norm_LFunction_one_le_subpower ψ hψ ha
  have hprodB := norm_LFunction_one_le_subpower (changeLevel hq χ * ψ) hprod ha
  have hχpos := LFunction_apply_one_re_pos_of_sq_eq_one hquad hχ
  calc
    _ ≤ ‖twoCharacterResidue (changeLevel hq χ) ψ‖ := re_le_norm _
    _ = (χ.LFunction 1).re * ‖inductionEulerProduct χ Q 1‖ *
        ‖ψ.LFunction 1‖ * ‖(changeLevel hq χ * ψ).LFunction 1‖ := by
      rw [twoCharacterResidue, LFunction_changeLevel hq χ (Or.inl hχ)]
      simp only [norm_mul, inductionEulerProduct,
        norm_LFunction_one_eq_re_of_quadratic hquad hχ]
    _ ≤ (χ.LFunction 1).re * ((3 + 1 / a) * (Q : ℝ) ^ a) *
        ((3 + 1 / a) * (Q : ℝ) ^ a) * ((3 + 1 / a) * (Q : ℝ) ^ a) := by
      gcongr
    _ = _ := by
      rw [mul_comm (3 : ℝ) a, Real.rpow_mul (Nat.cast_nonneg Q)]
      norm_num
      ring

end DirichletCharacter

end

section

/-! ## Partial sums of `1 * χ * ψ * χψ` -/

open Complex Finset Filter MeasureTheory
open scoped Topology

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
private theorem sum_Icc_zero_norm_zetaMul (χ : DirichletCharacter ℂ q) (m : ℕ) :
    (∑ n ∈ Finset.Icc 0 m, ‖χ.zetaMul n‖) = ∑ n ∈ Ioc 0 m, ‖χ.zetaMul n‖ := by
  rw [← insert_Icc_add_one_left_eq_Icc (Nat.zero_le m), sum_insert (by simp)]
  simp only [ArithmeticFunction.map_zero, norm_zero, zero_add]
  congr 1

/-- Partial summation from `∑_{n ≤ t} (1 * χ)(n) ≤ 9 q t`. -/
theorem sum_Ioc_norm_zetaMul_div_sqrt_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hquad : χ ^ 2 = 1) (m : ℕ) :
    (∑ n ∈ Ioc 0 m, ‖χ.zetaMul n‖ / Real.sqrt n) ≤ 18 * q * Real.sqrt m := by
  rcases m.eq_zero_or_pos with rfl | hm
  · simp
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let S : ℝ → ℝ := fun t => ∑ n ∈ Ioc 0 ⌊t⌋₊, ‖χ.zetaMul n‖
  have hS (t : ℝ) (ht : 0 ≤ t) : S t ≤ 9 * q * t :=
    (sum_Ioc_norm_zetaMul_le_nine_mul_modulus χ hχ hquad ⌊t⌋₊).trans
      (mul_le_mul_of_nonneg_left (Nat.floor_le ht) (by positivity))
  have hdiff (t : ℝ) (ht : t ∈ Set.Icc 1 (m : ℝ)) :
      DifferentiableAt ℝ (fun t : ℝ => t ^ (-1 / 2 : ℝ)) t :=
    (Real.hasDerivAt_rpow_const (Or.inl (by linarith [ht.1]))).differentiableAt
  have hint : IntegrableOn (deriv (fun t : ℝ => t ^ (-1 / 2 : ℝ)))
      (Set.Icc 1 (m : ℝ)) := by
    change IntegrableOn (fun t => deriv (fun t : ℝ => t ^ (-1 / 2 : ℝ)) t)
      (Set.Icc 1 (m : ℝ))
    simp only [Real.deriv_rpow_const]
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    exact ((Real.continuousAt_rpow_const t _ (Or.inl (by linarith [ht.1]))).const_mul
      (-1 / 2)).continuousWithinAt
  have hab := sum_mul_eq_sub_integral_mul₀' (c := fun n => ‖χ.zetaMul n‖)
    (by simp) m hdiff hint
  have hsum :
      (∑ n ∈ Finset.Icc 0 m, (n : ℝ) ^ (-1 / 2 : ℝ) * ‖χ.zetaMul n‖) =
        ∑ n ∈ Ioc 0 m, ‖χ.zetaMul n‖ / Real.sqrt n := by
    rw [← insert_Icc_add_one_left_eq_Icc (Nat.zero_le m), sum_insert (by simp)]
    simp only [ArithmeticFunction.map_zero, norm_zero, mul_zero, zero_add]
    have hI : Finset.Icc 1 m = Ioc 0 m := by ext n; simp; omega
    rw [hI]
    apply sum_congr rfl
    intro n _
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
      Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow]
    ring
  rw [hsum, sum_Icc_zero_norm_zetaMul] at hab
  have hi :
      (∫ t in Set.Ioc (1 : ℝ) m,
        deriv (fun t : ℝ => t ^ (-1 / 2 : ℝ)) t *
          ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, ‖χ.zetaMul n‖) =
      -(∫ t in Set.Ioc (1 : ℝ) m, (1 / 2 : ℝ) * t ^ (-3 / 2 : ℝ) * S t) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _
    dsimp only
    rw [Real.deriv_rpow_const, sum_Icc_zero_norm_zetaMul]
    dsimp [S]
    norm_num
  rw [hi, sub_neg_eq_add] at hab
  have hSint : IntegrableOn (fun t => (1 / 2 : ℝ) * t ^ (-3 / 2 : ℝ) * S t)
      (Set.Ioc (1 : ℝ) m) := by
    have hlocal := locallyIntegrableOn_mul_sum_Icc (fun n => ‖χ.zetaMul n‖)
      (show (0 : ℝ) ≤ 1 by norm_num)
      (g := fun t : ℝ => (1 / 2 : ℝ) * t ^ (-3 / 2 : ℝ)) (m := 0) ?_
    · have hc := hlocal.integrableOn_compact_subset
        (show Set.Icc 1 (m : ℝ) ⊆ Set.Ici 1 from fun _ ht => ht.1) isCompact_Icc
      simpa only [sum_Icc_zero_norm_zetaMul, S] using
        hc.mono_set Set.Ioc_subset_Icc_self
    · exact (show ContinuousOn (fun t : ℝ => (1 / 2 : ℝ) * t ^ (-3 / 2 : ℝ))
        (Set.Ici 1) from fun t ht =>
          ((Real.continuousAt_rpow_const t _
            (Or.inl (by have : (1 : ℝ) ≤ t := ht; linarith))).const_mul
            (1 / 2)).continuousWithinAt).locallyIntegrableOn measurableSet_Ici
  have hInt :
      (∫ t in Set.Ioc (1 : ℝ) m, (1 / 2 : ℝ) * t ^ (-3 / 2 : ℝ) * S t) ≤
        9 * q * Real.sqrt m := by
    calc
      _ ≤ ∫ t in Set.Ioc (1 : ℝ) m, (9 * q / 2 : ℝ) * t ^ (-1 / 2 : ℝ) := by
        apply setIntegral_mono_on hSint
          ((show ContinuousOn (fun t : ℝ => (9 * q / 2 : ℝ) * t ^ (-1 / 2 : ℝ))
              (Set.Icc 1 m) from fun t ht =>
            ((Real.continuousAt_rpow_const t _ (Or.inl (by linarith [ht.1]))).const_mul
              (9 * q / 2)).continuousWithinAt).integrableOn_Icc.mono_set
                Set.Ioc_subset_Icc_self) measurableSet_Ioc
        intro t ht
        have ht0 : 0 < t := by linarith [ht.1]
        calc
          _ ≤ (1 / 2 : ℝ) * t ^ (-3 / 2 : ℝ) * (9 * q * t) :=
            mul_le_mul_of_nonneg_left (hS t ht0.le) (by positivity)
          _ = _ := by
            rw [show (-1 / 2 : ℝ) = (-3 / 2 : ℝ) + 1 by norm_num,
              Real.rpow_add ht0, Real.rpow_one]
            ring
      _ = 9 * q * (Real.sqrt m - 1) := by
        rw [integral_const_mul, ← intervalIntegral.integral_of_le hmR,
          integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))]
        norm_num
        rw [← Real.sqrt_eq_rpow]
        ring
      _ ≤ 9 * q * Real.sqrt m :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [hab]
  have hboundary :
      (m : ℝ) ^ (-1 / 2 : ℝ) * (∑ n ∈ Ioc 0 m, ‖χ.zetaMul n‖) ≤
        9 * q * Real.sqrt m := by
    calc
      _ ≤ (m : ℝ) ^ (-1 / 2 : ℝ) * (9 * q * m) :=
        mul_le_mul_of_nonneg_left (sum_Ioc_norm_zetaMul_le_nine_mul_modulus χ hχ hquad m)
          (by positivity)
      _ = _ := by
        rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
          Real.rpow_neg (Nat.cast_nonneg m), ← Real.sqrt_eq_rpow]
        have hs : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
        field_simp
        nlinarith [Real.sq_sqrt (Nat.cast_nonneg m)]
  linarith only [hboundary, hInt]

private theorem sqrt_natDiv_le (N b : ℕ) :
    Real.sqrt ((N / b : ℕ) : ℝ) ≤ Real.sqrt N / Real.sqrt b := by
  rw [← Real.sqrt_div (Nat.cast_nonneg N)]
  exact Real.sqrt_le_sqrt Nat.cast_div_le

private theorem norm_sum_zetaMul_natDiv_sub_main_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N b : ℕ) (hb : 0 < b) :
    ‖(∑ n ∈ Ioc 0 (N / b), χ.zetaMul n) - (N : ℂ) / b * χ.LFunction 1‖ ≤
      7 * q * (Real.sqrt N / Real.sqrt b) + 2 * q := by
  have hmain := norm_sum_Ioc_zetaMul_sub_LFunction_main_le χ hχ (N / b)
  have hL := norm_LFunction_one_le_two_mul_modulus χ hχ
  have hfloor :
      ‖(((N / b : ℕ) : ℂ) - (N : ℂ) / b) * χ.LFunction 1‖ ≤ 2 * q := by
    rw [norm_mul]
    have hnorm : ‖((N / b : ℕ) : ℂ) - (N : ℂ) / b‖ ≤ 1 := by
      have h := abs_natDiv_cast_sub_div_le_one N b (by omega)
      simpa only [← ofReal_natCast, ← ofReal_div, ← ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs] using h
    exact (mul_le_mul hnorm hL (norm_nonneg _) (by norm_num)).trans (by simp)
  calc
    _ = ‖((∑ n ∈ Ioc 0 (N / b), χ.zetaMul n) -
        ((N / b : ℕ) : ℂ) * χ.LFunction 1) +
        (((N / b : ℕ) : ℂ) - (N : ℂ) / b) * χ.LFunction 1‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ 7 * q * Real.sqrt ((N / b : ℕ) : ℝ) + 2 * q := add_le_add hmain hfloor
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (sqrt_natDiv_le N b)
        (show (0 : ℝ) ≤ 7 * q by positivity)) le_rfl

omit [NeZero q] in
private theorem norm_pair_le_norm_zetaMul
    (χ ψ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖(toArithmeticFunction (ψ ·) * toArithmeticFunction ((χ * ψ) ·)) n‖ ≤
      ‖χ.zetaMul n‖ := by
  rw [character_mul_product_apply, norm_mul]
  exact (mul_le_mul_of_nonneg_right (norm_le_one ψ n) (norm_nonneg _)).trans (by simp)

set_option maxHeartbeats 800000 in
/-- For nonprincipal `χ`, `ψ`, `χψ` with `χ` quadratic,
`∑_{n ≤ N} (1 * χ * ψ * χψ)(n) = N L(1, χ) L(1, ψ) L(1, χψ) + O(q² N^{3/4})`.
The hyperbola method is applied to `(1 * χ) * (ψ * χψ)`, split at `√N`. -/
theorem norm_sum_Ioc_twoCharacterConvolution_sub_residue_main_le
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) (N : ℕ) :
    ‖(∑ n ∈ Ioc 0 N, twoCharacterConvolution χ ψ n) -
      (N : ℂ) * twoCharacterResidue χ ψ‖ ≤ 300 * (q : ℝ) ^ 2 * (N : ℝ) ^ (3 / 4 : ℝ) := by
  rcases N.eq_zero_or_pos with rfl | hN
  · simp
  -- Hyperbola method at `m = √N` with `A = 1 * χ` and `B = ψ * χψ`.
  let m := N.sqrt
  let A : ArithmeticFunction ℂ := χ.zetaMul
  let B : ArithmeticFunction ℂ :=
    toArithmeticFunction (ψ ·) * toArithmeticFunction ((χ * ψ) ·)
  let AS : ℕ → ℂ := fun n => ∑ a ∈ Ioc 0 n, A a
  let BS : ℕ → ℂ := fun n => ∑ a ∈ Ioc 0 n, B a
  let H : ℂ := ∑ b ∈ Ioc 0 m, B b / (b : ℂ)
  let U : ℂ := ∑ a ∈ Ioc 0 m, A a * BS (N / a)
  let V : ℂ := ∑ b ∈ Ioc 0 m, B b * AS (N / b)
  let T : ℂ := (N : ℂ) * χ.LFunction 1 * H
  have hI (n : ℕ) : Finset.Icc 1 n = Ioc 0 n := by ext a; simp; omega
  have hm : 1 ≤ m := Nat.sqrt_pos.mpr hN
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hsm1 : 1 ≤ Real.sqrt (m : ℝ) :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hmR)
  have hmle : (m : ℝ) ≤ Real.sqrt N :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' N)
  -- Since `|B(n)| ≤ A(n)`, the bounds for `A` also hold for `B`.
  have hB (n : ℕ) : ‖B n‖ ≤ ‖A n‖ := norm_pair_le_norm_zetaMul χ ψ n
  have hAnorm : (∑ a ∈ Ioc 0 m, ‖A a‖) ≤ 9 * q * m :=
    sum_Ioc_norm_zetaMul_le_nine_mul_modulus χ hχ hquad m
  have hBnorm : (∑ b ∈ Ioc 0 m, ‖B b‖) ≤ 9 * q * m :=
    (sum_le_sum fun b _ => hB b).trans hAnorm
  have hAweight : (∑ a ∈ Ioc 0 m, ‖A a‖ / Real.sqrt a) ≤ 18 * q * Real.sqrt m :=
    sum_Ioc_norm_zetaMul_div_sqrt_le χ hχ hquad m
  have hBweight : (∑ b ∈ Ioc 0 m, ‖B b‖ / Real.sqrt b) ≤ 18 * q * Real.sqrt m :=
    (sum_le_sum fun b _ =>
      div_le_div_of_nonneg_right (hB b) (Real.sqrt_nonneg _)).trans hAweight
  have hBS (n : ℕ) : ‖BS n‖ ≤ 3 * q * Real.sqrt n := by
    simpa only [hI] using
      norm_sum_Icc_character_pair_convolution_le_three_mul_sqrt ψ (χ * ψ) hψ hprod n
  -- `U` uses cancellation in partial sums of `B`, `V` the asymptotic for partial sums of `A`.
  have hU : ‖U‖ ≤ 54 * (q : ℝ) ^ 2 * Real.sqrt N * Real.sqrt m := by
    calc
      _ ≤ ∑ a ∈ Ioc 0 m, ‖A a‖ * ‖BS (N / a)‖ := by
        simpa only [U, norm_mul] using norm_sum_le (Ioc 0 m) (fun a => A a * BS (N / a))
      _ ≤ ∑ a ∈ Ioc 0 m, ‖A a‖ * (3 * q * (Real.sqrt N / Real.sqrt a)) := by
        apply sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left
          ((hBS _).trans (mul_le_mul_of_nonneg_left (sqrt_natDiv_le N a) (by positivity)))
          (norm_nonneg _)
      _ = (3 * q * Real.sqrt N) * ∑ a ∈ Ioc 0 m, ‖A a‖ / Real.sqrt a := by
        rw [mul_sum]
        apply sum_congr rfl
        intro a _
        ring
      _ ≤ (3 * q * Real.sqrt N) * (18 * q * Real.sqrt m) :=
        mul_le_mul_of_nonneg_left hAweight (by positivity)
      _ = _ := by ring
  have hV : ‖V - T‖ ≤
      126 * (q : ℝ) ^ 2 * Real.sqrt N * Real.sqrt m + 18 * (q : ℝ) ^ 2 * m := by
    have heq : V - T =
        ∑ b ∈ Ioc 0 m, B b * (AS (N / b) - (N : ℂ) / b * χ.LFunction 1) := by
      dsimp [V, T, H]
      rw [mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl
      intro b _
      ring
    rw [heq]
    calc
      _ ≤ ∑ b ∈ Ioc 0 m,
          ‖B b‖ * ‖AS (N / b) - (N : ℂ) / b * χ.LFunction 1‖ := by
        simpa only [norm_mul] using norm_sum_le (Ioc 0 m)
          (fun b => B b * (AS (N / b) - (N : ℂ) / b * χ.LFunction 1))
      _ ≤ ∑ b ∈ Ioc 0 m,
          ‖B b‖ * (7 * q * (Real.sqrt N / Real.sqrt b) + 2 * q) := by
        apply sum_le_sum
        intro b hb
        exact mul_le_mul_of_nonneg_left
          (norm_sum_zetaMul_natDiv_sub_main_le χ hχ N b (mem_Ioc.mp hb).1) (norm_nonneg _)
      _ = (7 * q * Real.sqrt N) * (∑ b ∈ Ioc 0 m, ‖B b‖ / Real.sqrt b) +
          (2 * q) * (∑ b ∈ Ioc 0 m, ‖B b‖) := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        apply sum_congr rfl
        intro b _
        ring
      _ ≤ (7 * q * Real.sqrt N) * (18 * q * Real.sqrt m) +
          (2 * q) * (9 * q * m) :=
        add_le_add (mul_le_mul_of_nonneg_left hBweight (by positivity))
          (mul_le_mul_of_nonneg_left hBnorm (by positivity))
      _ = _ := by ring
  -- Complete `H = ∑_{b ≤ m} B(b)/b` to `L(1, ψ) L(1, χψ)`.
  have hT : ‖T - (N : ℂ) * twoCharacterResidue χ ψ‖ ≤
      18 * (q : ℝ) ^ 2 * ((N : ℝ) / Real.sqrt m) := by
    have htail : ‖H - ψ.LFunction 1 * (χ * ψ).LFunction 1‖ ≤
        9 * q / Real.sqrt m := by
      simpa only [hI, norm_sub_rev] using
        norm_LFunction_one_mul_sub_characterPair_harmonic_le ψ (χ * ψ) hψ hprod hm
    have heq : T - (N : ℂ) * twoCharacterResidue χ ψ =
        (N : ℂ) * χ.LFunction 1 * (H - ψ.LFunction 1 * (χ * ψ).LFunction 1) := by
      dsimp [T, twoCharacterResidue]
      ring
    rw [heq, norm_mul, norm_mul, Complex.norm_natCast]
    calc
      _ ≤ ((N : ℝ) * (2 * q)) * (9 * q / Real.sqrt m) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left (norm_LFunction_one_le_two_mul_modulus χ hχ) (by positivity))
          htail (norm_nonneg _) (by positivity)
      _ = _ := by ring
  -- The overlap of the two halves of the hyperbola.
  have hO : ‖AS m * BS m‖ ≤ 27 * (q : ℝ) ^ 2 * m * Real.sqrt m := by
    rw [norm_mul]
    calc
      _ ≤ (9 * q * m) * (3 * q * Real.sqrt m) :=
        mul_le_mul ((norm_sum_le _ _).trans hAnorm) (hBS m) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  -- Bound the remaining terms by multiples of `√N √m`.
  have hNdiv : (N : ℝ) / Real.sqrt m ≤ 2 * Real.sqrt N * Real.sqrt m := by
    have hsN : Real.sqrt (N : ℝ) ≤ 2 * m := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      have hNle : (N : ℝ) ≤ (m : ℝ) * m + m + m := by
        exact_mod_cast Nat.sqrt_le_add N
      nlinarith
    rw [div_le_iff₀ hsm]
    nlinarith [Real.sq_sqrt hN0.le, Real.sq_sqrt (show (0 : ℝ) ≤ m by positivity),
      mul_le_mul_of_nonneg_left hsN (Real.sqrt_nonneg (N : ℝ))]
  have hmsmall : (m : ℝ) ≤ Real.sqrt N * Real.sqrt m := by
    calc
      (m : ℝ) = (m : ℝ) * 1 := (mul_one _).symm
      _ ≤ (m : ℝ) * Real.sqrt m :=
        mul_le_mul_of_nonneg_left hsm1 (Nat.cast_nonneg _)
      _ ≤ Real.sqrt N * Real.sqrt m :=
        mul_le_mul_of_nonneg_right hmle hsm.le
  have hOm : (m : ℝ) * Real.sqrt m ≤ Real.sqrt N * Real.sqrt m :=
    mul_le_mul_of_nonneg_right hmle hsm.le
  have heq :
      (∑ n ∈ Ioc 0 N, twoCharacterConvolution χ ψ n) -
        (N : ℂ) * twoCharacterResidue χ ψ =
      U + (V - T) + (T - (N : ℂ) * twoCharacterResidue χ ψ) - AS m * BS m := by
    have hid := sum_Ioc_convolution_eq_sqrt_hyperbola A B N
    have hconv : twoCharacterConvolution χ ψ = A * B := by
      dsimp [twoCharacterConvolution, A, B]
      rw [mul_assoc]
    rw [hconv, hid]
    dsimp [U, V, AS, BS, m]
    ring
  have hpower : Real.sqrt N * Real.sqrt m ≤ (N : ℝ) ^ (3 / 4 : ℝ) := by
    calc
      _ ≤ Real.sqrt N * Real.sqrt (Real.sqrt N) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmle) (Real.sqrt_nonneg _)
      _ = _ := by
        simp_rw [Real.sqrt_eq_rpow]
        rw [← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
        norm_num
  rw [heq]
  calc
    _ ≤ ‖U‖ + ‖V - T‖ + ‖T - (N : ℂ) * twoCharacterResidue χ ψ‖ + ‖AS m * BS m‖ :=
      (norm_sub_le _ _).trans
        (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ (54 * (q : ℝ) ^ 2 * Real.sqrt N * Real.sqrt m) +
        (126 * (q : ℝ) ^ 2 * Real.sqrt N * Real.sqrt m + 18 * (q : ℝ) ^ 2 * m) +
        (18 * (q : ℝ) ^ 2 * ((N : ℝ) / Real.sqrt m)) +
        (27 * (q : ℝ) ^ 2 * m * Real.sqrt m) :=
      add_le_add (add_le_add (add_le_add hU hV) hT) hO
    _ ≤ 300 * (q : ℝ) ^ 2 * (Real.sqrt N * Real.sqrt m) := by
      nlinarith only [mul_le_mul_of_nonneg_left hNdiv (show (0 : ℝ) ≤ 18 * (q : ℝ) ^ 2 by positivity),
        mul_le_mul_of_nonneg_left hmsmall (show (0 : ℝ) ≤ 18 * (q : ℝ) ^ 2 by positivity),
        mul_le_mul_of_nonneg_left hOm (show (0 : ℝ) ≤ 27 * (q : ℝ) ^ 2 by positivity),
        mul_nonneg (sq_nonneg (q : ℝ)) (mul_nonneg (Real.sqrt_nonneg (N : ℝ)) hsm.le)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hpower (by positivity)

/-- A crude bound, used to pass from integer to real endpoints in the error term. -/
theorem norm_twoCharacterResidue_le_eight_mul_modulus_cubed
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) :
    ‖twoCharacterResidue χ ψ‖ ≤ 8 * (q : ℝ) ^ 3 := by
  rw [twoCharacterResidue, norm_mul, norm_mul]
  calc
    _ ≤ ((2 * (q : ℝ)) * (2 * q)) * (2 * q) :=
      mul_le_mul
        (mul_le_mul (norm_LFunction_one_le_two_mul_modulus χ hχ)
          (norm_LFunction_one_le_two_mul_modulus ψ hψ) (norm_nonneg _) (by positivity))
        (norm_LFunction_one_le_two_mul_modulus (χ * ψ) hprod) (norm_nonneg _) (by positivity)
    _ = _ := by ring

end DirichletCharacter

end

section

/-!
## Continuation to `Re s > 3/4`

Write `a = 1 * χ * ψ * χψ`, `R = L(1, χ) L(1, ψ) L(1, χψ)` and
`E(t) = ∑_{n ≤ t} a(n) - R t`. Since `E(t) = O(q³ t^{3/4})`, the Mellin transform of `E`
continues `ζ(s) L(s, χ) L(s, ψ) L(s, χψ)` to `Re s > 3/4`.
-/

open Complex Finset Filter MeasureTheory Set Asymptotics
open scoped Topology

namespace BombieriVinogradov.Siegel

open DirichletCharacter
variable {q : ℕ} [NeZero q]

/-- `∑_{n ≤ N} a(n)`. -/
noncomputable def twoCharacterSummatory (χ ψ : DirichletCharacter ℂ q) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, twoCharacterConvolution χ ψ n

/-- The error `E(t) = ∑_{n ≤ t} a(n) - R t`. -/
noncomputable def twoCharacterError (χ ψ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  twoCharacterSummatory χ ψ ⌊t⌋₊ - (t : ℂ) * twoCharacterResidue χ ψ

/-- The Mellin kernel `E(t) t^{-s-1}`. -/
noncomputable def twoCharacterErrorKernel
    (χ ψ : DirichletCharacter ℂ q) (s : ℂ) (t : ℝ) : ℂ :=
  twoCharacterError χ ψ t * (t : ℂ) ^ (-(s + 1))

/-- `∫_1^∞ E(t) t^{-s-1} dt`, convergent and holomorphic for `Re s > 3/4`. -/
noncomputable def twoCharacterErrorIntegral
    (χ ψ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), twoCharacterErrorKernel χ ψ s t

/-- `E(t)` for `t > 1` and `0` otherwise; its Mellin transform at `-s` is the error
integral. -/
noncomputable def twoCharacterCutoffError (χ ψ : DirichletCharacter ℂ q) : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator (twoCharacterError χ ψ)

theorem norm_twoCharacterError_le
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {t : ℝ} (ht : 1 ≤ t) :
    ‖twoCharacterError χ ψ t‖ ≤ 308 * (q : ℝ) ^ 3 * t ^ (3 / 4 : ℝ) := by
  have hf := Nat.floor_le (show 0 ≤ t by linarith)
  have herror : |(⌊t⌋₊ : ℝ) - t| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [Nat.lt_floor_add_one t]
  have he : ‖((⌊t⌋₊ : ℂ) - (t : ℂ)) * twoCharacterResidue χ ψ‖ ≤
      8 * (q : ℝ) ^ 3 := by
    rw [norm_mul]
    have hc : ‖(⌊t⌋₊ : ℂ) - (t : ℂ)‖ ≤ 1 := by
      simpa only [← ofReal_natCast, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using herror
    exact (mul_le_mul hc
      (norm_twoCharacterResidue_le_eight_mul_modulus_cubed χ ψ hχ hψ hprod)
      (norm_nonneg _) (by norm_num)).trans (by simp)
  have hp : (⌊t⌋₊ : ℝ) ^ (3 / 4 : ℝ) ≤ t ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hf (by norm_num)
  have hp1 : 1 ≤ t ^ (3 / 4 : ℝ) := Real.one_le_rpow ht (by norm_num)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hqq : (q : ℝ) ^ 2 ≤ (q : ℝ) ^ 3 := pow_le_pow_right₀ hq (by norm_num)
  have hn :
      ‖twoCharacterSummatory χ ψ ⌊t⌋₊ - (⌊t⌋₊ : ℂ) * twoCharacterResidue χ ψ‖ ≤
        300 * (q : ℝ) ^ 2 * (⌊t⌋₊ : ℝ) ^ (3 / 4 : ℝ) := by
    have hI : Finset.Icc 1 ⌊t⌋₊ = Finset.Ioc 0 ⌊t⌋₊ :=
      Finset.Icc_add_one_left_eq_Ioc 0 ⌊t⌋₊
    simpa only [twoCharacterSummatory, hI] using
      norm_sum_Ioc_twoCharacterConvolution_sub_residue_main_le χ ψ hχ hχquad hψ hprod ⌊t⌋₊
  calc
    _ = ‖(twoCharacterSummatory χ ψ ⌊t⌋₊ - (⌊t⌋₊ : ℂ) * twoCharacterResidue χ ψ) +
        ((⌊t⌋₊ : ℂ) - (t : ℂ)) * twoCharacterResidue χ ψ‖ := by
      unfold twoCharacterError
      congr 1
      ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ 300 * (q : ℝ) ^ 2 * (⌊t⌋₊ : ℝ) ^ (3 / 4 : ℝ) + 8 * (q : ℝ) ^ 3 :=
      add_le_add hn he
    _ ≤ 300 * (q : ℝ) ^ 3 * t ^ (3 / 4 : ℝ) +
        8 * (q : ℝ) ^ 3 * t ^ (3 / 4 : ℝ) := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hqq (by norm_num)) hp
          (by positivity) (by positivity)
      · simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hp1 (show (0 : ℝ) ≤ 8 * (q : ℝ) ^ 3 by positivity)
    _ = _ := by ring

theorem measurable_twoCharacterError (χ ψ : DirichletCharacter ℂ q) :
    Measurable (twoCharacterError χ ψ) :=
  ((StronglyMeasurable.of_discrete (f := twoCharacterSummatory χ ψ)).measurable.comp
    measurable_id.nat_floor).sub (Complex.measurable_ofReal.mul_const _)

theorem measurable_twoCharacterCutoffError (χ ψ : DirichletCharacter ℂ q) :
    Measurable (twoCharacterCutoffError χ ψ) :=
  (measurable_twoCharacterError χ ψ).indicator measurableSet_Ioi

theorem norm_twoCharacterCutoffError_le
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) (t : ℝ) :
    ‖twoCharacterCutoffError χ ψ t‖ ≤ 308 * (q : ℝ) ^ 3 * |t| ^ (3 / 4 : ℝ) := by
  by_cases ht : 1 < t
  · simpa [twoCharacterCutoffError, ht, abs_of_pos (lt_trans zero_lt_one ht)] using
      norm_twoCharacterError_le χ ψ hχ hχquad hψ hprod ht.le
  · simp only [twoCharacterCutoffError, Set.mem_Ioi, ht, not_false_eq_true,
      indicator_of_notMem, norm_zero]
    positivity

theorem locallyIntegrable_twoCharacterCutoffError
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) :
    LocallyIntegrable (twoCharacterCutoffError χ ψ) := by
  have hc : Continuous (fun t : ℝ => 308 * (q : ℝ) ^ 3 * |t| ^ (3 / 4 : ℝ)) :=
    continuous_const.mul (continuous_abs.rpow_const (by norm_num))
  refine hc.locallyIntegrable.mono
    (measurable_twoCharacterCutoffError χ ψ).aestronglyMeasurable ?_
  filter_upwards [] with t
  exact (norm_twoCharacterCutoffError_le χ ψ hχ hχquad hψ hprod t).trans
    (Real.le_norm_self _)

theorem twoCharacterCutoffError_isBigO_atTop
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) :
    twoCharacterCutoffError χ ψ =O[atTop] (fun t : ℝ => t ^ (3 / 4 : ℝ)) := by
  refine isBigO_iff.mpr ⟨308 * (q : ℝ) ^ 3, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simpa [abs_of_nonneg ht, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht _)] using
    norm_twoCharacterCutoffError_le χ ψ hχ hχquad hψ hprod t

theorem twoCharacterCutoffError_isBigO_zero
    (χ ψ : DirichletCharacter ℂ q) (b : ℝ) :
    twoCharacterCutoffError χ ψ =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ b) := by
  refine isBigO_iff.mpr ⟨0, ?_⟩
  filter_upwards [((eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
    nhdsWithin_le_nhds)] with t ht
  simp [twoCharacterCutoffError, not_lt.mpr ht.le]

private theorem cutoff_mellin_kernel (χ ψ : DirichletCharacter ℂ q) (s : ℂ) :
    (fun t : ℝ => (t : ℂ) ^ (-s - 1) • twoCharacterCutoffError χ ψ t) =
      (Ioi (1 : ℝ)).indicator (twoCharacterErrorKernel χ ψ s) := by
  funext t
  by_cases ht : 1 < t
  · simp [twoCharacterCutoffError, twoCharacterErrorKernel, ht,
      smul_eq_mul, sub_eq_add_neg, mul_comm, add_comm]
  · simp [twoCharacterCutoffError, ht]

theorem mellin_twoCharacterCutoffError (χ ψ : DirichletCharacter ℂ q) (s : ℂ) :
    mellin (twoCharacterCutoffError χ ψ) (-s) = twoCharacterErrorIntegral χ ψ s := by
  rw [mellin, cutoff_mellin_kernel, setIntegral_indicator measurableSet_Ioi]
  simp only [Ioi_inter_Ioi, max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)]
  rfl

theorem integrableOn_twoCharacterErrorKernel
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {s : ℂ} (hs : 3 / 4 < s.re) :
    IntegrableOn (twoCharacterErrorKernel χ ψ s) (Ioi (1 : ℝ)) := by
  have h : MellinConvergent (twoCharacterCutoffError χ ψ) (-s) := by
    apply mellinConvergent_of_isBigO_rpow
      ((locallyIntegrable_twoCharacterCutoffError χ ψ hχ hχquad hψ hprod).locallyIntegrableOn _)
      (a := -(3 / 4)) (b := -s.re - 1)
    · simpa using twoCharacterCutoffError_isBigO_atTop χ ψ hχ hχquad hψ hprod
    · simp only [neg_re]; linarith
    · exact twoCharacterCutoffError_isBigO_zero χ ψ _
    · simp only [neg_re]; linarith
  rw [MellinConvergent, cutoff_mellin_kernel,
    integrableOn_indicator_iff measurableSet_Ioi] at h
  simpa only [Ioi_inter_Ioi, max_eq_left (show (0 : ℝ) ≤ 1 by norm_num)] using h

/-- The error integral is holomorphic on `Re s > 3/4`, since `E(t) = O(t^{3/4})`. -/
theorem differentiableAt_twoCharacterErrorIntegral
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {s : ℂ} (hs : 3 / 4 < s.re) :
    DifferentiableAt ℂ (twoCharacterErrorIntegral χ ψ) s := by
  have hm : DifferentiableAt ℂ (mellin (twoCharacterCutoffError χ ψ)) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow
      ((locallyIntegrable_twoCharacterCutoffError χ ψ hχ hχquad hψ hprod).locallyIntegrableOn _)
      (a := -(3 / 4)) (b := -s.re - 1)
    · simpa using twoCharacterCutoffError_isBigO_atTop χ ψ hχ hχquad hψ hprod
    · simp only [neg_re]; linarith
    · exact twoCharacterCutoffError_isBigO_zero χ ψ _
    · simp only [neg_re]; linarith
  simpa only [Function.comp_def, mellin_twoCharacterCutoffError] using
    hm.comp s differentiableAt_id.neg

theorem twoCharacterSummatory_isBigO
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) :
    twoCharacterSummatory χ ψ =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
  refine isBigO_iff.mpr ⟨308 * (q : ℝ) ^ 3 + ‖twoCharacterResidue χ ψ‖, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (n : ℝ) ^ (3 / 4 : ℝ) ≤ n := by
    simpa using Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (3 / 4 : ℝ) ≤ 1)
  have he := norm_twoCharacterError_le χ ψ hχ hχquad hψ hprod hnR
  simp only [twoCharacterError, Nat.floor_natCast, ofReal_natCast] at he
  have ht := norm_add_le
    (twoCharacterSummatory χ ψ n - (n : ℂ) * twoCharacterResidue χ ψ)
    ((n : ℂ) * twoCharacterResidue χ ψ)
  rw [sub_add_cancel, norm_mul, Complex.norm_natCast] at ht
  simp only [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  nlinarith [mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 308 * (q : ℝ) ^ 3 by positivity)]

private theorem mul_error_cpow (t : ℝ) (ht : 0 < t) (s : ℂ) :
    (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (-s) := by
  simpa only [cpow_one, neg_add_rev, add_neg_cancel_left] using
    (cpow_add (1 : ℂ) (-(s + 1)) (ofReal_ne_zero.mpr ht.ne')).symm

private theorem summatory_kernel_split
    (χ ψ : DirichletCharacter ℂ q) (s : ℂ) {t : ℝ} (ht : 1 < t) :
    twoCharacterSummatory χ ψ ⌊t⌋₊ * (t : ℂ) ^ (-(s + 1)) =
      twoCharacterErrorKernel χ ψ s t +
        twoCharacterResidue χ ψ * (t : ℂ) ^ (-s) := by
  rw [twoCharacterErrorKernel, twoCharacterError, sub_mul,
    ← mul_error_cpow t (by linarith) s]
  ring

theorem twoCharacter_product_eq_errorIntegral_of_one_lt_re
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ * ψ).LFunction s =
      twoCharacterResidue χ ψ * s / (s - 1) + s * twoCharacterErrorIntegral χ ψ s := by
  have hid := LSeries_eq_mul_integral (twoCharacterConvolution χ ψ)
    (r := 1) (by norm_num) hs (LSeriesSummable_twoCharacterConvolution χ ψ hs)
    (twoCharacterSummatory_isBigO χ ψ hχ hχquad hψ hprod)
  rw [LSeries_twoCharacterConvolution_eq_LFunction_product χ ψ hs] at hid
  change _ = s * ∫ t in Ioi (1 : ℝ),
    twoCharacterSummatory χ ψ ⌊t⌋₊ * (t : ℂ) ^ (-(s + 1)) at hid
  have hsplit :
      (∫ t in Ioi (1 : ℝ), twoCharacterSummatory χ ψ ⌊t⌋₊ * (t : ℂ) ^ (-(s + 1))) =
        twoCharacterErrorIntegral χ ψ s +
          twoCharacterResidue χ ψ * (-(1 : ℂ) / (-s + 1)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => summatory_kernel_split χ ψ s ht)]
    rw [integral_add
      (integrableOn_twoCharacterErrorKernel χ ψ hχ hχquad hψ hprod (by linarith))
      ((integrableOn_Ioi_cpow_of_lt (by simpa using (neg_lt_neg hs))
        (by norm_num : (0 : ℝ) < 1)).const_mul (twoCharacterResidue χ ψ)),
      integral_const_mul, integral_Ioi_cpow_of_lt (by simpa using (neg_lt_neg hs))
        (by norm_num : (0 : ℝ) < 1)]
    simp only [ofReal_one, one_cpow]
    rfl
  rw [hid, hsplit, show -s + 1 = -(s - 1) by ring, div_neg, neg_div, neg_neg]
  ring

/-- On `Re s > 3/4`,
`(s - 1) ζ(s) L(s, χ) L(s, ψ) L(s, χψ) = R s + (s - 1) s ∫_1^∞ E(t) t^{-s-1} dt`.
This holds for `Re s > 1` by partial summation and extends by the identity theorem. -/
theorem twoCharacter_regularized_product_eq_errorIntegral
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {s : ℂ} (hs : 3 / 4 < s.re) :
    riemannZeta₁ s * χ.LFunction s * ψ.LFunction s * (χ * ψ).LFunction s =
      twoCharacterResidue χ ψ * s + (s - 1) * s * twoCharacterErrorIntegral χ ψ s := by
  let U : Set ℂ := {z | 3 / 4 < z.re}
  let F : ℂ → ℂ := fun z => twoCharacterResidue χ ψ * z +
    (z - 1) * z * twoCharacterErrorIntegral χ ψ z
  let G : ℂ → ℂ := fun z =>
    riemannZeta₁ z * χ.LFunction z * ψ.LFunction z * (χ * ψ).LFunction z
  have hUopen : IsOpen U := continuous_re.isOpen_preimage _ isOpen_Ioi
  have hFdiff : DifferentiableOn ℂ F U := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have hE := differentiableAt_twoCharacterErrorIntegral χ ψ hχ hχquad hψ hprod hz
    dsimp [F]
    fun_prop
  have hF : AnalyticOnNhd ℂ F U := hFdiff.analyticOnNhd hUopen
  have hG : AnalyticOnNhd ℂ G U :=
    (((differentiable_riemannZeta₁.mul (χ.differentiable_LFunction hχ)).mul
      (ψ.differentiable_LFunction hψ)).mul
        ((χ * ψ).differentiable_LFunction hprod)).differentiableOn.analyticOnNhd hUopen
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt (3 / 4)).isPreconnected
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
    have hid := twoCharacter_product_eq_errorIntegral_of_one_lt_re χ ψ hχ hχquad hψ hprod hz
    dsimp [F, G]
    rw [hzeta]
    calc
      _ = (z - 1) * (riemannZeta z * χ.LFunction z * ψ.LFunction z *
          (χ * ψ).LFunction z) := by ring
      _ = _ := by rw [hid]; field_simp
  exact hG.eqOn_of_preconnected_of_eventuallyEq hF hpre htwo hevent hs

/-- `ζ(s) L(s, χ) L(s, ψ) L(s, χψ) = R s / (s - 1) + s ∫_1^∞ E(t) t^{-s-1} dt`
for `Re s > 3/4`, `s ≠ 1`. -/
theorem twoCharacter_product_eq_errorIntegral
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {s : ℂ} (hs : 3 / 4 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ * ψ).LFunction s =
      twoCharacterResidue χ ψ * s / (s - 1) + s * twoCharacterErrorIntegral χ ψ s := by
  have h := twoCharacter_regularized_product_eq_errorIntegral χ ψ hχ hχquad hψ hprod hs
  rw [riemannZeta_eq_inv_sub_mul hs1]
  calc
    _ = (s - 1)⁻¹ *
        (riemannZeta₁ s * χ.LFunction s * ψ.LFunction s * (χ * ψ).LFunction s) := by ring
    _ = _ := by rw [h]; field_simp

end BombieriVinogradov.Siegel

end

section

/-!
## Weighted sums and the lower bound for the residue

By Abel summation, `∑_{n ≤ x} a(n) n^{-β}` equals `R x^{1-β}/(1 - β)` plus the value of
`ζ(s) L(s, χ) L(s, ψ) L(s, χψ)` at `β`, up to `O(q³ x^{3/4-β})`. The weighted sum is at
least `1` by positivity, so if this value is `0` then `R` is bounded below.
-/

open Complex Finset Filter MeasureTheory
open scoped Topology

namespace BombieriVinogradov.Siegel

open DirichletCharacter
variable {q : ℕ} [NeZero q]

/-- `∑_{n ≤ x} Re a(n) n^{-β}`. For quadratic `χ` and `ψ` the coefficients `a(n)` are real. -/
noncomputable def twoCharacterWeightedSum
    (χ ψ : DirichletCharacter ℂ q) (β x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, (twoCharacterConvolution χ ψ n).re * (n : ℝ) ^ (-β)

omit [NeZero q] in
private theorem convolution_sum_from_zero (χ ψ : DirichletCharacter ℂ q) (N : ℕ) :
    ∑ n ∈ Icc 0 N, (twoCharacterConvolution χ ψ n).re =
      (twoCharacterSummatory χ ψ N).re := by
  rw [← insert_Icc_add_one_left_eq_Icc (Nat.zero_le N), sum_insert (by simp)]
  simp [twoCharacterSummatory, Complex.re_sum]

private theorem rpow_continuousOn (β x : ℝ) :
    ContinuousOn (fun t : ℝ => t ^ β) (Set.Icc 1 x) := by
  intro t ht
  exact (Real.continuousAt_rpow_const _ _
    (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))).continuousWithinAt

omit [NeZero q] in
theorem twoCharacterWeightedSum_eq_abel
    (χ ψ : DirichletCharacter ℂ q) (β x : ℝ) :
    twoCharacterWeightedSum χ ψ β x =
      x ^ (-β) * (twoCharacterSummatory χ ψ ⌊x⌋₊).re +
        β * ∫ t in Set.Ioc (1 : ℝ) x,
          (twoCharacterSummatory χ ψ ⌊t⌋₊).re * t ^ (-β - 1) := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc 1 x) :
      HasDerivAt (fun t : ℝ => t ^ (-β)) (-β * t ^ (-β - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))
  have hint : IntegrableOn (deriv (fun t : ℝ => t ^ (-β))) (Set.Icc 1 x) :=
    (((rpow_continuousOn (-β - 1) x).const_mul (-β)).integrableOn_Icc).congr_fun
      (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have h := sum_mul_eq_sub_integral_mul₀ (fun n => (twoCharacterConvolution χ ψ n).re)
    (by simp) x (fun t ht => (hd t ht).differentiableAt) hint
  have hs :
      (∑ n ∈ Icc 0 ⌊x⌋₊, (n : ℝ) ^ (-β) * (twoCharacterConvolution χ ψ n).re) =
        twoCharacterWeightedSum χ ψ β x := by
    rw [← insert_Icc_add_one_left_eq_Icc (Nat.zero_le ⌊x⌋₊), sum_insert (by simp)]
    simp [twoCharacterWeightedSum, mul_comm]
  rw [hs, convolution_sum_from_zero] at h
  have hi :
      (∫ t in Set.Ioc (1 : ℝ) x, deriv (fun t : ℝ => t ^ (-β)) t *
          ∑ n ∈ Icc 0 ⌊t⌋₊, (twoCharacterConvolution χ ψ n).re) =
      -β * ∫ t in Set.Ioc (1 : ℝ) x,
        (twoCharacterSummatory χ ψ ⌊t⌋₊).re * t ^ (-β - 1) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hd t ⟨ht.1.le, ht.2⟩).deriv, convolution_sum_from_zero]
    ring
  rw [hi] at h
  linarith

theorem re_twoCharacterErrorKernel_ofReal
    (χ ψ : DirichletCharacter ℂ q) (β : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (twoCharacterErrorKernel χ ψ (β : ℂ) t).re =
      (twoCharacterError χ ψ t).re * t ^ (-β - 1) := by
  have hp : (t : ℂ) ^ (-((β : ℂ) + 1)) = ((t ^ (-β - 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow ht]
    congr 1
    push_cast
    ring
  rw [twoCharacterErrorKernel, hp, re_mul_ofReal]

theorem integrableOn_re_twoCharacterErrorKernel
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {β : ℝ} (hβ : 3 / 4 < β) :
    IntegrableOn (fun t : ℝ => (twoCharacterError χ ψ t).re * t ^ (-β - 1))
      (Set.Ioi (1 : ℝ)) := by
  have h := (integrableOn_twoCharacterErrorKernel χ ψ hχ hχquad hψ hprod
    (s := (β : ℂ)) hβ).re
  exact IntegrableOn.congr_fun h
    (fun t ht => re_twoCharacterErrorKernel_ofReal χ ψ β
      (le_of_lt (lt_trans zero_lt_one ht))) measurableSet_Ioi

theorem re_twoCharacter_product_eq_errorIntegral
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {β : ℝ} (hβ : 3 / 4 < β) (hβ1 : β ≠ 1) :
    (riemannZeta (β : ℂ) * χ.LFunction (β : ℂ) * ψ.LFunction (β : ℂ) *
        (χ * ψ).LFunction (β : ℂ)).re =
      (twoCharacterResidue χ ψ).re * β / (β - 1) +
        β * ∫ t in Set.Ioi (1 : ℝ), (twoCharacterError χ ψ t).re * t ^ (-β - 1) := by
  have h := twoCharacter_product_eq_errorIntegral χ ψ hχ hχquad hψ hprod
    (s := (β : ℂ)) hβ (by exact_mod_cast hβ1)
  have hI :
      (twoCharacterErrorIntegral χ ψ (β : ℂ)).re =
        ∫ t in Set.Ioi (1 : ℝ), (twoCharacterError χ ψ t).re * t ^ (-β - 1) := by
    calc
      _ = ∫ t in Set.Ioi (1 : ℝ), (twoCharacterErrorKernel χ ψ (β : ℂ) t).re :=
        (integral_re
          (integrableOn_twoCharacterErrorKernel χ ψ hχ hχquad hψ hprod
            (s := (β : ℂ)) hβ)).symm
      _ = _ := setIntegral_congr_fun measurableSet_Ioi fun t ht =>
        re_twoCharacterErrorKernel_ofReal χ ψ β (le_of_lt (lt_trans zero_lt_one ht))
  rw [h, add_re, re_ofReal_mul, hI]
  congr 1
  rw [← ofReal_one, ← ofReal_sub, div_ofReal_re, re_mul_ofReal]

theorem abs_re_twoCharacterError_le
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {t : ℝ} (ht : 1 ≤ t) :
    |(twoCharacterError χ ψ t).re| ≤ 308 * (q : ℝ) ^ 3 * t ^ (3 / 4 : ℝ) :=
  (abs_re_le_norm _).trans (norm_twoCharacterError_le χ ψ hχ hχquad hψ hprod ht)

private theorem rpow_mul_weight {t : ℝ} (ht : 0 < t) (β : ℝ) :
    t ^ (3 / 4 : ℝ) * t ^ (-β - 1) = t ^ (-β - 1 / 4) := by
  rw [← Real.rpow_add ht]
  congr 1
  ring

theorem abs_re_twoCharacterError_tail_le
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {β x : ℝ} (hβ : 3 / 4 < β) (hx : 1 ≤ x) :
    |∫ t in Set.Ioi x, (twoCharacterError χ ψ t).re * t ^ (-β - 1)| ≤
      308 * (q : ℝ) ^ 3 * x ^ (3 / 4 - β) / (β - 3 / 4) := by
  have hp : -β - 1 / 4 < -1 := by linarith
  have hx0 : 0 < x := by linarith
  have hg := (integrableOn_Ioi_rpow_of_lt hp hx0).const_mul (308 * (q : ℝ) ^ 3)
  have hbound :
      ∀ᵐ t ∂volume.restrict (Set.Ioi x),
        ‖(twoCharacterError χ ψ t).re * t ^ (-β - 1)‖ ≤
          308 * (q : ℝ) ^ 3 * t ^ (-β - 1 / 4) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hx0 ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    calc
      _ ≤ (308 * (q : ℝ) ^ 3 * t ^ (3 / 4 : ℝ)) * t ^ (-β - 1) :=
        mul_le_mul_of_nonneg_right
          (abs_re_twoCharacterError_le χ ψ hχ hχquad hψ hprod (hx.trans ht.le))
          (Real.rpow_nonneg ht0.le _)
      _ = _ := by rw [mul_assoc, rpow_mul_weight ht0]
  have h := norm_integral_le_of_norm_le hg hbound
  rw [Real.norm_eq_abs, integral_const_mul, integral_Ioi_rpow_of_lt hp hx0] at h
  rw [show -β - 1 / 4 + 1 = -(β - 3 / 4) by ring,
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

/-- For `β > 3/4`, `β ≠ 1` and `x ≥ 1`, the weighted sum equals
`R x^{1-β}/(1 - β) + ζ(β) L(β, χ) L(β, ψ) L(β, χψ)` (real parts), plus the endpoint term
`E(x) x^{-β}` and the tail `-β ∫_x^∞ E(t) t^{-β-1} dt`. -/
theorem twoCharacterWeightedSum_eq_product_add_tail
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {β x : ℝ}
    (hβ : 3 / 4 < β) (hβ1 : β ≠ 1) (hx : 1 ≤ x) :
    twoCharacterWeightedSum χ ψ β x =
      (twoCharacterResidue χ ψ).re * x ^ (1 - β) / (1 - β) +
        (riemannZeta (β : ℂ) * χ.LFunction (β : ℂ) * ψ.LFunction (β : ℂ) *
          (χ * ψ).LFunction (β : ℂ)).re +
        (twoCharacterError χ ψ x).re * x ^ (-β) -
        β * ∫ t in Set.Ioi x, (twoCharacterError χ ψ t).re * t ^ (-β - 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hE := integrableOn_re_twoCharacterErrorKernel χ ψ hχ hχquad hψ hprod hβ
  have hEI : IntegrableOn
      (fun t : ℝ => (twoCharacterError χ ψ t).re * t ^ (-β - 1))
      (Set.Ioc 1 x) := hE.mono_set Set.Ioc_subset_Ioi_self
  have hP : IntegrableOn (fun t : ℝ => (twoCharacterResidue χ ψ).re * t ^ (-β))
      (Set.Ioc 1 x) :=
    ((rpow_continuousOn (-β) x).const_mul _).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hsplit :
      (∫ t in Set.Ioc (1 : ℝ) x,
        (twoCharacterSummatory χ ψ ⌊t⌋₊).re * t ^ (-β - 1)) =
      (∫ t in Set.Ioc (1 : ℝ) x, (twoCharacterError χ ψ t).re * t ^ (-β - 1)) +
      (twoCharacterResidue χ ψ).re * ∫ t in Set.Ioc (1 : ℝ) x, t ^ (-β) := by
    rw [← integral_const_mul, ← integral_add hEI hP]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    simp only [twoCharacterError, sub_re, re_ofReal_mul]
    rw [sub_mul, mul_assoc t _ _, mul_comm (twoCharacterResidue χ ψ).re,
      ← mul_assoc t, mul_weight (lt_trans zero_lt_one ht.1)]
    ring
  have hpow :
      (∫ t in Set.Ioc (1 : ℝ) x, t ^ (-β)) = (x ^ (1 - β) - 1) / (1 - β) := by
    rw [← intervalIntegral.integral_of_le hx]
    rw [integral_rpow (Or.inr ⟨fun h => hβ1 (by linarith), by
      rw [Set.uIcc_of_le hx]
      simp⟩)]
    simp only [Real.one_rpow]
    rw [show -β + 1 = 1 - β by ring]
  have htail := intervalIntegral.integral_Ioi_sub_Ioi hE hx
  rw [intervalIntegral.integral_of_le hx] at htail
  have hend :
      x ^ (-β) * (twoCharacterSummatory χ ψ ⌊x⌋₊).re =
        (twoCharacterError χ ψ x).re * x ^ (-β) +
          (twoCharacterResidue χ ψ).re * x ^ (1 - β) := by
    simp only [twoCharacterError, sub_re, re_ofReal_mul]
    rw [sub_mul, mul_assoc x _ _, mul_comm (twoCharacterResidue χ ψ).re,
      ← mul_assoc x, mul_comm x (x ^ (-β)), mul_weight_main hx0]
    ring
  rw [twoCharacterWeightedSum_eq_abel, hsplit, hpow, hend,
    re_twoCharacter_product_eq_errorIntegral χ ψ hχ hχquad hψ hprod hβ hβ1, ← htail]
  have hden : 1 - β ≠ 0 := sub_ne_zero.mpr hβ1.symm
  have hden' : β - 1 ≠ 0 := sub_ne_zero.mpr hβ1
  field_simp
  ring

/-- For `β > 3/4`, `β ≠ 1`, the weighted sum is
`R x^{1-β}/(1 - β) + ζ(β) L(β, χ) L(β, ψ) L(β, χψ) + O(q³ x^{3/4-β})` (real parts). -/
theorem abs_twoCharacterWeightedSum_sub_main_sub_product_le
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {β x : ℝ}
    (hβ : 3 / 4 < β) (hβ1 : β ≠ 1) (hx : 1 ≤ x) :
    |twoCharacterWeightedSum χ ψ β x -
        (twoCharacterResidue χ ψ).re * x ^ (1 - β) / (1 - β) -
        (riemannZeta (β : ℂ) * χ.LFunction (β : ℂ) * ψ.LFunction (β : ℂ) *
          (χ * ψ).LFunction (β : ℂ)).re| ≤
      308 * (q : ℝ) ^ 3 * (1 + β / (β - 3 / 4)) * x ^ (3 / 4 - β) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hβ0 : 0 ≤ β := by linarith
  have hend :
      |(twoCharacterError χ ψ x).re * x ^ (-β)| ≤
        308 * (q : ℝ) ^ 3 * x ^ (3 / 4 - β) := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    calc
      _ ≤ (308 * (q : ℝ) ^ 3 * x ^ (3 / 4 : ℝ)) * x ^ (-β) :=
        mul_le_mul_of_nonneg_right (abs_re_twoCharacterError_le χ ψ hχ hχquad hψ hprod hx)
          (Real.rpow_nonneg hx0.le _)
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add hx0]
        congr 2
  have htail :
      |β * ∫ t in Set.Ioi x, (twoCharacterError χ ψ t).re * t ^ (-β - 1)| ≤
        β * (308 * (q : ℝ) ^ 3 * x ^ (3 / 4 - β) / (β - 3 / 4)) := by
    rw [abs_mul, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left
      (abs_re_twoCharacterError_tail_le χ ψ hχ hχquad hψ hprod hβ hx) hβ0
  rw [twoCharacterWeightedSum_eq_product_add_tail χ ψ hχ hχquad hψ hprod hβ hβ1 hx]
  calc
    _ = |(twoCharacterError χ ψ x).re * x ^ (-β) -
        β * ∫ t in Set.Ioi x, (twoCharacterError χ ψ t).re * t ^ (-β - 1)| := by
      congr 1
      ring
    _ ≤ |(twoCharacterError χ ψ x).re * x ^ (-β)| +
        |β * ∫ t in Set.Ioi x, (twoCharacterError χ ψ t).re * t ^ (-β - 1)| :=
      abs_sub _ _
    _ ≤ 308 * (q : ℝ) ^ 3 * x ^ (3 / 4 - β) +
        β * (308 * (q : ℝ) ^ 3 * x ^ (3 / 4 - β) / (β - 3 / 4)) :=
      add_le_add hend htail
    _ = _ := by ring

omit [NeZero q] in
/-- For quadratic `χ` and `ψ` the coefficients are nonnegative and `a(1) = 1`, so the
weighted sum is at least `1`. -/
theorem one_le_twoCharacterWeightedSum
    (χ ψ : DirichletCharacter ℂ q) (hχquad : χ ^ 2 = 1) (hψquad : ψ ^ 2 = 1)
    (β : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ twoCharacterWeightedSum χ ψ β x := by
  have hfloor : 1 ≤ ⌊x⌋₊ :=
    Nat.le_floor (by simpa only [Nat.cast_one] using hx)
  have h := Finset.single_le_sum
    (f := fun n : ℕ => (twoCharacterConvolution χ ψ n).re * (n : ℝ) ^ (-β))
    (s := Finset.Icc 1 ⌊x⌋₊) (a := 1)
    (fun n _ => mul_nonneg (twoCharacterConvolution_re_nonneg hχquad hψquad n)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (by simp [hfloor])
  simpa [twoCharacterConvolution_one, twoCharacterWeightedSum] using h

/-- At `x = (5000 q³)^8` the error term above is at most `1/2` for every `β ≥ 7/8`. -/
theorem twoCharacter_error_at_endpoint_le_half
    {β : ℝ} (hβ : 7 / 8 ≤ β) :
    308 * (q : ℝ) ^ 3 * (1 + β / (β - 3 / 4)) *
        ((5000 * (q : ℝ) ^ 3) ^ 8) ^ (3 / 4 - β) ≤ 1 / 2 := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq3 : (1 : ℝ) ≤ (q : ℝ) ^ 3 := one_le_pow₀ hq
  have hbase : 1 ≤ 5000 * (q : ℝ) ^ 3 := by linarith
  have hx : 1 ≤ (5000 * (q : ℝ) ^ 3) ^ 8 := one_le_pow₀ hbase
  have hden : 0 < β - 3 / 4 := by linarith
  have hratio : 1 + β / (β - 3 / 4) ≤ 8 := by
    have hr : β / (β - 3 / 4) ≤ 7 := (div_le_iff₀ hden).mpr (by linarith)
    linarith
  have hpower :
      ((5000 * (q : ℝ) ^ 3) ^ 8) ^ (3 / 4 - β) ≤
        (5000 * (q : ℝ) ^ 3)⁻¹ := by
    calc
      _ ≤ ((5000 * (q : ℝ) ^ 3) ^ 8) ^ (-1 / 8 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num [Real.rpow_neg_one]
  calc
    _ ≤ (308 * (q : ℝ) ^ 3 * 8) * (5000 * (q : ℝ) ^ 3)⁻¹ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hratio (by positivity)) hpower
        (by positivity) (by positivity)
    _ = 308 * 8 / 5000 := by
      have hq0 : (q : ℝ) ≠ 0 := by positivity
      field_simp
    _ ≤ _ := by norm_num

/-- If one of `L(s, χ)`, `L(s, ψ)`, `L(s, χψ)` vanishes at a real `β ∈ [7/8, 1)`, then
`Re (L(1, χ) L(1, ψ) L(1, χψ)) ≥ (1 - β) / (2 x^{1-β})` with `x = (5000 q³)^8`. -/
theorem twoCharacterResidue_re_lower_bound_of_real_zero
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hχquad : χ ^ 2 = 1) (hψquad : ψ ^ 2 = 1) (hne : χ ≠ ψ)
    {β : ℝ} (hβ : 7 / 8 ≤ β) (hβ1 : β < 1)
    (hzero : χ.LFunction (β : ℂ) = 0 ∨ ψ.LFunction (β : ℂ) = 0 ∨
      (χ * ψ).LFunction (β : ℂ) = 0) :
    (1 - β) / (2 * ((5000 * (q : ℝ) ^ 3) ^ 8) ^ (1 - β)) ≤
      (twoCharacterResidue χ ψ).re := by
  let x : ℝ := (5000 * (q : ℝ) ^ 3) ^ 8
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq3 : (1 : ℝ) ≤ (q : ℝ) ^ 3 := one_le_pow₀ hq
  have hx : 1 ≤ x := one_le_pow₀ (show 1 ≤ 5000 * (q : ℝ) ^ 3 by linarith)
  have hprod := mul_ne_one_of_quadratic_ne hψquad hne
  have hconstant :
      (riemannZeta (β : ℂ) * χ.LFunction (β : ℂ) * ψ.LFunction (β : ℂ) *
        (χ * ψ).LFunction (β : ℂ)).re = 0 := by
    rcases hzero with hzero | hzero | hzero <;> simp [hzero]
  have herr := abs_twoCharacterWeightedSum_sub_main_sub_product_le
    χ ψ hχ hχquad hψ hprod (show 3 / 4 < β by linarith) hβ1.ne hx
  rw [hconstant, sub_zero] at herr
  have herr' : |twoCharacterWeightedSum χ ψ β x -
      (twoCharacterResidue χ ψ).re * x ^ (1 - β) / (1 - β)| ≤ 1 / 2 :=
    herr.trans (twoCharacter_error_at_endpoint_le_half (q := q) hβ)
  have hsum := one_le_twoCharacterWeightedSum χ ψ hχquad hψquad β hx
  have hmain : (1 / 2 : ℝ) ≤ (twoCharacterResidue χ ψ).re * x ^ (1 - β) / (1 - β) := by
    linarith [(abs_le.mp herr').2]
  have hd : 0 < 1 - β := by linarith
  have hp : 0 < x ^ (1 - β) := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hx) _
  apply (div_le_iff₀ (mul_pos (by norm_num) hp)).mpr
  have hm := (le_div_iff₀ hd).mp hmain
  dsimp only [x] at hm ⊢
  nlinarith

end BombieriVinogradov.Siegel

end
