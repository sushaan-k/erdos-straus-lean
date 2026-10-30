import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Bertrand
import ErdosStraus.Basic

/-! # Chebyshev's bounds and the prime-counting function

Chebyshev's upper bounds `θ(x) ≤ x log 4` (the first estimate of Lemma 3.1) and
`ψ(x) ≤ (log 4 + 2) x`, and the lower bound `π(N) ≫ N / log N`, which comes from
`ψ(2n) ≥ log binom(2n, n) ≥ n log 4 - log n`. The file also introduces the Euler product
`∏_{p ≤ x} (1 - 1/p)`, the sufficient condition of Lemma 2.3 for `m/n` to be a sum of three
unit fractions, and the bound for exceptional primes stated after Theorem 1.
-/

/-! ## Chebyshev's upper bound -/

namespace ErdosStraus.Estimates

open scoped BigOperators

/-- `∑_{p ≤ N} log p ≤ N log 4`, from the primorial bound `∏_{p ≤ N} p ≤ 4^N`
(proof of Lemma 3.1). -/
theorem primeLogSum_le_log_four_mul (N : ℕ) :
    (∑ p ∈ (Finset.Icc (1 : ℕ) N).filter (fun p => Nat.Prime p),
        Real.log (p : ℝ)) ≤
      Real.log (4 : ℝ) * (N : ℝ) := by
  classical
  let s := (Finset.range (N + 1)).filter Nat.Prime
  have hs_eq :
      (∑ p ∈ (Finset.Icc (1 : ℕ) N).filter (fun p => Nat.Prime p),
          Real.log (p : ℝ)) =
        ∑ p ∈ s, Real.log (p : ℝ) := by
    apply Finset.sum_congr
    · ext p
      by_cases hp : Nat.Prime p
      · simp [s, hp, hp.one_le]
      · simp [s, hp]
    · intro p _hp
      rfl
  have hlog_prod :
      Real.log (∏ p ∈ s, (p : ℝ)) = ∑ p ∈ s, Real.log (p : ℝ) := by
    rw [Real.log_prod]
    intro p hp
    have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2
    exact_mod_cast hpPrime.ne_zero
  have hprod_cast :
      (∏ p ∈ s, (p : ℝ)) = ((primorial N : ℕ) : ℝ) := by
    unfold primorial
    simp [s]
  have hprim : ((primorial N : ℕ) : ℝ) ≤ (4 : ℝ) ^ N := by
    exact_mod_cast primorial_le_four_pow N
  have hprod_pos : 0 < (∏ p ∈ s, (p : ℝ)) := by
    rw [hprod_cast]
    exact_mod_cast primorial_pos N
  have hlog_le :
      Real.log (∏ p ∈ s, (p : ℝ)) ≤ Real.log ((4 : ℝ) ^ N) := by
    exact Real.log_le_log hprod_pos (by simpa [hprod_cast] using hprim)
  have hlog_pow : Real.log ((4 : ℝ) ^ N) = (N : ℝ) * Real.log (4 : ℝ) := by
    rw [Real.log_pow]
  rw [hs_eq, ← hlog_prod]
  calc
    Real.log (∏ p ∈ s, (p : ℝ)) ≤ Real.log ((4 : ℝ) ^ N) := hlog_le
    _ = (N : ℝ) * Real.log (4 : ℝ) := hlog_pow
    _ = Real.log (4 : ℝ) * (N : ℝ) := by ring

end ErdosStraus.Estimates

/-! ## Primes up to `x` and the Euler product

The set of primes `p ≤ x`, the sum `∑_{p ≤ x} 1/p`, the product `∏_{p ≤ x} (1 - 1/p)`, and
the local estimate `|log(1 - 1/p) + 1/p| ≤ 2/p²`.
-/

namespace ErdosStraus.PrimeEstimates.Mertens

open Finset Real

/-- The set of primes `p ≤ x`. -/
def primesUpTo (x : ℕ) : Finset ℕ :=
  (range (x + 1)).filter Nat.Prime

@[simp]
theorem mem_primesUpTo {p x : ℕ} : p ∈ primesUpTo x ↔ p.Prime ∧ p ≤ x := by
  simp [primesUpTo, and_comm]

theorem primesUpTo_eq_empty_of_le_one {x : ℕ} (hx : x ≤ 1) : primesUpTo x = ∅ := by
  ext p
  simp only [mem_primesUpTo, Finset.notMem_empty, iff_false]
  intro hp'
  have hp2 := hp'.1.two_le
  omega

/-- The sum `∑_{p ≤ x} 1/p`. -/
noncomputable def primeReciprocalSum (x : ℕ) : ℝ :=
  (primesUpTo x).sum fun p => 1 / (p : ℝ)

/-- The Euler product `∏_{p ≤ x} (1 - 1/p)`. -/
noncomputable def primeProduct (x : ℕ) : ℝ :=
  (primesUpTo x).prod fun p => 1 - 1 / (p : ℝ)

theorem primeFactor_pos {p : ℕ} (hp : p.Prime) :
    0 < 1 - 1 / (p : ℝ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact sub_pos.mpr ((div_lt_one (zero_lt_one.trans hp1)).mpr hp1)

theorem primeProduct_pos (x : ℕ) : 0 < primeProduct x := by
  unfold primeProduct
  exact Finset.prod_pos fun p hp => primeFactor_pos (mem_primesUpTo.mp hp).1

theorem log_primeProduct (x : ℕ) :
    log (primeProduct x) =
      (primesUpTo x).sum (fun p => log (1 - 1 / (p : ℝ))) := by
  unfold primeProduct
  rw [Real.log_prod]
  intro p hp
  exact (primeFactor_pos (mem_primesUpTo.mp hp).1).ne'

theorem abs_log_one_sub_add_le {t : ℝ} (ht0 : 0 < t) (htle : t ≤ 1 / 2) :
    |log (1 - t) + t| ≤ 2 * t ^ 2 := by
  have hpos : 0 < 1 - t := by linarith
  have hne : 1 - t ≠ 0 := ne_of_gt hpos
  have hub : log (1 - t) ≤ -t := by
    have h := Real.log_le_sub_one_of_pos hpos
    linarith
  have hlb : -t - 2 * t ^ 2 ≤ log (1 - t) := by
    have hrec2 : 1 / (1 - t) ≤ 1 + 2 * t := by
      rw [div_le_iff₀ hpos]
      nlinarith
    have hmul : t / (1 - t) ≤ t * (1 + 2 * t) := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hrec2 (le_of_lt ht0)
    calc
      -t - 2 * t ^ 2 = -(t * (1 + 2 * t)) := by ring
      _ ≤ -(t / (1 - t)) := neg_le_neg hmul
      _ = 1 - (1 - t)⁻¹ := by field_simp [hne]; ring
      _ ≤ log (1 - t) := Real.one_sub_inv_le_log_of_pos hpos
  rw [abs_le]
  constructor <;> nlinarith

theorem abs_log_primeFactor_add_le {p : ℕ} (hp : p.Prime) :
    |log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)| ≤ 2 / (p : ℝ) ^ 2 := by
  have ht0 : 0 < 1 / (p : ℝ) := by
    exact div_pos one_pos (by exact_mod_cast hp.pos)
  have htle : 1 / (p : ℝ) ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (by exact_mod_cast hp.two_le)
  simpa only [div_pow, one_pow, mul_one_div] using
    abs_log_one_sub_add_le ht0 htle

end ErdosStraus.PrimeEstimates.Mertens

/-! ## Chebyshev's functions

The bounds `θ(x) ≤ x log 4`, `ψ(N) - θ(N) ≤ √N log N` and `ψ(x) ≤ (log 4 + 2) x`.
-/

namespace ErdosStraus.PrimeEstimates.Mertens

open Filter Finset Real
open scoped BigOperators ArithmeticFunction

/-- Chebyshev's function `θ(x) = ∑_{p ≤ x} log p`. -/
noncomputable def theta (x : ℝ) : ℝ := ∑ p ∈ primesUpTo ⌊x⌋₊, log p

/-- Chebyshev's function `ψ(x) = ∑_{n ≤ x} Λ(n)`. -/
noncomputable def psi (x : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n

theorem primesUpTo_eq_filter_Icc_one (N : ℕ) :
    primesUpTo N = (Icc 1 N).filter Nat.Prime := by
  ext p
  simp only [mem_primesUpTo, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hp, hpN⟩; exact ⟨⟨hp.one_le, hpN⟩, hp⟩
  · rintro ⟨⟨_, hpN⟩, hp⟩; exact ⟨hp, hpN⟩

theorem theta_floor (x : ℝ) : theta (⌊x⌋₊ : ℝ) = theta x := by
  simp only [theta, Nat.floor_natCast]

theorem psi_floor (x : ℝ) : psi (⌊x⌋₊ : ℝ) = psi x := by
  simp only [psi, Nat.floor_natCast]

/-- Grouping the prime powers `p^k ≤ N` according to the prime `p`. -/
theorem sum_vonMangoldt_mul (N : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, Λ n * f n =
      ∑ p ∈ primesUpTo N, log p * ∑ k ∈ Icc 1 (Nat.log p N), f (p ^ k) := by
  classical
  have hrestrict : ∑ n ∈ Icc 1 N, Λ n * f n =
      ∑ n ∈ (Icc 1 N).filter IsPrimePow, log (n.minFac : ℝ) * f n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    rw [ArithmeticFunction.vonMangoldt_apply]
    split_ifs <;> simp
  have hmaps : ∀ n ∈ (Icc 1 N).filter IsPrimePow, n.minFac ∈ primesUpTo N := by
    intro n hn
    obtain ⟨hnI, hpow⟩ := mem_filter.mp hn
    obtain ⟨h1n, hnN⟩ := mem_Icc.mp hnI
    exact mem_primesUpTo.mpr ⟨Nat.minFac_prime hpow.ne_one,
      (Nat.minFac_le (by omega)).trans hnN⟩
  rw [hrestrict, ← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpp, hpN⟩ := mem_primesUpTo.mp hp
  have hN0 : N ≠ 0 := by have := hpp.two_le; omega
  have hfib : ((Icc 1 N).filter IsPrimePow).filter (fun n => n.minFac = p) =
      (Icc 1 (Nat.log p N)).image (fun k => p ^ k) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨⟨_, hnN⟩, hpow⟩, hmin⟩
      obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpow
      rw [hq.pow_minFac hk.ne'] at hmin
      subst hmin
      exact ⟨k, ⟨hk, Nat.le_log_of_pow_le hq.one_lt hnN⟩, rfl⟩
    · rintro ⟨k, ⟨hk, hkN⟩, rfl⟩
      refine ⟨⟨⟨Nat.one_le_pow _ _ hpp.pos,
        (Nat.pow_le_pow_right hpp.pos hkN).trans (Nat.pow_log_le_self p hN0)⟩,
        hpp.isPrimePow.pow (by omega)⟩, hpp.pow_minFac (by omega)⟩
  have hcongr : ∀ n ∈ ((Icc 1 N).filter IsPrimePow).filter (fun n => n.minFac = p),
      log (n.minFac : ℝ) * f n = log p * f n := by
    intro n hn
    rw [(mem_filter.mp hn).2]
  rw [Finset.sum_congr rfl hcongr, hfib, Finset.sum_image, Finset.mul_sum]
  intro x _ y _ hxy
  exact Nat.pow_right_injective hpp.two_le hxy

/-- `ψ(N) = ∑_{p ≤ N} ⌊log N / log p⌋ log p`. -/
theorem psi_nat (N : ℕ) :
    psi N = ∑ p ∈ primesUpTo N, (Nat.log p N : ℝ) * log p := by
  have h := sum_vonMangoldt_mul N (fun _ => 1)
  simp only [mul_one, sum_const, Nat.card_Icc, nsmul_eq_mul] at h
  rw [psi, Nat.floor_natCast, h]
  apply Finset.sum_congr rfl
  intro p _
  rw [Nat.add_sub_cancel, mul_comm]

/-- Chebyshev's bound `θ(x) ≤ x log 4`. -/
theorem theta_le {x : ℝ} (hx : 0 ≤ x) : theta x ≤ log 4 * x := by
  rw [← theta_floor]
  have h := Estimates.primeLogSum_le_log_four_mul ⌊x⌋₊
  rw [← primesUpTo_eq_filter_Icc_one] at h
  simp only [theta, Nat.floor_natCast]
  exact h.trans (mul_le_mul_of_nonneg_left (Nat.floor_le hx) (log_pos (by norm_num)).le)

/-- The prime powers `p^k ≤ N` with `k ≥ 2` contribute `ψ(N) - θ(N) ≤ √N log N`. -/
theorem psi_sub_theta_nat_le (N : ℕ) :
    psi N - theta N ≤ Real.sqrt N * log N := by
  classical
  rw [psi_nat, theta, Nat.floor_natCast, ← sum_sub_distrib]
  have hlogN : 0 ≤ log (N : ℝ) := Real.log_natCast_nonneg N
  have hterm : ∀ p ∈ primesUpTo N, (Nat.log p N : ℝ) * log p - log p ≤
      if p ≤ Nat.sqrt N then log (N : ℝ) else 0 := by
    intro p hp
    obtain ⟨hpp, hpN⟩ := mem_primesUpTo.mp hp
    have hN0 : N ≠ 0 := by have := hpp.two_le; omega
    have hlogp : 0 ≤ log (p : ℝ) := Real.log_natCast_nonneg p
    have hpow : (Nat.log p N : ℝ) * log p ≤ log N := by
      rw [← Real.log_pow]
      exact log_le_log (by have := hpp.pos; positivity)
        (by exact_mod_cast Nat.pow_log_le_self p hN0)
    split_ifs with hsq
    · linarith
    · have hlt : N < p * p := by
        by_contra h
        exact hsq (Nat.le_sqrt.mpr (not_lt.mp h))
      have hL : Nat.log p N = 1 := Nat.log_eq_one_iff.mpr ⟨hlt, hpp.one_lt, hpN⟩
      simp [hL]
  have hcard : (((primesUpTo N).filter (fun p => p ≤ Nat.sqrt N)).card : ℝ) ≤
      Nat.sqrt N := by
    have hsub : (primesUpTo N).filter (fun p => p ≤ Nat.sqrt N) ⊆ Icc 1 (Nat.sqrt N) := by
      intro p hp
      obtain ⟨hp', hps⟩ := mem_filter.mp hp
      exact mem_Icc.mpr ⟨(mem_primesUpTo.mp hp').1.one_le, hps⟩
    have h := card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at h
    exact_mod_cast h
  calc
    _ ≤ ∑ p ∈ primesUpTo N, (if p ≤ Nat.sqrt N then log (N : ℝ) else 0) :=
      Finset.sum_le_sum hterm
    _ = (((primesUpTo N).filter (fun p => p ≤ Nat.sqrt N)).card : ℝ) * log N := by
      rw [← Finset.sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ (Nat.sqrt N : ℝ) * log N := mul_le_mul_of_nonneg_right hcard hlogN
    _ ≤ Real.sqrt N * log N :=
      mul_le_mul_of_nonneg_right Real.nat_sqrt_le_real_sqrt hlogN

theorem sqrt_mul_log_le {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x * log x ≤ 2 * x := by
  have hlog : log x ≤ 2 * Real.sqrt x := by
    have h := Real.log_le_rpow_div hx (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  rcases le_or_gt (log x) 0 with hl | hl
  · nlinarith [Real.sqrt_nonneg x]
  · calc
      Real.sqrt x * log x ≤ Real.sqrt x * (2 * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg x)
      _ = 2 * x := by rw [← mul_assoc, mul_comm _ 2, mul_assoc, Real.mul_self_sqrt hx]

/-- Chebyshev's bound `ψ(x) ≤ (log 4 + 2) x`. -/
theorem psi_le {x : ℝ} (hx : 0 ≤ x) : psi x ≤ (log 4 + 2) * x := by
  rw [← psi_floor]
  have hle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have h0 : (0 : ℝ) ≤ ⌊x⌋₊ := Nat.cast_nonneg _
  have h1 := psi_sub_theta_nat_le ⌊x⌋₊
  have h2 := theta_le h0
  have h3 := sqrt_mul_log_le h0
  have h4 : (log 4 + 2) * (⌊x⌋₊ : ℝ) ≤ (log 4 + 2) * x :=
    mul_le_mul_of_nonneg_left hle (by have := log_pos (by norm_num : (1 : ℝ) < 4); linarith)
  linarith

end ErdosStraus.PrimeEstimates.Mertens

namespace ErdosStraus

open scoped BigOperators
open Classical

/-! ## Fixed numerators -/

/-- `m/n` is a sum of three positive unit fractions. -/
def fixedNumeratorRepresentable (m n : ℕ) : Prop :=
  ∃ x y z : ℕ,
    0 < x ∧ 0 < y ∧ 0 < z ∧
    (m : ℚ) / (n : ℚ) =
      1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

/-- `E_m(N)`: the number of `1 ≤ n ≤ N` for which `m/n` is not a sum of three
positive unit fractions (Theorem 2). -/
noncomputable def fixedNumeratorExceptionalCount (m N : ℕ) : ℕ :=
  ((Finset.Icc (1 : ℕ) N).filter (fun n => ¬ fixedNumeratorRepresentable m n)).card

/-- Lemma 2.3: if `q = ma - 1`, `e ∣ a^2` and `n ≡ -me (mod q)`, then `m/n` is a sum of
three positive unit fractions. -/
theorem fixed_numerator_representable_of_fixed_fan
    (m n a e : ℕ)
    (hm : 2 ≤ m) (hn : 0 < n) (ha : 0 < a) (he : 0 < e)
    (hedvd : e ∣ a ^ 2)
    (hcong : ErdosStraus.Arithmetic.fixedQ m a ∣ n + m * e) :
    fixedNumeratorRepresentable m n :=
  ErdosStraus.Arithmetic.fixedFan_positive_unit_fractions m n a e hm hn ha he hedvd hcong

/-! ## The prime-counting function -/

/-- `π(N)`: the number of primes `p ≤ N`. -/
noncomputable def primePi (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter Nat.Prime).card

theorem primePi_eq_primeCounting (N : ℕ) :
    primePi N = Nat.primeCounting N := by
  classical
  rw [primePi, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  refine Finset.card_bij (fun p _ => p) ?_ ?_ ?_
  · intro p hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr
          (Nat.lt_succ_of_le (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2),
        (Finset.mem_filter.mp hp).2⟩
  · intro p _ q _ hpq
    exact hpq
  · intro p hp
    exact ⟨p, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr
        ⟨(Finset.mem_filter.mp hp).2.one_lt.le,
          Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)⟩,
        (Finset.mem_filter.mp hp).2⟩, rfl⟩

theorem primePi_nonneg (N : ℕ) : 0 ≤ (primePi N : ℝ) := by
  exact Nat.cast_nonneg _

theorem primePi_le_self (N : ℕ) : primePi N ≤ N := by
  classical
  unfold primePi
  calc
    ((Finset.Icc (1 : ℕ) N).filter Nat.Prime).card
        ≤ (Finset.Icc (1 : ℕ) N).card :=
          Finset.card_filter_le (Finset.Icc (1 : ℕ) N) Nat.Prime
    _ = N := by
          rw [Nat.card_Icc]
          omega

theorem primePi_cast_le_self (N : ℕ) : (primePi N : ℝ) ≤ (N : ℝ) := by
  exact_mod_cast primePi_le_self N

theorem primePi_pos_of_two_le {N : ℕ} (hN : 2 ≤ N) : 0 < primePi N := by
  classical
  unfold primePi
  exact Finset.card_pos.mpr
    ⟨2, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by norm_num, hN⟩, Nat.prime_two⟩⟩

/-- `π(x)` for real `x`: the number of primes `p ≤ x`. -/
noncomputable def realPrimePi (x : ℝ) : ℕ :=
  ((Finset.Icc (1 : ℕ) ⌊x⌋₊).filter Nat.Prime).card

theorem realPrimePi_natCast_eq_primePi (N : ℕ) :
    realPrimePi (N : ℝ) = primePi N := by
  classical
  unfold realPrimePi primePi
  simp

theorem realPrimePi_natCast_eq_primeCounting (N : ℕ) :
    realPrimePi (N : ℝ) = Nat.primeCounting N := by
  rw [realPrimePi_natCast_eq_primePi, primePi_eq_primeCounting]

/-! ## Chebyshev's lower bound

`log binom(2n, n) ≤ ψ(2n)` and `4^n < n binom(2n, n)` give `ψ(2^k) ≫ 2^k`. The prime powers
`p^j ≤ N` with `j ≥ 2` contribute at most `(√N + 1)(log₂ N + 1) log N`, so `θ(N) ≫ N` and
`π(N) ≫ N / log N`.
-/

/-- Chebyshev's function `θ(N) = ∑_{p ≤ N} log p`. -/
noncomputable def primeTheta (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc (1 : ℕ) N).filter Nat.Prime, Real.log (p : ℝ)

/-- Chebyshev's function `ψ(N) = ∑_{n ≤ N} Λ(n)`. -/
noncomputable def chebyshevPsi (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc (1 : ℕ) N, ArithmeticFunction.vonMangoldt n

/-- The logarithm of `4^n < n binom(2n, n)`. -/
theorem log_centralBinom_lower_from_four_pow (n : ℕ) (hn : 4 ≤ n) :
    (n : ℝ) * Real.log 4 - Real.log (n : ℝ) ≤
      Real.log ((Nat.centralBinom n : ℕ) : ℝ) := by
  have hn_pos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 4) hn
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hcb_pos : 0 < ((Nat.centralBinom n : ℕ) : ℝ) := by
    exact_mod_cast Nat.centralBinom_pos n
  have hfour_pow_pos : 0 < (4 : ℝ) ^ n := by positivity
  have hlt_nat : 4 ^ n < n * Nat.centralBinom n :=
    Nat.four_pow_lt_mul_centralBinom n hn
  have hlt_real : (4 : ℝ) ^ n < (n : ℝ) * ((Nat.centralBinom n : ℕ) : ℝ) := by
    exact_mod_cast hlt_nat
  have hlog_lt :
      Real.log ((4 : ℝ) ^ n) <
        Real.log ((n : ℝ) * ((Nat.centralBinom n : ℕ) : ℝ)) :=
    Real.log_lt_log hfour_pow_pos hlt_real
  have hlog_pow : Real.log ((4 : ℝ) ^ n) = (n : ℝ) * Real.log 4 := by
    rw [Real.log_pow]
  have hlog_mul :
      Real.log ((n : ℝ) * ((Nat.centralBinom n : ℕ) : ℝ)) =
      Real.log (n : ℝ) + Real.log ((Nat.centralBinom n : ℕ) : ℝ) := by
    rw [Real.log_mul (ne_of_gt hn_pos) (ne_of_gt hcb_pos)]
  linarith

/-- The exact power of `p` dividing `binom(2n, n)` is at most `2n`. -/
theorem centralBinom_factorization_pow_le_two_mul {n p : ℕ} (hn : 0 < n) :
    p ^ (Nat.centralBinom n).factorization p ≤ 2 * n := by
  have h :
      p ^ (Nat.choose (2 * n) n).factorization p ≤ 2 * n :=
    Nat.pow_factorization_choose_le (p := p) (n := 2 * n) (k := n)
      (mul_pos (by norm_num : 0 < 2) hn)
  simpa [Nat.centralBinom_eq_two_mul_choose] using h

theorem centralBinom_factorization_partial_pow_le_two_mul {n p j : ℕ}
    (hn : 0 < n) (hj : j ≤ (Nat.centralBinom n).factorization p) :
    p ^ j ≤ 2 * n := by
  by_cases hp0 : p = 0
  · subst p
    by_cases hj0 : j = 0
    · rw [hj0, pow_zero]
      omega
    · have hfac_zero : (Nat.centralBinom n).factorization 0 = 0 := by simp
      have : j = 0 := by omega
      exact (hj0 this).elim
  · have hp_pos : 0 < p := Nat.pos_of_ne_zero hp0
    exact (Nat.pow_le_pow_right hp_pos hj).trans
      (centralBinom_factorization_pow_le_two_mul (n := n) (p := p) hn)

theorem centralBinom_primePow_divisor_le_two_mul {n d : ℕ} (hn : 0 < n)
    (hdvd : d ∈ (Nat.centralBinom n).divisors) (hdpp : IsPrimePow d) :
    d ≤ 2 * n := by
  rcases (isPrimePow_nat_iff d).mp hdpp with ⟨p, k, hp, hk, hpk⟩
  rw [← hpk]
  have hC_ne_zero : Nat.centralBinom n ≠ 0 := (Nat.centralBinom_pos n).ne'
  have hdvd' : d ∣ Nat.centralBinom n := (Nat.mem_divisors.mp hdvd).1
  have hpow_dvd : p ^ k ∣ Nat.centralBinom n := by
    rwa [hpk]
  have hk_le : k ≤ (Nat.centralBinom n).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hC_ne_zero).mp hpow_dvd
  exact centralBinom_factorization_partial_pow_le_two_mul hn hk_le

theorem vonMangoldt_sum_eq_sum_filter_primePow (s : Finset ℕ) :
    (∑ d ∈ s, ArithmeticFunction.vonMangoldt d) =
      ∑ d ∈ s.filter IsPrimePow, ArithmeticFunction.vonMangoldt d := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _hd
  by_cases hdpp : IsPrimePow d
  · simp [hdpp]
  · simp [hdpp, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hdpp]

/-- The prime powers `p^j ≤ N` with `j ≥ 2`. -/
noncomputable def nonprimePrimePowerSet (N : ℕ) : Finset ℕ :=
  (Finset.Icc (1 : ℕ) N).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n)

/-- The contribution `ψ(N) - θ(N)` of the prime powers `p^j ≤ N` with `j ≥ 2`. -/
noncomputable def primePowerTail (N : ℕ) : ℝ :=
  ∑ n ∈ nonprimePrimePowerSet N, ArithmeticFunction.vonMangoldt n

theorem nonprime_primePow_minFac_factorization_ge_two {n : ℕ}
    (hnpp : IsPrimePow n) (hnprime : ¬ Nat.Prime n) :
    2 ≤ n.factorization n.minFac := by
  have hpos : 0 < n.factorization n.minFac :=
    Nat.pos_of_ne_zero (Nat.factorization_minFac_ne_zero hnpp.one_lt)
  by_contra hnot
  have heq_one : n.factorization n.minFac = 1 := by omega
  have hpow := hnpp.minFac_pow_factorization_eq
  rw [heq_one, pow_one] at hpow
  apply hnprime
  have hminprime : Nat.Prime n.minFac := Nat.minFac_prime hnpp.ne_one
  simpa [hpow] using hminprime

theorem nonprime_primePow_minFac_sq_le {n : ℕ}
    (hnpp : IsPrimePow n) (hnprime : ¬ Nat.Prime n) :
    n.minFac ^ 2 ≤ n := by
  calc
    n.minFac ^ 2
        ≤ n.minFac ^ n.factorization n.minFac :=
          Nat.pow_le_pow_right (Nat.minFac_pos n)
            (nonprime_primePow_minFac_factorization_ge_two hnpp hnprime)
    _ = n := hnpp.minFac_pow_factorization_eq

theorem nonprime_primePow_minFac_le_sqrt {N n : ℕ} (hnN : n ≤ N)
    (hnpp : IsPrimePow n) (hnprime : ¬ Nat.Prime n) :
    n.minFac ≤ Nat.sqrt N := by
  exact Nat.le_sqrt'.mpr
    ((nonprime_primePow_minFac_sq_le hnpp hnprime).trans hnN)

theorem nonprime_primePow_factorization_minFac_le_log {N n : ℕ} (hnN : n ≤ N)
    (hnpp : IsPrimePow n) :
    n.factorization n.minFac ≤ Nat.log 2 N := by
  have hmin_two : 2 ≤ n.minFac := (Nat.minFac_prime hnpp.ne_one).two_le
  have hpow_two_le_minfac :
      2 ^ n.factorization n.minFac ≤ n.minFac ^ n.factorization n.minFac :=
    Nat.pow_le_pow_left hmin_two _
  have hpow_le_N : 2 ^ n.factorization n.minFac ≤ N := by
    exact hpow_two_le_minfac.trans (by
      rw [hnpp.minFac_pow_factorization_eq]
      exact hnN)
  exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow_le_N

/-- `p^j ↦ (p, j)` maps the prime powers `p^j ≤ N` with `j ≥ 2` injectively to pairs with
`p ≤ √N` and `j ≤ log₂ N`. -/
theorem nonprimePrimePowerSet_card_le_sqrt_mul_log (N : ℕ) :
    (nonprimePrimePowerSet N).card ≤
      (Nat.sqrt N + 1) * (Nat.log 2 N + 1) := by
  classical
  let s := nonprimePrimePowerSet N
  let t := Finset.range (Nat.sqrt N + 1) ×ˢ Finset.range (Nat.log 2 N + 1)
  have hcard : s.card ≤ t.card := by
    apply Finset.card_le_card_of_injOn
      (f := fun n : ℕ => (n.minFac, n.factorization n.minFac))
    · intro n hn
      have hnmem : n ∈ nonprimePrimePowerSet N := by simpa [s] using hn
      have hnIcc : n ∈ Finset.Icc (1 : ℕ) N := (Finset.mem_filter.mp hnmem).1
      have hnN : n ≤ N := (Finset.mem_Icc.mp hnIcc).2
      have hnpp : IsPrimePow n := (Finset.mem_filter.mp hnmem).2.1
      have hnnot : ¬ Nat.Prime n := (Finset.mem_filter.mp hnmem).2.2
      rw [Finset.mem_coe, Finset.mem_product]
      exact ⟨Finset.mem_range.mpr
          (Nat.lt_succ_iff.mpr (nonprime_primePow_minFac_le_sqrt hnN hnpp hnnot)),
        Finset.mem_range.mpr
          (Nat.lt_succ_iff.mpr
            (nonprime_primePow_factorization_minFac_le_log hnN hnpp))⟩
    · intro n hn m hm hpair
      have hnmem : n ∈ nonprimePrimePowerSet N := by simpa [s] using hn
      have hmem : m ∈ nonprimePrimePowerSet N := by simpa [s] using hm
      have hnpp : IsPrimePow n := (Finset.mem_filter.mp hnmem).2.1
      have hmpp : IsPrimePow m := (Finset.mem_filter.mp hmem).2.1
      have hbase : n.minFac = m.minFac := congrArg Prod.fst hpair
      have hexp : n.factorization n.minFac = m.factorization m.minFac :=
        congrArg Prod.snd hpair
      have hexp' : n.factorization m.minFac = m.factorization m.minFac := by
        simpa [hbase] using hexp
      calc
        n = n.minFac ^ n.factorization n.minFac :=
          hnpp.minFac_pow_factorization_eq.symm
        _ = m.minFac ^ m.factorization m.minFac := by rw [hbase, hexp']
        _ = m := hmpp.minFac_pow_factorization_eq
  calc
    s.card ≤ t.card := hcard
    _ = (Nat.sqrt N + 1) * (Nat.log 2 N + 1) := by
      simp [t, Finset.card_product]

theorem primePowerTail_le_card_mul_log (N : ℕ) :
    primePowerTail N ≤ ((nonprimePrimePowerSet N).card : ℝ) * Real.log (N : ℝ) := by
  classical
  unfold primePowerTail
  calc
    (∑ n ∈ nonprimePrimePowerSet N, ArithmeticFunction.vonMangoldt n)
        ≤ ∑ _n ∈ nonprimePrimePowerSet N, Real.log (N : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          have hnmem : n ∈ (Finset.Icc (1 : ℕ) N).filter
              (fun n => IsPrimePow n ∧ ¬ Nat.Prime n) := by
            simpa [nonprimePrimePowerSet] using hn
          have hnIcc : n ∈ Finset.Icc (1 : ℕ) N := (Finset.mem_filter.mp hnmem).1
          have hn_pos : 0 < n := Nat.succ_le_iff.mp (Finset.mem_Icc.mp hnIcc).1
          have hn_le : n ≤ N := (Finset.mem_Icc.mp hnIcc).2
          exact ArithmeticFunction.vonMangoldt_le_log.trans
            (Real.log_le_log (by exact_mod_cast hn_pos) (by exact_mod_cast hn_le))
    _ = ((nonprimePrimePowerSet N).card : ℝ) * Real.log (N : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]

/-- `ψ(N) - θ(N) ≤ (√N + 1)(log₂ N + 1) log N`. -/
theorem primePowerTail_le_sqrt_mul_log_mul_log (N : ℕ) :
    primePowerTail N ≤
      (((Nat.sqrt N + 1) * (Nat.log 2 N + 1) : ℕ) : ℝ) *
        Real.log (N : ℝ) := by
  exact (primePowerTail_le_card_mul_log N).trans
    (mul_le_mul_of_nonneg_right
      (by exact_mod_cast nonprimePrimePowerSet_card_le_sqrt_mul_log N)
      (Real.log_natCast_nonneg N))

theorem chebyshevPsi_eq_primeTheta_add_primePowerTail (N : ℕ) :
    chebyshevPsi N = primeTheta N + primePowerTail N := by
  classical
  unfold chebyshevPsi primeTheta primePowerTail nonprimePrimePowerSet
  rw [vonMangoldt_sum_eq_sum_filter_primePow]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc (1 : ℕ) N).filter IsPrimePow) Nat.Prime
    (fun n => ArithmeticFunction.vonMangoldt n)
  rw [← hsplit]
  congr 1
  · apply Finset.sum_congr
    · ext n
      by_cases hnprime : Nat.Prime n
      · simp [hnprime, hnprime.isPrimePow]
      · simp [hnprime]
    · intro n hn
      exact ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2
  · apply Finset.sum_congr
    · ext n
      simp [and_assoc]
    · intro n _hn
      rfl

/-- `log binom(2n, n) ≤ ψ(2n)`, since every prime power dividing `binom(2n, n)` is at
most `2n`. -/
theorem log_centralBinom_le_chebyshevPsi_two_mul {n : ℕ} (hn : 0 < n) :
    Real.log ((Nat.centralBinom n : ℕ) : ℝ) ≤ chebyshevPsi (2 * n) := by
  rw [← ArithmeticFunction.vonMangoldt_sum (n := Nat.centralBinom n)]
  rw [vonMangoldt_sum_eq_sum_filter_primePow]
  unfold chebyshevPsi
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    rw [Finset.mem_filter] at hd
    have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd.1
    exact Finset.mem_Icc.mpr
      ⟨Nat.succ_le_iff.mpr hd_pos,
        centralBinom_primePow_divisor_le_two_mul hn hd.1 hd.2⟩
  · intro d _hdBig _hdSmall
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- `ψ(2n) ≥ n log 4 - log n` for `n ≥ 4`, from the central binomial
coefficient. -/
theorem chebyshevPsi_two_mul_lower_from_four_pow (n : ℕ) (hn : 4 ≤ n) :
    (n : ℝ) * Real.log 4 - Real.log (n : ℝ) ≤ chebyshevPsi (2 * n) := by
  exact (log_centralBinom_lower_from_four_pow n hn).trans
    (log_centralBinom_le_chebyshevPsi_two_mul
      (lt_of_lt_of_le (by norm_num : 0 < 4) hn))

/-- `ψ(2^k) ≥ (log 4 / 4) 2^k` for `k ≥ 3`. -/
theorem chebyshevPsi_dyadic_lower_bound :
    ∃ cψ > (0 : ℝ), ∀ k : ℕ, 3 ≤ k →
      cψ * ((2 ^ k : ℕ) : ℝ) ≤ chebyshevPsi (2 ^ k) := by
  refine ⟨Real.log 4 / 4, ?_, ?_⟩
  · exact div_pos (Real.log_pos (by norm_num : 1 < (4 : ℝ))) (by norm_num)
  intro k hk
  let m := k - 1
  have hk_eq : k = m + 1 := by omega
  have hm_ge_two : 2 ≤ m := by omega
  have hn_ge_four : 4 ≤ 2 ^ m := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hm_ge_two
  have hpsi :
      (((2 ^ m : ℕ) : ℝ) * Real.log 4 -
          Real.log (((2 ^ m : ℕ) : ℝ))) ≤ chebyshevPsi (2 ^ k) := by
    simpa [hk_eq, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using chebyshevPsi_two_mul_lower_from_four_pow (2 ^ m) hn_ge_four
  have hlog_pow :
      Real.log (((2 ^ m : ℕ) : ℝ)) = (m : ℝ) * Real.log (2 : ℝ) := by
    norm_num [Nat.cast_pow, Real.log_pow]
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
    have hfour : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
    rw [hfour, Real.log_pow]
    norm_num
  have hm_le_pow : (m : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
  have hlog2_nonneg : 0 ≤ Real.log (2 : ℝ) :=
    Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have hlog_le :
      Real.log (((2 ^ m : ℕ) : ℝ)) ≤
        ((2 ^ m : ℕ) : ℝ) * (Real.log 4 / 2) := by
    rw [hlog_pow]
    have hmul :
        (m : ℝ) * Real.log (2 : ℝ) ≤
          ((2 ^ m : ℕ) : ℝ) * Real.log (2 : ℝ) :=
      mul_le_mul_of_nonneg_right hm_le_pow hlog2_nonneg
    nlinarith
  have hpow_cast :
      ((2 ^ k : ℕ) : ℝ) = 2 * ((2 ^ m : ℕ) : ℝ) := by
    have hpow_nat : 2 ^ k = 2 * 2 ^ m := by
      rw [hk_eq, pow_succ, Nat.mul_comm]
    exact_mod_cast hpow_nat
  have hmain :
      (Real.log 4 / 4) * ((2 ^ k : ℕ) : ℝ) ≤
        ((2 ^ m : ℕ) : ℝ) * Real.log 4 -
          Real.log (((2 ^ m : ℕ) : ℝ)) := by
    rw [hpow_cast]
    nlinarith
  exact hmain.trans hpsi

/-- A constant `c > 0` with `ψ(2^k) ≥ c 2^k` for all `k ≥ 3`. -/
noncomputable def chebyshevPsiDyadicLowerConstant : ℝ :=
  Classical.choose chebyshevPsi_dyadic_lower_bound

theorem chebyshevPsiDyadicLowerConstant_pos :
    0 < chebyshevPsiDyadicLowerConstant :=
  (Classical.choose_spec chebyshevPsi_dyadic_lower_bound).1

theorem chebyshevPsiDyadicLowerConstant_bound :
    ∀ k : ℕ, 3 ≤ k →
      chebyshevPsiDyadicLowerConstant * ((2 ^ k : ℕ) : ℝ) ≤ chebyshevPsi (2 ^ k) :=
  (Classical.choose_spec chebyshevPsi_dyadic_lower_bound).2

theorem primeTheta_mono {M N : ℕ} (hMN : M ≤ N) :
    primeTheta M ≤ primeTheta N := by
  classical
  unfold primeTheta
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hp.1).1, le_trans (Finset.mem_Icc.mp hp.1).2 hMN⟩,
      hp.2⟩
  · intro p hp _hpNotSmall
    have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hp_ge_one : (1 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast hpPrime.one_le
    exact Real.log_nonneg hp_ge_one

theorem log_two_le_primeTheta {N : ℕ} (hN : 2 ≤ N) :
    Real.log (2 : ℝ) ≤ primeTheta N := by
  classical
  unfold primeTheta
  exact Finset.single_le_sum (s := (Finset.Icc (1 : ℕ) N).filter Nat.Prime)
    (f := fun p : ℕ => Real.log (p : ℝ))
    (a := (2 : ℕ))
    (by
      intro p hp
      have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2
      exact Real.log_nonneg (by exact_mod_cast hpPrime.one_le))
    (Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by norm_num, hN⟩, by norm_num⟩)

theorem primeTheta_le_primePi_mul_log (N : ℕ) :
    primeTheta N ≤ (primePi N : ℝ) * Real.log (N : ℝ) := by
  classical
  unfold primeTheta primePi
  calc
    (∑ p ∈ (Finset.Icc (1 : ℕ) N).filter Nat.Prime, Real.log (p : ℝ))
        ≤ ∑ _p ∈ (Finset.Icc (1 : ℕ) N).filter Nat.Prime,
            Real.log (N : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          have hpIcc : p ∈ Finset.Icc (1 : ℕ) N := (Finset.mem_filter.mp hp).1
          have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2
          have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
          have hp_le_N : (p : ℝ) ≤ (N : ℝ) := by
            exact_mod_cast (Finset.mem_Icc.mp hpIcc).2
          exact Real.log_le_log hp_pos hp_le_N
    _ = (((Finset.Icc (1 : ℕ) N).filter Nat.Prime).card : ℝ) *
        Real.log (N : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]

/-- `θ(N) ≫ N` implies `π(N) ≫ N/log N`, since `θ(N) ≤ π(N) log N`. -/
theorem realPrimePi_lower_bound_of_primeTheta_lower_bound
    (hθ :
      ∃ cθ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
        cθ * (N : ℝ) ≤ primeTheta N) :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      c₀ * (N : ℝ) / Real.log (N : ℝ) ≤
        (realPrimePi (N : ℝ) : ℝ) := by
  rcases hθ with ⟨cθ, hcθ, htheta_lower⟩
  refine ⟨cθ, hcθ, ?_⟩
  intro N hN
  have hN_gt_one : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (by omega : (1 : ℕ) < N)
  have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos hN_gt_one
  have htheta_upper := primeTheta_le_primePi_mul_log N
  have hkey : cθ * (N : ℝ) ≤ (primePi N : ℝ) * Real.log (N : ℝ) :=
    (htheta_lower N hN).trans htheta_upper
  have hpi :
      cθ * (N : ℝ) / Real.log (N : ℝ) ≤ (primePi N : ℝ) := by
    rw [div_le_iff₀ hlog_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hkey
  simpa [realPrimePi_natCast_eq_primePi N] using hpi

/-- A dyadic lower bound `θ(2^k) ≫ 2^k` implies `θ(N) ≫ N` for all `N ≥ 3`,
by monotonicity of `θ`. -/
theorem primeTheta_lower_bound_of_dyadic_lower_bound
    (hθ :
      ∃ cθ > (0 : ℝ), ∀ k : ℕ, 1 ≤ k →
        cθ * ((2 ^ k : ℕ) : ℝ) ≤ primeTheta (2 ^ k)) :
    ∃ cθ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      cθ * (N : ℝ) ≤ primeTheta N := by
  rcases hθ with ⟨cθ, hcθ, htheta_dyadic⟩
  refine ⟨cθ / 2, half_pos hcθ, ?_⟩
  intro N hN
  let k := Nat.log 2 N
  have hN_ne_zero : N ≠ 0 := by omega
  have hpow_le_N : 2 ^ k ≤ N := Nat.pow_log_le_self 2 hN_ne_zero
  have hk_ge_one : 1 ≤ k := by
    exact Nat.le_log_of_pow_le (by norm_num : 1 < 2)
      (by simpa [k] using (by omega : 2 ^ 1 ≤ N))
  have hN_le_pow_succ : N ≤ 2 ^ (k + 1) := by
    exact Nat.le_of_lt (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N)
  have hN_le_two_pow : (N : ℝ) ≤ 2 * ((2 ^ k : ℕ) : ℝ) := by
    have hcast : (N : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by
      exact_mod_cast hN_le_pow_succ
    calc
      (N : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := hcast
      _ = 2 * ((2 ^ k : ℕ) : ℝ) := by
        simp [pow_succ, mul_comm]
  have hscaled :
      (cθ / 2) * (N : ℝ) ≤ cθ * ((2 ^ k : ℕ) : ℝ) := by
    nlinarith [hcθ, hN_le_two_pow]
  exact hscaled.trans ((htheta_dyadic k hk_ge_one).trans (primeTheta_mono hpow_le_N))

/-- If `ψ(2^k) - θ(2^k) ≤ (c/2) 2^k` for all large `k`, with `c` the constant
`chebyshevPsiDyadicLowerConstant`, then `θ(2^k) ≫ 2^k` for all `k ≥ 1`. The finitely many
small `k` are covered by `θ(2^k) ≥ log 2`. -/
theorem primeTheta_dyadic_lower_bound_of_eventual_tail_dominated
    (hTail : ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      primePowerTail (2 ^ k) ≤
        (chebyshevPsiDyadicLowerConstant / 2) * ((2 ^ k : ℕ) : ℝ)) :
    ∃ c > (0 : ℝ), ∀ k : ℕ, 1 ≤ k →
      c * ((2 ^ k : ℕ) : ℝ) ≤ primeTheta (2 ^ k) := by
  rcases hTail with ⟨K, hTail⟩
  let L := max K 3
  let cLarge := chebyshevPsiDyadicLowerConstant / 2
  let cSmall := Real.log (2 : ℝ) / ((2 ^ L : ℕ) : ℝ)
  let c := min cLarge cSmall
  have hcLarge : 0 < cLarge :=
    half_pos chebyshevPsiDyadicLowerConstant_pos
  have hpowL_pos : 0 < ((2 ^ L : ℕ) : ℝ) := by positivity
  have hcSmall : 0 < cSmall :=
    div_pos (Real.log_pos (by norm_num : 1 < (2 : ℝ))) hpowL_pos
  refine ⟨c, lt_min hcLarge hcSmall, ?_⟩
  intro k hk1
  by_cases hLk : L ≤ k
  · have hKk : K ≤ k := le_trans (le_max_left K 3) hLk
    have hk3 : 3 ≤ k := le_trans (le_max_right K 3) hLk
    have hlarge : cLarge * ((2 ^ k : ℕ) : ℝ) ≤ primeTheta (2 ^ k) := by
      have hpsi := chebyshevPsiDyadicLowerConstant_bound k hk3
      have htail := hTail k hKk
      rw [chebyshevPsi_eq_primeTheta_add_primePowerTail] at hpsi
      dsimp [cLarge]
      nlinarith
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans hlarge
  · have hk_le_L : k ≤ L := by omega
    have hpow_le : ((2 ^ k : ℕ) : ℝ) ≤ ((2 ^ L : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) hk_le_L
    have hsmall_bound : cSmall * ((2 ^ k : ℕ) : ℝ) ≤ Real.log (2 : ℝ) := by
      dsimp [cSmall]
      rw [div_mul_eq_mul_div]
      rw [div_le_iff₀ hpowL_pos]
      nlinarith [Real.log_pos (by norm_num : 1 < (2 : ℝ)), hpow_le]
    have hc_le : c * ((2 ^ k : ℕ) : ℝ) ≤ cSmall * ((2 ^ k : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
    have htwo_le : 2 ≤ 2 ^ k := by
      have hpow : 2 ^ 1 ≤ 2 ^ k :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) hk1
      simpa using hpow
    exact (hc_le.trans hsmall_bound).trans
      (log_two_le_primeTheta (N := 2 ^ k) htwo_le)

/-- The ratio `(√N + 1)(log₂ N + 1) log N / N` at `N = 2^k`. -/
noncomputable def dyadicPrimePowerTailEnvelopeRatio (k : ℕ) : ℝ :=
  ((((Nat.sqrt (2 ^ k) + 1) * (Nat.log 2 (2 ^ k) + 1) : ℕ) : ℝ) *
      Real.log (((2 ^ k : ℕ) : ℝ))) / ((2 ^ k : ℕ) : ℝ)

theorem dyadicPrimePowerTailEnvelopeRatio_nonneg (k : ℕ) :
    0 ≤ dyadicPrimePowerTailEnvelopeRatio k := by
  unfold dyadicPrimePowerTailEnvelopeRatio
  positivity

theorem dyadicPrimePowerTailEnvelopeRatio_le_exp_decay {k : ℕ} (hk : 1 ≤ k) :
    dyadicPrimePowerTailEnvelopeRatio k ≤
      4 * (k : ℝ) ^ 2 * Real.exp (-(Real.log 2 / 2) * (k : ℝ)) := by
  unfold dyadicPrimePowerTailEnvelopeRatio
  let X : ℝ := ((2 ^ k : ℕ) : ℝ)
  have hX_pos : 0 < X := by positivity
  have hX_nonneg : 0 ≤ X := hX_pos.le
  have hX_ge_one : 1 ≤ X := by
    dsimp [X]
    exact_mod_cast (by
      have hpow : 2 ^ 0 ≤ 2 ^ k :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.zero_le k)
      simpa using hpow)
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hlog2_pos : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num : 1 < (2 : ℝ))
  have hlog2_nonneg : 0 ≤ Real.log (2 : ℝ) := hlog2_pos.le
  have hlog2_le_one : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ))
    norm_num at h
    exact h
  have hnatlog : Nat.log 2 (2 ^ k) = k :=
    Nat.log_pow (by norm_num : 1 < 2) k
  have hlogX :
      Real.log X = (k : ℝ) * Real.log (2 : ℝ) := by
    dsimp [X]
    norm_num [Nat.cast_pow, Real.log_pow]
  have hlogX_nonneg : 0 ≤ Real.log X := by
    rw [hlogX]
    positivity
  have hlogX_le_k : Real.log X ≤ (k : ℝ) := by
    rw [hlogX]
    nlinarith [mul_le_mul_of_nonneg_left hlog2_le_one hk_pos.le]
  have hsqrt_le :
      (Nat.sqrt (2 ^ k) : ℝ) ≤ X ^ ((1 : ℝ) / 2) := by
    dsimp [X]
    simpa [Real.sqrt_eq_rpow] using
      (Real.nat_sqrt_le_real_sqrt (a := 2 ^ k))
  have hXhalf_ge_one : 1 ≤ X ^ ((1 : ℝ) / 2) :=
    Real.one_le_rpow hX_ge_one (by norm_num : 0 ≤ (1 : ℝ) / 2)
  have hsqrt_succ_le :
      ((Nat.sqrt (2 ^ k) + 1 : ℕ) : ℝ) ≤
        2 * X ^ ((1 : ℝ) / 2) := by
    norm_num
    nlinarith
  have hsqrt_succ_le' :
      (Nat.sqrt (2 ^ k) : ℝ) + 1 ≤
        2 * X ^ ((1 : ℝ) / 2) := by
    simpa [Nat.cast_add] using hsqrt_succ_le
  have hnatlog_succ_le :
      ((Nat.log 2 (2 ^ k) + 1 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by
    rw [hnatlog]
    have hk_one_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    norm_num
    linarith
  have hnatlog_succ_le' :
      (Nat.log 2 (2 ^ k) : ℝ) + 1 ≤ 2 * (k : ℝ) := by
    simpa [Nat.cast_add] using hnatlog_succ_le
  have hprod_log_le :
      (((Nat.sqrt (2 ^ k) + 1) * (Nat.log 2 (2 ^ k) + 1) : ℕ) : ℝ) *
          Real.log X ≤
        (2 * X ^ ((1 : ℝ) / 2)) * (2 * (k : ℝ)) * (k : ℝ) := by
    have hprod :
        (((Nat.sqrt (2 ^ k) + 1) * (Nat.log 2 (2 ^ k) + 1) : ℕ) : ℝ) ≤
          (2 * X ^ ((1 : ℝ) / 2)) * (2 * (k : ℝ)) := by
      norm_num [Nat.cast_mul, Nat.cast_add]
      exact mul_le_mul hsqrt_succ_le' (by rwa [hnatlog] at hnatlog_succ_le')
        (by positivity) (by positivity)
    exact mul_le_mul hprod hlogX_le_k hlogX_nonneg (by positivity)
  calc
    ((((Nat.sqrt (2 ^ k) + 1) * (Nat.log 2 (2 ^ k) + 1) : ℕ) : ℝ) *
          Real.log (((2 ^ k : ℕ) : ℝ))) / ((2 ^ k : ℕ) : ℝ)
        = ((((Nat.sqrt (2 ^ k) + 1) * (Nat.log 2 (2 ^ k) + 1) : ℕ) : ℝ) *
          Real.log X) / X := rfl
    _ ≤ ((2 * X ^ ((1 : ℝ) / 2)) * (2 * (k : ℝ)) * (k : ℝ)) / X :=
        div_le_div_of_nonneg_right hprod_log_le hX_nonneg
    _ = 4 * (k : ℝ) ^ 2 * (X ^ ((1 : ℝ) / 2) / X) := by ring
    _ = 4 * (k : ℝ) ^ 2 * Real.exp (-(Real.log 2 / 2) * (k : ℝ)) := by
      have hX_eq : X = (2 : ℝ) ^ k := by
        dsimp [X]
        norm_num [Nat.cast_pow]
      have hXhalf_div :
          X ^ ((1 : ℝ) / 2) / X =
            Real.exp (-(Real.log 2 / 2) * (k : ℝ)) := by
        rw [hX_eq]
        have hpow_pos : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
        rw [Real.rpow_def_of_pos hpow_pos]
        rw [← Real.exp_log hpow_pos]
        rw [← Real.exp_sub]
        congr 1
        rw [Real.log_pow]
        rw [Real.log_exp]
        ring_nf
      rw [hXhalf_div]

theorem dyadicPrimePowerTailEnvelopeRatio_tendsto_zero :
    Filter.Tendsto dyadicPrimePowerTailEnvelopeRatio Filter.atTop (nhds 0) := by
  have hdecay :
      Filter.Tendsto
        (fun k : ℕ =>
          4 * (k : ℝ) ^ 2 * Real.exp (-(Real.log 2 / 2) * (k : ℝ)))
        Filter.atTop (nhds 0) := by
    have hb : 0 < Real.log (2 : ℝ) / 2 := by
      positivity
    have hreal :
        Filter.Tendsto
          (fun x : ℝ => x ^ (2 : ℝ) * Real.exp (-(Real.log 2 / 2) * x))
          Filter.atTop (nhds 0) :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ) (Real.log 2 / 2) hb
    have hnat := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Real.rpow_natCast, mul_assoc] using hnat.const_mul (4 : ℝ)
  refine squeeze_zero' ?_ ?_ hdecay
  · exact Filter.Eventually.of_forall dyadicPrimePowerTailEnvelopeRatio_nonneg
  · filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    exact dyadicPrimePowerTailEnvelopeRatio_le_exp_decay hk

theorem dyadicPrimePowerTailEnvelope_eventually_le_const_mul
    {c : ℝ} (hc : 0 < c) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      (((Nat.sqrt (2 ^ k) + 1) * (Nat.log 2 (2 ^ k) + 1) : ℕ) : ℝ) *
          Real.log (((2 ^ k : ℕ) : ℝ)) ≤
        c * ((2 ^ k : ℕ) : ℝ) := by
  have hsmall :
      ∀ᶠ k : ℕ in Filter.atTop, dyadicPrimePowerTailEnvelopeRatio k ≤ c :=
    dyadicPrimePowerTailEnvelopeRatio_tendsto_zero.eventually_le_const hc
  rcases Filter.eventually_atTop.mp hsmall with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk
  have hratio := hK k hk
  unfold dyadicPrimePowerTailEnvelopeRatio at hratio
  have hden_pos : 0 < (((2 ^ k : ℕ) : ℝ)) := by positivity
  rw [div_le_iff₀ hden_pos] at hratio
  simpa [mul_comm, mul_left_comm, mul_assoc] using hratio

/-- `θ(2^k) ≫ 2^k` as soon as the bound `(√N + 1)(log₂ N + 1) log N` for `ψ(N) - θ(N)`
is eventually at most half the lower bound for `ψ(N)`, `N = 2^k`. -/
theorem primeTheta_dyadic_lower_bound_of_envelope
    (hEnv : ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      (((Nat.sqrt (2 ^ k) + 1) * (Nat.log 2 (2 ^ k) + 1) : ℕ) : ℝ) *
          Real.log (((2 ^ k : ℕ) : ℝ)) ≤
        (chebyshevPsiDyadicLowerConstant / 2) * ((2 ^ k : ℕ) : ℝ)) :
    ∃ c > (0 : ℝ), ∀ k : ℕ, 1 ≤ k →
      c * ((2 ^ k : ℕ) : ℝ) ≤ primeTheta (2 ^ k) := by
  apply primeTheta_dyadic_lower_bound_of_eventual_tail_dominated
  rcases hEnv with ⟨K, hEnv⟩
  refine ⟨K, ?_⟩
  intro k hk
  exact (primePowerTail_le_sqrt_mul_log_mul_log (2 ^ k)).trans (hEnv k hk)

/-- `θ(2^k) ≫ 2^k` for `k ≥ 1`. -/
theorem primeTheta_dyadic_lower_bound :
    ∃ cθ > (0 : ℝ), ∀ k : ℕ, 1 ≤ k →
      cθ * ((2 ^ k : ℕ) : ℝ) ≤ primeTheta (2 ^ k) := by
  apply primeTheta_dyadic_lower_bound_of_envelope
  exact dyadicPrimePowerTailEnvelope_eventually_le_const_mul
    (half_pos chebyshevPsiDyadicLowerConstant_pos)

/-- Chebyshev lower bound `θ(N) ≫ N` for `N ≥ 3`. -/
theorem primeTheta_lower_bound :
    ∃ cθ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      cθ * (N : ℝ) ≤ primeTheta N :=
  primeTheta_lower_bound_of_dyadic_lower_bound primeTheta_dyadic_lower_bound

/-- `π(N) ≫ N/log N` for the real prime-counting function, from `θ(N) ≫ N`. -/
theorem realPrimePi_lower_bound :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      c₀ * (N : ℝ) / Real.log N ≤ (realPrimePi (N : ℝ) : ℝ) :=
  realPrimePi_lower_bound_of_primeTheta_lower_bound primeTheta_lower_bound

/-- `π(N) ≫ N/log N`, stated with `Nat.primeCounting`. -/
theorem primeCounting_lower_bound :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      c₀ * (N : ℝ) / Real.log N ≤ (Nat.primeCounting N : ℝ) := by
  rcases realPrimePi_lower_bound with ⟨c₀, hc₀, hreal⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro N hN
  simpa [realPrimePi_natCast_eq_primeCounting N] using hreal N hN

/-- `π(N) ≫ N/log N` for `N ≥ 3`. -/
theorem primePi_lower_bound :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N → c₀ * (N : ℝ) / Real.log N ≤ (primePi N : ℝ) := by
  obtain ⟨c₀, hc₀, hpi⟩ := primeCounting_lower_bound
  exact ⟨c₀, hc₀, fun N hN => by
    simpa [primePi_eq_primeCounting N] using hpi N hN⟩

/-- `π(N) ≫ N/log N` together with `0 < log N` and `0 < π(N)`, for `N ≥ 3`. -/
theorem primePi_lower_bound_and_pos :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      0 < Real.log N ∧ 0 < (primePi N : ℝ) ∧
        c₀ * (N : ℝ) / Real.log N ≤ (primePi N : ℝ) := by
  rcases primePi_lower_bound with ⟨c₀, hc₀, hpi⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro N hN
  have hN_gt_one : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (by omega : 1 < N)
  have hlog_pos : 0 < Real.log N := Real.log_pos hN_gt_one
  have hpi_pos : 0 < (primePi N : ℝ) := by
    exact_mod_cast primePi_pos_of_two_le (by omega : 2 ≤ N)
  exact ⟨hlog_pos, hpi_pos, hpi N hN⟩

/-- `π(N) ≫ N/log N` together with `0 < log N`, `0 < π(N) ≤ N` and `|π(N)| ≤ N`, for
`N ≥ 3`. -/
theorem primePi_lower_bound_and_le_self :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      0 < Real.log N ∧
        0 < (primePi N : ℝ) ∧
        c₀ * (N : ℝ) / Real.log N ≤ (primePi N : ℝ) ∧
        (primePi N : ℝ) ≤ (N : ℝ) ∧
        |(primePi N : ℝ)| ≤ (N : ℝ) := by
  rcases primePi_lower_bound_and_pos with ⟨c₀, hc₀, h⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro N hN
  rcases h N hN with ⟨hlog_pos, hpi_pos, hlower⟩
  have hupper : (primePi N : ℝ) ≤ (N : ℝ) := primePi_cast_le_self N
  exact ⟨hlog_pos, hpi_pos, hlower, hupper, by
    rw [abs_of_nonneg hpi_pos.le]
    exact hupper⟩

/-! ## Exceptional primes

The remark after Theorem 1: the number of exceptional primes up to `N` is
`≪ π(N) exp(-c(log N)^{3/4})` after decreasing `c`. -/

/-- If `E(N) ≪ N·exp(-c(log N)^{3/4})`, then the same bound holds for the
number `#𝒫_exc(N)` of exceptional primes, since
`primeExceptionalCount N ≤ exceptionalCount N`. -/
theorem prime_exceptional_of_main (h : IsMainBound exceptionalCount) :
    IsMainBound primeExceptionalCount :=
  IsMainBound.of_le primeExceptionalCount_le h

/-- If `E(N) ≪ N·exp(-c(log N)^{3/4})`, then for `N ≥ 3`
`#𝒫_exc(N) ≤ C' · π(N) · log N · exp(-c(log N)^{3/4})`, using
`N ≤ c₀⁻¹ π(N) log N`. -/
theorem prime_exceptional_le_primePi (h : IsMainBound exceptionalCount) :
    ∃ c > (0 : ℝ), ∃ C' > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      (primeExceptionalCount N : ℝ) ≤ C' * (primePi N : ℝ) * Real.log N * saving c N := by
  obtain ⟨c, hc, C, hC, hmain⟩ := prime_exceptional_of_main h
  obtain ⟨c₀, hc₀, hpi⟩ := primePi_lower_bound_and_le_self
  refine ⟨c, hc, C / c₀, by positivity, fun N hN => ?_⟩
  have hpi_data := hpi N hN
  have hlogN_pos : 0 < Real.log N := hpi_data.1
  have hsav_pos : 0 < saving c N := Real.exp_pos _
  have hkey : c₀ * (N : ℝ) ≤ (primePi N : ℝ) * Real.log N := by
    have := hpi_data.2.2.1
    rw [div_le_iff₀ hlogN_pos] at this
    linarith
  have hmb := hmain N hN
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  calc (primeExceptionalCount N : ℝ)
      ≤ C * N * saving c N := hmb
    _ = (C / c₀) * (c₀ * (N : ℝ)) * saving c N := by
        field_simp
    _ ≤ (C / c₀) * ((primePi N : ℝ) * Real.log N) * saving c N := by
        apply mul_le_mul_of_nonneg_right _ hsav_pos.le
        apply mul_le_mul_of_nonneg_left hkey
        positivity
    _ = (C / c₀) * (primePi N : ℝ) * Real.log N * saving c N := by ring

/-- A factor `log N` is absorbed by halving the constant in `exp(-c (log N)^{3/4})`. -/
theorem log_mul_saving_absorb {c₁ : ℝ} (hc₁ : 0 < c₁) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ N : ℕ, 3 ≤ N → Real.log N * saving c₁ N ≤ C * saving c N := by
  set c : ℝ := c₁ / 2 with hc
  refine ⟨c, by positivity, 1 + 16 / c₁ ^ 2, by positivity, ?_⟩
  intro N hN
  set L : ℝ := Real.log N with hLdef
  have hL0 : 0 < L := log_pos_of_three_le hN
  set t : ℝ := L ^ ((3 : ℝ) / 4) with htdef
  have ht0 : 0 < t := Real.rpow_pos_of_pos hL0 _
  have hsave₁ : saving c₁ N = Real.exp (-c₁ * t) := by
    unfold saving
    rw [← hLdef, ← htdef]
  have hsaveC : saving c N = Real.exp (-c * t) := by
    unfold saving
    rw [← hLdef, ← htdef]
  rw [hsave₁, hsaveC]
  have hLbound : L ≤ 1 + t ^ 2 := by
    have : t ^ ((4 : ℝ) / 3) = L := by
      rw [htdef]
      exact rpow_three_quarters_four_thirds hL0.le
    calc L = t ^ ((4 : ℝ) / 3) := this.symm
      _ ≤ 1 + t ^ 2 := rpow_four_thirds_le ht0.le
  have hquad : t ^ 2 ≤ (16 / c₁ ^ 2) * Real.exp (c * t) := by
    have hct : 0 ≤ c * t := by positivity
    have h := sq_le_four_mul_exp hct
    have hcsq : (c * t) ^ 2 = c ^ 2 * t ^ 2 := by ring
    have hcpos : 0 < c ^ 2 := by positivity
    have hdiv : t ^ 2 ≤ (4 / c ^ 2) * Real.exp (c * t) := by
      rw [hcsq] at h
      rw [div_mul_eq_mul_div, le_div_iff₀ hcpos]
      nlinarith [h]
    have hcc : c ^ 2 = c₁ ^ 2 / 4 := by rw [hc]; ring
    have e : (4 : ℝ) / c ^ 2 = 16 / c₁ ^ 2 := by
      rw [hcc]
      field_simp [ne_of_gt hc₁]
      ring
    rwa [← e]
  have hone : (1 : ℝ) ≤ Real.exp (c * t) := by
    exact Real.one_le_exp (by positivity)
  have hLexp : L ≤ (1 + 16 / c₁ ^ 2) * Real.exp (c * t) := by
    calc L ≤ 1 + t ^ 2 := hLbound
      _ ≤ Real.exp (c * t) + (16 / c₁ ^ 2) * Real.exp (c * t) :=
          add_le_add hone hquad
      _ = (1 + 16 / c₁ ^ 2) * Real.exp (c * t) := by ring
  calc L * Real.exp (-c₁ * t)
      ≤ ((1 + 16 / c₁ ^ 2) * Real.exp (c * t)) * Real.exp (-c₁ * t) := by
          exact mul_le_mul_of_nonneg_right hLexp (Real.exp_pos _).le
    _ = (1 + 16 / c₁ ^ 2) * Real.exp (-c * t) := by
        calc
          ((1 + 16 / c₁ ^ 2) * Real.exp (c * t)) * Real.exp (-c₁ * t)
              = (1 + 16 / c₁ ^ 2) * (Real.exp (c * t) * Real.exp (-c₁ * t)) := by ring
          _ = (1 + 16 / c₁ ^ 2) * Real.exp (c * t + (-c₁ * t)) := by
              rw [← Real.exp_add]
          _ = (1 + 16 / c₁ ^ 2) * Real.exp (-c * t) := by
              congr 1
              rw [hc]
              ring_nf

/-- The remark after Theorem 1: if `E(N) ≪ N·exp(-c(log N)^{3/4})`, then, after decreasing
the constant in the exponential to absorb the factor `log N`,
`#𝒫_exc(N) ≤ C π(N) exp(-c(log N)^{3/4})`. -/
theorem prime_exceptional_le_primePi_saving (h : IsMainBound exceptionalCount) :
    ∃ c > (0 : ℝ), ∃ C' > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      (primeExceptionalCount N : ℝ) ≤ C' * (primePi N : ℝ) * saving c N := by
  obtain ⟨c₁, hc₁, C₁, hC₁, hprime⟩ := prime_exceptional_le_primePi h
  obtain ⟨c, hc, Clog, hClog, hlog⟩ := log_mul_saving_absorb hc₁
  refine ⟨c, hc, C₁ * Clog, by positivity, fun N hN => ?_⟩
  have hpi_nonneg : 0 ≤ (primePi N : ℝ) := primePi_nonneg N
  have hlog' :
      (primePi N : ℝ) * Real.log N * saving c₁ N
        ≤ (primePi N : ℝ) * (Clog * saving c N) := by
    calc (primePi N : ℝ) * Real.log N * saving c₁ N
        = (primePi N : ℝ) * (Real.log N * saving c₁ N) := by ring
      _ ≤ (primePi N : ℝ) * (Clog * saving c N) :=
          mul_le_mul_of_nonneg_left (hlog N hN) hpi_nonneg
  have hprime_assoc :
      (primeExceptionalCount N : ℝ)
        ≤ C₁ * ((primePi N : ℝ) * Real.log N * saving c₁ N) := by
    calc
      (primeExceptionalCount N : ℝ)
          ≤ C₁ * (primePi N : ℝ) * Real.log N * saving c₁ N := hprime N hN
      _ = C₁ * ((primePi N : ℝ) * Real.log N * saving c₁ N) := by ring
  calc
    (primeExceptionalCount N : ℝ)
        ≤ C₁ * ((primePi N : ℝ) * Real.log N * saving c₁ N) := hprime_assoc
    _ ≤ C₁ * ((primePi N : ℝ) * (Clog * saving c N)) :=
        mul_le_mul_of_nonneg_left hlog' hC₁.le
    _ = (C₁ * Clog) * (primePi N : ℝ) * saving c N := by ring

/-- If `#𝒫_exc(N) ≪ N·exp(-c(log N)^{3/4})`, then
`#𝒫_exc(N) ≤ C' · π(N) · log N · exp(-c(log N)^{3/4})`, by `π(N) ≫ N/log N`. -/
theorem prime_bound_le_primePi (h : IsMainBound primeExceptionalCount) :
    ∃ c > (0 : ℝ), ∃ C' > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      (primeExceptionalCount N : ℝ) ≤ C' * (primePi N : ℝ) * Real.log N * saving c N := by
  obtain ⟨c, hc, C, hC, hmain⟩ := h
  obtain ⟨c₀, hc₀, hpi⟩ := primePi_lower_bound_and_le_self
  refine ⟨c, hc, C / c₀, by positivity, fun N hN => ?_⟩
  have hpi_data := hpi N hN
  have hlogN_pos : 0 < Real.log N := hpi_data.1
  have hsav_pos : 0 < saving c N := Real.exp_pos _
  have hkey : c₀ * (N : ℝ) ≤ (primePi N : ℝ) * Real.log N := by
    have := hpi_data.2.2.1
    rw [div_le_iff₀ hlogN_pos] at this
    linarith
  have hmb := hmain N hN
  calc (primeExceptionalCount N : ℝ)
      ≤ C * N * saving c N := hmb
    _ = (C / c₀) * (c₀ * (N : ℝ)) * saving c N := by
        field_simp [ne_of_gt hc₀]
    _ ≤ (C / c₀) * ((primePi N : ℝ) * Real.log N) * saving c N := by
        apply mul_le_mul_of_nonneg_right _ hsav_pos.le
        apply mul_le_mul_of_nonneg_left hkey
        positivity
    _ = (C / c₀) * (primePi N : ℝ) * Real.log N * saving c N := by ring

end ErdosStraus
