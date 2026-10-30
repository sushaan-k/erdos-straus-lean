import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Tactic
import Mathlib.Analysis.PSeries
import ErdosStraus.Estimates.Chebyshev
import Mathlib.MeasureTheory.Function.Floor
import Batteries.Tactic.Lemma
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AlmostPrime
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import ErdosStraus.Estimates.RoughProducts
import ErdosStraus.Estimates.PartialSummation

/-! # Lemma 3.1: Mertens' theorems

Mertens' first theorem `∑_{p ≤ x} log p / p = log x + O(1)`, from Legendre's identity for
`log n!`, and his second theorem `∑_{p ≤ x} 1/p = log log x + B + O(1/log x)`, by Abel
summation. From these follow `∏_{p ≤ x} (1 - 1/p)^{-1} ≍ log x` and
`∏_{z < p ≤ x} (1 + 1/p) ≍ log x / log z`; `prime_estimates` collects them, with Chebyshev's
bound `θ(x) ≪ x`, in the form of Lemma 3.1.
-/

/-! ## The integral of `1/(t (log t)²)` -/

namespace ErdosStraus.PrimeEstimates.Mertens

open Filter MeasureTheory Real Set
open scoped Topology

theorem hasDerivAt_neg_inv_log {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t : ℝ => -(log t)⁻¹) (x⁻¹ / (log x) ^ 2) x := by
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hl0 : log x ≠ 0 := (log_pos hx).ne'
  refine ((Real.hasDerivAt_log hx0).inv hl0).neg.congr_deriv ?_
  simp [div_eq_mul_inv]

theorem inv_log_tendsto_zero :
    Tendsto (fun t : ℝ => -(log t)⁻¹) atTop (𝓝 0) := by
  simpa using Real.tendsto_log_atTop.inv_tendsto_atTop.neg

theorem integrableOn_inv_div_log_sq_Ioi {x : ℝ} (hx : 1 < x) :
    IntegrableOn (fun t : ℝ => t⁻¹ / (log t) ^ 2) (Ioi x) := by
  apply integrableOn_Ioi_deriv_of_nonneg' (g := fun t : ℝ => -(log t)⁻¹)
    (l := 0) (fun t ht => hasDerivAt_neg_inv_log (hx.trans_le ht))
    (fun t ht => div_nonneg (inv_nonneg.mpr (zero_lt_one.trans (hx.trans ht)).le)
      (sq_nonneg _)) inv_log_tendsto_zero

theorem integral_inv_div_log_sq_Ioi {x : ℝ} (hx : 1 < x) :
    (∫ t in Ioi x, t⁻¹ / (log t) ^ 2) = 1 / log x := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (g := fun t : ℝ => -(log t)⁻¹)
    (l := 0) (fun t ht => hasDerivAt_neg_inv_log (hx.trans_le ht))
    (fun t ht => div_nonneg (inv_nonneg.mpr (zero_lt_one.trans (hx.trans ht)).le)
      (sq_nonneg _)) inv_log_tendsto_zero
  simpa using h

theorem integral_interval_sub_Ioi {f : ℝ → ℝ} {a x : ℝ}
    (hf : IntegrableOn f (Ioi a)) (hx : a ≤ x) :
    (∫ t in a..x, f t) - (∫ t in Ioi a, f t) = -(∫ t in Ioi x, f t) := by
  have hdisj : Disjoint (Ioc a x) (Ioi x) := by
    apply Set.disjoint_left.mpr
    intro t ht ht'
    exact (not_lt_of_ge ht.2) ht'
  have h := setIntegral_union hdisj measurableSet_Ioi
    (hf.mono_set Ioc_subset_Ioi_self) (hf.mono_set (Ioi_subset_Ioi hx))
  rw [Ioc_union_Ioi_eq_Ioi hx] at h
  rw [intervalIntegral.integral_of_le hx]
  linarith

end ErdosStraus.PrimeEstimates.Mertens

/-! ## Legendre's identity and Mertens' first theorem at integers

Counting prime factors of `n!` gives `log n! = ∑_{d ≤ n} Λ(d) ⌊n/d⌋`, hence
`0 ≤ n ∑_{d ≤ n} Λ(d)/d - log n! ≤ ψ(n)`. Together with
`log n! = n log n + O(n)`, `ψ(n) ≪ n` and the bounded contribution of proper
prime powers this gives `∑_{p ≤ n} log p / p = log n + O(1)`.
-/

namespace ErdosStraus.PrimeEstimates.Mertens

open Finset Real
open scoped BigOperators ArithmeticFunction Nat

/-- `log n! = ∑_{m ≤ n} log m`. -/
theorem log_factorial_eq_sum_log (n : ℕ) :
    log (n ! : ℝ) = ∑ m ∈ Icc 1 n, log (m : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity), ih,
      Finset.sum_Icc_succ_top (by omega)]
    ring

/-- Legendre's identity `log n! = ∑_{d ≤ n} Λ(d) ⌊n/d⌋`. -/
theorem log_factorial_eq (n : ℕ) :
    log (n ! : ℝ) = ∑ d ∈ Icc 1 n, Λ d * ((n / d : ℕ) : ℝ) := by
  rw [log_factorial_eq_sum_log]
  have hdiv : ∀ m ∈ Icc 1 n, log (m : ℝ) = ∑ d ∈ m.divisors, Λ d := fun m _ =>
    ArithmeticFunction.vonMangoldt_sum.symm
  rw [Finset.sum_congr rfl hdiv,
    Finset.sum_comm' (t' := Icc 1 n) (s' := fun d => (Icc 1 n).filter (fun m => d ∣ m))]
  · apply Finset.sum_congr rfl
    intro d _
    have hIcc : Icc 1 n = Ioc 0 n := Finset.Icc_add_one_left_eq_Ioc 0 n
    rw [sum_const, nsmul_eq_mul, hIcc, Nat.Ioc_filter_dvd_card_eq_div, mul_comm]
  · intro m d
    simp only [mem_Icc, Nat.mem_divisors, mem_filter]
    constructor
    · rintro ⟨⟨h1, hm⟩, hdm, -⟩
      exact ⟨⟨⟨h1, hm⟩, hdm⟩, Nat.pos_of_dvd_of_pos hdm h1, (Nat.le_of_dvd h1 hdm).trans hm⟩
    · rintro ⟨⟨⟨h1, hm⟩, hdm⟩, -, -⟩
      exact ⟨⟨h1, hm⟩, hdm, by omega⟩

/-- `⌊n/d⌋ ≤ n/d ≤ ⌊n/d⌋ + 1`. -/
theorem natDiv_le_div_le (n d : ℕ) (hd : 0 < d) :
    ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d ∧ (n : ℝ) / d ≤ ((n / d : ℕ) : ℝ) + 1 := by
  refine ⟨Nat.cast_div_le, ?_⟩
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_le_iff₀ hdr]
  have h3 : (n : ℝ) = d * (n / d : ℕ) + (n % d : ℕ) := by exact_mod_cast (Nat.div_add_mod n d).symm
  have h4 : ((n % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt n hd).le
  nlinarith

/-- `0 ≤ n ∑_{d ≤ n} Λ(d)/d - log n! ≤ ψ(n)`. -/
theorem legendre_bounds (n : ℕ) :
    0 ≤ n * ∑ d ∈ Icc 1 n, Λ d / d - log (n ! : ℝ) ∧
      n * ∑ d ∈ Icc 1 n, Λ d / d - log (n ! : ℝ) ≤ psi n := by
  have heq : (n : ℝ) * ∑ d ∈ Icc 1 n, Λ d / d - log (n ! : ℝ) =
      ∑ d ∈ Icc 1 n, Λ d * ((n : ℝ) / d - ((n / d : ℕ) : ℝ)) := by
    rw [log_factorial_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [heq]
  constructor
  · apply Finset.sum_nonneg
    intro d hd
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (sub_nonneg.mpr (natDiv_le_div_le n d (mem_Icc.mp hd).1).1)
  · rw [psi, Nat.floor_natCast]
    apply Finset.sum_le_sum
    intro d hd
    have h := natDiv_le_div_le n d (mem_Icc.mp hd).1
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (by linarith)

/-- `log n! = n log n + O(n)`. -/
theorem log_factorial_bounds (n : ℕ) :
    n * log n - n ≤ log (n ! : ℝ) ∧ log (n ! : ℝ) ≤ n * log n := by
  have hfpos : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  constructor
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have h := Real.pow_div_factorial_le_exp (n : ℝ) hnpos.le n
      have hl := Real.log_le_log (by positivity) h
      rw [Real.log_exp, Real.log_div (by positivity) hfpos.ne', Real.log_pow] at hl
      linarith
  · rw [← Real.log_pow]
    exact Real.log_le_log hfpos (by exact_mod_cast Nat.factorial_le_pow n)

/-- The proper prime powers `p ^ k ≤ N`, `k ≥ 2`, weighted by `log p / p ^ k`. -/
noncomputable def primePowerTail (N : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo N, ∑ k ∈ Icc 2 (Nat.log p N), log p / (p : ℝ) ^ k

/-- `∑_{d ≤ N} Λ(d)/d` splits into the primes and the proper prime powers. -/
theorem sum_vonMangoldt_div_eq (N : ℕ) :
    ∑ d ∈ Icc 1 N, Λ d / d = (∑ p ∈ primesUpTo N, log p / p) + primePowerTail N := by
  have h := sum_vonMangoldt_mul N (fun d => 1 / (d : ℝ))
  simp only [mul_one_div] at h
  rw [h, primePowerTail, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpp, hpN⟩ := mem_primesUpTo.mp hp
  have hL : 1 ≤ Nat.log p N := Nat.log_pos hpp.one_lt hpN
  rw [← Finset.insert_Icc_add_one_left_eq_Icc hL, Finset.sum_insert (by simp), mul_add,
    Finset.mul_sum]
  push_cast
  simp only [pow_one, mul_one_div]

/-- `log n / (n (n - 1)) ≥ 0`. -/
theorem primePowerWeight_nonneg (n : ℕ) :
    0 ≤ log (n : ℝ) / (n * ((n : ℝ) - 1)) := by
  apply div_nonneg (Real.log_natCast_nonneg n)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith

/-- `log n / (n (n - 1)) ≤ 4 n^{-3/2}`. -/
theorem primePowerWeight_le (n : ℕ) :
    log (n : ℝ) / (n * ((n : ℝ) - 1)) ≤ 4 * (1 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hpos : (0 : ℝ) < n := by linarith
    have hlog := Real.log_le_rpow_div hpos.le (by norm_num : (0 : ℝ) < 1 / 2)
    have hnn : (n : ℝ) * n = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_add hpos]; norm_num; ring
    have h32 : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hpos _
    have h12 : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hpos _
    rw [div_le_iff₀ (by nlinarith)]
    calc
      log (n : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) := hlog
      _ = 4 * (1 / (n : ℝ) ^ (3 / 2 : ℝ)) * (n * n / 2) := by
        rw [hnn]; field_simp; ring
      _ ≤ 4 * (1 / (n : ℝ) ^ (3 / 2 : ℝ)) * (n * ((n : ℝ) - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith

/-- `∑_{n ≥ 2} log n / (n (n - 1)) < ∞`. -/
theorem summable_primePowerWeight :
    Summable fun n : ℕ => log (n : ℝ) / (n * ((n : ℝ) - 1)) :=
  Summable.of_nonneg_of_le primePowerWeight_nonneg primePowerWeight_le
    ((Real.summable_one_div_nat_rpow.mpr (by norm_num)).mul_left 4)

/-- The proper prime powers contribute a bounded amount:
`∑_p ∑_{j ≥ 2} log p / p ^ j ≤ ∑_{n ≥ 2} log n / (n (n - 1))`. -/
theorem primePowerTail_bounds (N : ℕ) :
    0 ≤ primePowerTail N ∧
      primePowerTail N ≤ ∑' n : ℕ, log (n : ℝ) / (n * ((n : ℝ) - 1)) := by
  constructor
  · apply Finset.sum_nonneg
    intro p _
    apply Finset.sum_nonneg
    intro k _
    exact div_nonneg (Real.log_natCast_nonneg p) (by positivity)
  · calc
      primePowerTail N ≤ ∑ p ∈ primesUpTo N, log (p : ℝ) / (p * ((p : ℝ) - 1)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpp := (mem_primesUpTo.mp hp).1
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
        have hlogp : 0 ≤ log (p : ℝ) := Real.log_natCast_nonneg p
        have hset : Icc 2 (Nat.log p N) = Ico 2 (Nat.log p N + 1) := by
          ext k; simp only [mem_Icc, mem_Ico]; omega
        have hgeom : ∑ k ∈ Icc 2 (Nat.log p N), (1 / (p : ℝ)) ^ k ≤
            (1 / (p : ℝ)) ^ 2 / (1 - 1 / p) := by
          rw [hset]
          have hx : (0 : ℝ) ≤ 1 / p := by positivity
          have h'x : 1 / (p : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
          rcases le_or_gt 2 (Nat.log p N + 1) with hmn | hmn
          · rw [geom_sum_Ico' h'x.ne hmn]
            apply div_le_div₀ (pow_nonneg hx _) _ (sub_pos.2 h'x) le_rfl
            exact sub_le_self _ (pow_nonneg hx _)
          · rw [Ico_eq_empty (by omega), sum_empty]
            exact div_nonneg (pow_nonneg hx _) (sub_nonneg.2 h'x.le)
        have hval : (1 / (p : ℝ)) ^ 2 / (1 - 1 / p) = 1 / (p * ((p : ℝ) - 1)) := by
          have hp0 : (p : ℝ) ≠ 0 := by linarith
          have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
          field_simp
        calc
          ∑ k ∈ Icc 2 (Nat.log p N), log (p : ℝ) / (p : ℝ) ^ k =
              log (p : ℝ) * ∑ k ∈ Icc 2 (Nat.log p N), (1 / (p : ℝ)) ^ k := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            rw [one_div_pow, mul_one_div]
          _ ≤ log (p : ℝ) * (1 / (p * ((p : ℝ) - 1))) :=
            mul_le_mul_of_nonneg_left (hgeom.trans hval.le) hlogp
          _ = log (p : ℝ) / (p * ((p : ℝ) - 1)) := mul_one_div _ _
      _ ≤ ∑' n : ℕ, log (n : ℝ) / (n * ((n : ℝ) - 1)) :=
        summable_primePowerWeight.sum_le_tsum _ (fun n _ => primePowerWeight_nonneg n)

/-- Mertens' first theorem at integers: `∑_{p ≤ n} log p / p = log n + O(1)`. -/
theorem mertensFirst_nat :
    ∃ C > 0, ∀ n : ℕ, |(∑ p ∈ primesUpTo n, log p / p) - log n| ≤ C := by
  set D := ∑' n : ℕ, log (n : ℝ) / (n * ((n : ℝ) - 1))
  have hD0 : 0 ≤ D := tsum_nonneg primePowerWeight_nonneg
  have hlog4 : 0 < log (4 : ℝ) := log_pos (by norm_num)
  refine ⟨log 4 + 3 + D, by linarith, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [primesUpTo_eq_empty_of_le_one (by norm_num)]
    simp only [sum_empty, Nat.cast_zero, log_zero, sub_zero, abs_zero]
    linarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hL0, hL1⟩ := legendre_bounds n
  obtain ⟨hF0, hF1⟩ := log_factorial_bounds n
  have hpsi := psi_le hnr.le
  have hsplit := sum_vonMangoldt_div_eq n
  obtain ⟨hT0, hT1⟩ := primePowerTail_bounds n
  set S := ∑ d ∈ Icc 1 n, Λ d / d
  set B := ∑ p ∈ primesUpTo n, log (p : ℝ) / p
  have hS_lo : log n - 1 ≤ S := by
    have h : (n : ℝ) * (log n - 1) ≤ n * S := by nlinarith
    exact le_of_mul_le_mul_left h hnr
  have hS_hi : S ≤ log n + (log 4 + 2) := by
    have h : (n : ℝ) * S ≤ n * (log n + (log 4 + 2)) := by nlinarith
    exact le_of_mul_le_mul_left h hnr
  rw [abs_le]
  constructor <;> linarith

end ErdosStraus.PrimeEstimates.Mertens

/-! ## Mertens' first theorem for real `x`

`B₁(x) = ∑_{p ≤ x} log p / p = log x + O(1)` for all real `x ≥ 2`, deduced from
the integer case, and the bounded remainder `R(x) = B₁(x) - log x`.
-/

namespace ErdosStraus.PrimeEstimates.Mertens

open Finset Real
open scoped BigOperators

/-- Comparison of `log x` with `log ⌊x⌋` for `x ≥ 2`. -/
theorem floor_log_bounds {x : ℝ} (hx : 2 ≤ x) :
    0 < log (⌊x⌋₊ : ℝ) ∧ log (⌊x⌋₊ : ℝ) ≤ log x ∧
      log x ≤ 2 * log (⌊x⌋₊ : ℝ) ∧ log x - log (⌊x⌋₊ : ℝ) ≤ log 2 := by
  let n := ⌊x⌋₊
  have hn : 2 ≤ n := Nat.le_floor hx
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn2 : (2 : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hnx : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxn : x ≤ 2 * (n : ℝ) := by have hh := Nat.lt_floor_add_one x; dsimp [n] at *; linarith
  have hln : 0 < log (n : ℝ) := log_pos (by linarith)
  have hlog2 : log (2 : ℝ) ≤ log n := log_le_log (by norm_num) hn2
  have hup : log x ≤ log 2 + log n := by
    have hh := log_le_log (by linarith : 0 < x) hxn
    rwa [log_mul (by norm_num) hnp.ne'] at hh
  exact ⟨hln, log_le_log hnp hnx, by linarith, by linarith⟩

/-- Mertens' first theorem: `∑_{p ≤ x} log p / p = log x + O(1)` for real `x ≥ 2`. -/
theorem mertensFirst :
    ∃ C > 0, ∀ x : ℝ, 2 ≤ x →
      |(∑ p ∈ primesUpTo ⌊x⌋₊, log p / p) - log x| ≤ C := by
  obtain ⟨C, hC, h⟩ := mertensFirst_nat
  refine ⟨C + log 2 + 1, by positivity, ?_⟩
  intro x hx
  obtain ⟨hlp, hle, h2, hgap⟩ := floor_log_bounds hx
  have heq : (∑ p ∈ primesUpTo ⌊x⌋₊, log p / p) - log x =
      ((∑ p ∈ primesUpTo ⌊x⌋₊, log p / p) - log (⌊x⌋₊ : ℝ)) -
        (log x - log (⌊x⌋₊ : ℝ)) := by ring
  rw [heq]
  exact (abs_sub _ _).trans (by rw [abs_of_nonneg (sub_nonneg.mpr hle)]; linarith [h ⌊x⌋₊])

/-- `B₁(x) = ∑_{p ≤ x} log p / p`. -/
noncomputable def primeLogReciprocal (x : ℝ) : ℝ := ∑ p ∈ primesUpTo ⌊x⌋₊, log p / p

/-- The remainder `R(x) = B₁(x) - log x` in Mertens' first theorem. -/
noncomputable def mertensRemainder (x : ℝ) : ℝ := primeLogReciprocal x - log x

/-- `R(x) = B₁(x) - log x` is bounded on `[2, ∞)`. -/
theorem mertensRemainder_bound :
    ∃ C > 0, ∀ x : ℝ, 2 ≤ x → |mertensRemainder x| ≤ C :=
  mertensFirst

/-- `B₁(x)` as a prefix sum of prime-supported coefficients. -/
theorem primeLogReciprocal_eq_sum_Icc (x : ℝ) :
    primeLogReciprocal x =
      ∑ n ∈ Icc 0 ⌊x⌋₊, if n.Prime then log (n : ℝ) / n else 0 := by
  rw [primeLogReciprocal, primesUpTo, sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext n
  simp only [mem_range, mem_Icc]
  omega

theorem measurable_primeLogReciprocal : Measurable primeLogReciprocal :=
  (measurable_of_countable
    (fun N : ℕ => ∑ p ∈ primesUpTo N, log (p : ℝ) / p)).comp Nat.measurable_floor

theorem measurable_mertensRemainder : Measurable mertensRemainder :=
  measurable_primeLogReciprocal.sub measurable_log

end ErdosStraus.PrimeEstimates.Mertens

/-! ## Mertens' second theorem

Abel summation against `B₁` gives
`∑_{p ≤ x} 1/p = B₁(x)/log x + ∫_2^x B₁(t)/(t (log t)²) dt`.
Writing `B₁(t) = log t + R(t)` with `R` bounded, the error integral converges
with tail `O(1/log x)`, so `∑_{p ≤ x} 1/p = log log x + B + O(1/log x)`.
-/

namespace ErdosStraus.PrimeEstimates.Mertens

open Filter Finset MeasureTheory Real
open scoped BigOperators

/-- A function dominated by `C / (t (log t)²)` has tail integral at most `C / log x`. -/
theorem norm_integral_Ioi_le_div_log {f : ℝ → ℝ} {x C : ℝ} (hx : 1 < x)
    (hbound : ∀ t ∈ Set.Ioi x, ‖f t‖ ≤ C * (t⁻¹ / (log t) ^ 2)) :
    ‖∫ t in Set.Ioi x, f t‖ ≤ C / log x := by
  have hk : IntegrableOn (fun t : ℝ => t⁻¹ / (log t) ^ 2) (Set.Ioi x) volume :=
    integrableOn_inv_div_log_sq_Ioi hx
  have hCk : IntegrableOn (fun t : ℝ => C * (t⁻¹ / (log t) ^ 2)) (Set.Ioi x) volume :=
    hk.const_mul C
  calc
    ‖∫ t in Set.Ioi x, f t‖ ≤ ∫ t in Set.Ioi x, C * (t⁻¹ / (log t) ^ 2) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hCk
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hbound t ht
    _ = C * ∫ t in Set.Ioi x, t⁻¹ / (log t) ^ 2 := by rw [integral_const_mul]
    _ = C / log x := by rw [integral_inv_div_log_sq_Ioi hx]; ring

/-- `(1 / log t)' = -1 / (t (log t)²)`. -/
theorem hasDerivAt_inv_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun u : ℝ => (log u)⁻¹) (-(t⁻¹ / (log t) ^ 2)) t := by
  convert (hasDerivAt_neg_inv_log ht).neg using 1
  · rfl
  · rfl
  ext u
  simp

/-- Abel summation against `B₁`:
`∑_{p ≤ x} 1/p = B₁(x)/log x + ∫_2^x B₁(t)/(t (log t)²) dt`. -/
theorem primeReciprocalSum_abel {x : ℝ} (hx : 2 ≤ x) :
    primeReciprocalSum ⌊x⌋₊ =
      primeLogReciprocal x / log x +
        ∫ t in (2 : ℝ)..x, primeLogReciprocal t / (t * (log t) ^ 2) := by
  let c : ℕ → ℝ := fun n => if n.Prime then log (n : ℝ) / n else 0
  let f : ℝ → ℝ := fun u => (log u)⁻¹
  have hderiv : ∀ t : ℝ, 1 < t → deriv f t = -(t⁻¹ / (log t) ^ 2) :=
    fun t ht => (hasDerivAt_inv_log ht).deriv
  have hf : ∀ t ∈ Set.Icc 2 x, DifferentiableAt ℝ f t :=
    fun t ht => (hasDerivAt_inv_log (by linarith [ht.1])).differentiableAt
  have hfi : IntegrableOn (deriv f) (Set.Icc 2 x) := by
    have hc : ContinuousOn (fun t : ℝ => -(t⁻¹ / (log t) ^ 2)) (Set.Icc 2 x) := by
      have hlog : ContinuousOn log (Set.Icc 2 x) := fun t ht =>
        (Real.continuousAt_log (by linarith [ht.1])).continuousWithinAt
      refine (((continuousOn_id' _).inv₀ fun t ht => ?_).div (hlog.pow 2) fun t ht => ?_).neg
      · exact (show (0 : ℝ) < t by linarith [ht.1]).ne'
      · exact pow_ne_zero 2 (log_pos (by linarith [ht.1])).ne'
    exact hc.integrableOn_Icc.congr_fun
      (fun t ht => (hderiv t (by linarith [ht.1])).symm) measurableSet_Icc
  have h := sum_mul_eq_sub_sub_integral_mul c (by norm_num : (0 : ℝ) ≤ 2) hx hf hfi
  have hfloor : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
  simp only [Nat.floor_ofNat] at h
  rw [sum_Ioc_eq_prefix_sub (fun n => f n * c n) hfloor] at h
  have hinit : (∑ n ∈ Icc (0 : ℕ) 2, f n * c n) = f 2 * ∑ n ∈ Icc (0 : ℕ) 2, c n := by
    norm_num [c, Finset.sum_Icc_succ_top]
  have hB : ∀ t : ℝ, (∑ n ∈ Icc 0 ⌊t⌋₊, c n) = primeLogReciprocal t :=
    fun t => (primeLogReciprocal_eq_sum_Icc t).symm
  have hsum : (∑ n ∈ Icc 0 ⌊x⌋₊, f n * c n) = primeReciprocalSum ⌊x⌋₊ := by
    unfold primeReciprocalSum primesUpTo
    have hset : range (⌊x⌋₊ + 1) = Icc 0 ⌊x⌋₊ := by
      ext n
      simp only [mem_range, mem_Icc]
      omega
    rw [hset, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hp : n.Prime
    · have hl : log (n : ℝ) ≠ 0 := (log_pos (by exact_mod_cast hp.one_lt)).ne'
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      simp only [c, f, hp, if_true]
      field_simp
    · simp [c, hp]
  rw [hinit, hsum] at h
  simp_rw [hB] at h
  rw [← intervalIntegral.integral_of_le hx] at h
  have hint : -(∫ t in (2 : ℝ)..x, deriv f t * primeLogReciprocal t) =
      ∫ t in (2 : ℝ)..x, primeLogReciprocal t / (t * (log t) ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : t ≠ 0 := by linarith
    have hl0 : log t ≠ 0 := (log_pos ht1).ne'
    simp only [hderiv t ht1]
    field_simp
  have hfx : f x * primeLogReciprocal x = primeLogReciprocal x / log x := by
    simp only [f]; ring
  linarith

/-- The integrand `R(t) / (t (log t)²)` of the remainder in Mertens' second theorem. -/
noncomputable def mertensKernel (t : ℝ) : ℝ := mertensRemainder t * (t⁻¹ / (log t) ^ 2)

theorem measurable_mertensKernel : Measurable mertensKernel :=
  measurable_mertensRemainder.mul (measurable_inv.div (measurable_log.pow_const 2))

/-- `|R(t) / (t (log t)²)| ≤ C / (t (log t)²)` whenever `|R(t)| ≤ C`. -/
theorem norm_mertensKernel_le {C t : ℝ} (ht : 0 ≤ t) (hR : |mertensRemainder t| ≤ C) :
    ‖mertensKernel t‖ ≤ C * (t⁻¹ / (log t) ^ 2) := by
  have hpos : 0 ≤ t⁻¹ / (log t) ^ 2 := by positivity
  rw [Real.norm_eq_abs, mertensKernel, abs_mul, abs_of_nonneg hpos]
  exact mul_le_mul_of_nonneg_right hR hpos

/-- The error integral `∫_2^∞ R(t) / (t (log t)²) dt` converges. -/
theorem integrableOn_mertensKernel : IntegrableOn mertensKernel (Set.Ioi 2) := by
  obtain ⟨C, _, hR⟩ := mertensRemainder_bound
  have hg : IntegrableOn (fun t : ℝ => C * (t⁻¹ / (log t) ^ 2)) (Set.Ioi 2) :=
    (integrableOn_inv_div_log_sq_Ioi (by norm_num)).const_mul C
  refine hg.mono' measurable_mertensKernel.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht2 : (2 : ℝ) ≤ t := le_of_lt ht
  exact norm_mertensKernel_le (by linarith) (hR t ht2)

/-- The constant `B` in `∑_{p ≤ x} 1/p = log log x + B + O(1/log x)`. -/
noncomputable def mertensSecondConstant : ℝ :=
  1 - log (log 2) + ∫ t in Set.Ioi (2 : ℝ), mertensKernel t

/-- The remainder in Mertens' second theorem:
`∑_{p ≤ x} 1/p - log log x - B = R(x)/log x - ∫_x^∞ R(t)/(t (log t)²) dt`. -/
theorem mertensSecond_error_eq {x : ℝ} (hx : 2 ≤ x) :
    primeReciprocalSum ⌊x⌋₊ - (log (log x) + mertensSecondConstant) =
      mertensRemainder x / log x - ∫ t in Set.Ioi x, mertensKernel t := by
  have hlx : 0 < log x := log_pos (by linarith)
  have hlog : ContinuousOn log (Set.Icc 2 x) := fun t ht =>
    (Real.continuousAt_log (by linarith [ht.1])).continuousWithinAt
  have hK : IntervalIntegrable mertensKernel volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mpr
      (integrableOn_mertensKernel.mono_set Set.Ioc_subset_Ioi_self)
  have hL : IntervalIntegrable (fun t : ℝ => t⁻¹ / log t) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    refine ((continuousOn_id' _).inv₀ fun t ht => ?_).div hlog fun t ht => ?_
    · exact (show (0 : ℝ) < t by linarith [ht.1]).ne'
    · exact (log_pos (by linarith [ht.1])).ne'
  have hsplit : (∫ t in (2 : ℝ)..x, primeLogReciprocal t / (t * (log t) ^ 2)) =
      (∫ t in (2 : ℝ)..x, t⁻¹ / log t) + ∫ t in (2 : ℝ)..x, mertensKernel t := by
    rw [← intervalIntegral.integral_add hL hK]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl0 : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
    simp only [mertensKernel, mertensRemainder]
    field_simp
    ring
  have hloglog : (∫ t in (2 : ℝ)..x, t⁻¹ / log t) = log (log x) - log (log 2) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hL
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl0 : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
    exact (Real.hasDerivAt_log ht0).log hl0
  have htail := integral_interval_sub_Ioi integrableOn_mertensKernel hx
  have hBx : primeLogReciprocal x / log x = 1 + mertensRemainder x / log x := by
    unfold mertensRemainder
    field_simp
    ring
  rw [primeReciprocalSum_abel hx, hsplit, hloglog, hBx]
  unfold mertensSecondConstant
  linarith

/-- Mertens' second theorem: `∑_{p ≤ x} 1/p = log log x + B + O(1/log x)`. -/
theorem mertensSecond :
    ∃ C > 0, ∀ x : ℝ, 2 ≤ x →
      |primeReciprocalSum ⌊x⌋₊ - (log (log x) + mertensSecondConstant)| ≤ C / log x := by
  obtain ⟨C, hC, hR⟩ := mertensRemainder_bound
  refine ⟨2 * C, by positivity, fun x hx => ?_⟩
  have hlx : 0 < log x := log_pos (by linarith)
  rw [mertensSecond_error_eq hx]
  have h1 : |mertensRemainder x / log x| ≤ C / log x := by
    rw [abs_div, abs_of_pos hlx]
    exact div_le_div_of_nonneg_right (hR x hx) hlx.le
  have h2 : ‖∫ t in Set.Ioi x, mertensKernel t‖ ≤ C / log x :=
    norm_integral_Ioi_le_div_log (by linarith) fun t ht =>
      norm_mertensKernel_le (by linarith [ht.out]) (hR t (hx.trans ht.out.le))
  rw [Real.norm_eq_abs] at h2
  calc
    _ ≤ |mertensRemainder x / log x| + |∫ t in Set.Ioi x, mertensKernel t| := abs_sub _ _
    _ ≤ C / log x + C / log x := add_le_add h1 h2
    _ = 2 * C / log x := by ring

/-- Natural-number form of Mertens' second theorem. -/
theorem mertensSecond_nat :
    ∃ C > 0, ∀ n : ℕ, 2 ≤ n →
      |primeReciprocalSum n - (log (log n) + mertensSecondConstant)| ≤
        C / log n := by
  obtain ⟨C, hC, h⟩ := mertensSecond
  exact ⟨C, hC, fun n hn => by simpa [Nat.floor_natCast] using h n (by exact_mod_cast hn)⟩

/-- `∑_{p ≤ N} 1/p - log log N` is eventually bounded above. -/
theorem sharp_upper : Estimates.PrimeRecipSharpMertensNatDefectEventuallyUpperBound := by
  obtain ⟨C, hC, h⟩ := mertensSecond_nat
  refine ⟨mertensSecondConstant + C / log 2, eventually_atTop.mpr ⟨2, ?_⟩⟩
  intro N hN
  have hset : (Icc 2 N).filter Nat.Prime = primesUpTo N := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, mem_primesUpTo]
    constructor
    · rintro ⟨⟨_, hpN⟩, hp⟩; exact ⟨hp, hpN⟩
    · rintro ⟨hp, hpN⟩; exact ⟨⟨hp.two_le, hpN⟩, hp⟩
  have hln : log (2 : ℝ) ≤ log N :=
    log_le_log (by norm_num) (Nat.cast_le.mpr hN)
  have hh := (abs_le.mp (h N hN)).2
  have hdiv := div_le_div_of_nonneg_left hC.le
    (log_pos (by norm_num : (1 : ℝ) < 2)) hln
  unfold Estimates.primeRecipSharpMertensNatDefect
  rw [hset]
  have hfinal : primeReciprocalSum N - log (log N) ≤ mertensSecondConstant + C / log 2 := by
    linarith
  simpa only [primeReciprocalSum, one_div] using hfinal

end ErdosStraus.PrimeEstimates.Mertens

namespace ErdosStraus.PrimeEstimates

open Finset
open scoped BigOperators

/-- `∑_{k ≤ K} 1/k² ≤ 2`, by telescoping against `2(1/k - 1/(k+1))`. -/
theorem sum_reciprocal_sq_le_two (K : ℕ) :
    (∑ k ∈ Icc 1 K, (1 : ℝ) / (k : ℝ) ^ 2) ≤ 2 := by
  have hdom : (∑ k ∈ Icc 1 K, (1 : ℝ) / (k : ℝ) ^ 2) ≤
      ∑ k ∈ Icc 1 K, 2 * (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    have hnextpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    calc
      (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 / ((k : ℝ) * ((k : ℝ) + 1)) := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hkpos) (mul_pos hkpos hnextpos)).mpr
        nlinarith
      _ = 2 * (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) := by
        field_simp
        ring
  have hset : Icc 1 K = Ico 1 (K + 1) := by ext k; simp only [mem_Icc, mem_Ico]; omega
  have htel : (∑ k ∈ Icc 1 K, 2 * (1 / (k : ℝ) - 1 / ((k : ℝ) + 1))) =
      2 * (1 - 1 / ((K + 1 : ℕ) : ℝ)) := by
    rw [hset, ← Finset.mul_sum]
    have hh := sum_Ico_weight_differences (fun k : ℕ => (1 : ℝ) / k)
      (m := 1) (n := K + 1) (by omega)
    simpa only [Nat.cast_add, Nat.cast_one, div_one] using
      congrArg (fun y : ℝ => 2 * y) hh
  rw [htel] at hdom
  have hnonneg : (0 : ℝ) ≤ 1 / ((K + 1 : ℕ) : ℝ) := by positivity
  linarith

end ErdosStraus.PrimeEstimates

/-! ## Euler products at integers -/

namespace ErdosStraus.PrimeEstimates.Mertens

open Filter Finset Real
open scoped BigOperators

theorem primesUpTo_eq_filter_Icc (n : ℕ) :
    primesUpTo n = (Icc 0 n).filter Nat.Prime := by
  ext p
  simp only [mem_primesUpTo, mem_filter, mem_Icc, Nat.zero_le, true_and]
  tauto

theorem prime_square_sum_le_two (n : ℕ) :
    (∑ p ∈ primesUpTo n, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 2 := by
  apply le_trans _ (sum_reciprocal_sq_le_two n)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp', hpn⟩ := mem_primesUpTo.mp hp
    exact mem_Icc.mpr ⟨hp'.pos, hpn⟩
  · intro p _ _; positivity

/-- `∑_{p ≤ n} 1/p - log log n` is bounded for `n ≥ 2`. -/
theorem reciprocal_defect_bounded :
    ∃ E > 0, ∀ n : ℕ, 2 ≤ n →
      |primeReciprocalSum n - log (log n)| ≤ E := by
  obtain ⟨C, hC, h⟩ := mertensSecond_nat
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  refine ⟨C / log 2 + |mertensSecondConstant| + 1, by positivity, ?_⟩
  intro n hn
  have hln : log (2 : ℝ) ≤ log n := log_le_log (by norm_num) (by exact_mod_cast hn)
  have hh := (h n hn).trans (div_le_div_of_nonneg_left hC.le hl2 hln)
  have heq : primeReciprocalSum n - log (log n) =
      (primeReciprocalSum n - (log (log n) + mertensSecondConstant)) +
        mertensSecondConstant := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith)

/-- The difference `∑_{p ≤ n} (-log(1 - 1/p) - 1/p)` between `-log ∏_{p ≤ n} (1 - 1/p)` and
`∑_{p ≤ n} 1/p`. -/
noncomputable def correction (n : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo n, (-log (1 - 1 / (p : ℝ)) - 1 / p)

theorem correction_bounds (n : ℕ) : 0 ≤ correction n ∧ correction n ≤ 4 := by
  have hlocal : ∀ p ∈ primesUpTo n,
      0 ≤ -log (1 - 1 / (p : ℝ)) - 1 / p ∧
        -log (1 - 1 / (p : ℝ)) - 1 / p ≤ 2 / (p : ℝ) ^ 2 := by
    intro p hp
    have hp' := (mem_primesUpTo.mp hp).1
    have hu := Real.log_le_sub_one_of_pos (primeFactor_pos hp')
    have ha := (abs_le.mp (abs_log_primeFactor_add_le hp')).1
    constructor <;> linarith
  constructor
  · exact Finset.sum_nonneg (fun p hp => (hlocal p hp).1)
  · calc
      correction n ≤ ∑ p ∈ primesUpTo n, 2 / (p : ℝ) ^ 2 :=
        Finset.sum_le_sum (fun p hp => (hlocal p hp).2)
      _ = 2 * ∑ p ∈ primesUpTo n, (1 : ℝ) / (p : ℝ) ^ 2 := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p hp; ring
      _ ≤ 2 * 2 := mul_le_mul_of_nonneg_left (prime_square_sum_le_two n) (by norm_num)
      _ = 4 := by norm_num

theorem log_product_identity (n : ℕ) :
    log (primeProduct n) = -primeReciprocalSum n - correction n := by
  rw [log_primeProduct]
  unfold primeReciprocalSum correction
  rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- `∏_{p ≤ n} (1 - 1/p) ≍ 1/log n` for `n ≥ 2`. -/
theorem product_bounds_nat :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      c / log n ≤ primeProduct n ∧ primeProduct n ≤ C / log n := by
  obtain ⟨E, hE, h⟩ := reciprocal_defect_bounded
  refine ⟨exp (-(E + 4)), exp (E + 4), exp_pos _, exp_pos _, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hln := log_pos hn1
  have hP := primeProduct_pos n
  have hcorr := correction_bounds n
  have hlog : |log (primeProduct n) + log (log n)| ≤ E + 4 := by
    rw [log_product_identity]
    have heq : -primeReciprocalSum n - correction n + log (log n) =
        -(primeReciprocalSum n - log (log n)) - correction n := by ring
    rw [heq]
    exact (abs_sub _ _).trans (by rw [abs_neg, abs_of_nonneg hcorr.1]; linarith [h n hn])
  have hlow := Real.exp_le_exp.mpr (abs_le.mp hlog).1
  have hupp := Real.exp_le_exp.mpr (abs_le.mp hlog).2
  rw [exp_add, exp_log hP, exp_log hln] at hlow hupp
  exact ⟨(div_le_iff₀ hln).mpr hlow, (le_div_iff₀ hln).mpr hupp⟩

theorem log_one_add_reciprocal_bounds {p : ℕ} (hp : p.Prime) :
    0 ≤ 1 / (p : ℝ) - log (1 + 1 / p) ∧
      1 / (p : ℝ) - log (1 + 1 / p) ≤ 1 / (p : ℝ) ^ 2 := by
  have hpp : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have ht : 0 < (1 : ℝ) / p := one_div_pos.mpr hpp
  have hpos : 0 < 1 + (1 : ℝ) / p := by positivity
  have hu := log_le_sub_one_of_pos hpos
  have hl := one_sub_inv_le_log_of_pos hpos
  have hrec : 1 / (p : ℝ) - 1 / (p : ℝ) ^ 2 ≤ 1 - (1 + 1 / (p : ℝ))⁻¹ := by
    have hmul : (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2) * (1 + 1 / (p : ℝ)) ≤ 1 / p := by
      have heq : (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2) * (1 + 1 / (p : ℝ)) =
          1 / (p : ℝ) - ((1 : ℝ) / p) ^ 3 := by ring
      rw [heq]
      exact sub_le_self _ (by positivity)
    apply (le_of_mul_le_mul_right ?_ hpos)
    refine hmul.trans_eq ?_; field_simp; ring
  constructor <;> linarith

/-- The product `∏_{m < p ≤ n} (1 + 1/p)`. -/
noncomputable def plusProduct (m n : ℕ) : ℝ :=
  ∏ p ∈ (Ioc m n).filter Nat.Prime, (1 + 1 / (p : ℝ))

theorem plusProduct_pos (m n : ℕ) : 0 < plusProduct m n := by
  exact Finset.prod_pos (by intro p hp; positivity)

theorem primeReciprocalSum_sub {m n : ℕ} (hmn : m ≤ n) :
    (∑ p ∈ (Ioc m n).filter Nat.Prime, (1 : ℝ) / p) =
      primeReciprocalSum n - primeReciprocalSum m := by
  unfold primeReciprocalSum
  rw [primesUpTo_eq_filter_Icc, primesUpTo_eq_filter_Icc]
  simp only [Finset.sum_filter]
  exact sum_Ioc_eq_prefix_sub (fun p : ℕ => if p.Prime then (1 : ℝ) / p else 0) hmn

/-- `∏_{m < p ≤ n} (1 + 1/p) ≍ log n / log m` for `2 ≤ m ≤ n`. -/
theorem plus_product_bounds_nat :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ m n : ℕ, 2 ≤ m → m ≤ n →
      c * (log n / log m) ≤ plusProduct m n ∧
      plusProduct m n ≤ C * (log n / log m) := by
  obtain ⟨E, hE, h⟩ := reciprocal_defect_bounded
  refine ⟨exp (-(2 * E + 2)), exp (2 * E + 2), exp_pos _, exp_pos _, ?_⟩
  intro m n hm hmn
  let A := (Ioc m n).filter Nat.Prime
  let F : ℝ := ∑ p ∈ A, (1 / (p : ℝ) - log (1 + 1 / p))
  have hF0 : 0 ≤ F := Finset.sum_nonneg (fun p hp =>
    (log_one_add_reciprocal_bounds (Finset.mem_filter.mp hp).2).1)
  have hF2 : F ≤ 2 := by
    apply le_trans (Finset.sum_le_sum (fun p hp =>
      (log_one_add_reciprocal_bounds (Finset.mem_filter.mp hp).2).2))
    apply le_trans _ (prime_square_sum_le_two n)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp; exact mem_primesUpTo.mpr
        ⟨(Finset.mem_filter.mp hp).2, (mem_Ioc.mp (Finset.mem_filter.mp hp).1).2⟩
    · intro p _ _; positivity
  have hid : log (plusProduct m n) = primeReciprocalSum n - primeReciprocalSum m - F := by
    rw [plusProduct, Real.log_prod (by intro p hp; positivity)]
    rw [← primeReciprocalSum_sub hmn]
    dsimp [F, A]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp; ring
  have hmn1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hnn1 : (1 : ℝ) < n := hmn1.trans_le (Nat.cast_le.mpr hmn)
  have hlm := log_pos hmn1
  have hln := log_pos hnn1
  have hlog : |log (plusProduct m n) - log (log n / log m)| ≤ 2 * E + 2 := by
    rw [hid, log_div hln.ne' hlm.ne']
    have heq : primeReciprocalSum n - primeReciprocalSum m - F -
        (log (log n) - log (log m)) =
      (primeReciprocalSum n - log (log n)) -
        (primeReciprocalSum m - log (log m)) - F := by ring
    rw [heq]
    exact (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _)
      |>.trans (by rw [abs_of_nonneg hF0]; linarith [h m hm, h n (hm.trans hmn)])
  have hlow := Real.exp_le_exp.mpr (abs_le.mp hlog).1
  have hupp := Real.exp_le_exp.mpr (abs_le.mp hlog).2
  have hratio : 0 < log n / log m := div_pos hln hlm
  rw [exp_sub, exp_log (plusProduct_pos m n), exp_log hratio] at hlow hupp
  exact ⟨(le_div_iff₀ hratio).mp hlow, (div_le_iff₀ hratio).mp hupp⟩

end ErdosStraus.PrimeEstimates.Mertens

/-! ## Euler products for real `x` -/

namespace ErdosStraus.PrimeEstimates.Mertens

open Finset Real
open scoped BigOperators

/-- Mertens' product theorem: `∏_{p ≤ x} (1 - 1/p)⁻¹ ≍ log x` for real `x ≥ 2`. -/
theorem inverse_product_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      c * log x ≤ (primeProduct ⌊x⌋₊)⁻¹ ∧
        (primeProduct ⌊x⌋₊)⁻¹ ≤ C * log x := by
  obtain ⟨c, C, hc, hC, h⟩ := product_bounds_nat
  refine ⟨1 / (2 * C), 1 / c, by positivity, by positivity, ?_⟩
  intro x hx
  obtain ⟨hlp, hle, h2, hgap⟩ := floor_log_bounds hx
  obtain ⟨hl, hu⟩ := h ⌊x⌋₊ (Nat.le_floor hx)
  have hP := primeProduct_pos ⌊x⌋₊
  have hlow := one_div_le_one_div_of_le hP hu
  have hupp := one_div_le_one_div_of_le (div_pos hc hlp) hl
  have hlow' : log (⌊x⌋₊ : ℝ) / C ≤ (primeProduct ⌊x⌋₊)⁻¹ := by
    simpa only [one_div, inv_div] using hlow
  have hupp' : (primeProduct ⌊x⌋₊)⁻¹ ≤ log (⌊x⌋₊ : ℝ) / c := by
    simpa only [one_div, inv_div] using hupp
  constructor
  · apply le_trans _ hlow'
    apply (le_div_iff₀ hC).mpr
    have hidentity : (1 / (2 * C) * log x) * C = log x / 2 := by field_simp
    rw [hidentity]
    linarith
  · apply hupp'.trans
    simpa [div_eq_mul_inv, mul_comm] using
      (div_le_div_of_nonneg_right hle hc.le)

/-- `∏_{z < p ≤ x} (1 + 1/p) ≍ log x / log z` for real `2 ≤ z ≤ x`. -/
theorem plus_product_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z x : ℝ, 2 ≤ z → z ≤ x →
      c * (log x / log z) ≤ plusProduct ⌊z⌋₊ ⌊x⌋₊ ∧
        plusProduct ⌊z⌋₊ ⌊x⌋₊ ≤ C * (log x / log z) := by
  obtain ⟨c, C, hc, hC, h⟩ := plus_product_bounds_nat
  refine ⟨c / 2, 2 * C, by positivity, by positivity, ?_⟩
  intro z x hz hzx
  obtain ⟨hlz, hzle, hz2, _⟩ := floor_log_bounds hz
  obtain ⟨hlx, hxle, hx2, _⟩ := floor_log_bounds (hz.trans hzx)
  have hlogz : 0 < log z := hlz.trans_le hzle
  have hlo : (log x / log z) / 2 ≤ log (⌊x⌋₊ : ℝ) / log (⌊z⌋₊ : ℝ) := by
    have hh := (mul_le_mul_of_nonneg_right hx2 hlz.le).trans
      (mul_le_mul_of_nonneg_left hzle (by positivity : 0 ≤ 2 * log (⌊x⌋₊ : ℝ)))
    rw [div_div]
    apply (div_le_div_iff₀ (mul_pos hlogz (by norm_num : (0 : ℝ) < 2)) hlz).mpr
    nlinarith
  have hup : log (⌊x⌋₊ : ℝ) / log (⌊z⌋₊ : ℝ) ≤ 2 * (log x / log z) := by
    have hh := (mul_le_mul_of_nonneg_right hxle hlogz.le).trans
      (mul_le_mul_of_nonneg_left hz2 (hlx.trans_le hxle).le)
    rw [show 2 * (log x / log z) = (2 * log x) / log z by ring]
    apply (div_le_div_iff₀ hlz hlogz).mpr
    nlinarith
  have hh := h ⌊z⌋₊ ⌊x⌋₊ (Nat.le_floor hz) (Nat.floor_mono hzx)
  constructor
  · calc
      _ = c * ((log x / log z) / 2) := by ring
      _ ≤ c * (log (⌊x⌋₊ : ℝ) / log (⌊z⌋₊ : ℝ)) := mul_le_mul_of_nonneg_left hlo hc.le
      _ ≤ _ := hh.1
  · calc
      _ ≤ C * (log (⌊x⌋₊ : ℝ) / log (⌊z⌋₊ : ℝ)) := hh.2
      _ ≤ C * (2 * (log x / log z)) := mul_le_mul_of_nonneg_left hup hC.le
      _ = _ := by ring

/-! ## Lemma 3.1 -/

/-- Lemma 3.1: for `x ≥ 2`, `θ(x) ≪ x`, `∑_{p ≤ x} log p / p = log x + O(1)`,
`∑_{p ≤ x} 1/p = log log x + B + O(1/log x)` and `∏_{p ≤ x} (1 - 1/p)⁻¹ ≍ log x`; and
`∏_{z < p ≤ x} (1 + 1/p) ≍ log x / log z` for `2 ≤ z ≤ x`. -/
theorem prime_estimates :
    ∃ B c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ x : ℝ, 2 ≤ x →
        (∑ p ∈ primesUpTo ⌊x⌋₊, log p) ≤ C * x ∧
        |(∑ p ∈ primesUpTo ⌊x⌋₊, log p / p) - log x| ≤ C ∧
        |primeReciprocalSum ⌊x⌋₊ - (log (log x) + B)| ≤ C / log x ∧
        c * log x ≤ (primeProduct ⌊x⌋₊)⁻¹ ∧
        (primeProduct ⌊x⌋₊)⁻¹ ≤ C * log x) ∧
      (∀ z x : ℝ, 2 ≤ z → z ≤ x →
        c * (log x / log z) ≤ plusProduct ⌊z⌋₊ ⌊x⌋₊ ∧
        plusProduct ⌊z⌋₊ ⌊x⌋₊ ≤ C * (log x / log z)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := mertensFirst
  obtain ⟨C₂, hC₂, h₂⟩ := mertensSecond
  obtain ⟨c₃, C₃, hc₃, hC₃, h₃⟩ := inverse_product_bounds
  obtain ⟨c₄, C₄, hc₄, hC₄, h₄⟩ := plus_product_bounds
  let C := C₁ + C₂ + C₃ + C₄ + log 4 + 1
  have hlog4 : 0 < log (4 : ℝ) := log_pos (by norm_num)
  have hCC : C₁ ≤ C ∧ C₂ ≤ C ∧ C₃ ≤ C ∧ C₄ ≤ C ∧ log 4 ≤ C := by
    dsimp [C]
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  refine ⟨mertensSecondConstant, min c₃ c₄, C, lt_min hc₃ hc₄,
    hC₁.trans_le hCC.1, ?_, ?_⟩
  · intro x hx
    have hxp : 0 ≤ x := by linarith
    have hlx : 0 < log x := log_pos (by linarith)
    have htheta : (∑ p ∈ primesUpTo ⌊x⌋₊, log p) ≤ C * x :=
      (theta_le hxp).trans (mul_le_mul_of_nonneg_right hCC.2.2.2.2 hxp)
    have hprod := h₃ x hx
    exact ⟨htheta, (h₁ x hx).trans hCC.1,
      (h₂ x hx).trans (div_le_div_of_nonneg_right hCC.2.1 hlx.le),
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hlx.le).trans hprod.1,
      hprod.2.trans (mul_le_mul_of_nonneg_right hCC.2.2.1 hlx.le)⟩
  · intro z x hz hzx
    have hlz : 0 < log z := log_pos (by linarith)
    have hlx : 0 < log x := log_pos (by linarith)
    have hr := (div_pos hlx hlz).le
    have hh := h₄ z x hz hzx
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _) hr).trans hh.1,
      hh.2.trans (mul_le_mul_of_nonneg_right hCC.2.2.2.1 hr)⟩

end ErdosStraus.PrimeEstimates.Mertens
