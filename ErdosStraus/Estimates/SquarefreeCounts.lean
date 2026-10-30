import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import ErdosStraus.MaximalBV
import Mathlib.Data.Nat.Factorization.Root
import ErdosStraus.Estimates.Progressions
import ErdosStraus.Estimates.TotientSums

/-! # Lemma 3.2: squarefree integers coprime to `M`

Writing `μ²(n) = ∑_{k² ∣ n} μ(k)`, the number of squarefree `n ≤ x` with `n ≡ a (mod d)` and
`(n, M) = 1` is `κ(M, d) φ(M) x/(M d)` up to an error `7 τ(M) √x`, where
`κ(M, d) = ζ(2)⁻¹ ∏_{p ∣ dM} (1 - p⁻²)⁻¹ ∈ [1/ζ(2), 1]`. Partial summation then gives the
estimate (6) of Lemma 3.2: for squarefree `M ≤ X^{C₀}`,
`∑_{U₀ < n ≤ U₁, n squarefree, (n, M) = 1} 1/n ≍ (φ(M)/M) log(U₁/U₀)`.
-/

namespace ErdosStraus.DivisorEstimates

open scoped BigOperators

/-! ## The series `∑ μ(n)/n²` -/

section

open ArithmeticFunction

theorem abs_moebius_div_sq_le (n : ℕ) :
    |(ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2| ≤ 1 / (n : ℝ) ^ 2 := by
  have hd : |(n : ℝ) ^ 2| = (n : ℝ) ^ 2 := abs_of_nonneg (sq_nonneg _)
  rw [abs_div, hd]
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)) (sq_nonneg _)

theorem summable_moebius_div_sq :
    Summable (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2)
    hasSum_zeta_two.summable
  intro n
  simpa only [Real.norm_eq_abs] using abs_moebius_div_sq_le n

/-- `∑ μ(n)/n² = 1/ζ(2) = 6/π²`, the completed sum over `k` in the proof of Lemma 4.1. -/
theorem tsum_moebius_div_sq :
    (∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2) =
      1 / (Real.pi ^ 2 / 6) := by
  have hone : LSeries (fun _ : ℕ => (1 : ℂ)) 2 = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) := by
    have hs := (Complex.hasSum_ofReal.mpr hasSum_zeta_two).tsum_eq
    rw [LSeries]
    simp_rw [LSeries.term_of_ne_zero' (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_two]
    convert hs using 1
    congr 1
    funext n
    simp
  have hmu : LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) 2 =
      ((∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    rw [LSeries.term_of_ne_zero' (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_two]
    simp
  have hp := LSeries_one_mul_Lseries_moebius
    (s := (2 : ℂ)) (by norm_num)
  change LSeries (fun _ : ℕ => (1 : ℂ)) 2 *
    LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) 2 = 1 at hp
  rw [hone, hmu] at hp
  have hr := congrArg Complex.re hp
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.one_re] at hr
  apply (eq_div_iff (by positivity : (Real.pi ^ 2 / 6 : ℝ) ≠ 0)).mpr
  linarith

theorem tsum_reciprocal_sq_tail_le (N : ℕ) (hN : 0 < N) :
    (∑' k : ℕ, (1 : ℝ) / ((N + k + 1 : ℕ) : ℝ) ^ 2) ≤ 1 / (N : ℝ) := by
  have hfinite : ∀ K : ℕ,
      (∑ k ∈ Finset.range K, (1 : ℝ) / ((N + k + 1 : ℕ) : ℝ) ^ 2) ≤
        1 / (N : ℝ) - 1 / ((N + K : ℕ) : ℝ) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ]
      have hNK : (0 : ℝ) < ((N + K : ℕ) : ℝ) := by positivity
      have hNK1 : (0 : ℝ) < ((N + K + 1 : ℕ) : ℝ) := by positivity
      have hterm : (1 : ℝ) / ((N + K + 1 : ℕ) : ℝ) ^ 2 ≤
          1 / ((N + K : ℕ) : ℝ) - 1 / ((N + K + 1 : ℕ) : ℝ) := by
        have he : (1 : ℝ) / ((N + K : ℕ) : ℝ) - 1 / ((N + K + 1 : ℕ) : ℝ) =
            1 / (((N + K : ℕ) : ℝ) * ((N + K + 1 : ℕ) : ℝ)) := by
          push_cast
          field_simp
          ring
        rw [he]
        apply one_div_le_one_div_of_le (mul_pos hNK hNK1)
        push_cast
        nlinarith
      have he : N + (K + 1) = N + K + 1 := by omega
      rw [he]
      linarith
  apply Real.tsum_le_of_sum_range_le (fun k => by positivity)
  intro K
  exact (hfinite K).trans (sub_le_self _ (by positivity))

set_option maxHeartbeats 1000000 in
theorem abs_moebius_reciprocal_sq_partial_sub_constant_le (N : ℕ) (hN : 0 < N) :
    |(∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2) -
        1 / (Real.pi ^ 2 / 6)| ≤ 1 / (N : ℝ) := by
  let f : ℕ → ℝ := fun n => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2
  have hs : Summable f := summable_moebius_div_sq
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := hasSum_zeta_two.summable
  have ht := Summable.sum_add_tsum_nat_add (N + 1) hs
  have hset : Finset.Icc 1 N = (Finset.range (N + 1)).erase 0 := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
    omega
  have hfin : (∑ n ∈ Finset.range (N + 1), f n) = ∑ n ∈ Finset.Icc 1 N, f n := by
    rw [hset, Finset.sum_erase_eq_sub (by simp)]
    simp [f]
  rw [hfin, tsum_moebius_div_sq] at ht
  have htailSum : Summable (fun k : ℕ => f (k + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).mpr hs
  have hnorm := norm_tsum_le_tsum_norm htailSum.norm
  simp only [Real.norm_eq_abs] at hnorm
  have hcomp : (∑' k : ℕ, |f (k + (N + 1))|) ≤
      ∑' k : ℕ, (1 : ℝ) / ((k + (N + 1) : ℕ) : ℝ) ^ 2 := by
    apply Summable.tsum_le_tsum
    · intro k
      exact abs_moebius_div_sq_le _
    · exact htailSum.abs
    · exact (summable_nat_add_iff (N + 1)).mpr hbase
  have htail := tsum_reciprocal_sq_tail_le N hN
  have he : (fun k : ℕ => (1 : ℝ) / ((k + (N + 1) : ℕ) : ℝ) ^ 2) =
      (fun k : ℕ => (1 : ℝ) / ((N + k + 1 : ℕ) : ℝ) ^ 2) := by
    funext k
    congr 3
    omega
  rw [he] at hcomp
  have hfinal : |∑' k : ℕ, f (k + (N + 1))| ≤ 1 / (N : ℝ) :=
    hnorm.trans (hcomp.trans htail)
  change |(∑ n ∈ Finset.Icc 1 N, f n) - 1 / (Real.pi ^ 2 / 6)| ≤ _
  have heq : (∑ n ∈ Finset.Icc 1 N, f n) - 1 / (Real.pi ^ 2 / 6) =
      -(∑' k : ℕ, f (k + (N + 1))) := by linarith
  rw [heq, abs_neg]
  exact hfinal

theorem summable_log_div_sq :
    Summable (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ 2) := by
  have hp : Summable (fun n : ℕ => 2 * (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    (Real.summable_nat_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1)).mul_left 2
  apply Summable.of_norm_bounded hp
  intro n
  by_cases hn : n = 0
  · simp [hn, Real.zero_rpow (by norm_num : -(3 / 2 : ℝ) ≠ 0)]
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hlog : ‖Real.log (n : ℝ)‖ ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg n)]
    exact Real.log_natCast_le_rpow_div n (by norm_num : 0 < (1 / 2 : ℝ))
  have hd : ‖(n : ℝ) ^ 2‖ = (n : ℝ) ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [norm_div, hd]
  calc
    _ ≤ ((n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ)) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hlog (sq_nonneg _)
    _ = 2 * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
      have he : (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 =
          (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_sub hnpos]
        norm_num
      calc
        _ = 2 * ((n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2) := by ring
        _ = _ := by rw [he]

end

/-! ## The series `∑_{(n, M) = 1} μ(n)/n²` -/

theorem principalCharacter_apply (M n : ℕ) :
    (1 : DirichletCharacter ℂ M) n = if Nat.Coprime n M then 1 else 0 := by
  classical
  by_cases hn : Nat.Coprime n M
  · rw [if_pos hn]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n M).mpr hn)
  · rw [if_neg hn]
    exact MulChar.map_nonunit _ (by simpa only [ZMod.isUnit_iff_coprime] using hn)

theorem LSeries_one_two_eq_basel :
    LSeries (fun _ : ℕ => (1 : ℂ)) 2 = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) := by
  have hs := (Complex.hasSum_ofReal.mpr hasSum_zeta_two).tsum_eq
  rw [LSeries]
  simp_rw [LSeries.term_of_ne_zero' (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_two]
  convert hs using 1
  congr 1
  funext n
  simp

theorem principalCharacter_LSeries_two (M : ℕ) (hM : 0 < M) :
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ M) n) 2 =
      (((Real.pi ^ 2 / 6) *
        ∏ p ∈ M.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹) : ℝ) : ℂ) := by
  let : NeZero M := ⟨hM.ne'⟩
  have h := DirichletCharacter.LSeries_changeLevel (one_dvd M)
    (1 : DirichletCharacter ℂ 1) (s := (2 : ℂ)) (by norm_num)
  rw [DirichletCharacter.changeLevel_one] at h
  have hbase : (fun n : ℕ => (1 : DirichletCharacter ℂ 1) n) = (fun _ => (1 : ℂ)) := by
    funext n
    simp [principalCharacter_apply]
  change LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ M) n) 2 = _ at h
  rw [hbase, LSeries_one_two_eq_basel] at h
  convert h using 1
  push_cast
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  simp [principalCharacter_apply, one_mul, Complex.cpow_neg]

theorem abs_restricted_moebius_div_sq_le (M n : ℕ) :
    |if Nat.Coprime n M then (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 else 0| ≤
      1 / (n : ℝ) ^ 2 := by
  split_ifs
  · exact abs_moebius_div_sq_le n
  · simp

theorem summable_restricted_moebius_div_sq (M : ℕ) :
    Summable (fun n : ℕ =>
      if Nat.Coprime n M then (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 else 0) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2)
    hasSum_zeta_two.summable
  intro n
  simpa only [Real.norm_eq_abs] using abs_restricted_moebius_div_sq_le M n

/-- `∑_{(n,M)=1} μ(n)/n² = ζ(2)^{-1} ∏_{p ∣ M} (1 - p^{-2})^{-1}`, the constant
entering `𝔖(M)` in Proposition 4.3. -/
theorem tsum_restricted_moebius_div_sq (M : ℕ) (hM : 0 < M) :
    (∑' n : ℕ, if Nat.Coprime n M then
      (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 else 0) =
      (1 / (Real.pi ^ 2 / 6)) *
        ∏ p ∈ M.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ := by
  classical
  let S : ℝ := ∑' n : ℕ, if Nat.Coprime n M then
    (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 else 0
  let E : ℝ := ∏ p ∈ M.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹)
  have hmu : LSeries
      (fun n : ℕ => (1 : DirichletCharacter ℂ M) n * (ArithmeticFunction.moebius n : ℂ)) 2 =
      (S : ℂ) := by
    rw [LSeries]
    dsimp only [S]
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    rw [LSeries.term_of_ne_zero' (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_two]
    simp only [principalCharacter_apply]
    by_cases hn : Nat.Coprime n M
    · simp only [if_pos hn, one_mul]
      push_cast
      rfl
    · simp only [if_neg hn, zero_mul, zero_div, Complex.ofReal_zero]
  have hp := DirichletCharacter.LSeries.mul_mu_eq_one (1 : DirichletCharacter ℂ M)
    (s := (2 : ℂ)) (by norm_num)
  change LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ M) n) 2 *
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ M) n *
      (ArithmeticFunction.moebius n : ℂ)) 2 = 1 at hp
  rw [principalCharacter_LSeries_two M hM, hmu] at hp
  have hr := congrArg Complex.re hp
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.one_re] at hr
  have hE : 0 < E := by
    apply Finset.prod_pos
    intro p hp
    have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Nat.prime_of_mem_primeFactors hp).one_lt
    have hsq : (1 : ℝ) < (p : ℝ) ^ 2 := by nlinarith
    have hi : ((p : ℝ) ^ 2)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr hsq
    linarith
  have hbasel : 0 < (Real.pi ^ 2 / 6 : ℝ) := by positivity
  have hS : S = 1 / ((Real.pi ^ 2 / 6) * E) := by
    apply (eq_div_iff (mul_pos hbasel hE).ne').mpr
    change ((Real.pi ^ 2 / 6) * E) * S = 1 at hr
    nlinarith only [hr]
  change S = _
  rw [hS]
  simp only [div_eq_mul_inv, mul_inv, one_mul, Finset.prod_inv_distrib, E]

set_option maxHeartbeats 2000000 in
theorem abs_restricted_moebius_partial_sub_constant_le
    (M N : ℕ) (hM : 0 < M) (hN : 0 < N) :
    |(∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n M),
        (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2) -
      (1 / (Real.pi ^ 2 / 6)) *
        ∏ p ∈ M.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹| ≤ 1 / (N : ℝ) := by
  classical
  let f : ℕ → ℝ := fun n => if Nat.Coprime n M then
    (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 else 0
  have hs : Summable f := summable_restricted_moebius_div_sq M
  have hb : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := hasSum_zeta_two.summable
  have ht := Summable.sum_add_tsum_nat_add (N + 1) hs
  have hset : Finset.Icc 1 N = (Finset.range (N + 1)).erase 0 := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
    omega
  have hfin : (∑ n ∈ Finset.range (N + 1), f n) = ∑ n ∈ Finset.Icc 1 N, f n := by
    rw [hset, Finset.sum_erase_eq_sub (by simp)]
    simp [f]
  rw [hfin] at ht
  have htailSum : Summable (fun k : ℕ => f (k + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).mpr hs
  have hnorm := norm_tsum_le_tsum_norm htailSum.norm
  simp only [Real.norm_eq_abs] at hnorm
  have hcomp : (∑' k : ℕ, |f (k + (N + 1))|) ≤
      ∑' k : ℕ, (1 : ℝ) / ((k + (N + 1) : ℕ) : ℝ) ^ 2 := by
    apply Summable.tsum_le_tsum
    · intro k
      exact abs_restricted_moebius_div_sq_le M _
    · exact htailSum.abs
    · exact (summable_nat_add_iff (N + 1)).mpr hb
  have he : (fun k : ℕ => (1 : ℝ) / ((k + (N + 1) : ℕ) : ℝ) ^ 2) =
      (fun k : ℕ => (1 : ℝ) / ((N + k + 1 : ℕ) : ℝ) ^ 2) := by
    funext k
    congr 3
    omega
  rw [he] at hcomp
  have hfinal : |∑' k : ℕ, f (k + (N + 1))| ≤ 1 / (N : ℝ) :=
    hnorm.trans (hcomp.trans (tsum_reciprocal_sq_tail_le N hN))
  have hdiff : (∑ n ∈ Finset.Icc 1 N, f n) - ∑' n : ℕ, f n =
      -(∑' k : ℕ, f (k + (N + 1))) := by linarith only [ht]
  rw [Finset.sum_filter]
  change |(∑ n ∈ Finset.Icc 1 N, f n) - _| ≤ _
  rw [← tsum_restricted_moebius_div_sq M hM]
  change |(∑ n ∈ Finset.Icc 1 N, f n) - ∑' n : ℕ, f n| ≤ _
  rw [hdiff, abs_neg]
  exact hfinal

end ErdosStraus.DivisorEstimates

namespace ErdosStraus.ProgressionEstimates

open scoped BigOperators

/-! ## Partial summation -/

section

open Classical Finset MeasureTheory

theorem sqrt_div_self {t : ℝ} (ht : 0 < t) : Real.sqrt t / t = 1 / Real.sqrt t := by
  have hs := Real.sqrt_pos.mpr ht
  have he := Real.sq_sqrt ht.le
  field_simp
  exact he

theorem sqrt_div_square {t : ℝ} (ht : 0 < t) :
    Real.sqrt t / t ^ 2 = t ^ (-(3 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_two, ← Real.rpow_sub ht]
  norm_num

/-- If `|∑_{n ≤ t} f(n) - c t| ≤ D √t` for `t ≥ A`, then
`|∑_{A < n ≤ B} f(n)/n - c log(B/A)| ≤ 4D/√A`. -/
theorem harmonic_of_sqrt_prefix_local (f : ℕ → ℝ) (c D : ℝ) (hD : 0 ≤ D)
    {A B : ℝ} (hA : 0 < A) (hAB : A < B)
    (hprefix : ∀ t : ℝ, A ≤ t →
      |(∑ n ∈ Icc 0 ⌊t⌋₊, f n) - c * t| ≤ D * Real.sqrt t) :
    |(∑ n ∈ Ioc ⌊A⌋₊ ⌊B⌋₊, f n / n) - c * Real.log (B / A)| ≤
      4 * D / Real.sqrt A := by
  let F : ℝ → ℝ := fun t => ∑ n ∈ Icc 0 ⌊t⌋₊, f n
  let E : ℝ → ℝ := fun t => (F t - c * t) / t ^ 2
  let G : ℝ → ℝ := fun t => D * t ^ (-(3 / 2 : ℝ))
  have hApos : 0 < A := hA
  have hBpos : 0 < B := hApos.trans hAB
  have hzero : (0 : ℝ) ∉ Set.uIcc A B := by
    rw [Set.uIcc_of_le hAB.le]
    simp only [Set.mem_Icc, not_and]
    intro h
    linarith
  have hFmeas : Measurable F :=
    (measurable_of_countable (fun k : ℕ => ∑ n ∈ Icc 0 k, f n)).comp measurable_id.nat_floor
  have hEmeas : Measurable E :=
    (hFmeas.sub (measurable_const.mul measurable_id)).div (measurable_id.pow_const 2)
  have hGint : IntegrableOn G (Set.Ioc A B) := by
    have hi := (intervalIntegral.intervalIntegrable_rpow (μ := volume)
      (r := -(3 / 2 : ℝ)) (a := A) (b := B) (Or.inr hzero)).const_mul D
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hAB.le).mp hi).mono_set
      Set.Ioc_subset_Icc_self
  have hbound : ∀ t ∈ Set.Ioc A B, ‖E t‖ ≤ G t := by
    intro t ht
    have htpos : 0 < t := hApos.trans ht.1
    dsimp [E, G]
    rw [abs_div, abs_of_nonneg (sq_nonneg t)]
    calc
      _ ≤ D * Real.sqrt t / t ^ 2 :=
        div_le_div_of_nonneg_right (hprefix t ht.1.le) (sq_nonneg _)
      _ = D * t ^ (-(3 / 2 : ℝ)) := by rw [mul_div_assoc, sqrt_div_square htpos]
  have hboundAE : ∀ᵐ t ∂volume.restrict (Set.Ioc A B), ‖E t‖ ≤ G t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hbound t ht
  have hEint : IntegrableOn E (Set.Ioc A B) := hGint.mono' hEmeas.aestronglyMeasurable hboundAE
  have hcont : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.Icc A B) :=
    ((continuousOn_id.pow 2).inv₀ (fun t ht => pow_ne_zero _ (ne_of_gt (hApos.trans_le ht.1)))).neg
  have hderiv : IntegrableOn (deriv fun t : ℝ => t⁻¹) (Set.Icc A B) := by
    simpa only [deriv_inv'] using hcont.integrableOn_Icc
  have hAbel := sum_mul_eq_sub_sub_integral_mul f hApos.le hAB.le
    (fun t ht => (hasDerivAt_inv (ne_of_gt (hApos.trans_le ht.1))).differentiableAt) hderiv
  have hrewrite : (∫ t in Set.Ioc A B, (deriv fun x : ℝ => x⁻¹) t * F t) =
      -(∫ t in Set.Ioc A B, F t / t ^ 2) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by simp [deriv_inv', div_eq_mul_inv]; ring)
  have hmainint : IntegrableOn (fun t : ℝ => c * t⁻¹) (Set.Ioc A B) := by
    have hi := (intervalIntegral.intervalIntegrable_inv (μ := volume)
      (f := fun t : ℝ => t) (a := A) (b := B)
      (by
        intro t ht
        rw [Set.uIcc_of_le hAB.le] at ht
        exact ne_of_gt (hApos.trans_le ht.1))
      continuousOn_id).const_mul c
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hAB.le).mp hi).mono_set
      Set.Ioc_subset_Icc_self
  have hlog : (∫ t in Set.Ioc A B, c * t⁻¹) = c * Real.log (B / A) := by
    rw [← intervalIntegral.integral_of_le hAB.le, intervalIntegral.integral_const_mul,
      integral_inv_of_pos hApos hBpos]
  have hsplit : (∫ t in Set.Ioc A B, F t / t ^ 2) =
      c * Real.log (B / A) + ∫ t in Set.Ioc A B, E t := by
    rw [← hlog, ← integral_add hmainint hEint]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htpos : 0 < t := hApos.trans ht.1
    dsimp [E]
    field_simp
    ring
  have hsum : (∑ n ∈ Ioc ⌊A⌋₊ ⌊B⌋₊, f n / n) - c * Real.log (B / A) =
      (F B - c * B) / B - (F A - c * A) / A + ∫ t in Set.Ioc A B, E t := by
    have hs : (∑ n ∈ Ioc ⌊A⌋₊ ⌊B⌋₊, f n / n) =
        ∑ n ∈ Ioc ⌊A⌋₊ ⌊B⌋₊, (n : ℝ)⁻¹ * f n := by
      apply Finset.sum_congr rfl
      intro n hn
      ring
    rw [hs, hAbel]
    change B⁻¹ * F B - A⁻¹ * F A -
      (∫ t in Set.Ioc A B, (deriv fun x : ℝ => x⁻¹) t * F t) - c * Real.log (B / A) = _
    rw [hrewrite, hsplit]
    field_simp
    ring
  have hend (t : ℝ) (ht : A ≤ t) : |(F t - c * t) / t| ≤ D / Real.sqrt t := by
    have htpos : 0 < t := hA.trans_le ht
    rw [abs_div, abs_of_pos htpos]
    exact (div_le_div_of_nonneg_right (hprefix t ht) htpos.le).trans_eq
      (by rw [mul_div_assoc, sqrt_div_self htpos]; ring)
  have hAroot := Real.sqrt_pos.mpr hApos
  have hBroot := Real.sqrt_pos.mpr hBpos
  have hendB : |(F B - c * B) / B| ≤ D / Real.sqrt A :=
    (hend B hAB.le).trans
      (div_le_div_of_nonneg_left hD hAroot (Real.sqrt_le_sqrt hAB.le))
  have hGvalue : (∫ t in Set.Ioc A B, G t) =
      2 * D * (1 / Real.sqrt A - 1 / Real.sqrt B) := by
    dsimp [G]
    rw [← intervalIntegral.integral_of_le hAB.le, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inr ⟨by norm_num, hzero⟩)]
    norm_num
    rw [Real.rpow_neg hApos.le, Real.rpow_neg hBpos.le,
      ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    ring
  have hEbound : |∫ t in Set.Ioc A B, E t| ≤ 2 * D / Real.sqrt A := by
    have hi := MeasureTheory.norm_integral_le_of_norm_le hGint hboundAE
    rw [Real.norm_eq_abs, hGvalue] at hi
    exact hi.trans (by
      have hh := div_nonneg hD hBroot.le
      simp only [div_eq_mul_inv] at hh ⊢
      nlinarith)
  rw [hsum]
  exact (abs_add_le _ _).trans ((add_le_add_left (abs_sub _ _) _).trans (by
    have ha := hend A le_rfl
    simp only [div_eq_mul_inv] at ha hendB hEbound ⊢
    nlinarith))

theorem harmonic_of_sqrt_prefix (f : ℕ → ℝ) (c D : ℝ) (hD : 0 ≤ D)
    (hprefix : ∀ t : ℝ, 1 ≤ t →
      |(∑ n ∈ Icc 0 ⌊t⌋₊, f n) - c * t| ≤ D * Real.sqrt t)
    {A B : ℝ} (hA : 1 ≤ A) (hAB : A < B) :
    |(∑ n ∈ Ioc ⌊A⌋₊ ⌊B⌋₊, f n / n) - c * Real.log (B / A)| ≤
      4 * D / Real.sqrt A :=
  harmonic_of_sqrt_prefix_local f c D hD (by linarith) hAB
    (fun t ht => hprefix t (hA.trans ht))

theorem harmonic_of_bounded_prefix (f : ℕ → ℝ) (c D : ℝ) (hD : 0 ≤ D)
    {A B : ℝ} (hA : 0 < A) (hAB : A < B)
    (hprefix : ∀ t : ℝ, A ≤ t →
      |(∑ n ∈ Icc 0 ⌊t⌋₊, f n) - c * t| ≤ D) :
    |(∑ n ∈ Ioc ⌊A⌋₊ ⌊B⌋₊, f n / n) - c * Real.log (B / A)| ≤
      4 * D / A := by
  have hs := Real.sqrt_pos.mpr hA
  have h := harmonic_of_sqrt_prefix_local f c (D / Real.sqrt A)
    (div_nonneg hD hs.le) hA hAB (by
      intro t ht
      apply (hprefix t ht).trans
      have hroot := Real.sqrt_le_sqrt ht
      calc
        D = (D / Real.sqrt A) * Real.sqrt A := by field_simp
        _ ≤ (D / Real.sqrt A) * Real.sqrt t :=
          mul_le_mul_of_nonneg_left hroot (div_nonneg hD hs.le))
  have he : 4 * (D / Real.sqrt A) / Real.sqrt A = 4 * D / A := by
    rw [← mul_div_assoc, div_div, Real.mul_self_sqrt hA.le]
  rwa [he] at h

theorem progression_harmonic_of_sqrt_prefix (f : ℕ → ℝ) (c D : ℝ) (hD : 0 ≤ D)
    (d a : ℕ)
    (hprefix : ∀ t : ℝ, 1 ≤ t →
      |(∑ n ∈ (Estimates.natWindow 0 t).filter (fun n => n ≡ a [MOD d]), f n) - c * t| ≤
        D * Real.sqrt t)
    {A B : ℝ} (hA : 1 ≤ A) (hAB : A < B) :
    |(∑ n ∈ (Estimates.natWindow A B).filter (fun n => n ≡ a [MOD d]), f n / n) -
      c * Real.log (B / A)| ≤ 4 * D / Real.sqrt A := by
  let b : ℕ → ℝ := fun n => if n = 0 then 0 else if n ≡ a [MOD d] then f n else 0
  have hsum (t : ℝ) : (∑ n ∈ Icc 0 ⌊t⌋₊, b n) =
      ∑ n ∈ (Estimates.natWindow 0 t).filter (fun n => n ≡ a [MOD d]), f n := by
    rw [← Finset.add_sum_Ioc_eq_sum_Icc (f := b) (Nat.zero_le ⌊t⌋₊),
      PrimeEstimates.natWindow_eq_Ioc_floor (by norm_num)]
    simp only [b, if_pos rfl, Nat.floor_zero, zero_add, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by have := (Finset.mem_Ioc.mp hn).1; omega
    simp [hn0]
  have hi := harmonic_of_sqrt_prefix b c D hD (by
    intro t ht
    rw [hsum]
    exact hprefix t ht) hA hAB
  have hinterval : (∑ n ∈ Ioc ⌊A⌋₊ ⌊B⌋₊, b n / n) =
      ∑ n ∈ (Estimates.natWindow A B).filter (fun n => n ≡ a [MOD d]), f n / n := by
    rw [PrimeEstimates.natWindow_eq_Ioc_floor (by linarith), Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by have := (Finset.mem_Ioc.mp hn).1; omega
    by_cases hmod : n ≡ a [MOD d] <;> simp [b, hn0, hmod]
  rwa [hinterval] at hi

end

/-! ## Counting squarefree integers in progressions -/

section

open Classical Finset

theorem floorRoot_two_eq_one_iff {n : ℕ} :
    Nat.floorRoot 2 n = 1 ↔ Squarefree n := by
  constructor
  · intro h k hk
    have hd : k ∣ Nat.floorRoot 2 n :=
      Nat.pow_dvd_iff_dvd_floorRoot.mp (by simpa [pow_two] using hk)
    rw [h] at hd
    exact isUnit_of_dvd_one hd
  · intro h
    have hu := h (Nat.floorRoot 2 n) (by
      simpa [pow_two] using (Nat.floorRoot_pow_dvd (n := 2) (a := n)))
    exact Nat.isUnit_iff.mp hu

theorem squarefree_indicator_eq_square_moebius (n K : ℕ) (hn : 0 < n)
    (hbound : n ≤ K ^ 2) :
    (if Squarefree n then (1 : ℝ) else 0) =
      ∑ k ∈ Icc 1 K, if k ^ 2 ∣ n then (ArithmeticFunction.moebius k : ℝ) else 0 := by
  have hr : Nat.floorRoot 2 n ≠ 0 :=
    Nat.floorRoot_ne_zero.mpr ⟨by norm_num, hn.ne'⟩
  have hset : (Icc 1 K).filter (fun k => k ^ 2 ∣ n) = (Nat.floorRoot 2 n).divisors := by
    ext k
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨_, _⟩, hk⟩
      exact ⟨Nat.pow_dvd_iff_dvd_floorRoot.mp hk, hr⟩
    · rintro ⟨hk, _⟩
      have hk2 : k ^ 2 ∣ n := Nat.pow_dvd_iff_dvd_floorRoot.mpr hk
      have hkp : 0 < k := Nat.pos_of_dvd_of_pos hk (Nat.pos_of_ne_zero hr)
      have hkle : k ≤ K := by
        have := Nat.le_of_dvd hn hk2
        nlinarith
      exact ⟨⟨hkp, hkle⟩, hk2⟩
  rw [← sum_filter, hset]
  have hs := congrArg (fun f : ArithmeticFunction ℝ => f (Nat.floorRoot 2 n))
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  rw [ArithmeticFunction.coe_mul_zeta_apply] at hs
  simp only [ArithmeticFunction.intCoe_apply, ArithmeticFunction.one_apply] at hs
  rw [hs]
  simp only [floorRoot_two_eq_one_iff]

theorem squarefree_card_eq_square_moebius (S : Finset ℕ) (K : ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ K ^ 2) :
    ((S.filter Squarefree).card : ℝ) =
      ∑ k ∈ Icc 1 K, (ArithmeticFunction.moebius k : ℝ) *
        ((S.filter (fun n => k ^ 2 ∣ n)).card : ℝ) := by
  rw [← Finset.sum_boole]
  have hp : ∀ n ∈ S, (if Squarefree n then (1 : ℝ) else 0) =
      ∑ k ∈ Icc 1 K, if k ^ 2 ∣ n then (ArithmeticFunction.moebius k : ℝ) else 0 := by
    intro n hn
    exact squarefree_indicator_eq_square_moebius n K (hS n hn).1 (hS n hn).2
  rw [sum_congr rfl hp, sum_comm]
  apply sum_congr rfl
  intro k hk
  rw [← sum_filter]
  simp [mul_comm]

theorem coprime_square_multiples_error (x : ℝ) (hx : 1 ≤ x)
    (d a M k : ℕ) (hd : 0 < d) (hM : Squarefree M)
    (hdM : Nat.Coprime d M) (hk : 0 < k) (hkcop : Nat.Coprime k (d * M)) :
    |(((((Icc 1 ⌊x⌋₊).filter (fun n => n ≡ a [MOD d])).filter
        (fun n => Nat.Coprime n M)).filter (fun n => k ^ 2 ∣ n)).card : ℝ) -
      ((Nat.totient M : ℝ) / M) * x / ((d : ℝ) * (k : ℝ) ^ 2)| ≤
      3 * (M.divisors.card : ℝ) := by
  have hkD : Nat.Coprime k d := (Nat.coprime_mul_iff_right.mp hkcop).1
  have hkM : Nat.Coprime k M := (Nat.coprime_mul_iff_right.mp hkcop).2
  have hDk := hkD.symm.pow_right 2
  have hqM : Nat.Coprime (d * k ^ 2) M :=
    (hdM.symm.mul_right (hkM.pow_left 2).symm).symm
  have heq : (((Icc 1 ⌊x⌋₊).filter (fun n => n ≡ a [MOD d])).filter
      (fun n => Nat.Coprime n M)).filter (fun n => k ^ 2 ∣ n) =
      ((Ico 1 (⌊x⌋₊ + 1)).filter
        (fun n => n ≡ Nat.chineseRemainder hDk a 0 [MOD d * k ^ 2])).filter
        (fun n => Nat.Coprime n M) := by
    rw [← SieveEstimates.progression_multiples_eq_single_class
      1 (⌊x⌋₊ + 1) d a (k ^ 2) hDk]
    ext n
    simp only [mem_filter, mem_Icc, mem_Ico, Nat.lt_add_one_iff]
    tauto
  have hc := abs_coprime_progression_card_sub_totient_density
    1 (⌊x⌋₊ + 1) (d * k ^ 2) (Nat.chineseRemainder hDk a 0) M
    (by omega) (Nat.mul_pos hd (pow_pos hk 2)) hM hqM
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
    Nat.cast_mul, Nat.cast_pow] at hc
  have hpM : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM.ne_zero)
  have hphi : (0 : ℝ) ≤ (Nat.totient M : ℝ) / M := by positivity
  have hphile : (Nat.totient M : ℝ) / M ≤ 1 := by
    apply (div_le_one hpM).mpr
    exact_mod_cast Nat.totient_le M
  have hden : (1 : ℝ) ≤ (d : ℝ) * (k : ℝ) ^ 2 := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hfloor : |(⌊x⌋₊ : ℝ) - x| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le (by linarith)))]
    have := Nat.lt_floor_add_one x
    linarith
  have herr : |((⌊x⌋₊ : ℝ) / ((d : ℝ) * (k : ℝ) ^ 2)) *
        ((Nat.totient M : ℝ) / M) -
      ((Nat.totient M : ℝ) / M) * x / ((d : ℝ) * (k : ℝ) ^ 2)| ≤ 1 := by
    rw [show ((⌊x⌋₊ : ℝ) / ((d : ℝ) * (k : ℝ) ^ 2)) *
        ((Nat.totient M : ℝ) / M) -
      ((Nat.totient M : ℝ) / M) * x / ((d : ℝ) * (k : ℝ) ^ 2) =
      ((⌊x⌋₊ : ℝ) - x) / ((d : ℝ) * (k : ℝ) ^ 2) *
        ((Nat.totient M : ℝ) / M) by ring,
      abs_mul, abs_div, abs_of_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hden),
      abs_of_nonneg hphi]
    have hdiv : |(⌊x⌋₊ : ℝ) - x| / ((d : ℝ) * (k : ℝ) ^ 2) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      exact hfloor.trans hden
    simpa using mul_le_mul hdiv hphile hphi (by norm_num : (0 : ℝ) ≤ 1)
  have hcard : (1 : ℝ) ≤ M.divisors.card := by
    exact_mod_cast Finset.one_le_card.mpr ⟨1, Nat.one_mem_divisors.mpr hM.ne_zero⟩
  rw [heq]
  exact (abs_sub_le _ _ _).trans ((add_le_add hc herr).trans (by linarith))

theorem square_multiples_empty_of_not_coprime (x : ℝ) (d a M k : ℕ)
    (ha : Nat.Coprime a d) (hcop : ¬Nat.Coprime k (d * M)) :
    (((Icc 1 ⌊x⌋₊).filter (fun n => n ≡ a [MOD d])).filter
      (fun n => Nat.Coprime n M)).filter (fun n => k ^ 2 ∣ n) = ∅ := by
  apply filter_eq_empty_iff.mpr
  intro n hn hk
  obtain ⟨hn, hnM⟩ := mem_filter.mp hn
  obtain ⟨_, hmod⟩ := mem_filter.mp hn
  have hnD : Nat.Coprime n d := by
    rw [Nat.coprime_iff_gcd_eq_one, hmod.gcd_eq]
    exact ha
  have hkn : k ∣ n := (dvd_pow_self k (by norm_num : 2 ≠ 0)).trans hk
  exact hcop (Nat.coprime_mul_iff_right.mpr
    ⟨hnD.coprime_dvd_left hkn, hnM.coprime_dvd_left hkn⟩)

/-- `κ(M, d) = ζ(2)⁻¹ ∏_{p ∣ dM} (1 - p⁻²)⁻¹`. -/
noncomputable def coprimeKappa (M d : ℕ) : ℝ :=
  (1 / (Real.pi ^ 2 / 6)) *
    ∏ p ∈ (d * M).primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹

/-- The number of squarefree `n ≤ x` with `n ≡ a (mod d)` and `(n, M) = 1`. -/
noncomputable def coprimeSquarefreeCount (x : ℝ) (d a M : ℕ) : ℕ :=
  (((Icc 1 ⌊x⌋₊).filter (fun n => n ≡ a [MOD d])).filter
    (fun n => Nat.Coprime n M)).filter Squarefree |>.card

theorem squarefree_count_truncated_error (x : ℝ) (hx : 1 ≤ x)
    (d a M K : ℕ) (hd : 0 < d) (ha : Nat.Coprime a d) (hM : Squarefree M)
    (hdM : Nat.Coprime d M) (hbound : x ≤ (K : ℝ) ^ 2) :
    |(coprimeSquarefreeCount x d a M : ℝ) -
      (((Nat.totient M : ℝ) / M) * x / d) *
        ∑ k ∈ (Icc 1 K).filter (fun k => Nat.Coprime k (d * M)),
          (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2| ≤
      3 * (M.divisors.card : ℝ) * K := by
  let S := ((Icc 1 ⌊x⌋₊).filter (fun n => n ≡ a [MOD d])).filter
    (fun n => Nat.Coprime n M)
  have hS : ∀ n ∈ S, 0 < n ∧ n ≤ K ^ 2 := by
    intro n hn
    have hnI := mem_Icc.mp (mem_filter.mp (mem_filter.mp hn).1).1
    refine ⟨hnI.1, ?_⟩
    have hnx : (n : ℝ) ≤ x := (Nat.cast_le.mpr hnI.2).trans
      (Nat.floor_le (by linarith))
    exact_mod_cast hnx.trans hbound
  rw [coprimeSquarefreeCount, squarefree_card_eq_square_moebius S K hS,
    Finset.sum_filter, mul_sum, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ k ∈ Icc 1 K, 3 * (M.divisors.card : ℝ) := by
      apply sum_le_sum
      intro k hk
      by_cases hcop : Nat.Coprime k (d * M)
      · rw [if_pos hcop]
        have he : (ArithmeticFunction.moebius k : ℝ) *
              ((S.filter (fun n => k ^ 2 ∣ n)).card : ℝ) -
            (((Nat.totient M : ℝ) / M) * x / d) *
              ((ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2) =
            (ArithmeticFunction.moebius k : ℝ) *
              (((S.filter (fun n => k ^ 2 ∣ n)).card : ℝ) -
                ((Nat.totient M : ℝ) / M) * x / ((d : ℝ) * (k : ℝ) ^ 2)) := by ring
        rw [he, abs_mul]
        have hmu : |(ArithmeticFunction.moebius k : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
        have herr := coprime_square_multiples_error x hx d a M k hd hM hdM
          (mem_Icc.mp hk).1 hcop
        exact (mul_le_mul hmu herr (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
      · rw [if_neg hcop]
        have he : S.filter (fun n => k ^ 2 ∣ n) = ∅ :=
          square_multiples_empty_of_not_coprime x d a M k ha hcop
        rw [he]
        simp only [card_empty, Nat.cast_zero, mul_zero, sub_zero, abs_zero]
        positivity
    _ = _ := by simp; ring

/-- `|coprimeSquarefreeCount x d a M - κ(M, d) φ(M) x/(M d)| ≤ 7 τ(M) √x`. -/
theorem coprime_squarefree_count_error (x : ℝ) (hx : 1 ≤ x)
    (d a M : ℕ) (hd : 0 < d) (ha : Nat.Coprime a d) (hM : Squarefree M)
    (hdM : Nat.Coprime d M) :
    |(coprimeSquarefreeCount x d a M : ℝ) -
      (coprimeKappa M d * (Nat.totient M : ℝ) / (M * d)) * x| ≤
      7 * (M.divisors.card : ℝ) * Real.sqrt x := by
  let K := ⌊Real.sqrt x⌋₊ + 1
  have hx0 : 0 ≤ x := by linarith
  have hs1 : 1 ≤ Real.sqrt x := (Real.one_le_sqrt).mpr hx
  have hsq := Real.sq_sqrt hx0
  have hKpos : 0 < K := by dsimp [K]; omega
  have hKlow : Real.sqrt x ≤ (K : ℝ) := by
    have := Nat.lt_floor_add_one (Real.sqrt x)
    dsimp [K]
    push_cast
    linarith
  have hKup : (K : ℝ) ≤ 2 * Real.sqrt x := by
    have := Nat.floor_le (Real.sqrt_nonneg x)
    dsimp [K]
    push_cast
    linarith
  have hKbound : x ≤ (K : ℝ) ^ 2 := by nlinarith
  let c : ℝ := ((Nat.totient M : ℝ) / M) * x / d
  let s : ℝ := ∑ k ∈ (Icc 1 K).filter (fun k => Nat.Coprime k (d * M)),
    (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2
  have hfirst := squarefree_count_truncated_error x hx d a M K hd ha hM hdM hKbound
  change |(coprimeSquarefreeCount x d a M : ℝ) - c * s| ≤
    3 * (M.divisors.card : ℝ) * K at hfirst
  have htail : |s - coprimeKappa M d| ≤ 1 / (K : ℝ) :=
    DivisorEstimates.abs_restricted_moebius_partial_sub_constant_le
      (d * M) K (Nat.mul_pos hd (Nat.pos_of_ne_zero hM.ne_zero)) hKpos
  have hcp : 0 ≤ c := by dsimp [c]; positivity
  have hcle : c ≤ x := by
    have hpM : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM.ne_zero)
    have hp : (Nat.totient M : ℝ) / M ≤ 1 := by
      apply (div_le_one hpM).mpr
      exact_mod_cast Nat.totient_le M
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    exact (div_le_self (mul_nonneg (by positivity) hx0) hd1).trans
      (by nlinarith : (Nat.totient M : ℝ) / M * x ≤ x)
  have htailbound : |c * s - c * coprimeKappa M d| ≤ Real.sqrt x := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hcp]
    calc
      _ ≤ c * (1 / (K : ℝ)) := mul_le_mul_of_nonneg_left htail hcp
      _ ≤ x / K := by simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right hcle (by positivity : (0 : ℝ) ≤ 1 / K)
      _ ≤ Real.sqrt x := by
        apply (div_le_iff₀ (Nat.cast_pos.mpr hKpos)).mpr
        nlinarith
  have hcard : (1 : ℝ) ≤ M.divisors.card := by
    exact_mod_cast Finset.one_le_card.mpr ⟨1, Nat.one_mem_divisors.mpr hM.ne_zero⟩
  have he : c * coprimeKappa M d =
      (coprimeKappa M d * (Nat.totient M : ℝ) / (M * d)) * x := by
    dsimp [c]
    ring
  rw [← he]
  exact (abs_sub_le _ _ _).trans ((add_le_add hfirst htailbound).trans (by
    have hh := mul_le_mul_of_nonneg_left hKup
      (by positivity : 0 ≤ 3 * (M.divisors.card : ℝ))
    nlinarith [Real.sqrt_nonneg x]))

theorem coprime_squarefree_reciprocal_error (d a M : ℕ) (hd : 0 < d)
    (ha : Nat.Coprime a d) (hM : Squarefree M) (hdM : Nat.Coprime d M)
    {A B : ℝ} (hA : 1 ≤ A) (hAB : A < B) :
    |(∑ n ∈ (((Estimates.natWindow A B).filter (fun n => n ≡ a [MOD d])).filter
        (fun n => Nat.Coprime n M)).filter Squarefree, (1 : ℝ) / n) -
      (coprimeKappa M d * (Nat.totient M : ℝ) / (M * d)) * Real.log (B / A)| ≤
      28 * (M.divisors.card : ℝ) / Real.sqrt A := by
  let f : ℕ → ℝ := fun n => if Squarefree n ∧ Nat.Coprime n M then 1 else 0
  have hprefix (t : ℝ) (ht : 1 ≤ t) :
      |(∑ n ∈ (Estimates.natWindow 0 t).filter (fun n => n ≡ a [MOD d]), f n) -
        (coprimeKappa M d * (Nat.totient M : ℝ) / (M * d)) * t| ≤
        (7 * (M.divisors.card : ℝ)) * Real.sqrt t := by
    have hw : (Estimates.natWindow 0 t).filter (fun n => n ≡ a [MOD d]) =
        (Icc 1 ⌊t⌋₊).filter (fun n => n ≡ a [MOD d]) := by
      ext n
      simp only [Estimates.natWindow, mem_filter, mem_Icc]
      constructor
      · tauto
      · rintro ⟨hn, hmod⟩
        exact ⟨⟨hn, Nat.cast_pos.mpr hn.1⟩, hmod⟩
    rw [hw]
    have he : (∑ n ∈ (Icc 1 ⌊t⌋₊).filter (fun n => n ≡ a [MOD d]), f n) =
        (coprimeSquarefreeCount t d a M : ℝ) := by
      simp only [coprimeSquarefreeCount, ← Finset.sum_boole, sum_filter, f]
      apply sum_congr rfl
      intro n hn
      split_ifs <;> simp_all
    rw [he]
    exact coprime_squarefree_count_error t ht d a M hd ha hM hdM
  have h := progression_harmonic_of_sqrt_prefix f
    (coprimeKappa M d * (Nat.totient M : ℝ) / (M * d))
    (7 * (M.divisors.card : ℝ)) (by positivity) d a hprefix hA hAB
  have he : (∑ n ∈ (Estimates.natWindow A B).filter (fun n => n ≡ a [MOD d]), f n / n) =
      ∑ n ∈ (((Estimates.natWindow A B).filter (fun n => n ≡ a [MOD d])).filter
        (fun n => Nat.Coprime n M)).filter Squarefree, (1 : ℝ) / n := by
    simp only [sum_filter, f]
    apply sum_congr rfl
    intro n hn
    split_ifs <;> simp_all
  rw [he] at h
  convert h using 1; ring

theorem reciprocal_square_prime_power (p : ℕ) (hp : Nat.Prime p) :
    (∑' j : ℕ, (1 : ℝ) / ((p ^ j : ℕ) : ℝ) ^ 2) =
      (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ := by
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr hp.one_lt
  have hlt : ‖((p : ℝ) ^ 2)⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact (inv_lt_one₀ (by positivity)).mpr (by nlinarith)
  have he : (fun j : ℕ => (1 : ℝ) / ((p ^ j : ℕ) : ℝ) ^ 2) =
      (fun j : ℕ => (((p : ℝ) ^ 2)⁻¹) ^ j) := by
    funext j
    simp only [Nat.cast_pow, one_div, ← pow_mul, mul_comm j 2, inv_pow]
  rw [he]
  exact tsum_geometric_of_norm_lt_one hlt

theorem finite_reciprocal_square_product_le (N : ℕ) :
    (∏ p ∈ N.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹) ≤ Real.pi ^ 2 / 6 := by
  let f : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2
  have hf : Summable f := hasSum_zeta_two.summable
  have hn : Summable (fun n => ‖f n‖) := hf.norm
  have hprod := EulerProduct.prod_filter_prime_tsum_eq_tsum_factoredNumbers
    (f := f) (by simp [f]) (fun {m n} _ => by simp only [f, Nat.cast_mul, mul_pow]; ring)
    hn N.primeFactors
  have hfilter : N.primeFactors.filter Nat.Prime = N.primeFactors :=
    filter_true_of_mem (fun p hp => Nat.prime_of_mem_primeFactors hp)
  rw [hfilter] at hprod
  have hrewrite : (∏ p ∈ N.primeFactors, ∑' j : ℕ, f (p ^ j)) =
      ∏ p ∈ N.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ := by
    apply prod_congr rfl
    intro p hp
    exact reciprocal_square_prime_power p (Nat.prime_of_mem_primeFactors hp)
  rw [hrewrite] at hprod
  rw [hprod]
  exact (Summable.tsum_le_tsum_of_inj (f := fun n : Nat.factoredNumbers N.primeFactors => f n)
    (g := f) (fun n => (n : ℕ)) Subtype.val_injective
    (fun _ _ => by dsimp [f]; positivity) (fun _ => le_rfl)
    (hf.comp_injective Subtype.val_injective) hf).trans_eq
      hasSum_zeta_two.tsum_eq

theorem coprimeKappa_bounds (M d : ℕ) :
    1 / (Real.pi ^ 2 / 6) ≤ coprimeKappa M d ∧ coprimeKappa M d ≤ 1 := by
  have hb : 0 < Real.pi ^ 2 / 6 := by positivity
  have hprod : (1 : ℝ) ≤ ∏ p ∈ (d * M).primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ := by
    calc
      (1 : ℝ) = ∏ _p ∈ (d * M).primeFactors, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.prod_le_prod (fun _ _ => by norm_num : ∀ p ∈ (d * M).primeFactors,
          (0 : ℝ) ≤ 1)
        intro p hp
        have hp1 : (1 : ℝ) < p :=
          Nat.one_lt_cast.mpr (Nat.prime_of_mem_primeFactors hp).one_lt
        have hf : 0 < 1 - ((p : ℝ) ^ 2)⁻¹ := by
          have hi : ((p : ℝ) ^ 2)⁻¹ < 1 :=
            (inv_lt_one₀ (by positivity)).mpr (by nlinarith)
          linarith
        exact (one_le_inv₀ hf).mpr (by
          have : (0 : ℝ) ≤ ((p : ℝ) ^ 2)⁻¹ := by positivity
          linarith)
  constructor
  · change 1 / (Real.pi ^ 2 / 6) ≤ (1 / (Real.pi ^ 2 / 6)) * _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod
      (by positivity : (0 : ℝ) ≤ 1 / (Real.pi ^ 2 / 6))
  · have hh := mul_le_mul_of_nonneg_left (finite_reciprocal_square_product_le (d * M))
      (by positivity : (0 : ℝ) ≤ 1 / (Real.pi ^ 2 / 6))
    simpa only [coprimeKappa, one_div, inv_mul_cancel₀ hb.ne'] using hh

/-- The `n ∈ [1, t]` with `n ≡ a (mod d)` and `(n, M) = 1`. -/
noncomputable def coprimeProgression (t : ℝ) (d a M : ℕ) : Finset ℕ :=
  ((Icc 1 ⌊t⌋₊).filter (fun n => n ≡ a [MOD d])).filter (fun n => Nat.Coprime n M)

theorem coprime_progression_prefix_error (t : ℝ) (ht : 0 ≤ t)
    (d a M : ℕ) (hd : 0 < d) (hM : Squarefree M) (hdM : Nat.Coprime d M) :
    |((coprimeProgression t d a M).card : ℝ) -
      ((Nat.totient M : ℝ) / (M * d)) * t| ≤ 3 * (M.divisors.card : ℝ) := by
  have hc := abs_coprime_progression_card_sub_totient_density
    1 (⌊t⌋₊ + 1) d a M (by omega) hd hM hdM
  have hset : Ico 1 (⌊t⌋₊ + 1) = Icc 1 ⌊t⌋₊ := by ext n; simp only [mem_Ico, mem_Icc]; omega
  rw [hset] at hc
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hc
  have hMp : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM.ne_zero)
  have hdp : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hphi : 0 ≤ (Nat.totient M : ℝ) / M := by positivity
  have hphile : (Nat.totient M : ℝ) / M ≤ 1 := by
    apply (div_le_one hMp).mpr
    exact_mod_cast Nat.totient_le M
  have hfloor : |(⌊t⌋₊ : ℝ) - t| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le ht))]
    have := Nat.lt_floor_add_one t
    linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have he : |((⌊t⌋₊ : ℝ) / d) * ((Nat.totient M : ℝ) / M) -
      ((Nat.totient M : ℝ) / (M * d)) * t| ≤ 1 := by
    rw [show ((⌊t⌋₊ : ℝ) / d) * ((Nat.totient M : ℝ) / M) -
        ((Nat.totient M : ℝ) / (M * d)) * t =
        (((⌊t⌋₊ : ℝ) - t) / d) * ((Nat.totient M : ℝ) / M) by ring,
      abs_mul, abs_div, abs_of_pos hdp, abs_of_nonneg hphi]
    have hdiv : |(⌊t⌋₊ : ℝ) - t| / d ≤ 1 :=
      (div_le_one hdp).mpr (hfloor.trans hd1)
    simpa using mul_le_mul hdiv hphile hphi zero_le_one
  have hcard : (1 : ℝ) ≤ M.divisors.card := by
    exact_mod_cast Finset.one_le_card.mpr ⟨1, Nat.one_mem_divisors.mpr hM.ne_zero⟩
  exact (abs_sub_le _ _ _).trans ((add_le_add hc he).trans (by linarith))

theorem coprime_reciprocal_progression (d a M : ℕ) (hd : 0 < d)
    (hM : Squarefree M) (hdM : Nat.Coprime d M)
    {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    |(∑ n ∈ ((Estimates.natWindow A B).filter (fun n => n ≡ a [MOD d])).filter
        (fun n => Nat.Coprime n M), (1 : ℝ) / n) -
      ((Nat.totient M : ℝ) / (M * d)) * Real.log (B / A)| ≤
      12 * (M.divisors.card : ℝ) / A := by
  let f : ℕ → ℝ := fun n => if n = 0 then 0 else
    if n ≡ a [MOD d] ∧ Nat.Coprime n M then 1 else 0
  have hprefix (t : ℝ) : (∑ n ∈ Icc 0 ⌊t⌋₊, f n) =
      ((coprimeProgression t d a M).card : ℝ) := by
    rw [← Finset.add_sum_Ioc_eq_sum_Icc (f := f) (Nat.zero_le ⌊t⌋₊)]
    simp only [f, if_pos rfl, zero_add]
    have hset : Ioc 0 ⌊t⌋₊ = Icc 1 ⌊t⌋₊ := by ext n; simp; omega
    rw [hset]
    simp only [coprimeProgression, ← Finset.sum_boole, sum_filter]
    apply sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    by_cases hm : n ≡ a [MOD d] <;> by_cases hc : Nat.Coprime n M <;> simp [hn0, hm, hc]
  have h := harmonic_of_bounded_prefix f ((Nat.totient M : ℝ) / (M * d))
    (3 * M.divisors.card) (by positivity) hA hAB (by
      intro t ht
      rw [hprefix]
      exact coprime_progression_prefix_error t (hA.le.trans ht) d a M hd hM hdM)
  have hsum : (∑ n ∈ Ioc ⌊A⌋₊ ⌊B⌋₊, f n / n) =
      ∑ n ∈ ((Estimates.natWindow A B).filter (fun n => n ≡ a [MOD d])).filter
        (fun n => Nat.Coprime n M), (1 : ℝ) / n := by
    rw [PrimeEstimates.natWindow_eq_Ioc_floor hA.le]
    simp only [sum_filter]
    apply sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by have := (mem_Ioc.mp hn).1; omega
    by_cases hm : n ≡ a [MOD d]
    · simp only [f, if_neg hn0, hm, true_and, if_true]
      split_ifs <;> simp
    · simp [f, hn0, hm]
  rw [hsum] at h
  convert h using 1
  ring

end

/-! ## Long windows

The main term `κ(M,1) φ(M)/M · log(U₁/U₀)` has `κ ∈ [1/ζ(2), 1]`. The error
`28 τ(M)/√U₀` is `O(X^{-a₀/4})` because `τ(M) ≪ X^{a₀/4}`, whereas
`φ(M)/M · log(U₁/U₀) ≫ 1` by `M/φ(M) ≪ log(2M)`.
-/

section

open Filter

/-- `φ(M)/M · log(U₁/U₀) ≥ c₀ / (3 C_γ (1+|C₀|))` for `X ≥ 2`, `1 ≤ M ≤ X^{C₀}`
and `log(U₁/U₀) ≥ c₀ log X`. -/
theorem totient_density_mul_log_ge (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) {X : ℝ} (hX : 2 ≤ X)
    {M : ℕ} (hM : 0 < M) (hMX : (M : ℝ) ≤ X ^ C₀) {U₀ U₁ : ℝ}
    (hlog : c₀ * Real.log X ≤ Real.log (U₁ / U₀)) :
    c₀ / (3 * DivisorEstimates.gammaConstant * (1 + |C₀|)) ≤
      (Nat.totient M : ℝ) / M * Real.log (U₁ / U₀) := by
  have hG := DivisorEstimates.gammaConstant_pos
  have hXp : 0 < X := by linarith
  have hM0 : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hφ : (0 : ℝ) < Nat.totient M := Nat.cast_pos.mpr (Nat.totient_pos.mpr hM)
  have hL2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  have hL : 0 < Real.log X := (Real.log_pos (by norm_num)).trans_le hL2
  have hlogM : Real.log M ≤ C₀ * Real.log X := by
    rw [← Real.log_rpow hXp]
    exact Real.log_le_log hM0 hMX
  have hlog2M : Real.log (2 * M) ≤ (1 + |C₀|) * Real.log X := by
    rw [Real.log_mul (by norm_num) hM0.ne']
    have := mul_le_mul_of_nonneg_right (le_abs_self C₀) hL.le
    nlinarith
  have hratio := DivisorEstimates.totient_ratio_le_log M hM
  have hone : 1 ≤ (Nat.totient M : ℝ) / M * (3 * DivisorEstimates.gammaConstant *
      ((1 + |C₀|) * Real.log X)) := by
    have h1 : (M : ℝ) / Nat.totient M ≤
        3 * DivisorEstimates.gammaConstant * ((1 + |C₀|) * Real.log X) :=
      hratio.trans (mul_le_mul_of_nonneg_left hlog2M (by positivity))
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (Nat.totient M : ℝ) / M)
    have h3 : (Nat.totient M : ℝ) / M * ((M : ℝ) / Nat.totient M) = 1 := by
      field_simp
    linarith
  have hρ : 0 ≤ (Nat.totient M : ℝ) / M := by positivity
  have hden : 0 < 3 * DivisorEstimates.gammaConstant * (1 + |C₀|) := by positivity
  rw [div_le_iff₀ hden]
  have h4 := mul_le_mul_of_nonneg_left hlog hρ
  nlinarith

theorem squarefree_coprime_window_eq (U₀ U₁ : ℝ) (M : ℕ) :
    (Estimates.natWindow U₀ U₁).filter (fun n => Squarefree n ∧ Nat.Coprime n M) =
      (((Estimates.natWindow U₀ U₁).filter (fun n => n ≡ 0 [MOD 1])).filter
        (fun n => Nat.Coprime n M)).filter Squarefree := by
  ext n
  simp only [Finset.mem_filter, Nat.modEq_one]
  tauto

/-- The estimate (6) of Lemma 3.2: for fixed `0 < a₀`, `b₀`, `0 < c₀`, `C₀` there are
`c, C > 0` and `X₀` such that, uniformly for `X ≥ X₀`,
`X^{a₀} ≤ U₀ < U₁ ≤ X^{b₀}` with `U₁/U₀ ≥ X^{c₀}`, and squarefree `M ≤ X^{C₀}`,
`c (φ(M)/M) log(U₁/U₀) ≤ ∑_{U₀<n≤U₁, n squarefree, (n,M)=1} 1/n
  ≤ C (φ(M)/M) log(U₁/U₀)`. -/
theorem squarefree_coprime_reciprocal_asymp (a₀ b₀ c₀ C₀ : ℝ) (ha₀ : 0 < a₀)
    (hc₀ : 0 < c₀) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ U₀ U₁ : ℝ, X ^ a₀ ≤ U₀ → U₀ < U₁ → U₁ ≤ X ^ b₀ → X ^ c₀ ≤ U₁ / U₀ →
      ∀ M : ℕ, Squarefree M → (M : ℝ) ≤ X ^ C₀ →
        c * ((Nat.totient M : ℝ) / M) * Real.log (U₁ / U₀) ≤
            ∑ n ∈ (Estimates.natWindow U₀ U₁).filter
              (fun n => Squarefree n ∧ Nat.Coprime n M), (1 : ℝ) / n ∧
          ∑ n ∈ (Estimates.natWindow U₀ U₁).filter
              (fun n => Squarefree n ∧ Nat.Coprime n M), (1 : ℝ) / n ≤
            C * ((Nat.totient M : ℝ) / M) * Real.log (U₁ / U₀) := by
  have hG := DivisorEstimates.gammaConstant_pos
  set c₁ := c₀ / (3 * DivisorEstimates.gammaConstant * (1 + |C₀|)) with hc₁
  have hc₁pos : 0 < c₁ := div_pos hc₀ (by positivity)
  set κ₀ : ℝ := 1 / (Real.pi ^ 2 / 6) with hκ₀
  have hκ₀pos : 0 < κ₀ := by have := Real.pi_pos; positivity
  set δ := κ₀ * c₁ / 2 with hδ
  have hδpos : 0 < δ := by positivity
  set ε := a₀ / (4 * (1 + |C₀|)) with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨Cτ, hCτ, hτ⟩ := exists_squarefree_divisor_card_le_rpow hεpos
  have hpow : ∀ᶠ X : ℝ in atTop, 28 * Cτ / δ ≤ X ^ (a₀ / 4) :=
    (tendsto_rpow_atTop (by positivity : 0 < a₀ / 4)).eventually
      (eventually_ge_atTop (28 * Cτ / δ))
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp ((eventually_ge_atTop (2 : ℝ)).and hpow)
  refine ⟨κ₀ / 2, 2, X₀, by positivity, by norm_num, ?_⟩
  intro X hX U₀ U₁ hU₀ hU₀₁ _ hratio M hM hMX
  obtain ⟨hX2, hXpow⟩ := hX₀ X hX
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM.ne_zero
  have hM0 : (0 : ℝ) < M := Nat.cast_pos.mpr hMpos
  have hU₀1 : 1 ≤ U₀ := (Real.one_le_rpow hX1 ha₀.le).trans hU₀
  have hU₀p : 0 < U₀ := by linarith
  have hlog : c₀ * Real.log X ≤ Real.log (U₁ / U₀) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hXp c₀) hratio
    rwa [Real.log_rpow hXp] at h
  have hmain := totient_density_mul_log_ge c₀ C₀ hc₀ hX2 hMpos hMX hlog
  set ρℓ := (Nat.totient M : ℝ) / M * Real.log (U₁ / U₀) with hρℓ
  have herr := coprime_squarefree_reciprocal_error 1 0 M one_pos (Nat.coprime_one_right 0) hM
    (Nat.coprime_one_left M) hU₀1 hU₀₁
  rw [← squarefree_coprime_window_eq] at herr
  set S := ∑ n ∈ (Estimates.natWindow U₀ U₁).filter
    (fun n => Squarefree n ∧ Nat.Coprime n M), (1 : ℝ) / n with hS
  have hcoef : coprimeKappa M 1 * (Nat.totient M : ℝ) / (M * ((1 : ℕ) : ℝ)) *
      Real.log (U₁ / U₀) = coprimeKappa M 1 * ρℓ := by
    rw [hρℓ, Nat.cast_one, mul_one]
    ring
  rw [hcoef] at herr
  obtain ⟨hκlo, hκhi⟩ := coprimeKappa_bounds M 1
  have hτM : (M.divisors.card : ℝ) ≤ Cτ * X ^ (a₀ / 4) := by
    calc
      _ ≤ Cτ * (M : ℝ) ^ ε := hτ M hM
      _ ≤ Cτ * (X ^ C₀) ^ ε :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hM0.le hMX hεpos.le) hCτ.le
      _ = Cτ * X ^ (C₀ * ε) := by rw [← Real.rpow_mul hXp.le]
      _ ≤ Cτ * X ^ (a₀ / 4) := by
        apply mul_le_mul_of_nonneg_left _ hCτ.le
        apply Real.rpow_le_rpow_of_exponent_le hX1
        have h1 : C₀ * ε ≤ |C₀| * ε := mul_le_mul_of_nonneg_right (le_abs_self C₀) hεpos.le
        have h2 : ε + |C₀| * ε = a₀ / 4 := by
          rw [hε]
          field_simp
        linarith
  have hsqrt : X ^ (a₀ / 4) * X ^ (a₀ / 4) ≤ Real.sqrt U₀ := by
    rw [← Real.rpow_add hXp, show a₀ / 4 + a₀ / 4 = a₀ / 2 by ring]
    have hsq : (X ^ (a₀ / 2)) ^ (2 : ℕ) = X ^ a₀ := by
      rw [← Real.rpow_natCast (X ^ (a₀ / 2)) 2, ← Real.rpow_mul hXp.le]
      congr 1
      ring
    have hrootU := Real.sq_sqrt hU₀p.le
    nlinarith [Real.sqrt_nonneg U₀, Real.rpow_nonneg hXp.le (a₀ / 2)]
  have hXq : 0 < X ^ (a₀ / 4) := Real.rpow_pos_of_pos hXp _
  have hsmall : 28 * (M.divisors.card : ℝ) / Real.sqrt U₀ ≤ δ := by
    have hsU : 0 < Real.sqrt U₀ := Real.sqrt_pos.mpr hU₀p
    rw [div_le_iff₀ hsU]
    have h1 : 28 * Cτ ≤ δ * X ^ (a₀ / 4) := by
      have := (div_le_iff₀ hδpos).mp hXpow
      linarith
    calc
      28 * (M.divisors.card : ℝ) ≤ 28 * (Cτ * X ^ (a₀ / 4)) := by linarith
      _ = (28 * Cτ) * X ^ (a₀ / 4) := by ring
      _ ≤ (δ * X ^ (a₀ / 4)) * X ^ (a₀ / 4) := mul_le_mul_of_nonneg_right h1 hXq.le
      _ = δ * (X ^ (a₀ / 4) * X ^ (a₀ / 4)) := by ring
      _ ≤ δ * Real.sqrt U₀ := mul_le_mul_of_nonneg_left hsqrt hδpos.le
  have hρℓpos : 0 ≤ ρℓ := hc₁pos.le.trans hmain
  have hab := abs_le.mp (herr.trans hsmall)
  have hδle : δ ≤ κ₀ / 2 * ρℓ := by
    rw [hδ]
    have := mul_le_mul_of_nonneg_left hmain hκ₀pos.le
    linarith
  constructor
  · have h1 : κ₀ * ρℓ ≤ coprimeKappa M 1 * ρℓ := mul_le_mul_of_nonneg_right hκlo hρℓpos
    have h2 : κ₀ / 2 * ((Nat.totient M : ℝ) / M) * Real.log (U₁ / U₀) =
        κ₀ / 2 * ρℓ := by rw [hρℓ]; ring
    rw [h2]
    linarith [hab.1]
  · have h1 : coprimeKappa M 1 * ρℓ ≤ ρℓ := by
      simpa using mul_le_mul_of_nonneg_right hκhi hρℓpos
    have h2 : 2 * ((Nat.totient M : ℝ) / M) * Real.log (U₁ / U₀) = 2 * ρℓ := by
      rw [hρℓ]; ring
    have hκ₀le : κ₀ ≤ 1 := hκlo.trans hκhi
    have h3 : κ₀ * ρℓ ≤ 1 * ρℓ := mul_le_mul_of_nonneg_right hκ₀le hρℓpos
    rw [h2]
    linarith [hab.2]

/-- The first assertion of Lemma 3.2, the case `M = 1`:
`∑_{U₀<n≤U₁, n squarefree} 1/n ≍ log(U₁/U₀)` uniformly for
`X^{a₀} ≤ U₀ < U₁ ≤ X^{b₀}` with `U₁/U₀ ≥ X^{c₀}`. -/
theorem squarefree_reciprocal_asymp (a₀ b₀ c₀ : ℝ) (ha₀ : 0 < a₀) (hc₀ : 0 < c₀) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ U₀ U₁ : ℝ, X ^ a₀ ≤ U₀ → U₀ < U₁ → U₁ ≤ X ^ b₀ → X ^ c₀ ≤ U₁ / U₀ →
        c * Real.log (U₁ / U₀) ≤
            ∑ n ∈ (Estimates.natWindow U₀ U₁).filter Squarefree, (1 : ℝ) / n ∧
          ∑ n ∈ (Estimates.natWindow U₀ U₁).filter Squarefree, (1 : ℝ) / n ≤
            C * Real.log (U₁ / U₀) := by
  obtain ⟨c, C, X₀, hc, hC, h⟩ := squarefree_coprime_reciprocal_asymp a₀ b₀ c₀ 0 ha₀ hc₀
  refine ⟨c, C, X₀, hc, hC, ?_⟩
  intro X hX U₀ U₁ hU₀ hU₀₁ hU₁ hratio
  have h1 := h X hX U₀ U₁ hU₀ hU₀₁ hU₁ hratio 1 squarefree_one (by simp)
  have hset : (Estimates.natWindow U₀ U₁).filter (fun n => Squarefree n ∧ Nat.Coprime n 1) =
      (Estimates.natWindow U₀ U₁).filter Squarefree := by
    ext n
    simp
  simpa only [hset, Nat.totient_one, Nat.cast_one, div_one, mul_one] using h1

end

end ErdosStraus.ProgressionEstimates
