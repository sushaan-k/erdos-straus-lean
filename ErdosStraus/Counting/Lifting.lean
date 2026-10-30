import Mathlib.Tactic
import Batteries.Tactic.Lemma
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AlmostPrime
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import ErdosStraus.Basic
import Mathlib.NumberTheory.SmoothNumbers
import ErdosStraus.Estimates.PrimeCounts

/-!
# Lemma 5.5: lifting

Let `E` be a set of positive integers closed under taking divisors, and suppose that
`#{u ≤ T : u ∈ E, (u, P(y)) = 1} ≤ A T e^{-F}` for `√N ≤ T ≤ N`. Then for large `N`,
uniformly in `2 ≤ y ≤ C log N`, `#(E ∩ [1, N]) ≤ c A N log(2y) e^{-F} + N^{3/4+ε}`.
The proof writes `n = s u` with `s` the `y`-smooth part of `n` and bounds the terms with
`s > √N` by Rankin's method. The file also proves the two absorption lemmas that finish
the proof of Theorem 2.
-/

namespace ErdosStraus

/-! ## Rankin's bound for smooth numbers

The sum `∑ n^{-α}` over `z`-smooth `n ≤ K` is at most the Euler product
`∏_{p < z} ∑_{e ≤ log_p K} p^{-eα}`, whose logarithm is at most
`∑_{p < z} p^{-α}/(1 - p^{-α}) ≪ ∑_{n ≤ z} n^{-α}`. -/

section Rankin

open Classical

/-- `∑ n^{-α}` over the `n ≤ K` whose prime factors are all `< z`. -/
noncomputable def rankinWeightedSmoothSum (K z : ℕ) (α : ℝ) : ℝ :=
  ∑ n ∈ Nat.smoothNumbersUpTo K z, (n : ℝ) ^ (-α)

/-- The Euler product `∏_{p < z} ∑_{0 ≤ e ≤ log_p K} p^{-eα}`. -/
noncomputable def rankinPrimeGeomProduct (K z : ℕ) (α : ℝ) : ℝ :=
  ∏ p ∈ z.primesBelow,
    ∑ e ∈ Finset.range (Nat.log p K + 1), (((p ^ e : ℕ) : ℝ)) ^ (-α)

/-- The factor `∑_{0 ≤ e ≤ log_p K} p^{-eα}` of `rankinPrimeGeomProduct` at `p`. -/
noncomputable def rankinPrimeGeomLocalFactor (K : ℕ) (α : ℝ) (p : ℕ) : ℝ :=
  ∑ e ∈ Finset.range (Nat.log p K + 1), (((p ^ e : ℕ) : ℝ)) ^ (-α)

/-- The sum over `p < z` of the logarithms of the local factors. -/
noncomputable def rankinPrimeGeomLogSum (K z : ℕ) (α : ℝ) : ℝ :=
  ∑ p ∈ z.primesBelow, Real.log (rankinPrimeGeomLocalFactor K α p)

/-- The sum over `p < z` of the local factors minus `1`; it bounds
`rankinPrimeGeomLogSum` since `log x ≤ x - 1`. -/
noncomputable def rankinPrimeGeomExcessSum (K z : ℕ) (α : ℝ) : ℝ :=
  ∑ p ∈ z.primesBelow, (rankinPrimeGeomLocalFactor K α p - 1)

/-- The local factor without its `e = 0` term, `∑_{1 ≤ e ≤ log_p K} (p^e)^{-α}`; the
summation index `e` stands for the exponent `e + 1`. -/
noncomputable def rankinPrimeGeomLocalTail (K : ℕ) (α : ℝ) (p : ℕ) : ℝ :=
  ∑ e ∈ Finset.range (Nat.log p K), (((p ^ (e + 1) : ℕ) : ℝ)) ^ (-α)

/-- The sum over `p < z` of the local tails. -/
noncomputable def rankinPrimeGeomTailSum (K z : ℕ) (α : ℝ) : ℝ :=
  ∑ p ∈ z.primesBelow, rankinPrimeGeomLocalTail K α p

/-- The same local tail, written as a finite geometric sum with ratio
`p^{-α}`. -/
noncomputable def rankinPrimeGeomLocalRpowTail (K : ℕ) (α : ℝ) (p : ℕ) : ℝ :=
  ∑ e ∈ Finset.range (Nat.log p K), ((p : ℝ) ^ (-α)) ^ (e + 1)

/-- The sum over `p < z` of the local tails written as geometric sums. -/
noncomputable def rankinPrimeGeomRpowTailSum (K z : ℕ) (α : ℝ) : ℝ :=
  ∑ p ∈ z.primesBelow, rankinPrimeGeomLocalRpowTail K α p

/-- `p^{-α}/(1 - p^{-α})`, the sum of the infinite geometric series that bounds the
local tail. -/
noncomputable def rankinPrimeGeomLocalGeomMajorant (α : ℝ) (p : ℕ) : ℝ :=
  (p : ℝ) ^ (-α) / (1 - (p : ℝ) ^ (-α))

/-- `∑_{p < z} p^{-α}/(1 - p^{-α})`. -/
noncomputable def rankinPrimeGeomGeomMajorantSum (z : ℕ) (α : ℝ) : ℝ :=
  ∑ p ∈ z.primesBelow, rankinPrimeGeomLocalGeomMajorant α p

/-- `∑_{p < z} p^{-α}`. -/
noncomputable def rankinPrimeRpowSum (z : ℕ) (α : ℝ) : ℝ :=
  ∑ p ∈ z.primesBelow, (p : ℝ) ^ (-α)

/-- `∑_{1 ≤ n ≤ z} n^{-α}`. -/
noncomputable def rankinNatRpowSum (z : ℕ) (α : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 z, (n : ℝ) ^ (-α)

/-- The exponent vectors `(e_p)_{p < z}` with `0 ≤ e_p ≤ log_p K`. -/
noncomputable def rankinPrimeExponentBox (K z : ℕ) :
    Finset (∀ p : ℕ, p ∈ z.primesBelow → ℕ) :=
  z.primesBelow.pi fun p => Finset.range (Nat.log p K + 1)

/-- The weight `∏_{p < z} (p^{e_p})^{-α}` of an exponent vector. -/
noncomputable def rankinPrimeExponentBoxWeight (z : ℕ) (α : ℝ)
    (v : ∀ p : ℕ, p ∈ z.primesBelow → ℕ) : ℝ :=
  ∏ x ∈ z.primesBelow.attach,
    (((x.1 ^ v x.1 x.2 : ℕ) : ℝ)) ^ (-α)

theorem one_le_rankinPrimeGeomLocalFactor (K : ℕ) (α : ℝ) (p : ℕ) :
    1 ≤ rankinPrimeGeomLocalFactor K α p := by
  classical
  unfold rankinPrimeGeomLocalFactor
  have h0mem : 0 ∈ Finset.range (Nat.log p K + 1) := by
    rw [Finset.mem_range]
    omega
  have hterm0 :
      ((((p ^ 0 : ℕ) : ℝ)) ^ (-α)) = 1 := by
    simp
  calc
    (1 : ℝ) = (((p ^ 0 : ℕ) : ℝ)) ^ (-α) := hterm0.symm
    _ ≤ ∑ e ∈ Finset.range (Nat.log p K + 1), (((p ^ e : ℕ) : ℝ)) ^ (-α) :=
        Finset.single_le_sum
          (by
            intro e _he
            exact Real.rpow_nonneg (Nat.cast_nonneg (p ^ e)) (-α))
          h0mem

theorem rankinPrimeGeomLocalFactor_pos (K : ℕ) (α : ℝ) (p : ℕ) :
    0 < rankinPrimeGeomLocalFactor K α p :=
  lt_of_lt_of_le zero_lt_one (one_le_rankinPrimeGeomLocalFactor K α p)

theorem rankinPrimeGeomProduct_pos (K z : ℕ) (α : ℝ) :
    0 < rankinPrimeGeomProduct K z α := by
  classical
  unfold rankinPrimeGeomProduct
  exact Finset.prod_pos (by
    intro p _hp
    exact rankinPrimeGeomLocalFactor_pos K α p)

theorem log_rankinPrimeGeomProduct_eq_logSum (K z : ℕ) (α : ℝ) :
    Real.log (rankinPrimeGeomProduct K z α) =
      rankinPrimeGeomLogSum K z α := by
  classical
  unfold rankinPrimeGeomProduct rankinPrimeGeomLogSum rankinPrimeGeomLocalFactor
  rw [Real.log_prod]
  intro p _hp
  exact ne_of_gt (rankinPrimeGeomLocalFactor_pos K α p)

theorem rankinPrimeGeomLogSum_le_excessSum (K z : ℕ) (α : ℝ) :
    rankinPrimeGeomLogSum K z α ≤ rankinPrimeGeomExcessSum K z α := by
  classical
  unfold rankinPrimeGeomLogSum rankinPrimeGeomExcessSum
  apply Finset.sum_le_sum
  intro p _hp
  exact Real.log_le_sub_one_of_pos (rankinPrimeGeomLocalFactor_pos K α p)

theorem rankinPrimeGeomLocalFactor_eq_tail_add_one (K : ℕ) (α : ℝ) (p : ℕ) :
    rankinPrimeGeomLocalFactor K α p = rankinPrimeGeomLocalTail K α p + 1 := by
  classical
  unfold rankinPrimeGeomLocalFactor rankinPrimeGeomLocalTail
  rw [Finset.sum_range_succ']
  simp

theorem rankinPrimeGeomExcessSum_eq_tailSum (K z : ℕ) (α : ℝ) :
    rankinPrimeGeomExcessSum K z α = rankinPrimeGeomTailSum K z α := by
  classical
  unfold rankinPrimeGeomExcessSum rankinPrimeGeomTailSum
  apply Finset.sum_congr rfl
  intro p _hp
  rw [rankinPrimeGeomLocalFactor_eq_tail_add_one K α p]
  ring

theorem rankinPrimeGeomLocalTail_eq_rpowTail
    {K p : ℕ} {α : ℝ} (hp : Nat.Prime p) :
    rankinPrimeGeomLocalTail K α p = rankinPrimeGeomLocalRpowTail K α p := by
  classical
  unfold rankinPrimeGeomLocalTail rankinPrimeGeomLocalRpowTail
  have hp_pos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  apply Finset.sum_congr rfl
  intro e _he
  have hcast : (((p ^ (e + 1) : ℕ) : ℝ)) = (p : ℝ) ^ (e + 1) := by
    norm_num [Nat.cast_pow]
  calc
    (((p ^ (e + 1) : ℕ) : ℝ)) ^ (-α)
        = ((p : ℝ) ^ (e + 1)) ^ (-α) := by rw [hcast]
    _ = (p : ℝ) ^ ((e + 1 : ℕ) * (-α)) := by
          exact (Real.rpow_natCast_mul hp_pos.le (e + 1) (-α)).symm
    _ = (p : ℝ) ^ ((-α) * (e + 1 : ℕ)) := by
          congr 1
          ring_nf
    _ = ((p : ℝ) ^ (-α)) ^ (e + 1) := by
          exact Real.rpow_mul_natCast hp_pos.le (-α) (e + 1)

theorem rankinPrimeGeomTailSum_eq_rpowTailSum (K z : ℕ) (α : ℝ) :
    rankinPrimeGeomTailSum K z α = rankinPrimeGeomRpowTailSum K z α := by
  classical
  unfold rankinPrimeGeomTailSum rankinPrimeGeomRpowTailSum
  apply Finset.sum_congr rfl
  intro p hpz
  exact rankinPrimeGeomLocalTail_eq_rpowTail (Nat.prime_of_mem_primesBelow hpz)

theorem finite_geometric_shifted_sum_le_div_one_sub
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    (∑ e ∈ Finset.range N, q ^ (e + 1)) ≤ q / (1 - q) := by
  have hden_pos : 0 < 1 - q := sub_pos.mpr hq1
  have hden_ne : 1 - q ≠ 0 := ne_of_gt hden_pos
  have hq_ne : q ≠ 1 := ne_of_lt hq1
  have hq_sub_ne : q - 1 ≠ 0 := sub_ne_zero.mpr hq_ne
  have hsum_eq :
      (∑ e ∈ Finset.range N, q ^ (e + 1)) =
        q * ∑ e ∈ Finset.range N, q ^ e := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _he
    rw [pow_succ']
  have hgeom :
      (∑ e ∈ Finset.range N, q ^ e) = (1 - q ^ N) / (1 - q) := by
    rw [geom_sum_eq hq_ne N]
    field_simp [hden_ne, hq_sub_ne]
    ring_nf
  have hgeom_le :
      (∑ e ∈ Finset.range N, q ^ e) ≤ 1 / (1 - q) := by
    rw [hgeom]
    exact div_le_div_of_nonneg_right
      (sub_le_self 1 (pow_nonneg hq0 N)) hden_pos.le
  calc
    (∑ e ∈ Finset.range N, q ^ (e + 1))
        = q * ∑ e ∈ Finset.range N, q ^ e := hsum_eq
    _ ≤ q * (1 / (1 - q)) := mul_le_mul_of_nonneg_left hgeom_le hq0
    _ = q / (1 - q) := by ring_nf

theorem rankinPrimeGeomLocalRpowTail_le_geomMajorant
    {K p : ℕ} {α : ℝ} (hα0 : 0 < α) (hp : Nat.Prime p) :
    rankinPrimeGeomLocalRpowTail K α p ≤
      rankinPrimeGeomLocalGeomMajorant α p := by
  classical
  unfold rankinPrimeGeomLocalRpowTail rankinPrimeGeomLocalGeomMajorant
  have hp_pos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_one_lt : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq0 : 0 ≤ (p : ℝ) ^ (-α) :=
    (Real.rpow_pos_of_pos hp_pos (-α)).le
  have hq1 : (p : ℝ) ^ (-α) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp_one_lt (by linarith)
  exact finite_geometric_shifted_sum_le_div_one_sub hq0 hq1 (Nat.log p K)

theorem rankinPrimeGeomRpowTailSum_le_geomMajorantSum
    (K z : ℕ) {α : ℝ} (hα0 : 0 < α) :
    rankinPrimeGeomRpowTailSum K z α ≤ rankinPrimeGeomGeomMajorantSum z α := by
  classical
  unfold rankinPrimeGeomRpowTailSum rankinPrimeGeomGeomMajorantSum
  apply Finset.sum_le_sum
  intro p hpz
  exact rankinPrimeGeomLocalRpowTail_le_geomMajorant hα0
    (Nat.prime_of_mem_primesBelow hpz)

theorem rankinPrimeGeomLocalGeomMajorant_le_scaled_rpow
    {p : ℕ} {α : ℝ} (hα0 : 0 < α) (hp : Nat.Prime p) :
    rankinPrimeGeomLocalGeomMajorant α p ≤
      (1 / (1 - (2 : ℝ) ^ (-α))) * (p : ℝ) ^ (-α) := by
  unfold rankinPrimeGeomLocalGeomMajorant
  have htwo_pos : 0 < (2 : ℝ) := by norm_num
  have hp_pos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have htwo_le_p : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hq0 : 0 ≤ (p : ℝ) ^ (-α) := (Real.rpow_pos_of_pos hp_pos (-α)).le
  have hq2_lt_one : (2 : ℝ) ^ (-α) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (by linarith)
  have hden2_pos : 0 < 1 - (2 : ℝ) ^ (-α) := sub_pos.mpr hq2_lt_one
  have hq_le_q2 : (p : ℝ) ^ (-α) ≤ (2 : ℝ) ^ (-α) :=
    Real.rpow_le_rpow_of_nonpos htwo_pos htwo_le_p (by linarith)
  have hden_le : 1 - (2 : ℝ) ^ (-α) ≤ 1 - (p : ℝ) ^ (-α) := by
    linarith
  have hinv_le :
      1 / (1 - (p : ℝ) ^ (-α)) ≤ 1 / (1 - (2 : ℝ) ^ (-α)) :=
    one_div_le_one_div_of_le hden2_pos hden_le
  calc
    (p : ℝ) ^ (-α) / (1 - (p : ℝ) ^ (-α))
        = (p : ℝ) ^ (-α) * (1 / (1 - (p : ℝ) ^ (-α))) := by ring_nf
    _ ≤ (p : ℝ) ^ (-α) * (1 / (1 - (2 : ℝ) ^ (-α))) :=
        mul_le_mul_of_nonneg_left hinv_le hq0
    _ = (1 / (1 - (2 : ℝ) ^ (-α))) * (p : ℝ) ^ (-α) := by ring

theorem rankinPrimeGeomMajorantSum_le_scaled_primeRpowSum
    (z : ℕ) {α : ℝ} (hα0 : 0 < α) :
    rankinPrimeGeomGeomMajorantSum z α ≤
      (1 / (1 - (2 : ℝ) ^ (-α))) * rankinPrimeRpowSum z α := by
  classical
  unfold rankinPrimeGeomGeomMajorantSum rankinPrimeRpowSum
  calc
    (∑ p ∈ z.primesBelow, rankinPrimeGeomLocalGeomMajorant α p)
        ≤ ∑ p ∈ z.primesBelow,
            (1 / (1 - (2 : ℝ) ^ (-α))) * (p : ℝ) ^ (-α) := by
          apply Finset.sum_le_sum
          intro p hpz
          exact rankinPrimeGeomLocalGeomMajorant_le_scaled_rpow hα0
            (Nat.prime_of_mem_primesBelow hpz)
    _ = (1 / (1 - (2 : ℝ) ^ (-α))) *
          ∑ p ∈ z.primesBelow, (p : ℝ) ^ (-α) := by
          rw [Finset.mul_sum]

theorem rankinPrimeRpowSum_le_natRpowSum (z : ℕ) (α : ℝ) :
    rankinPrimeRpowSum z α ≤ rankinNatRpowSum z α := by
  classical
  unfold rankinPrimeRpowSum rankinNatRpowSum
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hpz
    rw [Finset.mem_Icc]
    exact ⟨(Nat.prime_of_mem_primesBelow hpz).one_le,
      Nat.le_of_lt (Nat.lt_of_mem_primesBelow hpz)⟩
  · intro p _hpz hpnot
    exact Real.rpow_nonneg (Nat.cast_nonneg p) (-α)

theorem rankinPrimeGeomProduct_eq_exponentBox_sum (K z : ℕ) (α : ℝ) :
    rankinPrimeGeomProduct K z α =
      ∑ v ∈ rankinPrimeExponentBox K z, rankinPrimeExponentBoxWeight z α v := by
  classical
  unfold rankinPrimeGeomProduct rankinPrimeExponentBox rankinPrimeExponentBoxWeight
  rw [Finset.prod_sum]

theorem rankinPrimeExponentBoxWeight_nonneg (z : ℕ) (α : ℝ)
    (v : ∀ p : ℕ, p ∈ z.primesBelow → ℕ) :
    0 ≤ rankinPrimeExponentBoxWeight z α v := by
  classical
  unfold rankinPrimeExponentBoxWeight
  exact Finset.prod_nonneg (by
    intro x _hx
    exact Real.rpow_nonneg (Nat.cast_nonneg (x.1 ^ v x.1 x.2)) (-α))

theorem smoothNumbersUpTo_factorization_le_log
    {K z n p : ℕ} (hn : n ∈ Nat.smoothNumbersUpTo K z) (hp : Nat.Prime p) :
    n.factorization p ≤ Nat.log p K := by
  have hnpack := Nat.mem_smoothNumbersUpTo.mp hn
  have hn_ne_zero : n ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hnpack.2
  by_cases hfac : n.factorization p = 0
  · rw [hfac]
    exact Nat.zero_le _
  · have hpow_dvd : p ^ n.factorization p ∣ n :=
      (hp.pow_dvd_iff_le_factorization hn_ne_zero).mpr le_rfl
    have hpow_le_n : p ^ n.factorization p ≤ n :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hn_ne_zero) hpow_dvd
    exact Nat.le_log_of_pow_le hp.one_lt (le_trans hpow_le_n hnpack.1)

theorem smoothNumbersUpTo_factorization_eq_zero
    {K z n p : ℕ} (hn : n ∈ Nat.smoothNumbersUpTo K z)
    (hp : Nat.Prime p) (hpnot : p ∉ z.primesBelow) :
    n.factorization p = 0 := by
  have hsmooth := (Nat.mem_smoothNumbersUpTo.mp hn).2
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hpdvd
  have hp_lt_z : p < z := (Nat.mem_smoothNumbers'.mp hsmooth) p hp hpdvd
  exact hpnot (Nat.mem_primesBelow.mpr ⟨hp_lt_z, hp⟩)

/-- The exponents `v_p(n)` of `n` at the primes `p < z`. -/
noncomputable def smoothExponentVector (z n : ℕ) :
    ∀ p : ℕ, p ∈ z.primesBelow → ℕ :=
  fun p _hp => n.factorization p

theorem smoothExponentVector_mem_rankinPrimeExponentBox
    {K z n : ℕ} (hn : n ∈ Nat.smoothNumbersUpTo K z) :
    smoothExponentVector z n ∈ rankinPrimeExponentBox K z := by
  classical
  rw [rankinPrimeExponentBox, Finset.mem_pi]
  intro p hpz
  rw [Finset.mem_range]
  exact Nat.lt_succ_of_le
    (smoothNumbersUpTo_factorization_le_log hn (Nat.prime_of_mem_primesBelow hpz))

theorem smoothExponentVector_injective_on_smoothNumbersUpTo
    {K z n m : ℕ}
    (hn : n ∈ Nat.smoothNumbersUpTo K z)
    (hm : m ∈ Nat.smoothNumbersUpTo K z)
    (hvec : smoothExponentVector z n = smoothExponentVector z m) :
    n = m := by
  have hnpack := Nat.mem_smoothNumbersUpTo.mp hn
  have hmpack := Nat.mem_smoothNumbersUpTo.mp hm
  have hn_ne_zero : n ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hnpack.2
  have hm_ne_zero : m ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hmpack.2
  refine Nat.eq_of_factorization_eq hn_ne_zero hm_ne_zero ?_
  intro p
  by_cases hp : Nat.Prime p
  · by_cases hpz : p ∈ z.primesBelow
    · have hcongr := congrFun (congrFun hvec p) hpz
      simpa [smoothExponentVector] using hcongr
    · rw [smoothNumbersUpTo_factorization_eq_zero hn hp hpz,
        smoothNumbersUpTo_factorization_eq_zero hm hp hpz]
  · rw [Nat.factorization_eq_zero_of_not_prime n hp,
      Nat.factorization_eq_zero_of_not_prime m hp]

theorem smoothNumbersUpTo_support_subset_primesBelow
    {K z n : ℕ} (hn : n ∈ Nat.smoothNumbersUpTo K z) :
    n.factorization.support ⊆ z.primesBelow := by
  intro p hp
  have hsmooth := (Nat.mem_smoothNumbersUpTo.mp hn).2
  have hpPrime : Nat.Prime p := by
    exact Nat.prime_of_mem_primeFactors (by simpa [Nat.support_factorization] using hp)
  have hpdvd : p ∣ n := by
    exact Nat.dvd_of_mem_primeFactors (by simpa [Nat.support_factorization] using hp)
  exact Nat.mem_primesBelow.mpr
    ⟨(Nat.mem_smoothNumbers'.mp hsmooth) p hpPrime hpdvd, hpPrime⟩

theorem smoothNumbersUpTo_prod_primesBelow_factorization_eq_self
    {K z n : ℕ} (hn : n ∈ Nat.smoothNumbersUpTo K z) :
    (∏ p ∈ z.primesBelow, p ^ n.factorization p) = n := by
  have hnpack := Nat.mem_smoothNumbersUpTo.mp hn
  have hn_ne_zero : n ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hnpack.2
  have hsupport := smoothNumbersUpTo_support_subset_primesBelow hn
  calc
    (∏ p ∈ z.primesBelow, p ^ n.factorization p)
        = n.factorization.prod (fun p e => p ^ e) := by
          exact (Finsupp.prod_of_support_subset n.factorization hsupport
            (fun p e => p ^ e)
            (by
              intro p _hp
              exact pow_zero p)).symm
    _ = n := Nat.prod_factorization_pow_eq_self hn_ne_zero

theorem smoothNumbersUpTo_real_prod_eq_self
    {K z n : ℕ} (hn : n ∈ Nat.smoothNumbersUpTo K z) :
    (∏ p ∈ z.primesBelow, ((p ^ n.factorization p : ℕ) : ℝ)) = (n : ℝ) := by
  exact_mod_cast smoothNumbersUpTo_prod_primesBelow_factorization_eq_self hn

theorem rankinPrimeExponentBoxWeight_smoothExponentVector
    {K z n : ℕ} (hn : n ∈ Nat.smoothNumbersUpTo K z) (α : ℝ) :
    rankinPrimeExponentBoxWeight z α (smoothExponentVector z n) = (n : ℝ) ^ (-α) := by
  classical
  unfold rankinPrimeExponentBoxWeight smoothExponentVector
  rw [Real.finsetProd_rpow]
  · have hprod :
        (∏ x ∈ z.primesBelow.attach,
          ((x.1 ^ n.factorization x.1 : ℕ) : ℝ)) = (n : ℝ) := by
        calc
          (∏ x ∈ z.primesBelow.attach,
              ((x.1 ^ n.factorization x.1 : ℕ) : ℝ))
              = ∏ p ∈ z.primesBelow, ((p ^ n.factorization p : ℕ) : ℝ) := by
                simpa using
                  (Finset.prod_attach z.primesBelow
                    (fun p : ℕ => ((p ^ n.factorization p : ℕ) : ℝ)))
          _ = (n : ℝ) := smoothNumbersUpTo_real_prod_eq_self hn
    rw [hprod]
  · intro x _hx
    exact Nat.cast_nonneg (x.1 ^ n.factorization x.1)

/-- Rankin's bound: distinct `z`-smooth `n ≤ K` have distinct exponent vectors in the box,
so `∑ n^{-α}` over them is at most the Euler product. -/
theorem rankinWeightedSmoothSum_le_rankinPrimeGeomProduct
    (K z : ℕ) (α : ℝ) :
    rankinWeightedSmoothSum K z α ≤ rankinPrimeGeomProduct K z α := by
  classical
  let S : Finset ℕ := Nat.smoothNumbersUpTo K z
  let f : ℕ → (∀ p : ℕ, p ∈ z.primesBelow → ℕ) := fun n => smoothExponentVector z n
  let w : (∀ p : ℕ, p ∈ z.primesBelow → ℕ) → ℝ :=
    fun v => rankinPrimeExponentBoxWeight z α v
  have hinj : Set.InjOn f ↑S := by
    intro n hn m hm hnm
    exact smoothExponentVector_injective_on_smoothNumbersUpTo hn hm hnm
  have himage_subset : S.image f ⊆ rankinPrimeExponentBox K z := by
    rw [Finset.image_subset_iff]
    intro n hn
    exact smoothExponentVector_mem_rankinPrimeExponentBox hn
  have hsum_image :
      (∑ n ∈ S, w (f n)) = ∑ v ∈ S.image f, w v := by
    exact (Finset.sum_image hinj).symm
  calc
    rankinWeightedSmoothSum K z α
        = ∑ n ∈ S, (n : ℝ) ^ (-α) := by rfl
    _ = ∑ n ∈ S, w (f n) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact (rankinPrimeExponentBoxWeight_smoothExponentVector hn α).symm
    _ = ∑ v ∈ S.image f, w v := hsum_image
    _ ≤ ∑ v ∈ rankinPrimeExponentBox K z, w v :=
        Finset.sum_le_sum_of_subset_of_nonneg himage_subset (by
          intro v _hvBox _hvImage
          exact rankinPrimeExponentBoxWeight_nonneg z α v)
    _ = rankinPrimeGeomProduct K z α := by
        rw [rankinPrimeGeomProduct_eq_exponentBox_sum]

/-- For `0 < α < 1` and `Y ≥ 1`, comparison with `∫ x^{-α} dx` gives
`∑_{1≤m≤Y} m^{-α} ≤ (1 + 1/(1-α)) Y^{1-α}`. -/
theorem divisor_rpow_neg_sum_Icc_le
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (Y : ℕ) (hY : 1 ≤ Y) :
    (∑ m ∈ Finset.Icc (1 : ℕ) Y, (m : ℝ) ^ (-α))
      ≤ (1 + 1 / (1 - α)) * (Y : ℝ) ^ (1 - α) := by
  classical
  let f : ℝ → ℝ := fun x => x ^ (-α)
  have hYreal : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hYpos : 0 < (Y : ℝ) := lt_of_lt_of_le zero_lt_one hYreal
  have hone_sub_pos : 0 < 1 - α := by linarith
  have hanti : AntitoneOn f (Set.Icc (1 : ℝ) (Y : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hx.1) hxy (by linarith)
  have htail :
      (∑ i ∈ Finset.Ico (1 : ℕ) Y, f ((i + 1 : ℕ) : ℝ))
        ≤ ∫ x in (1 : ℝ)..(Y : ℝ), f x :=
    by
      simpa [Nat.cast_one] using
        (AntitoneOn.sum_le_integral_Ico hY
          (show AntitoneOn f (Set.Icc (((1 : ℕ) : ℝ)) (Y : ℝ)) from by
            simpa using hanti))
  have htail_eq :
      (∑ m ∈ Finset.Icc (2 : ℕ) Y, (m : ℝ) ^ (-α))
        = ∑ i ∈ Finset.Ico (1 : ℕ) Y, f ((i + 1 : ℕ) : ℝ) := by
    let e : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩
    have hmap : (Finset.Ico (1 : ℕ) Y).map e = Finset.Icc (2 : ℕ) Y := by
      ext m
      simp [e, Nat.succ_eq_add_one, Finset.mem_Ico, Finset.mem_Icc]
      constructor
      · intro h
        omega
      · intro h
        refine ⟨m - 1, ?_, by omega⟩
        omega
    rw [← hmap]
    simp [e, f]
  have hsplit :
      (∑ m ∈ Finset.Icc (1 : ℕ) Y, (m : ℝ) ^ (-α))
        = 1 + ∑ m ∈ Finset.Icc (2 : ℕ) Y, (m : ℝ) ^ (-α) := by
    have hset : insert (1 : ℕ) (Finset.Icc (2 : ℕ) Y) = Finset.Icc (1 : ℕ) Y := by
      ext m
      simp [Finset.mem_Icc]
      omega
    have hone_not_mem : (1 : ℕ) ∉ Finset.Icc (2 : ℕ) Y := by
      simp [Finset.mem_Icc]
    calc
      (∑ m ∈ Finset.Icc (1 : ℕ) Y, (m : ℝ) ^ (-α))
          = ∑ m ∈ insert (1 : ℕ) (Finset.Icc (2 : ℕ) Y), (m : ℝ) ^ (-α) := by
              rw [hset]
      _ = (((1 : ℕ) : ℝ) ^ (-α)) +
            ∑ m ∈ Finset.Icc (2 : ℕ) Y, (m : ℝ) ^ (-α) := by
              rw [Finset.sum_insert hone_not_mem]
      _ = 1 + ∑ m ∈ Finset.Icc (2 : ℕ) Y, (m : ℝ) ^ (-α) := by
              simp
  have hintegral :
      (∫ x in (1 : ℝ)..(Y : ℝ), f x)
        = ((Y : ℝ) ^ (1 - α) - 1) / (1 - α) := by
    unfold f
    have hpow := integral_rpow
      (a := (1 : ℝ)) (b := (Y : ℝ)) (r := -α)
      (Or.inl (by linarith : -1 < -α))
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hpow
  have htail_bound :
      (∑ m ∈ Finset.Icc (2 : ℕ) Y, (m : ℝ) ^ (-α))
        ≤ ((Y : ℝ) ^ (1 - α) - 1) / (1 - α) := by
    rw [htail_eq, ← hintegral]
    exact htail
  have hYpow_ge_one : (1 : ℝ) ≤ (Y : ℝ) ^ (1 - α) :=
    Real.one_le_rpow hYreal hone_sub_pos.le
  calc
    (∑ m ∈ Finset.Icc (1 : ℕ) Y, (m : ℝ) ^ (-α))
        = 1 + ∑ m ∈ Finset.Icc (2 : ℕ) Y, (m : ℝ) ^ (-α) := hsplit
    _ ≤ 1 + ((Y : ℝ) ^ (1 - α) - 1) / (1 - α) :=
        add_le_add_right htail_bound 1
    _ ≤ (Y : ℝ) ^ (1 - α) + ((Y : ℝ) ^ (1 - α)) / (1 - α) := by
        have hnum_le :
            (Y : ℝ) ^ (1 - α) - 1 ≤ (Y : ℝ) ^ (1 - α) := by linarith
        have hfrac_le :
            ((Y : ℝ) ^ (1 - α) - 1) / (1 - α) ≤
              ((Y : ℝ) ^ (1 - α)) / (1 - α) :=
          div_le_div_of_nonneg_right hnum_le hone_sub_pos.le
        exact add_le_add hYpow_ge_one hfrac_le
    _ = (1 + 1 / (1 - α)) * (Y : ℝ) ^ (1 - α) := by
        field_simp [hone_sub_pos.ne']

theorem const_mul_sqrt_le_quad_linear {C ε L : ℝ} (hε : 0 < ε) (hL : 0 ≤ L) :
    C * L ^ ((1 : ℝ) / 2) ≤ C ^ 2 / (4 * ε) + ε * L := by
  let y : ℝ := L ^ ((1 : ℝ) / 2)
  have hy2 : y ^ 2 = L := by
    dsimp [y]
    rw [← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt hL
  have hbasic : C * y ≤ C ^ 2 / (4 * ε) + ε * (y ^ 2) := by
    have hden_pos : 0 < 4 * ε := by positivity
    rw [← (mul_le_mul_iff_right₀ hden_pos)]
    field_simp [hε.ne']
    ring_nf
    have hsq : 0 ≤ (C - 2 * ε * y) ^ 2 := sq_nonneg _
    ring_nf at hsq
    nlinarith
  rw [hy2] at hbasic
  exact hbasic

end Rankin

/-! ## The Euler product and absorption into the saving

For fixed `θ < 1` and `c₁ > 0`, both `N^θ` and `log N · N exp(-c₁ (log N)^{3/4})` are
`≪ N exp(-c (log N)^{3/4})` for some `c > 0`. -/

section Absorption

open scoped BigOperators
open Real

/-- The Euler product `∏_{p ≤ z} (1 - 1/p)^{-1}` of Lemma 5.5. -/
noncomputable def eulerProductFactor (z : ℝ) : ℝ := by
  classical
  exact
    ∏ p ∈ (Finset.Icc (2 : ℕ) ⌊z⌋₊).filter Nat.Prime,
      ((1 : ℝ) - (1 : ℝ) / (p : ℝ))⁻¹

theorem mul_saving_eq_exp (c : ℝ) {N : ℕ} (hN : 0 < N) :
    (N : ℝ) * saving c N
      = Real.exp (Real.log N + (-c) * (Real.log N) ^ ((3 : ℝ) / 4)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  unfold saving
  rw [← Real.exp_log hNpos, ← Real.exp_add, Real.log_exp]

/-- If `0 < θ < 1` and `Cs > 0`, then `Cs · N^θ ≤ C · N · saving c N` for all `N ≥ 3`,
with `c = (1-θ)/2` and `C = max Cs 1`. With `θ = 7/8` this absorbs the error term
`N^{3/4+o(1)}` of Lemma 5.5. The proof reduces to `(log N)^{1/4} ≥ 1/2`. -/
theorem poly_absorb {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {Cs : ℝ} (hCs : 0 < Cs) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ N : ℕ, 3 ≤ N → Cs * (N : ℝ) ^ θ ≤ C * ((N : ℝ) * saving c N) := by
  refine ⟨(1 - θ) / 2, by linarith, max Cs 1, lt_of_lt_of_le hCs (le_max_left _ _), ?_⟩
  intro N hN
  set c : ℝ := (1 - θ) / 2 with hc
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set L : ℝ := Real.log N with hLdef
  have hL0 : 0 < L := log_pos_of_three_le hN
  have hNrpow : (N : ℝ) ^ θ = Real.exp (θ * L) := by
    rw [Real.rpow_def_of_pos hNpos, ← hLdef]; ring_nf
  have hsave : (N : ℝ) * saving c N = Real.exp (L + (-c) * L ^ ((3 : ℝ) / 4)) := by
    have := mul_saving_eq_exp c (by omega : 0 < N); rw [← hLdef] at this; exact this
  rw [hNrpow, hsave]
  have hkey : θ * L ≤ L + (-c) * L ^ ((3 : ℝ) / 4) := by
    -- equivalently `c L^{3/4} ≤ (1-θ) L`
    have hL34pos : 0 < L ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL0 _
    -- `L^{1/4} ≥ 1/2` since `L ≥ 2/3 > 1/16`
    have hLlower : (1 : ℝ) / 16 < L := by
      have := log_ge_of_three_le hN; rw [← hLdef] at this; linarith
    have hquart : (1 : ℝ) / 2 ≤ L ^ ((1 : ℝ) / 4) := by
      have h16 : ((1 : ℝ) / 16) ^ ((1 : ℝ) / 4) ≤ L ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (by norm_num) hLlower.le (by norm_num)
      have : ((1 : ℝ) / 16) ^ ((1 : ℝ) / 4) = (1 : ℝ) / 2 := by
        rw [show (1 : ℝ) / 16 = (1 / 2) ^ (4 : ℕ) by norm_num,
          ← Real.rpow_natCast (1 / 2 : ℝ) 4, ← Real.rpow_mul (by norm_num)]
        norm_num
      linarith [this ▸ h16]
    -- `(1-θ) L = (1-θ) L^{1/4} · L^{3/4} ≥ c L^{3/4}`
    have hLsplit : L = L ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_add hL0]; norm_num
    have hcle : c ≤ (1 - θ) * L ^ ((1 : ℝ) / 4) := by
      have : c = (1 - θ) * (1 / 2) := by rw [hc]; ring
      rw [this]
      apply mul_le_mul_of_nonneg_left hquart (by linarith)
    have : c * L ^ ((3 : ℝ) / 4) ≤ (1 - θ) * L := by
      calc c * L ^ ((3 : ℝ) / 4)
          ≤ ((1 - θ) * L ^ ((1 : ℝ) / 4)) * L ^ ((3 : ℝ) / 4) :=
            mul_le_mul_of_nonneg_right hcle hL34pos.le
        _ = (1 - θ) * (L ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4)) := by ring
        _ = (1 - θ) * L := by rw [← hLsplit]
    linarith
  have hexpmono : Real.exp (θ * L) ≤ Real.exp (L + (-c) * L ^ ((3 : ℝ) / 4)) :=
    Real.exp_le_exp.mpr hkey
  have hCsle : Cs ≤ max Cs 1 := le_max_left _ _
  calc Cs * Real.exp (θ * L)
      ≤ Cs * Real.exp (L + (-c) * L ^ ((3 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left hexpmono hCs.le
    _ ≤ max Cs 1 * Real.exp (L + (-c) * L ^ ((3 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_right hCsle (Real.exp_pos _).le

/-- For `c₁, Ce, C₁ > 0`, `Ce · log N · (C₁ · N · saving c₁ N) ≤ C · N · saving c N` for all
`N ≥ 3`, with `c = c₁/2` and `C = Ce C₁ (1 + 16/c₁²)`. This absorbs the factor
`log(2y) ≪ log N` of Lemma 5.5. With `t = (log N)^{3/4}`, the proof uses `log N ≤ 1 + t²`
and `t² ≤ (16/c₁²) exp(c t)`. -/
theorem log_absorb {c₁ : ℝ} (hc₁ : 0 < c₁) {Ce C₁ : ℝ} (hCe : 0 < Ce) (hC₁ : 0 < C₁) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ N : ℕ, 3 ≤ N →
        Ce * Real.log N * (C₁ * ((N : ℝ) * saving c₁ N)) ≤ C * ((N : ℝ) * saving c N) := by
  set c : ℝ := c₁ / 2 with hc
  refine ⟨c, by positivity, Ce * C₁ * (1 + 16 / c₁ ^ 2), by positivity, ?_⟩
  intro N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set L : ℝ := Real.log N with hLdef
  have hL0 : 0 < L := log_pos_of_three_le hN
  set t : ℝ := L ^ ((3 : ℝ) / 4) with htdef
  have ht0 : 0 < t := Real.rpow_pos_of_pos hL0 _
  have hsave₁ : (N : ℝ) * saving c₁ N = (N : ℝ) * Real.exp (-c₁ * t) := by
    unfold saving; rw [← hLdef, ← htdef]
  have hsaveC : (N : ℝ) * saving c N = (N : ℝ) * Real.exp (-c * t) := by
    unfold saving; rw [← hLdef, ← htdef]
  rw [hsave₁, hsaveC]
  -- it suffices that `L ≤ (1 + 16/c₁²) exp(c t)`
  have hLbound : L ≤ 1 + t ^ 2 := by
    have : t ^ ((4 : ℝ) / 3) = L := by
      rw [htdef]; exact rpow_three_quarters_four_thirds hL0.le
    calc L = t ^ ((4 : ℝ) / 3) := this.symm
      _ ≤ 1 + t ^ 2 := rpow_four_thirds_le ht0.le
  have hquad : t ^ 2 ≤ (16 / c₁ ^ 2) * Real.exp (c * t) := by
    have hct : 0 ≤ c * t := by positivity
    have h := sq_le_four_mul_exp hct  -- `(c t)² ≤ 4 exp(c t)`
    have hcsq : (c * t) ^ 2 = c ^ 2 * t ^ 2 := by ring
    have hcpos : 0 < c ^ 2 := by positivity
    have hdiv : t ^ 2 ≤ (4 / c ^ 2) * Real.exp (c * t) := by
      rw [hcsq] at h
      rw [div_mul_eq_mul_div, le_div_iff₀ hcpos]
      nlinarith [h]
    have hcc : c ^ 2 = c₁ ^ 2 / 4 := by rw [hc]; ring
    have e : (4 : ℝ) / c ^ 2 = 16 / c₁ ^ 2 := by
      rw [hcc]; field_simp; ring
    rw [e] at hdiv; exact hdiv
  have hone : (1 : ℝ) ≤ Real.exp (c * t) := by
    have : (0 : ℝ) ≤ c * t := by positivity
    simpa using Real.one_le_exp this
  have hLexp : L ≤ (1 + 16 / c₁ ^ 2) * Real.exp (c * t) := by
    have : (1 : ℝ) + t ^ 2 ≤ (1 + 16 / c₁ ^ 2) * Real.exp (c * t) := by
      have h16 : (0 : ℝ) ≤ 16 / c₁ ^ 2 := by positivity
      nlinarith [hone, hquad, Real.exp_pos (c * t)]
    linarith
  have hexp_id : Real.exp (-c₁ * t) * Real.exp (c * t) = Real.exp (-c * t) := by
    rw [← Real.exp_add]; congr 1; rw [hc]; ring
  have hExpPos : 0 < Real.exp (-c₁ * t) := Real.exp_pos _
  have key : Ce * L * (C₁ * ((N : ℝ) * Real.exp (-c₁ * t)))
      ≤ Ce * C₁ * (1 + 16 / c₁ ^ 2) * ((N : ℝ) * Real.exp (-c * t)) := by
    have hmul : Ce * L * (C₁ * ((N : ℝ) * Real.exp (-c₁ * t)))
        ≤ Ce * ((1 + 16 / c₁ ^ 2) * Real.exp (c * t))
            * (C₁ * ((N : ℝ) * Real.exp (-c₁ * t))) := by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left hLexp hCe.le
      · positivity
    refine hmul.trans ?_
    have : Ce * ((1 + 16 / c₁ ^ 2) * Real.exp (c * t))
            * (C₁ * ((N : ℝ) * Real.exp (-c₁ * t)))
      = Ce * C₁ * (1 + 16 / c₁ ^ 2)
            * ((N : ℝ) * (Real.exp (-c₁ * t) * Real.exp (c * t))) := by ring
    rw [this, hexp_id]
  exact key

end Absorption

/-! ## Smooth and rough parts

For `n ≠ 0` write `n = s m`, where `s = smoothPart z n` collects the prime powers
`p^{v_p(n)}` with `p ≤ z` and `m = roughPart z n` those with `p > z`. This is the
factorization `n = su` in the proof of Lemma 5.5. -/

section SmoothRough

open Nat Finset
open Classical

/-- The `z`-smooth part `∏_{p ≤ z} p^{v_p(n)}` of `n`. -/
noncomputable def smoothPart (z n : ℕ) : ℕ :=
  ∏ p ∈ n.factorization.support.filter (· ≤ z), p ^ n.factorization p

/-- The `z`-rough part `∏_{p > z} p^{v_p(n)}` of `n`. -/
noncomputable def roughPart (z n : ℕ) : ℕ :=
  ∏ p ∈ n.factorization.support.filter (fun p => ¬ p ≤ z), p ^ n.factorization p

theorem prod_support_eq {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ n.factorization.support, p ^ n.factorization p = n := by
  have := Nat.prod_factorization_pow_eq_self hn
  rwa [Finsupp.prod] at this

theorem smooth_mul_rough (z : ℕ) {n : ℕ} (hn : n ≠ 0) :
    smoothPart z n * roughPart z n = n := by
  unfold smoothPart roughPart
  rw [Finset.prod_filter_mul_prod_filter_not n.factorization.support (· ≤ z)]
  exact prod_support_eq hn

theorem rough_pos {z n : ℕ} : 0 < roughPart z n := by
  unfold roughPart
  apply Finset.prod_pos
  intro p hp
  rw [Finset.mem_filter, Nat.support_factorization] at hp
  exact pow_pos (Nat.prime_of_mem_primeFactors hp.1).pos _

theorem smooth_pos {z n : ℕ} : 0 < smoothPart z n := by
  unfold smoothPart
  apply Finset.prod_pos
  intro p hp
  rw [Finset.mem_filter, Nat.support_factorization] at hp
  exact pow_pos (Nat.prime_of_mem_primeFactors hp.1).pos _

theorem smooth_le {z n : ℕ} (hn : 0 < n) : smoothPart z n ≤ n := by
  have h := smooth_mul_rough z hn.ne'
  calc smoothPart z n ≤ smoothPart z n * roughPart z n :=
        Nat.le_mul_of_pos_right _ rough_pos
    _ = n := h

theorem rough_dvd (z n : ℕ) : roughPart z n ∣ n := by
  by_cases hn : n = 0
  · simp [hn]
  · exact Dvd.intro_left _ (smooth_mul_rough z (by simpa using hn))

/-- Every prime factor of `m` is at most `z`. -/
def IsSmooth (z m : ℕ) : Prop := ∀ p, Nat.Prime p → p ∣ m → p ≤ z

/-- `(m, P(z)) = 1`: no prime `p ≤ z` divides `m`. -/
def IsRough (z m : ℕ) : Prop := ∀ p, Nat.Prime p → p ≤ z → ¬ p ∣ m

theorem prime_le_coprime_rough {z n p : ℕ} (hp : Nat.Prime p) (hpz : p ≤ z) :
    Nat.Coprime p (roughPart z n) := by
  unfold roughPart
  apply Nat.Coprime.prod_right
  intro q hq
  rw [Finset.mem_filter, Nat.support_factorization] at hq
  have hqprime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq.1
  have hne : p ≠ q := by rintro rfl; exact hq.2 hpz
  exact (Nat.coprime_primes hp hqprime).mpr hne |>.pow_right _

theorem roughPart_isRough (z n : ℕ) : IsRough z (roughPart z n) := by
  intro p hp hpz hdvd
  have hcop := prime_le_coprime_rough (z := z) (n := n) hp hpz
  have : p ∣ Nat.gcd p (roughPart z n) := Nat.dvd_gcd dvd_rfl hdvd
  rw [Nat.Coprime] at hcop; rw [hcop] at this
  exact Nat.Prime.one_lt hp |>.ne' (Nat.dvd_one.mp this)

theorem smoothPart_isSmooth (z n : ℕ) : IsSmooth z (smoothPart z n) := by
  intro p hp hdvd
  -- `p` divides some `q^{v_q(n)}` with `q ≤ z`, so `p = q`
  unfold smoothPart at hdvd
  obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hp).exists_mem_finset_dvd hdvd
  rw [Finset.mem_filter, Nat.support_factorization] at hq
  have hqprime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq.1
  have hpdvdq : p ∣ q := hp.dvd_of_dvd_pow hpq
  have : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp hpdvdq
  rw [this]; exact hq.2

/-- `Nat.smoothNumbers` bounds the prime factors strictly, so `IsSmooth z` is membership
in `Nat.smoothNumbers (z + 1)`. -/
theorem isSmooth_iff_mem_smoothNumbers_succ (z s : ℕ) :
    IsSmooth z s ↔ s ∈ Nat.smoothNumbers (z + 1) := by
  rw [Nat.mem_smoothNumbers']
  constructor
  · intro hs p hp hpd
    exact Nat.lt_succ_iff.mpr (hs p hp hpd)
  · intro hs p hp hpd
    exact Nat.lt_succ_iff.mp (hs p hp hpd)

end SmoothRough

end ErdosStraus

/-! ## Proof of Lemma 5.5 -/

namespace ErdosStraus.Counting

open Classical Filter

/-- `E` contains every divisor of each of its positive elements. -/
def DivisorClosed (E : Set ℕ) : Prop :=
  ∀ ⦃n d : ℕ⦄, n ∈ E → 0 < n → d ∣ n → d ∈ E

/-- `P(y) = ∏_{p ≤ y} p`. -/
def primorial (y : ℕ) : ℕ := ∏ p ∈ (y + 1).primesBelow, p

theorem isRough_iff_coprime_primorial (y n : ℕ) :
    IsRough y n ↔ Nat.Coprime n (primorial y) := by
  unfold primorial
  rw [Nat.coprime_prod_right_iff]
  constructor
  · intro h p hp
    obtain ⟨hpy, hpprime⟩ := Nat.mem_primesBelow.mp hp
    exact (hpprime.coprime_iff_not_dvd.mpr (h p hpprime (by omega))).symm
  · intro h p hp hpy
    exact hp.coprime_iff_not_dvd.mp
      (h p (Nat.mem_primesBelow.mpr ⟨by omega, hp⟩)).symm

/-- `#(E ∩ [1, N])`. -/
noncomputable def count (E : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (· ∈ E)).card

/-- `#{1 ≤ n ≤ N : n ∈ E, (n, P(y)) = 1}`. -/
noncomputable def reducedCount (E : Set ℕ) (y N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n => n ∈ E ∧ IsRough y n)).card

theorem reducedCount_eq_coprime_count (E : Set ℕ) (y N : ℕ) :
    reducedCount E y N =
      ((Finset.Icc 1 N).filter (fun n => n ∈ E ∧ Nat.Coprime n (primorial y))).card := by
  simp only [reducedCount, isRough_iff_coprime_primorial]

theorem reducedCount_le (E : Set ℕ) (y N : ℕ) : reducedCount E y N ≤ N :=
  (Finset.card_filter_le _ _).trans (by simp)

/-- The `n ∈ E ∩ [1, N]` with `y`-smooth part `s` map injectively to their rough parts,
which lie in `E ∩ [1, N/s]` and are coprime to `P(y)`. -/
theorem fiber_le_reducedCount (E : Set ℕ) (hE : DivisorClosed E)
    (y N s : ℕ) :
    (((Finset.Icc 1 N).filter (· ∈ E)).filter (fun n => smoothPart y n = s)).card ≤
      reducedCount E y (N / s) := by
  classical
  unfold reducedCount
  apply Finset.card_le_card_of_injOn (fun n => roughPart y n)
  · intro n hn
    obtain ⟨hnE, hfeq⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnrange, hnE⟩ := Finset.mem_filter.mp hnE
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hnrange
    have hnpos : 0 < n := by omega
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨rough_pos, ?_⟩,
      hE hnE hnpos (rough_dvd y n), roughPart_isRough y n⟩
    rw [Nat.le_div_iff_mul_le (by rw [← hfeq]; exact smooth_pos), ← hfeq]
    rw [Nat.mul_comm, smooth_mul_rough y hnpos.ne']
    exact hnN
  · intro a ha b hb hab
    obtain ⟨haE, hfa⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbE, hfb⟩ := Finset.mem_filter.mp hb
    have hapos : 0 < a := (Finset.mem_Icc.mp (Finset.mem_filter.mp haE).1).1
    have hbpos : 0 < b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hbE).1).1
    change roughPart y a = roughPart y b at hab
    rw [← smooth_mul_rough y hapos.ne', ← smooth_mul_rough y hbpos.ne', hfa, hfb, hab]

theorem count_le_smooth_sum (E : Set ℕ) (hE : DivisorClosed E) (y N : ℕ) :
    count E N ≤ ∑ s ∈ Nat.smoothNumbersUpTo N (y + 1), reducedCount E y (N / s) := by
  let R := (Finset.Icc 1 N).filter (· ∈ E)
  have hmem : ∀ n ∈ R, smoothPart y n ∈ Nat.smoothNumbersUpTo N (y + 1) := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    exact Nat.mem_smoothNumbersUpTo.mpr ⟨(smooth_le hn1).trans hnN,
      (isSmooth_iff_mem_smoothNumbers_succ y _).mp (smoothPart_isSmooth y n)⟩
  have hfib := Finset.card_eq_sum_card_fiberwise (f := smoothPart y) (s := R)
    (t := Nat.smoothNumbersUpTo N (y + 1)) hmem
  unfold count
  rw [hfib]
  exact Finset.sum_le_sum (fun s _ => fiber_le_reducedCount E hE y N s)

theorem weighted_smooth_sum_le_exp (N y : ℕ) (hy : 1 ≤ y) :
    rankinWeightedSmoothSum N (y + 1) (1 / 2) ≤
      Real.exp ((3 / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))) * (y + 1 : ℝ) ^ (1 / 2 : ℝ)) := by
  have hlog := log_rankinPrimeGeomProduct_eq_logSum N (y + 1) (1 / 2)
  have hsum := divisor_rpow_neg_sum_Icc_le
    (α := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (y + 1) (by omega)
  have hbound : rankinNatRpowSum (y + 1) (1 / 2) ≤
      3 * (y + 1 : ℝ) ^ (1 / 2 : ℝ) := by
    norm_num [rankinNatRpowSum] at hsum ⊢
    exact hsum
  have hden : 0 < 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hp : rankinPrimeGeomLogSum N (y + 1) (1 / 2) ≤
      (1 / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))) * rankinNatRpowSum (y + 1) (1 / 2) := by
    calc
      _ ≤ rankinPrimeGeomExcessSum N (y + 1) (1 / 2) :=
        rankinPrimeGeomLogSum_le_excessSum _ _ _
      _ = rankinPrimeGeomRpowTailSum N (y + 1) (1 / 2) := by
        rw [rankinPrimeGeomExcessSum_eq_tailSum, rankinPrimeGeomTailSum_eq_rpowTailSum]
      _ ≤ rankinPrimeGeomGeomMajorantSum (y + 1) (1 / 2) :=
        rankinPrimeGeomRpowTailSum_le_geomMajorantSum _ _ (by norm_num)
      _ ≤ (1 / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))) * rankinPrimeRpowSum (y + 1) (1 / 2) :=
        rankinPrimeGeomMajorantSum_le_scaled_primeRpowSum _ (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (rankinPrimeRpowSum_le_natRpowSum _ _) (by positivity)
  have hl : Real.log (rankinPrimeGeomProduct N (y + 1) (1 / 2)) ≤
      (3 / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))) * (y + 1 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [hlog]
    apply hp.trans
    have := mul_le_mul_of_nonneg_left hbound (le_of_lt (one_div_pos.mpr hden))
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using this
  exact (rankinWeightedSmoothSum_le_rankinPrimeGeomProduct _ _ _).trans
    ((Real.log_le_iff_le_exp (rankinPrimeGeomProduct_pos _ _ _)).mp hl)

theorem weighted_smooth_reciprocal_le_euler (N y : ℕ) :
    (∑ s ∈ Nat.smoothNumbersUpTo N (y + 1), (s : ℝ)⁻¹) ≤
      eulerProductFactor (y : ℝ) := by
  have hweight : (∑ s ∈ Nat.smoothNumbersUpTo N (y + 1), (s : ℝ)⁻¹) =
      rankinWeightedSmoothSum N (y + 1) 1 := by
    simp [rankinWeightedSmoothSum, Real.rpow_neg_one]
  rw [hweight]
  apply (rankinWeightedSmoothSum_le_rankinPrimeGeomProduct _ _ _).trans
  have hsupport : (y + 1).primesBelow = (Finset.Icc 2 y).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hp, hpprime⟩
      exact ⟨⟨hpprime.two_le, by omega⟩, hpprime⟩
    · rintro ⟨⟨_, hp⟩, hpprime⟩
      exact ⟨by omega, hpprime⟩
  unfold rankinPrimeGeomProduct eulerProductFactor
  simp only [Nat.floor_natCast]
  rw [← hsupport]
  apply Finset.prod_le_prod
  · intro p hp
    exact Finset.sum_nonneg (fun e _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · intro p hp
    have hpprime := Nat.prime_of_mem_primesBelow hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpprime.one_lt
    have hq0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
    have hq1 : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr hp1
    have htail := finite_geometric_shifted_sum_le_div_one_sub hq0 hq1 (Nat.log p N)
    have heq := rankinPrimeGeomLocalFactor_eq_tail_add_one N 1 p
    change rankinPrimeGeomLocalFactor N 1 p ≤ _
    rw [heq, rankinPrimeGeomLocalTail_eq_rpowTail hpprime]
    simp only [rankinPrimeGeomLocalRpowTail, Real.rpow_neg_one] at *
    have hden : 0 < 1 - (p : ℝ)⁻¹ := sub_pos.mpr hq1
    apply (add_le_add_left htail 1).trans
    simp only [one_div]
    have hid : (p : ℝ)⁻¹ / (1 - (p : ℝ)⁻¹) + 1 =
        (1 - (p : ℝ)⁻¹)⁻¹ := by
          rw [div_add_one hden.ne']
          simp only [add_sub_cancel, one_div]
    exact hid.le

/-- Lemma 5.5 with an explicit error term: the `n = s u` with `s ≤ √N` contribute at most
`A N e^{-F} ∏_{p ≤ y} (1 - 1/p)^{-1}`, and those with `s > √N` at most
`N^{3/4} ∑ s^{-1/2}`, which Rankin's bound controls. -/
theorem lift_finite (E : Set ℕ) (hE : DivisorClosed E) (N y : ℕ)
    (hN : 0 < N) (hy : 1 ≤ y) (A F : ℝ) (hA : 0 ≤ A)
    (hred : ∀ M : ℝ, Real.sqrt N ≤ M → M ≤ N →
      (reducedCount E y ⌊M⌋₊ : ℝ) ≤ A * M * Real.exp (-F)) :
    (count E N : ℝ) ≤ A * N * Real.exp (-F) * eulerProductFactor (y : ℝ) +
      (N : ℝ) ^ (3 / 4 : ℝ) *
        Real.exp ((3 / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))) * (y + 1 : ℝ) ^ (1 / 2 : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 := hNpos.le
  have hNsqrt : (Real.sqrt N) ^ 2 = (N : ℝ) := Real.sq_sqrt hN0
  have hpoint : ∀ s ∈ Nat.smoothNumbersUpTo N (y + 1),
      (reducedCount E y (N / s) : ℝ) ≤
        A * N * Real.exp (-F) * (s : ℝ)⁻¹ +
          (N : ℝ) ^ (3 / 4 : ℝ) * (s : ℝ) ^ (-(1 / 2 : ℝ)) := by
    intro s hs
    have hsposnat := Nat.pos_of_ne_zero
      (Nat.ne_zero_of_mem_smoothNumbers (Nat.mem_smoothNumbersUpTo.mp hs).2)
    have hspos : (0 : ℝ) < s := by exact_mod_cast hsposnat
    have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hsposnat
    by_cases hsmall : (s : ℝ) ≤ Real.sqrt N
    · have hMlo : Real.sqrt N ≤ (N : ℝ) / s := by
        rw [le_div_iff₀ hspos]
        nlinarith [mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg (N : ℝ))]
      have hMhi : (N : ℝ) / s ≤ N := (div_le_self hN0 hs1)
      have hr := hred ((N : ℝ) / s) hMlo hMhi
      have hfl : ⌊(N : ℝ) / s⌋₊ = N / s := by
        apply le_antisymm
        · rw [Nat.le_div_iff_mul_le hsposnat]
          have h1 : ((⌊(N : ℝ) / s⌋₊ * s : ℕ) : ℝ) ≤ N := by
            push_cast
            calc (⌊(N : ℝ) / s⌋₊ : ℝ) * s ≤ ((N : ℝ) / s) * s :=
                  mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) hspos.le
              _ = N := div_mul_cancel₀ _ hspos.ne'
          exact_mod_cast h1
        · exact Nat.le_floor Nat.cast_div_le
      rw [hfl] at hr
      have heq : A * ((N : ℝ) / s) * Real.exp (-F) =
          A * N * Real.exp (-F) * (s : ℝ)⁻¹ := by ring
      exact (hr.trans_eq heq).trans (le_add_of_nonneg_right (by positivity))
    · have hslarge : (N : ℝ) ^ (1 / 2 : ℝ) ≤ s := by
        simpa [Real.sqrt_eq_rpow] using (le_of_lt (lt_of_not_ge hsmall))
      have hquarter : (N : ℝ) ^ (1 / 4 : ℝ) ≤ (s : ℝ) ^ (1 / 2 : ℝ) := by
        have hp := Real.rpow_le_rpow (Real.rpow_nonneg hN0 (1 / 2 : ℝ)) hslarge
          (by norm_num : (0 : ℝ) ≤ 1 / 2)
        rw [← Real.rpow_mul hN0] at hp
        norm_num at hp ⊢
        exact hp
      have hsidentity : (s : ℝ) ^ (-(1 / 2 : ℝ)) * s = (s : ℝ) ^ (1 / 2 : ℝ) := by
        nth_rw 2 [← Real.rpow_one (s : ℝ)]
        rw [← Real.rpow_add hspos]
        norm_num
      have hNidentity : (N : ℝ) ^ (3 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) = N := by
        rw [← Real.rpow_add hNpos]
        norm_num
      have htail : (N : ℝ) / s ≤
          (N : ℝ) ^ (3 / 4 : ℝ) * (s : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [div_le_iff₀ hspos, mul_assoc, hsidentity]
        exact hNidentity.symm.le.trans
          (mul_le_mul_of_nonneg_left hquarter (by positivity))
      have hcr : (reducedCount E y (N / s) : ℝ) ≤ (N : ℝ) / s :=
        (show (reducedCount E y (N / s) : ℝ) ≤ (N / s : ℕ) by
          exact_mod_cast reducedCount_le E y (N / s)).trans Nat.cast_div_le
      exact (hcr.trans htail).trans (le_add_of_nonneg_left (by positivity))
  have hsum := Finset.sum_le_sum hpoint
  have hcount : (count E N : ℝ) ≤
      ∑ s ∈ Nat.smoothNumbersUpTo N (y + 1), (reducedCount E y (N / s) : ℝ) := by
    exact_mod_cast count_le_smooth_sum E hE y N
  calc
    _ ≤ A * N * Real.exp (-F) *
        (∑ s ∈ Nat.smoothNumbersUpTo N (y + 1), (s : ℝ)⁻¹) +
        (N : ℝ) ^ (3 / 4 : ℝ) * rankinWeightedSmoothSum N (y + 1) (1 / 2) := by
      apply hcount.trans
      simpa [Finset.sum_add_distrib, ← Finset.mul_sum, rankinWeightedSmoothSum] using hsum
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (weighted_smooth_reciprocal_le_euler N y) (by positivity))
      (mul_le_mul_of_nonneg_left (weighted_smooth_sum_le_exp N y hy) (by positivity))

/-- For `y ≤ C log N`, the error term of `lift_finite` is at most `N^{3/4+ε}` for large `N`. -/
theorem smooth_error_uniform (C : ℝ) (hC : 0 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ y : ℕ, (y : ℝ) ≤ C * Real.log N →
      (N : ℝ) ^ (3 / 4 : ℝ) *
        Real.exp ((3 / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))) * (y + 1 : ℝ) ^ (1 / 2 : ℝ)) ≤
          (N : ℝ) ^ (3 / 4 + ε : ℝ) := by
  let D : ℝ := 3 / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))
  let H : ℝ := D * Real.sqrt (C + 1)
  have hden : 0 < 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hD : 0 < D := div_pos (by norm_num) hden
  have hH : 0 ≤ H := mul_nonneg hD.le (Real.sqrt_nonneg _)
  have hlarge : ∀ᶠ N : ℕ in atTop,
      max 1 (H ^ 2 / ε ^ 2) ≤ Real.log N := by
    have ht := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact ht.eventually (eventually_ge_atTop _)
  filter_upwards [hlarge, eventually_ge_atTop 1] with N hL hN y hy
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hL1 : 1 ≤ Real.log N := (le_max_left _ _).trans hL
  have hL0 : 0 ≤ Real.log N := zero_le_one.trans hL1
  have hyL : (y + 1 : ℝ) ≤ (C + 1) * Real.log N := by nlinarith
  have hroot : Real.sqrt (y + 1 : ℝ) ≤
      Real.sqrt (C + 1) * Real.sqrt (Real.log N) := by
    have := Real.sqrt_le_sqrt hyL
    rw [Real.sqrt_mul (by linarith : 0 ≤ C + 1)] at this
    exact this
  have hquad := const_mul_sqrt_le_quad_linear (C := H) (ε := ε / 2)
    (L := Real.log N) (by positivity) hL0
  have hsmall : H ^ 2 / (4 * (ε / 2)) ≤ (ε / 2) * Real.log N := by
    have hlower : H ^ 2 / ε ^ 2 ≤ Real.log N := (le_max_right _ _).trans hL
    have hlower' := (div_le_iff₀ (by positivity : 0 < ε ^ 2)).mp hlower
    rw [div_le_iff₀ (by positivity : 0 < 4 * (ε / 2))]
    nlinarith
  have hexponent : D * (y + 1 : ℝ) ^ (1 / 2 : ℝ) ≤ ε * Real.log N := by
    rw [← Real.sqrt_eq_rpow]
    calc
      _ ≤ H * Real.sqrt (Real.log N) := by
        simpa [H, mul_assoc] using mul_le_mul_of_nonneg_left hroot hD.le
      _ = H * (Real.log N) ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
      _ ≤ _ := hquad.trans (by linarith)
  have hexp : Real.exp (D * (y + 1 : ℝ) ^ (1 / 2 : ℝ)) ≤ (N : ℝ) ^ ε := by
    rw [Real.rpow_def_of_pos hNpos]
    exact Real.exp_le_exp.mpr (by simpa [mul_comm] using hexponent)
  calc
    _ ≤ (N : ℝ) ^ (3 / 4 : ℝ) * (N : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := (Real.rpow_add hNpos _ _).symm

/-- Lemma 5.5: if `E` is closed under divisors and
`#{u ≤ M : u ∈ E, (u, P(y)) = 1} ≤ A M e^{-F}` for `√N ≤ M ≤ N`, then
`#(E ∩ [1, N]) ≤ c A N log(2y) e^{-F} + N^{3/4+ε}` for large `N`, uniformly in
`2 ≤ y ≤ C log N`. -/
theorem lifting :
    ∃ c : ℝ, 0 < c ∧ ∀ C : ℝ, 0 ≤ C → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ y : ℝ, 2 ≤ y → y ≤ C * Real.log N →
        ∀ E : Set ℕ, DivisorClosed E → ∀ A F : ℝ, 0 < A → 0 ≤ F →
          (∀ M : ℝ, Real.sqrt N ≤ M → M ≤ N →
            (((Finset.Icc 1 ⌊M⌋₊).filter
              (fun n => n ∈ E ∧ Nat.Coprime n (primorial ⌊y⌋₊))).card : ℝ) ≤
                A * M * Real.exp (-F)) →
          (count E N : ℝ) ≤ c * A * N * Real.log (2 * y) * Real.exp (-F) +
            (N : ℝ) ^ (3 / 4 + ε : ℝ) := by
  obtain ⟨c, hc, hprod⟩ := PrimeEstimates.primeProduct_inv_upper
  refine ⟨c, hc, ?_⟩
  intro C hC ε hε
  filter_upwards [smooth_error_uniform C hC ε hε, eventually_ge_atTop 1]
    with N herror hN y hy hyC E hE A F hA _hF hred
  have hy0 : 0 ≤ y := by linarith
  have hyfloor : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hfinite := lift_finite E hE N ⌊y⌋₊ (by omega) hyfloor A F hA.le (by
    intro M hMlo hMhi
    rw [reducedCount_eq_coprime_count]
    exact hred M hMlo hMhi)
  have heuler : eulerProductFactor (⌊y⌋₊ : ℝ) = (PrimeEstimates.primeProduct y)⁻¹ := by
    simp [eulerProductFactor, PrimeEstimates.primeProduct, PrimeEstimates.primes,
      Finset.prod_inv_distrib, one_div]
  have herror' := herror ⌊y⌋₊ ((Nat.floor_le hy0).trans hyC)
  have hmain : A * N * Real.exp (-F) * eulerProductFactor (⌊y⌋₊ : ℝ) ≤
      c * A * N * Real.log (2 * y) * Real.exp (-F) := by
    rw [heuler]
    have hm := mul_le_mul_of_nonneg_left (hprod y hy)
      (show 0 ≤ A * N * Real.exp (-F) by positivity)
    exact hm.trans_eq (by ring)
  exact hfinite.trans (add_le_add hmain herror')

end ErdosStraus.Counting
