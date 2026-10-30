import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.ZetaValues
import ErdosStraus.BombieriVinogradov.Assembly
import ErdosStraus.Basic

/-!
# Theorem 3.7 for `ϑ(y; q, a)` with a maximum over `y`

The Bombieri–Vinogradov theorem is proved in `ErdosStraus.BombieriVinogradov` for prime
counts `π(N; q, l)` centred at `li(N)/φ(q)`. Partial summation turns it into the bound
`∑_{q ≤ x^{1/2-ε}} max_{(a,q)=1} max_{2 ≤ y ≤ x} |ϑ(y; q, a) - y/φ(q)| ≪ x/(log x)^A`
for all `A, ε > 0`. The file ends with the recentring at `ϑ(y)/φ(q)` and the
coefficients used for the reciprocal prime sums of Lemma 3.8.
-/

namespace ErdosStraus.Estimates
open Filter Asymptotics
open scoped BigOperators Pointwise

/-! ## The maximal error -/

/-- The Chebyshev sum over a residue class,
`ϑ(y; q, a) = ∑_{p ≤ y, p ≡ a (mod q)} log p`. -/
noncomputable def thetaAP (y : ℝ) (q a : ℕ) : ℝ := by
  classical
  exact
    ∑ p ∈ (natWindow 0 y).filter (fun p : ℕ => Nat.Prime p ∧ congMod p a q),
      Real.log p

theorem thetaAP_nonneg (y : ℝ) (q a : ℕ) : 0 ≤ thetaAP y q a := by
  classical
  unfold thetaAP
  apply Finset.sum_nonneg
  intro p hp
  have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
  have hpOne : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hpPrime.one_lt.le
  exact Real.log_nonneg hpOne

/-- `∑_{1 ≤ n ≤ x} log n`, an upper bound for every `ϑ(y; q, a)` with `y ≤ x`. -/
noncomputable def thetaFullBound (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.Icc (1 : ℕ) ⌊x⌋₊, Real.log p

theorem thetaAP_le_full_bound {x y : ℝ} (q a : ℕ) (hyx : y ≤ x) :
    thetaAP y q a ≤ thetaFullBound x := by
  classical
  unfold thetaAP thetaFullBound natWindow
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hpIccY : p ∈ Finset.Icc (1 : ℕ) ⌊y⌋₊ :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
    have hp_le_floor_y : p ≤ ⌊y⌋₊ := (Finset.mem_Icc.mp hpIccY).2
    have hfloor_le : ⌊y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono hyx
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hpIccY).1, le_trans hp_le_floor_y hfloor_le⟩
  · intro p hpBig _hpSmall
    have hpOneNat : 1 ≤ p := (Finset.mem_Icc.mp hpBig).1
    have hpOne : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpOneNat
    exact Real.log_nonneg hpOne

theorem div_totient_abs_le_self {y : ℝ} (q : ℕ) (hy_nonneg : 0 ≤ y) :
    |y / (Nat.totient q : ℝ)| ≤ y := by
  by_cases htot : Nat.totient q = 0
  · simp [htot, hy_nonneg]
  · have htot_pos_nat : 0 < Nat.totient q := Nat.pos_of_ne_zero htot
    have htot_one : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by exact_mod_cast htot_pos_nat
    have htot_pos : 0 < (Nat.totient q : ℝ) := by exact_mod_cast htot_pos_nat
    have hdiv_nonneg : 0 ≤ y / (Nat.totient q : ℝ) :=
      div_nonneg hy_nonneg htot_pos.le
    rw [abs_of_nonneg hdiv_nonneg]
    exact div_le_self hy_nonneg htot_one

/-- The values `|ϑ(y; q, a) - y/φ(q)|` for `(a, q) = 1` and `2 ≤ y ≤ x`. -/
def bvErrorRawSet (x : ℝ) (q : ℕ) : Set ℝ :=
  {t : ℝ | ∃ a : ℕ, Nat.Coprime a q ∧ ∃ y : ℝ,
    2 ≤ y ∧ y ≤ x ∧ t = |thetaAP y q a - y / (Nat.totient q : ℝ)|}

/-- `bvErrorRawSet x q` together with `0`, so that the set is nonempty also for
`x < 2`. -/
def bvErrorSet (x : ℝ) (q : ℕ) : Set ℝ :=
  {0} ∪ bvErrorRawSet x q

theorem bvErrorRawSet_le_bound {x : ℝ} {q : ℕ} {t : ℝ}
    (ht : t ∈ bvErrorRawSet x q) : t ≤ thetaFullBound x + x := by
  rcases ht with ⟨a, _ha, y, hy2, hyx, rfl⟩
  have htheta_nonneg : 0 ≤ thetaAP y q a := thetaAP_nonneg y q a
  have htheta_le : thetaAP y q a ≤ thetaFullBound x := thetaAP_le_full_bound q a hyx
  have hy_nonneg : 0 ≤ y := le_trans (by norm_num) hy2
  have hdiv_abs : |y / (Nat.totient q : ℝ)| ≤ y :=
    div_totient_abs_le_self q hy_nonneg
  have hdiv_abs_x : |y / (Nat.totient q : ℝ)| ≤ x := le_trans hdiv_abs hyx
  calc
    |thetaAP y q a - y / (Nat.totient q : ℝ)|
        ≤ |thetaAP y q a| + |y / (Nat.totient q : ℝ)| := by
          simpa [sub_eq_add_neg, abs_neg]
            using abs_add_le (thetaAP y q a) (-(y / (Nat.totient q : ℝ)))
    _ = thetaAP y q a + |y / (Nat.totient q : ℝ)| := by
          rw [abs_of_nonneg htheta_nonneg]
    _ ≤ thetaFullBound x + x := add_le_add htheta_le hdiv_abs_x

theorem bvErrorSet_nonempty (x : ℝ) (q : ℕ) : (bvErrorSet x q).Nonempty :=
  ⟨0, Or.inl rfl⟩

theorem bvError_set_bddAbove (x : ℝ) (q : ℕ) : BddAbove (bvErrorSet x q) := by
  refine ⟨max 0 (thetaFullBound x + x), ?_⟩
  intro t ht
  rcases ht with ht0 | htErr
  · rw [ht0]
    exact le_max_left _ _
  · exact le_trans (bvErrorRawSet_le_bound htErr) (le_max_right _ _)

/-- The maximal error `max_{(a,q)=1} max_{2 ≤ y ≤ x} |ϑ(y; q, a) - y/φ(q)|`, defined
as the supremum of `bvErrorSet x q`; it is `0` for `x < 2`. -/
noncomputable def bvError (x : ℝ) (q : ℕ) : ℝ :=
  sSup (bvErrorSet x q)

theorem bvError_nonneg (x : ℝ) (q : ℕ) : 0 ≤ bvError x q := by
  unfold bvError
  exact le_csSup (bvError_set_bddAbove x q) (Or.inl rfl)

theorem bvErrorRawSet_le_bvError {x : ℝ} {q : ℕ} {t : ℝ}
    (ht : t ∈ bvErrorRawSet x q) : t ≤ bvError x q := by
  unfold bvError
  exact le_csSup (bvError_set_bddAbove x q) (Or.inr ht)

theorem thetaAP_error_le_bvError {x y : ℝ} {q a : ℕ}
    (ha : Nat.Coprime a q) (hy2 : 2 ≤ y) (hyx : y ≤ x) :
    |thetaAP y q a - y / (Nat.totient q : ℝ)| ≤ bvError x q := by
  exact bvErrorRawSet_le_bvError
    ⟨a, ha, y, hy2, hyx, rfl⟩

/-- The Bombieri–Vinogradov sum
`∑_{q ≤ x^{1/2-ε}} max_{(a,q)=1} max_{2 ≤ y ≤ x} |ϑ(y; q, a) - y/φ(q)|`. -/
noncomputable def bvSum (x ε : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc (1 : ℕ) ⌊x ^ ((1 : ℝ) / 2 - ε)⌋₊, bvError x q

/-- Theorem 3.7 for `ϑ` with a maximum over `y ≤ x`: for all `A, ε > 0`,
`bvSum x ε ≪ x/(log x)^A`. -/
def BombieriVinogradovMaximalForm : Prop :=
  ∀ A ε : ℝ, 0 < A → 0 < ε →
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      bvSum x ε ≤ C * (x / (Real.log x) ^ A)

/-! ## Deduction from the prime-count form -/

namespace MaximalForm

open Finset

/-- `Li x` is the logarithmic integral `li(x) = 2/log 2 + ∫_2^x dt/log t`. -/
local notation "Li" => BombieriVinogradov.logIntegral

/-! ### Partial summation -/

/-- Prefix count `∑_{p ≤ M} ι p` of a weight sequence. -/
noncomputable def cnt (ι : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑ p ∈ range (M + 1), ι p

/-- Log-weighted prefix sum `∑_{1 ≤ p ≤ M} ι p log p`. -/
noncomputable def wsum (ι : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑ p ∈ Icc 1 M, ι p * Real.log p

theorem cnt_succ (ι : ℕ → ℝ) (M : ℕ) : cnt ι (M + 1) = cnt ι M + ι (M + 1) := by
  unfold cnt
  rw [Finset.sum_range_succ]

theorem wsum_succ (ι : ℕ → ℝ) (M : ℕ) :
    wsum ι (M + 1) = wsum ι M + ι (M + 1) * Real.log ((M : ℝ) + 1) := by
  unfold wsum
  rw [Finset.sum_Icc_succ_top (by omega)]
  push_cast
  rfl

theorem trueLi_two : Li 2 = 2 / Real.log 2 := by
  simp [BombieriVinogradov.logIntegral, BombieriVinogradov.shiftedLogIntegral]

/-- One unit step of the logarithmic integral: `∫_m^{m+1} dt/log t` lies between
`1/log(m+1)` and `1/log m`. -/
theorem trueLi_step {m : ℝ} (hm : 2 ≤ m) :
    1 / Real.log (m + 1) ≤ Li (m + 1) - Li m ∧ Li (m + 1) - Li m ≤ 1 / Real.log m := by
  have hint1 := BombieriVinogradov.inv_log_intervalIntegrable_of_two_le
    (le_refl (2 : ℝ)) (show (2 : ℝ) ≤ m + 1 by linarith)
  have hint2 := BombieriVinogradov.inv_log_intervalIntegrable_of_two_le
    (le_refl (2 : ℝ)) hm
  have hint3 := BombieriVinogradov.inv_log_intervalIntegrable_of_two_le
    hm (show m ≤ m + 1 by linarith)
  have hdiff : Li (m + 1) - Li m = ∫ t in m..(m + 1), 1 / Real.log t := by
    simp only [BombieriVinogradov.logIntegral, BombieriVinogradov.shiftedLogIntegral]
    rw [← intervalIntegral.integral_interval_sub_left hint1 hint2]
    ring
  have hlogm : 0 < Real.log m := Real.log_pos (by linarith)
  rw [hdiff]
  constructor
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (show m ≤ m + 1 by linarith)
      (intervalIntegrable_const (c := 1 / Real.log (m + 1))) hint3
      (fun t ht => by
        have ht1 : m ≤ t := ht.1
        have hlt : 0 < Real.log t := Real.log_pos (by linarith)
        have hle : Real.log t ≤ Real.log (m + 1) := Real.log_le_log (by linarith) ht.2
        exact one_div_le_one_div_of_le hlt hle)
    simpa using h
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (show m ≤ m + 1 by linarith)
      hint3 (intervalIntegrable_const (c := 1 / Real.log m))
      (fun t ht => by
        have ht1 : m ≤ t := ht.1
        have hle : Real.log m ≤ Real.log t := Real.log_le_log (by linarith) ht1
        exact one_div_le_one_div_of_le hlogm hle)
    simpa using h

theorem trueLi_step_log {M : ℕ} (hM : 2 ≤ M) :
    0 ≤ (Li ((M : ℝ) + 1) - Li M) * Real.log ((M : ℝ) + 1) - 1 ∧
    (Li ((M : ℝ) + 1) - Li M) * Real.log ((M : ℝ) + 1) - 1 ≤
      (Real.log ((M : ℝ) + 1) - Real.log M) / Real.log 2 := by
  have hm : (2 : ℝ) ≤ M := by exact_mod_cast hM
  obtain ⟨hlo, hhi⟩ := trueLi_step hm
  have hlogm : 0 < Real.log M := Real.log_pos (by linarith)
  have hlogm1 : 0 < Real.log ((M : ℝ) + 1) := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmono : Real.log M ≤ Real.log ((M : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog2m : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) hm
  constructor
  · have h1 := mul_le_mul_of_nonneg_right hlo hlogm1.le
    have h2 : 1 / Real.log ((M : ℝ) + 1) * Real.log ((M : ℝ) + 1) = 1 := by
      field_simp
    linarith
  · have h1 := mul_le_mul_of_nonneg_right hhi hlogm1.le
    have h2 : 1 / Real.log M * Real.log ((M : ℝ) + 1) - 1 =
        (Real.log ((M : ℝ) + 1) - Real.log M) / Real.log M := by
      field_simp
    have h3 : (Real.log ((M : ℝ) + 1) - Real.log M) / Real.log M ≤
        (Real.log ((M : ℝ) + 1) - Real.log M) / Real.log 2 :=
      div_le_div_of_nonneg_left (by linarith) hlog2 hlog2m
    linarith

/-- Partial summation: if `|cnt ι n - li(n)/φ| ≤ K` for all `n ≤ N`, then
`|wsum ι M - M/φ - (cnt ι M - li(M)/φ) log M| ≤ (K + 1/log 2)(log M - log 2)`
for `2 ≤ M ≤ N`. -/
theorem partial_summation (ι : ℕ → ℝ) (h0 : ι 0 = 0) (h1 : ι 1 = 0)
    {φ K : ℝ} (hφ : 1 ≤ φ) {N : ℕ}
    (hE : ∀ n, n ≤ N → |cnt ι n - Li n / φ| ≤ K) :
    ∀ M, 2 ≤ M → M ≤ N →
      |wsum ι M - M / φ - (cnt ι M - Li M / φ) * Real.log M| ≤
        (K + 1 / Real.log 2) * (Real.log M - Real.log 2) := by
  intro M hM2
  induction M, hM2 using Nat.le_induction with
  | base =>
    intro _
    have hφ0 : φ ≠ 0 := by linarith
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    have hw : wsum ι 2 = ι 2 * Real.log 2 := by
      have : (Icc 1 2 : Finset ℕ) = {1, 2} := by decide
      simp [wsum, this, h1]
    have hc : cnt ι 2 = ι 2 := by simp [cnt, Finset.sum_range_succ, h0, h1]
    rw [hw, hc]
    push_cast
    rw [trueLi_two]
    have : ι 2 * Real.log 2 - 2 / φ - (ι 2 - 2 / Real.log 2 / φ) * Real.log 2 = 0 := by
      field_simp
      ring
    rw [this]
    simp
  | succ M hM ih =>
    intro hMN
    have ih' := ih (by omega)
    have hEM := hE M (by omega)
    obtain ⟨hlo, hhi⟩ := trueLi_step_log hM
    rw [wsum_succ, cnt_succ]
    push_cast
    have hφpos : 0 < φ := by linarith
    have hφ0 : φ ≠ 0 := hφpos.ne'
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hd : 0 ≤ Real.log ((M : ℝ) + 1) - Real.log M := by
      have hm : (2 : ℝ) ≤ M := by exact_mod_cast hM
      have := Real.log_le_log (by linarith : (0 : ℝ) < M) (by linarith : (M : ℝ) ≤ M + 1)
      linarith
    have key :
        wsum ι M + ι (M + 1) * Real.log ((M : ℝ) + 1) - ((M : ℝ) + 1) / φ -
            (cnt ι M + ι (M + 1) - Li ((M : ℝ) + 1) / φ) * Real.log ((M : ℝ) + 1) =
          (wsum ι M - M / φ - (cnt ι M - Li M / φ) * Real.log M)
            - (cnt ι M - Li M / φ) * (Real.log ((M : ℝ) + 1) - Real.log M)
            + ((Li ((M : ℝ) + 1) - Li M) * Real.log ((M : ℝ) + 1) - 1) / φ := by
      field_simp
      ring
    rw [key]
    have hEd : |(cnt ι M - Li M / φ) * (Real.log ((M : ℝ) + 1) - Real.log M)| ≤
        K * (Real.log ((M : ℝ) + 1) - Real.log M) := by
      rw [abs_mul, abs_of_nonneg hd]
      exact mul_le_mul_of_nonneg_right hEM hd
    have hc : |((Li ((M : ℝ) + 1) - Li M) * Real.log ((M : ℝ) + 1) - 1) / φ| ≤
        (Real.log ((M : ℝ) + 1) - Real.log M) / Real.log 2 := by
      rw [abs_div, abs_of_nonneg hlo, abs_of_pos hφpos]
      exact (div_le_self hlo hφ).trans hhi
    calc
      |(wsum ι M - M / φ - (cnt ι M - Li M / φ) * Real.log M)
            - (cnt ι M - Li M / φ) * (Real.log ((M : ℝ) + 1) - Real.log M)
            + ((Li ((M : ℝ) + 1) - Li M) * Real.log ((M : ℝ) + 1) - 1) / φ|
          ≤ |wsum ι M - M / φ - (cnt ι M - Li M / φ) * Real.log M|
            + |(cnt ι M - Li M / φ) * (Real.log ((M : ℝ) + 1) - Real.log M)|
            + |((Li ((M : ℝ) + 1) - Li M) * Real.log ((M : ℝ) + 1) - 1) / φ| := by
            refine (abs_add_le _ _).trans ?_
            gcongr
            exact abs_sub _ _
      _ ≤ (K + 1 / Real.log 2) * (Real.log M - Real.log 2)
            + K * (Real.log ((M : ℝ) + 1) - Real.log M)
            + (Real.log ((M : ℝ) + 1) - Real.log M) / Real.log 2 := by
            gcongr
      _ = (K + 1 / Real.log 2) * (Real.log ((M : ℝ) + 1) - Real.log 2) := by
            field_simp
            ring

/-- Consequently `|wsum ι M - M/φ| ≤ (2K + 2) log M`. -/
theorem wsum_sub_le (ι : ℕ → ℝ) (h0 : ι 0 = 0) (h1 : ι 1 = 0)
    {φ K : ℝ} (hφ : 1 ≤ φ) (hK : 0 ≤ K) {N : ℕ}
    (hE : ∀ n, n ≤ N → |cnt ι n - Li n / φ| ≤ K) {M : ℕ} (hM2 : 2 ≤ M) (hMN : M ≤ N) :
    |wsum ι M - M / φ| ≤ (2 * K + 2) * Real.log M := by
  have hps := partial_summation ι h0 h1 hφ hE M hM2 hMN
  have hEM := hE M hMN
  have hlog2gt : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  have hlog2pos : 0 < Real.log 2 := by linarith
  have hinv : 1 / Real.log 2 ≤ 2 := by
    rw [div_le_iff₀ hlog2pos]
    linarith
  have hlogM : Real.log 2 ≤ Real.log M :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hM2)
  have hlogMnn : 0 ≤ Real.log M := by linarith
  have hb1 : (K + 1 / Real.log 2) * (Real.log M - Real.log 2) ≤ (K + 2) * Real.log M := by
    apply mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hb2 : |(cnt ι M - Li M / φ) * Real.log M| ≤ K * Real.log M := by
    rw [abs_mul, abs_of_nonneg hlogMnn]
    exact mul_le_mul_of_nonneg_right hEM hlogMnn
  calc
    |wsum ι M - M / φ|
        = |(wsum ι M - M / φ - (cnt ι M - Li M / φ) * Real.log M)
            + (cnt ι M - Li M / φ) * Real.log M| := by
          congr 1
          ring
    _ ≤ |wsum ι M - M / φ - (cnt ι M - Li M / φ) * Real.log M|
          + |(cnt ι M - Li M / φ) * Real.log M| := abs_add_le _ _
    _ ≤ (K + 2) * Real.log M + K * Real.log M := add_le_add (hps.trans hb1) hb2
    _ = (2 * K + 2) * Real.log M := by ring

/-! ### Comparison with prime counts -/

/-- The indicator of primes in the residue class of `a` modulo `q`. -/
noncomputable def ind (q a : ℕ) (p : ℕ) : ℝ :=
  if p.Prime ∧ p % q = a % q then 1 else 0

theorem ind_zero (q a : ℕ) : ind q a 0 = 0 := by
  simp [ind, Nat.not_prime_zero]

theorem ind_one (q a : ℕ) : ind q a 1 = 0 := by
  simp [ind, Nat.not_prime_one]

theorem natWindow_zero (y : ℝ) : natWindow 0 y = Icc 1 ⌊y⌋₊ := by
  unfold natWindow
  apply Finset.filter_true_of_mem
  intro n hn
  have h1n : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  exact_mod_cast h1n

/-- `ϑ(y; q, a)` depends only on `⌊y⌋`. -/
theorem thetaAP_eq_wsum (y : ℝ) (q a : ℕ) : thetaAP y q a = wsum (ind q a) ⌊y⌋₊ := by
  classical
  unfold thetaAP wsum ind
  rw [natWindow_zero, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  unfold congMod
  split_ifs <;> simp_all

theorem primesInAP_eq_cnt (n q a : ℕ) :
    (BombieriVinogradov.primesInAP n q (a % q) : ℝ) = cnt (ind q a) n := by
  classical
  unfold BombieriVinogradov.primesInAP cnt ind
  rw [Finset.natCast_card_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h : p.Prime ∧ p % q = a % q
  · rw [if_pos h, if_pos]
    exact ⟨h.1, by unfold Nat.ModEq; rw [Nat.mod_mod]; exact h.2⟩
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    exact ⟨h'.1, by have := h'.2; unfold Nat.ModEq at this; rw [Nat.mod_mod] at this; exact this⟩

theorem mod_mem_unitResidues {q a : ℕ} (hq : 1 ≤ q) (ha : Nat.Coprime a q) :
    a % q ∈ BombieriVinogradov.unitResidues q := by
  unfold BombieriVinogradov.unitResidues
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨Nat.mod_lt _ (by omega), ?_⟩
  unfold Nat.Coprime
  rw [← Nat.gcd_rec, Nat.gcd_comm]
  exact ha

theorem standardMaxError_le_prefix {n N q : ℕ} (h : n ≤ N) :
    BombieriVinogradov.primeAPMaxError n q ≤
      BombieriVinogradov.primeAPPrefixMaxError N q := by
  unfold BombieriVinogradov.primeAPPrefixMaxError
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (by omega), rfl⟩

/-- For `2 ≤ y ≤ x`, `|ϑ(y; q, a) - y/φ(q)| ≤ (2K + 2) log x + 1`, where `K` is the
maximum of `|π(n; q, l) - li(n)/φ(q)|` over `n ≤ x` and reduced residues `l`. -/
theorem abs_thetaAP_sub_le {x y : ℝ} {q a : ℕ} (hq : 1 ≤ q) (ha : Nat.Coprime a q)
    (hy2 : 2 ≤ y) (hyx : y ≤ x) :
    |thetaAP y q a - y / (Nat.totient q : ℝ)| ≤
      (2 * BombieriVinogradov.primeAPPrefixMaxError ⌊x⌋₊ q + 2) * Real.log x + 1 := by
  set K := BombieriVinogradov.primeAPPrefixMaxError ⌊x⌋₊ q with hKdef
  set φ : ℝ := (Nat.totient q : ℝ) with hφdef
  have hφ : 1 ≤ φ := by
    have : 0 < q.totient := Nat.totient_pos.mpr (by omega)
    rw [hφdef]
    exact_mod_cast this
  have hK : 0 ≤ K := BombieriVinogradov.primeAPPrefixMaxError_nonneg _ _
  have hE : ∀ n, n ≤ ⌊x⌋₊ → |cnt (ind q a) n - Li n / φ| ≤ K := by
    intro n hn
    rw [← primesInAP_eq_cnt]
    exact (BombieriVinogradov.abs_primeAPError_le_max (mod_mem_unitResidues hq ha)).trans
      (standardMaxError_le_prefix hn)
  have hM2 : 2 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy2)
  have hMN : ⌊y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor hyx
  have hw := wsum_sub_le (ind q a) (ind_zero q a) (ind_one q a) hφ hK hE hM2 hMN
  rw [thetaAP_eq_wsum]
  have hy0 : 0 ≤ y := by linarith
  have hMy : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
  have hyM : y < ⌊y⌋₊ + 1 := Nat.lt_floor_add_one y
  have hMpos : (0 : ℝ) < ⌊y⌋₊ := by exact_mod_cast (show 0 < ⌊y⌋₊ by omega)
  have hlogMx : Real.log ⌊y⌋₊ ≤ Real.log x := Real.log_le_log hMpos (hMy.trans hyx)
  have hφpos : 0 < φ := by linarith
  have hfrac : |(⌊y⌋₊ : ℝ) / φ - y / φ| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos hφpos, div_le_one hφpos]
    rw [abs_le]
    constructor <;> linarith
  have hmono : (2 * K + 2) * Real.log ⌊y⌋₊ ≤ (2 * K + 2) * Real.log x :=
    mul_le_mul_of_nonneg_left hlogMx (by linarith)
  calc
    |wsum (ind q a) ⌊y⌋₊ - y / φ|
        ≤ |wsum (ind q a) ⌊y⌋₊ - ⌊y⌋₊ / φ| + |(⌊y⌋₊ : ℝ) / φ - y / φ| := abs_sub_le _ _ _
    _ ≤ (2 * K + 2) * Real.log ⌊y⌋₊ + 1 := add_le_add hw hfrac
    _ ≤ (2 * K + 2) * Real.log x + 1 := by linarith

/-- The same bound for `bvError x q`. -/
theorem bvError_le_prefix {x : ℝ} {q : ℕ} (hq : 1 ≤ q) (hx : 1 ≤ x) :
    bvError x q ≤
      (2 * BombieriVinogradov.primeAPPrefixMaxError ⌊x⌋₊ q + 2) * Real.log x + 1 := by
  have hK := BombieriVinogradov.primeAPPrefixMaxError_nonneg ⌊x⌋₊ q
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  unfold bvError
  apply csSup_le (bvErrorSet_nonempty x q)
  intro t ht
  rcases ht with ht0 | ⟨a, ha, y, hy2, hyx, rfl⟩
  · rw [Set.mem_singleton_iff.mp ht0]
    have := mul_nonneg (by linarith :
      (0 : ℝ) ≤ 2 * BombieriVinogradov.primeAPPrefixMaxError ⌊x⌋₊ q + 2) hlog
    linarith
  · exact abs_thetaAP_sub_le hq ha hy2 hyx

/-! ### Proof of the maximal form -/

/-- `BombieriVinogradovMaximalForm` follows from `BombieriVinogradov.standard_form`. -/
theorem bombieri_vinogradov_maximal_form : BombieriVinogradovMaximalForm := by
  intro A ε hA hε
  obtain ⟨B, hB, C₀, hC₀, hev⟩ :=
    BombieriVinogradov.standard_form
      (A + 1) (by linarith)
  have hevx := (tendsto_nat_floor_atTop (α := ℝ)).eventually hev
  have hcut : ∀ᶠ x : ℝ in atTop, 2 * Real.log x ^ B ≤ x ^ ε := by
    have hb := (isLittleO_log_rpow_rpow_atTop B hε).bound (show (0 : ℝ) < 1 / 2 by norm_num)
    filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) B),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) ε)] at hx
    linarith
  have hsmall : ∀ᶠ x : ℝ in atTop, 3 * Real.log x ^ (A + 1) ≤ x ^ ((1 : ℝ) / 2) := by
    have hb := (isLittleO_log_rpow_rpow_atTop (A + 1) (show (0 : ℝ) < 1 / 2 by norm_num)).bound
      (show (0 : ℝ) < 1 / 3 by norm_num)
    filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
    linarith
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    (hevx.and (hcut.and (hsmall.and (eventually_ge_atTop (4 : ℝ)))))
  refine ⟨2 * 2 ^ (A + 1) * C₀ + 1, x₀, by positivity, ?_⟩
  intro x hx
  obtain ⟨hBVx, hcutx, hsmallx, hx4⟩ := hx₀ x hx
  -- facts about `x` and `N = ⌊x⌋₊`
  have hx0 : 0 < x := by linarith
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxN : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  have hN4 : 4 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx4)
  have hN4r : (4 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN4
  have hNpos : (0 : ℝ) < ⌊x⌋₊ := by linarith
  have hx2N : x ≤ 2 * ⌊x⌋₊ := by linarith
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlogx4 : Real.log 4 ≤ Real.log x := Real.log_le_log (by norm_num) hx4
  have hlogx1 : 1 ≤ Real.log x := by linarith
  have hlogxpos : 0 < Real.log x := by linarith
  have hlogNx : Real.log ⌊x⌋₊ ≤ Real.log x := Real.log_le_log hNpos hNx
  have hlogN_half : Real.log x / 2 ≤ Real.log ⌊x⌋₊ := by
    have h : Real.log x ≤ Real.log 2 + Real.log ⌊x⌋₊ := by
      rw [← Real.log_mul (by norm_num) hNpos.ne']
      exact Real.log_le_log hx0 hx2N
    linarith
  have hlogNpos : 0 < Real.log ⌊x⌋₊ := by linarith
  have hBV := hBVx (by omega)
  -- `x^{1/2-ε} ≤ √N/(log N)^B`, so `standard_form` covers the moduli `q ≤ x^{1/2-ε}`
  have hQQ' : ⌊x ^ ((1 : ℝ) / 2 - ε)⌋₊ ≤ BombieriVinogradov.modulusCutoff ⌊x⌋₊ B := by
    unfold BombieriVinogradov.modulusCutoff
    apply Nat.floor_le_floor
    have hpowsub : x ^ ((1 : ℝ) / 2 - ε) = x ^ ((1 : ℝ) / 2) / x ^ ε := Real.rpow_sub hx0 _ _
    have hlogB : Real.log ⌊x⌋₊ ^ B ≤ Real.log x ^ B :=
      Real.rpow_le_rpow hlogNpos.le hlogNx hB
    have hlogBpos : 0 < Real.log ⌊x⌋₊ ^ B := Real.rpow_pos_of_pos hlogNpos B
    have hlogxBpos : 0 < Real.log x ^ B := Real.rpow_pos_of_pos hlogxpos B
    have hxεpos : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 ε
    have hNh : 0 ≤ (⌊x⌋₊ : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hNpos.le _
    have hsqrt : x ^ ((1 : ℝ) / 2) ≤ 2 * (⌊x⌋₊ : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      rw [mul_pow, Real.sq_sqrt hNpos.le]
      linarith
    rw [hpowsub]
    calc
      x ^ ((1 : ℝ) / 2) / x ^ ε ≤ (2 * (⌊x⌋₊ : ℝ) ^ ((1 : ℝ) / 2)) / x ^ ε :=
        div_le_div_of_nonneg_right hsqrt hxεpos.le
      _ ≤ (2 * (⌊x⌋₊ : ℝ) ^ ((1 : ℝ) / 2)) / (2 * Real.log x ^ B) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hcutx
      _ = (⌊x⌋₊ : ℝ) ^ ((1 : ℝ) / 2) / Real.log x ^ B := by
        field_simp
      _ ≤ (⌊x⌋₊ : ℝ) ^ ((1 : ℝ) / 2) / Real.log ⌊x⌋₊ ^ B :=
        div_le_div_of_nonneg_left hNh hlogBpos hlogB
  have hQx : ((⌊x ^ ((1 : ℝ) / 2 - ε)⌋₊ : ℕ) : ℝ) ≤ x ^ ((1 : ℝ) / 2) := by
    calc
      ((⌊x ^ ((1 : ℝ) / 2 - ε)⌋₊ : ℕ) : ℝ) ≤ x ^ ((1 : ℝ) / 2 - ε) :=
        Nat.floor_le (Real.rpow_nonneg hx0.le _)
      _ ≤ x ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  set N := ⌊x⌋₊ with hNdef
  set Q := ⌊x ^ ((1 : ℝ) / 2 - ε)⌋₊ with hQdef
  set Q' := BombieriVinogradov.modulusCutoff N B with hQ'def
  set Kq : ℕ → ℝ := fun q => BombieriVinogradov.primeAPPrefixMaxError N q with hKqdef
  have hKq : ∀ q, 0 ≤ Kq q := fun q =>
    BombieriVinogradov.primeAPPrefixMaxError_nonneg N q
  have hterm : ∀ q ∈ Icc 1 Q,
      bvError x q ≤ 2 * Real.log x * Kq q + (2 * Real.log x + 1) := by
    intro q hq
    have h := bvError_le_prefix (Finset.mem_Icc.mp hq).1 (show (1 : ℝ) ≤ x by linarith)
    simp only [hKqdef]
    linarith
  have hsumQ : ∑ q ∈ Icc 1 Q, Kq q ≤ ∑ q ∈ Icc 1 Q', Kq q :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hQQ')
      (fun q _ _ => hKq q)
  have hsumQ' : ∑ q ∈ Icc 1 Q', Kq q ≤ C₀ * (N : ℝ) / Real.log N ^ (A + 1) := hBV
  -- the moduli contribute `2 log x ∑_q K_q ≤ 2^{A+2} C₀ x/(log x)^A`
  have hLApos : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hlogxpos A
  have hLA : Real.log x ^ (A + 1) = Real.log x ^ A * Real.log x :=
    Real.rpow_add_one hlogxpos.ne' A
  have hmain : 2 * Real.log x * (C₀ * (N : ℝ) / Real.log N ^ (A + 1)) ≤
      2 * 2 ^ (A + 1) * C₀ * (x / Real.log x ^ A) := by
    have hpowN : (Real.log x / 2) ^ (A + 1) ≤ Real.log N ^ (A + 1) :=
      Real.rpow_le_rpow (by positivity) hlogN_half (by linarith)
    have hpow_eq : (Real.log x / 2) ^ (A + 1) = Real.log x ^ A * Real.log x / 2 ^ (A + 1) := by
      rw [Real.div_rpow hlogxpos.le (by norm_num), hLA]
    have h2pos : (0 : ℝ) < 2 ^ (A + 1) := by positivity
    have hD : 0 < Real.log x ^ A * Real.log x / 2 ^ (A + 1) := by positivity
    have h1 : C₀ * (N : ℝ) / Real.log N ^ (A + 1) ≤
        C₀ * x / (Real.log x ^ A * Real.log x / 2 ^ (A + 1)) := by
      calc
        C₀ * (N : ℝ) / Real.log N ^ (A + 1) ≤ C₀ * x / Real.log N ^ (A + 1) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hNx hC₀.le
        _ ≤ C₀ * x / (Real.log x ^ A * Real.log x / 2 ^ (A + 1)) := by
          apply div_le_div_of_nonneg_left (by positivity) hD
          rw [← hpow_eq]
          exact hpowN
    have h2 : 2 * Real.log x * (C₀ * x / (Real.log x ^ A * Real.log x / 2 ^ (A + 1))) =
        2 * 2 ^ (A + 1) * C₀ * (x / Real.log x ^ A) := by
      have hne1 : Real.log x ≠ 0 := hlogxpos.ne'
      have hne2 : Real.log x ^ A ≠ 0 := hLApos.ne'
      have hne3 : (2 : ℝ) ^ (A + 1) ≠ 0 := h2pos.ne'
      field_simp
    calc
      2 * Real.log x * (C₀ * (N : ℝ) / Real.log N ^ (A + 1))
          ≤ 2 * Real.log x * (C₀ * x / (Real.log x ^ A * Real.log x / 2 ^ (A + 1))) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * 2 ^ (A + 1) * C₀ * (x / Real.log x ^ A) := h2
  -- the terms `2 log x + 1` contribute at most `x/(log x)^A`
  have hsec : x ^ ((1 : ℝ) / 2) * (2 * Real.log x + 1) ≤ x / Real.log x ^ A := by
    rw [le_div_iff₀ hLApos]
    have hxh : 0 ≤ x ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hx0.le _
    have hsq : x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2) = x := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.mul_self_sqrt hx0.le
    have hlin : (2 * Real.log x + 1) * Real.log x ^ A ≤ 3 * Real.log x ^ (A + 1) := by
      rw [hLA]
      nlinarith
    calc
      x ^ ((1 : ℝ) / 2) * (2 * Real.log x + 1) * Real.log x ^ A
          = x ^ ((1 : ℝ) / 2) * ((2 * Real.log x + 1) * Real.log x ^ A) := by ring
      _ ≤ x ^ ((1 : ℝ) / 2) * (3 * Real.log x ^ (A + 1)) :=
            mul_le_mul_of_nonneg_left hlin hxh
      _ ≤ x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hsmallx hxh
      _ = x := hsq
  have hcard : ((Icc 1 Q).card : ℝ) = (Q : ℝ) := by
    rw [Nat.card_Icc]
    norm_num
  calc
    bvSum x ε = ∑ q ∈ Icc 1 Q, bvError x q := rfl
    _ ≤ ∑ q ∈ Icc 1 Q, (2 * Real.log x * Kq q + (2 * Real.log x + 1)) :=
          Finset.sum_le_sum hterm
    _ = 2 * Real.log x * ∑ q ∈ Icc 1 Q, Kq q + (Q : ℝ) * (2 * Real.log x + 1) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hcard]
    _ ≤ 2 * Real.log x * (C₀ * (N : ℝ) / Real.log N ^ (A + 1))
          + x ^ ((1 : ℝ) / 2) * (2 * Real.log x + 1) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (hsumQ.trans hsumQ') (by positivity)
          · exact mul_le_mul_of_nonneg_right hQx (by positivity)
    _ ≤ 2 * 2 ^ (A + 1) * C₀ * (x / Real.log x ^ A) + x / Real.log x ^ A :=
          add_le_add hmain hsec
    _ = (2 * 2 ^ (A + 1) * C₀ + 1) * (x / Real.log x ^ A) := by ring

end MaximalForm

/-- Theorem 3.7 (Bombieri 1965, Vinogradov 1965) in the form
`BombieriVinogradovMaximalForm`. -/
theorem standard_bombieri_vinogradov_maximal_form : BombieriVinogradovMaximalForm :=
  MaximalForm.bombieri_vinogradov_maximal_form

end ErdosStraus.Estimates

/-! ## Single moduli and recentring at `ϑ(y)/φ(q)` -/

namespace ErdosStraus.PrimeEstimates

open scoped BigOperators
open Estimates

theorem bvError_le_bvSum {x ε : ℝ} {q : ℕ}
    (hq : 1 ≤ q) (hqX : q ≤ ⌊x ^ ((1 : ℝ) / 2 - ε)⌋₊) :
    bvError x q ≤ bvSum x ε := by
  classical
  exact Finset.single_le_sum (fun k _ => bvError_nonneg x k)
    (Finset.mem_Icc.mpr ⟨hq, hqX⟩)

/-- Recentring from `y/φ(q)` to `ϑ(y)/φ(q)`: the difference
`ϑ(y; q, a) - ϑ(y)/φ(q)` is bounded by the maximal errors at `q` and at `1`. -/
theorem thetaAP_recenter_error_le {x y : ℝ} {q a : ℕ}
    (ha : Nat.Coprime a q) (hy2 : 2 ≤ y) (hyx : y ≤ x) :
    |thetaAP y q a - thetaAP y 1 0 / (Nat.totient q : ℝ)| ≤
      bvError x q + bvError x 1 / (Nat.totient q : ℝ) := by
  have hq := thetaAP_error_le_bvError ha hy2 hyx
  have h1 := thetaAP_error_le_bvError (q := 1) (a := 0) (by decide) hy2 hyx
  simp only [Nat.totient_one, Nat.cast_one, div_one] at h1
  have ht : 0 ≤ (Nat.totient q : ℝ) := Nat.cast_nonneg _
  calc
    |thetaAP y q a - thetaAP y 1 0 / (Nat.totient q : ℝ)| =
        |(thetaAP y q a - y / (Nat.totient q : ℝ)) -
          (thetaAP y 1 0 - y) / (Nat.totient q : ℝ)| := by congr 1; ring
    _ ≤ |thetaAP y q a - y / (Nat.totient q : ℝ)| +
        |(thetaAP y 1 0 - y) / (Nat.totient q : ℝ)| := abs_sub _ _
    _ = |thetaAP y q a - y / (Nat.totient q : ℝ)| +
        |thetaAP y 1 0 - y| / (Nat.totient q : ℝ) := by
      rw [abs_div, abs_of_nonneg ht]
    _ ≤ bvError x q + bvError x 1 / (Nat.totient q : ℝ) :=
      add_le_add hq (div_le_div_of_nonneg_right h1 ht)

end ErdosStraus.PrimeEstimates

/-!
## Coefficients for reciprocal prime sums

Partial summation for `∑ 1/p` over primes `p ≡ a (mod q)` uses the coefficients
`1_{p ≡ a (q)} log p`, whose prefix sums are `ϑ(x; q, a)`, and the weight
`1/(n log n)`, which turns them into `1/p`.
-/

namespace ErdosStraus.PrimeEstimates

open scoped BigOperators Classical
open Finset Estimates

/-- `log n` if `n` is a prime `≡ a (mod q)`, and `0` otherwise; its prefix sums are
`ϑ(k; q, a)`. -/
noncomputable def primeLogCoefficient (q a n : ℕ) : ℝ :=
  if Nat.Prime n ∧ congMod n a q then Real.log n else 0

/-- `1/(n log n)`. -/
noncomputable def reciprocalLogWeight (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * Real.log n)

theorem natWindow_eq_Ioc_floor {a b : ℝ} (ha : 0 ≤ a) :
    natWindow a b = Ioc ⌊a⌋₊ ⌊b⌋₊ := by
  classical
  ext n
  simp only [natWindow, mem_filter, mem_Icc, mem_Ioc]
  constructor
  · rintro ⟨⟨_, hn⟩, han⟩
    exact ⟨(Nat.floor_lt ha).mpr han, hn⟩
  · rintro ⟨han, hn⟩
    exact ⟨⟨by omega, hn⟩, (Nat.floor_lt ha).mp han⟩

theorem thetaAP_nat_eq_prefix (q a k : ℕ) :
    thetaAP (k : ℝ) q a = ∑ n ∈ Icc 0 k, primeLogCoefficient q a n := by
  classical
  rw [thetaAP, natWindow_eq_Ioc_floor (by norm_num)]
  simp only [Nat.floor_zero, Nat.floor_natCast, Finset.sum_filter]
  rw [← Finset.add_sum_Ioc_eq_sum_Icc (f := primeLogCoefficient q a)
    (Nat.zero_le k)]
  simp [primeLogCoefficient]

theorem reciprocalLogWeight_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ reciprocalLogWeight n := by
  unfold reciprocalLogWeight
  exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg n)
    (Real.log_nonneg (by exact_mod_cast hn)))

theorem reciprocalLogWeight_antitone {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    reciprocalLogWeight n ≤ reciprocalLogWeight m := by
  have hmreal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
  have hmnreal : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  apply one_div_le_one_div_of_le
  · exact mul_pos (by positivity) (Real.log_pos hmreal)
  · exact mul_le_mul hmnreal (Real.log_le_log (by positivity) hmnreal)
      (Real.log_pos hmreal).le (Nat.cast_nonneg n)

theorem reciprocalLogWeight_mul_primeLogCoefficient (q a n : ℕ) :
    reciprocalLogWeight n * primeLogCoefficient q a n =
      if Nat.Prime n ∧ congMod n a q then (1 : ℝ) / n else 0 := by
  classical
  unfold primeLogCoefficient
  split_ifs with h
  · have hn : (1 : ℝ) < (n : ℝ) := by exact_mod_cast h.1.one_lt
    have hlog : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hn)
    unfold reciprocalLogWeight
    field_simp
  · simp

end ErdosStraus.PrimeEstimates
