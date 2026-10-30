import ErdosStraus.Basic
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
import Mathlib.NumberTheory.Bertrand
import ErdosStraus.Estimates.DivisorMoments
import ErdosStraus.Family.Definition
import ErdosStraus.Estimates.Chebyshev

/-!
# Scales for the selected family and the choice of `X`

Scale functions and elementary bounds used in Sections 5 and 6: the medium-prime
scale `log Y/(z log z)` and its floor version, both `o((log X)^{-3})`, the bound
`log P(z) ≤ 2z`, factorial bounds for the proof of Theorem 5.4, and counts of a
residue class over complete periods. The file also records the coordinate sets of the
family used in Proposition 6.7, and the algebra of the choice
`log X = α (log N)^{1/4}` of (23), which turns the level condition (11) into
`log P(z) + 2R log X + 6μ ≤ log N`.
-/

/-! ## The choice `log X = α (log N)^{1/4}` -/

namespace ErdosStraus

open scoped BigOperators

/-- If `LX = α LN^{1/4}` with `LN ≥ 0`, then `LX³ = α³ LN^{3/4}`; so `μ_b ≍ (log X)³`
gives `μ_b ≍ (log N)^{3/4}`. -/
theorem logX_cube_eq {α LX LN : ℝ} (hLN : 0 ≤ LN)
    (hscale : LX = α * LN ^ ((1 : ℝ) / 4)) :
    LX ^ 3 = α ^ 3 * LN ^ ((3 : ℝ) / 4) := by
  subst hscale
  rw [mul_pow]
  congr 1
  rw [← Real.rpow_natCast (LN ^ ((1 : ℝ) / 4)) 3, ← Real.rpow_mul hLN]
  norm_num

/-- `z = (log X)⁴ = α⁴ log N` under the choice `log X = α (log N)^{1/4}`. -/
theorem z_eq_alpha4_LN {α LN : ℝ} (hLN : 0 ≤ LN)
    {X : ℝ} (hscale : Real.log X = α * LN ^ ((1 : ℝ) / 4)) :
    zScale X = α ^ 4 * LN := by
  unfold zScale
  rw [hscale, mul_pow]
  congr 1
  rw [← Real.rpow_natCast (LN ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul hLN]
  norm_num

/-- Logarithmic form of the level condition (11): for `P(z), X^{2R}, N > 0`,
`log P(z) + 2R log X + 6μ ≤ log N` implies `P(z) X^{2R} e^{2μ} ≤ N e^{-4μ}`. -/
theorem finite_level_condition_of_log
    {Pz N μ R LX : ℝ} {Xpow : ℝ}
    (hPz : 0 < Pz) (hXpow : 0 < Xpow) (hN : 0 < N)
    (hXpow_log : Real.log Xpow = 2 * R * LX)
    (hlog : Real.log Pz + (2 * R * LX + 6 * μ) ≤ Real.log N) :
    Pz * Xpow * Real.exp (2 * μ) ≤ N * Real.exp (-4 * μ) := by
  have hLHS : (0 : ℝ) < Pz * Xpow * Real.exp (2 * μ) :=
    mul_pos (mul_pos hPz hXpow) (Real.exp_pos _)
  have hRHS : (0 : ℝ) < N * Real.exp (-4 * μ) :=
    mul_pos hN (Real.exp_pos _)
  rw [← Real.log_le_log_iff hLHS hRHS]
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
      Real.log_mul (ne_of_gt hPz) (ne_of_gt hXpow),
      Real.log_mul (ne_of_gt hN) (Real.exp_ne_zero _),
      Real.log_exp, Real.log_exp, hXpow_log]
  linarith [hlog]

end ErdosStraus

/-! ## Factorial bounds and the medium-prime scale -/

namespace ErdosStraus

open Filter Topology
open scoped BigOperators

/-- `∑_{r<n} t^r/r! ≤ exp t` for `t ≥ 0`. -/
theorem sum_factorial_le_exp {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ∑ r ∈ Finset.range n, t ^ r / (Nat.factorial r : ℝ) ≤ Real.exp t :=
  Real.sum_le_exp_of_nonneg ht n

/-- If `F_r ≤ M^r/r!` for `r ≤ n` and `X ≥ 1`, then
`∑_{r≤n} X^r F_r ≤ X^n e^M`: the error term in the proof of Theorem 5.4,
with `M = 2μ_b` and `n = 2R_b`. -/
theorem brun_envelope_of_factorial_bound_up_to
    (F : ℕ → ℝ) (M X : ℝ) (n : ℕ)
    (hM : 0 ≤ M) (hX : 1 ≤ X)
    (hF : ∀ r : ℕ, r ≤ n →
      F r ≤ M ^ r / (Nat.factorial r : ℝ)) :
    (∑ r ∈ Finset.range (n + 1), X ^ r * F r) ≤
      X ^ n * Real.exp M := by
  have hXnonneg : 0 ≤ X := le_trans zero_le_one hX
  calc
    (∑ r ∈ Finset.range (n + 1), X ^ r * F r) ≤
        ∑ r ∈ Finset.range (n + 1),
          X ^ r * (M ^ r / (Nat.factorial r : ℝ)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left
        (hF r (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)))
        (pow_nonneg hXnonneg r)
    _ ≤ X ^ n * ∑ r ∈ Finset.range (n + 1),
        M ^ r / (Nat.factorial r : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hX
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)))
      exact div_nonneg (pow_nonneg hM r) (by positivity)
    _ ≤ X ^ n * Real.exp M :=
      mul_le_mul_of_nonneg_left
        (sum_factorial_le_exp hM (n + 1)) (pow_nonneg hXnonneg n)

/-- `n^n/n! ≤ e^n`, one term of the exponential series. -/
theorem pow_self_div_factorial_le_exp_self (n : ℕ) :
    ((n : ℝ) ^ n) / (Nat.factorial n : ℝ) ≤ Real.exp (n : ℝ) := by
  have hnonneg : ∀ r ∈ Finset.range (n + 1),
      0 ≤ (n : ℝ) ^ r / (Nat.factorial r : ℝ) := by
    intro r _hr
    positivity
  have hmem : n ∈ Finset.range (n + 1) := by
    rw [Finset.mem_range]
    omega
  exact le_trans (Finset.single_le_sum hnonneg hmem)
    (sum_factorial_le_exp (by positivity : 0 ≤ (n : ℝ)) (n + 1))

/-- `(n/e)^n ≤ n!`, which gives `(2μ_b)^r/r! ≤ (2eμ_b/r)^r` in the proof of
Theorem 5.4. -/
theorem factorial_lower_exp_self (n : ℕ) :
    ((n : ℝ) / Real.exp 1) ^ n ≤ (Nat.factorial n : ℝ) := by
  have hterm := pow_self_div_factorial_le_exp_self n
  have hfact_pos : 0 < (Nat.factorial n : ℝ) := by positivity
  have hmul : (n : ℝ) ^ n ≤ Real.exp (n : ℝ) * (Nat.factorial n : ℝ) := by
    exact (div_le_iff₀ hfact_pos).mp hterm
  calc
    ((n : ℝ) / Real.exp 1) ^ n = (n : ℝ) ^ n / (Real.exp 1) ^ n := by
      rw [div_pow]
    _ = (n : ℝ) ^ n / Real.exp (n : ℝ) := by
      rw [Real.exp_one_pow]
    _ ≤ (Nat.factorial n : ℝ) := by
      rw [div_le_iff₀ (Real.exp_pos (n : ℝ))]
      linarith

/-- The medium-prime scale `log Y/(z log z)` of Lemma 6.9, with `Y = X^σ` and
`z = (log X)^4`. -/
noncomputable def mediumScale (P : Params) (X : ℝ) : ℝ :=
  Real.log (YScale P X) / (zScale X * Real.log (zScale X))

/-- `(log X)^3 · log Y/(z log z) → 0`. For large `X` the product equals
`σ / log z`, and `log z → ∞`. Since `μ_b ≍ (log X)^3`, this gives
`μ_b log Y/(z log z) = o(1)` in the proof of Lemma 6.9. -/
theorem mediumScale_logCube_tendsto_zero (P : Params) :
    Tendsto (fun X : ℝ => (Real.log X) ^ 3 * mediumScale P X)
      atTop (𝓝 0) := by
  have hden :
      Tendsto (fun X : ℝ => (Real.log (zScale X))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Estimates.tendsto_log_zScale_atTop
  have htarget :
      Tendsto (fun X : ℝ => P.σ * (Real.log (zScale X))⁻¹) atTop (𝓝 0) := by
    simpa using hden.const_mul P.σ
  refine htarget.congr' ?_
  filter_upwards [eventually_ge_atTop (Real.exp 2)] with X hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 2) hX
  have hlogX_ge_two : (2 : ℝ) ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hX
  have hlogX_pos : 0 < Real.log X :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hlogX_ge_two
  have hlogX_ne : Real.log X ≠ 0 := ne_of_gt hlogX_pos
  have hlogz_pos : 0 < Real.log (zScale X) :=
    Estimates.log_zScale_pos_of_exp_two_le hX
  have hlogz_ne : Real.log (zScale X) ≠ 0 := ne_of_gt hlogz_pos
  have hloglog_pos : 0 < Real.log (Real.log X) :=
    Real.log_pos (lt_of_lt_of_le one_lt_two hlogX_ge_two)
  have hloglog_ne : Real.log (Real.log X) ≠ 0 := ne_of_gt hloglog_pos
  unfold mediumScale YScale zScale
  rw [Real.log_rpow hXpos]
  field_simp [hlogX_ne, hloglog_ne]

end ErdosStraus

/-! ## Coordinates of the family -/

namespace ErdosStraus

open Classical

/-- Every prime `p < ⌊z⌋ + 1` divides `P(z)`. -/
theorem prime_dvd_roughModulus_of_lt_succ_floor
    {X : ℝ} {p : ℕ} (hp : Nat.Prime p)
    (hlt : p < ⌊ErdosStraus.zScale X⌋₊ + 1) :
    p ∣ Estimates.roughModulus X := by
  exact Estimates.prime_dvd_primeProductBelow_of_le_floor
    (ErdosStraus.zScale X) p hp (by omega)

/-- For `X ≥ e`, the cutoff `⌊z⌋ + 1` is at least two. -/
theorem two_le_succ_floor_zScale
    {X : ℝ} (hX : Real.exp 1 ≤ X) :
    2 ≤ ⌊ErdosStraus.zScale X⌋₊ + 1 := by
  have hz : 1 ≤ ErdosStraus.zScale X :=
    Estimates.zScale_ge_one_of_exp_one_le hX
  have hfloor : 1 ≤ ⌊ErdosStraus.zScale X⌋₊ :=
    Nat.le_floor (by simpa using hz)
  omega

/-- The rough cofactors `d₊` of the members with given `e` and `d₋`. -/
noncomputable def familyDplusValues
    (indices : Finset Family.FamilyIndex) (E : ExactDivisor) (dminus : ℕ) :
    Finset ℕ :=
  (indices.filter (fun i => i.E = E ∧ i.dminus = dminus)).image
    (fun i => i.dplus)

/-- The large primes `p` of the members with given `(e, d₋, d₊)`. -/
noncomputable def familyPrimeValues
    (indices : Finset Family.FamilyIndex) (E : ExactDivisor)
    (dminus dplus : ℕ) : Finset ℕ :=
  (indices.filter
      (fun i => i.E = E ∧ i.dminus = dminus ∧ i.dplus = dplus)).image
    (fun i => i.p)

/-- The weight `∑ 1/(d₊ p)` of the members with given `(e, d₋)` and `D ∣ d₊`. -/
noncomputable def familyFixedEDminusDivisorMass
    (indices : Finset Family.FamilyIndex) (E : ExactDivisor)
    (dminus D : ℕ) : ℝ :=
  ∑ i ∈ indices.filter
      (fun i => i.E = E ∧ i.dminus = dminus ∧ D ∣ i.dplus),
    (1 : ℝ) / ((i.dplus * i.p : ℕ) : ℝ)

/-- The divisors `e = r s²` of the members of a finite set of indices. -/
noncomputable def familyExactValues
    (indices : Finset Family.FamilyIndex) : Finset ExactDivisor :=
  indices.image (fun i => i.E)

/-! ## Indices without the large prime -/

/-- A triple `(e, d₋, d₊)`, an index of the family before its large prime `p` is
chosen. -/
structure FamilyPrePrimeIndex where
  E : ExactDivisor
  dminus : ℕ
  dplus : ℕ

namespace FamilyPrePrimeIndex

/-- The index `(e, d₋, d₊, p)`. -/
def withPrime (j : FamilyPrePrimeIndex) (p : ℕ) : Family.FamilyIndex where
  E := j.E
  dminus := j.dminus
  dplus := j.dplus
  p := p

end FamilyPrePrimeIndex

/-- The index `(e, d₋, d₊, p)` of a pair `((e, d₋, d₊), p)`. -/
def familyPrePrimePairToIndex
    (x : Sigma fun _j : FamilyPrePrimeIndex => ℕ) : Family.FamilyIndex :=
  x.1.withPrime x.2

theorem familyPrePrimePairToIndex_injective :
    Function.Injective familyPrePrimePairToIndex := by
  intro x y hxy
  cases x with
  | mk j p =>
    cases y with
    | mk k q =>
      cases j with
      | mk Ej dmj dpj =>
        cases k with
        | mk Ek dmk dpk =>
          simp only [familyPrePrimePairToIndex,
            FamilyPrePrimeIndex.withPrime] at hxy
          injection hxy with hE hdm hdp hp
          subst Ek
          subst dmk
          subst dpk
          subst q
          rfl

theorem familyPrePrime_initial_scale_eventually (P : Params) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → 1 < X →
      UScale X * X ^ (P.σ / 2) ≤ YScale P X := by
  obtain ⟨X₀, hU⟩ := Estimates.eventually_UScale_le_rpow
    (δ := P.σ / 2) (by linarith [P.σ_pos])
  refine ⟨X₀, ?_⟩
  intro X hX hXgt
  calc
    UScale X * X ^ (P.σ / 2) ≤ X ^ (P.σ / 2) * X ^ (P.σ / 2) :=
      mul_le_mul_of_nonneg_right (hU X hX) (Real.rpow_nonneg (by linarith) _)
    _ = YScale P X := by
      rw [← Real.rpow_add (by linarith : 0 < X)]
      congr 1
      ring

/-- `⌊U⌋ · H_{⌊Y⌋} ≤ (1+σ)(log X)^9`, where `U = (log X)^8` and `H_n` is the
harmonic number. -/
theorem prePrimeErrorCutoffs_le_log_pow_nine
    (P : Params) (X : ℝ) (hX : Real.exp 1 ≤ X) :
    ((⌊UScale X⌋₊ : ℝ) * (harmonic ⌊YScale P X⌋₊ : ℝ)) ≤
      (1 + P.σ) * (Real.log X) ^ 9 := by
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hlogX : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hX
  have hσlt : P.σ < 1 := by linarith [P.β_pos, P.β_lt_one_sub_σ]
  have hYge : 1 ≤ YScale P X := by
    unfold YScale
    exact Real.one_le_rpow (le_trans (by norm_num) hX)
      P.σ_pos.le
  have hfloorU : (⌊UScale X⌋₊ : ℝ) ≤ (Real.log X) ^ 8 := by
    simpa [UScale] using Nat.floor_le (show 0 ≤ UScale X by
      unfold UScale
      positivity)
  have hharm : (harmonic ⌊YScale P X⌋₊ : ℝ) ≤
      (1 + P.σ) * Real.log X := by
    calc
      (harmonic ⌊YScale P X⌋₊ : ℝ) ≤ 1 + Real.log (YScale P X) :=
        harmonic_floor_le_one_add_log (YScale P X) hYge
      _ = 1 + P.σ * Real.log X := by
        unfold YScale
        rw [Real.log_rpow hXpos]
      _ ≤ (1 + P.σ) * Real.log X := by
        nlinarith [P.σ_pos]
  have hharm_nonneg : 0 ≤ (harmonic ⌊YScale P X⌋₊ : ℝ) :=
    Estimates.harmonic_nonneg_real _
  have hpow_nonneg : 0 ≤ (Real.log X) ^ 8 := by positivity
  calc
    (⌊UScale X⌋₊ : ℝ) * (harmonic ⌊YScale P X⌋₊ : ℝ) ≤
        (Real.log X) ^ 8 * (harmonic ⌊YScale P X⌋₊ : ℝ) :=
      mul_le_mul_of_nonneg_right hfloorU hharm_nonneg
    _ ≤ (Real.log X) ^ 8 * ((1 + P.σ) * Real.log X) :=
      mul_le_mul_of_nonneg_left hharm hpow_nonneg
    _ = (1 + P.σ) * (Real.log X) ^ 9 := by ring

/-- The conditions `d₋ = dminus`, `D ∣ d₊` and `e ≡ c (mod D)` on an index. -/
def familyTensorIndexPredicate
    (D c dminus : ℕ) (i : Family.FamilyIndex) : Prop :=
  i.dminus = dminus ∧ D ∣ i.dplus ∧ i.e % D = c

/-- The divisors `e` of the members satisfying `familyTensorIndexPredicate D c dminus`. -/
noncomputable def familyExactValuesAtDminus
    (indices : Finset Family.FamilyIndex) (D c dminus : ℕ) :
    Finset ExactDivisor :=
  familyExactValues (indices.filter (familyTensorIndexPredicate D c dminus))

/-! ## The scale `s(X)` -/

/-- The scale `s(X) = (log Y/log q)/q` with `q = ⌊z⌋ + 1`; it bounds `∑_{p ∣ d₊} 1/p`
for every member of the family. -/
noncomputable def incrementFloorScale (P : Params) (X : ℝ) : ℝ :=
  (Real.log (YScale P X) /
      Real.log (((⌊zScale X⌋₊ + 1 : ℕ) : ℝ))) /
    (((⌊zScale X⌋₊ + 1 : ℕ) : ℝ))

theorem incrementFloorScale_le_mediumScale
    (P : Params) {X : ℝ} (hX : Real.exp 2 ≤ X) :
    incrementFloorScale P X ≤ mediumScale P X := by
  have hXexp1 : Real.exp 1 ≤ X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)) hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 2) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (Real.one_le_exp (by norm_num)) hX
  have hz_pos : 0 < zScale X :=
    lt_of_lt_of_le zero_lt_one (Estimates.zScale_ge_one_of_exp_one_le hXexp1)
  have hlogz_pos : 0 < Real.log (zScale X) :=
    Estimates.log_zScale_pos_of_exp_two_le hX
  let q : ℝ := (((⌊zScale X⌋₊ + 1 : ℕ) : ℝ))
  have hz_le_q : zScale X ≤ q := by
    dsimp [q]
    simpa [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (zScale X)).le
  have hq_pos : 0 < q := lt_of_lt_of_le hz_pos hz_le_q
  have hlogz_le_logq : Real.log (zScale X) ≤ Real.log q :=
    Real.log_le_log hz_pos hz_le_q
  have hden : zScale X * Real.log (zScale X) ≤ q * Real.log q :=
    mul_le_mul hz_le_q hlogz_le_logq hlogz_pos.le hq_pos.le
  have hlogY_nonneg : 0 ≤ Real.log (YScale P X) := by
    unfold YScale
    rw [Real.log_rpow hXpos]
    exact mul_nonneg P.σ_pos.le (Real.log_nonneg hXone)
  have hdiv :
      Real.log (YScale P X) / (q * Real.log q) ≤
        Real.log (YScale P X) / (zScale X * Real.log (zScale X)) := by
    exact div_le_div_of_nonneg_left hlogY_nonneg
      (mul_pos hz_pos hlogz_pos) hden
  unfold incrementFloorScale mediumScale
  change Real.log (YScale P X) / Real.log q / q ≤ _
  rw [div_div]
  simpa [mul_comm] using hdiv

theorem incrementFloorScale_nonneg
    (P : Params) {X : ℝ} (hX : Real.exp 2 ≤ X) :
    0 ≤ incrementFloorScale P X := by
  have hXexp1 : Real.exp 1 ≤ X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)) hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 2) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (Real.one_le_exp (by norm_num)) hX
  have hq_two : 2 ≤ ⌊zScale X⌋₊ + 1 := two_le_succ_floor_zScale hXexp1
  have hlogq_pos :
      0 < Real.log (((⌊zScale X⌋₊ + 1 : ℕ) : ℝ)) :=
    Real.log_pos (by exact_mod_cast hq_two)
  have hlogY_nonneg : 0 ≤ Real.log (YScale P X) := by
    unfold YScale
    rw [Real.log_rpow hXpos]
    exact mul_nonneg P.σ_pos.le (Real.log_nonneg hXone)
  unfold incrementFloorScale
  positivity

/-- `(log X)³ s(X) → 0`. -/
theorem incrementFloorScale_logCube_tendsto_zero (P : Params) :
    Filter.Tendsto
      (fun X : ℝ => (Real.log X) ^ 3 * incrementFloorScale P X)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [Filter.eventually_ge_atTop (Real.exp 2)] with X hX
    exact mul_nonneg (pow_nonneg (Real.log_nonneg
      (le_trans (Real.one_le_exp (by norm_num)) hX)) 3)
      (incrementFloorScale_nonneg P hX)
  · filter_upwards [Filter.eventually_ge_atTop (Real.exp 2)] with X hX
    exact mul_le_mul_of_nonneg_left
      (incrementFloorScale_le_mediumScale P hX)
      (pow_nonneg (Real.log_nonneg
        (le_trans (Real.one_le_exp (by norm_num)) hX)) 3)
  · exact mediumScale_logCube_tendsto_zero P

/-! ## Compatibility of negated residue classes -/

/-- For positive moduli `q, r`: if the classes `-a (mod q)` and `-b (mod r)` are
compatible, then so are `a (mod q)` and `b (mod r)`. -/
theorem residueCompatible_of_negModResidue_compatible
    (q r a b : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hcompat : ErdosStraus.Arithmetic.residueCompatible q r
      (ErdosStraus.Arithmetic.negModResidue q a) (ErdosStraus.Arithmetic.negModResidue r b)) :
    ErdosStraus.Arithmetic.residueCompatible q r a b := by
  have hleft : ErdosStraus.Arithmetic.negModResidue q a + a ≡ 0
      [MOD Nat.gcd q r] :=
    Nat.ModEq.of_dvd (Nat.gcd_dvd_left q r)
      (ErdosStraus.Arithmetic.negModResidue_add_modEq_zero q a hq)
  have hright : ErdosStraus.Arithmetic.negModResidue r b + b ≡ 0
      [MOD Nat.gcd q r] :=
    Nat.ModEq.of_dvd (Nat.gcd_dvd_right q r)
      (ErdosStraus.Arithmetic.negModResidue_add_modEq_zero r b hr)
  exact Nat.ModEq.add_left_cancel hcompat (hleft.trans hright.symm)

/-! ## The factor `exp(s(X)) - 1` -/

/-- If `0 ≤ μ(X) ≪ (log X)³`, then `μ(X) · K · (exp(s(X)) - 1) → 0`, where
`s = incrementFloorScale`. -/
theorem singletonEulerMassError_tendsto_zero
    (P : Params) (mass : ℝ → ℝ) (K C : ℝ)
    (hK : 0 ≤ K) (_hC : 0 ≤ C)
    (hmass_nonneg : ∀ᶠ X in Filter.atTop, 0 ≤ mass X)
    (hmass_upper : ∀ᶠ X in Filter.atTop,
      mass X ≤ C * (Real.log X) ^ 3) :
    Filter.Tendsto
      (fun X => mass X * K *
        (Real.exp (incrementFloorScale P X) - 1))
      Filter.atTop (nhds 0) := by
  have hmassScale : Filter.Tendsto
      (fun X => mass X * incrementFloorScale P X)
      Filter.atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_
      (by simpa using
        (incrementFloorScale_logCube_tendsto_zero P).const_mul C)
    · filter_upwards [hmass_nonneg,
        Filter.eventually_ge_atTop (Real.exp 2)] with X hm hX
      exact mul_nonneg hm (incrementFloorScale_nonneg P hX)
    · filter_upwards [hmass_upper,
        Filter.eventually_ge_atTop (Real.exp 2)] with X hm hX
      have hs := incrementFloorScale_nonneg P hX
      calc
        mass X * incrementFloorScale P X ≤
            (C * (Real.log X) ^ 3) * incrementFloorScale P X :=
          mul_le_mul_of_nonneg_right hm hs
        _ = C * ((Real.log X) ^ 3 * incrementFloorScale P X) := by ring
  have hscale0 : Filter.Tendsto (incrementFloorScale P)
      Filter.atTop (nhds 0) := by
    have hlogCubeLower : ∀ᶠ X in Filter.atTop,
        1 ≤ (Real.log X) ^ 3 := by
      filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with X hX
      have hlog : 1 ≤ Real.log X := by
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) hX
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hlog 3]
    refine squeeze_zero' ?_ ?_
      (incrementFloorScale_logCube_tendsto_zero P)
    · filter_upwards [Filter.eventually_ge_atTop (Real.exp 2)] with X hX
      exact incrementFloorScale_nonneg P hX
    · filter_upwards [hlogCubeLower,
        Filter.eventually_ge_atTop (Real.exp 2)] with X hlog hX
      have hs := incrementFloorScale_nonneg P hX
      nlinarith
  have hbound : ∀ᶠ X in Filter.atTop,
      mass X * K * (Real.exp (incrementFloorScale P X) - 1) ≤
        2 * K * (mass X * incrementFloorScale P X) := by
    have hscaleSmall : ∀ᶠ X in Filter.atTop,
        incrementFloorScale P X < (1 : ℝ) / 2 :=
      Filter.Tendsto.eventually_lt_const
        (by norm_num : (0 : ℝ) < 1 / 2) hscale0
    filter_upwards [hmass_nonneg, hscaleSmall,
        Filter.eventually_ge_atTop (Real.exp 2)] with X hm hsSmall hX
    have hsNonneg := incrementFloorScale_nonneg P hX
    have hexp := Real.exp_bound_div_one_sub_of_interval hsNonneg
      (lt_trans hsSmall (by norm_num : (1 : ℝ) / 2 < 1))
    have hden : 0 < 1 - incrementFloorScale P X := by linarith
    have hexpLoss : Real.exp (incrementFloorScale P X) - 1 ≤
        2 * incrementFloorScale P X := by
      calc
        Real.exp (incrementFloorScale P X) - 1 ≤
            1 / (1 - incrementFloorScale P X) - 1 := by linarith
        _ ≤ 2 * incrementFloorScale P X := by
          rw [div_sub_one hden.ne']
          rw [div_le_iff₀ hden]
          nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hexpLoss (mul_nonneg hm hK)]
  refine squeeze_zero' ?_ hbound ?_
  · filter_upwards [hmass_nonneg,
      Filter.eventually_ge_atTop (Real.exp 2)] with X hm hX
    exact mul_nonneg (mul_nonneg hm hK)
      (sub_nonneg.mpr (Real.one_le_exp
        (incrementFloorScale_nonneg P hX)))
  · simpa [mul_assoc] using hmassScale.const_mul (2 * K)

/-! ## Periodic counts -/

theorem periodic_count_add_period
    (L n : ℕ) (pred : ℕ → Prop) [DecidablePred pred]
    (hperiodic : Function.Periodic pred L) :
    Nat.count pred (L + n) = Nat.count pred L + Nat.count pred n := by
  rw [Nat.count_add]
  apply congrArg₂ Nat.add rfl
  simp only [Nat.count_eq_card_filter_range]
  apply congrArg Finset.card
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hk, hp⟩
    exact ⟨hk, by
      have heq : pred (L + k) = pred k := by simpa [add_comm] using hperiodic k
      exact heq ▸ hp⟩
  · rintro ⟨hk, hp⟩
    exact ⟨hk, by
      have heq : pred (L + k) = pred k := by simpa [add_comm] using hperiodic k
      exact heq.symm ▸ hp⟩

theorem periodic_count_mul_add
    (L q r : ℕ) (pred : ℕ → Prop) [DecidablePred pred]
    (hperiodic : Function.Periodic pred L) :
    Nat.count pred (q * L + r) =
      q * Nat.count pred L + Nat.count pred r := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.succ_mul]
      conv_lhs => rw [show q * L + L + r = L + (q * L + r) by omega]
      rw [periodic_count_add_period L (q * L + r) pred hperiodic, ih]
      ring

theorem modEq_count_one_period (q a : ℕ) (hq : 0 < q) :
    Nat.count (fun n => n ≡ a [MOD q]) q = 1 := by
  rw [Nat.count_eq_card_filter_range]
  have hfilter :
      (Finset.range q).filter (fun n => n ≡ a [MOD q]) = {a % q} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hn, hmod⟩
      unfold Nat.ModEq at hmod
      simpa [Nat.mod_eq_of_lt hn] using hmod
    · intro hn
      subst n
      exact ⟨Nat.mod_lt a hq, Nat.mod_modEq a q⟩
  rw [hfilter]
  simp

/-- If `q ∣ L`, a residue class modulo `q` has exactly `L/q` elements in `[0, L)`. -/
theorem modEq_count_complete_multiple
    (L q a : ℕ) (hq : 0 < q) (hqL : q ∣ L) :
    Nat.count (fun n => n ≡ a [MOD q]) L = L / q := by
  have hperiodic : Function.Periodic (fun n => n ≡ a [MOD q]) q := by
    intro n
    apply propext
    unfold Nat.ModEq
    simp
  have hdecomp : L = (L / q) * q := (Nat.div_mul_cancel hqL).symm
  calc
    Nat.count (fun n => n ≡ a [MOD q]) L =
        Nat.count (fun n => n ≡ a [MOD q]) ((L / q) * q + 0) := by
          rw [add_zero, ← hdecomp]
    _ = (L / q) * Nat.count (fun n => n ≡ a [MOD q]) q +
        Nat.count (fun n => n ≡ a [MOD q]) 0 :=
      periodic_count_mul_add q (L / q) 0
        (fun n => n ≡ a [MOD q]) hperiodic
    _ = L / q := by rw [modEq_count_one_period q a hq]; simp

/-! ## Bonferroni rank -/

/-- The Bonferroni rank `⌊12 μ⌋ + 1`. -/
noncomputable def canonicalBrunRank (μ : ℝ) : ℕ := ⌊12 * μ⌋₊ + 1

theorem twelve_mul_le_canonicalBrunRank
    {μ : ℝ} (_hμ : 0 ≤ μ) :
    12 * μ ≤ (canonicalBrunRank μ : ℝ) := by
  unfold canonicalBrunRank
  have hlt : 12 * μ < ((⌊12 * μ⌋₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_floor_add_one (12 * μ)
  exact hlt.le

/-- `2R ≥ 24 μ` for the rank `R = ⌊12 μ⌋ + 1`. -/
theorem twentyFour_mul_le_two_canonicalBrunRank
    {μ : ℝ} (hμ : 0 ≤ μ) :
    24 * μ ≤ (2 * canonicalBrunRank μ : ℕ) := by
  have h := twelve_mul_le_canonicalBrunRank hμ
  norm_num at h ⊢
  nlinarith

/-! ## Scales in the level condition -/

/-- `log P(z) ≤ 2z`, the bound `∑_{p ≤ z} log p ≪ z` of Lemma 3.1 in the form
`∏_{p ≤ n} p ≤ 4^n`. -/
theorem log_roughModulus_le_two_zScale (X : ℝ)
    (hz : 0 ≤ zScale X) :
    Real.log (Estimates.roughModulus X : ℝ) ≤ 2 * zScale X := by
  let n := ⌊zScale X⌋₊
  let s := (Finset.Icc (2 : ℕ) n).filter Nat.Prime
  have hs_eq : s = (Finset.Icc (1 : ℕ) n).filter Nat.Prime := by
    ext p
    by_cases hp : Nat.Prime p
    · simp [s, hp, hp.two_le, hp.one_le]
    · simp [s, hp]
  have hlog_prod :
      Real.log (∏ p ∈ s, (p : ℝ)) =
        ∑ p ∈ s, Real.log (p : ℝ) := by
    rw [Real.log_prod]
    intro p hp
    exact_mod_cast ((Finset.mem_filter.mp hp).2.ne_zero)
  have hrough : (Estimates.roughModulus X : ℝ) =
      ∏ p ∈ s, (p : ℝ) := by
    simp [Estimates.roughModulus, Estimates.primeProductBelow, s, n]
  have hsum :
      (∑ p ∈ s, Real.log (p : ℝ)) ≤
        Real.log (4 : ℝ) * (n : ℝ) := by
    rw [hs_eq]
    exact Estimates.primeLogSum_le_log_four_mul n
  have hn : (n : ℝ) ≤ zScale X := by
    exact Nat.floor_le hz
  have hlog4_nonneg : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog4_two : Real.log (4 : ℝ) ≤ 2 := by
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    linarith
  calc
    Real.log (Estimates.roughModulus X : ℝ) =
        ∑ p ∈ s, Real.log (p : ℝ) := by rw [hrough, hlog_prod]
    _ ≤ Real.log (4 : ℝ) * (n : ℝ) := hsum
    _ ≤ Real.log (4 : ℝ) * zScale X :=
      mul_le_mul_of_nonneg_left hn hlog4_nonneg
    _ ≤ 2 * zScale X := mul_le_mul_of_nonneg_right hlog4_two hz

/-- The scale `X = exp(α (log N)^{1/4})` of (23). -/
noncomputable def optimizationScale (α : ℝ) (N : ℕ) : ℝ :=
  Real.exp (α * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))

theorem optimizationScale_tendsto_atTop
    {α : ℝ} (hα : 0 < α) :
    Filter.Tendsto (optimizationScale α)
      Filter.atTop Filter.atTop := by
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hquarter : Filter.Tendsto
      (fun N : ℕ => (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 4)).comp hlog
  have hexponent : Filter.Tendsto
      (fun N : ℕ => α * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hα hquarter
  exact Real.tendsto_exp_atTop.comp hexponent

end ErdosStraus

/-! ## Powers of `log X` at the scale of (23) -/

namespace ErdosStraus.CommonScale

open Filter

theorem log_scale_cube (α : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (Real.log (optimizationScale α N)) ^ 3 =
      α ^ 3 * (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4) := by
  apply logX_cube_eq (Real.log_nonneg (by exact_mod_cast hN))
  simp [optimizationScale]

theorem log_scale_fourth (α : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (Real.log (optimizationScale α N)) ^ 4 =
      α ^ 4 * Real.log (N : ℝ) := by
  simpa [zScale] using z_eq_alpha4_LN
    (Real.log_nonneg (by exact_mod_cast hN))
    (show Real.log (optimizationScale α N) =
      α * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4) by simp [optimizationScale])

end ErdosStraus.CommonScale
