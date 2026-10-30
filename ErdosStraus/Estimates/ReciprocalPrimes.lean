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
import ErdosStraus.Estimates.Squarefree
import ErdosStraus.Estimates.DivisorMoments
import ErdosStraus.MaximalBV
import ErdosStraus.Estimates.PartialSummation
import ErdosStraus.Estimates.Mertens

/-!
# Lemma 3.8: reciprocal primes in progressions

Let `𝒫_X = ∑_{X^β < p ≤ X^{1-σ}} 1/p`, let `G_q(a)` be the sum over the primes
`p ≡ a (mod q)` of the same window minus `𝒫_X/φ(q)`, and let `g_q = max_{(a,q)=1} |G_q(a)|`.
Partial summation from the maximal Bombieri–Vinogradov theorem gives
`∑_{q ≤ X^ν} g_q ≪ (log X)^{-A}` for `ν < β/2`, and Cauchy–Schwarz with `g_q ≪ log X/φ(q)`
gives `∑_{q ≤ X^ν} τ(q) g_q ≪ (log X)^{-7}` (Lemma 3.8), as well as the same bound with any
weight `τ(q)^C` and any power of `log X`. The file also proves
`𝒫_X = log((1-σ)/β) + O(1/log X)` and deduces Theorem 3.7, which concerns `π(x; q, a)`, from
the maximal form of the theorem for `ϑ(x; q, a)`.
-/

namespace ErdosStraus.Estimates

open Filter Asymptotics
open scoped BigOperators Pointwise

/-- The sum `∑_{X^β < p ≤ X^{1-σ}, p ≡ a (mod m)} 1/p` of Lemma 3.6. -/
noncomputable def btRecip (P : ErdosStraus.Params) (X : ℝ) (m a : ℕ) : ℝ := by
  classical
  exact
    ∑ p ∈ (natWindow (X ^ P.β) (X ^ (1 - P.σ))).filter
        (fun p : ℕ => Nat.Prime p ∧ congMod p a m),
      (1 : ℝ) / (p : ℝ)

theorem btRecip_nonneg (P : ErdosStraus.Params) (X : ℝ) (m a : ℕ) :
    0 ≤ btRecip P X m a := by
  classical
  unfold btRecip
  apply Finset.sum_nonneg
  intro p _hp
  exact div_nonneg zero_le_one (Nat.cast_nonneg p)

/-- The sum `𝒫_X = ∑_{X^β < p ≤ X^{1-σ}} 1/p` over all primes of the window. -/
noncomputable def primeRecipWindow (P : ErdosStraus.Params) (X : ℝ) : ℝ := by
  classical
  exact
    ∑ p ∈ (natWindow (X ^ P.β) (X ^ (1 - P.σ))).filter (fun p : ℕ => Nat.Prime p),
      (1 : ℝ) / (p : ℝ)

theorem btRecip_eq_of_mod_eq {P : ErdosStraus.Params} {X : ℝ} {m a b : ℕ}
    (hab : a % m = b % m) : btRecip P X m a = btRecip P X m b := by
  classical
  unfold btRecip congMod
  rw [hab]

theorem btRecip_mod_one_eq_primeRecipWindow (P : ErdosStraus.Params) (X : ℝ) (a : ℕ) :
    btRecip P X 1 a = primeRecipWindow P X := by
  classical
  unfold btRecip primeRecipWindow congMod
  simp [Nat.mod_one]

/-- The statement that `𝒫_X` is bounded below by a positive constant for large `X`; by
Lemma 3.1, `𝒫_X` tends to `log((1-σ)/β) > 0`. -/
def PrimeRecipWindowMertensLowerBound : Prop :=
  ∀ P : ErdosStraus.Params,
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      c ≤ btRecip P X 1 0

/-- The maximal error `g_m = max_{(a,m)=1} |G_m(a)|` of Lemma 3.8, where
`G_m(a) = ∑_{X^β < p ≤ X^{1-σ}, p ≡ a (mod m)} 1/p - 𝒫_X/φ(m)` and `a` runs over `1 ≤ a ≤ m`.
Every term is nonnegative, so starting the maximum at `0` does not change it. -/
noncomputable def reducedClassPrimeErrorMax (P : ErdosStraus.Params) (X : ℝ) (m : ℕ) : ℝ := by
  classical
  exact
    ((Finset.Icc (1 : ℕ) m).filter (fun a => Nat.Coprime a m)).fold max 0
      (fun a : ℕ =>
        |btRecip P X m a - (1 / (Nat.totient m : ℝ)) * btRecip P X 1 0|)

theorem reducedClassPrimeErrorMax_nonneg (P : ErdosStraus.Params) (X : ℝ) (m : ℕ) :
    0 ≤ reducedClassPrimeErrorMax P X m := by
  classical
  unfold reducedClassPrimeErrorMax
  rw [Finset.le_fold_max]
  exact Or.inl le_rfl

theorem reducedClassPrimeError_le_max {P : ErdosStraus.Params} {X : ℝ} {m a : ℕ}
    (ha : a ∈ (Finset.Icc (1 : ℕ) m).filter (fun a => Nat.Coprime a m)) :
    |btRecip P X m a - (1 / (Nat.totient m : ℝ)) * btRecip P X 1 0|
      ≤ reducedClassPrimeErrorMax P X m := by
  classical
  unfold reducedClassPrimeErrorMax
  rw [Finset.le_fold_max]
  exact Or.inr ⟨a, ha, le_rfl⟩

/-- A representative of `a` modulo `m` in `[1, m]` when `(a, m) = 1`: `1` if `m = 1`, and
`a % m` otherwise. -/
def reducedClassRepresentative (m a : ℕ) : ℕ :=
  if m = 1 then 1 else a % m

theorem reducedClassRepresentative_mod_eq (m a : ℕ) :
    (reducedClassRepresentative m a) % m = a % m := by
  by_cases hm1 : m = 1
  · subst hm1
    rw [reducedClassRepresentative, if_pos rfl, Nat.mod_one, Nat.mod_one]
  · by_cases hm0 : m = 0
    · subst hm0
      simp [reducedClassRepresentative, hm1]
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      simp [reducedClassRepresentative, hm1, Nat.mod_eq_of_lt (Nat.mod_lt a hmpos)]

theorem reducedClassRepresentative_mem {m a : ℕ} (hm : 0 < m) (ha : Nat.Coprime a m) :
    reducedClassRepresentative m a ∈
      (Finset.Icc (1 : ℕ) m).filter (fun r => Nat.Coprime r m) := by
  classical
  by_cases hm1 : m = 1
  · subst hm1
    simp [reducedClassRepresentative]
  · have hmod_lt : a % m < m := Nat.mod_lt a hm
    have hmod_pos : 0 < a % m := by
      by_contra hnot
      have hzero : a % m = 0 := Nat.eq_zero_of_not_pos hnot
      have hdiv : m ∣ a := Nat.dvd_of_mod_eq_zero hzero
      have hgcd_right : a.gcd m = m := Nat.gcd_eq_right hdiv
      have hgcd_one : a.gcd m = 1 := ha.gcd_eq_one
      have hm_eq_one : m = 1 := by
        rw [← hgcd_right, hgcd_one]
      exact hm1 hm_eq_one
    have hcop : Nat.Coprime (a % m) m := by
      rw [Nat.coprime_iff_gcd_eq_one]
      calc
        (a % m).gcd m = m.gcd a := by rw [← Nat.gcd_rec m a]
        _ = a.gcd m := Nat.gcd_comm m a
        _ = 1 := ha.gcd_eq_one
    have hIcc : a % m ∈ Finset.Icc (1 : ℕ) m :=
      Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hmod_pos, hmod_lt.le⟩
    have hfilter : a % m ∈
        (Finset.Icc (1 : ℕ) m).filter (fun r => Nat.Coprime r m) :=
      Finset.mem_filter.mpr ⟨hIcc, hcop⟩
    simpa [reducedClassRepresentative, hm1] using hfilter

/-- `|G_m(a)| ≤ g_m` for every `a` coprime to `m`. -/
theorem reducedClassPrimeError_le_max_of_coprime
    {P : ErdosStraus.Params} {X : ℝ} {m a : ℕ}
    (hm : 0 < m) (ha : Nat.Coprime a m) :
    |btRecip P X m a - (1 / (Nat.totient m : ℝ)) * btRecip P X 1 0|
      ≤ reducedClassPrimeErrorMax P X m := by
  let r := reducedClassRepresentative m a
  have hr_mem : r ∈ (Finset.Icc (1 : ℕ) m).filter (fun r => Nat.Coprime r m) :=
    reducedClassRepresentative_mem hm ha
  have hmod : a % m = r % m := by
    exact (reducedClassRepresentative_mod_eq m a).symm
  have hbt : btRecip P X m a = btRecip P X m r := btRecip_eq_of_mod_eq hmod
  rw [hbt]
  exact reducedClassPrimeError_le_max hr_mem

/-- The weighted sum `∑_{m ≤ X^ν} τ(m)^C g_m` of Lemma 3.8. -/
noncomputable def weightedBVSum (P : ErdosStraus.Params) (X C ν : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc (1 : ℕ) ⌊X ^ ν⌋₊,
    ((tau m : ℝ) ^ C) * reducedClassPrimeErrorMax P X m

theorem weightedBVSum_nonneg (P : ErdosStraus.Params) (X C ν : ℝ) :
    0 ≤ weightedBVSum P X C ν := by
  classical
  unfold weightedBVSum
  apply Finset.sum_nonneg
  intro m _hm
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) C)
    (reducedClassPrimeErrorMax_nonneg P X m)

/-- The statement of Lemma 3.8 with general weights: for `0 < ν < β/2`, `A > 0` and `C ≥ 0`,
`∑_{m ≤ X^ν} τ(m)^C g_m ≪ (log X)^{-A}`. Since `ν < β/2`, the moduli `m ≤ X^ν` lie below
`t^{1/2}` for every `t ≥ X^β`, within the range of Theorem 3.7. -/
def WeightedReciprocalBombieriVinogradov : Prop :=
  ∀ P : ErdosStraus.Params, ∀ ν A Cw : ℝ,
    0 < ν → ν < P.β / 2 → 0 < A → 0 ≤ Cw →
      ∃ K X₀ : ℝ, 0 < K ∧ ∀ X : ℝ, X₀ ≤ X →
        |weightedBVSum P X Cw ν| ≤ K * (Real.log X) ^ (-A)

end ErdosStraus.Estimates

namespace ErdosStraus.PrimeEstimates

/-! ## Partial summation from the Bombieri–Vinogradov theorem

Write `E(x, q) = max_{(a,q)=1} max_{2 ≤ y ≤ x} |ϑ(y; q, a) - y/φ(q)|` for `bvError x q`. -/

section

open scoped BigOperators Classical
open Finset Estimates

/-- `E(x, q) + E(x, 1)/φ(q)`, which bounds `|ϑ(y; q, a) - ϑ(y)/φ(q)|` for `2 ≤ y ≤ x` and
`(a, q) = 1`. -/
noncomputable def recenteredChebyshevError (x : ℝ) (q : ℕ) : ℝ :=
  bvError x q + bvError x 1 / (Nat.totient q : ℝ)

theorem recenteredChebyshevError_nonneg (x : ℝ) (q : ℕ) :
    0 ≤ recenteredChebyshevError x q :=
  add_nonneg (bvError_nonneg x q)
    (div_nonneg (bvError_nonneg x 1) (Nat.cast_nonneg _))

/-- The coefficient `n w(n) + m w(m+1) + ∑_{m<k<n} k (w(k) - w(k+1))`, with `w(k) = 1/(k log k)`,
that multiplies `D` when the prefix errors at height `k` are at most `D k`. -/
noncomputable def reciprocalPartialSummationWeight (m n : ℕ) : ℝ :=
  (n : ℝ) * reciprocalLogWeight n + (m : ℝ) * reciprocalLogWeight (m + 1) +
    ∑ k ∈ Ico (m + 1) n,
      (k : ℝ) * (reciprocalLogWeight k - reciprocalLogWeight (k + 1))

theorem reciprocalPartialSummationWeight_eq {m n : ℕ} (hmn : m < n) :
    reciprocalPartialSummationWeight m n =
      2 * m * reciprocalLogWeight (m + 1) +
        ∑ k ∈ Ioc m n, reciprocalLogWeight k :=
  global_partial_linear_coefficient reciprocalLogWeight hmn

theorem reciprocalPartialSummationWeight_le {m n : ℕ} (hm : 2 ≤ m) (hmn : m < n) :
    reciprocalPartialSummationWeight m n ≤
      (3 + Real.log (n : ℝ)) / Real.log ((m + 1 : ℕ) : ℝ) := by
  have hmreal : (1 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < m + 1 by omega)
  have hlogpos : 0 < Real.log ((m + 1 : ℕ) : ℝ) := Real.log_pos hmreal
  have hend : 2 * m * reciprocalLogWeight (m + 1) ≤
      2 / Real.log ((m + 1 : ℕ) : ℝ) := by
    unfold reciprocalLogWeight
    have hratio : (m : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by norm_cast; omega)
    calc
      2 * m * (1 / (↑(m + 1) * Real.log ↑(m + 1))) =
          (2 / Real.log ↑(m + 1)) * ((m : ℝ) / ↑(m + 1)) := by ring
      _ ≤ 2 / Real.log ↑(m + 1) := mul_le_of_le_one_right (by positivity) hratio
  have hsum : (∑ k ∈ Ioc m n, reciprocalLogWeight k) ≤
      (harmonic n : ℝ) / Real.log ((m + 1 : ℕ) : ℝ) := by
    calc
      (∑ k ∈ Ioc m n, reciprocalLogWeight k) ≤
          ∑ k ∈ Ioc m n, ((1 : ℝ) / k) / Real.log ((m + 1 : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        have hmk : ((m + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
          exact_mod_cast (show m + 1 ≤ k by have := (Finset.mem_Ioc.mp hk).1; omega)
        have hlog := Real.log_le_log (by positivity : (0 : ℝ) < ↑(m + 1)) hmk
        unfold reciprocalLogWeight
        rw [← div_div]
        exact div_le_div_of_nonneg_left (by positivity) hlogpos hlog
      _ = (∑ k ∈ Ioc m n, (1 : ℝ) / k) / Real.log ((m + 1 : ℕ) : ℝ) :=
        (Finset.sum_div _ _ _).symm
      _ ≤ (harmonic n : ℝ) / Real.log ((m + 1 : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right _ hlogpos.le
        have hh : (harmonic n : ℝ) = ∑ k ∈ Icc 1 n, (1 : ℝ) / k := by
          simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
        rw [hh]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Ioc.mp hk).1; omega,
            (Finset.mem_Ioc.mp hk).2⟩
        · intro k _ _
          positivity
  rw [reciprocalPartialSummationWeight_eq hmn]
  have hharm := harmonic_le_one_add_log n
  have hharmdiv := div_le_div_of_nonneg_right hharm hlogpos.le
  have hboth := add_le_add hend (hsum.trans hharmdiv)
  refine hboth.trans_eq ?_
  ring

/-- Summation by parts with the weight `1/(k log k)` bounds
`|∑_{m<p≤n, p ≡ a (q)} 1/p - (1/φ(q)) ∑_{m<p≤n} 1/p|` by the errors
`E(k, q) + E(k, 1)/φ(q)` at the heights `m ≤ k ≤ n`. -/
theorem reciprocal_prime_block_error_le_local {m n q a : ℕ}
    (hm : 2 ≤ m) (hmn : m < n) (ha : Nat.Coprime a q) :
    |(∑ p ∈ (Ioc m n).filter (fun p => Nat.Prime p ∧ congMod p a q), (1 : ℝ) / p) -
      (∑ p ∈ (Ioc m n).filter Nat.Prime, (1 : ℝ) / p) / (Nat.totient q : ℝ)| ≤
      reciprocalLogWeight n * recenteredChebyshevError (n : ℝ) q +
        reciprocalLogWeight (m + 1) * recenteredChebyshevError (m : ℝ) q +
          ∑ k ∈ Ico (m + 1) n,
            (reciprocalLogWeight k - reciprocalLogWeight (k + 1)) *
              recenteredChebyshevError (k : ℝ) q := by
  let c : ℕ → ℝ := fun k =>
    primeLogCoefficient q a k - primeLogCoefficient 1 0 k / (Nat.totient q : ℝ)
  have hprefix : ∀ k ∈ Icc m n, |∑ j ∈ Icc 0 k, c j| ≤
      recenteredChebyshevError (k : ℝ) q := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hm.trans (Finset.mem_Icc.mp hk).1
    simpa only [c, Finset.sum_sub_distrib, ← Finset.sum_div,
      ← thetaAP_nat_eq_prefix, recenteredChebyshevError] using
      thetaAP_recenter_error_le ha hk2 le_rfl
  have hbound := abs_sum_Ioc_mul_le_of_global c reciprocalLogWeight
    (fun k : ℕ => recenteredChebyshevError (k : ℝ) q) hmn
    (reciprocalLogWeight_nonneg (by omega))
    (reciprocalLogWeight_nonneg (by omega))
    (fun k hk => reciprocalLogWeight_antitone
      (by have := (Finset.mem_Ico.mp hk).1; omega) (Nat.le_succ k)) hprefix
  have heq : (∑ k ∈ Ioc m n, reciprocalLogWeight k * c k) =
      (∑ p ∈ (Ioc m n).filter (fun p => Nat.Prime p ∧ congMod p a q), (1 : ℝ) / p) -
        (∑ p ∈ (Ioc m n).filter Nat.Prime, (1 : ℝ) / p) / (Nat.totient q : ℝ) := by
    simp only [Finset.sum_filter]
    simp only [c, mul_sub, ← mul_div_assoc, Finset.sum_sub_distrib,
      ← Finset.sum_div, reciprocalLogWeight_mul_primeLogCoefficient,
      congMod, Nat.mod_one, and_true]
  rwa [heq] at hbound

/-- The same bound for `g_q` on the window `X^β < p ≤ X^{1-σ}`. -/
theorem reducedClassPrimeErrorMax_le_local (P : ErdosStraus.Params) (X : ℝ)
    (hX : 0 ≤ X) (q : ℕ) (hm : 2 ≤ ⌊X ^ P.β⌋₊)
    (hmn : ⌊X ^ P.β⌋₊ < ⌊X ^ (1 - P.σ)⌋₊) :
    let m : ℕ := ⌊X ^ P.β⌋₊
    let n : ℕ := ⌊X ^ (1 - P.σ)⌋₊
    reducedClassPrimeErrorMax P X q ≤
      reciprocalLogWeight n * recenteredChebyshevError (n : ℝ) q +
        reciprocalLogWeight (m + 1) * recenteredChebyshevError (m : ℝ) q +
          ∑ k ∈ Ico (m + 1) n,
            (reciprocalLogWeight k - reciprocalLogWeight (k + 1)) *
              recenteredChebyshevError (k : ℝ) q := by
  dsimp only
  unfold reducedClassPrimeErrorMax
  rw [Finset.fold_max_le]
  constructor
  · apply add_nonneg
    · exact add_nonneg
        (mul_nonneg (reciprocalLogWeight_nonneg (by omega))
          (recenteredChebyshevError_nonneg _ _))
        (mul_nonneg (reciprocalLogWeight_nonneg (by omega))
          (recenteredChebyshevError_nonneg _ _))
    · apply Finset.sum_nonneg
      intro k hk
      exact mul_nonneg (sub_nonneg.mpr (reciprocalLogWeight_antitone
        (by have := (Finset.mem_Ico.mp hk).1; omega) (Nat.le_succ k)))
        (recenteredChebyshevError_nonneg _ _)
  · intro a ha
    have hacop := (Finset.mem_filter.mp ha).2
    have hblock := reciprocal_prime_block_error_le_local hm hmn hacop
    rw [btRecip_mod_one_eq_primeRecipWindow]
    refine Eq.trans_le ?_ hblock
    simp only [btRecip, primeRecipWindow,
      natWindow_eq_Ioc_floor (Real.rpow_nonneg hX _)]
    congr 1
    ring

/-- If `∑_{q ≤ Q} (E(k, q) + E(k, 1)/φ(q)) ≤ D k` at every height `k` of the window, then
`∑_{q ≤ Q} g_q` is at most `D` times the partial summation coefficient. -/
theorem sum_reducedClassPrimeErrorMax_le_local_linear
    (P : ErdosStraus.Params) (X : ℝ) (hX : 0 ≤ X) (Q : ℕ) (D : ℝ)
    (hm : 2 ≤ ⌊X ^ P.β⌋₊)
    (hmn : ⌊X ^ P.β⌋₊ < ⌊X ^ (1 - P.σ)⌋₊)
    (hprefix : ∀ k ∈ Icc ⌊X ^ P.β⌋₊ ⌊X ^ (1 - P.σ)⌋₊,
      (∑ q ∈ Icc 1 Q, recenteredChebyshevError (k : ℝ) q) ≤ D * k) :
    (∑ q ∈ Icc 1 Q, reducedClassPrimeErrorMax P X q) ≤
      D * reciprocalPartialSummationWeight ⌊X ^ P.β⌋₊ ⌊X ^ (1 - P.σ)⌋₊ := by
  let m : ℕ := ⌊X ^ P.β⌋₊
  let n : ℕ := ⌊X ^ (1 - P.σ)⌋₊
  have hsum : (∑ q ∈ Icc 1 Q, reducedClassPrimeErrorMax P X q) ≤
      reciprocalLogWeight n * (∑ q ∈ Icc 1 Q, recenteredChebyshevError (n : ℝ) q) +
        reciprocalLogWeight (m + 1) * (∑ q ∈ Icc 1 Q, recenteredChebyshevError (m : ℝ) q) +
          ∑ k ∈ Ico (m + 1) n,
            (reciprocalLogWeight k - reciprocalLogWeight (k + 1)) *
              (∑ q ∈ Icc 1 Q, recenteredChebyshevError (k : ℝ) q) := by
    calc
      (∑ q ∈ Icc 1 Q, reducedClassPrimeErrorMax P X q) ≤
          ∑ q ∈ Icc 1 Q,
            (reciprocalLogWeight n * recenteredChebyshevError (n : ℝ) q +
              reciprocalLogWeight (m + 1) * recenteredChebyshevError (m : ℝ) q +
                ∑ k ∈ Ico (m + 1) n,
                  (reciprocalLogWeight k - reciprocalLogWeight (k + 1)) *
                    recenteredChebyshevError (k : ℝ) q) := by
        exact Finset.sum_le_sum (fun q _ => reducedClassPrimeErrorMax_le_local P X hX q hm hmn)
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
  have hsumlinear : (∑ q ∈ Icc 1 Q, reducedClassPrimeErrorMax P X q) ≤
      reciprocalLogWeight n * (D * n) + reciprocalLogWeight (m + 1) * (D * m) +
        ∑ k ∈ Ico (m + 1) n,
          (reciprocalLogWeight k - reciprocalLogWeight (k + 1)) * (D * k) := by
    apply hsum.trans
    apply add_le_add
    · exact add_le_add
        (mul_le_mul_of_nonneg_left (hprefix n (Finset.mem_Icc.mpr ⟨hmn.le, le_rfl⟩))
          (reciprocalLogWeight_nonneg (by omega)))
        (mul_le_mul_of_nonneg_left (hprefix m (Finset.mem_Icc.mpr ⟨le_rfl, hmn.le⟩))
          (reciprocalLogWeight_nonneg (by omega)))
    · apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left
        (hprefix k (Finset.mem_Icc.mpr
          ⟨by have := (Finset.mem_Ico.mp hk).1; omega, (Finset.mem_Ico.mp hk).2.le⟩))
        (sub_nonneg.mpr (reciprocalLogWeight_antitone
          (by have := (Finset.mem_Ico.mp hk).1; omega) (Nat.le_succ k)))
  have hfactor : (∑ k ∈ Ico (m + 1) n,
      (reciprocalLogWeight k - reciprocalLogWeight (k + 1)) * (D * k)) =
        D * (∑ k ∈ Ico (m + 1) n,
          (k : ℝ) * (reciprocalLogWeight k - reciprocalLogWeight (k + 1))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hfactor] at hsumlinear
  unfold reciprocalPartialSummationWeight
  convert hsumlinear using 1
  ring

/-- If `⌊X^ν⌋ ≤ ⌊k^{1/2-ε}⌋`, then
`∑_{q ≤ X^ν} (E(k, q) + E(k, 1)/φ(q)) ≤ bvSum k ε · (1 + ∑_{q ≤ X^ν} 1/φ(q))`. -/
theorem sum_recenteredChebyshevError_le_bvSum (X ν ε : ℝ) (k : ℕ)
    (hQ : 1 ≤ ⌊X ^ ν⌋₊)
    (hcut : ⌊X ^ ν⌋₊ ≤ ⌊(k : ℝ) ^ ((1 : ℝ) / 2 - ε)⌋₊) :
    (∑ q ∈ Icc 1 ⌊X ^ ν⌋₊, recenteredChebyshevError (k : ℝ) q) ≤
      bvSum (k : ℝ) ε * (1 + divisorPhiMoment X 0 ν) := by
  have hsum : (∑ q ∈ Icc 1 ⌊X ^ ν⌋₊, bvError (k : ℝ) q) ≤ bvSum (k : ℝ) ε := by
    unfold bvSum
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hq).1, (Finset.mem_Icc.mp hq).2.trans hcut⟩
    · intro q _ _
      exact bvError_nonneg _ _
  have hone : bvError (k : ℝ) 1 ≤ bvSum (k : ℝ) ε :=
    bvError_le_bvSum le_rfl (hQ.trans hcut)
  have hidentity : (∑ q ∈ Icc 1 ⌊X ^ ν⌋₊, recenteredChebyshevError (k : ℝ) q) =
      (∑ q ∈ Icc 1 ⌊X ^ ν⌋₊, bvError (k : ℝ) q) +
        bvError (k : ℝ) 1 * divisorPhiMoment X 0 ν := by
    simp only [recenteredChebyshevError, divisorPhiMoment, pow_zero, Nat.cast_one,
      Finset.sum_add_distrib, Finset.mul_sum, div_eq_mul_inv, one_mul]
  rw [hidentity]
  have hmajor := add_le_add hsum (mul_le_mul_of_nonneg_right hone (divisorPhiMoment_nonneg X 0 ν))
  refine hmajor.trans_eq ?_
  ring

theorem eventually_rpow_lt_floor_rpow {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∀ᶠ X : ℝ in Filter.atTop, X ^ a < (⌊X ^ b⌋₊ : ℝ) := by
  have hratio : ∀ᶠ X : ℝ in Filter.atTop, (2 : ℝ) ≤ X ^ (b - a) :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually (Filter.eventually_ge_atTop 2)
  filter_upwards [hratio, Filter.eventually_ge_atTop (1 : ℝ)] with X hratio hX
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hpowpos : 0 < X ^ a := Real.rpow_pos_of_pos hXpos _
  have hpowone : 1 ≤ X ^ a := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hX ha.le
  rw [Real.rpow_sub hXpos] at hratio
  have hlarge := (le_div_iff₀ hpowpos).mp hratio
  have hfloor := Nat.lt_floor_add_one (X ^ b)
  linarith

theorem eventually_rpow_le_floor_rpow {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∀ᶠ X : ℝ in Filter.atTop, X ^ a ≤ (⌊X ^ b⌋₊ : ℝ) :=
  (eventually_rpow_lt_floor_rpow ha hab).mono (fun _ h => h.le)

theorem one_add_divisorPhiMoment_zero_le_log_sq {X ν : ℝ}
    (hX : Real.exp 1 ≤ X) (hν : 0 < ν) :
    1 + divisorPhiMoment X 0 ν ≤ (1 + (ν + 1) ^ 2) * (Real.log X) ^ 2 := by
  have hXpos : 0 < X := (Real.exp_pos _).trans_le hX
  have hlog : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hX
  have hlognonneg : 0 ≤ Real.log X := zero_le_one.trans hlog
  have hpowpos : 0 < X ^ ν := Real.rpow_pos_of_pos hXpos _
  have hpowone : 1 ≤ X ^ ν := by
    apply (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 1) hpowpos).mp
    rw [Real.log_one, Real.log_rpow hXpos]
    exact mul_nonneg hν.le hlognonneg
  have hH : (harmonic ⌊X ^ ν⌋₊ : ℝ) ≤ (ν + 1) * Real.log X := by
    have hh := harmonic_floor_le_one_add_log (X ^ ν) hpowone
    rw [Real.log_rpow hXpos] at hh
    nlinarith
  have hHnonneg : (0 : ℝ) ≤ (harmonic ⌊X ^ ν⌋₊ : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact Finset.sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  have hmoment := (le_abs_self (divisorPhiMoment X 0 ν)).trans
    (abs_divisorPhiMoment_zero_le_harmonic_sq X ν)
  have hsquare := pow_le_pow_left₀ hHnonneg hH 2
  nlinarith [sq_nonneg (Real.log X - 1)]

/-- From the maximal Bombieri–Vinogradov theorem: for `0 < ν < β/2`,
`∑_{q ≤ X^ν} (E(k, q) + E(k, 1)/φ(q)) ≪ k/(log X)^A` uniformly for `k ≥ ⌊X^β⌋`. -/
theorem recenteredChebyshevError_sum_uniform_of_bv
    (hbv : BombieriVinogradovMaximalForm) {β ν A : ℝ}
    (hβ : 0 < β) (hν : 0 < ν) (hνβ : ν < β / 2) (hA : 0 < A) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ k : ℕ, ⌊X ^ β⌋₊ ≤ k →
        (∑ q ∈ Icc 1 ⌊X ^ ν⌋₊, recenteredChebyshevError (k : ℝ) q) ≤
          C * k / (Real.log X) ^ A := by
  let b : ℝ := (β + 2 * ν) / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hbβ : b < β := by dsimp [b]; linarith
  have hνb : ν / b < 1 / 2 := by
    apply (div_lt_iff₀ hb).mpr
    dsimp [b]
    linarith
  let δ : ℝ := (ν / b + 1 / 2) / 2
  let ε : ℝ := 1 / 2 - δ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hε : 0 < ε := by dsimp [ε, δ]; linarith
  have hmargin : ν ≤ b * δ := by
    have hdiv : b * (ν / b) = ν := by field_simp
    have hgap : 0 ≤ b * (1 / 2 - ν / b) := mul_nonneg hb.le (by linarith)
    dsimp [δ]
    nlinarith
  let L : ℝ := A + 2
  have hL : 0 < L := by dsimp [L]; linarith
  obtain ⟨C, x₀, hC, hBV⟩ := hbv L ε hL hε
  let S : ℝ := 1 + (ν + 1) ^ 2
  let Cb : ℝ := C * S / b ^ L
  have hCb : 0 < Cb := div_pos (mul_pos hC (by dsimp [S]; positivity))
    (Real.rpow_pos_of_pos hb _)
  have hfloor := eventually_rpow_le_floor_rpow hb hbβ
  have hheight : ∀ᶠ X : ℝ in Filter.atTop, max x₀ 2 ≤ X ^ b :=
    (tendsto_rpow_atTop hb).eventually (Filter.eventually_ge_atTop (max x₀ 2))
  have hfinal : ∀ᶠ X : ℝ in Filter.atTop, ∀ k : ℕ, ⌊X ^ β⌋₊ ≤ k →
      (∑ q ∈ Icc 1 ⌊X ^ ν⌋₊, recenteredChebyshevError (k : ℝ) q) ≤
        Cb * k / (Real.log X) ^ A := by
    filter_upwards [hfloor, hheight, Filter.eventually_ge_atTop (Real.exp 1)] with X hf hh hX
    have hXpos : 0 < X := (Real.exp_pos _).trans_le hX
    have hXone : 1 ≤ X := (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans hX
    have hlogX : 1 ≤ Real.log X := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hX
    have hlogXpos : 0 < Real.log X := by linarith
    have hpownu : 1 ≤ X ^ ν := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hXone hν.le
    have hQ : 1 ≤ ⌊X ^ ν⌋₊ := (Nat.one_le_floor_iff _).mpr hpownu
    intro k hk
    have hklow : X ^ b ≤ (k : ℝ) := hf.trans (by exact_mod_cast hk)
    have hkheight : max x₀ 2 ≤ (k : ℝ) := hh.trans hklow
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      have := (le_max_right _ _).trans hkheight
      linarith
    have hpower : X ^ ν ≤ (k : ℝ) ^ δ := by
      calc
        X ^ ν ≤ X ^ (b * δ) := Real.rpow_le_rpow_of_exponent_le hXone hmargin
        _ = (X ^ b) ^ δ := Real.rpow_mul hXpos.le b δ
        _ ≤ (k : ℝ) ^ δ :=
          Real.rpow_le_rpow (Real.rpow_nonneg hXpos.le _) hklow hδ.le
    have hcut : ⌊X ^ ν⌋₊ ≤ ⌊(k : ℝ) ^ ((1 : ℝ) / 2 - ε)⌋₊ := by
      have heq : (1 : ℝ) / 2 - ε = δ := by dsimp [ε]; ring
      rw [heq]
      exact Nat.floor_mono hpower
    have hlogk : b * Real.log X ≤ Real.log (k : ℝ) := by
      simpa only [Real.log_rpow hXpos] using
        Real.log_le_log (Real.rpow_pos_of_pos hXpos b) hklow
    have hbasepos : 0 < b * Real.log X := mul_pos hb hlogXpos
    have hdenpos : 0 < (b * Real.log X) ^ L := Real.rpow_pos_of_pos hbasepos _
    have hdenle : (b * Real.log X) ^ L ≤ (Real.log (k : ℝ)) ^ L :=
      Real.rpow_le_rpow hbasepos.le hlogk hL.le
    have hBVscaled : bvSum (k : ℝ) ε ≤ C * ((k : ℝ) / (b * Real.log X) ^ L) :=
      (hBV (k : ℝ) ((le_max_left _ _).trans hkheight)).trans
        (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left hkpos.le hdenpos hdenle) hC.le)
    have hproduct : (∑ q ∈ Icc 1 ⌊X ^ ν⌋₊, recenteredChebyshevError (k : ℝ) q) ≤
        (C * ((k : ℝ) / (b * Real.log X) ^ L)) * (S * (Real.log X) ^ 2) :=
      (sum_recenteredChebyshevError_le_bvSum X ν ε k hQ hcut).trans
        (mul_le_mul hBVscaled (one_add_divisorPhiMoment_zero_le_log_sq hX hν)
          (add_nonneg zero_le_one (divisorPhiMoment_nonneg X 0 ν)) (by positivity))
    have hidentity : (b * Real.log X) ^ L =
        b ^ L * ((Real.log X) ^ A * (Real.log X) ^ 2) := by
      rw [Real.mul_rpow hb.le hlogXpos.le]
      congr 1
      dsimp [L]
      rw [Real.rpow_add hlogXpos, Real.rpow_two]
    have hcalc : (C * ((k : ℝ) / (b * Real.log X) ^ L)) * (S * (Real.log X) ^ 2) =
        Cb * k / (Real.log X) ^ A := by
      rw [hidentity]
      dsimp [Cb]
      have hbp : 0 < b ^ L := Real.rpow_pos_of_pos hb _
      have hlp : 0 < (Real.log X) ^ A := Real.rpow_pos_of_pos hlogXpos _
      field_simp
    exact hproduct.trans_eq hcalc
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp hfinal
  exact ⟨Cb, X₀, hCb, hX₀⟩

theorem reciprocalPartialSummationWeight_power_bound (P : ErdosStraus.Params) (X : ℝ)
    (hX : Real.exp 1 ≤ X) (hm : 2 ≤ ⌊X ^ P.β⌋₊)
    (hmn : ⌊X ^ P.β⌋₊ < ⌊X ^ (1 - P.σ)⌋₊) :
    reciprocalPartialSummationWeight ⌊X ^ P.β⌋₊ ⌊X ^ (1 - P.σ)⌋₊ ≤
      (3 + (1 - P.σ)) / P.β := by
  let m : ℕ := ⌊X ^ P.β⌋₊
  let n : ℕ := ⌊X ^ (1 - P.σ)⌋₊
  have hXpos : 0 < X := (Real.exp_pos _).trans_le hX
  have hlogX : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hX
  have hκ : 0 < 1 - P.σ := P.β_pos.trans P.β_lt_one_sub_σ
  have hlogmpos : 0 < Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m + 1 by omega))
  have hlogm : P.β * Real.log X ≤ Real.log ((m + 1 : ℕ) : ℝ) := by
    have hlt := Nat.lt_floor_add_one (X ^ P.β)
    have hle : X ^ P.β ≤ ((m + 1 : ℕ) : ℝ) := by
      simpa only [m, Nat.cast_add, Nat.cast_one] using hlt.le
    simpa only [Real.log_rpow hXpos] using
      Real.log_le_log (Real.rpow_pos_of_pos hXpos _) hle
  have hlogn : Real.log (n : ℝ) ≤ (1 - P.σ) * Real.log X := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    simpa only [Real.log_rpow hXpos] using Real.log_le_log hnpos
      (Nat.floor_le (Real.rpow_nonneg hXpos.le (1 - P.σ)))
  have hcoef : 0 < (3 + (1 - P.σ)) / P.β := div_pos (by linarith) P.β_pos
  have hcancel : ((3 + (1 - P.σ)) / P.β) * P.β = 3 + (1 - P.σ) := by
    field_simp [ne_of_gt P.β_pos]
  have hscaled := mul_le_mul_of_nonneg_left hlogm hcoef.le
  have hnum : 3 + Real.log (n : ℝ) ≤ (3 + (1 - P.σ)) * Real.log X := by
    nlinarith
  apply (reciprocalPartialSummationWeight_le hm hmn).trans
  apply (div_le_iff₀ hlogmpos).mpr
  nlinarith [hscaled]

/-- The maximal Bombieri–Vinogradov theorem implies `∑_{q ≤ X^ν} g_q ≪ (log X)^{-A}` for
`0 < ν < β/2` and `A > 0`. -/
theorem reciprocalBV_unweighted_of_bv (hbv : BombieriVinogradovMaximalForm)
    (P : ErdosStraus.Params) (ν A : ℝ) (hν : 0 < ν) (hνβ : ν < P.β / 2) (hA : 0 < A) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      (∑ q ∈ Icc 1 ⌊X ^ ν⌋₊, reducedClassPrimeErrorMax P X q) ≤
        C / (Real.log X) ^ A := by
  obtain ⟨C, X₁, hC, hlocal⟩ := recenteredChebyshevError_sum_uniform_of_bv
    hbv P.β_pos hν hνβ hA
  let H : ℝ := (3 + (1 - P.σ)) / P.β
  have hH : 0 < H := div_pos (by
    have := P.β_pos.trans P.β_lt_one_sub_σ
    linarith) P.β_pos
  have hstrict := eventually_rpow_lt_floor_rpow P.β_pos P.β_lt_one_sub_σ
  have hlarge : ∀ᶠ X : ℝ in Filter.atTop, (2 : ℝ) ≤ X ^ P.β :=
    (tendsto_rpow_atTop P.β_pos).eventually (Filter.eventually_ge_atTop 2)
  have hfinal : ∀ᶠ X : ℝ in Filter.atTop,
      (∑ q ∈ Icc 1 ⌊X ^ ν⌋₊, reducedClassPrimeErrorMax P X q) ≤
        (C * H) / (Real.log X) ^ A := by
    filter_upwards [hstrict, hlarge, Filter.eventually_ge_atTop X₁,
      Filter.eventually_ge_atTop (Real.exp 1)] with X hs hl hX₁ hX
    have hXpos : 0 < X := (Real.exp_pos _).trans_le hX
    have hlogX : 1 ≤ Real.log X := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hX
    have hm : 2 ≤ ⌊X ^ P.β⌋₊ :=
      (Nat.le_floor_iff (Real.rpow_nonneg hXpos.le P.β)).mpr (by exact_mod_cast hl)
    have hmn : ⌊X ^ P.β⌋₊ < ⌊X ^ (1 - P.σ)⌋₊ := by
      have hmfloor := Nat.floor_le (Real.rpow_nonneg hXpos.le P.β)
      exact_mod_cast hmfloor.trans_lt hs
    have hD : 0 ≤ C / (Real.log X) ^ A :=
      div_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans hlogX) A)
    have hsum := sum_reducedClassPrimeErrorMax_le_local_linear P X hXpos.le
      ⌊X ^ ν⌋₊ (C / (Real.log X) ^ A) hm hmn (by
        intro k hk
        have hh := hlocal X hX₁ k (Finset.mem_Icc.mp hk).1
        convert hh using 1
        ring)
    have hweight := reciprocalPartialSummationWeight_power_bound P X hX hm hmn
    have hresult := hsum.trans (mul_le_mul_of_nonneg_left hweight hD)
    refine hresult.trans_eq ?_
    ring
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp hfinal
  exact ⟨C * H, X₀, mul_pos hC hH, hX₀⟩

/-- `∑_{q ≤ X^ν} g_q ≪ (log X)^{-A}` for `0 < ν < β/2` and `A > 0`. -/
theorem reciprocalBV_unweighted (P : ErdosStraus.Params) (ν A : ℝ)
    (hν : 0 < ν) (hνβ : ν < P.β / 2) (hA : 0 < A) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      (∑ q ∈ Icc 1 ⌊X ^ ν⌋₊, reducedClassPrimeErrorMax P X q) ≤
        C / (Real.log X) ^ A :=
  reciprocalBV_unweighted_of_bv standard_bombieri_vinogradov_maximal_form P ν A hν hνβ hA

end

/-! ## The bound `g_q ≪ log X / φ(q)` -/

section

open scoped BigOperators
open Estimates

theorem btRecip_le_progressionRecip (P : ErdosStraus.Params) (X : ℝ) (q a : ℕ) :
    btRecip P X q a ≤ progressionRecip q a (X ^ P.β) (X ^ (1 - P.σ)) := by
  classical
  unfold btRecip progressionRecip
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,
      (Finset.mem_filter.mp hp).2.2⟩
  · intro p _ _
    positivity

/-- Dropping primality, the bound (7) for progressions gives `2 log X/φ(q)`. -/
theorem btRecip_le_log_div_totient (P : ErdosStraus.Params) {X : ℝ}
    (hX : Real.exp 1 ≤ X) {q : ℕ} (hq : 0 < q)
    (hqX : (q : ℝ) ≤ X ^ P.β) (a : ℕ) :
    btRecip P X q a ≤ 2 * Real.log X / (Nat.totient q : ℝ) := by
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hlog : 1 ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hX
  have hXone : 1 < X := by
    have : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    exact this.trans_le hX
  have hA : 0 < X ^ P.β := Real.rpow_pos_of_pos hXpos _
  have hB : X ^ P.β < X ^ (1 - P.σ) :=
    Real.rpow_lt_rpow_of_exponent_lt hXone P.β_lt_one_sub_σ
  have hphi : 0 < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hphiq : (Nat.totient q : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hinv : (1 : ℝ) / (q : ℝ) ≤ 1 / (Nat.totient q : ℝ) :=
    one_div_le_one_div_of_le hphi hphiq
  have hlogratio : Real.log (X ^ (1 - P.σ) / X ^ P.β) ≤ Real.log X := by
    rw [Real.log_div (Real.rpow_pos_of_pos hXpos _).ne' hA.ne',
      Real.log_rpow hXpos, Real.log_rpow hXpos]
    nlinarith [P.σ_pos, P.β_pos]
  calc
    btRecip P X q a ≤ 1 / X ^ P.β +
        (1 / (q : ℝ)) * Real.log (X ^ (1 - P.σ) / X ^ P.β) :=
      (btRecip_le_progressionRecip P X q a).trans
        (progressionRecip_le_log_plus_inv q a hq hA hB)
    _ ≤ 1 / (Nat.totient q : ℝ) +
        (1 / (Nat.totient q : ℝ)) * Real.log X := by
      apply add_le_add
      · exact (one_div_le_one_div_of_le hqpos hqX).trans hinv
      · exact (mul_le_mul_of_nonneg_left hlogratio (by positivity)).trans
          (mul_le_mul_of_nonneg_right hinv (by linarith))
    _ ≤ 2 * Real.log X / (Nat.totient q : ℝ) := by
      rw [one_div_mul_eq_div, ← add_div]
      apply div_le_div_of_nonneg_right _ hphi.le
      linarith

theorem reducedClassPrimeErrorMax_le_log_div_totient (P : ErdosStraus.Params)
    {X : ℝ} (hX : Real.exp 1 ≤ X) {q : ℕ} (hq : 0 < q)
    (hqX : (q : ℝ) ≤ X ^ P.β) :
    reducedClassPrimeErrorMax P X q ≤ 4 * Real.log X / (Nat.totient q : ℝ) := by
  classical
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hXone : 1 ≤ X := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hX
  have hAone : (1 : ℝ) ≤ X ^ P.β := Real.one_le_rpow hXone P.β_pos.le
  have hphi : 0 < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hXone
  have hone := btRecip_le_log_div_totient P hX Nat.zero_lt_one (by simpa using hAone) 0
  simp only [Nat.totient_one, Nat.cast_one, div_one] at hone
  unfold reducedClassPrimeErrorMax
  rw [Finset.fold_max_le]
  refine ⟨by positivity, ?_⟩
  intro a _
  have ha := btRecip_le_log_div_totient P hX hq hqX a
  have href : (1 / (Nat.totient q : ℝ)) * btRecip P X 1 0 ≤
      2 * Real.log X / (Nat.totient q : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left hone (by positivity : (0 : ℝ) ≤ 1 / (Nat.totient q : ℝ))
  calc
    |btRecip P X q a - (1 / (Nat.totient q : ℝ)) * btRecip P X 1 0|
        ≤ |btRecip P X q a| + |(1 / (Nat.totient q : ℝ)) * btRecip P X 1 0| :=
      abs_sub _ _
    _ = btRecip P X q a + (1 / (Nat.totient q : ℝ)) * btRecip P X 1 0 := by
      rw [abs_of_nonneg (btRecip_nonneg P X q a),
        abs_of_nonneg (mul_nonneg (by positivity) (btRecip_nonneg P X 1 0))]
    _ ≤ 2 * Real.log X / (Nat.totient q : ℝ) +
        2 * Real.log X / (Nat.totient q : ℝ) := add_le_add ha href
    _ = 4 * Real.log X / (Nat.totient q : ℝ) := by ring

/-- `∑_{q ≤ X^ν} τ(q)^K g_q ≤ 4 log X ∑_{q ≤ X^ν} τ(q)^K/φ(q)` for `ν ≤ β`. -/
theorem weightedBVSum_nat_le_log_mul_moment (P : ErdosStraus.Params) (K : ℕ)
    {X ν : ℝ} (hX : Real.exp 1 ≤ X) (hν : ν ≤ P.β) :
    weightedBVSum P X (K : ℝ) ν ≤ 4 * Real.log X * divisorPhiMoment X K ν := by
  classical
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hXone : 1 ≤ X := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hX
  unfold weightedBVSum divisorPhiMoment
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
  have hqX : (q : ℝ) ≤ X ^ P.β := by
    calc
      (q : ℝ) ≤ (⌊X ^ ν⌋₊ : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hq).2
      _ ≤ X ^ ν := Nat.floor_le (Real.rpow_nonneg hXpos.le _)
      _ ≤ X ^ P.β := Real.rpow_le_rpow_of_exponent_le hXone hν
  have hb := mul_le_mul_of_nonneg_left
    (reducedClassPrimeErrorMax_le_log_div_totient P hX hqpos hqX)
    (show (0 : ℝ) ≤ (tau q : ℝ) ^ (K : ℝ) by positivity)
  convert hb using 1
  simp only [Real.rpow_natCast, Nat.cast_pow]
  ring

end

/-! ## Divisor weights -/

section

open scoped BigOperators
open Finset Estimates

/-- Cauchy–Schwarz: if `2·Cw ≤ K`, then
`(∑ τ(q)^{Cw} g_q)² ≤ (∑ g_q)(∑ τ(q)^K g_q)`, the sums over `q ≤ X^ν`. -/
theorem weightedBVSum_sq_le_nat_moment (P : ErdosStraus.Params) (X ν Cw : ℝ)
    (K : ℕ) (hK : 2 * Cw ≤ (K : ℝ)) :
    weightedBVSum P X Cw ν ^ 2 ≤
      weightedBVSum P X 0 ν * weightedBVSum P X (K : ℝ) ν := by
  classical
  have hcs :
      (∑ q ∈ Icc (1 : ℕ) ⌊X ^ ν⌋₊,
        (tau q : ℝ) ^ Cw * reducedClassPrimeErrorMax P X q) ^ 2 ≤
      (∑ q ∈ Icc (1 : ℕ) ⌊X ^ ν⌋₊, reducedClassPrimeErrorMax P X q) *
        (∑ q ∈ Icc (1 : ℕ) ⌊X ^ ν⌋₊,
          ((tau q : ℝ) ^ Cw) ^ 2 * reducedClassPrimeErrorMax P X q) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro q _
      exact reducedClassPrimeErrorMax_nonneg _ _ _
    · intro q _
      exact mul_nonneg (sq_nonneg _) (reducedClassPrimeErrorMax_nonneg _ _ _)
    · intro q _
      exact le_of_eq (by ring)
  have hdom :
      (∑ q ∈ Icc (1 : ℕ) ⌊X ^ ν⌋₊,
        ((tau q : ℝ) ^ Cw) ^ 2 * reducedClassPrimeErrorMax P X q) ≤
      weightedBVSum P X (K : ℝ) ν := by
    unfold weightedBVSum
    apply Finset.sum_le_sum
    intro q hq
    have hqpos : 0 < q := by have := (Finset.mem_Icc.mp hq).1; omega
    have hone : 1 ∈ q.divisors := Nat.mem_divisors.mpr ⟨one_dvd _, ne_of_gt hqpos⟩
    have htaupos : 0 < tau q := Finset.card_pos.mpr ⟨1, hone⟩
    have htauone : (1 : ℝ) ≤ (tau q : ℝ) := by exact_mod_cast htaupos
    have hpow : ((tau q : ℝ) ^ Cw) ^ 2 = (tau q : ℝ) ^ (2 * Cw) := by
      have hh := Real.rpow_mul (Nat.cast_nonneg (tau q) : (0 : ℝ) ≤ tau q) Cw 2
      rw [Real.rpow_two, mul_comm Cw 2] at hh
      exact hh.symm
    rw [hpow]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le htauone hK)
      (reducedClassPrimeErrorMax_nonneg _ _ _)
  unfold weightedBVSum
  simp only [Real.rpow_zero, one_mul]
  exact hcs.trans (mul_le_mul_of_nonneg_left hdom
    (Finset.sum_nonneg (fun q _ => reducedClassPrimeErrorMax_nonneg _ _ _)))

/-- The maximal Bombieri–Vinogradov theorem implies
`∑_{q ≤ X^ν} τ(q)^{Cw} g_q ≪ (log X)^{-A}` for every fixed `Cw ≥ 0`, `A > 0` and
`0 < ν < β/2`. -/
theorem reciprocalBV_weighted_of_bv (hbv : BombieriVinogradovMaximalForm) :
    WeightedReciprocalBombieriVinogradov := by
  intro P ν A Cw hν hνβ hA _hCw
  let K : ℕ := ⌈2 * Cw⌉₊
  have hK : 2 * Cw ≤ (K : ℝ) := Nat.le_ceil _
  obtain ⟨Cd, E, Xd, hCd, hmoment⟩ := divisor_phi_moment_general K ν hν
  let H : ℝ := |E| + 1
  let B : ℝ := 2 * A + H
  have hB : 0 < B := by dsimp [B, H]; positivity
  obtain ⟨C₀, Xb, hC₀, hunweighted⟩ := reciprocalBV_unweighted_of_bv hbv P ν B hν hνβ hB
  let M : ℝ := C₀ * (4 * Cd)
  have hM : 0 < M := mul_pos hC₀ (by positivity)
  refine ⟨M + 1, max Xd (max Xb (Real.exp 1)), by positivity, ?_⟩
  intro X hX
  have hXd : Xd ≤ X := (le_max_left _ _).trans hX
  have hXb : Xb ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hX)
  have hXe : Real.exp 1 ≤ X := (le_max_right _ _).trans ((le_max_right _ _).trans hX)
  have hXpos : 0 < X := (Real.exp_pos _).trans_le hXe
  have hlog : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hXe
  have hlogpos : 0 < Real.log X := by linarith
  have hνβfull : ν ≤ P.β := by linarith [P.β_pos]
  have hhigh : weightedBVSum P X (K : ℝ) ν ≤
      (4 * Cd) * (Real.log X) ^ H := by
    have hmomentX : divisorPhiMoment X K ν ≤ Cd * (Real.log X) ^ |E| :=
      ((le_abs_self _).trans (hmoment X hXd)).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hlog (le_abs_self E)) hCd.le)
    calc
      weightedBVSum P X (K : ℝ) ν ≤
          4 * Real.log X * divisorPhiMoment X K ν :=
        weightedBVSum_nat_le_log_mul_moment P K hXe hνβfull
      _ ≤ 4 * Real.log X * (Cd * (Real.log X) ^ |E|) :=
        mul_le_mul_of_nonneg_left hmomentX (by positivity)
      _ = (4 * Cd) * (Real.log X) ^ H := by
        dsimp [H]
        rw [Real.rpow_add hlogpos, Real.rpow_one]
        ring
  have hzero : weightedBVSum P X 0 ν ≤ C₀ / (Real.log X) ^ B := by
    simpa only [weightedBVSum, Real.rpow_zero, one_mul] using hunweighted X hXb
  have hsquared := weightedBVSum_sq_le_nat_moment P X ν Cw K hK
  have hproduct : weightedBVSum P X Cw ν ^ 2 ≤
      (C₀ / (Real.log X) ^ B) * ((4 * Cd) * (Real.log X) ^ H) :=
    hsquared.trans (mul_le_mul hzero hhigh
      (weightedBVSum_nonneg P X (K : ℝ) ν) (by positivity))
  have hden : (Real.log X) ^ B = ((Real.log X) ^ A) ^ 2 * (Real.log X) ^ H := by
    dsimp [B]
    rw [Real.rpow_add hlogpos]
    have hpow := Real.rpow_mul hlogpos.le A 2
    rw [mul_comm A 2, Real.rpow_two] at hpow
    rw [hpow]
  have hcalc : (C₀ / (Real.log X) ^ B) * ((4 * Cd) * (Real.log X) ^ H) =
      M * (1 / (Real.log X) ^ A) ^ 2 := by
    rw [hden]
    dsimp [M]
    have hpowA : 0 < (Real.log X) ^ A := Real.rpow_pos_of_pos hlogpos _
    have hpowH : 0 < (Real.log X) ^ H := Real.rpow_pos_of_pos hlogpos _
    field_simp
  rw [hcalc] at hproduct
  have hconstant : M ≤ (M + 1) ^ 2 := by nlinarith [sq_nonneg M]
  have htarget : weightedBVSum P X Cw ν ≤ (M + 1) * (1 / (Real.log X) ^ A) := by
    apply le_of_sq_le_sq _ (by positivity)
    have hmajor := hproduct.trans (mul_le_mul_of_nonneg_right hconstant (sq_nonneg _))
    convert hmajor using 1
    ring
  rw [abs_of_nonneg (weightedBVSum_nonneg _ _ _ _)]
  simpa only [Real.rpow_neg hlogpos.le, one_div] using htarget

/-- Lemma 3.8 with weights `τ(q)^C` and any power of `log X`. -/
theorem reciprocalBV_weighted : WeightedReciprocalBombieriVinogradov :=
  reciprocalBV_weighted_of_bv standard_bombieri_vinogradov_maximal_form

end

end ErdosStraus.PrimeEstimates

/-! ## Reciprocal sums over a window of primes -/

namespace ErdosStraus.PrimeEstimates.Mertens

open Filter Finset Real
open scoped BigOperators Topology

/-- For `0 < a < b`, `∑_{X^a < p ≤ X^b} 1/p = log(b/a) + O(1/log X)` (Lemma 3.1). -/
theorem prime_reciprocal_window {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      |(∑ p ∈ (Estimates.natWindow (X ^ a) (X ^ b)).filter Nat.Prime,
          (1 : ℝ) / p) - log (b / a)| ≤ C / log X := by
  obtain ⟨C, hC, h⟩ := mertensSecond
  have hb : 0 < b := ha.trans hab
  refine ⟨C * (1 / a + 1 / b), exp (max 1 (log 2 / a)), by positivity, ?_⟩
  intro X hX
  have hXp : 0 < X := (exp_pos _).trans_le hX
  have hlog : max 1 (log 2 / a) ≤ log X := (Real.le_log_iff_exp_le hXp).mpr hX
  have hlog1 : 1 ≤ log X := (le_max_left _ _).trans hlog
  have hlogp : 0 < log X := zero_lt_one.trans_le hlog1
  have hX1 : 1 ≤ X := (Real.log_nonneg_iff hXp).mp hlogp.le
  have hpowap : 0 < X ^ a := rpow_pos_of_pos hXp _
  have hpowbp : 0 < X ^ b := rpow_pos_of_pos hXp _
  have hpow2 : (2 : ℝ) ≤ X ^ a := by
    apply (log_le_log_iff (by norm_num) hpowap).mp
    rw [log_rpow hXp]
    have hh := (le_max_right 1 (log 2 / a)).trans hlog
    simpa only [mul_comm] using (div_le_iff₀ ha).mp hh
  have hpowers : X ^ a ≤ X ^ b := rpow_le_rpow_of_exponent_le hX1 hab.le
  have hpowerb2 := hpow2.trans hpowers
  have hw : (∑ p ∈ (Estimates.natWindow (X ^ a) (X ^ b)).filter Nat.Prime,
      (1 : ℝ) / p) = primeReciprocalSum ⌊X ^ b⌋₊ - primeReciprocalSum ⌊X ^ a⌋₊ := by
    rw [natWindow_eq_Ioc_floor hpowap.le]
    exact primeReciprocalSum_sub (Nat.floor_mono hpowers)
  have hlogdiff : log (log (X ^ b)) - log (log (X ^ a)) = log (b / a) := by
    rw [log_rpow hXp, log_rpow hXp, log_mul hb.ne' hlogp.ne',
      log_mul ha.ne' hlogp.ne', log_div hb.ne' ha.ne']
    ring
  have heq : primeReciprocalSum ⌊X ^ b⌋₊ - primeReciprocalSum ⌊X ^ a⌋₊ - log (b / a) =
      (primeReciprocalSum ⌊X ^ b⌋₊ - (log (log (X ^ b)) + mertensSecondConstant)) -
        (primeReciprocalSum ⌊X ^ a⌋₊ - (log (log (X ^ a)) + mertensSecondConstant)) := by
    rw [← hlogdiff]
    ring
  rw [hw, heq]
  calc
    _ ≤ |primeReciprocalSum ⌊X ^ b⌋₊ - (log (log (X ^ b)) + mertensSecondConstant)| +
        |primeReciprocalSum ⌊X ^ a⌋₊ - (log (log (X ^ a)) + mertensSecondConstant)| := abs_sub _ _
    _ ≤ C / log (X ^ b) + C / log (X ^ a) := add_le_add (h _ hpowerb2) (h _ hpow2)
    _ = (C * (1 / a + 1 / b)) / log X := by
      rw [log_rpow hXp, log_rpow hXp]
      field_simp
      ring

theorem primeRecipWindow_rate (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      |Estimates.primeRecipWindow P X - log ((1 - P.σ) / P.β)| ≤ C / log X := by
  simpa only [Estimates.primeRecipWindow] using
    prime_reciprocal_window P.β_pos P.β_lt_one_sub_σ

theorem primeRecipWindow_limit (P : Params) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      |Estimates.primeRecipWindow P X - log ((1 - P.σ) / P.β)| ≤ ε := by
  obtain ⟨C, T, hC, h⟩ := primeRecipWindow_rate P
  refine ⟨max T (exp (C / ε + 1)), ?_⟩
  intro X hX
  have hXe : exp (C / ε + 1) ≤ X := (le_max_right _ _).trans hX
  have hXp : 0 < X := (exp_pos _).trans_le hXe
  have hl : C / ε + 1 ≤ log X := (Real.le_log_iff_exp_le hXp).mpr hXe
  have hlp : 0 < log X := (show 0 < C / ε + 1 by positivity).trans_le hl
  have hh : C / log X ≤ ε := by
    apply (div_le_iff₀ hlp).mpr
    have hdiv := (div_le_iff₀ hε).mp (show C / ε ≤ log X by linarith)
    simpa only [mul_comm] using hdiv
  exact (h X ((le_max_left _ _).trans hX)).trans hh

end ErdosStraus.PrimeEstimates.Mertens

namespace ErdosStraus.PrimeEstimates

section

open scoped BigOperators Classical
open Finset Estimates

/-- `𝒫_X ≥ log((1-σ)/β)/2` for large `X`. -/
theorem primeRecipWindow_mertens_lower :
    PrimeRecipWindowMertensLowerBound := by
  intro P
  have hratio : 1 < (1 - P.σ) / P.β :=
    (lt_div_iff₀ P.β_pos).mpr (by simpa using P.β_lt_one_sub_σ)
  have hL : 0 < Real.log ((1 - P.σ) / P.β) := Real.log_pos hratio
  obtain ⟨X₀, h⟩ := Mertens.primeRecipWindow_limit P
    (Real.log ((1 - P.σ) / P.β) / 2) (half_pos hL)
  refine ⟨Real.log ((1 - P.σ) / P.β) / 2, X₀, half_pos hL, ?_⟩
  intro X hX
  rw [btRecip_mod_one_eq_primeRecipWindow]
  have hh := (abs_le.mp (h X hX)).1
  linarith

end

/-! ## Theorem 3.7 for `π(x; q, a)` -/

section

open Classical Finset Estimates Filter

/-- `π(x; q, a)`, the number of primes `p ≤ x` with `p ≡ a (mod q)`. -/
noncomputable def primeCountAP (x : ℝ) (q a : ℕ) : ℕ :=
  ((Icc 2 ⌊x⌋₊).filter (fun p => p.Prime ∧ congMod p a q)).card

/-- `π(x)`, the number of primes `p ≤ x`. -/
noncomputable def primeCount (x : ℝ) : ℕ :=
  ((Icc 2 ⌊x⌋₊).filter Nat.Prime).card

/-- `max_{(a,q)=1} |π(x; q, a) - π(x)/φ(q)|`, with `a` running over `1 ≤ a ≤ q`. -/
noncomputable def primeCountError (x : ℝ) (q : ℕ) : ℝ :=
  ((Icc 1 q).filter (fun a => Nat.Coprime a q)).fold max 0
    (fun a => |(primeCountAP x q a : ℝ) - (primeCount x : ℝ) / Nat.totient q|)

/-- `∑_{q ≤ x^ϑ} max_{(a,q)=1} |π(x; q, a) - π(x)/φ(q)|`. -/
noncomputable def primeCountErrorSum (x ϑ : ℝ) : ℝ :=
  ∑ q ∈ Icc 1 ⌊x ^ ϑ⌋₊, primeCountError x q

/-- `1/log n`. -/
noncomputable def inverseLogWeight (n : ℕ) : ℝ := 1 / Real.log n

theorem inverseLogWeight_nonneg {n : ℕ} (hn : 1 ≤ n) : 0 ≤ inverseLogWeight n := by
  exact one_div_nonneg.mpr (Real.log_nonneg (by exact_mod_cast hn))

theorem inverseLogWeight_antitone {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    inverseLogWeight n ≤ inverseLogWeight m := by
  exact one_div_le_one_div_of_le
    (Real.log_pos (by exact_mod_cast (show 1 < m by omega)))
    (Real.log_le_log (by positivity) (by exact_mod_cast hmn))

theorem inverseLogWeight_mul_primeLogCoefficient (q a n : ℕ) :
    inverseLogWeight n * primeLogCoefficient q a n =
      if n.Prime ∧ congMod n a q then (1 : ℝ) else 0 := by
  unfold primeLogCoefficient inverseLogWeight
  split_ifs with h
  · exact one_div_mul_cancel (ne_of_gt (Real.log_pos (by exact_mod_cast h.1.one_lt)))
  · simp

/-- Summation by parts with the weight `1/log n`, which turns `ϑ(x; q, a)` into
`π(x; q, a)`. -/
theorem primeCountAP_error_le_bvError {x : ℝ} (hx : 2 ≤ x) {q a : ℕ}
    (ha : Nat.Coprime a q) :
    |(primeCountAP x q a : ℝ) - (primeCount x : ℝ) / Nat.totient q| ≤
      (2 / Real.log 2) * (bvError x q + bvError x 1 / Nat.totient q) := by
  classical
  let n := ⌊x⌋₊
  let c : ℕ → ℝ := fun k => primeLogCoefficient q a k -
    primeLogCoefficient 1 0 k / (Nat.totient q : ℝ)
  have hn : 2 ≤ n := Nat.le_floor (by simpa using hx)
  have hprefix : ∀ k ∈ Icc 1 n, |∑ j ∈ Icc 0 k, c j| ≤
      bvError x q + bvError x 1 / (Nat.totient q : ℝ) := by
    intro k hk
    by_cases hk2 : 2 ≤ k
    · have hkx : (k : ℝ) ≤ x :=
        (show (k : ℝ) ≤ n by exact_mod_cast (mem_Icc.mp hk).2).trans (Nat.floor_le (by linarith))
      simpa only [c, Finset.sum_sub_distrib, ← Finset.sum_div,
        ← thetaAP_nat_eq_prefix] using thetaAP_recenter_error_le ha
          (by exact_mod_cast hk2) hkx
    · have hk1 : k = 1 := by have := (mem_Icc.mp hk).1; omega
      subst k
      norm_num [c, primeLogCoefficient, Finset.sum_Icc_succ_top] at *
      exact add_nonneg (bvError_nonneg _ _)
        (div_nonneg (bvError_nonneg _ _) (Nat.cast_nonneg _))
  have hab := abs_sum_Ioc_mul_le_of_partial c inverseLogWeight (show 1 < n by omega)
    (inverseLogWeight_nonneg (by omega))
    (fun k hk => inverseLogWeight_antitone (by have := (mem_Ico.mp hk).1; omega) (Nat.le_succ _))
    (fun k hk => abs_sum_Ioc_le_two_of_prefix c (mem_Ioc.mp hk).1.le
      (fun j hj => hprefix j (mem_Icc.mpr ⟨(mem_Icc.mp hj).1,
        (mem_Icc.mp hj).2.trans (mem_Ioc.mp hk).2⟩)))
  have heq : (∑ k ∈ Ioc 1 n, inverseLogWeight k * c k) =
      (primeCountAP x q a : ℝ) - (primeCount x : ℝ) / Nat.totient q := by
    have hsets : Ioc 1 n = Icc 2 n := by ext k; simp; omega
    simp only [c, mul_sub, ← mul_div_assoc, Finset.sum_sub_distrib,
      ← Finset.sum_div, inverseLogWeight_mul_primeLogCoefficient, hsets,
      primeCountAP, primeCount, Finset.sum_boole, congMod, Nat.mod_one, and_true]
    simp [n]
    convert Finset.sum_boole (R := ℝ) (fun p : ℕ => Nat.Prime p ∧ p % q = a % q)
      (Icc 2 ⌊x⌋₊) using 1 <;> congr 1
    · funext p
      congr
    · congr 1
      congr
  rw [heq] at hab
  convert hab using 1
  simp only [inverseLogWeight]
  norm_num
  ring

theorem primeCountError_le_bvError {x : ℝ} (hx : 2 ≤ x) (q : ℕ) :
    primeCountError x q ≤
      (2 / Real.log 2) * (bvError x q + bvError x 1 / Nat.totient q) := by
  unfold primeCountError
  rw [Finset.fold_max_le]
  refine ⟨mul_nonneg (by positivity) (add_nonneg (bvError_nonneg _ _)
    (div_nonneg (bvError_nonneg _ _) (Nat.cast_nonneg _))), ?_⟩
  exact fun a ha => primeCountAP_error_le_bvError hx (mem_filter.mp ha).2

theorem primeCountErrorSum_le_bvSum {x ϑ : ℝ} (hx : 2 ≤ x)
    (hϑ : 0 < ϑ) :
    primeCountErrorSum x ϑ ≤ (2 / Real.log 2) *
      (bvSum x (1 / 2 - ϑ) * (1 + divisorPhiMoment x 0 ϑ)) := by
  have hQ : 1 ≤ ⌊x ^ ϑ⌋₊ := Nat.le_floor (by
    norm_num
    exact Real.one_le_rpow (by linarith) hϑ.le)
  have hone : bvError x 1 ≤ bvSum x (1 / 2 - ϑ) := by
    apply bvError_le_bvSum le_rfl
    simpa only [sub_sub_cancel] using hQ
  have hidentity : (∑ q ∈ Icc 1 ⌊x ^ ϑ⌋₊,
      (bvError x q + bvError x 1 / (Nat.totient q : ℝ))) =
      bvSum x (1 / 2 - ϑ) + bvError x 1 * divisorPhiMoment x 0 ϑ := by
    simp [bvSum, divisorPhiMoment, Finset.sum_add_distrib, Finset.mul_sum,
      sub_sub_cancel, div_eq_mul_inv]
  unfold primeCountErrorSum
  calc
    _ ≤ (2 / Real.log 2) * (∑ q ∈ Icc 1 ⌊x ^ ϑ⌋₊,
        (bvError x q + bvError x 1 / Nat.totient q)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun q _ => primeCountError_le_bvError hx q)
    _ = (2 / Real.log 2) *
        (bvSum x (1 / 2 - ϑ) + bvError x 1 * divisorPhiMoment x 0 ϑ) := by rw [hidentity]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by
      have hm := mul_le_mul_of_nonneg_right hone (divisorPhiMoment_nonneg x 0 ϑ)
      nlinarith) (by positivity)

theorem primeCountErrorSum_eventual (A ϑ : ℝ) (hA : 0 < A) (hϑ : 0 < ϑ)
    (hϑhalf : ϑ < 1 / 2) :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      primeCountErrorSum x ϑ ≤ C * (x / (Real.log x) ^ A) := by
  obtain ⟨C, x₀, hC, hbv⟩ := standard_bombieri_vinogradov_maximal_form
    (A + 2) (1 / 2 - ϑ) (by linarith) (by linarith)
  refine ⟨(2 / Real.log 2) * C * (1 + (ϑ + 1) ^ 2), max x₀ (Real.exp 1),
    by positivity, ?_⟩
  intro x hx
  have hxe : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hxpos : 0 < x := (Real.exp_pos _).trans_le hxe
  have hlog : 0 < Real.log x := by
    have hl : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hxe
    linarith
  have hx2 : 2 ≤ x := (le_of_lt (by nlinarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)] :
    (2 : ℝ) < Real.exp 1)).trans hxe
  have hstep := mul_le_mul (hbv x ((le_max_left _ _).trans hx))
    (one_add_divisorPhiMoment_zero_le_log_sq hxe hϑ)
    (add_nonneg zero_le_one (divisorPhiMoment_nonneg x 0 ϑ))
    (by positivity : 0 ≤ C * (x / (Real.log x) ^ (A + 2)))
  apply (primeCountErrorSum_le_bvSum hx2 hϑ).trans
  apply (mul_le_mul_of_nonneg_left hstep (by positivity)).trans_eq
  rw [Real.rpow_add hlog, Real.rpow_two]
  field_simp

theorem primeCount_le_floor (x : ℝ) : primeCount x ≤ ⌊x⌋₊ := by
  unfold primeCount
  apply (Finset.card_filter_le _ _).trans
  simp only [Nat.card_Icc]
  omega

theorem primeCountAP_le_floor (x : ℝ) (q a : ℕ) : primeCountAP x q a ≤ ⌊x⌋₊ := by
  unfold primeCountAP
  apply (Finset.card_filter_le _ _).trans
  simp only [Nat.card_Icc]
  omega

theorem primeCountError_le_two_mul {x : ℝ} (hx : 0 ≤ x) {q : ℕ} (hq : 1 ≤ q) :
    primeCountError x q ≤ 2 * x := by
  have hφ : (1 : ℝ) ≤ Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have hcount : (primeCount x : ℝ) ≤ x :=
    (show (primeCount x : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast primeCount_le_floor x).trans (Nat.floor_le hx)
  have hdiv : (primeCount x : ℝ) / Nat.totient q ≤ x :=
    (div_le_self (Nat.cast_nonneg _) hφ).trans hcount
  unfold primeCountError
  rw [Finset.fold_max_le]
  refine ⟨by positivity, ?_⟩
  intro a ha
  have hc : (primeCountAP x q a : ℝ) ≤ x :=
    (show (primeCountAP x q a : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast primeCountAP_le_floor x q a).trans
      (Nat.floor_le hx)
  have hc0 : (0 : ℝ) ≤ primeCountAP x q a := Nat.cast_nonneg _
  have hdiv0 : 0 ≤ (primeCount x : ℝ) / Nat.totient q := by positivity
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem primeCountErrorSum_le_two_mul {x ϑ : ℝ} (hx : 0 ≤ x) :
    primeCountErrorSum x ϑ ≤ 2 * x * x ^ ϑ := by
  unfold primeCountErrorSum
  calc
    _ ≤ ∑ _q ∈ Icc 1 ⌊x ^ ϑ⌋₊, 2 * x :=
      Finset.sum_le_sum (fun q hq => primeCountError_le_two_mul hx (mem_Icc.mp hq).1)
    _ = (⌊x ^ ϑ⌋₊ : ℝ) * (2 * x) := by simp
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_right (Nat.floor_le (Real.rpow_nonneg hx ϑ))
        (by positivity : 0 ≤ 2 * x)
      nlinarith

/-- Theorem 3.7: for `A > 0` and `0 < ϑ < 1/2`,
`∑_{q ≤ x^ϑ} max_{(a,q)=1} |π(x; q, a) - π(x)/φ(q)| ≪ x/(log x)^A` for `x ≥ 3`. -/
theorem bombieri_vinogradov_prime_count (A ϑ : ℝ) (hA : 0 < A)
    (hϑ : 0 < ϑ) (hϑhalf : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
      primeCountErrorSum x ϑ ≤ C * (x / (Real.log x) ^ A) := by
  obtain ⟨C, x₀, hC, hlarge⟩ := primeCountErrorSum_eventual A ϑ hA hϑ hϑhalf
  let T := max 3 x₀
  let D := 2 * T * T ^ ϑ * (Real.log T) ^ A
  have hT : 3 ≤ T := le_max_left _ _
  have hTpos : 0 < T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨max C D, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
  intro x hx
  have hxpos : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  by_cases hxt : T ≤ x
  · exact (hlarge x ((le_max_right _ _).trans hxt)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hxT : x ≤ T := le_of_lt (lt_of_not_ge hxt)
    have hpow : (Real.log x) ^ A ≤ (Real.log T) ^ A :=
      Real.rpow_le_rpow hlogx.le (Real.log_le_log hxpos hxT) hA.le
    have hmain : primeCountErrorSum x ϑ ≤ 2 * T * T ^ ϑ :=
      (primeCountErrorSum_le_two_mul hxpos.le).trans
        (mul_le_mul (by linarith) (Real.rpow_le_rpow hxpos.le hxT hϑ.le)
          (Real.rpow_nonneg hxpos.le _) (by linarith))
    have hratio : 1 ≤ (Real.log T) ^ A * (x / (Real.log x) ^ A) := by
      rw [← mul_div_assoc, le_div_iff₀ (by positivity : 0 < (Real.log x) ^ A)]
      have hprod : (Real.log T) ^ A ≤ (Real.log T) ^ A * x := by
        have hm := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ x by linarith)
          (Real.rpow_nonneg hlogT.le A)
        simpa only [mul_one] using hm
      simpa only [one_mul] using hpow.trans hprod
    have hbound : primeCountErrorSum x ϑ ≤ D * (x / (Real.log x) ^ A) := by
      apply hmain.trans
      have hm := mul_le_mul_of_nonneg_left hratio
        (show 0 ≤ 2 * T * T ^ ϑ by positivity)
      simpa [D, mul_assoc] using hm
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end

/-! ## Proof of Lemma 3.8 -/

section

open scoped BigOperators
open Finset Estimates Filter

/-- `∑_{q ≤ X^ν} τ(q)² g_q ≪ (log X)^5`, from `g_q ≪ log X/φ(q)` and
`∑_{q ≤ Q} τ(q)²/φ(q) ≪ (log Q)^4`. -/
theorem weightedBVSum_two_le_log_fifth (P : ErdosStraus.Params) (ν : ℝ) (hν : 0 < ν)
    (hνβ : ν ≤ P.β) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, Real.exp 1 ≤ X →
      weightedBVSum P X 2 ν ≤ C * (Real.log X) ^ 5 := by
  obtain ⟨D, hD, hmoment⟩ :=
    DivisorEstimates.exists_square_divisor_card_totient_moment_le_log_fourth
  refine ⟨4 * D * (Real.log 4 + ν) ^ 4, by positivity, fun X hX => ?_⟩
  have hX1 : 1 ≤ X := (Real.one_le_exp (by norm_num)).trans hX
  have hXpos : 0 < X := by linarith
  have hlog1 : 1 ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hlog0 : 0 ≤ Real.log X := by linarith
  have hpoint : ∀ q ∈ Icc (1 : ℕ) ⌊X ^ ν⌋₊,
      (tau q : ℝ) ^ (2 : ℝ) * reducedClassPrimeErrorMax P X q ≤
        4 * Real.log X * ((q.divisors.card : ℝ) ^ 2 / Nat.totient q) := by
    intro q hq
    obtain ⟨hq1, hqX⟩ := Finset.mem_Icc.mp hq
    have hqν : (q : ℝ) ≤ X ^ ν := (Nat.cast_le.mpr hqX).trans (Nat.floor_le (by positivity))
    have hqβ : (q : ℝ) ≤ X ^ P.β := hqν.trans (Real.rpow_le_rpow_of_exponent_le hX1 hνβ)
    have hg := reducedClassPrimeErrorMax_le_log_div_totient P hX hq1 hqβ
    have hτ : (tau q : ℝ) ^ (2 : ℝ) = (q.divisors.card : ℝ) ^ 2 := by
      rw [Real.rpow_two]; rfl
    rw [hτ]
    calc (q.divisors.card : ℝ) ^ 2 * reducedClassPrimeErrorMax P X q ≤
        (q.divisors.card : ℝ) ^ 2 * (4 * Real.log X / Nat.totient q) :=
          mul_le_mul_of_nonneg_left hg (by positivity)
      _ = _ := by ring
  have hQ : 2 ≤ max 2 (X ^ ν) := le_max_left _ _
  have hsum : (∑ q ∈ Icc (1 : ℕ) ⌊X ^ ν⌋₊, (q.divisors.card : ℝ) ^ 2 / Nat.totient q) ≤
      D * Real.log (2 * max 2 (X ^ ν)) ^ 4 := by
    refine le_trans ?_ (hmoment _ hQ)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.Icc_subset_Icc le_rfl (Nat.floor_mono (le_max_right _ _))
    · intro q _ _; positivity
  have hlogQ : Real.log (2 * max 2 (X ^ ν)) ≤ (Real.log 4 + ν) * Real.log X := by
    have h2X : 2 * max 2 (X ^ ν) ≤ 4 * X ^ ν := by
      have : (1 : ℝ) ≤ X ^ ν := Real.one_le_rpow hX1 hν.le
      rcases le_total 2 (X ^ ν) with h | h
      · rw [max_eq_right h]; nlinarith
      · rw [max_eq_left h]; nlinarith
    calc Real.log (2 * max 2 (X ^ ν)) ≤ Real.log (4 * X ^ ν) :=
          Real.log_le_log (by positivity) h2X
      _ = Real.log 4 + ν * Real.log X := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hXpos]
      _ ≤ (Real.log 4 + ν) * Real.log X := by
          have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
          nlinarith
  have hlogQ0 : 0 ≤ Real.log (2 * max 2 (X ^ ν)) :=
    Real.log_nonneg (by have := le_max_left 2 (X ^ ν); linarith)
  unfold weightedBVSum
  calc (∑ q ∈ Icc (1 : ℕ) ⌊X ^ ν⌋₊, (tau q : ℝ) ^ (2 : ℝ) * reducedClassPrimeErrorMax P X q)
      ≤ ∑ q ∈ Icc (1 : ℕ) ⌊X ^ ν⌋₊,
          4 * Real.log X * ((q.divisors.card : ℝ) ^ 2 / Nat.totient q) :=
        Finset.sum_le_sum hpoint
    _ = 4 * Real.log X *
          ∑ q ∈ Icc (1 : ℕ) ⌊X ^ ν⌋₊, (q.divisors.card : ℝ) ^ 2 / Nat.totient q := by
        rw [Finset.mul_sum]
    _ ≤ 4 * Real.log X * (D * ((Real.log 4 + ν) * Real.log X) ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hsum.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hlogQ0 hlogQ 4) hD.le)
    _ = 4 * D * (Real.log 4 + ν) ^ 4 * Real.log X ^ 5 := by ring

/-- Lemma 3.8: `∑_{q ≤ X^ν} τ(q) g_q ≪ (log X)^{-7}` for `0 < ν < β/2`. Cauchy–Schwarz
combines `∑ g_q ≪ (log X)^{-19}` with `∑ τ(q)² g_q ≪ (log X)^5`. -/
theorem reciprocalBV_divisor_weighted (P : ErdosStraus.Params) (ν : ℝ) (hν : 0 < ν)
    (hνβ : ν < P.β / 2) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      (∑ q ∈ Icc (1 : ℕ) ⌊X ^ ν⌋₊, (tau q : ℝ) * reducedClassPrimeErrorMax P X q) ≤
        C / (Real.log X) ^ 7 := by
  obtain ⟨C₁, X₁, hC₁, hunw⟩ := reciprocalBV_unweighted P ν 19 hν hνβ (by norm_num)
  obtain ⟨C₂, hC₂, hmom⟩ := weightedBVSum_two_le_log_fifth P ν hν
    (by linarith [P.β_pos])
  refine ⟨Real.sqrt (C₁ * C₂), max X₁ (Real.exp 1), by positivity, fun X hX => ?_⟩
  have hXe : Real.exp 1 ≤ X := (le_max_right _ _).trans hX
  have hlog1 : 1 ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hXe
  have hlogpos : 0 < Real.log X := by linarith
  have hcs := weightedBVSum_sq_le_nat_moment P X ν 1 2 (by norm_num)
  have h0 : weightedBVSum P X 0 ν ≤ C₁ / Real.log X ^ (19 : ℝ) := by
    have h := hunw X ((le_max_left _ _).trans hX)
    refine le_of_eq_of_le ?_ h
    unfold weightedBVSum
    simp
  have h2 : weightedBVSum P X ((2 : ℕ) : ℝ) ν ≤ C₂ * Real.log X ^ 5 := by
    simpa using hmom X hXe
  have hw1 : weightedBVSum P X 1 ν =
      ∑ q ∈ Icc (1 : ℕ) ⌊X ^ ν⌋₊, (tau q : ℝ) * reducedClassPrimeErrorMax P X q := by
    unfold weightedBVSum; simp
  have hnn := weightedBVSum_nonneg P X 1 ν
  have h19 : Real.log X ^ (19 : ℝ) = Real.log X ^ (19 : ℕ) := by
    exact_mod_cast Real.rpow_natCast (Real.log X) 19
  rw [h19] at h0
  have hprod : weightedBVSum P X 1 ν ^ 2 ≤ (C₁ * C₂) / (Real.log X ^ 7) ^ 2 := by
    calc weightedBVSum P X 1 ν ^ 2 ≤
        weightedBVSum P X 0 ν * weightedBVSum P X ((2 : ℕ) : ℝ) ν := hcs
      _ ≤ (C₁ / Real.log X ^ 19) * (C₂ * Real.log X ^ 5) :=
          mul_le_mul h0 h2 (weightedBVSum_nonneg _ _ _ _) (by positivity)
      _ = (C₁ * C₂) / (Real.log X ^ 7) ^ 2 := by
          field_simp
  rw [← hw1]
  calc weightedBVSum P X 1 ν = Real.sqrt (weightedBVSum P X 1 ν ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((C₁ * C₂) / (Real.log X ^ 7) ^ 2) := Real.sqrt_le_sqrt hprod
    _ = Real.sqrt (C₁ * C₂) / Real.log X ^ 7 := by
        rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]

/-- Lemma 3.8 for the parameters (4), with `ν = 8/25`. -/
theorem reciprocalBV_explicit :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      (∑ q ∈ Icc (1 : ℕ) ⌊X ^ (8 / 25 : ℝ)⌋₊,
          (tau q : ℝ) * reducedClassPrimeErrorMax ErdosStraus.Params.explicit X q) ≤
        C / (Real.log X) ^ 7 :=
  reciprocalBV_divisor_weighted ErdosStraus.Params.explicit (8 / 25) (by norm_num)
    (by simp only [ErdosStraus.Params.explicit]; norm_num)

end

end ErdosStraus.PrimeEstimates
