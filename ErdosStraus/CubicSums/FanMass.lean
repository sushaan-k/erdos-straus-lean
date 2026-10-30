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
import ErdosStraus.CubicSums.DivisorIdentity
import ErdosStraus.CubicSums.LocalRestrictions
import ErdosStraus.Estimates.Squarefree

/-!
# Proposition 4.2: the cubic divisor sum

Let `Λ_int(a)` be the set of divisors of `a²` other than `1, a, a²`, and `Λ_<(a)` the set of
divisors `h` of `a²` with `1 < h < a`. From Lemma 4.1 we deduce
`∑_{a ≤ L} |Λ_int(a)|/(4a - 1) ∼ (log L)³/(24ζ(2))` and
`∑_{a ≤ L} |Λ_<(a)|/(4a - 1) ∼ (log L)³/(48ζ(2))`. We also state Lemma 4.1 and Proposition 4.3
in the form used later. For Proposition 4.5 we bound the terms with `4a - 1` prime by the sum of
Lemma 4.4, and the composite terms by a convergent sum over distinct least prime factors, using
`τ(a²) ≤ 30^81 a^{1/4}`.
-/

namespace ErdosStraus.Estimates
open Filter Asymptotics
open scoped BigOperators Pointwise

/-! ## The divisor sum over primes -/

/-- The sum `∑_{a ≤ L, 4a - 1 prime} τ(a²)/a` of Lemma 4.4. -/
noncomputable def titchSum (L : ℝ) : ℝ :=
  ∑ a ∈ (Finset.Icc (1 : ℕ) ⌊L⌋₊).filter (fun a => Nat.Prime (4 * a - 1)),
    ((tau (a ^ 2) : ℕ) : ℝ) / (a : ℝ)

theorem titchSum_nonneg (L : ℝ) : 0 ≤ titchSum L := by
  classical
  unfold titchSum
  apply Finset.sum_nonneg
  intro a _ha
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg a)

/-! ## Divisor sums with local restrictions -/

/-- `#{h ∈ Λ_int(a) : h ≡ u (mod M)}`, where `Λ_int(a)` is the set of divisors of `a²` other
than `1, a, a²`. -/
noncomputable def localObstrInteriorFiber (M u a : ℕ) : ℝ := by
  classical
  exact
    (((a ^ 2).divisors.filter
      (fun h => congMod h u M ∧ h ≠ 1 ∧ h ≠ a ∧ h ≠ a ^ 2)).card : ℝ)

/-- The sum `∑_{a ≤ L, a ≡ a_M (mod M)} #{h ∈ Λ_int(a) : h ≡ u (mod M)}/(4a - 1)` of
Proposition 4.3. -/
noncomputable def localObstrInteriorMass (L : ℝ) (M aM u : ℕ) : ℝ := by
  classical
  exact
    ∑ a ∈ (Finset.Icc (1 : ℕ) ⌊L⌋₊).filter (fun a => congMod a aM M),
      localObstrInteriorFiber M u a / ((4 : ℝ) * (a : ℝ) - 1)

/-- The singular series `𝔖(M) = (1/ζ(2)) ∏_{ℓ ∣ M} (1 - ℓ⁻¹)³/(1 - ℓ⁻²)` of
Proposition 4.3. -/
noncomputable def singularSeries (M : ℕ) : ℝ :=
  (1 / zeta2) *
    ∏ ℓ ∈ M.primeFactors,
      ((1 - (ℓ : ℝ)⁻¹) ^ 3 / (1 - ((ℓ : ℝ) ^ 2)⁻¹))

/-! ## Cubic divisor sums -/

/-- The sum `∑_{n ≤ L} τ(n²)/n` of Lemma 4.1. -/
noncomputable def tauSqSum (L : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc (1 : ℕ) ⌊L⌋₊, ((tau (n ^ 2) : ℕ) : ℝ) / (n : ℝ)

/-- The partial sums `∑_{n ≤ L} τ(n²)/n²` of a convergent series. They bound the error made in
Proposition 4.2 by replacing `1/(4a - 1)` with `1/(4a)`. -/
noncomputable def tauSqInvSqSum (L : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc (1 : ℕ) ⌊L⌋₊,
    ((tau (n ^ 2) : ℕ) : ℝ) / ((n : ℝ) ^ (2 : ℕ))

/-- The estimates of Lemma 4.1 and Proposition 4.3: `tauSqSum L / (log L)³ → 1/(6ζ(2))`, the
sums `∑_{n ≤ L} τ(n²)/n²` are bounded, `tauSqSum L ≍ (log L)³`, and for odd `M` and `a_M`, `u`
prime to `M` the sum of Proposition 4.3 divided by `(log L)³` tends to `𝔖(M)/(24 φ(M)²)`. -/
def CubicDivisorEstimates : Prop :=
  Filter.Tendsto
      (fun L : ℝ => tauSqSum L / (Real.log L) ^ (3 : ℝ))
      Filter.atTop (nhds (1 / (6 * zeta2))) ∧
    (∃ B : ℝ, 0 < B ∧ ∀ L : ℝ, tauSqInvSqSum L ≤ B) ∧
    (∃ c C L₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ L : ℝ, L₀ ≤ L →
      c * (Real.log L) ^ (3 : ℝ) ≤ tauSqSum L ∧
        tauSqSum L ≤ C * (Real.log L) ^ (3 : ℝ)) ∧
    ∀ M aM u : ℕ, Odd M → Nat.Coprime aM M → Nat.Coprime u M →
      Filter.Tendsto
        (fun L : ℝ => localObstrInteriorMass L M aM u /
          (Real.log L) ^ (3 : ℝ))
        Filter.atTop
        (nhds (singularSeries M /
          (24 * ((Nat.totient M : ℕ) : ℝ) ^ (2 : ℕ))))

/-- Lemma 4.1 and the limit form of Proposition 4.3. -/
theorem cubic_divisor_estimates :
    CubicDivisorEstimates := by
  have h3 (x : ℝ) : x ^ (3 : ℝ) = x ^ (3 : ℕ) := Real.rpow_natCast x 3
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [tauSqSum, tau, zeta2, h3] using
      ErdosStraus.DivisorEstimates.square_divisor_reciprocal_real_sum_cubic_limit
  · simpa only [tauSqInvSqSum, tau] using
      ErdosStraus.DivisorEstimates.square_divisor_reciprocal_real_square_sum_bounded
  · simpa only [tauSqSum, tau, h3] using
      ErdosStraus.DivisorEstimates.square_divisor_reciprocal_real_sum_cubic_bounds
  · intro M aM u hM haM hu
    have hMpos : 0 < M := by
      obtain ⟨k, hk⟩ := hM
      omega
    have h := ErdosStraus.DivisorEstimates.localInteriorMass_cubic_limit
      M aM u hMpos haM hu
    rw [ErdosStraus.DivisorEstimates.localReciprocalMainCoefficient_quarter M hMpos] at h
    simpa only [localObstrInteriorMass, localObstrInteriorFiber,
      ErdosStraus.DivisorEstimates.localInteriorMass,
      ErdosStraus.DivisorEstimates.localInteriorFiber, singularSeries, zeta2, h3] using h

/-- Lemma 4.1: `tauSqSum L = (log L)³/(6ζ(2)) + O((log L)²)`. -/
theorem tauSqSum_cubic_remainder :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, Real.exp 1 ≤ L →
      |tauSqSum L - (Real.log L) ^ 3 / (6 * zeta2)| ≤ C * (Real.log L) ^ 2 := by
  simpa only [tauSqSum, tau, zeta2] using
    ErdosStraus.DivisorEstimates.square_divisor_reciprocal_real_sum_cubic_remainder

/-- Proposition 4.3, equation (10): for odd `M`, `localObstrInteriorMass L M a_M u` equals
`𝔖(M)/(24 φ(M)²) (log L)³ + O_M((log L)²)`, with one constant for all `a_M`, `u` prime to `M`. -/
theorem localObstrInteriorMass_cubic_remainder (M : ℕ) (hM : Odd M) :
    ∃ C : ℝ, 0 < C ∧ ∀ aM u : ℕ, Nat.Coprime aM M → Nat.Coprime u M →
      ∀ L : ℝ, Real.exp 1 ≤ L →
        |localObstrInteriorMass L M aM u -
          (singularSeries M / (24 * (Nat.totient M : ℝ) ^ 2)) * (Real.log L) ^ 3| ≤
          C * (Real.log L) ^ 2 := by
  have hMpos : 0 < M := by
    obtain ⟨k, hk⟩ := hM
    omega
  have h := ErdosStraus.DivisorEstimates.localInteriorMass_cubic_remainder_uniform M hMpos
  rw [ErdosStraus.DivisorEstimates.localReciprocalMainCoefficient_quarter M hMpos] at h
  simpa only [localObstrInteriorMass, localObstrInteriorFiber,
    ErdosStraus.DivisorEstimates.localInteriorMass,
    ErdosStraus.DivisorEstimates.localInteriorFiber, singularSeries, zeta2] using h

theorem tauSqSum_asymptotic_from_cubic_estimate :
    Filter.Tendsto
      (fun L : ℝ => tauSqSum L / (Real.log L) ^ (3 : ℝ))
      Filter.atTop (nhds (1 / (6 * zeta2))) :=
  cubic_divisor_estimates.1

theorem tauSqInvSqSum_bounded_from_cubic_estimate :
    ∃ B : ℝ, 0 < B ∧ ∀ L : ℝ, tauSqInvSqSum L ≤ B :=
  cubic_divisor_estimates.2.1

/-! ## Divisor fans -/

/-- `∑_{a ≤ L} τ(a²)/(4a - 1)`, the sum of Proposition 4.2 before the divisors `1, a, a²` are
removed. -/
noncomputable def divisorFanTauMass (L : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc (1 : ℕ) ⌊L⌋₊,
    ((tau (a ^ 2) : ℕ) : ℝ) / ((4 : ℝ) * (a : ℝ) - 1)

/-- `∑_{a ≤ L} |Λ_int(a)|/(4a - 1)` from Proposition 4.2, written with `|Λ_int(a)| = τ(a²) - 3`
for `a > 1` and `|Λ_int(1)| = 0`. -/
noncomputable def divisorFanInteriorMass (L : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc (1 : ℕ) ⌊L⌋₊,
    (if a = 1 then 0
     else ((tau (a ^ 2) : ℕ) : ℝ) - 3) /
      ((4 : ℝ) * (a : ℝ) - 1)

/-- `∑_{a ≤ L} |Λ_<(a)|/(4a - 1)` from Proposition 4.2, written with `|Λ_<(a)| = (τ(a²) - 3)/2`
for `a > 1` (pair `h` with `a²/h`) and `|Λ_<(1)| = 0`. -/
noncomputable def divisorFanLowerMass (L : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc (1 : ℕ) ⌊L⌋₊,
    (if a = 1 then 0
     else (((tau (a ^ 2) : ℕ) : ℝ) - 3) / 2) /
      ((4 : ℝ) * (a : ℝ) - 1)

/-- The weight `|Λ_int(a)|/(4a - 1)`, written with `|Λ_int(a)| = τ(a²) - 3` for `a > 1`. -/
noncomputable def interiorFanWeight (a : ℕ) : ℝ :=
  (if a = 1 then 0 else ((tau (a ^ 2) : ℕ) : ℝ) - 3) /
    ((4 : ℝ) * (a : ℝ) - 1)

/-- `∑_{a ∈ B, 1 ≤ a ≤ L} |Λ_int(a)|/(4a - 1)`, the sum of Proposition 4.5. -/
noncomputable def pairwiseSubfanMass (L : ℝ) (B : Finset ℕ) : ℝ :=
  ∑ a ∈ B.filter (fun a => 1 ≤ a ∧ a ≤ ⌊L⌋₊), interiorFanWeight a

/-- The terms of `pairwiseSubfanMass L B` with `4a - 1` prime. -/
noncomputable def pairwisePrimeSubfanMass (L : ℝ) (B : Finset ℕ) : ℝ :=
  ∑ a ∈ (B.filter (fun a => 1 ≤ a ∧ a ≤ ⌊L⌋₊)).filter
      (fun a => Nat.Prime (4 * a - 1)),
    interiorFanWeight a

/-- The terms of `pairwiseSubfanMass L B` with `4a - 1` not prime. -/
noncomputable def pairwiseCompositeSubfanMass (L : ℝ) (B : Finset ℕ) : ℝ :=
  ∑ a ∈ (B.filter (fun a => 1 ≤ a ∧ a ≤ ⌊L⌋₊)).filter
      (fun a => ¬ Nat.Prime (4 * a - 1)),
    interiorFanWeight a

/-- The moduli `4a - 1` with `a ∈ B` are pairwise coprime. -/
def pairwiseFanModuliCoprime (B : Finset ℕ) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, a ≠ b → Nat.Coprime (4 * a - 1) (4 * b - 1)

theorem divisorFanLowerMass_eq_half_interior (L : ℝ) :
    divisorFanLowerMass L = (1 / 2 : ℝ) * divisorFanInteriorMass L := by
  classical
  unfold divisorFanLowerMass divisorFanInteriorMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases haeq : a = 1
  · simp [haeq]
  · simp [haeq]
    ring

/-- Removing the divisors `1, a, a²` changes the sum by at most `3 ∑_{a ≤ L} 1/a`. -/
theorem abs_divisorFanTauMass_sub_interior_le
    (L : ℝ) :
    |divisorFanTauMass L - divisorFanInteriorMass L|
      ≤ 3 * ((harmonic ⌊L⌋₊ : ℚ) : ℝ) := by
  classical
  unfold divisorFanTauMass divisorFanInteriorMass
  rw [← Finset.sum_sub_distrib]
  let S : Finset ℕ := Finset.Icc (1 : ℕ) ⌊L⌋₊
  let term : ℕ → ℝ := fun a =>
    ((tau (a ^ 2) : ℕ) : ℝ) / ((4 : ℝ) * (a : ℝ) - 1) -
      ((if a = 1 then 0 else ((tau (a ^ 2) : ℕ) : ℝ) - 3) /
        ((4 : ℝ) * (a : ℝ) - 1))
  change |∑ a ∈ S, term a| ≤ 3 * ((harmonic ⌊L⌋₊ : ℚ) : ℝ)
  calc
    |∑ a ∈ S, term a|
        ≤ ∑ a ∈ S, |term a| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ S, (3 : ℝ) / (a : ℝ) := by
          apply Finset.sum_le_sum
          intro a ha
          have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (by simpa [S] using ha)).1
          have ha_ge_one : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
          have ha_pos : 0 < (a : ℝ) := by exact_mod_cast ha1
          have hden_pos : 0 < (4 : ℝ) * (a : ℝ) - 1 := by
            nlinarith [ha_ge_one]
          have hden_ge : (a : ℝ) ≤ (4 : ℝ) * (a : ℝ) - 1 := by
            nlinarith [ha_ge_one]
          by_cases haeq : a = 1
          · subst a
            simp [term, tau]
            rw [abs_of_pos (by norm_num : (0 : ℝ) < 4 - 1)]
            norm_num
          · have hdiff :
                ((tau (a ^ 2) : ℕ) : ℝ) / ((4 : ℝ) * (a : ℝ) - 1) -
                  (((tau (a ^ 2) : ℕ) : ℝ) - 3) /
                    ((4 : ℝ) * (a : ℝ) - 1)
                    = (3 : ℝ) / ((4 : ℝ) * (a : ℝ) - 1) := by
                  ring
            simp [term, haeq, hdiff]
            rw [abs_of_nonneg (div_nonneg (by norm_num) hden_pos.le)]
            exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3)
              ha_pos hden_ge
    _ = 3 * ((harmonic ⌊L⌋₊ : ℚ) : ℝ) := by
          have hharm_eq :
              ((harmonic ⌊L⌋₊ : ℚ) : ℝ) =
                ∑ a ∈ Finset.Icc (1 : ℕ) ⌊L⌋₊, (1 : ℝ) / (a : ℝ) := by
            rw [harmonic_eq_sum_Icc]
            simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
            apply Finset.sum_congr rfl
            intro a ha
            ring
          dsimp [S]
          rw [hharm_eq, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          ring

/-! ## Pairwise coprime moduli -/

theorem interiorFanWeight_le_tau_div_self {a : ℕ} (ha1 : 1 ≤ a) :
    interiorFanWeight a ≤ ((tau (a ^ 2) : ℕ) : ℝ) / (a : ℝ) := by
  have ha_ge_one : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
  have ha_pos : 0 < (a : ℝ) := by exact_mod_cast ha1
  have hden_pos : 0 < (4 : ℝ) * (a : ℝ) - 1 := by nlinarith [ha_ge_one]
  have hden_ge : (a : ℝ) ≤ (4 : ℝ) * (a : ℝ) - 1 := by nlinarith [ha_ge_one]
  have htau_nonneg : 0 ≤ ((tau (a ^ 2) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hnum_le :
      (if a = 1 then 0 else ((tau (a ^ 2) : ℕ) : ℝ) - 3)
        ≤ ((tau (a ^ 2) : ℕ) : ℝ) := by
    by_cases haeq : a = 1
    · simp [haeq]
    · simp [haeq]
  calc
    interiorFanWeight a
        ≤ ((tau (a ^ 2) : ℕ) : ℝ) /
            ((4 : ℝ) * (a : ℝ) - 1) := by
          unfold interiorFanWeight
          exact div_le_div_of_nonneg_right hnum_le hden_pos.le
    _ ≤ ((tau (a ^ 2) : ℕ) : ℝ) / (a : ℝ) := by
          exact div_le_div_of_nonneg_left htau_nonneg ha_pos hden_ge

/-- The prime part of the proof of Proposition 4.5: the terms with `4a - 1` prime are bounded
by the sum of Lemma 4.4. -/
theorem pairwisePrimeSubfanMass_le_titchSum (L : ℝ) (B : Finset ℕ) :
    pairwisePrimeSubfanMass L B ≤ titchSum L := by
  classical
  unfold pairwisePrimeSubfanMass titchSum
  calc
    (∑ a ∈ (B.filter (fun a => 1 ≤ a ∧ a ≤ ⌊L⌋₊)).filter
        (fun a => Nat.Prime (4 * a - 1)), interiorFanWeight a)
        ≤ ∑ a ∈ (B.filter (fun a => 1 ≤ a ∧ a ≤ ⌊L⌋₊)).filter
            (fun a => Nat.Prime (4 * a - 1)),
            ((tau (a ^ 2) : ℕ) : ℝ) / (a : ℝ) := by
          apply Finset.sum_le_sum
          intro a ha
          have ha_base :
              a ∈ B.filter (fun a => 1 ≤ a ∧ a ≤ ⌊L⌋₊) :=
            (Finset.mem_filter.mp ha).1
          exact interiorFanWeight_le_tau_div_self (Finset.mem_filter.mp ha_base).2.1
    _ ≤ ∑ a ∈ (Finset.Icc (1 : ℕ) ⌊L⌋₊).filter
        (fun a => Nat.Prime (4 * a - 1)),
        ((tau (a ^ 2) : ℕ) : ℝ) / (a : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro a ha
            have haS := Finset.mem_filter.mp ha
            have haB := Finset.mem_filter.mp haS.1
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_Icc.mpr haB.2, haS.2⟩
          · intro a _haT _haS
            exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg a)

/-- If `τ(a²) ≤ K a^η` for all `a ≥ 1`, with `0 ≤ η < 1`, and `4a - 1` is composite with least
prime factor `r`, then `|Λ_int(a)|/(4a - 1) ≤ K r^{-2+2η}`, because `4a - 1 ≥ r²`. -/
theorem interiorFanWeight_le_minFac_rpow_of_tau_square_subpower
    {K η : ℝ} (hK : 0 ≤ K) (hη_nonneg : 0 ≤ η) (hη_lt_one : η < 1)
    (htau : ∀ a : ℕ, 1 ≤ a →
      ((tau (a ^ 2) : ℕ) : ℝ) ≤ K * (a : ℝ) ^ η)
    {a : ℕ} (ha1 : 1 ≤ a) (hcomp : ¬ Nat.Prime (4 * a - 1)) :
    interiorFanWeight a ≤
      K * ((Nat.minFac (4 * a - 1) : ℝ) ^ (-2 + 2 * η)) := by
  let n : ℕ := 4 * a - 1
  let r : ℕ := Nat.minFac n
  have hn_pos_nat : 0 < n := by
    dsimp [n]
    omega
  have hnR_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hnR_nonneg : (0 : ℝ) ≤ (n : ℝ) := hnR_pos.le
  have hden_cast : ((n : ℕ) : ℝ) = (4 : ℝ) * (a : ℝ) - 1 := by
    dsimp [n]
    rw [Nat.cast_sub (by omega : 1 ≤ 4 * a)]
    norm_num
  have hden_pos : 0 < (4 : ℝ) * (a : ℝ) - 1 := by
    rw [← hden_cast]
    exact hnR_pos
  have hnum_le :
      (if a = 1 then 0 else ((tau (a ^ 2) : ℕ) : ℝ) - 3)
        ≤ ((tau (a ^ 2) : ℕ) : ℝ) := by
    by_cases haeq : a = 1
    · simp [haeq]
    · simp [haeq]
  have hweight_tau_n :
      interiorFanWeight a ≤ ((tau (a ^ 2) : ℕ) : ℝ) / (n : ℝ) := by
    unfold interiorFanWeight
    rw [hden_cast]
    exact div_le_div_of_nonneg_right hnum_le hden_pos.le
  have htau_div :
      ((tau (a ^ 2) : ℕ) : ℝ) / (n : ℝ) ≤
        (K * (a : ℝ) ^ η) / (n : ℝ) := by
    exact div_le_div_of_nonneg_right (htau a ha1) hnR_pos.le
  have ha_le_n_nat : a ≤ n := by
    dsimp [n]
    omega
  have ha_le_n : (a : ℝ) ≤ (n : ℝ) := by exact_mod_cast ha_le_n_nat
  have ha_pow_le_n_pow : (a : ℝ) ^ η ≤ (n : ℝ) ^ η :=
    Real.rpow_le_rpow (Nat.cast_nonneg a) ha_le_n hη_nonneg
  have hK_pow : K * (a : ℝ) ^ η ≤ K * (n : ℝ) ^ η :=
    mul_le_mul_of_nonneg_left ha_pow_le_n_pow hK
  have hdiv_n_pow :
      (K * (a : ℝ) ^ η) / (n : ℝ) ≤
        (K * (n : ℝ) ^ η) / (n : ℝ) :=
    div_le_div_of_nonneg_right hK_pow hnR_pos.le
  have hpow_div_eq :
      (K * (n : ℝ) ^ η) / (n : ℝ) = K * (n : ℝ) ^ (η - 1) := by
    have hsub := Real.rpow_sub hnR_pos η 1
    rw [Real.rpow_one] at hsub
    calc
      (K * (n : ℝ) ^ η) / (n : ℝ)
          = K * ((n : ℝ) ^ η / (n : ℝ)) := by ring
      _ = K * (n : ℝ) ^ (η - 1) := by rw [← hsub]
  have hsq_nat : r ^ (2 : ℕ) ≤ n := by
    dsimp [r, n]
    exact Nat.minFac_sq_le_self hn_pos_nat hcomp
  have hr_sq_le_n : ((r : ℝ) ^ (2 : ℕ)) ≤ (n : ℝ) := by
    exact_mod_cast hsq_nat
  have hr_pos : (0 : ℝ) < (r : ℝ) := by
    exact_mod_cast Nat.minFac_pos n
  have hr_nonneg : (0 : ℝ) ≤ (r : ℝ) := hr_pos.le
  have hr_sq_pos : (0 : ℝ) < (r : ℝ) ^ (2 : ℕ) := by positivity
  have hexp_nonpos : η - 1 ≤ 0 := by linarith
  have hn_to_rsq :
      (n : ℝ) ^ (η - 1) ≤ ((r : ℝ) ^ (2 : ℕ)) ^ (η - 1) :=
    Real.rpow_le_rpow_of_nonpos hr_sq_pos hr_sq_le_n hexp_nonpos
  have hrsq_eq :
      ((r : ℝ) ^ (2 : ℕ)) ^ (η - 1) =
        (r : ℝ) ^ (-2 + 2 * η) := by
    rw [← Real.rpow_natCast (r : ℝ) 2]
    rw [← Real.rpow_mul hr_nonneg]
    congr 1
    ring
  have hmul_final :
      K * (n : ℝ) ^ (η - 1) ≤
        K * ((Nat.minFac (4 * a - 1) : ℝ) ^ (-2 + 2 * η)) := by
    dsimp [r, n] at hn_to_rsq hrsq_eq
    rw [hrsq_eq] at hn_to_rsq
    exact mul_le_mul_of_nonneg_left hn_to_rsq hK
  calc
    interiorFanWeight a ≤ ((tau (a ^ 2) : ℕ) : ℝ) / (n : ℝ) := hweight_tau_n
    _ ≤ (K * (a : ℝ) ^ η) / (n : ℝ) := htau_div
    _ ≤ (K * (n : ℝ) ^ η) / (n : ℝ) := hdiv_n_pow
    _ = K * (n : ℝ) ^ (η - 1) := hpow_div_eq
    _ ≤ K * ((Nat.minFac (4 * a - 1) : ℝ) ^ (-2 + 2 * η)) := hmul_final

/-- If the moduli `4a - 1` are pairwise coprime, then distinct `a ∈ B` have distinct least prime
factors `P⁻(4a - 1)`. -/
theorem pairwiseCompositeMinFac_injective
    {B : Finset ℕ} (hcop : pairwiseFanModuliCoprime B)
    {a b : ℕ} (haB : a ∈ B) (hbB : b ∈ B)
    (ha1 : 1 ≤ a) (_hb1 : 1 ≤ b)
    (_hcompa : ¬ Nat.Prime (4 * a - 1))
    (_hcompb : ¬ Nat.Prime (4 * b - 1))
    (heq : Nat.minFac (4 * a - 1) = Nat.minFac (4 * b - 1)) :
    a = b := by
  by_contra hne
  have hcop_ab : Nat.Coprime (4 * a - 1) (4 * b - 1) :=
    hcop a haB b hbB hne
  have hne_one_a : 4 * a - 1 ≠ 1 := by omega
  have hp : Nat.Prime (Nat.minFac (4 * a - 1)) :=
    Nat.minFac_prime hne_one_a
  have hda : Nat.minFac (4 * a - 1) ∣ 4 * a - 1 :=
    Nat.minFac_dvd _
  have hdb : Nat.minFac (4 * a - 1) ∣ 4 * b - 1 := by
    rw [heq]
    exact Nat.minFac_dvd _
  have hdg : Nat.minFac (4 * a - 1) ∣
      Nat.gcd (4 * a - 1) (4 * b - 1) :=
    Nat.dvd_gcd hda hdb
  rw [hcop_ab.gcd_eq_one] at hdg
  exact hp.not_dvd_one hdg

theorem pairwiseCompositeMinFac_injOn_support (L : ℝ) {B : Finset ℕ}
    (hcop : pairwiseFanModuliCoprime B) :
    Set.InjOn (fun a : ℕ => Nat.minFac (4 * a - 1))
      (((B.filter (fun a => 1 ≤ a ∧ a ≤ ⌊L⌋₊)).filter
        (fun a => ¬ Nat.Prime (4 * a - 1))) : Set ℕ) := by
  intro a ha b hb heq
  have ha_comp := Finset.mem_filter.mp ha
  have hb_comp := Finset.mem_filter.mp hb
  have ha_base := Finset.mem_filter.mp ha_comp.1
  have hb_base := Finset.mem_filter.mp hb_comp.1
  exact pairwiseCompositeMinFac_injective hcop ha_base.1 hb_base.1
    ha_base.2.1 hb_base.2.1 ha_comp.2 hb_comp.2 heq

/-- `∑ P⁻(4a - 1)^{-2+2η}` over the terms of `pairwiseSubfanMass L B` with `4a - 1` not prime.
Proposition 4.5 takes `η < 1/4`; the bound below only needs `η < 1/2`. -/
noncomputable def pairwiseCompositeLeastFactorEnvelope
    (L : ℝ) (B : Finset ℕ) (η : ℝ) : ℝ :=
  ∑ a ∈ (B.filter (fun a => 1 ≤ a ∧ a ≤ ⌊L⌋₊)).filter
      (fun a => ¬ Nat.Prime (4 * a - 1)),
    ((Nat.minFac (4 * a - 1) : ℝ) ^ (-2 + 2 * η))

theorem pairwiseCompositeSubfanMass_le_envelope
    (L : ℝ) (B : Finset ℕ) (K η : ℝ)
    (hpoint : ∀ a : ℕ,
      a ∈ (B.filter (fun a => 1 ≤ a ∧ a ≤ ⌊L⌋₊)).filter
        (fun a => ¬ Nat.Prime (4 * a - 1)) →
      interiorFanWeight a ≤
        K * ((Nat.minFac (4 * a - 1) : ℝ) ^ (-2 + 2 * η))) :
    pairwiseCompositeSubfanMass L B ≤
      K * pairwiseCompositeLeastFactorEnvelope L B η := by
  classical
  unfold pairwiseCompositeSubfanMass pairwiseCompositeLeastFactorEnvelope
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  exact hpoint a ha

/-- For pairwise coprime moduli the least prime factors are distinct, so the sum is at most
`∑_r r^{-2+2η}`, which converges for `η < 1/2`. -/
theorem pairwiseCompositeLeastFactorEnvelope_le_tsum
    (L : ℝ) {B : Finset ℕ} (hcop : pairwiseFanModuliCoprime B)
    {η : ℝ} (hη : η < 1 / 2) :
    pairwiseCompositeLeastFactorEnvelope L B η ≤
      ∑' r : ℕ, ((r : ℝ) ^ (-2 + 2 * η)) := by
  classical
  let S : Finset ℕ :=
    (B.filter (fun a => 1 ≤ a ∧ a ≤ ⌊L⌋₊)).filter
      (fun a => ¬ Nat.Prime (4 * a - 1))
  change
    (∑ a ∈ S, ((Nat.minFac (4 * a - 1) : ℝ) ^ (-2 + 2 * η))) ≤
      ∑' r : ℕ, ((r : ℝ) ^ (-2 + 2 * η))
  have hinj :
      ∀ x ∈ S, ∀ y ∈ S,
        Nat.minFac (4 * x - 1) = Nat.minFac (4 * y - 1) → x = y := by
    intro x hx y hy hxy
    exact pairwiseCompositeMinFac_injOn_support L hcop
      (by simpa [S] using hx) (by simpa [S] using hy) hxy
  have himage :
      (∑ r ∈ S.image (fun a : ℕ => Nat.minFac (4 * a - 1)),
          ((r : ℝ) ^ (-2 + 2 * η))) =
        ∑ a ∈ S, ((Nat.minFac (4 * a - 1) : ℝ) ^ (-2 + 2 * η)) := by
    exact Finset.sum_image hinj
  rw [← himage]
  have hsumm : Summable (fun r : ℕ => ((r : ℝ) ^ (-2 + 2 * η))) :=
    Real.summable_nat_rpow.mpr (by nlinarith)
  exact Summable.sum_le_tsum
    (S.image (fun a : ℕ => Nat.minFac (4 * a - 1)))
    (fun r _hr => Real.rpow_nonneg (Nat.cast_nonneg r) _)
    hsumm

/-- The composite part of Proposition 4.5: if `|Λ_int(a)|/(4a - 1) ≤ K P⁻(4a - 1)^{-2+2η}` for
the terms with `4a - 1` not prime, then these terms sum to at most `K ∑_r r^{-2+2η}`. -/
theorem pairwiseCompositeSubfanMass_upper_of_pointwise_minFac
    (L : ℝ) {B : Finset ℕ} (hcop : pairwiseFanModuliCoprime B)
    {K η : ℝ} (hK : 0 ≤ K) (hη : η < 1 / 2)
    (hpoint : ∀ a : ℕ,
      a ∈ (B.filter (fun a => 1 ≤ a ∧ a ≤ ⌊L⌋₊)).filter
        (fun a => ¬ Nat.Prime (4 * a - 1)) →
      interiorFanWeight a ≤
        K * ((Nat.minFac (4 * a - 1) : ℝ) ^ (-2 + 2 * η))) :
    pairwiseCompositeSubfanMass L B ≤
      K * (∑' r : ℕ, ((r : ℝ) ^ (-2 + 2 * η))) := by
  exact le_trans
    (pairwiseCompositeSubfanMass_le_envelope L B K η hpoint)
    (mul_le_mul_of_nonneg_left
      (pairwiseCompositeLeastFactorEnvelope_le_tsum L hcop hη) hK)

theorem pairwiseSubfanMass_eq_prime_add_composite (L : ℝ) (B : Finset ℕ) :
    pairwiseSubfanMass L B =
      pairwisePrimeSubfanMass L B + pairwiseCompositeSubfanMass L B := by
  classical
  unfold pairwiseSubfanMass pairwisePrimeSubfanMass pairwiseCompositeSubfanMass
  let S : Finset ℕ := B.filter (fun a => 1 ≤ a ∧ a ≤ ⌊L⌋₊)
  have hsplit := Finset.sum_filter_add_sum_filter_not S
    (fun a : ℕ => Nat.Prime (4 * a - 1)) interiorFanWeight
  simpa [S, add_comm] using hsplit.symm

/-! ## The asymptotics of Proposition 4.2 -/

theorem one_fourth_mul_tauSqSum_le_divisorFanTauMass (L : ℝ) :
    (1 / 4 : ℝ) * tauSqSum L ≤ divisorFanTauMass L := by
  classical
  unfold divisorFanTauMass tauSqSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
  have ha_ge_one : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
  have ha_pos : 0 < (a : ℝ) := by exact_mod_cast ha1
  have h4a_pos : 0 < (4 : ℝ) * (a : ℝ) := by positivity
  have hden_pos : 0 < (4 : ℝ) * (a : ℝ) - 1 := by nlinarith [ha_ge_one]
  have hden_le : (4 : ℝ) * (a : ℝ) - 1 ≤ (4 : ℝ) * (a : ℝ) := by nlinarith
  have hinv :
      1 / ((4 : ℝ) * (a : ℝ)) ≤
        1 / ((4 : ℝ) * (a : ℝ) - 1) :=
    one_div_le_one_div_of_le hden_pos hden_le
  have htau_nonneg : 0 ≤ ((tau (a ^ 2) : ℕ) : ℝ) := Nat.cast_nonneg _
  calc
    (1 / 4 : ℝ) * (((tau (a ^ 2) : ℕ) : ℝ) / (a : ℝ))
        = ((tau (a ^ 2) : ℕ) : ℝ) *
            (1 / ((4 : ℝ) * (a : ℝ))) := by field_simp [ha_pos.ne']
    _ ≤ ((tau (a ^ 2) : ℕ) : ℝ) *
          (1 / ((4 : ℝ) * (a : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_left hinv htau_nonneg
    _ = ((tau (a ^ 2) : ℕ) : ℝ) / ((4 : ℝ) * (a : ℝ) - 1) := by ring

/-- The bound `1/(4a - 1) ≤ 1/(4a) + 1/(4a²)`, summed against `τ(a²)`. -/
theorem divisorFanTauMass_le_quarter_tauSqSums (L : ℝ) :
    divisorFanTauMass L ≤
      (1 / 4 : ℝ) * tauSqSum L + (1 / 4 : ℝ) * tauSqInvSqSum L := by
  classical
  unfold divisorFanTauMass tauSqSum tauSqInvSqSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a ha
  have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
  have ha_ge_one : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
  have ha_pos : 0 < (a : ℝ) := by exact_mod_cast ha1
  have hden_pos : 0 < (4 : ℝ) * (a : ℝ) - 1 := by nlinarith [ha_ge_one]
  have htau_nonneg : 0 ≤ ((tau (a ^ 2) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrecip :
      1 / ((4 : ℝ) * (a : ℝ) - 1)
        ≤ 1 / ((4 : ℝ) * (a : ℝ)) +
          1 / ((4 : ℝ) * ((a : ℝ) ^ (2 : ℕ))) := by
    have ha_ne : (a : ℝ) ≠ 0 := ne_of_gt ha_pos
    have hden_ne : (4 : ℝ) * (a : ℝ) - 1 ≠ 0 := ne_of_gt hden_pos
    have h4a_ne : (4 : ℝ) * (a : ℝ) ≠ 0 := by positivity
    have h4a2_ne : (4 : ℝ) * ((a : ℝ) ^ (2 : ℕ)) ≠ 0 := by positivity
    have hbig_pos :
        0 < ((4 : ℝ) * (a : ℝ)) *
          ((4 : ℝ) * ((a : ℝ) ^ (2 : ℕ))) := by positivity
    have hsum_eq :
        (1 / ((4 : ℝ) * (a : ℝ)) +
            1 / ((4 : ℝ) * ((a : ℝ) ^ (2 : ℕ)))) *
            ((4 : ℝ) * (a : ℝ) - 1)
          =
        (((4 : ℝ) * ((a : ℝ) ^ (2 : ℕ)) + (4 : ℝ) * (a : ℝ)) *
            ((4 : ℝ) * (a : ℝ) - 1)) /
          (((4 : ℝ) * (a : ℝ)) *
            ((4 : ℝ) * ((a : ℝ) ^ (2 : ℕ)))) := by
      field_simp [hden_ne, h4a_ne, h4a2_ne, ha_ne]
    rw [div_le_iff₀ hden_pos]
    rw [hsum_eq]
    rw [le_div_iff₀ hbig_pos]
    nlinarith [ha_ge_one]
  calc
    ((tau (a ^ 2) : ℕ) : ℝ) / ((4 : ℝ) * (a : ℝ) - 1)
        = ((tau (a ^ 2) : ℕ) : ℝ) *
            (1 / ((4 : ℝ) * (a : ℝ) - 1)) := by ring
    _ ≤ ((tau (a ^ 2) : ℕ) : ℝ) *
          (1 / ((4 : ℝ) * (a : ℝ)) +
            1 / ((4 : ℝ) * ((a : ℝ) ^ (2 : ℕ)))) :=
          mul_le_mul_of_nonneg_left hrecip htau_nonneg
    _ = (1 / 4 : ℝ) * (((tau (a ^ 2) : ℕ) : ℝ) / (a : ℝ)) +
          (1 / 4 : ℝ) *
            (((tau (a ^ 2) : ℕ) : ℝ) / ((a : ℝ) ^ (2 : ℕ))) := by
          field_simp [ha_pos.ne']

theorem abs_divisorFanTauMass_sub_quarter_le
    (L : ℝ) :
    |divisorFanTauMass L - (1 / 4 : ℝ) * tauSqSum L|
      ≤ (1 / 4 : ℝ) * tauSqInvSqSum L := by
  have hlow := one_fourth_mul_tauSqSum_le_divisorFanTauMass L
  have hupper := divisorFanTauMass_le_quarter_tauSqSums L
  rw [abs_of_nonneg (sub_nonneg.mpr hlow)]
  linarith

theorem divisorFanTauMass_sub_quarter_bounded :
    ∃ B : ℝ, 0 < B ∧ ∀ L : ℝ,
      |divisorFanTauMass L - (1 / 4 : ℝ) * tauSqSum L| ≤ B := by
  rcases tauSqInvSqSum_bounded_from_cubic_estimate with ⟨B, hB, hbound⟩
  refine ⟨(1 / 4 : ℝ) * B, mul_pos (by norm_num) hB, ?_⟩
  intro L
  exact le_trans
    (abs_divisorFanTauMass_sub_quarter_le L)
    (mul_le_mul_of_nonneg_left (hbound L) (by norm_num))

theorem log_cube_tendsto_atTop :
    Filter.Tendsto (fun L : ℝ => (Real.log L) ^ (3 : ℝ))
      Filter.atTop Filter.atTop := by
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (3 : ℝ))).comp
    Real.tendsto_log_atTop

theorem bounded_div_log_cube_tendsto_zero
    (f : ℝ → ℝ) (B : ℝ) (_hB : 0 < B) (hbound : ∀ L : ℝ, |f L| ≤ B) :
    Filter.Tendsto
      (fun L : ℝ => f L / (Real.log L) ^ (3 : ℝ))
      Filter.atTop (nhds 0) := by
  have hden_top := log_cube_tendsto_atTop
  have hinv :
      Filter.Tendsto
        (fun L : ℝ => ((Real.log L) ^ (3 : ℝ))⁻¹)
        Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hden_top
  have hmajor :
      Filter.Tendsto
        (fun L : ℝ => B * ((Real.log L) ^ (3 : ℝ))⁻¹)
        Filter.atTop (nhds 0) := by
    simpa using hinv.const_mul B
  refine squeeze_zero_norm'
    (a := fun L : ℝ => B * ((Real.log L) ^ (3 : ℝ))⁻¹) ?_ hmajor
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with L hL
  have hlog_pos : 0 < Real.log L := Real.log_pos hL
  have hden_pos : 0 < (Real.log L) ^ (3 : ℝ) :=
    Real.rpow_pos_of_pos hlog_pos 3
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hden_pos]
  calc
    |f L| / (Real.log L) ^ (3 : ℝ)
        ≤ B / (Real.log L) ^ (3 : ℝ) :=
          div_le_div_of_nonneg_right (hbound L) hden_pos.le
    _ = B * ((Real.log L) ^ (3 : ℝ))⁻¹ := by ring

theorem harmonic_floor_div_log_cube_tendsto_zero :
    Filter.Tendsto
      (fun L : ℝ => ((harmonic ⌊L⌋₊ : ℚ) : ℝ) /
        (Real.log L) ^ (3 : ℝ))
      Filter.atTop (nhds 0) := by
  have hlog_sq_top :
      Filter.Tendsto (fun L : ℝ => (Real.log L) ^ (2 : ℝ))
        Filter.atTop Filter.atTop := by
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (2 : ℝ))).comp
      Real.tendsto_log_atTop
  have hinv :
      Filter.Tendsto (fun L : ℝ => ((Real.log L) ^ (2 : ℝ))⁻¹)
        Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hlog_sq_top
  have hmajor :
      Filter.Tendsto (fun L : ℝ => 2 * ((Real.log L) ^ (2 : ℝ))⁻¹)
        Filter.atTop (nhds 0) := by
    simpa using hinv.const_mul (2 : ℝ)
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [Filter.eventually_gt_atTop (Real.exp 1)] with L hL
    have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hL.le
    have hlog_pos : 0 < Real.log L := by
      rw [Real.log_pos_iff hLpos.le]
      exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < Real.exp 1) hL.le
    have hden_pos : 0 < (Real.log L) ^ (3 : ℝ) :=
      Real.rpow_pos_of_pos hlog_pos 3
    have hharm_nonneg : 0 ≤ ((harmonic ⌊L⌋₊ : ℚ) : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      apply Finset.sum_nonneg
      intro n _hn
      exact inv_nonneg.mpr (Nat.cast_nonneg n)
    exact div_nonneg hharm_nonneg hden_pos.le
  · filter_upwards [Filter.eventually_gt_atTop (Real.exp 1)] with L hL
    have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hL.le
    have hL_ge_one : 1 ≤ L :=
      le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hL.le
    have hlog_ge_one : 1 ≤ Real.log L := by
      rw [Real.le_log_iff_exp_le hLpos]
      exact hL.le
    have hlog_pos : 0 < Real.log L := lt_of_lt_of_le zero_lt_one hlog_ge_one
    have hden_pos : 0 < (Real.log L) ^ (3 : ℝ) :=
      Real.rpow_pos_of_pos hlog_pos 3
    have hlog_sq_pos : 0 < (Real.log L) ^ (2 : ℝ) :=
      Real.rpow_pos_of_pos hlog_pos 2
    have hharm : ((harmonic ⌊L⌋₊ : ℚ) : ℝ) ≤ 1 + Real.log L :=
      harmonic_floor_le_one_add_log L hL_ge_one
    have htail : 1 + Real.log L ≤ 2 * Real.log L := by
      linarith
    calc
      ((harmonic ⌊L⌋₊ : ℚ) : ℝ) / (Real.log L) ^ (3 : ℝ)
          ≤ (2 * Real.log L) / (Real.log L) ^ (3 : ℝ) :=
            div_le_div_of_nonneg_right (le_trans hharm htail) hden_pos.le
      _ = 2 * ((Real.log L) ^ (2 : ℝ))⁻¹ := by
            have hlog3 : (Real.log L) ^ (3 : ℝ) =
                (Real.log L) ^ (3 : ℕ) :=
              Real.rpow_natCast (Real.log L) 3
            have hlog2 : (Real.log L) ^ (2 : ℝ) =
                (Real.log L) ^ (2 : ℕ) :=
              Real.rpow_natCast (Real.log L) 2
            rw [hlog3, hlog2]
            field_simp [ne_of_gt hlog_pos]

/-- `∑_{a ≤ L} τ(a²)/(4a - 1) ∼ (log L)³/(24ζ(2))`, from Lemma 4.1 and
`1/(4a - 1) = 1/(4a) + O(a⁻²)`. -/
theorem divisorFanTauMass_asymptotic_from_cubic_estimate :
    Filter.Tendsto
      (fun L : ℝ => divisorFanTauMass L / (Real.log L) ^ (3 : ℝ))
      Filter.atTop (nhds (1 / (24 * zeta2))) := by
  rcases divisorFanTauMass_sub_quarter_bounded with
    ⟨B, hB, hbound⟩
  have hmain :
      Filter.Tendsto
        (fun L : ℝ => (1 / 4 : ℝ) *
          (tauSqSum L / (Real.log L) ^ (3 : ℝ)))
        Filter.atTop (nhds ((1 / 4 : ℝ) * (1 / (6 * zeta2)))) := by
    simpa using tauSqSum_asymptotic_from_cubic_estimate.const_mul (1 / 4 : ℝ)
  have herr :
      Filter.Tendsto
        (fun L : ℝ =>
          (divisorFanTauMass L - (1 / 4 : ℝ) * tauSqSum L) /
            (Real.log L) ^ (3 : ℝ))
        Filter.atTop (nhds 0) :=
    bounded_div_log_cube_tendsto_zero
      (fun L : ℝ => divisorFanTauMass L - (1 / 4 : ℝ) * tauSqSum L)
      B hB hbound
  have hsum := hmain.add herr
  have hdecomp :
      (fun L : ℝ => divisorFanTauMass L / (Real.log L) ^ (3 : ℝ))
        =
      (fun L : ℝ =>
        (1 / 4 : ℝ) * (tauSqSum L / (Real.log L) ^ (3 : ℝ)) +
          (divisorFanTauMass L - (1 / 4 : ℝ) * tauSqSum L) /
            (Real.log L) ^ (3 : ℝ)) := by
    funext L
    ring
  rw [hdecomp]
  convert hsum using 1
  ring_nf

/-- Proposition 4.2: `∑_{a ≤ L} |Λ_int(a)|/(4a - 1) ∼ (log L)³/(24ζ(2))`. -/
theorem divisorFanInteriorMass_asymptotic_from_cubic_estimate :
    Filter.Tendsto
      (fun L : ℝ => divisorFanInteriorMass L / (Real.log L) ^ (3 : ℝ))
      Filter.atTop (nhds (1 / (24 * zeta2))) := by
  have hmajor :
      Filter.Tendsto
        (fun L : ℝ => 3 *
          (((harmonic ⌊L⌋₊ : ℚ) : ℝ) / (Real.log L) ^ (3 : ℝ)))
        Filter.atTop (nhds 0) := by
    simpa using harmonic_floor_div_log_cube_tendsto_zero.const_mul (3 : ℝ)
  have herr :
      Filter.Tendsto
        (fun L : ℝ =>
          (divisorFanInteriorMass L - divisorFanTauMass L) /
            (Real.log L) ^ (3 : ℝ))
        Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm'
      (a := fun L : ℝ => 3 *
        (((harmonic ⌊L⌋₊ : ℚ) : ℝ) / (Real.log L) ^ (3 : ℝ))) ?_ hmajor
    filter_upwards [Filter.eventually_gt_atTop (Real.exp 1)] with L hL
    have hlog_ge_one : 1 ≤ Real.log L := by
      have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hL.le
      rw [Real.le_log_iff_exp_le hLpos]
      exact hL.le
    have hlog_pos : 0 < Real.log L := lt_of_lt_of_le zero_lt_one hlog_ge_one
    have hden_pos : 0 < (Real.log L) ^ (3 : ℝ) :=
      Real.rpow_pos_of_pos hlog_pos 3
    have hdiff :
        |divisorFanInteriorMass L - divisorFanTauMass L|
          ≤ 3 * ((harmonic ⌊L⌋₊ : ℚ) : ℝ) := by
      simpa [abs_sub_comm] using
        abs_divisorFanTauMass_sub_interior_le L
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hden_pos]
    calc
      |divisorFanInteriorMass L - divisorFanTauMass L| /
          (Real.log L) ^ (3 : ℝ)
          ≤ (3 * ((harmonic ⌊L⌋₊ : ℚ) : ℝ)) /
              (Real.log L) ^ (3 : ℝ) :=
            div_le_div_of_nonneg_right hdiff hden_pos.le
      _ = 3 * (((harmonic ⌊L⌋₊ : ℚ) : ℝ) /
            (Real.log L) ^ (3 : ℝ)) := by ring
  have hsum := divisorFanTauMass_asymptotic_from_cubic_estimate.add herr
  have hdecomp :
      (fun L : ℝ => divisorFanInteriorMass L / (Real.log L) ^ (3 : ℝ))
        =
      (fun L : ℝ =>
        divisorFanTauMass L / (Real.log L) ^ (3 : ℝ) +
          (divisorFanInteriorMass L - divisorFanTauMass L) /
            (Real.log L) ^ (3 : ℝ)) := by
    funext L
    ring
  rw [hdecomp]
  simpa using hsum

/-- Proposition 4.2: `∑_{a ≤ L} |Λ_<(a)|/(4a - 1) ∼ (log L)³/(48ζ(2))`. -/
theorem divisorFanLowerMass_asymptotic_from_cubic_estimate :
    Filter.Tendsto
      (fun L : ℝ => divisorFanLowerMass L / (Real.log L) ^ (3 : ℝ))
      Filter.atTop (nhds (1 / (48 * zeta2))) := by
  have hhalf :
      Filter.Tendsto
        (fun L : ℝ => (1 / 2 : ℝ) *
          (divisorFanInteriorMass L / (Real.log L) ^ (3 : ℝ)))
        Filter.atTop (nhds ((1 / 2 : ℝ) * (1 / (24 * zeta2)))) := by
    simpa using
      divisorFanInteriorMass_asymptotic_from_cubic_estimate.const_mul (1 / 2 : ℝ)
  have hdecomp :
      (fun L : ℝ => divisorFanLowerMass L / (Real.log L) ^ (3 : ℝ))
        =
      (fun L : ℝ => (1 / 2 : ℝ) *
        (divisorFanInteriorMass L / (Real.log L) ^ (3 : ℝ))) := by
    funext L
    rw [divisorFanLowerMass_eq_half_interior L]
    ring
  rw [hdecomp]
  convert hhalf using 1
  ring_nf

/-! ## The bound `τ(a²) ≪ a^{1/4}` -/

theorem two_mul_add_one_le_three_pow (e : ℕ) : 2 * e + 1 ≤ 3 ^ e := by
  induction e with
  | zero => norm_num
  | succ e ih =>
      calc
        2 * (e + 1) + 1 ≤ 3 * (2 * e + 1) := by omega
        _ ≤ 3 * 3 ^ e := Nat.mul_le_mul_left 3 ih
        _ = 3 ^ (e + 1) := by ring

theorem two_mul_add_one_le_thirty_mul_eleven_tenths_pow (e : ℕ) :
    ((2 * e + 1 : ℕ) : ℝ) ≤ 30 * ((11 : ℝ) / 10) ^ e := by
  induction e with
  | zero => norm_num
  | succ e ih =>
      by_cases he : e < 10
      · have hleft : ((2 * (e + 1) + 1 : ℕ) : ℝ) ≤ 30 := by
          have hleft_nat : 2 * (e + 1) + 1 ≤ 30 := by omega
          exact_mod_cast hleft_nat
        have hpow_ge : (1 : ℝ) ≤ ((11 : ℝ) / 10) ^ (e + 1) := by
          exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ (11 : ℝ) / 10)
        calc
          ((2 * (e + 1) + 1 : ℕ) : ℝ) ≤ 30 := hleft
          _ = 30 * 1 := by ring
          _ ≤ 30 * ((11 : ℝ) / 10) ^ (e + 1) := by
            exact mul_le_mul_of_nonneg_left hpow_ge (by norm_num)
      · have he10 : (10 : ℕ) ≤ e := Nat.le_of_not_lt he
        have hstep : ((2 * (e + 1) + 1 : ℕ) : ℝ) ≤
            ((11 : ℝ) / 10) * ((2 * e + 1 : ℕ) : ℝ) := by
          have he10r : (10 : ℝ) ≤ e := by exact_mod_cast he10
          norm_num
          nlinarith
        calc
          ((2 * (e + 1) + 1 : ℕ) : ℝ)
              ≤ ((11 : ℝ) / 10) * ((2 * e + 1 : ℕ) : ℝ) := hstep
          _ ≤ ((11 : ℝ) / 10) * (30 * ((11 : ℝ) / 10) ^ e) := by
            exact mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = 30 * ((11 : ℝ) / 10) ^ (e + 1) := by ring

theorem eleven_tenths_le_two_rpow_quarter :
    ((11 : ℝ) / 10) ≤ (2 : ℝ) ^ ((1 : ℝ) / 4) := by
  have h : ((11 : ℝ) / 10) ≤ (2 : ℝ) ^ (4 : ℝ)⁻¹ := by
    rw [Real.le_rpow_inv_iff_of_pos (by norm_num : (0 : ℝ) ≤ (11 : ℝ) / 10)
        (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) < 4)]
    norm_num
  simpa [one_div] using h

theorem two_mul_add_one_le_thirty_mul_two_rpow_quarter (e : ℕ) :
    ((2 * e + 1 : ℕ) : ℝ) ≤ 30 * (2 : ℝ) ^ ((e : ℝ) / 4) := by
  have hlin := two_mul_add_one_le_thirty_mul_eleven_tenths_pow e
  have hbasepow : ((11 : ℝ) / 10) ^ e ≤ ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ e := by
    exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (11 : ℝ) / 10)
      eleven_tenths_le_two_rpow_quarter e
  have hpoweq : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ e =
      (2 : ℝ) ^ ((e : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring_nf
  calc
    ((2 * e + 1 : ℕ) : ℝ) ≤ 30 * ((11 : ℝ) / 10) ^ e := hlin
    _ ≤ 30 * (((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ e) := by
      exact mul_le_mul_of_nonneg_left hbasepow (by norm_num)
    _ = 30 * (2 : ℝ) ^ ((e : ℝ) / 4) := by rw [hpoweq]

theorem two_mul_add_one_le_large_rpow_quarter {p e : ℕ} (hp : 81 ≤ p) :
    ((2 * e + 1 : ℕ) : ℝ) ≤ (p : ℝ) ^ ((e : ℝ) / 4) := by
  have hlin_nat := two_mul_add_one_le_three_pow e
  have hlin : ((2 * e + 1 : ℕ) : ℝ) ≤ ((3 ^ e : ℕ) : ℝ) := by
    exact_mod_cast hlin_nat
  have h3root : (3 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 4) := by
    have h : (3 : ℝ) ≤ (p : ℝ) ^ (4 : ℝ)⁻¹ := by
      rw [Real.le_rpow_inv_iff_of_pos (by norm_num : (0 : ℝ) ≤ 3)
          (Nat.cast_nonneg p) (by norm_num : (0 : ℝ) < 4)]
      norm_num
      exact_mod_cast hp
    simpa [one_div] using h
  have hpow : (3 : ℝ) ^ e ≤ ((p : ℝ) ^ ((1 : ℝ) / 4)) ^ e := by
    exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) h3root e
  have hpoweq : ((p : ℝ) ^ ((1 : ℝ) / 4)) ^ e =
      (p : ℝ) ^ ((e : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]
    ring_nf
  calc
    ((2 * e + 1 : ℕ) : ℝ) ≤ ((3 ^ e : ℕ) : ℝ) := hlin
    _ = (3 : ℝ) ^ e := by norm_num
    _ ≤ ((p : ℝ) ^ ((1 : ℝ) / 4)) ^ e := hpow
    _ = (p : ℝ) ^ ((e : ℝ) / 4) := hpoweq

/-- The constant in `τ(a²) ≤ C a^{1/4}`. Each prime factor `p < 81` of `a` contributes a factor
`30`, and there are fewer than `81` such primes. -/
noncomputable def tauSquareQuarterConstant : ℝ := 30 ^ (81 : ℕ)

/-- The factor allowed at the prime `p`: `30` if `p < 81`, and `1` otherwise. -/
private noncomputable def tauSquarePrimeCoeff (p : ℕ) : ℝ :=
  if p < 81 then 30 else 1

private theorem tauSquarePrimeCoeff_prod_le (s : Finset ℕ) :
    (∏ p ∈ s, tauSquarePrimeCoeff p) ≤ tauSquareQuarterConstant := by
  classical
  let small := s.filter (fun p => p < 81)
  have hsplit :
      (∏ p ∈ s, tauSquarePrimeCoeff p) =
        (∏ p ∈ small, tauSquarePrimeCoeff p) *
          (∏ p ∈ s.filter (fun p => ¬ p < 81), tauSquarePrimeCoeff p) := by
    dsimp [small]
    rw [Finset.prod_filter_mul_prod_filter_not]
  have hsmall_prod : (∏ p ∈ small, tauSquarePrimeCoeff p) = 30 ^ small.card := by
    calc
      (∏ p ∈ small, tauSquarePrimeCoeff p) = ∏ _p ∈ small, (30 : ℝ) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hp_lt : p < 81 := (Finset.mem_filter.mp hp).2
        simp [tauSquarePrimeCoeff, hp_lt]
      _ = 30 ^ small.card := Finset.prod_const 30
  have hlarge_prod :
      (∏ p ∈ s.filter (fun p => ¬ p < 81), tauSquarePrimeCoeff p) = 1 := by
    calc
      (∏ p ∈ s.filter (fun p => ¬ p < 81), tauSquarePrimeCoeff p) =
          ∏ _p ∈ s.filter (fun p => ¬ p < 81), (1 : ℝ) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hp_not : ¬ p < 81 := (Finset.mem_filter.mp hp).2
        simp [tauSquarePrimeCoeff, hp_not]
      _ = 1 := by simp
  have hcard : small.card ≤ 81 := by
    have hsubset : small ⊆ Finset.range 81 := by
      intro p hp
      exact Finset.mem_range.mpr ((Finset.mem_filter.mp hp).2)
    exact (Finset.card_le_card hsubset).trans (by simp)
  calc
    (∏ p ∈ s, tauSquarePrimeCoeff p)
        = 30 ^ small.card * 1 := by rw [hsplit, hsmall_prod, hlarge_prod]
    _ = 30 ^ small.card := by ring
    _ ≤ 30 ^ (81 : ℕ) := by
          exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 30) hcard
    _ = tauSquareQuarterConstant := by rfl

private theorem tau_square_prime_factor_term_le_coeff (a p : ℕ)
    (hp : p ∈ a.primeFactors) :
    (((a ^ 2).factorization p + 1 : ℕ) : ℝ) ≤
      tauSquarePrimeCoeff p * (p : ℝ) ^ (((a.factorization p : ℕ) : ℝ) / 4) := by
  classical
  have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp2_nat : 2 ≤ p := hpprime.two_le
  have hfactor : (a ^ 2).factorization p + 1 = 2 * a.factorization p + 1 := by
    rw [Nat.factorization_pow]
    simp [Finsupp.smul_apply, smul_eq_mul]
  by_cases hsmall : p < 81
  · have htwo := two_mul_add_one_le_thirty_mul_two_rpow_quarter (a.factorization p)
    have hbase : (2 : ℝ) ^ (((a.factorization p : ℕ) : ℝ) / 4) ≤
        (p : ℝ) ^ (((a.factorization p : ℕ) : ℝ) / 4) := by
      exact Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 2)
        (by exact_mod_cast hp2_nat)
        (by positivity)
    calc
      (((a ^ 2).factorization p + 1 : ℕ) : ℝ)
          = ((2 * a.factorization p + 1 : ℕ) : ℝ) := by rw [hfactor]
      _ ≤ 30 * (2 : ℝ) ^ (((a.factorization p : ℕ) : ℝ) / 4) := htwo
      _ ≤ 30 * (p : ℝ) ^ (((a.factorization p : ℕ) : ℝ) / 4) := by
            exact mul_le_mul_of_nonneg_left hbase (by norm_num)
      _ = tauSquarePrimeCoeff p *
            (p : ℝ) ^ (((a.factorization p : ℕ) : ℝ) / 4) := by
            simp [tauSquarePrimeCoeff, hsmall]
  · have hlarge_nat : 81 ≤ p := Nat.le_of_not_lt hsmall
    have hlarge := two_mul_add_one_le_large_rpow_quarter (p := p)
      (e := a.factorization p) hlarge_nat
    calc
      (((a ^ 2).factorization p + 1 : ℕ) : ℝ)
          = ((2 * a.factorization p + 1 : ℕ) : ℝ) := by rw [hfactor]
      _ ≤ (p : ℝ) ^ (((a.factorization p : ℕ) : ℝ) / 4) := hlarge
      _ = tauSquarePrimeCoeff p *
            (p : ℝ) ^ (((a.factorization p : ℕ) : ℝ) / 4) := by
            simp [tauSquarePrimeCoeff, hsmall]

/-- `τ(a²) ≤ 30^81 a^{1/4}`, the divisor bound used for the composite part of
Proposition 4.5. -/
theorem tau_square_le_const_rpow_quarter {a : ℕ} (ha : 1 ≤ a) :
    ((tau (a ^ 2) : ℕ) : ℝ) ≤
      tauSquareQuarterConstant * (a : ℝ) ^ ((1 : ℝ) / 4) := by
  classical
  have ha_ne : a ≠ 0 := by omega
  have ha2_ne : a ^ 2 ≠ 0 := pow_ne_zero 2 ha_ne
  have hcast : ((tau (a ^ 2) : ℕ) : ℝ) =
      ∏ p ∈ a.primeFactors, (((a ^ 2).factorization p + 1 : ℕ) : ℝ) := by
    unfold tau
    rw [Nat.card_divisors ha2_ne]
    rw [Nat.primeFactors_pow a (by norm_num : (2 : ℕ) ≠ 0)]
    norm_num
  have hprod_le :
      (∏ p ∈ a.primeFactors, (((a ^ 2).factorization p + 1 : ℕ) : ℝ)) ≤
        ∏ p ∈ a.primeFactors,
          tauSquarePrimeCoeff p * (p : ℝ) ^ (((a.factorization p : ℕ) : ℝ) / 4) := by
    exact Finset.prod_le_prod
      (fun _p _hp => Nat.cast_nonneg _)
      (fun p hp => tau_square_prime_factor_term_le_coeff a p hp)
  have hsplit :
      (∏ p ∈ a.primeFactors,
          tauSquarePrimeCoeff p * (p : ℝ) ^ (((a.factorization p : ℕ) : ℝ) / 4)) =
        (∏ p ∈ a.primeFactors, tauSquarePrimeCoeff p) *
          ∏ p ∈ a.primeFactors, (p : ℝ) ^ (((a.factorization p : ℕ) : ℝ) / 4) := by
    rw [Finset.prod_mul_distrib]
  have hcoeff := tauSquarePrimeCoeff_prod_le a.primeFactors
  have hpow_eq :
      (∏ p ∈ a.primeFactors, (p : ℝ) ^ (((a.factorization p : ℕ) : ℝ) / 4)) =
        (a : ℝ) ^ ((1 : ℝ) / 4) := by
    have hrewrite :
        (∏ p ∈ a.primeFactors, (p : ℝ) ^ (((a.factorization p : ℕ) : ℝ) / 4)) =
          ∏ p ∈ a.primeFactors, ((p : ℝ) ^ a.factorization p) ^ ((1 : ℝ) / 4) := by
      apply Finset.prod_congr rfl
      intro p _hp
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]
      ring_nf
    rw [hrewrite, Real.finsetProd_rpow]
    · have hprod_nat : (∏ p ∈ a.primeFactors, p ^ a.factorization p) = a := by
        calc
          (∏ p ∈ a.primeFactors, p ^ a.factorization p)
              = a.factorization.prod (fun p e => p ^ e) := by
                exact (Finsupp.prod_of_support_subset a.factorization
                  (by intro p hp; exact hp)
                  (fun p e => p ^ e) (by intro p _hp; simp)).symm
          _ = a := Nat.prod_factorization_pow_eq_self ha_ne
      have hprod : (∏ p ∈ a.primeFactors, (p : ℝ) ^ a.factorization p) =
          (a : ℝ) := by
        exact_mod_cast hprod_nat
      rw [hprod]
    · intro p _hp
      exact pow_nonneg (Nat.cast_nonneg p) _
  rw [hcast]
  calc
    (∏ p ∈ a.primeFactors, (((a ^ 2).factorization p + 1 : ℕ) : ℝ))
        ≤ ∏ p ∈ a.primeFactors,
          tauSquarePrimeCoeff p *
            (p : ℝ) ^ (((a.factorization p : ℕ) : ℝ) / 4) := hprod_le
    _ = (∏ p ∈ a.primeFactors, tauSquarePrimeCoeff p) *
          ∏ p ∈ a.primeFactors,
            (p : ℝ) ^ (((a.factorization p : ℕ) : ℝ) / 4) := hsplit
    _ ≤ tauSquareQuarterConstant * (a : ℝ) ^ ((1 : ℝ) / 4) := by
          rw [hpow_eq]
          exact mul_le_mul_of_nonneg_right hcoeff
            (Real.rpow_nonneg (Nat.cast_nonneg a) _)

/-! ## The singular series -/

theorem singularSeries_pos (M : ℕ) : 0 < singularSeries M := by
  classical
  unfold singularSeries
  apply mul_pos
  · exact div_pos zero_lt_one zeta2_pos
  · apply Finset.prod_pos
    intro ℓ hℓmem
    have hℓPrime : Nat.Prime ℓ := Nat.prime_of_mem_primeFactors hℓmem
    have h2nat : 2 ≤ ℓ := hℓPrime.two_le
    have h2 : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast h2nat
    have h1lt : (1 : ℝ) < (ℓ : ℝ) := by linarith
    have hinv_lt : (ℓ : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1lt
    have hbase : 0 < 1 - (ℓ : ℝ)⁻¹ := sub_pos.mpr hinv_lt
    have hnum : 0 < (1 - (ℓ : ℝ)⁻¹) ^ 3 := pow_pos hbase 3
    have hsquare_gt : (1 : ℝ) < (ℓ : ℝ) ^ 2 := by nlinarith
    have hinv_square_lt : ((ℓ : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hsquare_gt
    have hden : 0 < 1 - ((ℓ : ℝ) ^ 2)⁻¹ := sub_pos.mpr hinv_square_lt
    exact div_pos hnum hden

end ErdosStraus.Estimates
