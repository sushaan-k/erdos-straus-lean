import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.Tactic
import EscLeanChecks
import EscAnalytic.Counting

/-!
# Applications of the main bound

This module proves the prime, geometric, and large-prime-factor consequences.

Three results from the manuscript:

* `cor:prime-exceptional` (tex 2098-2114): the main exceptional-set bound
  `thm:main` restricts to prime denominators.  Part one
  (`prime_exceptional_of_main`) is elementary: prime denominators are
  a subset of all denominators, so `IsMainBound exceptionalCount` propagates to
  `IsMainBound primeExceptionalCount` through `EscAnalytic.IsMainBound.of_le`.
  Part two (the `≪ π(N)·saving` form, tex 2105-2108) is a conditional Lean proof
  using the cited lower bound `π(N) ≫ N/log N`.

* `prop:large-prime-factor` (tex 2118-2165): the elementary lifting principle.
  The structural core — *every prime divisor of an exceptional integer is itself
  an exceptional prime* is proved in Lean
  (`esExceptional_prime_factor_is_exceptional`, from
  `EscLeanChecks.esExceptional_prime_divisor_of_exceptional`).  The combinatorial
  union bound `E_{>Y}(N) ≤ ∑_{Y<p≤N, p exc} #{n≤N : p∣n}` is also proved.  The
  analytic envelope `∑ (N/p+1) ≪ N(1+log N)·exp(-c(log Y)^{3/4})` is available
  both as an explicit-envelope wrapper and, for the main applications, as a
  consequence of `IsMainBound primeExceptionalCount` by a checked dyadic shell
  summation over exceptional primes.

This file builds on top of `EscAnalytic.Counting` (`exceptionalCount`,
`primeExceptionalCount`, `saving`, `IsMainBound`) and the elementary lifting
lemmas of `EscLeanChecks`.
-/

namespace EscAnalytic

open scoped BigOperators
open Classical

/-! ## Geometric positive integral points

The geometric corollary counts fibres `U_n` that have a positive integral point.
For the affine surface `4xyz = n(xy+xz+yz)`, this is exactly the
cross-multiplied certificate predicate used by `EscLeanChecks`.
-/

/-- Positive integral point on the Erdős-Straus surface `U_n` in the positive
chamber. -/
def positiveIntegralPointOnSurface (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ EscLeanChecks.esCross n x y z

/-- The geometric positive-integral-point carrier agrees with the existing
positive unit-fraction representability predicate. -/
theorem positiveIntegralPointOnSurface_iff_esRepresentable (n : ℕ) (hn : 0 < n) :
    positiveIntegralPointOnSurface n ↔ EscLeanChecks.esRepresentable n := by
  constructor
  · rintro ⟨x, y, z, hx, hy, hz, hcross⟩
    exact ⟨x, y, z, hx, hy, hz,
      EscLeanChecks.esCross_unit_fraction_identity n x y z hn hx hy hz hcross⟩
  · rintro ⟨x, y, z, hx, hy, hz, hident⟩
    refine ⟨x, y, z, hx, hy, hz, ?_⟩
    unfold EscLeanChecks.esCross
    have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    have hxQ : (x : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
    have hyQ : (y : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hy)
    have hzQ : (z : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hz)
    field_simp [hnQ, hxQ, hyQ, hzQ] at hident
    ring_nf at hident
    have hcrossQ :
        ((n * (y * z + x * z + x * y) : ℕ) : ℚ) =
          ((4 * x * y * z : ℕ) : ℚ) := by
      norm_num
      ring_nf
      nlinarith [hident]
    exact_mod_cast hcrossQ

/-- Count of fibres `U_n`, `2 ≤ n ≤ N`, without a positive integral point in
the positive chamber.  The range matches `exceptionalCount`; the manuscript's
`n = 1` endpoint is immaterial for asymptotics and is kept out of the formal
carrier so this corollary composes directly with `thm:main`. -/
noncomputable def geometricExceptionalCount (N : ℕ) : ℕ :=
  ((Finset.Icc (2 : ℕ) N).filter (fun n => ¬ positiveIntegralPointOnSurface n)).card

/-- The geometric exceptional carrier differs from the ordinary exceptional
carrier only by unfolding the geometric positive-point predicate. -/
theorem geometricExceptionalCount_le_exceptionalCount (N : ℕ) :
    geometricExceptionalCount N ≤ exceptionalCount N := by
  classical
  let src : Finset ℕ :=
    (Finset.Icc (2 : ℕ) N).filter (fun n => ¬ positiveIntegralPointOnSurface n)
  let dst : Finset ℕ := (Finset.Icc (2 : ℕ) N).filter EscLeanChecks.esExceptional
  have hsub : src ⊆ dst := by
    intro n hn
    have hnIcc : n ∈ Finset.Icc (2 : ℕ) N := (Finset.mem_filter.mp hn).1
    have hbad : ¬ positiveIntegralPointOnSurface n := (Finset.mem_filter.mp hn).2
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hnIcc).1
    have hnpos : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2) hn2
    have hnotrep : EscLeanChecks.esExceptional n := by
      intro hrep
      exact hbad ((positiveIntegralPointOnSurface_iff_esRepresentable n hnpos).mpr hrep)
    exact Finset.mem_filter.mpr ⟨hnIcc, hnotrep⟩
  calc
    geometricExceptionalCount N = src.card := rfl
    _ ≤ dst.card := Finset.card_le_card hsub
    _ = exceptionalCount N := by rfl

theorem geometricExceptionalCount_cast_le_exceptionalCount (N : ℕ) :
    (geometricExceptionalCount N : ℝ) ≤ (exceptionalCount N : ℝ) := by
  exact_mod_cast geometricExceptionalCount_le_exceptionalCount N

/-- Geometric form of the main exceptional-set bound on the formal `2 ≤ n ≤ N`
carrier. -/
theorem geometric_exceptional_of_main (h : IsMainBound exceptionalCount) :
    IsMainBound geometricExceptionalCount :=
  IsMainBound.of_le geometricExceptionalCount_le_exceptionalCount h

/-! ## Fixed-numerator certificate core

The asymptotic fixed-numerator theorem also needs fixed-`m` analytic mass,
tensorisation, increment, dependency, and transfer estimates.  The elementary
certificate algebra itself is already checked in `EscLeanChecks`; the wrappers
below expose exactly the paper's `q = ma - 1`, `e ∣ a^2`,
`n ≡ -me (mod q)` bridge at the analytic-application layer.
-/

/-- `m/n` is a sum of three positive unit fractions. -/
def fixedNumeratorRepresentable (m n : ℕ) : Prop :=
  ∃ x y z : ℕ,
    0 < x ∧ 0 < y ∧ 0 < z ∧
    (m : ℚ) / (n : ℚ) =
      1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

/-- `E_m(N)`: fixed-numerator exceptional count from the manuscript's
fixed-`m` application section. -/
noncomputable def fixedNumeratorExceptionalCount (m N : ℕ) : ℕ :=
  ((Finset.Icc (1 : ℕ) N).filter (fun n => ¬ fixedNumeratorRepresentable m n)).card

/-- Trivial finite carrier bound for the fixed-numerator exceptional count. -/
theorem fixedNumeratorExceptionalCount_le_self (m N : ℕ) :
    fixedNumeratorExceptionalCount m N ≤ N := by
  classical
  unfold fixedNumeratorExceptionalCount
  calc
    ((Finset.Icc (1 : ℕ) N).filter (fun n => ¬ fixedNumeratorRepresentable m n)).card
        ≤ (Finset.Icc (1 : ℕ) N).card :=
          Finset.card_filter_le _ _
    _ = N := by
      rw [Nat.card_Icc]
      omega

/-- Fixed-numerator fan certificate: if `q = ma - 1`, `e ∣ a^2`, and
`n ≡ -me (mod q)`, then the displayed denominators represent `m/n`. -/
theorem fixed_numerator_representable_of_fixed_fan
    (m n a e : ℕ)
    (hm : 2 ≤ m) (hn : 0 < n) (ha : 0 < a) (he : 0 < e)
    (hedvd : e ∣ a ^ 2)
    (hcong : EscLeanChecks.fixedQ m a ∣ n + m * e) :
    fixedNumeratorRepresentable m n :=
  EscLeanChecks.fixedFan_positive_unit_fractions m n a e hm hn ha he hedvd hcong

/-- Fixed-numerator fan certificate in the manuscript's `Q = ma - 1` notation.
If `m * a = Q + 1`, `e ∣ a^2`, and `Q ∣ n + me`, then the same displayed
denominators represent `m/n`. -/
theorem fixed_numerator_representable_of_Q_add_one_eq_mul
    (m n Q a e : ℕ)
    (hm : 2 ≤ m) (hn : 0 < n) (ha : 0 < a) (he : 0 < e)
    (hQ : m * a = Q + 1)
    (hedvd : e ∣ a ^ 2)
    (hcong : Q ∣ n + m * e) :
    fixedNumeratorRepresentable m n := by
  have hfixedQ : EscLeanChecks.fixedQ m a = Q := by
    unfold EscLeanChecks.fixedQ
    omega
  exact fixed_numerator_representable_of_fixed_fan m n a e hm hn ha he hedvd
    (by simpa [hfixedQ] using hcong)

/-- Certificate-progression version of the fixed-numerator certificate core. -/
theorem fixed_numerator_representable_of_certificate_progression
    (m n Q r s : ℕ)
    (hm : 2 ≤ m) (hn : 0 < n) (hr : 0 < r) (hs : 0 < s)
    (hprogression : m * (r * s) ∣ Q + 1)
    (hcong : Q ∣ n + m * (r * s ^ 2)) :
    fixedNumeratorRepresentable m n := by
  rcases EscLeanChecks.fixedFan_positive_unit_fractions_of_certificate_progression
      m n Q r s hm hn hr hs hprogression hcong with
    ⟨_a, x, y, z, _ha, _hma, hx, hy, hz, hident⟩
  exact ⟨x, y, z, hx, hy, hz, hident⟩

/-- Base-plus-residual fixed-numerator certificate core, matching the event
decomposition used in the fixed-`m` certificate family. -/
theorem fixed_numerator_representable_of_base_residual_progression
    (m n dMinus dPlus p r s : ℕ)
    (hm : 2 ≤ m) (hn : 0 < n) (hr : 0 < r) (hs : 0 < s)
    (hcop : Nat.Coprime dMinus (dPlus * p))
    (hprogression : m * (r * s) ∣ dMinus * (dPlus * p) + 1)
    (hbase : dMinus ∣ n + m * (r * s ^ 2))
    (hresidual : dPlus * p ∣ n + m * (r * s ^ 2)) :
    fixedNumeratorRepresentable m n := by
  rcases EscLeanChecks.fixedFan_positive_unit_fractions_of_base_residual_progression
      m n dMinus dPlus p r s hm hn hr hs hcop hprogression hbase hresidual with
    ⟨_a, x, y, z, _ha, _hma, hx, hy, hz, hident⟩
  exact ⟨x, y, z, hx, hy, hz, hident⟩

/-- Conditioned base-class/residual-hit fixed-numerator certificate core. -/
theorem fixed_numerator_representable_of_conditioned_base_residual_hit
    (m n Pz b dMinus dPlus p r s : ℕ)
    (hm : 2 ≤ m) (hn : 0 < n) (hr : 0 < r) (hs : 0 < s)
    (hcop : Nat.Coprime dMinus (dPlus * p))
    (hdMinusDvdPz : dMinus ∣ Pz)
    (hnbase : n ≡ b [MOD Pz])
    (hsmall : b + m * (r * s ^ 2) ≡ 0 [MOD dMinus])
    (hprogression : m * (r * s) ∣ dMinus * (dPlus * p) + 1)
    (hresidual : dPlus * p ∣ n + m * (r * s ^ 2)) :
    fixedNumeratorRepresentable m n := by
  rcases EscLeanChecks.fixedFan_positive_unit_fractions_of_conditioned_base_residual_hit
      m n Pz b dMinus dPlus p r s hm hn hr hs hcop hdMinusDvdPz hnbase hsmall
      hprogression hresidual with
    ⟨_a, x, y, z, _ha, _hma, hx, hy, hz, hident⟩
  exact ⟨x, y, z, hx, hy, hz, hident⟩

/-! ## Prime-counting function

We define `primePi N = #{p ≤ N : p prime}` directly and prove below that it is
the same carrier as Mathlib's `Nat.primeCounting`.  This pins the manuscript's
`π(N)` notation to the standard library object while keeping the local notation
used by the existing application statements. -/

/-- `π(N)`: the number of primes `p ≤ N`. -/
noncomputable def primePi (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter Nat.Prime).card

/-- The local `π(N)` carrier agrees with Mathlib's standard prime-counting
function. -/
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

/-- The prime-counting carrier is nonnegative after coercion to `ℝ`. -/
theorem primePi_nonneg (N : ℕ) : 0 ≤ (primePi N : ℝ) := by
  exact Nat.cast_nonneg _

/-- The local prime-counting carrier is monotone. -/
theorem primePi_mono {M N : ℕ} (hMN : M ≤ N) : primePi M ≤ primePi N := by
  classical
  unfold primePi
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hp.1).1, le_trans (Finset.mem_Icc.mp hp.1).2 hMN⟩,
    hp.2⟩

/-- Bertrand's postulate gives a fully checked logarithmic fallback:
there are at least `k` primes up to `2^k`.

This is far weaker than the Chebyshev-scale theorem `π(N) ≫ N/log N`, but
it upgrades the prime-counting carrier from mere unboundedness to an explicit
quantitative lower bound available without any project axiom. -/
theorem primePi_two_pow_lower (k : ℕ) :
    k ≤ primePi (2 ^ k) := by
  classical
  induction k with
  | zero =>
      exact Nat.zero_le _
  | succ k ih =>
      rcases Nat.exists_prime_lt_and_le_two_mul (2 ^ k) (pow_ne_zero _ (by norm_num)) with
        ⟨p, hpPrime, hp_gt, hp_le⟩
      let small : Finset ℕ := (Finset.Icc (1 : ℕ) (2 ^ k)).filter Nat.Prime
      let big : Finset ℕ := (Finset.Icc (1 : ℕ) (2 ^ (k + 1))).filter Nat.Prime
      have hsmall_eq : small.card = primePi (2 ^ k) := rfl
      have hbig_eq : big.card = primePi (2 ^ (k + 1)) := rfl
      have hp_le_pow : p ≤ 2 ^ (k + 1) := by
        simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hp_le
      have hp_big : p ∈ big := by
        dsimp [big]
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr
            ⟨le_trans (by norm_num : 1 ≤ 2) hpPrime.two_le, hp_le_pow⟩,
            hpPrime⟩
      have hp_not_small : p ∉ small := by
        dsimp [small]
        intro hp_small
        have hp_le_small : p ≤ 2 ^ k :=
          (Finset.mem_Icc.mp (Finset.mem_filter.mp hp_small).1).2
        exact (not_le_of_gt hp_gt) hp_le_small
      have hsmall_subset_big : small ⊆ big := by
        intro q hq
        have hqIcc : q ∈ Finset.Icc (1 : ℕ) (2 ^ k) :=
          (Finset.mem_filter.mp hq).1
        have hqPrime : Nat.Prime q := (Finset.mem_filter.mp hq).2
        have hpow_mono : 2 ^ k ≤ 2 ^ (k + 1) := by
          exact Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.le_succ k)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr
            ⟨(Finset.mem_Icc.mp hqIcc).1,
              le_trans (Finset.mem_Icc.mp hqIcc).2 hpow_mono⟩,
            hqPrime⟩
      have hinsert_subset : insert p small ⊆ big := by
        intro q hq
        rw [Finset.mem_insert] at hq
        rcases hq with rfl | hqsmall
        · exact hp_big
        · exact hsmall_subset_big hqsmall
      have hcard : primePi (2 ^ k) + 1 ≤ primePi (2 ^ (k + 1)) := by
        calc
          primePi (2 ^ k) + 1 = (insert p small).card := by
            rw [← hsmall_eq, Finset.card_insert_of_not_mem hp_not_small]
          _ ≤ big.card := Finset.card_le_card hinsert_subset
          _ = primePi (2 ^ (k + 1)) := hbig_eq
      exact (Nat.succ_le_succ ih).trans hcard

/-- A logarithmic lower bound for `π(N)` obtained only from Bertrand's postulate
and monotonicity of the finite carrier.  The Chebyshev-scale lower bound
`π(N) ≫ N/log N` is proved later through the finite prime-log carrier. -/
theorem primePi_natLog_lower (N : ℕ) :
    Nat.log 2 N ≤ primePi N := by
  by_cases hN : N = 0
  · simp [hN]
  · have hpow : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN
    exact (primePi_two_pow_lower (Nat.log 2 N)).trans (primePi_mono hpow)

/-- Real-valued form of the Bertrand logarithmic lower fallback. -/
theorem primePi_natLog_lower_cast (N : ℕ) :
    (Nat.log 2 N : ℝ) ≤ (primePi N : ℝ) := by
  exact_mod_cast primePi_natLog_lower N

/-- Bertrand's postulate also gives a real-logarithmic lower bound for the
prime-counting carrier.  This remains much weaker than `π(N) ≫ N/log N`, but it
is a fully checked quantitative replacement for any argument that only needs
logarithmic growth of the denominator. -/
theorem real_log_le_two_log_two_mul_natLog (N : ℕ) (hN : 4 ≤ N) :
    Real.log (N : ℝ) ≤ 2 * Real.log 2 * (Nat.log 2 N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 4) hN)
  have hlt_nat : N < 2 ^ (Nat.log 2 N).succ :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  have hlt_real : (N : ℝ) < (2 : ℝ) ^ (Nat.log 2 N).succ := by
    exact_mod_cast hlt_nat
  have hlog_le_succ :
      Real.log (N : ℝ) ≤ ((Nat.log 2 N).succ : ℝ) * Real.log 2 := by
    have hlog_lt := Real.log_lt_log hNpos hlt_real
    have hlog_le := le_of_lt hlog_lt
    simpa [Real.log_pow] using hlog_le
  have hnatlog_ge_two : 2 ≤ Nat.log 2 N := by
    exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) (by simpa using hN)
  have hsucc_le_two :
      ((Nat.log 2 N).succ : ℝ) ≤ 2 * (Nat.log 2 N : ℝ) := by
    exact_mod_cast (by omega : (Nat.log 2 N).succ ≤ 2 * Nat.log 2 N)
  have hlog_two_nonneg : 0 ≤ Real.log 2 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  calc
    Real.log (N : ℝ)
        ≤ ((Nat.log 2 N).succ : ℝ) * Real.log 2 := hlog_le_succ
    _ ≤ (2 * (Nat.log 2 N : ℝ)) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hsucc_le_two hlog_two_nonneg
    _ = 2 * Real.log 2 * (Nat.log 2 N : ℝ) := by ring

/-- Fully checked Bertrand-scale lower bound `π(N) ≳ log N`.  The paper's
normalization still needs the stronger Chebyshev-scale theorem below, but this
removes any need to assume mere logarithmic growth of `π`. -/
theorem primePi_realLog_lower_bertrand :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 4 ≤ N →
      c₀ * Real.log (N : ℝ) ≤ (primePi N : ℝ) := by
  refine ⟨(2 * Real.log 2)⁻¹, ?_, ?_⟩
  · exact inv_pos.mpr
      (mul_pos (by norm_num : (0 : ℝ) < 2)
        (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  · intro N hN
    have hden_pos : 0 < 2 * Real.log 2 :=
      mul_pos (by norm_num : (0 : ℝ) < 2)
        (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    have hlog := real_log_le_two_log_two_mul_natLog N hN
    have hnat := primePi_natLog_lower_cast N
    calc
      (2 * Real.log 2)⁻¹ * Real.log (N : ℝ)
          ≤ (2 * Real.log 2)⁻¹ *
              (2 * Real.log 2 * (Nat.log 2 N : ℝ)) :=
            mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hden_pos.le)
      _ = (Nat.log 2 N : ℝ) := by
            field_simp [ne_of_gt hden_pos]
      _ ≤ (primePi N : ℝ) := hnat

/-- Trivial finite-carrier bound `π(N) ≤ N`. -/
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

/-- Real-valued form of the trivial finite-carrier bound `π(N) ≤ N`. -/
theorem primePi_cast_le_self (N : ℕ) : (primePi N : ℝ) ≤ (N : ℝ) := by
  exact_mod_cast primePi_le_self N

/-- Exceptional primes are a finite subset of all primes up to the same cutoff. -/
theorem primeExceptionalCount_le_primePi (N : ℕ) :
    primeExceptionalCount N ≤ primePi N := by
  classical
  unfold primeExceptionalCount primePi
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨Finset.mem_Icc.mpr
    ⟨le_trans (by norm_num : 1 ≤ 2) (Finset.mem_Icc.mp hp.1).1,
      (Finset.mem_Icc.mp hp.1).2⟩, hp.2.1⟩

/-- Real-valued form of `primeExceptionalCount_le_primePi`. -/
theorem primeExceptionalCount_cast_le_primePi (N : ℕ) :
    (primeExceptionalCount N : ℝ) ≤ (primePi N : ℝ) := by
  exact_mod_cast primeExceptionalCount_le_primePi N

/-- `π(N)` is positive once `N ≥ 2`, witnessed by the prime `2`. -/
theorem primePi_pos_of_two_le {N : ℕ} (hN : 2 ≤ N) : 0 < primePi N := by
  classical
  unfold primePi
  exact Finset.card_pos.mpr
    ⟨2, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by norm_num, hN⟩, Nat.prime_two⟩⟩

/-- There are no primes up to `N` when `N < 2`. -/
theorem primePi_eq_zero_of_lt_two {N : ℕ} (hN : N < 2) : primePi N = 0 := by
  classical
  unfold primePi
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro p hp
  rw [Finset.mem_filter] at hp
  have hp_le_one : p ≤ 1 := by
    have hp_le_N : p ≤ N := (Finset.mem_Icc.mp hp.1).2
    omega
  exact not_lt_of_ge hp_le_one hp.2.one_lt

/-- The local prime-counting carrier is positive exactly from the first prime
onward. -/
theorem primePi_pos_iff_two_le {N : ℕ} : 0 < primePi N ↔ 2 ≤ N := by
  constructor
  · intro hpos
    by_contra hN
    have hlt : N < 2 := Nat.lt_of_not_ge hN
    rw [primePi_eq_zero_of_lt_two hlt] at hpos
    exact Nat.lt_irrefl 0 hpos
  · exact primePi_pos_of_two_le

/-- The local prime-counting carrier vanishes exactly below the first prime. -/
theorem primePi_eq_zero_iff_lt_two {N : ℕ} : primePi N = 0 ↔ N < 2 := by
  constructor
  · intro hzero
    by_contra hN
    have htwo : 2 ≤ N := Nat.le_of_not_gt hN
    have hpos := primePi_pos_of_two_le htwo
    rw [hzero] at hpos
    exact Nat.lt_irrefl 0 hpos
  · exact primePi_eq_zero_of_lt_two

/-- Real-valued positivity criterion for the local prime-counting carrier. -/
theorem primePi_cast_pos_iff_two_le {N : ℕ} : 0 < (primePi N : ℝ) ↔ 2 ≤ N := by
  rw [Nat.cast_pos]
  exact primePi_pos_iff_two_le

/-- Real-valued nonzero criterion for the local prime-counting carrier. -/
theorem primePi_cast_ne_zero_of_two_le {N : ℕ} (hN : 2 ≤ N) :
    (primePi N : ℝ) ≠ 0 := by
  exact ne_of_gt (primePi_cast_pos_iff_two_le.mpr hN)

/-- Real-valued nonzero criterion for the local prime-counting carrier. -/
theorem primePi_cast_ne_zero_iff_two_le {N : ℕ} : (primePi N : ℝ) ≠ 0 ↔ 2 ≤ N := by
  constructor
  · intro hne
    by_contra hN
    have hlt : N < 2 := Nat.lt_of_not_ge hN
    have hzero : (primePi N : ℝ) = 0 := by
      simp [primePi_eq_zero_of_lt_two hlt]
    exact hne hzero
  · exact primePi_cast_ne_zero_of_two_le

/-- Bertrand-scale prime-counting lower bound bundled with the carrier side
conditions used in weaker prime-normalized estimates.  This is fully checked
but only gives `π(N) ≳ log N`, not the PNT-scale `π(N) ≳ N/log N` used in the
final prime-density corollary. -/
theorem primePi_realLog_lower_bertrand_with_carrier_bounds :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 4 ≤ N →
      0 < Real.log (N : ℝ) ∧
        0 < (primePi N : ℝ) ∧
        c₀ * Real.log (N : ℝ) ≤ (primePi N : ℝ) ∧
        (primePi N : ℝ) ≤ (N : ℝ) ∧
        |(primePi N : ℝ)| ≤ (N : ℝ) := by
  rcases primePi_realLog_lower_bertrand with ⟨c₀, hc₀, hpi⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro N hN
  have hN_gt_one : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (by omega : 1 < N)
  have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos hN_gt_one
  have hpi_pos : 0 < (primePi N : ℝ) := by
    exact_mod_cast primePi_pos_of_two_le (by omega : 2 ≤ N)
  have hupper : (primePi N : ℝ) ≤ (N : ℝ) := primePi_cast_le_self N
  exact ⟨hlog_pos, hpi_pos, hpi N hN, hupper, by
    rw [abs_of_nonneg hpi_pos.le]
    exact hupper⟩

/-- A bare Bertrand-scale logarithmic lower bound for `primePi` gives the
carrier-bundled version with finite-carrier side conditions. -/
theorem primePi_realLog_lower_bertrand_with_carrier_bounds_of_bound
    (h :
      ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 4 ≤ N →
        c₀ * Real.log (N : ℝ) ≤ (primePi N : ℝ)) :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 4 ≤ N →
      0 < Real.log (N : ℝ) ∧
        0 < (primePi N : ℝ) ∧
        c₀ * Real.log (N : ℝ) ≤ (primePi N : ℝ) ∧
        (primePi N : ℝ) ≤ (N : ℝ) ∧
        |(primePi N : ℝ)| ≤ (N : ℝ) := by
  rcases h with ⟨c₀, hc₀, hpi⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro N hN
  have hN_gt_one : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (by omega : 1 < N)
  have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos hN_gt_one
  have hpi_pos : 0 < (primePi N : ℝ) := by
    exact_mod_cast primePi_pos_of_two_le (by omega : 2 ≤ N)
  have hupper : (primePi N : ℝ) ≤ (N : ℝ) := primePi_cast_le_self N
  exact ⟨hlog_pos, hpi_pos, hpi N hN, hupper, by
    rw [abs_of_nonneg hpi_pos.le]
    exact hupper⟩

/-- Forget the checked side conditions from the bundled Bertrand-scale
`primePi` lower bound. -/
theorem primePi_realLog_lower_bertrand_bound_of_carrier_bounds
    (h :
      ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 4 ≤ N →
        0 < Real.log (N : ℝ) ∧
          0 < (primePi N : ℝ) ∧
          c₀ * Real.log (N : ℝ) ≤ (primePi N : ℝ) ∧
          (primePi N : ℝ) ≤ (N : ℝ) ∧
          |(primePi N : ℝ)| ≤ (N : ℝ)) :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 4 ≤ N →
      c₀ * Real.log (N : ℝ) ≤ (primePi N : ℝ) := by
  rcases h with ⟨c₀, hc₀, hcarrier⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro N hN
  exact (hcarrier N hN).2.2.1

/-- Bare and carrier-bundled Bertrand-scale `primePi` lower bounds have the same
analytic content. -/
theorem primePi_realLog_lower_bertrand_bound_iff_carrier_bounds :
    (∃ c₀ > (0 : ℝ), ∀ N : ℕ, 4 ≤ N →
      c₀ * Real.log (N : ℝ) ≤ (primePi N : ℝ)) ↔
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 4 ≤ N →
      0 < Real.log (N : ℝ) ∧
        0 < (primePi N : ℝ) ∧
        c₀ * Real.log (N : ℝ) ≤ (primePi N : ℝ) ∧
        (primePi N : ℝ) ≤ (N : ℝ) ∧
        |(primePi N : ℝ)| ≤ (N : ℝ) := by
  constructor
  · exact primePi_realLog_lower_bertrand_with_carrier_bounds_of_bound
  · exact primePi_realLog_lower_bertrand_bound_of_carrier_bounds

/-- There are no exceptional primes below the first prime. -/
theorem primeExceptionalCount_eq_zero_of_lt_two {N : ℕ} (hN : N < 2) :
    primeExceptionalCount N = 0 := by
  exact Nat.eq_zero_of_le_zero (by
    simpa [primePi_eq_zero_of_lt_two hN] using primeExceptionalCount_le_primePi N)

/-- Prime-exceptional fraction among primes, with the convention inherited from
real division when `π(N)=0`.  All nontrivial uses below are for `N ≥ 2`. -/
noncomputable def primeExceptionalRatio (N : ℕ) : ℝ :=
  (primeExceptionalCount N : ℝ) / (primePi N : ℝ)

/-- The prime-exceptional fraction is nonnegative. -/
theorem primeExceptionalRatio_nonneg (N : ℕ) :
    0 ≤ primeExceptionalRatio N := by
  unfold primeExceptionalRatio
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The prime-exceptional fraction is bounded by one once primes exist in the
denominator.  This is unconditional and uses only the subset relation
`𝒫_exc(N) ⊆ {p ≤ N : p prime}`. -/
theorem primeExceptionalRatio_le_one_of_two_le {N : ℕ} (hN : 2 ≤ N) :
    primeExceptionalRatio N ≤ 1 := by
  unfold primeExceptionalRatio
  have hpi_pos : 0 < (primePi N : ℝ) := by
    exact_mod_cast primePi_pos_of_two_le hN
  rw [div_le_iff₀ hpi_pos]
  simpa using primeExceptionalCount_cast_le_primePi N

/-- The normalized exceptional-prime ratio lies in the unit interval whenever
the denominator prime-counting carrier is nonempty. -/
theorem primeExceptionalRatio_mem_Icc_of_two_le {N : ℕ} (hN : 2 ≤ N) :
    primeExceptionalRatio N ∈ Set.Icc 0 1 :=
  ⟨primeExceptionalRatio_nonneg N, primeExceptionalRatio_le_one_of_two_le hN⟩

/-- Absolute-value form of the unconditional prime-exceptional fraction bound. -/
theorem abs_primeExceptionalRatio_le_one_of_two_le {N : ℕ} (hN : 2 ≤ N) :
    |primeExceptionalRatio N| ≤ 1 := by
  rw [abs_of_nonneg (primeExceptionalRatio_nonneg N)]
  exact primeExceptionalRatio_le_one_of_two_le hN

/-- The local prime-counting carrier tends to infinity.  This is the exact
Mathlib unboundedness theorem transported across `primePi_eq_primeCounting`.
The stronger `π(N) ≫ N/log N` lower bound used for the prime-normalized saving
is supplied below through the finite prime-log carrier. -/
theorem primePi_tendsto_atTop :
    Filter.Tendsto primePi Filter.atTop Filter.atTop := by
  have hfun : primePi = fun N : ℕ => Nat.primeCounting N := by
    funext N
    exact primePi_eq_primeCounting N
  rw [hfun]
  exact Nat.tensto_primeCounting

/-- Unconditional eventual lower bound for the local prime-counting carrier.
This is much weaker than the Chebyshev-scale lower bound below, but it proves that
the denominator carrier eventually exceeds any fixed finite threshold. -/
theorem primePi_eventually_ge_nat (A : ℕ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → A ≤ primePi N := by
  exact (Filter.tendsto_atTop_atTop.mp primePi_tendsto_atTop) A

/-- Real-cast version of `primePi_eventually_ge_nat`. -/
theorem primePi_eventually_cast_ge_nat (A : ℕ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (A : ℝ) ≤ (primePi N : ℝ) := by
  rcases primePi_eventually_ge_nat A with ⟨N₀, hN₀⟩
  exact ⟨N₀, fun N hN => by exact_mod_cast hN₀ N hN⟩

/-- Real-valued prime-counting carrier `π(x) = #{p ≤ x}`. -/
noncomputable def realPrimePi (x : ℝ) : ℕ :=
  ((Finset.Icc (1 : ℕ) ⌊x⌋₊).filter Nat.Prime).card

/-- The real-cutoff carrier is exactly the natural carrier at the floored
cutoff. -/
theorem realPrimePi_eq_primePi_floor (x : ℝ) :
    realPrimePi x = primePi ⌊x⌋₊ := by
  unfold realPrimePi primePi
  rfl

/-- The real-cutoff prime-counting carrier is monotone. -/
theorem realPrimePi_mono {x y : ℝ} (hxy : x ≤ y) :
    realPrimePi x ≤ realPrimePi y := by
  rw [realPrimePi_eq_primePi_floor x, realPrimePi_eq_primePi_floor y]
  exact primePi_mono (Nat.floor_mono hxy)

/-- The real-cutoff carrier is nonnegative after coercion to `ℝ`. -/
theorem realPrimePi_nonneg (x : ℝ) : 0 ≤ (realPrimePi x : ℝ) := by
  exact Nat.cast_nonneg _

/-- Trivial finite-carrier upper bound for the real-cutoff prime-counting
function. -/
theorem realPrimePi_le_floor (x : ℝ) :
    realPrimePi x ≤ ⌊x⌋₊ := by
  rw [realPrimePi_eq_primePi_floor x]
  exact primePi_le_self ⌊x⌋₊

/-- Real-valued form of the finite-carrier upper bound for `realPrimePi`. -/
theorem realPrimePi_cast_le_floor (x : ℝ) :
    (realPrimePi x : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
  exact_mod_cast realPrimePi_le_floor x

/-- Absolute-value form of the finite-carrier upper bound for `realPrimePi`. -/
theorem abs_realPrimePi_cast_le_floor (x : ℝ) :
    |(realPrimePi x : ℝ)| ≤ (⌊x⌋₊ : ℝ) := by
  rw [abs_of_nonneg (realPrimePi_nonneg x)]
  exact realPrimePi_cast_le_floor x

/-- Finite-carrier package for the real-cutoff prime-counting function.  The
Chebyshev-scale lower bound is supplied separately below; the
range and absolute-value facts are purely finite bookkeeping. -/
theorem realPrimePi_finite_carrier_bounds (x : ℝ) :
    0 ≤ (realPrimePi x : ℝ) ∧
      (realPrimePi x : ℝ) ≤ (⌊x⌋₊ : ℝ) ∧
      |(realPrimePi x : ℝ)| ≤ (⌊x⌋₊ : ℝ) :=
  ⟨realPrimePi_nonneg x, realPrimePi_cast_le_floor x,
    abs_realPrimePi_cast_le_floor x⟩

/-- For `x ≥ 2`, the floored cutoff is at least `x/2`. -/
theorem half_le_floor_of_two_le {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have hfloor_gt : x - 1 < (⌊x⌋₊ : ℝ) := Nat.sub_one_lt_floor x
  have hhalf_le_sub : x / 2 ≤ x - 1 := by nlinarith
  exact le_trans hhalf_le_sub hfloor_gt.le

/-- Bertrand-scale logarithmic lower bound for the real-cutoff prime-counting
carrier.  This is fully checked and does not use the Chebyshev-scale route;
the price is that it proves only `π(x) ≳ log x`, not `π(x) ≳ x/log x`. -/
theorem realPrimePi_realLog_lower_bertrand :
    ∃ c₀ > (0 : ℝ), ∀ x : ℝ, 8 ≤ x →
      c₀ * Real.log x ≤ (realPrimePi x : ℝ) := by
  rcases primePi_realLog_lower_bertrand with ⟨c₀, hc₀, hpi⟩
  refine ⟨c₀ / 2, by positivity, ?_⟩
  intro x hx
  have hxpos : 0 < x := by linarith
  have hfloor_ge_four : 4 ≤ ⌊x⌋₊ := by
    exact Nat.le_floor (by linarith : (4 : ℝ) ≤ x)
  have hfloor_pos : 0 < (⌊x⌋₊ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 4) hfloor_ge_four)
  have hhalf_pos : 0 < x / 2 := by positivity
  have hhalf_le_floor : x / 2 ≤ (⌊x⌋₊ : ℝ) :=
    half_le_floor_of_two_le (by linarith : (2 : ℝ) ≤ x)
  have hlog_half_le_floor :
      Real.log (x / 2) ≤ Real.log (⌊x⌋₊ : ℝ) :=
    Real.log_le_log hhalf_pos hhalf_le_floor
  have hlog_four_le : Real.log (4 : ℝ) ≤ Real.log x :=
    Real.log_le_log (by norm_num) (by linarith : (4 : ℝ) ≤ x)
  have hlog_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
      _ = 2 * Real.log 2 := by
          rw [Real.log_pow]
          norm_num
  have hlogx_ge_two_log_two : 2 * Real.log 2 ≤ Real.log x := by
    simpa [hlog_four] using hlog_four_le
  have hlog_half_eq : Real.log (x / 2) = Real.log x - Real.log 2 := by
    rw [Real.log_div (ne_of_gt hxpos) (by norm_num : (2 : ℝ) ≠ 0)]
  have hhalf_log : (1 / 2 : ℝ) * Real.log x ≤ Real.log (x / 2) := by
    rw [hlog_half_eq]
    nlinarith
  have hpi_floor := hpi ⌊x⌋₊ hfloor_ge_four
  rw [realPrimePi_eq_primePi_floor]
  calc
    (c₀ / 2) * Real.log x
        = c₀ * ((1 / 2 : ℝ) * Real.log x) := by ring
    _ ≤ c₀ * Real.log (x / 2) :=
        mul_le_mul_of_nonneg_left hhalf_log hc₀.le
    _ ≤ c₀ * Real.log (⌊x⌋₊ : ℝ) :=
        mul_le_mul_of_nonneg_left hlog_half_le_floor hc₀.le
    _ ≤ (primePi ⌊x⌋₊ : ℝ) := hpi_floor

/-- Real-cutoff Bertrand lower bound bundled with finite-carrier side
conditions. -/
theorem realPrimePi_realLog_lower_bertrand_with_carrier_bounds :
    ∃ c₀ > (0 : ℝ), ∀ x : ℝ, 8 ≤ x →
      0 < Real.log x ∧
        0 ≤ (realPrimePi x : ℝ) ∧
        c₀ * Real.log x ≤ (realPrimePi x : ℝ) ∧
        (realPrimePi x : ℝ) ≤ (⌊x⌋₊ : ℝ) ∧
        |(realPrimePi x : ℝ)| ≤ (⌊x⌋₊ : ℝ) := by
  rcases realPrimePi_realLog_lower_bertrand with ⟨c₀, hc₀, hlower⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro x hx
  have hx_gt_one : 1 < x := by linarith
  have hlog_pos : 0 < Real.log x := Real.log_pos hx_gt_one
  exact ⟨hlog_pos, realPrimePi_nonneg x, hlower x hx,
    realPrimePi_cast_le_floor x, abs_realPrimePi_cast_le_floor x⟩

/-- A bare Bertrand-scale logarithmic lower bound for the real-cutoff
prime-counting carrier gives the bundled finite-carrier side conditions. -/
theorem realPrimePi_realLog_lower_bertrand_with_carrier_bounds_of_bound
    (h :
      ∃ c₀ > (0 : ℝ), ∀ x : ℝ, 8 ≤ x →
        c₀ * Real.log x ≤ (realPrimePi x : ℝ)) :
    ∃ c₀ > (0 : ℝ), ∀ x : ℝ, 8 ≤ x →
      0 < Real.log x ∧
        0 ≤ (realPrimePi x : ℝ) ∧
        c₀ * Real.log x ≤ (realPrimePi x : ℝ) ∧
        (realPrimePi x : ℝ) ≤ (⌊x⌋₊ : ℝ) ∧
        |(realPrimePi x : ℝ)| ≤ (⌊x⌋₊ : ℝ) := by
  rcases h with ⟨c₀, hc₀, hlower⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro x hx
  have hx_gt_one : 1 < x := by linarith
  have hlog_pos : 0 < Real.log x := Real.log_pos hx_gt_one
  exact ⟨hlog_pos, realPrimePi_nonneg x, hlower x hx,
    realPrimePi_cast_le_floor x, abs_realPrimePi_cast_le_floor x⟩

/-- Forget the checked side conditions from the bundled Bertrand-scale
real-cutoff prime-counting lower bound. -/
theorem realPrimePi_realLog_lower_bertrand_bound_of_carrier_bounds
    (h :
      ∃ c₀ > (0 : ℝ), ∀ x : ℝ, 8 ≤ x →
        0 < Real.log x ∧
          0 ≤ (realPrimePi x : ℝ) ∧
          c₀ * Real.log x ≤ (realPrimePi x : ℝ) ∧
          (realPrimePi x : ℝ) ≤ (⌊x⌋₊ : ℝ) ∧
          |(realPrimePi x : ℝ)| ≤ (⌊x⌋₊ : ℝ)) :
    ∃ c₀ > (0 : ℝ), ∀ x : ℝ, 8 ≤ x →
      c₀ * Real.log x ≤ (realPrimePi x : ℝ) := by
  rcases h with ⟨c₀, hc₀, hcarrier⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro x hx
  exact (hcarrier x hx).2.2.1

/-- Bare and carrier-bundled Bertrand-scale real-cutoff prime-counting lower
bounds have the same analytic content. -/
theorem realPrimePi_realLog_lower_bertrand_bound_iff_carrier_bounds :
    (∃ c₀ > (0 : ℝ), ∀ x : ℝ, 8 ≤ x →
      c₀ * Real.log x ≤ (realPrimePi x : ℝ)) ↔
    ∃ c₀ > (0 : ℝ), ∀ x : ℝ, 8 ≤ x →
      0 < Real.log x ∧
        0 ≤ (realPrimePi x : ℝ) ∧
        c₀ * Real.log x ≤ (realPrimePi x : ℝ) ∧
        (realPrimePi x : ℝ) ≤ (⌊x⌋₊ : ℝ) ∧
        |(realPrimePi x : ℝ)| ≤ (⌊x⌋₊ : ℝ) := by
  constructor
  · exact realPrimePi_realLog_lower_bertrand_with_carrier_bounds_of_bound
  · exact realPrimePi_realLog_lower_bertrand_bound_of_carrier_bounds

/-- At natural inputs, the real-valued carrier agrees with the local natural
prime-counting carrier. -/
theorem realPrimePi_natCast_eq_primePi (N : ℕ) :
    realPrimePi (N : ℝ) = primePi N := by
  classical
  unfold realPrimePi primePi
  simp

/-- At natural inputs, the real-valued carrier agrees with Mathlib's standard
prime-counting function. -/
theorem realPrimePi_natCast_eq_primeCounting (N : ℕ) :
    realPrimePi (N : ℝ) = Nat.primeCounting N := by
  rw [realPrimePi_natCast_eq_primePi, primePi_eq_primeCounting]

/-- Chebyshev's first function at natural cutoffs, in the finite carrier
normalization needed to prove `π(N) ≫ N / log N`. -/
noncomputable def primeTheta (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc (1 : ℕ) N).filter Nat.Prime, Real.log (p : ℝ)

/-- Chebyshev's second function at natural cutoffs, expressed through Mathlib's
von Mangoldt carrier.  This is the internal carrier needed for a future
central-binomial proof of the Chebyshev lower bound. -/
noncomputable def chebyshevPsi (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc (1 : ℕ) N, ArithmeticFunction.vonMangoldt n

/-- The finite Chebyshev psi carrier is nonnegative. -/
theorem chebyshevPsi_nonneg (N : ℕ) : 0 ≤ chebyshevPsi N := by
  classical
  unfold chebyshevPsi
  exact Finset.sum_nonneg fun n _hn => ArithmeticFunction.vonMangoldt_nonneg

/-- The finite Chebyshev psi carrier is monotone in the cutoff. -/
theorem chebyshevPsi_mono {M N : ℕ} (hMN : M ≤ N) :
    chebyshevPsi M ≤ chebyshevPsi N := by
  classical
  unfold chebyshevPsi
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hn).1, le_trans (Finset.mem_Icc.mp hn).2 hMN⟩
  · intro n _hnBig _hnSmall
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- The logarithm of any nonzero integer up to `N` is already accounted for by
the von Mangoldt mass in Chebyshev's `ψ(N)`. -/
theorem log_nat_le_chebyshevPsi {n N : ℕ} (hn : n ≠ 0) (hN : n ≤ N) :
    Real.log (n : ℝ) ≤ chebyshevPsi N := by
  classical
  rw [← ArithmeticFunction.vonMangoldt_sum (n := n)]
  unfold chebyshevPsi
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
    have hd_le_n : d ≤ n :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_divisors hd)
    exact Finset.mem_Icc.mpr
      ⟨Nat.succ_le_iff.mpr hd_pos, le_trans hd_le_n hN⟩
  · intro d _hdBig _hdSmall
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- Same-cutoff form of `log_nat_le_chebyshevPsi`. -/
theorem log_nat_le_chebyshevPsi_self {n : ℕ} (hn : n ≠ 0) :
    Real.log (n : ℝ) ≤ chebyshevPsi n :=
  log_nat_le_chebyshevPsi hn le_rfl

/-- The prime-log carrier is the prime-supported part of the von Mangoldt
carrier. -/
theorem primeTheta_eq_sum_vonMangoldt_primes (N : ℕ) :
    primeTheta N =
      ∑ p ∈ (Finset.Icc (1 : ℕ) N).filter Nat.Prime,
        ArithmeticFunction.vonMangoldt p := by
  classical
  unfold primeTheta
  apply Finset.sum_congr rfl
  intro p hp
  have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2
  exact (ArithmeticFunction.vonMangoldt_apply_prime hpPrime).symm

/-- The prime-log carrier is bounded above by Chebyshev's psi carrier.  This is
one direction of the standard `θ ≤ ψ` comparison; the reverse linear lower
comparison requires controlling prime-power tails and is left as the next
Chebyshev formalization step. -/
theorem primeTheta_le_chebyshevPsi (N : ℕ) :
    primeTheta N ≤ chebyshevPsi N := by
  classical
  rw [primeTheta_eq_sum_vonMangoldt_primes]
  unfold chebyshevPsi
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset _ _
  · intro n _hnBig _hnSmall
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- Real-log form of Mathlib's central-binomial lower bound
`4^n < n * centralBinom n`.

This is the lower combinatorial half of the Chebyshev argument. -/
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

/-- Exact factorization-sum form of `log (centralBinom n)`. -/
theorem log_centralBinom_eq_factorization_sum (n : ℕ) :
    Real.log ((Nat.centralBinom n : ℕ) : ℝ) =
      (Nat.centralBinom n).factorization.sum
        (fun p e => (e : ℝ) * Real.log (p : ℝ)) := by
  simpa using Real.log_nat_eq_sum_factorization (Nat.centralBinom n)

/-- Every prime factor of `centralBinom n` is at most `2n`. -/
theorem centralBinom_factorization_support_subset_range (n : ℕ) :
    (Nat.centralBinom n).factorization.support ⊆ Finset.range (2 * n + 1) := by
  intro p hp
  have hp_ne_zero : (Nat.centralBinom n).factorization p ≠ 0 :=
    Finsupp.mem_support_iff.mp hp
  have hp_pos : 0 < (Nat.centralBinom n).factorization p :=
    Nat.pos_of_ne_zero hp_ne_zero
  exact Finset.mem_range.mpr
    (Nat.lt_succ_iff.mpr
      (Nat.le_two_mul_of_factorization_centralBinom_pos hp_pos))

/-- Exact finite-range form of `log (centralBinom n)`, with all zero
factorization terms filled in up to `2n`. -/
theorem log_centralBinom_eq_range_factorization_sum (n : ℕ) :
    Real.log ((Nat.centralBinom n : ℕ) : ℝ) =
      ∑ p ∈ Finset.range (2 * n + 1),
        ((Nat.centralBinom n).factorization p : ℝ) * Real.log (p : ℝ) := by
  rw [log_centralBinom_eq_factorization_sum]
  exact Finsupp.sum_of_support_subset
    (Nat.centralBinom n).factorization
    (centralBinom_factorization_support_subset_range n)
    (fun p e => (e : ℝ) * Real.log (p : ℝ))
    (by intro p _hp; simp)

/-- The full prime-power contribution attached to any factor of
`centralBinom n` is bounded by `2n`. -/
theorem centralBinom_factorization_pow_le_two_mul {n p : ℕ} (hn : 0 < n) :
    p ^ (Nat.centralBinom n).factorization p ≤ 2 * n := by
  have h :
      p ^ (Nat.choose (2 * n) n).factorization p ≤ 2 * n :=
    Nat.pow_factorization_choose_le (p := p) (n := 2 * n) (k := n)
      (mul_pos (by norm_num : 0 < 2) hn)
  simpa [Nat.centralBinom_eq_two_mul_choose] using h

/-- Every nonzero partial prime-power contribution below the full
`centralBinom n` multiplicity is also bounded by `2n`. -/
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

/-- Prime-power divisors of `centralBinom n` are bounded by `2n`. -/
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

/-- Filtering a finite von Mangoldt sum to prime powers loses no mass. -/
theorem vonMangoldt_sum_eq_sum_filter_primePow (s : Finset ℕ) :
    (∑ d ∈ s, ArithmeticFunction.vonMangoldt d) =
      ∑ d ∈ s.filter IsPrimePow, ArithmeticFunction.vonMangoldt d := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _hd
  by_cases hdpp : IsPrimePow d
  · simp [hdpp]
  · simp [hdpp, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hdpp]

/-- The finite set of non-prime prime powers up to `N`. -/
noncomputable def nonprimePrimePowerSet (N : ℕ) : Finset ℕ :=
  (Finset.Icc (1 : ℕ) N).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n)

/-- The non-prime prime-power contribution to Chebyshev's `ψ`. -/
noncomputable def primePowerTail (N : ℕ) : ℝ :=
  ∑ n ∈ nonprimePrimePowerSet N, ArithmeticFunction.vonMangoldt n

/-- The prime-power tail is nonnegative termwise. -/
theorem primePowerTail_nonneg (N : ℕ) : 0 ≤ primePowerTail N := by
  classical
  unfold primePowerTail
  exact Finset.sum_nonneg fun n _hn => ArithmeticFunction.vonMangoldt_nonneg

/-- A non-prime prime power has a squared prime base below it. -/
theorem nonprime_primePow_exists_prime_sq_le {n : ℕ}
    (hnpp : IsPrimePow n) (hnprime : ¬ Nat.Prime n) :
    ∃ p : ℕ, Nat.Prime p ∧ p ^ 2 ≤ n := by
  rcases (isPrimePow_nat_iff n).mp hnpp with ⟨p, k, hp, hk, hpk⟩
  refine ⟨p, hp, ?_⟩
  rw [← hpk]
  have hk_ne_one : k ≠ 1 := by
    intro hk1
    apply hnprime
    rw [← hpk, hk1, pow_one]
    exact hp
  have hk_ge_two : 2 ≤ k := by omega
  exact Nat.pow_le_pow_right hp.pos hk_ge_two

/-- A non-prime prime power at most `N` has a prime base at most `sqrt N`. -/
theorem nonprime_primePow_exists_prime_le_sqrt {N n : ℕ} (hnN : n ≤ N)
    (hnpp : IsPrimePow n) (hnprime : ¬ Nat.Prime n) :
    ∃ p : ℕ, Nat.Prime p ∧ p ≤ Nat.sqrt N := by
  rcases nonprime_primePow_exists_prime_sq_le hnpp hnprime with ⟨p, hp, hp2n⟩
  exact ⟨p, hp, Nat.le_sqrt'.mpr (hp2n.trans hnN)⟩

/-- In canonical `minFac` coordinates, a non-prime prime power has exponent at
least two. -/
theorem nonprime_primePow_minFac_factorization_ge_two {n : ℕ}
    (hnpp : IsPrimePow n) (hnprime : ¬ Nat.Prime n) :
    2 ≤ n.factorization n.minFac := by
  have hpos : 0 < n.factorization n.minFac :=
    Nat.pos_of_ne_zero hnpp.factorization_minFac_ne_zero
  by_contra hnot
  have heq_one : n.factorization n.minFac = 1 := by omega
  have hpow := hnpp.minFac_pow_factorization_eq
  rw [heq_one, pow_one] at hpow
  apply hnprime
  have hminprime : Nat.Prime n.minFac := Nat.minFac_prime hnpp.ne_one
  simpa [hpow] using hminprime

/-- Canonical squared-base form of the previous lemma. -/
theorem nonprime_primePow_minFac_sq_le {n : ℕ}
    (hnpp : IsPrimePow n) (hnprime : ¬ Nat.Prime n) :
    n.minFac ^ 2 ≤ n := by
  calc
    n.minFac ^ 2
        ≤ n.minFac ^ n.factorization n.minFac :=
          Nat.pow_le_pow_right (Nat.minFac_pos n)
            (nonprime_primePow_minFac_factorization_ge_two hnpp hnprime)
    _ = n := hnpp.minFac_pow_factorization_eq

/-- The canonical prime base of a tail term below `N` is at most `sqrt N`. -/
theorem nonprime_primePow_minFac_le_sqrt {N n : ℕ} (hnN : n ≤ N)
    (hnpp : IsPrimePow n) (hnprime : ¬ Nat.Prime n) :
    n.minFac ≤ Nat.sqrt N := by
  exact Nat.le_sqrt'.mpr
    ((nonprime_primePow_minFac_sq_le hnpp hnprime).trans hnN)

/-- The canonical exponent of a tail term below `N` is at most `log₂ N`. -/
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

/-- The non-prime prime-power tail set injects into canonical base/exponent
pairs with base at most `sqrt N` and exponent at most `log₂ N`. -/
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
      rw [Finset.mem_product]
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

/-- The prime-power tail is bounded by its cardinality times `log N`. -/
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

/-- Explicit elementary upper envelope for the non-prime prime-power tail. -/
theorem primePowerTail_le_sqrt_mul_log_mul_log (N : ℕ) :
    primePowerTail N ≤
      (((Nat.sqrt N + 1) * (Nat.log 2 N + 1) : ℕ) : ℝ) *
        Real.log (N : ℝ) := by
  exact (primePowerTail_le_card_mul_log N).trans
    (mul_le_mul_of_nonneg_right
      (by exact_mod_cast nonprimePrimePowerSet_card_le_sqrt_mul_log N)
      (Real.log_natCast_nonneg N))

/-- Chebyshev's `ψ` decomposes exactly as `θ` plus the non-prime prime-power
tail. -/
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

/-- Subtraction form of the exact `ψ = θ + tail` decomposition. -/
theorem primeTheta_eq_chebyshevPsi_sub_primePowerTail (N : ℕ) :
    primeTheta N = chebyshevPsi N - primePowerTail N := by
  rw [chebyshevPsi_eq_primeTheta_add_primePowerTail N]
  ring

/-- The central-binomial logarithm is bounded by Chebyshev's `ψ` at `2n`. -/
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

/-- Unconditional Chebyshev-`ψ` lower bound obtained from the central-binomial
coefficient. -/
theorem chebyshevPsi_two_mul_lower_from_four_pow (n : ℕ) (hn : 4 ≤ n) :
    (n : ℝ) * Real.log 4 - Real.log (n : ℝ) ≤ chebyshevPsi (2 * n) := by
  exact (log_centralBinom_lower_from_four_pow n hn).trans
    (log_centralBinom_le_chebyshevPsi_two_mul
      (lt_of_lt_of_le (by norm_num : 0 < 4) hn))

/-- Dyadic linear lower bound for Chebyshev's `ψ`, with an explicit positive
constant. -/
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
    exact_mod_cast (Nat.lt_two_pow m).le
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

/-- A fixed checked dyadic `ψ` lower-bound constant, extracted from
`chebyshevPsi_dyadic_lower_bound`. -/
noncomputable def chebyshevPsiDyadicLowerConstant : ℝ :=
  Classical.choose chebyshevPsi_dyadic_lower_bound

/-- The extracted dyadic `ψ` lower-bound constant is positive. -/
theorem chebyshevPsiDyadicLowerConstant_pos :
    0 < chebyshevPsiDyadicLowerConstant :=
  (Classical.choose_spec chebyshevPsi_dyadic_lower_bound).1

/-- The extracted dyadic `ψ` lower-bound constant satisfies the checked dyadic
lower bound for `ψ`. -/
theorem chebyshevPsiDyadicLowerConstant_bound :
    ∀ k : ℕ, 3 ≤ k →
      chebyshevPsiDyadicLowerConstant * ((2 ^ k : ℕ) : ℝ) ≤ chebyshevPsi (2 ^ k) :=
  (Classical.choose_spec chebyshevPsi_dyadic_lower_bound).2

/-- If the non-prime prime-power tail is at most half the checked dyadic `ψ`
mass, then the same dyadic scales have a linear `θ` lower bound. -/
theorem primeTheta_large_dyadic_lower_bound_of_tail_dominated
    (hTail : ∀ k : ℕ, 3 ≤ k →
      primePowerTail (2 ^ k) ≤
        (chebyshevPsiDyadicLowerConstant / 2) * ((2 ^ k : ℕ) : ℝ)) :
    ∃ c > (0 : ℝ), ∀ k : ℕ, 3 ≤ k →
      c * ((2 ^ k : ℕ) : ℝ) ≤ primeTheta (2 ^ k) := by
  refine ⟨chebyshevPsiDyadicLowerConstant / 2,
    half_pos chebyshevPsiDyadicLowerConstant_pos, ?_⟩
  intro k hk
  have hpsi := chebyshevPsiDyadicLowerConstant_bound k hk
  have htail := hTail k hk
  rw [chebyshevPsi_eq_primeTheta_add_primePowerTail] at hpsi
  nlinarith

/-- Crude global upper bound for Chebyshev's `ψ`. -/
theorem chebyshevPsi_le_nat_mul_log (N : ℕ) :
    chebyshevPsi N ≤ (N : ℝ) * Real.log (N : ℝ) := by
  classical
  unfold chebyshevPsi
  calc
    (∑ n ∈ Finset.Icc (1 : ℕ) N, ArithmeticFunction.vonMangoldt n)
        ≤ ∑ _n ∈ Finset.Icc (1 : ℕ) N, Real.log (N : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          have hn_pos : 0 < n := Nat.succ_le_iff.mp (Finset.mem_Icc.mp hn).1
          have hn_le : n ≤ N := (Finset.mem_Icc.mp hn).2
          exact ArithmeticFunction.vonMangoldt_le_log.trans
            (Real.log_le_log (by exact_mod_cast hn_pos) (by exact_mod_cast hn_le))
    _ = (((Finset.Icc (1 : ℕ) N).card : ℕ) : ℝ) * Real.log (N : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * Real.log (N : ℝ) := by
          have hcard : (Finset.Icc (1 : ℕ) N).card ≤ N := by
            rw [Nat.card_Icc]
            omega
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
            (Real.log_natCast_nonneg N)

/-- The finite Chebyshev theta carrier is monotone in the cutoff. -/
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

/-- The prime `2` supplies a uniform positive contribution to `θ(N)` once
`N ≥ 2`. -/
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

/-- The finite Chebyshev theta carrier is bounded above by `π(N) log N`. -/
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

/-- A Chebyshev lower bound for the finite prime-log carrier implies the exact
prime-counting primitive used downstream. -/
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

/-- A dyadic Chebyshev theta lower bound implies the all-cutoff form used by the
prime-counting lower-bound bridge. -/
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
        simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]
  have hscaled :
      (cθ / 2) * (N : ℝ) ≤ cθ * ((2 ^ k : ℕ) : ℝ) := by
    nlinarith [hcθ, hN_le_two_pow]
  exact hscaled.trans ((htheta_dyadic k hk_ge_one).trans (primeTheta_mono hpow_le_N))

/-- A dyadic `θ` lower bound for all large dyadic scales automatically extends
to the primitive all-dyadic statement; the two small scales are covered by the
prime `2`. -/
theorem primeTheta_dyadic_lower_bound_of_large_dyadic_lower_bound
    (hlarge :
      ∃ c > (0 : ℝ), ∀ k : ℕ, 3 ≤ k →
        c * ((2 ^ k : ℕ) : ℝ) ≤ primeTheta (2 ^ k)) :
    ∃ c > (0 : ℝ), ∀ k : ℕ, 1 ≤ k →
      c * ((2 ^ k : ℕ) : ℝ) ≤ primeTheta (2 ^ k) := by
  rcases hlarge with ⟨c, hc, hlarge⟩
  let c' := min c (Real.log (2 : ℝ) / 4)
  have hlog2_pos : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num : 1 < (2 : ℝ))
  refine ⟨c', lt_min hc (by positivity), ?_⟩
  intro k hk
  by_cases hk3 : 3 ≤ k
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans
      (hlarge k hk3)
  · have hk_cases : k = 1 ∨ k = 2 := by omega
    rcases hk_cases with rfl | rfl
    · have hc' : c' * ((2 ^ 1 : ℕ) : ℝ) ≤ Real.log (2 : ℝ) := by
        have hc'le : c' ≤ Real.log (2 : ℝ) / 4 := min_le_right _ _
        norm_num
        nlinarith
      exact hc'.trans (log_two_le_primeTheta (N := 2 ^ 1) (by norm_num))
    · have hc' : c' * ((2 ^ 2 : ℕ) : ℝ) ≤ Real.log (2 : ℝ) := by
        have hc'le : c' ≤ Real.log (2 : ℝ) / 4 := min_le_right _ _
        norm_num
        nlinarith
      exact hc'.trans (log_two_le_primeTheta (N := 2 ^ 2) (by norm_num))

/-- Tail-domination form of the dyadic Chebyshev `θ` lower bound.

Thus the remaining work needed to eliminate the Chebyshev primitive can be
localized to the explicit inequality that the non-prime prime-power tail is at
most half the checked dyadic `ψ` mass. -/
theorem primeTheta_dyadic_lower_bound_of_tail_dominated
    (hTail : ∀ k : ℕ, 3 ≤ k →
      primePowerTail (2 ^ k) ≤
        (chebyshevPsiDyadicLowerConstant / 2) * ((2 ^ k : ℕ) : ℝ)) :
    ∃ c > (0 : ℝ), ∀ k : ℕ, 1 ≤ k →
      c * ((2 ^ k : ℕ) : ℝ) ≤ primeTheta (2 ^ k) :=
  primeTheta_dyadic_lower_bound_of_large_dyadic_lower_bound
    (primeTheta_large_dyadic_lower_bound_of_tail_dominated hTail)

/-- Explicit-envelope form of `primeTheta_dyadic_lower_bound_of_tail_dominated`.

The hypothesis is now only the elementary dyadic growth comparison coming from
the checked prime-power-tail envelope. -/
theorem primeTheta_dyadic_lower_bound_of_tail_envelope_dominated
    (hEnv : ∀ k : ℕ, 3 ≤ k →
      (((Nat.sqrt (2 ^ k) + 1) * (Nat.log 2 (2 ^ k) + 1) : ℕ) : ℝ) *
          Real.log (((2 ^ k : ℕ) : ℝ)) ≤
        (chebyshevPsiDyadicLowerConstant / 2) * ((2 ^ k : ℕ) : ℝ)) :
    ∃ c > (0 : ℝ), ∀ k : ℕ, 1 ≤ k →
      c * ((2 ^ k : ℕ) : ℝ) ≤ primeTheta (2 ^ k) := by
  apply primeTheta_dyadic_lower_bound_of_tail_dominated
  intro k hk
  exact (primePowerTail_le_sqrt_mul_log_mul_log (2 ^ k)).trans (hEnv k hk)

/-- Eventual tail-domination form of the dyadic Chebyshev `θ` lower bound.

The finitely many dyadic scales below the eventual threshold are handled by the
prime `2` contribution. -/
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

/-- Ratio form of the explicit non-prime prime-power envelope on dyadic
cutoffs. -/
noncomputable def dyadicPrimePowerTailEnvelopeRatio (k : ℕ) : ℝ :=
  ((((Nat.sqrt (2 ^ k) + 1) * (Nat.log 2 (2 ^ k) + 1) : ℕ) : ℝ) *
      Real.log (((2 ^ k : ℕ) : ℝ))) / ((2 ^ k : ℕ) : ℝ)

/-- The dyadic tail-envelope ratio is nonnegative. -/
theorem dyadicPrimePowerTailEnvelopeRatio_nonneg (k : ℕ) :
    0 ≤ dyadicPrimePowerTailEnvelopeRatio k := by
  unfold dyadicPrimePowerTailEnvelopeRatio
  positivity

/-- The dyadic tail-envelope ratio is bounded by a quadratic times an
exponentially decaying factor. -/
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
      exact mul_le_mul hsqrt_succ_le' hnatlog_succ_le'
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

/-- The explicit dyadic non-prime prime-power envelope is negligible compared
with the dyadic mass. -/
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

/-- Eventual domination of the explicit dyadic non-prime prime-power envelope
by any fixed positive multiple of the dyadic mass. -/
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

/-- Eventual explicit-envelope form of the dyadic Chebyshev `θ` lower bound.

This is the current fully localized replacement target for the Chebyshev
primitive: an eventual elementary inequality comparing the checked
prime-power-tail envelope with half the checked dyadic `ψ` mass. -/
theorem primeTheta_dyadic_lower_bound_of_eventual_tail_envelope_dominated
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

/-- Dyadic Chebyshev lower bound for the finite prime-log carrier.

This is proved from the central-binomial `ψ` lower bound and the explicit
non-prime prime-power tail envelope above. -/
theorem primeTheta_dyadic_lower_bound :
    ∃ cθ > (0 : ℝ), ∀ k : ℕ, 1 ≤ k →
      cθ * ((2 ^ k : ℕ) : ℝ) ≤ primeTheta (2 ^ k) := by
  apply primeTheta_dyadic_lower_bound_of_eventual_tail_envelope_dominated
  exact dyadicPrimePowerTailEnvelope_eventually_le_const_mul
    (half_pos chebyshevPsiDyadicLowerConstant_pos)

/-- Chebyshev lower bound for the finite prime-log carrier. -/
theorem primeTheta_lower_bound :
    ∃ cθ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      cθ * (N : ℝ) ≤ primeTheta N :=
  primeTheta_lower_bound_of_dyadic_lower_bound primeTheta_dyadic_lower_bound

/-- Chebyshev/PNT lower bound for the standard real prime-counting carrier,
derived from the finite prime-log carrier. -/
theorem realPrimePi_lower_bound :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      c₀ * (N : ℝ) / Real.log N ≤ (realPrimePi (N : ℝ) : ℝ) :=
  realPrimePi_lower_bound_of_primeTheta_lower_bound primeTheta_lower_bound

/-- The real-carrier prime-counting route follows from the same lower bound
stated directly for Mathlib's standard `Nat.primeCounting` carrier. -/
theorem realPrimePi_lower_bound_of_primeCounting_lower_bound
    (h :
      ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
        c₀ * (N : ℝ) / Real.log N ≤ (Nat.primeCounting N : ℝ)) :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      c₀ * (N : ℝ) / Real.log N ≤ (realPrimePi (N : ℝ) : ℝ) := by
  rcases h with ⟨c₀, hc₀, hπ⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro N hN
  simpa [realPrimePi_natCast_eq_primeCounting N] using hπ N hN

/-- The Chebyshev-scale lower-bound route is independent of whether it is stated
for the local real-cutoff carrier at natural inputs or for Mathlib's
`Nat.primeCounting`. -/
theorem realPrimePi_lower_bound_iff_primeCounting_lower_bound :
    (∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      c₀ * (N : ℝ) / Real.log N ≤ (realPrimePi (N : ℝ) : ℝ)) ↔
    (∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      c₀ * (N : ℝ) / Real.log N ≤ (Nat.primeCounting N : ℝ)) := by
  constructor
  · intro h
    rcases h with ⟨c₀, hc₀, hreal⟩
    refine ⟨c₀, hc₀, ?_⟩
    intro N hN
    simpa [realPrimePi_natCast_eq_primeCounting N] using hreal N hN
  · exact realPrimePi_lower_bound_of_primeCounting_lower_bound

/-- Foundation-only packaging bridge from the bare real-carrier prime-counting
lower bound to the finite-carrier side conditions used downstream. -/
theorem realPrimePi_lower_bound_with_carrier_bounds_of_bound
    (h :
      ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
        c₀ * (N : ℝ) / Real.log N ≤ (realPrimePi (N : ℝ) : ℝ)) :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      0 < Real.log N ∧
        0 ≤ (realPrimePi (N : ℝ) : ℝ) ∧
        c₀ * (N : ℝ) / Real.log N ≤ (realPrimePi (N : ℝ) : ℝ) ∧
        (realPrimePi (N : ℝ) : ℝ) ≤ (N : ℝ) ∧
        |(realPrimePi (N : ℝ) : ℝ)| ≤ (N : ℝ) := by
  rcases h with ⟨c₀, hc₀, hreal⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro N hN
  have hN_gt_one : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (by omega : 1 < N)
  have hlog_pos : 0 < Real.log N := Real.log_pos hN_gt_one
  have hcarrier_nonneg : 0 ≤ (realPrimePi (N : ℝ) : ℝ) :=
    realPrimePi_nonneg (N : ℝ)
  have hupper : (realPrimePi (N : ℝ) : ℝ) ≤ (N : ℝ) := by
    simpa [realPrimePi_natCast_eq_primePi N] using primePi_cast_le_self N
  exact ⟨hlog_pos, hcarrier_nonneg, hreal N hN, hupper, by
    rw [abs_of_nonneg hcarrier_nonneg]
    exact hupper⟩

/-- Forget the checked finite-carrier side conditions from the bundled
real-carrier prime-counting lower bound. -/
theorem realPrimePi_lower_bound_of_carrier_bounds
    (h :
      ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
        0 < Real.log N ∧
          0 ≤ (realPrimePi (N : ℝ) : ℝ) ∧
          c₀ * (N : ℝ) / Real.log N ≤ (realPrimePi (N : ℝ) : ℝ) ∧
          (realPrimePi (N : ℝ) : ℝ) ≤ (N : ℝ) ∧
          |(realPrimePi (N : ℝ) : ℝ)| ≤ (N : ℝ)) :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      c₀ * (N : ℝ) / Real.log N ≤ (realPrimePi (N : ℝ) : ℝ) := by
  rcases h with ⟨c₀, hc₀, hcarrier⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro N hN
  exact (hcarrier N hN).2.2.1

/-- The bare real-carrier prime-counting lower bound is equivalent to its
finite-carrier bundled form; the extra clauses are checked bookkeeping. -/
theorem realPrimePi_lower_bound_iff_carrier_bounds :
    (∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      c₀ * (N : ℝ) / Real.log N ≤ (realPrimePi (N : ℝ) : ℝ)) ↔
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      0 < Real.log N ∧
        0 ≤ (realPrimePi (N : ℝ) : ℝ) ∧
        c₀ * (N : ℝ) / Real.log N ≤ (realPrimePi (N : ℝ) : ℝ) ∧
        (realPrimePi (N : ℝ) : ℝ) ≤ (N : ℝ) ∧
        |(realPrimePi (N : ℝ) : ℝ)| ≤ (N : ℝ) := by
  constructor
  · exact realPrimePi_lower_bound_with_carrier_bounds_of_bound
  · exact realPrimePi_lower_bound_of_carrier_bounds

/-- Prime-counting lower input bundled directly at the real carrier. -/
theorem realPrimePi_lower_bound_with_carrier_bounds :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      0 < Real.log N ∧
        0 ≤ (realPrimePi (N : ℝ) : ℝ) ∧
        c₀ * (N : ℝ) / Real.log N ≤ (realPrimePi (N : ℝ) : ℝ) ∧
        (realPrimePi (N : ℝ) : ℝ) ≤ (N : ℝ) ∧
        |(realPrimePi (N : ℝ) : ℝ)| ≤ (N : ℝ) :=
  realPrimePi_lower_bound_with_carrier_bounds_of_bound realPrimePi_lower_bound

/-- Prime number theorem, lower bound form `π(N) ≫ N/log N` for Mathlib's
standard prime-counting carrier, derived from the real-carrier standard input. -/
theorem primeCounting_lower_bound :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      c₀ * (N : ℝ) / Real.log N ≤ (Nat.primeCounting N : ℝ) := by
  rcases realPrimePi_lower_bound with ⟨c₀, hc₀, hreal⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro N hN
  simpa [realPrimePi_natCast_eq_primeCounting N] using hreal N hN

/-- Foundation-only packaging bridge from the bare Mathlib prime-counting lower
bound to the finite-carrier side conditions used downstream. -/
theorem primeCounting_lower_bound_with_carrier_bounds_of_bound
    (h :
      ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
        c₀ * (N : ℝ) / Real.log N ≤ (Nat.primeCounting N : ℝ)) :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      0 < Real.log N ∧
        0 < (Nat.primeCounting N : ℝ) ∧
        c₀ * (N : ℝ) / Real.log N ≤ (Nat.primeCounting N : ℝ) ∧
        (Nat.primeCounting N : ℝ) ≤ (N : ℝ) ∧
        |(Nat.primeCounting N : ℝ)| ≤ (N : ℝ) := by
  rcases h with ⟨c₀, hc₀, hπ⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro N hN
  have hN_gt_one : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (by omega : 1 < N)
  have hlog_pos : 0 < Real.log N := Real.log_pos hN_gt_one
  have hπ_pos : 0 < (Nat.primeCounting N : ℝ) := by
    simpa [primePi_eq_primeCounting N] using
      (show 0 < (primePi N : ℝ) from by
        exact_mod_cast primePi_pos_of_two_le (by omega : 2 ≤ N))
  have hupper : (Nat.primeCounting N : ℝ) ≤ (N : ℝ) := by
    simpa [primePi_eq_primeCounting N] using primePi_cast_le_self N
  exact ⟨hlog_pos, hπ_pos, hπ N hN, hupper, by
    rw [abs_of_nonneg hπ_pos.le]
    exact hupper⟩

/-- Forget the checked finite-carrier side conditions from the bundled Mathlib
prime-counting lower bound. -/
theorem primeCounting_lower_bound_of_carrier_bounds
    (h :
      ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
        0 < Real.log N ∧
          0 < (Nat.primeCounting N : ℝ) ∧
          c₀ * (N : ℝ) / Real.log N ≤ (Nat.primeCounting N : ℝ) ∧
          (Nat.primeCounting N : ℝ) ≤ (N : ℝ) ∧
          |(Nat.primeCounting N : ℝ)| ≤ (N : ℝ)) :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      c₀ * (N : ℝ) / Real.log N ≤ (Nat.primeCounting N : ℝ) := by
  rcases h with ⟨c₀, hc₀, hcarrier⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro N hN
  exact (hcarrier N hN).2.2.1

/-- The bare Mathlib prime-counting lower bound is equivalent to its
finite-carrier bundled form; the additional clauses are checked bookkeeping. -/
theorem primeCounting_lower_bound_iff_carrier_bounds :
    (∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      c₀ * (N : ℝ) / Real.log N ≤ (Nat.primeCounting N : ℝ)) ↔
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      0 < Real.log N ∧
        0 < (Nat.primeCounting N : ℝ) ∧
        c₀ * (N : ℝ) / Real.log N ≤ (Nat.primeCounting N : ℝ) ∧
        (Nat.primeCounting N : ℝ) ≤ (N : ℝ) ∧
        |(Nat.primeCounting N : ℝ)| ≤ (N : ℝ) := by
  constructor
  · exact primeCounting_lower_bound_with_carrier_bounds_of_bound
  · exact primeCounting_lower_bound_of_carrier_bounds

/-- Mathlib prime-counting lower input bundled with checked finite-carrier side
conditions. -/
theorem primeCounting_lower_bound_with_carrier_bounds :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      0 < Real.log N ∧
        0 < (Nat.primeCounting N : ℝ) ∧
        c₀ * (N : ℝ) / Real.log N ≤ (Nat.primeCounting N : ℝ) ∧
        (Nat.primeCounting N : ℝ) ≤ (N : ℝ) ∧
        |(Nat.primeCounting N : ℝ)| ≤ (N : ℝ) :=
  primeCounting_lower_bound_with_carrier_bounds_of_bound primeCounting_lower_bound

/-- Prime number theorem, lower bound form `π(N) ≫ N/log N` (cited, tex 2107).

The analytic input is stated for the real prime-counting carrier; Lean transports
it first to Mathlib's `Nat.primeCounting`, then to the local manuscript notation
`primePi` using `primePi_eq_primeCounting`. -/
theorem primePi_lower_bound :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N → c₀ * (N : ℝ) / Real.log N ≤ (primePi N : ℝ) := by
  obtain ⟨c₀, hc₀, hpi⟩ := primeCounting_lower_bound
  exact ⟨c₀, hc₀, fun N hN => by
    simpa [primePi_eq_primeCounting N] using hpi N hN⟩

/-- Prime-counting lower bound bundled with the positivity side conditions used
when normalizing by `π(N)` and `log N`. -/
theorem primePi_lower_bound_with_carrier_bounds :
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

/-- Foundation-only packaging bridge from the bare prime-counting lower bound to
the positivity side conditions used for normalizing by `π(N)` and `log N`. -/
theorem primePi_lower_bound_with_carrier_bounds_of_bound
    (h :
      ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
        c₀ * (N : ℝ) / Real.log N ≤ (primePi N : ℝ)) :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      0 < Real.log N ∧ 0 < (primePi N : ℝ) ∧
        c₀ * (N : ℝ) / Real.log N ≤ (primePi N : ℝ) := by
  rcases h with ⟨c₀, hc₀, hpi⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro N hN
  have hN_gt_one : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (by omega : 1 < N)
  have hlog_pos : 0 < Real.log N := Real.log_pos hN_gt_one
  have hpi_pos : 0 < (primePi N : ℝ) := by
    exact_mod_cast primePi_pos_of_two_le (by omega : 2 ≤ N)
  exact ⟨hlog_pos, hpi_pos, hpi N hN⟩

/-- Forget the checked positivity side conditions from the bundled
prime-counting lower bound. -/
theorem primePi_lower_bound_of_carrier_bounds
    (h :
      ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
        0 < Real.log N ∧ 0 < (primePi N : ℝ) ∧
          c₀ * (N : ℝ) / Real.log N ≤ (primePi N : ℝ)) :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      c₀ * (N : ℝ) / Real.log N ≤ (primePi N : ℝ) := by
  rcases h with ⟨c₀, hc₀, hcarrier⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro N hN
  exact (hcarrier N hN).2.2

/-- The bare prime-counting lower bound is equivalent to its positivity-bundled
form; the extra clauses are elementary carrier facts. -/
theorem primePi_lower_bound_iff_carrier_bounds :
    (∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      c₀ * (N : ℝ) / Real.log N ≤ (primePi N : ℝ)) ↔
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      0 < Real.log N ∧ 0 < (primePi N : ℝ) ∧
        c₀ * (N : ℝ) / Real.log N ≤ (primePi N : ℝ) := by
  constructor
  · exact primePi_lower_bound_with_carrier_bounds_of_bound
  · exact primePi_lower_bound_of_carrier_bounds

/-- Prime-counting lower input bundled with the checked finite-carrier upper and
absolute-value bounds.  The only analytic content is still the lower bound
`π(N) ≫ N/log N`; the upper/range facts are elementary properties of the finite
prime carrier. -/
theorem primePi_lower_bound_two_sided_with_carrier_bounds :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      0 < Real.log N ∧
        0 < (primePi N : ℝ) ∧
        c₀ * (N : ℝ) / Real.log N ≤ (primePi N : ℝ) ∧
        (primePi N : ℝ) ≤ (N : ℝ) ∧
        |(primePi N : ℝ)| ≤ (N : ℝ) := by
  rcases primePi_lower_bound_with_carrier_bounds with ⟨c₀, hc₀, hwrapped⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro N hN
  rcases hwrapped N hN with ⟨hlog_pos, hpi_pos, hlower⟩
  have hupper : (primePi N : ℝ) ≤ (N : ℝ) := primePi_cast_le_self N
  exact ⟨hlog_pos, hpi_pos, hlower, hupper, by
    rw [abs_of_nonneg hpi_pos.le]
    exact hupper⟩

/-- Foundation-only packaging bridge from the bare prime-counting lower bound to
the two-sided finite-carrier bundle. -/
theorem primePi_lower_bound_two_sided_with_carrier_bounds_of_bound
    (h :
      ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
        c₀ * (N : ℝ) / Real.log N ≤ (primePi N : ℝ)) :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      0 < Real.log N ∧
        0 < (primePi N : ℝ) ∧
        c₀ * (N : ℝ) / Real.log N ≤ (primePi N : ℝ) ∧
        (primePi N : ℝ) ≤ (N : ℝ) ∧
        |(primePi N : ℝ)| ≤ (N : ℝ) := by
  rcases primePi_lower_bound_with_carrier_bounds_of_bound h with ⟨c₀, hc₀, hwrapped⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro N hN
  rcases hwrapped N hN with ⟨hlog_pos, hpi_pos, hlower⟩
  have hupper : (primePi N : ℝ) ≤ (N : ℝ) := primePi_cast_le_self N
  exact ⟨hlog_pos, hpi_pos, hlower, hupper, by
    rw [abs_of_nonneg hpi_pos.le]
    exact hupper⟩

/-- Forget the checked finite-carrier upper and absolute-value clauses from the
two-sided prime-counting bundle. -/
theorem primePi_lower_bound_of_two_sided_carrier_bounds
    (h :
      ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
        0 < Real.log N ∧
          0 < (primePi N : ℝ) ∧
          c₀ * (N : ℝ) / Real.log N ≤ (primePi N : ℝ) ∧
          (primePi N : ℝ) ≤ (N : ℝ) ∧
          |(primePi N : ℝ)| ≤ (N : ℝ)) :
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      c₀ * (N : ℝ) / Real.log N ≤ (primePi N : ℝ) := by
  rcases h with ⟨c₀, hc₀, hcarrier⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro N hN
  exact (hcarrier N hN).2.2.1

/-- The bare prime-counting lower bound is equivalent to the two-sided
finite-carrier bundle; the upper and absolute-value clauses add no analytic
content. -/
theorem primePi_lower_bound_iff_two_sided_carrier_bounds :
    (∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      c₀ * (N : ℝ) / Real.log N ≤ (primePi N : ℝ)) ↔
    ∃ c₀ > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      0 < Real.log N ∧
        0 < (primePi N : ℝ) ∧
        c₀ * (N : ℝ) / Real.log N ≤ (primePi N : ℝ) ∧
        (primePi N : ℝ) ≤ (N : ℝ) ∧
        |(primePi N : ℝ)| ≤ (N : ℝ) := by
  constructor
  · exact primePi_lower_bound_two_sided_with_carrier_bounds_of_bound
  · exact primePi_lower_bound_of_two_sided_carrier_bounds

/-! ## `cor:prime-exceptional` (tex 2098-2114) -/

/-- **Corollary `cor:prime-exceptional`, part one (tex 2098-2104).**

If the full exceptional-count `E(N)` satisfies the main bound
`E(N) ≪ N·exp(-c(log N)^{3/4})`, then so does its restriction to prime
denominators `#𝒫_exc(N)`.

Proof: `primeExceptionalCount N ≤ exceptionalCount N` pointwise
(primes ⊆ all denominators), and `IsMainBound` is monotone under `≤`. -/
theorem prime_exceptional_of_main (h : IsMainBound exceptionalCount) :
    IsMainBound primeExceptionalCount :=
  IsMainBound.of_le primeExceptionalCount_le h

/-- Density-zero form of `cor:prime-exceptional`, derived from any already-proved
main bound for exceptional primes. -/
theorem prime_exceptional_density_zero_of_prime_main
    (h : IsMainBound primeExceptionalCount) :
    Filter.Tendsto (fun N : ℕ => (primeExceptionalCount N : ℝ) / (N : ℝ))
      Filter.atTop (nhds 0) :=
  h.density_tendsto_zero

/-- Density-zero form of `cor:prime-exceptional`, derived from the full main
exceptional-set bound by the prime-subset reduction. -/
theorem prime_exceptional_density_zero_of_main (h : IsMainBound exceptionalCount) :
    Filter.Tendsto (fun N : ℕ => (primeExceptionalCount N : ℝ) / (N : ℝ))
      Filter.atTop (nhds 0) :=
  (prime_exceptional_of_main h).density_tendsto_zero

/-- **Corollary `cor:prime-exceptional`, part two (tex 2105-2108).**

The `≪ π(N)·saving` form.  From part one we have constants `c, C` with
`#𝒫_exc(N) ≤ C·N·exp(-c(log N)^{3/4})`.  Multiplying by the cited lower bound
`π(N) ≥ c₀·N/log N` (`primePi_lower_bound`) and decreasing the exponential
exponential rate (here we simply expose the relation
`#𝒫_exc(N) ≤ C'·π(N)·log N·saving`,
the clean unconditional inequality available from `π(N) ≥ c₀ N/log N`).

Concretely we prove: there exist `c > 0` and `C' > 0` such that for all `N ≥ 3`,
`#𝒫_exc(N) ≤ C' · π(N) · log N · exp(-c(log N)^{3/4})`.  This is `cor`'s second
display once one absorbs the `log N` factor into the exponential saving (the
manuscript's "after decreasing the constant"). -/
theorem prime_exceptional_le_primePi (h : IsMainBound exceptionalCount) :
    ∃ c > (0 : ℝ), ∃ C' > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      (primeExceptionalCount N : ℝ) ≤ C' * (primePi N : ℝ) * Real.log N * saving c N := by
  obtain ⟨c, hc, C, hC, hmain⟩ := prime_exceptional_of_main h
  obtain ⟨c₀, hc₀, hpi⟩ := primePi_lower_bound_two_sided_with_carrier_bounds
  refine ⟨c, hc, C / c₀, by positivity, fun N hN => ?_⟩
  -- abbreviations
  have hpi_data := hpi N hN
  have hlogN_pos : 0 < Real.log N := hpi_data.1
  have hsav_pos : 0 < saving c N := Real.exp_pos _
  -- from PNT: c₀ N ≤ π(N) · log N
  have hkey : c₀ * (N : ℝ) ≤ (primePi N : ℝ) * Real.log N := by
    have := hpi_data.2.2.1
    rw [div_le_iff₀ hlogN_pos] at this
    linarith
  -- main bound: #P_exc ≤ C·N·sav
  have hmb := hmain N hN
  -- combine: #P_exc ≤ C·N·sav = (C/c₀)·(c₀ N)·sav ≤ (C/c₀)·(π N · log N)·sav
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  calc (primeExceptionalCount N : ℝ)
      ≤ C * N * saving c N := hmb
    _ = (C / c₀) * (c₀ * (N : ℝ)) * saving c N := by
        field_simp; ring
    _ ≤ (C / c₀) * ((primePi N : ℝ) * Real.log N) * saving c N := by
        apply mul_le_mul_of_nonneg_right _ hsav_pos.le
        apply mul_le_mul_of_nonneg_left hkey
        positivity
    _ = (C / c₀) * (primePi N : ℝ) * Real.log N * saving c N := by ring

/-- A fully checked Bertrand-scale prime-normalized fallback.

The PNT/Chebyshev lower bound `π(N) ≫ N/log N` is needed to obtain the clean
`π(N)·saving` corollary.  Without that external input, Bertrand's postulate still
gives `π(N) ≳ log N`, and hence a weaker but unconditional conversion with an
explicit extra factor `N/log N`. -/
theorem prime_exceptional_le_primePi_bertrand_loss (h : IsMainBound exceptionalCount) :
    ∃ c > (0 : ℝ), ∃ C' > (0 : ℝ), ∀ N : ℕ, 4 ≤ N →
      (primeExceptionalCount N : ℝ) ≤
        C' * (primePi N : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) * saving c N := by
  obtain ⟨c, hc, C, hC, hmain⟩ := prime_exceptional_of_main h
  obtain ⟨c₀, hc₀, hpi⟩ := primePi_realLog_lower_bertrand_with_carrier_bounds
  refine ⟨c, hc, C / c₀, by positivity, ?_⟩
  intro N hN
  have hpi_data := hpi N hN
  have hlogN_pos : 0 < Real.log (N : ℝ) := hpi_data.1
  have hsav_pos : 0 < saving c N := Real.exp_pos _
  have hN_over_log_nonneg : 0 ≤ (N : ℝ) / Real.log (N : ℝ) :=
    div_nonneg (Nat.cast_nonneg N) hlogN_pos.le
  have hkey :
      c₀ * (N : ℝ) ≤ (primePi N : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) := by
    calc
      c₀ * (N : ℝ)
          = (c₀ * Real.log (N : ℝ)) * ((N : ℝ) / Real.log (N : ℝ)) := by
            field_simp [ne_of_gt hlogN_pos]
            ring
      _ ≤ (primePi N : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) :=
          mul_le_mul_of_nonneg_right hpi_data.2.2.1 hN_over_log_nonneg
  have hmb := hmain N (by omega : 3 ≤ N)
  calc
    (primeExceptionalCount N : ℝ)
        ≤ C * N * saving c N := hmb
    _ = (C / c₀) * (c₀ * (N : ℝ)) * saving c N := by
        field_simp [ne_of_gt hc₀]
        ring
    _ ≤ (C / c₀) *
          ((primePi N : ℝ) * ((N : ℝ) / Real.log (N : ℝ))) * saving c N := by
        apply mul_le_mul_of_nonneg_right _ hsav_pos.le
        apply mul_le_mul_of_nonneg_left hkey
        positivity
    _ = (C / c₀) * (primePi N : ℝ) *
          ((N : ℝ) / Real.log (N : ℝ)) * saving c N := by
        ring

/-- Ratio form of the fully checked Bertrand-scale fallback.

The clean prime-relative density theorem still needs the PNT/Chebyshev-scale
lower bound `π(N) ≫ N/log N`; this theorem records exactly what the elementary
Bertrand replacement proves after dividing by the nonzero prime-counting
carrier. -/
theorem primeExceptionalRatio_le_bertrand_loss (h : IsMainBound exceptionalCount) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N : ℕ, 4 ≤ N →
      primeExceptionalRatio N ≤
        C * ((N : ℝ) / Real.log (N : ℝ)) * saving c N := by
  obtain ⟨c, hc, C, hC, hprime⟩ := prime_exceptional_le_primePi_bertrand_loss h
  refine ⟨c, hc, C, hC, ?_⟩
  intro N hN
  have hpi_pos : 0 < (primePi N : ℝ) := by
    exact_mod_cast primePi_pos_of_two_le (by omega : 2 ≤ N)
  unfold primeExceptionalRatio
  rw [div_le_iff₀ hpi_pos]
  calc
    (primeExceptionalCount N : ℝ)
        ≤ C * (primePi N : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) * saving c N :=
          hprime N hN
    _ = (C * ((N : ℝ) / Real.log (N : ℝ)) * saving c N) * (primePi N : ℝ) := by
        ring

/-- A single logarithm can be absorbed into the exponential saving after shrinking
the saving constant. -/
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

/-- The secondary large-prime-factor saving shape
`exp(-c (log N)^(9/16))` appearing when the cutoff is
`exp((log N)^(3/4))`. -/
noncomputable def savingNineSixteen (c : ℝ) (N : ℕ) : ℝ :=
  Real.exp (-c * (Real.log N) ^ ((9 : ℝ) / 16))

/-- A small real-power comparison used to absorb logarithmic factors into the
`9/16` saving. -/
theorem rpow_sixteen_ninths_le_one_add_sq {t : ℝ} (ht : 0 ≤ t) :
    t ^ ((16 : ℝ) / 9) ≤ 1 + t ^ 2 := by
  by_cases ht1 : t ≤ 1
  · have hpow_le_one : t ^ ((16 : ℝ) / 9) ≤ 1 :=
      Real.rpow_le_one ht ht1 (by norm_num)
    have hsquare_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
    linarith
  · have hgt : 1 ≤ t := le_of_lt (lt_of_not_ge ht1)
    have hpow_le_sq : t ^ ((16 : ℝ) / 9) ≤ t ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hgt (by norm_num)
    have hsq_eq : t ^ (2 : ℝ) = t ^ 2 := by norm_num
    rw [hsq_eq] at hpow_le_sq
    have : t ^ 2 ≤ 1 + t ^ 2 := by linarith
    exact le_trans hpow_le_sq this

/-- A single logarithm can be absorbed into the `9/16` exponential saving after
shrinking the saving constant. -/
theorem log_mul_savingNineSixteen_absorb {c₁ : ℝ} (hc₁ : 0 < c₁) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ N : ℕ, 3 ≤ N →
        Real.log N * savingNineSixteen c₁ N ≤ C * savingNineSixteen c N := by
  set c : ℝ := c₁ / 2 with hc
  refine ⟨c, by positivity, 1 + 16 / c₁ ^ 2, by positivity, ?_⟩
  intro N hN
  set L : ℝ := Real.log N with hLdef
  have hL0 : 0 < L := log_pos_of_three_le hN
  set t : ℝ := L ^ ((9 : ℝ) / 16) with htdef
  have ht0 : 0 < t := Real.rpow_pos_of_pos hL0 _
  have hsave₁ : savingNineSixteen c₁ N = Real.exp (-c₁ * t) := by
    unfold savingNineSixteen
    rw [← hLdef, ← htdef]
  have hsaveC : savingNineSixteen c N = Real.exp (-c * t) := by
    unfold savingNineSixteen
    rw [← hLdef, ← htdef]
  rw [hsave₁, hsaveC]
  have hLbound : L ≤ 1 + t ^ 2 := by
    have : t ^ ((16 : ℝ) / 9) = L := by
      rw [htdef, ← Real.rpow_mul hL0.le]
      norm_num
    calc L = t ^ ((16 : ℝ) / 9) := this.symm
      _ ≤ 1 + t ^ 2 := rpow_sixteen_ninths_le_one_add_sq ht0.le
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
  have hone : (1 : ℝ) ≤ Real.exp (c * t) :=
    Real.one_le_exp (by positivity)
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

/-- Clean `≪ π(N)·saving` form of `cor:prime-exceptional`.

This formalizes the manuscript's final absorption of the displayed `log N`
factor in `prime_exceptional_le_primePi`: after shrinking the exponential
constant, `#𝒫_exc(N) ≤ C π(N) exp(-c(log N)^{3/4})`. -/
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

/-- Prime-counting conversion for any already-established main-style bound on
the exceptional primes themselves.

This is useful for certificate-facing capstones that have already proved
`IsMainBound primeExceptionalCount`: the cited lower bound for `π(N)` gives a
single logarithmic loss. -/
theorem prime_bound_le_primePi (h : IsMainBound primeExceptionalCount) :
    ∃ c > (0 : ℝ), ∃ C' > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      (primeExceptionalCount N : ℝ) ≤ C' * (primePi N : ℝ) * Real.log N * saving c N := by
  obtain ⟨c, hc, C, hC, hmain⟩ := h
  obtain ⟨c₀, hc₀, hpi⟩ := primePi_lower_bound_two_sided_with_carrier_bounds
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
        ring
    _ ≤ (C / c₀) * ((primePi N : ℝ) * Real.log N) * saving c N := by
        apply mul_le_mul_of_nonneg_right _ hsav_pos.le
        apply mul_le_mul_of_nonneg_left hkey
        positivity
    _ = (C / c₀) * (primePi N : ℝ) * Real.log N * saving c N := by ring

/-- Bertrand-scale prime-counting conversion for an already-established main-style
bound on exceptional primes.

This is the `prime_bound_le_primePi` analogue that avoids the PNT/Chebyshev
input.  Bertrand's postulate supplies only `π(N) ≳ log N`, so the price is the
explicit extra factor `N / log N`. -/
theorem prime_bound_le_primePi_bertrand_loss (h : IsMainBound primeExceptionalCount) :
    ∃ c > (0 : ℝ), ∃ C' > (0 : ℝ), ∀ N : ℕ, 4 ≤ N →
      (primeExceptionalCount N : ℝ) ≤
        C' * (primePi N : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) * saving c N := by
  obtain ⟨c, hc, C, hC, hmain⟩ := h
  obtain ⟨c₀, hc₀, hpi⟩ := primePi_realLog_lower_bertrand_with_carrier_bounds
  refine ⟨c, hc, C / c₀, by positivity, ?_⟩
  intro N hN
  have hpi_data := hpi N hN
  have hlogN_pos : 0 < Real.log (N : ℝ) := hpi_data.1
  have hsav_pos : 0 < saving c N := Real.exp_pos _
  have hN_over_log_nonneg : 0 ≤ (N : ℝ) / Real.log (N : ℝ) :=
    div_nonneg (Nat.cast_nonneg N) hlogN_pos.le
  have hkey :
      c₀ * (N : ℝ) ≤ (primePi N : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) := by
    calc
      c₀ * (N : ℝ)
          = (c₀ * Real.log (N : ℝ)) * ((N : ℝ) / Real.log (N : ℝ)) := by
            field_simp [ne_of_gt hlogN_pos]
            ring
      _ ≤ (primePi N : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) :=
          mul_le_mul_of_nonneg_right hpi_data.2.2.1 hN_over_log_nonneg
  have hmb := hmain N (by omega : 3 ≤ N)
  calc
    (primeExceptionalCount N : ℝ)
        ≤ C * N * saving c N := hmb
    _ = (C / c₀) * (c₀ * (N : ℝ)) * saving c N := by
        field_simp [ne_of_gt hc₀]
        ring
    _ ≤ (C / c₀) *
          ((primePi N : ℝ) * ((N : ℝ) / Real.log (N : ℝ))) * saving c N := by
        apply mul_le_mul_of_nonneg_right _ hsav_pos.le
        apply mul_le_mul_of_nonneg_left hkey
        positivity
    _ = (C / c₀) * (primePi N : ℝ) *
          ((N : ℝ) / Real.log (N : ℝ)) * saving c N := by
        ring

/-- Clean `π(N)·saving` conversion for any already-established main-style bound
on exceptional primes.

Compared with `prime_exceptional_le_primePi_saving`, this starts from
`IsMainBound primeExceptionalCount` rather than from the full exceptional count.
It therefore applies directly to all certificate-facing prime corollaries. -/
theorem prime_bound_le_primePi_saving (h : IsMainBound primeExceptionalCount) :
    ∃ c > (0 : ℝ), ∃ C' > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      (primeExceptionalCount N : ℝ) ≤ C' * (primePi N : ℝ) * saving c N := by
  obtain ⟨c₁, hc₁, C₁, hC₁, hprime⟩ := prime_bound_le_primePi h
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

/-- Relative density-zero among primes from any clean `π(N)·saving` bound.

This is the reusable final step for certificate-facing prime capstones: once a
route has proved
`#𝒫_exc(N) ≤ C · π(N) · exp(-c(log N)^{3/4})`, division by `π(N)` leaves only the
exponential saving. -/
theorem prime_exceptional_relative_density_zero_of_primePi_saving
    (h : ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      (primeExceptionalCount N : ℝ) ≤ C * (primePi N : ℝ) * saving c N) :
    Filter.Tendsto (fun N : ℕ => (primeExceptionalCount N : ℝ) / (primePi N : ℝ))
      Filter.atTop (nhds 0) := by
  obtain ⟨c, hc, C, _hC, hprime⟩ := h
  refine squeeze_zero_norm' (a := fun N : ℕ => C * saving c N) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 3] with N hN
    have hpi_pos : 0 < (primePi N : ℝ) := by
      exact_mod_cast primePi_pos_of_two_le (by omega : 2 ≤ N)
    have hdiv :
        (primeExceptionalCount N : ℝ) / (primePi N : ℝ) ≤ C * saving c N := by
      rw [div_le_iff₀ hpi_pos]
      calc
        (primeExceptionalCount N : ℝ)
            ≤ C * (primePi N : ℝ) * saving c N := hprime N hN
        _ = (C * saving c N) * (primePi N : ℝ) := by ring
    rw [Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) hpi_pos.le)]
    exact hdiv
  · simpa using (saving_tendsto_zero hc).const_mul C

/-- Relative density-zero form among primes from a main-style exceptional-prime
bound. -/
theorem prime_exceptional_relative_density_zero_of_prime_main
    (h : IsMainBound primeExceptionalCount) :
    Filter.Tendsto (fun N : ℕ => (primeExceptionalCount N : ℝ) / (primePi N : ℝ))
      Filter.atTop (nhds 0) :=
  prime_exceptional_relative_density_zero_of_primePi_saving
    (prime_bound_le_primePi_saving h)

/-- Relative density-zero among primes from the full exceptional-set main bound. -/
theorem prime_exceptional_relative_density_zero_of_main
    (h : IsMainBound exceptionalCount) :
    Filter.Tendsto (fun N : ℕ => (primeExceptionalCount N : ℝ) / (primePi N : ℝ))
      Filter.atTop (nhds 0) :=
  prime_exceptional_relative_density_zero_of_prime_main (prime_exceptional_of_main h)

/-! ## `prop:large-prime-factor` (tex 2118-2165) -/

/-- **Elementary lifting core (tex 2150-2153).**

"Every prime divisor of an exceptional integer is itself an exceptional prime."

If `p ∣ n`, `p` prime, and `4/p = 1/x + 1/y + 1/z`, then
`4/n = 1/((n/p)x) + 1/((n/p)y) + 1/((n/p)z)`, so `n` is representable.
Contrapositive: an exceptional `n` forces every prime divisor `p` to be
exceptional.  Proved in Lean, via `EscLeanChecks.esExceptional_prime_divisor_of_exceptional`. -/
theorem esExceptional_prime_factor_is_exceptional
    (n p : ℕ) (hn : 0 < n) (hp : p.Prime) (hdvd : p ∣ n)
    (hex : EscLeanChecks.esExceptional n) :
    EscLeanChecks.esExceptional p :=
  EscLeanChecks.esExceptional_prime_divisor_of_exceptional n p hn hp hdvd hex

/-- The set counted by `E_{>Y}(N)` (tex 2122-2126): positive integers `n ≤ N`
that are exceptional for `4/n` and have a prime factor `p > Y`.

We package the largest-prime-factor condition `P⁺(n) > Y` faithfully as the
existence of a prime divisor `p` with `Y < p` (`P⁺(n) > Y ⟺ ∃ p∣n prime, p>Y`). -/
noncomputable def exceptionalGtY (N Y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter
    (fun n => EscLeanChecks.esExceptional n ∧ ∃ p, p.Prime ∧ p ∣ n ∧ Y < p)

/-- `E_{>Y}(N)` as a natural number (tex 2122-2126). -/
noncomputable def exceptionalGtYCount (N Y : ℕ) : ℕ := (exceptionalGtY N Y).card

/-- The finite set of **exceptional primes** in the range `Y < p ≤ N`
(the index set of the partial sum at tex 2155-2159). -/
noncomputable def excPrimesIoc (N Y : ℕ) : Finset ℕ :=
  (Finset.Ioc Y N).filter (fun p => p.Prime ∧ EscLeanChecks.esExceptional p)

/-- The dyadic sub-shell of exceptional primes with
`2^k Y ≤ p < 2^(k+1)Y`, still restricted to the ambient range `Y < p ≤ N`.

These shells are the finite combinatorial objects used to make the manuscript's
partial-summation step explicit. -/
noncomputable def excPrimesDyadicShell (N Y k : ℕ) : Finset ℕ :=
  (excPrimesIoc N Y).filter
    (fun p => 2 ^ k * Y ≤ p ∧ p < 2 ^ (k + 1) * Y)

/-- Every integer `p > Y` has a dyadic shell index relative to `Y`. -/
theorem dyadic_index_spec {p Y : ℕ} (hY : 0 < Y) (hp : Y < p) :
    let k := Nat.log 2 (p / Y)
    2 ^ k * Y ≤ p ∧ p < 2 ^ (k + 1) * Y := by
  dsimp
  constructor
  · have hdivpos : p / Y ≠ 0 := by
      exact Nat.ne_of_gt (Nat.div_pos (le_of_lt hp) hY)
    have hpow : 2 ^ Nat.log 2 (p / Y) ≤ p / Y :=
      Nat.pow_log_le_self 2 hdivpos
    exact (Nat.le_div_iff_mul_le hY).mp hpow
  · have hlt : p / Y < 2 ^ (Nat.log 2 (p / Y)).succ :=
      Nat.lt_pow_succ_log_self Nat.one_lt_two (p / Y)
    simpa [Nat.succ_eq_add_one] using Nat.lt_mul_of_div_lt hlt hY

/-- Membership in `excPrimesIoc` gives membership in the corresponding dyadic
shell selected by `Nat.log 2 (p / Y)`. -/
theorem mem_excPrimesDyadicShell_of_mem_excPrimesIoc
    {N Y p : ℕ} (hY : 0 < Y) (hp : p ∈ excPrimesIoc N Y) :
    p ∈ excPrimesDyadicShell N Y (Nat.log 2 (p / Y)) := by
  rw [excPrimesIoc, Finset.mem_filter, Finset.mem_Ioc] at hp
  rw [excPrimesDyadicShell, Finset.mem_filter]
  exact ⟨by
    rw [excPrimesIoc, Finset.mem_filter, Finset.mem_Ioc]
    exact hp, dyadic_index_spec hY hp.1.1⟩

/-- Count of multiples of `p` in `Icc 1 N` is at most `N/p + 1`.
(`#{n≤N : p∣n} ≤ N/p + 1`, the trivial per-class count behind the union bound
at tex 2154.) -/
theorem card_multiples_le (N p : ℕ) (_hp : 0 < p) :
    ((Finset.Icc 1 N).filter (fun n => p ∣ n)).card ≤ N / p + 1 := by
  classical
  -- map n ↦ n/p injectively into range (N/p + 1)
  set s : Finset ℕ := (Finset.Icc 1 N).filter (fun n => p ∣ n) with hs
  have hmaps : ∀ n ∈ s, n / p ∈ Finset.range (N / p + 1) := by
    intro n hn
    rw [hs, Finset.mem_filter, Finset.mem_Icc] at hn
    have hnle : n ≤ N := hn.1.2
    have : n / p ≤ N / p := Nat.div_le_div_right hnle
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le this)
  have hinj : (s : Set ℕ).InjOn (fun n => n / p) := by
    intro x hx y hy hxy
    rw [hs, Finset.coe_filter, Set.mem_setOf_eq] at hx hy
    obtain ⟨_, hxdvd⟩ := hx
    obtain ⟨_, hydvd⟩ := hy
    simp only at hxy
    -- p ∣ x, p ∣ y, x/p = y/p ⟹ x = y
    have hx' : x = p * (x / p) := (Nat.mul_div_cancel' hxdvd).symm
    have hy' : y = p * (y / p) := (Nat.mul_div_cancel' hydvd).symm
    rw [hx', hy', hxy]
  have hcard : s.card ≤ (Finset.range (N / p + 1)).card :=
    Finset.card_le_card_of_injOn (fun n => n / p) hmaps hinj
  simpa using hcard

/-- **Union bound (tex 2152-2154).**

The set `E_{>Y}(N)` is contained in the union, over exceptional primes
`Y < p ≤ N`, of the multiples of `p` in `Icc 1 N`.  Hence

`E_{>Y}(N) ≤ ∑_{Y<p≤N, p exc} #{n≤N : p∣n} ≤ ∑_{Y<p≤N, p exc} (N/p + 1)`.

The two inclusions are: (a) any exceptional `n≤N` with a prime factor `p>Y` has
such a `p ≤ n ≤ N`, and that `p` is exceptional (elementary lifting core); and
(b) the trivial per-prime count `#{n≤N : p∣n} ≤ N/p+1`.  Proved in Lean. -/
theorem exceptionalGtYCount_le_sum (N Y : ℕ) :
    exceptionalGtYCount N Y ≤ ∑ p ∈ excPrimesIoc N Y, (N / p + 1) := by
  classical
  -- Step 1: E_{>Y}(N) ⊆ ⋃_{p ∈ excPrimesIoc} {n≤N : p∣n}, via Finset.biUnion.
  have hsub : exceptionalGtY N Y ⊆
      (excPrimesIoc N Y).biUnion
        (fun p => (Finset.Icc 1 N).filter (fun n => p ∣ n)) := by
    intro n hn
    rw [exceptionalGtY, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hex, p, hp, hpdvd, hpY⟩ := hn
    have hnpos : 0 < n := hn1
    -- p ≤ n ≤ N
    have hpn : p ≤ n := Nat.le_of_dvd hnpos hpdvd
    have hpN : p ≤ N := le_trans hpn hnN
    -- p is exceptional
    have hpex : EscLeanChecks.esExceptional p :=
      esExceptional_prime_factor_is_exceptional n p hnpos hp hpdvd hex
    rw [Finset.mem_biUnion]
    refine ⟨p, ?_, ?_⟩
    · rw [excPrimesIoc, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hpY, hpN⟩, hp, hpex⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hn1, hnN⟩, hpdvd⟩
  -- Step 2: card of subset ≤ card of biUnion ≤ ∑ card of pieces
  have hcard_le : exceptionalGtYCount N Y ≤
      ∑ p ∈ excPrimesIoc N Y,
        ((Finset.Icc 1 N).filter (fun n => p ∣ n)).card := by
    rw [exceptionalGtYCount]
    exact le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le)
  -- Step 3: each piece ≤ N/p + 1 (p prime > Y ≥ 0, so p > 0)
  refine le_trans hcard_le (Finset.sum_le_sum ?_)
  intro p hp
  rw [excPrimesIoc, Finset.mem_filter, Finset.mem_Ioc] at hp
  exact card_multiples_le N p hp.2.1.pos

/-- The exponential saving is antitone in the level: for fixed positive `c`,
larger cutoffs have at least as much saving. -/
theorem saving_anti_of_le {c : ℝ} (hc : 0 < c) {Y N : ℕ}
    (hY : 3 ≤ Y) (hYN : Y ≤ N) :
    saving c N ≤ saving c Y := by
  unfold saving
  have hYpos : (0 : ℝ) < Y := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hY)
  have hYone : (1 : ℝ) ≤ Y := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) hY)
  have hYNreal : (Y : ℝ) ≤ N := by
    exact_mod_cast hYN
  have hlog : Real.log (Y : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hYpos hYNreal
  have hpow :
      (Real.log Y) ^ ((3 : ℝ) / 4) ≤
        (Real.log N) ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow (Real.log_nonneg hYone) hlog (by norm_num)
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- For a fixed level, a larger exponential constant gives a smaller saving. -/
theorem saving_anti_of_const_le {c c' : ℝ} (hcc' : c ≤ c') {Y : ℕ}
    (hY : 3 ≤ Y) :
    saving c' Y ≤ saving c Y := by
  unfold saving
  have hYone : (1 : ℝ) ≤ Y := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) hY)
  have hL : 0 ≤ (Real.log Y) ^ ((3 : ℝ) / 4) :=
    Real.rpow_nonneg (Real.log_nonneg hYone) _
  exact Real.exp_le_exp.mpr (by
    nlinarith [mul_le_mul_of_nonneg_right hcc' hL])

/-- If `Y ≥ N^η`, then the exponential saving at level `Y` may be moved to
level `N`, after shrinking the saving constant by the fixed power factor
`η^{3/4}`. -/
theorem saving_le_saving_of_power_lower {c η : ℝ} (hc : 0 < c) (hη : 0 < η)
    {N Y : ℕ} (hN : 3 ≤ N) (hNY : (N : ℝ) ^ η ≤ (Y : ℝ)) :
    saving c Y ≤ saving (c * η ^ ((3 : ℝ) / 4)) N := by
  unfold saving
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hYpos : (0 : ℝ) < Y :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos η) hNY
  have hlogNY :
      η * Real.log (N : ℝ) ≤ Real.log (Y : ℝ) := by
    have hlog := Real.log_le_log (Real.rpow_pos_of_pos hNpos η) hNY
    rw [Real.log_rpow hNpos η] at hlog
    exact hlog
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := (log_pos_of_three_le hN).le
  have heta_nonneg : 0 ≤ η := hη.le
  have hpow :
      η ^ ((3 : ℝ) / 4) * (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4) ≤
        (Real.log (Y : ℝ)) ^ ((3 : ℝ) / 4) := by
    have hmono :
        (η * Real.log (N : ℝ)) ^ ((3 : ℝ) / 4) ≤
          (Real.log (Y : ℝ)) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow (mul_nonneg heta_nonneg hlogN_nonneg) hlogNY (by norm_num)
    have hmul :
        (η * Real.log (N : ℝ)) ^ ((3 : ℝ) / 4) =
          η ^ ((3 : ℝ) / 4) * (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4) :=
      Real.mul_rpow heta_nonneg hlogN_nonneg
    rwa [hmul] at hmono
  exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hpow hc.le])

/-- If `Y ≥ exp((log N)^(3/4))`, then the usual `3/4` saving at level `Y`
becomes the `9/16` saving at level `N`. -/
theorem saving_le_savingNineSixteen_of_exp_log_three_fourths_lower {c : ℝ}
    (hc : 0 < c) {N Y : ℕ} (hN : 3 ≤ N)
    (hYexp : Real.exp ((Real.log (N : ℝ)) ^ ((3 : ℝ) / 4)) ≤ (Y : ℝ)) :
    saving c Y ≤ savingNineSixteen c N := by
  unfold saving savingNineSixteen
  have hYpos : (0 : ℝ) < Y :=
    lt_of_lt_of_le (Real.exp_pos _) hYexp
  have hlogY :
      (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4) ≤ Real.log (Y : ℝ) := by
    have hlog :=
      Real.log_le_log (Real.exp_pos _) hYexp
    simpa using hlog
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := (log_pos_of_three_le hN).le
  have hbase_nonneg :
      0 ≤ (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4) :=
    Real.rpow_nonneg hlogN_nonneg _
  have hpow :
      (Real.log (N : ℝ)) ^ ((9 : ℝ) / 16) ≤
        (Real.log (Y : ℝ)) ^ ((3 : ℝ) / 4) := by
    have hmono :
        ((Real.log (N : ℝ)) ^ ((3 : ℝ) / 4)) ^ ((3 : ℝ) / 4) ≤
          (Real.log (Y : ℝ)) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow hbase_nonneg hlogY (by norm_num)
    have hmul :
        ((Real.log (N : ℝ)) ^ ((3 : ℝ) / 4)) ^ ((3 : ℝ) / 4) =
          (Real.log (N : ℝ)) ^ ((9 : ℝ) / 16) := by
      rw [← Real.rpow_mul hlogN_nonneg]
      norm_num
    rwa [hmul] at hmono
  exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hpow hc.le])

/-- Exceptional primes in `(Y,N]` are a subset of all exceptional primes up to
`N`. -/
theorem excPrimesIoc_card_le_primeExceptionalCount (N Y : ℕ) :
    (excPrimesIoc N Y).card ≤ primeExceptionalCount N := by
  classical
  apply Finset.card_le_card
  intro p hp
  rw [excPrimesIoc, Finset.mem_filter, Finset.mem_Ioc] at hp
  change p ∈ (Finset.Icc 2 N).filter
    (fun n => n.Prime ∧ EscLeanChecks.esExceptional n)
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hp.2.1.two_le, hp.1.2⟩, hp.2⟩

/-- Main exceptional-set control bounds the number of exceptional primes in any
interval `(Y,N]` by the same saving evaluated at `Y`. -/
theorem excPrimesIoc_card_bound_of_main (h : IsMainBound exceptionalCount) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N Y : ℕ, 3 ≤ Y → Y ≤ N →
      ((excPrimesIoc N Y).card : ℝ) ≤ C * (N : ℝ) * saving c Y := by
  obtain ⟨c, hc, C, hC, hprime⟩ := prime_exceptional_of_main h
  refine ⟨c, hc, C, hC, fun N Y hY hYN => ?_⟩
  have hN : 3 ≤ N := le_trans hY hYN
  have hcard :
      ((excPrimesIoc N Y).card : ℝ) ≤ (primeExceptionalCount N : ℝ) := by
    exact_mod_cast excPrimesIoc_card_le_primeExceptionalCount N Y
  have hsav : saving c N ≤ saving c Y := saving_anti_of_le hc hY hYN
  calc ((excPrimesIoc N Y).card : ℝ)
      ≤ (primeExceptionalCount N : ℝ) := hcard
    _ ≤ C * (N : ℝ) * saving c N := hprime N hN
    _ ≤ C * (N : ℝ) * saving c Y := by
        apply mul_le_mul_of_nonneg_left hsav
        positivity

/-- Prime-main-bound variant of `excPrimesIoc_card_bound_of_main`.

This avoids routing through the full exceptional set when a certificate route has
already produced `IsMainBound primeExceptionalCount` directly. -/
theorem excPrimesIoc_card_bound_of_prime_main (h : IsMainBound primeExceptionalCount) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N Y : ℕ, 3 ≤ Y → Y ≤ N →
      ((excPrimesIoc N Y).card : ℝ) ≤ C * (N : ℝ) * saving c Y := by
  obtain ⟨c, hc, C, hC, hprime⟩ := h
  refine ⟨c, hc, C, hC, fun N Y hY hYN => ?_⟩
  have hN : 3 ≤ N := le_trans hY hYN
  have hcard :
      ((excPrimesIoc N Y).card : ℝ) ≤ (primeExceptionalCount N : ℝ) := by
    exact_mod_cast excPrimesIoc_card_le_primeExceptionalCount N Y
  have hsav : saving c N ≤ saving c Y := saving_anti_of_le hc hY hYN
  calc ((excPrimesIoc N Y).card : ℝ)
      ≤ (primeExceptionalCount N : ℝ) := hcard
    _ ≤ C * (N : ℝ) * saving c N := hprime N hN
    _ ≤ C * (N : ℝ) * saving c Y := by
        apply mul_le_mul_of_nonneg_left hsav
        positivity

/-- Real form of the union bound split into the reciprocal part and the
cardinality of the exceptional-prime index set. -/
theorem exceptionalGtYCount_le_sum_div_add_card_real (N Y : ℕ) :
    (exceptionalGtYCount N Y : ℝ) ≤
      (∑ p ∈ excPrimesIoc N Y, ((N / p : ℕ) : ℝ)) +
        ((excPrimesIoc N Y).card : ℝ) := by
  have hub := exceptionalGtYCount_le_sum N Y
  have hub_real : (exceptionalGtYCount N Y : ℝ)
      ≤ (∑ p ∈ excPrimesIoc N Y, ((N / p : ℕ) + 1) : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hub
    rw [Nat.cast_sum] at this
    convert this using 2 with p
    push_cast
    ring
  refine le_trans hub_real ?_
  exact le_of_eq (by
    trans (∑ p ∈ excPrimesIoc N Y, (((N / p : ℕ) : ℝ) + 1))
    · simp
    · rw [Finset.sum_add_distrib]
      simp)

/-- The floor-divisor part of the large-prime-factor union bound is dominated
by `N` times the reciprocal sum over the same exceptional primes. -/
theorem exceptionalGtY_floor_div_sum_le_mul_prime_recip_sum (N Y : ℕ) :
    (∑ p ∈ excPrimesIoc N Y, ((N / p : ℕ) : ℝ)) ≤
      (N : ℝ) * ∑ p ∈ excPrimesIoc N Y, (1 : ℝ) / (p : ℝ) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  rw [excPrimesIoc, Finset.mem_filter, Finset.mem_Ioc] at hp
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.2.1.pos
  calc ((N / p : ℕ) : ℝ)
      ≤ (N : ℝ) / (p : ℝ) :=
        (Nat.cast_div_le : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / (p : ℝ))
    _ = (N : ℝ) * ((1 : ℝ) / (p : ℝ)) := by
        field_simp [hp_pos.ne']

/-- On the exceptional-prime interval `(Y,N]`, the reciprocal sum is bounded by
the interval cardinality divided by `Y`. -/
theorem excPrimesIoc_recip_sum_le_card_div (N Y : ℕ) (hYpos : 0 < Y) :
    (∑ p ∈ excPrimesIoc N Y, (1 : ℝ) / (p : ℝ))
      ≤ ((excPrimesIoc N Y).card : ℝ) / (Y : ℝ) := by
  classical
  have hYposR : (0 : ℝ) < Y := by exact_mod_cast hYpos
  calc
    (∑ p ∈ excPrimesIoc N Y, (1 : ℝ) / (p : ℝ))
        ≤ ∑ _p ∈ excPrimesIoc N Y, (1 : ℝ) / (Y : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          rw [excPrimesIoc, Finset.mem_filter, Finset.mem_Ioc] at hp
          have hYp : (Y : ℝ) ≤ (p : ℝ) := by exact_mod_cast (le_of_lt hp.1.1)
          have hp_pos : (0 : ℝ) < p := lt_of_lt_of_le hYposR hYp
          exact one_div_le_one_div_of_le hYposR hYp
      _ = ((excPrimesIoc N Y).card : ℝ) / (Y : ℝ) := by
          simp [div_eq_mul_inv, mul_comm]

/-- A dyadic shell is contained in the exceptional primes up to its right
endpoint. -/
theorem excPrimesDyadicShell_card_le_primeExceptionalCount (N Y k : ℕ) :
    (excPrimesDyadicShell N Y k).card ≤ primeExceptionalCount (2 ^ (k + 1) * Y) := by
  classical
  apply Finset.card_le_card
  intro p hp
  rw [excPrimesDyadicShell, Finset.mem_filter] at hp
  obtain ⟨hbase, _hlower, hupper⟩ := hp
  rw [excPrimesIoc, Finset.mem_filter, Finset.mem_Ioc] at hbase
  change p ∈ (Finset.Icc 2 (2 ^ (k + 1) * Y)).filter
    (fun n => n.Prime ∧ EscLeanChecks.esExceptional n)
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hbase.2.1.two_le, le_of_lt hupper⟩, hbase.2⟩

/-- Reciprocal sum over a dyadic shell is bounded by shell cardinality divided
by its left endpoint. -/
theorem excPrimesDyadicShell_recip_sum_le_card_div
    (N Y k : ℕ) (hYpos : 0 < Y) :
    (∑ p ∈ excPrimesDyadicShell N Y k, (1 : ℝ) / (p : ℝ))
      ≤ ((excPrimesDyadicShell N Y k).card : ℝ) / ((2 ^ k * Y : ℕ) : ℝ) := by
  classical
  have hdenNat : 0 < 2 ^ k * Y :=
    Nat.mul_pos (Nat.pow_pos (a := 2) (n := k) (by norm_num)) hYpos
  have hden : (0 : ℝ) < (2 ^ k * Y : ℕ) := by exact_mod_cast hdenNat
  calc
    (∑ p ∈ excPrimesDyadicShell N Y k, (1 : ℝ) / (p : ℝ))
        ≤ ∑ _p ∈ excPrimesDyadicShell N Y k, (1 : ℝ) / ((2 ^ k * Y : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          rw [excPrimesDyadicShell, Finset.mem_filter] at hp
          have hdenp : ((2 ^ k * Y : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.1
          have hp_pos : (0 : ℝ) < p := lt_of_lt_of_le hden hdenp
          exact one_div_le_one_div_of_le hden hdenp
      _ = ((excPrimesDyadicShell N Y k).card : ℝ) / ((2 ^ k * Y : ℕ) : ℝ) := by
          simp [div_eq_mul_inv, mul_comm]

/-- Dyadic-shell reciprocal estimate from the prime-main exceptional bound.

Each shell has relative width at most a factor of two, so cardinality control at
the right endpoint gives a reciprocal contribution `O(saving(Y))`.  Summing
these checked shell estimates over the dyadic shell indices is the remaining
finite-sum step in the global partial-summation envelope. -/
theorem excPrimesDyadicShell_recip_bound_of_prime_main
    (hprime : IsMainBound primeExceptionalCount) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N Y k : ℕ, 3 ≤ Y →
      (∑ p ∈ excPrimesDyadicShell N Y k, (1 : ℝ) / (p : ℝ))
        ≤ C * saving c Y := by
  obtain ⟨c, hc, C₀, hC₀, hmain⟩ := hprime
  refine ⟨c, hc, 2 * C₀, by positivity, fun N Y k hY => ?_⟩
  let L : ℕ := 2 ^ k * Y
  let U : ℕ := 2 ^ (k + 1) * Y
  have hYpos : 0 < Y := lt_of_lt_of_le (by norm_num : 0 < 3) hY
  have hLpos : 0 < L := by
    dsimp [L]
    exact Nat.mul_pos (Nat.pow_pos (a := 2) (n := k) (by norm_num)) hYpos
  have hLposR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  have hU_eq : U = 2 * L := by
    dsimp [U, L]
    rw [Nat.pow_succ]
    ring
  have hYU : Y ≤ U := by
    dsimp [U]
    have hone : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow (k + 1) 2 (by norm_num)
    nlinarith [Nat.mul_le_mul_right Y hone]
  have hU_ge : 3 ≤ U := le_trans hY hYU
  have hsav : saving c U ≤ saving c Y := saving_anti_of_le hc hY hYU
  have hcardNat :
      (excPrimesDyadicShell N Y k).card ≤ primeExceptionalCount U := by
    dsimp [U]
    exact excPrimesDyadicShell_card_le_primeExceptionalCount N Y k
  have hcard :
      ((excPrimesDyadicShell N Y k).card : ℝ) ≤ C₀ * (U : ℝ) * saving c U := by
    exact le_trans (by exact_mod_cast hcardNat) (hmain U hU_ge)
  calc
    (∑ p ∈ excPrimesDyadicShell N Y k, (1 : ℝ) / (p : ℝ))
        ≤ ((excPrimesDyadicShell N Y k).card : ℝ) / (L : ℝ) :=
          excPrimesDyadicShell_recip_sum_le_card_div N Y k hYpos
    _ ≤ (C₀ * (U : ℝ) * saving c U) / (L : ℝ) := by
        exact div_le_div_of_nonneg_right hcard hLposR.le
    _ ≤ (C₀ * (U : ℝ) * saving c Y) / (L : ℝ) := by
        apply div_le_div_of_nonneg_right _ hLposR.le
        apply mul_le_mul_of_nonneg_left hsav
        positivity
    _ = 2 * C₀ * saving c Y := by
        rw [hU_eq]
        field_simp [hLposR.ne']
        ring

/-- The exceptional-prime interval is covered by dyadic shells with indices
`k ≤ log₂ N`. -/
theorem excPrimesIoc_subset_dyadicShell_biUnion (N Y : ℕ) (hY : 0 < Y) :
    excPrimesIoc N Y ⊆
      (Finset.range (Nat.log 2 N + 1)).biUnion
        (fun k => excPrimesDyadicShell N Y k) := by
  classical
  intro p hp
  rw [Finset.mem_biUnion]
  let k := Nat.log 2 (p / Y)
  refine ⟨k, ?_, ?_⟩
  · rw [Finset.mem_range]
    have hp_le_N : p ≤ N := by
      rw [excPrimesIoc, Finset.mem_filter, Finset.mem_Ioc] at hp
      exact hp.1.2
    have hdiv_le_N : p / Y ≤ N := le_trans (Nat.div_le_self p Y) hp_le_N
    have hk_le : k ≤ Nat.log 2 N := Nat.log_mono_right hdiv_le_N
    exact Nat.lt_succ_of_le hk_le
  · exact mem_excPrimesDyadicShell_of_mem_excPrimesIoc hY hp

/-- Dyadic shells are pairwise disjoint. -/
theorem excPrimesDyadicShell_pairwiseDisjoint (N Y K : ℕ) :
    (↑(Finset.range K) : Set ℕ).PairwiseDisjoint
      (fun k => excPrimesDyadicShell N Y k) := by
  classical
  intro i _hi j _hj hij
  change Disjoint (excPrimesDyadicShell N Y i) (excPrimesDyadicShell N Y j)
  rw [Finset.disjoint_left]
  intro p hpi hpj
  rw [excPrimesDyadicShell, Finset.mem_filter] at hpi hpj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hi_succ_le_j : i + 1 ≤ j := Nat.succ_le_of_lt hijlt
    have hpow : 2 ^ (i + 1) ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) hi_succ_le_j
    have hleft : 2 ^ (i + 1) * Y ≤ 2 ^ j * Y :=
      Nat.mul_le_mul_right Y hpow
    exact not_le_of_gt hpi.2.2 (le_trans hleft hpj.2.1)
  · have hj_succ_le_i : j + 1 ≤ i := Nat.succ_le_of_lt hjilt
    have hpow : 2 ^ (j + 1) ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) hj_succ_le_i
    have hleft : 2 ^ (j + 1) * Y ≤ 2 ^ i * Y :=
      Nat.mul_le_mul_right Y hpow
    exact not_le_of_gt hpj.2.2 (le_trans hleft hpi.2.1)

/-- The reciprocal sum over all exceptional primes in `(Y,N]` is bounded by the
sum of the reciprocal sums over the finite dyadic shell cover. -/
theorem excPrimesIoc_recip_sum_le_dyadicShell_sum (N Y : ℕ) (hY : 0 < Y) :
    (∑ p ∈ excPrimesIoc N Y, (1 : ℝ) / (p : ℝ)) ≤
      ∑ k ∈ Finset.range (Nat.log 2 N + 1),
        ∑ p ∈ excPrimesDyadicShell N Y k, (1 : ℝ) / (p : ℝ) := by
  classical
  have hsub := excPrimesIoc_subset_dyadicShell_biUnion N Y hY
  calc
    (∑ p ∈ excPrimesIoc N Y, (1 : ℝ) / (p : ℝ))
        ≤ ∑ p ∈
            (Finset.range (Nat.log 2 N + 1)).biUnion
              (fun k => excPrimesDyadicShell N Y k),
            (1 : ℝ) / (p : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro p _hpbig _hpnot
          positivity
    _ = ∑ k ∈ Finset.range (Nat.log 2 N + 1),
          ∑ p ∈ excPrimesDyadicShell N Y k, (1 : ℝ) / (p : ℝ) := by
        rw [Finset.sum_biUnion
          (excPrimesDyadicShell_pairwiseDisjoint N Y (Nat.log 2 N + 1))]

/-- Real logarithmic bound for the number of dyadic shells. -/
theorem nat_log_two_add_one_le_log (N : ℕ) (hN : 3 ≤ N) :
    ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤
      (1 / Real.log 2 + 1) * (1 + Real.log N) := by
  have hlogNnonneg : 0 ≤ Real.log (N : ℝ) := by
    have hNone : (1 : ℝ) ≤ N := by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) hN)
    exact Real.log_nonneg hNone
  have hnatlog : ((Nat.log 2 N : ℕ) : ℝ) ≤
      Real.log (N : ℝ) / Real.log (2 : ℝ) := by
    have h := Real.natLog_le_logb N 2
    simpa [Real.logb] using h
  have hstep : ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤
      Real.log (N : ℝ) / Real.log (2 : ℝ) + 1 := by
    norm_num
    linarith
  calc
    ((Nat.log 2 N + 1 : ℕ) : ℝ)
        ≤ Real.log (N : ℝ) / Real.log (2 : ℝ) + 1 := hstep
    _ = (1 / Real.log 2) * Real.log N + 1 := by ring
    _ ≤ (1 / Real.log 2 + 1) * (1 + Real.log N) := by
      have hinvnonneg : 0 ≤ 1 / Real.log (2 : ℝ) := by positivity
      nlinarith [mul_nonneg hinvnonneg hlogNnonneg]

/-- Global reciprocal-prime envelope obtained by summing checked dyadic shells.

This formalizes the finite summation step behind the manuscript's
partial-summation estimate: from `IsMainBound primeExceptionalCount` alone, the
reciprocal sum over exceptional primes in `(Y,N]` is
`O((1+log N) saving(Y))`. -/
theorem excPrimesIoc_recip_envelope_of_prime_main
    (hprime : IsMainBound primeExceptionalCount) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N Y : ℕ, 3 ≤ Y → Y ≤ N →
      (∑ p ∈ excPrimesIoc N Y, (1 : ℝ) / (p : ℝ))
        ≤ C * (1 + Real.log N) * saving c Y := by
  obtain ⟨c, hc, Cs, hCs, hshell⟩ :=
    excPrimesDyadicShell_recip_bound_of_prime_main hprime
  let B : ℝ := 1 / Real.log 2 + 1
  refine ⟨c, hc, B * Cs, by dsimp [B]; positivity, fun N Y hY hYN => ?_⟩
  have hYpos : 0 < Y := lt_of_lt_of_le (by norm_num : 0 < 3) hY
  have hN : 3 ≤ N := le_trans hY hYN
  have hK : (((Finset.range (Nat.log 2 N + 1)).card : ℕ) : ℝ) ≤
      B * (1 + Real.log N) := by
    rw [Finset.card_range]
    exact nat_log_two_add_one_le_log N hN
  calc
    (∑ p ∈ excPrimesIoc N Y, (1 : ℝ) / (p : ℝ))
        ≤ ∑ k ∈ Finset.range (Nat.log 2 N + 1),
            ∑ p ∈ excPrimesDyadicShell N Y k, (1 : ℝ) / (p : ℝ) :=
          excPrimesIoc_recip_sum_le_dyadicShell_sum N Y hYpos
    _ ≤ ∑ _k ∈ Finset.range (Nat.log 2 N + 1), Cs * saving c Y := by
        exact Finset.sum_le_sum (fun k _hk => hshell N Y k hY)
    _ = (((Finset.range (Nat.log 2 N + 1)).card : ℕ) : ℝ) *
          (Cs * saving c Y) := by
        simp [mul_comm]
    _ ≤ (B * (1 + Real.log N)) * (Cs * saving c Y) := by
        apply mul_le_mul_of_nonneg_right hK
        exact mul_nonneg hCs.le (Real.exp_pos _).le
    _ = (B * Cs) * (1 + Real.log N) * saving c Y := by ring

/-- Short-shell reciprocal bound from the main exceptional-prime estimate.

If `N` is in a fixed multiplicative shell above `Y`, the reciprocal sum over
exceptional primes in `(Y,N]` needs no partial summation: cardinality divided by
`Y` is enough.  The full large-prime-factor argument is then reduced to summing
these shell estimates. -/
theorem excPrimesIoc_recip_shell_bound_of_main
    (hmain : IsMainBound exceptionalCount) {A : ℝ} (_hA : 0 < A) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N Y : ℕ, 3 ≤ Y → Y ≤ N →
      (N : ℝ) ≤ A * (Y : ℝ) →
      (∑ p ∈ excPrimesIoc N Y, (1 : ℝ) / (p : ℝ)) ≤ C * A * saving c Y := by
  obtain ⟨c, hc, C, hC, hcard⟩ := excPrimesIoc_card_bound_of_main hmain
  refine ⟨c, hc, C, hC, fun N Y hY hYN hshell => ?_⟩
  have hYposNat : 0 < Y := lt_of_lt_of_le (by norm_num : 0 < 3) hY
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast hYposNat
  have hratio : (N : ℝ) / (Y : ℝ) ≤ A := by
    rw [div_le_iff₀ hYpos]
    exact hshell
  calc
    (∑ p ∈ excPrimesIoc N Y, (1 : ℝ) / (p : ℝ))
        ≤ ((excPrimesIoc N Y).card : ℝ) / (Y : ℝ) :=
          excPrimesIoc_recip_sum_le_card_div N Y hYposNat
    _ ≤ (C * (N : ℝ) * saving c Y) / (Y : ℝ) := by
        exact div_le_div_of_nonneg_right (hcard N Y hY hYN) hYpos.le
    _ = C * ((N : ℝ) / (Y : ℝ)) * saving c Y := by
        ring
    _ ≤ C * A * saving c Y := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left hratio hC.le

/-- Prime-main-bound variant of the short-shell reciprocal estimate. -/
theorem excPrimesIoc_recip_shell_bound_of_prime_main
    (hprime : IsMainBound primeExceptionalCount) {A : ℝ} (_hA : 0 < A) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N Y : ℕ, 3 ≤ Y → Y ≤ N →
      (N : ℝ) ≤ A * (Y : ℝ) →
      (∑ p ∈ excPrimesIoc N Y, (1 : ℝ) / (p : ℝ)) ≤ C * A * saving c Y := by
  obtain ⟨c, hc, C, hC, hcard⟩ := excPrimesIoc_card_bound_of_prime_main hprime
  refine ⟨c, hc, C, hC, fun N Y hY hYN hshell => ?_⟩
  have hYposNat : 0 < Y := lt_of_lt_of_le (by norm_num : 0 < 3) hY
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast hYposNat
  have hratio : (N : ℝ) / (Y : ℝ) ≤ A := by
    rw [div_le_iff₀ hYpos]
    exact hshell
  calc
    (∑ p ∈ excPrimesIoc N Y, (1 : ℝ) / (p : ℝ))
        ≤ ((excPrimesIoc N Y).card : ℝ) / (Y : ℝ) :=
          excPrimesIoc_recip_sum_le_card_div N Y hYposNat
    _ ≤ (C * (N : ℝ) * saving c Y) / (Y : ℝ) := by
        exact div_le_div_of_nonneg_right (hcard N Y hY hYN) hYpos.le
    _ = C * ((N : ℝ) / (Y : ℝ)) * saving c Y := by
        ring
    _ ≤ C * A * saving c Y := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left hratio hC.le

/-- Large-prime-factor bound on a single multiplicative shell.

This is the checked local piece of the manuscript's partial-summation argument:
for `N ≤ A Y`, the reciprocal contribution is obtained from the exceptional-prime
cardinality bound alone.  The remaining global envelope is the dyadic summation
over such shells. -/
theorem exceptionalGtY_quantitative_on_shell
    (hmain : IsMainBound exceptionalCount) {A : ℝ} (hA : 0 < A) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N Y : ℕ, 3 ≤ Y → Y ≤ N →
      (N : ℝ) ≤ A * (Y : ℝ) →
      (exceptionalGtYCount N Y : ℝ)
        ≤ C * (N : ℝ) * (1 + Real.log N) * saving c Y := by
  obtain ⟨crecip, hcrecip, Crecip, hCrecip, hrecipShell⟩ :=
    excPrimesIoc_recip_shell_bound_of_main hmain hA
  obtain ⟨ccard, hccard, Ccard, hCcard, hcard⟩ :=
    excPrimesIoc_card_bound_of_main hmain
  let c := min crecip ccard
  have hc : 0 < c := lt_min hcrecip hccard
  let C := Crecip * A + Ccard
  have hC : 0 < C := by positivity
  refine ⟨c, hc, C, hC, fun N Y hY hYN hshell => ?_⟩
  have hN : 3 ≤ N := le_trans hY hYN
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := by
    have hNone : (1 : ℝ) ≤ N := by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) hN)
    exact Real.log_nonneg hNone
  have hlog_factor : (1 : ℝ) ≤ 1 + Real.log (N : ℝ) := by linarith
  have hsav_recip : saving crecip Y ≤ saving c Y :=
    saving_anti_of_const_le (min_le_left crecip ccard) hY
  have hsav_card : saving ccard Y ≤ saving c Y :=
    saving_anti_of_const_le (min_le_right crecip ccard) hY
  have hNnonneg : (0 : ℝ) ≤ N := by positivity
  have hrecip' :
      (∑ p ∈ excPrimesIoc N Y, ((N / p : ℕ) : ℝ))
        ≤ Crecip * A * (N : ℝ) * (1 + Real.log N) * saving c Y := by
    calc
      (∑ p ∈ excPrimesIoc N Y, ((N / p : ℕ) : ℝ))
          ≤ (N : ℝ) * ∑ p ∈ excPrimesIoc N Y, (1 : ℝ) / (p : ℝ) :=
            exceptionalGtY_floor_div_sum_le_mul_prime_recip_sum N Y
      _ ≤ (N : ℝ) * (Crecip * A * saving crecip Y) := by
          exact mul_le_mul_of_nonneg_left (hrecipShell N Y hY hYN hshell) hNnonneg
      _ ≤ (N : ℝ) * (Crecip * A * saving c Y) := by
          apply mul_le_mul_of_nonneg_left _ hNnonneg
          apply mul_le_mul_of_nonneg_left hsav_recip
          positivity
      _ = Crecip * A * (N : ℝ) * saving c Y := by ring
      _ ≤ Crecip * A * (N : ℝ) * (1 + Real.log N) * saving c Y := by
          have hcoef : 0 ≤ Crecip * A * (N : ℝ) := by positivity
          have hsav_nonneg : 0 ≤ saving c Y := (Real.exp_pos _).le
          nlinarith [mul_le_mul_of_nonneg_left hlog_factor hcoef,
            mul_nonneg hcoef hsav_nonneg]
  have hcard' :
      ((excPrimesIoc N Y).card : ℝ)
        ≤ Ccard * (N : ℝ) * (1 + Real.log N) * saving c Y := by
    calc
      ((excPrimesIoc N Y).card : ℝ)
          ≤ Ccard * (N : ℝ) * saving ccard Y := hcard N Y hY hYN
      _ ≤ Ccard * (N : ℝ) * saving c Y := by
          apply mul_le_mul_of_nonneg_left hsav_card
          positivity
      _ ≤ Ccard * (N : ℝ) * (1 + Real.log N) * saving c Y := by
          have hcoef : 0 ≤ Ccard * (N : ℝ) := by positivity
          have hsav_nonneg : 0 ≤ saving c Y := (Real.exp_pos _).le
          nlinarith [mul_le_mul_of_nonneg_left hlog_factor hcoef,
            mul_nonneg hcoef hsav_nonneg]
  calc
    (exceptionalGtYCount N Y : ℝ)
        ≤ (∑ p ∈ excPrimesIoc N Y, ((N / p : ℕ) : ℝ)) +
            ((excPrimesIoc N Y).card : ℝ) :=
          exceptionalGtYCount_le_sum_div_add_card_real N Y
    _ ≤ Crecip * A * (N : ℝ) * (1 + Real.log N) * saving c Y +
          Ccard * (N : ℝ) * (1 + Real.log N) * saving c Y :=
        add_le_add hrecip' hcard'
    _ = C * (N : ℝ) * (1 + Real.log N) * saving c Y := by
        dsimp [C]
        ring

/-- Prime-main-bound variant of the one-shell large-prime-factor estimate.

This form is tailored to certificate-facing routes that first prove
`IsMainBound primeExceptionalCount`: the shell bound then follows without going
back through `IsMainBound exceptionalCount`. -/
theorem exceptionalGtY_quantitative_on_shell_of_prime_main
    (hprime : IsMainBound primeExceptionalCount) {A : ℝ} (hA : 0 < A) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N Y : ℕ, 3 ≤ Y → Y ≤ N →
      (N : ℝ) ≤ A * (Y : ℝ) →
      (exceptionalGtYCount N Y : ℝ)
        ≤ C * (N : ℝ) * (1 + Real.log N) * saving c Y := by
  obtain ⟨crecip, hcrecip, Crecip, hCrecip, hrecipShell⟩ :=
    excPrimesIoc_recip_shell_bound_of_prime_main hprime hA
  obtain ⟨ccard, hccard, Ccard, hCcard, hcard⟩ :=
    excPrimesIoc_card_bound_of_prime_main hprime
  let c := min crecip ccard
  have hc : 0 < c := lt_min hcrecip hccard
  let C := Crecip * A + Ccard
  have hC : 0 < C := by positivity
  refine ⟨c, hc, C, hC, fun N Y hY hYN hshell => ?_⟩
  have hN : 3 ≤ N := le_trans hY hYN
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := by
    have hNone : (1 : ℝ) ≤ N := by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) hN)
    exact Real.log_nonneg hNone
  have hlog_factor : (1 : ℝ) ≤ 1 + Real.log (N : ℝ) := by linarith
  have hsav_recip : saving crecip Y ≤ saving c Y :=
    saving_anti_of_const_le (min_le_left crecip ccard) hY
  have hsav_card : saving ccard Y ≤ saving c Y :=
    saving_anti_of_const_le (min_le_right crecip ccard) hY
  have hNnonneg : (0 : ℝ) ≤ N := by positivity
  have hrecip' :
      (∑ p ∈ excPrimesIoc N Y, ((N / p : ℕ) : ℝ))
        ≤ Crecip * A * (N : ℝ) * (1 + Real.log N) * saving c Y := by
    calc
      (∑ p ∈ excPrimesIoc N Y, ((N / p : ℕ) : ℝ))
          ≤ (N : ℝ) * ∑ p ∈ excPrimesIoc N Y, (1 : ℝ) / (p : ℝ) :=
            exceptionalGtY_floor_div_sum_le_mul_prime_recip_sum N Y
      _ ≤ (N : ℝ) * (Crecip * A * saving crecip Y) := by
          exact mul_le_mul_of_nonneg_left (hrecipShell N Y hY hYN hshell) hNnonneg
      _ ≤ (N : ℝ) * (Crecip * A * saving c Y) := by
          apply mul_le_mul_of_nonneg_left _ hNnonneg
          apply mul_le_mul_of_nonneg_left hsav_recip
          positivity
      _ = Crecip * A * (N : ℝ) * saving c Y := by ring
      _ ≤ Crecip * A * (N : ℝ) * (1 + Real.log N) * saving c Y := by
          have hcoef : 0 ≤ Crecip * A * (N : ℝ) := by positivity
          have hsav_nonneg : 0 ≤ saving c Y := (Real.exp_pos _).le
          nlinarith [mul_le_mul_of_nonneg_left hlog_factor hcoef,
            mul_nonneg hcoef hsav_nonneg]
  have hcard' :
      ((excPrimesIoc N Y).card : ℝ)
        ≤ Ccard * (N : ℝ) * (1 + Real.log N) * saving c Y := by
    calc
      ((excPrimesIoc N Y).card : ℝ)
          ≤ Ccard * (N : ℝ) * saving ccard Y := hcard N Y hY hYN
      _ ≤ Ccard * (N : ℝ) * saving c Y := by
          apply mul_le_mul_of_nonneg_left hsav_card
          positivity
      _ ≤ Ccard * (N : ℝ) * (1 + Real.log N) * saving c Y := by
          have hcoef : 0 ≤ Ccard * (N : ℝ) := by positivity
          have hsav_nonneg : 0 ≤ saving c Y := (Real.exp_pos _).le
          nlinarith [mul_le_mul_of_nonneg_left hlog_factor hcoef,
            mul_nonneg hcoef hsav_nonneg]
  calc
    (exceptionalGtYCount N Y : ℝ)
        ≤ (∑ p ∈ excPrimesIoc N Y, ((N / p : ℕ) : ℝ)) +
            ((excPrimesIoc N Y).card : ℝ) :=
          exceptionalGtYCount_le_sum_div_add_card_real N Y
    _ ≤ Crecip * A * (N : ℝ) * (1 + Real.log N) * saving c Y +
          Ccard * (N : ℝ) * (1 + Real.log N) * saving c Y :=
        add_le_add hrecip' hcard'
    _ = C * (N : ℝ) * (1 + Real.log N) * saving c Y := by
        dsimp [C]
        ring

/-- **Proposition `prop:large-prime-factor` (tex 2118-2165), quantitative form.**

`E_{>Y}(N) ≪ N(1+log N)·exp(-c(log Y)^{3/4})` uniformly for `3 ≤ Y ≤ N`.

The proof in the manuscript is partial summation of `cor:prime-exceptional`
against `A(t)=#𝒫_exc(t)`:
`∑_{Y<p≤N, exc} 1/p ≤ A(N)/N + ∫_Y^N A(t)/t² dt ≪ (1+log N)exp(-c(log Y)^{3/4})`,
and `E_{>Y}(N) ≤ N · ∑ 1/p`.

We have proved the **combinatorial union bound**
`E_{>Y}(N) ≤ ∑_{Y<p≤N, exc} (N/p+1)` (`exceptionalGtYCount_le_sum`).  The
remaining ingredient — the analytic *envelope* for that prime sum, obtained by
Abel summation of `cor:prime-exceptional` (tex 2155-2160) — is taken here as an
explicit **hypothesis** `henv`, so the theorem is an explicit conditional
derivation.  (This is a downstream analytic estimate built on
`cor:prime-exceptional`; per the interface rule we do not axiomatize it but expose
it as a hypothesis.) -/
theorem exceptionalGtY_quantitative
    {C : ℝ} (_hC : 0 < C) {c : ℝ} (_hc : 0 < c)
    (henv : ∀ N Y : ℕ, 3 ≤ Y → Y ≤ N →
      (∑ p ∈ excPrimesIoc N Y, ((N / p : ℕ) + 1) : ℝ)
        ≤ C * (N : ℝ) * (1 + Real.log N) * Real.exp (-c * (Real.log Y) ^ ((3 : ℝ) / 4))) :
    ∀ N Y : ℕ, 3 ≤ Y → Y ≤ N →
      (exceptionalGtYCount N Y : ℝ)
        ≤ C * (N : ℝ) * (1 + Real.log N) * Real.exp (-c * (Real.log Y) ^ ((3 : ℝ) / 4)) := by
  intro N Y hY hYN
  -- cast the integer union bound to ℝ, then chain with the envelope hypothesis.
  have hub := exceptionalGtYCount_le_sum N Y
  have hub_real : (exceptionalGtYCount N Y : ℝ)
      ≤ (∑ p ∈ excPrimesIoc N Y, ((N / p : ℕ) + 1) : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hub
    rw [Nat.cast_sum] at this
    convert this using 2 with p
    push_cast
    ring
  exact le_trans hub_real (henv N Y hY hYN)

/-- Quantitative large-prime-factor bound with the `+1` part of the union bound
handled by the main exceptional-prime estimate.

The remaining hypothesis only needs to bound the reciprocal contribution
`∑_{Y<p≤N, p exc} ⌊N/p⌋`; the cardinality of the exceptional-prime index set is
absorbed formally from `IsMainBound exceptionalCount`. -/
theorem exceptionalGtY_quantitative_of_recip_envelope
    (hmain : IsMainBound exceptionalCount)
    {Crecip : ℝ} (hCrecip : 0 < Crecip) {crecip : ℝ} (hcrecip : 0 < crecip)
    (hrecip : ∀ N Y : ℕ, 3 ≤ Y → Y ≤ N →
      (∑ p ∈ excPrimesIoc N Y, ((N / p : ℕ) : ℝ))
        ≤ Crecip * (N : ℝ) * (1 + Real.log N) * saving crecip Y) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N Y : ℕ, 3 ≤ Y → Y ≤ N →
      (exceptionalGtYCount N Y : ℝ)
        ≤ C * (N : ℝ) * (1 + Real.log N) * saving c Y := by
  obtain ⟨cprime, hcprime, Cprime, hCprime, hcard⟩ :=
    excPrimesIoc_card_bound_of_main hmain
  let c := min crecip cprime
  have hc : 0 < c := lt_min hcrecip hcprime
  let C := Crecip + Cprime
  have hC : 0 < C := by positivity
  refine ⟨c, hc, C, hC, fun N Y hY hYN => ?_⟩
  have hN : 3 ≤ N := le_trans hY hYN
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := by
    have hNone : (1 : ℝ) ≤ N := by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) hN)
    exact Real.log_nonneg hNone
  have hlog_factor : (1 : ℝ) ≤ 1 + Real.log (N : ℝ) := by linarith
  have hsav_recip : saving crecip Y ≤ saving c Y :=
    saving_anti_of_const_le (min_le_left crecip cprime) hY
  have hsav_card : saving cprime Y ≤ saving c Y :=
    saving_anti_of_const_le (min_le_right crecip cprime) hY
  have hrecip' :
      (∑ p ∈ excPrimesIoc N Y, ((N / p : ℕ) : ℝ))
        ≤ Crecip * (N : ℝ) * (1 + Real.log N) * saving c Y := by
    calc
      (∑ p ∈ excPrimesIoc N Y, ((N / p : ℕ) : ℝ))
          ≤ Crecip * (N : ℝ) * (1 + Real.log N) * saving crecip Y :=
            hrecip N Y hY hYN
      _ ≤ Crecip * (N : ℝ) * (1 + Real.log N) * saving c Y := by
          apply mul_le_mul_of_nonneg_left hsav_recip
          positivity
  have hcard' :
      ((excPrimesIoc N Y).card : ℝ)
        ≤ Cprime * (N : ℝ) * (1 + Real.log N) * saving c Y := by
    calc
      ((excPrimesIoc N Y).card : ℝ)
          ≤ Cprime * (N : ℝ) * saving cprime Y := hcard N Y hY hYN
      _ ≤ Cprime * (N : ℝ) * saving c Y := by
          apply mul_le_mul_of_nonneg_left hsav_card
          positivity
      _ ≤ Cprime * (N : ℝ) * (1 + Real.log N) * saving c Y := by
          have hcoef : 0 ≤ Cprime * (N : ℝ) := by positivity
          have hsav_nonneg : 0 ≤ saving c Y := (Real.exp_pos _).le
          nlinarith [mul_le_mul_of_nonneg_left hlog_factor hcoef,
            mul_nonneg hcoef hsav_nonneg]
  calc
    (exceptionalGtYCount N Y : ℝ)
        ≤ (∑ p ∈ excPrimesIoc N Y, ((N / p : ℕ) : ℝ)) +
            ((excPrimesIoc N Y).card : ℝ) :=
          exceptionalGtYCount_le_sum_div_add_card_real N Y
    _ ≤ Crecip * (N : ℝ) * (1 + Real.log N) * saving c Y +
          Cprime * (N : ℝ) * (1 + Real.log N) * saving c Y :=
        add_le_add hrecip' hcard'
    _ = C * (N : ℝ) * (1 + Real.log N) * saving c Y := by
        dsimp [C]
        ring

/-- Prime-main-bound variant of
`exceptionalGtY_quantitative_of_recip_envelope`.

The only difference is the source of the cardinality term:
`IsMainBound primeExceptionalCount` is enough to bound exceptional primes in
`(Y,N]`, so certificate-facing prime capstones do not need a full exceptional-set
main bound to use this large-prime-factor wrapper. -/
theorem exceptionalGtY_quantitative_of_recip_envelope_prime_main
    (hprime : IsMainBound primeExceptionalCount)
    {Crecip : ℝ} (hCrecip : 0 < Crecip) {crecip : ℝ} (hcrecip : 0 < crecip)
    (hrecip : ∀ N Y : ℕ, 3 ≤ Y → Y ≤ N →
      (∑ p ∈ excPrimesIoc N Y, ((N / p : ℕ) : ℝ))
        ≤ Crecip * (N : ℝ) * (1 + Real.log N) * saving crecip Y) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N Y : ℕ, 3 ≤ Y → Y ≤ N →
      (exceptionalGtYCount N Y : ℝ)
        ≤ C * (N : ℝ) * (1 + Real.log N) * saving c Y := by
  obtain ⟨cprime, hcprime, Cprime, hCprime, hcard⟩ :=
    excPrimesIoc_card_bound_of_prime_main hprime
  let c := min crecip cprime
  have hc : 0 < c := lt_min hcrecip hcprime
  let C := Crecip + Cprime
  have hC : 0 < C := by positivity
  refine ⟨c, hc, C, hC, fun N Y hY hYN => ?_⟩
  have hN : 3 ≤ N := le_trans hY hYN
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := by
    have hNone : (1 : ℝ) ≤ N := by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) hN)
    exact Real.log_nonneg hNone
  have hlog_factor : (1 : ℝ) ≤ 1 + Real.log (N : ℝ) := by linarith
  have hsav_recip : saving crecip Y ≤ saving c Y :=
    saving_anti_of_const_le (min_le_left crecip cprime) hY
  have hsav_card : saving cprime Y ≤ saving c Y :=
    saving_anti_of_const_le (min_le_right crecip cprime) hY
  have hrecip' :
      (∑ p ∈ excPrimesIoc N Y, ((N / p : ℕ) : ℝ))
        ≤ Crecip * (N : ℝ) * (1 + Real.log N) * saving c Y := by
    calc
      (∑ p ∈ excPrimesIoc N Y, ((N / p : ℕ) : ℝ))
          ≤ Crecip * (N : ℝ) * (1 + Real.log N) * saving crecip Y :=
            hrecip N Y hY hYN
      _ ≤ Crecip * (N : ℝ) * (1 + Real.log N) * saving c Y := by
          apply mul_le_mul_of_nonneg_left hsav_recip
          positivity
  have hcard' :
      ((excPrimesIoc N Y).card : ℝ)
        ≤ Cprime * (N : ℝ) * (1 + Real.log N) * saving c Y := by
    calc
      ((excPrimesIoc N Y).card : ℝ)
          ≤ Cprime * (N : ℝ) * saving cprime Y := hcard N Y hY hYN
      _ ≤ Cprime * (N : ℝ) * saving c Y := by
          apply mul_le_mul_of_nonneg_left hsav_card
          positivity
      _ ≤ Cprime * (N : ℝ) * (1 + Real.log N) * saving c Y := by
          have hcoef : 0 ≤ Cprime * (N : ℝ) := by positivity
          have hsav_nonneg : 0 ≤ saving c Y := (Real.exp_pos _).le
          nlinarith [mul_le_mul_of_nonneg_left hlog_factor hcoef,
            mul_nonneg hcoef hsav_nonneg]
  calc
    (exceptionalGtYCount N Y : ℝ)
        ≤ (∑ p ∈ excPrimesIoc N Y, ((N / p : ℕ) : ℝ)) +
            ((excPrimesIoc N Y).card : ℝ) :=
          exceptionalGtYCount_le_sum_div_add_card_real N Y
    _ ≤ Crecip * (N : ℝ) * (1 + Real.log N) * saving c Y +
          Cprime * (N : ℝ) * (1 + Real.log N) * saving c Y :=
        add_le_add hrecip' hcard'
    _ = C * (N : ℝ) * (1 + Real.log N) * saving c Y := by
        dsimp [C]
        ring

/-- Quantitative large-prime-factor bound from the manuscript-shaped reciprocal
prime-sum envelope.

Compared with `exceptionalGtY_quantitative_of_recip_envelope`, the remaining
analytic hypothesis is now the partial-summation estimate for
`∑_{Y<p≤N, p exc} 1 / p`; the conversion from `∑⌊N/p⌋` to `N∑1/p` is performed
inside Lean. -/
theorem exceptionalGtY_quantitative_of_prime_recip_envelope
    (hmain : IsMainBound exceptionalCount)
    {Crecip : ℝ} (hCrecip : 0 < Crecip) {crecip : ℝ} (hcrecip : 0 < crecip)
    (hrecip : ∀ N Y : ℕ, 3 ≤ Y → Y ≤ N →
      (∑ p ∈ excPrimesIoc N Y, (1 : ℝ) / (p : ℝ))
        ≤ Crecip * (1 + Real.log N) * saving crecip Y) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N Y : ℕ, 3 ≤ Y → Y ≤ N →
      (exceptionalGtYCount N Y : ℝ)
        ≤ C * (N : ℝ) * (1 + Real.log N) * saving c Y :=
  exceptionalGtY_quantitative_of_recip_envelope hmain hCrecip hcrecip
    (fun N Y hY hYN => by
      calc
        (∑ p ∈ excPrimesIoc N Y, ((N / p : ℕ) : ℝ))
            ≤ (N : ℝ) * ∑ p ∈ excPrimesIoc N Y, (1 : ℝ) / (p : ℝ) :=
              exceptionalGtY_floor_div_sum_le_mul_prime_recip_sum N Y
        _ ≤ (N : ℝ) * (Crecip * (1 + Real.log N) * saving crecip Y) := by
            apply mul_le_mul_of_nonneg_left (hrecip N Y hY hYN)
            positivity
        _ = Crecip * (N : ℝ) * (1 + Real.log N) * saving crecip Y := by
            ring)

/-- Prime-main-bound variant of the manuscript-shaped reciprocal prime-sum
envelope wrapper.

This starts from `IsMainBound primeExceptionalCount`, so the global
large-prime-factor route can be attached directly to certificate-facing prime
capstones once the reciprocal partial-summation envelope is supplied. -/
theorem exceptionalGtY_quantitative_of_prime_recip_envelope_prime_main
    (hprime : IsMainBound primeExceptionalCount)
    {Crecip : ℝ} (hCrecip : 0 < Crecip) {crecip : ℝ} (hcrecip : 0 < crecip)
    (hrecip : ∀ N Y : ℕ, 3 ≤ Y → Y ≤ N →
      (∑ p ∈ excPrimesIoc N Y, (1 : ℝ) / (p : ℝ))
        ≤ Crecip * (1 + Real.log N) * saving crecip Y) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N Y : ℕ, 3 ≤ Y → Y ≤ N →
      (exceptionalGtYCount N Y : ℝ)
        ≤ C * (N : ℝ) * (1 + Real.log N) * saving c Y :=
  exceptionalGtY_quantitative_of_recip_envelope_prime_main hprime hCrecip hcrecip
    (fun N Y hY hYN => by
      calc
        (∑ p ∈ excPrimesIoc N Y, ((N / p : ℕ) : ℝ))
            ≤ (N : ℝ) * ∑ p ∈ excPrimesIoc N Y, (1 : ℝ) / (p : ℝ) :=
              exceptionalGtY_floor_div_sum_le_mul_prime_recip_sum N Y
        _ ≤ (N : ℝ) * (Crecip * (1 + Real.log N) * saving crecip Y) := by
            apply mul_le_mul_of_nonneg_left (hrecip N Y hY hYN)
            positivity
        _ = Crecip * (N : ℝ) * (1 + Real.log N) * saving crecip Y := by
            ring)

/-- Unconditional large-prime-factor quantitative bound from the prime-main
exceptional estimate.

This discharges the reciprocal partial-summation envelope internally by the
checked dyadic-shell summation in `excPrimesIoc_recip_envelope_of_prime_main`. -/
theorem exceptionalGtY_quantitative_of_prime_main
    (hprime : IsMainBound primeExceptionalCount) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N Y : ℕ, 3 ≤ Y → Y ≤ N →
      (exceptionalGtYCount N Y : ℝ)
        ≤ C * (N : ℝ) * (1 + Real.log N) * saving c Y := by
  obtain ⟨crecip, hcrecip, Crecip, hCrecip, hrecip⟩ :=
    excPrimesIoc_recip_envelope_of_prime_main hprime
  exact exceptionalGtY_quantitative_of_prime_recip_envelope_prime_main
    hprime hCrecip hcrecip hrecip

/-- Unconditional large-prime-factor quantitative bound from the full exceptional
main estimate. -/
theorem exceptionalGtY_quantitative_of_main (hmain : IsMainBound exceptionalCount) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N Y : ℕ, 3 ≤ Y → Y ≤ N →
      (exceptionalGtYCount N Y : ℝ)
        ≤ C * (N : ℝ) * (1 + Real.log N) * saving c Y :=
  exceptionalGtY_quantitative_of_prime_main (prime_exceptional_of_main hmain)

/-- Power-threshold form of the large-prime-factor estimate.

This is the checked application-layer version of the manuscript's fixed-`η`
consequence: once `Y ≥ N^η`, the remaining logarithmic prefactor in the
large-prime-factor bound is absorbed into the exponential saving at level `N`. -/
theorem exceptionalGtY_power_threshold_of_main
    (hmain : IsMainBound exceptionalCount) {η : ℝ} (hη : 0 < η) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N Y : ℕ, 3 ≤ N → 3 ≤ Y → Y ≤ N →
      (N : ℝ) ^ η ≤ (Y : ℝ) →
      (exceptionalGtYCount N Y : ℝ) ≤ C * (N : ℝ) * saving c N := by
  obtain ⟨c₀, hc₀, C₀, hC₀, hlarge⟩ := exceptionalGtY_quantitative_of_main hmain
  set c₁ : ℝ := c₀ * η ^ ((3 : ℝ) / 4) with hc₁def
  have hc₁ : 0 < c₁ := by
    rw [hc₁def]
    exact mul_pos hc₀ (Real.rpow_pos_of_pos hη _)
  obtain ⟨c, hc, Clog, hClog, hlog⟩ := log_mul_saving_absorb hc₁
  refine ⟨c, hc, C₀ * ((5 : ℝ) / 2) * Clog, by positivity, ?_⟩
  intro N Y hN hY hYN hpower
  have hsav : saving c₀ Y ≤ saving c₁ N := by
    rw [hc₁def]
    exact saving_le_saving_of_power_lower hc₀ hη hN hpower
  have hlog_ge : (2 : ℝ) / 3 ≤ Real.log (N : ℝ) := log_ge_of_three_le hN
  have hone_add_log :
      1 + Real.log (N : ℝ) ≤ ((5 : ℝ) / 2) * Real.log (N : ℝ) := by
    nlinarith
  have hlarge' :
      (exceptionalGtYCount N Y : ℝ)
        ≤ C₀ * (N : ℝ) * (1 + Real.log N) * saving c₀ Y :=
    hlarge N Y hY hYN
  calc
    (exceptionalGtYCount N Y : ℝ)
        ≤ C₀ * (N : ℝ) * (1 + Real.log N) * saving c₀ Y := hlarge'
    _ ≤ C₀ * (N : ℝ) * (1 + Real.log N) * saving c₁ N := by
        apply mul_le_mul_of_nonneg_left hsav
        positivity
    _ ≤ C₀ * (N : ℝ) * (((5 : ℝ) / 2) * Real.log N) * saving c₁ N := by
        apply mul_le_mul_of_nonneg_right _ (by
          unfold saving
          exact (Real.exp_pos _).le)
        apply mul_le_mul_of_nonneg_left hone_add_log
        positivity
    _ = C₀ * ((5 : ℝ) / 2) * (N : ℝ) * (Real.log N * saving c₁ N) := by
        ring
    _ ≤ C₀ * ((5 : ℝ) / 2) * (N : ℝ) * (Clog * saving c N) := by
        apply mul_le_mul_of_nonneg_left (hlog N hN)
        positivity
    _ = (C₀ * ((5 : ℝ) / 2) * Clog) * (N : ℝ) * saving c N := by
        ring

/-- Exponential-threshold form of the large-prime-factor estimate.

This is the checked application-layer version of the manuscript's second
specialization: if `Y` is at least `exp((log N)^(3/4))`, the large-prime-factor
bound has `9/16` logarithmic saving after absorbing the remaining logarithmic
prefactor. -/
theorem exceptionalGtY_exp_log_threshold_of_main
    (hmain : IsMainBound exceptionalCount) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N Y : ℕ, 3 ≤ N → 3 ≤ Y → Y ≤ N →
      Real.exp ((Real.log (N : ℝ)) ^ ((3 : ℝ) / 4)) ≤ (Y : ℝ) →
      (exceptionalGtYCount N Y : ℝ) ≤ C * (N : ℝ) * savingNineSixteen c N := by
  obtain ⟨c₀, hc₀, C₀, hC₀, hlarge⟩ := exceptionalGtY_quantitative_of_main hmain
  obtain ⟨c, hc, Clog, hClog, hlog⟩ := log_mul_savingNineSixteen_absorb hc₀
  refine ⟨c, hc, C₀ * ((5 : ℝ) / 2) * Clog, by positivity, ?_⟩
  intro N Y hN hY hYN hYexp
  have hsav : saving c₀ Y ≤ savingNineSixteen c₀ N :=
    saving_le_savingNineSixteen_of_exp_log_three_fourths_lower hc₀ hN hYexp
  have hlog_ge : (2 : ℝ) / 3 ≤ Real.log (N : ℝ) := log_ge_of_three_le hN
  have hone_add_log :
      1 + Real.log (N : ℝ) ≤ ((5 : ℝ) / 2) * Real.log (N : ℝ) := by
    nlinarith
  have hlarge' :
      (exceptionalGtYCount N Y : ℝ)
        ≤ C₀ * (N : ℝ) * (1 + Real.log N) * saving c₀ Y :=
    hlarge N Y hY hYN
  calc
    (exceptionalGtYCount N Y : ℝ)
        ≤ C₀ * (N : ℝ) * (1 + Real.log N) * saving c₀ Y := hlarge'
    _ ≤ C₀ * (N : ℝ) * (1 + Real.log N) * savingNineSixteen c₀ N := by
        apply mul_le_mul_of_nonneg_left hsav
        positivity
    _ ≤ C₀ * (N : ℝ) * (((5 : ℝ) / 2) * Real.log N) *
          savingNineSixteen c₀ N := by
        apply mul_le_mul_of_nonneg_right _ (by
          unfold savingNineSixteen
          exact (Real.exp_pos _).le)
        apply mul_le_mul_of_nonneg_left hone_add_log
        positivity
    _ = C₀ * ((5 : ℝ) / 2) * (N : ℝ) *
          (Real.log N * savingNineSixteen c₀ N) := by
        ring
    _ ≤ C₀ * ((5 : ℝ) / 2) * (N : ℝ) * (Clog * savingNineSixteen c N) := by
        apply mul_le_mul_of_nonneg_left (hlog N hN)
        positivity
    _ = (C₀ * ((5 : ℝ) / 2) * Clog) * (N : ℝ) * savingNineSixteen c N := by
        ring

end EscAnalytic
