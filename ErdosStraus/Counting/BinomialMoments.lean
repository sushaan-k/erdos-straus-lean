import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Int.CardIntervalMod
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
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AlmostPrime
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import ErdosStraus.Family.Scales

/-!
# Lemma 5.1: binomial moments of a family of congruences

For a finite family of congruences `n ≡ c_i (mod q_i)` put `L_S = lcm(q_i : i ∈ S)` and
`F_r = ∑ 1/L_S`, the sum over compatible sets `S` of size `r`. The deletion identity
`r F_r = ∑_{|S| = r-1} A(S)/L_S` gives `F_r ≤ M^r / r!` whenever `A(S) ≤ M` (Lemma 5.1).
The file also counts common solutions `n ≤ N` in one class `b (mod P)` (Lemma 5.3) and
proves the Bonferroni inequality with which the proof of Theorem 5.4 begins.
-/

namespace ErdosStraus.Estimates

/-! ## Congruence events -/

/-- A congruence event `n ≡ residue (mod modulus)`; the `tag` distinguishes events
with the same congruence. -/
structure ModularEvent where
  tag : ℕ × ℕ × ℕ × ℕ
  modulus : ℕ
  residue : ℕ
deriving DecidableEq

/-- `n` lies in the event: `n ≡ residue (mod modulus)`. -/
def ModularEvent.Hits (event : ModularEvent) (n : ℕ) : Prop :=
  n ≡ event.residue [MOD event.modulus]

instance (event : ModularEvent) (n : ℕ) : Decidable (event.Hits n) := by
  unfold ModularEvent.Hits
  infer_instance

/-- The proportion of `0 ≤ n < L` lying in none of the events. When `L` is a common
period of the moduli this is the probability `P(W = 0)` of Theorem 5.2. -/
noncomputable def modularNoHitProbability
    (L : ℕ) (events : Finset ModularEvent) : ℝ :=
  ((Finset.range L).filter (fun n => ∀ event ∈ events, ¬ event.Hits n)).card / L

/-- The probability `1/q` of an event with modulus `q`. -/
noncomputable def modularEventMass (event : ModularEvent) : ℝ :=
  1 / event.modulus

/-- Two events are dependent, `i ∼ j`, when they are distinct and their moduli are
not coprime. -/
def modularDependent (event other : ModularEvent) : Prop :=
  event ≠ other ∧ ¬ Nat.Coprime event.modulus other.modulus

instance (event other : ModularEvent) : Decidable (modularDependent event other) := by
  unfold modularDependent
  infer_instance

/-- The total mass `μ = ∑_i 1/q_i`. -/
noncomputable def modularMass (events : Finset ModularEvent) : ℝ :=
  ∑ event ∈ events, modularEventMass event

/-- The neighbourhood mass `∑_{j ∼ i} 1/q_j` of an event `i`. -/
noncomputable def modularNeighbourMass
    (events : Finset ModularEvent) (event : ModularEvent) : ℝ :=
  ∑ other ∈ events.filter (modularDependent event), modularEventMass other

/-- The largest neighbourhood mass `δ`, with `δ = 0` for the empty family. -/
noncomputable def modularDelta (events : Finset ModularEvent) : ℝ :=
  if h : events.Nonempty then
    events.sup' h (modularNeighbourMass events)
  else 0

theorem modularEventMass_nonneg (event : ModularEvent) :
    0 ≤ modularEventMass event := by
  unfold modularEventMass
  positivity

theorem modularNeighbourMass_le_delta
    (events : Finset ModularEvent) {event : ModularEvent}
    (hevent : event ∈ events) :
    modularNeighbourMass events event ≤ modularDelta events := by
  classical
  rw [modularDelta, dif_pos ⟨event, hevent⟩]
  exact Finset.le_sup' (modularNeighbourMass events) hevent

/-- The probability of `A_i ∩ A_j`: `1/lcm(q_i, q_j)` if `c_i ≡ c_j (mod (q_i, q_j))`,
and `0` otherwise. -/
noncomputable def modularPairMass (event other : ModularEvent) : ℝ :=
  if event.residue ≡ other.residue [MOD Nat.gcd event.modulus other.modulus] then
    1 / Nat.lcm event.modulus other.modulus
  else 0

/-- The sum of `P(A_i ∩ A_j)` over ordered dependent pairs `(i, j)`, which is `2Δ`. -/
noncomputable def modularDependencyMass (events : Finset ModularEvent) : ℝ :=
  ∑ event ∈ events,
    ∑ other ∈ events.filter (modularDependent event), modularPairMass event other

end ErdosStraus.Estimates

namespace ErdosStraus.ModularFamily

open Classical
open ErdosStraus.Arithmetic

/-! ## Compatible sets and the coefficients `F_r` -/

abbrev Event := Estimates.ModularEvent

/-- The congruence of an event as the pair `(q_i, c_i)`. -/
def row (i : Event) : ℕ × ℕ := (i.modulus, i.residue)

/-- The congruences of the events of `S`, as a list. -/
noncomputable def rows (S : Finset Event) : List (ℕ × ℕ) := S.toList.map row

/-- `L_S = lcm(q_i : i ∈ S)`, with `L_∅ = 1`. -/
noncomputable def period (S : Finset Event) : ℕ := congruenceLcm (rows S)

/-- `S` is compatible when `c_i ≡ c_j (mod (q_i, q_j))` for all `i, j ∈ S`. -/
def Compatible (S : Finset Event) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, residueCompatible i.modulus j.modulus i.residue j.residue

/-- The compatible subsets of `E` of size `r`. -/
noncomputable def subsets (E : Finset Event) (r : ℕ) : Finset (Finset Event) :=
  (E.powersetCard r).filter Compatible

/-- The events `i ∈ E` outside `S` for which `S ∪ {i}` is compatible. -/
noncomputable def extensions (E S : Finset Event) : Finset Event :=
  E.filter (fun i => i ∉ S ∧ Compatible (insert i S))

/-- The weight `1/L_S`. -/
noncomputable def weight (S : Finset Event) : ℚ := 1 / (period S : ℚ)

/-- `F_r = ∑ 1/L_S` over the compatible `S ⊆ E` with `|S| = r`. -/
noncomputable def coefficient (E : Finset Event) (r : ℕ) : ℚ :=
  ∑ S ∈ subsets E r, weight S

/-- `A(S) = ∑ (q_i, L_S)/q_i` over the events `i ∉ S` with `S ∪ {i}` compatible. -/
noncomputable def increment (E S : Finset Event) : ℚ :=
  ∑ i ∈ extensions E S, (1 : ℚ) / (i.modulus : ℚ) *
    (Nat.gcd (period S) i.modulus : ℚ)

theorem period_pos (E : Finset Event) (hpos : ∀ i ∈ E, 0 < i.modulus) :
    0 < period E := by
  apply congruenceLcm_pos_of_rows_positive
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
  exact hpos i (by simpa using hi)

theorem modulus_dvd_period {E : Finset Event} {i : Event} (hi : i ∈ E) :
    i.modulus ∣ period E :=
  congruenceRow_modulus_dvd_lcm (rows E) (row i)
    (List.mem_map.mpr ⟨i, by simpa using hi, rfl⟩)

theorem period_dvd_of_subset {S E : Finset Event} (hSE : S ⊆ E) :
    period S ∣ period E := by
  apply congruenceLcm_dvd_of_forall_modulus_dvd
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
  exact modulus_dvd_period (hSE (by simpa using hi))

theorem period_insert (S : Finset Event) (i : Event) :
    period (insert i S) = Nat.lcm i.modulus (period S) := by
  apply Nat.dvd_antisymm
  · apply congruenceLcm_dvd_of_forall_modulus_dvd
    intro r hr
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
    have hj' : j ∈ insert i S := by simpa using hj
    obtain rfl | hjS := Finset.mem_insert.mp hj'
    · exact Nat.dvd_lcm_left _ _
    · exact (modulus_dvd_period hjS).trans (Nat.dvd_lcm_right _ _)
  · apply Nat.lcm_dvd
    · exact modulus_dvd_period (Finset.mem_insert_self _ _)
    · exact period_dvd_of_subset (Finset.subset_insert _ _)

theorem rows_compatible_iff (S : Finset Event) :
    congruenceRowsPairwiseCompatible (rows S) ↔ Compatible S := by
  constructor
  · intro h i hi j hj
    exact h (row i) (List.mem_map.mpr ⟨i, by simpa using hi, rfl⟩)
      (row j) (List.mem_map.mpr ⟨j, by simpa using hj, rfl⟩)
  · intro h r hr t ht
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
    exact h i (by simpa using hi) j (by simpa using hj)

theorem rows_satisfied_iff (S : Finset Event) (n : ℕ) :
    satisfiesCongruenceRows n (rows S) ↔ ∀ i ∈ S, i.Hits n := by
  simp only [satisfiesCongruenceRows, rows, List.forall_mem_map,
    Finset.mem_toList, row, Estimates.ModularEvent.Hits]

theorem compatible_of_common_hit {S : Finset Event} {n : ℕ}
    (h : ∀ i ∈ S, i.Hits n) : Compatible S :=
  (rows_compatible_iff S).mp
    (congruenceRowsPairwiseCompatible_of_solution (rows S) n
      ((rows_satisfied_iff S n).mpr h))

theorem weight_nonneg (S : Finset Event) : 0 ≤ weight S := by
  unfold weight
  positivity

theorem coefficient_nonneg (E : Finset Event) (r : ℕ) : 0 ≤ coefficient E r :=
  Finset.sum_nonneg (fun S _hS => weight_nonneg S)

@[simp] theorem coefficient_zero (E : Finset Event) : coefficient E 0 = 1 := by
  have hC : Compatible ∅ := by intro i hi; simp at hi
  have hfilter : ({∅} : Finset (Finset Event)).filter Compatible = {∅} := by
    apply Finset.filter_eq_self.mpr
    intro S hS
    have hS0 : S = ∅ := Finset.mem_singleton.mp hS
    simpa [hS0] using hC
  unfold coefficient subsets
  rw [Finset.powersetCard_zero, hfilter]
  simp [weight, period, rows, congruenceLcm]

/-! ## The recurrence for `F_r` -/

theorem weight_insert_ratio (S : Finset Event) (i : Event)
    (hS : 0 < period S) (hi : 0 < i.modulus) :
    weight (insert i S) / weight S =
      (1 : ℚ) / (i.modulus : ℚ) * (Nat.gcd (period S) i.modulus : ℚ) := by
  have hid := brun_lcm_weight_identity (period S) i.modulus hS hi
  unfold weight
  rw [period_insert, Nat.lcm_comm, hid]
  have hSne : (period S : ℚ) ≠ 0 := by exact_mod_cast hS.ne'
  field_simp [hSne]

/-- Each compatible set of size `r` arises from `r` compatible sets of size `r - 1`
by adding one element. -/
theorem deletion_identity (E : Finset Event) (r : ℕ) (hr : 0 < r) :
    (r : ℚ) * coefficient E r =
      ∑ S ∈ subsets E (r - 1),
        ∑ i ∈ extensions E S, weight (insert i S) := by
  apply weighted_subset_deletion_sum E Compatible weight r hr
  intro T hT i hi j hj k hk
  exact hT j (Finset.mem_of_mem_erase hj) k (Finset.mem_of_mem_erase hk)

/-- The recurrence `r F_r = ∑_{|S| = r-1} A(S)/L_S`. -/
theorem increment_recurrence (E : Finset Event)
    (hpos : ∀ i ∈ E, 0 < i.modulus) (r : ℕ) (hr : 0 < r) :
    (r : ℚ) * coefficient E r =
      ∑ S ∈ subsets E (r - 1), weight S * increment E S := by
  rw [deletion_identity E r hr]
  apply Finset.sum_congr rfl
  intro S hS
  have hSE : S ⊆ E :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).1
  have hSp := period_pos S (fun i hi => hpos i (hSE hi))
  have hweight : weight S ≠ 0 := by unfold weight; positivity
  unfold increment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hiE := (Finset.mem_filter.mp hi).1
  rw [← weight_insert_ratio S i hSp (hpos i hiE)]
  field_simp [hweight]

/-- Lemma 5.1: if `A(S) ≤ M` for every compatible `S ⊆ E` with `|S| < k`, then
`F_r ≤ M^r / r!` for all `r ≤ k`. -/
theorem coefficient_factorial_bound (E : Finset Event)
    (hpos : ∀ i ∈ E, 0 < i.modulus) (M : ℝ) (hM : 0 ≤ M) (k : ℕ)
    (hext : ∀ S ∈ E.powerset, Compatible S → S.card < k →
      (increment E S : ℝ) ≤ M) :
    ∀ r : ℕ, r ≤ k → (coefficient E r : ℝ) ≤ M ^ r / (r.factorial : ℝ) := by
  intro r hr
  induction r with
  | zero => simp
  | succ r ih =>
    have hrec := increment_recurrence E hpos (r + 1) (by omega)
    have hrecR : ((r + 1 : ℕ) : ℝ) * (coefficient E (r + 1) : ℝ) =
        ∑ S ∈ subsets E r, (weight S : ℝ) * (increment E S : ℝ) := by
      exact_mod_cast hrec
    have hbound : ((r + 1 : ℕ) : ℝ) * (coefficient E (r + 1) : ℝ) ≤
        M * (coefficient E r : ℝ) := by
      rw [hrecR, coefficient, Rat.cast_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro S hS
      obtain ⟨hpow, hcompat⟩ := Finset.mem_filter.mp hS
      obtain ⟨hSE, hcard⟩ := Finset.mem_powersetCard.mp hpow
      have hinc := hext S (Finset.mem_powerset.mpr hSE) hcompat (by omega)
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hinc
        (by exact_mod_cast weight_nonneg S : (0 : ℝ) ≤ weight S)
    have hstep : ((r + 1 : ℕ) : ℝ) * (coefficient E (r + 1) : ℝ) ≤
        M * (M ^ r / (r.factorial : ℝ)) :=
      hbound.trans (mul_le_mul_of_nonneg_left (ih (by omega)) hM)
    have hrp : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < ((r + 1).factorial : ℝ))]
    have hfac : (((r + 1).factorial : ℕ) : ℝ) = ((r + 1 : ℕ) : ℝ) * (r.factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
    rw [hfac, pow_succ]
    have hfpos : (0 : ℝ) < (r.factorial : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hstep hfpos.le
    field_simp [hfpos.ne'] at hmul
    push_cast at hmul ⊢
    nlinarith [hmul]

/-! ## Counting in one residue class -/

theorem base_coprime_period (S : Finset Event) {P : ℕ} (hP : 0 < P)
    (hpos : ∀ i ∈ S, 0 < i.modulus) (hcop : ∀ i ∈ S, Nat.Coprime P i.modulus) :
    Nat.Coprime P (period S) := by
  apply congruenceLcm_coprime_of_rows_coprime P (rows S) hP
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact hpos i (by simpa using hi)
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact hcop i (by simpa using hi)

theorem exists_base_solution (S : Finset Event) {P b : ℕ} (hP : 0 < P)
    (hpos : ∀ i ∈ S, 0 < i.modulus) (hcop : ∀ i ∈ S, Nat.Coprime P i.modulus)
    (hcompat : Compatible S) :
    ∃ n, n ≡ b [MOD P] ∧ ∀ i ∈ S, i.Hits n := by
  have hrows : congruenceRowsPairwiseCompatible ((P, b) :: rows S) := by
    intro a ha c hc
    obtain rfl | ha := List.mem_cons.mp ha
    · obtain rfl | hc := List.mem_cons.mp hc
      · exact Nat.ModEq.refl _
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
        unfold residueCompatible
        change b ≡ i.residue [MOD Nat.gcd P i.modulus]
        rw [(hcop i (by simpa using hi)).gcd_eq_one]
        exact Nat.modEq_one
    · obtain rfl | hc := List.mem_cons.mp hc
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
        unfold residueCompatible
        change i.residue ≡ b [MOD Nat.gcd i.modulus P]
        rw [(hcop i (by simpa using hi)).symm.gcd_eq_one]
        exact Nat.modEq_one
      · exact (rows_compatible_iff S).mpr hcompat a ha c hc
  obtain ⟨n, hn⟩ := baseResidualRows_solution_exists_of_pairwiseCompatible
    P b (rows S) hP (by
      intro r hr
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
      exact hpos i (by simpa using hi)) hrows
  exact ⟨n, hn.1, (rows_satisfied_iff S n).mp hn.2⟩

/-- The number of `n ≤ N` with `n ≡ b (mod P)` lying in every event of `S`. -/
noncomputable def baseCommonCount (N P b : ℕ) (S : Finset Event) : ℕ :=
  eventSubsetCommonHitCount
    ((Finset.range (N + 1)).filter (fun n => n ≡ b [MOD P]))
    (fun n i => i.Hits n) S

/-- The number of `n ≤ N` with `n ≡ b (mod P)` lying in no event of `E`. -/
noncomputable def baseNoHitCount (N P b : ℕ) (E : Finset Event) : ℕ :=
  (((Finset.range (N + 1)).filter (fun n => n ≡ b [MOD P])).filter
    (fun n => ∀ i ∈ E, ¬ i.Hits n)).card

theorem baseCommonCount_eq_residueCount (N P b n : ℕ) (S : Finset Event)
    (hcop : Nat.Coprime P (period S)) (hnbase : n ≡ b [MOD P])
    (hn : ∀ i ∈ S, i.Hits n) :
    baseCommonCount N P b S = residueClassCountUpTo N (P * period S) n := by
  have hcount : baseCommonCount N P b S = baseResidualRowsCountUpTo N P b (rows S) := by
    unfold baseCommonCount eventSubsetCommonHitCount baseResidualRowsCountUpTo
    rw [Finset.filter_filter]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro k hk
    exact and_congr_right (fun _ => (rows_satisfied_iff S k).symm)
  rw [hcount]
  exact baseResidualRowsCountUpTo_eq_residueClassCountUpTo
    N P b n (rows S) hcop hnbase ((rows_satisfied_iff S n).mpr hn)

/-- For compatible `S` with moduli coprime to `P`, the common solutions form one class
modulo `P L_S`, so their number differs from `N/(P L_S)` by at most `1`. -/
theorem baseCommonCount_bounds (N P b : ℕ) (S : Finset Event) (hP : 0 < P)
    (hpos : ∀ i ∈ S, 0 < i.modulus) (hcop : ∀ i ∈ S, Nat.Coprime P i.modulus)
    (hcompat : Compatible S) :
    (N : ℚ) / (P : ℚ) * weight S - 1 ≤ (baseCommonCount N P b S : ℚ) ∧
      (baseCommonCount N P b S : ℚ) ≤ (N : ℚ) / (P : ℚ) * weight S + 1 := by
  obtain ⟨n, hnb, hn⟩ := exists_base_solution S hP hpos hcop hcompat
  rw [baseCommonCount_eq_residueCount N P b n S
    (base_coprime_period S hP hpos hcop) hnb hn]
  have hp := Nat.mul_pos hP (period_pos S hpos)
  have hlow := div_sub_one_le_residueClassCountUpTo_cast N (P * period S) n hp
  have hupp := residueClassCountUpTo_cast_le_div_add_one N (P * period S) n hp
  have hupp' : (residueClassCountUpTo N (P * period S) n : ℚ) ≤
      (N : ℚ) / (P * period S : ℕ) + 1 :=
    hupp.trans (add_le_add_left (Nat.cast_div_le (α := ℚ)) _)
  have heq : (N : ℚ) / (P * period S : ℕ) = (N : ℚ) / (P : ℚ) * weight S := by
    simp only [Nat.cast_mul, weight]
    ring
  rw [heq] at hlow hupp'
  exact ⟨hlow, hupp'⟩

theorem baseCommonCount_zero_of_incompatible (N P b : ℕ) (S : Finset Event)
    (hnot : ¬ Compatible S) : baseCommonCount N P b S = 0 := by
  unfold baseCommonCount eventSubsetCommonHitCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n hn hall
  exact hnot (compatible_of_common_hit hall)

theorem period_le_pow (S : Finset Event) (B : ℕ)
    (hpos : ∀ i ∈ S, 0 < i.modulus) (hB : ∀ i ∈ S, i.modulus ≤ B) :
    period S ≤ B ^ S.card := by
  have hdiv : period S ∣ ∏ i ∈ S, i.modulus := by
    simpa [period, rows, row, List.map_map, Function.comp_def] using
      Family.congruenceLcm_dvd_moduli_product (rows S)
  exact (Nat.le_of_dvd (Finset.prod_pos hpos) hdiv).trans (by
    calc
      ∏ i ∈ S, i.modulus ≤ ∏ _i ∈ S, B := Finset.prod_le_prod' hB
      _ = B ^ S.card := by simp)

theorem one_le_pow_weight (S : Finset Event) (B : ℕ)
    (hpos : ∀ i ∈ S, 0 < i.modulus) (hB : ∀ i ∈ S, i.modulus ≤ B) :
    (1 : ℚ) ≤ (B : ℚ) ^ S.card * weight S := by
  have hp : (0 : ℚ) < (period S : ℚ) := by exact_mod_cast period_pos S hpos
  unfold weight
  rw [mul_one_div, le_div_iff₀ hp, one_mul]
  exact_mod_cast period_le_pow S B hpos hB

/-! ## The counting decomposition -/

/-- `C_r(N)`: the sum of `baseCommonCount N P b S` over the `S ⊆ E` with `|S| = r`. -/
noncomputable def rankCount (N P b : ℕ) (E : Finset Event) (r : ℕ) : ℕ :=
  ∑ S ∈ E.powersetCard r, baseCommonCount N P b S

theorem rankCount_eq_compatible (N P b : ℕ) (E : Finset Event) (r : ℕ) :
    rankCount N P b E r = ∑ S ∈ subsets E r, baseCommonCount N P b S := by
  unfold rankCount subsets
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hC : Compatible S
  · simp [hC]
  · simp [hC, baseCommonCount_zero_of_incompatible N P b S hC]

/-- Bonferroni: the number of `n` in no event is at most `∑_{r ≤ 2R} (-1)^r C_r(N)`. -/
theorem baseNoHitCount_le_prefix (N P b R : ℕ) (E : Finset Event) :
    (baseNoHitCount N P b E : ℚ) ≤
      ∑ r ∈ Finset.range (2 * R + 1), (-1 : ℚ) ^ r * rankCount N P b E r := by
  have hzero : ∀ n, hitEventCount E (fun i => i.Hits n) = 0 ↔
      ∀ i ∈ E, ¬ i.Hits n := by
    intro n
    simp only [hitEventCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  have h := hitEventSubsets_bonferroni_lower_double_count
    ((Finset.range (N + 1)).filter (fun n => n ≡ b [MOD P])) E
    (fun n i => i.Hits n) R
  have hleft : (∑ n ∈ ((Finset.range (N + 1)).filter (fun n => n ≡ b [MOD P])),
      if hitEventCount E (fun i => i.Hits n) = 0 then (1 : ℤ) else 0) =
      (baseNoHitCount N P b E : ℤ) := by
    simp only [Finset.sum_boole, hzero, baseNoHitCount]
  rw [hleft] at h
  exact_mod_cast h

/-- Lemma 5.3 in signed form: `(-1)^r C_r(N) ≤ (N/P) (-1)^r F_r + B^r F_r`. -/
theorem signed_rank_bound (N P b B r : ℕ) (E : Finset Event) (hP : 0 < P)
    (hpos : ∀ i ∈ E, 0 < i.modulus) (hcop : ∀ i ∈ E, Nat.Coprime P i.modulus)
    (hB : ∀ i ∈ E, i.modulus ≤ B) :
    (-1 : ℚ) ^ r * rankCount N P b E r ≤
      (N : ℚ) / P * ((-1 : ℚ) ^ r * coefficient E r) +
        (B : ℚ) ^ r * coefficient E r := by
  rw [rankCount_eq_compatible, Nat.cast_sum, coefficient]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro S hS
  obtain ⟨hpow, hcompat⟩ := Finset.mem_filter.mp hS
  obtain ⟨hSE, hcard⟩ := Finset.mem_powersetCard.mp hpow
  have hspos := fun i hi => hpos i (hSE hi)
  have hsB := fun i hi => hB i (hSE hi)
  obtain ⟨hlo, hup⟩ := baseCommonCount_bounds N P b S hP hspos
    (fun i hi => hcop i (hSE hi)) hcompat
  have hone : (1 : ℚ) ≤ (B : ℚ) ^ r * weight S := by
    simpa [hcard] using one_le_pow_weight S B hspos hsB
  obtain heven | hodd := Nat.even_or_odd r
  · rw [heven.neg_one_pow]
    nlinarith [hup, hone]
  · rw [hodd.neg_one_pow]
    nlinarith [hlo, hone]

theorem finite_prefix_bound (N P b B R : ℕ) (E : Finset Event) (hP : 0 < P)
    (hpos : ∀ i ∈ E, 0 < i.modulus) (hcop : ∀ i ∈ E, Nat.Coprime P i.modulus)
    (hB : ∀ i ∈ E, i.modulus ≤ B) :
    (baseNoHitCount N P b E : ℚ) ≤
      (N : ℚ) / P * (∑ r ∈ Finset.range (2 * R + 1), (-1 : ℚ) ^ r * coefficient E r) +
        ∑ r ∈ Finset.range (2 * R + 1), (B : ℚ) ^ r * coefficient E r := by
  apply (baseNoHitCount_le_prefix N P b R E).trans
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun r _hr => signed_rank_bound N P b B r E hP hpos hcop hB)

theorem subset_common_period_count (E S : Finset Event)
    (hpos : ∀ i ∈ E, 0 < i.modulus) (hSE : S ⊆ E) (hcompat : Compatible S) :
    eventSubsetCommonHitCount (Finset.range (period E)) (fun n i => i.Hits n) S =
      period E / period S := by
  have hspos := fun i hi => hpos i (hSE hi)
  have hrowspos : congruenceRowsModuliPositive (rows S) := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact hspos i (by simpa using hi)
  obtain ⟨n, hn⟩ := congruenceRows_solution_exists_of_pairwiseCompatible
    (rows S) hrowspos ((rows_compatible_iff S).mpr hcompat)
  have heq : eventSubsetCommonHitCount (Finset.range (period E))
      (fun n i => i.Hits n) S =
      Nat.count (fun k => k ≡ n [MOD period S]) (period E) := by
    unfold eventSubsetCommonHitCount
    rw [Nat.count_eq_card_filter_range]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro k hk
    exact (rows_satisfied_iff S k).symm.trans
      (congruenceRows_solution_iff_modEq_lcm (rows S) n k hn)
  rw [heq, modEq_count_complete_multiple (period E) (period S) n
    (period_pos S hspos) (period_dvd_of_subset hSE)]

/-- The analogue of `C_r` over one period `0 ≤ n < L_E`. -/
noncomputable def periodRankCount (E : Finset Event) (r : ℕ) : ℕ :=
  ∑ S ∈ E.powersetCard r,
    eventSubsetCommonHitCount (Finset.range (period E)) (fun n i => i.Hits n) S

/-- Over one period, `periodRankCount E r / L_E = F_r`; that is, `F_r = 𝔼 binom(W, r)`. -/
theorem periodRankDensity (E : Finset Event) (hpos : ∀ i ∈ E, 0 < i.modulus) (r : ℕ) :
    (periodRankCount E r : ℝ) / period E = (coefficient E r : ℝ) := by
  have hzero : ∀ S, ¬ Compatible S → eventSubsetCommonHitCount
      (Finset.range (period E)) (fun n i => i.Hits n) S = 0 := by
    intro S hS
    unfold eventSubsetCommonHitCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro n hn hall
    exact hS (compatible_of_common_hit hall)
  have heq : periodRankCount E r =
      ∑ S ∈ subsets E r, eventSubsetCommonHitCount (Finset.range (period E))
        (fun n i => i.Hits n) S := by
    unfold periodRankCount subsets
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S hS
    by_cases hC : Compatible S
    · simp [hC]
    · simp [hC, hzero S hC]
  rw [heq, coefficient, Rat.cast_sum, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro S hS
  obtain ⟨hpow, hcompat⟩ := Finset.mem_filter.mp hS
  have hSE := (Finset.mem_powersetCard.mp hpow).1
  have hspos := period_pos S (fun i hi => hpos i (hSE hi))
  have hepos := period_pos E hpos
  rw [subset_common_period_count E S hpos hSE hcompat,
    Nat.cast_div (period_dvd_of_subset hSE) (by positivity : (period S : ℝ) ≠ 0)]
  unfold weight
  push_cast
  field_simp [Nat.cast_ne_zero.mpr hspos.ne', Nat.cast_ne_zero.mpr hepos.ne']

/-- Bonferroni in the model over one period:
`∑_{r ≤ 2R} (-1)^r F_r ≤ P(W = 0) + F_{2R}`. -/
theorem prefix_le_probability_add_top (E : Finset Event)
    (hpos : ∀ i ∈ E, 0 < i.modulus) (R : ℕ) :
    (∑ r ∈ Finset.range (2 * R + 1), (-1 : ℝ) ^ r * (coefficient E r : ℝ)) ≤
      Estimates.modularNoHitProbability (period E) E + (coefficient E (2 * R) : ℝ) := by
  have hzero : ∀ n, hitEventCount E (fun i => i.Hits n) = 0 ↔
      ∀ i ∈ E, ¬ i.Hits n := by
    intro n
    simp only [hitEventCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  have hu := hitEventSubsets_bonferroni_upper_double_count (Finset.range (period E)) E
    (fun n i => i.Hits n) R
  rw [hitEventSubsets_alternating_double_count] at hu
  have hu' : (∑ r ∈ Finset.range (2 * R + 1), (-1 : ℤ) ^ r *
      (periodRankCount E r : ℤ)) ≤
      (((Finset.range (period E)).filter (fun n => ∀ i ∈ E, ¬ i.Hits n)).card : ℤ) +
        (periodRankCount E (2 * R) : ℤ) := by
    simpa only [periodRankCount, Finset.sum_boole, hzero, Nat.cast_sum] using hu
  have huR := (Int.cast_le (R := ℝ)).mpr hu'
  have hdiv := div_le_div_of_nonneg_right huR
    (show (0 : ℝ) ≤ period E by positivity)
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast, Int.cast_add, Finset.sum_div, mul_div_assoc, add_div] at hdiv
  simp_rw [periodRankDensity E hpos] at hdiv
  exact hdiv

/-- The first inequality in the proof of Theorem 5.4: the number of `n ≤ N` with
`n ≡ b (mod P)` lying in no event is at most
`(N/P)(P(W = 0) + F_{2R}) + ∑_{r ≤ 2R} B^r F_r`. -/
theorem finite_transfer_decomposition (N P b B R : ℕ) (E : Finset Event) (hP : 0 < P)
    (hpos : ∀ i ∈ E, 0 < i.modulus) (hcop : ∀ i ∈ E, Nat.Coprime P i.modulus)
    (hB : ∀ i ∈ E, i.modulus ≤ B) :
    (baseNoHitCount N P b E : ℝ) ≤ (N : ℝ) / P *
      (Estimates.modularNoHitProbability (period E) E + (coefficient E (2 * R) : ℝ)) +
      ∑ r ∈ Finset.range (2 * R + 1), (B : ℝ) ^ r * (coefficient E r : ℝ) := by
  have hfinite := finite_prefix_bound N P b B R E hP hpos hcop hB
  have hfiniteR : (baseNoHitCount N P b E : ℝ) ≤ (N : ℝ) / P *
      (∑ r ∈ Finset.range (2 * R + 1), (-1 : ℝ) ^ r * (coefficient E r : ℝ)) +
      ∑ r ∈ Finset.range (2 * R + 1), (B : ℝ) ^ r * (coefficient E r : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hfinite
    push_cast at hc
    exact hc
  apply hfiniteR.trans
  exact add_le_add_left (mul_le_mul_of_nonneg_left
    (prefix_le_probability_add_top E hpos R) (by positivity)) _

end ErdosStraus.ModularFamily
