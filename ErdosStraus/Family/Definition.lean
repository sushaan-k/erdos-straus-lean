import Mathlib.Data.Nat.ChineseRemainder
import ErdosStraus.Congruences.Certificates
import ErdosStraus.Basic
import ErdosStraus.Estimates.Chebyshev
import ErdosStraus.Estimates.WeightedSums

/-!
# The selected family

The quadruples `i = (e, d₋, d₊, p)` of Section 6, with `Q_i = d₋ d₊ p` and `q_i = d₊ p`,
the index set `I_b` cut out by (12) and (14)–(16), and the events `n ≡ -m e (mod q_i)`.
A hit gives a representation of `m/n` (Lemma 2.3), two compatible members of `I_b` with the
same large prime coincide (Lemma 6.8), and the number of exceptions coprime to `P(z)` is at
most the sum over reduced classes `b` of the number of `n ≡ b (mod P(z))` hit by no event.
The prime-class counts `C_ℓ(S)` bound the class-count divisor sums of Lemma 6.9 by an Euler
product.
-/

namespace ErdosStraus.Family

open ErdosStraus
open scoped BigOperators

/-! ## The family index -/

/-- A family index `i = (e, d₋, d₊, p)`: an exact divisor `e = r s²` together with
the small divisor `d₋`, the rough cofactor `d₊` and the prime `p`.
The range and congruence conditions (12), (14)–(16) are imposed separately. -/
structure FamilyIndex where
  /-- The exact divisor `e = r s²`, with `ρ(e) = r s`. -/
  E : ErdosStraus.ExactDivisor
  /-- The small squarefree odd divisor `d₋ ∣ P(z)`. -/
  dminus : ℕ
  /-- The rough squarefree cofactor `d₊`, coprime to `P(z)`. -/
  dplus : ℕ
  /-- The prime `p` with `X^β < p ≤ X^{1-σ}`. -/
  p : ℕ

namespace FamilyIndex

variable (i : FamilyIndex)

/-- The exact divisor `e = r s²`. -/
def e : ℕ := i.E.e

/-- The radical `ρ(e) = rad(e) = r s`. -/
def rho : ℕ := i.E.rho

/-- The full modulus `Q = d₋ d₊ p`. -/
def Q : ℕ := i.dminus * i.dplus * i.p

/-- The residual modulus `q = d₊ p`. -/
def q : ℕ := i.dplus * i.p

/-- The event `(e, d₋, d₊, p)` attached to a family index. -/
def toSatEvent (i : FamilyIndex) : ErdosStraus.Arithmetic.SatEvent :=
  { e := i.e
    dMinus := i.dminus
    dPlus := i.dplus
    p := i.p }

end FamilyIndex

/-! ## Prime-class counts -/

/-- The residues `e_i mod ℓ` over the events `i ∈ S = old` with `ℓ ∣ d₊(i)`;
its cardinality is `C_ℓ(S)`. -/
noncomputable def familyOldPrimeResidueClasses
    (old : Finset ErdosStraus.Arithmetic.SatEvent) (ell : ℕ) : Finset ℕ :=
  (old.filter (fun event => ell ∣ event.dPlus)).image
    (fun event => event.e % ell)

/-- The multiplicative class count `∏_{ℓ ∣ D} C_ℓ(S)` for squarefree odd `D`,
and `0` otherwise. -/
noncomputable def familyIncrementClassProductRat
    (old : Finset ErdosStraus.Arithmetic.SatEvent) (D : ℕ) : ℚ :=
  if Squarefree D ∧ Odd D then
    ∏ ell ∈ D.primeFactors,
      ((familyOldPrimeResidueClasses old ell).card : ℚ)
  else 0

theorem congruenceLcm_dvd_moduli_product (rows : List (ℕ × ℕ)) :
    ErdosStraus.Arithmetic.congruenceLcm rows ∣ (rows.map Prod.fst).prod := by
  induction rows with
  | nil => simp [ErdosStraus.Arithmetic.congruenceLcm]
  | cons row rows ih =>
      simp only [ErdosStraus.Arithmetic.congruenceLcm, List.map_cons, List.prod_cons]
      apply Nat.lcm_dvd
      · exact dvd_mul_right row.1 _
      · exact ih.trans (dvd_mul_left _ row.1)

/-- `1 + ∑_{2 ≤ D ≤ B} (∏_{ℓ ∣ D} C_ℓ(S))/D ≤ ∏_{ℓ ≤ B} (1 + C_ℓ(S)/ℓ)`. -/
theorem familyIncrementClassProduct_sum_le_eulerProduct
    (old : Finset ErdosStraus.Arithmetic.SatEvent) (B : ℕ) (hB : 1 ≤ B) :
    1 + (∑ D ∈ Finset.Icc 2 B,
      familyIncrementClassProductRat old D / (D : ℚ)) ≤
      ∏ p ∈ ErdosStraus.Arithmetic.primeFinsetUpTo B,
        (1 + ((familyOldPrimeResidueClasses old p).card : ℚ) / (p : ℚ)) := by
  classical
  let a : ℕ → ℚ := fun p =>
    ((familyOldPrimeResidueClasses old p).card : ℚ) / (p : ℚ)
  have ha : ∀ p ∈ ErdosStraus.Arithmetic.primeFinsetUpTo B, 0 ≤ a p := by
    intro p hp
    unfold a
    positivity
  have hterm : ∀ D ∈ Finset.Icc 2 B,
      familyIncrementClassProductRat old D / (D : ℚ) ≤
        if Squarefree D then ∏ p ∈ D.primeFactors, a p else 0 := by
    intro D hD
    by_cases hsq : Squarefree D
    · rw [if_pos hsq]
      by_cases hodd : Odd D
      · rw [familyIncrementClassProductRat, if_pos ⟨hsq, hodd⟩]
        have hprodD := Nat.prod_primeFactors_of_squarefree hsq
        have hDcast : (D : ℚ) = ∏ p ∈ D.primeFactors, (p : ℚ) := by
          simpa using congrArg (fun n : ℕ => (n : ℚ)) hprodD.symm
        unfold a
        rw [hDcast, ← Finset.prod_div_distrib]
      · rw [familyIncrementClassProductRat, if_neg (by simp [hsq, hodd])]
        simp
        apply Finset.prod_nonneg
        intro p hp
        positivity
    · rw [if_neg hsq, familyIncrementClassProductRat,
        if_neg (by simp [hsq])]
      simp
  have hmajor :
      (∑ D ∈ Finset.Icc 2 B,
        familyIncrementClassProductRat old D / (D : ℚ)) ≤
      ∑ D ∈ (Finset.Icc 2 B).filter Squarefree,
        ∏ p ∈ D.primeFactors, a p := by
    calc
      (∑ D ∈ Finset.Icc 2 B,
          familyIncrementClassProductRat old D / (D : ℚ)) ≤
        ∑ D ∈ Finset.Icc 2 B,
          if Squarefree D then ∏ p ∈ D.primeFactors, a p else 0 := by
            apply Finset.sum_le_sum
            intro D hD
            exact hterm D hD
      _ = ∑ D ∈ (Finset.Icc 2 B).filter Squarefree,
          ∏ p ∈ D.primeFactors, a p := by
            rw [Finset.sum_filter]
  have hIcc : (Finset.Icc 1 B).filter Squarefree =
      insert 1 ((Finset.Icc 2 B).filter Squarefree) := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
    constructor
    · intro h
      by_cases hD1 : D = 1
      · exact Or.inl hD1
      · exact Or.inr ⟨⟨by omega, h.1.2⟩, h.2⟩
    · intro h
      rcases h with rfl | h
      · simp [hB]
      · exact ⟨⟨by omega, h.1.2⟩, h.2⟩
  have heuler := ErdosStraus.Arithmetic.squarefree_primeFactor_sum_le_eulerProduct
    B a ha
  calc
    1 + (∑ D ∈ Finset.Icc 2 B,
        familyIncrementClassProductRat old D / (D : ℚ)) ≤
      1 + ∑ D ∈ (Finset.Icc 2 B).filter Squarefree,
        ∏ p ∈ D.primeFactors, a p := add_le_add_right hmajor 1
    _ = ∑ D ∈ (Finset.Icc 1 B).filter Squarefree,
        ∏ p ∈ D.primeFactors, a p := by
      rw [hIcc, Finset.sum_insert]
      · simp [a]
      · simp
    _ ≤ ∏ p ∈ ErdosStraus.Arithmetic.primeFinsetUpTo B, (1 + a p) := heuler
    _ = ∏ p ∈ ErdosStraus.Arithmetic.primeFinsetUpTo B,
        (1 + ((familyOldPrimeResidueClasses old p).card : ℚ) / (p : ℚ)) := rfl

/-- `1 + ∑_{2 ≤ D ≤ B} (∏_{ℓ ∣ D} C_ℓ(S))/D ≤ exp(∑_{ℓ ≤ B} C_ℓ(S)/ℓ)`. -/
theorem familyIncrementClassProduct_real_sum_le_exp
    (old : Finset ErdosStraus.Arithmetic.SatEvent) (B : ℕ) (hB : 1 ≤ B) :
    (1 : ℝ) + (∑ D ∈ Finset.Icc 2 B,
      (familyIncrementClassProductRat old D : ℝ) / (D : ℝ)) ≤
      Real.exp (∑ p ∈ ErdosStraus.Arithmetic.primeFinsetUpTo B,
        ((familyOldPrimeResidueClasses old p).card : ℝ) / (p : ℝ)) := by
  have heulerQ := familyIncrementClassProduct_sum_le_eulerProduct old B hB
  have heulerR :
      (1 : ℝ) + (∑ D ∈ Finset.Icc 2 B,
        (familyIncrementClassProductRat old D : ℝ) / (D : ℝ)) ≤
        ∏ p ∈ ErdosStraus.Arithmetic.primeFinsetUpTo B,
          (1 + ((familyOldPrimeResidueClasses old p).card : ℝ) / (p : ℝ)) := by
    have hcast :
        (((1 + (∑ D ∈ Finset.Icc 2 B,
          familyIncrementClassProductRat old D / (D : ℚ))) : ℚ) : ℝ) ≤
        (((∏ p ∈ ErdosStraus.Arithmetic.primeFinsetUpTo B,
          (1 + ((familyOldPrimeResidueClasses old p).card : ℚ) / (p : ℚ))) : ℚ) : ℝ) := by
      exact_mod_cast heulerQ
    simpa using hcast
  calc
    (1 : ℝ) + (∑ D ∈ Finset.Icc 2 B,
        (familyIncrementClassProductRat old D : ℝ) / (D : ℝ)) ≤
      ∏ p ∈ ErdosStraus.Arithmetic.primeFinsetUpTo B,
        (1 + ((familyOldPrimeResidueClasses old p).card : ℝ) / (p : ℝ)) := heulerR
    _ ≤ ∏ p ∈ ErdosStraus.Arithmetic.primeFinsetUpTo B,
        Real.exp (((familyOldPrimeResidueClasses old p).card : ℝ) / (p : ℝ)) := by
      gcongr with p hp
      have h := Real.add_one_le_exp
        (((familyOldPrimeResidueClasses old p).card : ℝ) / (p : ℝ))
      linarith
    _ = Real.exp (∑ p ∈ ErdosStraus.Arithmetic.primeFinsetUpTo B,
        ((familyOldPrimeResidueClasses old p).card : ℝ) / (p : ℝ)) := by
      rw [Real.exp_sum]

/-- `C_p(S)` is at most the number of events in `S` with `p ∣ d₊`. -/
theorem familyOldPrimeResidueClasses_card_le_incidence
    (old : Finset ErdosStraus.Arithmetic.SatEvent) (p : ℕ) :
    (familyOldPrimeResidueClasses old p).card ≤
      (old.filter (fun event => p ∣ event.dPlus)).card := by
  classical
  unfold familyOldPrimeResidueClasses
  exact Finset.card_image_le

/-- Double counting of prime/event incidences:
`∑_{p ≤ B} #{i ∈ S : p ∣ d₊(i)}/p = ∑_{i ∈ S} ∑_{p ≤ B, p ∣ d₊(i)} 1/p`. -/
theorem familyOldPrimeIncidence_sum_eq_event_primeDivisor_sum
    (old : Finset ErdosStraus.Arithmetic.SatEvent) (B : ℕ) :
    (∑ p ∈ ErdosStraus.Arithmetic.primeFinsetUpTo B,
      ((old.filter (fun event => p ∣ event.dPlus)).card : ℝ) / (p : ℝ)) =
      ∑ event ∈ old,
        ∑ p ∈ (ErdosStraus.Arithmetic.primeFinsetUpTo B).filter
          (fun p => p ∣ event.dPlus), (1 : ℝ) / (p : ℝ) := by
  classical
  calc
    (∑ p ∈ ErdosStraus.Arithmetic.primeFinsetUpTo B,
        ((old.filter (fun event => p ∣ event.dPlus)).card : ℝ) / (p : ℝ)) =
      ∑ p ∈ ErdosStraus.Arithmetic.primeFinsetUpTo B,
        ∑ event ∈ old,
          if p ∣ event.dPlus then (1 : ℝ) / (p : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.card_eq_sum_ones]
      push_cast
      rw [Finset.sum_div]
      rw [Finset.sum_filter]
    _ = ∑ event ∈ old,
        ∑ p ∈ ErdosStraus.Arithmetic.primeFinsetUpTo B,
          if p ∣ event.dPlus then (1 : ℝ) / (p : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ event ∈ old,
        ∑ p ∈ (ErdosStraus.Arithmetic.primeFinsetUpTo B).filter
          (fun p => p ∣ event.dPlus), (1 : ℝ) / (p : ℝ) := by
      apply Finset.sum_congr rfl
      intro event hevent
      rw [Finset.sum_filter]

/-- `∑_{p ≤ B} C_p(S)/p ≤ ∑_{i ∈ S} ∑_{p ≤ B, p ∣ d₊(i)} 1/p`. -/
theorem familyOldPrimeClass_exponent_le_event_primeDivisor_sum
    (old : Finset ErdosStraus.Arithmetic.SatEvent) (B : ℕ) :
    (∑ p ∈ ErdosStraus.Arithmetic.primeFinsetUpTo B,
      ((familyOldPrimeResidueClasses old p).card : ℝ) / (p : ℝ)) ≤
      ∑ event ∈ old,
        ∑ p ∈ (ErdosStraus.Arithmetic.primeFinsetUpTo B).filter
          (fun p => p ∣ event.dPlus), (1 : ℝ) / (p : ℝ) := by
  rw [← familyOldPrimeIncidence_sum_eq_event_primeDivisor_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpPrime : Nat.Prime p :=
    (Finset.mem_filter.mp hp).2
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  apply div_le_div_of_nonneg_right _ hpPos.le
  exact_mod_cast familyOldPrimeResidueClasses_card_le_incidence old p

end ErdosStraus.Family

/-! ## The index set `I_b` and its events -/

namespace ErdosStraus.FixedNumeratorFamily

open Classical Family

/-- Membership of `i = (e, d₋, d₊, p)` in `I_b` for the class `b` modulo `Pz = P(z)`:
the conditions (12) and (14)–(16), together with `(ρ(e), m) = 1`. -/
structure StaticMem (m : ℕ) (P : Params) (X : ℝ) (Pz b : ℕ)
    (i : FamilyIndex) : Prop where
  s_pos : 1 ≤ i.E.s
  s_le_S : (i.E.s : ℝ) ≤ SScale P X
  r_gt : Y0Scale P X / (i.E.s : ℝ) < (i.E.r : ℝ)
  r_le : (i.E.r : ℝ) ≤ HScale P X / ((i.E.s : ℝ) ^ 2)
  dminus_pos : 0 < i.dminus
  dminus_le_U : (i.dminus : ℝ) ≤ UScale X
  dminus_dvd_Pz : i.dminus ∣ Pz
  dminus_squarefree : Squarefree i.dminus
  dminus_odd : Odd i.dminus
  base_cong : b + m * i.e ≡ 0 [MOD i.dminus]
  dplus_pos : 0 < i.dplus
  dplus_squarefree : Squarefree i.dplus
  dd_le_Y : (i.dminus * i.dplus : ℝ) ≤ YScale P X
  dplus_coprime_Pz : Nat.Coprime i.dplus Pz
  rho_coprime_m : Nat.Coprime i.rho m
  dd_coprime_mrho : Nat.Coprime (i.dminus * i.dplus) (m * i.rho)
  p_prime : Nat.Prime i.p
  p_gt : X ^ P.β < (i.p : ℝ)
  p_le : (i.p : ℝ) ≤ X ^ (1 - P.σ)
  sat_cong : m * i.rho ∣ i.Q + 1

/-- The index set `I_b`. -/
def indexSet (m : ℕ) (P : Params) (X : ℝ) (Pz b : ℕ) : Set FamilyIndex :=
  { i | StaticMem m P X Pz b i }

/-- `n` lies in the event of `i`: `n ≡ -m e (mod q_i)`. -/
def Hit (m n : ℕ) (i : FamilyIndex) : Prop := i.q ∣ n + m * i.e

/-- The event of `i` as a congruence `(q_i, -m e mod q_i)`. -/
def hitRow (m : ℕ) (i : FamilyIndex) : ℕ × ℕ :=
  (i.q, ErdosStraus.Arithmetic.negModResidue i.q (m * i.e))

theorem hit_iff_row {m n : ℕ} {i : FamilyIndex} (hq : 0 < i.q) :
    Hit m n i ↔ n ≡ (hitRow m i).2 [MOD (hitRow m i).1] :=
  (ErdosStraus.Arithmetic.modEq_negModResidue_iff_dvd_add n i.q (m * i.e) hq).symm

theorem compatible_same_prime_e_eq
    {m : ℕ} {i j : FamilyIndex} (hprime : i.p = j.p)
    (hcop : Nat.Coprime i.p m)
    (hcompat : ErdosStraus.Arithmetic.residueCompatible i.q j.q (m * i.e) (m * j.e))
    (hi : i.e < i.p) (hj : j.e < j.p) : i.e = j.e := by
  have hpi : i.p ∣ i.q := by simp [FamilyIndex.q]
  have hpj : i.p ∣ j.q := by simp [FamilyIndex.q, hprime]
  have hmod : m * i.e ≡ m * j.e [MOD i.p] :=
    hcompat.of_dvd (Nat.dvd_gcd hpi hpj)
  exact (Nat.ModEq.cancel_left_of_coprime hcop.gcd_eq_one hmod).eq_of_lt_of_lt
    hi (by simpa [hprime] using hj)

theorem StaticMem.dminus_coprime_residual
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (h : StaticMem m P X Pz b i) (hlt : i.dminus < i.p) :
    Nat.Coprime i.dminus i.q := by
  have hd : Nat.Coprime i.dminus i.dplus :=
    Nat.Coprime.coprime_dvd_left h.dminus_dvd_Pz h.dplus_coprime_Pz.symm
  have hp : Nat.Coprime i.dminus i.p :=
    ((h.p_prime.coprime_iff_not_dvd).2
      (Nat.not_dvd_of_pos_of_lt h.dminus_pos hlt)).symm
  exact hd.mul_right hp

theorem StaticMem.prime_coprime_numerator
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (h : StaticMem m P X Pz b i) : Nat.Coprime i.p m := by
  apply h.p_prime.coprime_iff_not_dvd.mpr
  intro hpm
  have hpQ : i.p ∣ i.Q := by simp [FamilyIndex.Q]
  have hpQ1 : i.p ∣ i.Q + 1 :=
    (dvd_mul_of_dvd_left hpm i.rho).trans h.sat_cong
  have hp1 : i.p ∣ 1 := (Nat.dvd_add_iff_right hpQ).mpr hpQ1
  exact h.p_prime.ne_one (Nat.dvd_one.mp hp1)

theorem StaticMem.dminus_lt_prime
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (h : StaticMem m P X Pz b i) (hU : UScale X < X ^ P.β) :
    i.dminus < i.p := by
  exact_mod_cast h.dminus_le_U.trans_lt (hU.trans h.p_gt)

theorem StaticMem.e_lt_prime
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (h : StaticMem m P X Pz b i) (hX : 1 < X) : i.e < i.p := by
  have hs : (0 : ℝ) < i.E.s := by exact_mod_cast h.s_pos
  have he : (i.e : ℝ) ≤ HScale P X := by
    have hprod := (le_div_iff₀ (pow_pos hs 2)).mp h.r_le
    simpa [FamilyIndex.e, ExactDivisor.e, Nat.cast_mul, Nat.cast_pow] using hprod
  have hH : HScale P X < X ^ P.β :=
    Real.rpow_lt_rpow_of_exponent_lt hX (by
      linarith [P.two_θ_lt_β, P.θ_pos])
  exact_mod_cast he.trans_lt (hH.trans h.p_gt)

theorem StaticMem.medium_lt_rho
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (h : StaticMem m P X Pz b i) (hX : 1 < X) :
    i.dminus * i.dplus < i.rho := by
  have hs : (0 : ℝ) < i.E.s := by exact_mod_cast h.s_pos
  have hrho : Y0Scale P X < (i.rho : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right h.r_gt hs
    rw [div_mul_cancel₀ _ hs.ne'] at hmul
    simpa [FamilyIndex.rho, ExactDivisor.rho, Nat.cast_mul] using hmul
  exact_mod_cast h.dd_le_Y.trans_lt ((YScale_lt_Y0Scale P hX).trans hrho)

theorem StaticMem.prime_coprime_mrho
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (h : StaticMem m P X Pz b i) : Nat.Coprime i.p (m * i.rho) := by
  apply h.p_prime.coprime_iff_not_dvd.mpr
  intro hpm
  have hpQ : i.p ∣ i.Q := by simp [FamilyIndex.Q]
  have hpQ1 : i.p ∣ i.Q + 1 := hpm.trans h.sat_cong
  have hp1 : i.p ∣ 1 := (Nat.dvd_add_iff_right hpQ).mpr hpQ1
  exact h.p_prime.ne_one (Nat.dvd_one.mp hp1)

/-- Lemma 6.8: two compatible members of `I_b` with the same large prime coincide.
The cancellation is modulo `m ρ(e)`. -/
theorem StaticMem.eq_of_compatible_same_prime
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ} {i j : FamilyIndex}
    (hm : 0 < m) (hX : 1 < X)
    (hi : StaticMem m P X Pz b i) (hj : StaticMem m P X Pz b j)
    (hprime : i.p = j.p)
    (hcompat : ErdosStraus.Arithmetic.residueCompatible i.q j.q (m * i.e) (m * j.e)) :
    i = j := by
  have he := compatible_same_prime_e_eq hprime hi.prime_coprime_numerator hcompat
    (hi.e_lt_prime hX) (hj.e_lt_prime hX)
  have hrho := ExactDivisor.rho_eq_of_e_eq i.E j.E he
  have hRho : i.rho = j.rho := hrho
  have hprog : (i.dminus * i.dplus) * i.p + 1 ≡ 0 [MOD m * i.rho] :=
    Nat.modEq_zero_iff_dvd.mpr hi.sat_cong
  have hprog' : (j.dminus * j.dplus) * i.p + 1 ≡ 0 [MOD m * i.rho] := by
    rw [hRho, hprime]
    exact Nat.modEq_zero_iff_dvd.mpr hj.sat_cong
  have hmul := Nat.ModEq.add_right_cancel' (c := 1) (hprog.trans hprog'.symm)
  have hmod := Nat.ModEq.cancel_right_of_coprime hi.prime_coprime_mrho.symm.gcd_eq_one hmul
  have hrhole : i.rho ≤ m * i.rho := Nat.le_mul_of_pos_left _ hm
  have hrholej : j.rho ≤ m * i.rho := by rw [← hRho]; exact hrhole
  have hmed := hmod.eq_of_lt_of_lt ((hi.medium_lt_rho hX).trans_le hrhole)
    ((hj.medium_lt_rho hX).trans_le hrholej)
  obtain ⟨hdm, hdp⟩ := ErdosStraus.Arithmetic.smallRough_split_unique
    Pz i.dminus i.dplus j.dminus j.dplus hi.dminus_pos hmed
    hi.dminus_dvd_Pz hj.dminus_dvd_Pz hi.dplus_coprime_Pz hj.dplus_coprime_Pz
  have hiRho : 0 < i.E.rho := lt_of_le_of_lt (Nat.zero_le _)
    (hi.medium_lt_rho hX)
  have hE := ExactDivisor.eq_of_e_eq_of_rho_pos i.E j.E he hiRho
  cases i
  cases j
  simp only at hprime hdm hdp
  cases hE
  cases hdm
  cases hdp
  cases hprime
  rfl

/-- A hit of a member of `I_b` gives a representation of `m/n` as a sum of three
positive unit fractions. -/
theorem StaticMem.hit_representable
    {m : ℕ} {P : Params} {X : ℝ} {Pz b n : ℕ} {i : FamilyIndex}
    (hm : 2 ≤ m) (h : StaticMem m P X Pz b i)
    (hU : UScale X < X ^ P.β) (hn : 0 < n)
    (hbase : n ≡ b [MOD Pz]) (hhit : Hit m n i) :
    fixedNumeratorRepresentable m n := by
  have hrho : 0 < i.rho := by
    by_contra hnpos
    have hz : i.rho = 0 := Nat.eq_zero_of_not_pos hnpos
    have hsat := h.sat_cong
    rw [hz, Nat.mul_zero] at hsat
    simp at hsat
  have hr : 0 < i.E.r := Nat.pos_of_mul_pos_right hrho
  have hs : 0 < i.E.s := Nat.pos_of_mul_pos_left hrho
  rcases ErdosStraus.Arithmetic.fixedFan_positive_unit_fractions_of_base_class
      m n Pz b i.dminus i.dplus i.p i.E.r i.E.s hm hn hr hs
      (h.dminus_coprime_residual (h.dminus_lt_prime hU)) h.dminus_dvd_Pz hbase
      h.base_cong (by simpa [FamilyIndex.Q, FamilyIndex.rho, ExactDivisor.rho, Nat.mul_assoc] using h.sat_cong)
      hhit with ⟨a, x, y, z, _ha, _hcenter, hx, hy, hz, hid⟩
  exact ⟨x, y, z, hx, hy, hz, hid⟩

theorem indexSet_finite
    (m : ℕ) (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 0 < X) :
    (indexSet m P X Pz b).Finite := by
  let rBound : ℕ := ⌊HScale P X⌋₊
  let sBound : ℕ := ⌊SScale P X⌋₊
  let dminusBound : ℕ := ⌊UScale X⌋₊
  let dplusBound : ℕ := ⌊YScale P X⌋₊
  let pBound : ℕ := ⌊X ^ (1 - P.σ)⌋₊
  let code : FamilyIndex → ℕ × ℕ × ℕ × ℕ × ℕ :=
    fun i => (i.E.r, i.E.s, i.dminus, i.dplus, i.p)
  let box : Set (ℕ × ℕ × ℕ × ℕ × ℕ) :=
    Set.Iic rBound ×ˢ Set.Iic sBound ×ˢ Set.Iic dminusBound ×ˢ
      Set.Iic dplusBound ×ˢ Set.Iic pBound
  have hbox_finite : box.Finite := by
    dsimp [box]
    exact (Set.finite_Iic rBound).prod
      ((Set.finite_Iic sBound).prod
        ((Set.finite_Iic dminusBound).prod
          ((Set.finite_Iic dplusBound).prod (Set.finite_Iic pBound))))
  have hcode_injective : Function.Injective code := by
    intro i j hij
    cases i with
    | mk Ei dmi dpi pi =>
      cases Ei with
      | mk ri si hri hsi hcopi =>
        cases j with
        | mk Ej dmj dpj pj =>
          cases Ej with
          | mk rj sj hrj hsj hcopj =>
            simp only [code] at hij
            injection hij with hr htail1
            injection htail1 with hs htail2
            injection htail2 with hdm htail3
            injection htail3 with hdp hp
            subst rj
            subst sj
            subst dmj
            subst dpj
            subst pj
            rfl
  have hpre_finite : (code ⁻¹' box).Finite :=
    hbox_finite.preimage (by
      intro i hi j hj hij
      exact hcode_injective hij)
  apply hpre_finite.subset
  intro i hi
  have hmem : StaticMem m P X Pz b i := by
    simpa [indexSet] using hi
  have hH_nonneg : 0 ≤ HScale P X := by
    exact Real.rpow_nonneg hX.le _
  have hs_real : (1 : ℝ) ≤ (i.E.s : ℝ) := by
    exact_mod_cast hmem.s_pos
  have hs_sq : (1 : ℝ) ≤ (i.E.s : ℝ) ^ 2 :=
    one_le_pow₀ hs_real
  have hr_real : (i.E.r : ℝ) ≤ HScale P X :=
    le_trans hmem.r_le (div_le_self hH_nonneg hs_sq)
  have hdm_real : (1 : ℝ) ≤ (i.dminus : ℝ) := by
    exact_mod_cast hmem.dminus_pos
  have hdp_nonneg : 0 ≤ (i.dplus : ℝ) := by positivity
  have hdp_le_prod : (i.dplus : ℝ) ≤ (i.dminus * i.dplus : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right hdm_real hdp_nonneg]
  have hdp_real : (i.dplus : ℝ) ≤ YScale P X :=
    le_trans hdp_le_prod hmem.dd_le_Y
  change code i ∈ box
  simp only [box, code, Set.mem_prod, Set.mem_Iic]
  exact ⟨Nat.le_floor hr_real, Nat.le_floor hmem.s_le_S,
    Nat.le_floor hmem.dminus_le_U, Nat.le_floor hdp_real,
    Nat.le_floor hmem.p_le⟩

/-- The finite index set `I_b` (empty when `X ≤ 0`). -/
noncomputable def indexFinset (m : ℕ) (P : Params) (X : ℝ) (Pz b : ℕ) :
    Finset FamilyIndex :=
  if hX : 0 < X then (indexSet_finite m P X Pz b hX).toFinset else ∅

theorem mem_indexFinset_iff
    (m : ℕ) (P : Params) (X : ℝ) (Pz b : ℕ) (i : FamilyIndex) (hX : 0 < X) :
    i ∈ indexFinset m P X Pz b ↔ StaticMem m P X Pz b i := by
  simp [indexFinset, hX, indexSet]

/-- The number of `1 ≤ n ≤ N` with `n % Pz = b` that lie in no event of `indices`. -/
noncomputable def rowNoHitCount (m N Pz b : ℕ) (indices : Finset FamilyIndex) : ℕ :=
  ((Finset.Icc 1 N).filter
    (fun n => n % Pz = b ∧ ∀ i ∈ indices, ¬ Hit m n i)).card

/-- The number of `1 ≤ n ≤ N` coprime to `Pz` for which `m/n` has no representation. -/
noncomputable def reducedExceptionalCount (m N Pz : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter
    (fun n => Nat.Coprime (n % Pz) Pz ∧ ¬ fixedNumeratorRepresentable m n)).card

/-- An exceptional `n` coprime to `Pz` lies in no event of `I_b` for its class
`b = n % Pz`, so the reduced exceptional count is at most the sum of the no-hit
counts over reduced classes. -/
theorem reducedExceptionalCount_le_noHitSum
    (m : ℕ) (hm : 2 ≤ m) (P : Params) (X : ℝ) (hX : 0 < X)
    (N Pz : ℕ) (hPz : 0 < Pz) (hU : UScale X < X ^ P.β) :
    reducedExceptionalCount m N Pz ≤
      ∑ b ∈ ErdosStraus.Arithmetic.reducedResiduesMod Pz,
        rowNoHitCount m N Pz b (indexFinset m P X Pz b) := by
  classical
  let E := (Finset.Icc 1 N).filter
    (fun n => Nat.Coprime (n % Pz) Pz ∧ ¬ fixedNumeratorRepresentable m n)
  have hmem : ∀ n ∈ E, n % Pz ∈ ErdosStraus.Arithmetic.reducedResiduesMod Pz := by
    intro n hn
    have hd := Finset.mem_filter.mp hn
    exact (ErdosStraus.Arithmetic.mem_reducedResiduesMod_iff Pz (n % Pz)).mpr
      ⟨Nat.mod_lt _ hPz, hd.2.1⟩
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun n => n % Pz) (s := E)
    (t := ErdosStraus.Arithmetic.reducedResiduesMod Pz) hmem
  change E.card ≤ _
  rw [hfib]
  apply Finset.sum_le_sum
  intro b _hb
  unfold rowNoHitCount
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hnE, hnb⟩ := Finset.mem_filter.mp hn
  obtain ⟨hnrange, _hcop, hex⟩ := Finset.mem_filter.mp hnE
  apply Finset.mem_filter.mpr
  refine ⟨hnrange, hnb, ?_⟩
  intro i hi hhit
  apply hex
  have hstatic := (mem_indexFinset_iff m P X Pz b i hX).mp hi
  have hbase : n ≡ b [MOD Pz] := by
    change n % Pz = b % Pz
    rw [← hnb, Nat.mod_mod]
  exact hstatic.hit_representable hm hU
    (Finset.mem_Icc.mp hnrange).1 hbase hhit

end ErdosStraus.FixedNumeratorFamily

/-! ## The moduli `q_i` -/

namespace ErdosStraus.FixedNumeratorLifting

open Classical Filter Family

theorem index_modulus_le (P : Params) {X : ℝ} (hX : 1 < X) {m b : ℕ}
    {i : FamilyIndex}
    (h : FixedNumeratorFamily.StaticMem m P X (Estimates.roughModulus X) b i) :
    (i.q : ℝ) ≤ X := by
  have hXpos := zero_lt_one.trans hX
  have hqQ : i.q ≤ i.Q := by
    simpa [FamilyIndex.q, FamilyIndex.Q, Nat.mul_assoc] using
      Nat.mul_le_mul_right i.p (Nat.le_mul_of_pos_left i.dplus h.dminus_pos)
  have hQ : (i.Q : ℝ) ≤ YScale P X * X ^ (1 - P.σ) := by
    simp only [FamilyIndex.Q, Nat.cast_mul]
    exact mul_le_mul h.dd_le_Y h.p_le (Nat.cast_nonneg _)
      (Real.rpow_nonneg hXpos.le _)
  apply (show (i.q : ℝ) ≤ i.Q by exact_mod_cast hqQ).trans (hQ.trans_eq ?_)
  change X ^ P.σ * X ^ (1 - P.σ) = X
  rw [← Real.rpow_add hXpos]
  norm_num

/-- For large `X`, every index of the family has `0 < q_i ≤ X` and `(P(z), q_i) = 1`. -/
theorem eventual_index_data (P : Params) :
    ∀ᶠ X : ℝ in atTop, 1 < X ∧
      ∀ m b : ℕ, ∀ i ∈ FixedNumeratorFamily.indexFinset m P X
        (Estimates.roughModulus X) b,
        0 < i.q ∧ (i.q : ℝ) ≤ X ∧ Nat.Coprime (Estimates.roughModulus X) i.q := by
  obtain ⟨X₀, hsep⟩ := FixedNumeratorFamily.scale_separation P
  filter_upwards [eventually_ge_atTop X₀] with X hX
  obtain ⟨hX1, _hU, hZ⟩ := hsep X hX
  refine ⟨hX1, ?_⟩
  intro m b i hi
  have hm := (FixedNumeratorFamily.mem_indexFinset_iff m P X _ b i
    (zero_lt_one.trans hX1)).mp hi
  have hpnot : ¬ i.p ∣ Estimates.roughModulus X := by
    intro hd
    have hpz := Estimates.prime_dvd_roughModulus_le_floor_zScale X hm.p_prime hd
    have hpr : (i.p : ℝ) ≤ (⌊zScale X⌋₊ : ℕ) := by exact_mod_cast hpz
    exact (not_lt_of_ge hpr) (hZ.trans hm.p_gt)
  exact ⟨Nat.mul_pos hm.dplus_pos hm.p_prime.pos, index_modulus_le P hX1 hm,
    hm.dplus_coprime_Pz.symm.mul_right
      ((hm.p_prime.coprime_iff_not_dvd.mpr hpnot).symm)⟩

end ErdosStraus.FixedNumeratorLifting
