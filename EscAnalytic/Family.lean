import EscAnalytic.Core
import EscLeanChecks
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Tactic

/-!
# The conductor-separated certificate family

This module defines the family used in the central sieve construction of
`esc.tex`.

We bundle the quadruple `i = (e, d₋, d₊, p)` of `(eq:rs-range)`,
`(eq:dminus-dplus)`, `(eq:dplus-conditions)`, `(eq:p-condition-sat)` into a
`FamilyIndex`, define the derived data
```
  Q = d₋·d₊·p,   q = d₊·p,   a = (Q+1)/4,   w = 1/q
```
(tex lines 738–751), and encode the family-membership predicate `FamilyMem`
relative to `Params`, the scale `X`, and a fixed base class `b`.

The MAIN derivation of this file is `familyHit_esRepresentable`
(tex lines 752–764, "Thus every such hit is a valid certificate by Cref{lem:fan}"):
from the family conditions — the congruence
`d₋d₊p ≡ -1 (mod 4ρ(e))` (which makes `a` integral and forces `ρ(e) ∣ a`,
hence `e ∣ a²` by `EscAnalytic.ExactDivisor.e_dvd_sq_of_rho_dvd`, with
`Q = 4a-1`) together with the conditional residue congruence
`n ≡ -4e (mod Q)` — we conclude `EscLeanChecks.esRepresentable n` by reducing to
the divisor-fan certificate `EscLeanChecks.divisorFan_nat_certificate`.

This is the paper's deduction from `lem:fan`, proved directly in Lean.

Imports are restricted to modules present in the local Mathlib cache plus the two
already-built local modules `EscAnalytic.Core` and `EscLeanChecks`.
-/

namespace EscAnalytic.Family

open EscAnalytic
open scoped BigOperators

/-! ## The family index `i = (e, d₋, d₊, p)`. -/

/-- A family index `i = (e, d₋, d₊, p)`: an exact divisor `e = r s²` together with
the small medium part `d₋`, the rough cofactor `d₊`, and the prime `p`
(tex lines 716–737, `eq:dminus-dplus`, `eq:dplus-conditions`, `eq:p-condition-sat`).
The membership ranges are carried separately by `FamilyMem`. -/
structure FamilyIndex where
  /-- The linearized exact divisor `e = r s²`, `ρ(e) = r s`. -/
  E : EscAnalytic.ExactDivisor
  /-- The small squarefree odd divisor `d₋ ∣ P(z)`. -/
  dminus : ℕ
  /-- The rough squarefree cofactor `d₊`, coprime to `P(z)`. -/
  dplus : ℕ
  /-- The prime `p` with `X^β < p ≤ X^{1-σ}`. -/
  p : ℕ

namespace FamilyIndex

variable (i : FamilyIndex)

/-- The exact divisor `e = r s²` (tex line 695). -/
def e : ℕ := i.E.e

/-- The reduced conductor `ρ(e) = r s` (tex line 697). -/
def rho : ℕ := i.E.rho

/-- The composite modulus `Q = d₋ d₊ p` (tex line 740). -/
def Q : ℕ := i.dminus * i.dplus * i.p

/-- The conditional modulus `q = d₊ p` (tex line 741). -/
def q : ℕ := i.dplus * i.p

/-- The fan center `a = (Q+1)/4` (tex line 746). -/
def a : ℕ := (i.Q + 1) / 4

/-- The reciprocal weight `w = 1/q` (tex line 750). -/
noncomputable def w : ℝ := (1 : ℝ) / (i.q : ℝ)

/-- Rational form of the same reciprocal weight, used by the exact finite
Bonferroni and elementary-symmetric layers. -/
noncomputable def wRat : ℚ := (1 : ℚ) / (i.q : ℚ)

@[simp] theorem e_eq : i.e = i.E.r * i.E.s ^ 2 := rfl
@[simp] theorem rho_eq : i.rho = i.E.r * i.E.s := rfl
@[simp] theorem Q_eq : i.Q = i.dminus * i.dplus * i.p := rfl
@[simp] theorem q_eq : i.q = i.dplus * i.p := rfl

@[simp] theorem wRat_cast_eq_w : (i.wRat : ℝ) = i.w := by
  simp [wRat, w]

/-- The residual event associated with a paper family index. -/
def toSatEvent (i : FamilyIndex) : EscLeanChecks.SatEvent :=
  { e := i.e
    dMinus := i.dminus
    dPlus := i.dplus
    p := i.p }

@[simp] theorem toSatEvent_e : i.toSatEvent.e = i.e := rfl
@[simp] theorem toSatEvent_dMinus : i.toSatEvent.dMinus = i.dminus := rfl
@[simp] theorem toSatEvent_dPlus : i.toSatEvent.dPlus = i.dplus := rfl
@[simp] theorem toSatEvent_p : i.toSatEvent.p = i.p := rfl

end FamilyIndex

/-! ## Membership in the conductor-separated certificate family. -/

/-- The membership predicate `i ∈ 𝓘_b` for the conductor-separated certificate
family at scale `X` with base class `b ∈ (ℤ/P(z)ℤ)ˣ` (tex lines 692–764).

This bundles, faithfully to the manuscript:

* `(eq:rs-range)` (tex lines 700–704): `1 ≤ s ≤ S`, `Y₀/s < r ≤ H/s²`;
* `(eq:dminus-dplus)` (tex lines 718–724): `d₋ ≤ U`, `d₋ ∣ P(z)`,
  `b ≡ -4e (mod d₋)` — here encoded through the derived conditional congruence;
* `(eq:dplus-conditions)` (tex lines 725–731): `d₋ d₊ ≤ Y`, `(d₊, P(z)) = 1`,
  `(d₋ d₊, 4ρ(e)) = 1`;
* `(eq:p-condition-sat)` (tex lines 732–737): `X^β < p ≤ X^{1-σ}`, `p` prime,
  and the certificate congruence `d₋ d₊ p ≡ -1 (mod 4 ρ(e))`.

The real-power range bounds are stated via `Nat.cast` into `ℝ` using the scales
of `EscAnalytic.Core`. `Pz` is the radical `P(z) = ∏_{ℓ ≤ z} ℓ` passed as a
parameter (the prime product is built elsewhere). Classical logic makes the
predicate usable as a `Prop`/`Set` membership condition. -/
structure FamilyMem (P : Params) (X : ℝ) (Pz b n : ℕ) (i : FamilyIndex) : Prop where
  -- eq:rs-range (tex 700–704)
  s_pos : 1 ≤ i.E.s
  s_le_S : (i.E.s : ℝ) ≤ SScale P X
  r_gt : Y0Scale P X / (i.E.s : ℝ) < (i.E.r : ℝ)
  r_le : (i.E.r : ℝ) ≤ HScale P X / ((i.E.s : ℝ) ^ 2)
  -- eq:dminus-dplus (tex 718–724)
  dminus_pos : 0 < i.dminus
  dminus_le_U : (i.dminus : ℝ) ≤ UScale X
  dminus_dvd_Pz : i.dminus ∣ Pz
  dminus_squarefree : Squarefree i.dminus
  dminus_odd : Odd i.dminus
  -- eq:dplus-conditions (tex 725–731)
  dplus_pos : 0 < i.dplus
  dplus_squarefree : Squarefree i.dplus
  dd_le_Y : (i.dminus * i.dplus : ℝ) ≤ YScale P X
  dplus_coprime_Pz : Nat.Coprime i.dplus Pz
  dd_coprime_four_rho : Nat.Coprime (i.dminus * i.dplus) (4 * i.rho)
  -- eq:p-condition-sat (tex 732–737)
  p_prime : Nat.Prime i.p
  p_gt : X ^ P.β < (i.p : ℝ)
  p_le : (i.p : ℝ) ≤ X ^ (1 - P.σ)
  /-- The certificate congruence `d₋ d₊ p ≡ -1 (mod 4 ρ(e))` (tex line 736):
  `4 ρ(e) ∣ Q + 1`. -/
  sat_cong : 4 * i.rho ∣ i.Q + 1
  /-- The conditional residue congruence `n ≡ -4e (mod Q)` (tex lines 752–760):
  combining the base class `n ≡ b ≡ -4e (mod d₋)` with the family-hit congruence
  `n ≡ -4e (mod d₊p)` and `(d₋, d₊p) = 1`, every integer in the conditional class
  and in `𝒜ᵢ^(b)` satisfies `n ≡ -4e (mod Q)`, i.e. `Q ∣ n + 4e`. -/
  cond_cong : i.Q ∣ n + 4 * i.e
  -- positivity of `n` (so that `4/n` makes sense)
  n_pos : 0 < n

/-- Static membership in the paper's family `I_b`.

Unlike `FamilyMem`, this records only conditions that define an event before a
point `n` is tested against it.  In particular, it includes the base-class
compatibility `b = -4e (mod dminus)` and has no hit congruence. -/
structure FamilyStaticMem (P : Params) (X : ℝ) (Pz b : ℕ)
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
  base_cong : b + 4 * i.e ≡ 0 [MOD i.dminus]
  dplus_pos : 0 < i.dplus
  dplus_squarefree : Squarefree i.dplus
  dd_le_Y : (i.dminus * i.dplus : ℝ) ≤ YScale P X
  dplus_coprime_Pz : Nat.Coprime i.dplus Pz
  dd_coprime_four_rho : Nat.Coprime (i.dminus * i.dplus) (4 * i.rho)
  p_prime : Nat.Prime i.p
  p_gt : X ^ P.β < (i.p : ℝ)
  p_le : (i.p : ℝ) ≤ X ^ (1 - P.σ)
  sat_cong : 4 * i.rho ∣ i.Q + 1

/-- The finite residual-event family attached to any finite set of paper
indices.  Repeated indices with the same residual data are removed by `image`. -/
noncomputable def familyEvents (indices : Finset FamilyIndex) :
    Finset EscLeanChecks.SatEvent :=
  indices.image FamilyIndex.toSatEvent

/-- Exact reciprocal weight attached to a residual event. -/
noncomputable def familyEventWeightRat (event : EscLeanChecks.SatEvent) : ℚ :=
  (1 : ℚ) /
    (EscLeanChecks.conditionalModulus event.dPlus event.p : ℚ)

@[simp] theorem familyEventWeightRat_toSatEvent (i : FamilyIndex) :
    familyEventWeightRat i.toSatEvent = i.wRat := by
  rfl

/-- Rational mass of the paper indices before passing to residual events. -/
noncomputable def familyIndexMassRat (indices : Finset FamilyIndex) : ℚ :=
  ∑ i ∈ indices, i.wRat

/-- Rational mass of the residual-event image. -/
noncomputable def familyEventMassRat (indices : Finset FamilyIndex) : ℚ :=
  ∑ event ∈ familyEvents indices, familyEventWeightRat event

/-- Total family weight in one residue class of the event parameter `e`
modulo `D`, restricted by `D ∣ dplus`; this is the exact finite
`B^{(b)}_{D,c}` carrier from `prop:event-tensor`. -/
noncomputable def familyResidueMassRat
    (indices : Finset FamilyIndex) (D c : ℕ) : ℚ :=
  ∑ event ∈ (familyEvents indices).filter
      (fun event => D ∣ event.dPlus ∧ event.e % D = c),
    familyEventWeightRat event

/-- Concrete list of event weights consumed by the finite
elementary-symmetric coefficient model. -/
noncomputable def familyEventWeightsRat (indices : Finset FamilyIndex) : List ℚ :=
  (familyEvents indices).toList.map familyEventWeightRat

theorem familyEventWeightRat_nonneg (event : EscLeanChecks.SatEvent) :
    0 ≤ familyEventWeightRat event := by
  unfold familyEventWeightRat
  positivity

theorem familyEventWeightsRat_nonneg (indices : Finset FamilyIndex) :
    ∀ w ∈ familyEventWeightsRat indices, 0 ≤ w := by
  intro w hw
  rcases List.mem_map.mp hw with ⟨event, _hevent, rfl⟩
  exact familyEventWeightRat_nonneg event

theorem familyEventWeightRat_pos_of_mem
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    {event : EscLeanChecks.SatEvent}
    (hevent : event ∈ familyEvents indices) :
    0 < familyEventWeightRat event := by
  rw [familyEvents] at hevent
  rcases Finset.mem_image.mp hevent with ⟨i, hi, rfl⟩
  unfold familyEventWeightRat EscLeanChecks.conditionalModulus
  have hq : 0 < i.dplus * i.p :=
    Nat.mul_pos (hmem i hi).dplus_pos (hmem i hi).p_prime.pos
  have hqRat : 0 < ((i.dplus * i.p : ℕ) : ℚ) := by
    exact_mod_cast hq
  exact one_div_pos.mpr hqRat

theorem familyEventWeightsRat_pos_of_static
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i) :
    ∀ w ∈ familyEventWeightsRat indices, 0 < w := by
  intro w hw
  rcases List.mem_map.mp hw with ⟨event, hevent, rfl⟩
  apply familyEventWeightRat_pos_of_mem P X Pz b indices hmem
  simpa using hevent

@[simp] theorem familyEventWeightsRat_sum_eq (indices : Finset FamilyIndex) :
    (familyEventWeightsRat indices).sum = familyEventMassRat indices := by
  classical
  simp [familyEventWeightsRat, familyEventMassRat]

/-- The recursive list model for elementary symmetric coefficients agrees with
the standard multiset elementary symmetric polynomial. -/
theorem elemSymmList_eq_multiset_esymm (xs : List ℚ) (r : ℕ) :
    EscLeanChecks.elemSymmList xs r = (↑xs : Multiset ℚ).esymm r := by
  induction xs generalizing r with
  | nil =>
      cases r <;> simp [EscLeanChecks.elemSymmList, Multiset.esymm]
  | cons x xs ih =>
      cases r with
      | zero =>
          simp [EscLeanChecks.elemSymmList, Multiset.esymm]
      | succ r =>
          rw [EscLeanChecks.elemSymmList_cons_succ, ih (r + 1), ih r]
          change (↑xs : Multiset ℚ).esymm (r + 1) +
              x * (↑xs : Multiset ℚ).esymm r =
            (x ::ₘ (↑xs : Multiset ℚ)).esymm (r + 1)
          unfold Multiset.esymm
          rw [Multiset.powersetCard_cons]
          simp [Multiset.sum_add, Multiset.map_add, Multiset.prod_cons,
            mul_comm, mul_left_comm, mul_assoc]
          exact Multiset.sum_map_mul_left.symm

/-- The elementary symmetric coefficient of the actual event-weight list is
exactly the sum of products over rank-`r` subsets of the paper family. -/
theorem familyEventWeightsRat_elemSymm_eq_powersetCard_sum
    (indices : Finset FamilyIndex) (r : ℕ) :
    EscLeanChecks.elemSymmList (familyEventWeightsRat indices) r =
      ∑ events ∈ (familyEvents indices).powersetCard r,
        ∏ event ∈ events, familyEventWeightRat event := by
  rw [elemSymmList_eq_multiset_esymm]
  change
    (Multiset.map familyEventWeightRat
      (↑(familyEvents indices).toList : Multiset _)).esymm r = _
  rw [Finset.coe_toList]
  exact Finset.esymm_map_val familyEventWeightRat (familyEvents indices) r

/-- Rank-`r` compatible event subsets in the sense used to define the
manuscript's truncated-sieve coefficient `F_r`. -/
noncomputable def familyCompatibleSubsetsOfCard
    (indices : Finset FamilyIndex) (r : ℕ) :
    Finset (Finset EscLeanChecks.SatEvent) := by
  classical
  exact ((familyEvents indices).powersetCard r).filter fun events =>
    ∀ event ∈ events, ∀ other ∈ events,
      event ≠ other → EscLeanChecks.satEventCompatible event other

/-- Exact rational realization of the manuscript's `F_r`: the reciprocal-lcm
mass of compatible rank-`r` subsets of the actual event family. -/
noncomputable def familyCompatibleLcmMassRat
    (indices : Finset FamilyIndex) (r : ℕ) : ℚ :=
  ∑ events ∈ familyCompatibleSubsetsOfCard indices r,
    (1 : ℚ) /
      (EscLeanChecks.congruenceLcm
        (EscLeanChecks.satEventResidualHitRows events.toList) : ℚ)

/-- Events which can be appended to a compatible old set while remaining in
the paper family and preserving pairwise compatibility. -/
noncomputable def familyCompatibleExtensions
    (indices : Finset FamilyIndex) (old : Finset EscLeanChecks.SatEvent) :
    Finset EscLeanChecks.SatEvent := by
  classical
  exact (familyEvents indices).filter fun event =>
    event ∉ old ∧
      ∀ x ∈ insert event old, ∀ y ∈ insert event old,
        x ≠ y → EscLeanChecks.satEventCompatible x y

/-- Exact deletion double count for the manuscript's reciprocal-lcm
coefficients.  This is the combinatorial equality underlying `r F_r`: every
compatible rank-`r` set is obtained once for each choice of the deleted event. -/
theorem familyCompatibleLcmMassRat_deletion_identity
    (indices : Finset FamilyIndex) (r : ℕ) (hr : 0 < r) :
    (r : ℚ) * familyCompatibleLcmMassRat indices r =
      ∑ old ∈ familyCompatibleSubsetsOfCard indices (r - 1),
        ∑ event ∈ familyCompatibleExtensions indices old,
          (1 : ℚ) /
            (EscLeanChecks.congruenceLcm
              (EscLeanChecks.satEventResidualHitRows
                (insert event old).toList) : ℚ) := by
  classical
  let compatible : Finset EscLeanChecks.SatEvent → Prop := fun events =>
    ∀ event ∈ events, ∀ other ∈ events,
      event ≠ other → EscLeanChecks.satEventCompatible event other
  have herase : ∀ T, compatible T → ∀ i ∈ T, compatible (T.erase i) := by
    intro T hT i hi event hevent other hother hne
    exact hT event (Finset.mem_of_mem_erase hevent) other
      (Finset.mem_of_mem_erase hother) hne
  simpa [familyCompatibleLcmMassRat, familyCompatibleSubsetsOfCard,
    familyCompatibleExtensions, compatible] using
    (EscLeanChecks.weighted_subset_deletion_sum
      (familyEvents indices) compatible
      (fun events => (1 : ℚ) /
        (EscLeanChecks.congruenceLcm
          (EscLeanChecks.satEventResidualHitRows events.toList) : ℚ))
      r hr herase)

/-- Reciprocal-lcm weight of one finite event set. -/
noncomputable def familySubsetLcmRecipRat
    (events : Finset EscLeanChecks.SatEvent) : ℚ :=
  (1 : ℚ) /
    (EscLeanChecks.congruenceLcm
      (EscLeanChecks.satEventResidualHitRows events.toList) : ℚ)

/-- Exact multiplicative increment in reciprocal-lcm weight when extending an
old compatible set.  Its gcd/weight realization is proved separately below. -/
noncomputable def familyIncrementRatioRat
    (indices : Finset FamilyIndex) (old : Finset EscLeanChecks.SatEvent) : ℚ :=
  ∑ event ∈ familyCompatibleExtensions indices old,
    familySubsetLcmRecipRat (insert event old) /
      familySubsetLcmRecipRat old

/-- The overlap factor `g(i;S) = gcd(L_S,q_i)` on the concrete event carrier. -/
noncomputable def familyIncrementG
    (old : Finset EscLeanChecks.SatEvent)
    (event : EscLeanChecks.SatEvent) : ℕ :=
  Nat.gcd
    (EscLeanChecks.congruenceLcm
      (EscLeanChecks.satEventResidualHitRows old.toList))
    (EscLeanChecks.conditionalModulus event.dPlus event.p)

/-- Manuscript increment quantity `A(S)`: each compatible extension contributes
its true event weight `1/q_i` multiplied by `g(i;S) = gcd(q_i,L_S)`. -/
noncomputable def familyIncrementRat
    (indices : Finset FamilyIndex) (old : Finset EscLeanChecks.SatEvent) : ℚ :=
  ∑ event ∈ familyCompatibleExtensions indices old,
    familyEventWeightRat event *
      (familyIncrementG old event : ℚ)

/-- Extensions restricted by `D | g(i;S)`. -/
noncomputable def familyIncrementDivisorEvents
    (indices : Finset FamilyIndex) (old : Finset EscLeanChecks.SatEvent)
    (D : ℕ) : Finset EscLeanChecks.SatEvent :=
  (familyCompatibleExtensions indices old).filter
    (fun event => D ∣ familyIncrementG old event)

/-- Extension mass restricted by `D | g(i;S)`, the exact finite carrier to
which the event-tensor residue-class estimate is applied in `lem:increment`. -/
noncomputable def familyIncrementDivisorMassRat
    (indices : Finset FamilyIndex) (old : Finset EscLeanChecks.SatEvent)
    (D : ℕ) : ℚ :=
  ∑ event ∈ familyIncrementDivisorEvents indices old D,
    familyEventWeightRat event

/-- Residue classes modulo `D` actually represented by divisor-restricted
compatible extensions. -/
noncomputable def familyIncrementResidueClasses
    (indices : Finset FamilyIndex) (old : Finset EscLeanChecks.SatEvent)
    (D : ℕ) : Finset ℕ :=
  (familyIncrementDivisorEvents indices old D).image
    (fun event => event.e % D)

/-- Residue classes modulo a medium prime represented by old events whose
medium factor is divisible by that prime; its cardinality is `C_ell(S)`. -/
noncomputable def familyOldPrimeResidueClasses
    (old : Finset EscLeanChecks.SatEvent) (ell : ℕ) : Finset ℕ :=
  (old.filter (fun event => ell ∣ event.dPlus)).image
    (fun event => event.e % ell)

/-- Multiplicative class count used in the squarefree Euler tail, with the
actual squarefree/odd support retained explicitly. -/
noncomputable def familyIncrementClassProductRat
    (old : Finset EscLeanChecks.SatEvent) (D : ℕ) : ℚ :=
  if Squarefree D ∧ Odd D then
    ∏ ell ∈ D.primeFactors,
      ((familyOldPrimeResidueClasses old ell).card : ℚ)
  else 0

/-- Weight in one realized residue class modulo `D`. -/
noncomputable def familyIncrementResidueMassRat
    (indices : Finset FamilyIndex) (old : Finset EscLeanChecks.SatEvent)
    (D c : ℕ) : ℚ :=
  ∑ event ∈ (familyIncrementDivisorEvents indices old D).filter
      (fun event => event.e % D = c),
    familyEventWeightRat event

/-- The `D=1` contribution to the increment expansion. -/
noncomputable def familyIncrementBaseMassRat
    (indices : Finset FamilyIndex) (old : Finset EscLeanChecks.SatEvent) : ℚ :=
  ∑ event ∈ familyCompatibleExtensions indices old,
    familyEventWeightRat event

/-- The finite `D>1` contribution in the totient-divisor expansion of `A(S)`. -/
noncomputable def familyIncrementTailRat
    (indices : Finset FamilyIndex) (old : Finset EscLeanChecks.SatEvent)
    (B : ℕ) : ℚ :=
  ∑ D ∈ Finset.Icc 2 B, (Nat.totient D : ℚ) *
    familyIncrementDivisorMassRat indices old D

/-- The exact extension ratio is the manuscript factor `w_i g(i;S)`. -/
theorem familyExtensionRatio_eq_weight_mul_gcd
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ familyEvents indices)
    (event : EscLeanChecks.SatEvent)
    (hevent : event ∈ familyEvents indices) :
    familySubsetLcmRecipRat (insert event old) /
        familySubsetLcmRecipRat old =
      familyEventWeightRat event *
        (familyIncrementG old event : ℚ) := by
  have hLpos : 0 < EscLeanChecks.congruenceLcm
      (EscLeanChecks.satEventResidualHitRows old.toList) := by
    apply EscLeanChecks.congruenceLcm_pos_of_rows_positive
    intro row hrow
    rcases List.mem_map.mp hrow with ⟨other, hother, rfl⟩
    rcases Finset.mem_image.mp (hsub (by simpa using hother)) with
      ⟨i, hi, rfl⟩
    exact Nat.mul_pos (hmem i hi).dplus_pos (hmem i hi).p_prime.pos
  have hqpos : 0 < EscLeanChecks.conditionalModulus event.dPlus event.p := by
    rcases Finset.mem_image.mp hevent with ⟨i, hi, rfl⟩
    exact Nat.mul_pos (hmem i hi).dplus_pos (hmem i hi).p_prime.pos
  have hid := EscLeanChecks.brun_lcm_weight_identity
    (EscLeanChecks.congruenceLcm
      (EscLeanChecks.satEventResidualHitRows old.toList))
    (EscLeanChecks.conditionalModulus event.dPlus event.p) hLpos hqpos
  unfold familySubsetLcmRecipRat familyEventWeightRat
  unfold familyIncrementG
  rw [EscLeanChecks.congruenceLcm_satEventResidualHitRows_insert_eq_lcm,
    Nat.lcm_comm, hid]
  have hLne : (EscLeanChecks.congruenceLcm
      (EscLeanChecks.satEventResidualHitRows old.toList) : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hLpos)
  field_simp [hLne]
  ring

/-- The ratio-defined increment and the paper's `w_i g(i;S)` increment agree
term by term. -/
theorem familyIncrementRatioRat_eq_incrementRat
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ familyEvents indices) :
    familyIncrementRatioRat indices old =
      familyIncrementRat indices old := by
  classical
  unfold familyIncrementRatioRat familyIncrementRat
  apply Finset.sum_congr rfl
  intro event hext
  apply familyExtensionRatio_eq_weight_mul_gcd
    P X Pz b indices hmem old hsub
  rw [familyCompatibleExtensions] at hext
  exact (Finset.mem_filter.mp hext).1

/-- Exact factored recurrence for the actual paper coefficient.  Positivity of
the old reciprocal-lcm weight follows from static family membership, so every
extension term factors without a zero-denominator exception. -/
theorem familyCompatibleLcmMassRat_ratio_recurrence
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (r : ℕ) (hr : 0 < r) :
    (r : ℚ) * familyCompatibleLcmMassRat indices r =
      ∑ old ∈ familyCompatibleSubsetsOfCard indices (r - 1),
        familySubsetLcmRecipRat old *
          familyIncrementRatioRat indices old := by
  classical
  rw [familyCompatibleLcmMassRat_deletion_identity indices r hr]
  apply Finset.sum_congr rfl
  intro old hold
  rw [familyCompatibleSubsetsOfCard] at hold
  have hpowerset : old ∈ (familyEvents indices).powersetCard (r - 1) :=
    Finset.mem_of_mem_filter old hold
  have hsub : old ⊆ familyEvents indices :=
    (Finset.mem_powersetCard.mp hpowerset).1
  have hLpos : 0 < EscLeanChecks.congruenceLcm
      (EscLeanChecks.satEventResidualHitRows old.toList) := by
    apply EscLeanChecks.congruenceLcm_pos_of_rows_positive
    intro row hrow
    rcases List.mem_map.mp hrow with ⟨event, hevent, rfl⟩
    rcases Finset.mem_image.mp (hsub (by simpa using hevent)) with
      ⟨i, hi, rfl⟩
    exact Nat.mul_pos (hmem i hi).dplus_pos (hmem i hi).p_prime.pos
  have hfoldPos : 0 < familySubsetLcmRecipRat old := by
    unfold familySubsetLcmRecipRat
    positivity
  have hfoldNe : familySubsetLcmRecipRat old ≠ 0 := ne_of_gt hfoldPos
  rw [familyIncrementRatioRat, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro event hevent
  change familySubsetLcmRecipRat (insert event old) =
    familySubsetLcmRecipRat old *
      (familySubsetLcmRecipRat (insert event old) /
        familySubsetLcmRecipRat old)
  field_simp [hfoldNe]

/-- Exact recurrence stated with the manuscript's one-step increment
`A(S) = \sum_i w_i gcd(L_S,q_i)`. -/
theorem familyCompatibleLcmMassRat_increment_recurrence
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (r : ℕ) (hr : 0 < r) :
    (r : ℚ) * familyCompatibleLcmMassRat indices r =
      ∑ old ∈ familyCompatibleSubsetsOfCard indices (r - 1),
        familySubsetLcmRecipRat old *
          familyIncrementRat indices old := by
  classical
  rw [familyCompatibleLcmMassRat_ratio_recurrence
    P X Pz b indices hmem r hr]
  apply Finset.sum_congr rfl
  intro old hold
  rw [familyCompatibleSubsetsOfCard] at hold
  have hsub : old ⊆ familyEvents indices :=
    (Finset.mem_powersetCard.mp (Finset.mem_of_mem_filter old hold)).1
  rw [familyIncrementRatioRat_eq_incrementRat
    P X Pz b indices hmem old hsub]

@[simp] theorem familyCompatibleLcmMassRat_zero
    (indices : Finset FamilyIndex) :
    familyCompatibleLcmMassRat indices 0 = 1 := by
  classical
  have hzero : familyCompatibleSubsetsOfCard indices 0 = {∅} := by
    ext events
    rw [familyCompatibleSubsetsOfCard]
    simp only [Finset.mem_filter, Finset.mem_powersetCard,
      Finset.mem_singleton]
    constructor
    · intro h
      exact Finset.card_eq_zero.mp h.1.2
    · intro h
      subst events
      simp
  rw [familyCompatibleLcmMassRat, hzero]
  simp [EscLeanChecks.congruenceLcm,
    EscLeanChecks.satEventResidualHitRows]

/-- The exact ratio recurrence implies the manuscript's multiplicative Brun
recurrence as soon as the compatible extension increment is uniformly bounded. -/
theorem familyCompatibleLcmMassRat_recurrence_le_of_incrementRatio_le
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (M : ℚ) (r : ℕ)
    (hinc : ∀ old ∈ familyCompatibleSubsetsOfCard indices (r - 1),
      familyIncrementRatioRat indices old ≤ M)
    (hr : 0 < r) :
    (r : ℚ) * familyCompatibleLcmMassRat indices r ≤
      M * familyCompatibleLcmMassRat indices (r - 1) := by
  rw [familyCompatibleLcmMassRat_ratio_recurrence
    P X Pz b indices hmem r hr]
  calc
    (∑ old ∈ familyCompatibleSubsetsOfCard indices (r - 1),
        familySubsetLcmRecipRat old *
          familyIncrementRatioRat indices old) ≤
      ∑ old ∈ familyCompatibleSubsetsOfCard indices (r - 1),
        familySubsetLcmRecipRat old * M := by
      apply Finset.sum_le_sum
      intro old hold
      apply mul_le_mul_of_nonneg_left (hinc old hold)
      unfold familySubsetLcmRecipRat
      positivity
    _ = M * familyCompatibleLcmMassRat indices (r - 1) := by
      rw [← Finset.sum_mul]
      simp [familyCompatibleLcmMassRat, familyCompatibleSubsetsOfCard,
        familySubsetLcmRecipRat, mul_comm]

/-- The paper's uniform increment estimate `A(S) ≤ M` gives its Brun
recurrence for the actual reciprocal-lcm coefficients. -/
theorem familyCompatibleLcmMassRat_recurrence_le_of_increment_le
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (M : ℚ) (r : ℕ)
    (hinc : ∀ old ∈ familyCompatibleSubsetsOfCard indices (r - 1),
      familyIncrementRat indices old ≤ M)
    (hr : 0 < r) :
    (r : ℚ) * familyCompatibleLcmMassRat indices r ≤
      M * familyCompatibleLcmMassRat indices (r - 1) := by
  classical
  rw [familyCompatibleLcmMassRat_increment_recurrence
    P X Pz b indices hmem r hr]
  calc
    (∑ old ∈ familyCompatibleSubsetsOfCard indices (r - 1),
        familySubsetLcmRecipRat old *
          familyIncrementRat indices old) ≤
      ∑ old ∈ familyCompatibleSubsetsOfCard indices (r - 1),
        familySubsetLcmRecipRat old * M := by
      apply Finset.sum_le_sum
      intro old hold
      apply mul_le_mul_of_nonneg_left (hinc old hold)
      unfold familySubsetLcmRecipRat
      positivity
    _ = M * familyCompatibleLcmMassRat indices (r - 1) := by
      rw [← Finset.sum_mul]
      simp [familyCompatibleLcmMassRat, familyCompatibleSubsetsOfCard,
        familySubsetLcmRecipRat, mul_comm]

/-- Finite Brun iteration for the actual reciprocal-lcm coefficients.  This
discharges the combinatorial part of `thm:Brun`; the only remaining input is
the uniform analytic bound for the concrete compatible extension increment. -/
theorem familyCompatibleLcmMassRat_le_pow_div_factorial_of_incrementRatio_le
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (M : ℚ) (hM : 0 ≤ M)
    (hinc : ∀ r : ℕ, 1 ≤ r →
      ∀ old ∈ familyCompatibleSubsetsOfCard indices (r - 1),
        familyIncrementRatioRat indices old ≤ M) :
    ∀ r : ℕ, familyCompatibleLcmMassRat indices r ≤
      M ^ r / (Nat.factorial r : ℚ) := by
  apply EscLeanChecks.brun_recurrence_iterated_bound_from_mul
    (familyCompatibleLcmMassRat indices) M hM
  · simp
  · intro r hr
    exact familyCompatibleLcmMassRat_recurrence_le_of_incrementRatio_le
      P X Pz b indices hmem M r (hinc r hr) (lt_of_lt_of_le Nat.zero_lt_one hr)

/-- Finite Brun iteration directly from a uniform bound for the manuscript's
one-step increment `A(S)`. -/
theorem familyCompatibleLcmMassRat_le_pow_div_factorial_of_increment_le
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (M : ℚ) (hM : 0 ≤ M)
    (hinc : ∀ r : ℕ, 1 ≤ r →
      ∀ old ∈ familyCompatibleSubsetsOfCard indices (r - 1),
        familyIncrementRat indices old ≤ M) :
    ∀ r : ℕ, familyCompatibleLcmMassRat indices r ≤
      M ^ r / (Nat.factorial r : ℚ) := by
  apply EscLeanChecks.brun_recurrence_iterated_bound_from_mul
    (familyCompatibleLcmMassRat indices) M hM
  · simp
  · intro r hr
    exact familyCompatibleLcmMassRat_recurrence_le_of_increment_le
      P X Pz b indices hmem M r (hinc r hr) (lt_of_lt_of_le Nat.zero_lt_one hr)

/-- Exact rank-`r` common-hit count `C_r^(b)(N)` for the finite paper family. -/
noncomputable def familyRankCommonHitCountRat
    (N Pz b : ℕ) (indices : Finset FamilyIndex) (r : ℕ) : ℚ :=
  (∑ events ∈ (familyEvents indices).powersetCard r,
    EscLeanChecks.baseSatEventCommonHitCountUpTo N Pz b events : ℕ)

/-- The lcm of a finite list of congruence moduli divides their product. -/
theorem congruenceLcm_dvd_moduli_product (rows : List (ℕ × ℕ)) :
    EscLeanChecks.congruenceLcm rows ∣ (rows.map Prod.fst).prod := by
  induction rows with
  | nil => simp [EscLeanChecks.congruenceLcm]
  | cons row rows ih =>
      simp only [EscLeanChecks.congruenceLcm, List.map_cons, List.prod_cons]
      apply Nat.lcm_dvd
      · exact dvd_mul_right row.1 _
      · exact ih.trans (dvd_mul_left _ row.1)

/-- Replacing each prime reciprocal by its event weight costs at most one
factor of the chosen cofactor bound per event. -/
theorem primeRecipProduct_le_scale_pow_mul_familyEventWeightProduct
    (events : Finset EscLeanChecks.SatEvent) (Xq : ℚ)
    (hdplusPos : ∀ event ∈ events, 0 < event.dPlus)
    (hpPos : ∀ event ∈ events, 0 < event.p)
    (hdplus : ∀ event ∈ events, (event.dPlus : ℚ) ≤ Xq) :
    (∏ event ∈ events, (1 : ℚ) / (event.p : ℚ)) ≤
      Xq ^ events.card *
        ∏ event ∈ events, familyEventWeightRat event := by
  classical
  have hprod :
      (∏ event ∈ events, (1 : ℚ) / (event.p : ℚ)) ≤
        ∏ event ∈ events, Xq * familyEventWeightRat event := by
    apply Finset.prod_le_prod
    · intro event hevent
      exact div_nonneg zero_le_one (by
        exact_mod_cast (Nat.zero_le event.p))
    · intro event hevent
      have hdq : (event.dPlus : ℚ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (hdplusPos event hevent))
      have hpq : (event.p : ℚ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (hpPos event hevent))
      have hweight : 0 ≤ familyEventWeightRat event :=
        familyEventWeightRat_nonneg event
      have hidentity :
          (1 : ℚ) / (event.p : ℚ) =
            (event.dPlus : ℚ) * familyEventWeightRat event := by
        unfold familyEventWeightRat EscLeanChecks.conditionalModulus
        field_simp [hdq, hpq]
      rw [hidentity]
      exact mul_le_mul_of_nonneg_right (hdplus event hevent) hweight
  calc
    (∏ event ∈ events, (1 : ℚ) / (event.p : ℚ)) ≤
        ∏ event ∈ events, Xq * familyEventWeightRat event := hprod
    _ = (∏ _event ∈ events, Xq) *
          ∏ event ∈ events, familyEventWeightRat event := by
          rw [Finset.prod_mul_distrib]
    _ = Xq ^ events.card *
          ∏ event ∈ events, familyEventWeightRat event := by
          simp

/-- The reduced conductor selected for an exact-divisor value occurring in a
finite paper family.  Outside that finite family it is set to `1`; on the
family it is well-defined because the squarefree decomposition determines
`rho(e)`. -/
noncomputable def familyRhoOf (indices : Finset FamilyIndex) (e : ℕ) : ℕ :=
  if h : ∃ i ∈ indices, i.e = e then (Classical.choose h).rho else 1

/-- On an actual family index, the chosen reduced conductor agrees with the
index's own conductor. -/
theorem familyRhoOf_eq_of_mem (indices : Finset FamilyIndex) {i : FamilyIndex}
    (hi : i ∈ indices) :
    familyRhoOf indices i.e = i.rho := by
  classical
  let h : ∃ j ∈ indices, j.e = i.e := ⟨i, hi, rfl⟩
  rw [familyRhoOf, dif_pos h]
  obtain ⟨_hjMem, hjE⟩ := Classical.choose_spec h
  exact ExactDivisor.rho_eq_of_e_eq (Classical.choose h).E i.E hjE

/-- The exact-divisor coordinate `r` is positive on the genuine large scale.
This is the only positivity fact not stored literally in `FamilyStaticMem`. -/
theorem FamilyStaticMem.r_pos
    {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (hX : 1 < X) (hmem : FamilyStaticMem P X Pz b i) : 0 < i.E.r := by
  have hXpos : 0 < X := lt_trans zero_lt_one hX
  have hY0 : 0 < Y0Scale P X := by
    simpa [Y0Scale] using Real.rpow_pos_of_pos hXpos P.lam
  have hsNat : 0 < i.E.s := lt_of_lt_of_le Nat.zero_lt_one hmem.s_pos
  have hs : 0 < (i.E.s : ℝ) := by exact_mod_cast hsNat
  have hquot : 0 < Y0Scale P X / (i.E.s : ℝ) := div_pos hY0 hs
  have hr : 0 < (i.E.r : ℝ) := lt_trans hquot hmem.r_gt
  exact_mod_cast hr

/-- On the positive-scale static family, the residual event retains the entire
paper index.  In particular, passing to `familyEvents` does not collapse two
different weighted indices. -/
theorem FamilyStaticMem.eq_of_toSatEvent_eq
    {P : Params} {X : ℝ} {Pz b : ℕ} {i j : FamilyIndex}
    (hX : 1 < X) (hi : FamilyStaticMem P X Pz b i)
    (hj : FamilyStaticMem P X Pz b j)
    (hevent : i.toSatEvent = j.toSatEvent) : i = j := by
  have he : i.E.e = j.E.e := by
    have h := congrArg EscLeanChecks.SatEvent.e hevent
    simpa [FamilyIndex.toSatEvent, FamilyIndex.e] using h
  have hrho : 0 < i.E.rho := by
    unfold ExactDivisor.rho
    exact Nat.mul_pos (hi.r_pos hX)
      (lt_of_lt_of_le Nat.zero_lt_one hi.s_pos)
  have hE : i.E = j.E := ExactDivisor.eq_of_e_eq_of_rho_pos i.E j.E he hrho
  have hdminus : i.dminus = j.dminus := by
    have h := congrArg EscLeanChecks.SatEvent.dMinus hevent
    simpa [FamilyIndex.toSatEvent] using h
  have hdplus : i.dplus = j.dplus := by
    have h := congrArg EscLeanChecks.SatEvent.dPlus hevent
    simpa [FamilyIndex.toSatEvent] using h
  have hp : i.p = j.p := by
    have h := congrArg EscLeanChecks.SatEvent.p hevent
    simpa [FamilyIndex.toSatEvent] using h
  cases i
  cases j
  simp_all

/-- The event image map is injective on every finite static paper family. -/
theorem familyIndex_toSatEvent_injOn
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i) :
    Set.InjOn FamilyIndex.toSatEvent (indices : Set FamilyIndex) := by
  intro i hi j hj hevent
  exact (hmem i hi).eq_of_toSatEvent_eq hX (hmem j hj) hevent

/-- The residual-event mass is exactly the manuscript's index mass; no weight
is lost when the finite family is converted to events. -/
theorem familyEventMassRat_eq_familyIndexMassRat
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i) :
    familyEventMassRat indices = familyIndexMassRat indices := by
  classical
  have hinj : Set.InjOn FamilyIndex.toSatEvent (indices : Set FamilyIndex) :=
    familyIndex_toSatEvent_injOn P X Pz b indices hX hmem
  calc
    familyEventMassRat indices =
        ∑ i ∈ indices, familyEventWeightRat i.toSatEvent := by
          unfold familyEventMassRat familyEvents
          exact Finset.sum_image hinj
    _ = familyIndexMassRat indices := by
          simp [familyIndexMassRat]

/-- Residue-fiber version of `familyEventMassRat_eq_familyIndexMassRat`.
Passing to residual events preserves not only the total mass but every exact
`e mod D` fiber used in `prop:event-tensor`. -/
theorem familyResidueMassRat_eq_index_sum
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (D c : ℕ) :
    familyResidueMassRat indices D c =
      ∑ i ∈ indices.filter
        (fun i => D ∣ i.dplus ∧ i.e % D = c), i.wRat := by
  classical
  have hinj : Set.InjOn FamilyIndex.toSatEvent (indices : Set FamilyIndex) :=
    familyIndex_toSatEvent_injOn P X Pz b indices hX hmem
  have hfilterImage :
      (familyEvents indices).filter
          (fun event => D ∣ event.dPlus ∧ event.e % D = c) =
        (indices.filter
          (fun i => D ∣ i.dplus ∧ i.e % D = c)).image
          FamilyIndex.toSatEvent := by
    ext event
    simp only [familyEvents, Finset.mem_filter, Finset.mem_image]
    constructor
    · intro hevent
      rcases hevent.1 with ⟨i, hi, rfl⟩
      exact ⟨i, ⟨hi, hevent.2⟩, rfl⟩
    · rintro ⟨i, ⟨hi, hires⟩, rfl⟩
      exact ⟨⟨i, hi, rfl⟩, hires⟩
  unfold familyResidueMassRat
  rw [hfilterImage]
  have hinjFilter : Set.InjOn FamilyIndex.toSatEvent
      ((indices.filter (fun i => D ∣ i.dplus ∧ i.e % D = c) :
          Finset FamilyIndex) :
        Set FamilyIndex) :=
    hinj.mono (Finset.filter_subset _ _)
  rw [Finset.sum_image hinjFilter]
  simp

/-- A static member of the paper's family satisfies the finite admissibility
conditions used by the residual-event layer.  The two strict scale comparisons
are derived from the manuscript parameters: `e ≤ H < X^β < p` and
`dminus * dplus ≤ Y < Y0 < rho(e)`. -/
theorem FamilyStaticMem.toSatEvent_admissible
    {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (hX : 1 < X) (hmem : FamilyStaticMem P X Pz b i) :
    EscLeanChecks.satEventAdmissible Pz i.rho i.toSatEvent := by
  refine ⟨hmem.p_prime, ?_, ?_, ?_, hmem.dminus_pos, hmem.dplus_pos,
    hmem.dminus_dvd_Pz, hmem.dplus_coprime_Pz⟩
  · have hs_pos : 0 < (i.E.s : ℝ) := by
      exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hmem.s_pos
    have hs_sq_pos : 0 < (i.E.s : ℝ) ^ 2 := pow_pos hs_pos _
    have he_le_H : (i.e : ℝ) ≤ HScale P X := by
      have hr_le := (le_div_iff₀ hs_sq_pos).mp hmem.r_le
      simpa [FamilyIndex.e_eq, Nat.cast_mul, Nat.cast_pow] using hr_le
    have htheta_lt_beta : P.θ < P.β := by
      linarith [P.two_θ_lt_β, P.θ_pos]
    have hH_lt : HScale P X < X ^ P.β := by
      unfold HScale
      exact Real.rpow_lt_rpow_of_exponent_lt hX htheta_lt_beta
    have he_lt_p : (i.e : ℝ) < (i.p : ℝ) :=
      lt_of_le_of_lt he_le_H (lt_trans hH_lt hmem.p_gt)
    exact_mod_cast he_lt_p
  · have hs_pos : 0 < (i.E.s : ℝ) := by
      exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hmem.s_pos
    have hdiv_mul :
        (Y0Scale P X / (i.E.s : ℝ)) * (i.E.s : ℝ) = Y0Scale P X := by
      field_simp [ne_of_gt hs_pos]
    have hrho_gt_Y0 : Y0Scale P X < (i.rho : ℝ) := by
      have hmul := mul_lt_mul_of_pos_right hmem.r_gt hs_pos
      rw [hdiv_mul] at hmul
      simpa [FamilyIndex.rho_eq, Nat.cast_mul] using hmul
    have hdd_lt_rho : (i.dminus * i.dplus : ℝ) < (i.rho : ℝ) :=
      lt_of_le_of_lt hmem.dd_le_Y
        (lt_trans (YScale_lt_Y0Scale P hX) hrho_gt_Y0)
    exact_mod_cast hdd_lt_rho
  · apply Nat.modEq_zero_iff_dvd.mpr
    simpa [FamilyIndex.toSatEvent, FamilyIndex.Q, Nat.mul_assoc] using hmem.sat_cong

/-- The rough cofactor of a paper-family index lies below the lower end of the
selected-prime range. -/
theorem FamilyStaticMem.dplus_lt_primeScale
    {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (hX : 1 < X) (hmem : FamilyStaticMem P X Pz b i) :
    (i.dplus : ℝ) < X ^ P.β := by
  have hdplus_le_product : i.dplus ≤ i.dminus * i.dplus :=
    Nat.le_mul_of_pos_left i.dplus hmem.dminus_pos
  have htheta_lt_beta : P.θ < P.β := by
    nlinarith [P.two_θ_lt_β, P.θ_pos]
  have hsigma_lt_beta : P.σ < P.β :=
    P.σ_lt_θ.trans htheta_lt_beta
  have hY_lt : YScale P X < X ^ P.β := by
    unfold YScale
    exact Real.rpow_lt_rpow_left_iff hX |>.mpr hsigma_lt_beta
  exact lt_of_le_of_lt
    (le_trans (by exact_mod_cast hdplus_le_product) hmem.dd_le_Y) hY_lt

/-- The rough cofactor is strictly below the ambient family scale. -/
theorem FamilyStaticMem.dplus_lt_X
    {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (hX : 1 < X) (hmem : FamilyStaticMem P X Pz b i) :
    (i.dplus : ℝ) < X := by
  have hbeta : X ^ P.β < X := by
    simpa using (Real.rpow_lt_rpow_left_iff hX).2 P.β_lt_one
  exact (hmem.dplus_lt_primeScale hX).trans hbeta

/-- The rough cofactor is at most the manuscript's medium-factor scale
`Y = X^σ`. -/
theorem FamilyStaticMem.dplus_le_YScale
    {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (hmem : FamilyStaticMem P X Pz b i) :
    (i.dplus : ℝ) ≤ YScale P X := by
  have hdm : (1 : ℝ) ≤ i.dminus := by
    exact_mod_cast hmem.dminus_pos
  have hdp : 0 ≤ (i.dplus : ℝ) := by positivity
  calc
    (i.dplus : ℝ) ≤ (i.dminus : ℝ) * (i.dplus : ℝ) := by
      nlinarith
    _ ≤ YScale P X := hmem.dd_le_Y

/-- Natural-floor form of the same cofactor bound, used by the exact rational
finite-interval estimates. -/
theorem FamilyStaticMem.dplus_le_floor_X
    {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (hX : 1 < X) (hmem : FamilyStaticMem P X Pz b i) :
    i.dplus ≤ ⌊X⌋₊ :=
  Nat.le_floor (hmem.dplus_lt_X hX).le

/-- The rough medium cofactor is odd, as forced by its coprimality with the
factor `4` in the certificate modulus. -/
theorem FamilyStaticMem.dplus_odd
    {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (hmem : FamilyStaticMem P X Pz b i) : Odd i.dplus := by
  have hcopFour : Nat.Coprime i.dplus 4 :=
    Nat.Coprime.coprime_dvd_right (by norm_num : 4 ∣ 4 * i.rho)
      (Nat.Coprime.coprime_dvd_left
        (dvd_mul_left i.dplus i.dminus) hmem.dd_coprime_four_rho)
  have hcopTwo : Nat.Coprime i.dplus 2 :=
    Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 4) hcopFour
  exact Nat.coprime_two_right.mp hcopTwo

/-- Elementary roughness bound for one actual family cofactor.  The only
cutoff hypothesis says that every prime below `q` was included in `Pz`; the
family coprimality condition then forces every prime divisor of `dplus` to be
at least `q`. -/
theorem FamilyStaticMem.dplus_primeFactors_recip_sum_le_YScale
    {P : Params} {X : ℝ} {Pz b q : ℕ} {i : FamilyIndex}
    (hX : 1 < X) (hmem : FamilyStaticMem P X Pz b i)
    (hq2 : 2 ≤ q)
    (hsmall : ∀ p : ℕ, Nat.Prime p → p < q → p ∣ Pz) :
    (∑ p ∈ i.dplus.primeFactors, (1 : ℝ) / (p : ℝ)) ≤
      (Real.log (YScale P X) / Real.log (q : ℝ)) / (q : ℝ) := by
  have hrough : ∀ p ∈ i.dplus.primeFactors, q ≤ p := by
    intro p hp
    by_contra hpq
    have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hpDvd : p ∣ i.dplus := (Nat.mem_primeFactors.mp hp).2.1
    have hpPz : p ∣ Pz := hsmall p hpPrime (Nat.lt_of_not_ge hpq)
    have hpGcd : p ∣ Nat.gcd i.dplus Pz := Nat.dvd_gcd hpDvd hpPz
    have hcop : Nat.gcd i.dplus Pz = 1 := hmem.dplus_coprime_Pz
    have hpOne : p ∣ 1 := by
      simpa [hcop] using hpGcd
    exact hpPrime.not_dvd_one hpOne
  have hroughSum := EscLeanChecks.primeFactors_recip_sum_le_log_div_log_div
    i.dplus q hmem.dplus_pos hq2 hrough
  have hYpos : 0 < YScale P X := by
    unfold YScale
    positivity
  have hlog : Real.log (i.dplus : ℝ) ≤ Real.log (YScale P X) :=
    Real.log_le_log (by exact_mod_cast hmem.dplus_pos) hmem.dplus_le_YScale
  have hlogqpos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast hq2)
  have hqpos : 0 < (q : ℝ) := by positivity
  calc
    (∑ p ∈ i.dplus.primeFactors, (1 : ℝ) / (p : ℝ)) ≤
        (Real.log (i.dplus : ℝ) / Real.log (q : ℝ)) / (q : ℝ) :=
      hroughSum
    _ ≤ (Real.log (YScale P X) / Real.log (q : ℝ)) / (q : ℝ) := by
      exact div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hlog hlogqpos.le) hqpos.le

/-- Any rough cofactor in the static paper family is smaller than any selected
prime in that same family.  This is the scale separation used by the increment
argument. -/
theorem FamilyStaticMem.dplus_lt_other_p
    {P : Params} {X : ℝ} {Pz b : ℕ} {i j : FamilyIndex}
    (hX : 1 < X) (hi : FamilyStaticMem P X Pz b i)
    (hj : FamilyStaticMem P X Pz b j) :
    i.dplus < j.p := by
  have hlt : (i.dplus : ℝ) < (j.p : ℝ) :=
    lt_trans (hi.dplus_lt_primeScale hX) hj.p_gt
  exact_mod_cast hlt

/-- The finite image of the actual paper family carries a single
`e`-indexed conductor function, so it can be used directly by the generic
admissibility-for-event machinery. -/
theorem familyEvents_admissibleFor
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i) :
    ∀ event ∈ familyEvents indices,
      EscLeanChecks.satEventAdmissibleFor Pz (familyRhoOf indices) event := by
  intro event hevent
  rw [familyEvents] at hevent
  rcases Finset.mem_image.mp hevent with ⟨i, hi, rfl⟩
  unfold EscLeanChecks.satEventAdmissibleFor
  change EscLeanChecks.satEventAdmissible Pz (familyRhoOf indices i.e) i.toSatEvent
  rw [familyRhoOf_eq_of_mem indices hi]
  exact FamilyStaticMem.toSatEvent_admissible hX (hmem i hi)

/-- Distinct compatible events in the actual static paper family have distinct
selected primes. -/
theorem familyEvents_largePrime_ne_of_compatible_ne
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    {event other : EscLeanChecks.SatEvent}
    (hevent : event ∈ familyEvents indices)
    (hother : other ∈ familyEvents indices)
    (hcompat : EscLeanChecks.satEventCompatible event other)
    (hne : event ≠ other) :
    event.p ≠ other.p := by
  exact
    EscLeanChecks.satEvent_largePrime_ne_of_compatible_ne_admissibleFor_autoCoprime
      Pz (familyRhoOf indices) event other hcompat hne
      (familyEvents_admissibleFor P X Pz b indices hX hmem event hevent)
      (familyEvents_admissibleFor P X Pz b indices hX hmem other hother)

/-- The cross-event scale separation for the finite image of the actual paper
family. -/
theorem familyEvents_dPlus_lt_p_of_mem
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    {event other : EscLeanChecks.SatEvent}
    (hevent : event ∈ familyEvents indices)
    (hother : other ∈ familyEvents indices) :
    other.dPlus < event.p := by
  rcases Finset.mem_image.mp hevent with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp hother with ⟨j, hj, rfl⟩
  exact (hmem j hj).dplus_lt_other_p hX (hmem i hi)

/-- Every event in a static paper family inherits the natural-floor cofactor
bound from its index. -/
theorem familyEvents_dPlus_le_floor_X_of_mem
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    {event : EscLeanChecks.SatEvent}
    (hevent : event ∈ familyEvents indices) :
    event.dPlus ≤ ⌊X⌋₊ := by
  rcases Finset.mem_image.mp hevent with ⟨i, hi, rfl⟩
  exact (hmem i hi).dplus_le_floor_X hX

/-- Any ordering of distinct events from the same static paper family has the
cofactor/large-prime separation required by the iterative increment bound. -/
theorem familyEvents_orderedDPlusLtLargePrime
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i) :
    ∀ events : List EscLeanChecks.SatEvent,
      (∀ event ∈ events, event ∈ familyEvents indices) →
      EscLeanChecks.satEventOrderedDPlusLtLargePrime events := by
  intro events
  induction events with
  | nil =>
      simp [EscLeanChecks.satEventOrderedDPlusLtLargePrime]
  | cons event old ih =>
      intro hsub
      constructor
      · intro other hother
        exact familyEvents_dPlus_lt_p_of_mem P X Pz b indices hX hmem
          (hsub event (by simp)) (hsub other (by simp [hother]))
      · apply ih
        intro other hother
        exact hsub other (by simp [hother])

/-- Reciprocal-lcm estimate for a compatible subset of the actual paper
family.  This is the manuscript's increment step in the exact finite carrier:
each added event costs one factor `floor(X)` times its true weight `1/q`. -/
theorem familyEvents_congruenceLcm_recip_le_floor_scale_pow_weightProduct
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (events : Finset EscLeanChecks.SatEvent)
    (hsub : events ⊆ familyEvents indices)
    (hcompat : ∀ event ∈ events, ∀ other ∈ events,
      event ≠ other → EscLeanChecks.satEventCompatible event other) :
    (1 : ℚ) /
        (EscLeanChecks.congruenceLcm
          (EscLeanChecks.satEventResidualHitRows events.toList) : ℚ) ≤
      (⌊X⌋₊ : ℚ) ^ events.card *
        ∏ event ∈ events, familyEventWeightRat event := by
  classical
  have hadmList : ∀ event ∈ events.toList,
      EscLeanChecks.satEventAdmissibleFor Pz (familyRhoOf indices) event := by
    intro event hevent
    exact familyEvents_admissibleFor P X Pz b indices hX hmem event
      (hsub (by simpa using hevent))
  have hordered :
      EscLeanChecks.satEventOrderedDPlusLtLargePrime events.toList :=
    familyEvents_orderedDPlusLtLargePrime P X Pz b indices hX hmem
      events.toList (by
        intro event hevent
        exact hsub (by simpa using hevent))
  have hlcmList :=
    EscLeanChecks.congruenceLcm_satEventResidualHitRows_recip_le_primeRecipProduct_of_pairwiseCompatible_admissibleFor_ordered
      Pz (familyRhoOf indices) events.toList hadmList hordered
      (by
        intro event hevent other hother hne
        exact hcompat event (by simpa using hevent) other
          (by simpa using hother) hne)
      events.nodup_toList
  have hlcm :
      (1 : ℚ) /
          (EscLeanChecks.congruenceLcm
            (EscLeanChecks.satEventResidualHitRows events.toList) : ℚ) ≤
        ∏ event ∈ events, (1 : ℚ) / (event.p : ℚ) := by
    simpa using hlcmList
  have hweights :
      (∏ event ∈ events, (1 : ℚ) / (event.p : ℚ)) ≤
        (⌊X⌋₊ : ℚ) ^ events.card *
          ∏ event ∈ events, familyEventWeightRat event := by
    apply primeRecipProduct_le_scale_pow_mul_familyEventWeightProduct
    · intro event hevent
      have hadm' : EscLeanChecks.satEventAdmissible Pz
          (familyRhoOf indices event.e) event := by
        simpa [EscLeanChecks.satEventAdmissibleFor] using
          familyEvents_admissibleFor P X Pz b indices hX hmem event
            (hsub hevent)
      exact hadm'.2.2.2.2.2.1
    · intro event hevent
      have hadm' : EscLeanChecks.satEventAdmissible Pz
          (familyRhoOf indices event.e) event := by
        simpa [EscLeanChecks.satEventAdmissibleFor] using
          familyEvents_admissibleFor P X Pz b indices hX hmem event
            (hsub hevent)
      exact hadm'.1.pos
    · intro event hevent
      exact_mod_cast
        familyEvents_dPlus_le_floor_X_of_mem P X Pz b indices hX hmem
          (hsub hevent)
  exact hlcm.trans hweights

/-- The structural increment conclusion for a list of pairwise distinct
compatible events from the actual static paper family. -/
theorem familyEvents_incrementCommonDivisor_dvd_medium_of_compatible
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (event : EscLeanChecks.SatEvent) (old : List EscLeanChecks.SatEvent)
    (hevent : event ∈ familyEvents indices)
    (hold : ∀ other ∈ old, other ∈ familyEvents indices)
    (hcompat : ∀ other ∈ old, EscLeanChecks.satEventCompatible event other)
    (hdistinct : ∀ other ∈ old, event ≠ other) :
    EscLeanChecks.incrementG event.dPlus event.p
        (EscLeanChecks.residualLcm (EscLeanChecks.satEventRows old)) ∣
      event.dPlus := by
  apply
    EscLeanChecks.incrementCommonDivisor_dvd_medium_of_compatible_events_admissibleFor_autoCoprime
      Pz (familyRhoOf indices) event old
  · exact familyEvents_admissibleFor P X Pz b indices hX hmem event hevent
  · intro other hother
    exact familyEvents_admissibleFor P X Pz b indices hX hmem other
      (hold other hother)
  · intro other hother
    exact familyEvents_dPlus_lt_p_of_mem P X Pz b indices hX hmem hevent
      (hold other hother)
  · exact hcompat
  · exact hdistinct

/-- For an event in the concrete compatible-extension carrier, the gcd appearing
in `A(S)` divides that event's medium factor. -/
theorem familyCompatibleExtension_gcd_dvd_dPlus
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ familyEvents indices)
    (event : EscLeanChecks.SatEvent)
    (hext : event ∈ familyCompatibleExtensions indices old) :
    Nat.gcd
        (EscLeanChecks.congruenceLcm
          (EscLeanChecks.satEventResidualHitRows old.toList))
        (EscLeanChecks.conditionalModulus event.dPlus event.p) ∣
      event.dPlus := by
  classical
  rw [familyCompatibleExtensions] at hext
  rcases Finset.mem_filter.mp hext with ⟨hevent, hnot, hpair⟩
  have hdiv := familyEvents_incrementCommonDivisor_dvd_medium_of_compatible
    P X Pz b indices hX hmem event old.toList hevent
    (by
      intro other hother
      exact hsub (by simpa using hother))
    (by
      intro other hother
      have hotherOld : other ∈ old := by simpa using hother
      apply hpair event (by simp) other (Finset.mem_insert_of_mem hotherOld)
      intro heq
      subst other
      exact hnot hotherOld)
    (by
      intro other hother heq
      have hotherOld : other ∈ old := by simpa using hother
      subst other
      exact hnot hotherOld)
  rw [EscLeanChecks.congruenceLcm_satEventResidualHitRows_eq_residualLcm_satEventRows]
  simpa [EscLeanChecks.incrementG, Nat.gcd_comm] using hdiv

/-- If a prime `ell` divides the overlap of a compatible extension, then the
extension's `e`-class modulo `ell` was already represented by an old event
whose medium factor is divisible by `ell`.  This is the prime-by-prime
compatibility assertion defining `C_ell(S)` in the manuscript. -/
theorem familyIncrement_primeResidue_mem_oldClasses
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ familyEvents indices)
    (D : ℕ) (event : EscLeanChecks.SatEvent)
    (heventD : event ∈ familyIncrementDivisorEvents indices old D)
    (ell : ℕ) (hell : Nat.Prime ell) (hellD : ell ∣ D)
    (hcop : Nat.gcd ell 4 = 1) :
    event.e % ell ∈ familyOldPrimeResidueClasses old ell := by
  classical
  have heventD' := heventD
  rw [familyIncrementDivisorEvents] at heventD
  rcases Finset.mem_filter.mp heventD with ⟨hext, hDg⟩
  have hext' := hext
  rw [familyCompatibleExtensions] at hext
  rcases Finset.mem_filter.mp hext with ⟨hevent, hnot, hpair⟩
  have hellg : ell ∣ familyIncrementG old event := hellD.trans hDg
  have hellL : ell ∣ EscLeanChecks.congruenceLcm
      (EscLeanChecks.satEventResidualHitRows old.toList) := by
    exact hellg.trans (Nat.gcd_dvd_left _ _)
  rcases (EscLeanChecks.prime_dvd_congruenceLcm_iff ell hell
    (EscLeanChecks.satEventResidualHitRows old.toList)).mp hellL with
    ⟨row, hrow, hellrow⟩
  rcases List.mem_map.mp hrow with ⟨other, hotherList, rfl⟩
  have hotherOld : other ∈ old := by simpa using hotherList
  have hotherFamily : other ∈ familyEvents indices := hsub hotherOld
  change ell ∣ EscLeanChecks.conditionalModulus other.dPlus other.p at hellrow
  have hellEventDPlus : ell ∣ event.dPlus := by
    exact hellg.trans (familyCompatibleExtension_gcd_dvd_dPlus
      P X Pz b indices hX hmem old hsub event hext')
  have hellOtherDPlus : ell ∣ other.dPlus := by
    rcases hell.dvd_mul.mp hellrow with hdplus | hp
    · exact hdplus
    · have hpprime : Nat.Prime other.p := by
        rcases Finset.mem_image.mp hotherFamily with ⟨i, hi, rfl⟩
        exact (hmem i hi).p_prime
      rcases (Nat.dvd_prime hpprime).mp hp with hellOne | hellP
      · exact (hell.ne_one hellOne).elim
      · have heventDPlusPos : 0 < event.dPlus := by
          rcases Finset.mem_image.mp hevent with ⟨i, hi, rfl⟩
          exact (hmem i hi).dplus_pos
        have hellLe : ell ≤ event.dPlus :=
          Nat.le_of_dvd heventDPlusPos hellEventDPlus
        have hdplusLt : event.dPlus < other.p :=
          familyEvents_dPlus_lt_p_of_mem P X Pz b indices hX hmem
            hotherFamily hevent
        omega
  have hellEventQ : ell ∣ EscLeanChecks.conditionalModulus event.dPlus event.p :=
    hellEventDPlus.trans (dvd_mul_right event.dPlus event.p)
  have hdivGcd : ell ∣ Nat.gcd
      (EscLeanChecks.conditionalModulus event.dPlus event.p)
      (EscLeanChecks.conditionalModulus other.dPlus other.p) :=
    Nat.dvd_gcd hellEventQ hellrow
  have hne : event ≠ other := by
    intro heq
    subst other
    exact hnot hotherOld
  have hcompat : EscLeanChecks.satEventCompatible event other :=
    hpair event (by simp) other (Finset.mem_insert_of_mem hotherOld) hne
  have hmod : event.e ≡ other.e [MOD ell] :=
    EscLeanChecks.satEvent_modEq_of_compatible_of_dvd_gcd_of_coprime
      event other ell hcompat hdivGcd hcop
  unfold familyOldPrimeResidueClasses
  exact Finset.mem_image.mpr
    ⟨other, Finset.mem_filter.mpr ⟨hotherOld, hellOtherDPlus⟩, hmod.symm⟩

/-- For squarefree odd `D`, the represented increment classes modulo `D` inject
into the product of the old prime-residue class sets.  This is the exact CRT
cardinality bound `|C_D(S)| ≤ prod_{ell|D} C_ell(S)`. -/
theorem familyIncrementResidueClasses_card_le_prod_oldPrimeClasses
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ familyEvents indices)
    (D : ℕ) (hDpos : 0 < D) (hDsqf : Squarefree D) (hDodd : Odd D) :
    (familyIncrementResidueClasses indices old D).card ≤
      ∏ ell ∈ D.primeFactors, (familyOldPrimeResidueClasses old ell).card := by
  classical
  let target := D.primeFactors.pi
    (fun ell => familyOldPrimeResidueClasses old ell)
  let code : ℕ → ((ell : ℕ) → ell ∈ D.primeFactors → ℕ) :=
    fun c ell _hell => c % ell
  have hcopFour : ∀ ell ∈ D.primeFactors,
      Nat.gcd ell 4 = 1 := by
    intro ell hellMem
    have hellData := (Nat.mem_primeFactors.mp hellMem)
    have hellPrime : Nat.Prime ell := hellData.1
    have hellD : ell ∣ D := hellData.2.1
    have hellNotDvdTwo : ¬ell ∣ 2 := by
      intro hellTwo
      rcases (Nat.dvd_prime Nat.prime_two).mp hellTwo with hellOne | hellEqTwo
      · exact hellPrime.ne_one hellOne
      · subst ell
        exact hDodd.not_two_dvd_nat hellD
    have hellNotDvdFour : ¬ell ∣ 4 := by
      intro hellFour
      have : ell ∣ 2 * 2 := by simpa using hellFour
      exact (hellPrime.dvd_mul.mp this).elim hellNotDvdTwo hellNotDvdTwo
    exact (hellPrime.coprime_iff_not_dvd.mpr hellNotDvdFour)
  have hmap : ∀ c ∈ familyIncrementResidueClasses indices old D,
      code c ∈ target := by
    intro c hc
    rw [familyIncrementResidueClasses] at hc
    rcases Finset.mem_image.mp hc with ⟨event, heventD, rfl⟩
    change code (event.e % D) ∈ D.primeFactors.pi
      (fun ell => familyOldPrimeResidueClasses old ell)
    rw [Finset.mem_pi]
    intro ell hellMem
    have hellData := Nat.mem_primeFactors.mp hellMem
    have hclass := familyIncrement_primeResidue_mem_oldClasses
      P X Pz b indices hX hmem old hsub D event heventD
      ell hellData.1 hellData.2.1 (hcopFour ell hellMem)
    simpa [code, Nat.mod_mod_of_dvd event.e hellData.2.1] using hclass
  have pairwiseCoprime_of_nodup_primes : ∀ l : List ℕ,
      l.Nodup → (∀ p ∈ l, Nat.Prime p) → l.Pairwise Nat.Coprime := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
        intro hnodup hprime
        rw [List.nodup_cons] at hnodup
        rw [List.pairwise_cons]
        constructor
        · intro q hq
          apply (Nat.coprime_primes
            (hprime p (by simp)) (hprime q (by simp [hq]))).2
          intro hpq
          apply hnodup.1
          simpa [hpq] using hq
        · apply ih hnodup.2
          intro q hq
          exact hprime q (by simp [hq])
  have hDne : D ≠ 0 := hDpos.ne'
  have hpair : D.primeFactorsList.Pairwise Nat.Coprime := by
    apply pairwiseCoprime_of_nodup_primes D.primeFactorsList
    · exact (Nat.squarefree_iff_nodup_primeFactorsList hDne).mp hDsqf
    · intro ell hell
      exact Nat.prime_of_mem_primeFactorsList hell
  have hinj : Set.InjOn code
      (familyIncrementResidueClasses indices old D : Set ℕ) := by
    intro c hc c' hc' hcode
    have hmodD : c ≡ c' [MOD D] := by
      rw [← Nat.prod_primeFactorsList hDne]
      apply (Nat.modEq_list_prod_iff hpair).2
      intro i
      have hellList : D.primeFactorsList.get i ∈ D.primeFactorsList :=
        D.primeFactorsList.get_mem i i.isLt
      have hellMem : D.primeFactorsList.get i ∈ D.primeFactors :=
        Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hellList
      have hvalue := congrFun (congrFun hcode (D.primeFactorsList.get i)) hellMem
      simpa [code] using hvalue
    have hcLt : c < D := by
      rw [familyIncrementResidueClasses] at hc
      rcases Finset.mem_image.mp hc with ⟨event, _hevent, rfl⟩
      exact Nat.mod_lt event.e hDpos
    have hc'Lt : c' < D := by
      rw [familyIncrementResidueClasses] at hc'
      rcases Finset.mem_image.mp hc' with ⟨event, _hevent, rfl⟩
      exact Nat.mod_lt event.e hDpos
    exact hmodD.eq_of_lt_of_lt hcLt hc'Lt
  have hcard := Finset.card_le_card_of_injOn code hmap hinj
  change (familyIncrementResidueClasses indices old D).card ≤
    (D.primeFactors.pi
      (fun ell => familyOldPrimeResidueClasses old ell)).card at hcard
  simpa only [Finset.card_pi] using hcard

/-- The same CRT class bound without separate hypotheses on `D`: if a class is
represented then `D | g(i;S) | d_{+,i}`, so positivity, squarefreeness, and
oddness follow from static family membership; if no class is represented the
bound is trivial. -/
theorem familyIncrementResidueClasses_card_le_prod_oldPrimeClasses_auto
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ familyEvents indices)
    (D : ℕ) :
    (familyIncrementResidueClasses indices old D).card ≤
      ∏ ell ∈ D.primeFactors, (familyOldPrimeResidueClasses old ell).card := by
  classical
  by_cases hempty : familyIncrementResidueClasses indices old D = ∅
  · simp [hempty]
  · have hnonempty :
        (familyIncrementResidueClasses indices old D).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    rcases hnonempty with ⟨c, hc⟩
    rw [familyIncrementResidueClasses] at hc
    rcases Finset.mem_image.mp hc with ⟨event, heventD, _hc⟩
    have heventD' := heventD
    rw [familyIncrementDivisorEvents] at heventD
    rcases Finset.mem_filter.mp heventD with ⟨hext, hDg⟩
    have hext' := hext
    rw [familyCompatibleExtensions] at hext
    have hevent : event ∈ familyEvents indices := (Finset.mem_filter.mp hext).1
    have hDdiv : D ∣ event.dPlus :=
      hDg.trans (by
        simpa [familyIncrementG] using
          familyCompatibleExtension_gcd_dvd_dPlus
            P X Pz b indices hX hmem old hsub event hext')
    rcases Finset.mem_image.mp hevent with ⟨i, hi, rfl⟩
    have hDpos : 0 < D := Nat.pos_of_dvd_of_pos hDdiv (hmem i hi).dplus_pos
    have hDsqf : Squarefree D :=
      Squarefree.squarefree_of_dvd hDdiv (hmem i hi).dplus_squarefree
    have hDodd : Odd D := Odd.of_dvd_nat (hmem i hi).dplus_odd hDdiv
    exact familyIncrementResidueClasses_card_le_prod_oldPrimeClasses
      P X Pz b indices hX hmem old hsub D hDpos hDsqf hDodd

/-- No divisor-restricted increment residue class exists outside the
squarefree odd support inherited from `d_+`. -/
theorem familyIncrementResidueClasses_eq_empty_of_not_squarefree_or_not_odd
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ familyEvents indices)
    (D : ℕ) (hbad : ¬(Squarefree D ∧ Odd D)) :
    familyIncrementResidueClasses indices old D = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro c hc
  rw [familyIncrementResidueClasses] at hc
  rcases Finset.mem_image.mp hc with ⟨event, heventD, _hc⟩
  have heventD' := heventD
  rw [familyIncrementDivisorEvents] at heventD
  rcases Finset.mem_filter.mp heventD with ⟨hext, hDg⟩
  have hext' := hext
  rw [familyCompatibleExtensions] at hext
  have hevent : event ∈ familyEvents indices := (Finset.mem_filter.mp hext).1
  have hDdiv : D ∣ event.dPlus :=
    hDg.trans (by
      simpa [familyIncrementG] using
        familyCompatibleExtension_gcd_dvd_dPlus
          P X Pz b indices hX hmem old hsub event hext')
  rcases Finset.mem_image.mp hevent with ⟨i, hi, rfl⟩
  apply hbad
  exact ⟨Squarefree.squarefree_of_dvd hDdiv (hmem i hi).dplus_squarefree,
    Odd.of_dvd_nat (hmem i hi).dplus_odd hDdiv⟩

/-- The realized class count is bounded by the correctly supported
squarefree multiplicative class product. -/
theorem familyIncrementResidueClasses_card_le_classProductRat
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ familyEvents indices)
    (D : ℕ) :
    ((familyIncrementResidueClasses indices old D).card : ℚ) ≤
      familyIncrementClassProductRat old D := by
  classical
  by_cases hgood : Squarefree D ∧ Odd D
  · rw [familyIncrementClassProductRat, if_pos hgood]
    exact_mod_cast
      familyIncrementResidueClasses_card_le_prod_oldPrimeClasses_auto
        P X Pz b indices hX hmem old hsub D
  · rw [familyIncrementClassProductRat, if_neg hgood,
      familyIncrementResidueClasses_eq_empty_of_not_squarefree_or_not_odd
        P X Pz b indices hX hmem old hsub D hgood]
    simp

/-- The correctly supported class-count divisor sum is bounded by the finite
Euler product over primes up to `B`. -/
theorem familyIncrementClassProduct_sum_le_eulerProduct
    (old : Finset EscLeanChecks.SatEvent) (B : ℕ) (hB : 1 ≤ B) :
    1 + (∑ D ∈ Finset.Icc 2 B,
      familyIncrementClassProductRat old D / (D : ℚ)) ≤
      ∏ p ∈ EscLeanChecks.primeFinsetUpTo B,
        (1 + ((familyOldPrimeResidueClasses old p).card : ℚ) / (p : ℚ)) := by
  classical
  let a : ℕ → ℚ := fun p =>
    ((familyOldPrimeResidueClasses old p).card : ℚ) / (p : ℚ)
  have ha : ∀ p ∈ EscLeanChecks.primeFinsetUpTo B, 0 ≤ a p := by
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
  have heuler := EscLeanChecks.squarefree_primeFactor_sum_le_eulerProduct
    B a ha
  calc
    1 + (∑ D ∈ Finset.Icc 2 B,
        familyIncrementClassProductRat old D / (D : ℚ)) ≤
      1 + ∑ D ∈ (Finset.Icc 2 B).filter Squarefree,
        ∏ p ∈ D.primeFactors, a p := add_le_add_left hmajor 1
    _ = ∑ D ∈ (Finset.Icc 1 B).filter Squarefree,
        ∏ p ∈ D.primeFactors, a p := by
      rw [hIcc, Finset.sum_insert]
      · simp [a]
      · simp
    _ ≤ ∏ p ∈ EscLeanChecks.primeFinsetUpTo B, (1 + a p) := heuler
    _ = ∏ p ∈ EscLeanChecks.primeFinsetUpTo B,
        (1 + ((familyOldPrimeResidueClasses old p).card : ℚ) / (p : ℚ)) := rfl

/-- Real exponential form of the finite increment Euler-product bound. -/
theorem familyIncrementClassProduct_real_sum_le_exp
    (old : Finset EscLeanChecks.SatEvent) (B : ℕ) (hB : 1 ≤ B) :
    (1 : ℝ) + (∑ D ∈ Finset.Icc 2 B,
      (familyIncrementClassProductRat old D : ℝ) / (D : ℝ)) ≤
      Real.exp (∑ p ∈ EscLeanChecks.primeFinsetUpTo B,
        ((familyOldPrimeResidueClasses old p).card : ℝ) / (p : ℝ)) := by
  have heulerQ := familyIncrementClassProduct_sum_le_eulerProduct old B hB
  have heulerR :
      (1 : ℝ) + (∑ D ∈ Finset.Icc 2 B,
        (familyIncrementClassProductRat old D : ℝ) / (D : ℝ)) ≤
        ∏ p ∈ EscLeanChecks.primeFinsetUpTo B,
          (1 + ((familyOldPrimeResidueClasses old p).card : ℝ) / (p : ℝ)) := by
    have hcast :
        (((1 + (∑ D ∈ Finset.Icc 2 B,
          familyIncrementClassProductRat old D / (D : ℚ))) : ℚ) : ℝ) ≤
        (((∏ p ∈ EscLeanChecks.primeFinsetUpTo B,
          (1 + ((familyOldPrimeResidueClasses old p).card : ℚ) / (p : ℚ))) : ℚ) : ℝ) := by
      exact_mod_cast heulerQ
    simpa using hcast
  calc
    (1 : ℝ) + (∑ D ∈ Finset.Icc 2 B,
        (familyIncrementClassProductRat old D : ℝ) / (D : ℝ)) ≤
      ∏ p ∈ EscLeanChecks.primeFinsetUpTo B,
        (1 + ((familyOldPrimeResidueClasses old p).card : ℝ) / (p : ℝ)) := heulerR
    _ ≤ ∏ p ∈ EscLeanChecks.primeFinsetUpTo B,
        Real.exp (((familyOldPrimeResidueClasses old p).card : ℝ) / (p : ℝ)) := by
      gcongr with p hp
      have h := Real.add_one_le_exp
        (((familyOldPrimeResidueClasses old p).card : ℝ) / (p : ℝ))
      linarith
    _ = Real.exp (∑ p ∈ EscLeanChecks.primeFinsetUpTo B,
        ((familyOldPrimeResidueClasses old p).card : ℝ) / (p : ℝ)) := by
      rw [Real.exp_sum]

/-- `C_p(S)` is at most the number of old events whose medium factor is
divisible by `p`. -/
theorem familyOldPrimeResidueClasses_card_le_incidence
    (old : Finset EscLeanChecks.SatEvent) (p : ℕ) :
    (familyOldPrimeResidueClasses old p).card ≤
      (old.filter (fun event => p ∣ event.dPlus)).card := by
  classical
  unfold familyOldPrimeResidueClasses
  exact Finset.card_image_le

/-- Exact double-counting identity for prime/event incidences in the exponent
of the increment Euler product. -/
theorem familyOldPrimeIncidence_sum_eq_event_primeDivisor_sum
    (old : Finset EscLeanChecks.SatEvent) (B : ℕ) :
    (∑ p ∈ EscLeanChecks.primeFinsetUpTo B,
      ((old.filter (fun event => p ∣ event.dPlus)).card : ℝ) / (p : ℝ)) =
      ∑ event ∈ old,
        ∑ p ∈ (EscLeanChecks.primeFinsetUpTo B).filter
          (fun p => p ∣ event.dPlus), (1 : ℝ) / (p : ℝ) := by
  classical
  calc
    (∑ p ∈ EscLeanChecks.primeFinsetUpTo B,
        ((old.filter (fun event => p ∣ event.dPlus)).card : ℝ) / (p : ℝ)) =
      ∑ p ∈ EscLeanChecks.primeFinsetUpTo B,
        ∑ event ∈ old,
          if p ∣ event.dPlus then (1 : ℝ) / (p : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.card_eq_sum_ones]
      push_cast
      rw [Finset.sum_div]
      rw [Finset.sum_filter]
    _ = ∑ event ∈ old,
        ∑ p ∈ EscLeanChecks.primeFinsetUpTo B,
          if p ∣ event.dPlus then (1 : ℝ) / (p : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ event ∈ old,
        ∑ p ∈ (EscLeanChecks.primeFinsetUpTo B).filter
          (fun p => p ∣ event.dPlus), (1 : ℝ) / (p : ℝ) := by
      apply Finset.sum_congr rfl
      intro event hevent
      rw [Finset.sum_filter]

/-- Prime-class exponent bounded by the corresponding event-prime incidence
sum, exactly as in the manuscript's prime-by-prime estimate. -/
theorem familyOldPrimeClass_exponent_le_event_primeDivisor_sum
    (old : Finset EscLeanChecks.SatEvent) (B : ℕ) :
    (∑ p ∈ EscLeanChecks.primeFinsetUpTo B,
      ((familyOldPrimeResidueClasses old p).card : ℝ) / (p : ℝ)) ≤
      ∑ event ∈ old,
        ∑ p ∈ (EscLeanChecks.primeFinsetUpTo B).filter
          (fun p => p ∣ event.dPlus), (1 : ℝ) / (p : ℝ) := by
  rw [← familyOldPrimeIncidence_sum_eq_event_primeDivisor_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpPrime : Nat.Prime p :=
    (Finset.mem_filter.mp hp).2
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  apply div_le_div_of_nonneg_right _ hpPos.le
  exact_mod_cast familyOldPrimeResidueClasses_card_le_incidence old p

/-- The truncated reciprocal prime-divisor sum of any event in the actual
family obeys the same roughness bound as its underlying `dplus`. -/
theorem familyEvent_primeDivisor_sum_le_YScale
    (P : Params) (X : ℝ) (Pz b q B : ℕ)
    (indices : Finset FamilyIndex) (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (hq2 : 2 ≤ q)
    (hsmall : ∀ p : ℕ, Nat.Prime p → p < q → p ∣ Pz)
    (event : EscLeanChecks.SatEvent) (hevent : event ∈ familyEvents indices) :
    (∑ p ∈ (EscLeanChecks.primeFinsetUpTo B).filter
        (fun p => p ∣ event.dPlus), (1 : ℝ) / (p : ℝ)) ≤
      (Real.log (YScale P X) / Real.log (q : ℝ)) / (q : ℝ) := by
  classical
  rcases Finset.mem_image.mp hevent with ⟨i, hi, rfl⟩
  calc
    (∑ p ∈ (EscLeanChecks.primeFinsetUpTo B).filter
        (fun p => p ∣ i.toSatEvent.dPlus), (1 : ℝ) / (p : ℝ)) ≤
        ∑ p ∈ i.dplus.primeFactors, (1 : ℝ) / (p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hpData := Finset.mem_filter.mp hp
        have hpPrime : Nat.Prime p :=
          (Finset.mem_filter.mp hpData.1).2
        exact (Nat.mem_primeFactors).mpr
          ⟨hpPrime, hpData.2, (hmem i hi).dplus_pos.ne'⟩
      · intro p _hp _hnot
        positivity
    _ ≤ (Real.log (YScale P X) / Real.log (q : ℝ)) / (q : ℝ) :=
      (hmem i hi).dplus_primeFactors_recip_sum_le_YScale hX hq2 hsmall

/-- Quantitative form of the manuscript's prime-class exponent estimate for
an old compatible set: it is at most its cardinality times the one-event
roughness bound. -/
theorem familyOldPrimeClass_exponent_le_card_mul_YScale
    (P : Params) (X : ℝ) (Pz b q B : ℕ)
    (indices : Finset FamilyIndex) (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (hq2 : 2 ≤ q)
    (hsmall : ∀ p : ℕ, Nat.Prime p → p < q → p ∣ Pz)
    (old : Finset EscLeanChecks.SatEvent) (hsub : old ⊆ familyEvents indices) :
    (∑ p ∈ EscLeanChecks.primeFinsetUpTo B,
      ((familyOldPrimeResidueClasses old p).card : ℝ) / (p : ℝ)) ≤
      (old.card : ℝ) *
        ((Real.log (YScale P X) / Real.log (q : ℝ)) / (q : ℝ)) := by
  calc
    (∑ p ∈ EscLeanChecks.primeFinsetUpTo B,
        ((familyOldPrimeResidueClasses old p).card : ℝ) / (p : ℝ)) ≤
      ∑ event ∈ old,
        ∑ p ∈ (EscLeanChecks.primeFinsetUpTo B).filter
          (fun p => p ∣ event.dPlus), (1 : ℝ) / (p : ℝ) :=
      familyOldPrimeClass_exponent_le_event_primeDivisor_sum old B
    _ ≤ ∑ _event ∈ old,
        ((Real.log (YScale P X) / Real.log (q : ℝ)) / (q : ℝ)) := by
      apply Finset.sum_le_sum
      intro event hevent
      exact familyEvent_primeDivisor_sum_le_YScale P X Pz b q B indices hX
        hmem hq2 hsmall event (hsub hevent)
    _ = (old.card : ℝ) *
        ((Real.log (YScale P X) / Real.log (q : ℝ)) / (q : ℝ)) := by
      simp

/-- Exact totient-divisor expansion of the concrete manuscript increment.
The upper cutoff is finite because every overlap gcd divides the new event's
medium factor, which is at most `floor X`. -/
theorem familyIncrementRat_eq_totient_divisorMass
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ familyEvents indices) :
    familyIncrementRat indices old =
      ∑ D ∈ Finset.Icc 1 ⌊X⌋₊, (Nat.totient D : ℚ) *
        familyIncrementDivisorMassRat indices old D := by
  classical
  unfold familyIncrementRat familyIncrementDivisorMassRat
  apply EscLeanChecks.weighted_sum_eq_totient_divisor_mass
  · intro event hext
    rw [familyIncrementG]
    apply Nat.gcd_pos_of_pos_right
    rw [familyCompatibleExtensions] at hext
    rcases Finset.mem_filter.mp hext with ⟨hevent, _hrest⟩
    rcases Finset.mem_image.mp hevent with ⟨i, hi, rfl⟩
    exact Nat.mul_pos (hmem i hi).dplus_pos (hmem i hi).p_prime.pos
  · intro event hext
    have hdiv : familyIncrementG old event ∣ event.dPlus := by
      simpa [familyIncrementG] using
        familyCompatibleExtension_gcd_dvd_dPlus
          P X Pz b indices hX hmem old hsub event hext
    rw [familyCompatibleExtensions] at hext
    rcases Finset.mem_filter.mp hext with ⟨hevent, _hrest⟩
    rcases Finset.mem_image.mp hevent with ⟨i, hi, rfl⟩
    exact (Nat.le_of_dvd (hmem i hi).dplus_pos hdiv).trans
      (FamilyStaticMem.dplus_le_floor_X hX (hmem i hi))

@[simp] theorem familyIncrementDivisorMassRat_one
    (indices : Finset FamilyIndex) (old : Finset EscLeanChecks.SatEvent) :
    familyIncrementDivisorMassRat indices old 1 =
      familyIncrementBaseMassRat indices old := by
  classical
  simp [familyIncrementDivisorMassRat, familyIncrementDivisorEvents,
    familyIncrementBaseMassRat]

/-- Exact partition of the `D | g(i;S)` mass by the represented residue
classes modulo `D`. -/
theorem familyIncrementDivisorMassRat_eq_sum_residueMass
    (indices : Finset FamilyIndex) (old : Finset EscLeanChecks.SatEvent)
    (D : ℕ) :
    familyIncrementDivisorMassRat indices old D =
      ∑ c ∈ familyIncrementResidueClasses indices old D,
        familyIncrementResidueMassRat indices old D c := by
  classical
  unfold familyIncrementDivisorMassRat familyIncrementResidueClasses
    familyIncrementResidueMassRat
  symm
  apply Finset.sum_fiberwise_of_maps_to
  intro event hevent
  exact Finset.mem_image.mpr ⟨event, hevent, rfl⟩

/-- A uniform event-tensor bound on each represented residue class bounds the
whole divisor-restricted mass by the number of represented classes. -/
theorem familyIncrementDivisorMassRat_le_card_mul_of_residueMass_le
    (indices : Finset FamilyIndex) (old : Finset EscLeanChecks.SatEvent)
    (D : ℕ) (M : ℚ)
    (hM : ∀ c ∈ familyIncrementResidueClasses indices old D,
      familyIncrementResidueMassRat indices old D c ≤ M) :
    familyIncrementDivisorMassRat indices old D ≤
      (familyIncrementResidueClasses indices old D).card * M := by
  rw [familyIncrementDivisorMassRat_eq_sum_residueMass]
  calc
    (∑ c ∈ familyIncrementResidueClasses indices old D,
        familyIncrementResidueMassRat indices old D c) ≤
      ∑ _c ∈ familyIncrementResidueClasses indices old D, M := by
        apply Finset.sum_le_sum
        intro c hc
        exact hM c hc
    _ = (familyIncrementResidueClasses indices old D).card * M := by
      simp

/-- Every increment residue fiber is a subfamily of the corresponding full
event-tensor residue fiber. -/
theorem familyIncrementResidueMassRat_le_familyResidueMassRat
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ familyEvents indices) (D c : ℕ) :
    familyIncrementResidueMassRat indices old D c ≤
      familyResidueMassRat indices D c := by
  classical
  unfold familyIncrementResidueMassRat familyIncrementDivisorEvents
    familyResidueMassRat
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro event hevent
    rcases Finset.mem_filter.mp hevent with ⟨hdivEvent, hresidue⟩
    rcases Finset.mem_filter.mp hdivEvent with ⟨hext, hdiv⟩
    have hgDvd : familyIncrementG old event ∣ event.dPlus := by
      simpa [familyIncrementG] using
        familyCompatibleExtension_gcd_dvd_dPlus
          P X Pz b indices hX hmem old hsub event hext
    have hDvd : D ∣ event.dPlus := hdiv.trans hgDvd
    rw [familyCompatibleExtensions] at hext
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hext).1, hDvd, hresidue⟩
  · intro event _hevent _hnot
    exact familyEventWeightRat_nonneg event

/-- The exact paper decomposition `A(S) = mass(extensions) + divisor tail`. -/
theorem familyIncrementRat_eq_base_add_tail
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ familyEvents indices) :
    familyIncrementRat indices old =
      familyIncrementBaseMassRat indices old +
        familyIncrementTailRat indices old ⌊X⌋₊ := by
  classical
  rw [familyIncrementRat_eq_totient_divisorMass
    P X Pz b indices hX hmem old hsub]
  have hBpos : 0 < ⌊X⌋₊ := Nat.floor_pos.mpr hX.le
  have hB : 1 ≤ ⌊X⌋₊ := by omega
  have hIcc : Finset.Icc 1 ⌊X⌋₊ =
      insert 1 (Finset.Icc 2 ⌊X⌋₊) := by
    ext D
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hIcc, Finset.sum_insert (by simp)]
  simp [familyIncrementTailRat]

/-- The compatible-extension base mass is at most the total mass of the exact
finite paper family. -/
theorem familyIncrementBaseMassRat_le_indexMassRat
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (old : Finset EscLeanChecks.SatEvent) :
    familyIncrementBaseMassRat indices old ≤ familyIndexMassRat indices := by
  classical
  rw [← familyEventMassRat_eq_familyIndexMassRat
    P X Pz b indices hX hmem]
  unfold familyIncrementBaseMassRat familyEventMassRat
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro event hext
    rw [familyCompatibleExtensions] at hext
    exact (Finset.mem_filter.mp hext).1
  · intro event _hevent _hnot
    exact familyEventWeightRat_nonneg event

/-- Once the finite divisor tail is bounded by `mu * epsilon`, the concrete
increment has the manuscript form `A(S) ≤ mu(1+epsilon)`. -/
theorem familyIncrementRat_le_mass_mul_one_add
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ familyEvents indices)
    (ε : ℚ)
    (htail : familyIncrementTailRat indices old ⌊X⌋₊ ≤
      familyIndexMassRat indices * ε) :
    familyIncrementRat indices old ≤
      familyIndexMassRat indices * (1 + ε) := by
  rw [familyIncrementRat_eq_base_add_tail
    P X Pz b indices hX hmem old hsub]
  calc
    familyIncrementBaseMassRat indices old +
        familyIncrementTailRat indices old ⌊X⌋₊ ≤
      familyIndexMassRat indices + familyIndexMassRat indices * ε :=
        add_le_add
          (familyIncrementBaseMassRat_le_indexMassRat
            P X Pz b indices hX hmem old)
          htail
    _ = familyIndexMassRat indices * (1 + ε) := by ring

/-- Divisor-by-divisor event-tensor bounds control the complete finite
increment tail.  This is the checked sum reversal and `phi(D)/D^2 ≤ 1/D`
step in the proof of `lem:increment`. -/
theorem familyIncrementTailRat_le_mass_mul_classTail
    (indices : Finset FamilyIndex) (old : Finset EscLeanChecks.SatEvent)
    (B : ℕ) (μ : ℚ) (C : ℕ → ℚ)
    (hμ : 0 ≤ μ)
    (hC : ∀ D ∈ Finset.Icc 2 B, 0 ≤ C D)
    (hmass : ∀ D ∈ Finset.Icc 2 B,
      familyIncrementDivisorMassRat indices old D ≤
        μ * C D / (D : ℚ) ^ 2) :
    familyIncrementTailRat indices old B ≤
      μ * ∑ D ∈ Finset.Icc 2 B, C D / (D : ℚ) := by
  unfold familyIncrementTailRat
  calc
    (∑ D ∈ Finset.Icc 2 B, (Nat.totient D : ℚ) *
        familyIncrementDivisorMassRat indices old D) ≤
      ∑ D ∈ Finset.Icc 2 B, μ * (C D / (D : ℚ)) := by
      apply Finset.sum_le_sum
      intro D hD
      have hDpos : 0 < D := by
        have := (Finset.mem_Icc.mp hD).1
        omega
      have hphi : 0 ≤ (Nat.totient D : ℚ) := by positivity
      have hμC : 0 ≤ μ * C D := mul_nonneg hμ (hC D hD)
      calc
        (Nat.totient D : ℚ) *
            familyIncrementDivisorMassRat indices old D ≤
          (Nat.totient D : ℚ) *
            (μ * C D / (D : ℚ) ^ 2) :=
              mul_le_mul_of_nonneg_left (hmass D hD) hphi
        _ = (μ * C D) *
            ((Nat.totient D : ℚ) / (D : ℚ) ^ 2) := by ring
        _ ≤ (μ * C D) * (1 / (D : ℚ)) :=
          mul_le_mul_of_nonneg_left
            (EscLeanChecks.totient_over_square_le_recip D hDpos) hμC
        _ = μ * (C D / (D : ℚ)) := by ring
    _ = μ * ∑ D ∈ Finset.Icc 2 B, C D / (D : ℚ) := by
      rw [Finset.mul_sum]

/-- Concrete `lem:increment` bound from the event-tensor estimate for every
divisor and the resulting finite class-count tail. -/
theorem familyIncrementRat_le_of_divisorMass
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ familyEvents indices)
    (C : ℕ → ℚ)
    (hC : ∀ D ∈ Finset.Icc 2 ⌊X⌋₊, 0 ≤ C D)
    (hmass : ∀ D ∈ Finset.Icc 2 ⌊X⌋₊,
      familyIncrementDivisorMassRat indices old D ≤
        familyIndexMassRat indices * C D / (D : ℚ) ^ 2) :
    familyIncrementRat indices old ≤
      familyIndexMassRat indices *
        (1 + ∑ D ∈ Finset.Icc 2 ⌊X⌋₊, C D / (D : ℚ)) := by
  apply familyIncrementRat_le_mass_mul_one_add
    P X Pz b indices hX hmem old hsub
  apply familyIncrementTailRat_le_mass_mul_classTail
  · unfold familyIndexMassRat
    apply Finset.sum_nonneg
    intro i _hi
    unfold FamilyIndex.wRat
    positivity
  · exact hC
  · exact hmass

/-- Paper-shaped increment bound after applying the event-tensor estimate to
each residue class actually represented modulo `D`.  The only remaining term
is the explicit finite class-count tail. -/
theorem familyIncrementRat_le_of_residueMass
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ familyEvents indices)
    (hresidue : ∀ D ∈ Finset.Icc 2 ⌊X⌋₊,
      ∀ c ∈ familyIncrementResidueClasses indices old D,
        familyIncrementResidueMassRat indices old D c ≤
          familyIndexMassRat indices / (D : ℚ) ^ 2) :
    familyIncrementRat indices old ≤
      familyIndexMassRat indices *
        (1 + ∑ D ∈ Finset.Icc 2 ⌊X⌋₊,
          ((familyIncrementResidueClasses indices old D).card : ℚ) /
            (D : ℚ)) := by
  apply familyIncrementRat_le_of_divisorMass
    P X Pz b indices hX hmem old hsub
    (fun D => (familyIncrementResidueClasses indices old D).card)
  · intro D _hD
    positivity
  · intro D hD
    calc
      familyIncrementDivisorMassRat indices old D ≤
          (familyIncrementResidueClasses indices old D).card *
            (familyIndexMassRat indices / (D : ℚ) ^ 2) :=
        familyIncrementDivisorMassRat_le_card_mul_of_residueMass_le
          indices old D _ (hresidue D hD)
      _ = familyIndexMassRat indices *
          (familyIncrementResidueClasses indices old D).card /
            (D : ℚ) ^ 2 := by ring

/-- Actual-family increment bound from the full event-tensor estimate
`B_{D,c} ≤ K mu / D^2`.  All compatibility, divisor expansion, residue-fiber
partitioning, and class multiplicity bookkeeping are internal to this theorem. -/
theorem familyIncrementRat_le_of_familyResidueMass
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ familyEvents indices)
    (K : ℚ) (hK : 0 ≤ K)
    (htensor : ∀ D ∈ Finset.Icc 2 ⌊X⌋₊,
      ∀ c ∈ familyIncrementResidueClasses indices old D,
        familyResidueMassRat indices D c ≤
          K * familyIndexMassRat indices / (D : ℚ) ^ 2) :
    familyIncrementRat indices old ≤
      familyIndexMassRat indices *
        (1 + ∑ D ∈ Finset.Icc 2 ⌊X⌋₊,
          (K * (familyIncrementResidueClasses indices old D).card) /
            (D : ℚ)) := by
  apply familyIncrementRat_le_of_divisorMass
    P X Pz b indices hX hmem old hsub
    (fun D => K * (familyIncrementResidueClasses indices old D).card)
  · intro D _hD
    positivity
  · intro D hD
    have hfiber : ∀ c ∈ familyIncrementResidueClasses indices old D,
        familyIncrementResidueMassRat indices old D c ≤
          K * familyIndexMassRat indices / (D : ℚ) ^ 2 := by
      intro c hc
      exact (familyIncrementResidueMassRat_le_familyResidueMassRat
        P X Pz b indices hX hmem old hsub D c).trans (htensor D hD c hc)
    calc
      familyIncrementDivisorMassRat indices old D ≤
          (familyIncrementResidueClasses indices old D).card *
            (K * familyIndexMassRat indices / (D : ℚ) ^ 2) :=
        familyIncrementDivisorMassRat_le_card_mul_of_residueMass_le
          indices old D _ hfiber
      _ = familyIndexMassRat indices *
          (K * (familyIncrementResidueClasses indices old D).card) /
            (D : ℚ) ^ 2 := by ring

/-- The event-tensor increment bound with the manuscript's multiplicative
class count `C_D(S) = prod_{ell|D} C_ell(S)` exposed explicitly. -/
theorem familyIncrementRat_le_of_familyResidueMass_prod_classes
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ familyEvents indices)
    (K : ℚ) (hK : 0 ≤ K)
    (htensor : ∀ D ∈ Finset.Icc 2 ⌊X⌋₊,
      ∀ c ∈ familyIncrementResidueClasses indices old D,
        familyResidueMassRat indices D c ≤
          K * familyIndexMassRat indices / (D : ℚ) ^ 2) :
    familyIncrementRat indices old ≤
      familyIndexMassRat indices *
        (1 + ∑ D ∈ Finset.Icc 2 ⌊X⌋₊,
          (K * (∏ ell ∈ D.primeFactors,
            (familyOldPrimeResidueClasses old ell).card : ℚ)) / (D : ℚ)) := by
  have hfirst := familyIncrementRat_le_of_familyResidueMass
    P X Pz b indices hX hmem old hsub K hK htensor
  apply hfirst.trans
  have hmassNonneg : 0 ≤ familyIndexMassRat indices := by
    unfold familyIndexMassRat
    apply Finset.sum_nonneg
    intro i _hi
    unfold FamilyIndex.wRat
    positivity
  apply mul_le_mul_of_nonneg_left _ hmassNonneg
  gcongr with D hD
  have hcard := familyIncrementResidueClasses_card_le_prod_oldPrimeClasses_auto
    P X Pz b indices hX hmem old hsub D
  have hcardQ :
      ((familyIncrementResidueClasses indices old D).card : ℚ) ≤
        (∏ ell ∈ D.primeFactors,
          (familyOldPrimeResidueClasses old ell).card : ℚ) := by
    exact_mod_cast hcard
  exact hcardQ

/-- Supported version of the multiplicative class-count bound.  Unlike the
raw product majorant, this retains the fact that nonsquarefree or even `D`
have empty increment carrier. -/
theorem familyIncrementRat_le_of_familyResidueMass_classProduct
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ familyEvents indices)
    (K : ℚ) (hK : 0 ≤ K)
    (htensor : ∀ D ∈ Finset.Icc 2 ⌊X⌋₊,
      ∀ c ∈ familyIncrementResidueClasses indices old D,
        familyResidueMassRat indices D c ≤
          K * familyIndexMassRat indices / (D : ℚ) ^ 2) :
    familyIncrementRat indices old ≤
      familyIndexMassRat indices *
        (1 + ∑ D ∈ Finset.Icc 2 ⌊X⌋₊,
          (K * familyIncrementClassProductRat old D) / (D : ℚ)) := by
  have hfirst := familyIncrementRat_le_of_familyResidueMass
    P X Pz b indices hX hmem old hsub K hK htensor
  apply hfirst.trans
  have hmassNonneg : 0 ≤ familyIndexMassRat indices := by
    unfold familyIndexMassRat
    apply Finset.sum_nonneg
    intro i _hi
    unfold FamilyIndex.wRat
    positivity
  apply mul_le_mul_of_nonneg_left _ hmassNonneg
  gcongr with D hD
  exact familyIncrementResidueClasses_card_le_classProductRat
    P X Pz b indices hX hmem old hsub D

/-- The actual reciprocal-lcm Brun coefficients satisfy the manuscript's
factorial bound once the concrete family residue tensor and prime-class Euler
tail are bounded uniformly along compatible chains. -/
theorem familyCompatibleLcmMassRat_le_mass_one_add_pow_of_residueTensor
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (K ε : ℚ) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (htensor : ∀ r : ℕ, 1 ≤ r →
      ∀ old ∈ familyCompatibleSubsetsOfCard indices (r - 1),
      ∀ D ∈ Finset.Icc 2 ⌊X⌋₊,
      ∀ c ∈ familyIncrementResidueClasses indices old D,
        familyResidueMassRat indices D c ≤
          K * familyIndexMassRat indices / (D : ℚ) ^ 2)
    (htail : ∀ r : ℕ, 1 ≤ r →
      ∀ old ∈ familyCompatibleSubsetsOfCard indices (r - 1),
        (∑ D ∈ Finset.Icc 2 ⌊X⌋₊,
          (K * familyIncrementClassProductRat old D) / (D : ℚ)) ≤ ε) :
    ∀ r : ℕ, familyCompatibleLcmMassRat indices r ≤
      (familyIndexMassRat indices * (1 + ε)) ^ r /
        (Nat.factorial r : ℚ) := by
  classical
  have hmassNonneg : 0 ≤ familyIndexMassRat indices := by
    unfold familyIndexMassRat
    apply Finset.sum_nonneg
    intro i _hi
    unfold FamilyIndex.wRat
    positivity
  apply familyCompatibleLcmMassRat_le_pow_div_factorial_of_increment_le
    P X Pz b indices hmem (familyIndexMassRat indices * (1 + ε))
  · exact mul_nonneg hmassNonneg (by linarith)
  · intro r hr old hold
    rw [familyCompatibleSubsetsOfCard] at hold
    have hsub : old ⊆ familyEvents indices :=
      (Finset.mem_powersetCard.mp (Finset.mem_of_mem_filter old hold)).1
    have hincrement :=
      familyIncrementRat_le_of_familyResidueMass_classProduct
        P X Pz b indices hX hmem old hsub K hK
          (htensor r hr old (by
            rw [familyCompatibleSubsetsOfCard]
            exact hold))
    exact hincrement.trans (mul_le_mul_of_nonneg_left
      (add_le_add_left (htail r hr old (by
        rw [familyCompatibleSubsetsOfCard]
        exact hold)) 1) hmassNonneg)

/-- The full conductor of a paper-family index stays below the ambient scale:
`Q = dminus * dplus * p ≤ X^sigma * X^(1-sigma) = X`. -/
theorem FamilyStaticMem.Q_le_X
    {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (hX : 1 < X) (hmem : FamilyStaticMem P X Pz b i) :
    (i.Q : ℝ) ≤ X := by
  have hXpos : 0 < X := lt_trans zero_lt_one hX
  have hQ_le : (i.Q : ℝ) ≤ YScale P X * X ^ (1 - P.σ) := by
    rw [FamilyIndex.Q_eq, Nat.cast_mul, Nat.cast_mul]
    have hp_nonneg : 0 ≤ (i.p : ℝ) := by positivity
    have hY_nonneg : 0 ≤ YScale P X := Real.rpow_nonneg hXpos.le _
    exact mul_le_mul hmem.dd_le_Y hmem.p_le hp_nonneg hY_nonneg
  calc
    (i.Q : ℝ) ≤ YScale P X * X ^ (1 - P.σ) := hQ_le
    _ = X ^ P.σ * X ^ (1 - P.σ) := rfl
    _ = X ^ (P.σ + (1 - P.σ)) := by
      rw [← Real.rpow_add hXpos]
    _ = X := by
      rw [show P.σ + (1 - P.σ) = (1 : ℝ) by ring, Real.rpow_one]

/-- The residual modulus `q = dplus * p` is bounded by the full conductor and
therefore by `X`, as required by the finite-interval approximation. -/
theorem FamilyStaticMem.q_le_X
    {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (hX : 1 < X) (hmem : FamilyStaticMem P X Pz b i) :
    (i.q : ℝ) ≤ X := by
  have hq_le_Q : i.q ≤ i.Q := by
    simpa [FamilyIndex.q_eq, FamilyIndex.Q_eq, Nat.mul_assoc] using
      Nat.mul_le_mul_right i.p (Nat.le_mul_of_pos_left i.dplus hmem.dminus_pos)
  exact le_trans (by exact_mod_cast hq_le_Q) (hmem.Q_le_X hX)

/-- Every actual event weight absorbs one endpoint-counting error after
multiplication by the natural scale: `1 ≤ floor(X) / q`. -/
theorem one_le_floor_scale_mul_familyEventWeightRat
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    {event : EscLeanChecks.SatEvent}
    (hevent : event ∈ familyEvents indices) :
    (1 : ℚ) ≤ (⌊X⌋₊ : ℚ) * familyEventWeightRat event := by
  rw [familyEvents] at hevent
  rcases Finset.mem_image.mp hevent with ⟨i, hi, rfl⟩
  have hqPos : 0 < i.q :=
    Nat.mul_pos (hmem i hi).dplus_pos (hmem i hi).p_prime.pos
  have hqPosRat : 0 < (i.q : ℚ) := by exact_mod_cast hqPos
  have hqFloor : i.q ≤ ⌊X⌋₊ :=
    Nat.le_floor ((hmem i hi).q_le_X hX)
  have hqFloorRat : (i.q : ℚ) ≤ (⌊X⌋₊ : ℚ) := by
    exact_mod_cast hqFloor
  change (1 : ℚ) ≤ (⌊X⌋₊ : ℚ) * ((1 : ℚ) / (i.q : ℚ))
  rw [mul_one_div]
  exact (le_div_iff₀ hqPosRat).2 (by simpa using hqFloorRat)

/-- Rankwise endpoint-error bound for the actual paper family.  The number of
rank-`r` subsets is at most `floor(X)^r` times the true elementary symmetric
coefficient `F_r` of the event weights. -/
theorem familyEvents_powersetCard_card_le_floor_scale_pow_elemSymm
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (r : ℕ) :
    ((familyEvents indices).powersetCard r).card ≤
      (⌊X⌋₊ : ℚ) ^ r *
        EscLeanChecks.elemSymmList (familyEventWeightsRat indices) r := by
  rw [familyEventWeightsRat_elemSymm_eq_powersetCard_sum]
  calc
    (((familyEvents indices).powersetCard r).card : ℚ) =
        ∑ events ∈ (familyEvents indices).powersetCard r, (1 : ℚ) := by
          simp
    _ ≤ ∑ events ∈ (familyEvents indices).powersetCard r,
        (⌊X⌋₊ : ℚ) ^ r *
          ∏ event ∈ events, familyEventWeightRat event := by
      apply Finset.sum_le_sum
      intro events hevents
      have hsub : events ⊆ familyEvents indices :=
        (Finset.mem_powersetCard.mp hevents).1
      have hcard : events.card = r :=
        (Finset.mem_powersetCard.mp hevents).2
      calc
        (1 : ℚ) = ∏ event ∈ events, (1 : ℚ) := by simp
        _ ≤ ∏ event ∈ events,
            (⌊X⌋₊ : ℚ) * familyEventWeightRat event := by
          apply Finset.prod_le_prod
          · intro _event _hevent
            norm_num
          · intro event hevent
            exact one_le_floor_scale_mul_familyEventWeightRat
              P X Pz b indices hX hmem (hsub hevent)
        _ = (⌊X⌋₊ : ℚ) ^ events.card *
            ∏ event ∈ events, familyEventWeightRat event := by
          rw [Finset.prod_mul_distrib]
          simp
        _ = (⌊X⌋₊ : ℚ) ^ r *
            ∏ event ∈ events, familyEventWeightRat event := by rw [hcard]
    _ = (⌊X⌋₊ : ℚ) ^ r *
        ∑ events ∈ (familyEvents indices).powersetCard r,
          ∏ event ∈ events, familyEventWeightRat event := by
      rw [Finset.mul_sum]

/-- The small factor is coprime to the residual modulus once the selected
prime is above that small factor.  This is the condition used in the paper;
it does not require the full roughness modulus to be below the selected prime. -/
theorem FamilyStaticMem.dminus_coprime_residual_of_lt
    {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (hdminus_lt_p : i.dminus < i.p)
    (hmem : FamilyStaticMem P X Pz b i) :
    Nat.Coprime i.dminus (i.dplus * i.p) := by
  have hcop_dplus : Nat.Coprime i.dminus i.dplus :=
    Nat.Coprime.coprime_dvd_left hmem.dminus_dvd_Pz
      hmem.dplus_coprime_Pz.symm
  have hnot : ¬ i.p ∣ i.dminus :=
    Nat.not_dvd_of_pos_of_lt hmem.dminus_pos hdminus_lt_p
  have hcop_p : Nat.Coprime i.dminus i.p :=
    ((hmem.p_prime.coprime_iff_not_dvd).2 hnot).symm
  exact Nat.Coprime.mul_right hcop_dplus hcop_p

/-- A modulus bound is a sufficient, but stronger than necessary, way to
obtain the small-factor separation used by
`FamilyStaticMem.dminus_coprime_residual_of_lt`. -/
theorem FamilyStaticMem.dminus_coprime_residual
    {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (hPz : 0 < Pz) (hlarge : Pz < i.p)
    (hmem : FamilyStaticMem P X Pz b i) :
    Nat.Coprime i.dminus (i.dplus * i.p) := by
  apply hmem.dminus_coprime_residual_of_lt
  exact lt_of_le_of_lt (Nat.le_of_dvd hPz hmem.dminus_dvd_Pz) hlarge

/-- Static paper-family membership supplies the exact certificate expected by
the finite Bonferroni layer.  The only external scale fact needed here is that
the conditioned modulus lies below the selected large prime. -/
theorem FamilyStaticMem.toSatEvent_certificate
    {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (hX : 1 < X) (hPz : 0 < Pz) (hlarge : Pz < i.p)
    (hmem : FamilyStaticMem P X Pz b i) :
    ∃ r s : ℕ,
      0 < r ∧ 0 < s ∧ i.toSatEvent.e = r * s ^ 2 ∧
      Nat.Coprime i.toSatEvent.dMinus
        (i.toSatEvent.dPlus * i.toSatEvent.p) ∧
      i.toSatEvent.dMinus ∣ Pz ∧
      b + 4 * i.toSatEvent.e ≡ 0 [MOD i.toSatEvent.dMinus] ∧
      4 * (r * s) ∣
        i.toSatEvent.dMinus * (i.toSatEvent.dPlus * i.toSatEvent.p) + 1 := by
  refine ⟨i.E.r, i.E.s, hmem.r_pos hX, ?_, rfl, ?_, hmem.dminus_dvd_Pz,
    hmem.base_cong, ?_⟩
  · exact lt_of_lt_of_le Nat.zero_lt_one hmem.s_pos
  · exact hmem.dminus_coprime_residual hPz hlarge
  · simpa [FamilyIndex.Q, FamilyIndex.rho, Nat.mul_assoc] using hmem.sat_cong

/-- Static paper-family membership supplies the finite-event certificate as
soon as its small divisor is below the selected prime. -/
theorem FamilyStaticMem.toSatEvent_certificate_of_dminus_lt_p
    {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (hX : 1 < X) (hdminus_lt_p : i.dminus < i.p)
    (hmem : FamilyStaticMem P X Pz b i) :
    ∃ r s : ℕ,
      0 < r ∧ 0 < s ∧ i.toSatEvent.e = r * s ^ 2 ∧
      Nat.Coprime i.toSatEvent.dMinus
        (i.toSatEvent.dPlus * i.toSatEvent.p) ∧
      i.toSatEvent.dMinus ∣ Pz ∧
      b + 4 * i.toSatEvent.e ≡ 0 [MOD i.toSatEvent.dMinus] ∧
      4 * (r * s) ∣
        i.toSatEvent.dMinus * (i.toSatEvent.dPlus * i.toSatEvent.p) + 1 := by
  refine ⟨i.E.r, i.E.s, hmem.r_pos hX, ?_, rfl, ?_, hmem.dminus_dvd_Pz,
    hmem.base_cong, ?_⟩
  · exact lt_of_lt_of_le Nat.zero_lt_one hmem.s_pos
  · exact hmem.dminus_coprime_residual_of_lt hdminus_lt_p
  · simpa [FamilyIndex.Q, FamilyIndex.rho, Nat.mul_assoc] using hmem.sat_cong

/-- Every event in the finite image of paper indices has the required divisor-fan
certificate, without a separate certificate hypothesis. -/
theorem familyEvents_certificate
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X) (hPz : 0 < Pz)
    (hlarge : ∀ i ∈ indices, Pz < i.p)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i) :
    ∀ event ∈ familyEvents indices,
      ∃ r s : ℕ,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ Pz ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1 := by
  intro event hevent
  rcases Finset.mem_image.mp hevent with ⟨i, hi, rfl⟩
  exact FamilyStaticMem.toSatEvent_certificate hX hPz (hlarge i hi) (hmem i hi)

/-- Every event in the finite image has the required certificate when the
small divisor of each family index lies below its selected prime. -/
theorem familyEvents_certificate_of_dminus_lt_p
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hdminus_lt_p : ∀ i ∈ indices, i.dminus < i.p)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i) :
    ∀ event ∈ familyEvents indices,
      ∃ r s : ℕ,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ Pz ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1 := by
  intro event hevent
  rcases Finset.mem_image.mp hevent with ⟨i, hi, rfl⟩
  exact FamilyStaticMem.toSatEvent_certificate_of_dminus_lt_p
    hX (hdminus_lt_p i hi) (hmem i hi)

/-- The residual congruence modulus of every event in a concrete paper family
is positive. -/
theorem familyEvents_residualModulus_pos
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i) :
    ∀ event ∈ familyEvents indices,
      0 < EscLeanChecks.conditionalModulus event.dPlus event.p := by
  intro event hevent
  rcases Finset.mem_image.mp hevent with ⟨i, hi, rfl⟩
  exact Nat.mul_pos (hmem i hi).dplus_pos (hmem i hi).p_prime.pos

/-- The number of compatible rank-`r` subsets is bounded by
`floor(X)^r F_r`.  This is the endpoint-error estimate used in the
finite-interval approximation lemma, now for the exact paper coefficient
`familyCompatibleLcmMassRat`. -/
theorem familyCompatibleSubsets_card_le_floor_scale_pow_lcmMass
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (r : ℕ) :
    ((familyCompatibleSubsetsOfCard indices r).card : ℚ) ≤
      (⌊X⌋₊ : ℚ) ^ r * familyCompatibleLcmMassRat indices r := by
  classical
  rw [familyCompatibleLcmMassRat]
  calc
    ((familyCompatibleSubsetsOfCard indices r).card : ℚ) =
        ∑ events ∈ familyCompatibleSubsetsOfCard indices r, (1 : ℚ) := by
          simp
    _ ≤ ∑ events ∈ familyCompatibleSubsetsOfCard indices r,
        (⌊X⌋₊ : ℚ) ^ r *
          ((1 : ℚ) / (EscLeanChecks.congruenceLcm
            (EscLeanChecks.satEventResidualHitRows events.toList) : ℚ)) := by
      apply Finset.sum_le_sum
      intro events hevents
      have hpowerset := (Finset.mem_filter.mp hevents).1
      have hsub : events ⊆ familyEvents indices :=
        (Finset.mem_powersetCard.mp hpowerset).1
      have hcard : events.card = r :=
        (Finset.mem_powersetCard.mp hpowerset).2
      have hqPos : ∀ event ∈ events,
          0 < EscLeanChecks.conditionalModulus event.dPlus event.p := by
        intro event hevent
        exact familyEvents_residualModulus_pos P X Pz b indices hmem event
          (hsub hevent)
      have hprodPos : 0 < ∏ event ∈ events,
          EscLeanChecks.conditionalModulus event.dPlus event.p :=
        Finset.prod_pos hqPos
      have hLdvd : EscLeanChecks.congruenceLcm
          (EscLeanChecks.satEventResidualHitRows events.toList) ∣
            ∏ event ∈ events,
              EscLeanChecks.conditionalModulus event.dPlus event.p := by
        simpa [EscLeanChecks.satEventResidualHitRows,
          EscLeanChecks.satEventResidualHitRow] using
          congruenceLcm_dvd_moduli_product
            (EscLeanChecks.satEventResidualHitRows events.toList)
      have hLleProd : EscLeanChecks.congruenceLcm
          (EscLeanChecks.satEventResidualHitRows events.toList) ≤
            ∏ event ∈ events,
              EscLeanChecks.conditionalModulus event.dPlus event.p :=
        Nat.le_of_dvd hprodPos hLdvd
      have hprodLe : (∏ event ∈ events,
          EscLeanChecks.conditionalModulus event.dPlus event.p) ≤
          ⌊X⌋₊ ^ events.card := by
        calc
          (∏ event ∈ events,
              EscLeanChecks.conditionalModulus event.dPlus event.p) ≤
              ∏ _event ∈ events, ⌊X⌋₊ := by
            apply Finset.prod_le_prod'
            intro event hevent
            rcases Finset.mem_image.mp (hsub hevent) with ⟨i, hi, rfl⟩
            exact Nat.le_floor ((hmem i hi).q_le_X hX)
          _ = ⌊X⌋₊ ^ events.card := by simp
      have hLle : EscLeanChecks.congruenceLcm
          (EscLeanChecks.satEventResidualHitRows events.toList) ≤ ⌊X⌋₊ ^ r := by
        rw [← hcard]
        exact hLleProd.trans hprodLe
      have hLPos : 0 < EscLeanChecks.congruenceLcm
          (EscLeanChecks.satEventResidualHitRows events.toList) := by
        apply EscLeanChecks.congruenceLcm_pos_of_rows_positive
        intro row hrow
        rcases List.mem_map.mp hrow with ⟨event, hevent, rfl⟩
        exact hqPos event (by simpa using hevent)
      have hLPosRat : 0 < (EscLeanChecks.congruenceLcm
          (EscLeanChecks.satEventResidualHitRows events.toList) : ℚ) := by
        exact_mod_cast hLPos
      have hLleRat : (EscLeanChecks.congruenceLcm
          (EscLeanChecks.satEventResidualHitRows events.toList) : ℚ) ≤
          (⌊X⌋₊ : ℚ) ^ r := by
        exact_mod_cast hLle
      rw [mul_one_div]
      exact (le_div_iff₀ hLPosRat).2 (by simpa using hLleRat)
    _ = (⌊X⌋₊ : ℚ) ^ r * familyCompatibleLcmMassRat indices r := by
      simp [familyCompatibleLcmMassRat, Finset.mul_sum]

/-- A subset which is not pairwise compatible has no common residual hit in
any conditioned base class. -/
theorem baseFamilyCommonHitCount_eq_zero_of_not_compatible
    (N Pz b : ℕ) (events : Finset EscLeanChecks.SatEvent)
    (hnot : ¬ ∀ event ∈ events, ∀ other ∈ events,
      event ≠ other → EscLeanChecks.satEventCompatible event other) :
    EscLeanChecks.baseSatEventCommonHitCountUpTo N Pz b events = 0 := by
  apply EscLeanChecks.baseSatEventCommonHitCountUpTo_eq_zero_of_no_common_base_hit
  intro hhit
  rcases hhit with ⟨x, _hxbase, hxhit⟩
  apply hnot
  intro event hevent other hother _hne
  exact EscLeanChecks.satEventCompatible_of_common_hit x event other
    (hxhit event hevent) (hxhit other hother)

/-- The rank count is supported exactly on compatible subsets. -/
theorem familyRankCommonHitCountRat_eq_sum_compatible
    (N Pz b : ℕ) (indices : Finset FamilyIndex) (r : ℕ) :
    familyRankCommonHitCountRat N Pz b indices r =
      ∑ events ∈ familyCompatibleSubsetsOfCard indices r,
        (EscLeanChecks.baseSatEventCommonHitCountUpTo N Pz b events : ℚ) := by
  classical
  unfold familyRankCommonHitCountRat familyCompatibleSubsetsOfCard
  rw [Nat.cast_sum]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro events hevents hnotmem
  have hnotcompat : ¬ ∀ event ∈ events, ∀ other ∈ events,
      event ≠ other → EscLeanChecks.satEventCompatible event other := by
    intro hcompat
    exact hnotmem (Finset.mem_filter.mpr ⟨hevents, hcompat⟩)
  rw [baseFamilyCommonHitCount_eq_zero_of_not_compatible
    N Pz b events hnotcompat]
  norm_num

/-- Lower half of the finite-interval approximation for the actual rank count:
`(N/Pz) F_r - floor(X)^r F_r ≤ C_r^(b)(N)`.

Pairwise event compatibility is converted to compatibility of the residual
CRT rows, base coprimality adds the conditioned row, and the rational lower
endpoint estimate is then summed over the exact compatible-lcm carrier. -/
theorem familyRankCommonHitCountRat_main_sub_endpoint_le
    (P : Params) (X : ℝ) (N Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X) (hPz : 0 < Pz)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (hpCop : ∀ event ∈ familyEvents indices, Nat.Coprime Pz event.p)
    (r : ℕ) :
    (N : ℚ) / (Pz : ℚ) * familyCompatibleLcmMassRat indices r -
        (⌊X⌋₊ : ℚ) ^ r * familyCompatibleLcmMassRat indices r ≤
      familyRankCommonHitCountRat N Pz b indices r := by
  classical
  rw [familyRankCommonHitCountRat_eq_sum_compatible]
  have hpoint : ∀ events ∈ familyCompatibleSubsetsOfCard indices r,
      (N : ℚ) / (Pz : ℚ) *
          ((1 : ℚ) / (EscLeanChecks.congruenceLcm
            (EscLeanChecks.satEventResidualHitRows events.toList) : ℚ)) - 1 ≤
        (EscLeanChecks.baseSatEventCommonHitCountUpTo N Pz b events : ℚ) := by
    intro events hevents
    have hpowerset : events ∈ (familyEvents indices).powersetCard r :=
      (Finset.mem_filter.mp hevents).1
    have hcompat := (Finset.mem_filter.mp hevents).2
    have hsub : events ⊆ familyEvents indices :=
      (Finset.mem_powersetCard.mp hpowerset).1
    have hadm : ∀ event ∈ events,
        EscLeanChecks.satEventAdmissibleFor Pz (familyRhoOf indices) event := by
      intro event hevent
      exact familyEvents_admissibleFor P X Pz b indices hX hmem event
        (hsub hevent)
    have hpCop' : ∀ event ∈ events, Nat.Coprime Pz event.p := by
      intro event hevent
      exact hpCop event (hsub hevent)
    let rows := EscLeanChecks.satEventResidualHitRowsFinset events
    have hpos : ∀ row ∈ rows, 0 < row.1 :=
      EscLeanChecks.satEventResidualHitRowsFinset_moduliPositive_of_admissibleFor
        Pz (familyRhoOf indices) events hadm
    have hposList : EscLeanChecks.congruenceRowsModuliPositive rows.toList :=
      EscLeanChecks.congruenceRowsModuliPositive_toList_of_forall_mem rows hpos
    have hcopRows : ∀ row ∈ rows, Nat.Coprime Pz row.1 :=
      EscLeanChecks.satEventResidualHitRowsFinset_base_coprime_of_admissibleFor
        Pz (familyRhoOf indices) events hadm hpCop'
    have hrowsCompat : EscLeanChecks.congruenceRowsPairwiseCompatible rows.toList := by
      intro rowA hrowA rowB hrowB
      have hrowAFin : rowA ∈ rows := by simpa using hrowA
      have hrowBFin : rowB ∈ rows := by simpa using hrowB
      rcases Finset.mem_image.mp hrowAFin with ⟨event, hevent, rfl⟩
      rcases Finset.mem_image.mp hrowBFin with ⟨other, hother, rfl⟩
      have heventAdm : EscLeanChecks.satEventAdmissible Pz
          (familyRhoOf indices event.e) event := by
        simpa [EscLeanChecks.satEventAdmissibleFor] using hadm event hevent
      have hotherAdm : EscLeanChecks.satEventAdmissible Pz
          (familyRhoOf indices other.e) other := by
        simpa [EscLeanChecks.satEventAdmissibleFor] using hadm other hother
      apply EscLeanChecks.satEventResidualHitRow_compatible_of_satEventCompatible
      · exact Nat.mul_pos heventAdm.2.2.2.2.2.1 heventAdm.1.pos
      · exact Nat.mul_pos hotherAdm.2.2.2.2.2.1 hotherAdm.1.pos
      · by_cases heq : event = other
        · subst heq
          exact Nat.ModEq.refl _
        · exact hcompat event hevent other hother heq
    have hbaseCompat : EscLeanChecks.congruenceRowsPairwiseCompatible
        ((Pz, b) :: rows.toList) := by
      intro rowA hrowA rowB hrowB
      rcases List.mem_cons.mp hrowA with hA | hA
      · subst hA
        rcases List.mem_cons.mp hrowB with hB | hB
        · subst hB
          exact Nat.ModEq.refl _
        · have hrowBFin : rowB ∈ rows := by simpa using hB
          have hc := hcopRows rowB hrowBFin
          unfold EscLeanChecks.residueCompatible
          simp only
          rw [show Nat.gcd Pz rowB.1 = 1 from hc.gcd_eq_one]
          exact Nat.modEq_one
      · rcases List.mem_cons.mp hrowB with hB | hB
        · subst hB
          have hrowAFin : rowA ∈ rows := by simpa using hA
          have hc := hcopRows rowA hrowAFin
          unfold EscLeanChecks.residueCompatible
          simp only
          rw [show Nat.gcd rowA.1 Pz = 1 from hc.symm.gcd_eq_one]
          exact Nat.modEq_one
        · exact hrowsCompat rowA hA rowB hB
    rcases EscLeanChecks.baseResidualRows_solution_exists_of_pairwiseCompatible
        Pz b rows.toList hPz hposList hbaseCompat with ⟨x, hxbase, hxrows⟩
    have hxhit : ∀ event ∈ events, EscLeanChecks.satEventHit x event := by
      intro event hevent
      have hrowFin : EscLeanChecks.satEventResidualHitRow event ∈ rows :=
        Finset.mem_image.mpr ⟨event, hevent, rfl⟩
      have hrow : EscLeanChecks.satEventResidualHitRow event ∈ rows.toList := by
        simpa using hrowFin
      have heventAdm : EscLeanChecks.satEventAdmissible Pz
          (familyRhoOf indices event.e) event := by
        simpa [EscLeanChecks.satEventAdmissibleFor] using hadm event hevent
      have hq : 0 < EscLeanChecks.conditionalModulus event.dPlus event.p :=
        Nat.mul_pos heventAdm.2.2.2.2.2.1 heventAdm.1.pos
      exact (EscLeanChecks.satEventHit_iff_modEq_residualHitRow x event hq).1
        (hxrows (EscLeanChecks.satEventResidualHitRow event) hrow)
    have hlower :=
      EscLeanChecks.baseSatEventCommonHitCountUpTo_rat_lower_of_common_hit_admissibleFor
        N Pz b x (familyRhoOf indices) events hPz hadm hpCop' hxbase hxhit
    have hL : EscLeanChecks.congruenceLcm rows.toList =
        EscLeanChecks.congruenceLcm
          (EscLeanChecks.satEventResidualHitRows events.toList) :=
      EscLeanChecks.congruenceLcm_satEventResidualHitRowsFinset_toList_eq events
    have hPzRat : (Pz : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hPz)
    have hLPos : 0 < EscLeanChecks.congruenceLcm rows.toList :=
      EscLeanChecks.congruenceLcm_pos_of_rows_positive _ hposList
    have hLRat : (EscLeanChecks.congruenceLcm rows.toList : ℚ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hLPos)
    calc
      (N : ℚ) / (Pz : ℚ) *
          ((1 : ℚ) / (EscLeanChecks.congruenceLcm
            (EscLeanChecks.satEventResidualHitRows events.toList) : ℚ)) - 1 =
          (N : ℚ) / ((Pz * EscLeanChecks.congruenceLcm rows.toList : ℕ) : ℚ) - 1 := by
        rw [← hL]
        push_cast
        field_simp [hPzRat, hLRat]
      _ ≤ (EscLeanChecks.baseSatEventCommonHitCountUpTo N Pz b events : ℚ) :=
        hlower
  have hsumLower :
      ∑ events ∈ familyCompatibleSubsetsOfCard indices r,
          ((N : ℚ) / (Pz : ℚ) *
            ((1 : ℚ) / (EscLeanChecks.congruenceLcm
              (EscLeanChecks.satEventResidualHitRows events.toList) : ℚ)) - 1) ≤
        ∑ events ∈ familyCompatibleSubsetsOfCard indices r,
          (EscLeanChecks.baseSatEventCommonHitCountUpTo N Pz b events : ℚ) :=
    Finset.sum_le_sum hpoint
  have hcard := familyCompatibleSubsets_card_le_floor_scale_pow_lcmMass
    P X Pz b indices hX hmem r
  calc
    (N : ℚ) / (Pz : ℚ) * familyCompatibleLcmMassRat indices r -
        (⌊X⌋₊ : ℚ) ^ r * familyCompatibleLcmMassRat indices r ≤
      (N : ℚ) / (Pz : ℚ) * familyCompatibleLcmMassRat indices r -
        (familyCompatibleSubsetsOfCard indices r).card := by linarith
    _ = ∑ events ∈ familyCompatibleSubsetsOfCard indices r,
          ((N : ℚ) / (Pz : ℚ) *
            ((1 : ℚ) / (EscLeanChecks.congruenceLcm
              (EscLeanChecks.satEventResidualHitRows events.toList) : ℚ)) - 1) := by
      simp [familyCompatibleLcmMassRat, Finset.mul_sum,
        Finset.sum_sub_distrib]
    _ ≤ ∑ events ∈ familyCompatibleSubsetsOfCard indices r,
          (EscLeanChecks.baseSatEventCommonHitCountUpTo N Pz b events : ℚ) :=
      hsumLower

/-- One-sided finite-interval approximation for the actual rank count:
`C_r^(b)(N) ≤ (N/Pz) F_r + floor(X)^r F_r`.

This proves the direction consumed by the upper-bound transfer.  Incompatible
subsets contribute zero, compatible subsets contribute their reciprocal-lcm
density plus one endpoint error, and the preceding cardinality theorem sums
those endpoint errors. -/
theorem familyRankCommonHitCountRat_le_main_add_endpoint
    (P : Params) (X : ℝ) (N Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X) (hPz : 0 < Pz)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (hpCop : ∀ event ∈ familyEvents indices, Nat.Coprime Pz event.p)
    (r : ℕ) :
    familyRankCommonHitCountRat N Pz b indices r ≤
      (N : ℚ) / (Pz : ℚ) * familyCompatibleLcmMassRat indices r +
        (⌊X⌋₊ : ℚ) ^ r * familyCompatibleLcmMassRat indices r := by
  classical
  let compatible : Finset (Finset EscLeanChecks.SatEvent) :=
    familyCompatibleSubsetsOfCard indices r
  have hsumFilter : familyRankCommonHitCountRat N Pz b indices r =
      ∑ events ∈ compatible,
        (EscLeanChecks.baseSatEventCommonHitCountUpTo N Pz b events : ℚ) := by
    unfold familyRankCommonHitCountRat compatible familyCompatibleSubsetsOfCard
    rw [Nat.cast_sum]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro events hevents hnotmem
    have hnotcompat : ¬ ∀ event ∈ events, ∀ other ∈ events,
        event ≠ other → EscLeanChecks.satEventCompatible event other := by
      intro hcompat
      exact hnotmem (Finset.mem_filter.mpr ⟨hevents, hcompat⟩)
    rw [baseFamilyCommonHitCount_eq_zero_of_not_compatible
      N Pz b events hnotcompat]
    norm_num
  rw [hsumFilter]
  have hsumDensity :
      (∑ events ∈ compatible,
          (EscLeanChecks.baseSatEventCommonHitCountUpTo N Pz b events : ℚ)) ≤
        ∑ events ∈ compatible,
          ((N : ℚ) / (Pz : ℚ) *
              ((1 : ℚ) / (EscLeanChecks.congruenceLcm
                (EscLeanChecks.satEventResidualHitRows events.toList) : ℚ)) + 1) := by
    apply Finset.sum_le_sum
    intro events hevents
    have hpowerset : events ∈ (familyEvents indices).powersetCard r :=
      (Finset.mem_filter.mp hevents).1
    have hsub : events ⊆ familyEvents indices :=
      (Finset.mem_powersetCard.mp hpowerset).1
    have hadm : ∀ event ∈ events,
        EscLeanChecks.satEventAdmissibleFor Pz (familyRhoOf indices) event := by
      intro event hevent
      exact familyEvents_admissibleFor P X Pz b indices hX hmem event
        (hsub hevent)
    have hpCop' : ∀ event ∈ events, Nat.Coprime Pz event.p := by
      intro event hevent
      exact hpCop event (hsub hevent)
    by_cases hhit : ∃ x : ℕ, x ≡ b [MOD Pz] ∧
        ∀ event ∈ events, EscLeanChecks.satEventHit x event
    · rcases hhit with ⟨x, hxbase, hxhit⟩
      have hnat :=
        EscLeanChecks.baseSatEventCommonHitCountUpTo_le_div_add_one_of_common_hit_admissibleFor
          N Pz b x (familyRhoOf indices) events hPz hadm hpCop' hxbase hxhit
      have hcast :
          (EscLeanChecks.baseSatEventCommonHitCountUpTo N Pz b events : ℚ) ≤
            ((N / (Pz * EscLeanChecks.congruenceLcm
              (EscLeanChecks.satEventResidualHitRowsFinset events).toList) : ℕ) : ℚ) + 1 := by
        exact_mod_cast hnat
      have hdiv :
          ((N / (Pz * EscLeanChecks.congruenceLcm
            (EscLeanChecks.satEventResidualHitRowsFinset events).toList) : ℕ) : ℚ) ≤
            (N : ℚ) / ((Pz * EscLeanChecks.congruenceLcm
              (EscLeanChecks.satEventResidualHitRowsFinset events).toList : ℕ) : ℚ) :=
        Nat.cast_div_le
      have hL : EscLeanChecks.congruenceLcm
          (EscLeanChecks.satEventResidualHitRowsFinset events).toList =
          EscLeanChecks.congruenceLcm
            (EscLeanChecks.satEventResidualHitRows events.toList) :=
        EscLeanChecks.congruenceLcm_satEventResidualHitRowsFinset_toList_eq events
      calc
        (EscLeanChecks.baseSatEventCommonHitCountUpTo N Pz b events : ℚ) ≤
            ((N / (Pz * EscLeanChecks.congruenceLcm
              (EscLeanChecks.satEventResidualHitRowsFinset events).toList) : ℕ) : ℚ) + 1 := hcast
        _ ≤ (N : ℚ) / ((Pz * EscLeanChecks.congruenceLcm
              (EscLeanChecks.satEventResidualHitRowsFinset events).toList : ℕ) : ℚ) + 1 :=
            add_le_add_right hdiv 1
        _ = (N : ℚ) / (Pz : ℚ) *
              ((1 : ℚ) / (EscLeanChecks.congruenceLcm
                (EscLeanChecks.satEventResidualHitRows events.toList) : ℚ)) + 1 := by
            rw [hL]
            push_cast
            ring
    · have hzero :=
        EscLeanChecks.baseSatEventCommonHitCountUpTo_eq_zero_of_no_common_base_hit
          N Pz b events hhit
      rw [hzero]
      positivity
  calc
    (∑ events ∈ compatible,
        (EscLeanChecks.baseSatEventCommonHitCountUpTo N Pz b events : ℚ)) ≤
        ∑ events ∈ compatible,
          ((N : ℚ) / (Pz : ℚ) *
              ((1 : ℚ) / (EscLeanChecks.congruenceLcm
                (EscLeanChecks.satEventResidualHitRows events.toList) : ℚ)) + 1) :=
      hsumDensity
    _ = (N : ℚ) / (Pz : ℚ) * familyCompatibleLcmMassRat indices r +
        (compatible.card : ℚ) := by
      simp [compatible, familyCompatibleLcmMassRat, Finset.mul_sum,
        Finset.sum_add_distrib]
    _ ≤ (N : ℚ) / (Pz : ℚ) * familyCompatibleLcmMassRat indices r +
        (⌊X⌋₊ : ℚ) ^ r * familyCompatibleLcmMassRat indices r := by
      exact add_le_add_left
        (familyCompatibleSubsets_card_le_floor_scale_pow_lcmMass
          P X Pz b indices hX hmem r) _

/-- Two-sided form of the manuscript's finite-interval approximation:
`|C_r^(b)(N) - (N/Pz) F_r| ≤ floor(X)^r F_r`. -/
theorem familyRankCommonHitCountRat_abs_sub_main_le_endpoint
    (P : Params) (X : ℝ) (N Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X) (hPz : 0 < Pz)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (hpCop : ∀ event ∈ familyEvents indices, Nat.Coprime Pz event.p)
    (r : ℕ) :
    |familyRankCommonHitCountRat N Pz b indices r -
        (N : ℚ) / (Pz : ℚ) * familyCompatibleLcmMassRat indices r| ≤
      (⌊X⌋₊ : ℚ) ^ r * familyCompatibleLcmMassRat indices r := by
  rw [abs_le]
  constructor
  · have hlower := familyRankCommonHitCountRat_main_sub_endpoint_le
      P X N Pz b indices hX hPz hmem hpCop r
    linarith
  · have hupper := familyRankCommonHitCountRat_le_main_add_endpoint
      P X N Pz b indices hX hPz hmem hpCop r
    linarith

/-- Signed parity form consumed directly by Bonferroni rank budgets.  Even
ranks use the upper approximation and odd ranks use the newly proved lower
approximation. -/
theorem familyRankSignedCommonHitCountRat_le_main_parity_add_endpoint
    (P : Params) (X : ℝ) (N Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X) (hPz : 0 < Pz)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (hpCop : ∀ event ∈ familyEvents indices, Nat.Coprime Pz event.p)
    (r : ℕ) :
    (((-1 : Int) ^ r) *
        ((∑ events ∈ (familyEvents indices).powersetCard r,
          EscLeanChecks.baseSatEventCommonHitCountUpTo N Pz b events : ℕ) : Int) : ℚ) ≤
      if Even r then
        (N : ℚ) / (Pz : ℚ) * familyCompatibleLcmMassRat indices r +
          (⌊X⌋₊ : ℚ) ^ r * familyCompatibleLcmMassRat indices r
      else
        -((N : ℚ) / (Pz : ℚ) * familyCompatibleLcmMassRat indices r) +
          (⌊X⌋₊ : ℚ) ^ r * familyCompatibleLcmMassRat indices r := by
  change ((-1 : ℚ) ^ r) * familyRankCommonHitCountRat N Pz b indices r ≤ _
  rcases Nat.even_or_odd r with hr | hr
  · rw [if_pos hr, hr.neg_one_pow, one_mul]
    exact familyRankCommonHitCountRat_le_main_add_endpoint
      P X N Pz b indices hX hPz hmem hpCop r
  · rw [if_neg (Nat.not_even_iff_odd.mpr hr), hr.neg_one_pow, neg_one_mul]
    have hlower := familyRankCommonHitCountRat_main_sub_endpoint_le
      P X N Pz b indices hX hPz hmem hpCop r
    linarith

/-- Finite Bonferroni decomposition for the actual reciprocal-LCM
coefficients.  The main alternating polynomial and the endpoint error both use
`familyCompatibleLcmMassRat`; no elementary-symmetric replacement occurs. -/
theorem familyBaseNoHitRat_le_lcmMain_add_endpoint
    (P : Params) (X : ℝ) (N Pz b R : ℕ)
    (indices : Finset FamilyIndex)
    (hX : 1 < X) (hPz : 0 < Pz)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (hpCop : ∀ event ∈ familyEvents indices, Nat.Coprime Pz event.p) :
    (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N Pz b
        (familyEvents indices) : ℚ) ≤
      (N : ℚ) / (Pz : ℚ) *
          (∑ r ∈ Finset.range (2 * R + 1),
            (-1 : ℚ) ^ r * familyCompatibleLcmMassRat indices r) +
        ∑ r ∈ Finset.range (2 * R + 1),
          (⌊X⌋₊ : ℚ) ^ r * familyCompatibleLcmMassRat indices r := by
  have hbonf := EscLeanChecks.baseSatEventSubsets_bonferroni_lower_double_count
    N Pz b R (familyEvents indices)
  change EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N Pz b
      (familyEvents indices) ≤
    ∑ r ∈ Finset.range (2 * R + 1),
      ((-1 : Int) ^ r) *
        ((∑ events ∈ (familyEvents indices).powersetCard r,
          EscLeanChecks.baseSatEventCommonHitCountUpTo N Pz b events : ℕ) : Int)
    at hbonf
  have hbonfQ :
      (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N Pz b
        (familyEvents indices) : ℚ) ≤
      ((∑ r ∈ Finset.range (2 * R + 1),
        ((-1 : Int) ^ r) *
          ((∑ events ∈ (familyEvents indices).powersetCard r,
            EscLeanChecks.baseSatEventCommonHitCountUpTo N Pz b events : ℕ) : Int)) : Int) := by
    exact_mod_cast hbonf
  calc
    (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N Pz b
        (familyEvents indices) : ℚ) ≤
      ((∑ r ∈ Finset.range (2 * R + 1),
        ((-1 : Int) ^ r) *
          ((∑ events ∈ (familyEvents indices).powersetCard r,
            EscLeanChecks.baseSatEventCommonHitCountUpTo N Pz b events : ℕ) : Int)) : Int) :=
      hbonfQ
    _ = ∑ r ∈ Finset.range (2 * R + 1),
        ((((-1 : Int) ^ r) *
          ((∑ events ∈ (familyEvents indices).powersetCard r,
            EscLeanChecks.baseSatEventCommonHitCountUpTo N Pz b events : ℕ) : Int) : Int) : ℚ) := by
      norm_cast
    _ ≤ ∑ r ∈ Finset.range (2 * R + 1),
        ((-1 : ℚ) ^ r *
            ((N : ℚ) / (Pz : ℚ) *
              familyCompatibleLcmMassRat indices r) +
          (⌊X⌋₊ : ℚ) ^ r * familyCompatibleLcmMassRat indices r) := by
      apply Finset.sum_le_sum
      intro r hr
      have hsigned := familyRankSignedCommonHitCountRat_le_main_parity_add_endpoint
        P X N Pz b indices hX hPz hmem hpCop r
      rcases Nat.even_or_odd r with heven | hodd
      · rw [if_pos heven] at hsigned
        simpa [heven.neg_one_pow] using hsigned
      · rw [if_neg (Nat.not_even_iff_odd.mpr hodd)] at hsigned
        simpa [hodd.neg_one_pow] using hsigned
    _ = (N : ℚ) / (Pz : ℚ) *
          (∑ r ∈ Finset.range (2 * R + 1),
            (-1 : ℚ) ^ r * familyCompatibleLcmMassRat indices r) +
        ∑ r ∈ Finset.range (2 * R + 1),
          (⌊X⌋₊ : ℚ) ^ r * familyCompatibleLcmMassRat indices r := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro r hr
        ring
      · rfl

/-- The base modulus is coprime to every residual modulus whenever no selected
prime divides that base modulus. -/
theorem familyEvents_baseCoprime_residual_of_prime_not_dvd
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hnot : ∀ i ∈ indices, ¬ i.p ∣ Pz)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i) :
    ∀ event ∈ familyEvents indices,
      Nat.Coprime Pz (EscLeanChecks.conditionalModulus event.dPlus event.p) := by
  intro event hevent
  rcases Finset.mem_image.mp hevent with ⟨i, hi, rfl⟩
  have hcop_dplus : Nat.Coprime Pz i.dplus := (hmem i hi).dplus_coprime_Pz.symm
  have hcop_p : Nat.Coprime Pz i.p :=
    (((hmem i hi).p_prime.coprime_iff_not_dvd).2 (hnot i hi)).symm
  exact Nat.Coprime.mul_right hcop_dplus hcop_p

/-- A selected prime above the full base modulus is a sufficient, but stronger
than necessary, way to obtain base-residual coprimality. -/
theorem familyEvents_baseCoprime_residual
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hPz : 0 < Pz) (hlarge : ∀ i ∈ indices, Pz < i.p)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i) :
    ∀ event ∈ familyEvents indices,
      Nat.Coprime Pz (EscLeanChecks.conditionalModulus event.dPlus event.p) := by
  apply familyEvents_baseCoprime_residual_of_prime_not_dvd P X Pz b indices
    (fun i hi => Nat.not_dvd_of_pos_of_lt hPz (hlarge i hi)) hmem

/-- The finite interval transfer for the concrete paper family, before any
analytic estimate of the compatible-lcm sum.  This proves the paper's CRT and
Bonferroni reduction directly for the actual events. -/
theorem familyEvents_baseFiniteIntervalTransfer_le_compatible_lcm_of_baseCoprime
    (P : Params) (X : ℝ) (N Pz b R : ℕ) (indices : Finset FamilyIndex)
    (hPz : 0 < Pz)
    (hbaseCoprime : ∀ event ∈ familyEvents indices,
      Nat.Coprime Pz (EscLeanChecks.conditionalModulus event.dPlus event.p))
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i) :
    EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N Pz b (familyEvents indices) ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ EscLeanChecks.baseRowCompatibleSubsetsOfCard Pz b
            (EscLeanChecks.satEventResidualHitRowsFinset (familyEvents indices)) r,
          (N / (Pz * EscLeanChecks.congruenceLcm s.toList) + 1) : Nat) : Int) := by
  have hrowNoHit :
      EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N Pz b (familyEvents indices) =
        EscLeanChecks.baseRowNoHitIndicatorSumUpTo N Pz b
          (EscLeanChecks.satEventResidualHitRowsFinset (familyEvents indices)) := by
    classical
    unfold EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo
      EscLeanChecks.baseRowNoHitIndicatorSumUpTo
    apply Finset.sum_congr rfl
    intro n _hn
    have hzero :
        EscLeanChecks.hitEventCount
            (EscLeanChecks.satEventResidualHitRowsFinset (familyEvents indices))
            (fun row => n ≡ row.2 [MOD row.1]) = 0 ↔
          EscLeanChecks.hitEventCount (familyEvents indices)
            (fun event => EscLeanChecks.satEventHit n event) = 0 := by
      simpa [EscLeanChecks.satEventResidualHitRowsFinset] using
        (EscLeanChecks.hitEventCount_image_eq_zero_iff (familyEvents indices)
          EscLeanChecks.satEventResidualHitRow
          (fun event => EscLeanChecks.satEventHit n event)
          (fun row : Nat × Nat => n ≡ row.2 [MOD row.1]) (by
            intro event hevent
            exact (EscLeanChecks.satEventHit_iff_modEq_residualHitRow n event
              (familyEvents_residualModulus_pos P X Pz b indices hmem event hevent)).symm))
    by_cases hevents :
        EscLeanChecks.hitEventCount (familyEvents indices)
          (fun event => EscLeanChecks.satEventHit n event) = 0
    · have hrows :
          EscLeanChecks.hitEventCount
              (EscLeanChecks.satEventResidualHitRowsFinset (familyEvents indices))
              (fun row => n ≡ row.2 [MOD row.1]) = 0 :=
        hzero.mpr hevents
      simp [hevents, hrows]
    · have hrows :
          EscLeanChecks.hitEventCount
              (EscLeanChecks.satEventResidualHitRowsFinset (familyEvents indices))
              (fun row => n ≡ row.2 [MOD row.1]) ≠ 0 := by
        intro h
        exact hevents (hzero.mp h)
      simp [hevents, hrows]
  rw [hrowNoHit]
  apply EscLeanChecks.baseFiniteIntervalTransfer_le_compatible_lcm_bound
  · exact hPz
  · intro row hrow
    rcases Finset.mem_image.mp hrow with ⟨event, hevent, rfl⟩
    exact familyEvents_residualModulus_pos P X Pz b indices hmem event hevent
  · intro row hrow
    rcases Finset.mem_image.mp hrow with ⟨event, hevent, rfl⟩
    exact hbaseCoprime event hevent

/-- The finite interval transfer under the stronger sufficient hypothesis that
each selected prime lies above the entire base modulus. -/
theorem familyEvents_baseFiniteIntervalTransfer_le_compatible_lcm
    (P : Params) (X : ℝ) (N Pz b R : ℕ) (indices : Finset FamilyIndex)
    (hPz : 0 < Pz) (hlarge : ∀ i ∈ indices, Pz < i.p)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i) :
    EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N Pz b (familyEvents indices) ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ EscLeanChecks.baseRowCompatibleSubsetsOfCard Pz b
            (EscLeanChecks.satEventResidualHitRowsFinset (familyEvents indices)) r,
          (N / (Pz * EscLeanChecks.congruenceLcm s.toList) + 1) : Nat) : Int) :=
  familyEvents_baseFiniteIntervalTransfer_le_compatible_lcm_of_baseCoprime
    P X N Pz b R indices hPz
    (familyEvents_baseCoprime_residual P X Pz b indices hPz hlarge hmem) hmem

/-- The finite interval transfer under the paper's actual base-coprimality
condition: selected primes are excluded from the roughness modulus. -/
theorem familyEvents_baseFiniteIntervalTransfer_le_compatible_lcm_of_prime_not_dvd
    (P : Params) (X : ℝ) (N Pz b R : ℕ) (indices : Finset FamilyIndex)
    (hPz : 0 < Pz) (hnot : ∀ i ∈ indices, ¬ i.p ∣ Pz)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i) :
    EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N Pz b (familyEvents indices) ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ EscLeanChecks.baseRowCompatibleSubsetsOfCard Pz b
            (EscLeanChecks.satEventResidualHitRowsFinset (familyEvents indices)) r,
          (N / (Pz * EscLeanChecks.congruenceLcm s.toList) + 1) : Nat) : Int) :=
  familyEvents_baseFiniteIntervalTransfer_le_compatible_lcm_of_baseCoprime
    P X N Pz b R indices hPz
    (familyEvents_baseCoprime_residual_of_prime_not_dvd P X Pz b indices hnot hmem) hmem

/-- A residual hit in the static paper family, together with the conditioned
base congruence, is the full fan congruence modulo `Q`. -/
theorem FamilyStaticMem.eventHit_Q_dvd_of_dminus_lt_p
    {P : Params} {X : ℝ} {Pz b n : ℕ} {i : FamilyIndex}
    (hdminus_lt_p : i.dminus < i.p)
    (hmem : FamilyStaticMem P X Pz b i)
    (hbase : n ≡ b [MOD Pz])
    (hhit : EscLeanChecks.satEventHit n i.toSatEvent) :
    i.Q ∣ n + 4 * i.e := by
  have hbase_small : n ≡ b [MOD i.dminus] :=
    hbase.of_dvd hmem.dminus_dvd_Pz
  have hshift : n + 4 * i.e ≡ b + 4 * i.e [MOD i.dminus] :=
    hbase_small.add_right _
  have hsmall : i.dminus ∣ n + 4 * i.e :=
    (hshift.dvd_iff (dvd_refl i.dminus)).mpr
      (Nat.modEq_zero_iff_dvd.mp hmem.base_cong)
  have hresidual : i.q ∣ n + 4 * i.e := by
    simpa [FamilyIndex.q, FamilyIndex.toSatEvent,
      EscLeanChecks.satEventHit, EscLeanChecks.conditionalModulus] using hhit
  have hproduct : i.dminus * i.q ∣ n + 4 * i.e :=
    (hmem.dminus_coprime_residual_of_lt hdminus_lt_p).mul_dvd_of_dvd_of_dvd
      hsmall hresidual
  simpa [FamilyIndex.Q, FamilyIndex.q, Nat.mul_assoc] using hproduct

/-- The stronger whole-modulus separation is a sufficient special case of the
actual small-divisor separation used by `eventHit_Q_dvd_of_dminus_lt_p`. -/
theorem FamilyStaticMem.eventHit_Q_dvd
    {P : Params} {X : ℝ} {Pz b n : ℕ} {i : FamilyIndex}
    (hPz : 0 < Pz) (hlarge : Pz < i.p)
    (hmem : FamilyStaticMem P X Pz b i)
    (hbase : n ≡ b [MOD Pz])
    (hhit : EscLeanChecks.satEventHit n i.toSatEvent) :
    i.Q ∣ n + 4 * i.e := by
  apply hmem.eventHit_Q_dvd_of_dminus_lt_p
    (lt_of_le_of_lt (Nat.le_of_dvd hPz hmem.dminus_dvd_Pz) hlarge)
    hbase hhit

/-! ## Arithmetic of the fan center `a = (Q+1)/4`. -/

/-- From the certificate congruence `4 ρ(e) ∣ Q + 1` the fan center `a = (Q+1)/4`
is integral and satisfies `4 a = Q + 1`, i.e. `Q = 4a - 1`
(tex lines 761–763: "the congruence implies `aᵢ` is an integer ... `Qᵢ = 4aᵢ-1`"). -/
theorem four_mul_a_eq (i : FamilyIndex) (hsat : 4 * i.rho ∣ i.Q + 1) :
    4 * i.a = i.Q + 1 := by
  obtain ⟨k, hk⟩ := hsat
  have h4 : (4 : ℕ) ∣ i.Q + 1 := ⟨i.rho * k, by rw [hk]; ring⟩
  unfold FamilyIndex.a
  omega

/-- `Q = qOf a`, i.e. `Q = 4a - 1` in `ℕ` (tex line 763). -/
theorem Q_eq_qOf_a (i : FamilyIndex) (hsat : 4 * i.rho ∣ i.Q + 1) :
    i.Q = EscLeanChecks.qOf i.a := by
  have h := four_mul_a_eq i hsat
  unfold EscLeanChecks.qOf
  omega

/-- The fan center is positive once `Q ≥ 3` (which holds in the family because
`Q = d₋ d₊ p` with `p` a prime `> X^β > 1`).  Here we deduce it directly from
`4 a = Q + 1` and `Q > 0`. -/
theorem a_pos (i : FamilyIndex) (hsat : 4 * i.rho ∣ i.Q + 1) (hQ : 0 < i.Q) :
    0 < i.a := by
  have h := four_mul_a_eq i hsat
  omega

/-- The conductor divides the fan center: `ρ(e) ∣ a`.

This is the certificate step (tex lines 761–762: "the congruence implies that
`aᵢ` is an integer and `ρ(e) ∣ aᵢ`").  Indeed `4 ρ(e) ∣ Q + 1 = 4 a` gives
`ρ(e) ∣ a`. -/
theorem rho_dvd_a (i : FamilyIndex) (hsat : 4 * i.rho ∣ i.Q + 1) :
    i.rho ∣ i.a := by
  have h4a : 4 * i.a = i.Q + 1 := four_mul_a_eq i hsat
  obtain ⟨k, hk⟩ := hsat
  -- 4 * a = Q + 1 = 4 * rho * k  ⟹  a = rho * k
  refine ⟨k, ?_⟩
  have : 4 * i.a = 4 * (i.rho * k) := by rw [h4a, hk]; ring
  omega

/-- The exact-divisor certificate: `e ∣ a²`
(tex line 762: "Because `e = rs²` and `ρ(e) = rs`, this gives `e ∣ aᵢ²`"). -/
theorem e_dvd_a_sq (i : FamilyIndex) (hsat : 4 * i.rho ∣ i.Q + 1) :
    i.e ∣ i.a ^ 2 :=
  i.E.e_dvd_sq_of_rho_dvd (rho_dvd_a i hsat)

/-- The certificate congruence forces the reduced conductor `ρ(e)` to be positive.

If `ρ(e) = 0`, then the divisor `4ρ(e)` is zero, so `4ρ(e) ∣ Q+1` would force
`Q+1 = 0`, impossible in `ℕ`. -/
theorem rho_pos_of_sat (i : FamilyIndex) (hsat : 4 * i.rho ∣ i.Q + 1) :
    0 < i.rho := by
  by_contra h
  have hrho0 : i.rho = 0 := Nat.eq_zero_of_not_pos h
  obtain ⟨k, hk⟩ := hsat
  rw [hrho0] at hk
  simp at hk

/-- The certificate congruence also forces `Q > 0`.  If `Q=0`, then the positive
number `4ρ(e)` would divide `1`. -/
theorem Q_pos_of_sat (i : FamilyIndex) (hsat : 4 * i.rho ∣ i.Q + 1) :
    0 < i.Q := by
  have hrho : 0 < i.rho := rho_pos_of_sat i hsat
  by_contra h
  have hQ0 : i.Q = 0 := Nat.eq_zero_of_not_pos h
  have hsat' := hsat
  rw [hQ0] at hsat'
  have hdiv1 : 4 * i.rho ∣ 1 := hsat'
  have hle : 4 * i.rho ≤ 1 := Nat.le_of_dvd (by norm_num : 0 < 1) hdiv1
  omega

/-- The exact divisor `e = r s²` is positive whenever the certificate congruence
holds.  This removes the last auxiliary positivity hypothesis from the
family-membership-to-representability corollary. -/
theorem e_pos_of_sat (i : FamilyIndex) (hsat : 4 * i.rho ∣ i.Q + 1) :
    0 < i.e := by
  have hrho : 0 < i.rho := rho_pos_of_sat i hsat
  rw [FamilyIndex.e_eq, FamilyIndex.rho_eq] at *
  have hr : 0 < i.E.r := Nat.pos_of_mul_pos_right hrho
  have hs : 0 < i.E.s := Nat.pos_of_mul_pos_left hrho
  exact Nat.mul_pos hr (pow_pos hs 2)

/-! ## The key derivation: every family hit is a valid certificate. -/

/-- **Every family hit is a valid certificate ⟹ representable.**

(tex lines 752–764: "Thus every such hit is a valid certificate by
\Cref{lem:fan}.")

Given a family index `i` whose data satisfy the certificate congruence
`4 ρ(e) ∣ Q + 1` (so that `a = (Q+1)/4` is integral with `ρ(e) ∣ a`, hence
`e ∣ a²`, `Q > 0`, `e > 0`, and `Q = 4a-1 = qOf a`) and the conditional residue
congruence `Q ∣ n + 4e`, the number `n` is Erdős–Straus representable:
`4/n = 1/x + 1/y + 1/z` with positive integers `x, y, z`.

This is the paper's derivation built directly on the divisor-fan
certificate `EscLeanChecks.divisorFan_nat_certificate` (the encoding of
`lem:fan`).  The whole reduction is a Lean proof. -/
theorem familyHit_esRepresentable
    (i : FamilyIndex) (n : ℕ)
    (hn : 0 < n)
    (hsat : 4 * i.rho ∣ i.Q + 1)
    (hcond : i.Q ∣ n + 4 * i.e) :
    EscLeanChecks.esRepresentable n := by
  -- a > 0
  have hapos : 0 < i.a := a_pos i hsat (Q_pos_of_sat i hsat)
  have he : 0 < i.e := e_pos_of_sat i hsat
  -- e ∣ a²
  have hedvd : i.e ∣ i.a ^ 2 := e_dvd_a_sq i hsat
  -- Q = qOf a, so the conditional congruence becomes qOf a ∣ n + 4e
  have hQa : i.Q = EscLeanChecks.qOf i.a := Q_eq_qOf_a i hsat
  have hfan : EscLeanChecks.qOf i.a ∣ n + 4 * i.e := hQa ▸ hcond
  -- Apply the divisor-fan certificate and read off representability.
  exact EscLeanChecks.divisorFan_positive_unit_fractions
    n i.a i.e hn hapos he hedvd hfan

/-- The finite-event hit used by the analytic layer is a genuine paper-family
certificate and therefore yields an Erdos--Straus representation under the
small-divisor separation present in the paper. -/
theorem FamilyStaticMem.eventHit_esRepresentable_of_dminus_lt_p
    {P : Params} {X : ℝ} {Pz b n : ℕ} {i : FamilyIndex}
    (hdminus_lt_p : i.dminus < i.p)
    (hmem : FamilyStaticMem P X Pz b i)
    (hn : 0 < n) (hbase : n ≡ b [MOD Pz])
    (hhit : EscLeanChecks.satEventHit n i.toSatEvent) :
    EscLeanChecks.esRepresentable n :=
  familyHit_esRepresentable i n hn hmem.sat_cong
    (hmem.eventHit_Q_dvd_of_dminus_lt_p hdminus_lt_p hbase hhit)

/-- Whole-modulus separation is a sufficient special case of the paper's
small-divisor separation for a family hit. -/
theorem FamilyStaticMem.eventHit_esRepresentable
    {P : Params} {X : ℝ} {Pz b n : ℕ} {i : FamilyIndex}
    (hPz : 0 < Pz) (hlarge : Pz < i.p)
    (hmem : FamilyStaticMem P X Pz b i)
    (hn : 0 < n) (hbase : n ≡ b [MOD Pz])
    (hhit : EscLeanChecks.satEventHit n i.toSatEvent) :
    EscLeanChecks.esRepresentable n :=
  hmem.eventHit_esRepresentable_of_dminus_lt_p
    (lt_of_le_of_lt (Nat.le_of_dvd hPz hmem.dminus_dvd_Pz) hlarge) hn hbase hhit

/-- An exceptional point in a conditioned residue class cannot hit any event
from the concrete paper family for that class when every small divisor lies
below its selected prime. -/
theorem familyEvents_noHit_of_esExceptional_of_dminus_lt_p
    (P : Params) (X : ℝ) (Pz b n : ℕ) (indices : Finset FamilyIndex)
    (hdminus_lt_p : ∀ i ∈ indices, i.dminus < i.p)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (hn : 0 < n) (hbase : n ≡ b [MOD Pz])
    (hexceptional : EscLeanChecks.esExceptional n) :
    EscLeanChecks.hitEventCount (familyEvents indices)
      (fun event => EscLeanChecks.satEventHit n event) = 0 := by
  classical
  unfold EscLeanChecks.hitEventCount
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_not_mem]
  intro event hevent
  rcases Finset.mem_filter.mp hevent with ⟨heventFamily, hhit⟩
  rw [familyEvents] at heventFamily
  rcases Finset.mem_image.mp heventFamily with ⟨i, hi, rfl⟩
  exact hexceptional
    ((hmem i hi).eventHit_esRepresentable_of_dminus_lt_p
      (hdminus_lt_p i hi) hn hbase hhit)

/-- Whole-modulus separation is a sufficient special case of the no-hit
criterion above. -/
theorem familyEvents_noHit_of_esExceptional
    (P : Params) (X : ℝ) (Pz b n : ℕ) (indices : Finset FamilyIndex)
    (hPz : 0 < Pz)
    (hlarge : ∀ i ∈ indices, Pz < i.p)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i)
    (hn : 0 < n) (hbase : n ≡ b [MOD Pz])
    (hexceptional : EscLeanChecks.esExceptional n) :
    EscLeanChecks.hitEventCount (familyEvents indices)
      (fun event => EscLeanChecks.satEventHit n event) = 0 := by
  apply familyEvents_noHit_of_esExceptional_of_dminus_lt_p P X Pz b n indices
    (fun i hi =>
      lt_of_le_of_lt (Nat.le_of_dvd hPz (hmem i hi).dminus_dvd_Pz) (hlarge i hi))
    hmem hn hbase hexceptional

/-- Exceptional integers in a conditioned residue class up to `N`. -/
noncomputable def baseExceptionalClass (N Pz b : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Icc 1 N).filter
      (fun n => n ≡ b [MOD Pz] ∧ EscLeanChecks.esExceptional n)

/-- The exceptional points in a conditioned base class are bounded by the
actual finite no-hit count of the paper family.  This is the deterministic
reduced-class majorant that precedes the analytic finite-transfer estimate. -/
theorem familyExceptionalClassCard_le_baseNoHit
    (P : Params) (X : ℝ) (N Pz b : ℕ) (indices : Finset FamilyIndex)
    (hPz : 0 < Pz)
    (hlarge : ∀ i ∈ indices, Pz < i.p)
    (hmem : ∀ i ∈ indices, FamilyStaticMem P X Pz b i) :
    ((baseExceptionalClass N Pz b).card : ℚ) ≤
      (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N Pz b
        (familyEvents indices) : ℚ) := by
  classical
  let exceptionalClass : Finset ℕ := baseExceptionalClass N Pz b
  let noHitClass : Finset ℕ :=
    ((Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz])).filter
      (fun n => EscLeanChecks.hitEventCount (familyEvents indices)
        (fun event => EscLeanChecks.satEventHit n event) = 0)
  have hsubset : exceptionalClass ⊆ noHitClass := by
    intro n hn
    have hn' : n ∈ (Finset.Icc 1 N).filter
        (fun n => n ≡ b [MOD Pz] ∧ EscLeanChecks.esExceptional n) := by
      simpa [exceptionalClass, baseExceptionalClass] using hn
    have hnData := Finset.mem_filter.mp hn'
    have hnIcc : n ∈ Finset.Icc 1 N := hnData.1
    have hnBase : n ≡ b [MOD Pz] := hnData.2.1
    have hnExceptional : EscLeanChecks.esExceptional n := hnData.2.2
    have hnPos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one
      (Finset.mem_Icc.mp hnIcc).1
    have hnLe : n ≤ N := (Finset.mem_Icc.mp hnIcc).2
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hnLe), hnBase⟩
    · exact familyEvents_noHit_of_esExceptional P X Pz b n indices hPz
        hlarge hmem hnPos hnBase hnExceptional
  have hcard : exceptionalClass.card ≤ noHitClass.card :=
    Finset.card_le_card hsubset
  have hsum :
      EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N Pz b
        (familyEvents indices) = (noHitClass.card : Int) := by
    unfold EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo
    simpa [noHitClass] using
      (Finset.sum_boole
        (fun n => EscLeanChecks.hitEventCount (familyEvents indices)
          (fun event => EscLeanChecks.satEventHit n event) = 0)
        ((Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz])) :
        (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz]),
          if EscLeanChecks.hitEventCount (familyEvents indices)
            (fun event => EscLeanChecks.satEventHit n event) = 0
          then (1 : Int) else 0) = (noHitClass.card : Int))
  have hsumQ :
      (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N Pz b
        (familyEvents indices) : ℚ) = (noHitClass.card : ℚ) := by
    rw [hsum]
    norm_cast
  change (exceptionalClass.card : ℚ) ≤ _
  calc
    (exceptionalClass.card : ℚ) ≤ (noHitClass.card : ℚ) := by exact_mod_cast hcard
    _ = (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N Pz b
      (familyEvents indices) : ℚ) := hsumQ.symm

/-- The same conclusion phrased directly from a `FamilyMem` hit at scale `X`
with base class `b` and conductor `P(z) = Pz`.  All the divisibility data needed
by `familyHit_esRepresentable` is extracted from the membership fields. -/
theorem familyMem_esRepresentable
    (P : Params) (X : ℝ) (Pz b n : ℕ) (i : FamilyIndex)
    (hmem : FamilyMem P X Pz b n i) :
    EscLeanChecks.esRepresentable n :=
  familyHit_esRepresentable i n hmem.n_pos hmem.sat_cong hmem.cond_cong

/-- Positivity of `Q = d₋ d₊ p` from the membership data: `d₋ > 0`, `d₊ > 0`, and
`p` prime (hence `p > 0`).  This discharges the `hQ` hypothesis of
`familyMem_esRepresentable`. -/
theorem Q_pos_of_mem
    (P : Params) (X : ℝ) (Pz b n : ℕ) (i : FamilyIndex)
    (hmem : FamilyMem P X Pz b n i) :
    0 < i.Q := by
  rw [FamilyIndex.Q_eq]
  have hp : 0 < i.p := hmem.p_prime.pos
  have hdm : 0 < i.dminus := hmem.dminus_pos
  have hdp : 0 < i.dplus := hmem.dplus_pos
  positivity

/-- Membership hit ⟹ representable, with both `Q`-positivity and `e`-positivity
discharged from the membership data and the certificate congruence. -/
theorem familyMem_esRepresentable'
    (P : Params) (X : ℝ) (Pz b n : ℕ) (i : FamilyIndex)
    (hmem : FamilyMem P X Pz b n i) :
    EscLeanChecks.esRepresentable n :=
  familyMem_esRepresentable P X Pz b n i hmem

/-! ## The index set `𝓘_b` and the certificate mass `μ_b`. -/

/-- The set `𝓘_b` of all static family quadruples for base class `b` at scale
`X` (tex line 764: "Let `𝓘_b` be the set of all quadruples above").  It is
independent of a tested integer `n`; the residual hit condition belongs to
`SatEventHit`, not to family membership. -/
def familyIndexSet (P : Params) (X : ℝ) (Pz b : ℕ) : Set FamilyIndex :=
  { i | FamilyStaticMem P X Pz b i }

/-- The static paper family is finite at every positive scale.  Each coordinate
of a member is bounded by one of the defining scale inequalities. -/
theorem familyIndexSet_finite
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 0 < X) :
    (familyIndexSet P X Pz b).Finite := by
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
  have hmem : FamilyStaticMem P X Pz b i := by
    simpa [familyIndexSet] using hi
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

/-- The actual finite index family used by the paper at one base class. -/
noncomputable def familyIndexFinset (P : Params) (X : ℝ) (Pz b : ℕ) :
    Finset FamilyIndex :=
  if hX : 0 < X then (familyIndexSet_finite P X Pz b hX).toFinset else ∅

/-- At a positive scale, the finite family has exactly the static-membership
predicate from the manuscript. -/
theorem mem_familyIndexFinset_iff
    (P : Params) (X : ℝ) (Pz b : ℕ) (i : FamilyIndex) (hX : 0 < X) :
    i ∈ familyIndexFinset P X Pz b ↔ FamilyStaticMem P X Pz b i := by
  simp [familyIndexFinset, hX, familyIndexSet_finite, familyIndexSet]

/-- Exact Brun deletion recurrence for the complete finite family `𝓘_b` used
in the manuscript. -/
theorem actualPaperFamily_compatibleLcmMassRat_increment_recurrence
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 0 < X)
    (r : ℕ) (hr : 0 < r) :
    (r : ℚ) *
        familyCompatibleLcmMassRat (familyIndexFinset P X Pz b) r =
      ∑ old ∈ familyCompatibleSubsetsOfCard
          (familyIndexFinset P X Pz b) (r - 1),
        familySubsetLcmRecipRat old *
          familyIncrementRat
            (familyIndexFinset P X Pz b) old := by
  apply familyCompatibleLcmMassRat_increment_recurrence
    P X Pz b (familyIndexFinset P X Pz b)
  · intro i hi
    exact (mem_familyIndexFinset_iff P X Pz b i hX).1 hi
  · exact hr

/-- The actual paper coefficients satisfy the factorial Brun bound once the
paper's concrete increment `A(S)` has its asserted uniform estimate. -/
theorem actualPaperFamily_compatibleLcmMassRat_le_pow_div_factorial
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 0 < X)
    (M : ℚ) (hM : 0 ≤ M)
    (hinc : ∀ r : ℕ, 1 ≤ r →
      ∀ old ∈ familyCompatibleSubsetsOfCard
          (familyIndexFinset P X Pz b) (r - 1),
        familyIncrementRat
          (familyIndexFinset P X Pz b) old ≤ M) :
    ∀ r : ℕ,
      familyCompatibleLcmMassRat (familyIndexFinset P X Pz b) r ≤
        M ^ r / (Nat.factorial r : ℚ) := by
  apply familyCompatibleLcmMassRat_le_pow_div_factorial_of_increment_le
    P X Pz b (familyIndexFinset P X Pz b)
  · intro i hi
    exact (mem_familyIndexFinset_iff P X Pz b i hX).1 hi
  · exact hM
  · exact hinc

/-- At the complete static family, the small divisor lies below the selected
prime once the polylogarithmic small-divisor scale is below the prime scale. -/
theorem familyIndexFinset_dminus_lt_prime
    (P : Params) (X : ℝ) (Pz b : ℕ)
    (hX : 1 < X) (hU_lt_primeScale : UScale X < X ^ P.β) :
    ∀ i ∈ familyIndexFinset P X Pz b, i.dminus < i.p := by
  intro i hi
  have hmem : FamilyStaticMem P X Pz b i :=
    (mem_familyIndexFinset_iff P X Pz b i (lt_trans zero_lt_one hX)).1 hi
  have hreal : (i.dminus : ℝ) < (i.p : ℝ) :=
    lt_of_le_of_lt hmem.dminus_le_U (lt_trans hU_lt_primeScale hmem.p_gt)
  exact_mod_cast hreal

/-- At the complete static family, a selected prime cannot divide a base
modulus whose prime factors all lie below `z`, provided `z` lies below the
selected-prime scale. -/
theorem familyIndexFinset_prime_not_dvd_Pz
    (P : Params) (X : ℝ) (z Pz b : ℕ)
    (hPfac : ∀ q : ℕ, Nat.Prime q → q ∣ Pz → q ≤ z)
    (hX : 1 < X) (hz_lt_primeScale : (z : ℝ) < X ^ P.β) :
    ∀ i ∈ familyIndexFinset P X Pz b, ¬ i.p ∣ Pz := by
  intro i hi hdiv
  have hmem : FamilyStaticMem P X Pz b i :=
    (mem_familyIndexFinset_iff P X Pz b i (lt_trans zero_lt_one hX)).1 hi
  have hp_gt_z : z < i.p := by
    have hp : (z : ℝ) < (i.p : ℝ) :=
      lt_trans hz_lt_primeScale hmem.p_gt
    exact_mod_cast hp
  exact (not_le_of_gt hp_gt_z) (hPfac i.p hmem.p_prime hdiv)

/-- The complete finite static paper family has a canonical event-wise reduced
conductor function and satisfies the residual-event admissibility conditions. -/
theorem actualPaperFamily_events_admissibleFor
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 1 < X) :
    ∀ event ∈ familyEvents (familyIndexFinset P X Pz b),
      EscLeanChecks.satEventAdmissibleFor
        Pz (familyRhoOf (familyIndexFinset P X Pz b)) event := by
  apply familyEvents_admissibleFor P X Pz b (familyIndexFinset P X Pz b) hX
  intro i hi
  exact (mem_familyIndexFinset_iff P X Pz b i
    (lt_trans zero_lt_one hX)).1 hi

/-- The complete static family has exactly the manuscript's rational mass after
conversion to the residual-event list used by finite transfer. -/
theorem actualPaperFamily_eventWeights_sum_eq_indexMass
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 1 < X) :
    (familyEventWeightsRat (familyIndexFinset P X Pz b)).sum =
      familyIndexMassRat (familyIndexFinset P X Pz b) := by
  rw [familyEventWeightsRat_sum_eq]
  apply familyEventMassRat_eq_familyIndexMassRat P X Pz b
    (familyIndexFinset P X Pz b) hX
  intro i hi
  exact (mem_familyIndexFinset_iff P X Pz b i
    (lt_trans zero_lt_one hX)).1 hi

/-- The large-prime uniqueness conclusion for distinct compatible events from
the complete static paper family. -/
theorem actualPaperFamily_largePrime_ne_of_compatible_ne
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 1 < X)
    {event other : EscLeanChecks.SatEvent}
    (hevent : event ∈ familyEvents (familyIndexFinset P X Pz b))
    (hother : other ∈ familyEvents (familyIndexFinset P X Pz b))
    (hcompat : EscLeanChecks.satEventCompatible event other)
    (hne : event ≠ other) :
    event.p ≠ other.p := by
  apply familyEvents_largePrime_ne_of_compatible_ne P X Pz b
    (familyIndexFinset P X Pz b) hX
  · intro i hi
    exact (mem_familyIndexFinset_iff P X Pz b i
      (lt_trans zero_lt_one hX)).1 hi
  · exact hevent
  · exact hother
  · exact hcompat
  · exact hne

/-- The structural increment divisibility conclusion for the complete static
paper family. -/
theorem actualPaperFamily_incrementCommonDivisor_dvd_medium_of_compatible
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 1 < X)
    (event : EscLeanChecks.SatEvent) (old : List EscLeanChecks.SatEvent)
    (hevent : event ∈ familyEvents (familyIndexFinset P X Pz b))
    (hold : ∀ other ∈ old,
      other ∈ familyEvents (familyIndexFinset P X Pz b))
    (hcompat : ∀ other ∈ old, EscLeanChecks.satEventCompatible event other)
    (hdistinct : ∀ other ∈ old, event ≠ other) :
    EscLeanChecks.incrementG event.dPlus event.p
        (EscLeanChecks.residualLcm (EscLeanChecks.satEventRows old)) ∣
      event.dPlus := by
  apply familyEvents_incrementCommonDivisor_dvd_medium_of_compatible P X Pz b
    (familyIndexFinset P X Pz b) hX
  · intro i hi
    exact (mem_familyIndexFinset_iff P X Pz b i
      (lt_trans zero_lt_one hX)).1 hi
  · exact hevent
  · exact hold
  · exact hcompat
  · exact hdistinct

/-- The finite interval transfer specialized to the complete concrete paper
family.  No analytic estimate has yet been applied to the compatible-lcm sum. -/
theorem actualPaperFamily_baseFiniteIntervalTransfer_le_compatible_lcm
    (P : Params) (X : ℝ) (N z Pz b R : ℕ)
    (hPfac : ∀ q : ℕ, Nat.Prime q → q ∣ Pz → q ≤ z)
    (hPz : 0 < Pz) (hX : 1 < X)
    (hz_lt_primeScale : (z : ℝ) < X ^ P.β) :
    EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N Pz b
        (familyEvents (familyIndexFinset P X Pz b)) ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ EscLeanChecks.baseRowCompatibleSubsetsOfCard Pz b
            (EscLeanChecks.satEventResidualHitRowsFinset
              (familyEvents (familyIndexFinset P X Pz b))) r,
          (N / (Pz * EscLeanChecks.congruenceLcm s.toList) + 1) : Nat) : Int) := by
  apply familyEvents_baseFiniteIntervalTransfer_le_compatible_lcm_of_prime_not_dvd
    P X N Pz b R (familyIndexFinset P X Pz b) hPz
  · intro i hi
    exact familyIndexFinset_prime_not_dvd_Pz P X z Pz b hPfac hX
      hz_lt_primeScale i hi
  · intro i hi
    exact (mem_familyIndexFinset_iff P X Pz b i
      (lt_trans zero_lt_one hX)).1 hi

/-- Every large prime in the complete paper family is coprime to the roughness
modulus under the manuscript's prime-factor cutoff. -/
theorem actualPaperFamily_eventPrime_coprime_Pz
    (P : Params) (X : ℝ) (z Pz b : ℕ)
    (hPfac : ∀ q : ℕ, Nat.Prime q → q ∣ Pz → q ≤ z)
    (hX : 1 < X) (hz_lt_primeScale : (z : ℝ) < X ^ P.β) :
    ∀ event ∈ familyEvents (familyIndexFinset P X Pz b),
      Nat.Coprime Pz event.p := by
  intro event hevent
  rcases Finset.mem_image.mp hevent with ⟨i, hi, rfl⟩
  have hmem : FamilyStaticMem P X Pz b i :=
    (mem_familyIndexFinset_iff P X Pz b i
      (lt_trans zero_lt_one hX)).1 hi
  have hnot : ¬ i.p ∣ Pz :=
    familyIndexFinset_prime_not_dvd_Pz P X z Pz b hPfac hX
      hz_lt_primeScale i hi
  exact (((hmem.p_prime.coprime_iff_not_dvd).2 hnot).symm)

/-- The paper's finite-interval rank upper approximation for the complete
conductor-separated family, with base coprimality discharged from the stated
prime-factor cutoff for `Pz`. -/
theorem actualPaperFamily_rankCommonHitCountRat_le_main_add_endpoint
    (P : Params) (X : ℝ) (N z Pz b r : ℕ)
    (hPfac : ∀ q : ℕ, Nat.Prime q → q ∣ Pz → q ≤ z)
    (hPz : 0 < Pz) (hX : 1 < X)
    (hz_lt_primeScale : (z : ℝ) < X ^ P.β) :
    familyRankCommonHitCountRat N Pz b (familyIndexFinset P X Pz b) r ≤
      (N : ℚ) / (Pz : ℚ) *
          familyCompatibleLcmMassRat (familyIndexFinset P X Pz b) r +
        (⌊X⌋₊ : ℚ) ^ r *
          familyCompatibleLcmMassRat (familyIndexFinset P X Pz b) r := by
  apply familyRankCommonHitCountRat_le_main_add_endpoint
    P X N Pz b (familyIndexFinset P X Pz b) hX hPz
  · intro i hi
    exact (mem_familyIndexFinset_iff P X Pz b i
      (lt_trans zero_lt_one hX)).1 hi
  · exact actualPaperFamily_eventPrime_coprime_Pz
      P X z Pz b hPfac hX hz_lt_primeScale

/-- Complete two-sided formalization of the manuscript's finite-interval
approximation lemma for the actual conductor-separated family. -/
theorem actualPaperFamily_rankCommonHitCountRat_abs_sub_main_le_endpoint
    (P : Params) (X : ℝ) (N z Pz b r : ℕ)
    (hPfac : ∀ q : ℕ, Nat.Prime q → q ∣ Pz → q ≤ z)
    (hPz : 0 < Pz) (hX : 1 < X)
    (hz_lt_primeScale : (z : ℝ) < X ^ P.β) :
    |familyRankCommonHitCountRat N Pz b (familyIndexFinset P X Pz b) r -
        (N : ℚ) / (Pz : ℚ) *
          familyCompatibleLcmMassRat (familyIndexFinset P X Pz b) r| ≤
      (⌊X⌋₊ : ℚ) ^ r *
        familyCompatibleLcmMassRat (familyIndexFinset P X Pz b) r := by
  apply familyRankCommonHitCountRat_abs_sub_main_le_endpoint
    P X N Pz b (familyIndexFinset P X Pz b) hX hPz
  · intro i hi
    exact (mem_familyIndexFinset_iff P X Pz b i
      (lt_trans zero_lt_one hX)).1 hi
  · exact actualPaperFamily_eventPrime_coprime_Pz
      P X z Pz b hPfac hX hz_lt_primeScale

/-- Actual-family signed rank estimate, ready for direct use in the
Bonferroni certificate budget. -/
theorem actualPaperFamily_rankSignedCommonHitCountRat_le_main_parity_add_endpoint
    (P : Params) (X : ℝ) (N z Pz b r : ℕ)
    (hPfac : ∀ q : ℕ, Nat.Prime q → q ∣ Pz → q ≤ z)
    (hPz : 0 < Pz) (hX : 1 < X)
    (hz_lt_primeScale : (z : ℝ) < X ^ P.β) :
    (((-1 : Int) ^ r) *
        ((∑ events ∈
            (familyEvents (familyIndexFinset P X Pz b)).powersetCard r,
          EscLeanChecks.baseSatEventCommonHitCountUpTo N Pz b events : ℕ) : Int) : ℚ) ≤
      if Even r then
        (N : ℚ) / (Pz : ℚ) *
            familyCompatibleLcmMassRat (familyIndexFinset P X Pz b) r +
          (⌊X⌋₊ : ℚ) ^ r *
            familyCompatibleLcmMassRat (familyIndexFinset P X Pz b) r
      else
        -((N : ℚ) / (Pz : ℚ) *
            familyCompatibleLcmMassRat (familyIndexFinset P X Pz b) r) +
          (⌊X⌋₊ : ℚ) ^ r *
            familyCompatibleLcmMassRat (familyIndexFinset P X Pz b) r := by
  apply familyRankSignedCommonHitCountRat_le_main_parity_add_endpoint
    P X N Pz b (familyIndexFinset P X Pz b) hX hPz
  · intro i hi
    exact (mem_familyIndexFinset_iff P X Pz b i
      (lt_trans zero_lt_one hX)).1 hi
  · exact actualPaperFamily_eventPrime_coprime_Pz
      P X z Pz b hPfac hX hz_lt_primeScale

end EscAnalytic.Family
