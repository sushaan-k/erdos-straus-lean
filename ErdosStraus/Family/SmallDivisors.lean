import Batteries.Tactic.Lemma
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AlmostPrime
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import ErdosStraus.Estimates.WeightedSums
import ErdosStraus.Family.TotientAverage
import ErdosStraus.Family.DivisorSums

/-!
# Lemmas 6.4 and 6.5: averages over small divisors

For `A_s = ∑_{d ≤ U, d ∣ P(z), d odd, (d, sm) = 1} 1/d`, Lemma 6.4 states that
`∑_{s ≤ S₀ squarefree, (s, m) = 1} A_s/s ≍ log S₀ log z`. The lower bound comes from the sum
without the conditions `(s, m) = (d, m) = 1`, which is larger by at most the factor
`(∑_{g ∣ m} 1/g)²`. Lemma 6.5 follows: uniformly in the reduced classes `b` modulo `P(z)`,
`Σ_b = ∑_{d₋} ∑_{e : b ≡ -m e (mod d₋)} 1/φ(m rad(e)) ≍ (log X)² log z`, where `d₋ ≤ U` runs
over the odd divisors of `P(z)` and `e` over the set `E_lin` of Section 6.
-/

namespace ErdosStraus.FixedNumeratorFamily

open Classical Filter
open scoped BigOperators

/-! ## The small-divisor average -/

/-- The pairs `(s, d)` with `s ≤ S₀` squarefree and `d ≤ U` odd, `d ∣ P(z)`, `(d, s) = 1`. -/
noncomputable def smallPairs (P : Params) (X : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 ⌊SScale P X⌋₊).product (Finset.Icc 1 ⌊UScale X⌋₊)).filter
    (fun sd => Squarefree sd.1 ∧ sd.2 ∣ Estimates.roughModulus X ∧ Odd sd.2 ∧
      Nat.Coprime sd.2 sd.1)

/-- The pairs of `smallPairs` with `(s, m) = (d, m) = 1`. -/
noncomputable def numeratorSmallPairs (m : ℕ) (P : Params) (X : ℝ) :
    Finset (ℕ × ℕ) :=
  (smallPairs P X).filter (fun sd => Nat.Coprime sd.1 m ∧ Nat.Coprime sd.2 m)

/-- `∑_{(s, d)} 1/(s d) = ∑_s A_s/s`, the sum of Lemma 6.4. -/
noncomputable def numeratorSmallDivisorAverage (m : ℕ) (P : Params) (X : ℝ) : ℝ :=
  ∑ sd ∈ numeratorSmallPairs m P X, (1 : ℝ) / (sd.1 : ℝ) / (sd.2 : ℝ)

/-- `∑_{g ∣ m} 1/g`. -/
noncomputable def numeratorDivisorLoss (m : ℕ) : ℝ :=
  ∑ g ∈ m.divisors, (1 : ℝ) / (g : ℝ)

theorem numeratorDivisorLoss_pos {m : ℕ} (hm : 0 < m) :
    0 < numeratorDivisorLoss m := by
  apply Finset.sum_pos'
  · intro g _; positivity
  · exact ⟨1, Nat.mem_divisors.mpr ⟨one_dvd m, hm.ne'⟩, by norm_num⟩

theorem smallDivisorAverage_eq_pair_sum (P : Params) (X : ℝ) :
    Estimates.smallDivisorAverage P X =
      ∑ sd ∈ smallPairs P X, (1 : ℝ) / (sd.1 : ℝ) / (sd.2 : ℝ) := by
  unfold Estimates.smallDivisorAverage Estimates.smallDivisorWeight smallPairs
  simp only [Finset.sum_filter]
  erw [Finset.sum_product (Finset.Icc 1 ⌊SScale P X⌋₊) (Finset.Icc 1 ⌊UScale X⌋₊)
    (fun sd : ℕ × ℕ => if Squarefree sd.1 ∧ sd.2 ∣ Estimates.roughModulus X ∧
      Odd sd.2 ∧ Nat.Coprime sd.2 sd.1 then (1 : ℝ) / sd.1 / sd.2 else 0)]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hsq : Squarefree s
  · simp only [hsq, ite_true, true_and]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    split_ifs <;> simp_all [div_eq_mul_inv, mul_comm]
  · simp [hsq]

/-- Dividing `s` and `d` by their gcds with `m` shows that dropping the conditions
`(s, m) = (d, m) = 1` costs at most the factor `(∑_{g ∣ m} 1/g)²`. -/
theorem smallDivisorAverage_le_numeratorLoss (m : ℕ) (hm : 0 < m)
    (P : Params) (X : ℝ) :
    Estimates.smallDivisorAverage P X ≤
      numeratorDivisorLoss m ^ 2 * numeratorSmallDivisorAverage m P X := by
  let S := smallPairs P X
  let T := numeratorSmallPairs m P X
  let F : ℕ × ℕ → (ℕ × ℕ) × (ℕ × ℕ) := fun sd =>
    ((Nat.gcd sd.1 m, Nat.gcd sd.2 m),
      (sd.1 / Nat.gcd sd.1 m, sd.2 / Nat.gcd sd.2 m))
  let G : (ℕ × ℕ) × (ℕ × ℕ) → ℝ := fun t =>
    ((1 : ℝ) / t.1.1 / t.1.2) * ((1 : ℝ) / t.2.1 / t.2.2)
  have hFmem : ∀ sd ∈ S, F sd ∈ (m.divisors.product m.divisors).product T := by
    rintro ⟨s, d⟩ hsd
    obtain ⟨hbox, hsq, hdP, hodd, hds⟩ := Finset.mem_filter.mp hsd
    obtain ⟨hsbox, hdbox⟩ := Finset.mem_product.mp hbox
    have hspos : 0 < s := (Finset.mem_Icc.mp hsbox).1
    have hdpos : 0 < d := (Finset.mem_Icc.mp hdbox).1
    have hdSq : Squarefree d :=
      (Estimates.roughModulus_squarefree X).squarefree_of_dvd hdP
    have hgs : 0 < Nat.gcd s m := Nat.gcd_pos_of_pos_left m hspos
    have hgd : 0 < Nat.gcd d m := Nat.gcd_pos_of_pos_left m hdpos
    have hqs : 0 < s / Nat.gcd s m := Nat.div_pos (Nat.gcd_le_left m hspos) hgs
    have hqd : 0 < d / Nat.gcd d m := Nat.div_pos (Nat.gcd_le_left m hdpos) hgd
    have hsdiv : s / Nat.gcd s m ∣ s := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left s m)
    have hddiv : d / Nat.gcd d m ∣ d := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left d m)
    have hqodd : Odd (d / Nat.gcd d m) := by
      apply Nat.not_even_iff_odd.mp
      intro heven
      exact hodd.not_two_dvd_nat (heven.two_dvd.trans hddiv)
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right s m, hm.ne'⟩
    · exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right d m, hm.ne'⟩
    · apply Finset.mem_filter.mpr
      refine ⟨?_, Nat.coprime_div_gcd_of_squarefree hsq hm.ne',
        Nat.coprime_div_gcd_of_squarefree hdSq hm.ne'⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩,
        hsq.squarefree_of_dvd hsdiv, hddiv.trans hdP, hqodd,
        (hds.coprime_dvd_left hddiv).coprime_dvd_right hsdiv⟩
      · exact Finset.mem_Icc.mpr ⟨hqs, (Nat.div_le_self _ _).trans
          (Finset.mem_Icc.mp hsbox).2⟩
      · exact Finset.mem_Icc.mpr ⟨hqd, (Nat.div_le_self _ _).trans
          (Finset.mem_Icc.mp hdbox).2⟩
  have hFleft : ∀ sd : ℕ × ℕ,
      (F sd).1.1 * (F sd).2.1 = sd.1 ∧ (F sd).1.2 * (F sd).2.2 = sd.2 := by
    intro sd
    constructor <;> dsimp [F] <;>
      rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)]
  have hFinj : ∀ a ∈ S, ∀ b ∈ S, F a = F b → a = b := by
    intro a ha b hb hab
    apply Prod.ext
    · calc
        a.1 = (F a).1.1 * (F a).2.1 := (hFleft a).1.symm
        _ = (F b).1.1 * (F b).2.1 := by rw [hab]
        _ = b.1 := (hFleft b).1
    · calc
        a.2 = (F a).1.2 * (F a).2.2 := (hFleft a).2.symm
        _ = (F b).1.2 * (F b).2.2 := by rw [hab]
        _ = b.2 := (hFleft b).2
  have hterm : ∀ sd : ℕ × ℕ,
      (1 : ℝ) / (sd.1 : ℝ) / (sd.2 : ℝ) = G (F sd) := by
    intro sd
    have hs : ((F sd).1.1 : ℝ) * (F sd).2.1 = sd.1 := by
      exact_mod_cast (hFleft sd).1
    have hd : ((F sd).1.2 : ℝ) * (F sd).2.2 = sd.2 := by
      exact_mod_cast (hFleft sd).2
    rw [← hs, ← hd]
    dsimp [G]
    simp only [div_div, one_div_mul_one_div]
    congr 1
    ring
  rw [smallDivisorAverage_eq_pair_sum]
  change (∑ sd ∈ S, (1 : ℝ) / (sd.1 : ℝ) / (sd.2 : ℝ)) ≤ _
  calc
    _ = ∑ t ∈ S.image F, G t := by
      rw [Finset.sum_image hFinj]
      exact Finset.sum_congr rfl (fun sd _ => hterm sd)
    _ ≤ ∑ t ∈ (m.divisors.product m.divisors).product T, G t := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.image_subset_iff.mpr hFmem
      · intro t _ _; dsimp [G]; positivity
    _ = numeratorDivisorLoss m ^ 2 * numeratorSmallDivisorAverage m P X := by
      change (∑ t ∈ (m.divisors.product m.divisors).product T,
        ((1 : ℝ) / t.1.1 / t.1.2) * ((1 : ℝ) / t.2.1 / t.2.2)) = _
      erw [Finset.sum_product (m.divisors.product m.divisors) T
        (fun t : (ℕ × ℕ) × (ℕ × ℕ) =>
          ((1 : ℝ) / t.1.1 / t.1.2) * ((1 : ℝ) / t.2.1 / t.2.2))]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      congr 1
      unfold numeratorDivisorLoss
      erw [Finset.sum_product m.divisors m.divisors
        (fun gh : ℕ × ℕ => (1 : ℝ) / gh.1 / gh.2), pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro g hg
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun h hh => by ring)

theorem numeratorSmallDivisorAverage_lower (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      c * Real.log (SScale P X) * Real.log (zScale X) ≤
        numeratorSmallDivisorAverage m P X := by
  obtain ⟨c, X₀, hc, hbound⟩ := Estimates.smallDivisorAverage_lower P
  have hL : 0 < numeratorDivisorLoss m := numeratorDivisorLoss_pos hm
  refine ⟨c / numeratorDivisorLoss m ^ 2, X₀, by positivity, ?_⟩
  intro X hX
  have h := (hbound X hX).trans (smallDivisorAverage_le_numeratorLoss m hm P X)
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hL)).mp
  convert h using 1
  field_simp

/-! ## The base congruence -/

/-- The class `-b (m s²)⁻¹ mod d` of `r` in the congruence `b ≡ -m r s² (mod d)`. -/
noncomputable def numeratorBaseResidue (m b d s : ℕ) (hb : Nat.Coprime b d)
    (hcoef : Nat.Coprime (m * s ^ 2) d) : ℕ :=
  ((-(ZMod.unitOfCoprime b hb *
    (ZMod.unitOfCoprime (m * s ^ 2) hcoef)⁻¹) : (ZMod d)ˣ) : ZMod d).val

theorem numeratorBaseResidue_coprime (m b d s : ℕ) (hb : Nat.Coprime b d)
    (hcoef : Nat.Coprime (m * s ^ 2) d) :
    Nat.Coprime (numeratorBaseResidue m b d s hb hcoef) d := by
  exact ZMod.val_coe_unit_coprime
    (-(ZMod.unitOfCoprime b hb * (ZMod.unitOfCoprime (m * s ^ 2) hcoef)⁻¹))

theorem numeratorBaseResidue_sat (m b d s : ℕ) (hd : 0 < d)
    (hb : Nat.Coprime b d) (hcoef : Nat.Coprime (m * s ^ 2) d) :
    d ∣ b + m * numeratorBaseResidue m b d s hb hcoef * s ^ 2 := by
  let : NeZero d := ⟨hd.ne'⟩
  rw [← ZMod.natCast_eq_zero_iff]
  unfold numeratorBaseResidue
  push_cast
  rw [ZMod.natCast_zmod_val, ← ZMod.coe_unitOfCoprime b hb]
  have hcoefCast : (m : ZMod d) * (s : ZMod d) ^ 2 =
      ((ZMod.unitOfCoprime (m * s ^ 2) hcoef : (ZMod d)ˣ) : ZMod d) := by
    rw [ZMod.coe_unitOfCoprime]
    push_cast
    rfl
  calc
    ((ZMod.unitOfCoprime b hb : (ZMod d)ˣ) : ZMod d) +
        m * -(((ZMod.unitOfCoprime b hb : (ZMod d)ˣ) : ZMod d) *
          (((ZMod.unitOfCoprime (m * s ^ 2) hcoef)⁻¹ : (ZMod d)ˣ) : ZMod d)) *
          (s : ZMod d) ^ 2 =
      ((ZMod.unitOfCoprime b hb : (ZMod d)ˣ) : ZMod d) -
        ((ZMod.unitOfCoprime b hb : (ZMod d)ˣ) : ZMod d) *
          (((ZMod.unitOfCoprime (m * s ^ 2) hcoef : (ZMod d)ˣ) : ZMod d) *
            (((ZMod.unitOfCoprime (m * s ^ 2) hcoef)⁻¹ : (ZMod d)ˣ) : ZMod d)) := by
              rw [← hcoefCast]
              ring
    _ = 0 := by rw [← Units.val_mul]; simp

/-- `numeratorBaseResidue`, or `1` when `b` or `m s²` is not invertible modulo `d`. -/
noncomputable def numeratorBaseResidueTotal (m b d s : ℕ) : ℕ :=
  if h : Nat.Coprime b d ∧ Nat.Coprime (m * s ^ 2) d then
    numeratorBaseResidue m b d s h.1 h.2
  else 1

/-- `Σ_b` as a sum over the pairs `(s, d)` of the progression sums of Lemma 6.1. -/
noncomputable def numeratorSmallCertificateMass (m : ℕ) (P : Params) (X : ℝ)
    (b : ℕ) : ℝ :=
  ∑ sd ∈ numeratorSmallPairs m P X,
    numeratorPhiAverage m P X sd.2 (numeratorBaseResidueTotal m b sd.2 sd.1) sd.1

theorem numeratorSmallCertificateMass_ge_log_average (m : ℕ) (hm : 0 < m)
    (P : Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X → ∀ b : ℕ,
      Nat.Coprime b (Estimates.roughModulus X) →
      c * Real.log X * numeratorSmallDivisorAverage m P X ≤
        numeratorSmallCertificateMass m P X b := by
  obtain ⟨cφ, Xφ, hcφ, hφ⟩ := numeratorPhiAverage_lower m hm P
  obtain ⟨cL, CL, XL, hcL, hCL, hL⟩ := slantLogLength_uniform_bounds P
  refine ⟨cφ * cL, max Xφ XL, mul_pos hcφ hcL, ?_⟩
  intro X hX hXgt b hbP
  unfold numeratorSmallDivisorAverage numeratorSmallCertificateMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  rintro ⟨s, d⟩ hsd
  obtain ⟨hsd, hsm, hdm⟩ := Finset.mem_filter.mp hsd
  obtain ⟨hbox, hsq, hdP, hodd, hds⟩ := Finset.mem_filter.mp hsd
  obtain ⟨hsbox, hdbox⟩ := Finset.mem_product.mp hbox
  obtain ⟨hspos, hsmax⟩ := Finset.mem_Icc.mp hsbox
  obtain ⟨hdpos, hdmax⟩ := Finset.mem_Icc.mp hdbox
  have hsS : (s : ℝ) ≤ SScale P X :=
    (Nat.cast_le.mpr hsmax).trans (Nat.floor_le (Real.rpow_nonneg (by linarith) _))
  have hdU : (d : ℝ) ≤ UScale X :=
    (Nat.cast_le.mpr hdmax).trans (Nat.floor_le (by unfold UScale; positivity))
  have hdSq := (Estimates.roughModulus_squarefree X).squarefree_of_dvd hdP
  have hcoef : Nat.Coprime (m * s ^ 2) d :=
    Nat.coprime_mul_iff_left.mpr ⟨hdm.symm,
      (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) s d).mpr hds.symm⟩
  have hbd := hbP.coprime_dvd_right hdP
  have hres : numeratorBaseResidueTotal m b d s =
      numeratorBaseResidue m b d s hbd hcoef := by
    rw [numeratorBaseResidueTotal, dif_pos ⟨hbd, hcoef⟩]
  have hrescop : Nat.Coprime (numeratorBaseResidueTotal m b d s) d := by
    rw [hres]
    exact numeratorBaseResidue_coprime _ _ _ _ _ _
  have hφsd := hφ X ((le_max_left _ _).trans hX) d
    (numeratorBaseResidueTotal m b d s) s hdpos hdSq hdU hrescop hspos hsq hsS hsm
      (Nat.coprime_mul_iff_left.mpr ⟨hds.symm, hdm.symm⟩)
  have hlen := (hL X ((le_max_right _ _).trans hX) s hspos hsS).1
  apply le_trans _ hφsd
  calc
    cφ * cL * Real.log X * ((1 : ℝ) / s / d) =
        cφ * ((cL * Real.log X) / ((s : ℝ) * d)) := by ring
    _ ≤ cφ * (slantLogLength P s X / ((s : ℝ) * d)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hlen (by positivity)) hcφ.le

theorem numeratorSmallCertificateMass_lower (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X → ∀ b : ℕ,
      Nat.Coprime b (Estimates.roughModulus X) →
      c * Real.log X * Real.log (SScale P X) * Real.log (zScale X) ≤
        numeratorSmallCertificateMass m P X b := by
  obtain ⟨cφ, Xφ, hcφ, hφ⟩ := numeratorSmallCertificateMass_ge_log_average m hm P
  obtain ⟨cA, XA, hcA, hA⟩ := numeratorSmallDivisorAverage_lower m hm P
  refine ⟨cφ * cA, max Xφ XA, mul_pos hcφ hcA, ?_⟩
  intro X hX hXgt b hb
  have h := mul_le_mul_of_nonneg_left (hA X ((le_max_right _ _).trans hX))
    (show 0 ≤ cφ * Real.log X from mul_nonneg hcφ.le (Real.log_nonneg hXgt.le))
  calc
    cφ * cA * Real.log X * Real.log (SScale P X) * Real.log (zScale X) =
        (cφ * Real.log X) * (cA * Real.log (SScale P X) * Real.log (zScale X)) := by ring
    _ ≤ (cφ * Real.log X) * numeratorSmallDivisorAverage m P X := h
    _ ≤ numeratorSmallCertificateMass m P X b :=
      hφ X ((le_max_left _ _).trans hX) hXgt b hb

theorem numeratorBaseResidueTotal_cong_iff (m b d s r : ℕ) (hd : 0 < d)
    (hb : Nat.Coprime b d) (hcoef : Nat.Coprime (m * s ^ 2) d) :
    Estimates.congMod r (numeratorBaseResidueTotal m b d s) d ↔
      d ∣ b + m * r * s ^ 2 := by
  have hres : numeratorBaseResidueTotal m b d s =
      numeratorBaseResidue m b d s hb hcoef := by
    rw [numeratorBaseResidueTotal, dif_pos ⟨hb, hcoef⟩]
  have hbase : b + m * numeratorBaseResidueTotal m b d s * s ^ 2 ≡ 0 [MOD d] := by
    rw [hres]
    exact Nat.modEq_zero_iff_dvd.mpr (numeratorBaseResidue_sat m b d s hd hb hcoef)
  constructor
  · intro hr
    have hmul := (show r ≡ numeratorBaseResidueTotal m b d s [MOD d] from hr).mul_left
      (m * s ^ 2)
    have hadd := hmul.add_left b
    have hprod : ∀ a : ℕ, m * s ^ 2 * a = m * a * s ^ 2 := by intro a; ring
    simp only [hprod] at hadd
    exact Nat.modEq_zero_iff_dvd.mp (hadd.trans hbase)
  · intro hr
    have hh := (Nat.modEq_zero_iff_dvd.mpr hr).trans hbase.symm
    have hh' := Nat.ModEq.add_left_cancel' b hh
    have hprod : ∀ a : ℕ, m * a * s ^ 2 = (m * s ^ 2) * a := by intro a; ring
    simp only [hprod] at hh'
    exact Nat.ModEq.cancel_left_of_coprime hcoef.symm.gcd_eq_one hh'

theorem numeratorSmallCertificateMass_eq_congruence_sum
    (m : ℕ) (P : Params) (X : ℝ) (b : ℕ)
    (hb : Nat.Coprime b (Estimates.roughModulus X)) :
    numeratorSmallCertificateMass m P X b =
      ∑ sd ∈ numeratorSmallPairs m P X,
        ∑ r ∈ (numeratorRRange m P X 1 0 sd.1).filter
          (fun r => sd.2 ∣ b + m * r * sd.1 ^ 2),
          (1 : ℝ) / Nat.totient (m * sd.1 * r) := by
  unfold numeratorSmallCertificateMass numeratorPhiAverage
  apply Finset.sum_congr rfl
  rintro ⟨s, d⟩ hsd
  obtain ⟨hsd, hsm, hdm⟩ := Finset.mem_filter.mp hsd
  obtain ⟨hbox, hsq, hdP, hodd, hds⟩ := Finset.mem_filter.mp hsd
  have hd := (Finset.mem_Icc.mp (Finset.mem_product.mp hbox).2).1
  have hcoef : Nat.Coprime (m * s ^ 2) d :=
    Nat.coprime_mul_iff_left.mpr ⟨hdm.symm,
      (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) s d).mpr hds.symm⟩
  congr 1
  ext r
  simp only [numeratorRRange, Finset.mem_filter]
  simp only [Estimates.congMod, Nat.mod_one]
  have hh := numeratorBaseResidueTotal_cong_iff m b d s r hd
    (hb.coprime_dvd_right hdP) hcoef
  change (_ ∧ _ ∧ _ ∧ Estimates.congMod r (numeratorBaseResidueTotal m b d s) d) ↔ _
  rw [hh]
  tauto

theorem numeratorSmallDivisorAverage_le_ordinary (m : ℕ) (P : Params) (X : ℝ) :
    numeratorSmallDivisorAverage m P X ≤ Estimates.smallDivisorAverage P X := by
  rw [smallDivisorAverage_eq_pair_sum]
  unfold numeratorSmallDivisorAverage numeratorSmallPairs
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (by intro sd _ _; positivity)

/-- Lemma 6.4: `∑_s A_s/s ≍ log S₀ log z`. -/
theorem numeratorSmallDivisorAverage_two_sided (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * Real.log (SScale P X) * Real.log (zScale X) ≤
        numeratorSmallDivisorAverage m P X ∧
      numeratorSmallDivisorAverage m P X ≤
        C * Real.log (SScale P X) * Real.log (zScale X) := by
  obtain ⟨c, Xl, hc, hl⟩ := numeratorSmallDivisorAverage_lower m hm P
  obtain ⟨C, Xu, hC, hu⟩ := Estimates.smallDivisorAverage_upper P
  refine ⟨c, C, max Xl Xu, hc, hC, ?_⟩
  intro X hX
  exact ⟨hl X ((le_max_left _ _).trans hX),
    (numeratorSmallDivisorAverage_le_ordinary m P X).trans
      (hu X ((le_max_right _ _).trans hX))⟩

theorem numeratorSmallCertificateMass_le_log_average (m : ℕ) (hm : 0 < m)
    (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X → ∀ b : ℕ,
      Nat.Coprime b (Estimates.roughModulus X) →
      numeratorSmallCertificateMass m P X b ≤
        C * Real.log X * numeratorSmallDivisorAverage m P X := by
  obtain ⟨Cφ, Xφ, hCφ, hφ⟩ := numeratorPhiAverage_upper m hm P
  obtain ⟨cL, CL, XL, hcL, hCL, hL⟩ := slantLogLength_uniform_bounds P
  refine ⟨Cφ * CL, max Xφ XL, mul_pos hCφ hCL, ?_⟩
  intro X hX hXgt b hbP
  unfold numeratorSmallDivisorAverage numeratorSmallCertificateMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  rintro ⟨s, d⟩ hsd
  obtain ⟨hsd, hsm, hdm⟩ := Finset.mem_filter.mp hsd
  obtain ⟨hbox, hsq, hdP, hodd, hds⟩ := Finset.mem_filter.mp hsd
  obtain ⟨hsbox, hdbox⟩ := Finset.mem_product.mp hbox
  obtain ⟨hspos, hsmax⟩ := Finset.mem_Icc.mp hsbox
  obtain ⟨hdpos, hdmax⟩ := Finset.mem_Icc.mp hdbox
  have hsS : (s : ℝ) ≤ SScale P X :=
    (Nat.cast_le.mpr hsmax).trans (Nat.floor_le (Real.rpow_nonneg (by linarith) _))
  have hdU : (d : ℝ) ≤ UScale X :=
    (Nat.cast_le.mpr hdmax).trans (Nat.floor_le (by unfold UScale; positivity))
  have hcoef : Nat.Coprime (m * s ^ 2) d :=
    Nat.coprime_mul_iff_left.mpr ⟨hdm.symm,
      (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) s d).mpr hds.symm⟩
  have hbd := hbP.coprime_dvd_right hdP
  have hres : numeratorBaseResidueTotal m b d s =
      numeratorBaseResidue m b d s hbd hcoef := by
    rw [numeratorBaseResidueTotal, dif_pos ⟨hbd, hcoef⟩]
  have hrescop : Nat.Coprime (numeratorBaseResidueTotal m b d s) d := by
    rw [hres]
    exact numeratorBaseResidue_coprime _ _ _ _ _ _
  have hφsd := hφ X ((le_max_left _ _).trans hX) d
    (numeratorBaseResidueTotal m b d s) s hdpos hdU hrescop hspos hsS hds.symm hsm
  have hlen := (hL X ((le_max_right _ _).trans hX) s hspos hsS).2
  calc
    _ ≤ Cφ * (slantLogLength P s X / ((s : ℝ) * d)) := hφsd
    _ ≤ Cφ * ((CL * Real.log X) / ((s : ℝ) * d)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hlen (by positivity)) hCφ.le
    _ = _ := by ring

theorem numeratorSmallCertificateMass_two_sided (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X → ∀ b : ℕ,
      Nat.Coprime b (Estimates.roughModulus X) →
      c * Real.log X * Real.log (SScale P X) * Real.log (zScale X) ≤
        numeratorSmallCertificateMass m P X b ∧
      numeratorSmallCertificateMass m P X b ≤
        C * Real.log X * Real.log (SScale P X) * Real.log (zScale X) := by
  obtain ⟨c, Xl, hc, hl⟩ := numeratorSmallCertificateMass_lower m hm P
  obtain ⟨Cφ, Xφ, hCφ, hφ⟩ := numeratorSmallCertificateMass_le_log_average m hm P
  obtain ⟨CA, XA, hCA, hA⟩ := Estimates.smallDivisorAverage_upper P
  refine ⟨c, Cφ * CA, max Xl (max Xφ XA), hc, mul_pos hCφ hCA, ?_⟩
  intro X hX hXgt b hb
  refine ⟨hl X ((le_max_left _ _).trans hX) hXgt b hb, ?_⟩
  have hupper := (numeratorSmallDivisorAverage_le_ordinary m P X).trans
    (hA X ((le_max_right Xφ XA).trans ((le_max_right _ _).trans hX)))
  calc
    _ ≤ Cφ * Real.log X * numeratorSmallDivisorAverage m P X :=
      hφ X ((le_max_left Xφ XA).trans ((le_max_right _ _).trans hX)) hXgt b hb
    _ ≤ Cφ * Real.log X *
        (CA * Real.log (SScale P X) * Real.log (zScale X)) :=
      mul_le_mul_of_nonneg_left hupper (mul_nonneg hCφ.le (Real.log_nonneg hXgt.le))
    _ = _ := by ring

/-- Lemma 6.5, for `Σ_b` written as `numeratorSmallCertificateMass`. -/
theorem saturation_average (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → ∀ b : ℕ,
      Nat.Coprime b (Estimates.roughModulus X) →
      c * (Real.log X) ^ 2 * Real.log (zScale X) ≤
        numeratorSmallCertificateMass m P X b ∧
      numeratorSmallCertificateMass m P X b ≤
        C * (Real.log X) ^ 2 * Real.log (zScale X) := by
  obtain ⟨c, C, X₀, hc, hC, h⟩ := numeratorSmallCertificateMass_two_sided m hm P
  refine ⟨c * P.η, C * P.η, max X₀ (Real.exp 1),
    mul_pos hc P.η_pos, mul_pos hC P.η_pos, ?_⟩
  intro X hX b hb
  have hXe : Real.exp 1 ≤ X := (le_max_right _ _).trans hX
  have hX1 : 1 < X := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hXe
  have hh := h X ((le_max_left _ _).trans hX) hX1 b hb
  rw [log_SScale P (zero_lt_one.trans hX1)] at hh
  convert hh using 1 <;> ring_nf

end ErdosStraus.FixedNumeratorFamily

/-! ## The sum `Σ_b` -/

namespace ErdosStraus.FixedNumeratorFamily

open Classical
open scoped BigOperators

/-- The odd `d ≤ U` with `d ∣ P(z)`. -/
noncomputable def smallOddDivisors (X : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊UScale X⌋₊).filter
    (fun d => d ∣ Estimates.roughModulus X ∧ Odd d)

/-- `Σ_b = ∑_{d₋} ∑_{e : b ≡ -m e (mod d₋)} 1/φ(m rad(e))`, the sum of Lemma 6.5. -/
noncomputable def saturationMass (m : ℕ) (P : Params) (X : ℝ) (b : ℕ) : ℝ :=
  ∑ d ∈ smallOddDivisors X,
    ∑ x ∈ (numeratorDivisorSupport m P X).filter
      (fun x => d ∣ b + m * x.2 * x.1 ^ 2),
      (1 : ℝ) / Nat.totient (m * x.1 * x.2)

theorem base_congruence_coprime {m b d s r : ℕ}
    (hb : Nat.Coprime b d) (h : d ∣ b + m * r * s ^ 2) :
    Nat.Coprime d s ∧ Nat.Coprime d m := by
  have hcop : Nat.Coprime (m * r * s ^ 2) d := by
    apply Nat.coprime_iff_gcd_eq_one.mpr
    apply Nat.eq_one_of_dvd_coprimes hb
    · have hg : Nat.gcd (m * r * s ^ 2) d ∣ b + m * r * s ^ 2 :=
        (Nat.gcd_dvd_right _ _).trans h
      simpa using Nat.dvd_sub hg (Nat.gcd_dvd_left (m * r * s ^ 2) d)
    · exact Nat.gcd_dvd_right _ _
  refine ⟨(hcop.coprime_dvd_left ?_).symm, (hcop.coprime_dvd_left ?_).symm⟩
  · exact dvd_mul_of_dvd_right (dvd_pow_self s (by norm_num : 2 ≠ 0)) (m * r)
  · exact dvd_mul_of_dvd_left (dvd_mul_right m r) _

theorem saturationMass_eq_certificate (m : ℕ) (P : Params) (X : ℝ) (b : ℕ)
    (hb : Nat.Coprime b (Estimates.roughModulus X)) :
    saturationMass m P X b = numeratorSmallCertificateMass m P X b := by
  rw [numeratorSmallCertificateMass_eq_congruence_sum m P X b hb]
  unfold saturationMass numeratorDivisorSupport
  simp_rw [Finset.sum_filter, Finset.sum_sigma]
  unfold numeratorSmallPairs smallPairs
  simp_rw [Finset.sum_filter]
  erw [Finset.sum_product]
  rw [Finset.sum_comm]
  unfold smallOddDivisors exactDivisorSRange
  simp_rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hsq : Squarefree s
  · simp only [hsq, ite_true, true_and]
    by_cases hsm : Nat.Coprime s m
    · apply Finset.sum_congr rfl
      intro d hd
      by_cases hdP : d ∣ Estimates.roughModulus X
      · by_cases hodd : Odd d
        · by_cases hds : Nat.Coprime d s
          · by_cases hdm : Nat.Coprime d m
            · simp only [hdP, hodd, true_and, ite_true]
              split_ifs <;> first | rfl | tauto
            · simp only [hdP, hodd, hdm, and_self, and_false, true_and, ite_false, ite_true]
              split_ifs
              apply Finset.sum_eq_zero
              intro r hr
              split_ifs with hcong
              · exact False.elim (hdm (base_congruence_coprime
                  (hb.coprime_dvd_right hdP) hcong).2)
              · rfl
          · simp only [hdP, hodd, hds, and_self, and_false, ite_false, ite_true]
            split_ifs
            apply Finset.sum_eq_zero
            intro r hr
            split_ifs with hcong
            · exact False.elim (hds (base_congruence_coprime
                (hb.coprime_dvd_right hdP) hcong).1)
            · rfl
        · simp [hdP, hodd]
      · simp [hdP]
    · simp [hsm]
  · simp [hsq]

/-- Lemma 6.5: `Σ_b ≍ (log X)² log z`, uniformly in the reduced classes `b`. -/
theorem saturationMass_two_sided (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → ∀ b : ℕ,
      Nat.Coprime b (Estimates.roughModulus X) →
      c * (Real.log X) ^ 2 * Real.log (zScale X) ≤ saturationMass m P X b ∧
      saturationMass m P X b ≤ C * (Real.log X) ^ 2 * Real.log (zScale X) := by
  obtain ⟨c, C, X₀, hc, hC, h⟩ := saturation_average m hm P
  refine ⟨c, C, X₀, hc, hC, ?_⟩
  intro X hX b hb
  rw [saturationMass_eq_certificate m P X b hb]
  exact h X hX b hb

end ErdosStraus.FixedNumeratorFamily
