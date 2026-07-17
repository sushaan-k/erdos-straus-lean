import EscAnalytic.Family
import EscAnalytic.Inputs
import EscAnalytic.MassEstimates
import EscAnalytic.BrunSuen
import EscAnalytic.Optimization

/-!
# Increment and roughness estimates

This file specializes the elementary increment bounds in `Family` to the
manuscript's actual rough modulus `P(z)`.  No analytic estimate is assumed:
the only ingredients are the explicit finite prime product, family
coprimality, and elementary logarithmic bounds for prime factors.
-/

namespace EscAnalytic

open Classical

/-- Every prime below `floor(z)+1` divides the manuscript's finite prime
product `P(z)`. -/
theorem prime_dvd_roughModulus_of_lt_succ_floor
    {X : ℝ} {p : ℕ} (hp : Nat.Prime p)
    (hlt : p < ⌊EscAnalytic.zScale X⌋₊ + 1) :
    p ∣ Inputs.roughModulus X := by
  exact Inputs.prime_dvd_primeProductBelow_of_le_floor
    (EscAnalytic.zScale X) p hp (by omega)

/-- For `X ≥ e`, the actual rough cutoff `floor(z(X))+1` is at least two. -/
theorem two_le_succ_floor_zScale
    {X : ℝ} (hX : Real.exp 1 ≤ X) :
    2 ≤ ⌊EscAnalytic.zScale X⌋₊ + 1 := by
  have hz : 1 ≤ EscAnalytic.zScale X :=
    Inputs.zScale_ge_one_of_exp_one_le hX
  have hfloor : 1 ≤ ⌊EscAnalytic.zScale X⌋₊ :=
    Nat.le_floor (by simpa using hz)
  omega

/-- Eventually the rough-prime cutoff lies below the selected-prime scale. -/
theorem floor_zScale_lt_primeScale_eventually (P : Params) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ((⌊zScale X⌋₊ : ℕ) : ℝ) < X ^ P.β := by
  rcases Inputs.eventually_UScale_le_rpow
      (δ := P.β / 2) (by linarith [P.β_pos]) with ⟨XU, hU⟩
  refine ⟨max XU (Real.exp 1), ?_⟩
  intro X hX
  have hXU : XU ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXgt : 1 < X := lt_of_lt_of_le
    (Real.one_lt_exp_iff.mpr (by norm_num)) hXexp
  have hlog : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (lt_trans zero_lt_one hXgt)]
    exact hXexp
  have hzU : zScale X ≤ UScale X := by
    unfold zScale UScale
    exact pow_le_pow_right₀ hlog (by omega)
  have hfloor : ((⌊zScale X⌋₊ : ℕ) : ℝ) ≤ zScale X :=
    Nat.floor_le (by unfold zScale; positivity)
  have hhalf : X ^ (P.β / 2) < X ^ P.β :=
    Real.rpow_lt_rpow_of_exponent_lt hXgt (by linarith [P.β_pos])
  exact lt_of_le_of_lt (hfloor.trans (hzU.trans (hU X hXU))) hhalf

/-- Actual-family finite Bonferroni decomposition over the rough modulus.  Both
the main alternating term and endpoint error use the true compatible-LCM
coefficients. -/
theorem actualPaperFamily_baseNoHitRat_le_lcmMain_add_endpoint
    (P : Params) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → 1 < X →
      ∀ N b R : ℕ,
      (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N
        (Inputs.roughModulus X) b
        (Family.familyEvents (Family.familyIndexFinset P X
          (Inputs.roughModulus X) b)) : ℚ) ≤
      (N : ℚ) / (Inputs.roughModulus X : ℚ) *
          (∑ r ∈ Finset.range (2 * R + 1),
            (-1 : ℚ) ^ r * Family.familyCompatibleLcmMassRat
              (Family.familyIndexFinset P X (Inputs.roughModulus X) b) r) +
        ∑ r ∈ Finset.range (2 * R + 1),
          (⌊X⌋₊ : ℚ) ^ r * Family.familyCompatibleLcmMassRat
            (Family.familyIndexFinset P X (Inputs.roughModulus X) b) r := by
  rcases floor_zScale_lt_primeScale_eventually P with ⟨X₀, hcut⟩
  refine ⟨X₀, ?_⟩
  intro X hX hXgt N b R
  let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
  have hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X (Inputs.roughModulus X) b i := by
    intro i hi
    exact (Family.mem_familyIndexFinset_iff P X
      (Inputs.roughModulus X) b i (lt_trans zero_lt_one hXgt)).1 hi
  apply Family.familyBaseNoHitRat_le_lcmMain_add_endpoint
    P X N (Inputs.roughModulus X) b R indices hXgt
      (Inputs.roughModulus_pos X) hmem
  exact Family.actualPaperFamily_eventPrime_coprime_Pz P X ⌊zScale X⌋₊
    (Inputs.roughModulus X) b
    (fun q hq hdiv => Inputs.prime_dvd_roughModulus_le_floor_zScale X hq hdiv)
    hXgt (hcut X hX)

/-- After writing an actual rough cofactor as `dplus = D * t`, the quotient
`t` belongs to the paper's initial rough reciprocal carrier at exponent
`sigma`, with the exact auxiliary coprimality `4 * rho(e)`. -/
theorem Family.FamilyStaticMem.dplus_div_mem_roughInitial_support
    {P : Params} {X : ℝ} {b D : ℕ} {i : Family.FamilyIndex}
    (hX : 1 < X)
    (hmem : Family.FamilyStaticMem P X (Inputs.roughModulus X) b i)
    (hD : 0 < D) (hDdvd : D ∣ i.dplus) :
    i.dplus / D ∈
      (Finset.Icc (1 : ℕ) ⌊X ^ P.σ⌋₊).filter
        (fun t => Squarefree t ∧
          Nat.Coprime t (Inputs.roughModulus X) ∧
          Nat.Coprime t (Inputs.auxiliaryModulus (4 * i.rho))) := by
  have htDvd : i.dplus / D ∣ i.dplus := Nat.div_dvd_of_dvd hDdvd
  have htpos : 0 < i.dplus / D :=
    Nat.div_pos (Nat.le_of_dvd hmem.dplus_pos hDdvd) hD
  have htSqf : Squarefree (i.dplus / D) :=
    hmem.dplus_squarefree.squarefree_of_dvd htDvd
  have htRough : Nat.Coprime (i.dplus / D) (Inputs.roughModulus X) :=
    hmem.dplus_coprime_Pz.coprime_dvd_left htDvd
  have hdplusCopRho : Nat.Coprime i.dplus (4 * i.rho) :=
    hmem.dd_coprime_four_rho.coprime_dvd_left (dvd_mul_left i.dplus i.dminus)
  have htRho : Nat.Coprime (i.dplus / D) (4 * i.rho) :=
    hdplusCopRho.coprime_dvd_left htDvd
  have hauxPos : 0 < 4 * i.rho := by
    have hrho : 0 < i.rho := by
      unfold Family.FamilyIndex.rho EscAnalytic.ExactDivisor.rho
      have hs : 0 < i.E.s := lt_of_lt_of_le Nat.zero_lt_one hmem.s_pos
      have hr : 0 < i.E.r := hmem.r_pos hX
      exact Nat.mul_pos hr hs
    positivity
  have htAux : Nat.Coprime (i.dplus / D)
      (Inputs.auxiliaryModulus (4 * i.rho)) := by
    rw [Inputs.auxiliaryModulus_eq_self_of_pos hauxPos]
    exact htRho
  have htLe : i.dplus / D ≤ ⌊X ^ P.σ⌋₊ := by
    have hdplusLe : i.dplus ≤ ⌊X ^ P.σ⌋₊ := by
      exact Nat.le_floor (by simpa [YScale] using hmem.dplus_le_YScale)
    exact (Nat.div_le_self i.dplus D).trans hdplusLe
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr htpos, htLe⟩,
      htSqf, htRough, htAux⟩

/-- The conductor coordinate of an actual family member is below the
manuscript conductor scale `H = X^theta`. -/
theorem Family.FamilyStaticMem.rho_le_HScale
    {P : Params} {X : ℝ} {Pz b : ℕ} {i : Family.FamilyIndex}
    (hX : 1 < X)
    (hmem : Family.FamilyStaticMem P X Pz b i) :
    (i.rho : ℝ) ≤ HScale P X := by
  have hs_nat : 1 ≤ i.E.s := hmem.s_pos
  have hs_real : (1 : ℝ) ≤ (i.E.s : ℝ) := by exact_mod_cast hs_nat
  have hs_pos : 0 < (i.E.s : ℝ) := lt_of_lt_of_le zero_lt_one hs_real
  have hs_sq_pos : 0 < (i.E.s : ℝ) ^ 2 := sq_pos_of_pos hs_pos
  have hr_pos : 0 < (i.E.r : ℝ) := by
    exact_mod_cast hmem.r_pos hX
  have hrs_le_hrsq :
      (i.E.r : ℝ) * (i.E.s : ℝ) ≤
        (i.E.r : ℝ) * (i.E.s : ℝ) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ hr_pos.le
    nlinarith
  have hrsq_le_H :
      (i.E.r : ℝ) * (i.E.s : ℝ) ^ 2 ≤ HScale P X := by
    exact (le_div_iff₀ hs_sq_pos).mp hmem.r_le
  simpa [Family.FamilyIndex.rho, ExactDivisor.rho, Nat.cast_mul] using
    hrs_le_hrsq.trans hrsq_le_H

/-- Rough cofactors occurring over a fixed exact divisor and small factor.
The prime coordinate is deliberately forgotten after the Brun--Titchmarsh
prime sum has been bounded. -/
noncomputable def familyDplusValues
    (indices : Finset Family.FamilyIndex) (E : ExactDivisor) (dminus : ℕ) :
    Finset ℕ :=
  (indices.filter (fun i => i.E = E ∧ i.dminus = dminus)).image
    (fun i => i.dplus)

/-- Prime coordinates occurring over a fixed `(e,dminus,dplus)` fiber. -/
noncomputable def familyPrimeValues
    (indices : Finset Family.FamilyIndex) (E : ExactDivisor)
    (dminus dplus : ℕ) : Finset ℕ :=
  (indices.filter
      (fun i => i.E = E ∧ i.dminus = dminus ∧ i.dplus = dplus)).image
    (fun i => i.p)

/-- Actual reciprocal mass over one `(e,dminus)` fiber with `D | dplus`. -/
noncomputable def familyFixedEDminusDivisorMass
    (indices : Finset Family.FamilyIndex) (E : ExactDivisor)
    (dminus D : ℕ) : ℝ :=
  ∑ i ∈ indices.filter
      (fun i => i.E = E ∧ i.dminus = dminus ∧ D ∣ i.dplus),
    (1 : ℝ) / ((i.dplus * i.p : ℕ) : ℝ)

/-- Exact-divisor coordinates represented by a finite family. -/
noncomputable def familyExactValues
    (indices : Finset Family.FamilyIndex) : Finset ExactDivisor :=
  indices.image (fun i => i.E)

/-- Small-divisor coordinates represented over one exact-divisor coordinate. -/
noncomputable def familyDminusValues
    (indices : Finset Family.FamilyIndex) (E : ExactDivisor) : Finset ℕ :=
  (indices.filter (fun i => i.E = E)).image (fun i => i.dminus)

/-- The represented large cofactors of the complete paper family lie in the
same positive interval used to prove finiteness of that family. -/
theorem actualPaperFamily_familyDplusValues_subset_Icc
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 0 < X)
    (E : ExactDivisor) (dminus : ℕ) :
    familyDplusValues (Family.familyIndexFinset P X Pz b) E dminus ⊆
      Finset.Icc (1 : ℕ) ⌊YScale P X⌋₊ := by
  intro dplus hdplus
  rcases Finset.mem_image.mp hdplus with ⟨i, hi, rfl⟩
  have hiFamily : i ∈ Family.familyIndexFinset P X Pz b :=
    (Finset.mem_filter.mp hi).1
  have himem : Family.FamilyStaticMem P X Pz b i :=
    (Family.mem_familyIndexFinset_iff P X Pz b i hX).1 hiFamily
  exact Finset.mem_Icc.mpr
    ⟨himem.dplus_pos, Nat.le_floor himem.dplus_le_YScale⟩

/-- The reciprocal weight of every represented large-cofactor fiber is at
most the full harmonic sum at the manuscript cutoff. -/
theorem actualPaperFamily_familyDplusValues_recip_le_harmonic
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 0 < X)
    (E : ExactDivisor) (dminus : ℕ) :
    (∑ dplus ∈ familyDplusValues
        (Family.familyIndexFinset P X Pz b) E dminus,
      (1 : ℝ) / (dplus : ℝ)) ≤
      (harmonic ⌊YScale P X⌋₊ : ℝ) := by
  classical
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  simp_rw [one_div]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact actualPaperFamily_familyDplusValues_subset_Icc P X Pz b hX E dminus
  · intro n _hnBig _hnSmall
    exact inv_nonneg.mpr (Nat.cast_nonneg n)

/-- The represented small cofactors of the complete paper family lie in their
defining positive interval. -/
theorem actualPaperFamily_familyDminusValues_subset_Icc
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 0 < X)
    (E : ExactDivisor) :
    familyDminusValues (Family.familyIndexFinset P X Pz b) E ⊆
      Finset.Icc (1 : ℕ) ⌊UScale X⌋₊ := by
  intro dminus hdminus
  rcases Finset.mem_image.mp hdminus with ⟨i, hi, rfl⟩
  have hiFamily : i ∈ Family.familyIndexFinset P X Pz b :=
    (Finset.mem_filter.mp hi).1
  have himem : Family.FamilyStaticMem P X Pz b i :=
    (Family.mem_familyIndexFinset_iff P X Pz b i hX).1 hiFamily
  exact Finset.mem_Icc.mpr
    ⟨himem.dminus_pos, Nat.le_floor himem.dminus_le_U⟩

/-- There are at most `floor(U)` represented small cofactors over a fixed
exact-divisor coordinate. -/
theorem actualPaperFamily_familyDminusValues_card_le
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 0 < X)
    (E : ExactDivisor) :
    (familyDminusValues
      (Family.familyIndexFinset P X Pz b) E).card ≤ ⌊UScale X⌋₊ := by
  refine le_trans (Finset.card_le_card
    (actualPaperFamily_familyDminusValues_subset_Icc P X Pz b hX E)) ?_
  cases ⌊UScale X⌋₊ <;> simp

/-! ## Prime-independent support of the complete paper family -/

/-- A paper-family coordinate before the prime in its certificate progression
is chosen.  This support must be independent of whether that progression
already contains a prime in the prescribed window. -/
structure FamilyPrePrimeIndex where
  E : ExactDivisor
  dminus : ℕ
  dplus : ℕ

namespace FamilyPrePrimeIndex

/-- Adjoin a prime candidate to a pre-prime family coordinate. -/
def withPrime (j : FamilyPrePrimeIndex) (p : ℕ) : Family.FamilyIndex where
  E := j.E
  dminus := j.dminus
  dplus := j.dplus
  p := p

end FamilyPrePrimeIndex

/-- Static paper-family conditions that do not involve the prime coordinate. -/
structure FamilyPrePrimeMem
    (P : Params) (X : ℝ) (Pz b : ℕ) (j : FamilyPrePrimeIndex) : Prop where
  s_pos : 1 ≤ j.E.s
  s_le_S : (j.E.s : ℝ) ≤ SScale P X
  r_gt : Y0Scale P X / (j.E.s : ℝ) < (j.E.r : ℝ)
  r_le : (j.E.r : ℝ) ≤ HScale P X / ((j.E.s : ℝ) ^ 2)
  dminus_pos : 0 < j.dminus
  dminus_le_U : (j.dminus : ℝ) ≤ UScale X
  dminus_dvd_Pz : j.dminus ∣ Pz
  dminus_squarefree : Squarefree j.dminus
  dminus_odd : Odd j.dminus
  base_cong : b + 4 * j.E.e ≡ 0 [MOD j.dminus]
  dplus_pos : 0 < j.dplus
  dplus_squarefree : Squarefree j.dplus
  dd_le_Y : (j.dminus * j.dplus : ℝ) ≤ YScale P X
  dplus_coprime_Pz : Nat.Coprime j.dplus Pz
  dd_coprime_four_rho :
    Nat.Coprime (j.dminus * j.dplus) (4 * j.E.rho)

/-- The reduced conductor of a pre-prime structural coordinate is below the
paper's conductor scale. -/
theorem FamilyPrePrimeMem.rho_le_HScale
    {P : Params} {X : ℝ} {Pz b : ℕ} {j : FamilyPrePrimeIndex}
    (hmem : FamilyPrePrimeMem P X Pz b j) :
    (j.E.rho : ℝ) ≤ HScale P X := by
  have hs : (1 : ℝ) ≤ (j.E.s : ℝ) := by exact_mod_cast hmem.s_pos
  have hr_nonneg : 0 ≤ (j.E.r : ℝ) := Nat.cast_nonneg _
  have hrs_le : (j.E.r : ℝ) * (j.E.s : ℝ) ≤
      (j.E.r : ℝ) * (j.E.s : ℝ) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ hr_nonneg
    nlinarith
  have hrsq_le : (j.E.r : ℝ) * (j.E.s : ℝ) ^ 2 ≤ HScale P X := by
    apply (le_div_iff₀ (by positivity : 0 < (j.E.s : ℝ) ^ 2)).mp
    simpa [mul_assoc] using hmem.r_le
  simpa [ExactDivisor.rho, Nat.cast_mul] using hrs_le.trans hrsq_le

/-- The pre-prime paper support is finite at every positive scale. -/
theorem familyPrePrimeSet_finite
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 0 < X) :
    {j : FamilyPrePrimeIndex | FamilyPrePrimeMem P X Pz b j}.Finite := by
  let rBound : ℕ := ⌊HScale P X⌋₊
  let sBound : ℕ := ⌊SScale P X⌋₊
  let dminusBound : ℕ := ⌊UScale X⌋₊
  let dplusBound : ℕ := ⌊YScale P X⌋₊
  let code : FamilyPrePrimeIndex → ℕ × ℕ × ℕ × ℕ :=
    fun j => (j.E.r, j.E.s, j.dminus, j.dplus)
  let box : Set (ℕ × ℕ × ℕ × ℕ) :=
    Set.Iic rBound ×ˢ Set.Iic sBound ×ˢ
      Set.Iic dminusBound ×ˢ Set.Iic dplusBound
  have hbox : box.Finite := by
    dsimp [box]
    exact (Set.finite_Iic rBound).prod
      ((Set.finite_Iic sBound).prod
        ((Set.finite_Iic dminusBound).prod (Set.finite_Iic dplusBound)))
  have hcode : Function.Injective code := by
    intro j k hjk
    cases j with
    | mk Ej dmj dpj =>
      cases Ej with
      | mk rj sj hrj hsj hcj =>
        cases k with
        | mk Ek dmk dpk =>
          cases Ek with
          | mk rk sk hrk hsk hck =>
            simp only [code] at hjk
            injection hjk with hr htail1
            injection htail1 with hs htail2
            injection htail2 with hdm hdp
            subst rk
            subst sk
            subst dmk
            subst dpk
            rfl
  have hpre : (code ⁻¹' box).Finite :=
    hbox.preimage (by
      intro j hj k hk hjk
      exact hcode hjk)
  apply hpre.subset
  intro j hj
  have hmem : FamilyPrePrimeMem P X Pz b j := hj
  have hH_nonneg : 0 ≤ HScale P X := Real.rpow_nonneg hX.le _
  have hs_real : (1 : ℝ) ≤ (j.E.s : ℝ) := by exact_mod_cast hmem.s_pos
  have hs_sq : (1 : ℝ) ≤ (j.E.s : ℝ) ^ 2 := one_le_pow₀ hs_real
  have hr_real : (j.E.r : ℝ) ≤ HScale P X :=
    le_trans hmem.r_le (div_le_self hH_nonneg hs_sq)
  have hdm_real : (1 : ℝ) ≤ (j.dminus : ℝ) := by
    exact_mod_cast hmem.dminus_pos
  have hdp_nonneg : 0 ≤ (j.dplus : ℝ) := by positivity
  have hdp_real : (j.dplus : ℝ) ≤ YScale P X := by
    calc
      (j.dplus : ℝ) ≤ ((j.dminus * j.dplus : ℕ) : ℝ) := by
        rw [Nat.cast_mul]
        nlinarith
      _ ≤ YScale P X := by simpa [Nat.cast_mul] using hmem.dd_le_Y
  change code j ∈ box
  simp only [box, code, Set.mem_prod, Set.mem_Iic]
  exact ⟨Nat.le_floor hr_real, Nat.le_floor hmem.s_le_S,
    Nat.le_floor hmem.dminus_le_U, Nat.le_floor hdp_real⟩

/-- The complete finite support of paper-family coordinates before the prime
in the certificate progression is chosen. -/
noncomputable def familyPrePrimeFinset
    (P : Params) (X : ℝ) (Pz b : ℕ) : Finset FamilyPrePrimeIndex :=
  if hX : 0 < X then (familyPrePrimeSet_finite P X Pz b hX).toFinset else ∅

/-- Membership in the finite pre-prime support is exactly the static
prime-independent paper predicate. -/
theorem mem_familyPrePrimeFinset_iff
    (P : Params) (X : ℝ) (Pz b : ℕ) (j : FamilyPrePrimeIndex) (hX : 0 < X) :
    j ∈ familyPrePrimeFinset P X Pz b ↔ FamilyPrePrimeMem P X Pz b j := by
  simp [familyPrePrimeFinset, hX, familyPrePrimeSet_finite]

/-- The canonical reduced residue of the prime that solves the certificate
congruence attached to a pre-prime coordinate. -/
noncomputable def familyPrePrimeResidue
    (j : FamilyPrePrimeIndex)
    (hcop : Nat.Coprime (j.dminus * j.dplus) (4 * j.E.rho)) : ℕ :=
  ((-(ZMod.unitOfCoprime (j.dminus * j.dplus) hcop)⁻¹ :
      (ZMod (4 * j.E.rho))ˣ) : ZMod (4 * j.E.rho)).val

/-- The canonical certificate residue is reduced modulo `4*rho`. -/
theorem familyPrePrimeResidue_coprime
    (j : FamilyPrePrimeIndex)
    (hcop : Nat.Coprime (j.dminus * j.dplus) (4 * j.E.rho)) :
    Nat.Coprime (familyPrePrimeResidue j hcop) (4 * j.E.rho) := by
  unfold familyPrePrimeResidue
  exact ZMod.val_coe_unit_coprime
    (-(ZMod.unitOfCoprime (j.dminus * j.dplus) hcop)⁻¹)

/-- Totalized canonical residue, with the harmless reduced default `1` away
from the coprime structural support. -/
noncomputable def familyPrePrimeResidueTotal (j : FamilyPrePrimeIndex) : ℕ :=
  if hcop : Nat.Coprime (j.dminus * j.dplus) (4 * j.E.rho) then
    familyPrePrimeResidue j hcop
  else 1

/-- The canonical residue solves the prime certificate congruence exactly. -/
theorem familyPrePrimeResidue_sat
    (j : FamilyPrePrimeIndex)
    (hcop : Nat.Coprime (j.dminus * j.dplus) (4 * j.E.rho))
    (hrho : 0 < j.E.rho) :
    4 * j.E.rho ∣
      (j.dminus * j.dplus) * familyPrePrimeResidue j hcop + 1 := by
  letI : NeZero (4 * j.E.rho) := ⟨by positivity⟩
  rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
  unfold familyPrePrimeResidue
  rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  simp only [Units.val_neg]
  rw [← ZMod.coe_unitOfCoprime (j.dminus * j.dplus) hcop]
  rw [mul_neg]
  rw [← Units.val_mul]
  simp

/-- Prime candidates in the paper window and in the canonical certificate
class attached to a pre-prime coordinate. -/
noncomputable def familyPrePrimePrimeValues
    (P : Params) (X : ℝ) (j : FamilyPrePrimeIndex)
    (hcop : Nat.Coprime (j.dminus * j.dplus) (4 * j.E.rho)) : Finset ℕ :=
  (Inputs.natWindow (X ^ P.β) (X ^ (1 - P.σ))).filter
    (fun p => Nat.Prime p ∧
      Inputs.congMod p (familyPrePrimeResidue j hcop) (4 * j.E.rho))

/-- For a coordinate in the pre-prime support, its canonical prime progression
is exactly the set of primes whose adjoining produces a member of the complete
paper family. -/
theorem mem_familyPrePrimePrimeValues_iff_withPrime_mem_familyIndexFinset
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 1 < X)
    (j : FamilyPrePrimeIndex) (hj : j ∈ familyPrePrimeFinset P X Pz b)
    (p : ℕ) :
    p ∈ familyPrePrimePrimeValues P X j
        ((mem_familyPrePrimeFinset_iff P X Pz b j
          (lt_trans zero_lt_one hX)).1 hj).dd_coprime_four_rho ↔
      j.withPrime p ∈ Family.familyIndexFinset P X Pz b := by
  let hpre : FamilyPrePrimeMem P X Pz b j :=
    (mem_familyPrePrimeFinset_iff P X Pz b j
      (lt_trans zero_lt_one hX)).1 hj
  let hcop := hpre.dd_coprime_four_rho
  have hs : 0 < j.E.s := lt_of_lt_of_le Nat.zero_lt_one hpre.s_pos
  have hY0 : 0 ≤ Y0Scale P X :=
    Real.rpow_nonneg (le_trans zero_le_one hX.le) _
  have hrReal : 0 < (j.E.r : ℝ) :=
    lt_of_le_of_lt (div_nonneg hY0 (Nat.cast_nonneg _)) hpre.r_gt
  have hr : 0 < j.E.r := by exact_mod_cast hrReal
  have hrho : 0 < j.E.rho := ExactDivisor.rho_pos j.E hr hs
  change p ∈ familyPrePrimePrimeValues P X j hcop ↔ _
  constructor
  · intro hp
    have hpData := Finset.mem_filter.mp hp
    have hpWindow := Finset.mem_filter.mp hpData.1
    have hpIcc := Finset.mem_Icc.mp hpWindow.1
    have hpPrime := hpData.2.1
    have hpCong : p ≡ familyPrePrimeResidue j hcop
        [MOD 4 * j.E.rho] := by
      simpa [Inputs.congMod, Nat.ModEq] using hpData.2.2
    have hUpperNonneg : 0 ≤ X ^ (1 - P.σ) :=
      Real.rpow_nonneg (le_trans zero_le_one hX.le) _
    have hpLe : (p : ℝ) ≤ X ^ (1 - P.σ) :=
      le_trans (by exact_mod_cast hpIcc.2) (Nat.floor_le hUpperNonneg)
    have hsat0 := familyPrePrimeResidue_sat j hcop hrho
    have hsatMod :
        (j.dminus * j.dplus) * familyPrePrimeResidue j hcop + 1 ≡
          0 [MOD 4 * j.E.rho] :=
      Nat.modEq_zero_iff_dvd.mpr hsat0
    have hsat : (j.dminus * j.dplus) * p + 1 ≡
        0 [MOD 4 * j.E.rho] :=
      ((hpCong.mul_left (j.dminus * j.dplus)).add_right 1).trans hsatMod
    have hstatic : Family.FamilyStaticMem P X Pz b (j.withPrime p) := by
      refine
        { s_pos := hpre.s_pos, s_le_S := hpre.s_le_S,
          r_gt := hpre.r_gt, r_le := hpre.r_le,
          dminus_pos := hpre.dminus_pos,
          dminus_le_U := hpre.dminus_le_U,
          dminus_dvd_Pz := hpre.dminus_dvd_Pz,
          dminus_squarefree := hpre.dminus_squarefree,
          dminus_odd := hpre.dminus_odd, base_cong := hpre.base_cong,
          dplus_pos := hpre.dplus_pos,
          dplus_squarefree := hpre.dplus_squarefree,
          dd_le_Y := hpre.dd_le_Y,
          dplus_coprime_Pz := hpre.dplus_coprime_Pz,
          dd_coprime_four_rho := by
            simpa [FamilyPrePrimeIndex.withPrime, Family.FamilyIndex.rho] using hcop,
          p_prime := hpPrime, p_gt := hpWindow.2, p_le := hpLe,
          sat_cong := by
            apply Nat.modEq_zero_iff_dvd.mp
            simpa [FamilyPrePrimeIndex.withPrime, Family.FamilyIndex.Q,
              Family.FamilyIndex.rho, Nat.mul_assoc] using hsat }
    exact (Family.mem_familyIndexFinset_iff P X Pz b (j.withPrime p)
      (lt_trans zero_lt_one hX)).2 hstatic
  · intro hp
    have hstatic : Family.FamilyStaticMem P X Pz b (j.withPrime p) :=
      (Family.mem_familyIndexFinset_iff P X Pz b (j.withPrime p)
        (lt_trans zero_lt_one hX)).1 hp
    have hpWindow : p ∈ Inputs.natWindow
        (X ^ P.β) (X ^ (1 - P.σ)) := by
      unfold Inputs.natWindow
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨hstatic.p_prime.one_le, ?_⟩, hstatic.p_gt⟩
      exact Nat.le_floor hstatic.p_le
    have hpSat : (j.dminus * j.dplus) * p + 1 ≡
        0 [MOD 4 * j.E.rho] := by
      apply Nat.modEq_zero_iff_dvd.mpr
      simpa [FamilyPrePrimeIndex.withPrime, Family.FamilyIndex.Q,
        Family.FamilyIndex.rho, Nat.mul_assoc] using hstatic.sat_cong
    have hresSat :
        (j.dminus * j.dplus) * familyPrePrimeResidue j hcop + 1 ≡
          0 [MOD 4 * j.E.rho] :=
      Nat.modEq_zero_iff_dvd.mpr (familyPrePrimeResidue_sat j hcop hrho)
    have hmul : (j.dminus * j.dplus) * p ≡
        (j.dminus * j.dplus) * familyPrePrimeResidue j hcop
          [MOD 4 * j.E.rho] :=
      Nat.ModEq.add_right_cancel' 1 (hpSat.trans hresSat.symm)
    have hgcd : Nat.gcd (4 * j.E.rho) (j.dminus * j.dplus) = 1 := by
      simpa [Nat.coprime_iff_gcd_eq_one] using hcop.symm
    have hpCong : p ≡ familyPrePrimeResidue j hcop
        [MOD 4 * j.E.rho] := Nat.ModEq.cancel_left_of_coprime hgcd hmul
    exact Finset.mem_filter.mpr
      ⟨hpWindow, hstatic.p_prime,
        by simpa [Inputs.congMod, Nat.ModEq] using hpCong⟩

/-- Totalized prime fiber; outside the coprime structural support it is empty. -/
noncomputable def familyPrePrimePrimeValuesTotal
    (P : Params) (X : ℝ) (j : FamilyPrePrimeIndex) : Finset ℕ :=
  if hcop : Nat.Coprime (j.dminus * j.dplus) (4 * j.E.rho) then
    familyPrePrimePrimeValues P X j hcop
  else ∅

/-- Finite pairs consisting of a pre-prime coordinate and a prime in its
canonical certificate progression. -/
noncomputable def familyPrePrimePairs
    (P : Params) (X : ℝ) (Pz b : ℕ) :
    Finset (Sigma fun _j : FamilyPrePrimeIndex => ℕ) :=
  (familyPrePrimeFinset P X Pz b).sigma
    (familyPrePrimePrimeValuesTotal P X)

/-- Adjoin the prime coordinate of a structural pair. -/
def familyPrePrimePairToIndex
    (x : Sigma fun _j : FamilyPrePrimeIndex => ℕ) : Family.FamilyIndex :=
  x.1.withPrime x.2

/-- Adjoining the prime coordinate is injective on structural pairs. -/
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

/-- The prime-independent support, after adjoining all primes in its canonical
progressions, is exactly the complete paper family. -/
theorem familyPrePrimePairs_image_eq_familyIndexFinset
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 1 < X) :
    (familyPrePrimePairs P X Pz b).image familyPrePrimePairToIndex =
      Family.familyIndexFinset P X Pz b := by
  ext i
  constructor
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨x, hx, rfl⟩
    have hxSigma := Finset.mem_sigma.mp hx
    have hj := hxSigma.1
    have hpre : FamilyPrePrimeMem P X Pz b x.1 :=
      (mem_familyPrePrimeFinset_iff P X Pz b x.1
        (lt_trans zero_lt_one hX)).1 hj
    unfold familyPrePrimePrimeValuesTotal at hxSigma
    rw [dif_pos hpre.dd_coprime_four_rho] at hxSigma
    exact (mem_familyPrePrimePrimeValues_iff_withPrime_mem_familyIndexFinset
      P X Pz b hX x.1 hj x.2).1 hxSigma.2
  · intro hi
    have himem : Family.FamilyStaticMem P X Pz b i :=
      (Family.mem_familyIndexFinset_iff P X Pz b i
        (lt_trans zero_lt_one hX)).1 hi
    let j : FamilyPrePrimeIndex :=
      { E := i.E, dminus := i.dminus, dplus := i.dplus }
    have hpre : FamilyPrePrimeMem P X Pz b j := by
      exact
        { s_pos := himem.s_pos, s_le_S := himem.s_le_S,
          r_gt := himem.r_gt, r_le := himem.r_le,
          dminus_pos := himem.dminus_pos,
          dminus_le_U := himem.dminus_le_U,
          dminus_dvd_Pz := himem.dminus_dvd_Pz,
          dminus_squarefree := himem.dminus_squarefree,
          dminus_odd := himem.dminus_odd, base_cong := himem.base_cong,
          dplus_pos := himem.dplus_pos,
          dplus_squarefree := himem.dplus_squarefree,
          dd_le_Y := himem.dd_le_Y,
          dplus_coprime_Pz := himem.dplus_coprime_Pz,
          dd_coprime_four_rho := by
            simpa [j, Family.FamilyIndex.rho] using
              himem.dd_coprime_four_rho }
    have hj : j ∈ familyPrePrimeFinset P X Pz b :=
      (mem_familyPrePrimeFinset_iff P X Pz b j
        (lt_trans zero_lt_one hX)).2 hpre
    have hp : i.p ∈ familyPrePrimePrimeValuesTotal P X j := by
      unfold familyPrePrimePrimeValuesTotal
      rw [dif_pos hpre.dd_coprime_four_rho]
      exact (mem_familyPrePrimePrimeValues_iff_withPrime_mem_familyIndexFinset
        P X Pz b hX j hj i.p).2 (by simpa [j] using hi)
    apply Finset.mem_image.mpr
    refine ⟨⟨j, i.p⟩, Finset.mem_sigma.mpr ⟨hj, hp⟩, ?_⟩
    simp [familyPrePrimePairToIndex, FamilyPrePrimeIndex.withPrime, j]

/-- Exact expansion of the complete actual-family mass over the
prime-independent structural support and its canonical prime progressions. -/
theorem actualPaperFamily_indexMassRat_real_eq_prePrimePairs
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 1 < X) :
    (Family.familyIndexMassRat
        (Family.familyIndexFinset P X Pz b) : ℝ) =
      ∑ x ∈ familyPrePrimePairs P X Pz b,
        (1 : ℝ) / ((x.1.dplus * x.2 : ℕ) : ℝ) := by
  rw [← familyPrePrimePairs_image_eq_familyIndexFinset P X Pz b hX]
  unfold Family.familyIndexMassRat
  simp only [Rat.cast_sum]
  rw [Finset.sum_image (fun x _hx y _hy hxy =>
    familyPrePrimePairToIndex_injective hxy)]
  apply Finset.sum_congr rfl
  intro x hx
  simp [familyPrePrimePairToIndex, FamilyPrePrimeIndex.withPrime,
    Family.FamilyIndex.wRat, Family.FamilyIndex.q]

/-- Exact complete-family mass expansion over every prime-independent
structural coordinate.  Empty prime progressions remain present and contribute
zero, rather than disappearing from the main-term comparison. -/
theorem actualPaperFamily_indexMassRat_real_eq_prePrimeFibers
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 1 < X) :
    (Family.familyIndexMassRat
        (Family.familyIndexFinset P X Pz b) : ℝ) =
      ∑ j ∈ familyPrePrimeFinset P X Pz b,
        ((1 : ℝ) / (j.dplus : ℝ)) *
          Inputs.btRecip P X (4 * j.E.rho)
            (familyPrePrimeResidueTotal j) := by
  rw [actualPaperFamily_indexMassRat_real_eq_prePrimePairs P X Pz b hX]
  unfold familyPrePrimePairs
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  let hpre : FamilyPrePrimeMem P X Pz b j :=
    (mem_familyPrePrimeFinset_iff P X Pz b j
      (lt_trans zero_lt_one hX)).1 hj
  let hcop := hpre.dd_coprime_four_rho
  have hres : familyPrePrimeResidueTotal j = familyPrePrimeResidue j hcop := by
    unfold familyPrePrimeResidueTotal
    rw [dif_pos hcop]
  change (∑ p ∈ familyPrePrimePrimeValuesTotal P X j,
      (1 : ℝ) / ((j.dplus * p : ℕ) : ℝ)) =
    ((1 : ℝ) / (j.dplus : ℝ)) *
      Inputs.btRecip P X (4 * j.E.rho) (familyPrePrimeResidueTotal j)
  rw [hres]
  unfold familyPrePrimePrimeValuesTotal
  rw [dif_pos hcop]
  unfold familyPrePrimePrimeValues Inputs.btRecip
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  simp [Nat.cast_mul, one_div, mul_comm]

/-- Prime-independent main term for the complete actual-family mass. -/
noncomputable def actualPaperPrePrimeMassMainCarrier
    (P : Params) (X : ℝ) (Pz b : ℕ) : ℝ :=
  ∑ j ∈ familyPrePrimeFinset P X Pz b,
    ((1 : ℝ) / (j.dplus : ℝ)) *
      ((1 / (Nat.totient (4 * j.E.rho) : ℝ)) *
        Inputs.btRecip P X 1 0)

/-- The purely structural coefficient in the complete-family prime main term,
corresponding exactly to the finite sum in `eq:certificate-mass-main`. -/
noncomputable def actualPaperPrePrimeStructuralMass
    (P : Params) (X : ℝ) (Pz b : ℕ) : ℝ :=
  ∑ j ∈ familyPrePrimeFinset P X Pz b,
    ((1 : ℝ) / (j.dplus : ℝ)) *
      (1 / (Nat.totient (4 * j.E.rho) : ℝ))

/-- Exact-divisor/small-divisor coordinate obtained by forgetting `dplus`. -/
structure FamilyPrePrimeSmallIndex where
  E : ExactDivisor
  dminus : ℕ

/-- Forget the large cofactor of a pre-prime coordinate. -/
def FamilyPrePrimeIndex.toSmall (j : FamilyPrePrimeIndex) :
    FamilyPrePrimeSmallIndex where
  E := j.E
  dminus := j.dminus

/-- Small structural coordinates represented in the complete pre-prime
support. -/
noncomputable def familyPrePrimeSmallValues
    (P : Params) (X : ℝ) (Pz b : ℕ) : Finset FamilyPrePrimeSmallIndex :=
  (familyPrePrimeFinset P X Pz b).image FamilyPrePrimeIndex.toSmall

/-- Large cofactors represented over one small structural coordinate. -/
noncomputable def familyPrePrimeDplusValues
    (P : Params) (X : ℝ) (Pz b : ℕ)
    (k : FamilyPrePrimeSmallIndex) : Finset ℕ :=
  ((familyPrePrimeFinset P X Pz b).filter
    (fun j => j.toSmall = k)).image (fun j => j.dplus)

/-- Exact partition of the structural mass into small coordinates and their
large-cofactor reciprocal sums. -/
theorem actualPaperPrePrimeStructuralMass_eq_small_dplus_partition
    (P : Params) (X : ℝ) (Pz b : ℕ) :
    actualPaperPrePrimeStructuralMass P X Pz b =
      ∑ k ∈ familyPrePrimeSmallValues P X Pz b,
        (1 / (Nat.totient (4 * k.E.rho) : ℝ)) *
          (∑ dplus ∈ familyPrePrimeDplusValues P X Pz b k,
            (1 : ℝ) / (dplus : ℝ)) := by
  classical
  let J := familyPrePrimeFinset P X Pz b
  let K := familyPrePrimeSmallValues P X Pz b
  have hmaps : ∀ j ∈ J, j.toSmall ∈ K := by
    intro j hj
    exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
  have hpartition := Finset.sum_fiberwise_of_maps_to hmaps
    (fun j : FamilyPrePrimeIndex =>
      ((1 : ℝ) / (j.dplus : ℝ)) *
        (1 / (Nat.totient (4 * j.E.rho) : ℝ)))
  unfold actualPaperPrePrimeStructuralMass
  change (∑ j ∈ J, ((1 : ℝ) / (j.dplus : ℝ)) *
      (1 / (Nat.totient (4 * j.E.rho) : ℝ))) = _
  rw [← hpartition]
  apply Finset.sum_congr rfl
  intro k hk
  let F := J.filter (fun j => j.toSmall = k)
  have hinj : Set.InjOn (fun j : FamilyPrePrimeIndex => j.dplus) F := by
    intro j hj l hl hdp
    have hjk := (Finset.mem_filter.mp hj).2
    have hlk := (Finset.mem_filter.mp hl).2
    have hjl : j.toSmall = l.toSmall := hjk.trans hlk.symm
    cases j with
    | mk Ej dmj dpj =>
      cases l with
      | mk El dml dpl =>
        simp only [FamilyPrePrimeIndex.toSmall] at hjl hdp
        injection hjl with hE hdm
        subst El
        subst dml
        simp_all
  have himage : F.image (fun j => j.dplus) =
      familyPrePrimeDplusValues P X Pz b k := by rfl
  change (∑ j ∈ F, ((1 : ℝ) / (j.dplus : ℝ)) *
      (1 / (Nat.totient (4 * j.E.rho) : ℝ))) = _
  have hE : ∀ j ∈ F, j.E = k.E := by
    intro j hj
    have hjk := (Finset.mem_filter.mp hj).2
    cases j
    cases k
    simpa [FamilyPrePrimeIndex.toSmall] using congrArg FamilyPrePrimeSmallIndex.E hjk
  calc
    (∑ j ∈ F, ((1 : ℝ) / (j.dplus : ℝ)) *
        (1 / (Nat.totient (4 * j.E.rho) : ℝ))) =
      ∑ j ∈ F, (1 / (Nat.totient (4 * k.E.rho) : ℝ)) *
        ((1 : ℝ) / (j.dplus : ℝ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hE j hj]
          ring
    _ = (1 / (Nat.totient (4 * k.E.rho) : ℝ)) *
        (∑ j ∈ F, (1 : ℝ) / (j.dplus : ℝ)) := by
          rw [Finset.mul_sum]
    _ = (1 / (Nat.totient (4 * k.E.rho) : ℝ)) *
        (∑ dplus ∈ familyPrePrimeDplusValues P X Pz b k,
          (1 : ℝ) / (dplus : ℝ)) := by
          rw [← himage]
          rw [Finset.sum_image hinj]

/-- On every represented small structural coordinate, the full `dplus`
support contains the fixed-power rough reciprocal interval used in the
manuscript's lower bound. -/
theorem roughRecip_le_familyPrePrimeDplusValues
    (P : Params) (X : ℝ) (b : ℕ) (hX : 1 < X)
    (hscale : UScale X * X ^ (3 * P.σ / 4) ≤ YScale P X)
    (k : FamilyPrePrimeSmallIndex)
    (hk : k ∈ familyPrePrimeSmallValues P X (Inputs.roughModulus X) b) :
    Inputs.roughRecip X (4 * k.E.rho) (P.σ / 2) (3 * P.σ / 4) ≤
      ∑ dplus ∈ familyPrePrimeDplusValues
          P X (Inputs.roughModulus X) b k,
        (1 : ℝ) / (dplus : ℝ) := by
  classical
  rcases Finset.mem_image.mp hk with ⟨j0, hj0, hj0k⟩
  have hj0mem : FamilyPrePrimeMem P X (Inputs.roughModulus X) b j0 :=
    (mem_familyPrePrimeFinset_iff P X (Inputs.roughModulus X) b j0
      (lt_trans zero_lt_one hX)).1 hj0
  have hs : 0 < j0.E.s := lt_of_lt_of_le Nat.zero_lt_one hj0mem.s_pos
  have hY0 : 0 ≤ Y0Scale P X :=
    Real.rpow_nonneg (le_trans zero_le_one hX.le) _
  have hrReal : 0 < (j0.E.r : ℝ) :=
    lt_of_le_of_lt (div_nonneg hY0 (Nat.cast_nonneg _)) hj0mem.r_gt
  have hr : 0 < j0.E.r := by exact_mod_cast hrReal
  have hrho : 0 < k.E.rho := by
    rw [← congrArg FamilyPrePrimeSmallIndex.E hj0k]
    exact ExactDivisor.rho_pos j0.E hr hs
  unfold Inputs.roughRecip
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    have hnData := Finset.mem_filter.mp hn
    have hnWindow := Finset.mem_filter.mp hnData.1
    have hnIcc := Finset.mem_Icc.mp hnWindow.1
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hnIcc.1
    have hnUpperNonneg : 0 ≤ X ^ (3 * P.σ / 4) :=
      Real.rpow_nonneg (le_trans zero_le_one hX.le) _
    have hnle : (n : ℝ) ≤ X ^ (3 * P.σ / 4) :=
      le_trans (by exact_mod_cast hnIcc.2) (Nat.floor_le hnUpperNonneg)
    have hdmn : (j0.dminus * n : ℝ) ≤ YScale P X := by
      calc
        (j0.dminus * n : ℝ) = (j0.dminus : ℝ) * (n : ℝ) := by norm_num
        _ ≤ UScale X * X ^ (3 * P.σ / 4) :=
          mul_le_mul hj0mem.dminus_le_U hnle (Nat.cast_nonneg _)
            (by unfold UScale; positivity)
        _ ≤ YScale P X := hscale
    have hnAux : Nat.Coprime n (4 * k.E.rho) := by
      have hauxPos : 0 < 4 * k.E.rho := Nat.mul_pos (by norm_num) hrho
      rw [← Inputs.auxiliaryModulus_eq_self_of_pos hauxPos]
      exact hnData.2.2.2
    have hdm : Nat.Coprime j0.dminus (4 * k.E.rho) := by
      rw [← congrArg FamilyPrePrimeSmallIndex.E hj0k]
      exact hj0mem.dd_coprime_four_rho.coprime_dvd_left
        (dvd_mul_right j0.dminus j0.dplus)
    let j : FamilyPrePrimeIndex :=
      { E := j0.E, dminus := j0.dminus, dplus := n }
    have hjmem : FamilyPrePrimeMem P X (Inputs.roughModulus X) b j := by
      refine
        { s_pos := hj0mem.s_pos, s_le_S := hj0mem.s_le_S,
          r_gt := hj0mem.r_gt, r_le := hj0mem.r_le,
          dminus_pos := hj0mem.dminus_pos,
          dminus_le_U := hj0mem.dminus_le_U,
          dminus_dvd_Pz := hj0mem.dminus_dvd_Pz,
          dminus_squarefree := hj0mem.dminus_squarefree,
          dminus_odd := hj0mem.dminus_odd,
          base_cong := hj0mem.base_cong,
          dplus_pos := hnpos, dplus_squarefree := hnData.2.1,
          dd_le_Y := by simpa [j, Nat.cast_mul] using hdmn,
          dplus_coprime_Pz := hnData.2.2.1,
          dd_coprime_four_rho := by
            simpa [j, ← congrArg FamilyPrePrimeSmallIndex.E hj0k] using
              (Nat.coprime_mul_iff_left.mpr ⟨hdm, hnAux⟩) }
    have hj : j ∈ familyPrePrimeFinset
        P X (Inputs.roughModulus X) b :=
      (mem_familyPrePrimeFinset_iff P X (Inputs.roughModulus X) b j
        (lt_trans zero_lt_one hX)).2 hjmem
    unfold familyPrePrimeDplusValues
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_filter.mpr ⟨hj, ?_⟩, rfl⟩
    simpa [j, FamilyPrePrimeIndex.toSmall] using hj0k
  · intro n _hnBig _hnSmall
    positivity

/-- The polylogarithmic small-divisor cutoff times the fixed-power rough
interval remains below `Y = X^sigma`. -/
theorem familyPrePrime_rough_interval_scale_eventually (P : Params) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      UScale X * X ^ (3 * P.σ / 4) ≤ YScale P X := by
  rcases Inputs.eventually_UScale_le_rpow (δ := P.σ / 4)
      (by linarith [P.σ_pos]) with
    ⟨XU, hU⟩
  refine ⟨max XU 1, ?_⟩
  intro X hX
  have hXU : XU ≤ X := le_trans (le_max_left _ _) hX
  have hXone : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hpow_nonneg : 0 ≤ X ^ (3 * P.σ / 4) :=
    Real.rpow_nonneg (le_trans zero_le_one hXone) _
  calc
    UScale X * X ^ (3 * P.σ / 4)
        ≤ X ^ (P.σ / 4) * X ^ (3 * P.σ / 4) :=
          mul_le_mul_of_nonneg_right (hU X hXU) hpow_nonneg
    _ = X ^ P.σ := by
      rw [← Real.rpow_add hXpos]
      congr 1
      ring
    _ = YScale P X := rfl

/-- In particular, the polylogarithmic small-divisor cutoff itself lies below
the structural `Y` cutoff for all sufficiently large `X`. -/
theorem familyPrePrime_small_cutoff_scale_eventually (P : Params) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → 1 < X →
      UScale X ≤ YScale P X := by
  rcases familyPrePrime_rough_interval_scale_eventually P with ⟨X₀, hscale⟩
  refine ⟨X₀, ?_⟩
  intro X hX hXgt
  have hpow : 1 ≤ X ^ (3 * P.σ / 4) :=
    Real.one_le_rpow hXgt.le (by linarith [P.σ_pos])
  have hU : 0 ≤ UScale X := by unfold UScale; positivity
  calc
    UScale X = UScale X * 1 := by ring
    _ ≤ UScale X * X ^ (3 * P.σ / 4) :=
      mul_le_mul_of_nonneg_left hpow hU
    _ ≤ YScale P X := hscale X hX

/-- Every represented pre-prime modulus lies in the standard rough-reciprocal
range `X^(beta/2)` for all sufficiently large `X`. -/
theorem familyPrePrimeSmall_modulus_range_eventually (P : Params) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → 1 < X → ∀ b : ℕ,
      ∀ k ∈ familyPrePrimeSmallValues P X (Inputs.roughModulus X) b,
        (4 * k.E.rho : ℝ) ≤ X ^ (P.β / 2) := by
  have hgap : 0 < P.β / 2 - P.θ := by linarith [P.two_θ_lt_β]
  rcases fixedNat_le_rpow_eventually_threshold 4 hgap with ⟨X4, h4⟩
  refine ⟨max X4 1, ?_⟩
  intro X hX hXgt b k hk
  rcases Finset.mem_image.mp hk with ⟨j, hj, hjk⟩
  have hjmem : FamilyPrePrimeMem P X (Inputs.roughModulus X) b j :=
    (mem_familyPrePrimeFinset_iff P X (Inputs.roughModulus X) b j
      (lt_trans zero_lt_one hXgt)).1 hj
  have hX4 : X4 ≤ X := le_trans (le_max_left _ _) hX
  have hXone : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hfour : (4 : ℝ) ≤ X ^ (P.β / 2 - P.θ) := h4 X hX4
  have hrho : (k.E.rho : ℝ) ≤ HScale P X := by
    rw [← congrArg FamilyPrePrimeSmallIndex.E hjk]
    exact hjmem.rho_le_HScale
  calc
    (4 * k.E.rho : ℝ) = (4 : ℝ) * (k.E.rho : ℝ) := by norm_num
    _ ≤ X ^ (P.β / 2 - P.θ) * (k.E.rho : ℝ) :=
      mul_le_mul_of_nonneg_right hfour (Nat.cast_nonneg _)
    _ ≤ X ^ (P.β / 2 - P.θ) * X ^ P.θ :=
      mul_le_mul_of_nonneg_left hrho
        (Real.rpow_nonneg (le_trans zero_le_one hXone) _)
    _ = X ^ (P.β / 2) := by
      rw [← Real.rpow_add hXpos]
      congr 1
      ring

/-- Every represented pre-prime modulus lies below `X^ν` for any fixed
exponent strictly larger than the structural exponent `θ`. -/
theorem familyPrePrimeSmall_modulus_range_eventually_of_theta_lt
    (P : Params) {ν : ℝ} (hθν : P.θ < ν) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → 1 < X → ∀ b : ℕ,
      ∀ k ∈ familyPrePrimeSmallValues P X (Inputs.roughModulus X) b,
        (4 * k.E.rho : ℝ) ≤ X ^ ν := by
  have hgap : 0 < ν - P.θ := sub_pos.mpr hθν
  rcases fixedNat_le_rpow_eventually_threshold 4 hgap with ⟨X4, h4⟩
  refine ⟨max X4 1, ?_⟩
  intro X hX hXgt b k hk
  rcases Finset.mem_image.mp hk with ⟨j, hj, hjk⟩
  have hjmem : FamilyPrePrimeMem P X (Inputs.roughModulus X) b j :=
    (mem_familyPrePrimeFinset_iff P X (Inputs.roughModulus X) b j
      (lt_trans zero_lt_one hXgt)).1 hj
  have hX4 : X4 ≤ X := le_trans (le_max_left _ _) hX
  have hXone : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hfour : (4 : ℝ) ≤ X ^ (ν - P.θ) := h4 X hX4
  have hrho : (k.E.rho : ℝ) ≤ HScale P X := by
    rw [← congrArg FamilyPrePrimeSmallIndex.E hjk]
    exact hjmem.rho_le_HScale
  calc
    (4 * k.E.rho : ℝ) = (4 : ℝ) * (k.E.rho : ℝ) := by norm_num
    _ ≤ X ^ (ν - P.θ) * (k.E.rho : ℝ) :=
      mul_le_mul_of_nonneg_right hfour (Nat.cast_nonneg _)
    _ ≤ X ^ (ν - P.θ) * X ^ P.θ :=
      mul_le_mul_of_nonneg_left hrho
        (Real.rpow_nonneg (le_trans zero_le_one hXone) _)
    _ = X ^ ν := by
      rw [← Real.rpow_add hXpos]
      congr 1
      ring

/-- The exact finite small-certificate coefficient left after removing the
rough `dplus` factor from the structural mass. -/
noncomputable def actualPaperPrePrimeSmallMass
    (P : Params) (X : ℝ) (b : ℕ) : ℝ :=
  ∑ k ∈ familyPrePrimeSmallValues P X (Inputs.roughModulus X) b,
    (1 / (Nat.totient (4 * k.E.rho) : ℝ))

/-- Canonical reduced `r`-residue solving the base congruence
`b + 4 r s^2 = 0 (mod d)`. -/
noncomputable def familySmallBaseResidue
    (b d s : ℕ) (hb : Nat.Coprime b d)
    (hcoef : Nat.Coprime (4 * s ^ 2) d) : ℕ :=
  ((-(ZMod.unitOfCoprime b hb *
      (ZMod.unitOfCoprime (4 * s ^ 2) hcoef)⁻¹) : (ZMod d)ˣ) : ZMod d).val

/-- The canonical base residue is reduced modulo the small divisor. -/
theorem familySmallBaseResidue_coprime
    (b d s : ℕ) (hb : Nat.Coprime b d)
    (hcoef : Nat.Coprime (4 * s ^ 2) d) :
    Nat.Coprime (familySmallBaseResidue b d s hb hcoef) d := by
  unfold familySmallBaseResidue
  exact ZMod.val_coe_unit_coprime
    (-(ZMod.unitOfCoprime b hb *
      (ZMod.unitOfCoprime (4 * s ^ 2) hcoef)⁻¹))

/-- The canonical base residue satisfies the exact base congruence. -/
theorem familySmallBaseResidue_sat
    (b d s : ℕ) (hd : 0 < d) (hb : Nat.Coprime b d)
    (hcoef : Nat.Coprime (4 * s ^ 2) d) :
    d ∣ b + 4 * familySmallBaseResidue b d s hb hcoef * s ^ 2 := by
  letI : NeZero d := ⟨ne_of_gt hd⟩
  rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
  unfold familySmallBaseResidue
  push_cast
  rw [ZMod.natCast_zmod_val]
  rw [← ZMod.coe_unitOfCoprime b hb]
  have hcoefCast :
      (4 : ZMod d) * (s : ZMod d) ^ 2 =
        ((ZMod.unitOfCoprime (4 * s ^ 2) hcoef : (ZMod d)ˣ) : ZMod d) := by
    rw [ZMod.coe_unitOfCoprime]
    push_cast
    rfl
  calc
    ((ZMod.unitOfCoprime b hb : (ZMod d)ˣ) : ZMod d) +
        4 * -(((ZMod.unitOfCoprime b hb : (ZMod d)ˣ) : ZMod d) *
          (((ZMod.unitOfCoprime (4 * s ^ 2) hcoef)⁻¹ : (ZMod d)ˣ) : ZMod d)) *
          (s : ZMod d) ^ 2 =
      ((ZMod.unitOfCoprime b hb : (ZMod d)ˣ) : ZMod d) -
        ((ZMod.unitOfCoprime b hb : (ZMod d)ˣ) : ZMod d) *
          (((ZMod.unitOfCoprime (4 * s ^ 2) hcoef : (ZMod d)ˣ) : ZMod d) *
            (((ZMod.unitOfCoprime (4 * s ^ 2) hcoef)⁻¹ : (ZMod d)ˣ) : ZMod d)) := by
              rw [← hcoefCast]
              ring
    _ = 0 := by
      rw [← Units.val_mul]
      simp

/-- Totalized base residue used inside finite sums. -/
noncomputable def familySmallBaseResidueTotal (b d s : ℕ) : ℕ :=
  if h : Nat.Coprime b d ∧ Nat.Coprime (4 * s ^ 2) d then
    familySmallBaseResidue b d s h.1 h.2
  else 1

/-- The finite small-certificate model obtained by summing the exact
reciprocal-totient progression carrier over `s` and `dminus`. -/
noncomputable def actualPaperSmallCertificateModel
    (P : Params) (X : ℝ) (b : ℕ) : ℝ :=
  ∑ s ∈ exactDivisorSRange P X,
    (1 / (Nat.totient s : ℝ)) *
      ∑ d ∈ (Finset.Icc (1 : ℕ) ⌊UScale X⌋₊).filter
          (fun d => d ∣ Inputs.roughModulus X ∧ Odd d ∧ Nat.Coprime d s),
        phiProgressionAverage P X d (familySmallBaseResidueTotal b d s) s

/-- The exact phi-progression theorem and deterministic slanted-length bound
give the manuscript's lower estimate for the finite small-certificate model. -/
theorem actualPaperSmallCertificateModel_ge_log_mul_smallDivisorAverage
    (P : Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X → ∀ b : ℕ,
      Nat.Coprime b (Inputs.roughModulus X) →
        c * Real.log X * Inputs.smallDivisorAverage P X ≤
          actualPaperSmallCertificateModel P X b := by
  rcases PhiProgressionBareLower_of_sqfRecipLower
      (PhiProgressionSqfRecipLower_of_standard_ordinarySquarefree P) with
    ⟨cφ, Xφ, hcφ, hφ⟩
  rcases slantLogLength_uniform_bounds P with
    ⟨cL, CL, XL, hcL, hCL, hL⟩
  refine ⟨cφ * cL, max Xφ XL, mul_pos hcφ hcL, ?_⟩
  intro X hX hXgt b hbP
  have hXφ : Xφ ≤ X := le_trans (le_max_left _ _) hX
  have hXL : XL ≤ X := le_trans (le_max_right _ _) hX
  unfold actualPaperSmallCertificateModel Inputs.smallDivisorAverage
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hsData := Finset.mem_filter.mp hs
  have hsIcc := Finset.mem_Icc.mp hsData.1
  have hspos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hsIcc.1
  have hsS_nonneg : 0 ≤ SScale P X :=
    Real.rpow_nonneg (le_trans zero_le_one hXgt.le) _
  have hsS : (s : ℝ) ≤ SScale P X :=
    le_trans (by exact_mod_cast hsIcc.2) (Nat.floor_le hsS_nonneg)
  have hslant := (hL X hXL s hsIcc.1 hsS).1
  unfold Inputs.smallDivisorWeight
  rw [Finset.mul_sum]
  let D := (Finset.Icc (1 : ℕ) ⌊UScale X⌋₊).filter
    (fun d => d ∣ Inputs.roughModulus X ∧ Odd d ∧ Nat.Coprime d s)
  change (cφ * cL) * Real.log X *
      ((∑ d ∈ D, (1 : ℝ) / (d : ℝ)) / (s : ℝ)) ≤
    ∑ d ∈ D, (1 / (Nat.totient s : ℝ)) *
      phiProgressionAverage P X d (familySmallBaseResidueTotal b d s) s
  rw [show (cφ * cL) * Real.log X *
      ((∑ d ∈ D, (1 : ℝ) / (d : ℝ)) / (s : ℝ)) =
    ∑ d ∈ D, (cφ * cL) * Real.log X *
      ((1 : ℝ) / (d : ℝ)) / (s : ℝ) by
        calc
          (cφ * cL) * Real.log X *
              ((∑ d ∈ D, (1 : ℝ) / (d : ℝ)) / (s : ℝ)) =
            (((cφ * cL) * Real.log X) *
              (∑ d ∈ D, (1 : ℝ) / (d : ℝ))) / (s : ℝ) := by ring
          _ = (∑ d ∈ D, ((cφ * cL) * Real.log X) *
              ((1 : ℝ) / (d : ℝ))) / (s : ℝ) := by rw [Finset.mul_sum]
          _ = ∑ d ∈ D, (cφ * cL) * Real.log X *
              ((1 : ℝ) / (d : ℝ)) / (s : ℝ) := by rw [Finset.sum_div]]
  apply Finset.sum_le_sum
  intro d hd
  dsimp [D] at hd
  have hdData := Finset.mem_filter.mp hd
  have hdIcc := Finset.mem_Icc.mp hdData.1
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hdIcc.1
  have hdU_nonneg : 0 ≤ UScale X := by unfold UScale; positivity
  have hdU : (d : ℝ) ≤ UScale X :=
    le_trans (by exact_mod_cast hdIcc.2) (Nat.floor_le hdU_nonneg)
  have hdsqf : Squarefree d :=
    (Inputs.roughModulus_squarefree X).squarefree_of_dvd hdData.2.1
  have hbd : Nat.Coprime b d := hbP.coprime_dvd_right hdData.2.1
  have h2d : Nat.Coprime 2 d := hdData.2.2.1.coprime_two_left
  have h4d : Nat.Coprime 4 d := by
    have h2' : Nat.Coprime d 2 := h2d.symm
    have h22 : Nat.Coprime d (2 * 2) := Nat.Coprime.mul_right h2' h2'
    simpa using h22.symm
  have hsd : Nat.Coprime s d := hdData.2.2.2.symm
  have hs2d : Nat.Coprime (s ^ 2) d :=
    (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) s d).2 hsd
  have hcoef : Nat.Coprime (4 * s ^ 2) d :=
    Nat.coprime_mul_iff_left.mpr ⟨h4d, hs2d⟩
  have hres : familySmallBaseResidueTotal b d s =
      familySmallBaseResidue b d s hbd hcoef := by
    unfold familySmallBaseResidueTotal
    rw [dif_pos ⟨hbd, hcoef⟩]
  have hrescop : Nat.Coprime (familySmallBaseResidueTotal b d s) d := by
    rw [hres]
    exact familySmallBaseResidue_coprime b d s hbd hcoef
  have hφsd := phiProgressionAverage_lower_of_bare_lower
    (hφ X hXφ d (familySmallBaseResidueTotal b d s) s
      hdpos hdsqf hdData.2.2.1 hdU hrescop hsIcc.1 hsData.2
        hsd hsS)
  have htotpos : 0 < Nat.totient s := Nat.totient_pos.mpr (by omega)
  have htotR : 0 < (Nat.totient s : ℝ) := by exact_mod_cast htotpos
  have hscale_nonneg : 0 ≤ (1 : ℝ) / (Nat.totient s : ℝ) := by positivity
  calc
    (cφ * cL) * Real.log X * ((1 : ℝ) / (d : ℝ)) /
          (s : ℝ) =
        ((1 : ℝ) / (Nat.totient s : ℝ)) *
          (cφ * (((1 : ℝ) / (d : ℝ)) *
            ((Nat.totient s : ℝ) / (s : ℝ)) *
              (cL * Real.log X))) := by
            field_simp [ne_of_gt htotR, Nat.cast_ne_zero.mpr (ne_of_gt hspos),
              Nat.cast_ne_zero.mpr (ne_of_gt hdpos)]
            ring
    _ ≤ ((1 : ℝ) / (Nat.totient s : ℝ)) *
          (cφ * phiProgressionAverageShape P X d s) := by
      apply mul_le_mul_of_nonneg_left _ hscale_nonneg
      unfold phiProgressionAverageShape
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hslant (by positivity)) hcφ.le
    _ ≤ ((1 : ℝ) / (Nat.totient s : ℝ)) *
        phiProgressionAverage P X d
          (familySmallBaseResidueTotal b d s) s :=
      mul_le_mul_of_nonneg_left hφsd hscale_nonneg

/-- Every point of the finite small-certificate progression model gives an
actual `(E,dminus)` coordinate of the prime-independent paper family. -/
theorem phiProgressionSupport_to_familyPrePrimeSmallValues
    (P : Params) (X : ℝ) (b s d r : ℕ) (hX : 1 < X)
    (hbP : Nat.Coprime b (Inputs.roughModulus X))
    (hUY : UScale X ≤ YScale P X)
    (hs : s ∈ exactDivisorSRange P X)
    (hd : d ∈ (Finset.Icc (1 : ℕ) ⌊UScale X⌋₊).filter
      (fun d => d ∣ Inputs.roughModulus X ∧ Odd d ∧ Nat.Coprime d s))
    (hr : r ∈ phiProgressionSupport P X d
      (familySmallBaseResidueTotal b d s) s) :
    ({ E :=
        { r := r, s := s,
          r_squarefree := (Finset.mem_filter.mp hr).2.1,
          s_squarefree := (Finset.mem_filter.mp hs).2,
          coprime_rs := (Finset.mem_filter.mp hr).2.2.1 }
       dminus := d } : FamilyPrePrimeSmallIndex) ∈
      familyPrePrimeSmallValues P X (Inputs.roughModulus X) b := by
  have hsData := Finset.mem_filter.mp hs
  have hsIcc := Finset.mem_Icc.mp hsData.1
  have hdData := Finset.mem_filter.mp hd
  have hdIcc := Finset.mem_Icc.mp hdData.1
  have hrData := Finset.mem_filter.mp hr
  have hrWindow := Finset.mem_filter.mp hrData.1
  have hrIcc := Finset.mem_Icc.mp hrWindow.1
  have hspos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hsIcc.1
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hdIcc.1
  have hrpos : 0 < r := lt_of_lt_of_le Nat.zero_lt_one hrIcc.1
  have hU_nonneg : 0 ≤ UScale X := by unfold UScale; positivity
  have hdU : (d : ℝ) ≤ UScale X :=
    le_trans (by exact_mod_cast hdIcc.2) (Nat.floor_le hU_nonneg)
  have hS_nonneg : 0 ≤ SScale P X :=
    Real.rpow_nonneg (le_trans zero_le_one hX.le) _
  have hsS : (s : ℝ) ≤ SScale P X :=
    le_trans (by exact_mod_cast hsIcc.2) (Nat.floor_le hS_nonneg)
  have hU1_nonneg : 0 ≤ phiProgressionU1 P s X := by
    unfold phiProgressionU1 HScale
    positivity
  have hrle : (r : ℝ) ≤ phiProgressionU1 P s X :=
    le_trans (by exact_mod_cast hrIcc.2) (Nat.floor_le hU1_nonneg)
  have hbd : Nat.Coprime b d := hbP.coprime_dvd_right hdData.2.1
  have h2d : Nat.Coprime 2 d := hdData.2.2.1.coprime_two_left
  have h4d : Nat.Coprime 4 d := by
    have h2' : Nat.Coprime d 2 := h2d.symm
    exact (Nat.Coprime.mul_right h2' h2').symm
  have hsd : Nat.Coprime s d := hdData.2.2.2.symm
  have hs2d : Nat.Coprime (s ^ 2) d :=
    (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) s d).2 hsd
  have hcoef : Nat.Coprime (4 * s ^ 2) d :=
    Nat.coprime_mul_iff_left.mpr ⟨h4d, hs2d⟩
  have hres : familySmallBaseResidueTotal b d s =
      familySmallBaseResidue b d s hbd hcoef := by
    unfold familySmallBaseResidueTotal
    rw [dif_pos ⟨hbd, hcoef⟩]
  have hrescop : Nat.Coprime (familySmallBaseResidueTotal b d s) d := by
    rw [hres]
    exact familySmallBaseResidue_coprime b d s hbd hcoef
  have hrCong : r ≡ familySmallBaseResidueTotal b d s [MOD d] := by
    simpa [Inputs.congMod, Nat.ModEq] using hrData.2.2.2
  have hrd : Nat.Coprime r d := by
    rw [← ZMod.isUnit_iff_coprime r d]
    have hcast : (r : ZMod d) =
        (familySmallBaseResidueTotal b d s : ZMod d) :=
      (ZMod.natCast_eq_natCast_iff r
        (familySmallBaseResidueTotal b d s) d).2 hrCong
    rw [hcast]
    exact (ZMod.isUnit_iff_coprime _ _).2 hrescop
  have hresSat : b + 4 * familySmallBaseResidueTotal b d s * s ^ 2 ≡
      0 [MOD d] := by
    apply Nat.modEq_zero_iff_dvd.mpr
    rw [hres]
    exact familySmallBaseResidue_sat b d s hdpos hbd hcoef
  have hbase : b + 4 * r * s ^ 2 ≡ 0 [MOD d] := by
    have hmul := (hrCong.mul_left (4 * s ^ 2)).add_left b
    have hmul' : b + 4 * r * s ^ 2 ≡
        b + 4 * familySmallBaseResidueTotal b d s * s ^ 2 [MOD d] := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
    exact hmul'.trans hresSat
  let E : ExactDivisor :=
    { r := r, s := s, r_squarefree := hrData.2.1,
      s_squarefree := hsData.2, coprime_rs := hrData.2.2.1 }
  let j : FamilyPrePrimeIndex := { E := E, dminus := d, dplus := 1 }
  have hjmem : FamilyPrePrimeMem P X (Inputs.roughModulus X) b j := by
    refine
      { s_pos := hsIcc.1, s_le_S := hsS,
        r_gt := by simpa [j, E, phiProgressionU0] using hrWindow.2,
        r_le := by simpa [j, E, phiProgressionU1] using hrle,
        dminus_pos := hdpos, dminus_le_U := hdU,
        dminus_dvd_Pz := hdData.2.1,
        dminus_squarefree :=
          (Inputs.roughModulus_squarefree X).squarefree_of_dvd hdData.2.1,
        dminus_odd := hdData.2.2.1,
        base_cong := by
          simpa [j, E, ExactDivisor.e, Nat.mul_assoc] using hbase,
        dplus_pos := by simp [j], dplus_squarefree := by simp [j],
        dd_le_Y := by simpa [j] using hdU.trans hUY,
        dplus_coprime_Pz := by simp [j],
        dd_coprime_four_rho := by
          have hd4rs : Nat.Coprime d (4 * (r * s)) :=
            Nat.Coprime.mul_right h4d.symm
              (Nat.Coprime.mul_right hrd.symm hdData.2.2.2)
          simpa [j, E, ExactDivisor.rho] using hd4rs }
  have hj : j ∈ familyPrePrimeFinset P X (Inputs.roughModulus X) b :=
    (mem_familyPrePrimeFinset_iff P X (Inputs.roughModulus X) b j
      (lt_trans zero_lt_one hX)).2 hjmem
  unfold familyPrePrimeSmallValues
  apply Finset.mem_image.mpr
  refine ⟨j, hj, ?_⟩
  rfl

/-- Multiplication by the fixed factor `4` changes the reciprocal-totient
weight of a coprime `r,s` pair by at most an absolute factor. -/
theorem one_div_totient_mul_le_eight_div_totient_four_mul
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hrs : Nat.Coprime r s) :
    ((1 : ℝ) / (Nat.totient r : ℝ)) *
        ((1 : ℝ) / (Nat.totient s : ℝ)) ≤
      8 * ((1 : ℝ) / (Nat.totient (4 * (r * s)) : ℝ)) := by
  let g := Nat.gcd 4 (r * s)
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hφg : 1 ≤ Nat.totient g := (Nat.totient_pos.mpr (by omega))
  have hgle : g ≤ 4 := Nat.gcd_le_left (r * s) (by norm_num)
  have heq := Nat.totient_gcd_mul_totient_mul 4 (r * s)
  have hrsφ : Nat.totient (r * s) = Nat.totient r * Nat.totient s :=
    Nat.totient_mul hrs
  have hφboundNat : Nat.totient (4 * (r * s)) ≤
      8 * (Nat.totient r * Nat.totient s) := by
    change Nat.totient (4 * (r * s)) ≤ _
    change g ≤ 4 at hgle
    change Nat.totient g * Nat.totient (4 * (r * s)) =
      Nat.totient 4 * Nat.totient (r * s) * g at heq
    norm_num [hrsφ] at heq
    calc
      Nat.totient (4 * (r * s)) ≤
          Nat.totient g * Nat.totient (4 * (r * s)) := by
            nlinarith [Nat.zero_le (Nat.totient (4 * (r * s)))]
      _ = 2 * (Nat.totient r * Nat.totient s) * g := heq
      _ ≤ 2 * (Nat.totient r * Nat.totient s) * 4 :=
        Nat.mul_le_mul_left _ hgle
      _ = 8 * (Nat.totient r * Nat.totient s) := by ring
  have hφr : 0 < (Nat.totient r : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hφs : 0 < (Nat.totient s : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hφ4rs : 0 < (Nat.totient (4 * (r * s)) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by positivity)
  have hφbound : (Nat.totient (4 * (r * s)) : ℝ) ≤
      8 * ((Nat.totient r : ℝ) * (Nat.totient s : ℝ)) := by
    exact_mod_cast hφboundNat
  have hdiv : (1 : ℝ) /
      ((Nat.totient r : ℝ) * (Nat.totient s : ℝ)) ≤
      8 / (Nat.totient (4 * (r * s)) : ℝ) := by
    apply (div_le_div_iff₀ (mul_pos hφr hφs) hφ4rs).2
    simpa using hφbound
  calc
    ((1 : ℝ) / (Nat.totient r : ℝ)) *
          ((1 : ℝ) / (Nat.totient s : ℝ)) =
        (1 : ℝ) / ((Nat.totient r : ℝ) * (Nat.totient s : ℝ)) := by
          field_simp [ne_of_gt hφr, ne_of_gt hφs]
    _ ≤ 8 / (Nat.totient (4 * (r * s)) : ℝ) := hdiv
    _ = 8 * ((1 : ℝ) / (Nat.totient (4 * (r * s)) : ℝ)) := by ring

/-- Small-divisor support at one conductor coordinate. -/
noncomputable def familySmallDivisorValues (X : ℝ) (s : ℕ) : Finset ℕ :=
  (Finset.Icc (1 : ℕ) ⌊UScale X⌋₊).filter
    (fun d => d ∣ Inputs.roughModulus X ∧ Odd d ∧ Nat.Coprime d s)

/-- Triples `(s,dminus,r)` in the exact finite small-certificate model. -/
noncomputable def actualPaperSmallCertificateTriples
    (P : Params) (X : ℝ) (b : ℕ) :
    Finset (Sigma fun _s : ℕ => Sigma fun _d : ℕ => ℕ) :=
  (exactDivisorSRange P X).sigma (fun s =>
    (familySmallDivisorValues X s).sigma (fun d =>
      phiProgressionSupport P X d (familySmallBaseResidueTotal b d s) s))

/-- Forgetful map from a small-certificate model triple to its actual
`(E,dminus)` structural coordinate. -/
def actualPaperSmallCertificateTripleToSmall
    (P : Params) (X : ℝ) (b : ℕ)
    (x : {x // x ∈ actualPaperSmallCertificateTriples P X b}) :
    FamilyPrePrimeSmallIndex where
  E :=
    { r := x.1.2.2
      s := x.1.1
      r_squarefree := by
        classical
        have hx := Finset.mem_sigma.mp x.2
        have hdx := Finset.mem_sigma.mp hx.2
        exact (Finset.mem_filter.mp hdx.2).2.1
      s_squarefree := by
        classical
        have hx := Finset.mem_sigma.mp x.2
        exact (Finset.mem_filter.mp hx.1).2
      coprime_rs := by
        classical
        have hx := Finset.mem_sigma.mp x.2
        have hdx := Finset.mem_sigma.mp hx.2
        exact (Finset.mem_filter.mp hdx.2).2.2.1 }
  dminus := x.1.2.1

/-- Distinct model triples give distinct small structural coordinates. -/
theorem actualPaperSmallCertificateTripleToSmall_injective
    (P : Params) (X : ℝ) (b : ℕ) :
    Function.Injective (actualPaperSmallCertificateTripleToSmall P X b) := by
  intro x y hxy
  cases x with
  | mk xv hx =>
    cases xv with
    | mk sx dx =>
      cases dx with
      | mk dx rx =>
        cases y with
        | mk yv hy =>
          cases yv with
          | mk sy dy =>
            cases dy with
            | mk dy ry =>
              simp only [actualPaperSmallCertificateTripleToSmall] at hxy
              injection hxy with hE hd
              injection hE with hr hs
              subst sy
              subst dy
              subst ry
              rfl

/-- Exact flattening of the nested small-certificate model into its triple
support. -/
theorem actualPaperSmallCertificateModel_eq_triple_sum
    (P : Params) (X : ℝ) (b : ℕ) :
    actualPaperSmallCertificateModel P X b =
      ∑ x ∈ actualPaperSmallCertificateTriples P X b,
        ((1 : ℝ) / (Nat.totient x.1 : ℝ)) *
          ((1 : ℝ) / (Nat.totient x.2.2 : ℝ)) := by
  unfold actualPaperSmallCertificateModel
    actualPaperSmallCertificateTriples familySmallDivisorValues
    phiProgressionAverage phiProgressionSupport
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.sum_sigma]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]

/-- Every small-certificate model triple maps into the actual small structural
support once the polylogarithmic cutoff lies below `Y`. -/
theorem actualPaperSmallCertificateTriples_image_subset_smallValues
    (P : Params) (X : ℝ) (b : ℕ) (hX : 1 < X)
    (hbP : Nat.Coprime b (Inputs.roughModulus X))
    (hUY : UScale X ≤ YScale P X) :
    (actualPaperSmallCertificateTriples P X b).attach.image
        (actualPaperSmallCertificateTripleToSmall P X b) ⊆
      familyPrePrimeSmallValues P X (Inputs.roughModulus X) b := by
  intro k hk
  rcases Finset.mem_image.mp hk with ⟨x, hx, rfl⟩
  have hxData := Finset.mem_sigma.mp x.2
  have hs := hxData.1
  have hdx := Finset.mem_sigma.mp hxData.2
  have hd := hdx.1
  have hr := hdx.2
  exact phiProgressionSupport_to_familyPrePrimeSmallValues
    P X b x.1.1 x.1.2.1 x.1.2.2 hX hbP hUY hs hd hr

/-- The finite certificate model injects into the actual small structural
support, with only the absolute totient loss caused by the fixed factor `4`. -/
theorem actualPaperSmallCertificateModel_le_eight_mul_smallMass
    (P : Params) (X : ℝ) (b : ℕ) (hX : 1 < X)
    (hbP : Nat.Coprime b (Inputs.roughModulus X))
    (hUY : UScale X ≤ YScale P X) :
    actualPaperSmallCertificateModel P X b ≤
      8 * actualPaperPrePrimeSmallMass P X b := by
  rw [actualPaperSmallCertificateModel_eq_triple_sum]
  let T := actualPaperSmallCertificateTriples P X b
  let F := actualPaperSmallCertificateTripleToSmall P X b
  calc
    (∑ x ∈ T,
        ((1 : ℝ) / (Nat.totient x.1 : ℝ)) *
          ((1 : ℝ) / (Nat.totient x.2.2 : ℝ))) =
        ∑ x ∈ T.attach,
          ((1 : ℝ) / (Nat.totient x.1.1 : ℝ)) *
            ((1 : ℝ) / (Nat.totient x.1.2.2 : ℝ)) := by
      exact (Finset.sum_attach T (fun x =>
        ((1 : ℝ) / (Nat.totient x.1 : ℝ)) *
          ((1 : ℝ) / (Nat.totient x.2.2 : ℝ)))).symm
    _ ≤ ∑ x ∈ T.attach,
        8 * ((1 : ℝ) / (Nat.totient (4 * (F x).E.rho) : ℝ)) := by
      apply Finset.sum_le_sum
      intro x hx
      have hxmem : x.1 ∈ actualPaperSmallCertificateTriples P X b := by
        simpa [T] using x.2
      have hxData := Finset.mem_sigma.mp hxmem
      have hsIcc := (Finset.mem_filter.mp hxData.1).1
      have hrData := (Finset.mem_sigma.mp hxData.2).2
      have hrWindow := (Finset.mem_filter.mp hrData).1
      have hrIcc := (Finset.mem_filter.mp hrWindow).1
      have htot := one_div_totient_mul_le_eight_div_totient_four_mul
        (r := x.1.1) (s := x.1.2.2)
        (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hsIcc).1)
        (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hrIcc).1)
        (Finset.mem_filter.mp hrData).2.2.1.symm
      simpa [F, actualPaperSmallCertificateTripleToSmall, ExactDivisor.rho,
        Nat.mul_comm]
        using htot
    _ = ∑ k ∈ T.attach.image F,
        8 * ((1 : ℝ) / (Nat.totient (4 * k.E.rho) : ℝ)) := by
      symm
      apply Finset.sum_image
      intro x hx y hy hxy
      exact actualPaperSmallCertificateTripleToSmall_injective P X b hxy
    _ ≤ ∑ k ∈ familyPrePrimeSmallValues
          P X (Inputs.roughModulus X) b,
        8 * ((1 : ℝ) / (Nat.totient (4 * k.E.rho) : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact actualPaperSmallCertificateTriples_image_subset_smallValues
          P X b hX hbP hUY
      · intro k hk hnot
        positivity
    _ = 8 * actualPaperPrePrimeSmallMass P X b := by
      unfold actualPaperPrePrimeSmallMass
      rw [Finset.mul_sum]

/-- The actual small structural mass has the full logarithmic size obtained
from the cited squarefree-progression input and the proved small-divisor
average. -/
theorem actualPaperPrePrimeSmallMass_ge_log_product
    (P : Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X → ∀ b : ℕ,
      Nat.Coprime b (Inputs.roughModulus X) →
        c * Real.log X * Real.log (SScale P X) * Real.log (zScale X) ≤
          actualPaperPrePrimeSmallMass P X b := by
  rcases actualPaperSmallCertificateModel_ge_log_mul_smallDivisorAverage P with
    ⟨cφ, Xφ, hcφ, hφ⟩
  rcases Inputs.smallDivisorAverage_lower_from_standard_inputs P with
    ⟨cA, XA, hcA, hA⟩
  rcases familyPrePrime_small_cutoff_scale_eventually P with ⟨XY, hY⟩
  refine ⟨cφ * cA / 8, max (max Xφ XA) XY, by positivity, ?_⟩
  intro X hX hXgt b hbP
  have hXφ : Xφ ≤ X :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hX)
  have hXA : XA ≤ X :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hX)
  have hXY : XY ≤ X := le_trans (le_max_right _ _) hX
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hXgt.le
  have hA' := hA X hXA
  have hφ' := hφ X hXφ hXgt b hbP
  have hupper := actualPaperSmallCertificateModel_le_eight_mul_smallMass
    P X b hXgt hbP (hY X hXY hXgt)
  have havg : 0 ≤ Inputs.smallDivisorAverage P X :=
    Inputs.smallDivisorAverage_nonneg P X
  have hmain : cφ * cA * Real.log X * Real.log (SScale P X) *
      Real.log (zScale X) ≤ actualPaperSmallCertificateModel P X b := by
    calc
      cφ * cA * Real.log X * Real.log (SScale P X) *
          Real.log (zScale X) =
        (cφ * Real.log X) *
          (cA * Real.log (SScale P X) * Real.log (zScale X)) := by ring
      _ ≤ (cφ * Real.log X) * Inputs.smallDivisorAverage P X :=
        mul_le_mul_of_nonneg_left hA' (mul_nonneg hcφ.le hlogX)
      _ ≤ actualPaperSmallCertificateModel P X b := hφ'
  calc
    (cφ * cA / 8) * Real.log X * Real.log (SScale P X) *
          Real.log (zScale X) =
        (cφ * cA * Real.log X * Real.log (SScale P X) *
          Real.log (zScale X)) / 8 := by ring
    _ ≤ actualPaperSmallCertificateModel P X b / 8 :=
      div_le_div_of_nonneg_right hmain (by norm_num)
    _ ≤ actualPaperPrePrimeSmallMass P X b := by
      linarith

/-- The structural mass contains the manuscript's fixed-power rough factor on
every small structural coordinate. -/
theorem actualPaperPrePrimeStructuralMass_ge_rough_mul_smallMass
    (P : Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X → ∀ b : ℕ,
      c * (Real.log X / Real.log (zScale X)) *
          actualPaperPrePrimeSmallMass P X b ≤
        actualPaperPrePrimeStructuralMass
          P X (Inputs.roughModulus X) b := by
  rcases Inputs.rough_sqf_recip P (P.σ / 2) (3 * P.σ / 4)
      (P.σ / 4) (P.β / 2) (by linarith [P.σ_pos])
      (by linarith [P.σ_pos]) (by linarith [P.σ_pos]) with
    ⟨c, C, Xrough, hc, hC, hrough⟩
  rcases familyPrePrime_rough_interval_scale_eventually P with ⟨Xscale, hscale⟩
  rcases familyPrePrimeSmall_modulus_range_eventually P with ⟨Xmod, hmod⟩
  refine ⟨c, max (max Xrough Xscale) Xmod, hc, ?_⟩
  intro X hX hXgt b
  have hXrough : Xrough ≤ X :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hX)
  have hXscale : Xscale ≤ X :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hX)
  have hXmod : Xmod ≤ X := le_trans (le_max_right _ _) hX
  rw [actualPaperPrePrimeStructuralMass_eq_small_dplus_partition]
  unfold actualPaperPrePrimeSmallMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hmodk := hmod X hXmod hXgt b k hk
  have hroughk := (hrough X hXrough (4 * k.E.rho)
    (by simpa [Nat.cast_mul] using hmodk)
    (P.σ / 2) (3 * P.σ / 4) (le_rfl)
    (by linarith [P.σ_pos]) (le_rfl) (by ring_nf; exact le_rfl)).1
  have hdplus := roughRecip_le_familyPrePrimeDplusValues
    P X b hXgt (hscale X hXscale) k hk
  have hphi : 0 ≤ (1 / (Nat.totient (4 * k.E.rho) : ℝ)) := by positivity
  calc
    c * (Real.log X / Real.log (zScale X)) *
          (1 / (Nat.totient (4 * k.E.rho) : ℝ))
        ≤ (1 / (Nat.totient (4 * k.E.rho) : ℝ)) *
            Inputs.roughRecip X (4 * k.E.rho)
              (P.σ / 2) (3 * P.σ / 4) := by
          rw [mul_comm (c * _)]
          exact mul_le_mul_of_nonneg_left hroughk hphi
    _ ≤ (1 / (Nat.totient (4 * k.E.rho) : ℝ)) *
        (∑ dplus ∈ familyPrePrimeDplusValues
            P X (Inputs.roughModulus X) b k,
          (1 : ℝ) / (dplus : ℝ)) :=
      mul_le_mul_of_nonneg_left hdplus hphi

/-- Exact factorization of the prime main carrier into the unrestricted
reciprocal-prime window and the manuscript's structural mass sum. -/
theorem actualPaperPrePrimeMassMainCarrier_eq_primeWindow_mul_structuralMass
    (P : Params) (X : ℝ) (Pz b : ℕ) :
    actualPaperPrePrimeMassMainCarrier P X Pz b =
      Inputs.btRecip P X 1 0 *
        actualPaperPrePrimeStructuralMass P X Pz b := by
  unfold actualPaperPrePrimeMassMainCarrier
    actualPaperPrePrimeStructuralMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The cited fixed-window Mertens theorem turns a lower bound for the
structural mass into the same lower bound for the complete prime main term,
up to an absolute positive constant. -/
theorem actualPaperPrePrimeMassMainCarrier_ge_mertens_mul_structuralMass
    (P : Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X → ∀ Pz b : ℕ,
      c * actualPaperPrePrimeStructuralMass P X Pz b ≤
        actualPaperPrePrimeMassMainCarrier P X Pz b := by
  rcases Inputs.prime_recip_window_mertens_lower_bound P with
    ⟨c, X₀, hc, hprime⟩
  refine ⟨c, X₀, hc, ?_⟩
  intro X hX Pz b
  rw [actualPaperPrePrimeMassMainCarrier_eq_primeWindow_mul_structuralMass]
  have hstruct : 0 ≤ actualPaperPrePrimeStructuralMass P X Pz b := by
    unfold actualPaperPrePrimeStructuralMass
    apply Finset.sum_nonneg
    intro j hj
    positivity
  exact mul_le_mul_of_nonneg_right (hprime X hX) hstruct

/-- Combining the cited fixed-window Mertens theorem with the fully matched
fixed-power rough factor reduces the complete prime main term to the explicit
finite small structural mass. -/
theorem actualPaperPrePrimeMassMainCarrier_ge_rough_smallMass
    (P : Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X → ∀ b : ℕ,
      c * (Real.log X / Real.log (zScale X)) *
          actualPaperPrePrimeSmallMass P X b ≤
        actualPaperPrePrimeMassMainCarrier
          P X (Inputs.roughModulus X) b := by
  rcases actualPaperPrePrimeMassMainCarrier_ge_mertens_mul_structuralMass P with
    ⟨cp, Xp, hcp, hp⟩
  rcases actualPaperPrePrimeStructuralMass_ge_rough_mul_smallMass P with
    ⟨cr, Xr, hcr, hr⟩
  refine ⟨cp * cr, max Xp Xr, mul_pos hcp hcr, ?_⟩
  intro X hX hXgt b
  have hXp : Xp ≤ X := le_trans (le_max_left _ _) hX
  have hXr : Xr ≤ X := le_trans (le_max_right _ _) hX
  have hrX := hr X hXr hXgt b
  have hpX := hp X hXp (Inputs.roughModulus X) b
  calc
    (cp * cr) * (Real.log X / Real.log (zScale X)) *
          actualPaperPrePrimeSmallMass P X b =
        cp * (cr * (Real.log X / Real.log (zScale X)) *
          actualPaperPrePrimeSmallMass P X b) := by ring
    _ ≤ cp * actualPaperPrePrimeStructuralMass
          P X (Inputs.roughModulus X) b :=
      mul_le_mul_of_nonneg_left hrX hcp.le
    _ ≤ actualPaperPrePrimeMassMainCarrier
          P X (Inputs.roughModulus X) b := hpX

/-- The complete prime main carrier has the manuscript's cubic logarithmic
size on the actual family support. -/
theorem actualPaperPrePrimeMassMainCarrier_ge_log_cube
    (P : Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X → ∀ b : ℕ,
      Nat.Coprime b (Inputs.roughModulus X) →
        c * (Real.log X) ^ 3 ≤
          actualPaperPrePrimeMassMainCarrier
            P X (Inputs.roughModulus X) b := by
  rcases actualPaperPrePrimeMassMainCarrier_ge_rough_smallMass P with
    ⟨cr, Xr, hcr, hr⟩
  rcases actualPaperPrePrimeSmallMass_ge_log_product P with
    ⟨cs, Xs, hcs, hs⟩
  refine ⟨cr * cs * P.η, max (max Xr Xs) (Real.exp 2),
    mul_pos (mul_pos hcr hcs) P.η_pos, ?_⟩
  intro X hX hXgt b hbP
  have hXr : Xr ≤ X :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hX)
  have hXs : Xs ≤ X :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hX)
  have hXexp : Real.exp 2 ≤ X := le_trans (le_max_right _ _) hX
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hXgt.le
  have hlogZ : 0 < Real.log (zScale X) :=
    Inputs.log_zScale_pos_of_exp_two_le hXexp
  have hfactor : 0 ≤ cr * (Real.log X / Real.log (zScale X)) :=
    mul_nonneg hcr.le (div_nonneg hlogX hlogZ.le)
  have hsX := hs X hXs hXgt b hbP
  have hrX := hr X hXr hXgt b
  calc
    (cr * cs * P.η) * (Real.log X) ^ 3 =
        (cr * (Real.log X / Real.log (zScale X))) *
          (cs * Real.log X * Real.log (SScale P X) *
            Real.log (zScale X)) := by
      rw [log_SScale P (lt_trans zero_lt_one hXgt)]
      field_simp [ne_of_gt hlogZ]
      ring
    _ ≤ (cr * (Real.log X / Real.log (zScale X))) *
          actualPaperPrePrimeSmallMass P X b :=
      mul_le_mul_of_nonneg_left hsX hfactor
    _ ≤ actualPaperPrePrimeMassMainCarrier
          P X (Inputs.roughModulus X) b := hrX

/-- Exact weighted progression-error carrier on the full prime-independent
support. -/
noncomputable def actualPaperPrePrimeMassErrorCarrier
    (P : Params) (X : ℝ) (Pz b : ℕ) : ℝ :=
  ∑ j ∈ familyPrePrimeFinset P X Pz b,
    ((1 : ℝ) / (j.dplus : ℝ)) *
      Inputs.reducedClassPrimeErrorMax P X (4 * j.E.rho)

/-- Exact partition of the pre-prime error by the small structural coordinate. -/
theorem actualPaperPrePrimeMassErrorCarrier_eq_small_dplus_partition
    (P : Params) (X : ℝ) (Pz b : ℕ) :
    actualPaperPrePrimeMassErrorCarrier P X Pz b =
      ∑ k ∈ familyPrePrimeSmallValues P X Pz b,
        (∑ dplus ∈ familyPrePrimeDplusValues P X Pz b k,
          (1 : ℝ) / (dplus : ℝ)) *
          Inputs.reducedClassPrimeErrorMax P X (4 * k.E.rho) := by
  classical
  let J := familyPrePrimeFinset P X Pz b
  let K := familyPrePrimeSmallValues P X Pz b
  have hmaps : ∀ j ∈ J, j.toSmall ∈ K := by
    intro j hj
    exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
  have hpartition := Finset.sum_fiberwise_of_maps_to hmaps
    (fun j : FamilyPrePrimeIndex =>
      ((1 : ℝ) / (j.dplus : ℝ)) *
        Inputs.reducedClassPrimeErrorMax P X (4 * j.E.rho))
  unfold actualPaperPrePrimeMassErrorCarrier
  change (∑ j ∈ J, ((1 : ℝ) / (j.dplus : ℝ)) *
      Inputs.reducedClassPrimeErrorMax P X (4 * j.E.rho)) = _
  rw [← hpartition]
  apply Finset.sum_congr rfl
  intro k hk
  let F := J.filter (fun j => j.toSmall = k)
  have hinj : Set.InjOn (fun j : FamilyPrePrimeIndex => j.dplus) F := by
    intro j hj l hl hdp
    have hjk := (Finset.mem_filter.mp hj).2
    have hlk := (Finset.mem_filter.mp hl).2
    cases j
    cases l
    cases k
    simp_all [FamilyPrePrimeIndex.toSmall]
  have hE : ∀ j ∈ F, j.E = k.E := by
    intro j hj
    exact congrArg FamilyPrePrimeSmallIndex.E (Finset.mem_filter.mp hj).2
  change (∑ j ∈ F, ((1 : ℝ) / (j.dplus : ℝ)) *
      Inputs.reducedClassPrimeErrorMax P X (4 * j.E.rho)) = _
  calc
    (∑ j ∈ F, ((1 : ℝ) / (j.dplus : ℝ)) *
        Inputs.reducedClassPrimeErrorMax P X (4 * j.E.rho)) =
      (∑ j ∈ F, (1 : ℝ) / (j.dplus : ℝ)) *
        Inputs.reducedClassPrimeErrorMax P X (4 * k.E.rho) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          rw [hE j hj]
    _ = (∑ dplus ∈ familyPrePrimeDplusValues P X Pz b k,
          (1 : ℝ) / (dplus : ℝ)) *
        Inputs.reducedClassPrimeErrorMax P X (4 * k.E.rho) := by
          congr 1
          unfold familyPrePrimeDplusValues
          rw [Finset.sum_image hinj]

/-- The represented large-cofactor reciprocals over one pre-prime small
coordinate are bounded by the full harmonic sum at `Y`. -/
theorem familyPrePrimeDplusValues_recip_le_harmonic
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 0 < X)
    (k : FamilyPrePrimeSmallIndex) :
    (∑ dplus ∈ familyPrePrimeDplusValues P X Pz b k,
      (1 : ℝ) / (dplus : ℝ)) ≤
      (harmonic ⌊YScale P X⌋₊ : ℝ) := by
  classical
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  simp_rw [one_div]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro dplus hdplus
    rcases Finset.mem_image.mp hdplus with ⟨j, hj, rfl⟩
    have hjJ := (Finset.mem_filter.mp hj).1
    have hjmem := (mem_familyPrePrimeFinset_iff P X Pz b j hX).1 hjJ
    have hdplusY : (j.dplus : ℝ) ≤ YScale P X := by
      calc
        (j.dplus : ℝ) ≤ (j.dminus * j.dplus : ℕ) := by
          exact_mod_cast Nat.le_mul_of_pos_left j.dplus hjmem.dminus_pos
        _ ≤ YScale P X := by simpa [Nat.cast_mul] using hjmem.dd_le_Y
    exact Finset.mem_Icc.mpr
      ⟨hjmem.dplus_pos, Nat.le_floor hdplusY⟩
  · intro n hn hnot
    positivity

/-- Prime moduli represented by the complete pre-prime support. -/
noncomputable def actualPaperPrePrimeMassModuli
    (P : Params) (X : ℝ) (Pz b : ℕ) : Finset ℕ :=
  (familyPrePrimeSmallValues P X Pz b).image (fun k => 4 * k.E.rho)

/-- Total reciprocal large-cofactor coefficient at one pre-prime modulus. -/
noncomputable def actualPaperPrePrimeMassErrorCoefficient
    (P : Params) (X : ℝ) (Pz b m : ℕ) : ℝ :=
  ∑ k ∈ (familyPrePrimeSmallValues P X Pz b).filter
      (fun k => 4 * k.E.rho = m),
    ∑ dplus ∈ familyPrePrimeDplusValues P X Pz b k,
      (1 : ℝ) / (dplus : ℝ)

/-- Exact regrouping of the pre-prime error by its progression modulus. -/
theorem actualPaperPrePrimeMassErrorCarrier_eq_modulus_sum
    (P : Params) (X : ℝ) (Pz b : ℕ) :
    actualPaperPrePrimeMassErrorCarrier P X Pz b =
      ∑ m ∈ actualPaperPrePrimeMassModuli P X Pz b,
        actualPaperPrePrimeMassErrorCoefficient P X Pz b m *
          Inputs.reducedClassPrimeErrorMax P X m := by
  classical
  rw [actualPaperPrePrimeMassErrorCarrier_eq_small_dplus_partition]
  let K := familyPrePrimeSmallValues P X Pz b
  let M := actualPaperPrePrimeMassModuli P X Pz b
  have hmaps : ∀ k ∈ K, 4 * k.E.rho ∈ M := by
    intro k hk
    exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
  have hpartition := Finset.sum_fiberwise_of_maps_to hmaps
    (fun k : FamilyPrePrimeSmallIndex =>
      (∑ dplus ∈ familyPrePrimeDplusValues P X Pz b k,
        (1 : ℝ) / (dplus : ℝ)) *
        Inputs.reducedClassPrimeErrorMax P X (4 * k.E.rho))
  change (∑ k ∈ K, _) = _
  rw [← hpartition]
  apply Finset.sum_congr rfl
  intro m hm
  unfold actualPaperPrePrimeMassErrorCoefficient
  change (∑ k ∈ K.filter (fun k => 4 * k.E.rho = m), _) = _
  calc
    (∑ k ∈ K.filter (fun k => 4 * k.E.rho = m),
        (∑ dplus ∈ familyPrePrimeDplusValues P X Pz b k,
          (1 : ℝ) / (dplus : ℝ)) *
          Inputs.reducedClassPrimeErrorMax P X (4 * k.E.rho)) =
      ∑ k ∈ K.filter (fun k => 4 * k.E.rho = m),
        (∑ dplus ∈ familyPrePrimeDplusValues P X Pz b k,
          (1 : ℝ) / (dplus : ℝ)) *
          Inputs.reducedClassPrimeErrorMax P X m := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [(Finset.mem_filter.mp hk).2]
    _ = (∑ k ∈ K.filter (fun k => 4 * k.E.rho = m),
        ∑ dplus ∈ familyPrePrimeDplusValues P X Pz b k,
          (1 : ℝ) / (dplus : ℝ)) *
          Inputs.reducedClassPrimeErrorMax P X m := by
      rw [Finset.sum_mul]
    _ = actualPaperPrePrimeMassErrorCoefficient P X Pz b m *
          Inputs.reducedClassPrimeErrorMax P X m := rfl

/-- At a fixed progression modulus, small structural coordinates inject into
the product of a divisor of the modulus and the admissible `dminus` interval. -/
theorem familyPrePrimeSmallValues_at_modulus_card_le_tau_mul_floorU
    (P : Params) (X : ℝ) (Pz b m : ℕ) (hX : 0 < X) :
    ((familyPrePrimeSmallValues P X Pz b).filter
      (fun k => 4 * k.E.rho = m)).card ≤
        Inputs.tau m * ⌊UScale X⌋₊ := by
  classical
  let S := (familyPrePrimeSmallValues P X Pz b).filter
    (fun k => 4 * k.E.rho = m)
  let T := m.divisors.product (Finset.Icc (1 : ℕ) ⌊UScale X⌋₊)
  have hdata : ∀ k ∈ S,
      0 < k.E.s ∧ 0 < k.E.r ∧ 4 * k.E.rho = m ∧
        k.dminus ∈ Finset.Icc (1 : ℕ) ⌊UScale X⌋₊ := by
    intro k hk
    have hkFilter := Finset.mem_filter.mp hk
    rcases Finset.mem_image.mp hkFilter.1 with ⟨j, hj, hjk⟩
    have hjmem := (mem_familyPrePrimeFinset_iff P X Pz b j hX).1 hj
    have hs : 0 < j.E.s := lt_of_lt_of_le Nat.zero_lt_one hjmem.s_pos
    have hY0 : 0 ≤ Y0Scale P X := Real.rpow_nonneg hX.le _
    have hrReal : 0 < (j.E.r : ℝ) :=
      lt_of_le_of_lt (div_nonneg hY0 (Nat.cast_nonneg _)) hjmem.r_gt
    have hr : 0 < j.E.r := by exact_mod_cast hrReal
    have hdm : j.dminus ∈ Finset.Icc (1 : ℕ) ⌊UScale X⌋₊ :=
      Finset.mem_Icc.mpr
        ⟨hjmem.dminus_pos, Nat.le_floor hjmem.dminus_le_U⟩
    subst k
    exact ⟨hs, hr, hkFilter.2, hdm⟩
  have hmap : ∀ k ∈ S, (k.E.s, k.dminus) ∈ T := by
    intro k hk
    have hd := hdata k hk
    apply Finset.mem_product.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨?_, ?_⟩, hd.2.2.2⟩
    · have hsRho : k.E.s ∣ k.E.rho := by
        unfold ExactDivisor.rho
        exact dvd_mul_left k.E.s k.E.r
      exact hsRho.trans (by
        rw [← hd.2.2.1]
        exact dvd_mul_left k.E.rho 4)
    · rw [← hd.2.2.1]
      exact (Nat.mul_pos (by norm_num)
        (ExactDivisor.rho_pos k.E hd.2.1 hd.1)).ne'
  have hinj : Set.InjOn
      (fun k : FamilyPrePrimeSmallIndex => (k.E.s, k.dminus)) S := by
    intro k hk l hl hkl
    have hkdata := hdata k hk
    have hldata := hdata l hl
    have hs : k.E.s = l.E.s := congrArg Prod.fst hkl
    have hdm : k.dminus = l.dminus := congrArg Prod.snd hkl
    have hrho : k.E.rho = l.E.rho := by omega
    have hrMul : k.E.r * k.E.s = l.E.r * k.E.s := by
      calc
        k.E.r * k.E.s = k.E.rho := rfl
        _ = l.E.rho := hrho
        _ = l.E.r * l.E.s := rfl
        _ = l.E.r * k.E.s := by rw [hs]
    have hr : k.E.r = l.E.r :=
      Nat.eq_of_mul_eq_mul_right hkdata.1 hrMul
    cases k with
    | mk Ek dk =>
      cases l with
      | mk El dl =>
        cases Ek with
        | mk rk sk hrksq hsksq hrsk =>
          cases El with
          | mk rl sl hrlsq hslsq hrsl =>
            simp_all [ExactDivisor.rho]
  have hcard : S.card ≤ T.card :=
    Finset.card_le_card_of_injOn
      (fun k : FamilyPrePrimeSmallIndex => (k.E.s, k.dminus)) hmap hinj
  calc
    ((familyPrePrimeSmallValues P X Pz b).filter
        (fun k => 4 * k.E.rho = m)).card = S.card := rfl
    _ ≤ T.card := hcard
    _ = m.divisors.card * (Finset.Icc (1 : ℕ) ⌊UScale X⌋₊).card := by
      change (m.divisors.product
        (Finset.Icc (1 : ℕ) ⌊UScale X⌋₊)).card = _
      exact Finset.card_product _ _
    _ ≤ m.divisors.card * ⌊UScale X⌋₊ := by
      apply Nat.mul_le_mul_left
      cases ⌊UScale X⌋₊ <;> simp
    _ = Inputs.tau m * ⌊UScale X⌋₊ := by rfl

/-- The exact coefficient at a pre-prime modulus has the divisor weight used
by weighted BV, up to the explicit small- and large-cofactor cutoffs. -/
theorem actualPaperPrePrimeMassErrorCoefficient_le_tau_mul_cutoffs
    (P : Params) (X : ℝ) (Pz b m : ℕ) (hX : 0 < X) :
    actualPaperPrePrimeMassErrorCoefficient P X Pz b m ≤
      (Inputs.tau m : ℝ) *
        ((⌊UScale X⌋₊ : ℝ) * (harmonic ⌊YScale P X⌋₊ : ℝ)) := by
  let S := (familyPrePrimeSmallValues P X Pz b).filter
    (fun k => 4 * k.E.rho = m)
  let H : ℝ := harmonic ⌊YScale P X⌋₊
  have hsum : actualPaperPrePrimeMassErrorCoefficient P X Pz b m ≤
      ∑ _k ∈ S, H := by
    unfold actualPaperPrePrimeMassErrorCoefficient
    change (∑ k ∈ S,
      ∑ dplus ∈ familyPrePrimeDplusValues P X Pz b k,
        (1 : ℝ) / (dplus : ℝ)) ≤ _
    apply Finset.sum_le_sum
    intro k hk
    exact familyPrePrimeDplusValues_recip_le_harmonic P X Pz b hX k
  have hH : 0 ≤ H := Inputs.harmonic_nonneg_real _
  have hcard := familyPrePrimeSmallValues_at_modulus_card_le_tau_mul_floorU
    P X Pz b m hX
  calc
    actualPaperPrePrimeMassErrorCoefficient P X Pz b m
        ≤ ∑ _k ∈ S, H := hsum
    _ = (S.card : ℝ) * H := by simp
    _ ≤ ((Inputs.tau m * ⌊UScale X⌋₊ : ℕ) : ℝ) * H := by
      apply mul_le_mul_of_nonneg_right _ hH
      exact_mod_cast hcard
    _ = (Inputs.tau m : ℝ) *
        ((⌊UScale X⌋₊ : ℝ) * (harmonic ⌊YScale P X⌋₊ : ℝ)) := by
      simp [H]
      ring

/-- The exact pre-prime progression error is dominated by the manuscript's
same-carrier divisor-weighted BV sum, with only the two explicit cutoff
factors outside that sum. -/
theorem actualPaperPrePrimeMassErrorCarrier_le_cutoffs_mul_weightedBV_of_theta_lt
    (P : Params) {ν : ℝ} (hθν : P.θ < ν) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → 1 < X → ∀ b : ℕ,
      actualPaperPrePrimeMassErrorCarrier
          P X (Inputs.roughModulus X) b ≤
        ((⌊UScale X⌋₊ : ℝ) * (harmonic ⌊YScale P X⌋₊ : ℝ)) *
          Inputs.weightedBVSum P X 1 ν := by
  rcases familyPrePrimeSmall_modulus_range_eventually_of_theta_lt P hθν with
    ⟨X₀, hrange⟩
  refine ⟨X₀, ?_⟩
  intro X hX hXgt b
  let M := actualPaperPrePrimeMassModuli
    P X (Inputs.roughModulus X) b
  let A : ℝ := (⌊UScale X⌋₊ : ℝ) *
    (harmonic ⌊YScale P X⌋₊ : ℝ)
  have hA : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _)
    (Inputs.harmonic_nonneg_real _)
  have hMsubset : M ⊆ Finset.Icc (1 : ℕ) ⌊X ^ ν⌋₊ := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨k, hk, rfl⟩
    rcases Finset.mem_image.mp hk with ⟨j, hj, hjk⟩
    have hjmem := (mem_familyPrePrimeFinset_iff P X
      (Inputs.roughModulus X) b j (lt_trans zero_lt_one hXgt)).1 hj
    have hs : 0 < j.E.s := lt_of_lt_of_le Nat.zero_lt_one hjmem.s_pos
    have hY0 : 0 ≤ Y0Scale P X :=
      Real.rpow_nonneg (le_trans zero_le_one hXgt.le) _
    have hrReal : 0 < (j.E.r : ℝ) :=
      lt_of_le_of_lt (div_nonneg hY0 (Nat.cast_nonneg _)) hjmem.r_gt
    have hr : 0 < j.E.r := by exact_mod_cast hrReal
    have hmodPos : 0 < 4 * k.E.rho := by
      rw [← congrArg FamilyPrePrimeSmallIndex.E hjk]
      exact Nat.mul_pos (by norm_num) (ExactDivisor.rho_pos j.E hr hs)
    have hupper := hrange X hX hXgt b k hk
    exact Finset.mem_Icc.mpr
      ⟨hmodPos, Nat.le_floor (by simpa [Nat.cast_mul] using hupper)⟩
  rw [actualPaperPrePrimeMassErrorCarrier_eq_modulus_sum]
  calc
    (∑ m ∈ M,
        actualPaperPrePrimeMassErrorCoefficient
            P X (Inputs.roughModulus X) b m *
          Inputs.reducedClassPrimeErrorMax P X m) ≤
      ∑ m ∈ M, ((Inputs.tau m : ℝ) * A) *
          Inputs.reducedClassPrimeErrorMax P X m := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_right
        (actualPaperPrePrimeMassErrorCoefficient_le_tau_mul_cutoffs
          P X (Inputs.roughModulus X) b m (lt_trans zero_lt_one hXgt))
        (Inputs.reducedClassPrimeErrorMax_nonneg P X m)
    _ = A * ∑ m ∈ M, (Inputs.tau m : ℝ) *
          Inputs.reducedClassPrimeErrorMax P X m := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ ≤ A * Inputs.weightedBVSum P X 1 ν := by
      apply mul_le_mul_of_nonneg_left _ hA
      unfold Inputs.weightedBVSum
      simpa using Finset.sum_le_sum_of_subset_of_nonneg hMsubset
        (fun m hm hnot => mul_nonneg (by positivity)
          (Inputs.reducedClassPrimeErrorMax_nonneg P X m))

/-- Manuscript-cutoff specialization of the generic weighted-BV carrier
bridge. -/
theorem actualPaperPrePrimeMassErrorCarrier_le_cutoffs_mul_weightedBV
    (P : Params) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → 1 < X → ∀ b : ℕ,
      actualPaperPrePrimeMassErrorCarrier
          P X (Inputs.roughModulus X) b ≤
        ((⌊UScale X⌋₊ : ℝ) * (harmonic ⌊YScale P X⌋₊ : ℝ)) *
          Inputs.weightedBVSum P X 1 (P.β / 2) :=
  actualPaperPrePrimeMassErrorCarrier_le_cutoffs_mul_weightedBV_of_theta_lt
    P (by linarith [P.two_θ_lt_β])

/-- The two elementary cutoff factors outside weighted BV cost at most nine
powers of `log X`. -/
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
    Inputs.harmonic_nonneg_real _
  have hpow_nonneg : 0 ≤ (Real.log X) ^ 8 := by positivity
  calc
    (⌊UScale X⌋₊ : ℝ) * (harmonic ⌊YScale P X⌋₊ : ℝ) ≤
        (Real.log X) ^ 8 * (harmonic ⌊YScale P X⌋₊ : ℝ) :=
      mul_le_mul_of_nonneg_right hfloorU hharm_nonneg
    _ ≤ (Real.log X) ^ 8 * ((1 + P.σ) * Real.log X) :=
      mul_le_mul_of_nonneg_left hharm hpow_nonneg
    _ = (1 + P.σ) * (Real.log X) ^ 9 := by ring

/-- The complete reciprocal `dminus` envelope costs only `O(log z)`. -/
theorem harmonic_floor_UScale_le_three_log_zScale
    (X : ℝ) (hX : Real.exp (Real.exp 1) ≤ X) :
    (harmonic ⌊UScale X⌋₊ : ℝ) ≤ 3 * Real.log (zScale X) := by
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hlogX : Real.exp 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hX
  have hlogXpos : 0 < Real.log X := lt_of_lt_of_le (Real.exp_pos 1) hlogX
  have hloglog : 1 ≤ Real.log (Real.log X) := by
    rw [Real.le_log_iff_exp_le hlogXpos]
    exact hlogX
  have hUge : 1 ≤ UScale X := by
    unfold UScale
    have hexp : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    exact one_le_pow₀ (hexp.trans hlogX)
  have hharm : (harmonic ⌊UScale X⌋₊ : ℝ) ≤
      1 + Real.log (UScale X) :=
    harmonic_floor_le_one_add_log (UScale X) hUge
  have hlogU : Real.log (UScale X) = 8 * Real.log (Real.log X) := by
    unfold UScale
    rw [Real.log_pow]
    ring
  have hlogZ : Real.log (zScale X) = 4 * Real.log (Real.log X) := by
    unfold zScale
    rw [Real.log_pow]
    ring
  rw [hlogU] at hharm
  rw [hlogZ]
  linarith

/-- Under the manuscript's cited reciprocal weighted-BV/EH input, the exact
complete pre-prime error carrier is eventually bounded by an absolute
constant. -/
theorem actualPaperPrePrimeMassErrorCarrier_eventually_bounded
    (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X → ∀ b : ℕ,
      actualPaperPrePrimeMassErrorCarrier
          P X (Inputs.roughModulus X) b ≤ C := by
  let ν : ℝ := (P.θ + P.β / 2) / 2
  have hνpos : 0 < ν := by dsimp [ν]; linarith [P.θ_pos, P.β_pos]
  have hθν : P.θ < ν := by dsimp [ν]; linarith [P.two_θ_lt_β]
  have hνhalf : ν < P.β / 2 := by
    dsimp [ν]
    linarith [P.two_θ_lt_β]
  rcases Inputs.reciprocal_bombieri_vinogradov_weighted_same_carrier
      P ν 12 1 hνpos hνhalf (by norm_num) (by norm_num) with
    ⟨K, XBV, hK, hBVbound⟩
  rcases actualPaperPrePrimeMassErrorCarrier_le_cutoffs_mul_weightedBV_of_theta_lt
      P hθν with
    ⟨XE, herror⟩
  refine ⟨(1 + P.σ) * K, max (max XBV XE) (Real.exp 1),
    mul_pos (by linarith [P.σ_pos]) hK, ?_⟩
  intro X hX hXgt b
  have hXBV : XBV ≤ X :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hX)
  have hXE : XE ≤ X :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hX)
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hlog : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) hXexp)]
    exact hXexp
  have hlogpos : 0 < Real.log X := lt_of_lt_of_le zero_lt_one hlog
  let W := Inputs.weightedBVSum P X 1 ν
  let A : ℝ := (⌊UScale X⌋₊ : ℝ) *
    (harmonic ⌊YScale P X⌋₊ : ℝ)
  have hW : 0 ≤ W := Inputs.weightedBVSum_nonneg P X 1 ν
  have hA : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _)
    (Inputs.harmonic_nonneg_real _)
  have hWbound : W ≤ K * (Real.log X) ^ (-(12 : ℝ)) := by
    calc
      W = |W| := (abs_of_nonneg hW).symm
      _ ≤ K * (Real.log X) ^ (-(12 : ℝ)) := hBVbound X hXBV
  have hcut : A ≤ (1 + P.σ) * (Real.log X) ^ 9 :=
    prePrimeErrorCutoffs_le_log_pow_nine P X hXexp
  have hcutRhs : 0 ≤ (1 + P.σ) * (Real.log X) ^ 9 :=
    mul_nonneg (by linarith [P.σ_pos]) (by positivity)
  have hpowprod : (Real.log X) ^ 9 *
      (Real.log X) ^ (-(12 : ℝ)) =
        (Real.log X) ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add hlogpos]
    norm_num
  have hnegpow : (Real.log X) ^ (-(3 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hlog (by norm_num)
  calc
    actualPaperPrePrimeMassErrorCarrier
          P X (Inputs.roughModulus X) b ≤ A * W := herror X hXE hXgt b
    _ ≤ ((1 + P.σ) * (Real.log X) ^ 9) * W :=
      mul_le_mul_of_nonneg_right hcut hW
    _ ≤ ((1 + P.σ) * (Real.log X) ^ 9) *
          (K * (Real.log X) ^ (-(12 : ℝ))) :=
      mul_le_mul_of_nonneg_left hWbound hcutRhs
    _ = ((1 + P.σ) * K) * (Real.log X) ^ (-(3 : ℝ)) := by
      rw [← hpowprod]
      ring
    _ ≤ (1 + P.σ) * K := by
      calc
        ((1 + P.σ) * K) * (Real.log X) ^ (-(3 : ℝ)) ≤
            ((1 + P.σ) * K) * 1 :=
          mul_le_mul_of_nonneg_left hnegpow
            (mul_nonneg (show 0 ≤ 1 + P.σ by linarith [P.σ_pos]) hK.le)
        _ = (1 + P.σ) * K := by ring

/-- The complete actual-family mass dominates the full structural main term
minus its exact weighted progression error.  Unlike the represented-support
version, this comparison includes empty prime fibers. -/
theorem actualPaperPrePrime_massMain_sub_error_le_indexMass
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 1 < X) :
    actualPaperPrePrimeMassMainCarrier P X Pz b -
        actualPaperPrePrimeMassErrorCarrier P X Pz b ≤
      (Family.familyIndexMassRat
        (Family.familyIndexFinset P X Pz b) : ℝ) := by
  rw [actualPaperFamily_indexMassRat_real_eq_prePrimeFibers P X Pz b hX]
  unfold actualPaperPrePrimeMassMainCarrier
    actualPaperPrePrimeMassErrorCarrier
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j hj
  let hpre : FamilyPrePrimeMem P X Pz b j :=
    (mem_familyPrePrimeFinset_iff P X Pz b j
      (lt_trans zero_lt_one hX)).1 hj
  let hcop := hpre.dd_coprime_four_rho
  have hres : familyPrePrimeResidueTotal j = familyPrePrimeResidue j hcop := by
    unfold familyPrePrimeResidueTotal
    rw [dif_pos hcop]
  have hmodPos : 0 < 4 * j.E.rho := by
    have hs : 0 < j.E.s := lt_of_lt_of_le Nat.zero_lt_one hpre.s_pos
    have hY0 : 0 ≤ Y0Scale P X :=
      Real.rpow_nonneg (le_trans zero_le_one hX.le) _
    have hrReal : 0 < (j.E.r : ℝ) :=
      lt_of_le_of_lt (div_nonneg hY0 (Nat.cast_nonneg _)) hpre.r_gt
    have hr : 0 < j.E.r := by exact_mod_cast hrReal
    exact Nat.mul_pos (by norm_num) (ExactDivisor.rho_pos j.E hr hs)
  have hresCop : Nat.Coprime (familyPrePrimeResidueTotal j) (4 * j.E.rho) := by
    rw [hres]
    exact familyPrePrimeResidue_coprime j hcop
  have herr := Inputs.reducedClassPrimeError_le_max_of_coprime
    (P := P) (X := X) hmodPos hresCop
  have hprime :
      Inputs.btRecip P X (4 * j.E.rho) (familyPrePrimeResidueTotal j) =
        ∑ p ∈ familyPrePrimePrimeValuesTotal P X j,
          (1 : ℝ) / (p : ℝ) := by
    rw [hres]
    unfold familyPrePrimePrimeValuesTotal
    rw [dif_pos hcop]
    rfl
  have hneg :
      -Inputs.reducedClassPrimeErrorMax P X (4 * j.E.rho) ≤
        Inputs.btRecip P X (4 * j.E.rho)
            (familyPrePrimeResidueTotal j) -
          (1 / (Nat.totient (4 * j.E.rho) : ℝ)) *
            Inputs.btRecip P X 1 0 :=
    (neg_le_neg herr).trans (neg_abs_le _)
  rw [hprime]
  have hweight : 0 ≤ (1 : ℝ) / (j.dplus : ℝ) := by positivity
  calc
    ((1 : ℝ) / (j.dplus : ℝ)) *
          ((1 / (Nat.totient (4 * j.E.rho) : ℝ)) *
            Inputs.btRecip P X 1 0) -
        ((1 : ℝ) / (j.dplus : ℝ)) *
          Inputs.reducedClassPrimeErrorMax P X (4 * j.E.rho) =
      ((1 : ℝ) / (j.dplus : ℝ)) *
        ((1 / (Nat.totient (4 * j.E.rho) : ℝ)) *
            Inputs.btRecip P X 1 0 -
          Inputs.reducedClassPrimeErrorMax P X (4 * j.E.rho)) := by ring
    _ ≤ ((1 : ℝ) / (j.dplus : ℝ)) *
        (∑ p ∈ familyPrePrimePrimeValuesTotal P X j,
          (1 : ℝ) / (p : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hweight
      linarith

/-- The actual complete paper family has cubic reciprocal mass, conditional
only on the manuscript's cited reciprocal weighted-BV/EH theorem. -/
theorem actualPaperFamily_indexMassRat_ge_log_cube
    (P : Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X → ∀ b : ℕ,
      Nat.Coprime b (Inputs.roughModulus X) →
        c * (Real.log X) ^ 3 ≤
          (Family.familyIndexMassRat
            (Family.familyIndexFinset
              P X (Inputs.roughModulus X) b) : ℝ) := by
  rcases actualPaperPrePrimeMassMainCarrier_ge_log_cube P with
    ⟨cm, Xm, hcm, hmain⟩
  rcases actualPaperPrePrimeMassErrorCarrier_eventually_bounded P with
    ⟨Ce, Xe, hCe, herror⟩
  let q : ℝ := 2 * Ce / cm
  let Xq : ℝ := Real.exp (max 1 q)
  refine ⟨cm / 2, max (max Xm Xe) Xq, by positivity, ?_⟩
  intro X hX hXgt b hbP
  have hXm : Xm ≤ X :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hX)
  have hXe : Xe ≤ X :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hX)
  have hXq : Xq ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := lt_trans zero_lt_one hXgt
  have hlogq : max 1 q ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hXq
  have hlogone : 1 ≤ Real.log X := (le_max_left _ _).trans hlogq
  have hqlog : q ≤ Real.log X := (le_max_right _ _).trans hlogq
  have hlogcube : Real.log X ≤ (Real.log X) ^ 3 := by
    have hsquare : (1 : ℝ) * 1 ≤ Real.log X * Real.log X :=
      mul_self_le_mul_self (by norm_num) hlogone
    calc
      Real.log X = Real.log X * 1 := by ring
      _ ≤ Real.log X * (Real.log X * Real.log X) :=
        mul_le_mul_of_nonneg_left (by simpa using hsquare) (by linarith)
      _ = (Real.log X) ^ 3 := by ring
  have hqcube : q ≤ (Real.log X) ^ 3 := hqlog.trans hlogcube
  have hcq : cm * q = 2 * Ce := by
    dsimp [q]
    field_simp [ne_of_gt hcm]
  have hCeHalf : Ce ≤ (cm / 2) * (Real.log X) ^ 3 := by
    have := mul_le_mul_of_nonneg_left hqcube hcm.le
    rw [hcq] at this
    nlinarith
  have hm := hmain X hXm hXgt b hbP
  have he := herror X hXe hXgt b
  have hmass := actualPaperPrePrime_massMain_sub_error_le_indexMass
    P X (Inputs.roughModulus X) b hXgt
  calc
    (cm / 2) * (Real.log X) ^ 3 ≤
        actualPaperPrePrimeMassMainCarrier
            P X (Inputs.roughModulus X) b -
          actualPaperPrePrimeMassErrorCarrier
            P X (Inputs.roughModulus X) b := by
      linarith
    _ ≤ (Family.familyIndexMassRat
          (Family.familyIndexFinset
            P X (Inputs.roughModulus X) b) : ℝ) := hmass

/-- Natural-scale mass sequence of the actual manuscript family, allowing the
reduced residue to vary with the ambient integer. -/
noncomputable def actualPaperFamilyMassNat
    (P : Params) (b : ℕ → ℕ) (N : ℕ) : ℝ :=
  (Family.familyIndexMassRat
    (Family.familyIndexFinset P (N : ℝ)
      (Inputs.roughModulus (N : ℝ)) (b N)) : ℝ)

/-- Natural-number form of the actual-family cubic mass theorem used by the
Suen assembly.  Its only residue-side premise is the manuscript's reduced
class condition. -/
theorem actualPaperFamilyMassNat_eventual_logCube_lower
    (P : Params) (b : ℕ → ℕ) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ N : ℕ, X₀ ≤ (N : ℝ) → 3 ≤ N →
      Nat.Coprime (b N) (Inputs.roughModulus (N : ℝ)) →
        c * logCube (N : ℝ) ≤ actualPaperFamilyMassNat P b N := by
  rcases actualPaperFamily_indexMassRat_ge_log_cube P with
    ⟨c, X₀, hc, hmass⟩
  refine ⟨c, X₀, hc, ?_⟩
  intro N hX hN hcop
  have hNgt : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 3) hN)
  simpa [actualPaperFamilyMassNat, logCube] using
    hmass (N : ℝ) hX hNgt (b N) hcop

/-- Small-divisor coordinates occurring in a residue fiber of the actual
family. -/
noncomputable def familyDminusResidueValues
    (indices : Finset Family.FamilyIndex) (D c : ℕ) : Finset ℕ :=
  (indices.filter (fun i => i.e % D = c)).image (fun i => i.dminus)

/-- Every small divisor represented in a residue fiber lies in the manuscript's
defining positive interval. -/
theorem familyDminusResidueValues_subset_Icc
    (P : Params) (X : ℝ) (Pz b : ℕ)
    (indices : Finset Family.FamilyIndex)
    (hX : 0 < X)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i)
    (D c : ℕ) :
    familyDminusResidueValues indices D c ⊆
      Finset.Icc (1 : ℕ) ⌊UScale X⌋₊ := by
  intro dminus hdminus
  rcases Finset.mem_image.mp hdminus with ⟨i, hi, rfl⟩
  have hiIndices := (Finset.mem_filter.mp hi).1
  have himem := hmem i hiIndices
  exact Finset.mem_Icc.mpr
    ⟨himem.dminus_pos, Nat.le_floor himem.dminus_le_U⟩

/-- Consequently, the reciprocal small-divisor sum in any actual residue
fiber is bounded by the full harmonic sum at `U`. -/
theorem familyDminusResidueValues_recip_le_harmonic
    (P : Params) (X : ℝ) (Pz b : ℕ)
    (indices : Finset Family.FamilyIndex)
    (hX : 0 < X)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i)
    (D c : ℕ) :
    (∑ dminus ∈ familyDminusResidueValues indices D c,
      (1 : ℝ) / (dminus : ℝ)) ≤
        (harmonic ⌊UScale X⌋₊ : ℝ) := by
  classical
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  simp_rw [one_div]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact familyDminusResidueValues_subset_Icc
      P X Pz b indices hX hmem D c
  · intro n hn hnot
    positivity

/-- The exact-divisor part of the actual family at a fixed small divisor and
residue constraint. -/
def familyTensorIndexPredicate
    (D c dminus : ℕ) (i : Family.FamilyIndex) : Prop :=
  i.dminus = dminus ∧ D ∣ i.dplus ∧ i.e % D = c

noncomputable def familyExactValuesAtDminus
    (indices : Finset Family.FamilyIndex) (D c dminus : ℕ) :
    Finset ExactDivisor :=
  familyExactValues (indices.filter (familyTensorIndexPredicate D c dminus))

/-- A canonical exact-divisor progression residue.  If a fixed small-divisor
fiber is nonempty at a given `s`, choose its `r`-coordinate; otherwise use the
reduced residue `1`. -/
noncomputable def familyTensorResidueSelector
    (indices : Finset Family.FamilyIndex) (D c dminus b : ℕ) (s : ℕ) : ℕ := by
  classical
  exact if h : ∃ i ∈ indices,
      familyTensorIndexPredicate D c dminus i ∧ i.E.s = s then
    (Classical.choose h).E.r
  else 1

/-- A base congruence with a reduced base class forces the exact-divisor
coordinate to be reduced modulo the small divisor. -/
theorem family_coprime_of_base_cong
    (b e d : ℕ) (hbcop : Nat.Coprime b d)
    (hbase : b + 4 * e ≡ 0 [MOD d]) : Nat.Coprime e d := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let g := Nat.gcd e d
  have hge : g ∣ e := Nat.gcd_dvd_left e d
  have hgd : g ∣ d := Nat.gcd_dvd_right e d
  have hg4e : g ∣ 4 * e := dvd_mul_of_dvd_right hge 4
  have hdvd : d ∣ b + 4 * e := (Nat.modEq_zero_iff_dvd).1 hbase
  have hgsmall : g ∣ b + 4 * e := hgd.trans hdvd
  have hgb : g ∣ b := by
    have hsub := Nat.dvd_sub (Nat.le_add_left (4 * e) b) hgsmall hg4e
    simpa [Nat.add_sub_cancel_right] using hsub
  have hggcd : g ∣ Nat.gcd b d := Nat.dvd_gcd hgb hgd
  rw [Nat.coprime_iff_gcd_eq_one] at hbcop
  rw [hbcop] at hggcd
  exact Nat.dvd_one.mp hggcd

/-- Every actual exact-divisor fiber at fixed `d_-` lies in one reduced
progression modulo `D d_-`.  This is the finite CRT/change-of-variables bridge
from the paper's `(e mod D, b+4e mod d_-)` conditions to the concrete
`phiProgressionSupport` carrier. -/
theorem familyExactValuesAtDminus_mem_support
    (P : Params) (X : ℝ) (Pz b : ℕ)
    (indices : Finset Family.FamilyIndex)
    (hX : 1 < X) (hbcop : Nat.Coprime b Pz)
    (hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X Pz b i)
    (D c dminus : ℕ) (hD : 0 < D)
    {E : ExactDivisor}
    (hE : E ∈ familyExactValuesAtDminus indices D c dminus) :
    E.s ∈ exactDivisorSRange P X ∧
      Nat.Coprime E.s (D * dminus) ∧
      Nat.Coprime
        (familyTensorResidueSelector indices D c dminus b E.s)
        (D * dminus) ∧
      E.r ∈ phiProgressionSupport P X (D * dminus)
        (familyTensorResidueSelector indices D c dminus b E.s) E.s := by
  classical
  unfold familyExactValuesAtDminus familyExactValues at hE
  rcases Finset.mem_image.mp hE with ⟨i, hi, rfl⟩
  have hiIndices : i ∈ indices := (Finset.mem_filter.mp hi).1
  have hiPred : familyTensorIndexPredicate D c dminus i :=
    (Finset.mem_filter.mp hi).2
  have himem := hmem i hiIndices
  rcases hiPred with ⟨hiMinus, hiDvd, hiResidue⟩
  have hDcopPz : Nat.Coprime D Pz :=
    himem.dplus_coprime_Pz.coprime_dvd_left hiDvd
  have hDcopFourRho : Nat.Coprime D (4 * i.rho) := by
    have hdpFourRho : Nat.Coprime i.dplus (4 * i.rho) :=
      himem.dd_coprime_four_rho.coprime_dvd_left
        (dvd_mul_left i.dplus i.dminus)
    exact hdpFourRho.coprime_dvd_left hiDvd
  have hDcopRho : Nat.Coprime D i.rho :=
    hDcopFourRho.coprime_dvd_right (dvd_mul_left i.rho 4)
  have hsRho : i.E.s ∣ i.rho := by
    simpa [Family.FamilyIndex.rho, ExactDivisor.rho] using
      (dvd_mul_of_dvd_right (dvd_refl i.E.s) i.E.r)
  have hrRho : i.E.r ∣ i.rho := by
    simpa [Family.FamilyIndex.rho, ExactDivisor.rho] using
      (dvd_mul_of_dvd_left (dvd_refl i.E.r) i.E.s)
  have hscopD : Nat.Coprime i.E.s D :=
    hDcopRho.symm.coprime_dvd_left hsRho
  have hrcopD : Nat.Coprime i.E.r D :=
    hDcopRho.symm.coprime_dvd_left hrRho
  have hbDminus : Nat.Coprime b i.dminus :=
    hbcop.coprime_dvd_right himem.dminus_dvd_Pz
  have h2Dminus : Nat.Coprime 2 i.dminus :=
    himem.dminus_odd.coprime_two_left
  have h4Dminus : Nat.Coprime 4 i.dminus := by
    have h2' : Nat.Coprime i.dminus 2 := h2Dminus.symm
    have h22 : Nat.Coprime i.dminus (2 * 2) :=
      Nat.Coprime.mul_right h2' h2'
    simpa [show (4 : ℕ) = 2 * 2 by norm_num] using h22.symm
  have heDminus : Nat.Coprime i.e i.dminus :=
    family_coprime_of_base_cong b i.e i.dminus hbDminus himem.base_cong
  have hrcopDminus : Nat.Coprime i.E.r i.dminus := by
    have hrE : i.E.r ∣ i.e := by
      simpa [Family.FamilyIndex.e, ExactDivisor.e] using
        (dvd_mul_of_dvd_left (dvd_refl i.E.r) (i.E.s ^ 2))
    exact heDminus.coprime_dvd_left hrE
  have hscopDminus : Nat.Coprime i.E.s i.dminus := by
    exact heDminus.coprime_dvd_left
      (dvd_mul_of_dvd_right (dvd_pow_self i.E.s (by norm_num)) i.E.r)
  have hscopDminus' : Nat.Coprime i.E.s dminus := by
    simpa [hiMinus] using hscopDminus
  have hscop : Nat.Coprime i.E.s (D * dminus) := by
    exact Nat.Coprime.mul_right hscopD hscopDminus'
  have hselector_exists : ∃ j ∈ indices,
      familyTensorIndexPredicate D c dminus j ∧ j.E.s = i.E.s := by
    exact ⟨i, hiIndices, ⟨hiMinus, hiDvd, hiResidue⟩, rfl⟩
  let hsel := hselector_exists
  let j : Family.FamilyIndex := Classical.choose hsel
  have hjData := Classical.choose_spec hsel
  have hjIndices : j ∈ indices := hjData.1
  have hjPred : familyTensorIndexPredicate D c dminus j := hjData.2.1
  have hjS : j.E.s = i.E.s := hjData.2.2
  have hjmem := hmem j hjIndices
  have hjMinus : j.dminus = dminus := hjPred.1
  have hjDvd : D ∣ j.dplus := hjPred.2.1
  have hjResidue : j.e % D = c := hjPred.2.2
  have hjiDcopRho : Nat.Coprime D j.rho := by
    have hdpFourRho : Nat.Coprime j.dplus (4 * j.rho) :=
      hjmem.dd_coprime_four_rho.coprime_dvd_left
        (dvd_mul_left j.dplus j.dminus)
    have hDcopFourRhoJ : Nat.Coprime D (4 * j.rho) :=
      hdpFourRho.coprime_dvd_left hjDvd
    exact hDcopFourRhoJ.coprime_dvd_right (dvd_mul_left j.rho 4)
  have hjSrho : j.E.s ∣ j.rho := by
    simpa [Family.FamilyIndex.rho, ExactDivisor.rho] using
      (dvd_mul_of_dvd_right (dvd_refl j.E.s) j.E.r)
  have hjRrho : j.E.r ∣ j.rho := by
    simpa [Family.FamilyIndex.rho, ExactDivisor.rho] using
      (dvd_mul_of_dvd_left (dvd_refl j.E.r) j.E.s)
  have hjScopD : Nat.Coprime j.E.s D := by
    simpa [hjS] using
      hjiDcopRho.symm.coprime_dvd_left hjSrho
  have hjRcopD : Nat.Coprime j.E.r D :=
    hjiDcopRho.symm.coprime_dvd_left hjRrho
  have hjbDminus : Nat.Coprime b j.dminus :=
    hbcop.coprime_dvd_right hjmem.dminus_dvd_Pz
  have hj2Dminus : Nat.Coprime 2 j.dminus := hjmem.dminus_odd.coprime_two_left
  have hj4Dminus : Nat.Coprime 4 j.dminus := by
    have hj2' : Nat.Coprime j.dminus 2 := hj2Dminus.symm
    have hj22 : Nat.Coprime j.dminus (2 * 2) :=
      Nat.Coprime.mul_right hj2' hj2'
    simpa [show (4 : ℕ) = 2 * 2 by norm_num] using hj22.symm
  have hjeDminus : Nat.Coprime j.e j.dminus :=
    family_coprime_of_base_cong b j.e j.dminus hjbDminus hjmem.base_cong
  have hjRcopDminus : Nat.Coprime j.E.r j.dminus := by
    have hjrE : j.E.r ∣ j.e := by
      simpa [Family.FamilyIndex.e, ExactDivisor.e] using
        (dvd_mul_of_dvd_left (dvd_refl j.E.r) (j.E.s ^ 2))
    exact hjeDminus.coprime_dvd_left hjrE
  have hjScopDminus : Nat.Coprime j.E.s j.dminus := by
    exact hjeDminus.coprime_dvd_left
      (dvd_mul_of_dvd_right (dvd_pow_self j.E.s (by norm_num)) j.E.r)
  have hjRcopDminus' : Nat.Coprime j.E.r dminus := by
    simpa [hjMinus] using hjRcopDminus
  have hselector_coprime :
      Nat.Coprime
        (familyTensorResidueSelector indices D c dminus b i.E.s)
        (D * dminus) := by
    simp [familyTensorResidueSelector, hsel]
    exact Nat.Coprime.mul_right
      (by simpa [hjS] using hjRcopD) hjRcopDminus'
  have hresD : i.e ≡ j.e [MOD D] := by
    unfold Nat.ModEq
    exact hiResidue.trans hjResidue.symm
  have hresDmul : i.E.r * i.E.s ^ 2 ≡ j.E.r * i.E.s ^ 2 [MOD D] := by
    simpa [Family.FamilyIndex.e, ExactDivisor.e, hjS] using hresD
  have hscopDpow : Nat.Coprime D (i.E.s ^ 2) :=
    (Nat.coprime_pow_right_iff (by norm_num : 0 < 2) D i.E.s).2 hscopD.symm
  have hresD_r : i.E.r ≡ j.E.r [MOD D] :=
    Nat.ModEq.cancel_right_of_coprime hscopDpow.gcd_eq_one hresDmul
  have hresDm : i.e ≡ j.e [MOD dminus] := by
    have hiBase : b + 4 * i.e ≡ 0 [MOD dminus] := by
      simpa [hiMinus] using himem.base_cong
    have hjBase : b + 4 * j.e ≡ 0 [MOD dminus] := by
      simpa [hjMinus] using hjmem.base_cong
    have hbase : b + 4 * i.e ≡ b + 4 * j.e [MOD dminus] :=
      hiBase.trans hjBase.symm
    have hfour : 4 * i.e ≡ 4 * j.e [MOD dminus] :=
      Nat.ModEq.add_left_cancel' b hbase
    have h4dminus : Nat.Coprime 4 dminus := by simpa [hiMinus] using h4Dminus
    exact Nat.ModEq.cancel_left_of_coprime h4dminus.symm.gcd_eq_one hfour
  have hresDmmul : i.E.r * i.E.s ^ 2 ≡ j.E.r * i.E.s ^ 2 [MOD dminus] := by
    simpa [Family.FamilyIndex.e, ExactDivisor.e, hjS] using hresDm
  have hscopDmpow : Nat.Coprime dminus (i.E.s ^ 2) :=
    (Nat.coprime_pow_right_iff (by norm_num : 0 < 2) dminus i.E.s).2
      hscopDminus'.symm
  have hresDm_r : i.E.r ≡ j.E.r [MOD dminus] :=
    Nat.ModEq.cancel_right_of_coprime hscopDmpow.gcd_eq_one hresDmmul
  have hresProd : i.E.r ≡ j.E.r [MOD D * i.dminus] :=
    (Nat.modEq_and_modEq_iff_modEq_mul
      (hDcopPz.coprime_dvd_right himem.dminus_dvd_Pz)).1
      ⟨hresD_r, by simpa [hiMinus] using hresDm_r⟩
  have hwindow : i.E.r ∈ Inputs.natWindow
      (phiProgressionU0 P i.E.s X) (phiProgressionU1 P i.E.s X) := by
    unfold Inputs.natWindow
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Nat.succ_le_iff.mpr (himem.r_pos hX)
    · apply Nat.le_floor
      simpa [phiProgressionU1] using himem.r_le
    · simpa [phiProgressionU0] using himem.r_gt
  have hsupport : i.E.r ∈ phiProgressionSupport P X (D * dminus)
      (familyTensorResidueSelector indices D c dminus b i.E.s) i.E.s := by
    unfold phiProgressionSupport
    apply Finset.mem_filter.mpr
    refine ⟨hwindow, i.E.r_squarefree, i.E.coprime_rs, ?_⟩
    simpa [Inputs.congMod, Nat.ModEq, familyTensorResidueSelector, hsel,
      hiMinus] using hresProd
  exact ⟨by
    unfold exactDivisorSRange
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨himem.s_pos, Nat.le_floor himem.s_le_S⟩, i.E.s_squarefree⟩,
    hscop, hselector_coprime, hsupport⟩

/-- The selected residue is reduced modulo `D d_-` on every exact-divisor
fiber, including the empty-fiber branch where the selector is `1`. -/
theorem familyTensorResidueSelector_coprime
    (P : Params) (X : ℝ) (Pz b : ℕ)
    (indices : Finset Family.FamilyIndex)
    (hX : 1 < X) (hbcop : Nat.Coprime b Pz)
    (hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X Pz b i)
    (D c dminus s : ℕ) (hD : 0 < D) :
    Nat.Coprime
      (familyTensorResidueSelector indices D c dminus b s)
      (D * dminus) := by
  classical
  by_cases h : ∃ i ∈ indices,
      familyTensorIndexPredicate D c dminus i ∧ i.E.s = s
  · let i : Family.FamilyIndex := Classical.choose h
    have hiData := Classical.choose_spec h
    have hi : i ∈ indices := hiData.1
    have hiPred : familyTensorIndexPredicate D c dminus i := hiData.2.1
    have hiS : i.E.s = s := hiData.2.2
    have hE : i.E ∈ familyExactValuesAtDminus indices D c dminus := by
      unfold familyExactValuesAtDminus familyExactValues
      exact Finset.mem_image.mpr ⟨i,
        Finset.mem_filter.mpr ⟨hi, hiPred⟩, rfl⟩
    have hsupport := familyExactValuesAtDminus_mem_support
      P X Pz b indices hX hbcop hmem D c dminus hD hE
    simpa [familyTensorResidueSelector, h, hiS] using hsupport.2.2.1
  · simp [familyTensorResidueSelector, h]

/-- The reciprocal-`\varphi` mass of an actual fixed-`d_-` fiber is bounded by
the corresponding concrete exact-divisor tensor.  This is the exact finite
sum comparison used before the cited progression upper estimate is applied. -/
theorem familyExactValuesAtDminus_recipTotient_le_tensor
    (P : Params) (X : ℝ) (Pz b : ℕ)
    (indices : Finset Family.FamilyIndex)
    (hX : 1 < X) (hbcop : Nat.Coprime b Pz)
    (hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X Pz b i)
    (D c dminus : ℕ) (hD : 0 < D) :
    (∑ E ∈ familyExactValuesAtDminus indices D c dminus,
      (1 : ℝ) / (Nat.totient E.rho : ℝ)) ≤
      exactDivisorMPhiTensorFiberCoprime P X (D * dminus)
        (fun s => familyTensorResidueSelector indices D c dminus b s) := by
  classical
  let Eset := familyExactValuesAtDminus indices D c dminus
  let Sset := Eset.image (fun E => E.s)
  have hEMaps : ∀ E ∈ Eset, E.s ∈ Sset := by
    intro E hE
    exact Finset.mem_image.mpr ⟨E, hE, rfl⟩
  have hpartition := Finset.sum_fiberwise_of_maps_to hEMaps
    (fun E : ExactDivisor => (1 : ℝ) / (Nat.totient E.rho : ℝ))
  have hsource :
      (∑ E ∈ Eset, (1 : ℝ) / (Nat.totient E.rho : ℝ)) =
        ∑ s ∈ Sset,
          ∑ E ∈ Eset.filter (fun E => E.s = s),
            (1 : ℝ) / (Nat.totient E.rho : ℝ) := by
    exact hpartition.symm
  rw [show familyExactValuesAtDminus indices D c dminus = Eset from rfl, hsource]
  let a : ℕ → ℕ := fun s => familyTensorResidueSelector indices D c dminus b s
  have hSsubset : Sset ⊆ exactDivisorSRange P X := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨E, hE, rfl⟩
    exact (familyExactValuesAtDminus_mem_support P X Pz b indices hX hbcop hmem
      D c dminus hD hE).1
  have hSterm : ∀ s ∈ Sset,
      (∑ E ∈ Eset.filter (fun E => E.s = s),
          (1 : ℝ) / (Nat.totient E.rho : ℝ)) ≤
        (if Nat.Coprime s (D * dminus) then
          ((1 : ℝ) / (Nat.totient s : ℝ)) *
            phiProgressionAverage P X (D * dminus) (a s) s
        else 0) := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨E0, hE0, rfl⟩
    have hE0support := familyExactValuesAtDminus_mem_support P X Pz b indices
      hX hbcop hmem D c dminus hD hE0
    have hsCoprime : Nat.Coprime E0.s (D * dminus) := hE0support.2.1
    have hEfilterSubset :
        Eset.filter (fun E => E.s = E0.s) ⊆ Eset :=
      Finset.filter_subset _ _
    have hRinj : Set.InjOn (fun E : ExactDivisor => E.r)
        ((Eset.filter (fun E => E.s = E0.s)) : Set ExactDivisor) := by
      intro E hE F hF hR
      have hEs : E.s = E0.s := (Finset.mem_filter.mp hE).2
      have hFs : F.s = E0.s := (Finset.mem_filter.mp hF).2
      cases E
      cases F
      simp_all
    have hRsubset :
        (Eset.filter (fun E => E.s = E0.s)).image (fun E => E.r) ⊆
          phiProgressionSupport P X (D * dminus) (a E0.s) E0.s := by
      intro r hr
      rcases Finset.mem_image.mp hr with ⟨E, hE, rfl⟩
      have hEall := (Finset.mem_filter.mp hE).1
      have hEs : E.s = E0.s := (Finset.mem_filter.mp hE).2
      simpa [a, hEs] using
        (familyExactValuesAtDminus_mem_support P X Pz b indices hX hbcop hmem
        D c dminus hD hEall).2.2.2
    have hRsum :
        (∑ r ∈ (Eset.filter (fun E => E.s = E0.s)).image
            (fun E => E.r),
          (1 : ℝ) / (Nat.totient r : ℝ)) =
          ∑ E ∈ Eset.filter (fun E => E.s = E0.s),
            (1 : ℝ) / (Nat.totient E.r : ℝ) := by
      exact Finset.sum_image hRinj
    have hfactor :
        (∑ E ∈ Eset.filter (fun E => E.s = E0.s),
            (1 : ℝ) / (Nat.totient E.rho : ℝ)) =
          ((1 : ℝ) / (Nat.totient E0.s : ℝ)) *
            (∑ E ∈ Eset.filter (fun E => E.s = E0.s),
              (1 : ℝ) / (Nat.totient E.r : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E hE
      have hEall : E ∈ Eset := hEfilterSubset hE
      unfold Eset familyExactValuesAtDminus familyExactValues at hEall
      rcases Finset.mem_image.mp hEall with ⟨i, hi, rfl⟩
      have hiMem : i ∈ indices := (Finset.mem_filter.mp hi).1
      have hiStatic := hmem i hiMem
      have hEposr : 0 < i.E.r := hiStatic.r_pos hX
      have hEposs : 0 < i.E.s := lt_of_lt_of_le Nat.zero_lt_one hiStatic.s_pos
      have hfactor := ExactDivisor.one_div_totient_rho_cast_eq
        i.E hEposr hEposs
      have hEs : i.E.s = E0.s := (Finset.mem_filter.mp hE).2
      simpa [Family.FamilyIndex.rho, hEs, mul_comm] using hfactor
    rw [if_pos hsCoprime, hfactor, ← hRsum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum_of_subset_of_nonneg hRsubset
    intro r _hr _hnot
    exact div_nonneg zero_le_one (by positivity)
  have houter :
      (∑ s ∈ Sset,
        ∑ E ∈ Eset.filter (fun E => E.s = s),
          (1 : ℝ) / (Nat.totient E.rho : ℝ)) ≤
        ∑ s ∈ Sset,
          (if Nat.Coprime s (D * dminus) then
            ((1 : ℝ) / (Nat.totient s : ℝ)) *
              phiProgressionAverage P X (D * dminus) (a s) s
          else 0) := by
    apply Finset.sum_le_sum
    intro s hs
    exact hSterm s hs
  have hnonneg : ∀ s ∈ exactDivisorSRange P X,
      0 ≤ (if Nat.Coprime s (D * dminus) then
        ((1 : ℝ) / (Nat.totient s : ℝ)) *
          phiProgressionAverage P X (D * dminus) (a s) s
      else 0) := by
    intro s _hs
    by_cases hcop : Nat.Coprime s (D * dminus)
    · rw [if_pos hcop]
      exact mul_nonneg
        (div_nonneg zero_le_one (Nat.cast_nonneg _))
        (phiProgressionAverage_nonneg P X (D * dminus) (a s) s)
    · rw [if_neg hcop]
  calc
    (∑ s ∈ Sset,
        ∑ E ∈ Eset.filter (fun E => E.s = s),
          (1 : ℝ) / (Nat.totient E.rho : ℝ)) ≤
        ∑ s ∈ Sset,
          (if Nat.Coprime s (D * dminus) then
            ((1 : ℝ) / (Nat.totient s : ℝ)) *
              phiProgressionAverage P X (D * dminus) (a s) s
          else 0) := houter
    _ ≤ ∑ s ∈ exactDivisorSRange P X,
          (if Nat.Coprime s (D * dminus) then
            ((1 : ℝ) / (Nat.totient s : ℝ)) *
              phiProgressionAverage P X (D * dminus) (a s) s
          else 0) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSsubset
      intro s _hs _hnot
      exact hnonneg s _hs
    _ = exactDivisorMPhiTensorFiberCoprime P X (D * dminus) a := by
      rfl

/-- Standard tensor propagation for one actual small-divisor fiber.  All
finite-family conditions are discharged here; the only analytic datum exposed
is the cited `M_\varphi` tensor estimate together with its mass lower
comparison. -/
theorem familyExactValuesAtDminus_recipTotient_le_of_tensor_bound
    (P : Params) (X : ℝ) (Pz b : ℕ)
    (indices : Finset Family.FamilyIndex)
    (hX : 1 < X) (hbcop : Nat.Coprime b Pz)
    (hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X Pz b i)
    (D c dminus : ℕ)
    (hDone : 1 ≤ D) (hDsqf : Squarefree D) (hDodd : Odd D)
    (hDcopPz : Nat.Coprime D Pz)
    (hDleY : (D : ℝ) ≤ YScale P X)
    (hdmpos : 0 < dminus) (hdmleU : (dminus : ℝ) ≤ UScale X)
    (hdmdiv : dminus ∣ Pz) (hdmsqf : Squarefree dminus)
    (hdmodd : Odd dminus)
    (K cφ Xtensor Xmass : ℝ) (hcφ : 0 < cφ)
    (hTensor : ∀ X : ℝ, Xtensor ≤ X → ∀ M : ℕ, 1 ≤ M →
      Squarefree M → Odd M →
      (M : ℝ) ≤ YScale P X * UScale X →
      ∀ a : ℕ → ℕ,
        (∀ s ∈ exactDivisorSRange P X, Nat.Coprime s M →
          Nat.Coprime (a s) M) →
        ∀ cφ' : ℝ, 0 < cφ' →
          cφ' * exactDivisorMPhiMassShape P X ≤
            exactDivisorMPhiMassFiber P X →
          exactDivisorMPhiTensorFiberCoprime P X M a ≤
            (K / cφ') * (exactDivisorMPhiMassRaw P X / (M : ℝ)))
    (hMass : ∀ X : ℝ, Xmass ≤ X →
      cφ * exactDivisorMPhiMassShape P X ≤
        exactDivisorMPhiMassFiber P X)
    (hXbound : max Xtensor Xmass ≤ X) :
    (∑ E ∈ familyExactValuesAtDminus indices D c dminus,
      (1 : ℝ) / (Nat.totient E.rho : ℝ)) ≤
      (K / cφ) *
        (exactDivisorMPhiMassRaw P X / ((D * dminus : ℕ) : ℝ)) := by
  have hXtensor : Xtensor ≤ X :=
    le_trans (le_max_left _ _) hXbound
  have hXmass : Xmass ≤ X :=
    le_trans (le_max_right _ _) hXbound
  have hMone : 1 ≤ D * dminus := by
    simpa using Nat.mul_le_mul hDone (Nat.succ_le_iff.mpr hdmpos)
  have hDcopDm : Nat.Coprime D dminus :=
    hDcopPz.coprime_dvd_right hdmdiv
  have hMsqf : Squarefree (D * dminus) :=
    (Nat.squarefree_mul hDcopDm).mpr ⟨hDsqf, hdmsqf⟩
  have hModd : Odd (D * dminus) := hDodd.mul hdmodd
  have hYnonneg : 0 ≤ YScale P X := by
    exact Real.rpow_nonneg (lt_trans zero_lt_one hX).le P.σ
  have hUnonneg : 0 ≤ UScale X := by
    unfold UScale
    positivity
  have hMrange : ((D * dminus : ℕ) : ℝ) ≤
      YScale P X * UScale X := by
    calc
      ((D * dminus : ℕ) : ℝ) = (D : ℝ) * (dminus : ℝ) := by norm_num
      _ ≤ YScale P X * UScale X :=
        mul_le_mul hDleY hdmleU (Nat.cast_nonneg _) hYnonneg
  let a : ℕ → ℕ :=
    fun s => familyTensorResidueSelector indices D c dminus b s
  have ha : ∀ s ∈ exactDivisorSRange P X,
      Nat.Coprime s (D * dminus) → Nat.Coprime (a s) (D * dminus) := by
    intro s _hs _hcop
    exact familyTensorResidueSelector_coprime P X Pz b indices hX hbcop
      hmem D c dminus s (by omega)
  have hT := hTensor X hXtensor (D * dminus) hMone hMsqf hModd hMrange a ha
    cφ hcφ (hMass X hXmass)
  have hfinite := familyExactValuesAtDminus_recipTotient_le_tensor
    P X Pz b indices hX hbcop hmem D c dminus (by omega)
  exact hfinite.trans hT

/-- Fully instantiated actual-family tensor bound on one `dminus` fiber.  The
only analytic dependencies are the cited ordinary-squarefree progression
estimates already used by the manuscript's exact-divisor tensor theorem. -/
theorem familyExactValuesAtDminus_recipTotient_le_standard_tensor
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ K X₀ : ℝ, 0 < K ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X →
      ∀ Pz b : ℕ, Nat.Coprime b Pz →
      ∀ indices : Finset Family.FamilyIndex,
      (∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i) →
      ∀ D c dminus : ℕ,
      1 ≤ D → Squarefree D → Odd D → Nat.Coprime D Pz →
      (D : ℝ) ≤ YScale P X →
      0 < dminus → (dminus : ℝ) ≤ UScale X →
      dminus ∣ Pz → Squarefree dminus → Odd dminus →
      (∑ E ∈ familyExactValuesAtDminus indices D c dminus,
        (1 : ℝ) / (Nat.totient E.rho : ℝ)) ≤
        K * (exactDivisorMPhiMassRaw P X /
          ((D * dminus : ℕ) : ℝ)) := by
  rcases
      exactDivisorMPhiTensorFiberCoprime_le_massRaw_over_modulus_of_standard_ordinarySquarefree
        (P := P) with
    ⟨Kt, Xt, hKt, htensor⟩
  rcases exactDivisorMPhiMassFiber_comparable_to_shape_of_fiberAverageTwoSided
      (ExactDivisorMPhiFiberAverageTwoSided_of_standard_ordinarySquarefree
        (P := P)) with
    ⟨cφ, _Cφ, Xm, hcφ, _hCφ, hmass⟩
  refine ⟨Kt / cφ, max Xt Xm, div_pos hKt hcφ, ?_⟩
  intro X hX hXgt Pz b hbcop indices hmem D c dminus
    hDone hDsqf hDodd hDcopPz hDleY hdmpos hdmleU hdmdiv hdmsqf hdmodd
  have hXt : Xt ≤ X := le_trans (le_max_left _ _) hX
  have hXm : Xm ≤ X := le_trans (le_max_right _ _) hX
  have hbound := familyExactValuesAtDminus_recipTotient_le_of_tensor_bound
    P X Pz b indices hXgt hbcop hmem D c dminus hDone hDsqf hDodd
      hDcopPz hDleY hdmpos hdmleU hdmdiv hdmsqf hdmodd
      Kt cφ Xt Xm hcφ htensor (fun X hX => (hmass X hX).1)
      (show max Xt Xm ≤ X from hX)
  simpa [div_mul_eq_mul_div, mul_assoc] using hbound

/-- Every exact divisor represented in an actual residue fiber has prime
modulus `4*rho` in the fixed Brun--Titchmarsh range `X^(beta/2)`. -/
theorem familyExactValuesAtDminus_modulus_range_eventually
    (P : Params) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → 1 < X →
      ∀ Pz b : ℕ, ∀ indices : Finset Family.FamilyIndex,
      (∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i) →
      ∀ D c dminus : ℕ,
      ∀ E ∈ familyExactValuesAtDminus indices D c dminus,
        (4 * E.rho : ℝ) ≤ X ^ (P.β / 2) := by
  have hgap : 0 < P.β / 2 - P.θ := by linarith [P.two_θ_lt_β]
  rcases fixedNat_le_rpow_eventually_threshold 4 hgap with ⟨X4, h4⟩
  refine ⟨max X4 1, ?_⟩
  intro X hX hXgt Pz b indices hmem D c dminus E hE
  unfold familyExactValuesAtDminus familyExactValues at hE
  rcases Finset.mem_image.mp hE with ⟨i, hi, rfl⟩
  have hiIndices := (Finset.mem_filter.mp hi).1
  have himem := hmem i hiIndices
  have hsNat : 1 ≤ i.E.s := himem.s_pos
  have hsPos : 0 < (i.E.s : ℝ) := by exact_mod_cast
    (lt_of_lt_of_le Nat.zero_lt_one hsNat)
  have hsSqPos : 0 < (i.E.s : ℝ) ^ 2 := pow_pos hsPos _
  have heH : (i.E.e : ℝ) ≤ HScale P X := by
    have hr := (le_div_iff₀ hsSqPos).mp himem.r_le
    simpa [ExactDivisor.e, Nat.cast_mul, Nat.cast_pow] using hr
  have hρeNat : i.E.rho ≤ i.E.e := by
    unfold ExactDivisor.rho ExactDivisor.e
    exact Nat.mul_le_mul_left i.E.r
      (by simpa [pow_two] using Nat.le_mul_of_pos_left i.E.s hsNat)
  have hρH : (i.E.rho : ℝ) ≤ HScale P X := by
    have hρe : (i.E.rho : ℝ) ≤ (i.E.e : ℝ) := by exact_mod_cast hρeNat
    exact hρe.trans heH
  have hX4 : X4 ≤ X := le_trans (le_max_left _ _) hX
  have hfour := h4 X hX4
  have hXpos : 0 < X := lt_trans zero_lt_one hXgt
  calc
    (4 * i.E.rho : ℝ) = (4 : ℝ) * (i.E.rho : ℝ) := by norm_num
    _ ≤ X ^ (P.β / 2 - P.θ) * (i.E.rho : ℝ) :=
      mul_le_mul_of_nonneg_right hfour (Nat.cast_nonneg _)
    _ ≤ X ^ (P.β / 2 - P.θ) * X ^ P.θ := by
      exact mul_le_mul_of_nonneg_left hρH
        (Real.rpow_nonneg (le_trans zero_le_one hXgt.le) _)
    _ = X ^ (P.β / 2) := by
      rw [← Real.rpow_add hXpos]
      congr 1
      ring

/-- Sum the fixed-`dminus` prime estimates after replacing the denominator
`φ (4 * rho)` by the smaller carrier denominator `φ rho`. -/
theorem familyFixedDminusResidueMass_le_bt
    (P : Params) (X : ℝ)
    (indices : Finset Family.FamilyIndex)
    (D c dminus : ℕ) (hD : 0 < D)
    (Cbt R : ℝ) (hCbt : 0 ≤ Cbt) (hR : 0 ≤ R)
    (hρpos : ∀ E ∈ familyExactValuesAtDminus indices D c dminus,
      0 < E.rho)
    (hbt : ∀ E ∈ familyExactValuesAtDminus indices D c dminus,
      familyFixedEDminusDivisorMass
          (indices.filter (fun i => i.e % D = c)) E dminus D ≤
        (Cbt / (Nat.totient (4 * E.rho) : ℝ)) *
          (1 / (D : ℝ)) * Inputs.roughInitial X (4 * E.rho) P.σ)
    (hrough : ∀ E ∈ familyExactValuesAtDminus indices D c dminus,
      Inputs.roughInitial X (4 * E.rho) P.σ ≤ R) :
    (∑ E ∈ familyExactValuesAtDminus indices D c dminus,
      familyFixedEDminusDivisorMass
        (indices.filter (fun i => i.e % D = c)) E dminus D) ≤
      Cbt * R * (1 / (D : ℝ)) *
        (∑ E ∈ familyExactValuesAtDminus indices D c dminus,
          (1 : ℝ) / (Nat.totient E.rho : ℝ)) := by
  classical
  let Eset := familyExactValuesAtDminus indices D c dminus
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast hD
  have hDinv : 0 ≤ (1 / (D : ℝ)) := by positivity
  have hterm : ∀ E ∈ Eset,
      familyFixedEDminusDivisorMass
          (indices.filter (fun i => i.e % D = c)) E dminus D ≤
        Cbt * R * (1 / (D : ℝ)) *
          ((1 : ℝ) / (Nat.totient E.rho : ℝ)) := by
    intro E hE
    have hφrho : 0 < (Nat.totient E.rho : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (hρpos E hE)
    have htot_le_nat : Nat.totient E.rho ≤ Nat.totient (4 * E.rho) := by
      have hsmall : Nat.totient E.rho ≤
          Nat.totient 4 * Nat.totient E.rho := by
        have hphi4 : Nat.totient 4 = 2 := by
          simpa [show (4 : ℕ) = 2 * 2 by norm_num] using
            Nat.totient_mul_of_prime_of_dvd Nat.prime_two
              (by norm_num : 2 ∣ 2)
        rw [hphi4]
        omega
      exact hsmall.trans (Nat.totient_super_multiplicative 4 E.rho)
    have htot_le : (Nat.totient E.rho : ℝ) ≤
        (Nat.totient (4 * E.rho) : ℝ) := by exact_mod_cast htot_le_nat
    have hrecip :
        (1 : ℝ) / (Nat.totient (4 * E.rho) : ℝ) ≤
          (1 : ℝ) / (Nat.totient E.rho : ℝ) :=
      one_div_le_one_div_of_le hφrho htot_le
    have hroughE := hrough E hE
    have hbtE := hbt E hE
    have hfac_nonneg : 0 ≤
        (Cbt / (Nat.totient (4 * E.rho) : ℝ)) *
          (1 / (D : ℝ)) := by positivity
    have hfacR_nonneg : 0 ≤ Cbt * R * (1 / (D : ℝ)) := by positivity
    calc
      familyFixedEDminusDivisorMass
          (indices.filter (fun i => i.e % D = c)) E dminus D ≤
          (Cbt / (Nat.totient (4 * E.rho) : ℝ)) *
            (1 / (D : ℝ)) * R := by
        calc
          _ ≤ (Cbt / (Nat.totient (4 * E.rho) : ℝ)) *
              (1 / (D : ℝ)) * Inputs.roughInitial X
                (4 * E.rho) P.σ := hbtE
          _ ≤ (Cbt / (Nat.totient (4 * E.rho) : ℝ)) *
              (1 / (D : ℝ)) * R := by
            exact mul_le_mul_of_nonneg_left hroughE
              (mul_nonneg (div_nonneg hCbt (by positivity)) hDinv)
      _ ≤ Cbt * R * (1 / (D : ℝ)) *
          ((1 : ℝ) / (Nat.totient E.rho : ℝ)) := by
        calc
          (Cbt / (Nat.totient (4 * E.rho) : ℝ)) *
              (1 / (D : ℝ)) * R =
              (Cbt * R * (1 / (D : ℝ))) *
                (1 / (Nat.totient (4 * E.rho) : ℝ)) := by ring
          _ ≤ (Cbt * R * (1 / (D : ℝ))) *
                (1 / (Nat.totient E.rho : ℝ)) :=
            mul_le_mul_of_nonneg_left hrecip hfacR_nonneg
  rw [show familyExactValuesAtDminus indices D c dminus = Eset from rfl]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro E hE
  exact hterm E hE

/-- Exact partition of one actual `(e,dminus)` divisor-restricted mass into
its `dplus` fibers, followed by the prime reciprocal sum in each fiber. -/
theorem familyFixedEDminusDivisorMass_eq_sum_dplus_primeValues
    (P : Params) (X : ℝ) (Pz b : ℕ)
    (indices : Finset Family.FamilyIndex) (E : ExactDivisor)
    (dminus D : ℕ)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i) :
    familyFixedEDminusDivisorMass indices E dminus D =
      ∑ dplus ∈ (familyDplusValues indices E dminus).filter
          (fun dplus => D ∣ dplus),
        ((1 : ℝ) / (dplus : ℝ)) *
          (∑ p ∈ familyPrimeValues indices E dminus dplus,
            (1 : ℝ) / (p : ℝ)) := by
  classical
  let s := indices.filter
    (fun i => i.E = E ∧ i.dminus = dminus ∧ D ∣ i.dplus)
  let t := (familyDplusValues indices E dminus).filter
    (fun dplus => D ∣ dplus)
  have hmaps : ∀ i ∈ s, i.dplus ∈ t := by
    intro i hi
    have hiData := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨?_, hiData.2.2.2⟩
    unfold familyDplusValues
    apply Finset.mem_image.mpr
    exact ⟨i, Finset.mem_filter.mpr
      ⟨hiData.1, hiData.2.1, hiData.2.2.1⟩, rfl⟩
  have hpartition := Finset.sum_fiberwise_of_maps_to hmaps
    (fun i : Family.FamilyIndex =>
      (1 : ℝ) / ((i.dplus * i.p : ℕ) : ℝ))
  unfold familyFixedEDminusDivisorMass
  change (∑ i ∈ s, (1 : ℝ) / ((i.dplus * i.p : ℕ) : ℝ)) = _
  rw [← hpartition]
  apply Finset.sum_congr rfl
  intro dplus hdplus
  have hdplusData := Finset.mem_filter.mp hdplus
  have hdplusPos : 0 < dplus := by
    rcases Finset.mem_image.mp hdplusData.1 with ⟨i, hi, rfl⟩
    exact (hmem i (Finset.mem_of_mem_filter i hi)).dplus_pos
  let fiber := indices.filter
    (fun i => i.E = E ∧ i.dminus = dminus ∧ i.dplus = dplus)
  have hfilter : (s.filter (fun i => i.dplus = dplus)) = fiber := by
    ext i
    simp only [s, fiber, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hi, hiE, hiMinus, hiD⟩, hiPlus⟩
      exact ⟨hi, hiE, hiMinus, hiPlus⟩
    · rintro ⟨hi, hiE, hiMinus, hiPlus⟩
      exact ⟨⟨hi, hiE, hiMinus, hiPlus ▸ hdplusData.2⟩, hiPlus⟩
  rw [hfilter]
  have hinj : Set.InjOn (fun i : Family.FamilyIndex => i.p) (fiber : Set _) := by
    intro i hi j hj hp
    have hiData := Finset.mem_filter.mp hi
    have hjData := Finset.mem_filter.mp hj
    cases i
    cases j
    simp_all
  have hprimeSum :
      (∑ p ∈ familyPrimeValues indices E dminus dplus,
          (1 : ℝ) / (p : ℝ)) =
        ∑ i ∈ fiber, (1 : ℝ) / (i.p : ℝ) := by
    unfold familyPrimeValues
    exact Finset.sum_image hinj
  rw [hprimeSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hiPlus : i.dplus = dplus := (Finset.mem_filter.mp hi).2.2.2
  rw [hiPlus]
  simp only [Nat.cast_mul]
  field_simp

/-- Exact finite decomposition of the corrected residue carrier into exact
divisors and small divisors.  This is the carrier-level identity needed before
the analytic prime and rough-cofactor estimates are applied. -/
theorem familyResidueMassRat_real_eq_exactDminus_partition
    (P : Params) (X : ℝ) (Pz b : ℕ)
    (indices : Finset Family.FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i)
    (D c : ℕ) :
    (Family.familyResidueMassRat indices D c : ℝ) =
      ∑ E ∈ familyExactValues indices,
        ∑ dminus ∈ familyDminusValues
            (indices.filter (fun i => i.e % D = c)) E,
          familyFixedEDminusDivisorMass
            (indices.filter (fun i => i.e % D = c)) E dminus D := by
  classical
  let I := indices.filter (fun i => i.e % D = c)
  let S := I.filter (fun i => D ∣ i.dplus)
  have hindex := Family.familyResidueMassRat_eq_index_sum
    P X Pz b indices hX hmem D c
  have hindexReal :
      (Family.familyResidueMassRat indices D c : ℝ) =
        ((∑ i ∈ Finset.filter
          (fun i => D ∣ i.dplus ∧ i.e % D = c) indices, i.wRat : ℚ) : ℝ) := by
    exact_mod_cast hindex
  rw [hindexReal]
  have hsumRat :
      (∑ i ∈ Finset.filter
          (fun i => D ∣ i.dplus ∧ i.e % D = c) indices, i.wRat) =
        ∑ i ∈ S, i.wRat := by
    simp [S, I, Finset.filter_filter, and_comm, and_left_comm]
  have hsumReal' :
      ((∑ i ∈ Finset.filter
          (fun i => D ∣ i.dplus ∧ i.e % D = c) indices, i.wRat : ℚ) : ℝ) =
        ∑ i ∈ S, (i.wRat : ℝ) := by
    exact_mod_cast hsumRat
  rw [hsumReal']
  have hEMaps : ∀ i ∈ S, i.E ∈ familyExactValues indices := by
    intro i hi
    have hiI := (Finset.mem_filter.mp hi).1
    have hiIndices := (Finset.mem_filter.mp hiI).1
    unfold familyExactValues
    exact Finset.mem_image.mpr ⟨i, hiIndices, rfl⟩
  have hEPartition := Finset.sum_fiberwise_of_maps_to hEMaps
    (fun i : Family.FamilyIndex => (i.wRat : ℝ))
  rw [← hEPartition]
  apply Finset.sum_congr rfl
  intro E hE
  let SE := S.filter (fun i => i.E = E)
  let tE := familyDminusValues I E
  have hdmMaps : ∀ i ∈ SE, i.dminus ∈ tE := by
    intro i hi
    have hiS := (Finset.mem_filter.mp hi).1
    have hiI := (Finset.mem_filter.mp hiS).1
    have hiIndices := (Finset.mem_filter.mp hiI).1
    have hiE := (Finset.mem_filter.mp hi).2
    change i.dminus ∈ familyDminusValues I E
    unfold familyDminusValues
    exact Finset.mem_image.mpr ⟨i,
      Finset.mem_filter.mpr ⟨hiI, hiE⟩, rfl⟩
  have hdmPartition := Finset.sum_fiberwise_of_maps_to hdmMaps
    (fun i : Family.FamilyIndex => (i.wRat : ℝ))
  rw [← hdmPartition]
  apply Finset.sum_congr rfl
  intro dminus hdminus
  unfold familyFixedEDminusDivisorMass
  have hfilter :
      SE.filter (fun i => i.dminus = dminus) =
        I.filter (fun i => i.E = E ∧ i.dminus = dminus ∧ D ∣ i.dplus) := by
    ext i
    constructor
    · intro hi
      have hiDm := Finset.mem_filter.mp hi
      have hiSE := Finset.mem_filter.mp hiDm.1
      have hiS := Finset.mem_filter.mp hiSE.1
      exact Finset.mem_filter.mpr
        ⟨hiS.1, ⟨hiSE.2, hiDm.2, hiS.2⟩⟩
    · intro hi
      have hiI := Finset.mem_filter.mp hi
      have hiData := hiI.2
      have hiS : i ∈ S := Finset.mem_filter.mpr ⟨hiI.1, hiData.2.2⟩
      have hiSE : i ∈ SE := Finset.mem_filter.mpr ⟨hiS, hiData.1⟩
      exact Finset.mem_filter.mpr ⟨hiSE, hiData.2.1⟩
  rw [hfilter]
  simp [I, Finset.filter_filter, and_assoc, and_left_comm, and_comm,
    Family.FamilyIndex.wRat, EscLeanChecks.conditionalModulus]

/-- The same finite carrier identity with the two sums ordered by `dminus`
first.  This is the order needed to apply the tensor estimate at modulus
`D * dminus` and then sum the resulting `1 / dminus` factor. -/
theorem familyResidueMassRat_real_eq_dminus_partition
    (P : Params) (X : ℝ) (Pz b : ℕ)
    (indices : Finset Family.FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i)
    (D c : ℕ) :
    (Family.familyResidueMassRat indices D c : ℝ) =
      ∑ dminus ∈ familyDminusResidueValues indices D c,
        ∑ E ∈ familyExactValuesAtDminus indices D c dminus,
          familyFixedEDminusDivisorMass
            (indices.filter (fun i => i.e % D = c)) E dminus D := by
  classical
  let I := indices.filter (fun i => i.e % D = c)
  let S := indices.filter (fun i => D ∣ i.dplus ∧ i.e % D = c)
  let U := familyDminusResidueValues indices D c
  have hindex := Family.familyResidueMassRat_eq_index_sum
    P X Pz b indices hX hmem D c
  have hindexReal :
      (Family.familyResidueMassRat indices D c : ℝ) =
        ((∑ i ∈ Finset.filter
          (fun i => D ∣ i.dplus ∧ i.e % D = c) indices, i.wRat : ℚ) : ℝ) := by
    exact_mod_cast hindex
  rw [hindexReal]
  have hsumRat :
      (∑ i ∈ Finset.filter
          (fun i => D ∣ i.dplus ∧ i.e % D = c) indices, i.wRat) =
        ∑ i ∈ S, i.wRat := by
    simp [S]
  have hsumReal :
      ((∑ i ∈ Finset.filter
          (fun i => D ∣ i.dplus ∧ i.e % D = c) indices, i.wRat : ℚ) : ℝ) =
        ∑ i ∈ S, (i.wRat : ℝ) := by
    exact_mod_cast hsumRat
  rw [hsumReal]
  have hdmMaps : ∀ i ∈ S, i.dminus ∈ U := by
    intro i hi
    have hiI : i ∈ I := by
      apply Finset.mem_filter.mpr
      exact ⟨(Finset.mem_filter.mp hi).1,
        (Finset.mem_filter.mp hi).2.2⟩
    unfold U familyDminusResidueValues
    exact Finset.mem_image.mpr ⟨i, hiI, rfl⟩
  have hdmPartition := Finset.sum_fiberwise_of_maps_to hdmMaps
    (fun i : Family.FamilyIndex => (i.wRat : ℝ))
  rw [← hdmPartition]
  apply Finset.sum_congr rfl
  intro dminus hdminus
  let T := S.filter (fun i => i.dminus = dminus)
  have hEMaps : ∀ i ∈ T,
      i.E ∈ familyExactValuesAtDminus indices D c dminus := by
    intro i hi
    have hiT := Finset.mem_filter.mp hi
    have hiS := Finset.mem_filter.mp hiT.1
    have hiS' : i ∈ indices ∧ D ∣ i.dplus ∧ i.e % D = c := by
      simpa [S] using hiS
    unfold familyExactValuesAtDminus familyExactValues
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨hiS'.1, ?_⟩
    simpa [familyTensorIndexPredicate] using
      (show i.dminus = dminus ∧ D ∣ i.dplus ∧ i.e % D = c from
        ⟨hiT.2, hiS'.2.1, hiS'.2.2⟩)
  have hEPartition := Finset.sum_fiberwise_of_maps_to hEMaps
    (fun i : Family.FamilyIndex => (i.wRat : ℝ))
  rw [← hEPartition]
  apply Finset.sum_congr rfl
  intro E hE
  unfold familyFixedEDminusDivisorMass
  have hfilter :
      T.filter (fun i => i.E = E) =
        I.filter (fun i => i.E = E ∧ i.dminus = dminus ∧ D ∣ i.dplus) := by
    ext i
    constructor
    · intro hi
      have hiOuter := Finset.mem_filter.mp hi
      have hiT := Finset.mem_filter.mp hiOuter.1
      have hiS : i ∈ indices ∧ D ∣ i.dplus ∧ i.e % D = c := by
        simpa [S] using hiT.1
      have hiI : i ∈ I := by
        apply Finset.mem_filter.mpr
        exact ⟨hiS.1, hiS.2.2⟩
      exact Finset.mem_filter.mpr
        ⟨hiI, ⟨hiOuter.2, hiT.2, hiS.2.1⟩⟩
    · intro hi
      have hiI := Finset.mem_filter.mp hi
      have hiData := hiI.2
      have hiI' : i ∈ indices ∧ i.e % D = c := by
        simpa [I] using hiI.1
      have hiS : i ∈ S := by
        apply Finset.mem_filter.mpr
        exact ⟨hiI'.1, ⟨hiData.2.2, hiI'.2⟩⟩
      have hiT : i ∈ T := by
        apply Finset.mem_filter.mpr
        exact ⟨hiS, hiData.2.1⟩
      exact Finset.mem_filter.mpr ⟨hiT, hiData.1⟩
  rw [hfilter]
  simp [I, T, S, Finset.filter_filter, and_assoc, and_left_comm, and_comm,
    Family.FamilyIndex.wRat, EscLeanChecks.conditionalModulus]

/-- Exact finite decomposition of the complete family mass by its exact
divisor and small-divisor coordinates. -/
theorem familyIndexMassRat_real_eq_exactDminus_partition
    (P : Params) (X : ℝ) (Pz b : ℕ)
    (indices : Finset Family.FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i) :
    (Family.familyIndexMassRat indices : ℝ) =
      ∑ E ∈ familyExactValues indices,
        ∑ dminus ∈ familyDminusValues indices E,
          familyFixedEDminusDivisorMass indices E dminus 1 := by
  have hEvent : Family.familyEventMassRat indices =
      Family.familyIndexMassRat indices :=
    Family.familyEventMassRat_eq_familyIndexMassRat
      P X Pz b indices hX hmem
  have hResidue : Family.familyResidueMassRat indices 1 0 =
      Family.familyEventMassRat indices := by
    simp [Family.familyResidueMassRat, Family.familyEventMassRat, Nat.mod_one]
  have hPartition := familyResidueMassRat_real_eq_exactDminus_partition
    P X Pz b indices hX hmem 1 0
  calc
    (Family.familyIndexMassRat indices : ℝ) =
        (Family.familyResidueMassRat indices 1 0 : ℝ) := by
      exact_mod_cast (hResidue.trans hEvent).symm
    _ = ∑ E ∈ familyExactValues indices,
        ∑ dminus ∈ familyDminusValues indices E,
          familyFixedEDminusDivisorMass indices E dminus 1 := by
      simpa [Nat.mod_one] using hPartition

/-- Exact prime-fiber expansion of the complete finite family mass.  This is
the carrier identity needed before comparing the actual prime fibers with the
reciprocal prime progression main term and weighted-BV error. -/
theorem familyIndexMassRat_real_eq_primeFibers
    (P : Params) (X : ℝ) (Pz b : ℕ)
    (indices : Finset Family.FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i) :
    (Family.familyIndexMassRat indices : ℝ) =
      ∑ E ∈ familyExactValues indices,
        ∑ dminus ∈ familyDminusValues indices E,
          ∑ dplus ∈ familyDplusValues indices E dminus,
            ((1 : ℝ) / (dplus : ℝ)) *
              (∑ p ∈ familyPrimeValues indices E dminus dplus,
                (1 : ℝ) / (p : ℝ)) := by
  rw [familyIndexMassRat_real_eq_exactDminus_partition
    P X Pz b indices hX hmem]
  apply Finset.sum_congr rfl
  intro E hE
  apply Finset.sum_congr rfl
  intro dminus hdminus
  rw [familyFixedEDminusDivisorMass_eq_sum_dplus_primeValues
    P X Pz b indices E dminus 1 hmem]
  simp

private theorem familyDplusValues_multiples_recip_le_roughInitial_pre
    (P : Params) (X : ℝ) (b D : ℕ)
    (indices : Finset Family.FamilyIndex) (E : ExactDivisor) (dminus : ℕ)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X (Inputs.roughModulus X) b i)
    (hD : 0 < D) :
    (∑ dplus ∈ (familyDplusValues indices E dminus).filter
        (fun dplus => D ∣ dplus), (1 : ℝ) / (dplus : ℝ)) ≤
      (1 / (D : ℝ)) * Inputs.roughInitial X (4 * E.rho) P.σ := by
  classical
  let U := familyDplusValues indices E dminus
  have hUpos : ∀ dplus ∈ U, 0 < dplus := by
    intro dplus hdplus
    rcases Finset.mem_image.mp hdplus with ⟨i, hi, rfl⟩
    exact (hmem i (Finset.mem_of_mem_filter i hi)).dplus_pos
  have hfactor :=
    EscLeanChecks.reciprocal_sum_multiples_eq_divisor_inv_mul_quotient_image
      U D hD hUpos
  rw [hfactor]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold Inputs.roughInitial
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    rcases Finset.mem_image.mp ht with ⟨dplus, hdplus, rfl⟩
    have hdplusData := Finset.mem_filter.mp hdplus
    rcases Finset.mem_image.mp hdplusData.1 with ⟨i, hi, hidplus⟩
    have hiData := Finset.mem_filter.mp hi
    have hiMem : i ∈ indices := hiData.1
    have hiE : i.E = E := hiData.2.1
    have hDi : D ∣ i.dplus := by simpa [hidplus] using hdplusData.2
    have hsupport :=
      (hmem i hiMem).dplus_div_mem_roughInitial_support hX hD hDi
    simpa [hidplus, Family.FamilyIndex.rho, hiE] using hsupport
  · intro t _htBig _htSmall
    positivity

/-- Quantitative propagation on one exact-divisor/small-divisor fiber.  Once
the fixed-prime Brun--Titchmarsh estimate is supplied, the `dplus = D*t`
change of variables gives the first reciprocal divisor factor without any
additional analytic assumption. -/
theorem familyFixedEDminusDivisorMass_le_bt_mul_roughInitial
    (P : Params) (X : ℝ) (b : ℕ)
    (indices : Finset Family.FamilyIndex) (E : ExactDivisor)
    (dminus D c : ℕ) (C : ℝ)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X (Inputs.roughModulus X) b i)
    (hD : 0 < D) (hC : 0 ≤ C) (hρ : 0 < E.rho)
    (hPrime : ∀ dplus ∈ familyDplusValues
        (indices.filter (fun i => i.e % D = c)) E dminus,
      (∑ p ∈ familyPrimeValues
          (indices.filter (fun i => i.e % D = c)) E dminus dplus,
            (1 : ℝ) / (p : ℝ)) ≤
        C / (Nat.totient (4 * E.rho) : ℝ)) :
    familyFixedEDminusDivisorMass
        (indices.filter (fun i => i.e % D = c)) E dminus D ≤
      (C / (Nat.totient (4 * E.rho) : ℝ)) *
        (1 / (D : ℝ)) * Inputs.roughInitial X (4 * E.rho) P.σ := by
  classical
  let I := indices.filter (fun i => i.e % D = c)
  have hmemI : ∀ i ∈ I,
      Family.FamilyStaticMem P X (Inputs.roughModulus X) b i := by
    intro i hi
    exact hmem i (Finset.mem_filter.mp hi).1
  rw [familyFixedEDminusDivisorMass_eq_sum_dplus_primeValues
    P X (Inputs.roughModulus X) b I E dminus D hmemI]
  have hphi : 0 < (Nat.totient (4 * E.rho) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hfactorNonneg : 0 ≤ C / (Nat.totient (4 * E.rho) : ℝ) :=
    div_nonneg hC hphi.le
  have hrough := familyDplusValues_multiples_recip_le_roughInitial_pre
    P X b D I E dminus hX hmemI hD
  have hterm :
      ∀ dplus ∈ (familyDplusValues I E dminus).filter
          (fun dplus => D ∣ dplus),
        ((1 : ℝ) / (dplus : ℝ)) *
            (∑ p ∈ familyPrimeValues I E dminus dplus,
              (1 : ℝ) / (p : ℝ)) ≤
          ((1 : ℝ) / (dplus : ℝ)) *
            (C / (Nat.totient (4 * E.rho) : ℝ)) := by
    intro dplus hdplus
    exact mul_le_mul_of_nonneg_left
      (hPrime dplus (Finset.mem_of_mem_filter dplus hdplus))
      (by positivity)
  calc
    (∑ dplus ∈ (familyDplusValues I E dminus).filter
        (fun dplus => D ∣ dplus),
        ((1 : ℝ) / (dplus : ℝ)) *
          (∑ p ∈ familyPrimeValues I E dminus dplus,
            (1 : ℝ) / (p : ℝ))) ≤
      ∑ dplus ∈ (familyDplusValues I E dminus).filter
        (fun dplus => D ∣ dplus),
        ((1 : ℝ) / (dplus : ℝ)) *
          (C / (Nat.totient (4 * E.rho) : ℝ)) := by
      apply Finset.sum_le_sum
      intro dplus hdplus
      exact hterm dplus hdplus
    _ = (C / (Nat.totient (4 * E.rho) : ℝ)) *
        (∑ dplus ∈ (familyDplusValues I E dminus).filter
          (fun dplus => D ∣ dplus), (1 : ℝ) / (dplus : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro dplus hdplus
      ring
    _ ≤ (C / (Nat.totient (4 * E.rho) : ℝ)) *
        ((1 / (D : ℝ)) * Inputs.roughInitial X (4 * E.rho) P.σ) := by
      exact mul_le_mul_of_nonneg_left hrough hfactorNonneg
    _ = (C / (Nat.totient (4 * E.rho) : ℝ)) *
        (1 / (D : ℝ)) * Inputs.roughInitial X (4 * E.rho) P.σ := by
      ring

/-- All primes in a fixed `(e,dminus,dplus)` fiber occupy one reduced residue
class modulo `4*rho(e)`.  Consequently their reciprocal mass is bounded by
the exact Brun--Titchmarsh carrier used by the manuscript. -/
theorem familyPrimeValues_recip_le_btRecip
    (P : Params) (X : ℝ) (Pz b : ℕ)
    (indices : Finset Family.FamilyIndex) (E : ExactDivisor)
    (dminus dplus : ℕ)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i) :
    ∃ a : ℕ, Nat.Coprime a (4 * E.rho) ∧
      (∑ p ∈ familyPrimeValues indices E dminus dplus,
        (1 : ℝ) / (p : ℝ)) ≤
        Inputs.btRecip P X (4 * E.rho) a := by
  classical
  let primes := familyPrimeValues indices E dminus dplus
  by_cases hprimes : primes.Nonempty
  · rcases hprimes with ⟨p0, hp0⟩
    have hp0Data :
        ∃ i ∈ indices, i.E = E ∧ i.dminus = dminus ∧
          i.dplus = dplus ∧ i.p = p0 := by
      rcases Finset.mem_image.mp hp0 with ⟨i, hi, hip⟩
      rcases Finset.mem_filter.mp hi with ⟨hiIndices, hiFiber⟩
      exact ⟨i, hiIndices, hiFiber.1, hiFiber.2.1, hiFiber.2.2, hip⟩
    rcases hp0Data with ⟨i0, hi0, hi0E, hi0Minus, hi0Plus, hi0p⟩
    have hi0mem := hmem i0 hi0
    have hmodPos : 0 < 4 * E.rho := by
      have his : 0 < i0.E.s := lt_of_lt_of_le Nat.zero_lt_one hi0mem.s_pos
      have hs : 0 < E.s := by simpa [hi0E] using his
      have hY0 : 0 ≤ Y0Scale P X := by
        unfold Y0Scale
        exact Real.rpow_nonneg (le_trans zero_le_one hX.le) P.lam
      have hdiv : 0 ≤ Y0Scale P X / (i0.E.s : ℝ) := by positivity
      have hirReal : 0 < (i0.E.r : ℝ) := lt_of_le_of_lt hdiv hi0mem.r_gt
      have hir : 0 < i0.E.r := by exact_mod_cast hirReal
      have hr : 0 < E.r := by simpa [hi0E] using hir
      unfold ExactDivisor.rho
      positivity
    have hcoefCoprime : Nat.Coprime (dminus * dplus) (4 * E.rho) := by
      simpa [hi0E, hi0Minus, hi0Plus, Family.FamilyIndex.rho] using
        hi0mem.dd_coprime_four_rho
    have hp0Sat : (dminus * dplus) * p0 + 1 ≡ 0 [MOD 4 * E.rho] := by
      apply Nat.modEq_zero_iff_dvd.mpr
      simpa [Family.FamilyIndex.Q, Family.FamilyIndex.rho,
        hi0E, hi0Minus, hi0Plus, hi0p, Nat.mul_assoc] using hi0mem.sat_cong
    have hp0CoprimeTotal : Nat.Coprime p0 ((dminus * dplus) * p0 + 1) := by
      rw [show (dminus * dplus) * p0 + 1 = 1 + (dminus * dplus) * p0 by omega]
      simpa using (Nat.coprime_add_mul_right_right p0 1 (dminus * dplus))
    have hp0Coprime : Nat.Coprime p0 (4 * E.rho) :=
      hp0CoprimeTotal.coprime_dvd_right
        (Nat.modEq_zero_iff_dvd.mp hp0Sat)
    refine ⟨p0, hp0Coprime, ?_⟩
    unfold Inputs.btRecip
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rcases Finset.mem_image.mp hp with ⟨i, hi, hip⟩
      rcases Finset.mem_filter.mp hi with ⟨hiIndices, hiFiber⟩
      have himem := hmem i hiIndices
      have hiE := hiFiber.1
      have hiMinus := hiFiber.2.1
      have hiPlus := hiFiber.2.2
      have hpPrime : Nat.Prime p := by simpa [hip] using himem.p_prime
      have hpWindow : p ∈ Inputs.natWindow (X ^ P.β) (X ^ (1 - P.σ)) := by
        unfold Inputs.natWindow
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨hpPrime.one_le, ?_⟩, ?_⟩
        · apply Nat.le_floor
          simpa [hip] using himem.p_le
        · simpa [hip] using himem.p_gt
      have hpSat : (dminus * dplus) * p + 1 ≡ 0 [MOD 4 * E.rho] := by
        apply Nat.modEq_zero_iff_dvd.mpr
        simpa [Family.FamilyIndex.Q, Family.FamilyIndex.rho,
          hiE, hiMinus, hiPlus, hip, Nat.mul_assoc] using himem.sat_cong
      have hmul : (dminus * dplus) * p ≡
          (dminus * dplus) * p0 [MOD 4 * E.rho] :=
        Nat.ModEq.add_right_cancel' 1 (hpSat.trans hp0Sat.symm)
      have hcoefGcd : Nat.gcd (4 * E.rho) (dminus * dplus) = 1 := by
        simpa [Nat.coprime_iff_gcd_eq_one] using hcoefCoprime.symm
      have hpCong : p ≡ p0 [MOD 4 * E.rho] :=
        Nat.ModEq.cancel_left_of_coprime hcoefGcd hmul
      exact Finset.mem_filter.mpr
        ⟨hpWindow, hpPrime, by simpa [Inputs.congMod, Nat.ModEq] using hpCong⟩
    · intro p _hpBig _hpSmall
      positivity
  · refine ⟨1, Nat.coprime_one_left _, ?_⟩
    have hempty : primes = ∅ := Finset.not_nonempty_iff_eq_empty.mp hprimes
    rw [show familyPrimeValues indices E dminus dplus = ∅ from hempty]
    simp [Inputs.btRecip_nonneg]

/-- For the complete static paper family, every nonempty fixed
`(e,dminus,dplus)` prime fiber is exactly one reciprocal-prime progression
carrier.  The reverse inclusion uses completeness of `familyIndexFinset` and
rebuilds the family index after replacing its prime by a prime in the same
residue class. -/
theorem actualPaperFamily_primeValues_recip_eq_btRecip_of_nonempty
    (P : Params) (X : ℝ) (Pz b : ℕ)
    (E : ExactDivisor) (dminus dplus : ℕ)
    (hX : 1 < X)
    (hprimes : (familyPrimeValues
      (Family.familyIndexFinset P X Pz b) E dminus dplus).Nonempty) :
    ∃ a : ℕ, Nat.Coprime a (4 * E.rho) ∧
      (∑ p ∈ familyPrimeValues
          (Family.familyIndexFinset P X Pz b) E dminus dplus,
        (1 : ℝ) / (p : ℝ)) =
        Inputs.btRecip P X (4 * E.rho) a := by
  classical
  let indices := Family.familyIndexFinset P X Pz b
  rcases hprimes with ⟨p0, hp0⟩
  rcases Finset.mem_image.mp hp0 with ⟨i0, hi0, hi0p⟩
  rcases Finset.mem_filter.mp hi0 with ⟨hi0Indices, hi0Fiber⟩
  have hi0mem : Family.FamilyStaticMem P X Pz b i0 :=
    (Family.mem_familyIndexFinset_iff P X Pz b i0
      (lt_trans zero_lt_one hX)).1 hi0Indices
  have hi0E : i0.E = E := hi0Fiber.1
  have hi0Minus : i0.dminus = dminus := hi0Fiber.2.1
  have hi0Plus : i0.dplus = dplus := hi0Fiber.2.2
  subst E
  subst dminus
  subst dplus
  subst p0
  have hmodPos : 0 < 4 * i0.E.rho := by
    have hs : 0 < i0.E.s := lt_of_lt_of_le Nat.zero_lt_one hi0mem.s_pos
    have hr : 0 < i0.E.r := hi0mem.r_pos hX
    unfold ExactDivisor.rho
    positivity
  have hcoefCoprime : Nat.Coprime (i0.dminus * i0.dplus)
      (4 * i0.E.rho) := by
    simpa [Family.FamilyIndex.rho] using hi0mem.dd_coprime_four_rho
  have hp0Sat : (i0.dminus * i0.dplus) * i0.p + 1 ≡
      0 [MOD 4 * i0.E.rho] := by
    apply Nat.modEq_zero_iff_dvd.mpr
    simpa [Family.FamilyIndex.Q, Family.FamilyIndex.rho, Nat.mul_assoc] using
      hi0mem.sat_cong
  have hp0CoprimeTotal : Nat.Coprime i0.p
      ((i0.dminus * i0.dplus) * i0.p + 1) := by
    rw [show (i0.dminus * i0.dplus) * i0.p + 1 =
      1 + (i0.dminus * i0.dplus) * i0.p by omega]
    simpa using
      (Nat.coprime_add_mul_right_right i0.p 1 (i0.dminus * i0.dplus))
  have hp0Coprime : Nat.Coprime i0.p (4 * i0.E.rho) :=
    hp0CoprimeTotal.coprime_dvd_right
      (Nat.modEq_zero_iff_dvd.mp hp0Sat)
  refine ⟨i0.p, hp0Coprime, ?_⟩
  have hsets : familyPrimeValues indices i0.E i0.dminus i0.dplus =
      (Inputs.natWindow (X ^ P.β) (X ^ (1 - P.σ))).filter
        (fun p : ℕ => Nat.Prime p ∧ Inputs.congMod p i0.p
          (4 * i0.E.rho)) := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨i, hi, hip⟩
      rcases Finset.mem_filter.mp hi with ⟨hiIndices, hiFiber⟩
      have himem : Family.FamilyStaticMem P X Pz b i :=
        (Family.mem_familyIndexFinset_iff P X Pz b i
          (lt_trans zero_lt_one hX)).1 hiIndices
      have hiE := hiFiber.1
      have hiMinus := hiFiber.2.1
      have hiPlus := hiFiber.2.2
      have hpPrime : Nat.Prime p := by simpa [hip] using himem.p_prime
      have hpWindow : p ∈ Inputs.natWindow
          (X ^ P.β) (X ^ (1 - P.σ)) := by
        unfold Inputs.natWindow
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨hpPrime.one_le, ?_⟩, ?_⟩
        · apply Nat.le_floor
          simpa [hip] using himem.p_le
        · simpa [hip] using himem.p_gt
      have hpSat : (i0.dminus * i0.dplus) * p + 1 ≡
          0 [MOD 4 * i0.E.rho] := by
        apply Nat.modEq_zero_iff_dvd.mpr
        simpa [Family.FamilyIndex.Q, Family.FamilyIndex.rho,
          hiE, hiMinus, hiPlus, hip, Nat.mul_assoc] using himem.sat_cong
      have hmul : (i0.dminus * i0.dplus) * p ≡
          (i0.dminus * i0.dplus) * i0.p [MOD 4 * i0.E.rho] :=
        Nat.ModEq.add_right_cancel' 1 (hpSat.trans hp0Sat.symm)
      have hcoefGcd : Nat.gcd (4 * i0.E.rho)
          (i0.dminus * i0.dplus) = 1 := by
        simpa [Nat.coprime_iff_gcd_eq_one] using hcoefCoprime.symm
      have hpCong : p ≡ i0.p [MOD 4 * i0.E.rho] :=
        Nat.ModEq.cancel_left_of_coprime hcoefGcd hmul
      exact Finset.mem_filter.mpr
        ⟨hpWindow, hpPrime,
          by simpa [Inputs.congMod, Nat.ModEq] using hpCong⟩
    · intro hp
      have hpData := Finset.mem_filter.mp hp
      have hpWindow := hpData.1
      have hpPrime := hpData.2.1
      have hpCong : p ≡ i0.p [MOD 4 * i0.E.rho] := by
        simpa [Inputs.congMod, Nat.ModEq] using hpData.2.2
      have hpWindowData := Finset.mem_filter.mp hpWindow
      have hpIcc := Finset.mem_Icc.mp hpWindowData.1
      have hUpperNonneg : 0 ≤ X ^ (1 - P.σ) :=
        Real.rpow_nonneg (le_trans zero_le_one hX.le) _
      have hpLe : (p : ℝ) ≤ X ^ (1 - P.σ) :=
        le_trans (by exact_mod_cast hpIcc.2) (Nat.floor_le hUpperNonneg)
      have hpSat : (i0.dminus * i0.dplus) * p + 1 ≡
          0 [MOD 4 * i0.E.rho] := by
        have hmul := hpCong.mul_left (i0.dminus * i0.dplus)
        have hadd := hmul.add_right 1
        exact hadd.trans hp0Sat
      let j : Family.FamilyIndex :=
        { E := i0.E
          dminus := i0.dminus
          dplus := i0.dplus
          p := p }
      have hjmem : Family.FamilyStaticMem P X Pz b j := by
        refine
          { s_pos := ?_, s_le_S := ?_, r_gt := ?_, r_le := ?_,
            dminus_pos := ?_, dminus_le_U := ?_, dminus_dvd_Pz := ?_,
            dminus_squarefree := ?_, dminus_odd := ?_, base_cong := ?_,
            dplus_pos := ?_, dplus_squarefree := ?_, dd_le_Y := ?_,
            dplus_coprime_Pz := ?_, dd_coprime_four_rho := ?_,
            p_prime := hpPrime, p_gt := hpWindowData.2, p_le := hpLe,
            sat_cong := ?_ }
        all_goals try simpa [j] using hi0mem.s_pos
        all_goals try simpa [j] using hi0mem.s_le_S
        all_goals try simpa [j] using hi0mem.r_gt
        all_goals try simpa [j] using hi0mem.r_le
        all_goals try simpa [j] using hi0mem.dminus_pos
        all_goals try simpa [j] using hi0mem.dminus_le_U
        all_goals try simpa [j] using hi0mem.dminus_dvd_Pz
        all_goals try simpa [j] using hi0mem.dminus_squarefree
        all_goals try simpa [j] using hi0mem.dminus_odd
        all_goals try simpa [j] using hi0mem.base_cong
        all_goals try simpa [j] using hi0mem.dplus_pos
        all_goals try simpa [j] using hi0mem.dplus_squarefree
        all_goals try simpa [j] using hi0mem.dd_le_Y
        all_goals try simpa [j] using hi0mem.dplus_coprime_Pz
        all_goals try simpa [j, Family.FamilyIndex.rho] using
          hi0mem.dd_coprime_four_rho
        simpa [j, Family.FamilyIndex.Q, Family.FamilyIndex.rho,
          Nat.mul_assoc] using (Nat.modEq_zero_iff_dvd.mp hpSat)
      have hjIndices : j ∈ indices :=
        (Family.mem_familyIndexFinset_iff P X Pz b j
          (lt_trans zero_lt_one hX)).2 hjmem
      unfold familyPrimeValues
      apply Finset.mem_image.mpr
      refine ⟨j, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨hjIndices, by simp [j]⟩
  unfold Inputs.btRecip
  rw [hsets]

/-- Every prime fiber represented in the complete family is nonempty, so the
exact progression identity applies on each `dplus` coordinate occurring in
the family-mass expansion. -/
theorem actualPaperFamily_primeValues_recip_eq_btRecip
    (P : Params) (X : ℝ) (Pz b : ℕ)
    (E : ExactDivisor) (dminus dplus : ℕ)
    (hX : 1 < X)
    (hdplus : dplus ∈ familyDplusValues
      (Family.familyIndexFinset P X Pz b) E dminus) :
    ∃ a : ℕ, Nat.Coprime a (4 * E.rho) ∧
      (∑ p ∈ familyPrimeValues
          (Family.familyIndexFinset P X Pz b) E dminus dplus,
        (1 : ℝ) / (p : ℝ)) =
        Inputs.btRecip P X (4 * E.rho) a := by
  rcases Finset.mem_image.mp hdplus with ⟨i, hi, rfl⟩
  have hiData := Finset.mem_filter.mp hi
  have hpMem : i.p ∈ familyPrimeValues
      (Family.familyIndexFinset P X Pz b) E dminus i.dplus := by
    unfold familyPrimeValues
    apply Finset.mem_image.mpr
    exact ⟨i, Finset.mem_filter.mpr
      ⟨hiData.1, hiData.2.1, hiData.2.2, rfl⟩, rfl⟩
  exact actualPaperFamily_primeValues_recip_eq_btRecip_of_nonempty
    P X Pz b E dminus i.dplus hX ⟨i.p, hpMem⟩

/-- Canonical reduced prime residue attached to each represented complete-family
fiber.  Outside the represented support the harmless default is `1`. -/
noncomputable def actualPaperFamilyPrimeResidueSelector
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 1 < X)
    (E : ExactDivisor) (dminus dplus : ℕ) : ℕ := by
  classical
  exact if h : dplus ∈ familyDplusValues
      (Family.familyIndexFinset P X Pz b) E dminus then
    Classical.choose
      (actualPaperFamily_primeValues_recip_eq_btRecip
        P X Pz b E dminus dplus hX h)
  else 1

theorem actualPaperFamilyPrimeResidueSelector_coprime
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 1 < X)
    (E : ExactDivisor) (dminus dplus : ℕ)
    (hdplus : dplus ∈ familyDplusValues
      (Family.familyIndexFinset P X Pz b) E dminus) :
    Nat.Coprime
      (actualPaperFamilyPrimeResidueSelector
        P X Pz b hX E dminus dplus)
      (4 * E.rho) := by
  classical
  unfold actualPaperFamilyPrimeResidueSelector
  rw [dif_pos hdplus]
  exact (Classical.choose_spec
    (actualPaperFamily_primeValues_recip_eq_btRecip
      P X Pz b E dminus dplus hX hdplus)).1

theorem actualPaperFamily_primeValues_recip_eq_selector_btRecip
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 1 < X)
    (E : ExactDivisor) (dminus dplus : ℕ)
    (hdplus : dplus ∈ familyDplusValues
      (Family.familyIndexFinset P X Pz b) E dminus) :
    (∑ p ∈ familyPrimeValues
        (Family.familyIndexFinset P X Pz b) E dminus dplus,
      (1 : ℝ) / (p : ℝ)) =
      Inputs.btRecip P X (4 * E.rho)
        (actualPaperFamilyPrimeResidueSelector
          P X Pz b hX E dminus dplus) := by
  classical
  unfold actualPaperFamilyPrimeResidueSelector
  rw [dif_pos hdplus]
  exact (Classical.choose_spec
    (actualPaperFamily_primeValues_recip_eq_btRecip
      P X Pz b E dminus dplus hX hdplus)).2

/-- The complete finite paper mass is exactly a finite weighted sum of the
same reciprocal-prime progression carriers used by weighted BV. -/
theorem actualPaperFamily_indexMassRat_real_eq_btFibers
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 1 < X) :
    (Family.familyIndexMassRat
      (Family.familyIndexFinset P X Pz b) : ℝ) =
      ∑ E ∈ familyExactValues (Family.familyIndexFinset P X Pz b),
        ∑ dminus ∈ familyDminusValues
            (Family.familyIndexFinset P X Pz b) E,
          ∑ dplus ∈ familyDplusValues
              (Family.familyIndexFinset P X Pz b) E dminus,
            ((1 : ℝ) / (dplus : ℝ)) *
              Inputs.btRecip P X (4 * E.rho)
                (actualPaperFamilyPrimeResidueSelector
                  P X Pz b hX E dminus dplus) := by
  have hmem : ∀ i ∈ Family.familyIndexFinset P X Pz b,
      Family.FamilyStaticMem P X Pz b i := by
    intro i hi
    exact (Family.mem_familyIndexFinset_iff P X Pz b i
      (lt_trans zero_lt_one hX)).1 hi
  rw [familyIndexMassRat_real_eq_primeFibers
    P X Pz b (Family.familyIndexFinset P X Pz b) hX hmem]
  apply Finset.sum_congr rfl
  intro E hE
  apply Finset.sum_congr rfl
  intro dminus hdminus
  apply Finset.sum_congr rfl
  intro dplus hdplus
  rw [actualPaperFamily_primeValues_recip_eq_selector_btRecip
    P X Pz b hX E dminus dplus hdplus]

/-- The reciprocal-prime main term over the exact support of the complete
family. -/
noncomputable def actualPaperFamilyMassMainCarrier
    (P : Params) (X : ℝ) (Pz b : ℕ) : ℝ :=
  ∑ E ∈ familyExactValues (Family.familyIndexFinset P X Pz b),
    ∑ dminus ∈ familyDminusValues
        (Family.familyIndexFinset P X Pz b) E,
      ∑ dplus ∈ familyDplusValues
          (Family.familyIndexFinset P X Pz b) E dminus,
        ((1 : ℝ) / (dplus : ℝ)) *
          ((1 / (Nat.totient (4 * E.rho) : ℝ)) *
            Inputs.btRecip P X 1 0)

/-- The weighted reciprocal-prime progression error over the same complete
family support. -/
noncomputable def actualPaperFamilyMassErrorCarrier
    (P : Params) (X : ℝ) (Pz b : ℕ) : ℝ :=
  ∑ E ∈ familyExactValues (Family.familyIndexFinset P X Pz b),
    ∑ dminus ∈ familyDminusValues
        (Family.familyIndexFinset P X Pz b) E,
      ∑ dplus ∈ familyDplusValues
          (Family.familyIndexFinset P X Pz b) E dminus,
        ((1 : ℝ) / (dplus : ℝ)) *
          Inputs.reducedClassPrimeErrorMax P X (4 * E.rho)

/-- Moduli `4*rho(e)` represented by the complete family. -/
noncomputable def actualPaperFamilyMassModuli
    (P : Params) (X : ℝ) (Pz b : ℕ) : Finset ℕ :=
  (familyExactValues (Family.familyIndexFinset P X Pz b)).image
    (fun E => 4 * E.rho)

/-- Total `dminus,dplus` reciprocal coefficient carried by one represented
prime modulus. -/
noncomputable def actualPaperFamilyMassErrorCoefficient
    (P : Params) (X : ℝ) (Pz b m : ℕ) : ℝ :=
  ∑ E ∈ (familyExactValues
      (Family.familyIndexFinset P X Pz b)).filter (fun E => 4 * E.rho = m),
    ∑ dminus ∈ familyDminusValues
        (Family.familyIndexFinset P X Pz b) E,
      ∑ dplus ∈ familyDplusValues
          (Family.familyIndexFinset P X Pz b) E dminus,
        (1 : ℝ) / (dplus : ℝ)

/-- For one exact-divisor coordinate, the total coefficient from its
`dminus,dplus` fibers is bounded by the number of possible small cofactors
times the full harmonic sum at the large-cofactor cutoff. -/
theorem actualPaperFamily_exactDivisorErrorCoefficient_le
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 0 < X)
    (E : ExactDivisor) :
    (∑ dminus ∈ familyDminusValues
        (Family.familyIndexFinset P X Pz b) E,
      ∑ dplus ∈ familyDplusValues
          (Family.familyIndexFinset P X Pz b) E dminus,
        (1 : ℝ) / (dplus : ℝ)) ≤
      (⌊UScale X⌋₊ : ℝ) * (harmonic ⌊YScale P X⌋₊ : ℝ) := by
  have hsum :
      (∑ dminus ∈ familyDminusValues
          (Family.familyIndexFinset P X Pz b) E,
        ∑ dplus ∈ familyDplusValues
            (Family.familyIndexFinset P X Pz b) E dminus,
          (1 : ℝ) / (dplus : ℝ)) ≤
        ∑ _dminus ∈ familyDminusValues
            (Family.familyIndexFinset P X Pz b) E,
          (harmonic ⌊YScale P X⌋₊ : ℝ) := by
    apply Finset.sum_le_sum
    intro dminus _hdminus
    exact actualPaperFamily_familyDplusValues_recip_le_harmonic
      P X Pz b hX E dminus
  calc
    (∑ dminus ∈ familyDminusValues
        (Family.familyIndexFinset P X Pz b) E,
      ∑ dplus ∈ familyDplusValues
          (Family.familyIndexFinset P X Pz b) E dminus,
        (1 : ℝ) / (dplus : ℝ))
        ≤ ∑ _dminus ∈ familyDminusValues
            (Family.familyIndexFinset P X Pz b) E,
          (harmonic ⌊YScale P X⌋₊ : ℝ) := hsum
    _ = ((familyDminusValues
          (Family.familyIndexFinset P X Pz b) E).card : ℝ) *
          (harmonic ⌊YScale P X⌋₊ : ℝ) := by simp
    _ ≤ (⌊UScale X⌋₊ : ℝ) * (harmonic ⌊YScale P X⌋₊ : ℝ) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast actualPaperFamily_familyDminusValues_card_le
          P X Pz b hX E
      · exact Inputs.harmonic_nonneg_real ⌊YScale P X⌋₊

/-- At a fixed represented modulus `m = 4*rho`, exact-divisor coordinates
inject into the divisors of `m` through their `s` coordinate. -/
theorem actualPaperFamily_exactDivisorsAtModulus_card_le_tau
    (P : Params) (X : ℝ) (Pz b m : ℕ) (hX : 1 < X) :
    ((familyExactValues (Family.familyIndexFinset P X Pz b)).filter
      (fun E => 4 * E.rho = m)).card ≤ Inputs.tau m := by
  classical
  let S := (familyExactValues (Family.familyIndexFinset P X Pz b)).filter
    (fun E => 4 * E.rho = m)
  have hSdata : ∀ E ∈ S,
      0 < E.s ∧ 0 < E.rho ∧ 4 * E.rho = m := by
    intro E hE
    have hEf := Finset.mem_filter.mp hE
    rcases Finset.mem_image.mp hEf.1 with ⟨i, hi, hiE⟩
    have himem : Family.FamilyStaticMem P X Pz b i :=
      (Family.mem_familyIndexFinset_iff P X Pz b i
        (lt_trans zero_lt_one hX)).1 hi
    subst E
    have hs : 0 < i.E.s := lt_of_lt_of_le Nat.zero_lt_one himem.s_pos
    have hr : 0 < i.E.r := himem.r_pos hX
    exact ⟨hs, ExactDivisor.rho_pos i.E hr hs, hEf.2⟩
  have hcard : S.card ≤ m.divisors.card := by
    apply Finset.card_le_card_of_injOn (fun E : ExactDivisor => E.s)
    · intro E hE
      have hdata := hSdata E hE
      apply Nat.mem_divisors.mpr
      refine ⟨?_, by omega⟩
      have hsRho : E.s ∣ E.rho := by
        unfold ExactDivisor.rho
        exact dvd_mul_left E.s E.r
      exact hsRho.trans (by
        rw [← hdata.2.2]
        exact dvd_mul_left E.rho 4)
    · intro E hE F hF hs
      change E.s = F.s at hs
      have hEdata := hSdata E hE
      have hFdata := hSdata F hF
      have hrho : E.rho = F.rho := by omega
      have hrMul : E.r * E.s = F.r * E.s := by
        calc
          E.r * E.s = E.rho := rfl
          _ = F.rho := hrho
          _ = F.r * F.s := rfl
          _ = F.r * E.s := by rw [← hs]
      have hr : E.r = F.r :=
        Nat.eq_of_mul_eq_mul_right hEdata.1 hrMul
      cases E
      cases F
      simp_all
  simpa [S, Inputs.tau] using hcard

/-- The exact coefficient at one represented prime modulus has precisely the
divisor weight required by weighted BV, up to the two explicit elementary
cutoff factors. -/
theorem actualPaperFamilyMassErrorCoefficient_le_tau_mul_cutoffs
    (P : Params) (X : ℝ) (Pz b m : ℕ) (hX : 1 < X) :
    actualPaperFamilyMassErrorCoefficient P X Pz b m ≤
      (Inputs.tau m : ℝ) *
        ((⌊UScale X⌋₊ : ℝ) * (harmonic ⌊YScale P X⌋₊ : ℝ)) := by
  let S := (familyExactValues (Family.familyIndexFinset P X Pz b)).filter
    (fun E => 4 * E.rho = m)
  let A : ℝ := (⌊UScale X⌋₊ : ℝ) * (harmonic ⌊YScale P X⌋₊ : ℝ)
  have hsum : actualPaperFamilyMassErrorCoefficient P X Pz b m ≤
      ∑ _E ∈ S, A := by
    unfold actualPaperFamilyMassErrorCoefficient
    change (∑ E ∈ S,
      ∑ dminus ∈ familyDminusValues
          (Family.familyIndexFinset P X Pz b) E,
        ∑ dplus ∈ familyDplusValues
            (Family.familyIndexFinset P X Pz b) E dminus,
          (1 : ℝ) / (dplus : ℝ)) ≤ _
    apply Finset.sum_le_sum
    intro E _hE
    exact actualPaperFamily_exactDivisorErrorCoefficient_le
      P X Pz b (lt_trans zero_lt_one hX) E
  have hA : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _)
    (Inputs.harmonic_nonneg_real _)
  calc
    actualPaperFamilyMassErrorCoefficient P X Pz b m
        ≤ ∑ _E ∈ S, A := hsum
    _ = (S.card : ℝ) * A := by simp
    _ ≤ (Inputs.tau m : ℝ) * A := by
      apply mul_le_mul_of_nonneg_right _ hA
      exact_mod_cast actualPaperFamily_exactDivisorsAtModulus_card_le_tau
        P X Pz b m hX
    _ = (Inputs.tau m : ℝ) *
        ((⌊UScale X⌋₊ : ℝ) * (harmonic ⌊YScale P X⌋₊ : ℝ)) := rfl

/-- Exact regrouping of the complete-family reciprocal-prime error by its
weighted-BV modulus. -/
theorem actualPaperFamilyMassErrorCarrier_eq_modulus_sum
    (P : Params) (X : ℝ) (Pz b : ℕ) :
    actualPaperFamilyMassErrorCarrier P X Pz b =
      ∑ m ∈ actualPaperFamilyMassModuli P X Pz b,
        actualPaperFamilyMassErrorCoefficient P X Pz b m *
          Inputs.reducedClassPrimeErrorMax P X m := by
  classical
  let Eset := familyExactValues (Family.familyIndexFinset P X Pz b)
  let Mset := actualPaperFamilyMassModuli P X Pz b
  have hmaps : ∀ E ∈ Eset, 4 * E.rho ∈ Mset := by
    intro E hE
    unfold Mset actualPaperFamilyMassModuli
    exact Finset.mem_image.mpr ⟨E, hE, rfl⟩
  have hpartition := Finset.sum_fiberwise_of_maps_to hmaps
    (fun E : ExactDivisor =>
      ∑ dminus ∈ familyDminusValues
          (Family.familyIndexFinset P X Pz b) E,
        ∑ dplus ∈ familyDplusValues
            (Family.familyIndexFinset P X Pz b) E dminus,
          ((1 : ℝ) / (dplus : ℝ)) *
            Inputs.reducedClassPrimeErrorMax P X (4 * E.rho))
  unfold actualPaperFamilyMassErrorCarrier
  change (∑ E ∈ Eset,
      ∑ dminus ∈ familyDminusValues
          (Family.familyIndexFinset P X Pz b) E,
        ∑ dplus ∈ familyDplusValues
            (Family.familyIndexFinset P X Pz b) E dminus,
          ((1 : ℝ) / (dplus : ℝ)) *
            Inputs.reducedClassPrimeErrorMax P X (4 * E.rho)) = _
  rw [← hpartition]
  apply Finset.sum_congr rfl
  intro m hm
  unfold actualPaperFamilyMassErrorCoefficient
  change (∑ E ∈ Eset.filter (fun E => 4 * E.rho = m),
      ∑ dminus ∈ familyDminusValues
          (Family.familyIndexFinset P X Pz b) E,
        ∑ dplus ∈ familyDplusValues
            (Family.familyIndexFinset P X Pz b) E dminus,
          ((1 : ℝ) / (dplus : ℝ)) *
            Inputs.reducedClassPrimeErrorMax P X (4 * E.rho)) = _
  calc
    (∑ E ∈ Eset.filter (fun E => 4 * E.rho = m),
        ∑ dminus ∈ familyDminusValues
            (Family.familyIndexFinset P X Pz b) E,
          ∑ dplus ∈ familyDplusValues
              (Family.familyIndexFinset P X Pz b) E dminus,
            ((1 : ℝ) / (dplus : ℝ)) *
              Inputs.reducedClassPrimeErrorMax P X (4 * E.rho)) =
      ∑ E ∈ Eset.filter (fun E => 4 * E.rho = m),
        (∑ dminus ∈ familyDminusValues
            (Family.familyIndexFinset P X Pz b) E,
          ∑ dplus ∈ familyDplusValues
              (Family.familyIndexFinset P X Pz b) E dminus,
            (1 : ℝ) / (dplus : ℝ)) *
          Inputs.reducedClassPrimeErrorMax P X m := by
      apply Finset.sum_congr rfl
      intro E hE
      have hEm : 4 * E.rho = m := (Finset.mem_filter.mp hE).2
      rw [hEm]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro dminus hdminus
      rw [Finset.sum_mul]
    _ = (∑ E ∈ Eset.filter (fun E => 4 * E.rho = m),
        ∑ dminus ∈ familyDminusValues
            (Family.familyIndexFinset P X Pz b) E,
          ∑ dplus ∈ familyDplusValues
              (Family.familyIndexFinset P X Pz b) E dminus,
            (1 : ℝ) / (dplus : ℝ)) *
          Inputs.reducedClassPrimeErrorMax P X m := by
      rw [Finset.sum_mul]
    _ = actualPaperFamilyMassErrorCoefficient P X Pz b m *
        Inputs.reducedClassPrimeErrorMax P X m := by
      rfl

/-- Fiberwise reciprocal-prime lower bound: main term minus the exact
same-carrier progression error is no larger than the represented prime fiber. -/
theorem actualPaperFamily_primeMain_sub_error_le_recip
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 1 < X)
    (E : ExactDivisor) (dminus dplus : ℕ)
    (hdplus : dplus ∈ familyDplusValues
      (Family.familyIndexFinset P X Pz b) E dminus) :
    (1 / (Nat.totient (4 * E.rho) : ℝ)) * Inputs.btRecip P X 1 0 -
        Inputs.reducedClassPrimeErrorMax P X (4 * E.rho) ≤
      ∑ p ∈ familyPrimeValues
          (Family.familyIndexFinset P X Pz b) E dminus dplus,
        (1 : ℝ) / (p : ℝ) := by
  rcases Finset.mem_image.mp hdplus with ⟨i, hi, hidplus⟩
  have hiData := Finset.mem_filter.mp hi
  have hiIndices : i ∈ Family.familyIndexFinset P X Pz b := hiData.1
  have himem : Family.FamilyStaticMem P X Pz b i :=
    (Family.mem_familyIndexFinset_iff P X Pz b i
      (lt_trans zero_lt_one hX)).1 hiIndices
  have hiE : i.E = E := hiData.2.1
  have hmodPos : 0 < 4 * E.rho := by
    have hs : 0 < i.E.s := lt_of_lt_of_le Nat.zero_lt_one himem.s_pos
    have hr : 0 < i.E.r := himem.r_pos hX
    have hρ : 0 < i.E.rho := by
      unfold ExactDivisor.rho
      positivity
    simpa [hiE] using Nat.mul_pos (by norm_num : 0 < 4) hρ
  have hcop := actualPaperFamilyPrimeResidueSelector_coprime
    P X Pz b hX E dminus dplus hdplus
  have herror := Inputs.reducedClassPrimeError_le_max_of_coprime
    (P := P) (X := X) hmodPos hcop
  have hprime := actualPaperFamily_primeValues_recip_eq_selector_btRecip
    P X Pz b hX E dminus dplus hdplus
  have hneg :
      -Inputs.reducedClassPrimeErrorMax P X (4 * E.rho) ≤
        Inputs.btRecip P X (4 * E.rho)
            (actualPaperFamilyPrimeResidueSelector
              P X Pz b hX E dminus dplus) -
          (1 / (Nat.totient (4 * E.rho) : ℝ)) *
            Inputs.btRecip P X 1 0 :=
    (neg_le_neg herror).trans (neg_abs_le _)
  rw [hprime]
  linarith

/-- The complete family mass dominates its reciprocal-prime main carrier minus
the exact weighted progression-error carrier.  No analytic estimate is used in
this finite comparison. -/
theorem actualPaperFamily_massMain_sub_error_le_indexMass
    (P : Params) (X : ℝ) (Pz b : ℕ) (hX : 1 < X) :
    actualPaperFamilyMassMainCarrier P X Pz b -
        actualPaperFamilyMassErrorCarrier P X Pz b ≤
      (Family.familyIndexMassRat
        (Family.familyIndexFinset P X Pz b) : ℝ) := by
  rw [actualPaperFamily_indexMassRat_real_eq_btFibers P X Pz b hX]
  unfold actualPaperFamilyMassMainCarrier
    actualPaperFamilyMassErrorCarrier
  simp_rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro E hE
  apply Finset.sum_le_sum
  intro dminus hdminus
  apply Finset.sum_le_sum
  intro dplus hdplus
  calc
    ((1 : ℝ) / (dplus : ℝ)) *
          ((1 / (Nat.totient (4 * E.rho) : ℝ)) *
            Inputs.btRecip P X 1 0) -
        ((1 : ℝ) / (dplus : ℝ)) *
          Inputs.reducedClassPrimeErrorMax P X (4 * E.rho) =
      ((1 : ℝ) / (dplus : ℝ)) *
        ((1 / (Nat.totient (4 * E.rho) : ℝ)) *
            Inputs.btRecip P X 1 0 -
          Inputs.reducedClassPrimeErrorMax P X (4 * E.rho)) := by ring
    _ ≤ ((1 : ℝ) / (dplus : ℝ)) *
        (∑ p ∈ familyPrimeValues
            (Family.familyIndexFinset P X Pz b) E dminus dplus,
          (1 : ℝ) / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (actualPaperFamily_primeMain_sub_error_le_recip
          P X Pz b hX E dminus dplus hdplus) (by positivity)
    _ = ((1 : ℝ) / (dplus : ℝ)) *
        Inputs.btRecip P X (4 * E.rho)
          (actualPaperFamilyPrimeResidueSelector
            P X Pz b hX E dminus dplus) := by
      rw [actualPaperFamily_primeValues_recip_eq_selector_btRecip
        P X Pz b hX E dminus dplus hdplus]

/-- Brun--Titchmarsh applied to an actual fixed family fiber.  The residue
class and its reducedness are discharged by
`familyPrimeValues_recip_le_btRecip`; only the standard theorem's modulus
range remains visible. -/
theorem familyPrimeValues_recip_le_const_div_totient
    (P : Params) (ν : ℝ) (hνpos : 0 < ν) (hνβ : ν < P.β) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X →
      ∀ Pz b : ℕ, ∀ indices : Finset Family.FamilyIndex,
      ∀ E : ExactDivisor, ∀ dminus dplus : ℕ,
      1 ≤ 4 * E.rho → (4 * E.rho : ℝ) ≤ X ^ ν →
      (∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i) →
      (∑ p ∈ familyPrimeValues indices E dminus dplus,
        (1 : ℝ) / (p : ℝ)) ≤ C / (Nat.totient (4 * E.rho) : ℝ) := by
  rcases Inputs.brun_titchmarsh_reciprocal_bound P ν hνpos hνβ with
    ⟨C, X₀, hC, hBT⟩
  refine ⟨C, X₀, hC, ?_⟩
  intro X hX₀ hX Pz b indices E dminus dplus hmodOne hmodRange hmem
  rcases familyPrimeValues_recip_le_btRecip
      P X Pz b indices E dminus dplus hX hmem with
    ⟨a, haCoprime, hfiber⟩
  have hmodRange' : ((4 * E.rho : ℕ) : ℝ) ≤ X ^ ν := by
    simpa [Nat.cast_mul] using hmodRange
  exact hfiber.trans
    (hBT X hX₀ (4 * E.rho) a hmodOne hmodRange' haCoprime)

/-- Actual fixed-fiber propagation with the cited Brun--Titchmarsh input
instantiated.  The only quantitative side condition left at this layer is
the manuscript modulus range `4*rho(e) <= X^nu`. -/
theorem familyFixedEDminusDivisorMass_le_bt_standard_mul_roughInitial
    (P : Params) (ν : ℝ) (hνpos : 0 < ν) (hνβ : ν < P.β) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X →
      ∀ b : ℕ, ∀ indices : Finset Family.FamilyIndex,
      ∀ E : ExactDivisor, ∀ dminus D c : ℕ,
      0 < D → 0 < E.rho → (4 * E.rho : ℝ) ≤ X ^ ν →
      (∀ i ∈ indices,
        Family.FamilyStaticMem P X (Inputs.roughModulus X) b i) →
      familyFixedEDminusDivisorMass
          (indices.filter (fun i => i.e % D = c)) E dminus D ≤
        (C / (Nat.totient (4 * E.rho) : ℝ)) *
          (1 / (D : ℝ)) * Inputs.roughInitial X (4 * E.rho) P.σ := by
  rcases familyPrimeValues_recip_le_const_div_totient P ν hνpos hνβ with
    ⟨C, X₀, hC, hprime⟩
  refine ⟨C, X₀, hC, ?_⟩
  intro X hX₀ hX b indices E dminus D c hD hρ hmodRange hmem
  let I := indices.filter (fun i => i.e % D = c)
  have hmemI : ∀ i ∈ I,
      Family.FamilyStaticMem P X (Inputs.roughModulus X) b i := by
    intro i hi
    exact hmem i (Finset.mem_filter.mp hi).1
  have hPrime : ∀ dplus ∈ familyDplusValues I E dminus,
      (∑ p ∈ familyPrimeValues I E dminus dplus,
        (1 : ℝ) / (p : ℝ)) ≤
          C / (Nat.totient (4 * E.rho) : ℝ) := by
    intro dplus hdplus
    exact hprime X hX₀ hX (Inputs.roughModulus X) b I E dminus dplus
      (by omega) hmodRange hmemI
  exact familyFixedEDminusDivisorMass_le_bt_mul_roughInitial
    P X b indices E dminus D c C hX hmem hD hC.le hρ hPrime

/-- Fully composed bound for one actual residue `dminus` fiber.  This combines
the cited Brun--Titchmarsh theorem, the sharp initial rough-sum estimate, and
the cited ordinary-squarefree exact-divisor tensor. -/
theorem familyFixedDminusResidueMass_le_standard_tensor
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ K X₀ : ℝ, 0 < K ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X →
      ∀ b : ℕ, Nat.Coprime b (Inputs.roughModulus X) →
      ∀ indices : Finset Family.FamilyIndex,
      (∀ i ∈ indices,
        Family.FamilyStaticMem P X (Inputs.roughModulus X) b i) →
      ∀ D c dminus : ℕ,
      1 ≤ D → Squarefree D → Odd D →
      Nat.Coprime D (Inputs.roughModulus X) →
      (D : ℝ) ≤ YScale P X →
      0 < dminus → (dminus : ℝ) ≤ UScale X →
      dminus ∣ Inputs.roughModulus X → Squarefree dminus → Odd dminus →
      (∑ E ∈ familyExactValuesAtDminus indices D c dminus,
        familyFixedEDminusDivisorMass
          (indices.filter (fun i => i.e % D = c)) E dminus D) ≤
        K * (Real.log X / Real.log (zScale X)) *
          exactDivisorMPhiMassRaw P X *
          ((1 : ℝ) / (D : ℝ) ^ 2) * ((1 : ℝ) / (dminus : ℝ)) := by
  rcases familyFixedEDminusDivisorMass_le_bt_standard_mul_roughInitial
      P (P.β / 2) (by linarith [P.β_pos]) (by linarith [P.β_pos]) with
    ⟨Cbt, Xbt, hCbt, hbt⟩
  rcases Inputs.roughInitial_two_sided_from_rough_sqf_and_selberg
      P P.σ (P.β / 2) 4 P.σ_pos (by norm_num) with
    ⟨_cr, Cr, Xr, _hcr, hCr, hrough⟩
  rcases familyExactValuesAtDminus_recipTotient_le_standard_tensor P with
    ⟨Kt, Xt, hKt, htensor⟩
  rcases familyExactValuesAtDminus_modulus_range_eventually P with
    ⟨Xmod, hmod⟩
  refine ⟨Cbt * Cr * Kt, max (max (max (max Xbt Xr) Xt) Xmod) (Real.exp 2),
    mul_pos (mul_pos hCbt hCr) hKt, ?_⟩
  intro X hX hXgt b hbcop indices hmem D c dminus hDone hDsqf hDodd
    hDcop hDleY hdmpos hdmleU hdmdiv hdmsqf hdmodd
  have hXbase : max (max (max Xbt Xr) Xt) Xmod ≤ X :=
    le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 2 ≤ X := le_trans (le_max_right _ _) hX
  have hXbt : Xbt ≤ X := le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hXbase))
  have hXr : Xr ≤ X := le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hXbase))
  have hXt : Xt ≤ X := le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) hXbase)
  have hXmod : Xmod ≤ X := le_trans (le_max_right _ _) hXbase
  have hmodE : ∀ E ∈ familyExactValuesAtDminus indices D c dminus,
      (4 * E.rho : ℝ) ≤ X ^ (P.β / 2) :=
    hmod X hXmod hXgt (Inputs.roughModulus X) b indices hmem D c dminus
  have hρpos : ∀ E ∈ familyExactValuesAtDminus indices D c dminus,
      0 < E.rho := by
    intro E hE
    unfold familyExactValuesAtDminus familyExactValues at hE
    rcases Finset.mem_image.mp hE with ⟨i, hi, rfl⟩
    have himem := hmem i (Finset.mem_filter.mp hi).1
    exact ExactDivisor.rho_pos i.E (himem.r_pos hXgt)
      (lt_of_lt_of_le Nat.zero_lt_one himem.s_pos)
  have hroughUpper : ∀ E ∈ familyExactValuesAtDminus indices D c dminus,
      Inputs.roughInitial X (4 * E.rho) P.σ ≤
        Cr * (Real.log X / Real.log (zScale X)) := by
    intro E hE
    rcases hrough X hXr (4 * E.rho)
        (by simpa [Nat.cast_mul] using hmodE E hE) with
      ⟨_hlogX, _hlogz, _hratio, _hnonneg, _hlower, hupper, _habs⟩
    exact hupper
  have hfixed := familyFixedDminusResidueMass_le_bt
    P X indices D c dminus (by omega) Cbt
      (Cr * (Real.log X / Real.log (zScale X))) hCbt.le
      (mul_nonneg hCr.le (div_nonneg
        (Real.log_nonneg hXgt.le)
        (Inputs.log_zScale_pos_of_exp_two_le hXexp).le))
      hρpos
      (fun E hE => hbt X hXbt hXgt b indices E dminus D c
        (by omega) (hρpos E hE) (hmodE E hE) hmem)
      hroughUpper
  have ht := htensor X hXt hXgt (Inputs.roughModulus X) b hbcop indices
    hmem D c dminus hDone hDsqf hDodd hDcop hDleY hdmpos hdmleU
    hdmdiv hdmsqf hdmodd
  have hratio : 0 ≤ Real.log X / Real.log (zScale X) :=
    div_nonneg (Real.log_nonneg hXgt.le)
      (Inputs.log_zScale_pos_of_exp_two_le hXexp).le
  have hcoef : 0 ≤ Cbt * (Cr * (Real.log X / Real.log (zScale X))) *
      (1 / (D : ℝ)) := by
    exact mul_nonneg (mul_nonneg hCbt.le (mul_nonneg hCr.le hratio)) (by positivity)
  calc
    (∑ E ∈ familyExactValuesAtDminus indices D c dminus,
        familyFixedEDminusDivisorMass
          (indices.filter (fun i => i.e % D = c)) E dminus D) ≤
      Cbt * (Cr * (Real.log X / Real.log (zScale X))) *
        (1 / (D : ℝ)) *
          (∑ E ∈ familyExactValuesAtDminus indices D c dminus,
            (1 : ℝ) / (Nat.totient E.rho : ℝ)) := hfixed
    _ ≤ Cbt * (Cr * (Real.log X / Real.log (zScale X))) *
        (1 / (D : ℝ)) *
          (Kt * (exactDivisorMPhiMassRaw P X /
            ((D * dminus : ℕ) : ℝ))) := by
      exact mul_le_mul_of_nonneg_left ht hcoef
    _ = (Cbt * Cr * Kt) * (Real.log X / Real.log (zScale X)) *
          exactDivisorMPhiMassRaw P X *
          ((1 : ℝ) / (D : ℝ) ^ 2) * ((1 : ℝ) / (dminus : ℝ)) := by
      field_simp [show (D : ℝ) ≠ 0 by exact_mod_cast (by omega : D ≠ 0),
        show (dminus : ℝ) ≠ 0 by exact_mod_cast (by omega : dminus ≠ 0)]
      ring

/-- The modulus-one residue fiber is the whole finite family mass. -/
theorem familyResidueMassRat_one_zero_eq_indexMassRat
    (P : Params) (X : ℝ) (Pz b : ℕ)
    (indices : Finset Family.FamilyIndex) (hX : 1 < X)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i) :
    Family.familyResidueMassRat indices 1 0 =
      Family.familyIndexMassRat indices := by
  rw [← Family.familyEventMassRat_eq_familyIndexMassRat
    P X Pz b indices hX hmem]
  unfold Family.familyResidueMassRat Family.familyEventMassRat
  have hfilter : (Family.familyEvents indices).filter
      (fun event => 1 ∣ event.dPlus ∧ event.e % 1 = 0) =
        Family.familyEvents indices := by
    apply Finset.filter_eq_self.mpr
    intro event hevent
    exact ⟨one_dvd _, Nat.mod_one event.e⟩
  rw [hfilter]

/-- The actual complete-family reciprocal mass is at most cubic-logarithmic.
This is the modulus-one specialization of the already proved fixed-`dminus`
tensor and uses no lower mass estimate. -/
theorem actualPaperFamily_indexMassRat_le_log_cube
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X →
      ∀ b : ℕ, Nat.Coprime b (Inputs.roughModulus X) →
        (Family.familyIndexMassRat
          (Family.familyIndexFinset P X (Inputs.roughModulus X) b) : ℝ) ≤
            C * logCube X := by
  rcases familyFixedDminusResidueMass_le_standard_tensor P with
    ⟨Kf, Xf, hKf, hfiber⟩
  have hMφ := exactDivisorMPhiMassRaw_logSq_of_fiberAverageTwoSided
    (ExactDivisorMPhiFiberAverageTwoSided_of_standard_ordinarySquarefree
      (P := P))
  rcases hMφ with ⟨_cmass, Cmass, Xmass, _hcmass, hCmass, hmassRaw⟩
  refine ⟨3 * Kf * Cmass, max (max Xf Xmass) (Real.exp (Real.exp 2)),
    mul_pos (mul_pos (by norm_num) hKf) hCmass, ?_⟩
  intro X hX hXgt b hbcop
  have hXbase : max Xf Xmass ≤ X := le_trans (le_max_left _ _) hX
  have hXf : Xf ≤ X := le_trans (le_max_left _ _) hXbase
  have hXmass : Xmass ≤ X := le_trans (le_max_right _ _) hXbase
  have hXexp2 : Real.exp (Real.exp 2) ≤ X :=
    le_trans (le_max_right _ _) hX
  have hXexp : Real.exp (Real.exp 1) ≤ X := by
    exact le_trans (Real.exp_le_exp.mpr
      (Real.exp_le_exp.mpr (by norm_num))) hXexp2
  let indices := Family.familyIndexFinset
    P X (Inputs.roughModulus X) b
  have hXpos : 0 < X := lt_trans zero_lt_one hXgt
  have hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X (Inputs.roughModulus X) b i := by
    intro i hi
    exact (Family.mem_familyIndexFinset_iff P X
      (Inputs.roughModulus X) b i hXpos).1 hi
  have hlogZ : 0 < Real.log (zScale X) := by
    have hexp2 : Real.exp 2 ≤ Real.exp (Real.exp 2) :=
      Real.exp_le_exp.mpr (by
        have he := Real.add_one_le_exp (2 : ℝ)
        linarith)
    exact Inputs.log_zScale_pos_of_exp_two_le (hexp2.trans hXexp2)
  let A : ℝ := Kf * (Real.log X / Real.log (zScale X)) *
    exactDivisorMPhiMassRaw P X
  have hrawNonneg : 0 ≤ exactDivisorMPhiMassRaw P X := by
    unfold exactDivisorMPhiMassRaw
    apply Finset.sum_nonneg
    intro x hx
    positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg hKf.le (div_nonneg (Real.log_nonneg hXgt.le) hlogZ.le))
      hrawNonneg
  have hdmTerm : ∀ dminus ∈ familyDminusResidueValues indices 1 0,
      (∑ E ∈ familyExactValuesAtDminus indices 1 0 dminus,
        familyFixedEDminusDivisorMass
          (indices.filter (fun i => i.e % 1 = 0)) E dminus 1) ≤
        A * ((1 : ℝ) / (dminus : ℝ)) := by
    intro dminus hdminus
    rcases Finset.mem_image.mp hdminus with ⟨i, hi, rfl⟩
    have hiIndices := (Finset.mem_filter.mp hi).1
    have himem := hmem i hiIndices
    simpa [A] using hfiber X hXf hXgt b hbcop indices hmem 1 0 i.dminus
      (by norm_num) (by simp) (by simp) (by simp)
      (by simpa using Real.one_le_rpow hXgt.le P.σ_pos.le)
      himem.dminus_pos himem.dminus_le_U himem.dminus_dvd_Pz
      himem.dminus_squarefree himem.dminus_odd
  have hdmSum := familyDminusResidueValues_recip_le_harmonic
    P X (Inputs.roughModulus X) b indices hXpos hmem 1 0
  have hharm := harmonic_floor_UScale_le_three_log_zScale X hXexp
  have hrawUpper := (hmassRaw X hXmass).2
  rw [← familyResidueMassRat_one_zero_eq_indexMassRat
    P X (Inputs.roughModulus X) b indices hXgt hmem]
  rw [familyResidueMassRat_real_eq_dminus_partition
    P X (Inputs.roughModulus X) b indices hXgt hmem 1 0]
  calc
    (∑ dminus ∈ familyDminusResidueValues indices 1 0,
        ∑ E ∈ familyExactValuesAtDminus indices 1 0 dminus,
          familyFixedEDminusDivisorMass
            (indices.filter (fun i => i.e % 1 = 0)) E dminus 1) ≤
      ∑ dminus ∈ familyDminusResidueValues indices 1 0,
        A * ((1 : ℝ) / (dminus : ℝ)) := by
      apply Finset.sum_le_sum
      exact hdmTerm
    _ = A * (∑ dminus ∈ familyDminusResidueValues indices 1 0,
        (1 : ℝ) / (dminus : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ A * (harmonic ⌊UScale X⌋₊ : ℝ) :=
      mul_le_mul_of_nonneg_left hdmSum hA
    _ ≤ A * (3 * Real.log (zScale X)) :=
      mul_le_mul_of_nonneg_left hharm hA
    _ = 3 * Kf * Real.log X * exactDivisorMPhiMassRaw P X := by
      dsimp [A]
      field_simp [ne_of_gt hlogZ]
      ring
    _ ≤ 3 * Kf * Real.log X * (Cmass * logSq X) :=
      mul_le_mul_of_nonneg_left hrawUpper
        (mul_nonneg (mul_nonneg (by norm_num) hKf.le)
          (Real.log_nonneg hXgt.le))
    _ = (3 * Kf * Cmass) * logCube X := by
      unfold logSq logCube
      ring

/-- Natural-number form of the actual-family cubic upper mass theorem. -/
theorem actualPaperFamilyMassNat_eventual_logCube_upper
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)]
    (b : ℕ → ℕ) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ N : ℕ, X₀ ≤ (N : ℝ) → 3 ≤ N →
      Nat.Coprime (b N) (Inputs.roughModulus (N : ℝ)) →
        actualPaperFamilyMassNat P b N ≤ C * logCube (N : ℝ) := by
  rcases actualPaperFamily_indexMassRat_le_log_cube P with
    ⟨C, X₀, hC, hmass⟩
  refine ⟨C, X₀, hC, ?_⟩
  intro N hX hN hcop
  have hNgt : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 3) hN)
  simpa [actualPaperFamilyMassNat] using
    hmass (N : ℝ) hX hNgt (b N) hcop

/-- Actual family mass evaluated at an auxiliary real scale depending on the
ambient natural parameter. -/
noncomputable def actualPaperFamilyMassAtScaleNat
    (P : Params) (scale : ℕ → ℝ) (b : ℕ → ℕ) (N : ℕ) : ℝ :=
  (Family.familyIndexMassRat
    (Family.familyIndexFinset P (scale N)
      (Inputs.roughModulus (scale N)) (b N)) : ℝ)

/-- Cubic lower mass law at an arbitrary auxiliary scale. -/
theorem actualPaperFamilyMassAtScaleNat_logCube_lower
    (P : Params) (scale : ℕ → ℝ) (b : ℕ → ℕ) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ N : ℕ,
      X₀ ≤ scale N → 1 < scale N →
      Nat.Coprime (b N) (Inputs.roughModulus (scale N)) →
        c * logCube (scale N) ≤
          actualPaperFamilyMassAtScaleNat P scale b N := by
  rcases actualPaperFamily_indexMassRat_ge_log_cube P with
    ⟨c, X₀, hc, hmass⟩
  refine ⟨c, X₀, hc, ?_⟩
  intro N hscale hscaleOne hcop
  simpa [actualPaperFamilyMassAtScaleNat, logCube] using
    hmass (scale N) hscale hscaleOne (b N) hcop

/-- Cubic upper mass law at an arbitrary auxiliary scale. -/
theorem actualPaperFamilyMassAtScaleNat_logCube_upper
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)]
    (scale : ℕ → ℝ) (b : ℕ → ℕ) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ N : ℕ,
      X₀ ≤ scale N → 1 < scale N →
      Nat.Coprime (b N) (Inputs.roughModulus (scale N)) →
        actualPaperFamilyMassAtScaleNat P scale b N ≤
          C * logCube (scale N) := by
  rcases actualPaperFamily_indexMassRat_le_log_cube P with
    ⟨C, X₀, hC, hmass⟩
  refine ⟨C, X₀, hC, ?_⟩
  intro N hscale hscaleOne hcop
  simpa [actualPaperFamilyMassAtScaleNat] using
    hmass (scale N) hscale hscaleOne (b N) hcop

/-- Uniform residue tensor for the complete actual paper family.  All
nonstandard hypotheses have been discharged; the remaining dependencies are
exactly the manuscript's cited analytic inputs. -/
theorem actualPaperFamily_residueMass_le_indexMass_div_square
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ K X₀ : ℝ, 0 < K ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X →
      ∀ b : ℕ, Nat.Coprime b (Inputs.roughModulus X) →
      ∀ D c : ℕ, 1 ≤ D → Squarefree D → Odd D →
      Nat.Coprime D (Inputs.roughModulus X) →
      (D : ℝ) ≤ YScale P X →
        (Family.familyResidueMassRat
          (Family.familyIndexFinset P X (Inputs.roughModulus X) b) D c : ℝ) ≤
        K * (Family.familyIndexMassRat
          (Family.familyIndexFinset P X (Inputs.roughModulus X) b) : ℝ) /
          (D : ℝ) ^ 2 := by
  rcases familyFixedDminusResidueMass_le_standard_tensor P with
    ⟨Kf, Xf, hKf, hfiber⟩
  have hMφ := exactDivisorMPhiMassRaw_logSq_of_fiberAverageTwoSided
    (ExactDivisorMPhiFiberAverageTwoSided_of_standard_ordinarySquarefree
      (P := P))
  rcases hMφ with ⟨_cmass, Cmass, Xmass, _hcmass, hCmass, hmassRaw⟩
  rcases actualPaperFamily_indexMassRat_ge_log_cube P with
    ⟨cm, Xm, hcm, hfamilyMass⟩
  refine ⟨3 * Kf * Cmass / cm,
    max (max (max Xf Xmass) Xm) (Real.exp (Real.exp 2)),
    div_pos (mul_pos (mul_pos (by norm_num) hKf) hCmass) hcm, ?_⟩
  intro X hX hXgt b hbcop D c hDone hDsqf hDodd hDcop hDleY
  have hXbase : max (max Xf Xmass) Xm ≤ X :=
    le_trans (le_max_left _ _) hX
  have hXexp2 : Real.exp (Real.exp 2) ≤ X :=
    le_trans (le_max_right _ _) hX
  have hXexp : Real.exp (Real.exp 1) ≤ X := by
    apply le_trans _ hXexp2
    exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by norm_num))
  have hXf : Xf ≤ X := le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) hXbase)
  have hXmass : Xmass ≤ X := le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) hXbase)
  have hXm : Xm ≤ X := le_trans (le_max_right _ _) hXbase
  let indices := Family.familyIndexFinset
    P X (Inputs.roughModulus X) b
  have hXpos : 0 < X := lt_trans zero_lt_one hXgt
  have hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X (Inputs.roughModulus X) b i := by
    intro i hi
    exact (Family.mem_familyIndexFinset_iff P X
      (Inputs.roughModulus X) b i hXpos).1 hi
  have hlogZ : 0 < Real.log (zScale X) := by
    have hexp2 : Real.exp 2 ≤ Real.exp (Real.exp 2) :=
      Real.exp_le_exp.mpr (by
        have h := Real.add_one_le_exp (2 : ℝ)
        linarith)
    exact Inputs.log_zScale_pos_of_exp_two_le (hexp2.trans hXexp2)
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hXgt.le
  have hrawNonneg : 0 ≤ exactDivisorMPhiMassRaw P X := by
    unfold exactDivisorMPhiMassRaw
    apply Finset.sum_nonneg
    intro x hx
    positivity
  let A : ℝ := Kf * (Real.log X / Real.log (zScale X)) *
    exactDivisorMPhiMassRaw P X * ((1 : ℝ) / (D : ℝ) ^ 2)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hdmTerm : ∀ dminus ∈ familyDminusResidueValues indices D c,
      (∑ E ∈ familyExactValuesAtDminus indices D c dminus,
        familyFixedEDminusDivisorMass
          (indices.filter (fun i => i.e % D = c)) E dminus D) ≤
        A * ((1 : ℝ) / (dminus : ℝ)) := by
    intro dminus hdminus
    rcases Finset.mem_image.mp hdminus with ⟨i, hi, rfl⟩
    have hiIndices := (Finset.mem_filter.mp hi).1
    have himem := hmem i hiIndices
    exact hfiber X hXf hXgt b hbcop indices hmem D c i.dminus
      hDone hDsqf hDodd hDcop hDleY himem.dminus_pos himem.dminus_le_U
      himem.dminus_dvd_Pz himem.dminus_squarefree himem.dminus_odd
  have hdmSum := familyDminusResidueValues_recip_le_harmonic
    P X (Inputs.roughModulus X) b indices hXpos hmem D c
  have hharm := harmonic_floor_UScale_le_three_log_zScale X hXexp
  have hrawUpper := (hmassRaw X hXmass).2
  have hfamilyLower := hfamilyMass X hXm hXgt b hbcop
  rw [familyResidueMassRat_real_eq_dminus_partition
    P X (Inputs.roughModulus X) b indices hXgt hmem D c]
  calc
    (∑ dminus ∈ familyDminusResidueValues indices D c,
        ∑ E ∈ familyExactValuesAtDminus indices D c dminus,
          familyFixedEDminusDivisorMass
            (indices.filter (fun i => i.e % D = c)) E dminus D) ≤
      ∑ dminus ∈ familyDminusResidueValues indices D c,
        A * ((1 : ℝ) / (dminus : ℝ)) := by
      apply Finset.sum_le_sum
      exact hdmTerm
    _ = A * (∑ dminus ∈ familyDminusResidueValues indices D c,
        (1 : ℝ) / (dminus : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ A * (harmonic ⌊UScale X⌋₊ : ℝ) :=
      mul_le_mul_of_nonneg_left hdmSum hA
    _ ≤ A * (3 * Real.log (zScale X)) :=
      mul_le_mul_of_nonneg_left hharm hA
    _ = 3 * Kf * Real.log X * exactDivisorMPhiMassRaw P X *
          ((1 : ℝ) / (D : ℝ) ^ 2) := by
      dsimp [A]
      field_simp [ne_of_gt hlogZ]
      ring
    _ ≤ 3 * Kf * Real.log X * (Cmass * logSq X) *
          ((1 : ℝ) / (D : ℝ) ^ 2) := by
      gcongr
    _ = (3 * Kf * Cmass) * logCube X *
          ((1 : ℝ) / (D : ℝ) ^ 2) := by
      unfold logSq logCube
      ring
    _ ≤ (3 * Kf * Cmass / cm) *
          (Family.familyIndexMassRat indices : ℝ) /
          (D : ℝ) ^ 2 := by
      have hscale : (3 * Kf * Cmass) * logCube X ≤
          (3 * Kf * Cmass / cm) *
            (Family.familyIndexMassRat indices : ℝ) := by
        calc
          (3 * Kf * Cmass) * logCube X =
              (3 * Kf * Cmass / cm) * (cm * logCube X) := by
            field_simp [ne_of_gt hcm]
            ring
          _ ≤ (3 * Kf * Cmass / cm) *
              (Family.familyIndexMassRat indices : ℝ) :=
            mul_le_mul_of_nonneg_left hfamilyLower (by positivity)
      have hDsq : 0 ≤ (1 : ℝ) / (D : ℝ) ^ 2 := by positivity
      calc
        (3 * Kf * Cmass) * logCube X * ((1 : ℝ) / (D : ℝ) ^ 2) ≤
            ((3 * Kf * Cmass / cm) *
              (Family.familyIndexMassRat indices : ℝ)) *
                ((1 : ℝ) / (D : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hscale hDsq
        _ = (3 * Kf * Cmass / cm) *
            (Family.familyIndexMassRat indices : ℝ) / (D : ℝ) ^ 2 := by ring

/-- Rational-coefficient form of the complete actual-family residue tensor,
matching the exact Brun recurrence API. -/
theorem actualPaperFamily_residueMassRat_le_indexMassRat_div_square
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ K : ℚ, ∃ X₀ : ℝ, 0 < K ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X →
      ∀ b : ℕ, Nat.Coprime b (Inputs.roughModulus X) →
      ∀ D c : ℕ, 1 ≤ D → Squarefree D → Odd D →
      Nat.Coprime D (Inputs.roughModulus X) →
      (D : ℝ) ≤ YScale P X →
        Family.familyResidueMassRat
          (Family.familyIndexFinset P X (Inputs.roughModulus X) b) D c ≤
        K * Family.familyIndexMassRat
          (Family.familyIndexFinset P X (Inputs.roughModulus X) b) /
          (D : ℚ) ^ 2 := by
  rcases actualPaperFamily_residueMass_le_indexMass_div_square P with
    ⟨Kr, X₀, hKr, hreal⟩
  let Kn : ℕ := Nat.ceil Kr
  let Kq : ℚ := Kn
  have hKn : 1 ≤ Kn := by
    have hceil : Kr ≤ (Kn : ℝ) := Nat.le_ceil Kr
    apply Nat.one_le_iff_ne_zero.mpr
    intro hzero
    rw [hzero, Nat.cast_zero] at hceil
    linarith
  have hKrKq : Kr ≤ (Kq : ℝ) := by
    exact Nat.le_ceil Kr
  refine ⟨Kq, X₀, by
    change (0 : ℚ) < (Kn : ℚ)
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hKn), ?_⟩
  intro X hX hXgt b hbcop D c hDone hDsqf hDodd hDcop hDleY
  let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
  have hmassNonneg : 0 ≤ (Family.familyIndexMassRat indices : ℝ) := by
    have hmassQ : 0 ≤ Family.familyIndexMassRat indices := by
      unfold Family.familyIndexMassRat
      apply Finset.sum_nonneg
      intro i hi
      unfold Family.FamilyIndex.wRat
      positivity
    exact_mod_cast hmassQ
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hDone)
  have hr := hreal X hX hXgt b hbcop D c hDone hDsqf hDodd hDcop hDleY
  have hscaled :
      (Family.familyResidueMassRat indices D c : ℝ) ≤
        (Kq : ℝ) * (Family.familyIndexMassRat indices : ℝ) / (D : ℝ) ^ 2 := by
    calc
      (Family.familyResidueMassRat indices D c : ℝ) ≤
          Kr * (Family.familyIndexMassRat indices : ℝ) / (D : ℝ) ^ 2 := hr
      _ ≤ (Kq : ℝ) * (Family.familyIndexMassRat indices : ℝ) / (D : ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right hKrKq hmassNonneg
        · positivity
  exact_mod_cast hscaled

/-- Any represented increment residue class of the complete paper family
automatically lies on the supported tensor moduli. -/
theorem actualPaperFamily_incrementResidueClass_modulus_data
    (P : Params) (X : ℝ) (b D c : ℕ) (hX : 1 < X)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ Family.familyEvents
      (Family.familyIndexFinset P X (Inputs.roughModulus X) b))
    (hc : c ∈ Family.familyIncrementResidueClasses
      (Family.familyIndexFinset P X (Inputs.roughModulus X) b) old D) :
    1 ≤ D ∧ Squarefree D ∧ Odd D ∧
      Nat.Coprime D (Inputs.roughModulus X) ∧
      (D : ℝ) ≤ YScale P X := by
  let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
  rw [Family.familyIncrementResidueClasses] at hc
  rcases Finset.mem_image.mp hc with ⟨event, heventD, rfl⟩
  rw [Family.familyIncrementDivisorEvents] at heventD
  rcases Finset.mem_filter.mp heventD with ⟨hext, hDg⟩
  have hext' := hext
  rw [Family.familyCompatibleExtensions] at hext
  have hevent : event ∈ Family.familyEvents indices :=
    (Finset.mem_filter.mp hext).1
  have hDdiv : D ∣ event.dPlus :=
    hDg.trans (by
      simpa [Family.familyIncrementG] using
        Family.familyCompatibleExtension_gcd_dvd_dPlus
          P X (Inputs.roughModulus X) b indices hX
          (fun i hi => (Family.mem_familyIndexFinset_iff P X
            (Inputs.roughModulus X) b i (lt_trans zero_lt_one hX)).1 hi)
          old hsub event hext')
  rcases Finset.mem_image.mp hevent with ⟨i, hi, rfl⟩
  have himem := (Family.mem_familyIndexFinset_iff P X
    (Inputs.roughModulus X) b i (lt_trans zero_lt_one hX)).1 hi
  have hDpos : 0 < D := Nat.pos_of_dvd_of_pos hDdiv himem.dplus_pos
  have hDlePlus : D ≤ i.dplus := Nat.le_of_dvd himem.dplus_pos hDdiv
  have hplusProd : (i.dplus : ℝ) ≤ (i.dminus * i.dplus : ℕ) := by
    exact_mod_cast Nat.le_mul_of_pos_left i.dplus himem.dminus_pos
  refine ⟨hDpos, himem.dplus_squarefree.squarefree_of_dvd hDdiv,
    Odd.of_dvd_nat himem.dplus_odd hDdiv, ?_, ?_⟩
  · exact himem.dplus_coprime_Pz.coprime_dvd_left hDdiv
  · calc
      (D : ℝ) ≤ (i.dplus : ℝ) := by exact_mod_cast hDlePlus
      _ ≤ (i.dminus * i.dplus : ℕ) := hplusProd
      _ ≤ YScale P X := by simpa [Nat.cast_mul] using himem.dd_le_Y

/-- The complete actual family satisfies the exact factorial Brun bound once
only the explicit increment Euler tail is supplied.  The residue-tensor field
is discharged by the proved `D^-2` theorem above. -/
theorem actualPaperFamily_compatibleLcmMassRat_le_mass_one_add_pow
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ K : ℚ, ∃ X₀ : ℝ, 0 < K ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X →
      ∀ b : ℕ, Nat.Coprime b (Inputs.roughModulus X) →
      ∀ ε : ℚ, 0 ≤ ε →
      (∀ r : ℕ, 1 ≤ r →
        ∀ old ∈ Family.familyCompatibleSubsetsOfCard
          (Family.familyIndexFinset P X (Inputs.roughModulus X) b) (r - 1),
          (∑ D ∈ Finset.Icc 2 ⌊X⌋₊,
            (K * Family.familyIncrementClassProductRat old D) / (D : ℚ)) ≤ ε) →
      ∀ r : ℕ,
        Family.familyCompatibleLcmMassRat
            (Family.familyIndexFinset P X (Inputs.roughModulus X) b) r ≤
          (Family.familyIndexMassRat
              (Family.familyIndexFinset P X (Inputs.roughModulus X) b) *
            (1 + ε)) ^ r / (Nat.factorial r : ℚ) := by
  rcases actualPaperFamily_residueMassRat_le_indexMassRat_div_square P with
    ⟨K, X₀, hK, htensor⟩
  refine ⟨K, X₀, hK, ?_⟩
  intro X hX hXgt b hbcop ε hε htail r
  let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
  have hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X (Inputs.roughModulus X) b i := by
    intro i hi
    exact (Family.mem_familyIndexFinset_iff P X
      (Inputs.roughModulus X) b i (lt_trans zero_lt_one hXgt)).1 hi
  apply Family.familyCompatibleLcmMassRat_le_mass_one_add_pow_of_residueTensor
    P X (Inputs.roughModulus X) b indices hXgt hmem K ε hK.le hε
  · intro rank hrank old hold D hD c hc
    have hsub : old ⊆ Family.familyEvents indices := by
      rw [Family.familyCompatibleSubsetsOfCard] at hold
      exact (Finset.mem_powersetCard.mp (Finset.mem_of_mem_filter old hold)).1
    have hdata := actualPaperFamily_incrementResidueClass_modulus_data
      P X b D c hXgt old hsub hc
    exact htensor X hX hXgt b hbcop D c hdata.1 hdata.2.1 hdata.2.2.1
      hdata.2.2.2.1 hdata.2.2.2.2
  · exact htail

/-- Direct `dplus = D*t` upper bound for one fixed `(e,dminus)` fiber of the
actual family.  This proves the first `D⁻¹` in `prop:event-tensor` from the
finite family itself and enlarges only to the existing initial rough carrier. -/
theorem familyDplusValues_multiples_recip_le_roughInitial
    (P : Params) (X : ℝ) (b D : ℕ)
    (indices : Finset Family.FamilyIndex) (E : ExactDivisor) (dminus : ℕ)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X (Inputs.roughModulus X) b i)
    (hD : 0 < D) :
    (∑ dplus ∈ (familyDplusValues indices E dminus).filter
        (fun dplus => D ∣ dplus), (1 : ℝ) / (dplus : ℝ)) ≤
      (1 / (D : ℝ)) * Inputs.roughInitial X (4 * E.rho) P.σ := by
  classical
  let U := familyDplusValues indices E dminus
  have hUpos : ∀ dplus ∈ U, 0 < dplus := by
    intro dplus hdplus
    rcases Finset.mem_image.mp hdplus with ⟨i, hi, rfl⟩
    exact (hmem i (Finset.mem_of_mem_filter i hi)).dplus_pos
  have hfactor :=
    EscLeanChecks.reciprocal_sum_multiples_eq_divisor_inv_mul_quotient_image
      U D hD hUpos
  rw [hfactor]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold Inputs.roughInitial
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    rcases Finset.mem_image.mp ht with ⟨dplus, hdplus, rfl⟩
    have hdplusData := Finset.mem_filter.mp hdplus
    rcases Finset.mem_image.mp hdplusData.1 with ⟨i, hi, hidplus⟩
    have hiData := Finset.mem_filter.mp hi
    have hiMem : i ∈ indices := hiData.1
    have hiE : i.E = E := hiData.2.1
    have hDi : D ∣ i.dplus := by simpa [hidplus] using hdplusData.2
    have hsupport :=
      (hmem i hiMem).dplus_div_mem_roughInitial_support
        hX hD hDi
    simpa [hidplus, Family.FamilyIndex.rho, hiE] using hsupport
  · intro t _htBig _htSmall
    positivity

/-- The prime-class exponent for an old subset of the actual paper family is
bounded with no extra roughness hypothesis.  Coprimality with the explicit
`P(z)` supplies the lower bound on every prime divisor. -/
theorem actualRoughFamily_oldPrimeClass_exponent_le
    (P : Params) (X : ℝ) (b B : ℕ)
    (indices : Finset Family.FamilyIndex)
    (hX : Real.exp 1 ≤ X)
    (hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X (Inputs.roughModulus X) b i)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ Family.familyEvents indices) :
    (∑ p ∈ EscLeanChecks.primeFinsetUpTo B,
      ((Family.familyOldPrimeResidueClasses old p).card : ℝ) / (p : ℝ)) ≤
      (old.card : ℝ) *
        ((Real.log (YScale P X) /
            Real.log ((⌊EscAnalytic.zScale X⌋₊ + 1 : ℕ) : ℝ)) /
          ((⌊EscAnalytic.zScale X⌋₊ + 1 : ℕ) : ℝ)) := by
  apply Family.familyOldPrimeClass_exponent_le_card_mul_YScale
    P X (Inputs.roughModulus X) b (⌊EscAnalytic.zScale X⌋₊ + 1) B
      indices (lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hX)
      hmem (two_le_succ_floor_zScale hX)
  · intro p hp hlt
    exact prime_dvd_roughModulus_of_lt_succ_floor hp hlt
  · exact hsub

/-- Fully elementary Euler-product estimate for the increment class factor of
an old subset of the actual paper family. -/
theorem actualRoughFamily_incrementClassProduct_real_sum_le_exp_card
    (P : Params) (X : ℝ) (b B : ℕ)
    (indices : Finset Family.FamilyIndex)
    (hX : Real.exp 1 ≤ X)
    (hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X (Inputs.roughModulus X) b i)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ Family.familyEvents indices) (hB : 1 ≤ B) :
    (1 : ℝ) + (∑ D ∈ Finset.Icc 2 B,
      (Family.familyIncrementClassProductRat old D : ℝ) / (D : ℝ)) ≤
      Real.exp ((old.card : ℝ) *
        ((Real.log (YScale P X) /
            Real.log ((⌊EscAnalytic.zScale X⌋₊ + 1 : ℕ) : ℝ)) /
          ((⌊EscAnalytic.zScale X⌋₊ + 1 : ℕ) : ℝ))) := by
  calc
    (1 : ℝ) + (∑ D ∈ Finset.Icc 2 B,
        (Family.familyIncrementClassProductRat old D : ℝ) / (D : ℝ)) ≤
      Real.exp (∑ p ∈ EscLeanChecks.primeFinsetUpTo B,
        ((Family.familyOldPrimeResidueClasses old p).card : ℝ) / (p : ℝ)) :=
      Family.familyIncrementClassProduct_real_sum_le_exp old B hB
    _ ≤ Real.exp ((old.card : ℝ) *
        ((Real.log (YScale P X) /
            Real.log ((⌊EscAnalytic.zScale X⌋₊ + 1 : ℕ) : ℝ)) /
          ((⌊EscAnalytic.zScale X⌋₊ + 1 : ℕ) : ℝ))) := by
      apply Real.exp_le_exp.mpr
      exact actualRoughFamily_oldPrimeClass_exponent_le
        P X b B indices hX hmem old hsub

/-- Specialization of the exponent bound to the complete finite family
`I_b(X)` itself; no family-membership hypothesis remains. -/
theorem actualPaperFamily_oldPrimeClass_exponent_le
    (P : Params) (X : ℝ) (b B : ℕ) (hX : Real.exp 1 ≤ X)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ Family.familyEvents
      (Family.familyIndexFinset P X (Inputs.roughModulus X) b)) :
    (∑ p ∈ EscLeanChecks.primeFinsetUpTo B,
      ((Family.familyOldPrimeResidueClasses old p).card : ℝ) / (p : ℝ)) ≤
      (old.card : ℝ) *
        ((Real.log (YScale P X) /
            Real.log ((⌊EscAnalytic.zScale X⌋₊ + 1 : ℕ) : ℝ)) /
          ((⌊EscAnalytic.zScale X⌋₊ + 1 : ℕ) : ℝ)) := by
  exact actualRoughFamily_oldPrimeClass_exponent_le P X b B
    (Family.familyIndexFinset P X (Inputs.roughModulus X) b) hX
    (fun i hi =>
      (Family.mem_familyIndexFinset_iff P X (Inputs.roughModulus X) b i
        (lt_of_lt_of_le (Real.exp_pos 1) hX)).mp hi)
    old hsub

/-- Complete-paper-family form of the elementary increment Euler-product
bound. -/
theorem actualPaperFamily_incrementClassProduct_real_sum_le_exp_card
    (P : Params) (X : ℝ) (b B : ℕ) (hX : Real.exp 1 ≤ X)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ Family.familyEvents
      (Family.familyIndexFinset P X (Inputs.roughModulus X) b))
    (hB : 1 ≤ B) :
    (1 : ℝ) + (∑ D ∈ Finset.Icc 2 B,
      (Family.familyIncrementClassProductRat old D : ℝ) / (D : ℝ)) ≤
      Real.exp ((old.card : ℝ) *
        ((Real.log (YScale P X) /
            Real.log ((⌊EscAnalytic.zScale X⌋₊ + 1 : ℕ) : ℝ)) /
          ((⌊EscAnalytic.zScale X⌋₊ + 1 : ℕ) : ℝ))) := by
  exact actualRoughFamily_incrementClassProduct_real_sum_le_exp_card P X b B
    (Family.familyIndexFinset P X (Inputs.roughModulus X) b) hX
    (fun i hi =>
      (Family.mem_familyIndexFinset_iff P X (Inputs.roughModulus X) b i
        (lt_of_lt_of_le (Real.exp_pos 1) hX)).mp hi)
    old hsub hB

/-- Rank-sensitive form of the complete-family increment Euler tail.  This is
the precise loss used in the truncated Brun/Suen iteration. -/
theorem actualPaperFamily_incrementTail_real_le
    (P : Params) (X : ℝ) (b : ℕ) (hX : Real.exp 1 ≤ X)
    (K : ℝ) (hK : 0 ≤ K)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ Family.familyEvents
      (Family.familyIndexFinset P X (Inputs.roughModulus X) b)) :
    (∑ D ∈ Finset.Icc 2 ⌊X⌋₊,
      K * (Family.familyIncrementClassProductRat old D : ℝ) / (D : ℝ)) ≤
      K * (Real.exp ((old.card : ℝ) *
        ((Real.log (YScale P X) /
            Real.log ((⌊zScale X⌋₊ + 1 : ℕ) : ℝ)) /
          ((⌊zScale X⌋₊ + 1 : ℕ) : ℝ))) - 1) := by
  have hXone : (1 : ℝ) ≤ X := le_trans (by
    have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    exact this) hX
  have hfloor : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by simpa using hXone)
  have hbase := actualPaperFamily_incrementClassProduct_real_sum_le_exp_card
    P X b ⌊X⌋₊ hX old hsub hfloor
  have hsum : (∑ D ∈ Finset.Icc 2 ⌊X⌋₊,
      (Family.familyIncrementClassProductRat old D : ℝ) / (D : ℝ)) ≤
      Real.exp ((old.card : ℝ) *
        ((Real.log (YScale P X) /
            Real.log ((⌊zScale X⌋₊ + 1 : ℕ) : ℝ)) /
          ((⌊zScale X⌋₊ + 1 : ℕ) : ℝ))) - 1 := by
    linarith
  calc
    (∑ D ∈ Finset.Icc 2 ⌊X⌋₊,
        K * (Family.familyIncrementClassProductRat old D : ℝ) / (D : ℝ)) =
      K * (∑ D ∈ Finset.Icc 2 ⌊X⌋₊,
        (Family.familyIncrementClassProductRat old D : ℝ) / (D : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D hD
      ring
    _ ≤ K * (Real.exp ((old.card : ℝ) *
        ((Real.log (YScale P X) /
            Real.log ((⌊zScale X⌋₊ + 1 : ℕ) : ℝ)) /
          ((⌊zScale X⌋₊ + 1 : ℕ) : ℝ))) - 1) :=
      mul_le_mul_of_nonneg_left hsum hK

/-! ## Truncated-rank increment scale -/

/-- The exact floor-based scale produced by the finite Euler product. -/
noncomputable def paperIncrementFloorScale (P : Params) (X : ℝ) : ℝ :=
  (Real.log (YScale P X) /
      Real.log (((⌊zScale X⌋₊ + 1 : ℕ) : ℝ))) /
    (((⌊zScale X⌋₊ + 1 : ℕ) : ℝ))

/-- The exact floor-based increment scale is no larger than the manuscript's
medium-prime scale once `X ≥ exp 2`. -/
theorem paperIncrementFloorScale_le_paperMediumScale
    (P : Params) {X : ℝ} (hX : Real.exp 2 ≤ X) :
    paperIncrementFloorScale P X ≤ paperMediumScale P X := by
  have hXexp1 : Real.exp 1 ≤ X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)) hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 2) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (Real.one_le_exp (by norm_num)) hX
  have hz_pos : 0 < zScale X :=
    lt_of_lt_of_le zero_lt_one (Inputs.zScale_ge_one_of_exp_one_le hXexp1)
  have hlogz_pos : 0 < Real.log (zScale X) :=
    Inputs.log_zScale_pos_of_exp_two_le hX
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
  unfold paperIncrementFloorScale paperMediumScale
  change Real.log (YScale P X) / Real.log q / q ≤ _
  rw [div_div]
  simpa [mul_comm] using hdiv

/-- The floor-based scale is nonnegative on the same large range. -/
theorem paperIncrementFloorScale_nonneg
    (P : Params) {X : ℝ} (hX : Real.exp 2 ≤ X) :
    0 ≤ paperIncrementFloorScale P X := by
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
  unfold paperIncrementFloorScale
  positivity

/-- At the manuscript's cubic rank scale, the exact floor-based increment
loss tends to zero. -/
theorem paperIncrementFloorScale_logCube_tendsto_zero (P : Params) :
    Filter.Tendsto
      (fun X : ℝ => (Real.log X) ^ 3 * paperIncrementFloorScale P X)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [Filter.eventually_ge_atTop (Real.exp 2)] with X hX
    exact mul_nonneg (pow_nonneg (Real.log_nonneg
      (le_trans (Real.one_le_exp (by norm_num)) hX)) 3)
      (paperIncrementFloorScale_nonneg P hX)
  · filter_upwards [Filter.eventually_ge_atTop (Real.exp 2)] with X hX
    exact mul_le_mul_of_nonneg_left
      (paperIncrementFloorScale_le_paperMediumScale P hX)
      (pow_nonneg (Real.log_nonneg
        (le_trans (Real.one_le_exp (by norm_num)) hX)) 3)
  · exact paperMediumScale_logCube_tendsto_zero P

/-- A fixed cubic-log rank envelope makes the complete increment Euler loss
vanish. -/
theorem paperIncrementCubicRankError_tendsto_zero
    (P : Params) (K C : ℝ) :
    Filter.Tendsto
      (fun X : ℝ => K *
        (Real.exp (C * ((Real.log X) ^ 3 * paperIncrementFloorScale P X)) - 1))
      Filter.atTop (nhds 0) := by
  have htail : Filter.Tendsto
      (fun X : ℝ => C *
        ((Real.log X) ^ 3 * paperIncrementFloorScale P X))
      Filter.atTop (nhds 0) := by
    simpa using
      (paperIncrementFloorScale_logCube_tendsto_zero P).const_mul C
  have hexp : Filter.Tendsto
      (fun X : ℝ =>
        Real.exp (C * ((Real.log X) ^ 3 * paperIncrementFloorScale P X)) - 1)
      Filter.atTop (nhds 0) := by
    simpa using ((Real.continuous_exp.tendsto 0).comp htail).sub
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
        Filter.atTop (nhds 1))
  simpa using hexp.const_mul K

/-- A pointwise rank below `C(log X)^3` is dominated by the vanishing cubic
rank envelope. -/
theorem paperIncrementRankError_le_cubicRankError
    (P : Params) {X K C : ℝ} {R : ℕ}
    (hX : Real.exp 2 ≤ X) (hK : 0 ≤ K) (_hC : 0 ≤ C)
    (hR : (R : ℝ) ≤ C * (Real.log X) ^ 3) :
    K * (Real.exp ((R : ℝ) * paperIncrementFloorScale P X) - 1) ≤
      K * (Real.exp
        (C * ((Real.log X) ^ 3 * paperIncrementFloorScale P X)) - 1) := by
  have hscale : 0 ≤ paperIncrementFloorScale P X :=
    paperIncrementFloorScale_nonneg P hX
  apply mul_le_mul_of_nonneg_left _ hK
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  simpa [mul_assoc] using mul_le_mul_of_nonneg_right hR hscale

/-- The canonical rank `floor(12 μ)+1` is at most `13 μ` once `μ ≥ 1`. -/
theorem brunFloorRank_le_thirteen_mul {μ : ℝ} (hμ : 1 ≤ μ) :
    (((⌊12 * μ⌋₊ + 1 : ℕ) : ℝ)) ≤ 13 * μ := by
  have hfloor : ((⌊12 * μ⌋₊ : ℕ) : ℝ) ≤ 12 * μ :=
    Nat.floor_le (by nlinarith)
  norm_num at hfloor ⊢
  linarith

/-- If the event mass is at most cubic-logarithmic, the increment loss at the
canonical Brun rank tends to zero. -/
theorem paperIncrementBrunFloorRankError_tendsto_zero_of_mass_logCube_upper
    (P : Params) (μ : ℝ → ℝ) (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hμ_one : ∀ᶠ X in Filter.atTop, 1 ≤ μ X)
    (hμ_upper : ∀ᶠ X in Filter.atTop,
      μ X ≤ C * (Real.log X) ^ 3) :
    Filter.Tendsto
      (fun X : ℝ => K *
        (Real.exp
          ((((⌊12 * μ X⌋₊ + 1 : ℕ) : ℝ)) *
            paperIncrementFloorScale P X) - 1))
      Filter.atTop (nhds 0) := by
  have hXlarge : ∀ᶠ X in Filter.atTop, Real.exp 2 ≤ X :=
    Filter.eventually_ge_atTop (Real.exp 2)
  have hnonneg : ∀ᶠ X in Filter.atTop,
      0 ≤ K * (Real.exp
        ((((⌊12 * μ X⌋₊ + 1 : ℕ) : ℝ)) *
          paperIncrementFloorScale P X) - 1) := by
    filter_upwards [hXlarge] with X hX
    have hscale := paperIncrementFloorScale_nonneg P hX
    exact mul_nonneg hK (sub_nonneg.mpr
      (Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) hscale)))
  have hupper : ∀ᶠ X in Filter.atTop,
      K * (Real.exp
        ((((⌊12 * μ X⌋₊ + 1 : ℕ) : ℝ)) *
          paperIncrementFloorScale P X) - 1) ≤
      K * (Real.exp
        ((13 * C) * ((Real.log X) ^ 3 *
          paperIncrementFloorScale P X)) - 1) := by
    filter_upwards [hXlarge, hμ_one, hμ_upper] with X hX hμ1 hμup
    have hrank : (((⌊12 * μ X⌋₊ + 1 : ℕ) : ℝ)) ≤
        (13 * C) * (Real.log X) ^ 3 := by
      calc
        (((⌊12 * μ X⌋₊ + 1 : ℕ) : ℝ)) ≤ 13 * μ X :=
          brunFloorRank_le_thirteen_mul hμ1
        _ ≤ 13 * (C * (Real.log X) ^ 3) :=
          mul_le_mul_of_nonneg_left hμup (by norm_num)
        _ = (13 * C) * (Real.log X) ^ 3 := by ring
    exact paperIncrementRankError_le_cubicRankError P hX hK
      (mul_nonneg (by norm_num) hC) hrank
  exact squeeze_zero' hnonneg hupper
    (paperIncrementCubicRankError_tendsto_zero P K (13 * C))

/-- Brun iteration needs the increment estimate only through the truncation
rank.  This bounded-rank form avoids imposing a false all-rank uniformity. -/
theorem familyCompatibleLcmMassRat_le_pow_div_factorial_of_increment_le_up_to
    (P : Params) (X : ℝ) (Pz b : ℕ)
    (indices : Finset Family.FamilyIndex)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i)
    (M : ℚ) (hM : 0 ≤ M) (R : ℕ)
    (hinc : ∀ r : ℕ, 1 ≤ r → r ≤ R →
      ∀ old ∈ Family.familyCompatibleSubsetsOfCard indices (r - 1),
        Family.familyIncrementRat indices old ≤ M) :
    ∀ r : ℕ, r ≤ R →
      Family.familyCompatibleLcmMassRat indices r ≤
        M ^ r / (Nat.factorial r : ℚ) := by
  intro r hrR
  induction r with
  | zero => simp
  | succ r ih =>
      have hrsucc : 1 ≤ r + 1 := Nat.succ_le_succ (Nat.zero_le r)
      have hrR' : r ≤ R := le_trans (Nat.le_succ r) hrR
      have hrec := Family.familyCompatibleLcmMassRat_recurrence_le_of_increment_le
        P X Pz b indices hmem M (r + 1)
          (hinc (r + 1) hrsucc hrR) (by omega)
      have hrpos : (0 : ℚ) < (r + 1 : ℕ) := by positivity
      have hstep :
          Family.familyCompatibleLcmMassRat indices (r + 1) ≤
            (M / (r + 1 : ℕ)) *
              Family.familyCompatibleLcmMassRat indices r := by
        have hrne : ((r + 1 : ℕ) : ℚ) ≠ 0 := ne_of_gt hrpos
        rw [show (M / (r + 1 : ℕ)) *
            Family.familyCompatibleLcmMassRat indices r =
          (M * Family.familyCompatibleLcmMassRat indices r) /
            (r + 1 : ℕ) by field_simp [hrne]]
        rw [le_div_iff₀ hrpos]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hrec
      calc
        Family.familyCompatibleLcmMassRat indices (r + 1) ≤
            (M / (r + 1 : ℕ)) *
              Family.familyCompatibleLcmMassRat indices r := hstep
        _ ≤ (M / (r + 1 : ℕ)) *
              (M ^ r / (Nat.factorial r : ℚ)) :=
          mul_le_mul_of_nonneg_left (ih hrR') (div_nonneg hM hrpos.le)
        _ = M ^ (r + 1) / (Nat.factorial (r + 1) : ℚ) := by
          have hrne : ((r + 1 : ℕ) : ℚ) ≠ 0 := by positivity
          have hfactne : (Nat.factorial r : ℚ) ≠ 0 := by positivity
          field_simp [Nat.factorial_succ, hrne, hfactne, pow_succ]
          ring

/-- Bounded-rank event-tensor Brun bound.  Both the tensor and Euler-tail
inputs are required only at ranks actually used by the truncation. -/
theorem familyCompatibleLcmMassRat_le_mass_one_add_pow_of_residueTensor_up_to
    (P : Params) (X : ℝ) (Pz b : ℕ)
    (indices : Finset Family.FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i)
    (K ε : ℚ) (hK : 0 ≤ K) (hε : 0 ≤ ε) (R : ℕ)
    (htensor : ∀ r : ℕ, 1 ≤ r → r ≤ R →
      ∀ old ∈ Family.familyCompatibleSubsetsOfCard indices (r - 1),
      ∀ D ∈ Finset.Icc 2 ⌊X⌋₊,
      ∀ c ∈ Family.familyIncrementResidueClasses indices old D,
        Family.familyResidueMassRat indices D c ≤
          K * Family.familyIndexMassRat indices / (D : ℚ) ^ 2)
    (htail : ∀ r : ℕ, 1 ≤ r → r ≤ R →
      ∀ old ∈ Family.familyCompatibleSubsetsOfCard indices (r - 1),
        (∑ D ∈ Finset.Icc 2 ⌊X⌋₊,
          (K * Family.familyIncrementClassProductRat old D) / (D : ℚ)) ≤ ε) :
    ∀ r : ℕ, r ≤ R →
      Family.familyCompatibleLcmMassRat indices r ≤
        (Family.familyIndexMassRat indices * (1 + ε)) ^ r /
          (Nat.factorial r : ℚ) := by
  classical
  have hmassNonneg : 0 ≤ Family.familyIndexMassRat indices := by
    unfold Family.familyIndexMassRat
    apply Finset.sum_nonneg
    intro i _hi
    unfold Family.FamilyIndex.wRat
    positivity
  apply familyCompatibleLcmMassRat_le_pow_div_factorial_of_increment_le_up_to
    P X Pz b indices hmem
      (Family.familyIndexMassRat indices * (1 + ε))
      (mul_nonneg hmassNonneg (by linarith)) R
  intro r hr hrR old hold
  rw [Family.familyCompatibleSubsetsOfCard] at hold
  have hsub : old ⊆ Family.familyEvents indices :=
    (Finset.mem_powersetCard.mp (Finset.mem_of_mem_filter old hold)).1
  have hincrement :=
    Family.familyIncrementRat_le_of_familyResidueMass_classProduct
      P X Pz b indices hX hmem old hsub K hK
        (htensor r hr hrR old (by
          rw [Family.familyCompatibleSubsetsOfCard]
          exact hold))
  exact hincrement.trans (mul_le_mul_of_nonneg_left
    (add_le_add_left (htail r hr hrR old (by
      rw [Family.familyCompatibleSubsetsOfCard]
      exact hold)) 1) hmassNonneg)

/-- The actual finite Euler tail at any rank up to `R` is reduced to one
scalar exponential inequality. -/
theorem actualPaperFamily_incrementTailRat_le_of_rank_scale
    (P : Params) (X : ℝ) (b r R : ℕ) (K ε : ℚ)
    (hX : Real.exp 2 ≤ X) (hK : 0 ≤ K) (hr : 1 ≤ r) (hrR : r ≤ R)
    (old : Finset EscLeanChecks.SatEvent)
    (hold : old ∈ Family.familyCompatibleSubsetsOfCard
      (Family.familyIndexFinset P X (Inputs.roughModulus X) b) (r - 1))
    (hscalar : (K : ℝ) *
      (Real.exp ((R : ℝ) * paperIncrementFloorScale P X) - 1) ≤ (ε : ℝ)) :
    (∑ D ∈ Finset.Icc 2 ⌊X⌋₊,
      (K * Family.familyIncrementClassProductRat old D) / (D : ℚ)) ≤ ε := by
  let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
  have hold' := hold
  rw [Family.familyCompatibleSubsetsOfCard] at hold'
  have hpowerset : old ∈ (Family.familyEvents indices).powersetCard (r - 1) :=
    Finset.mem_of_mem_filter old hold'
  have hsub : old ⊆ Family.familyEvents indices :=
    (Finset.mem_powersetCard.mp hpowerset).1
  have hcard : old.card = r - 1 :=
    (Finset.mem_powersetCard.mp hpowerset).2
  have hcardR : old.card ≤ R := by omega
  have hscale_nonneg : 0 ≤ paperIncrementFloorScale P X :=
    paperIncrementFloorScale_nonneg P hX
  have hexponent :
      (old.card : ℝ) * paperIncrementFloorScale P X ≤
        (R : ℝ) * paperIncrementFloorScale P X := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcardR) hscale_nonneg
  have htail := actualPaperFamily_incrementTail_real_le P X b
    (le_trans (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)) hX)
    (K : ℝ) (by exact_mod_cast hK) old hsub
  have hreal :
      (∑ D ∈ Finset.Icc 2 ⌊X⌋₊,
        ((K * Family.familyIncrementClassProductRat old D) / (D : ℚ) : ℝ)) ≤
        (ε : ℝ) := by
    calc
      _ = (∑ D ∈ Finset.Icc 2 ⌊X⌋₊,
          (K : ℝ) * (Family.familyIncrementClassProductRat old D : ℝ) /
            (D : ℝ)) := by norm_num
      _ ≤ (K : ℝ) *
          (Real.exp ((old.card : ℝ) * paperIncrementFloorScale P X) - 1) := by
        simpa [paperIncrementFloorScale] using htail
      _ ≤ (K : ℝ) *
          (Real.exp ((R : ℝ) * paperIncrementFloorScale P X) - 1) := by
        apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast hK)
        linarith [Real.exp_le_exp.mpr hexponent]
      _ ≤ (ε : ℝ) := hscalar
  exact_mod_cast hreal

/-- Fully concrete bounded-rank Brun estimate for the actual paper family.
The former family-wise tail hypothesis is replaced by a single explicit
scalar inequality at the truncation rank. -/
theorem actualPaperFamily_compatibleLcmMassRat_le_up_to_of_rank_scale
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ K : ℚ, ∃ X₀ : ℝ, 0 < K ∧ ∀ X : ℝ,
      X₀ ≤ X → Real.exp 2 ≤ X →
      ∀ b : ℕ, Nat.Coprime b (Inputs.roughModulus X) →
      ∀ ε : ℚ, 0 ≤ ε → ∀ R : ℕ,
      (K : ℝ) *
        (Real.exp ((R : ℝ) * paperIncrementFloorScale P X) - 1) ≤ (ε : ℝ) →
      ∀ r : ℕ, r ≤ R →
        Family.familyCompatibleLcmMassRat
            (Family.familyIndexFinset P X (Inputs.roughModulus X) b) r ≤
          (Family.familyIndexMassRat
              (Family.familyIndexFinset P X (Inputs.roughModulus X) b) *
            (1 + ε)) ^ r / (Nat.factorial r : ℚ) := by
  rcases actualPaperFamily_residueMassRat_le_indexMassRat_div_square P with
    ⟨K, X₀, hK, htensor⟩
  refine ⟨K, X₀, hK, ?_⟩
  intro X hX hXexp b hbcop ε hε R hscalar
  let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
  have hXgt : 1 < X :=
    lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num))
      (le_trans (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)) hXexp)
  have hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X (Inputs.roughModulus X) b i := by
    intro i hi
    exact (Family.mem_familyIndexFinset_iff P X
      (Inputs.roughModulus X) b i (lt_trans zero_lt_one hXgt)).1 hi
  apply familyCompatibleLcmMassRat_le_mass_one_add_pow_of_residueTensor_up_to
    P X (Inputs.roughModulus X) b indices hXgt hmem K ε hK.le hε R
  · intro rank hrank hrankR old hold D hD c hc
    have hsub : old ⊆ Family.familyEvents indices := by
      rw [Family.familyCompatibleSubsetsOfCard] at hold
      exact (Finset.mem_powersetCard.mp
        (Finset.mem_of_mem_filter old hold)).1
    have hdata := actualPaperFamily_incrementResidueClass_modulus_data
      P X b D c hXgt old hsub hc
    exact htensor X hX hXgt b hbcop D c hdata.1 hdata.2.1 hdata.2.2.1
      hdata.2.2.2.1 hdata.2.2.2.2
  · intro rank hrank hrankR old hold
    exact actualPaperFamily_incrementTailRat_le_of_rank_scale
      P X b rank R K ε hXexp hK.le hrank hrankR old hold hscalar

/-! ## Exact modular-event carrier for the cited Suen step -/

/-- The concrete modular event represented by one certificate-family event.  The
tag retains the full family datum, while the modulus and residue are exactly
the congruence `n = -4e (mod dPlus*p)` used in the paper. -/
def familyModularEvent (event : EscLeanChecks.SatEvent) :
    Inputs.ModularEvent where
  tag := (event.e, event.dMinus, event.dPlus, event.p)
  modulus := EscLeanChecks.conditionalModulus event.dPlus event.p
  residue := EscLeanChecks.negModResidue
    (EscLeanChecks.conditionalModulus event.dPlus event.p) (4 * event.e)

theorem familyModularEvent_injective : Function.Injective familyModularEvent := by
  intro event other h
  cases event with
  | mk e dMinus dPlus p =>
      cases other with
      | mk e' dMinus' dPlus' p' =>
          simp only [familyModularEvent] at h
          have htag : (e, dMinus, dPlus, p) =
              (e', dMinus', dPlus', p') := congrArg Inputs.ModularEvent.tag h
          simp only [Prod.mk.injEq] at htag
          rcases htag with ⟨rfl, rfl, rfl, rfl⟩
          rfl

/-- Exact finite modular-event family attached to a finite paper family. -/
noncomputable def familyModularEvents (indices : Finset Family.FamilyIndex) :
    Finset Inputs.ModularEvent :=
  (Family.familyEvents indices).image familyModularEvent

/-- Passing to the exact modular-event carrier preserves the first moment. -/
theorem modularMass_familyModularEvents
    (indices : Finset Family.FamilyIndex) :
    Inputs.modularMass (familyModularEvents indices) =
      (Family.familyEventMassRat indices : ℝ) := by
  classical
  rw [Inputs.modularMass, familyModularEvents, Finset.sum_image]
  · simp only [Inputs.modularEventMass, familyModularEvent,
      Family.familyEventMassRat, Family.familyEventWeightRat]
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro event hevent
    rw [Rat.cast_div]
    norm_num
  · intro event hevent other hother heq
    exact familyModularEvent_injective heq

/-- A common complete period for all congruence events in a finite paper
family. -/
noncomputable def familyModularPeriod (indices : Finset Family.FamilyIndex) : ℕ :=
  EscLeanChecks.congruenceLcm
    (EscLeanChecks.satEventResidualHitRows (Family.familyEvents indices).toList)

theorem familyModularPeriod_pos
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset Family.FamilyIndex)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i) :
    0 < familyModularPeriod indices := by
  apply EscLeanChecks.congruenceLcm_pos_of_rows_positive
  intro row hrow
  rcases List.mem_map.mp hrow with ⟨event, hevent, rfl⟩
  apply Family.familyEvents_residualModulus_pos P X Pz b indices hmem event
  simpa using hevent

theorem familyModularEvent_modulus_dvd_period
    (indices : Finset Family.FamilyIndex)
    {event : EscLeanChecks.SatEvent}
    (hevent : event ∈ Family.familyEvents indices) :
    (familyModularEvent event).modulus ∣ familyModularPeriod indices := by
  unfold familyModularEvent familyModularPeriod
  change EscLeanChecks.conditionalModulus event.dPlus event.p ∣
    EscLeanChecks.congruenceLcm
      (EscLeanChecks.satEventResidualHitRows (Family.familyEvents indices).toList)
  have hrow : EscLeanChecks.satEventResidualHitRow event ∈
      EscLeanChecks.satEventResidualHitRows (Family.familyEvents indices).toList :=
    List.mem_map.mpr ⟨event, by simpa using hevent, rfl⟩
  simpa [EscLeanChecks.satEventResidualHitRow] using
    (EscLeanChecks.congruenceRow_modulus_dvd_lcm
      (EscLeanChecks.satEventResidualHitRows (Family.familyEvents indices).toList)
      (EscLeanChecks.satEventResidualHitRow event) hrow)

/-- Every event in the exact modular image has a positive modulus dividing the
canonical common period. -/
theorem familyModularEvents_period_data
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset Family.FamilyIndex)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i) :
    ∀ event ∈ familyModularEvents indices,
      0 < event.modulus ∧ event.modulus ∣ familyModularPeriod indices := by
  intro event hevent
  rcases Finset.mem_image.mp hevent with ⟨source, hsource, rfl⟩
  exact ⟨Family.familyEvents_residualModulus_pos P X Pz b indices hmem
      source hsource,
    familyModularEvent_modulus_dvd_period indices hsource⟩

/-- The cited Suen theorem instantiated on the actual finite paper family.
The exponent contains only the concrete family mass, maximal dependency
neighborhood, and exact ordered pair-intersection sum. -/
theorem family_modular_suen_inequality
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset Family.FamilyIndex)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i) :
    ∃ K : ℝ, 0 < K ∧
      Inputs.modularNoHitProbability
          (familyModularPeriod indices) (familyModularEvents indices) ≤
        Real.exp
          (-(Family.familyEventMassRat indices : ℝ) +
            K * Inputs.modularDependencyMass (familyModularEvents indices) *
              Real.exp (2 * Inputs.modularDelta (familyModularEvents indices))) := by
  rcases Inputs.modular_suen_inequality
      (familyModularPeriod indices) (familyModularEvents indices)
      (familyModularPeriod_pos P X Pz b indices hmem)
      (familyModularEvents_period_data P X Pz b indices hmem) with
    ⟨K, hK, hbound⟩
  refine ⟨K, hK, ?_⟩
  simpa [modularMass_familyModularEvents] using hbound

/-- Structural split behind the manuscript's dependency estimate.  Two
dependent actual events either share their selected large prime or their
medium factors are non-coprime.  Cross divisibility between a large prime and
the other event's medium factor is excluded by the paper's scale separation. -/
theorem familyModularDependent_largePrime_or_medium
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset Family.FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i)
    {event other : EscLeanChecks.SatEvent}
    (hevent : event ∈ Family.familyEvents indices)
    (hother : other ∈ Family.familyEvents indices)
    (hdep : Inputs.modularDependent
      (familyModularEvent event) (familyModularEvent other)) :
    event.p = other.p ∨ ¬ Nat.Coprime event.dPlus other.dPlus := by
  rcases hdep with ⟨hne, hnotCoprime⟩
  by_contra hsplit
  push_neg at hsplit
  rcases hsplit with ⟨hpne, hmedium⟩
  have heventPrime : Nat.Prime event.p := by
    rcases Finset.mem_image.mp hevent with ⟨i, hi, rfl⟩
    exact (hmem i hi).p_prime
  have hotherPrime : Nat.Prime other.p := by
    rcases Finset.mem_image.mp hother with ⟨i, hi, rfl⟩
    exact (hmem i hi).p_prime
  have hotherDlt : other.dPlus < event.p :=
    Family.familyEvents_dPlus_lt_p_of_mem P X Pz b indices hX hmem
      hevent hother
  have heventDlt : event.dPlus < other.p :=
    Family.familyEvents_dPlus_lt_p_of_mem P X Pz b indices hX hmem
      hother hevent
  have hp_otherD : Nat.Coprime event.p other.dPlus := by
    rw [heventPrime.coprime_iff_not_dvd]
    exact Nat.not_dvd_of_pos_of_lt
      (by rcases Finset.mem_image.mp hother with ⟨i, hi, rfl⟩
          exact (hmem i hi).dplus_pos)
      hotherDlt
  have hq_eventD : Nat.Coprime other.p event.dPlus := by
    rw [hotherPrime.coprime_iff_not_dvd]
    exact Nat.not_dvd_of_pos_of_lt
      (by rcases Finset.mem_image.mp hevent with ⟨i, hi, rfl⟩
          exact (hmem i hi).dplus_pos)
      heventDlt
  have hpq : Nat.Coprime event.p other.p := by
    rw [heventPrime.coprime_iff_not_dvd]
    intro hdvd
    rcases (Nat.dvd_prime hotherPrime).mp hdvd with hp1 | hpeq
    · exact heventPrime.ne_one hp1
    · exact hpne hpeq
  have hleft : Nat.Coprime event.dPlus
      (other.dPlus * other.p) := by
    rw [Nat.coprime_mul_iff_right]
    exact ⟨hmedium, hq_eventD.symm⟩
  have hright : Nat.Coprime event.p
      (other.dPlus * other.p) := by
    rw [Nat.coprime_mul_iff_right]
    exact ⟨hp_otherD, hpq⟩
  apply hnotCoprime
  rw [show (familyModularEvent event).modulus =
      event.dPlus * event.p by rfl,
    show (familyModularEvent other).modulus =
      other.dPlus * other.p by rfl,
    Nat.coprime_mul_iff_left]
  exact ⟨hleft, hright⟩

/-- Negating both residue classes preserves and reflects compatibility when
the two moduli are positive.  The forward direction already appears in the CRT
core; this reverse direction closes the identification needed for pair masses. -/
theorem residueCompatible_of_negModResidue_compatible
    (q r a b : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hcompat : EscLeanChecks.residueCompatible q r
      (EscLeanChecks.negModResidue q a) (EscLeanChecks.negModResidue r b)) :
    EscLeanChecks.residueCompatible q r a b := by
  have hleft : EscLeanChecks.negModResidue q a + a ≡ 0
      [MOD Nat.gcd q r] :=
    Nat.ModEq.of_dvd (Nat.gcd_dvd_left q r)
      (EscLeanChecks.negModResidue_add_modEq_zero q a hq)
  have hright : EscLeanChecks.negModResidue r b + b ≡ 0
      [MOD Nat.gcd q r] :=
    Nat.ModEq.of_dvd (Nat.gcd_dvd_right q r)
      (EscLeanChecks.negModResidue_add_modEq_zero r b hr)
  exact Nat.ModEq.add_left_cancel hcompat (hleft.trans hright.symm)

theorem familyModularEvent_residualCompatible_iff
    (event other : EscLeanChecks.SatEvent)
    (heventMod : 0 < EscLeanChecks.conditionalModulus event.dPlus event.p)
    (hotherMod : 0 < EscLeanChecks.conditionalModulus other.dPlus other.p) :
    (familyModularEvent event).residue ≡ (familyModularEvent other).residue
        [MOD Nat.gcd (familyModularEvent event).modulus
          (familyModularEvent other).modulus] ↔
      EscLeanChecks.satEventCompatible event other := by
  constructor
  · exact residueCompatible_of_negModResidue_compatible
      _ _ _ _ heventMod hotherMod
  · exact EscLeanChecks.satEventResidualHitRow_compatible_of_satEventCompatible
      event other heventMod hotherMod

/-- On positive actual moduli, the modular pair-intersection mass is exactly
the reciprocal-LCM coefficient used by the paper for compatible pairs. -/
theorem modularPairMass_familyModularEvent
    (event other : EscLeanChecks.SatEvent)
    (heventMod : 0 < EscLeanChecks.conditionalModulus event.dPlus event.p)
    (hotherMod : 0 < EscLeanChecks.conditionalModulus other.dPlus other.p) :
    Inputs.modularPairMass (familyModularEvent event) (familyModularEvent other) =
      if EscLeanChecks.satEventCompatible event other then
        (Family.familySubsetLcmRecipRat {event, other} : ℝ)
      else 0 := by
  classical
  rw [Inputs.modularPairMass]
  rw [if_congr
    (familyModularEvent_residualCompatible_iff event other heventMod hotherMod)
    rfl rfl]
  split_ifs with hcompat
  · have hlcm : EscLeanChecks.congruenceLcm
        (EscLeanChecks.satEventResidualHitRows ({event, other} :
          Finset EscLeanChecks.SatEvent).toList) =
        Nat.lcm (EscLeanChecks.conditionalModulus event.dPlus event.p)
          (EscLeanChecks.conditionalModulus other.dPlus other.p) := by
      have hsingle : EscLeanChecks.congruenceLcm
          (EscLeanChecks.satEventResidualHitRows
            ({other} : Finset EscLeanChecks.SatEvent).toList) =
          EscLeanChecks.conditionalModulus other.dPlus other.p := by
        simpa [EscLeanChecks.congruenceLcm,
          EscLeanChecks.satEventResidualHitRows, Nat.lcm_one_right] using
          (EscLeanChecks.congruenceLcm_satEventResidualHitRows_insert_eq_lcm
            (∅ : Finset EscLeanChecks.SatEvent) other)
      rw [EscLeanChecks.congruenceLcm_satEventResidualHitRows_insert_eq_lcm]
      rw [hsingle]
    unfold Family.familySubsetLcmRecipRat
    rw [hlcm, Rat.cast_div]
    change 1 / ((EscLeanChecks.conditionalModulus event.dPlus event.p).lcm
        (EscLeanChecks.conditionalModulus other.dPlus other.p) : ℝ) = _
    norm_num
  · rfl

/-! ## Exact dependency-neighborhood decomposition -/

/-- Neighborhood mass pulled back from the modular image to the actual
certificate-event carrier. -/
noncomputable def familyDependentNeighbourMass
    (indices : Finset Family.FamilyIndex)
    (event : EscLeanChecks.SatEvent) : ℝ :=
  ∑ other ∈ (Family.familyEvents indices).filter
      (fun other => Inputs.modularDependent
        (familyModularEvent event) (familyModularEvent other)),
    (Family.familyEventWeightRat other : ℝ)

/-- Contribution from events sharing the selected large prime. -/
noncomputable def familyLargePrimeNeighbourMass
    (indices : Finset Family.FamilyIndex)
    (event : EscLeanChecks.SatEvent) : ℝ :=
  ∑ other ∈ (Family.familyEvents indices).filter
      (fun other => other ≠ event ∧ other.p = event.p),
    (Family.familyEventWeightRat other : ℝ)

/-- Maximal shared-large-prime neighborhood mass in the actual finite family. -/
noncomputable def familyLargePrimeDelta
    (indices : Finset Family.FamilyIndex) : ℝ :=
  if h : (Family.familyEvents indices).Nonempty then
    (Family.familyEvents indices).sup' h
      (familyLargePrimeNeighbourMass indices)
  else 0

theorem familyLargePrimeNeighbourMass_nonneg
    (indices : Finset Family.FamilyIndex) (event : EscLeanChecks.SatEvent) :
    0 ≤ familyLargePrimeNeighbourMass indices event := by
  unfold familyLargePrimeNeighbourMass
  apply Finset.sum_nonneg
  intro other hother
  exact_mod_cast Family.familyEventWeightRat_nonneg other

theorem familyLargePrimeDelta_nonneg (indices : Finset Family.FamilyIndex) :
    0 ≤ familyLargePrimeDelta indices := by
  classical
  unfold familyLargePrimeDelta
  split_ifs with h
  · rcases h with ⟨event, hevent⟩
    exact le_trans (familyLargePrimeNeighbourMass_nonneg indices event)
      (Finset.le_sup' (familyLargePrimeNeighbourMass indices) hevent)
  · exact le_rfl

theorem familyLargePrimeNeighbourMass_le_delta
    (indices : Finset Family.FamilyIndex) {event : EscLeanChecks.SatEvent}
    (hevent : event ∈ Family.familyEvents indices) :
    familyLargePrimeNeighbourMass indices event ≤
      familyLargePrimeDelta indices := by
  classical
  rw [familyLargePrimeDelta, dif_pos ⟨event, hevent⟩]
  exact Finset.le_sup' (familyLargePrimeNeighbourMass indices) hevent

/-- Contribution from events sharing a nontrivial residual medium factor. -/
noncomputable def familyMediumNeighbourMass
    (indices : Finset Family.FamilyIndex)
    (event : EscLeanChecks.SatEvent) : ℝ :=
  ∑ other ∈ (Family.familyEvents indices).filter
      (fun other => other ≠ event ∧
        ¬ Nat.Coprime event.dPlus other.dPlus),
    (Family.familyEventWeightRat other : ℝ)

/-- Total event weight whose residual medium factor is divisible by `D`. -/
noncomputable def familyMediumDivisorMass
    (indices : Finset Family.FamilyIndex) (D : ℕ) : ℝ :=
  ∑ other ∈ (Family.familyEvents indices).filter
      (fun other => D ∣ other.dPlus),
    (Family.familyEventWeightRat other : ℝ)

theorem modularNeighbourMass_familyModularEvents
    (indices : Finset Family.FamilyIndex)
    (event : EscLeanChecks.SatEvent) :
    Inputs.modularNeighbourMass (familyModularEvents indices)
        (familyModularEvent event) =
      familyDependentNeighbourMass indices event := by
  classical
  unfold Inputs.modularNeighbourMass familyModularEvents
    familyDependentNeighbourMass Inputs.modularEventMass
  rw [Finset.sum_filter]
  rw [Finset.sum_image]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro other hother
    by_cases hdep : Inputs.modularDependent
        (familyModularEvent event) (familyModularEvent other)
    · simp [hdep, Family.familyEventWeightRat, familyModularEvent,
        Rat.cast_div]
    · simp [hdep]
  · intro left hleft right hright heq
    exact familyModularEvent_injective heq

/-- Exact manuscript split of one dependency neighborhood. -/
theorem familyDependentNeighbourMass_le_large_add_medium
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset Family.FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i)
    (event : EscLeanChecks.SatEvent)
    (hevent : event ∈ Family.familyEvents indices) :
    familyDependentNeighbourMass indices event ≤
      familyLargePrimeNeighbourMass indices event +
        familyMediumNeighbourMass indices event := by
  classical
  unfold familyDependentNeighbourMass familyLargePrimeNeighbourMass
    familyMediumNeighbourMass
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro other hother
  have hweight : 0 ≤ (Family.familyEventWeightRat other : ℝ) := by
    exact_mod_cast Family.familyEventWeightRat_nonneg other
  by_cases hdep : Inputs.modularDependent
      (familyModularEvent event) (familyModularEvent other)
  · have hotherFamily : other ∈ Family.familyEvents indices :=
      hother
    have hsplit := familyModularDependent_largePrime_or_medium
      P X Pz b indices hX hmem hevent hotherFamily hdep
    have hne : other ≠ event := by
      intro heq
      subst heq
      exact hdep.1 rfl
    rcases hsplit with hp | hmedium
    · simp [hdep, hne, hp.symm]
      split_ifs <;> linarith
    · simp [hdep, hne, hmedium]
      split_ifs <;> linarith
  ·
    simp only [hdep, if_false, zero_le]
    split_ifs <;> positivity

/-- Pointwise bounds for the two manuscript dependency mechanisms control the
actual maximal Suen neighborhood parameter. -/
theorem modularDelta_familyModularEvents_le
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset Family.FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i)
    (largeBound mediumBound : ℝ)
    (hlarge_nonneg : 0 ≤ largeBound)
    (hmedium_nonneg : 0 ≤ mediumBound)
    (hlarge : ∀ event ∈ Family.familyEvents indices,
      familyLargePrimeNeighbourMass indices event ≤ largeBound)
    (hmedium : ∀ event ∈ Family.familyEvents indices,
      familyMediumNeighbourMass indices event ≤ mediumBound) :
    Inputs.modularDelta (familyModularEvents indices) ≤
      largeBound + mediumBound := by
  classical
  unfold Inputs.modularDelta
  split_ifs with hnonempty
  · apply Finset.sup'_le hnonempty
    intro modularEvent hmodularEvent
    rcases Finset.mem_image.mp hmodularEvent with ⟨event, hevent, rfl⟩
    rw [modularNeighbourMass_familyModularEvents]
    calc
      familyDependentNeighbourMass indices event ≤
          familyLargePrimeNeighbourMass indices event +
            familyMediumNeighbourMass indices event :=
        familyDependentNeighbourMass_le_large_add_medium
          P X Pz b indices hX hmem event hevent
      _ ≤ largeBound + mediumBound :=
        add_le_add (hlarge event hevent) (hmedium event hevent)
  · linarith

/-- Union bound over the prime divisors of the fixed event's medium factor.
This is the exact finite combinatorial step preceding the event-tensor bound
in the manuscript's estimate for medium-prime neighbors. -/
theorem familyMediumNeighbourMass_le_sum_primeDivisorMass
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset Family.FamilyIndex)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i)
    (event : EscLeanChecks.SatEvent)
    (hevent : event ∈ Family.familyEvents indices) :
    familyMediumNeighbourMass indices event ≤
      ∑ ell ∈ event.dPlus.primeFactors,
        familyMediumDivisorMass indices ell := by
  classical
  unfold familyMediumNeighbourMass familyMediumDivisorMass
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro other hother
  have hweight : 0 ≤ (Family.familyEventWeightRat other : ℝ) := by
    exact_mod_cast Family.familyEventWeightRat_nonneg other
  by_cases hmedium : other ≠ event ∧
      ¬ Nat.Coprime event.dPlus other.dPlus
  · have heventPos : 0 < event.dPlus := by
      rcases Finset.mem_image.mp hevent with ⟨i, hi, rfl⟩
      exact (hmem i hi).dplus_pos
    have hgcdNe : Nat.gcd event.dPlus other.dPlus ≠ 1 := by
      simpa [Nat.Coprime] using hmedium.2
    rcases Nat.exists_prime_and_dvd hgcdNe with ⟨ell, hellPrime, hellGcd⟩
    have hellEvent : ell ∣ event.dPlus := (Nat.dvd_gcd_iff.mp hellGcd).1
    have hellOther : ell ∣ other.dPlus := (Nat.dvd_gcd_iff.mp hellGcd).2
    have hellMem : ell ∈ event.dPlus.primeFactors :=
      Nat.mem_primeFactors.mpr
        ⟨hellPrime, hellEvent, Nat.ne_of_gt heventPos⟩
    have hsingle := Finset.single_le_sum
      (s := event.dPlus.primeFactors)
      (f := fun ell => if ell ∣ other.dPlus then
        (Family.familyEventWeightRat other : ℝ) else 0)
      (fun ell hell => by dsimp; split_ifs <;> positivity) hellMem
    simpa [hmedium, hellOther] using hsingle
  · simp [hmedium]
    apply Finset.sum_nonneg
    intro ell hell
    split_ifs <;> positivity

/-- A divisor mass is the sum of the exact event-tensor residue fibers. -/
theorem familyMediumDivisorMass_eq_sum_residueMass
    (indices : Finset Family.FamilyIndex) (D : ℕ) (hD : 0 < D) :
    familyMediumDivisorMass indices D =
      ∑ c ∈ Finset.range D, (Family.familyResidueMassRat indices D c : ℝ) := by
  classical
  unfold familyMediumDivisorMass Family.familyResidueMassRat
  simp only [Finset.sum_filter, Rat.cast_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro event hevent
  simp only [apply_ite, Rat.cast_zero]
  by_cases hdiv : D ∣ event.dPlus
  · have hc : event.e % D ∈ Finset.range D :=
      Finset.mem_range.mpr (Nat.mod_lt _ hD)
    calc
      (if D ∣ event.dPlus then
          (Family.familyEventWeightRat event : ℝ)
        else 0) =
          (Family.familyEventWeightRat event : ℝ) := by
            simp [hdiv]
      _ = ∑ c ∈ Finset.range D,
          if D ∣ event.dPlus ∧ event.e % D = c then
            (Family.familyEventWeightRat event : ℝ)
          else 0 := by
            symm
            rw [Finset.sum_eq_single (event.e % D)]
            · simp [hdiv]
            · intro c hcMem hcne
              simp [hdiv, Ne.symm hcne]
            · exact fun hnot => (hnot hc).elim
  · simp [hdiv]

theorem familyMediumDivisorMass_le_card_mul
    (indices : Finset Family.FamilyIndex) (D : ℕ) (A : ℝ)
    (hD : 0 < D)
    (hresidue : ∀ c < D,
      (Family.familyResidueMassRat indices D c : ℝ) ≤ A) :
    familyMediumDivisorMass indices D ≤ (D : ℝ) * A := by
  rw [familyMediumDivisorMass_eq_sum_residueMass indices D hD]
  calc
    (∑ c ∈ Finset.range D,
        (Family.familyResidueMassRat indices D c : ℝ)) ≤
      ∑ _c ∈ Finset.range D, A := by
        apply Finset.sum_le_sum
        intro c hc
        exact hresidue c (Finset.mem_range.mp hc)
    _ = (D : ℝ) * A := by simp

/-- Tensor bound `B_(D,c) <= K*mu/D^2` summed over residue classes. -/
theorem familyMediumDivisorMass_le_of_residue_square_bound
    (indices : Finset Family.FamilyIndex) (D : ℕ) (K mass : ℝ)
    (hD : 0 < D)
    (hresidue : ∀ c < D,
      (Family.familyResidueMassRat indices D c : ℝ) ≤
        K * mass / (D : ℝ) ^ 2) :
    familyMediumDivisorMass indices D ≤ K * mass / (D : ℝ) := by
  have hsum := familyMediumDivisorMass_le_card_mul indices D
    (K * mass / (D : ℝ) ^ 2) hD hresidue
  calc
    familyMediumDivisorMass indices D ≤
        (D : ℝ) * (K * mass / (D : ℝ) ^ 2) := hsum
    _ = K * mass / (D : ℝ) := by
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)]
      ring

/-- Exact event-tensor consequence for one medium-prime neighborhood. -/
theorem familyMediumNeighbourMass_le_mass_mul_primeRecipSum
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset Family.FamilyIndex)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i)
    (event : EscLeanChecks.SatEvent)
    (hevent : event ∈ Family.familyEvents indices)
    (K mass : ℝ)
    (hresidue : ∀ ell ∈ event.dPlus.primeFactors, ∀ c < ell,
      (Family.familyResidueMassRat indices ell c : ℝ) ≤
        K * mass / (ell : ℝ) ^ 2) :
    familyMediumNeighbourMass indices event ≤
      K * mass *
        ∑ ell ∈ event.dPlus.primeFactors, (1 : ℝ) / (ell : ℝ) := by
  calc
    familyMediumNeighbourMass indices event ≤
        ∑ ell ∈ event.dPlus.primeFactors,
          familyMediumDivisorMass indices ell :=
      familyMediumNeighbourMass_le_sum_primeDivisorMass
        P X Pz b indices hmem event hevent
    _ ≤ ∑ ell ∈ event.dPlus.primeFactors,
        K * mass / (ell : ℝ) := by
      apply Finset.sum_le_sum
      intro ell hell
      have hellPrime : Nat.Prime ell := (Nat.mem_primeFactors.mp hell).1
      exact familyMediumDivisorMass_le_of_residue_square_bound
        indices ell K mass hellPrime.pos (hresidue ell hell)
    _ = K * mass *
        ∑ ell ∈ event.dPlus.primeFactors, (1 : ℝ) / (ell : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ell hell
      ring

/-- The medium-neighbor contribution at the paper's rough cutoff.  Once the
residue-tensor estimate is supplied, the remaining rough-prime sum is bounded
entirely by the checked finite arithmetic of the actual family. -/
theorem actualRoughFamily_mediumNeighbourMass_le_floorScale
    (P : Params) (X : ℝ) (b : ℕ) (indices : Finset Family.FamilyIndex)
    (hXexp : Real.exp 1 ≤ X)
    (hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X (Inputs.roughModulus X) b i)
    (event : EscLeanChecks.SatEvent)
    (hevent : event ∈ Family.familyEvents indices)
    (K mass : ℝ)
    (hK : 0 ≤ K) (hmass : 0 ≤ mass)
    (hresidue : ∀ ell ∈ event.dPlus.primeFactors, ∀ c < ell,
      (Family.familyResidueMassRat indices ell c : ℝ) ≤
        K * mass / (ell : ℝ) ^ 2) :
    familyMediumNeighbourMass indices event ≤
      K * mass * paperIncrementFloorScale P X := by
  have hX : 1 < X :=
    lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hXexp
  have hprimeSum :
      (∑ ell ∈ event.dPlus.primeFactors, (1 : ℝ) / (ell : ℝ)) ≤
        (Real.log (YScale P X) /
          Real.log (((⌊zScale X⌋₊ + 1 : ℕ) : ℝ))) /
            (((⌊zScale X⌋₊ + 1 : ℕ) : ℝ)) := by
    rcases Finset.mem_image.mp hevent with ⟨i, hi, hieq⟩
    subst event
    exact (hmem i hi).dplus_primeFactors_recip_sum_le_YScale
      hX (two_le_succ_floor_zScale hXexp)
      (fun p hp hlt => prime_dvd_roughModulus_of_lt_succ_floor hp hlt)
  calc
    familyMediumNeighbourMass indices event ≤
        K * mass *
          ∑ ell ∈ event.dPlus.primeFactors, (1 : ℝ) / (ell : ℝ) :=
      familyMediumNeighbourMass_le_mass_mul_primeRecipSum
        P X (Inputs.roughModulus X) b indices hmem event hevent K mass hresidue
    _ ≤ K * mass * paperIncrementFloorScale P X := by
      exact mul_le_mul_of_nonneg_left hprimeSum (mul_nonneg hK hmass)

/-- Complete actual-family medium-neighbor estimate, with the residue tensor
discharged by the already formalized standard-input route. -/
theorem actualPaperFamily_mediumNeighbourMass_le_floorScale
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ K : ℝ, ∃ X₀ : ℝ, 0 < K ∧ ∀ X : ℝ,
      X₀ ≤ X → Real.exp 1 ≤ X →
      ∀ b : ℕ, Nat.Coprime b (Inputs.roughModulus X) →
      ∀ event ∈ Family.familyEvents
        (Family.familyIndexFinset P X (Inputs.roughModulus X) b),
        familyMediumNeighbourMass
            (Family.familyIndexFinset P X (Inputs.roughModulus X) b) event ≤
          K * (Family.familyIndexMassRat
            (Family.familyIndexFinset P X (Inputs.roughModulus X) b) : ℝ) *
              paperIncrementFloorScale P X := by
  rcases actualPaperFamily_residueMassRat_le_indexMassRat_div_square P with
    ⟨Kq, X₀, hKq, htensor⟩
  refine ⟨(Kq : ℝ), X₀, by exact_mod_cast hKq, ?_⟩
  intro X hX hXexp b hbcop event hevent
  let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
  have hXgt : 1 < X :=
    lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hXexp
  have hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X (Inputs.roughModulus X) b i := by
    intro i hi
    exact (Family.mem_familyIndexFinset_iff P X
      (Inputs.roughModulus X) b i (lt_trans zero_lt_one hXgt)).1 hi
  apply actualRoughFamily_mediumNeighbourMass_le_floorScale
    P X b indices hXexp hmem event hevent (Kq : ℝ)
      (Family.familyIndexMassRat indices : ℝ)
  · exact_mod_cast hKq.le
  · have hmassQ : 0 ≤ Family.familyIndexMassRat indices := by
      unfold Family.familyIndexMassRat
      apply Finset.sum_nonneg
      intro i hi
      unfold Family.FamilyIndex.wRat
      positivity
    exact_mod_cast hmassQ
  · intro ell hell c hc
    rcases Finset.mem_image.mp hevent with ⟨i, hi, hieq⟩
    have hellDplus : ell ∣ i.dplus := by
      simpa [← hieq] using (Nat.mem_primeFactors.mp hell).2.1
    have hellPrime : Nat.Prime ell := (Nat.mem_primeFactors.mp hell).1
    have hellOdd : Odd ell :=
      Odd.of_dvd_nat (hmem i hi).dplus_odd hellDplus
    have hellCop : Nat.Coprime ell (Inputs.roughModulus X) :=
      Nat.Coprime.coprime_dvd_left hellDplus (hmem i hi).dplus_coprime_Pz
    have hellLeDplus : ell ≤ i.dplus :=
      Nat.le_of_dvd (hmem i hi).dplus_pos hellDplus
    have hellLeY : (ell : ℝ) ≤ YScale P X := by
      exact le_trans (by exact_mod_cast hellLeDplus)
        (hmem i hi).dplus_le_YScale
    have hq := htensor X hX hXgt b hbcop ell c hellPrime.one_le
      hellPrime.squarefree hellOdd hellCop hellLeY
    exact_mod_cast hq

/-- Actual Suen neighborhood parameter reduced to the one remaining
large-prime-neighbor carrier plus the completely discharged medium-prime term. -/
theorem actualPaperFamily_modularDelta_le_largePrime_add_floorScale
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ K : ℝ, ∃ X₀ : ℝ, 0 < K ∧ ∀ X : ℝ,
      X₀ ≤ X → Real.exp 2 ≤ X →
      ∀ b : ℕ, Nat.Coprime b (Inputs.roughModulus X) →
      Inputs.modularDelta
          (familyModularEvents
            (Family.familyIndexFinset P X (Inputs.roughModulus X) b)) ≤
        familyLargePrimeDelta
            (Family.familyIndexFinset P X (Inputs.roughModulus X) b) +
          K * (Family.familyIndexMassRat
            (Family.familyIndexFinset P X (Inputs.roughModulus X) b) : ℝ) *
              paperIncrementFloorScale P X := by
  rcases actualPaperFamily_mediumNeighbourMass_le_floorScale P with
    ⟨K, X₀, hK, hmedium⟩
  refine ⟨K, X₀, hK, ?_⟩
  intro X hX hXexp b hbcop
  have hXexp1 : Real.exp 1 ≤ X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)) hXexp
  let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
  have hXgt : 1 < X :=
    lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hXexp
  have hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X (Inputs.roughModulus X) b i := by
    intro i hi
    exact (Family.mem_familyIndexFinset_iff P X
      (Inputs.roughModulus X) b i (lt_trans zero_lt_one hXgt)).1 hi
  apply modularDelta_familyModularEvents_le P X (Inputs.roughModulus X) b
    indices hXgt hmem (familyLargePrimeDelta indices)
      (K * (Family.familyIndexMassRat indices : ℝ) *
        paperIncrementFloorScale P X)
  · exact familyLargePrimeDelta_nonneg indices
  · have hmediumScale : 0 ≤ paperIncrementFloorScale P X :=
      paperIncrementFloorScale_nonneg P hXexp
    have hmassQ : 0 ≤ Family.familyIndexMassRat indices := by
      unfold Family.familyIndexMassRat
      apply Finset.sum_nonneg
      intro i hi
      unfold Family.FamilyIndex.wRat
      positivity
    exact mul_nonneg (mul_nonneg hK.le (by exact_mod_cast hmassQ)) hmediumScale
  · intro event hevent
    exact familyLargePrimeNeighbourMass_le_delta indices hevent
  · intro event hevent
    exact hmedium X hX hXexp1 b hbcop event hevent

/-! ## Exact pair-correlation carrier -/

/-- Ordered reciprocal-LCM mass of distinct compatible pairs that share a
nontrivial residual medium factor. -/
noncomputable def familyCompatibleMediumPairMass
    (indices : Finset Family.FamilyIndex) : ℝ :=
  ∑ event ∈ Family.familyEvents indices,
    ∑ other ∈ (Family.familyEvents indices).filter (fun other =>
      other ≠ event ∧ EscLeanChecks.satEventCompatible event other ∧
        ¬ Nat.Coprime event.dPlus other.dPlus),
      (Family.familySubsetLcmRecipRat {event, other} : ℝ)

/-- Pull the modular ordered dependency sum back to the actual certificate-event
carrier. -/
theorem modularDependencyMass_familyModularEvents
    (indices : Finset Family.FamilyIndex) :
    Inputs.modularDependencyMass (familyModularEvents indices) =
      ∑ event ∈ Family.familyEvents indices,
        ∑ other ∈ (Family.familyEvents indices).filter (fun other =>
          Inputs.modularDependent
            (familyModularEvent event) (familyModularEvent other)),
          Inputs.modularPairMass
            (familyModularEvent event) (familyModularEvent other) := by
  classical
  unfold Inputs.modularDependencyMass familyModularEvents
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro event hevent
    rw [Finset.sum_filter]
    rw [Finset.sum_image]
    · rw [Finset.sum_filter]
    · intro left hleft right hright heq
      exact familyModularEvent_injective heq
  · intro left hleft right hright heq
    exact familyModularEvent_injective heq

/-- The exact modular correlation parameter is the manuscript's ordered
compatible medium-pair reciprocal-LCM sum.  Incompatible pairs have zero
intersection; compatible distinct pairs cannot share their selected large
prime, so every dependent compatible pair shares a medium factor. -/
theorem modularDependencyMass_eq_familyCompatibleMediumPairMass
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset Family.FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i) :
    Inputs.modularDependencyMass (familyModularEvents indices) =
      familyCompatibleMediumPairMass indices := by
  classical
  rw [modularDependencyMass_familyModularEvents]
  unfold familyCompatibleMediumPairMass
  apply Finset.sum_congr rfl
  intro event hevent
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro other hother
  have heventMod := Family.familyEvents_residualModulus_pos
    P X Pz b indices hmem event hevent
  have hotherMod := Family.familyEvents_residualModulus_pos
    P X Pz b indices hmem other hother
  by_cases hcompat : EscLeanChecks.satEventCompatible event other
  · by_cases hne : other ≠ event
    · have hpne : event.p ≠ other.p :=
        Family.familyEvents_largePrime_ne_of_compatible_ne
          P X Pz b indices hX hmem hevent hother hcompat (Ne.symm hne)
      by_cases hmedium : ¬ Nat.Coprime event.dPlus other.dPlus
      · have hdep : Inputs.modularDependent
            (familyModularEvent event) (familyModularEvent other) := by
          constructor
          · intro heq
            exact hne (familyModularEvent_injective heq).symm
          · intro hcop
            have hdplusCop : Nat.Coprime event.dPlus other.dPlus :=
              Nat.Coprime.coprime_dvd_right
                (dvd_mul_right other.dPlus other.p)
                (Nat.Coprime.coprime_dvd_left
                  (dvd_mul_right event.dPlus event.p) hcop)
            exact hmedium hdplusCop
        rw [if_pos hdep, if_pos ⟨hne, hcompat, hmedium⟩]
        simpa [hcompat] using modularPairMass_familyModularEvent
          event other heventMod hotherMod
      · have hnotdep : ¬ Inputs.modularDependent
            (familyModularEvent event) (familyModularEvent other) := by
          intro hdep
          rcases familyModularDependent_largePrime_or_medium
              P X Pz b indices hX hmem hevent hother hdep with hp | hm
          · exact hpne hp
          · exact hm (not_not.mp hmedium)
        simp [hnotdep, hmedium]
    · have heq : other = event := not_ne_iff.mp hne
      subst other
      simp [Inputs.modularDependent]
  · have hpairZero : Inputs.modularPairMass
          (familyModularEvent event) (familyModularEvent other) = 0 := by
      rw [modularPairMass_familyModularEvent event other heventMod hotherMod]
      simp [hcompat]
    simp [hcompat, hpairZero]

/-- Reciprocal-LCM mass of a singleton is its event weight. -/
theorem familySingletonCongruenceLcm
    (event : EscLeanChecks.SatEvent) :
    EscLeanChecks.congruenceLcm
      (EscLeanChecks.satEventResidualHitRows
        ({event} : Finset EscLeanChecks.SatEvent).toList) =
      EscLeanChecks.conditionalModulus event.dPlus event.p := by
  classical
  simpa [EscLeanChecks.congruenceLcm,
    EscLeanChecks.satEventResidualHitRows, Nat.lcm_one_right] using
    (EscLeanChecks.congruenceLcm_satEventResidualHitRows_insert_eq_lcm
      (∅ : Finset EscLeanChecks.SatEvent) event)

theorem familySubsetLcmRecipRat_singleton
    (event : EscLeanChecks.SatEvent) :
    Family.familySubsetLcmRecipRat {event} =
      Family.familyEventWeightRat event := by
  classical
  unfold Family.familySubsetLcmRecipRat Family.familyEventWeightRat
  rw [familySingletonCongruenceLcm event]

/-- Exact two-event reciprocal-LCM factorization through the increment gcd. -/
theorem familyPairLcmRecipRat_eq_weights_mul_gcd
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset Family.FamilyIndex)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i)
    (event other : EscLeanChecks.SatEvent)
    (hevent : event ∈ Family.familyEvents indices)
    (hother : other ∈ Family.familyEvents indices) :
    Family.familySubsetLcmRecipRat {event, other} =
      Family.familyEventWeightRat event *
        Family.familyEventWeightRat other *
          (Family.familyIncrementG {event} other : ℚ) := by
  have hratio := Family.familyExtensionRatio_eq_weight_mul_gcd
    P X Pz b indices hmem {event}
      (by
        intro x hx
        have hxeq : x = event := Finset.mem_singleton.mp hx
        subst x
        exact hevent) other hother
  rw [show insert other {event} = ({event, other} :
      Finset EscLeanChecks.SatEvent) by ext x; simp [or_comm],
    familySubsetLcmRecipRat_singleton event] at hratio
  have hweightPos : 0 < Family.familyEventWeightRat event :=
    Family.familyEventWeightRat_pos_of_mem P X Pz b indices hmem hevent
  have hweightNe : Family.familyEventWeightRat event ≠ 0 := ne_of_gt hweightPos
  field_simp [hweightNe] at hratio
  nlinarith

/-- Finite weighted `g>1` divisor switch.  Since
`g <= 2(g-1)` for integral `g>1`, the dependent part of a weighted gcd sum is
at most twice its `D>=2` totient-divisor tail. -/
theorem weighted_gcd_gt_one_le_two_totient_tail
    {α : Type} [DecidableEq α]
    (U : Finset α) (w : α → ℚ) (g : α → ℕ) (B : ℕ)
    (hB : 1 ≤ B)
    (hw : ∀ i ∈ U, 0 ≤ w i)
    (hgpos : ∀ i ∈ U, 0 < g i)
    (hgle : ∀ i ∈ U, g i ≤ B) :
    (∑ i ∈ U.filter (fun i => 1 < g i), w i * (g i : ℚ)) ≤
      2 * ∑ D ∈ Finset.Icc 2 B, (Nat.totient D : ℚ) *
        ∑ i ∈ U.filter (fun i => D ∣ g i), w i := by
  classical
  let V := U.filter (fun i => 1 < g i)
  have hVsub : V ⊆ U := Finset.filter_subset _ _
  have hfull := EscLeanChecks.weighted_sum_eq_totient_divisor_mass
    V w g B
      (fun i hi => hgpos i (hVsub hi))
      (fun i hi => hgle i (hVsub hi))
  have hIcc : Finset.Icc 1 B = insert 1 (Finset.Icc 2 B) := by
    ext D
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have honeNotMem : 1 ∉ Finset.Icc 2 B := by simp
  rw [hIcc, Finset.sum_insert honeNotMem] at hfull
  simp at hfull
  let tailV : ℚ := ∑ D ∈ Finset.Icc 2 B, (Nat.totient D : ℚ) *
    ∑ i ∈ V.filter (fun i => D ∣ g i), w i
  have hfullSplit : (∑ i ∈ V, w i * (g i : ℚ)) =
      (∑ i ∈ V, w i) + tailV := by
    simpa [tailV] using hfull
  have htwobase : 2 * (∑ i ∈ V, w i) ≤
      ∑ i ∈ V, w i * (g i : ℚ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hiU : i ∈ U := hVsub hi
    have hgi : 2 ≤ g i := by
      have := (Finset.mem_filter.mp hi).2
      omega
    have hgiQ : (2 : ℚ) ≤ (g i : ℚ) := by exact_mod_cast hgi
    have hwI := hw i hiU
    nlinarith
  have hbaseTail : (∑ i ∈ V, w i) ≤ tailV := by
    rw [hfullSplit] at htwobase
    linarith
  have hfull_le_two_tailV : (∑ i ∈ V, w i * (g i : ℚ)) ≤
      2 * tailV := by
    rw [hfullSplit]
    linarith
  have htailMono : tailV ≤
      ∑ D ∈ Finset.Icc 2 B, (Nat.totient D : ℚ) *
        ∑ i ∈ U.filter (fun i => D ∣ g i), w i := by
    unfold tailV
    apply Finset.sum_le_sum
    intro D hD
    apply mul_le_mul_of_nonneg_left
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        have hiData := Finset.mem_filter.mp hi
        exact Finset.mem_filter.mpr ⟨hVsub hiData.1, hiData.2⟩
      · intro i hiU hiNot
        exact hw i (Finset.mem_filter.mp hiU).1
    · positivity
  exact hfull_le_two_tailV.trans (mul_le_mul_of_nonneg_left htailMono (by norm_num))

/-- For one fixed actual event, the compatible dependent pair mass is bounded
by twice its event weight times the complete singleton increment tail. -/
theorem familyCompatibleMediumPairMass_fixed_le_two_weight_mul_tail
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset Family.FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i)
    (event : EscLeanChecks.SatEvent)
    (hevent : event ∈ Family.familyEvents indices) :
    (∑ other ∈ (Family.familyEvents indices).filter (fun other =>
      other ≠ event ∧ EscLeanChecks.satEventCompatible event other ∧
        ¬ Nat.Coprime event.dPlus other.dPlus),
      Family.familySubsetLcmRecipRat {event, other}) ≤
      2 * Family.familyEventWeightRat event *
        Family.familyIncrementTailRat indices {event} ⌊X⌋₊ := by
  classical
  let U := (Family.familyEvents indices).filter (fun other =>
    other ≠ event ∧ EscLeanChecks.satEventCompatible event other ∧
      ¬ Nat.Coprime event.dPlus other.dPlus)
  have hsub : ({event} : Finset EscLeanChecks.SatEvent) ⊆
      Family.familyEvents indices := by
    intro x hx
    have hxeq : x = event := Finset.mem_singleton.mp hx
    subst x
    exact hevent
  have hUext : U ⊆ Family.familyCompatibleExtensions indices {event} := by
    intro other hother
    rcases Finset.mem_filter.mp hother with ⟨hotherFamily, hne, hcompat, hmedium⟩
    rw [Family.familyCompatibleExtensions]
    refine Finset.mem_filter.mpr ⟨hotherFamily, ?_, ?_⟩
    · simpa using hne
    · intro x hx y hy hxy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hxy rfl).elim
      · simpa [EscLeanChecks.satEventCompatible,
          EscLeanChecks.residueCompatible, Nat.gcd_comm] using hcompat.symm
      · exact hcompat
      · exact (hxy rfl).elim
  have hgpos : ∀ other ∈ U,
      0 < Family.familyIncrementG {event} other := by
    intro other hother
    apply Nat.gcd_pos_of_pos_right
    rcases Finset.mem_filter.mp hother with ⟨hotherFamily, _⟩
    exact Family.familyEvents_residualModulus_pos
      P X Pz b indices hmem other hotherFamily
  have hggt : ∀ other ∈ U,
      1 < Family.familyIncrementG {event} other := by
    intro other hother
    rcases Finset.mem_filter.mp hother with
      ⟨hotherFamily, hne, hcompat, hmedium⟩
    have hnotCoprimeQ : ¬ Nat.Coprime
        (EscLeanChecks.conditionalModulus event.dPlus event.p)
        (EscLeanChecks.conditionalModulus other.dPlus other.p) := by
      intro hcop
      apply hmedium
      exact Nat.Coprime.coprime_dvd_right
        (dvd_mul_right other.dPlus other.p)
        (Nat.Coprime.coprime_dvd_left
          (dvd_mul_right event.dPlus event.p) hcop)
    have hgNe : Family.familyIncrementG {event} other ≠ 1 := by
      intro hg
      apply hnotCoprimeQ
      rw [Nat.coprime_iff_gcd_eq_one]
      unfold Family.familyIncrementG at hg
      rw [familySingletonCongruenceLcm event, Nat.gcd_comm] at hg
      simpa [Nat.gcd_comm] using hg
    have hgPositive := hgpos other hother
    omega
  have hgle : ∀ other ∈ U,
      Family.familyIncrementG {event} other ≤ ⌊X⌋₊ := by
    intro other hother
    have hdiv := Family.familyCompatibleExtension_gcd_dvd_dPlus
      P X Pz b indices hX hmem {event} hsub other (hUext hother)
    rcases Finset.mem_filter.mp hother with ⟨hotherFamily, _⟩
    rcases Finset.mem_image.mp hotherFamily with ⟨i, hi, rfl⟩
    exact (Nat.le_of_dvd (hmem i hi).dplus_pos hdiv).trans
      ((hmem i hi).dplus_le_floor_X hX)
  have hB : 1 ≤ ⌊X⌋₊ := Nat.floor_pos.mpr hX.le
  have hweighted := weighted_gcd_gt_one_le_two_totient_tail
    U Family.familyEventWeightRat (Family.familyIncrementG {event}) ⌊X⌋₊ hB
      (fun other hother => Family.familyEventWeightRat_nonneg other)
      hgpos hgle
  have hfilter : U.filter (fun other =>
      1 < Family.familyIncrementG {event} other) = U := by
    apply Finset.filter_eq_self.mpr
    exact hggt
  rw [hfilter] at hweighted
  have htailMono :
      (∑ D ∈ Finset.Icc 2 ⌊X⌋₊, (Nat.totient D : ℚ) *
        ∑ other ∈ U.filter (fun other =>
          D ∣ Family.familyIncrementG {event} other),
          Family.familyEventWeightRat other) ≤
        Family.familyIncrementTailRat indices {event} ⌊X⌋₊ := by
    unfold Family.familyIncrementTailRat Family.familyIncrementDivisorMassRat
      Family.familyIncrementDivisorEvents
    apply Finset.sum_le_sum
    intro D hD
    apply mul_le_mul_of_nonneg_left
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro other hother
        have hdata := Finset.mem_filter.mp hother
        exact Finset.mem_filter.mpr ⟨hUext hdata.1, hdata.2⟩
      · intro other hother hnot
        exact Family.familyEventWeightRat_nonneg other
    · positivity
  have hpairs :
      (∑ other ∈ U, Family.familySubsetLcmRecipRat {event, other}) =
        Family.familyEventWeightRat event *
          ∑ other ∈ U, Family.familyEventWeightRat other *
            (Family.familyIncrementG {event} other : ℚ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro other hother
    rcases Finset.mem_filter.mp hother with ⟨hotherFamily, _⟩
    simpa [mul_assoc] using familyPairLcmRecipRat_eq_weights_mul_gcd
      P X Pz b indices hmem event other hevent hotherFamily
  change (∑ other ∈ U, Family.familySubsetLcmRecipRat {event, other}) ≤ _
  rw [hpairs]
  have hweightNonneg : 0 ≤ Family.familyEventWeightRat event :=
    Family.familyEventWeightRat_nonneg event
  calc
    Family.familyEventWeightRat event *
        (∑ other ∈ U, Family.familyEventWeightRat other *
          (Family.familyIncrementG {event} other : ℚ)) ≤
      Family.familyEventWeightRat event *
        (2 * ∑ D ∈ Finset.Icc 2 ⌊X⌋₊, (Nat.totient D : ℚ) *
          ∑ other ∈ U.filter (fun other =>
            D ∣ Family.familyIncrementG {event} other),
            Family.familyEventWeightRat other) :=
      mul_le_mul_of_nonneg_left hweighted hweightNonneg
    _ ≤ Family.familyEventWeightRat event *
        (2 * Family.familyIncrementTailRat indices {event} ⌊X⌋₊) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htailMono (by norm_num)) hweightNonneg
    _ = 2 * Family.familyEventWeightRat event *
        Family.familyIncrementTailRat indices {event} ⌊X⌋₊ := by ring

/-- Direct tensor bound for the complete increment tail.  This isolates the
`D>=2` part itself, rather than bounding it indirectly through the full
one-step increment. -/
theorem familyIncrementTailRat_le_indexMass_mul_classTail_of_residueTensor
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset Family.FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i)
    (old : Finset EscLeanChecks.SatEvent)
    (hsub : old ⊆ Family.familyEvents indices)
    (K : ℚ) (hK : 0 ≤ K)
    (htensor : ∀ D ∈ Finset.Icc 2 ⌊X⌋₊,
      ∀ c ∈ Family.familyIncrementResidueClasses indices old D,
        Family.familyResidueMassRat indices D c ≤
          K * Family.familyIndexMassRat indices / (D : ℚ) ^ 2) :
    Family.familyIncrementTailRat indices old ⌊X⌋₊ ≤
      Family.familyIndexMassRat indices *
        ∑ D ∈ Finset.Icc 2 ⌊X⌋₊,
          (K * Family.familyIncrementClassProductRat old D) / (D : ℚ) := by
  have hmassNonneg : 0 ≤ Family.familyIndexMassRat indices := by
    unfold Family.familyIndexMassRat
    apply Finset.sum_nonneg
    intro i hi
    unfold Family.FamilyIndex.wRat
    positivity
  apply Family.familyIncrementTailRat_le_mass_mul_classTail
    indices old ⌊X⌋₊ (Family.familyIndexMassRat indices)
      (fun D => K * Family.familyIncrementClassProductRat old D)
      hmassNonneg
  · intro D hD
    apply mul_nonneg hK
    unfold Family.familyIncrementClassProductRat
    split_ifs <;> positivity
  · intro D hD
    have hdivisor :=
      Family.familyIncrementDivisorMassRat_le_card_mul_of_residueMass_le
        indices old D
          (K * Family.familyIndexMassRat indices / (D : ℚ) ^ 2)
          (fun c hc =>
            (Family.familyIncrementResidueMassRat_le_familyResidueMassRat
              P X Pz b indices hX hmem old hsub D c).trans
                (htensor D hD c hc))
    have hclass := Family.familyIncrementResidueClasses_card_le_classProductRat
      P X Pz b indices hX hmem old hsub D
    have hMnonneg : 0 ≤
        K * Family.familyIndexMassRat indices / (D : ℚ) ^ 2 := by
      positivity
    calc
      Family.familyIncrementDivisorMassRat indices old D ≤
          ((Family.familyIncrementResidueClasses indices old D).card : ℚ) *
            (K * Family.familyIndexMassRat indices / (D : ℚ) ^ 2) :=
        hdivisor
      _ ≤ Family.familyIncrementClassProductRat old D *
            (K * Family.familyIndexMassRat indices / (D : ℚ) ^ 2) :=
        mul_le_mul_of_nonneg_right hclass hMnonneg
      _ = Family.familyIndexMassRat indices *
          (K * Family.familyIncrementClassProductRat old D) / (D : ℚ) ^ 2 := by
        ring

/-- Concrete singleton increment-tail bound for the actual family.  The only
remaining scalar is the explicit finite Euler loss at rank two. -/
theorem actualPaperFamily_singletonIncrementTail_le_of_scalar
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ K : ℚ, ∃ X₀ : ℝ, 0 < K ∧ ∀ X : ℝ,
      X₀ ≤ X → Real.exp 2 ≤ X →
      ∀ b : ℕ, Nat.Coprime b (Inputs.roughModulus X) →
      ∀ ε : ℚ, 0 ≤ ε →
      (K : ℝ) *
        (Real.exp (2 * paperIncrementFloorScale P X) - 1) ≤ (ε : ℝ) →
      ∀ event ∈ Family.familyEvents
        (Family.familyIndexFinset P X (Inputs.roughModulus X) b),
        Family.familyIncrementTailRat
            (Family.familyIndexFinset P X (Inputs.roughModulus X) b)
            {event} ⌊X⌋₊ ≤
          Family.familyIndexMassRat
            (Family.familyIndexFinset P X (Inputs.roughModulus X) b) * ε := by
  rcases actualPaperFamily_residueMassRat_le_indexMassRat_div_square P with
    ⟨K, X₀, hK, htensor⟩
  refine ⟨K, X₀, hK, ?_⟩
  intro X hX hXexp b hbcop ε hε hscalar event hevent
  let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
  have hXgt : 1 < X :=
    lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num))
      (le_trans (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)) hXexp)
  have hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X (Inputs.roughModulus X) b i := by
    intro i hi
    exact (Family.mem_familyIndexFinset_iff P X
      (Inputs.roughModulus X) b i (lt_trans zero_lt_one hXgt)).1 hi
  have hsub : ({event} : Finset EscLeanChecks.SatEvent) ⊆
      Family.familyEvents indices := by
    intro x hx
    have hxeq : x = event := Finset.mem_singleton.mp hx
    subst x
    exact hevent
  have htail := familyIncrementTailRat_le_indexMass_mul_classTail_of_residueTensor
    P X (Inputs.roughModulus X) b indices hXgt hmem {event} hsub K hK.le
      (by
        intro D hD c hc
        have hdata := actualPaperFamily_incrementResidueClass_modulus_data
          P X b D c hXgt {event} hsub hc
        exact htensor X hX hXgt b hbcop D c hdata.1 hdata.2.1
          hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2)
  have hold : ({event} : Finset EscLeanChecks.SatEvent) ∈
      Family.familyCompatibleSubsetsOfCard indices 1 := by
    rw [Family.familyCompatibleSubsetsOfCard]
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_powersetCard.mpr ⟨hsub, by simp⟩
    · intro x hx y hy hxy
      simp only [Finset.mem_singleton] at hx hy
      subst x
      subst y
      exact (hxy rfl).elim
  have hclassTail := actualPaperFamily_incrementTailRat_le_of_rank_scale
    P X b 2 2 K ε hXexp hK.le (by norm_num) (by norm_num)
      {event} (by simpa using hold) (by simpa using hscalar)
  exact htail.trans (mul_le_mul_of_nonneg_left hclassTail (by
    unfold Family.familyIndexMassRat
    apply Finset.sum_nonneg
    intro i hi
    unfold Family.FamilyIndex.wRat
    positivity))

/-- Concrete ordered pair-correlation bound for the actual modular family.
The pair parameter is at most `2*mu^2*epsilon`, where `epsilon` is the explicit
rank-two Euler loss. -/
theorem actualPaperFamily_modularDependencyMass_le_of_scalar
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ K : ℚ, ∃ X₀ : ℝ, 0 < K ∧ ∀ X : ℝ,
      X₀ ≤ X → Real.exp 2 ≤ X →
      ∀ b : ℕ, Nat.Coprime b (Inputs.roughModulus X) →
      ∀ ε : ℚ, 0 ≤ ε →
      (K : ℝ) *
        (Real.exp (2 * paperIncrementFloorScale P X) - 1) ≤ (ε : ℝ) →
      Inputs.modularDependencyMass
          (familyModularEvents
            (Family.familyIndexFinset P X (Inputs.roughModulus X) b)) ≤
        2 * (Family.familyIndexMassRat
          (Family.familyIndexFinset P X (Inputs.roughModulus X) b) : ℝ) ^ 2 *
            (ε : ℝ) := by
  rcases actualPaperFamily_singletonIncrementTail_le_of_scalar P with
    ⟨K, X₀, hK, hsingleton⟩
  refine ⟨K, X₀, hK, ?_⟩
  intro X hX hXexp b hbcop ε hε hscalar
  let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
  let μq := Family.familyIndexMassRat indices
  have hXgt : 1 < X :=
    lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num))
      (le_trans (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)) hXexp)
  have hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X (Inputs.roughModulus X) b i := by
    intro i hi
    exact (Family.mem_familyIndexFinset_iff P X
      (Inputs.roughModulus X) b i (lt_trans zero_lt_one hXgt)).1 hi
  rw [modularDependencyMass_eq_familyCompatibleMediumPairMass
    P X (Inputs.roughModulus X) b indices hXgt hmem]
  unfold familyCompatibleMediumPairMass
  calc
    (∑ event ∈ Family.familyEvents indices,
      ∑ other ∈ (Family.familyEvents indices).filter (fun other =>
        other ≠ event ∧ EscLeanChecks.satEventCompatible event other ∧
          ¬ Nat.Coprime event.dPlus other.dPlus),
        (Family.familySubsetLcmRecipRat {event, other} : ℝ)) ≤
      ∑ event ∈ Family.familyEvents indices,
        2 * (Family.familyEventWeightRat event : ℝ) * (μq : ℝ) * (ε : ℝ) := by
      apply Finset.sum_le_sum
      intro event hevent
      have hfixedQ := familyCompatibleMediumPairMass_fixed_le_two_weight_mul_tail
        P X (Inputs.roughModulus X) b indices hXgt hmem event hevent
      have htailQ := hsingleton X hX hXexp b hbcop ε hε hscalar event hevent
      have hfixedR :
          ((∑ other ∈ (Family.familyEvents indices).filter (fun other =>
              other ≠ event ∧ EscLeanChecks.satEventCompatible event other ∧
                ¬ Nat.Coprime event.dPlus other.dPlus),
              Family.familySubsetLcmRecipRat {event, other}) : ℚ) ≤
            2 * Family.familyEventWeightRat event * μq * ε := by
        calc
          _ ≤ 2 * Family.familyEventWeightRat event *
              Family.familyIncrementTailRat indices {event} ⌊X⌋₊ := hfixedQ
          _ ≤ 2 * Family.familyEventWeightRat event * (μq * ε) := by
            exact mul_le_mul_of_nonneg_left htailQ
              (mul_nonneg (by norm_num) (Family.familyEventWeightRat_nonneg event))
          _ = 2 * Family.familyEventWeightRat event * μq * ε := by ring
      exact_mod_cast hfixedR
    _ = 2 * (μq : ℝ) ^ 2 * (ε : ℝ) := by
      have hsum := Family.actualPaperFamily_eventWeights_sum_eq_indexMass
        P X (Inputs.roughModulus X) b hXgt
      rw [Family.familyEventWeightsRat_sum_eq] at hsum
      have hsumR : (∑ event ∈ Family.familyEvents indices,
          (Family.familyEventWeightRat event : ℝ)) = (μq : ℝ) := by
        exact_mod_cast hsum
      calc
        (∑ event ∈ Family.familyEvents indices,
            2 * (Family.familyEventWeightRat event : ℝ) * (μq : ℝ) * (ε : ℝ)) =
          (2 * (μq : ℝ) * (ε : ℝ)) *
            ∑ event ∈ Family.familyEvents indices,
              (Family.familyEventWeightRat event : ℝ) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro event hevent
                ring
        _ = 2 * (μq : ℝ) ^ 2 * (ε : ℝ) := by rw [hsumR]; ring

/-- Direct real-valued singleton tail estimate, with no rational majorant
parameter. -/
theorem actualPaperFamily_singletonIncrementTail_real_le
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ K : ℝ, ∃ X₀ : ℝ, 0 < K ∧ ∀ X : ℝ,
      X₀ ≤ X → Real.exp 2 ≤ X →
      ∀ b : ℕ, Nat.Coprime b (Inputs.roughModulus X) →
      ∀ event ∈ Family.familyEvents
        (Family.familyIndexFinset P X (Inputs.roughModulus X) b),
        (Family.familyIncrementTailRat
            (Family.familyIndexFinset P X (Inputs.roughModulus X) b)
            {event} ⌊X⌋₊ : ℝ) ≤
          (Family.familyIndexMassRat
            (Family.familyIndexFinset P X (Inputs.roughModulus X) b) : ℝ) *
            K * (Real.exp (paperIncrementFloorScale P X) - 1) := by
  rcases actualPaperFamily_residueMassRat_le_indexMassRat_div_square P with
    ⟨Kq, X₀, hKq, htensor⟩
  refine ⟨(Kq : ℝ), X₀, by exact_mod_cast hKq, ?_⟩
  intro X hX hXexp b hbcop event hevent
  let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
  have hXexp1 : Real.exp 1 ≤ X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)) hXexp
  have hXgt : 1 < X :=
    lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hXexp1
  have hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X (Inputs.roughModulus X) b i := by
    intro i hi
    exact (Family.mem_familyIndexFinset_iff P X
      (Inputs.roughModulus X) b i (lt_trans zero_lt_one hXgt)).1 hi
  have hsub : ({event} : Finset EscLeanChecks.SatEvent) ⊆
      Family.familyEvents indices := by
    intro x hx
    have hxeq : x = event := Finset.mem_singleton.mp hx
    subst x
    exact hevent
  have htailQ := familyIncrementTailRat_le_indexMass_mul_classTail_of_residueTensor
    P X (Inputs.roughModulus X) b indices hXgt hmem {event} hsub Kq hKq.le
      (by
        intro D hD c hc
        have hdata := actualPaperFamily_incrementResidueClass_modulus_data
          P X b D c hXgt {event} hsub hc
        exact htensor X hX hXgt b hbcop D c hdata.1 hdata.2.1
          hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2)
  have htailR : (Family.familyIncrementTailRat indices {event} ⌊X⌋₊ : ℝ) ≤
      (Family.familyIndexMassRat indices : ℝ) *
        ∑ D ∈ Finset.Icc 2 ⌊X⌋₊,
          (Kq : ℝ) * (Family.familyIncrementClassProductRat {event} D : ℝ) /
            (D : ℝ) := by
    exact_mod_cast htailQ
  have hclass := actualPaperFamily_incrementTail_real_le P X b hXexp1
    (Kq : ℝ) (by exact_mod_cast hKq.le) {event} hsub
  calc
    (Family.familyIncrementTailRat indices {event} ⌊X⌋₊ : ℝ) ≤
        (Family.familyIndexMassRat indices : ℝ) *
          ∑ D ∈ Finset.Icc 2 ⌊X⌋₊,
            (Kq : ℝ) * (Family.familyIncrementClassProductRat {event} D : ℝ) /
              (D : ℝ) := htailR
    _ ≤ (Family.familyIndexMassRat indices : ℝ) *
        ((Kq : ℝ) *
          (Real.exp (paperIncrementFloorScale P X) - 1)) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [paperIncrementFloorScale] using hclass
      · exact_mod_cast (show 0 ≤ Family.familyIndexMassRat indices by
          unfold Family.familyIndexMassRat
          apply Finset.sum_nonneg
          intro i hi
          unfold Family.FamilyIndex.wRat
          positivity)
    _ = (Family.familyIndexMassRat indices : ℝ) * (Kq : ℝ) *
        (Real.exp (paperIncrementFloorScale P X) - 1) := by ring

/-- Direct paper-shaped bound for the actual ordered Suen pair parameter. -/
theorem actualPaperFamily_modularDependencyMass_real_le
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ K : ℝ, ∃ X₀ : ℝ, 0 < K ∧ ∀ X : ℝ,
      X₀ ≤ X → Real.exp 2 ≤ X →
      ∀ b : ℕ, Nat.Coprime b (Inputs.roughModulus X) →
      Inputs.modularDependencyMass
          (familyModularEvents
            (Family.familyIndexFinset P X (Inputs.roughModulus X) b)) ≤
        2 * (Family.familyIndexMassRat
          (Family.familyIndexFinset P X (Inputs.roughModulus X) b) : ℝ) ^ 2 *
          K * (Real.exp (paperIncrementFloorScale P X) - 1) := by
  rcases actualPaperFamily_singletonIncrementTail_real_le P with
    ⟨K, X₀, hK, hsingleton⟩
  refine ⟨K, X₀, hK, ?_⟩
  intro X hX hXexp b hbcop
  let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
  let μq := Family.familyIndexMassRat indices
  have hXgt : 1 < X :=
    lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num))
      (le_trans (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)) hXexp)
  have hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X (Inputs.roughModulus X) b i := by
    intro i hi
    exact (Family.mem_familyIndexFinset_iff P X
      (Inputs.roughModulus X) b i (lt_trans zero_lt_one hXgt)).1 hi
  rw [modularDependencyMass_eq_familyCompatibleMediumPairMass
    P X (Inputs.roughModulus X) b indices hXgt hmem]
  unfold familyCompatibleMediumPairMass
  calc
    (∑ event ∈ Family.familyEvents indices,
      ∑ other ∈ (Family.familyEvents indices).filter (fun other =>
        other ≠ event ∧ EscLeanChecks.satEventCompatible event other ∧
          ¬ Nat.Coprime event.dPlus other.dPlus),
        (Family.familySubsetLcmRecipRat {event, other} : ℝ)) ≤
      ∑ event ∈ Family.familyEvents indices,
        2 * (Family.familyEventWeightRat event : ℝ) * (μq : ℝ) * K *
          (Real.exp (paperIncrementFloorScale P X) - 1) := by
      apply Finset.sum_le_sum
      intro event hevent
      have hfixedQ := familyCompatibleMediumPairMass_fixed_le_two_weight_mul_tail
        P X (Inputs.roughModulus X) b indices hXgt hmem event hevent
      have hfixedR :
          (∑ other ∈ (Family.familyEvents indices).filter (fun other =>
            other ≠ event ∧ EscLeanChecks.satEventCompatible event other ∧
              ¬ Nat.Coprime event.dPlus other.dPlus),
            (Family.familySubsetLcmRecipRat {event, other} : ℝ)) ≤
          2 * (Family.familyEventWeightRat event : ℝ) *
            (Family.familyIncrementTailRat indices {event} ⌊X⌋₊ : ℝ) := by
        exact_mod_cast hfixedQ
      calc
        _ ≤ 2 * (Family.familyEventWeightRat event : ℝ) *
            (Family.familyIncrementTailRat indices {event} ⌊X⌋₊ : ℝ) := hfixedR
        _ ≤ 2 * (Family.familyEventWeightRat event : ℝ) *
            ((μq : ℝ) * K *
              (Real.exp (paperIncrementFloorScale P X) - 1)) := by
          exact mul_le_mul_of_nonneg_left
            (hsingleton X hX hXexp b hbcop event hevent)
            (mul_nonneg (by norm_num) (by
              exact_mod_cast Family.familyEventWeightRat_nonneg event))
        _ = 2 * (Family.familyEventWeightRat event : ℝ) * (μq : ℝ) * K *
            (Real.exp (paperIncrementFloorScale P X) - 1) := by ring
    _ = 2 * (μq : ℝ) ^ 2 * K *
        (Real.exp (paperIncrementFloorScale P X) - 1) := by
      have hsum := Family.actualPaperFamily_eventWeights_sum_eq_indexMass
        P X (Inputs.roughModulus X) b hXgt
      rw [Family.familyEventWeightsRat_sum_eq] at hsum
      have hsumR : (∑ event ∈ Family.familyEvents indices,
          (Family.familyEventWeightRat event : ℝ)) = (μq : ℝ) := by
        exact_mod_cast hsum
      calc
        (∑ event ∈ Family.familyEvents indices,
          2 * (Family.familyEventWeightRat event : ℝ) * (μq : ℝ) * K *
            (Real.exp (paperIncrementFloorScale P X) - 1)) =
          (2 * (μq : ℝ) * K *
            (Real.exp (paperIncrementFloorScale P X) - 1)) *
              ∑ event ∈ Family.familyEvents indices,
                (Family.familyEventWeightRat event : ℝ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro event hevent
            ring
        _ = _ := by rw [hsumR]; ring

/-- A cubic-log mass times the singleton Euler loss tends to zero. -/
theorem singletonEulerMassError_tendsto_zero
    (P : Params) (mass : ℝ → ℝ) (K C : ℝ)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hmass_nonneg : ∀ᶠ X in Filter.atTop, 0 ≤ mass X)
    (hmass_upper : ∀ᶠ X in Filter.atTop,
      mass X ≤ C * (Real.log X) ^ 3) :
    Filter.Tendsto
      (fun X => mass X * K *
        (Real.exp (paperIncrementFloorScale P X) - 1))
      Filter.atTop (nhds 0) := by
  have hmassScale : Filter.Tendsto
      (fun X => mass X * paperIncrementFloorScale P X)
      Filter.atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_
      (by simpa using
        (paperIncrementFloorScale_logCube_tendsto_zero P).const_mul C)
    · filter_upwards [hmass_nonneg,
        Filter.eventually_ge_atTop (Real.exp 2)] with X hm hX
      exact mul_nonneg hm (paperIncrementFloorScale_nonneg P hX)
    · filter_upwards [hmass_upper,
        Filter.eventually_ge_atTop (Real.exp 2)] with X hm hX
      have hs := paperIncrementFloorScale_nonneg P hX
      calc
        mass X * paperIncrementFloorScale P X ≤
            (C * (Real.log X) ^ 3) * paperIncrementFloorScale P X :=
          mul_le_mul_of_nonneg_right hm hs
        _ = C * ((Real.log X) ^ 3 * paperIncrementFloorScale P X) := by ring
  have hscale0 : Filter.Tendsto (paperIncrementFloorScale P)
      Filter.atTop (nhds 0) := by
    have hlogCubeLower : ∀ᶠ X in Filter.atTop,
        1 ≤ (Real.log X) ^ 3 := by
      filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with X hX
      have hlog : 1 ≤ Real.log X := by
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) hX
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hlog 3]
    refine squeeze_zero' ?_ ?_
      (paperIncrementFloorScale_logCube_tendsto_zero P)
    · filter_upwards [Filter.eventually_ge_atTop (Real.exp 2)] with X hX
      exact paperIncrementFloorScale_nonneg P hX
    · filter_upwards [hlogCubeLower,
        Filter.eventually_ge_atTop (Real.exp 2)] with X hlog hX
      have hs := paperIncrementFloorScale_nonneg P hX
      nlinarith
  have hbound : ∀ᶠ X in Filter.atTop,
      mass X * K * (Real.exp (paperIncrementFloorScale P X) - 1) ≤
        2 * K * (mass X * paperIncrementFloorScale P X) := by
    have hscaleSmall : ∀ᶠ X in Filter.atTop,
        paperIncrementFloorScale P X < (1 : ℝ) / 2 :=
      Filter.Tendsto.eventually_lt_const
        (by norm_num : (0 : ℝ) < 1 / 2) hscale0
    filter_upwards [hmass_nonneg, hscaleSmall,
        Filter.eventually_ge_atTop (Real.exp 2)] with X hm hsSmall hX
    have hsNonneg := paperIncrementFloorScale_nonneg P hX
    have hexp := Real.exp_bound_div_one_sub_of_interval hsNonneg
      (lt_trans hsSmall (by norm_num : (1 : ℝ) / 2 < 1))
    have hden : 0 < 1 - paperIncrementFloorScale P X := by linarith
    have hexpLoss : Real.exp (paperIncrementFloorScale P X) - 1 ≤
        2 * paperIncrementFloorScale P X := by
      calc
        Real.exp (paperIncrementFloorScale P X) - 1 ≤
            1 / (1 - paperIncrementFloorScale P X) - 1 := by linarith
        _ ≤ 2 * paperIncrementFloorScale P X := by
          rw [div_sub_one hden.ne']
          rw [div_le_iff₀ hden]
          nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hexpLoss (mul_nonneg hm hK)]
  refine squeeze_zero' ?_ hbound ?_
  · filter_upwards [hmass_nonneg,
      Filter.eventually_ge_atTop (Real.exp 2)] with X hm hX
    exact mul_nonneg (mul_nonneg hm hK)
      (sub_nonneg.mpr (Real.one_le_exp
        (paperIncrementFloorScale_nonneg P hX)))
  · simpa [mul_assoc] using hmassScale.const_mul (2 * K)

/-- A pair bound of shape `Delta <= 2*mu^2*K*(exp(scale)-1)` implies
`Delta/mu -> 0` for a nonnegative cubic-log mass. -/
theorem dependencyRatio_tendsto_zero_of_singletonEuler_bound
    (P : Params) (mass dependency : ℝ → ℝ) (K C : ℝ)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hmass_pos : ∀ᶠ X in Filter.atTop, 0 < mass X)
    (hmass_upper : ∀ᶠ X in Filter.atTop,
      mass X ≤ C * (Real.log X) ^ 3)
    (hdependency_nonneg : ∀ᶠ X in Filter.atTop, 0 ≤ dependency X)
    (hdependency : ∀ᶠ X in Filter.atTop,
      dependency X ≤ 2 * (mass X) ^ 2 * K *
        (Real.exp (paperIncrementFloorScale P X) - 1)) :
    Filter.Tendsto (fun X => dependency X / mass X)
      Filter.atTop (nhds 0) := by
  have herror := singletonEulerMassError_tendsto_zero
    P mass (2 * K) C (mul_nonneg (by norm_num) hK) hC
      (hmass_pos.mono (fun X hX => hX.le)) hmass_upper
  apply squeeze_zero'
  · filter_upwards [hdependency_nonneg, hmass_pos] with X hdep hmass
    exact div_nonneg hdep hmass.le
  · filter_upwards [hdependency, hmass_pos] with X hdep hmass
    rw [div_le_iff₀ hmass]
    calc
      dependency X ≤ 2 * mass X ^ 2 * K *
          (Real.exp (paperIncrementFloorScale P X) - 1) := hdep
      _ = (mass X * (2 * K) *
          (Real.exp (paperIncrementFloorScale P X) - 1)) * mass X := by ring
  · simpa [mul_assoc] using herror

theorem modularPairMass_nonneg
    (event other : Inputs.ModularEvent) :
    0 ≤ Inputs.modularPairMass event other := by
  unfold Inputs.modularPairMass
  split_ifs <;> positivity

theorem modularDependencyMass_nonneg
    (events : Finset Inputs.ModularEvent) :
    0 ≤ Inputs.modularDependencyMass events := by
  unfold Inputs.modularDependencyMass
  apply Finset.sum_nonneg
  intro event hevent
  apply Finset.sum_nonneg
  intro other hother
  exact modularPairMass_nonneg event other

/-- The actual ordered pair parameter satisfies `Delta_b=o(mu_b)` uniformly
along every choice of admissible base class. -/
theorem actualPaperFamily_modularDependencyRatio_tendsto_zero
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)]
    (base : ℝ → ℕ)
    (hbase : ∀ᶠ X in Filter.atTop,
      Nat.Coprime (base X) (Inputs.roughModulus X)) :
    Filter.Tendsto
      (fun X =>
        Inputs.modularDependencyMass
          (familyModularEvents
            (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X))) /
        (Family.familyIndexMassRat
          (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X)) : ℝ))
      Filter.atTop (nhds 0) := by
  rcases actualPaperFamily_indexMassRat_ge_log_cube P with
    ⟨c, Xlower, hc, hlower⟩
  rcases actualPaperFamily_indexMassRat_le_log_cube P with
    ⟨C, Xupper, hC, hupper⟩
  rcases actualPaperFamily_modularDependencyMass_real_le P with
    ⟨K, Xdep, hK, hdep⟩
  let mass : ℝ → ℝ := fun X =>
    (Family.familyIndexMassRat
      (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X)) : ℝ)
  let dependency : ℝ → ℝ := fun X =>
    Inputs.modularDependencyMass
      (familyModularEvents
        (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X)))
  apply dependencyRatio_tendsto_zero_of_singletonEuler_bound
    P mass dependency K C hK.le hC.le
  · filter_upwards [hbase,
      Filter.eventually_ge_atTop (max Xlower (Real.exp 1))] with X hcop hX
    have hXlower : Xlower ≤ X := le_trans (le_max_left _ _) hX
    have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
    have hXgt : 1 < X := lt_of_lt_of_le
      (Real.one_lt_exp_iff.mpr (by norm_num)) hXexp
    have hlogPos : 0 < Real.log X := Real.log_pos hXgt
    have hl := hlower X hXlower hXgt (base X) hcop
    dsimp [mass]
    nlinarith [mul_pos hc (pow_pos hlogPos 3)]
  · filter_upwards [hbase,
      Filter.eventually_ge_atTop (max Xupper (Real.exp 1))] with X hcop hX
    have hXupper : Xupper ≤ X := le_trans (le_max_left _ _) hX
    have hXgt : 1 < X := lt_of_lt_of_le
      (Real.one_lt_exp_iff.mpr (by norm_num))
      (le_trans (le_max_right _ _) hX)
    simpa [mass, logCube] using hupper X hXupper hXgt (base X) hcop
  · filter_upwards with X
    exact modularDependencyMass_nonneg _
  · filter_upwards [hbase,
      Filter.eventually_ge_atTop (max Xdep (Real.exp 2))] with X hcop hX
    have hXdep : Xdep ≤ X := le_trans (le_max_left _ _) hX
    have hXexp : Real.exp 2 ≤ X := le_trans (le_max_right _ _) hX
    simpa [mass, dependency] using hdep X hXdep hXexp (base X) hcop

/-! ## Shared-large-prime neighborhood -/

/-- Index-side mass of the fiber with selected prime `p`. -/
noncomputable def familyIndexPrimeMass
    (indices : Finset Family.FamilyIndex) (p : ℕ) : ℝ :=
  ∑ i ∈ indices.filter (fun i => i.p = p), (i.wRat : ℝ)

/-- The event-side shared-prime neighborhood is bounded by the corresponding
full index fiber. -/
theorem familyLargePrimeNeighbourMass_le_indexPrimeMass
    (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset Family.FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i)
    (event : EscLeanChecks.SatEvent) :
    familyLargePrimeNeighbourMass indices event ≤
      familyIndexPrimeMass indices event.p := by
  classical
  unfold familyLargePrimeNeighbourMass familyIndexPrimeMass
  have hinj : Set.InjOn Family.FamilyIndex.toSatEvent
      (indices : Set Family.FamilyIndex) :=
    Family.familyIndex_toSatEvent_injOn P X Pz b indices hX hmem
  calc
    (∑ other ∈ (Family.familyEvents indices).filter
        (fun other => other ≠ event ∧ other.p = event.p),
        (Family.familyEventWeightRat other : ℝ)) ≤
      ∑ other ∈ (Family.familyEvents indices).filter
        (fun other => other.p = event.p),
        (Family.familyEventWeightRat other : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro other hother
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hother).1, (Finset.mem_filter.mp hother).2.2⟩
      · intro other hother hnot
        exact_mod_cast Family.familyEventWeightRat_nonneg other
    _ = ∑ i ∈ indices.filter (fun i => i.p = event.p), (i.wRat : ℝ) := by
      unfold Family.familyEvents
      rw [Finset.filter_image]
      rw [Finset.sum_image]
      · apply Finset.sum_congr
        · ext i
          simp
        · intro i hi
          rfl
      · intro i hi j hj hij
        exact hinj (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hij

theorem familyIndexPrimeMass_le_card_div_prime
    (P : Params) (X : ℝ) (Pz b p : ℕ) (indices : Finset Family.FamilyIndex)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i)
    (hp : 0 < p) :
    familyIndexPrimeMass indices p ≤
      ((indices.filter (fun i => i.p = p)).card : ℝ) / (p : ℝ) := by
  unfold familyIndexPrimeMass
  calc
    (∑ i ∈ indices.filter (fun i => i.p = p), (i.wRat : ℝ)) ≤
      ∑ _i ∈ indices.filter (fun i => i.p = p), (1 : ℝ) / (p : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiIndices := (Finset.mem_filter.mp hi).1
      have hip : i.p = p := (Finset.mem_filter.mp hi).2
      unfold Family.FamilyIndex.wRat Family.FamilyIndex.q
      rw [Rat.cast_div]
      norm_num
      rw [hip]
      have hdplusOne : (1 : ℝ) ≤ (i.dplus : ℝ) := by
        exact_mod_cast (hmem i hiIndices).dplus_pos
      have hpReal : 0 < (p : ℝ) := by exact_mod_cast hp
      have hden : (p : ℝ) ≤ (i.dplus : ℝ) * (p : ℝ) := by
        nlinarith
      simpa [one_div, mul_inv, mul_comm] using
        (one_div_le_one_div_of_le hpReal hden)
    _ = ((indices.filter (fun i => i.p = p)).card : ℝ) / (p : ℝ) := by
      simp [div_eq_mul_inv]

/-- Crude but sufficient four-coordinate box bound for a fixed selected prime.
The prime coordinate is frozen, leaving only `(r,s,dminus,dplus)`. -/
theorem familyIndex_fixedPrime_card_le_box
    (P : Params) (X : ℝ) (Pz b p : ℕ) (indices : Finset Family.FamilyIndex)
    (hX : 1 < X)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i) :
    (indices.filter (fun i => i.p = p)).card ≤
      (⌊HScale P X⌋₊ + 1) * (⌊SScale P X⌋₊ + 1) *
        (⌊UScale X⌋₊ + 1) * (⌊YScale P X⌋₊ + 1) := by
  classical
  let code : Family.FamilyIndex → ((ℕ × ℕ) × ℕ) × ℕ :=
    fun i => (((i.E.r, i.E.s), i.dminus), i.dplus)
  let box : Finset (((ℕ × ℕ) × ℕ) × ℕ) :=
    (((Finset.range (⌊HScale P X⌋₊ + 1) ×ˢ
      Finset.range (⌊SScale P X⌋₊ + 1)) ×ˢ
        Finset.range (⌊UScale X⌋₊ + 1)) ×ˢ
          Finset.range (⌊YScale P X⌋₊ + 1))
  have hmaps : ∀ i ∈ indices.filter (fun i => i.p = p), code i ∈ box := by
    intro i hi
    have hiIndices := (Finset.mem_filter.mp hi).1
    have himem := hmem i hiIndices
    have hHnonneg : 0 ≤ HScale P X := Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hX)) _
    have hsOne : (1 : ℝ) ≤ (i.E.s : ℝ) := by exact_mod_cast himem.s_pos
    have hsSq : (1 : ℝ) ≤ (i.E.s : ℝ) ^ 2 := one_le_pow₀ hsOne
    have hrLe : (i.E.r : ℝ) ≤ HScale P X :=
      le_trans himem.r_le (div_le_self hHnonneg hsSq)
    have hdpLe : (i.dplus : ℝ) ≤ YScale P X := himem.dplus_le_YScale
    simp only [code, box, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨⟨Nat.lt_succ_of_le (Nat.le_floor hrLe),
      Nat.lt_succ_of_le (Nat.le_floor himem.s_le_S)⟩,
      Nat.lt_succ_of_le (Nat.le_floor himem.dminus_le_U)⟩,
      Nat.lt_succ_of_le (Nat.le_floor hdpLe)⟩
  have hinj : Set.InjOn code
      (indices.filter (fun i => i.p = p) : Set Family.FamilyIndex) := by
    intro i hi j hj hcode
    have hip : i.p = p := (Finset.mem_filter.mp hi).2
    have hjp : j.p = p := (Finset.mem_filter.mp hj).2
    cases i with
    | mk Ei dmi dpi pi =>
      cases Ei with
      | mk ri si hri hsi hcopi =>
        cases j with
        | mk Ej dmj dpj pj =>
          cases Ej with
          | mk rj sj hrj hsj hcopj =>
            simp only [code] at hcode
            injection hcode with hrs hdp
            injection hrs with hrs' hdm
            injection hrs' with hr hs
            simp only at hip hjp
            subst rj
            subst sj
            subst dmj
            subst dpj
            rw [hip, hjp]
  have hcard := Finset.card_le_card_of_injOn code hmaps hinj
  simpa [box, Finset.card_product, Finset.card_range, mul_assoc] using hcard

/-- Elementary fixed-prime neighborhood bound.  The manuscript's stronger
divisor-count estimate is unnecessary: the crude four-coordinate box already
has exponent `theta+eta+sigma < beta`. -/
theorem actualPaperFamily_largePrimeNeighbourMass_le_box_div_primeScale
    (P : Params) (X : ℝ) (b : ℕ)
    (hX : 1 < X)
    (event : EscLeanChecks.SatEvent)
    (hevent : event ∈ Family.familyEvents
      (Family.familyIndexFinset P X (Inputs.roughModulus X) b)) :
    familyLargePrimeNeighbourMass
        (Family.familyIndexFinset P X (Inputs.roughModulus X) b) event ≤
      (((⌊HScale P X⌋₊ + 1) * (⌊SScale P X⌋₊ + 1) *
        (⌊UScale X⌋₊ + 1) * (⌊YScale P X⌋₊ + 1) : ℕ) : ℝ) /
          X ^ P.β := by
  let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
  have hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X (Inputs.roughModulus X) b i := by
    intro i hi
    exact (Family.mem_familyIndexFinset_iff P X
      (Inputs.roughModulus X) b i (lt_trans zero_lt_one hX)).1 hi
  have hpPrime : Nat.Prime event.p := by
    rcases Finset.mem_image.mp hevent with ⟨i, hi, rfl⟩
    exact (hmem i hi).p_prime
  have hpLower : X ^ P.β < (event.p : ℝ) := by
    rcases Finset.mem_image.mp hevent with ⟨i, hi, rfl⟩
    exact (hmem i hi).p_gt
  have hcard := familyIndex_fixedPrime_card_le_box
    P X (Inputs.roughModulus X) b event.p indices hX hmem
  have hprimeMass := familyIndexPrimeMass_le_card_div_prime
    P X (Inputs.roughModulus X) b event.p indices hmem hpPrime.pos
  have hlarge := familyLargePrimeNeighbourMass_le_indexPrimeMass
    P X (Inputs.roughModulus X) b indices hX hmem event
  have hboxNonneg : 0 ≤
      ((((⌊HScale P X⌋₊ + 1) * (⌊SScale P X⌋₊ + 1) *
        (⌊UScale X⌋₊ + 1) * (⌊YScale P X⌋₊ + 1) : ℕ) : ℝ)) := by
    positivity
  calc
    familyLargePrimeNeighbourMass indices event ≤
        familyIndexPrimeMass indices event.p := hlarge
    _ ≤ ((indices.filter (fun i => i.p = event.p)).card : ℝ) /
        (event.p : ℝ) := hprimeMass
    _ ≤ ((((⌊HScale P X⌋₊ + 1) * (⌊SScale P X⌋₊ + 1) *
        (⌊UScale X⌋₊ + 1) * (⌊YScale P X⌋₊ + 1) : ℕ) : ℝ)) /
          (event.p : ℝ) := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ ≤ ((((⌊HScale P X⌋₊ + 1) * (⌊SScale P X⌋₊ + 1) *
        (⌊UScale X⌋₊ + 1) * (⌊YScale P X⌋₊ + 1) : ℕ) : ℝ)) /
          X ^ P.β := by
      apply div_le_div_of_nonneg_left hboxNonneg
      · exact Real.rpow_pos_of_pos (lt_trans zero_lt_one hX) P.β
      · exact hpLower.le

/-- The four-coordinate box used for the large-prime neighborhood is
asymptotically smaller than the prime scale. -/
theorem paperLargePrimeBoxRatio_tendsto_zero (P : Params) :
    Filter.Tendsto
      (fun X : ℝ =>
        (((⌊HScale P X⌋₊ + 1) * (⌊SScale P X⌋₊ + 1) *
          (⌊UScale X⌋₊ + 1) * (⌊YScale P X⌋₊ + 1) : ℕ) : ℝ) /
            X ^ P.β)
      Filter.atTop (nhds 0) := by
  have hgap : 0 < P.β - (P.θ + P.η + P.σ) := by
    have hησθ : P.η + P.σ < P.θ := by
      have hlamθ : P.lam < P.θ := by
        linarith [P.lam_add_η_lt_θ, P.η_pos]
      exact P.η_add_σ_lt_lam.trans hlamθ
    linarith [P.two_θ_lt_β]
  have hmodel : Filter.Tendsto
      (fun X : ℝ => 16 * ((Real.log X) ^ 8 /
        X ^ (P.β - (P.θ + P.η + P.σ))))
      Filter.atTop (nhds 0) := by
    have hsmall : Filter.Tendsto
        (fun X : ℝ => (Real.log X) ^ 8 /
          X ^ (P.β - (P.θ + P.η + P.σ)))
        Filter.atTop (nhds 0) := by
      convert
        (isLittleO_log_rpow_rpow_atTop (8 : ℝ) hgap).tendsto_div_nhds_zero using 1
      ext X
      rw [← Real.rpow_natCast]
      norm_num
    simpa using hsmall.const_mul 16
  apply squeeze_zero'
  · filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with X hX
    exact div_nonneg (by positivity)
      (Real.rpow_nonneg (le_trans (Real.exp_pos 1).le hX) _)
  · filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with X hX
    have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hX
    have hXone : (1 : ℝ) ≤ X :=
      le_trans (Real.one_le_exp (by norm_num)) hX
    have hlog : (1 : ℝ) ≤ Real.log X := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hX
    have hHone : (1 : ℝ) ≤ HScale P X := by
      exact Real.one_le_rpow hXone P.θ_pos.le
    have hSone : (1 : ℝ) ≤ SScale P X := by
      exact Real.one_le_rpow hXone P.η_pos.le
    have hUone : (1 : ℝ) ≤ UScale X := by
      unfold UScale
      exact one_le_pow₀ hlog
    have hYone : (1 : ℝ) ≤ YScale P X := by
      exact Real.one_le_rpow hXone P.σ_pos.le
    have hHfloor : ((⌊HScale P X⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * HScale P X := by
      rw [Nat.cast_add, Nat.cast_one]
      have := Nat.floor_le (show 0 ≤ HScale P X by positivity)
      linarith
    have hSfloor : ((⌊SScale P X⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * SScale P X := by
      rw [Nat.cast_add, Nat.cast_one]
      have := Nat.floor_le (show 0 ≤ SScale P X by positivity)
      linarith
    have hUfloor : ((⌊UScale X⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * UScale X := by
      rw [Nat.cast_add, Nat.cast_one]
      have := Nat.floor_le (show 0 ≤ UScale X by positivity)
      linarith
    have hYfloor : ((⌊YScale P X⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * YScale P X := by
      rw [Nat.cast_add, Nat.cast_one]
      have := Nat.floor_le (show 0 ≤ YScale P X by positivity)
      linarith
    have hnumer :
        (((⌊HScale P X⌋₊ + 1) * (⌊SScale P X⌋₊ + 1) *
          (⌊UScale X⌋₊ + 1) * (⌊YScale P X⌋₊ + 1) : ℕ) : ℝ) ≤
          (2 * HScale P X) * (2 * SScale P X) *
            (2 * UScale X) * (2 * YScale P X) := by
      push_cast
      gcongr
      · simpa using hHfloor
      · simpa using hSfloor
      · simpa using hUfloor
      · simpa using hYfloor
    calc
      (((⌊HScale P X⌋₊ + 1) * (⌊SScale P X⌋₊ + 1) *
          (⌊UScale X⌋₊ + 1) * (⌊YScale P X⌋₊ + 1) : ℕ) : ℝ) /
            X ^ P.β ≤
          ((2 * HScale P X) * (2 * SScale P X) *
            (2 * UScale X) * (2 * YScale P X)) / X ^ P.β :=
        div_le_div_of_nonneg_right hnumer (Real.rpow_nonneg hXpos.le _)
      _ = 16 * ((Real.log X) ^ 8 /
          X ^ (P.β - (P.θ + P.η + P.σ))) := by
        have hsum : X ^ (P.θ + P.η + P.σ) =
            X ^ P.θ * X ^ P.η * X ^ P.σ := by
          rw [Real.rpow_add hXpos, Real.rpow_add hXpos]
        have hden : X ^ P.β = X ^ (P.θ + P.η + P.σ) *
            X ^ (P.β - (P.θ + P.η + P.σ)) := by
          rw [← Real.rpow_add hXpos]
          congr 1
          ring
        unfold HScale SScale UScale YScale
        rw [hden, hsum]
        field_simp [ne_of_gt (Real.rpow_pos_of_pos hXpos _)]
        ring
  · exact hmodel

/-- The maximal shared-large-prime neighborhood is bounded by the same
four-coordinate box, uniformly in the base residue class. -/
theorem actualPaperFamily_largePrimeDelta_le_box_div_primeScale
    (P : Params) (X : ℝ) (b : ℕ) (hX : 1 < X) :
    familyLargePrimeDelta
        (Family.familyIndexFinset P X (Inputs.roughModulus X) b) ≤
      (((⌊HScale P X⌋₊ + 1) * (⌊SScale P X⌋₊ + 1) *
        (⌊UScale X⌋₊ + 1) * (⌊YScale P X⌋₊ + 1) : ℕ) : ℝ) /
          X ^ P.β := by
  classical
  unfold familyLargePrimeDelta
  split_ifs with hnonempty
  · apply Finset.sup'_le hnonempty
    intro event hevent
    exact actualPaperFamily_largePrimeNeighbourMass_le_box_div_primeScale
      P X b hX event hevent
  · positivity

/-- The shared-large-prime contribution to the actual dependency
neighborhood vanishes uniformly along every choice of base class. -/
theorem actualPaperFamily_largePrimeDelta_tendsto_zero
    (P : Params) (base : ℝ → ℕ) :
    Filter.Tendsto
      (fun X => familyLargePrimeDelta
        (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X)))
      Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards with X
    exact familyLargePrimeDelta_nonneg
      (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X))
  · filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with X hX
    exact actualPaperFamily_largePrimeDelta_le_box_div_primeScale
      P X (base X)
        (lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hX)
  · exact paperLargePrimeBoxRatio_tendsto_zero P

/-- A nonnegative cubic-log mass times the floor-scale dependency loss
vanishes. -/
theorem mass_mul_paperIncrementFloorScale_tendsto_zero
    (P : Params) (mass : ℝ → ℝ) (K C : ℝ)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hmass_nonneg : ∀ᶠ X in Filter.atTop, 0 ≤ mass X)
    (hmass_upper : ∀ᶠ X in Filter.atTop,
      mass X ≤ C * (Real.log X) ^ 3) :
    Filter.Tendsto
      (fun X => K * mass X * paperIncrementFloorScale P X)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [hmass_nonneg,
      Filter.eventually_ge_atTop (Real.exp 2)] with X hmass hX
    exact mul_nonneg (mul_nonneg hK hmass)
      (paperIncrementFloorScale_nonneg P hX)
  · filter_upwards [hmass_upper,
      Filter.eventually_ge_atTop (Real.exp 2)] with X hmass hX
    have hscale := paperIncrementFloorScale_nonneg P hX
    calc
      K * mass X * paperIncrementFloorScale P X ≤
          K * (C * (Real.log X) ^ 3) *
            paperIncrementFloorScale P X := by
        gcongr
      _ = (K * C) *
          ((Real.log X) ^ 3 * paperIncrementFloorScale P X) := by ring
  · simpa using
      (paperIncrementFloorScale_logCube_tendsto_zero P).const_mul (K * C)

/-- The full maximal dependency-neighborhood parameter of the actual modular
event family tends to zero.  Both dependency mechanisms are now discharged. -/
theorem actualPaperFamily_modularDelta_tendsto_zero
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)]
    (base : ℝ → ℕ)
    (hbase : ∀ᶠ X in Filter.atTop,
      Nat.Coprime (base X) (Inputs.roughModulus X)) :
    Filter.Tendsto
      (fun X => Inputs.modularDelta
        (familyModularEvents
          (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X))))
      Filter.atTop (nhds 0) := by
  rcases actualPaperFamily_modularDelta_le_largePrime_add_floorScale P with
    ⟨K, Xdelta, hK, hdelta⟩
  rcases actualPaperFamily_indexMassRat_le_log_cube P with
    ⟨C, Xmass, hC, hmassUpper⟩
  let mass : ℝ → ℝ := fun X =>
    (Family.familyIndexMassRat
      (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X)) : ℝ)
  have hmassNonneg : ∀ᶠ X in Filter.atTop, 0 ≤ mass X := by
    filter_upwards with X
    dsimp [mass]
    have hmassQ : 0 ≤ Family.familyIndexMassRat
        (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X)) := by
      unfold Family.familyIndexMassRat
      apply Finset.sum_nonneg
      intro i hi
      unfold Family.FamilyIndex.wRat
      positivity
    exact_mod_cast hmassQ
  have hmassBound : ∀ᶠ X in Filter.atTop,
      mass X ≤ C * (Real.log X) ^ 3 := by
    filter_upwards [hbase,
      Filter.eventually_ge_atTop (max Xmass (Real.exp 1))] with X hcop hX
    have hXmass : Xmass ≤ X := le_trans (le_max_left _ _) hX
    have hXgt : 1 < X := lt_of_lt_of_le
      (Real.one_lt_exp_iff.mpr (by norm_num))
      (le_trans (le_max_right _ _) hX)
    simpa [mass, logCube] using
      hmassUpper X hXmass hXgt (base X) hcop
  have hmedium : Filter.Tendsto
      (fun X => K * mass X * paperIncrementFloorScale P X)
      Filter.atTop (nhds 0) :=
    mass_mul_paperIncrementFloorScale_tendsto_zero
      P mass K C hK.le hC.le hmassNonneg hmassBound
  have hlarge := actualPaperFamily_largePrimeDelta_tendsto_zero P base
  apply squeeze_zero'
  · filter_upwards with X
    exact Inputs.modularDelta_nonneg _
  · filter_upwards [hbase,
      Filter.eventually_ge_atTop (max Xdelta (Real.exp 2))] with X hcop hX
    have hXdelta : Xdelta ≤ X := le_trans (le_max_left _ _) hX
    have hXexp : Real.exp 2 ≤ X := le_trans (le_max_right _ _) hX
    simpa [mass] using hdelta X hXdelta hXexp (base X) hcop
  · simpa [mass] using hlarge.add hmedium

/-- The cited modular Suen inequality supplies one absolute constant for all
actual paper families, rather than a separately chosen constant at each
scale. -/
theorem actualPaperFamily_modularSuen_fixed_constant (P : Params) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 1 < X → ∀ b : ℕ,
      Inputs.modularNoHitProbability
          (familyModularPeriod
            (Family.familyIndexFinset P X (Inputs.roughModulus X) b))
          (familyModularEvents
            (Family.familyIndexFinset P X (Inputs.roughModulus X) b)) ≤
        Real.exp
          (-(Family.familyIndexMassRat
              (Family.familyIndexFinset P X (Inputs.roughModulus X) b) : ℝ) +
            K * Inputs.modularDependencyMass
              (familyModularEvents
                (Family.familyIndexFinset P X (Inputs.roughModulus X) b)) *
              Real.exp (2 * Inputs.modularDelta
                (familyModularEvents
                  (Family.familyIndexFinset P X (Inputs.roughModulus X) b)))) := by
  rcases Inputs.standard_modular_suen_correlation_inequality with
    ⟨K, hK, hSuen⟩
  refine ⟨K, hK, ?_⟩
  intro X hX b
  let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
  have hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X (Inputs.roughModulus X) b i := by
    intro i hi
    exact (Family.mem_familyIndexFinset_iff P X
      (Inputs.roughModulus X) b i (lt_trans zero_lt_one hX)).1 hi
  have hbound := hSuen (familyModularPeriod indices)
    (familyModularEvents indices)
    (Inputs.modularDelta (familyModularEvents indices))
    (familyModularPeriod_pos P X (Inputs.roughModulus X) b indices hmem)
    (familyModularEvents_period_data
      P X (Inputs.roughModulus X) b indices hmem)
    (Inputs.modularDelta_nonneg _)
    (fun event hevent => Inputs.modularNeighbourMass_le_delta _ hevent)
  have hmassEq : Family.familyEventMassRat indices =
      Family.familyIndexMassRat indices :=
    Family.familyEventMassRat_eq_familyIndexMassRat
      P X (Inputs.roughModulus X) b indices hX hmem
  simpa [indices, modularMass_familyModularEvents, hmassEq] using hbound

/-- Relative Suen correction in the exact actual-family model tends to zero:
the ordered pair mass is `o(mu)` and the maximal neighborhood tends to zero. -/
theorem actualPaperFamily_modularSuenCorrectionRatio_tendsto_zero
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)]
    (base : ℝ → ℕ) (K : ℝ)
    (hbase : ∀ᶠ X in Filter.atTop,
      Nat.Coprime (base X) (Inputs.roughModulus X)) :
    Filter.Tendsto
      (fun X => K *
        (Inputs.modularDependencyMass
          (familyModularEvents
            (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X))) /
          (Family.familyIndexMassRat
            (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X)) : ℝ)) *
        Real.exp (2 * Inputs.modularDelta
          (familyModularEvents
            (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X)))))
      Filter.atTop (nhds 0) := by
  have hratio := actualPaperFamily_modularDependencyRatio_tendsto_zero
    P base hbase
  have hdelta := actualPaperFamily_modularDelta_tendsto_zero P base hbase
  have hexp : Filter.Tendsto
      (fun X => Real.exp (2 * Inputs.modularDelta
        (familyModularEvents
          (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X)))))
      Filter.atTop (nhds 1) := by
    have htwo : Filter.Tendsto
        (fun X => 2 * Inputs.modularDelta
          (familyModularEvents
            (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X))))
        Filter.atTop (nhds 0) := by
      simpa using hdelta.const_mul 2
    simpa using (Real.continuous_exp.tendsto 0).comp htwo
  simpa using (hratio.const_mul K).mul hexp

/-- Eventual paper-scale exponential no-hit bound for the exact modular event
family.  This is the concrete replacement for the legacy scalar probability
carrier. -/
theorem actualPaperFamily_modularNoHit_le_exp_one_sub
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)]
    (base : ℝ → ℕ)
    (hbase : ∀ᶠ X in Filter.atTop,
      Nat.Coprime (base X) (Inputs.roughModulus X))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X in Filter.atTop,
      Inputs.modularNoHitProbability
          (familyModularPeriod
            (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X)))
          (familyModularEvents
            (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X))) ≤
        Real.exp (-(1 - ε) *
          (Family.familyIndexMassRat
            (Family.familyIndexFinset P X
              (Inputs.roughModulus X) (base X)) : ℝ)) := by
  rcases actualPaperFamily_modularSuen_fixed_constant P with
    ⟨K, hK, hSuen⟩
  rcases actualPaperFamily_indexMassRat_ge_log_cube P with
    ⟨c, Xmass, hc, hmassLower⟩
  have hcorr := actualPaperFamily_modularSuenCorrectionRatio_tendsto_zero
    P base K hbase
  have hcorrSmall : ∀ᶠ X in Filter.atTop,
      K *
        (Inputs.modularDependencyMass
          (familyModularEvents
            (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X))) /
          (Family.familyIndexMassRat
            (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X)) : ℝ)) *
        Real.exp (2 * Inputs.modularDelta
          (familyModularEvents
            (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X)))) < ε :=
    Filter.Tendsto.eventually_lt_const hε hcorr
  filter_upwards [hbase, hcorrSmall,
      Filter.eventually_ge_atTop (max Xmass (Real.exp 1))] with X hcop hsmall hX
  have hXmass : Xmass ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXgt : 1 < X := lt_of_lt_of_le
    (Real.one_lt_exp_iff.mpr (by norm_num)) hXexp
  let mass : ℝ :=
    (Family.familyIndexMassRat
      (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X)) : ℝ)
  let dependency : ℝ := Inputs.modularDependencyMass
    (familyModularEvents
      (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X)))
  let delta : ℝ := Inputs.modularDelta
    (familyModularEvents
      (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X)))
  have hlogPos : 0 < Real.log X := Real.log_pos hXgt
  have hmassLower' := hmassLower X hXmass hXgt (base X) hcop
  have hmassPos : 0 < mass := by
    dsimp [mass]
    nlinarith [mul_pos hc (pow_pos hlogPos 3)]
  have hcorrBound :
      K * dependency * Real.exp (2 * delta) ≤ ε * mass := by
    have hid :
        (K * (dependency / mass) * Real.exp (2 * delta)) * mass =
          K * dependency * Real.exp (2 * delta) := by
      field_simp [ne_of_gt hmassPos]
    have hs : K * (dependency / mass) * Real.exp (2 * delta) < ε := by
      simpa [mass, dependency, delta] using hsmall
    nlinarith [mul_lt_mul_of_pos_right hs hmassPos]
  have hsuen := hSuen X hXgt (base X)
  calc
    Inputs.modularNoHitProbability
          (familyModularPeriod
            (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X)))
          (familyModularEvents
            (Family.familyIndexFinset P X (Inputs.roughModulus X) (base X))) ≤
        Real.exp (-mass + K * dependency * Real.exp (2 * delta)) := by
      simpa [mass, dependency, delta] using hsuen
    _ ≤ Real.exp (-(1 - ε) * mass) := by
      apply Real.exp_le_exp.mpr
      nlinarith

/-! ## Finite base-progression to complete-period transfer -/

/-- An affine map with invertible slope is injective on a complete system of
natural representatives modulo `L`. -/
theorem affineMod_injOn_range
    (L shift slope : ℕ) (hL : 0 < L) (hcop : Nat.Coprime slope L) :
    Set.InjOn (fun k => (shift + slope * k) % L) (Finset.range L : Set ℕ) := by
  intro x hx y hy hxy
  have hxlt : x < L := Finset.mem_range.mp hx
  have hylt : y < L := Finset.mem_range.mp hy
  have haffine : shift + slope * x ≡ shift + slope * y [MOD L] := by
    unfold Nat.ModEq
    simpa using hxy
  have hmul : slope * x ≡ slope * y [MOD L] :=
    Nat.ModEq.add_left_cancel' shift haffine
  have hmod : x ≡ y [MOD L] :=
    Nat.ModEq.cancel_left_of_coprime hcop.symm.gcd_eq_one hmul
  unfold Nat.ModEq at hmod
  simpa [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] using hmod

/-- The affine map `k ↦ shift+slope*k` permutes every complete residue system
when the slope is coprime to the modulus. -/
theorem affineMod_image_range_eq_range
    (L shift slope : ℕ) (hL : 0 < L) (hcop : Nat.Coprime slope L) :
    (Finset.range L).image (fun k => (shift + slope * k) % L) =
      Finset.range L := by
  apply Finset.eq_of_subset_of_card_le
  · intro n hn
    rcases Finset.mem_image.mp hn with ⟨k, hk, rfl⟩
    exact Finset.mem_range.mpr (Nat.mod_lt _ hL)
  · rw [Finset.card_range,
      Finset.card_image_of_injOn (affineMod_injOn_range L shift slope hL hcop)]
    simp

/-- Reindexing a predicate over a complete period by an affine permutation
does not change its count. -/
theorem affineMod_filter_card_eq
    (L shift slope : ℕ) (hL : 0 < L) (hcop : Nat.Coprime slope L)
    (pred : ℕ → Prop) [DecidablePred pred] :
    ((Finset.range L).filter
      (fun k => pred ((shift + slope * k) % L))).card =
      ((Finset.range L).filter pred).card := by
  let f : ℕ → ℕ := fun k => (shift + slope * k) % L
  have hinj : Set.InjOn f (Finset.range L : Set ℕ) :=
    affineMod_injOn_range L shift slope hL hcop
  have himage : (Finset.range L).image f = Finset.range L :=
    affineMod_image_range_eq_range L shift slope hL hcop
  have hfiltered :
      ((Finset.range L).filter (fun k => pred (f k))).image f =
        (Finset.range L).filter pred := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_image.mp hn with ⟨k, hk, rfl⟩
      have hfkRange : f k ∈ Finset.range L := by
        rw [← himage]
        exact Finset.mem_image.mpr ⟨k, (Finset.mem_filter.mp hk).1, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨hfkRange, (Finset.mem_filter.mp hk).2⟩
    · intro hn
      have hnRange : n ∈ (Finset.range L).image f := by
        rw [himage]
        exact (Finset.mem_filter.mp hn).1
      rcases Finset.mem_image.mp hnRange with ⟨k, hk, hkEq⟩
      exact Finset.mem_image.mpr
        ⟨k, Finset.mem_filter.mpr
          ⟨hk, by simpa [hkEq] using (Finset.mem_filter.mp hn).2⟩, hkEq⟩
  calc
    ((Finset.range L).filter (fun k => pred (f k))).card =
        (((Finset.range L).filter (fun k => pred (f k))).image f).card := by
      symm
      apply Finset.card_image_of_injOn
      exact hinj.mono (by exact Finset.filter_subset _ _)
    _ = ((Finset.range L).filter pred).card := by rw [hfiltered]

/-- Adding one full period adds exactly one complete-period predicate count. -/
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

/-- Exact complete-block decomposition of a periodic predicate count. -/
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

/-- A periodic count consists of complete blocks plus at most one point for
each position in its final partial block. -/
theorem periodic_count_le_complete_blocks_add_remainder
    (L T : ℕ) (hL : 0 < L) (pred : ℕ → Prop) [DecidablePred pred]
    (hperiodic : Function.Periodic pred L) :
    Nat.count pred T ≤
      (T / L) * Nat.count pred L + T % L := by
  have hdecomp : T = (T / L) * L + T % L := by
    rw [Nat.mul_comm, Nat.add_comm]
    exact (Nat.mod_add_div T L).symm
  calc
    Nat.count pred T =
        Nat.count pred ((T / L) * L + T % L) := by rw [← hdecomp]
    _ = (T / L) * Nat.count pred L + Nat.count pred (T % L) :=
      periodic_count_mul_add L (T / L) (T % L) pred hperiodic
    _ ≤ (T / L) * Nat.count pred L + T % L :=
      Nat.add_le_add_left (Nat.count_le (p := pred)) _

/-- Predicate that a residue avoids every event of a finite modular family. -/
def modularNoHitPred (events : Finset Inputs.ModularEvent) (n : ℕ) : Prop :=
  ∀ event ∈ events, ¬ event.Hits n

instance (events : Finset Inputs.ModularEvent) (n : ℕ) :
    Decidable (modularNoHitPred events n) := by
  unfold modularNoHitPred
  infer_instance

/-- Avoidance of modular events is periodic with any common multiple of all
event moduli. -/
theorem modularNoHitPred_periodic
    (L : ℕ) (events : Finset Inputs.ModularEvent)
    (hperiod : ∀ event ∈ events, event.modulus ∣ L) :
    Function.Periodic (modularNoHitPred events) L := by
  intro n
  apply propext
  constructor
  · intro h event hevent hhit
    apply h event hevent
    unfold Inputs.ModularEvent.Hits at hhit ⊢
    unfold Nat.ModEq at hhit ⊢
    simpa [Nat.add_mod, Nat.mod_eq_zero_of_dvd (hperiod event hevent)] using hhit
  · intro h event hevent hhit
    apply h event hevent
    unfold Inputs.ModularEvent.Hits at hhit ⊢
    unfold Nat.ModEq at hhit ⊢
    simpa [Nat.add_mod, Nat.mod_eq_zero_of_dvd (hperiod event hevent)] using hhit

/-- Reducing the affine parameter modulo a common period does not change the
no-hit predicate. -/
theorem modularNoHitPred_affine_mod
    (L shift slope k : ℕ) (events : Finset Inputs.ModularEvent)
    (hperiod : ∀ event ∈ events, event.modulus ∣ L) :
    modularNoHitPred events ((shift + slope * k) % L) ↔
      modularNoHitPred events (shift + slope * k) := by
  have hp := modularNoHitPred_periodic L events hperiod
  exact Iff.of_eq (hp.map_mod_nat (shift + slope * k))

/-- Over one complete parameter period, an affine base progression with
coprime step has exactly the uniform modular no-hit numerator. -/
theorem affineModularNoHit_count_period_eq
    (L shift slope : ℕ) (events : Finset Inputs.ModularEvent)
    (hL : 0 < L) (hcop : Nat.Coprime slope L)
    (hperiod : ∀ event ∈ events, event.modulus ∣ L) :
    Nat.count (fun k => modularNoHitPred events (shift + slope * k)) L =
      ((Finset.range L).filter (modularNoHitPred events)).card := by
  rw [Nat.count_eq_card_filter_range]
  calc
    ((Finset.range L).filter
        (fun k => modularNoHitPred events (shift + slope * k))).card =
      ((Finset.range L).filter
        (fun k => modularNoHitPred events ((shift + slope * k) % L))).card := by
        apply congrArg Finset.card
        apply Finset.filter_congr
        intro k hk
        exact (modularNoHitPred_affine_mod
          L shift slope k events hperiod).symm
    _ = ((Finset.range L).filter (modularNoHitPred events)).card :=
      affineMod_filter_card_eq L shift slope hL hcop (modularNoHitPred events)

/-- The event-count zero condition used by the finite exceptional-set sum is
exactly avoidance of the corresponding modular-event image. -/
theorem family_hitEventCount_zero_iff_modularNoHitPred
    (events : Finset EscLeanChecks.SatEvent)
    (hmodpos : ∀ event ∈ events,
      0 < EscLeanChecks.conditionalModulus event.dPlus event.p)
    (n : ℕ) :
    EscLeanChecks.hitEventCount events
        (fun event => EscLeanChecks.satEventHit n event) = 0 ↔
      modularNoHitPred (events.image familyModularEvent) n := by
  classical
  unfold EscLeanChecks.hitEventCount modularNoHitPred
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h modularEvent hmodularEvent hhit
    rcases Finset.mem_image.mp hmodularEvent with ⟨event, hevent, rfl⟩
    apply h hevent
    apply (EscLeanChecks.satEventHit_iff_modEq_residualHitRow
      n event (hmodpos event hevent)).1
    simpa [Inputs.ModularEvent.Hits, familyModularEvent,
      EscLeanChecks.satEventResidualHitRow] using hhit
  · intro h event hevent hhit
    apply h (familyModularEvent event) (Finset.mem_image.mpr ⟨event, hevent, rfl⟩)
    have hmod := (EscLeanChecks.satEventHit_iff_modEq_residualHitRow
      n event (hmodpos event hevent)).2 hhit
    simpa [Inputs.ModularEvent.Hits, familyModularEvent,
      EscLeanChecks.satEventResidualHitRow] using hmod

/-- The finite no-hit count in one base progression injects into the first
`N/Pz+1` values of its affine progression parameter. -/
theorem baseSatEventNoHitIndicatorSum_le_affine_count
    (N Pz b : ℕ) (events : Finset EscLeanChecks.SatEvent)
    (hPz : 0 < Pz)
    (hmodpos : ∀ event ∈ events,
      0 < EscLeanChecks.conditionalModulus event.dPlus event.p) :
    EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N Pz b events ≤
      Nat.count
        (fun k => modularNoHitPred (events.image familyModularEvent)
          (b % Pz + Pz * k)) (N / Pz + 1) := by
  classical
  let source : Finset ℕ :=
    ((Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz])).filter
      (fun n => EscLeanChecks.hitEventCount events
        (fun event => EscLeanChecks.satEventHit n event) = 0)
  let target : Finset ℕ :=
    (Finset.range (N / Pz + 1)).filter
      (fun k => modularNoHitPred (events.image familyModularEvent)
        (b % Pz + Pz * k))
  have hmaps : ∀ n ∈ source, n / Pz ∈ target := by
    intro n hn
    have hnSource := Finset.mem_filter.mp hn
    have hnBase := Finset.mem_filter.mp hnSource.1
    have hnLe : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hnBase.1)
    have hkRange : n / Pz < N / Pz + 1 :=
      Nat.lt_succ_of_le (Nat.div_le_div_right hnLe)
    have hnMod : n % Pz = b % Pz := hnBase.2
    have hnEq : b % Pz + Pz * (n / Pz) = n := by
      rw [← hnMod]
      exact Nat.mod_add_div n Pz
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hkRange,
        by rw [hnEq]; exact
          (family_hitEventCount_zero_iff_modularNoHitPred
            events hmodpos n).1 hnSource.2⟩
  have hinj : Set.InjOn (fun n => n / Pz) (source : Set ℕ) := by
    intro x hx y hy hdiv
    dsimp only at hdiv
    have hxBase := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
    have hyBase := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
    unfold Nat.ModEq at hxBase hyBase
    calc
      x = x % Pz + Pz * (x / Pz) := (Nat.mod_add_div x Pz).symm
      _ = y % Pz + Pz * (y / Pz) := by rw [hxBase, hyBase, hdiv]
      _ = y := Nat.mod_add_div y Pz
  have hcard : source.card ≤ target.card :=
    Finset.card_le_card_of_injOn (fun n => n / Pz) hmaps hinj
  have hsource :
      EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N Pz b events =
        (source.card : ℤ) := by
    unfold EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo source
    simp only [Finset.sum_boole]
  have htarget : target.card = Nat.count
      (fun k => modularNoHitPred (events.image familyModularEvent)
        (b % Pz + Pz * k)) (N / Pz + 1) := by
    simp [target, Nat.count_eq_card_filter_range]
  rw [hsource]
  exact_mod_cast hcard.trans_eq htarget

/-- Finite base-progression no-hit count bounded by complete modular periods
plus the exact length of the final partial block. -/
theorem baseSatEventNoHitIndicatorSum_le_modular_complete_blocks
    (N Pz b L : ℕ) (events : Finset EscLeanChecks.SatEvent)
    (hPz : 0 < Pz) (hL : 0 < L) (hcop : Nat.Coprime Pz L)
    (hmodpos : ∀ event ∈ events,
      0 < EscLeanChecks.conditionalModulus event.dPlus event.p)
    (hperiod : ∀ event ∈ events,
      EscLeanChecks.conditionalModulus event.dPlus event.p ∣ L) :
    EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N Pz b events ≤
      ((((N / Pz + 1) / L) *
          ((Finset.range L).filter
            (modularNoHitPred (events.image familyModularEvent))).card +
        (N / Pz + 1) % L : ℕ) : ℤ) := by
  let modularEvents := events.image familyModularEvent
  let pred : ℕ → Prop := fun k =>
    modularNoHitPred modularEvents (b % Pz + Pz * k)
  have hmodularPeriod : ∀ event ∈ modularEvents, event.modulus ∣ L := by
    intro modularEvent hmodularEvent
    rcases Finset.mem_image.mp hmodularEvent with ⟨event, hevent, rfl⟩
    exact hperiod event hevent
  have hpredPeriodic : Function.Periodic pred L := by
    intro k
    apply propext
    have hp := (modularNoHitPred_periodic L modularEvents hmodularPeriod).nsmul Pz
      (b % Pz + Pz * k)
    simpa [pred, Nat.mul_add, add_assoc, add_comm, add_left_comm] using hp
  have hfinite := baseSatEventNoHitIndicatorSum_le_affine_count
    N Pz b events hPz hmodpos
  have hblocks := periodic_count_le_complete_blocks_add_remainder
    L (N / Pz + 1) hL pred hpredPeriodic
  have hperiodCount := affineModularNoHit_count_period_eq
    L (b % Pz) Pz modularEvents hL hcop hmodularPeriod
  calc
    EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N Pz b events ≤
        (Nat.count pred (N / Pz + 1) : ℤ) := by
          simpa [pred, modularEvents] using hfinite
    _ ≤ (((N / Pz + 1) / L) * Nat.count pred L +
        (N / Pz + 1) % L : ℕ) := by exact_mod_cast hblocks
    _ = (((N / Pz + 1) / L) *
          ((Finset.range L).filter
            (modularNoHitPred modularEvents)).card +
        (N / Pz + 1) % L : ℕ) := by rw [hperiodCount]

/-- Real-valued finite transfer: progression length times the exact modular
no-hit probability, plus one common-period endpoint block. -/
theorem baseSatEventNoHitIndicatorSum_real_le_modularProbability_add_period
    (N Pz b L : ℕ) (events : Finset EscLeanChecks.SatEvent)
    (hPz : 0 < Pz) (hL : 0 < L) (hcop : Nat.Coprime Pz L)
    (hmodpos : ∀ event ∈ events,
      0 < EscLeanChecks.conditionalModulus event.dPlus event.p)
    (hperiod : ∀ event ∈ events,
      EscLeanChecks.conditionalModulus event.dPlus event.p ∣ L) :
    (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℝ) ≤
      (N / Pz + 1 : ℕ) *
          Inputs.modularNoHitProbability L (events.image familyModularEvent) +
        L := by
  let T := N / Pz + 1
  let modularEvents := events.image familyModularEvent
  let C := ((Finset.range L).filter (modularNoHitPred modularEvents)).card
  have hnat := baseSatEventNoHitIndicatorSum_le_modular_complete_blocks
    N Pz b L events hPz hL hcop hmodpos hperiod
  have hcast :
      (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℝ) ≤
        (((T / L) * C + T % L : ℕ) : ℝ) := by
    have hnat' :
        EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N Pz b events ≤
          (((T / L) * C + T % L : ℕ) : ℤ) := by
      simpa [T, C, modularEvents] using hnat
    have hreal := (Int.cast_le (R := ℝ)).2 hnat'
    simpa using hreal
  have hq : ((T / L : ℕ) : ℝ) ≤ (T : ℝ) / (L : ℝ) :=
    Nat.cast_div_le
  have hr : ((T % L : ℕ) : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast (Nat.mod_lt T hL).le
  have hC : 0 ≤ (C : ℝ) := by positivity
  have hprob : Inputs.modularNoHitProbability L modularEvents =
      (C : ℝ) / (L : ℝ) := by
    rfl
  calc
    (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℝ) ≤
        (((T / L) * C + T % L : ℕ) : ℝ) := hcast
    _ = ((T / L : ℕ) : ℝ) * (C : ℝ) + (T % L : ℕ) := by push_cast; rfl
    _ ≤ ((T : ℝ) / (L : ℝ)) * (C : ℝ) + L :=
      add_le_add (mul_le_mul_of_nonneg_right hq hC) hr
    _ = (T : ℝ) * Inputs.modularNoHitProbability L modularEvents + L := by
      rw [hprob]
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hL)]
    _ = (N / Pz + 1 : ℕ) *
          Inputs.modularNoHitProbability L (events.image familyModularEvent) + L := rfl

/-- If every selected large prime avoids the base modulus, the base modulus
is coprime to the actual family's complete modular period. -/
theorem familyModularPeriod_coprime_base_of_prime_not_dvd
    (P : Params) (X : ℝ) (Pz b : ℕ)
    (indices : Finset Family.FamilyIndex)
    (hPz : 0 < Pz)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i)
    (hnot : ∀ i ∈ indices, ¬ i.p ∣ Pz) :
    Nat.Coprime Pz (familyModularPeriod indices) := by
  let events := Family.familyEvents indices
  have hbaseCop : ∀ event ∈ events,
      Nat.Coprime Pz
        (EscLeanChecks.conditionalModulus event.dPlus event.p) :=
    Family.familyEvents_baseCoprime_residual_of_prime_not_dvd
      P X Pz b indices hnot hmem
  unfold familyModularPeriod
  apply EscLeanChecks.congruenceLcm_coprime_of_rows_coprime Pz
  · exact hPz
  · intro row hrow
    rcases List.mem_map.mp hrow with ⟨event, hevent, rfl⟩
    exact Family.familyEvents_residualModulus_pos
      P X Pz b indices hmem event (by simpa [events] using hevent)
  · intro row hrow
    rcases List.mem_map.mp hrow with ⟨event, hevent, rfl⟩
    simpa [EscLeanChecks.satEventResidualHitRow] using
      hbaseCop event (by simpa [events] using hevent)

/-- Actual-family finite transfer to the exact modular probability.  This is
the concrete finite-count bridge missing from the former scalar Suen route. -/
theorem actualPaperFamily_baseNoHit_real_le_modularProbability_add_period
    (P : Params) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → 1 < X → ∀ N b : ℕ,
      (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N
        (Inputs.roughModulus X) b
        (Family.familyEvents
          (Family.familyIndexFinset P X (Inputs.roughModulus X) b)) : ℝ) ≤
      (N / Inputs.roughModulus X + 1 : ℕ) *
          Inputs.modularNoHitProbability
            (familyModularPeriod
              (Family.familyIndexFinset P X (Inputs.roughModulus X) b))
            (familyModularEvents
              (Family.familyIndexFinset P X (Inputs.roughModulus X) b)) +
        familyModularPeriod
          (Family.familyIndexFinset P X (Inputs.roughModulus X) b) := by
  rcases floor_zScale_lt_primeScale_eventually P with ⟨X₀, hcut⟩
  refine ⟨X₀, ?_⟩
  intro X hX hXgt N b
  let Pz := Inputs.roughModulus X
  let indices := Family.familyIndexFinset P X Pz b
  let events := Family.familyEvents indices
  let L := familyModularPeriod indices
  have hPz : 0 < Pz := Inputs.roughModulus_pos X
  have hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i := by
    intro i hi
    exact (Family.mem_familyIndexFinset_iff P X Pz b i
      (lt_trans zero_lt_one hXgt)).1 hi
  have hnot : ∀ i ∈ indices, ¬ i.p ∣ Pz := by
    intro i hi hip
    have hpFloor := Inputs.prime_dvd_roughModulus_le_floor_zScale
      X (hmem i hi).p_prime hip
    have hpLower : ((⌊zScale X⌋₊ : ℕ) : ℝ) < (i.p : ℝ) :=
      lt_trans (hcut X hX) (hmem i hi).p_gt
    exact (not_lt_of_ge (by exact_mod_cast hpFloor)) hpLower
  have hL : 0 < L :=
    familyModularPeriod_pos P X Pz b indices hmem
  have hcop : Nat.Coprime Pz L :=
    familyModularPeriod_coprime_base_of_prime_not_dvd
      P X Pz b indices hPz hmem hnot
  have hmodpos : ∀ event ∈ events,
      0 < EscLeanChecks.conditionalModulus event.dPlus event.p := by
    intro event hevent
    exact Family.familyEvents_residualModulus_pos
      P X Pz b indices hmem event hevent
  have hperiod : ∀ event ∈ events,
      EscLeanChecks.conditionalModulus event.dPlus event.p ∣ L := by
    intro event hevent
    exact familyModularEvent_modulus_dvd_period indices hevent
  simpa [Pz, indices, events, L, familyModularEvents] using
    baseSatEventNoHitIndicatorSum_real_le_modularProbability_add_period
      N Pz b L events hPz hL hcop hmodpos hperiod

/-- End-to-end finite no-hit estimate for the actual family, using the exact
modular Suen model rather than the legacy scalar carrier. -/
theorem actualPaperFamily_baseNoHit_real_le_exp_add_period
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)]
    (base : ℝ → ℕ) (ambient : ℝ → ℕ)
    (hbase : ∀ᶠ X in Filter.atTop,
      Nat.Coprime (base X) (Inputs.roughModulus X))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X in Filter.atTop,
      (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo (ambient X)
        (Inputs.roughModulus X) (base X)
        (Family.familyEvents
          (Family.familyIndexFinset P X
            (Inputs.roughModulus X) (base X))) : ℝ) ≤
      (ambient X / Inputs.roughModulus X + 1 : ℕ) *
          Real.exp (-(1 - ε) *
            (Family.familyIndexMassRat
              (Family.familyIndexFinset P X
                (Inputs.roughModulus X) (base X)) : ℝ)) +
        familyModularPeriod
          (Family.familyIndexFinset P X
            (Inputs.roughModulus X) (base X)) := by
  rcases actualPaperFamily_baseNoHit_real_le_modularProbability_add_period P with
    ⟨Xfinite, hfinite⟩
  have hprob := actualPaperFamily_modularNoHit_le_exp_one_sub
    P base hbase ε hε
  filter_upwards [hprob,
      Filter.eventually_ge_atTop (max Xfinite (Real.exp 1))] with X hprobX hX
  have hXfinite : Xfinite ≤ X := le_trans (le_max_left _ _) hX
  have hXgt : 1 < X := lt_of_lt_of_le
    (Real.one_lt_exp_iff.mpr (by norm_num))
    (le_trans (le_max_right _ _) hX)
  have htransfer := hfinite X hXfinite hXgt (ambient X) (base X)
  calc
    (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo (ambient X)
        (Inputs.roughModulus X) (base X)
        (Family.familyEvents
          (Family.familyIndexFinset P X
            (Inputs.roughModulus X) (base X))) : ℝ) ≤
      (ambient X / Inputs.roughModulus X + 1 : ℕ) *
          Inputs.modularNoHitProbability
            (familyModularPeriod
              (Family.familyIndexFinset P X
                (Inputs.roughModulus X) (base X)))
            (familyModularEvents
              (Family.familyIndexFinset P X
                (Inputs.roughModulus X) (base X))) +
        familyModularPeriod
          (Family.familyIndexFinset P X
            (Inputs.roughModulus X) (base X)) := htransfer
    _ ≤ (ambient X / Inputs.roughModulus X + 1 : ℕ) *
          Real.exp (-(1 - ε) *
            (Family.familyIndexMassRat
              (Family.familyIndexFinset P X
                (Inputs.roughModulus X) (base X)) : ℝ)) +
        familyModularPeriod
          (Family.familyIndexFinset P X
            (Inputs.roughModulus X) (base X)) := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left hprobX (by positivity)) _

/-! ## Manuscript-aligned Bonferroni expectation in the exact CRT model -/

/-- Exactly one representative of a residue class occurs in one positive
modulus period. -/
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

/-- If `q` divides a complete period `L`, one residue class modulo `q`
occurs exactly `L/q` times in `range L`. -/
theorem modEq_count_complete_multiple
    (L q a : ℕ) (hq : 0 < q) (hqL : q ∣ L) :
    Nat.count (fun n => n ≡ a [MOD q]) L = L / q := by
  have hperiodic : Function.Periodic (fun n => n ≡ a [MOD q]) q := by
    intro n
    apply propext
    unfold Nat.ModEq
    simp [Nat.add_mod]
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

/-- A compatible subset of actual family events has exactly `L/L_S` common
hits in the complete family period. -/
theorem familyCompatibleSubset_commonHitCount_period_eq_div
    (P : Params) (X : ℝ) (Pz b : ℕ)
    (indices : Finset Family.FamilyIndex)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i)
    (subset : Finset EscLeanChecks.SatEvent)
    (hsub : subset ⊆ Family.familyEvents indices)
    (hcompat : ∀ event ∈ subset, ∀ other ∈ subset,
      event ≠ other → EscLeanChecks.satEventCompatible event other) :
    EscLeanChecks.eventSubsetCommonHitCount
        (Finset.range (familyModularPeriod indices))
        (fun n event => EscLeanChecks.satEventHit n event) subset =
      familyModularPeriod indices /
        EscLeanChecks.congruenceLcm
          (EscLeanChecks.satEventResidualHitRows subset.toList) := by
  classical
  let rows := EscLeanChecks.satEventResidualHitRows subset.toList
  let q := EscLeanChecks.congruenceLcm rows
  have hrowPos : EscLeanChecks.congruenceRowsModuliPositive rows := by
    intro row hrow
    rcases List.mem_map.mp hrow with ⟨event, hevent, rfl⟩
    exact Family.familyEvents_residualModulus_pos
      P X Pz b indices hmem event (hsub (by simpa using hevent))
  have hqPos : 0 < q :=
    EscLeanChecks.congruenceLcm_pos_of_rows_positive rows hrowPos
  have hrowCompat : EscLeanChecks.congruenceRowsPairwiseCompatible rows := by
    intro rowA hrowA rowB hrowB
    rcases List.mem_map.mp hrowA with ⟨event, hevent, rfl⟩
    rcases List.mem_map.mp hrowB with ⟨other, hother, rfl⟩
    have heventFin : event ∈ subset := by simpa using hevent
    have hotherFin : other ∈ subset := by simpa using hother
    by_cases heq : event = other
    · subst other
      unfold EscLeanChecks.residueCompatible
      exact Nat.ModEq.refl _
    · exact EscLeanChecks.satEventResidualHitRow_compatible_of_satEventCompatible
        event other
        (Family.familyEvents_residualModulus_pos
          P X Pz b indices hmem event (hsub heventFin))
        (Family.familyEvents_residualModulus_pos
          P X Pz b indices hmem other (hsub hotherFin))
        (hcompat event heventFin other hotherFin heq)
  rcases EscLeanChecks.congruenceRows_solution_exists_of_pairwiseCompatible
    rows hrowPos hrowCompat with ⟨solution, hsolution⟩
  have hqPeriod : q ∣ familyModularPeriod indices := by
    apply EscLeanChecks.congruenceLcm_dvd_of_forall_modulus_dvd
    intro row hrow
    rcases List.mem_map.mp hrow with ⟨event, hevent, rfl⟩
    exact familyModularEvent_modulus_dvd_period indices
      (hsub (by simpa using hevent))
  have hcount :
      EscLeanChecks.eventSubsetCommonHitCount
          (Finset.range (familyModularPeriod indices))
          (fun n event => EscLeanChecks.satEventHit n event) subset =
        Nat.count (fun n => n ≡ solution [MOD q])
          (familyModularPeriod indices) := by
    unfold EscLeanChecks.eventSubsetCommonHitCount
    rw [Nat.count_eq_card_filter_range]
    apply congrArg Finset.card
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, and_congr_right_iff]
    intro hn
    constructor
    · intro hhit
      apply EscLeanChecks.congruenceRows_unique_mod_lcm rows n solution
      · intro row hrow
        rcases List.mem_map.mp hrow with ⟨event, hevent, rfl⟩
        apply (EscLeanChecks.satEventHit_iff_modEq_residualHitRow n event
          (Family.familyEvents_residualModulus_pos P X Pz b indices hmem
            event (hsub (by simpa using hevent)))).2
        exact hhit event (by simpa using hevent)
      · exact hsolution
    · intro hmod event hevent
      apply (EscLeanChecks.satEventHit_iff_modEq_residualHitRow n event
        (Family.familyEvents_residualModulus_pos P X Pz b indices hmem
          event (hsub hevent))).1
      apply EscLeanChecks.congruenceRows_of_modEq_lcm rows solution n hsolution hmod
      exact List.mem_map.mpr ⟨event, by simpa using hevent, rfl⟩
  rw [hcount, modEq_count_complete_multiple
    (familyModularPeriod indices) q solution hqPos hqPeriod]

/-- An incompatible event subset has no common hit in any point set. -/
theorem familyIncompatibleSubset_commonHitCount_eq_zero
    (points : Finset ℕ) (subset : Finset EscLeanChecks.SatEvent)
    (hincompat : ¬ ∀ event ∈ subset, ∀ other ∈ subset,
      event ≠ other → EscLeanChecks.satEventCompatible event other) :
    EscLeanChecks.eventSubsetCommonHitCount points
        (fun n event => EscLeanChecks.satEventHit n event) subset = 0 := by
  classical
  unfold EscLeanChecks.eventSubsetCommonHitCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n hn hhit
  apply hincompat
  intro event hevent other hother hne
  exact EscLeanChecks.satEventCompatible_of_common_hit n event other
    (hhit event hevent) (hhit other hother)

/-- Rank-`r` common-hit total over the complete period of the actual family. -/
noncomputable def familyPeriodRankCommonHitCount
    (indices : Finset Family.FamilyIndex) (r : ℕ) : ℕ :=
  ∑ subset ∈ (Family.familyEvents indices).powersetCard r,
    EscLeanChecks.eventSubsetCommonHitCount
      (Finset.range (familyModularPeriod indices))
      (fun n event => EscLeanChecks.satEventHit n event) subset

/-- The normalized rank common-hit count in the exact CRT model is precisely
the manuscript's compatible reciprocal-LCM coefficient `F_r`. -/
theorem familyPeriodRankCommonHitDensity_eq_compatibleLcmMass
    (P : Params) (X : ℝ) (Pz b : ℕ)
    (indices : Finset Family.FamilyIndex)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i)
    (r : ℕ) :
    (familyPeriodRankCommonHitCount indices r : ℝ) /
        familyModularPeriod indices =
      (Family.familyCompatibleLcmMassRat indices r : ℝ) := by
  classical
  let all := (Family.familyEvents indices).powersetCard r
  let compatible := Family.familyCompatibleSubsetsOfCard indices r
  let count : Finset EscLeanChecks.SatEvent → ℕ := fun subset =>
    EscLeanChecks.eventSubsetCommonHitCount
      (Finset.range (familyModularPeriod indices))
      (fun n event => EscLeanChecks.satEventHit n event) subset
  have hsum : familyPeriodRankCommonHitCount indices r =
      ∑ subset ∈ compatible, count subset := by
    unfold familyPeriodRankCommonHitCount
    change (∑ subset ∈ all, count subset) = _
    calc
      (∑ subset ∈ all, count subset) =
          ∑ subset ∈ all,
            if (∀ event ∈ subset, ∀ other ∈ subset,
              event ≠ other → EscLeanChecks.satEventCompatible event other)
            then count subset else 0 := by
        apply Finset.sum_congr rfl
        intro subset hsubset
        split_ifs with hcompat
        · rfl
        · change count subset = 0
          exact familyIncompatibleSubset_commonHitCount_eq_zero
            (Finset.range (familyModularPeriod indices)) subset hcompat
      _ = ∑ subset ∈ compatible, count subset := by
        dsimp [compatible]
        rw [Family.familyCompatibleSubsetsOfCard]
        rw [Finset.sum_filter]
  dsimp [compatible] at hsum
  rw [hsum]
  unfold Family.familyCompatibleLcmMassRat
  rw [Rat.cast_sum, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro subset hsubset
  have hpower : subset ∈ all := by
    have hdata := hsubset
    rw [Family.familyCompatibleSubsetsOfCard] at hdata
    dsimp [all]
    exact Finset.mem_of_mem_filter subset hdata
  have hsub : subset ⊆ Family.familyEvents indices :=
    (Finset.mem_powersetCard.mp hpower).1
  have hcompat : ∀ event ∈ subset, ∀ other ∈ subset,
      event ≠ other → EscLeanChecks.satEventCompatible event other := by
    rw [Family.familyCompatibleSubsetsOfCard] at hsubset
    exact (Finset.mem_filter.mp hsubset).2
  change ((EscLeanChecks.eventSubsetCommonHitCount
      (Finset.range (familyModularPeriod indices))
      (fun n event => EscLeanChecks.satEventHit n event) subset : ℕ) : ℝ) /
      familyModularPeriod indices = _
  rw [familyCompatibleSubset_commonHitCount_period_eq_div
    P X Pz b indices hmem subset hsub hcompat]
  let q := EscLeanChecks.congruenceLcm
    (EscLeanChecks.satEventResidualHitRows subset.toList)
  have hqPos : 0 < q := by
    apply EscLeanChecks.congruenceLcm_pos_of_rows_positive
    intro row hrow
    rcases List.mem_map.mp hrow with ⟨event, hevent, rfl⟩
    exact Family.familyEvents_residualModulus_pos
      P X Pz b indices hmem event (hsub (by simpa using hevent))
  have hqPeriod : q ∣ familyModularPeriod indices := by
    apply EscLeanChecks.congruenceLcm_dvd_of_forall_modulus_dvd
    intro row hrow
    rcases List.mem_map.mp hrow with ⟨event, hevent, rfl⟩
    exact familyModularEvent_modulus_dvd_period indices
      (hsub (by simpa using hevent))
  rw [Nat.cast_div hqPeriod (by positivity : (q : ℝ) ≠ 0), Rat.cast_div]
  norm_num
  field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hqPos),
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt
      (familyModularPeriod_pos P X Pz b indices hmem))]
  dsimp [q]
  ring

/-- Unnormalized companion Bonferroni inequality over the actual family's
complete CRT period. -/
theorem familyPeriodAlternatingPrefix_le_noHit_add_topRank
    (P : Params) (X : ℝ) (Pz b R : ℕ)
    (indices : Finset Family.FamilyIndex)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i) :
    (∑ r ∈ Finset.range (2 * R + 1),
      ((-1 : ℤ) ^ r) * (familyPeriodRankCommonHitCount indices r : ℤ)) ≤
      (((Finset.range (familyModularPeriod indices)).filter
        (modularNoHitPred (familyModularEvents indices))).card : ℤ) +
        (familyPeriodRankCommonHitCount indices (2 * R) : ℤ) := by
  classical
  let events := Family.familyEvents indices
  let L := familyModularPeriod indices
  have hmodpos : ∀ event ∈ events,
      0 < EscLeanChecks.conditionalModulus event.dPlus event.p := by
    intro event hevent
    exact Family.familyEvents_residualModulus_pos
      P X Pz b indices hmem event hevent
  have hnohit :
      (Finset.range L).filter
          (fun n => EscLeanChecks.hitEventCount events
            (fun event => EscLeanChecks.satEventHit n event) = 0) =
        (Finset.range L).filter
          (modularNoHitPred (events.image familyModularEvent)) := by
    apply Finset.filter_congr
    intro n hn
    exact family_hitEventCount_zero_iff_modularNoHitPred events hmodpos n
  have hbonf :=
    EscLeanChecks.hitEventSubsets_bonferroni_upper_double_count
      (Finset.range L) events
      (fun n event => EscLeanChecks.satEventHit n event) R
  have hdouble := EscLeanChecks.hitEventSubsets_alternating_double_count
    (Finset.range L) events
    (fun n event => EscLeanChecks.satEventHit n event) (2 * R)
  calc
    (∑ r ∈ Finset.range (2 * R + 1),
      ((-1 : ℤ) ^ r) * (familyPeriodRankCommonHitCount indices r : ℤ)) =
      ∑ n ∈ Finset.range L,
        EscLeanChecks.alternatingChoosePrefix
          (EscLeanChecks.hitEventCount events
            (fun event => EscLeanChecks.satEventHit n event)) (2 * R) := by
        symm
        simpa [familyPeriodRankCommonHitCount, events, L] using hdouble
    _ ≤ (∑ n ∈ Finset.range L,
          if EscLeanChecks.hitEventCount events
            (fun event => EscLeanChecks.satEventHit n event) = 0
          then (1 : ℤ) else 0) +
        (familyPeriodRankCommonHitCount indices (2 * R) : ℤ) := by
          simpa [familyPeriodRankCommonHitCount, events, L] using hbonf
    _ = (((Finset.range (familyModularPeriod indices)).filter
          (modularNoHitPred (familyModularEvents indices))).card : ℤ) +
        (familyPeriodRankCommonHitCount indices (2 * R) : ℤ) := by
          rw [Finset.sum_boole, hnohit]
          rfl

/-- Paper-facing normalized companion bound: the truncated compatible-LCM
alternating sum is at most the exact modular no-hit probability plus its top
rank coefficient. -/
theorem familyCompatibleLcmAlternatingPrefix_le_modularNoHit_add_topRank
    (P : Params) (X : ℝ) (Pz b R : ℕ)
    (indices : Finset Family.FamilyIndex)
    (hmem : ∀ i ∈ indices, Family.FamilyStaticMem P X Pz b i) :
    (∑ r ∈ Finset.range (2 * R + 1),
      (-1 : ℝ) ^ r * (Family.familyCompatibleLcmMassRat indices r : ℝ)) ≤
      Inputs.modularNoHitProbability
          (familyModularPeriod indices) (familyModularEvents indices) +
        (Family.familyCompatibleLcmMassRat indices (2 * R) : ℝ) := by
  let L := familyModularPeriod indices
  let C := ((Finset.range L).filter
    (modularNoHitPred (familyModularEvents indices))).card
  have hL : 0 < L := familyModularPeriod_pos P X Pz b indices hmem
  have hbonf := familyPeriodAlternatingPrefix_le_noHit_add_topRank
    P X Pz b R indices hmem
  have hbonfR :
      ((∑ r ∈ Finset.range (2 * R + 1),
        ((-1 : ℤ) ^ r) *
          (familyPeriodRankCommonHitCount indices r : ℤ) : ℤ) : ℝ) ≤
        ((C : ℕ) : ℝ) +
          (familyPeriodRankCommonHitCount indices (2 * R) : ℝ) := by
    have hcast := (Int.cast_le (R := ℝ)).2 hbonf
    simpa [L, C] using hcast
  have hdiv := div_le_div_of_nonneg_right hbonfR (by positivity : 0 ≤ (L : ℝ))
  have hleft :
      ((↑(∑ r ∈ Finset.range (2 * R + 1),
        ((-1 : ℤ) ^ r) *
          (familyPeriodRankCommonHitCount indices r : ℤ)) : ℝ) / L) =
        ∑ r ∈ Finset.range (2 * R + 1),
          (-1 : ℝ) ^ r *
            (Family.familyCompatibleLcmMassRat indices r : ℝ) := by
    rw [Int.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
    have hdensity := familyPeriodRankCommonHitDensity_eq_compatibleLcmMass
      P X Pz b indices hmem r
    calc
      ((-1 : ℝ) ^ r *
          (familyPeriodRankCommonHitCount indices r : ℝ)) / L =
        (-1 : ℝ) ^ r *
          ((familyPeriodRankCommonHitCount indices r : ℝ) / L) := by ring
      _ = _ := by rw [hdensity]
  have hright :
      (((C : ℕ) : ℝ) +
          (familyPeriodRankCommonHitCount indices (2 * R) : ℝ)) / L =
        Inputs.modularNoHitProbability L (familyModularEvents indices) +
          (Family.familyCompatibleLcmMassRat indices (2 * R) : ℝ) := by
    rw [add_div]
    have htop := familyPeriodRankCommonHitDensity_eq_compatibleLcmMass
      P X Pz b indices hmem (2 * R)
    rw [htop]
    rfl
  rw [hleft, hright] at hdiv
  exact hdiv

/-- Actual manuscript finite-interval decomposition with its model term
controlled by the exact modular no-hit probability and the top Bonferroni
rank.  The endpoint remains the paper's sharp `X^r F_r` sum. -/
theorem actualPaperFamily_baseNoHit_real_le_modularNoHit_add_topRank_endpoint
    (P : Params) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → 1 < X →
      ∀ N b R : ℕ,
      (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N
        (Inputs.roughModulus X) b
        (Family.familyEvents
          (Family.familyIndexFinset P X (Inputs.roughModulus X) b)) : ℝ) ≤
      (N : ℝ) / (Inputs.roughModulus X : ℝ) *
          (Inputs.modularNoHitProbability
              (familyModularPeriod
                (Family.familyIndexFinset P X (Inputs.roughModulus X) b))
              (familyModularEvents
                (Family.familyIndexFinset P X (Inputs.roughModulus X) b)) +
            (Family.familyCompatibleLcmMassRat
              (Family.familyIndexFinset P X (Inputs.roughModulus X) b)
              (2 * R) : ℝ)) +
        ∑ r ∈ Finset.range (2 * R + 1),
          (⌊X⌋₊ : ℝ) ^ r *
            (Family.familyCompatibleLcmMassRat
              (Family.familyIndexFinset P X (Inputs.roughModulus X) b) r : ℝ) := by
  rcases actualPaperFamily_baseNoHitRat_le_lcmMain_add_endpoint P with
    ⟨X₀, hfinite⟩
  refine ⟨X₀, ?_⟩
  intro X hX hXgt N b R
  let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
  have hmem : ∀ i ∈ indices,
      Family.FamilyStaticMem P X (Inputs.roughModulus X) b i := by
    intro i hi
    exact (Family.mem_familyIndexFinset_iff P X
      (Inputs.roughModulus X) b i (lt_trans zero_lt_one hXgt)).1 hi
  have hfiniteQ := hfinite X hX hXgt N b R
  have hfiniteR := (Rat.cast_le (K := ℝ)).2 hfiniteQ
  have hmodel := familyCompatibleLcmAlternatingPrefix_le_modularNoHit_add_topRank
    P X (Inputs.roughModulus X) b R indices hmem
  have hmainNonneg : 0 ≤ (N : ℝ) / (Inputs.roughModulus X : ℝ) := by
    positivity
  calc
    (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N
        (Inputs.roughModulus X) b (Family.familyEvents indices) : ℝ) ≤
      (N : ℝ) / (Inputs.roughModulus X : ℝ) *
          (∑ r ∈ Finset.range (2 * R + 1),
            (-1 : ℝ) ^ r *
              (Family.familyCompatibleLcmMassRat indices r : ℝ)) +
        ∑ r ∈ Finset.range (2 * R + 1),
          (⌊X⌋₊ : ℝ) ^ r *
            (Family.familyCompatibleLcmMassRat indices r : ℝ) := by
      simpa [indices, Rat.cast_sum, Rat.cast_mul, Rat.cast_div,
        Rat.cast_pow] using hfiniteR
    _ ≤ (N : ℝ) / (Inputs.roughModulus X : ℝ) *
          (Inputs.modularNoHitProbability
              (familyModularPeriod indices) (familyModularEvents indices) +
            (Family.familyCompatibleLcmMassRat indices (2 * R) : ℝ)) +
        ∑ r ∈ Finset.range (2 * R + 1),
          (⌊X⌋₊ : ℝ) ^ r *
            (Family.familyCompatibleLcmMassRat indices r : ℝ) := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left hmodel hmainNonneg) _

/-- Manuscript-aligned actual-family finite transfer after inserting the exact
modular Suen exponential bound.  No legacy `suenProb` carrier occurs. -/
theorem actualPaperFamily_baseNoHit_real_le_exp_add_topRank_endpoint
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)]
    (base ambient rank : ℝ → ℕ)
    (hbase : ∀ᶠ X in Filter.atTop,
      Nat.Coprime (base X) (Inputs.roughModulus X))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X in Filter.atTop,
      (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo (ambient X)
        (Inputs.roughModulus X) (base X)
        (Family.familyEvents
          (Family.familyIndexFinset P X
            (Inputs.roughModulus X) (base X))) : ℝ) ≤
      (ambient X : ℝ) / (Inputs.roughModulus X : ℝ) *
          (Real.exp (-(1 - ε) *
              (Family.familyIndexMassRat
                (Family.familyIndexFinset P X
                  (Inputs.roughModulus X) (base X)) : ℝ)) +
            (Family.familyCompatibleLcmMassRat
              (Family.familyIndexFinset P X
                (Inputs.roughModulus X) (base X))
              (2 * rank X) : ℝ)) +
        ∑ r ∈ Finset.range (2 * rank X + 1),
          (⌊X⌋₊ : ℝ) ^ r *
            (Family.familyCompatibleLcmMassRat
              (Family.familyIndexFinset P X
                (Inputs.roughModulus X) (base X)) r : ℝ) := by
  rcases actualPaperFamily_baseNoHit_real_le_modularNoHit_add_topRank_endpoint P with
    ⟨Xfinite, hfinite⟩
  have hprob := actualPaperFamily_modularNoHit_le_exp_one_sub
    P base hbase ε hε
  filter_upwards [hprob,
      Filter.eventually_ge_atTop (max Xfinite (Real.exp 1))] with X hprobX hX
  have hXfinite : Xfinite ≤ X := le_trans (le_max_left _ _) hX
  have hXgt : 1 < X := lt_of_lt_of_le
    (Real.one_lt_exp_iff.mpr (by norm_num))
    (le_trans (le_max_right _ _) hX)
  have htransfer := hfinite X hXfinite hXgt
    (ambient X) (base X) (rank X)
  have hscaleNonneg :
      0 ≤ (ambient X : ℝ) / (Inputs.roughModulus X : ℝ) := by
    positivity
  calc
    (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo (ambient X)
        (Inputs.roughModulus X) (base X)
        (Family.familyEvents
          (Family.familyIndexFinset P X
            (Inputs.roughModulus X) (base X))) : ℝ) ≤
      (ambient X : ℝ) / (Inputs.roughModulus X : ℝ) *
          (Inputs.modularNoHitProbability
              (familyModularPeriod
                (Family.familyIndexFinset P X
                  (Inputs.roughModulus X) (base X)))
              (familyModularEvents
                (Family.familyIndexFinset P X
                  (Inputs.roughModulus X) (base X))) +
            (Family.familyCompatibleLcmMassRat
              (Family.familyIndexFinset P X
                (Inputs.roughModulus X) (base X))
              (2 * rank X) : ℝ)) +
        ∑ r ∈ Finset.range (2 * rank X + 1),
          (⌊X⌋₊ : ℝ) ^ r *
            (Family.familyCompatibleLcmMassRat
              (Family.familyIndexFinset P X
                (Inputs.roughModulus X) (base X)) r : ℝ) := htransfer
    _ ≤ (ambient X : ℝ) / (Inputs.roughModulus X : ℝ) *
          (Real.exp (-(1 - ε) *
              (Family.familyIndexMassRat
                (Family.familyIndexFinset P X
                  (Inputs.roughModulus X) (base X)) : ℝ)) +
            (Family.familyCompatibleLcmMassRat
              (Family.familyIndexFinset P X
                (Inputs.roughModulus X) (base X))
              (2 * rank X) : ℝ)) +
        ∑ r ∈ Finset.range (2 * rank X + 1),
          (⌊X⌋₊ : ℝ) ^ r *
            (Family.familyCompatibleLcmMassRat
              (Family.familyIndexFinset P X
                (Inputs.roughModulus X) (base X)) r : ℝ) := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left (add_le_add_right hprobX _) hscaleNonneg) _

/-! ## Canonical top-rank and endpoint discharge -/

/-- The manuscript's canonical Bonferroni rank `floor(12 μ)+1`. -/
noncomputable def canonicalBrunRank (μ : ℝ) : ℕ := ⌊12 * μ⌋₊ + 1

/-- The canonical rank is at least `12 μ` for nonnegative mass. -/
theorem twelve_mul_le_canonicalBrunRank
    {μ : ℝ} (hμ : 0 ≤ μ) :
    12 * μ ≤ (canonicalBrunRank μ : ℝ) := by
  unfold canonicalBrunRank
  have hlt : 12 * μ < ((⌊12 * μ⌋₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_floor_add_one (12 * μ)
  exact hlt.le

/-- Consequently `2R ≥ 24 μ`, the rank condition needed for the elementary
factorial tail. -/
theorem twentyFour_mul_le_two_canonicalBrunRank
    {μ : ℝ} (hμ : 0 ≤ μ) :
    24 * μ ≤ (2 * canonicalBrunRank μ : ℕ) := by
  have h := twelve_mul_le_canonicalBrunRank hμ
  norm_num at h ⊢
  nlinarith

/-- Pointwise top-rank discharge for the actual family.  Once the bounded-rank
increment error is at most one, the coefficient at the canonical even rank is
at most `exp(-3 μ)`. -/
theorem actualPaperFamily_topRank_le_exp_neg_three_of_scalar
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ K : ℚ, ∃ X₀ : ℝ, 0 < K ∧ ∀ X : ℝ,
      X₀ ≤ X → Real.exp 2 ≤ X →
      ∀ b : ℕ, Nat.Coprime b (Inputs.roughModulus X) →
      let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
      let μ := (Family.familyIndexMassRat indices : ℝ)
      let R := canonicalBrunRank μ
      (K : ℝ) *
          (Real.exp (((2 * R : ℕ) : ℝ) *
            paperIncrementFloorScale P X) - 1) ≤ 1 →
      (Family.familyCompatibleLcmMassRat indices (2 * R) : ℝ) ≤
        Real.exp (-3 * μ) := by
  rcases actualPaperFamily_compatibleLcmMassRat_le_up_to_of_rank_scale P with
    ⟨K, X₀, hK, hcoef⟩
  refine ⟨K, X₀, hK, ?_⟩
  intro X hX hXexp b hbcop
  dsimp only
  let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
  let μ := (Family.familyIndexMassRat indices : ℝ)
  let R := canonicalBrunRank μ
  intro hscalar
  have hμQ : 0 ≤ Family.familyIndexMassRat indices := by
    unfold Family.familyIndexMassRat
    apply Finset.sum_nonneg
    intro i hi
    unfold Family.FamilyIndex.wRat
    positivity
  have hμ : 0 ≤ μ := by
    simpa [μ] using (Rat.cast_nonneg.mpr hμQ :
      (0 : ℝ) ≤ (Family.familyIndexMassRat indices : ℝ))
  have hcoefQ := hcoef X hX hXexp b hbcop 1 (by norm_num)
    (2 * R) (by simpa [R] using hscalar) (2 * R) le_rfl
  have hcoefR :
      (Family.familyCompatibleLcmMassRat indices (2 * R) : ℝ) ≤
        (2 * μ) ^ (2 * R) / (Nat.factorial (2 * R) : ℝ) := by
    have hcast :
        (Family.familyCompatibleLcmMassRat indices (2 * R) : ℝ) ≤
          (((Family.familyIndexMassRat indices * (1 + 1)) ^ (2 * R) /
            (Nat.factorial (2 * R) : ℚ) : ℚ) : ℝ) := by
      exact_mod_cast hcoefQ
    convert hcast using 1 <;> simp [μ] <;> ring
  have htail :
      (2 * μ) ^ (2 * R) / (Nat.factorial (2 * R) : ℝ) ≤
        Real.exp (-3 * μ) := by
    apply scalar_two_mu_factorial_tail_of_rank_ge hμ
    simpa [R, Nat.cast_mul] using
      (twentyFour_mul_le_two_canonicalBrunRank hμ)
  exact hcoefR.trans
    htail

/-- For the actual family, the scalar premise in the pointwise top-rank
estimate holds uniformly in the base residue once `X` is large. -/
theorem actualPaperFamily_topRank_le_exp_neg_three
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → Real.exp 2 ≤ X →
      ∀ b : ℕ, Nat.Coprime b (Inputs.roughModulus X) →
      let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
      let μ := (Family.familyIndexMassRat indices : ℝ)
      let R := canonicalBrunRank μ
      (Family.familyCompatibleLcmMassRat indices (2 * R) : ℝ) ≤
        Real.exp (-3 * μ) := by
  rcases actualPaperFamily_topRank_le_exp_neg_three_of_scalar P with
    ⟨K, XK, hK, htop⟩
  rcases actualPaperFamily_indexMassRat_ge_log_cube P with
    ⟨c, Xc, hc, hlower⟩
  rcases actualPaperFamily_indexMassRat_le_log_cube P with
    ⟨C, XC, hC, hupper⟩
  have herr := paperIncrementCubicRankError_tendsto_zero
    P (K : ℝ) (26 * C)
  have herr_one : ∀ᶠ X in Filter.atTop,
      (K : ℝ) *
        (Real.exp ((26 * C) *
          ((Real.log X) ^ 3 * paperIncrementFloorScale P X)) - 1) ≤ 1 :=
    Filter.Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) herr
  rcases (Filter.eventually_atTop.1 herr_one) with ⟨XE, hXE⟩
  let Xone := Real.exp (max 1 (1 / c))
  refine ⟨max (max (max XK Xc) XC) (max XE Xone), ?_⟩
  intro X hX hXexp b hbcop
  dsimp only
  let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
  let μ := (Family.familyIndexMassRat indices : ℝ)
  let R := canonicalBrunRank μ
  apply htop X
  · exact le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hX))
  · exact hXexp
  · exact hbcop
  have hXgt : 1 < X := lt_of_lt_of_le
    (lt_of_lt_of_le (by norm_num : (1 : ℝ) < Real.exp 2) hXexp) le_rfl
  have hmassLower : c * (Real.log X) ^ 3 ≤ μ := by
    apply hlower X
    · exact le_trans (le_max_right _ _)
        (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hX))
    · exact hXgt
    · exact hbcop
  have hmassUpper : μ ≤ C * (Real.log X) ^ 3 := by
    apply hupper X
    · exact le_trans (le_max_right _ _)
        (le_trans (le_max_left _ _) hX)
    · exact hXgt
    · exact hbcop
  have hXone : Xone ≤ X :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX)
  have hlog : max 1 (1 / c) ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (lt_trans zero_lt_one hXgt)]
    exact hXone
  have hlog_one : 1 ≤ Real.log X := (le_max_left _ _).trans hlog
  have hc_inv : 1 / c ≤ Real.log X := (le_max_right _ _).trans hlog
  have hcube_ge_log : Real.log X ≤ (Real.log X) ^ 3 := by
    nlinarith [sq_nonneg (Real.log X - 1)]
  have hμ_one : 1 ≤ μ := by
    have hc_nonneg : 0 ≤ c := hc.le
    have hc_mul : 1 ≤ c * Real.log X := by
      calc
        1 = c * (1 / c) := by field_simp
        _ ≤ c * Real.log X := mul_le_mul_of_nonneg_left hc_inv hc_nonneg
    calc
      1 ≤ c * Real.log X := hc_mul
      _ ≤ c * (Real.log X) ^ 3 :=
        mul_le_mul_of_nonneg_left hcube_ge_log hc_nonneg
      _ ≤ μ := hmassLower
  have hR : ((2 * R : ℕ) : ℝ) ≤
      (26 * C) * (Real.log X) ^ 3 := by
    calc
      ((2 * R : ℕ) : ℝ) = 2 * (R : ℝ) := by norm_num
      _ ≤ 2 * (13 * μ) :=
        mul_le_mul_of_nonneg_left (brunFloorRank_le_thirteen_mul hμ_one)
          (by norm_num)
      _ ≤ 26 * (C * (Real.log X) ^ 3) := by nlinarith
      _ = (26 * C) * (Real.log X) ^ 3 := by ring
  have hEnvelope := hXE X
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX))
  exact (paperIncrementRankError_le_cubicRankError P hXexp
    (Rat.cast_nonneg.mpr hK.le) (mul_nonneg (by norm_num) hC.le) hR).trans
      hEnvelope

/-- The same bounded-rank coefficient estimate controls the complete sharp
finite-interval endpoint by the manuscript's exponential envelope. -/
theorem actualPaperFamily_endpoint_le_of_scalar
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ K : ℚ, ∃ X₀ : ℝ, 0 < K ∧ ∀ X : ℝ,
      X₀ ≤ X → Real.exp 2 ≤ X →
      ∀ b : ℕ, Nat.Coprime b (Inputs.roughModulus X) →
      let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
      let μ := (Family.familyIndexMassRat indices : ℝ)
      let R := canonicalBrunRank μ
      (K : ℝ) *
          (Real.exp (((2 * R : ℕ) : ℝ) *
            paperIncrementFloorScale P X) - 1) ≤ 1 →
      (∑ r ∈ Finset.range (2 * R + 1),
          (⌊X⌋₊ : ℝ) ^ r *
            (Family.familyCompatibleLcmMassRat indices r : ℝ)) ≤
        X ^ (2 * R) * Real.exp (2 * μ) := by
  rcases actualPaperFamily_compatibleLcmMassRat_le_up_to_of_rank_scale P with
    ⟨K, X₀, hK, hcoef⟩
  refine ⟨K, X₀, hK, ?_⟩
  intro X hX hXexp b hbcop
  dsimp only
  let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
  let μ := (Family.familyIndexMassRat indices : ℝ)
  let R := canonicalBrunRank μ
  intro hscalar
  have hμQ : 0 ≤ Family.familyIndexMassRat indices := by
    unfold Family.familyIndexMassRat
    apply Finset.sum_nonneg
    intro i hi
    unfold Family.FamilyIndex.wRat
    positivity
  have hμ : 0 ≤ μ := by
    simpa [μ] using (Rat.cast_nonneg.mpr hμQ :
      (0 : ℝ) ≤ (Family.familyIndexMassRat indices : ℝ))
  have hcoefR : ∀ r : ℕ, r ≤ 2 * R →
      (Family.familyCompatibleLcmMassRat indices r : ℝ) ≤
        (2 * μ) ^ r / (Nat.factorial r : ℝ) := by
    intro r hr
    have hcoefQ := hcoef X hX hXexp b hbcop 1 (by norm_num)
      (2 * R) (by simpa [R] using hscalar) r hr
    have hcast :
        (Family.familyCompatibleLcmMassRat indices r : ℝ) ≤
          (((Family.familyIndexMassRat indices * (1 + 1)) ^ r /
            (Nat.factorial r : ℚ) : ℚ) : ℝ) := by
      exact_mod_cast hcoefQ
    convert hcast using 1 <;> simp [μ] <;> ring
  have hfloor_one : (1 : ℝ) ≤ (⌊X⌋₊ : ℝ) := by
    exact_mod_cast (Nat.le_floor
      (le_trans (by norm_num : ((1 : ℕ) : ℝ) ≤ Real.exp 2) hXexp) :
        1 ≤ ⌊X⌋₊)
  have henvelope := brun_envelope_of_factorial_bound_up_to
    (fun r => (Family.familyCompatibleLcmMassRat indices r : ℝ))
    (2 * μ) (⌊X⌋₊ : ℝ) (2 * R) (mul_nonneg (by norm_num) hμ)
    hfloor_one hcoefR
  have hfloor_le : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le
    (le_trans (by positivity : (0 : ℝ) ≤ Real.exp 2) hXexp)
  exact henvelope.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) hfloor_le (2 * R))
    (Real.exp_pos _).le)

/-- Any fixed nonnegative increment constant satisfies the canonical
two-rank scalar condition uniformly over admissible base residues. -/
theorem actualPaperFamily_canonicalScalar_eventually
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)]
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → Real.exp 2 ≤ X →
      ∀ b : ℕ, Nat.Coprime b (Inputs.roughModulus X) →
      let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
      let μ := (Family.familyIndexMassRat indices : ℝ)
      let R := canonicalBrunRank μ
      K * (Real.exp (((2 * R : ℕ) : ℝ) *
        paperIncrementFloorScale P X) - 1) ≤ 1 := by
  rcases actualPaperFamily_indexMassRat_ge_log_cube P with
    ⟨c, Xc, hc, hlower⟩
  rcases actualPaperFamily_indexMassRat_le_log_cube P with
    ⟨C, XC, hC, hupper⟩
  have herr := paperIncrementCubicRankError_tendsto_zero P K (26 * C)
  have herr_one : ∀ᶠ X in Filter.atTop,
      K * (Real.exp ((26 * C) *
        ((Real.log X) ^ 3 * paperIncrementFloorScale P X)) - 1) ≤ 1 :=
    Filter.Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) herr
  rcases Filter.eventually_atTop.1 herr_one with ⟨XE, hXE⟩
  let Xone := Real.exp (max 1 (1 / c))
  refine ⟨max (max Xc XC) (max XE Xone), ?_⟩
  intro X hX hXexp b hbcop
  dsimp only
  let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
  let μ := (Family.familyIndexMassRat indices : ℝ)
  let R := canonicalBrunRank μ
  have hXgt : 1 < X := lt_of_lt_of_le
    (by norm_num : (1 : ℝ) < Real.exp 2) hXexp
  have hmassLower : c * (Real.log X) ^ 3 ≤ μ := by
    apply hlower X
    · exact le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _) hX)
    · exact hXgt
    · exact hbcop
  have hmassUpper : μ ≤ C * (Real.log X) ^ 3 := by
    apply hupper X
    · exact le_trans (le_max_right _ _)
        (le_trans (le_max_left _ _) hX)
    · exact hXgt
    · exact hbcop
  have hXone : Xone ≤ X :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX)
  have hlog : max 1 (1 / c) ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (lt_trans zero_lt_one hXgt)]
    exact hXone
  have hlog_one : 1 ≤ Real.log X := (le_max_left _ _).trans hlog
  have hc_inv : 1 / c ≤ Real.log X := (le_max_right _ _).trans hlog
  have hcube_ge_log : Real.log X ≤ (Real.log X) ^ 3 := by
    nlinarith [sq_nonneg (Real.log X - 1)]
  have hμ_one : 1 ≤ μ := by
    have hc_nonneg : 0 ≤ c := hc.le
    have hc_mul : 1 ≤ c * Real.log X := by
      calc
        1 = c * (1 / c) := by field_simp
        _ ≤ c * Real.log X := mul_le_mul_of_nonneg_left hc_inv hc_nonneg
    exact hc_mul.trans ((mul_le_mul_of_nonneg_left hcube_ge_log hc_nonneg).trans
      hmassLower)
  have hR : ((2 * R : ℕ) : ℝ) ≤
      (26 * C) * (Real.log X) ^ 3 := by
    calc
      ((2 * R : ℕ) : ℝ) = 2 * (R : ℝ) := by norm_num
      _ ≤ 2 * (13 * μ) :=
        mul_le_mul_of_nonneg_left (brunFloorRank_le_thirteen_mul hμ_one)
          (by norm_num)
      _ ≤ 26 * (C * (Real.log X) ^ 3) := by nlinarith
      _ = (26 * C) * (Real.log X) ^ 3 := by ring
  have hEnvelope := hXE X
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX))
  exact (paperIncrementRankError_le_cubicRankError P hXexp hK
    (mul_nonneg (by norm_num) hC.le) hR).trans hEnvelope

/-- The manuscript's level condition absorbs the complete finite-interval
endpoint at the canonical rank. -/
theorem actualPaperFamily_endpoint_le_of_level
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)]
    (base ambient : ℝ → ℕ)
    (hbase : ∀ᶠ X in Filter.atTop,
      Nat.Coprime (base X) (Inputs.roughModulus X))
    (hlevel : ∀ᶠ X in Filter.atTop,
      let indices := Family.familyIndexFinset P X
        (Inputs.roughModulus X) (base X)
      let μ := (Family.familyIndexMassRat indices : ℝ)
      let R := canonicalBrunRank μ
      (Inputs.roughModulus X : ℝ) *
          (X ^ (2 * R) * Real.exp (2 * μ)) ≤
        (ambient X : ℝ) * Real.exp (-4 * μ)) :
    ∀ᶠ X in Filter.atTop,
      let indices := Family.familyIndexFinset P X
        (Inputs.roughModulus X) (base X)
      let μ := (Family.familyIndexMassRat indices : ℝ)
      let R := canonicalBrunRank μ
      (∑ r ∈ Finset.range (2 * R + 1),
          (⌊X⌋₊ : ℝ) ^ r *
            (Family.familyCompatibleLcmMassRat indices r : ℝ)) ≤
        (ambient X : ℝ) / (Inputs.roughModulus X : ℝ) *
          Real.exp (-4 * μ) := by
  rcases actualPaperFamily_endpoint_le_of_scalar P with
    ⟨K, XK, hK, hendpoint⟩
  rcases actualPaperFamily_canonicalScalar_eventually P (K : ℝ)
      (Rat.cast_nonneg.mpr hK.le) with ⟨XS, hscalar⟩
  filter_upwards [hbase, hlevel,
      Filter.eventually_ge_atTop (max (max XK XS) (Real.exp 2))] with
      X hcop hlevelX hX
  dsimp only at hlevelX ⊢
  let indices := Family.familyIndexFinset P X
    (Inputs.roughModulus X) (base X)
  let μ := (Family.familyIndexMassRat indices : ℝ)
  let R := canonicalBrunRank μ
  have hXK : XK ≤ X :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hX)
  have hXS : XS ≤ X :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hX)
  have hXexp : Real.exp 2 ≤ X := le_trans (le_max_right _ _) hX
  have hscalarX : (K : ℝ) *
      (Real.exp (((2 * R : ℕ) : ℝ) *
        paperIncrementFloorScale P X) - 1) ≤ 1 := by
    simpa [indices, μ, R] using hscalar X hXS hXexp (base X) hcop
  have hendpointX :
      (∑ r ∈ Finset.range (2 * R + 1),
          (⌊X⌋₊ : ℝ) ^ r *
            (Family.familyCompatibleLcmMassRat indices r : ℝ)) ≤
        X ^ (2 * R) * Real.exp (2 * μ) := by
    simpa [indices, μ, R] using
      hendpoint X hXK hXexp (base X) hcop hscalarX
  have hq : (0 : ℝ) < (Inputs.roughModulus X : ℝ) := by
    exact_mod_cast Inputs.roughModulus_pos X
  have habsorb : X ^ (2 * R) * Real.exp (2 * μ) ≤
      ((ambient X : ℝ) * Real.exp (-4 * μ)) /
        (Inputs.roughModulus X : ℝ) := by
    apply (le_div_iff₀ hq).2
    simpa [mul_comm, mul_left_comm, mul_assoc, indices, μ, R] using hlevelX
  calc
    (∑ r ∈ Finset.range (2 * R + 1),
        (⌊X⌋₊ : ℝ) ^ r *
          (Family.familyCompatibleLcmMassRat indices r : ℝ)) ≤
        X ^ (2 * R) * Real.exp (2 * μ) := hendpointX
    _ ≤ ((ambient X : ℝ) * Real.exp (-4 * μ)) /
        (Inputs.roughModulus X : ℝ) := habsorb
    _ = (ambient X : ℝ) / (Inputs.roughModulus X : ℝ) *
        Real.exp (-4 * μ) := by field_simp

/-- Manuscript-aligned finite transfer at the canonical Brun rank.  Apart from
the cited analytic inputs used upstream, the only premise is the manuscript's
explicit level condition. -/
theorem actualPaperFamily_baseNoHit_le_canonical_exponentials_of_level
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)]
    (base ambient : ℝ → ℕ)
    (hbase : ∀ᶠ X in Filter.atTop,
      Nat.Coprime (base X) (Inputs.roughModulus X))
    (ε : ℝ) (hε : 0 < ε)
    (hlevel : ∀ᶠ X in Filter.atTop,
      let indices := Family.familyIndexFinset P X
        (Inputs.roughModulus X) (base X)
      let μ := (Family.familyIndexMassRat indices : ℝ)
      let R := canonicalBrunRank μ
      (Inputs.roughModulus X : ℝ) *
          (X ^ (2 * R) * Real.exp (2 * μ)) ≤
        (ambient X : ℝ) * Real.exp (-4 * μ)) :
    ∀ᶠ X in Filter.atTop,
      let indices := Family.familyIndexFinset P X
        (Inputs.roughModulus X) (base X)
      let μ := (Family.familyIndexMassRat indices : ℝ)
      (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo (ambient X)
        (Inputs.roughModulus X) (base X)
        (Family.familyEvents indices) : ℝ) ≤
      (ambient X : ℝ) / (Inputs.roughModulus X : ℝ) *
        (Real.exp (-(1 - ε) * μ) + Real.exp (-3 * μ) +
          Real.exp (-4 * μ)) := by
  let rank : ℝ → ℕ := fun X =>
    canonicalBrunRank
      (Family.familyIndexMassRat
        (Family.familyIndexFinset P X
          (Inputs.roughModulus X) (base X)) : ℝ)
  have htransfer := actualPaperFamily_baseNoHit_real_le_exp_add_topRank_endpoint
    P base ambient rank hbase ε hε
  rcases actualPaperFamily_topRank_le_exp_neg_three P with ⟨XT, htop⟩
  have htopEventually : ∀ᶠ X in Filter.atTop,
      let indices := Family.familyIndexFinset P X
        (Inputs.roughModulus X) (base X)
      let μ := (Family.familyIndexMassRat indices : ℝ)
      (Family.familyCompatibleLcmMassRat indices
        (2 * canonicalBrunRank μ) : ℝ) ≤ Real.exp (-3 * μ) := by
    filter_upwards [hbase,
        Filter.eventually_ge_atTop (max XT (Real.exp 2))] with X hcop hX
    dsimp only
    exact htop X (le_trans (le_max_left _ _) hX)
      (le_trans (le_max_right _ _) hX) (base X) hcop
  have hendpoint := actualPaperFamily_endpoint_le_of_level
    P base ambient hbase hlevel
  filter_upwards [htransfer, htopEventually, hendpoint] with
      X htransferX htopX hendpointX
  dsimp only at htransferX htopX hendpointX ⊢
  let indices := Family.familyIndexFinset P X
    (Inputs.roughModulus X) (base X)
  let μ := (Family.familyIndexMassRat indices : ℝ)
  let R := canonicalBrunRank μ
  have hscale : 0 ≤ (ambient X : ℝ) /
      (Inputs.roughModulus X : ℝ) := by positivity
  calc
    (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo (ambient X)
        (Inputs.roughModulus X) (base X)
        (Family.familyEvents indices) : ℝ) ≤
      (ambient X : ℝ) / (Inputs.roughModulus X : ℝ) *
          (Real.exp (-(1 - ε) * μ) +
            (Family.familyCompatibleLcmMassRat indices (2 * R) : ℝ)) +
        ∑ r ∈ Finset.range (2 * R + 1),
          (⌊X⌋₊ : ℝ) ^ r *
            (Family.familyCompatibleLcmMassRat indices r : ℝ) := by
      simpa [indices, μ, R, rank] using htransferX
    _ ≤ (ambient X : ℝ) / (Inputs.roughModulus X : ℝ) *
          (Real.exp (-(1 - ε) * μ) + Real.exp (-3 * μ)) +
        (ambient X : ℝ) / (Inputs.roughModulus X : ℝ) *
          Real.exp (-4 * μ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add_left
          (by simpa [indices, μ, R] using htopX) _) hscale)
        (by simpa [indices, μ, R] using hendpointX)
    _ = (ambient X : ℝ) / (Inputs.roughModulus X : ℝ) *
        (Real.exp (-(1 - ε) * μ) + Real.exp (-3 * μ) +
          Real.exp (-4 * μ)) := by ring

/-! ## Concrete optimization-scale level condition -/

/-- The logarithm of the actual rough prime product satisfies the manuscript's
`log P(z) ≤ 2z` bound.  This is proved from Mathlib's elementary primorial
estimate, so no additional analytic axiom is needed. -/
theorem log_roughModulus_le_two_zScale (X : ℝ)
    (hz : 0 ≤ zScale X) :
    Real.log (Inputs.roughModulus X : ℝ) ≤ 2 * zScale X := by
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
  have hrough : (Inputs.roughModulus X : ℝ) =
      ∏ p ∈ s, (p : ℝ) := by
    simp [Inputs.roughModulus, Inputs.primeProductBelow, s, n]
  have hsum :
      (∑ p ∈ s, Real.log (p : ℝ)) ≤
        Real.log (4 : ℝ) * (n : ℝ) := by
    rw [hs_eq]
    exact Inputs.primeLogSum_le_log_four_mul n
  have hn : (n : ℝ) ≤ zScale X := by
    exact Nat.floor_le hz
  have hlog4_nonneg : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog4_two : Real.log (4 : ℝ) ≤ 2 := by
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    linarith
  calc
    Real.log (Inputs.roughModulus X : ℝ) =
        ∑ p ∈ s, Real.log (p : ℝ) := by rw [hrough, hlog_prod]
    _ ≤ Real.log (4 : ℝ) * (n : ℝ) := hsum
    _ ≤ Real.log (4 : ℝ) * zScale X :=
      mul_le_mul_of_nonneg_left hn hlog4_nonneg
    _ ≤ 2 * zScale X := mul_le_mul_of_nonneg_right hlog4_two hz

/-- The actual cubic mass law and canonical rank imply the manuscript's
quartic logarithmic level budget, uniformly over admissible base residues. -/
theorem actualPaperFamily_canonical_levelBudget
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → Real.exp 2 ≤ X →
      ∀ b : ℕ, Nat.Coprime b (Inputs.roughModulus X) →
      let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
      let μ := (Family.familyIndexMassRat indices : ℝ)
      let R := canonicalBrunRank μ
      2 * (R : ℝ) * Real.log X + 6 * μ ≤
        (32 * C) * (Real.log X) ^ 4 := by
  rcases actualPaperFamily_indexMassRat_ge_log_cube P with
    ⟨c, Xc, hc, hlower⟩
  rcases actualPaperFamily_indexMassRat_le_log_cube P with
    ⟨C, XC, hC, hupper⟩
  let Xone := Real.exp (max 2 (1 / c))
  refine ⟨C, max (max Xc XC) Xone, hC, ?_⟩
  intro X hX hXexp b hbcop
  dsimp only
  let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
  let μ := (Family.familyIndexMassRat indices : ℝ)
  let R := canonicalBrunRank μ
  have hXgt : 1 < X := lt_of_lt_of_le
    (by norm_num : (1 : ℝ) < Real.exp 2) hXexp
  have hmassLower : c * (Real.log X) ^ 3 ≤ μ := by
    apply hlower X
    · exact le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _) hX)
    · exact hXgt
    · exact hbcop
  have hmassUpper : μ ≤ C * (Real.log X) ^ 3 := by
    apply hupper X
    · exact le_trans (le_max_right _ _)
        (le_trans (le_max_left _ _) hX)
    · exact hXgt
    · exact hbcop
  have hXone : Xone ≤ X := le_trans (le_max_right _ _) hX
  have hlog : max 2 (1 / c) ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (lt_trans zero_lt_one hXgt)]
    exact hXone
  have hlog_one : 1 ≤ Real.log X :=
    (by norm_num : (1 : ℝ) ≤ 2).trans ((le_max_left _ _).trans hlog)
  have hc_inv : 1 / c ≤ Real.log X := (le_max_right _ _).trans hlog
  have hcube_ge_log : Real.log X ≤ (Real.log X) ^ 3 := by
    nlinarith [sq_nonneg (Real.log X - 1)]
  have hμ_one : 1 ≤ μ := by
    have hc_nonneg : 0 ≤ c := hc.le
    have hc_mul : 1 ≤ c * Real.log X := by
      calc
        1 = c * (1 / c) := by field_simp
        _ ≤ c * Real.log X := mul_le_mul_of_nonneg_left hc_inv hc_nonneg
    exact hc_mul.trans ((mul_le_mul_of_nonneg_left hcube_ge_log hc_nonneg).trans
      hmassLower)
  have hμ_nonneg : 0 ≤ μ := le_trans (by norm_num) hμ_one
  have hR : 2 * (R : ℝ) ≤ 26 * μ := by
    calc
      2 * (R : ℝ) ≤ 2 * (13 * μ) :=
        mul_le_mul_of_nonneg_left (brunFloorRank_le_thirteen_mul hμ_one)
          (by norm_num)
      _ = 26 * μ := by ring
  calc
    2 * (R : ℝ) * Real.log X + 6 * μ ≤
        (26 * μ) * Real.log X + 6 * μ :=
      add_le_add_right (mul_le_mul_of_nonneg_right hR
        (le_trans (by norm_num) hlog_one)) _
    _ ≤ (26 * μ) * Real.log X + 6 * (μ * Real.log X) := by
      have hμlog : μ ≤ μ * Real.log X := by
        simpa using mul_le_mul_of_nonneg_left hlog_one hμ_nonneg
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left hμlog (by norm_num)) _
    _ = 32 * μ * Real.log X := by ring
    _ ≤ 32 * (C * (Real.log X) ^ 3) * Real.log X := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmassUpper (by norm_num))
        (le_trans (by norm_num) hlog_one)
    _ = (32 * C) * (Real.log X) ^ 4 := by ring

/-- The manuscript's auxiliary family scale, parameterized by a positive
constant `α`. -/
noncomputable def paperOptimizationScale (α : ℝ) (N : ℕ) : ℝ :=
  Real.exp (α * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))

theorem paperOptimizationScale_tendsto_atTop
    {α : ℝ} (hα : 0 < α) :
    Filter.Tendsto (paperOptimizationScale α)
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

/-- At the concrete optimization scale, sufficiently small positive `α`
forces the manuscript's finite-level condition for the actual family. -/
theorem actualPaperFamily_levelCondition_at_optimizationScale
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α →
      (2 + 32 * C) * α ^ 4 ≤ 1 →
      ∃ T : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
        ∀ b : ℕ,
        Nat.Coprime b
          (Inputs.roughModulus (paperOptimizationScale α N)) →
        let X := paperOptimizationScale α N
        let indices := Family.familyIndexFinset P X
          (Inputs.roughModulus X) b
        let μ := (Family.familyIndexMassRat indices : ℝ)
        let R := canonicalBrunRank μ
        (Inputs.roughModulus X : ℝ) *
            (X ^ (2 * R) * Real.exp (2 * μ)) ≤
          (N : ℝ) * Real.exp (-4 * μ) := by
  rcases actualPaperFamily_canonical_levelBudget P with
    ⟨C, X₀, hC, hbudget⟩
  refine ⟨C, hC, ?_⟩
  intro α hα hsmall
  have hscaleTop := paperOptimizationScale_tendsto_atTop hα
  have hlarge : ∀ᶠ N : ℕ in Filter.atTop,
      max X₀ (Real.exp 2) ≤ paperOptimizationScale α N :=
    hscaleTop.eventually (Filter.eventually_ge_atTop _)
  rcases Filter.eventually_atTop.1 hlarge with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro N hN hTN b hbcop
  dsimp only
  let X := paperOptimizationScale α N
  let indices := Family.familyIndexFinset P X (Inputs.roughModulus X) b
  let μ := (Family.familyIndexMassRat indices : ℝ)
  let R := canonicalBrunRank μ
  have hlargeN := hT N hTN
  have hX₀ : X₀ ≤ X := le_trans (le_max_left _ _) hlargeN
  have hXexp : Real.exp 2 ≤ X := le_trans (le_max_right _ _) hlargeN
  have hbudgetX : 2 * (R : ℝ) * Real.log X + 6 * μ ≤
      (32 * C) * (Real.log X) ^ 4 := by
    simpa [X, indices, μ, R] using hbudget X hX₀ hXexp b hbcop
  have hNge : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hLN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNge
  have hscale : Real.log X =
      α * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4) := by
    simp [X, paperOptimizationScale]
  have hfour : (Real.log X) ^ 4 =
      α ^ 4 * Real.log (N : ℝ) := by
    simpa [zScale] using
      (z_eq_alpha4_LN hLN hscale)
  have hbudgetOpt : 2 * (R : ℝ) * Real.log X + 6 * μ ≤
      (32 * C) * (α ^ 4 * Real.log (N : ℝ)) := by
    simpa [hfour] using hbudgetX
  have hXpos : 0 < X := by
    exact Real.exp_pos _
  have hPzpos : (0 : ℝ) < (Inputs.roughModulus X : ℝ) := by
    exact_mod_cast Inputs.roughModulus_pos X
  have hXpowpos : 0 < X ^ (2 * R) := pow_pos hXpos _
  have hXpowlog : Real.log (X ^ (2 * R)) =
      2 * (R : ℝ) * Real.log X := by
    rw [Real.log_pow]
    norm_num
  have hmertens : Real.log (Inputs.roughModulus X : ℝ) ≤
      2 * zScale X :=
    log_roughModulus_le_two_zScale X (by
      unfold zScale
      positivity)
  have hlevel := finite_level_condition_of_optimization
    (α := α) (R := (R : ℝ)) (μ := μ)
    (Pz := (Inputs.roughModulus X : ℝ)) (N := (N : ℝ))
    (LN := Real.log (N : ℝ)) (X := X) (Xpow := X ^ (2 * R))
    hLN rfl hPzpos hXpowpos (lt_of_lt_of_le zero_lt_one hNge)
    hscale hXpowlog hmertens hbudgetOpt hsmall
  change (Inputs.roughModulus X : ℝ) *
      (X ^ (2 * R) * Real.exp (2 * μ)) ≤
    (N : ℝ) * Real.exp (-4 * μ)
  simpa [mul_assoc] using hlevel

/-- A concrete positive optimization constant for the actual-family level
budget. -/
noncomputable def actualPaperOptimizationAlpha (C : ℝ) : ℝ :=
  (2 + 32 * C)⁻¹

theorem actualPaperOptimizationAlpha_pos
    {C : ℝ} (hC : 0 < C) :
    0 < actualPaperOptimizationAlpha C := by
  unfold actualPaperOptimizationAlpha
  positivity

theorem actualPaperOptimizationAlpha_small
    {C : ℝ} (hC : 0 < C) :
    (2 + 32 * C) * (actualPaperOptimizationAlpha C) ^ 4 ≤ 1 := by
  let A : ℝ := 2 + 32 * C
  have hA : 1 ≤ A := by dsimp [A]; nlinarith
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hA3 : 1 ≤ A ^ 3 := one_le_pow₀ hA
  change A * A⁻¹ ^ 4 ≤ 1
  calc
    A * A⁻¹ ^ 4 = (A ^ 3)⁻¹ := by
      field_simp [hApos.ne']
      ring
    _ ≤ 1 := inv_le_one_of_one_le₀ hA3

/-- Fully concrete level-condition choice: there exists a fixed positive
`α`, depending only on the paper parameters, for which the actual canonical
family satisfies the finite-level inequality for every sufficiently large
ambient `N` and every admissible base residue. -/
theorem actualPaperFamily_levelCondition_concrete
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ α : ℝ, 0 < α ∧ ∃ T : ℕ, ∀ N : ℕ, 3 ≤ N → T ≤ N →
      ∀ b : ℕ,
      Nat.Coprime b
        (Inputs.roughModulus (paperOptimizationScale α N)) →
      let X := paperOptimizationScale α N
      let indices := Family.familyIndexFinset P X
        (Inputs.roughModulus X) b
      let μ := (Family.familyIndexMassRat indices : ℝ)
      let R := canonicalBrunRank μ
      (Inputs.roughModulus X : ℝ) *
          (X ^ (2 * R) * Real.exp (2 * μ)) ≤
        (N : ℝ) * Real.exp (-4 * μ) := by
  rcases actualPaperFamily_levelCondition_at_optimizationScale P with
    ⟨C, hC, hlevel⟩
  let α := actualPaperOptimizationAlpha C
  refine ⟨α, actualPaperOptimizationAlpha_pos hC, ?_⟩
  exact hlevel α (actualPaperOptimizationAlpha_pos hC)
    (actualPaperOptimizationAlpha_small hC)

/-! ## Natural-parameter specialization of the finite transfer -/

theorem paperOptimizationScale_injective_above_three
    {α : ℝ} (hα : 0 < α) {M N : ℕ}
    (hM : 3 ≤ M) (hN : 3 ≤ N)
    (hscale : paperOptimizationScale α M = paperOptimizationScale α N) :
    M = N := by
  have harg := Real.exp_injective hscale
  have hpow : (Real.log (M : ℝ)) ^ ((1 : ℝ) / 4) =
      (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4) := by
    apply mul_left_cancel₀ hα.ne'
    simpa [paperOptimizationScale] using harg
  have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
  have hNone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hlogM : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hMone
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNone
  have hlog : Real.log (M : ℝ) = Real.log (N : ℝ) :=
    (Real.rpow_left_inj hlogM hlogN (by norm_num)).mp hpow
  have hcast : (M : ℝ) = (N : ℝ) := by
    calc
      (M : ℝ) = Real.exp (Real.log (M : ℝ)) :=
        (Real.exp_log (lt_of_lt_of_le zero_lt_one hMone)).symm
      _ = Real.exp (Real.log (N : ℝ)) := by rw [hlog]
      _ = (N : ℝ) := Real.exp_log (lt_of_lt_of_le zero_lt_one hNone)
  exact_mod_cast hcast

/-- Extend a natural sequence to real family scales by using its unique value
on the manuscript's optimization-scale image and a fixed default elsewhere. -/
noncomputable def optimizationSequenceExtension
    (α : ℝ) (u : ℕ → ℕ) (T default : ℕ) (X : ℝ) : ℕ :=
  if h : ∃ N : ℕ, 3 ≤ N ∧ T ≤ N ∧ X = paperOptimizationScale α N then
    u (Nat.find h)
  else default

theorem optimizationSequenceExtension_at_scale
    {α : ℝ} (hα : 0 < α) (u : ℕ → ℕ) (T default N : ℕ)
    (hN : 3 ≤ N) (hTN : T ≤ N) :
    optimizationSequenceExtension α u T default
      (paperOptimizationScale α N) = u N := by
  let witness : ∃ M : ℕ, 3 ≤ M ∧ T ≤ M ∧
      paperOptimizationScale α N = paperOptimizationScale α M :=
    ⟨N, hN, hTN, rfl⟩
  rw [optimizationSequenceExtension, dif_pos witness]
  have hspec := Nat.find_spec witness
  congr 1
  exact paperOptimizationScale_injective_above_three hα hspec.1 hN
    hspec.2.2.symm

theorem optimizationBaseExtension_coprime
    {α : ℝ} (hα : 0 < α) (base : ℕ → ℕ) (T : ℕ)
    (hcop : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      Nat.Coprime (base N)
        (Inputs.roughModulus (paperOptimizationScale α N))) :
    ∀ X : ℝ, Nat.Coprime
      (optimizationSequenceExtension α base T 1 X)
      (Inputs.roughModulus X) := by
  intro X
  unfold optimizationSequenceExtension
  split_ifs with h
  · have hs := Nat.find_spec h
    have hr : Inputs.roughModulus X =
        Inputs.roughModulus (paperOptimizationScale α (Nat.find h)) :=
      congrArg Inputs.roughModulus hs.2.2
    rw [hr]
    exact hcop (Nat.find h) hs.1 hs.2.1
  · simp

/-- The exact modular Suen finite-transfer decomposition specialized to
natural ambient parameters and the manuscript's optimization scale. -/
theorem actualPaperFamily_baseNoHit_natural_decomposition
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)]
    {α : ℝ} (hα : 0 < α)
    (base ambient : ℕ → ℕ) (T : ℕ)
    (hcop : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      Nat.Coprime (base N)
        (Inputs.roughModulus (paperOptimizationScale α N)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop,
      let X := paperOptimizationScale α N
      let indices := Family.familyIndexFinset P X
        (Inputs.roughModulus X) (base N)
      let μ := (Family.familyIndexMassRat indices : ℝ)
      let R := canonicalBrunRank μ
      (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo (ambient N)
        (Inputs.roughModulus X) (base N)
        (Family.familyEvents indices) : ℝ) ≤
      (ambient N : ℝ) / (Inputs.roughModulus X : ℝ) *
          (Real.exp (-(1 - ε) * μ) +
            (Family.familyCompatibleLcmMassRat indices (2 * R) : ℝ)) +
        ∑ r ∈ Finset.range (2 * R + 1),
          (⌊X⌋₊ : ℝ) ^ r *
            (Family.familyCompatibleLcmMassRat indices r : ℝ) := by
  let baseR : ℝ → ℕ := optimizationSequenceExtension α base T 1
  let ambientR : ℝ → ℕ := optimizationSequenceExtension α ambient T 0
  let rankR : ℝ → ℕ := fun X =>
    canonicalBrunRank
      (Family.familyIndexMassRat
        (Family.familyIndexFinset P X
          (Inputs.roughModulus X) (baseR X)) : ℝ)
  have hbaseR : ∀ᶠ X in Filter.atTop,
      Nat.Coprime (baseR X) (Inputs.roughModulus X) := by
    filter_upwards [] with X
    exact optimizationBaseExtension_coprime hα base T hcop X
  have hreal := actualPaperFamily_baseNoHit_real_le_exp_add_topRank_endpoint
    P baseR ambientR rankR hbaseR ε hε
  have hnat := (paperOptimizationScale_tendsto_atTop hα).eventually hreal
  filter_upwards [hnat, Filter.eventually_ge_atTop (max 3 T)] with N hN hNT
  have hN3 : 3 ≤ N := le_trans (le_max_left _ _) hNT
  have hTN : T ≤ N := le_trans (le_max_right _ _) hNT
  have hbaseEq : baseR (paperOptimizationScale α N) = base N := by
    exact optimizationSequenceExtension_at_scale hα base T 1 N hN3 hTN
  have hambientEq : ambientR (paperOptimizationScale α N) = ambient N := by
    exact optimizationSequenceExtension_at_scale hα ambient T 0 N hN3 hTN
  have hrankEq : rankR (paperOptimizationScale α N) =
      canonicalBrunRank
        (Family.familyIndexMassRat
          (Family.familyIndexFinset P (paperOptimizationScale α N)
            (Inputs.roughModulus (paperOptimizationScale α N)) (base N)) : ℝ) := by
    simp only [rankR, hbaseEq]
  rw [hbaseEq, hambientEq, hrankEq] at hN
  exact hN

/-- Natural-parameter finite transfer at the canonical rank.  Once the level
condition is supplied, all other truncation and dependency hypotheses are
discharged by the actual family. -/
theorem actualPaperFamily_baseNoHit_natural_of_level
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)]
    {α : ℝ} (hα : 0 < α)
    (base ambient : ℕ → ℕ) (T : ℕ)
    (hcop : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      Nat.Coprime (base N)
        (Inputs.roughModulus (paperOptimizationScale α N)))
    (ε : ℝ) (hε : 0 < ε)
    (hlevel : ∀ᶠ N : ℕ in Filter.atTop,
      let X := paperOptimizationScale α N
      let indices := Family.familyIndexFinset P X
        (Inputs.roughModulus X) (base N)
      let μ := (Family.familyIndexMassRat indices : ℝ)
      let R := canonicalBrunRank μ
      (Inputs.roughModulus X : ℝ) *
          (X ^ (2 * R) * Real.exp (2 * μ)) ≤
        (ambient N : ℝ) * Real.exp (-4 * μ)) :
    ∀ᶠ N : ℕ in Filter.atTop,
      let X := paperOptimizationScale α N
      let indices := Family.familyIndexFinset P X
        (Inputs.roughModulus X) (base N)
      let μ := (Family.familyIndexMassRat indices : ℝ)
      (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo (ambient N)
        (Inputs.roughModulus X) (base N)
        (Family.familyEvents indices) : ℝ) ≤
      (ambient N : ℝ) / (Inputs.roughModulus X : ℝ) *
        (Real.exp (-(1 - ε) * μ) + Real.exp (-3 * μ) +
          Real.exp (-4 * μ)) := by
  have hdecomp := actualPaperFamily_baseNoHit_natural_decomposition
    P hα base ambient T hcop ε hε
  rcases actualPaperFamily_topRank_le_exp_neg_three P with ⟨XT, htop⟩
  rcases actualPaperFamily_endpoint_le_of_scalar P with
    ⟨K, XK, hK, hendpoint⟩
  rcases actualPaperFamily_canonicalScalar_eventually P (K : ℝ)
      (Rat.cast_nonneg.mpr hK.le) with ⟨XS, hscalar⟩
  have hscaleLarge : ∀ᶠ N : ℕ in Filter.atTop,
      max (max XT XK) (max XS (Real.exp 2)) ≤
        paperOptimizationScale α N :=
    (paperOptimizationScale_tendsto_atTop hα).eventually
      (Filter.eventually_ge_atTop _)
  filter_upwards [hdecomp, hlevel, hscaleLarge,
      Filter.eventually_ge_atTop (max 3 T)] with
      N hdecompN hlevelN hscaleN hNT
  dsimp only at hdecompN hlevelN ⊢
  let X := paperOptimizationScale α N
  let indices := Family.familyIndexFinset P X
    (Inputs.roughModulus X) (base N)
  let μ := (Family.familyIndexMassRat indices : ℝ)
  let R := canonicalBrunRank μ
  have hN3 : 3 ≤ N := le_trans (le_max_left _ _) hNT
  have hTN : T ≤ N := le_trans (le_max_right _ _) hNT
  have hcopN := hcop N hN3 hTN
  have hXT : XT ≤ X :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hscaleN)
  have hXK : XK ≤ X :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hscaleN)
  have hXS : XS ≤ X :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hscaleN)
  have hXexp : Real.exp 2 ≤ X :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hscaleN)
  have htopN :
      (Family.familyCompatibleLcmMassRat indices (2 * R) : ℝ) ≤
        Real.exp (-3 * μ) := by
    simpa [X, indices, μ, R] using htop X hXT hXexp (base N) hcopN
  have hscalarN : (K : ℝ) *
      (Real.exp (((2 * R : ℕ) : ℝ) *
        paperIncrementFloorScale P X) - 1) ≤ 1 := by
    simpa [X, indices, μ, R] using hscalar X hXS hXexp (base N) hcopN
  have hendpointEnvelope :
      (∑ r ∈ Finset.range (2 * R + 1),
          (⌊X⌋₊ : ℝ) ^ r *
            (Family.familyCompatibleLcmMassRat indices r : ℝ)) ≤
        X ^ (2 * R) * Real.exp (2 * μ) := by
    simpa [X, indices, μ, R] using
      hendpoint X hXK hXexp (base N) hcopN hscalarN
  have hq : (0 : ℝ) < (Inputs.roughModulus X : ℝ) := by
    exact_mod_cast Inputs.roughModulus_pos X
  have hendpointN :
      (∑ r ∈ Finset.range (2 * R + 1),
          (⌊X⌋₊ : ℝ) ^ r *
            (Family.familyCompatibleLcmMassRat indices r : ℝ)) ≤
        (ambient N : ℝ) / (Inputs.roughModulus X : ℝ) *
          Real.exp (-4 * μ) := by
    have habsorb : X ^ (2 * R) * Real.exp (2 * μ) ≤
        ((ambient N : ℝ) * Real.exp (-4 * μ)) /
          (Inputs.roughModulus X : ℝ) := by
      apply (le_div_iff₀ hq).2
      simpa [X, indices, μ, R, mul_comm, mul_left_comm, mul_assoc] using hlevelN
    exact hendpointEnvelope.trans (habsorb.trans_eq (by field_simp))
  have hscaleNonneg : 0 ≤ (ambient N : ℝ) /
      (Inputs.roughModulus X : ℝ) := by positivity
  calc
    (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo (ambient N)
        (Inputs.roughModulus X) (base N)
        (Family.familyEvents indices) : ℝ) ≤
      (ambient N : ℝ) / (Inputs.roughModulus X : ℝ) *
          (Real.exp (-(1 - ε) * μ) +
            (Family.familyCompatibleLcmMassRat indices (2 * R) : ℝ)) +
        ∑ r ∈ Finset.range (2 * R + 1),
          (⌊X⌋₊ : ℝ) ^ r *
            (Family.familyCompatibleLcmMassRat indices r : ℝ) := by
      simpa [X, indices, μ, R] using hdecompN
    _ ≤ (ambient N : ℝ) / (Inputs.roughModulus X : ℝ) *
          (Real.exp (-(1 - ε) * μ) + Real.exp (-3 * μ)) +
        (ambient N : ℝ) / (Inputs.roughModulus X : ℝ) *
          Real.exp (-4 * μ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add_left htopN _) hscaleNonneg)
        hendpointN
    _ = (ambient N : ℝ) / (Inputs.roughModulus X : ℝ) *
        (Real.exp (-(1 - ε) * μ) + Real.exp (-3 * μ) +
          Real.exp (-4 * μ)) := by ring

/-- Fully concrete finite-transfer theorem at ambient size `N`.  The
optimization constant and level condition are constructed internally; the
only base-side premise is eventual reducedness modulo the actual rough
modulus. -/
theorem actualPaperFamily_baseNoHit_natural_concrete
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ α : ℝ, 0 < α ∧ ∀ base : ℕ → ℕ,
      (∃ Tb : ℕ, ∀ N : ℕ, 3 ≤ N → Tb ≤ N →
        Nat.Coprime (base N)
          (Inputs.roughModulus (paperOptimizationScale α N))) →
      ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in Filter.atTop,
        let X := paperOptimizationScale α N
        let indices := Family.familyIndexFinset P X
          (Inputs.roughModulus X) (base N)
        let μ := (Family.familyIndexMassRat indices : ℝ)
        (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N
          (Inputs.roughModulus X) (base N)
          (Family.familyEvents indices) : ℝ) ≤
        (N : ℝ) / (Inputs.roughModulus X : ℝ) *
          (Real.exp (-(1 - ε) * μ) + Real.exp (-3 * μ) +
            Real.exp (-4 * μ)) := by
  rcases actualPaperFamily_levelCondition_concrete P with
    ⟨α, hα, TL, hlevel⟩
  refine ⟨α, hα, ?_⟩
  intro base hbase ε hε
  rcases hbase with ⟨Tb, hcop⟩
  let T := max TL Tb
  have hcopT : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      Nat.Coprime (base N)
        (Inputs.roughModulus (paperOptimizationScale α N)) := by
    intro N hN hTN
    exact hcop N hN (le_trans (le_max_right _ _) hTN)
  have hlevelEventually : ∀ᶠ N : ℕ in Filter.atTop,
      let X := paperOptimizationScale α N
      let indices := Family.familyIndexFinset P X
        (Inputs.roughModulus X) (base N)
      let μ := (Family.familyIndexMassRat indices : ℝ)
      let R := canonicalBrunRank μ
      (Inputs.roughModulus X : ℝ) *
          (X ^ (2 * R) * Real.exp (2 * μ)) ≤
        (N : ℝ) * Real.exp (-4 * μ) := by
    filter_upwards [Filter.eventually_ge_atTop (max 3 T)] with N hNT
    have hN3 : 3 ≤ N := le_trans (le_max_left _ _) hNT
    have hTL : TL ≤ N := le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) hNT)
    exact hlevel N hN3 hTL (base N) (hcopT N hN3
      (le_trans (le_max_right _ _) hNT))
  simpa using actualPaperFamily_baseNoHit_natural_of_level
    P hα base id T hcopT ε hε hlevelEventually

/-- Diagonal uniformization on natural parameters: if every sequence of good
choices eventually satisfies `P`, then `P` eventually holds uniformly for all
good choices. -/
theorem eventually_forall_good_of_all_good_sequences
    (Good P : ℕ → ℕ → Prop)
    (default : ℕ → ℕ)
    (hdefault : ∀ N, Good N (default N))
    (hseq : ∀ u : ℕ → ℕ, (∀ N, Good N (u N)) →
      ∀ᶠ N : ℕ in Filter.atTop, P N (u N)) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ b : ℕ, Good N b → P N b := by
  classical
  by_contra hnot
  have hbad : ∀ T : ℕ, ∃ N : ℕ, T ≤ N ∧
      ∃ b : ℕ, Good N b ∧ ¬ P N b := by
    intro T
    by_contra hT
    push_neg at hT
    apply hnot
    filter_upwards [Filter.eventually_ge_atTop T] with N hTN
    intro b hb
    exact hT N hTN b hb
  let u : ℕ → ℕ := fun N =>
    if h : ∃ b : ℕ, Good N b ∧ ¬ P N b then Classical.choose h
    else default N
  have huGood : ∀ N, Good N (u N) := by
    intro N
    dsimp [u]
    split_ifs with h
    · exact (Classical.choose_spec h).1
    · exact hdefault N
  have huEventually := hseq u huGood
  rcases Filter.eventually_atTop.1 huEventually with ⟨T, hT⟩
  rcases hbad T with ⟨N, hTN, b, hbGood, hbBad⟩
  have hex : ∃ b : ℕ, Good N b ∧ ¬ P N b := ⟨b, hbGood, hbBad⟩
  have huBad : ¬ P N (u N) := by
    dsimp [u]
    rw [dif_pos hex]
    exact (Classical.choose_spec hex).2
  exact huBad (hT N hTN)

/-- Uniform paper-facing finite transfer: one fixed optimization scale works
simultaneously for every reduced base class at each sufficiently large
ambient `N`. -/
theorem actualPaperFamily_baseNoHit_uniform_reduced_concrete
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ α : ℝ, 0 < α ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in Filter.atTop, ∀ b : ℕ,
        Nat.Coprime b
          (Inputs.roughModulus (paperOptimizationScale α N)) →
        let X := paperOptimizationScale α N
        let indices := Family.familyIndexFinset P X
          (Inputs.roughModulus X) b
        let μ := (Family.familyIndexMassRat indices : ℝ)
        (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N
          (Inputs.roughModulus X) b
          (Family.familyEvents indices) : ℝ) ≤
        (N : ℝ) / (Inputs.roughModulus X : ℝ) *
          (Real.exp (-(1 - ε) * μ) + Real.exp (-3 * μ) +
            Real.exp (-4 * μ)) := by
  rcases actualPaperFamily_baseNoHit_natural_concrete P with
    ⟨α, hα, hsequence⟩
  refine ⟨α, hα, ?_⟩
  intro ε hε
  let Good : ℕ → ℕ → Prop := fun N b =>
    Nat.Coprime b
      (Inputs.roughModulus (paperOptimizationScale α N))
  let Bound : ℕ → ℕ → Prop := fun N b =>
    let X := paperOptimizationScale α N
    let indices := Family.familyIndexFinset P X
      (Inputs.roughModulus X) b
    let μ := (Family.familyIndexMassRat indices : ℝ)
    (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N
      (Inputs.roughModulus X) b
      (Family.familyEvents indices) : ℝ) ≤
    (N : ℝ) / (Inputs.roughModulus X : ℝ) *
      (Real.exp (-(1 - ε) * μ) + Real.exp (-3 * μ) +
        Real.exp (-4 * μ))
  apply eventually_forall_good_of_all_good_sequences Good Bound
    (fun _ => 1)
  · intro N
    simp [Good]
  · intro u hu
    apply hsequence u
    · refine ⟨0, ?_⟩
      intro N hN hzero
      exact hu N
    · exact hε

/-- Uniform mass lower bound on the concrete optimization scale, in the
manuscript's ambient `(log N)^(3/4)` normalization. -/
theorem actualPaperFamily_mass_lower_optimizationScale
    (P : Params) {α : ℝ} (hα : 0 < α) :
    ∃ d : ℝ, 0 < d ∧
      ∀ᶠ N : ℕ in Filter.atTop, ∀ b : ℕ,
        Nat.Coprime b
          (Inputs.roughModulus (paperOptimizationScale α N)) →
        d * (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4) ≤
          (Family.familyIndexMassRat
            (Family.familyIndexFinset P (paperOptimizationScale α N)
              (Inputs.roughModulus (paperOptimizationScale α N)) b) : ℝ) := by
  rcases actualPaperFamily_indexMassRat_ge_log_cube P with
    ⟨c, X₀, hc, hlower⟩
  refine ⟨c * α ^ 3, mul_pos hc (pow_pos hα 3), ?_⟩
  have hlarge : ∀ᶠ N : ℕ in Filter.atTop,
      max X₀ 1 < paperOptimizationScale α N :=
    (paperOptimizationScale_tendsto_atTop hα).eventually
      (Filter.eventually_gt_atTop _)
  filter_upwards [hlarge, Filter.eventually_ge_atTop 1] with N hXN hN
  intro b hcop
  have hX₀ : X₀ ≤ paperOptimizationScale α N :=
    le_trans (le_max_left _ _) hXN.le
  have hXone : 1 < paperOptimizationScale α N :=
    lt_of_le_of_lt (le_max_right _ _) hXN
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hcube : (Real.log (paperOptimizationScale α N)) ^ 3 =
      α ^ 3 * (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4) := by
    apply logX_cube_eq (Real.log_nonneg hNreal)
    simp [paperOptimizationScale]
  have hm := hlower (paperOptimizationScale α N) hX₀ hXone b hcop
  rw [hcube] at hm
  simpa [mul_assoc] using hm

/-- Uniform simplified row bound with the manuscript's
`exp(-c (log N)^(3/4))` saving made explicit. -/
theorem actualPaperFamily_baseNoHit_uniform_reduced_saving
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ α c : ℝ, 0 < α ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop, ∀ b : ℕ,
        Nat.Coprime b
          (Inputs.roughModulus (paperOptimizationScale α N)) →
        let X := paperOptimizationScale α N
        let indices := Family.familyIndexFinset P X
          (Inputs.roughModulus X) b
        (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N
          (Inputs.roughModulus X) b
          (Family.familyEvents indices) : ℝ) ≤
        (N : ℝ) / (Inputs.roughModulus X : ℝ) *
          (3 * Real.exp (-c *
            (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4))) := by
  rcases actualPaperFamily_baseNoHit_uniform_reduced_concrete P with
    ⟨α, hα, htransfer⟩
  rcases actualPaperFamily_mass_lower_optimizationScale P hα with
    ⟨d, hd, hmass⟩
  refine ⟨α, d / 2, hα, div_pos hd (by norm_num), ?_⟩
  have hrow := htransfer (1 / 2) (by norm_num)
  filter_upwards [hrow, hmass, Filter.eventually_ge_atTop 1] with
      N hrowN hmassN hN
  intro b hcop
  dsimp only at hrowN ⊢
  let X := paperOptimizationScale α N
  let indices := Family.familyIndexFinset P X
    (Inputs.roughModulus X) b
  let μ := (Family.familyIndexMassRat indices : ℝ)
  let L := (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4)
  have hmassLower : d * L ≤ μ := by
    simpa [X, indices, μ, L] using hmassN b hcop
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogNonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNreal
  have hL : 0 ≤ L := by
    exact Real.rpow_nonneg hlogNonneg _
  have hμ : 0 ≤ μ := le_trans (mul_nonneg hd.le hL) hmassLower
  have hmainExp : Real.exp (-(1 - (1 / 2 : ℝ)) * μ) ≤
      Real.exp (-(d / 2) * L) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have htopExp : Real.exp (-3 * μ) ≤ Real.exp (-(d / 2) * L) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hendExp : Real.exp (-4 * μ) ≤ Real.exp (-(d / 2) * L) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hexpSum : Real.exp (-(1 - (1 / 2 : ℝ)) * μ) +
      Real.exp (-3 * μ) + Real.exp (-4 * μ) ≤
        3 * Real.exp (-(d / 2) * L) := by
    linarith
  have hscale : 0 ≤ (N : ℝ) / (Inputs.roughModulus X : ℝ) := by positivity
  have hrowB := hrowN b hcop
  calc
    (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo N
        (Inputs.roughModulus X) b
        (Family.familyEvents indices) : ℝ) ≤
      (N : ℝ) / (Inputs.roughModulus X : ℝ) *
        (Real.exp (-(1 - (1 / 2 : ℝ)) * μ) + Real.exp (-3 * μ) +
          Real.exp (-4 * μ)) := by
      simpa [X, indices, μ] using hrowB
    _ ≤ (N : ℝ) / (Inputs.roughModulus X : ℝ) *
        (3 * Real.exp (-(d / 2) * L)) :=
      mul_le_mul_of_nonneg_left hexpSum hscale

/-- Summing the uniform row estimate over all reduced residue classes cancels
the rough-modulus denominator and gives the manuscript's reduced no-hit
bound. -/
theorem actualPaperFamily_reducedNoHitSum_saving
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ α c : ℝ, 0 < α ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let X := paperOptimizationScale α N
        let Pz := Inputs.roughModulus X
        let eventsByBase : ℕ → Finset EscLeanChecks.SatEvent := fun b =>
          Family.familyEvents (Family.familyIndexFinset P X Pz b)
        (∑ b ∈ EscLeanChecks.reducedResiduesMod Pz,
          (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo
            N Pz b (eventsByBase b) : ℝ)) ≤
        3 * (N : ℝ) * Real.exp (-c *
          (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4)) := by
  rcases actualPaperFamily_baseNoHit_uniform_reduced_saving P with
    ⟨α, c, hα, hc, hrow⟩
  refine ⟨α, c, hα, hc, ?_⟩
  filter_upwards [hrow] with N hrowN
  dsimp only
  let X := paperOptimizationScale α N
  let Pz := Inputs.roughModulus X
  let E := Real.exp (-c * (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4))
  let A := (N : ℝ) / (Pz : ℝ) * (3 * E)
  let eventsByBase : ℕ → Finset EscLeanChecks.SatEvent := fun b =>
    Family.familyEvents (Family.familyIndexFinset P X Pz b)
  have hrows : ∀ b ∈ EscLeanChecks.reducedResiduesMod Pz,
      (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo
        N Pz b (eventsByBase b) : ℝ) ≤ A := by
    intro b hb
    have hcop := (EscLeanChecks.mem_reducedResiduesMod_iff Pz b).1 hb |>.2
    simpa [X, Pz, E, A, eventsByBase] using hrowN b hcop
  have hcard : (EscLeanChecks.reducedResiduesMod Pz).card ≤ Pz := by
    unfold EscLeanChecks.reducedResiduesMod
    exact (Finset.card_filter_le (Finset.range Pz)
      (fun b => Nat.Coprime b Pz)).trans_eq (Finset.card_range Pz)
  have hA : 0 ≤ A := by
    dsimp [A, E]
    positivity
  have hPzpos : (0 : ℝ) < (Pz : ℝ) := by
    exact_mod_cast Inputs.roughModulus_pos X
  calc
    (∑ b ∈ EscLeanChecks.reducedResiduesMod Pz,
        (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo
          N Pz b (eventsByBase b) : ℝ)) ≤
      ∑ b ∈ EscLeanChecks.reducedResiduesMod Pz, A :=
        Finset.sum_le_sum hrows
    _ = ((EscLeanChecks.reducedResiduesMod Pz).card : ℝ) * A := by
      simp
    _ ≤ (Pz : ℝ) * A := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hA
    _ = 3 * (N : ℝ) * E := by
      dsimp [A]
      field_simp [hPzpos.ne']
      ring

/-- The actual reduced exceptional carrier (away from the harmless values
`0,1`) is bounded by the summed paper-family no-hit estimate. -/
theorem actualPaperFamily_reducedExceptionalGeTwo_saving
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ α c : ℝ, 0 < α ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let X := paperOptimizationScale α N
        let Pz := Inputs.roughModulus X
        (EscLeanChecks.reducedBaseExceptionalCountGeTwo N Pz : ℝ) ≤
          3 * (N : ℝ) * Real.exp (-c *
            (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4)) := by
  rcases actualPaperFamily_reducedNoHitSum_saving P with
    ⟨α, c, hα, hc, hsum⟩
  refine ⟨α, c, hα, hc, ?_⟩
  rcases Inputs.eventually_UScale_le_rpow (δ := P.β / 2)
      (by linarith [P.β_pos]) with ⟨XU, hUbound⟩
  have hscaleLarge : ∀ᶠ N : ℕ in Filter.atTop,
      max XU 1 < paperOptimizationScale α N :=
    (paperOptimizationScale_tendsto_atTop hα).eventually
      (Filter.eventually_gt_atTop _)
  filter_upwards [hsum, hscaleLarge] with N hsumN hXLarge
  dsimp only at hsumN ⊢
  let X := paperOptimizationScale α N
  let Pz := Inputs.roughModulus X
  let indicesByBase : ℕ → Finset Family.FamilyIndex := fun b =>
    Family.familyIndexFinset P X Pz b
  let eventsByBase : ℕ → Finset EscLeanChecks.SatEvent := fun b =>
    Family.familyEvents (indicesByBase b)
  have hXU : XU ≤ X := le_trans (le_max_left _ _) hXLarge.le
  have hX : 1 < X := lt_of_le_of_lt (le_max_right _ _) hXLarge
  have hlam_beta : P.lam < P.β := by
    linarith [P.lam_add_η_lt_θ, P.two_θ_lt_β, P.η_pos, P.θ_pos]
  have hU : UScale X < X ^ P.β := by
    calc
      UScale X ≤ X ^ (P.β / 2) := hUbound X hXU
      _ < X ^ P.β := Real.rpow_lt_rpow_of_exponent_lt hX (by
        nlinarith [P.β_pos])
  have hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : ℕ,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ Pz ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1 := by
    intro b event hevent
    apply Family.familyEvents_certificate_of_dminus_lt_p P X Pz b
      (indicesByBase b) hX
    · intro i hi
      exact Family.familyIndexFinset_dminus_lt_prime P X Pz b hX hU i hi
    · intro i hi
      exact (Family.mem_familyIndexFinset_iff P X Pz b i
        (lt_trans zero_lt_one hX)).1 hi
    · exact hevent
  have hbadInt :
      (EscLeanChecks.reducedBaseExceptionalCountGeTwo N Pz : ℤ) ≤
        EscLeanChecks.reducedBaseSatEventNoHitIndicatorSumUpTo
          N Pz eventsByBase :=
    EscLeanChecks.reducedBaseExceptionalCountGeTwo_le_reducedBaseSatEventNoHitIndicatorSum_of_variable_certs
      N Pz eventsByBase hcert
  have hPz : 0 < Pz := by
    exact Inputs.roughModulus_pos X
  have hsumEq := EscLeanChecks.reducedBaseSatEventNoHitIndicatorSum_eq_sum_base
    N Pz eventsByBase hPz
  have hbadReal :
      (EscLeanChecks.reducedBaseExceptionalCountGeTwo N Pz : ℝ) ≤
        ∑ b ∈ EscLeanChecks.reducedResiduesMod Pz,
          (EscLeanChecks.baseSatEventNoHitIndicatorSumUpTo
            N Pz b (eventsByBase b) : ℝ) := by
    rw [← hsumEq] at hbadInt
    exact_mod_cast hbadInt
  exact hbadReal.trans (by
    simpa [X, Pz, indicesByBase, eventsByBase] using hsumN)

end EscAnalytic
