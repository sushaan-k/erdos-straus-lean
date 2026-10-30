import ErdosStraus.Family.Definition
import ErdosStraus.Family.Scales
import ErdosStraus.Counting.BinomialMoments

/-!
# Events of the selected family

Once the conditions on an index of `I_b` that do not involve the prime are fixed, the
admissible `p` are the primes in `(X^β, X^{1-σ}]` in one reduced class modulo `m ρ(e)`
(`withPrime_static_iff`). The index `i` gives the event `n ≡ -m e (mod q_i)`, tagged by the
coordinates of `i` so that coincident congruences are counted with multiplicity. Two dependent
events share their large prime or a prime factor of `d₊`.
-/

/-! ## Indices without the prime -/

namespace ErdosStraus.FixedNumeratorFamily

open Classical Family
open scoped BigOperators

/-- The conditions of `StaticMem` that do not involve the prime `p`. -/
structure PrePrimeMem (m : ℕ) (P : Params) (X : ℝ) (Pz b : ℕ)
    (j : FamilyPrePrimeIndex) : Prop where
  s_pos : 1 ≤ j.E.s
  s_le_S : (j.E.s : ℝ) ≤ SScale P X
  r_gt : Y0Scale P X / (j.E.s : ℝ) < (j.E.r : ℝ)
  r_le : (j.E.r : ℝ) ≤ HScale P X / ((j.E.s : ℝ) ^ 2)
  dminus_pos : 0 < j.dminus
  dminus_le_U : (j.dminus : ℝ) ≤ UScale X
  dminus_dvd_Pz : j.dminus ∣ Pz
  dminus_squarefree : Squarefree j.dminus
  dminus_odd : Odd j.dminus
  base_cong : b + m * j.E.e ≡ 0 [MOD j.dminus]
  dplus_pos : 0 < j.dplus
  dplus_squarefree : Squarefree j.dplus
  dd_le_Y : (j.dminus * j.dplus : ℝ) ≤ YScale P X
  dplus_coprime_Pz : Nat.Coprime j.dplus Pz
  rho_coprime_m : Nat.Coprime j.E.rho m
  dd_coprime_mrho : Nat.Coprime (j.dminus * j.dplus) (m * j.E.rho)

theorem prePrimeSet_finite (m : ℕ) (P : Params) (X : ℝ) (Pz b : ℕ)
    (hX : 0 < X) : {j : FamilyPrePrimeIndex | PrePrimeMem m P X Pz b j}.Finite := by
  let code : FamilyPrePrimeIndex → ℕ × ℕ × ℕ × ℕ :=
    fun j => (j.E.r, j.E.s, j.dminus, j.dplus)
  let box : Set (ℕ × ℕ × ℕ × ℕ) :=
    Set.Iic ⌊HScale P X⌋₊ ×ˢ Set.Iic ⌊SScale P X⌋₊ ×ˢ
      Set.Iic ⌊UScale X⌋₊ ×ˢ Set.Iic ⌊YScale P X⌋₊
  have hbox : box.Finite := (Set.finite_Iic _).prod
    ((Set.finite_Iic _).prod ((Set.finite_Iic _).prod (Set.finite_Iic _)))
  have hcode : Function.Injective code := by
    rintro ⟨⟨r, s, hrsq, hssq, hrs⟩, dm, dp⟩
      ⟨⟨r', s', hrsq', hssq', hrs'⟩, dm', dp'⟩ h
    simp only [code, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rfl
  apply (hbox.preimage (fun j _ k _ h => hcode h)).subset
  intro j hj
  have hmem : PrePrimeMem m P X Pz b j := hj
  have hs : (1 : ℝ) ≤ j.E.s := by exact_mod_cast hmem.s_pos
  have hH : 0 ≤ HScale P X := Real.rpow_nonneg hX.le _
  have hr : (j.E.r : ℝ) ≤ HScale P X :=
    hmem.r_le.trans (div_le_self hH (one_le_pow₀ hs : (1 : ℝ) ≤ (j.E.s : ℝ) ^ 2))
  have hdm : (1 : ℝ) ≤ j.dminus := by exact_mod_cast hmem.dminus_pos
  have hdp : (j.dplus : ℝ) ≤ YScale P X := by
    have h := hmem.dd_le_Y
    nlinarith [show (0 : ℝ) ≤ (j.dplus : ℝ) from Nat.cast_nonneg _]
  change code j ∈ box
  exact ⟨Nat.le_floor hr, Nat.le_floor hmem.s_le_S,
    Nat.le_floor hmem.dminus_le_U, Nat.le_floor hdp⟩

/-- The finite set of indices satisfying `PrePrimeMem` (empty when `X ≤ 0`). -/
noncomputable def prePrimeFinset (m : ℕ) (P : Params) (X : ℝ) (Pz b : ℕ) :
    Finset FamilyPrePrimeIndex :=
  if hX : 0 < X then (prePrimeSet_finite m P X Pz b hX).toFinset else ∅

theorem mem_prePrimeFinset_iff (m : ℕ) (P : Params) (X : ℝ) (Pz b : ℕ)
    (j : FamilyPrePrimeIndex) (hX : 0 < X) :
    j ∈ prePrimeFinset m P X Pz b ↔ PrePrimeMem m P X Pz b j := by
  simp [prePrimeFinset, hX]

/-- The residue `-(d₋ d₊)⁻¹ mod m ρ(e)`. -/
noncomputable def prePrimeResidue (m : ℕ) (j : FamilyPrePrimeIndex)
    (hcop : Nat.Coprime (j.dminus * j.dplus) (m * j.E.rho)) : ℕ :=
  ((-(ZMod.unitOfCoprime (j.dminus * j.dplus) hcop)⁻¹ :
    (ZMod (m * j.E.rho))ˣ) : ZMod (m * j.E.rho)).val

theorem prePrimeResidue_coprime (m : ℕ) (j : FamilyPrePrimeIndex)
    (hcop : Nat.Coprime (j.dminus * j.dplus) (m * j.E.rho)) :
    Nat.Coprime (prePrimeResidue m j hcop) (m * j.E.rho) :=
  ZMod.val_coe_unit_coprime (-(ZMod.unitOfCoprime (j.dminus * j.dplus) hcop)⁻¹)

theorem prePrimeResidue_sat (m : ℕ) (hm : 0 < m) (j : FamilyPrePrimeIndex)
    (hcop : Nat.Coprime (j.dminus * j.dplus) (m * j.E.rho)) (hrho : 0 < j.E.rho) :
    m * j.E.rho ∣ (j.dminus * j.dplus) * prePrimeResidue m j hcop + 1 := by
  let : NeZero (m * j.E.rho) := ⟨(Nat.mul_pos hm hrho).ne'⟩
  rw [← ZMod.natCast_eq_zero_iff]
  unfold prePrimeResidue
  rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  simp only [Units.val_neg]
  rw [← ZMod.coe_unitOfCoprime (j.dminus * j.dplus) hcop, mul_neg, ← Units.val_mul]
  simp

theorem prePrime_cong_iff_sat (m : ℕ) (hm : 0 < m) (j : FamilyPrePrimeIndex)
    (hcop : Nat.Coprime (j.dminus * j.dplus) (m * j.E.rho))
    (hrho : 0 < j.E.rho) (p : ℕ) :
    Estimates.congMod p (prePrimeResidue m j hcop) (m * j.E.rho) ↔
      m * j.E.rho ∣ (j.dminus * j.dplus) * p + 1 := by
  have hres := Nat.modEq_zero_iff_dvd.mpr (prePrimeResidue_sat m hm j hcop hrho)
  change p ≡ prePrimeResidue m j hcop [MOD m * j.E.rho] ↔ _
  constructor
  · intro hp
    exact Nat.modEq_zero_iff_dvd.mp
      (((hp.mul_left (j.dminus * j.dplus)).add_right 1).trans hres)
  · intro hp
    exact Nat.ModEq.cancel_left_of_coprime hcop.symm.gcd_eq_one
      (Nat.ModEq.add_right_cancel' 1 ((Nat.modEq_zero_iff_dvd.mpr hp).trans hres.symm))

/-- The primes `X^β < p ≤ X^{1-σ}` with `p ≡ -(d₋ d₊)⁻¹ (mod m ρ(e))`. -/
noncomputable def prePrimePrimeValues (m : ℕ) (P : Params) (X : ℝ)
    (j : FamilyPrePrimeIndex)
    (hcop : Nat.Coprime (j.dminus * j.dplus) (m * j.E.rho)) : Finset ℕ :=
  (Estimates.natWindow (X ^ P.β) (X ^ (1 - P.σ))).filter
    (fun p => Nat.Prime p ∧ Estimates.congMod p (prePrimeResidue m j hcop) (m * j.E.rho))

/-- Adding the prime `p` to `j` gives a member of `I_b` exactly when `p` is one of
`prePrimePrimeValues`. -/
theorem withPrime_static_iff (m : ℕ) (hm : 0 < m) (P : Params) (X : ℝ)
    (Pz b : ℕ) (hX : 0 < X) (j : FamilyPrePrimeIndex)
    (hj : PrePrimeMem m P X Pz b j) (p : ℕ) :
    StaticMem m P X Pz b (j.withPrime p) ↔
      p ∈ prePrimePrimeValues m P X j hj.dd_coprime_mrho := by
  have hrho : 0 < j.E.rho := by
    exact Nat.pos_of_ne_zero j.E.rho_squarefree.ne_zero
  have hsat := prePrime_cong_iff_sat m hm j hj.dd_coprime_mrho hrho p
  constructor
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨?_, h.p_prime, hsat.mpr ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨h.p_prime.one_le, Nat.le_floor h.p_le⟩, h.p_gt⟩
    · simpa only [FamilyPrePrimeIndex.withPrime, FamilyIndex.rho, FamilyIndex.Q,
        Nat.mul_assoc] using h.sat_cong
  · intro hp
    obtain ⟨hpwin, hprime, hcong⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpbox, hpgt⟩ := Finset.mem_filter.mp hpwin
    have hple : (p : ℝ) ≤ X ^ (1 - P.σ) :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hpbox).2).trans
        (Nat.floor_le (Real.rpow_nonneg hX.le _))
    exact
      { s_pos := hj.s_pos, s_le_S := hj.s_le_S, r_gt := hj.r_gt, r_le := hj.r_le,
        dminus_pos := hj.dminus_pos, dminus_le_U := hj.dminus_le_U,
        dminus_dvd_Pz := hj.dminus_dvd_Pz, dminus_squarefree := hj.dminus_squarefree,
        dminus_odd := hj.dminus_odd, base_cong := hj.base_cong,
        dplus_pos := hj.dplus_pos, dplus_squarefree := hj.dplus_squarefree,
        dd_le_Y := hj.dd_le_Y, dplus_coprime_Pz := hj.dplus_coprime_Pz,
        rho_coprime_m := hj.rho_coprime_m, dd_coprime_mrho := hj.dd_coprime_mrho,
        p_prime := hprime, p_gt := hpgt, p_le := hple,
        sat_cong := by simpa only [FamilyPrePrimeIndex.withPrime, FamilyIndex.rho,
          FamilyIndex.Q, Nat.mul_assoc] using hsat.mp hcong }

end ErdosStraus.FixedNumeratorFamily

/-! ## Modular events -/

namespace ErdosStraus.FixedNumeratorFamily

open Classical Family

/-- The event `n ≡ -m e (mod q_i)` of the index `i`, tagged by the coordinates of `i`. -/
def modularEvent (m : ℕ) (i : FamilyIndex) : Estimates.ModularEvent where
  tag := (Nat.pair i.E.r i.E.s, i.dminus, i.dplus, i.p)
  modulus := i.q
  residue := ErdosStraus.Arithmetic.negModResidue i.q (m * i.e)

theorem modularEvent_injective (m : ℕ) : Function.Injective (modularEvent m) := by
  intro i j h
  have ht := congrArg Estimates.ModularEvent.tag h
  cases i with
  | mk Ei dmi dpi pi =>
    cases Ei with
    | mk ri si hri hsi hci =>
      cases j with
      | mk Ej dmj dpj pj =>
        cases Ej with
        | mk rj sj hrj hsj hcj =>
          simp only [modularEvent, Prod.mk.injEq, Nat.pair_eq_pair] at ht
          obtain ⟨⟨hr, hs⟩, hdm, hdp, hp⟩ := ht
          subst rj
          subst sj
          subst dmj
          subst dpj
          subst pj
          rfl

/-- The events of a set of indices. -/
noncomputable def modularEvents (m : ℕ) (indices : Finset FamilyIndex) :
    Finset Estimates.ModularEvent := indices.image (modularEvent m)

/-- The total weight `∑_i 1/q_i` of a set of indices. -/
noncomputable def indexMass (indices : Finset FamilyIndex) : ℝ :=
  ∑ i ∈ indices, (1 : ℝ) / (i.q : ℝ)

theorem indexMass_nonneg (indices : Finset FamilyIndex) : 0 ≤ indexMass indices :=
  Finset.sum_nonneg (fun _ _ => by positivity)

@[simp] theorem modularMass_eq_indexMass (m : ℕ) (indices : Finset FamilyIndex) :
    Estimates.modularMass (modularEvents m indices) = indexMass indices := by
  unfold Estimates.modularMass modularEvents indexMass
  rw [Finset.sum_image (fun i _ j _ h => modularEvent_injective m h)]
  rfl

theorem StaticMem.q_pos
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (h : StaticMem m P X Pz b i) : 0 < i.q :=
  Nat.mul_pos h.dplus_pos h.p_prime.pos

theorem StaticMem.dplus_le_YScale
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (h : StaticMem m P X Pz b i) : (i.dplus : ℝ) ≤ YScale P X := by
  have hd : (1 : ℝ) ≤ i.dminus := by exact_mod_cast h.dminus_pos
  calc
    (i.dplus : ℝ) ≤ (i.dminus : ℝ) * i.dplus := by nlinarith
    _ ≤ YScale P X := h.dd_le_Y

theorem StaticMem.q_coprime_numerator
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (h : StaticMem m P X Pz b i) : Nat.Coprime i.q m := by
  have hd := (h.dd_coprime_mrho.coprime_dvd_left
    (dvd_mul_left i.dplus i.dminus)).coprime_dvd_right (dvd_mul_right m i.rho)
  exact Nat.coprime_mul_iff_left.mpr ⟨hd, h.prime_coprime_numerator⟩

theorem StaticMem.dplus_lt_other_prime
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ} {i j : FamilyIndex}
    (hX : 1 < X) (hi : StaticMem m P X Pz b i)
    (hj : StaticMem m P X Pz b j) : i.dplus < j.p := by
  have hσβ : P.σ < P.β := by linarith [P.σ_lt_θ, P.two_θ_lt_β, P.θ_pos]
  have hY : YScale P X < X ^ P.β :=
    Real.rpow_lt_rpow_of_exponent_lt hX hσβ
  exact_mod_cast hi.dplus_le_YScale.trans_lt (hY.trans hj.p_gt)

theorem modular_compatible_iff
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ} {i j : FamilyIndex}
    (hi : StaticMem m P X Pz b i) (hj : StaticMem m P X Pz b j) :
    ErdosStraus.Arithmetic.residueCompatible i.q j.q
      (modularEvent m i).residue (modularEvent m j).residue ↔
        ErdosStraus.Arithmetic.residueCompatible i.q j.q (m * i.e) (m * j.e) := by
  constructor
  · exact residueCompatible_of_negModResidue_compatible _ _ _ _ hi.q_pos hj.q_pos
  · exact ErdosStraus.Arithmetic.residueCompatible_negModResidue_of_residueCompatible
      _ _ _ _ hi.q_pos hj.q_pos

/-- Since `q_i` is coprime to `m`, compatible events have `e_i ≡ e_j (mod (q_i, q_j))`. -/
theorem e_modEq_of_modular_compatible
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ} {i j : FamilyIndex}
    (hi : StaticMem m P X Pz b i) (hj : StaticMem m P X Pz b j)
    (hc : ErdosStraus.Arithmetic.residueCompatible i.q j.q
      (modularEvent m i).residue (modularEvent m j).residue) :
    i.e ≡ j.e [MOD Nat.gcd i.q j.q] := by
  have hu := hi.q_coprime_numerator.coprime_dvd_left (Nat.gcd_dvd_left i.q j.q)
  exact Nat.ModEq.cancel_left_of_coprime hu.gcd_eq_one
    ((modular_compatible_iff hi hj).mp hc)

/-- Two dependent events share their large prime or a prime factor of `d₊`. -/
theorem dependent_largePrime_or_medium
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ} {i j : FamilyIndex}
    (hX : 1 < X) (hi : StaticMem m P X Pz b i) (hj : StaticMem m P X Pz b j)
    (hdep : Estimates.modularDependent (modularEvent m i) (modularEvent m j)) :
    i.p = j.p ∨ ¬ Nat.Coprime i.dplus j.dplus := by
  by_contra h
  obtain ⟨hpp, hdd⟩ := not_or.mp h
  have hdd' : Nat.Coprime i.dplus j.dplus := by simpa using hdd
  have hipj : Nat.Coprime i.dplus j.p :=
    ((hj.p_prime.coprime_iff_not_dvd).mpr
      (Nat.not_dvd_of_pos_of_lt hi.dplus_pos (hi.dplus_lt_other_prime hX hj))).symm
  have hpjd : Nat.Coprime i.p j.dplus :=
    (hi.p_prime.coprime_iff_not_dvd).mpr
      (Nat.not_dvd_of_pos_of_lt hj.dplus_pos (hj.dplus_lt_other_prime hX hi))
  have hpp' := (Nat.coprime_primes hi.p_prime hj.p_prime).mpr hpp
  apply hdep.2
  exact Nat.coprime_mul_iff_left.mpr
    ⟨hdd'.mul_right hipj, hpjd.mul_right hpp'⟩

end ErdosStraus.FixedNumeratorFamily
