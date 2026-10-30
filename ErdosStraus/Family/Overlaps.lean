import ErdosStraus.Counting.BinomialMoments
import ErdosStraus.Family.Events
import ErdosStraus.Family.Definition
import ErdosStraus.Family.ResidueWeights
import ErdosStraus.Family.TotalWeight

/-!
# Lemma 6.9: overlap bounds for the selected family

For the events of the selected family `I_b` this file proves the three bounds of
Lemma 6.9, uniformly in the base class `b`: the neighbour mass satisfies `δ_b → 0`,
the dependency mass satisfies `Δ_b ≤ ε μ_b` for large `X`, and
`A(S) ≤ (1 + ε) μ_b` for every compatible `S` with `|S| ≤ K μ_b`. Along the way it
proves the direct count of Lemma 6.8: the events with a given large prime `p` have
total weight at most `H/p ≤ X^{θ-β}`.
-/

namespace ErdosStraus.FixedNumeratorFamily

open Classical Family

/-- A set of indices is compatible when its congruences are pairwise compatible. -/
def Compatible (m : ℕ) (S : Finset FamilyIndex) : Prop :=
  ModularFamily.Compatible (modularEvents m S)

/-- The indices `i ∈ I \ S` such that `S ∪ {i}` is compatible. -/
noncomputable def extensions (m : ℕ) (I S : Finset FamilyIndex) : Finset FamilyIndex :=
  I.filter (fun i => i ∉ S ∧ Compatible m (insert i S))

/-- The period `L_S = lcm(q_i : i ∈ S)`. -/
noncomputable def period (m : ℕ) (S : Finset FamilyIndex) : ℕ :=
  ModularFamily.period (modularEvents m S)

/-- The overlap `(L_S, q_i)` of an index with a set. -/
noncomputable def overlap (m : ℕ) (S : Finset FamilyIndex) (i : FamilyIndex) : ℕ :=
  Nat.gcd (period m S) i.q

/-- The increment `A(S) = ∑ w_i (q_i, L_S)` over the compatible extensions `i` of `S`. -/
noncomputable def increment (m : ℕ) (I S : Finset FamilyIndex) : ℝ :=
  ∑ i ∈ extensions m I S, (1 : ℝ) / (i.q : ℝ) * (overlap m S i : ℝ)

theorem compatible_iff (m : ℕ) (S : Finset FamilyIndex) :
    Compatible m S ↔ ∀ i ∈ S, ∀ j ∈ S,
      ErdosStraus.Arithmetic.residueCompatible i.q j.q
        (modularEvent m i).residue (modularEvent m j).residue := by
  constructor
  · intro h i hi j hj
    exact h _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩) _
      (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  · intro h a ha b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    exact h i hi j hj

theorem prime_dvd_period_iff (m : ℕ) (S : Finset FamilyIndex) (p : ℕ)
    (hp : Nat.Prime p) :
    p ∣ period m S ↔ ∃ i ∈ S, p ∣ i.q := by
  rw [period, ModularFamily.period,
    ErdosStraus.Arithmetic.prime_dvd_congruenceLcm_iff p hp]
  constructor
  · rintro ⟨row, hr, hpq⟩
    obtain ⟨event, he, rfl⟩ := List.mem_map.mp hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_toList.mp he)
    exact ⟨i, hi, hpq⟩
  · rintro ⟨i, hi, hpi⟩
    refine ⟨ModularFamily.row (modularEvent m i), ?_, hpi⟩
    exact List.mem_map.mpr ⟨modularEvent m i,
      Finset.mem_toList.mpr (Finset.mem_image.mpr ⟨i, hi, rfl⟩), rfl⟩

theorem extension_compatible
    {m : ℕ} {I S : Finset FamilyIndex} {i j : FamilyIndex}
    (hi : i ∈ extensions m I S) (hj : j ∈ S) :
    ErdosStraus.Arithmetic.residueCompatible i.q j.q
      (modularEvent m i).residue (modularEvent m j).residue := by
  obtain ⟨_hiI, _hinot, hc⟩ := Finset.mem_filter.mp hi
  exact (compatible_iff m _).mp hc i (Finset.mem_insert_self _ _) j
    (Finset.mem_insert_of_mem hj)

theorem extension_prime_not_dvd_period
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ}
    (hm : 0 < m) (hX : 1 < X) (I S : Finset FamilyIndex)
    (hmem : ∀ i ∈ I, StaticMem m P X Pz b i) (hSI : S ⊆ I)
    {i : FamilyIndex} (hi : i ∈ extensions m I S) :
    ¬ i.p ∣ period m S := by
  have his := hmem i (Finset.mem_filter.mp hi).1
  intro hp
  obtain ⟨j, hj, hpj⟩ := (prime_dvd_period_iff m S i.p his.p_prime).mp hp
  have hjs := hmem j (hSI hj)
  obtain hd | hpp := his.p_prime.dvd_mul.mp hpj
  · exact Nat.not_dvd_of_pos_of_lt hjs.dplus_pos
      (hjs.dplus_lt_other_prime hX his) hd
  · have hpeq : i.p = j.p :=
      (Nat.dvd_prime hjs.p_prime).mp hpp |>.resolve_left his.p_prime.ne_one
    have hcomp := (modular_compatible_iff his hjs).mp (extension_compatible hi hj)
    have heq := his.eq_of_compatible_same_prime hm hX hjs hpeq hcomp
    exact (Finset.mem_filter.mp hi).2.1 (heq.symm ▸ hj)

theorem overlap_dvd_dplus
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ}
    (hm : 0 < m) (hX : 1 < X) (I S : Finset FamilyIndex)
    (hmem : ∀ i ∈ I, StaticMem m P X Pz b i) (hSI : S ⊆ I)
    {i : FamilyIndex} (hi : i ∈ extensions m I S) :
    overlap m S i ∣ i.dplus := by
  have his := hmem i (Finset.mem_filter.mp hi).1
  have hp := his.p_prime.coprime_iff_not_dvd.mpr
    (extension_prime_not_dvd_period hm hX I S hmem hSI hi)
  have hg := hp.symm.coprime_dvd_left (Nat.gcd_dvd_left (period m S) i.q)
  exact hg.dvd_mul_right.mp (Nat.gcd_dvd_right (period m S) i.q)

/-- The residues `e_j mod p` of the members `j ∈ S` with `p ∣ d₊(j)`. -/
noncomputable def oldPrimeClasses (S : Finset FamilyIndex) (p : ℕ) : Finset ℕ :=
  (S.filter (fun i => p ∣ i.dplus)).image (fun i => i.e % p)

theorem oldPrimeClasses_eq (S : Finset FamilyIndex) (p : ℕ) :
    oldPrimeClasses S p =
      Family.familyOldPrimeResidueClasses (S.image FamilyIndex.toSatEvent) p := by
  unfold oldPrimeClasses Family.familyOldPrimeResidueClasses
  rw [Finset.filter_image, Finset.image_image]
  rfl

theorem extension_prime_class
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ}
    (hm : 0 < m) (hX : 1 < X) (I S : Finset FamilyIndex)
    (hmem : ∀ i ∈ I, StaticMem m P X Pz b i) (hSI : S ⊆ I)
    {i : FamilyIndex} (hi : i ∈ extensions m I S)
    {p : ℕ} (hp : Nat.Prime p) (hpg : p ∣ overlap m S i) :
    i.e % p ∈ oldPrimeClasses S p := by
  have his := hmem i (Finset.mem_filter.mp hi).1
  have hpL := hpg.trans (Nat.gcd_dvd_left (period m S) i.q)
  obtain ⟨j, hj, hpj⟩ := (prime_dvd_period_iff m S p hp).mp hpL
  have hjs := hmem j (hSI hj)
  have hpdp := hpg.trans (overlap_dvd_dplus hm hX I S hmem hSI hi)
  have hpdpj : p ∣ j.dplus := by
    obtain hd | hpp := hp.dvd_mul.mp hpj
    · exact hd
    · have heq : p = j.p :=
        (Nat.dvd_prime hjs.p_prime).mp hpp |>.resolve_left hp.ne_one
      exact (Nat.not_dvd_of_pos_of_lt his.dplus_pos
        (his.dplus_lt_other_prime hX hjs) (heq ▸ hpdp)).elim
  have hmod := (e_modEq_of_modular_compatible his hjs
    (extension_compatible hi hj)).of_dvd
      (Nat.dvd_gcd (hpdp.trans (dvd_mul_right i.dplus i.p)) hpj)
  exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hpdpj⟩, hmod.symm⟩

end ErdosStraus.FixedNumeratorFamily

/-! ## Events sharing a large prime (Lemma 6.8) -/

namespace ErdosStraus.DirectPrimeCount

open Classical Family
open scoped BigOperators

private theorem fiber_card_le_floor (I : Finset FamilyIndex) (p : ℕ) (H : ℝ)
    (hpos : ∀ i ∈ I, 0 < i.e)
    (hbound : ∀ i ∈ I, (i.e : ℝ) ≤ H)
    (hunique : ∀ i ∈ I, ∀ j ∈ I, i.e = j.e → i.p = j.p → i = j) :
    (I.filter (fun i => i.p = p)).card ≤ ⌊H⌋₊ := by
  have hh := Finset.card_le_card_of_injOn FamilyIndex.e
    (s := I.filter (fun i => i.p = p)) (t := Finset.Icc 1 ⌊H⌋₊)
    (fun i hi => Finset.mem_Icc.mpr
      ⟨hpos i (Finset.mem_filter.mp hi).1,
        Nat.le_floor (hbound i (Finset.mem_filter.mp hi).1)⟩)
    (by
      intro i hi j hj he
      exact hunique i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 he
        ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm))
  simpa using hh

private theorem fiber_reciprocal_le (I : Finset FamilyIndex) (p : ℕ) (H : ℝ)
    (hp : 0 < p) (hH : 0 ≤ H)
    (hcard : (I.filter (fun i => i.p = p)).card ≤ ⌊H⌋₊)
    (hd : ∀ i ∈ I, 0 < i.dplus) :
    (∑ i ∈ I.filter (fun i => i.p = p), (1 : ℝ) / i.q) ≤ H / p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  calc
    _ ≤ ∑ _i ∈ I.filter (fun i => i.p = p), (1 : ℝ) / p := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨hiI, hip⟩ := Finset.mem_filter.mp hi
      have hdR : (1 : ℝ) ≤ i.dplus := by exact_mod_cast hd i hiI
      change 1 / ((i.dplus * i.p : ℕ) : ℝ) ≤ _
      rw [Nat.cast_mul, hip]
      exact one_div_le_one_div_of_le hpR (le_mul_of_one_le_left hpR.le hdR)
    _ = ((I.filter (fun i => i.p = p)).card : ℝ) / p := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    _ ≤ (⌊H⌋₊ : ℝ) / p :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) hpR.le
    _ ≤ H / p := div_le_div_of_nonneg_right (Nat.floor_le hH) hpR.le

theorem fixed_prime_fiber_card_le (m : ℕ) (hm : 0 < m)
    (P : Params) (X : ℝ) (Pz b p : ℕ) (I : Finset FamilyIndex) (hX : 1 < X)
    (hmem : ∀ i ∈ I, FixedNumeratorFamily.StaticMem m P X Pz b i) :
    (I.filter (fun i => i.p = p)).card ≤ ⌊HScale P X⌋₊ := by
  apply fiber_card_le_floor
  · intro i hi
    have hs : (0 : ℝ) < i.E.s := by exact_mod_cast (hmem i hi).s_pos
    have hrR : (0 : ℝ) < i.E.r :=
      (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hX) _) hs).trans (hmem i hi).r_gt
    have hr : 0 < i.E.r := by exact_mod_cast hrR
    exact Nat.mul_pos hr (pow_pos (by exact_mod_cast hs) 2)
  · intro i hi
    have hs : (0 : ℝ) < i.E.s := by exact_mod_cast (hmem i hi).s_pos
    simpa only [FamilyIndex.e, ExactDivisor.e, Nat.cast_mul, Nat.cast_pow] using
      (le_div_iff₀ (pow_pos hs 2)).mp (hmem i hi).r_le
  · intro i hi j hj he hp
    apply FixedNumeratorFamily.StaticMem.eq_of_compatible_same_prime hm hX
      (hmem i hi) (hmem j hj) hp
    change m * i.e ≡ m * j.e [MOD Nat.gcd i.q j.q]
    rw [he]

/-- Lemma 6.8: the members with a given large prime `p` have total weight at most
`H/p`, since such a member is determined by `e ≤ H`. -/
theorem fixed_prime_fiber_reciprocal_le (m : ℕ) (hm : 0 < m)
    (P : Params) (X : ℝ) (Pz b p : ℕ) (I : Finset FamilyIndex) (hX : 1 < X)
    (hmem : ∀ i ∈ I, FixedNumeratorFamily.StaticMem m P X Pz b i) (hp : 0 < p) :
    (∑ i ∈ I.filter (fun i => i.p = p), (1 : ℝ) / i.q) ≤ HScale P X / p :=
  fiber_reciprocal_le I p _ hp (Real.rpow_nonneg (zero_lt_one.trans hX).le _)
    (fixed_prime_fiber_card_le m hm P X Pz b p I hX hmem)
    (fun i hi => (hmem i hi).dplus_pos)

theorem conductor_div_prime_le_power (P : Params) {X : ℝ} (hX : 0 < X)
    {p : ℕ} (hp : X ^ P.β ≤ (p : ℝ)) :
    HScale P X / p ≤ X ^ (P.θ - P.β) := by
  calc
    HScale P X / p ≤ HScale P X / X ^ P.β :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hX.le _)
        (Real.rpow_pos_of_pos hX _) hp
    _ = _ := (Real.rpow_sub hX _ _).symm

theorem fixed_prime_fiber_le_power (m : ℕ) (hm : 0 < m)
    (P : Params) (X : ℝ) (Pz b : ℕ) (I : Finset FamilyIndex) (hX : 1 < X)
    (hmem : ∀ i ∈ I, FixedNumeratorFamily.StaticMem m P X Pz b i)
    {i : FamilyIndex} (hi : i ∈ I) :
    (∑ j ∈ I.filter (fun j => j.p = i.p), (1 : ℝ) / j.q) ≤ X ^ (P.θ - P.β) :=
  (fixed_prime_fiber_reciprocal_le m hm P X Pz b i.p I hX hmem
    (hmem i hi).p_prime.pos).trans
      (conductor_div_prime_le_power P (zero_lt_one.trans hX) (hmem i hi).p_gt.le)

theorem prime_power_tendsto_zero (P : Params) :
    Filter.Tendsto (fun X : ℝ => X ^ (P.θ - P.β)) Filter.atTop (nhds 0) := by
  have hgap : 0 < P.β - P.θ := by linarith [P.two_θ_lt_β, P.θ_pos]
  simpa only [neg_sub] using tendsto_rpow_neg_atTop hgap

end ErdosStraus.DirectPrimeCount

/-! ## The neighbour mass `δ_b` -/

namespace ErdosStraus.FixedNumeratorFamily

open Classical Family Filter
open scoped BigOperators

theorem StaticMem.medium_prime_recip_sum_le
    {m : ℕ} {P : Params} {X : ℝ} {b : ℕ} {i : FamilyIndex}
    (hX : Real.exp 2 ≤ X) (h : StaticMem m P X (Estimates.roughModulus X) b i) :
    (∑ p ∈ i.dplus.primeFactors, (1 : ℝ) / p) ≤ incrementFloorScale P X := by
  let q := ⌊zScale X⌋₊ + 1
  have hXe : Real.exp 1 ≤ X := (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hX
  have hq : 2 ≤ q := two_le_succ_floor_zScale hXe
  have hrough : ∀ p ∈ i.dplus.primeFactors, q ≤ p := by
    intro p hp
    by_contra hpq
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpdiv := (Nat.mem_primeFactors.mp hp).2.1
    have hpP : p ∣ Estimates.roughModulus X := by
      unfold Estimates.roughModulus Estimates.primeProductBelow
      apply Finset.dvd_prod_of_mem
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨hpp.two_le, by dsimp [q] at hpq; omega⟩, hpp⟩
    exact hpp.not_dvd_one (by simpa only [h.dplus_coprime_Pz.gcd_eq_one] using
      (Nat.dvd_gcd hpdiv hpP))
  have hh := ErdosStraus.Arithmetic.primeFactors_recip_sum_le_log_div_log_div
    i.dplus q h.dplus_pos hq hrough
  have hlog : Real.log (i.dplus : ℝ) ≤ Real.log (YScale P X) :=
    Real.log_le_log (by exact_mod_cast h.dplus_pos) h.dplus_le_YScale
  exact hh.trans (div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right hlog
      (Real.log_pos (by exact_mod_cast hq : (1 : ℝ) < q)).le) (Nat.cast_nonneg q))

/-- A neighbour `j` of `i` either has the same large prime as `i` or satisfies
`p ∣ d₊(j)` for some prime `p ∣ d₊(i)`. -/
theorem neighbour_mass_le_prime_divisor_sums
    (m : ℕ) (P : Params) (X : ℝ) (Pz b : ℕ) (indices : Finset FamilyIndex)
    (hX : 1 < X) (hmem : ∀ i ∈ indices, StaticMem m P X Pz b i)
    {i : FamilyIndex} (hi : i ∈ indices) :
    Estimates.modularNeighbourMass (modularEvents m indices) (modularEvent m i) ≤
      (∑ j ∈ indices.filter (fun j => j.p = i.p), (1 : ℝ) / j.q) +
        ∑ p ∈ i.dplus.primeFactors,
          ∑ j ∈ indices.filter (fun j => p ∣ j.dplus), (1 : ℝ) / j.q := by
  unfold Estimates.modularNeighbourMass modularEvents
  rw [Finset.filter_image, Finset.sum_image (fun a _ b _ h => modularEvent_injective m h)]
  change (∑ j ∈ indices.filter (fun j =>
    Estimates.modularDependent (modularEvent m i) (modularEvent m j)), (1 : ℝ) / j.q) ≤ _
  let w : FamilyIndex → ℝ := fun j => (1 : ℝ) / j.q
  have hpos : ∀ j, 0 ≤ (if j.p = i.p then w j else 0) +
      ∑ p ∈ i.dplus.primeFactors, if p ∣ j.dplus then w j else 0 := by
    intro j
    apply add_nonneg
    · dsimp only [w]
      split_ifs <;> positivity
    · apply Finset.sum_nonneg
      intro p _hp
      dsimp only [w]
      split_ifs <;> positivity
  calc
    _ ≤ ∑ j ∈ indices.filter (fun j =>
        Estimates.modularDependent (modularEvent m i) (modularEvent m j)),
        ((if j.p = i.p then w j else 0) +
          ∑ p ∈ i.dplus.primeFactors, if p ∣ j.dplus then w j else 0) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hjI, hdep⟩ := Finset.mem_filter.mp hj
      have hsplit := dependent_largePrime_or_medium hX (hmem i hi) (hmem j hjI) hdep
      rcases hsplit with hsame | hmedium
      · rw [if_pos hsame.symm]
        have hn : 0 ≤ ∑ p ∈ i.dplus.primeFactors, if p ∣ j.dplus then w j else 0 := by
          apply Finset.sum_nonneg
          intro p _hp
          dsimp only [w]
          split_ifs <;> positivity
        change w j ≤ _
        linarith
      · obtain ⟨p, hpp, hpi, hpj⟩ := Nat.Prime.not_coprime_iff_dvd.mp hmedium
        have hpI : p ∈ i.dplus.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hpp, hpi, (hmem i hi).dplus_pos.ne'⟩
        have hh := Finset.single_le_sum (s := i.dplus.primeFactors)
          (f := fun p => if p ∣ j.dplus then w j else 0)
          (by intro p _hp; dsimp only [w]; split_ifs <;> positivity) hpI
        rw [if_pos hpj] at hh
        have hn : 0 ≤ if j.p = i.p then w j else 0 := by
          dsimp only [w]
          split_ifs <;> positivity
        change w j ≤ _
        linarith
    _ ≤ ∑ j ∈ indices, ((if j.p = i.p then w j else 0) +
        ∑ p ∈ i.dplus.primeFactors, if p ∣ j.dplus then w j else 0) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun j _hj _hnot => hpos j)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      simp only [← Finset.sum_filter, w]

theorem modularDelta_upper (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → Real.exp 2 ≤ X →
      ∀ b : ℕ, ∀ indices : Finset FamilyIndex,
        (∀ i ∈ indices, StaticMem m P X (Estimates.roughModulus X) b i) →
        Estimates.modularDelta (modularEvents m indices) ≤
          C * (Real.log X) ^ 3 * incrementFloorScale P X +
            X ^ (P.θ - P.β) := by
  obtain ⟨C, X₀, hC, hu⟩ := event_upper_log_cube m hm P
  refine ⟨C, X₀, hC, ?_⟩
  intro X hX hXe b indices hmem
  have hX1 : 1 < X := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).trans_le hXe
  have hlog : 0 ≤ Real.log X := (Real.log_pos hX1).le
  have hpoint : ∀ i ∈ indices,
      Estimates.modularNeighbourMass (modularEvents m indices) (modularEvent m i) ≤
        C * (Real.log X) ^ 3 * incrementFloorScale P X +
          X ^ (P.θ - P.β) := by
    intro i hi
    have h := hmem i hi
    have hmedium : (∑ p ∈ i.dplus.primeFactors,
        ∑ j ∈ indices.filter (fun j => p ∣ j.dplus), (1 : ℝ) / j.q) ≤
        C * (Real.log X) ^ 3 * incrementFloorScale P X := by
      calc
        _ ≤ ∑ p ∈ i.dplus.primeFactors, C * (Real.log X) ^ 3 / (p : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          obtain ⟨hpp, hpdiv, _hpne⟩ := Nat.mem_primeFactors.mp hp
          have hpP := h.dplus_coprime_Pz.coprime_dvd_left hpdiv
          have hpY : (p : ℝ) ≤ YScale P X :=
            (show (p : ℝ) ≤ i.dplus by exact_mod_cast Nat.le_of_dvd h.dplus_pos hpdiv).trans
              h.dplus_le_YScale
          simpa only [FamilyIndex.q] using
            (hu X hX hX1 b indices hmem p hpp.pos hpP hpY).2
        _ = C * (Real.log X) ^ 3 * ∑ p ∈ i.dplus.primeFactors, (1 : ℝ) / p := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun _ _ => by ring)
        _ ≤ _ := mul_le_mul_of_nonneg_left (h.medium_prime_recip_sum_le hXe) (by positivity)
    have hsplit := neighbour_mass_le_prime_divisor_sums m P X _ b indices hX1 hmem hi
    have hlarge := DirectPrimeCount.fixed_prime_fiber_le_power
      m hm P X _ b indices hX1 hmem hi
    linarith
  unfold Estimates.modularDelta
  split_ifs with hne
  · apply Finset.sup'_le hne
    intro event hevent
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hevent
    exact hpoint i hi
  · exact add_nonneg
      (mul_nonneg (mul_nonneg hC.le (pow_nonneg hlog _)) (incrementFloorScale_nonneg P hXe))
      (Real.rpow_nonneg (zero_le_one.trans hX1.le) _)

/-- Lemma 6.9, first bound: `δ_b = o_m(1)` uniformly in `b`. For every `ε > 0`,
eventually `δ_b ≤ ε` for all base classes `b`. -/
theorem modularDelta_eventually_small (m : ℕ) (hm : 0 < m) (P : Params)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ b : ℕ,
      Estimates.modularDelta (modularEvents m
        (indexFinset m P X (Estimates.roughModulus X) b)) ≤ ε := by
  obtain ⟨C, X₀, _hC, hu⟩ := modularDelta_upper m hm P
  have hlim : Tendsto (fun X : ℝ =>
      C * (Real.log X) ^ 3 * incrementFloorScale P X +
        X ^ (P.θ - P.β)) atTop (nhds 0) := by
    have hh := ((incrementFloorScale_logCube_tendsto_zero P).const_mul C).add
      (DirectPrimeCount.prime_power_tendsto_zero P)
    simpa only [mul_assoc, mul_zero, zero_add] using hh
  have hsmall := hlim.eventually (gt_mem_nhds hε)
  filter_upwards [hsmall, eventually_ge_atTop X₀, eventually_ge_atTop (Real.exp 2)] with
    X hsmallX hX hXe
  intro b
  apply (hu X hX hXe b _ _).trans hsmallX.le
  intro i hi
  exact (mem_indexFinset_iff m P X _ b i
    ((Real.exp_pos 2).trans_le hXe)).mp hi

end ErdosStraus.FixedNumeratorFamily

/-! ## Residue classes of compatible extensions -/

namespace ErdosStraus.FixedNumeratorFamily

open Classical Family

theorem StaticMem.dplus_odd_at_rough_scale
    {m : ℕ} {P : Params} {X : ℝ} {b : ℕ} {i : FamilyIndex}
    (hX : Real.exp 2 ≤ X) (hi : StaticMem m P X (Estimates.roughModulus X) b i) :
    Odd i.dplus := by
  have hlog : 2 ≤ Real.log X := by
    rw [← Real.log_exp 2]
    exact Real.log_le_log (Real.exp_pos 2) hX
  have hz : (2 : ℝ) ≤ zScale X := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hlog 4
    norm_num at h
    exact (by norm_num : (2 : ℝ) ≤ 16).trans h
  have htwo : 2 ∣ Estimates.roughModulus X :=
    prime_dvd_roughModulus_of_lt_succ_floor Nat.prime_two
      (Nat.lt_succ_of_le (Nat.le_floor hz))
  exact Nat.coprime_two_right.mp (hi.dplus_coprime_Pz.coprime_dvd_right htwo)

theorem residue_classes_card_le_prime_product
    (D : ℕ) (hD : 0 < D) (hDs : Squarefree D)
    (C : Finset ℕ) (A : ℕ → Finset ℕ)
    (hC : ∀ c ∈ C, c < D)
    (hA : ∀ c ∈ C, ∀ p ∈ D.primeFactors, c % p ∈ A p) :
    C.card ≤ ∏ p ∈ D.primeFactors, (A p).card := by
  let target := D.primeFactors.pi A
  let code : ℕ → ((p : ℕ) → p ∈ D.primeFactors → ℕ) := fun c p _ => c % p
  have hmap : ∀ c ∈ C, code c ∈ target := by
    intro c hc
    exact Finset.mem_pi.mpr (hA c hc)
  have hpairwise : ∀ l : List ℕ, l.Nodup →
      (∀ p ∈ l, Nat.Prime p) → l.Pairwise Nat.Coprime := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
      intro hn hp
      rw [List.nodup_cons] at hn
      rw [List.pairwise_cons]
      refine ⟨?_, ih hn.2 (fun q hq => hp q (by simp [hq]))⟩
      intro q hq
      apply (Nat.coprime_primes (hp p (by simp)) (hp q (by simp [hq]))).mpr
      intro heq
      exact hn.1 (heq ▸ hq)
  have hpair : D.primeFactorsList.Pairwise Nat.Coprime :=
    hpairwise _ ((Nat.squarefree_iff_nodup_primeFactorsList hD.ne').mp hDs)
      (fun _ hp => Nat.prime_of_mem_primeFactorsList hp)
  have hinj : Set.InjOn code (C : Set ℕ) := by
    intro c hc d hd heq
    have hmod : c ≡ d [MOD D] := by
      rw [← Nat.prod_primeFactorsList hD.ne']
      apply (Nat.modEq_list_prod_iff hpair).mpr
      intro k
      have hk := Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr
        (D.primeFactorsList.get_mem k)
      exact congrFun (congrFun heq _) hk
    exact hmod.eq_of_lt_of_lt (hC c hc) (hC d hd)
  have hcard := Finset.card_le_card_of_injOn code hmap hinj
  simpa only [target, Finset.card_pi] using hcard

/-- The compatible extensions `i` of `S` with `D ∣ (q_i, L_S)`. -/
noncomputable def divisorExtensions (m : ℕ) (I S : Finset FamilyIndex) (D : ℕ) :
    Finset FamilyIndex := (extensions m I S).filter (fun i => D ∣ overlap m S i)

/-- The residues `e_i mod D` of the extensions in `divisorExtensions m I S D`. -/
noncomputable def extensionResidueClasses
    (m : ℕ) (I S : Finset FamilyIndex) (D : ℕ) : Finset ℕ :=
  (divisorExtensions m I S D).image (fun i => i.e % D)

theorem extensionResidueClasses_card_le
    {m : ℕ} {P : Params} {X : ℝ} {b : ℕ}
    (hm : 0 < m) (hX : Real.exp 2 ≤ X) (I S : Finset FamilyIndex)
    (hmem : ∀ i ∈ I, StaticMem m P X (Estimates.roughModulus X) b i)
    (hSI : S ⊆ I) (D : ℕ) :
    ((extensionResidueClasses m I S D).card : ℝ) ≤
      (Family.familyIncrementClassProductRat (S.image FamilyIndex.toSatEvent) D : ℝ) := by
  have hX1 : 1 < X := (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hX
  by_cases hne : (extensionResidueClasses m I S D).Nonempty
  · obtain ⟨c, hc⟩ := hne
    obtain ⟨i, hi, _⟩ := Finset.mem_image.mp hc
    obtain ⟨hiext, hDg⟩ := Finset.mem_filter.mp hi
    have his := hmem i (Finset.mem_filter.mp hiext).1
    have hDdp := hDg.trans (overlap_dvd_dplus hm hX1 I S hmem hSI hiext)
    have hDpos := Nat.pos_of_dvd_of_pos hDdp his.dplus_pos
    have hDsq := his.dplus_squarefree.squarefree_of_dvd hDdp
    have hDodd := Odd.of_dvd_nat (his.dplus_odd_at_rough_scale hX) hDdp
    have hcard := residue_classes_card_le_prime_product D hDpos hDsq
      (extensionResidueClasses m I S D) (oldPrimeClasses S) (by
        intro c hc
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
        exact Nat.mod_lt _ hDpos) (by
        intro c hc p hp
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
        obtain ⟨hiext, hDg⟩ := Finset.mem_filter.mp hi
        have hpD := (Nat.mem_primeFactors.mp hp).2.1
        have ht := extension_prime_class hm hX1 I S hmem hSI hiext
          (Nat.mem_primeFactors.mp hp).1 (hpD.trans hDg)
        simpa only [Nat.mod_mod_of_dvd _ hpD] using ht)
    rw [Family.familyIncrementClassProductRat, if_pos ⟨hDsq, hDodd⟩]
    simp only [oldPrimeClasses_eq] at hcard
    exact_mod_cast hcard
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
    unfold Family.familyIncrementClassProductRat
    split_ifs <;> positivity

theorem classProduct_sum_le_exp_card
    {m : ℕ} {P : Params} {X : ℝ} {b : ℕ}
    (hX : Real.exp 2 ≤ X) (S : Finset FamilyIndex)
    (hmem : ∀ i ∈ S, StaticMem m P X (Estimates.roughModulus X) b i)
    (B : ℕ) (hB : 1 ≤ B) :
    (∑ D ∈ Finset.Icc 2 B,
      (Family.familyIncrementClassProductRat (S.image FamilyIndex.toSatEvent) D : ℝ) /
        (D : ℝ)) ≤ Real.exp ((S.card : ℝ) * incrementFloorScale P X) - 1 := by
  let old := S.image FamilyIndex.toSatEvent
  have hexp := Family.familyOldPrimeClass_exponent_le_event_primeDivisor_sum old B
  have hprime : ∀ event ∈ old,
      (∑ p ∈ (ErdosStraus.Arithmetic.primeFinsetUpTo B).filter (fun p => p ∣ event.dPlus),
        (1 : ℝ) / (p : ℝ)) ≤ incrementFloorScale P X := by
    intro event he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    apply (Finset.sum_le_sum_of_subset_of_nonneg ?_ (by intros; positivity)).trans
      ((hmem i hi).medium_prime_recip_sum_le hX)
    intro p hp
    obtain ⟨hpB, hpdp⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr
      ⟨(Finset.mem_filter.mp hpB).2, hpdp, (hmem i hi).dplus_pos.ne'⟩
  have hbound : (∑ p ∈ ErdosStraus.Arithmetic.primeFinsetUpTo B,
      ((Family.familyOldPrimeResidueClasses old p).card : ℝ) / (p : ℝ)) ≤
        (S.card : ℝ) * incrementFloorScale P X := by
    apply hexp.trans
    calc
      _ ≤ ∑ _event ∈ old, incrementFloorScale P X :=
        Finset.sum_le_sum hprime
      _ = (old.card : ℝ) * incrementFloorScale P X := by simp
      _ ≤ (S.card : ℝ) * incrementFloorScale P X :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_image_le)
          (incrementFloorScale_nonneg P hX)
  have h := (Family.familyIncrementClassProduct_real_sum_le_exp old B hB).trans
    (Real.exp_le_exp.mpr hbound)
  linarith

/-! ## The correction term -/

/-- The weight of the compatible extensions `i` of `S` with `D ∣ (q_i, L_S)`. -/
noncomputable def divisorExtensionMass
    (m : ℕ) (I S : Finset FamilyIndex) (D : ℕ) : ℝ :=
  ∑ i ∈ divisorExtensions m I S D, (1 : ℝ) / (i.q : ℝ)

/-- The part of `A(S)` coming from extensions with overlap `(q_i, L_S) > 1`. -/
noncomputable def correction (m : ℕ) (I S : Finset FamilyIndex) : ℝ :=
  ∑ i ∈ extensions m I S,
    (1 : ℝ) / (i.q : ℝ) * (if 1 < overlap m S i then (overlap m S i : ℝ) else 0)

theorem divisorExtensionMass_eq_classes
    (m : ℕ) (I S : Finset FamilyIndex) (D : ℕ) :
    divisorExtensionMass m I S D =
      ∑ c ∈ extensionResidueClasses m I S D,
        ∑ i ∈ (divisorExtensions m I S D).filter (fun i => i.e % D = c),
          (1 : ℝ) / (i.q : ℝ) := by
  unfold divisorExtensionMass extensionResidueClasses
  symm
  apply Finset.sum_fiberwise_of_maps_to
  intro i hi
  exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

theorem divisorExtensionMass_le
    {m : ℕ} {P : Params} {X : ℝ} {b : ℕ}
    (hm : 0 < m) (hX : Real.exp 2 ≤ X) (I S : Finset FamilyIndex)
    (hmem : ∀ i ∈ I, StaticMem m P X (Estimates.roughModulus X) b i)
    (hSI : S ⊆ I) (A : ℝ) (hA : 0 ≤ A)
    (htensor : ∀ D c : ℕ, 0 < D → Nat.Coprime D (Estimates.roughModulus X) →
      (D : ℝ) ≤ YScale P X →
      (∑ i ∈ I.filter (fun i => D ∣ i.dplus ∧ i.e % D = c),
        (1 : ℝ) / (i.q : ℝ)) ≤ A / (D : ℝ) ^ 2)
    (D : ℕ) (hD : 0 < D) :
    divisorExtensionMass m I S D ≤
      A * (Family.familyIncrementClassProductRat (S.image FamilyIndex.toSatEvent) D : ℝ) /
        (D : ℝ) ^ 2 := by
  have hX1 : 1 < X := (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hX
  have hinner : ∀ c ∈ extensionResidueClasses m I S D,
      (∑ i ∈ (divisorExtensions m I S D).filter (fun i => i.e % D = c),
        (1 : ℝ) / (i.q : ℝ)) ≤ A / (D : ℝ) ^ 2 := by
    intro c hc
    obtain ⟨i, hi, _⟩ := Finset.mem_image.mp hc
    obtain ⟨hiext, hDg⟩ := Finset.mem_filter.mp hi
    have his := hmem i (Finset.mem_filter.mp hiext).1
    have hDdp := hDg.trans (overlap_dvd_dplus hm hX1 I S hmem hSI hiext)
    have hcop := his.dplus_coprime_Pz.coprime_dvd_left hDdp
    have hDY : (D : ℝ) ≤ YScale P X :=
      (Nat.cast_le.mpr (Nat.le_of_dvd his.dplus_pos hDdp)).trans his.dplus_le_YScale
    apply (Finset.sum_le_sum_of_subset_of_nonneg ?_ (by intros; positivity)).trans
      (htensor D c hD hcop hDY)
    intro j hj
    obtain ⟨hjD, hje⟩ := Finset.mem_filter.mp hj
    obtain ⟨hjext, hDgj⟩ := Finset.mem_filter.mp hjD
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hjext).1,
      hDgj.trans (overlap_dvd_dplus hm hX1 I S hmem hSI hjext), hje⟩
  rw [divisorExtensionMass_eq_classes]
  calc
    _ ≤ ∑ _c ∈ extensionResidueClasses m I S D, A / (D : ℝ) ^ 2 :=
      Finset.sum_le_sum hinner
    _ = ((extensionResidueClasses m I S D).card : ℝ) * (A / (D : ℝ) ^ 2) := by simp
    _ ≤ (Family.familyIncrementClassProductRat (S.image FamilyIndex.toSatEvent) D : ℝ) *
        (A / (D : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right
        (extensionResidueClasses_card_le hm hX I S hmem hSI D) (by positivity)
    _ = _ := by ring

theorem overlap_le_floor
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ}
    (hm : 0 < m) (hX : 1 < X) (I S : Finset FamilyIndex)
    (hmem : ∀ i ∈ I, StaticMem m P X Pz b i) (hSI : S ⊆ I)
    {i : FamilyIndex} (hi : i ∈ extensions m I S) : overlap m S i ≤ ⌊X⌋₊ := by
  have his := hmem i (Finset.mem_filter.mp hi).1
  have hg := Nat.le_of_dvd his.dplus_pos (overlap_dvd_dplus hm hX I S hmem hSI hi)
  have hY : YScale P X ≤ X := by
    calc
      _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX.le (by
        linarith [P.β_pos, P.β_lt_one_sub_σ])
      _ = X := Real.rpow_one X
  exact hg.trans (Nat.le_floor (his.dplus_le_YScale.trans hY))

theorem correction_le_divisor_sum
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ}
    (hm : 0 < m) (hX : 1 < X) (I S : Finset FamilyIndex)
    (hmem : ∀ i ∈ I, StaticMem m P X Pz b i) (hSI : S ⊆ I) :
    correction m I S ≤ ∑ D ∈ Finset.Icc 2 ⌊X⌋₊,
      (D : ℝ) * divisorExtensionMass m I S D := by
  unfold correction
  calc
    _ ≤ ∑ i ∈ extensions m I S, ∑ D ∈ Finset.Icc 2 ⌊X⌋₊,
        (D : ℝ) * (if D ∣ overlap m S i then (1 : ℝ) / (i.q : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hg : 1 < overlap m S i
      · have hgm : overlap m S i ∈ Finset.Icc 2 ⌊X⌋₊ :=
          Finset.mem_Icc.mpr ⟨by omega, overlap_le_floor hm hX I S hmem hSI hi⟩
        have hs := Finset.single_le_sum (s := Finset.Icc (2 : ℕ) ⌊X⌋₊)
          (f := fun D : ℕ => (D : ℝ) *
            (if D ∣ overlap m S i then (1 : ℝ) / (i.q : ℝ) else 0))
          (fun _ _ => by split_ifs <;> positivity) hgm
        simpa [hg, mul_comm] using hs
      · simp only [hg, if_false, mul_zero]
        exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro D hD
      simp only [divisorExtensionMass, divisorExtensions, Finset.sum_filter, Finset.mul_sum]

/-- If every residue-class weight `B_{D,c}` is at most `A/D²`, the correction term of a
set `S` is at most `A (exp(|S| s(X)) - 1)`, where `s = incrementFloorScale`. -/
theorem correction_le_euler_loss
    {m : ℕ} {P : Params} {X : ℝ} {b : ℕ}
    (hm : 0 < m) (hX : Real.exp 2 ≤ X) (I S : Finset FamilyIndex)
    (hmem : ∀ i ∈ I, StaticMem m P X (Estimates.roughModulus X) b i)
    (hSI : S ⊆ I) (A : ℝ) (hA : 0 ≤ A)
    (htensor : ∀ D c : ℕ, 0 < D → Nat.Coprime D (Estimates.roughModulus X) →
      (D : ℝ) ≤ YScale P X →
      (∑ i ∈ I.filter (fun i => D ∣ i.dplus ∧ i.e % D = c),
        (1 : ℝ) / (i.q : ℝ)) ≤ A / (D : ℝ) ^ 2) :
    correction m I S ≤ A *
      (Real.exp ((S.card : ℝ) * incrementFloorScale P X) - 1) := by
  have hX1 : 1 < X := (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hX
  apply (correction_le_divisor_sum hm hX1 I S hmem hSI).trans
  calc
    _ ≤ ∑ D ∈ Finset.Icc 2 ⌊X⌋₊,
        A * ((Family.familyIncrementClassProductRat (S.image FamilyIndex.toSatEvent) D : ℝ) /
          (D : ℝ)) := by
      apply Finset.sum_le_sum
      intro D hD
      have hDp : 0 < D := by have := (Finset.mem_Icc.mp hD).1; omega
      apply (mul_le_mul_of_nonneg_left
        (divisorExtensionMass_le hm hX I S hmem hSI A hA htensor D hDp)
        (Nat.cast_nonneg D)).trans_eq
      field_simp [Nat.cast_ne_zero.mpr hDp.ne']
    _ = A * (∑ D ∈ Finset.Icc 2 ⌊X⌋₊,
        (Family.familyIncrementClassProductRat (S.image FamilyIndex.toSatEvent) D : ℝ) /
          (D : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (classProduct_sum_le_exp_card hX S (fun i hi => hmem i (hSI hi))
        ⌊X⌋₊ (Nat.floor_pos.mpr hX1.le)) hA

theorem increment_le_mass_add_correction
    (m : ℕ) (I S : Finset FamilyIndex) :
    increment m I S ≤ indexMass I + correction m I S := by
  unfold increment correction
  calc
    _ ≤ ∑ i ∈ extensions m I S,
        ((1 : ℝ) / (i.q : ℝ) + (1 : ℝ) / (i.q : ℝ) *
          (if 1 < overlap m S i then (overlap m S i : ℝ) else 0)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hw : (0 : ℝ) ≤ 1 / (i.q : ℝ) := by positivity
      split_ifs with hg
      · nlinarith
      · have hg' : (overlap m S i : ℝ) ≤ 1 := by exact_mod_cast (by omega : overlap m S i ≤ 1)
        simpa using mul_le_mul_of_nonneg_left hg' hw
    _ = (∑ i ∈ extensions m I S, (1 : ℝ) / (i.q : ℝ)) +
        ∑ i ∈ extensions m I S, (1 : ℝ) / (i.q : ℝ) *
          (if 1 < overlap m S i then (overlap m S i : ℝ) else 0) := by
      rw [Finset.sum_add_distrib]
    _ ≤ _ := add_le_add_left (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (by intros; positivity)) _

/-! ## The dependency mass `Δ_b` -/

theorem period_singleton (m : ℕ) (i : FamilyIndex) : period m {i} = i.q := by
  simp [period, modularEvents, ModularFamily.period, ModularFamily.rows,
    ModularFamily.row, ErdosStraus.Arithmetic.congruenceLcm, modularEvent]

theorem compatible_insert_singleton_iff (m : ℕ) (i j : FamilyIndex) :
    Compatible m (insert j {i}) ↔
      ErdosStraus.Arithmetic.residueCompatible i.q j.q
        (modularEvent m i).residue (modularEvent m j).residue := by
  rw [compatible_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    exact h i (Or.inr rfl) j (Or.inl rfl)
  · intro h a ha b hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Nat.ModEq.refl _
    · simpa [ErdosStraus.Arithmetic.residueCompatible, Nat.gcd_comm] using h.symm
    · exact h
    · exact Nat.ModEq.refl _

theorem pairMass_eq_weight_gcd (m : ℕ) (i j : FamilyIndex)
    (hi : 0 < i.q) (hj : 0 < j.q)
    (hc : ErdosStraus.Arithmetic.residueCompatible i.q j.q
      (modularEvent m i).residue (modularEvent m j).residue) :
    Estimates.modularPairMass (modularEvent m i) (modularEvent m j) =
      (1 : ℝ) / i.q * (1 / j.q) * (Nat.gcd i.q j.q : ℝ) := by
  have hl : 0 < Nat.lcm i.q j.q := Nat.lcm_pos hi hj
  have hg : (Nat.gcd i.q j.q : ℝ) * (Nat.lcm i.q j.q : ℝ) =
      (i.q : ℝ) * j.q := by exact_mod_cast Nat.gcd_mul_lcm i.q j.q
  change (modularEvent m i).residue ≡ (modularEvent m j).residue
    [MOD Nat.gcd i.q j.q] at hc
  unfold Estimates.modularPairMass
  simp only [show (modularEvent m i).modulus = i.q from rfl,
    show (modularEvent m j).modulus = j.q from rfl]
  rw [if_pos hc]
  field_simp [Nat.cast_ne_zero.mpr hi.ne', Nat.cast_ne_zero.mpr hj.ne',
    Nat.cast_ne_zero.mpr hl.ne']
  nlinarith only [hg]

theorem dependencyMass_le_singleton_corrections
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ}
    (I : Finset FamilyIndex)
    (hmem : ∀ i ∈ I, StaticMem m P X Pz b i) :
    Estimates.modularDependencyMass (modularEvents m I) ≤
      ∑ i ∈ I, (1 : ℝ) / i.q * correction m I {i} := by
  unfold Estimates.modularDependencyMass modularEvents
  rw [Finset.sum_image (fun i _ j _ h => modularEvent_injective m h)]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.sum_filter, Finset.sum_image (fun i _ j _ h => modularEvent_injective m h)]
  rw [correction, Finset.mul_sum, extensions, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hd : Estimates.modularDependent (modularEvent m i) (modularEvent m j)
  · by_cases hc : ErdosStraus.Arithmetic.residueCompatible i.q j.q
        (modularEvent m i).residue (modularEvent m j).residue
    · have hneq : j ≠ i := by
        intro he; exact hd.1 (congrArg (modularEvent m) he.symm)
      have hext : j ∉ ({i} : Finset FamilyIndex) ∧ Compatible m (insert j {i}) :=
        ⟨by simpa using hneq, (compatible_insert_singleton_iff m i j).mpr hc⟩
      have hg : 1 < Nat.gcd i.q j.q := by
        have hp := Nat.gcd_pos_of_pos_left j.q (hmem i hi).q_pos
        have hn : Nat.gcd i.q j.q ≠ 1 := hd.2
        omega
      simp only [hd, if_pos, hext, overlap, period_singleton, hg]
      rw [pairMass_eq_weight_gcd m i j (hmem i hi).q_pos (hmem j hj).q_pos hc]
      simp only [not_false_eq_true, true_and, ite_true]
      ring_nf
      exact le_rfl
    · have hz : Estimates.modularPairMass (modularEvent m i) (modularEvent m j) = 0 := by
        exact if_neg hc
      simp only [hd, if_pos, hz]
      positivity
  · simp only [hd, if_false]
    positivity

theorem dependencyMass_le_euler_loss
    {m : ℕ} {P : Params} {X : ℝ} {b : ℕ}
    (hm : 0 < m) (hX : Real.exp 2 ≤ X) (I : Finset FamilyIndex)
    (hmem : ∀ i ∈ I, StaticMem m P X (Estimates.roughModulus X) b i)
    (A : ℝ) (hA : 0 ≤ A)
    (htensor : ∀ D c : ℕ, 0 < D → Nat.Coprime D (Estimates.roughModulus X) →
      (D : ℝ) ≤ YScale P X →
      (∑ i ∈ I.filter (fun i => D ∣ i.dplus ∧ i.e % D = c),
        (1 : ℝ) / i.q) ≤ A / (D : ℝ) ^ 2) :
    Estimates.modularDependencyMass (modularEvents m I) ≤
      indexMass I * (A * (Real.exp (incrementFloorScale P X) - 1)) := by
  apply (dependencyMass_le_singleton_corrections I hmem).trans
  calc
    _ ≤ ∑ i ∈ I, (1 : ℝ) / i.q *
        (A * (Real.exp (incrementFloorScale P X) - 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa using correction_le_euler_loss hm hX I {i} hmem
        (Finset.singleton_subset_iff.mpr hi) A hA htensor
    _ = _ := by rw [indexMass, Finset.sum_mul]

/-- Lemma 6.9, second bound: for every `ε > 0`, eventually the dependency mass of
`I_b` is at most `ε μ_b`, for all reduced base classes `b`. -/
theorem modularDependencyMass_eventually_small
    (m : ℕ) (hm : 0 < m) (P : Params) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X in Filter.atTop, ∀ b : ℕ,
      Nat.Coprime b (Estimates.roughModulus X) →
      Estimates.modularDependencyMass
          (modularEvents m (indexFinset m P X (Estimates.roughModulus X) b)) ≤
        ε * indexMass (indexFinset m P X (Estimates.roughModulus X) b) := by
  obtain ⟨C, X₀, hC, hu⟩ := indexFinset_event_upper_log_cube m hm P
  have herr := singletonEulerMassError_tendsto_zero P
    (fun X => (Real.log X) ^ 3) C 1 hC.le (by norm_num)
    (by filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with X hX
        exact pow_nonneg (Real.log_nonneg hX) 3)
    (by filter_upwards [] with X; simp)
  have hsmall : ∀ᶠ X in Filter.atTop,
      (Real.log X) ^ 3 * C * (Real.exp (incrementFloorScale P X) - 1) < ε :=
    herr.eventually_lt_const hε
  filter_upwards [Filter.eventually_ge_atTop X₀,
    Filter.eventually_ge_atTop (Real.exp 2), hsmall] with X hX₀ hX hs
  intro b _hb
  have hX1 : 1 < X := (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hX
  let I := indexFinset m P X (Estimates.roughModulus X) b
  have hmem : ∀ i ∈ I, StaticMem m P X (Estimates.roughModulus X) b i := by
    intro i hi
    exact (mem_indexFinset_iff m P X _ b i (zero_lt_one.trans hX1)).mp hi
  have htensor : ∀ D c : ℕ, 0 < D → Nat.Coprime D (Estimates.roughModulus X) →
      (D : ℝ) ≤ YScale P X →
      (∑ i ∈ I.filter (fun i => D ∣ i.dplus ∧ i.e % D = c),
        (1 : ℝ) / i.q) ≤ (C * (Real.log X) ^ 3) / (D : ℝ) ^ 2 := by
    intro D c hD hc hDY
    exact (hu X hX₀ hX1 b D hD hc hDY).1 c
  have hA : 0 ≤ C * (Real.log X) ^ 3 :=
    mul_nonneg hC.le (pow_nonneg (Real.log_nonneg hX1.le) 3)
  exact (dependencyMass_le_euler_loss hm hX I hmem _ hA htensor).trans (by
    rw [mul_comm ε]
    apply mul_le_mul_of_nonneg_left _ (indexMass_nonneg I)
    nlinarith)

end ErdosStraus.FixedNumeratorFamily

/-! ## The increment `A(S)` -/

namespace ErdosStraus.FixedNumeratorFamily

open Classical Family Filter

theorem modularEvents_extensions_eq (m : ℕ) (I S : Finset FamilyIndex) :
    modularEvents m (extensions m I S) =
      ModularFamily.extensions (modularEvents m I) (modularEvents m S) := by
  ext event
  constructor
  · intro he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp
      (show event ∈ (extensions m I S).image (modularEvent m) from he)
    obtain ⟨hiI, hiS, hc⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨i, hiI, rfl⟩, ?_, ?_⟩
    · intro h
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
      exact hiS (modularEvent_injective m hji ▸ hj)
    · simpa only [Compatible, modularEvents, Finset.image_insert] using hc
  · intro he
    obtain ⟨hiI, hiS, hc⟩ := Finset.mem_filter.mp he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hiI
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_filter.mpr ⟨hi, ?_, ?_⟩, rfl⟩
    · intro hi'
      exact hiS (Finset.mem_image.mpr ⟨i, hi', rfl⟩)
    · simpa only [Compatible, modularEvents, Finset.image_insert] using hc

theorem modular_increment_eq (m : ℕ) (I S : Finset FamilyIndex) :
    (ModularFamily.increment (modularEvents m I) (modularEvents m S) : ℝ) =
      increment m I S := by
  unfold ModularFamily.increment
  rw [Rat.cast_sum, ← modularEvents_extensions_eq]
  unfold modularEvents
  rw [Finset.sum_image (fun i _ j _ h => modularEvent_injective m h)]
  simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  rfl

/-- Lemma 6.9, third bound: for fixed `K ≥ 0` and `ε > 0`, eventually
`A(S) ≤ (1 + ε) μ_b` for every compatible `S ⊆ I_b` with `|S| ≤ K μ_b`, for all
reduced base classes `b`. -/
theorem increment_eventually_le_one_add_mul_mass
    (m : ℕ) (hm : 0 < m) (P : Params)
    (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ b : ℕ, Nat.Coprime b (Estimates.roughModulus X) →
      let E := modularEvents m (indexFinset m P X (Estimates.roughModulus X) b)
      ∀ S ∈ E.powerset, ModularFamily.Compatible S →
        (S.card : ℝ) ≤ K * Estimates.modularMass E →
        (ModularFamily.increment E S : ℝ) ≤ (1 + ε) * Estimates.modularMass E := by
  obtain ⟨C, XT, hC, hT⟩ := event_upper_log_cube m hm P
  obtain ⟨c, XL, hc, hL⟩ := indexMass_lower m hm P
  obtain ⟨M, XM, hM, hU⟩ := indexFinset_mass_upper_log_cube m hm P
  have hs : Tendsto
      (fun X : ℝ => C * (Real.exp ((K * M) *
        ((Real.log X) ^ 3 * incrementFloorScale P X)) - 1)) atTop (nhds 0) := by
    have ht : Tendsto (fun X : ℝ => (K * M) *
        ((Real.log X) ^ 3 * incrementFloorScale P X)) atTop (nhds 0) := by
      simpa using (incrementFloorScale_logCube_tendsto_zero P).const_mul (K * M)
    have he := (((Real.continuous_exp.tendsto (0 : ℝ)).comp ht).sub_const 1).const_mul C
    simpa using he
  have hsmall : ∀ᶠ X : ℝ in atTop,
      C * (Real.exp ((K * M) *
        ((Real.log X) ^ 3 * incrementFloorScale P X)) - 1) ≤ ε * c := by
    filter_upwards [(tendsto_order.mp hs).2 (ε * c) (mul_pos hε hc)] with X hX
    exact hX.le
  filter_upwards [hsmall, eventually_ge_atTop XT, eventually_ge_atTop XL,
    eventually_ge_atTop XM, eventually_ge_atTop (Real.exp 2)] with X hsmall hXT hXL hXM hX
  intro b hb
  let I := indexFinset m P X (Estimates.roughModulus X) b
  let E := modularEvents m I
  change ∀ T ∈ E.powerset, ModularFamily.Compatible T →
    (T.card : ℝ) ≤ K * Estimates.modularMass E →
    (ModularFamily.increment E T : ℝ) ≤ (1 + ε) * Estimates.modularMass E
  intro T hTpow _hTcompat hTcard
  have hTI : T ⊆ E := Finset.mem_powerset.mp hTpow
  let S := I.filter (fun i => modularEvent m i ∈ T)
  have hSI : S ⊆ I := Finset.filter_subset _ _
  have himage : modularEvents m S = T := by
    ext event
    constructor
    · intro he
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
      exact (Finset.mem_filter.mp hi).2
    · intro he
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hTI he)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, he⟩, rfl⟩
  have hScard : S.card = T.card := by
    rw [← himage]
    exact (Finset.card_image_of_injective S (modularEvent_injective m)).symm
  have hX1 : 1 < X := (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hX
  have hlog : 0 ≤ Real.log X := (Real.log_pos hX1).le
  have hmem : ∀ i ∈ I, StaticMem m P X (Estimates.roughModulus X) b i := by
    intro i hi
    exact (mem_indexFinset_iff m P X _ b i (zero_lt_one.trans hX1)).mp hi
  have hmassL : c * (Real.log X) ^ 3 ≤ indexMass I := hL X hXL hX1 b hb
  have hmassU : indexMass I ≤ M * (Real.log X) ^ 3 := hU X hXM hX1 b
  have hcard : (S.card : ℝ) ≤ K * indexMass I := by
    simpa only [hScard, E, modularMass_eq_indexMass] using hTcard
  have hscale := incrementFloorScale_nonneg P hX
  have hexp : Real.exp ((S.card : ℝ) * incrementFloorScale P X) - 1 ≤
      Real.exp ((K * M) * ((Real.log X) ^ 3 * incrementFloorScale P X)) - 1 := by
    apply sub_le_sub_right (Real.exp_le_exp.mpr ?_) 1
    calc
      _ ≤ (K * indexMass I) * incrementFloorScale P X :=
        mul_le_mul_of_nonneg_right hcard hscale
      _ ≤ (K * (M * (Real.log X) ^ 3)) * incrementFloorScale P X :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmassU hK) hscale
      _ = _ := by ring
  have hcor := correction_le_euler_loss hm hX I S hmem hSI
    (C * (Real.log X) ^ 3) (by positivity) (by
      intro D c hD hcop hDY
      exact (hT X hXT hX1 b I hmem D hD hcop hDY).1 c)
  have hcormass : correction m I S ≤ ε * indexMass I := by
    apply hcor.trans
    calc
      _ ≤ (C * (Real.log X) ^ 3) *
          (Real.exp ((K * M) * ((Real.log X) ^ 3 * incrementFloorScale P X)) - 1) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (Real.log X) ^ 3 *
          (C * (Real.exp ((K * M) * ((Real.log X) ^ 3 *
            incrementFloorScale P X)) - 1)) := by ring
      _ ≤ (Real.log X) ^ 3 * (ε * c) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = ε * (c * (Real.log X) ^ 3) := by ring
      _ ≤ ε * indexMass I := mul_le_mul_of_nonneg_left hmassL hε.le
  change (ModularFamily.increment (modularEvents m I) T : ℝ) ≤
    (1 + ε) * Estimates.modularMass (modularEvents m I)
  rw [← himage, modular_increment_eq, modularMass_eq_indexMass]
  exact (increment_le_mass_add_correction m I S).trans (by linarith)

/-- The case `K = 26`, `ε = 1`: `A(S) ≤ 2 μ_b` whenever `|S| ≤ 26 μ_b`, the hypothesis of
Section 5 with `K = 13`. -/
theorem increment_eventually_le_two_mass
    (m : ℕ) (hm : 0 < m) (P : Params) :
    ∀ᶠ X : ℝ in atTop, ∀ b : ℕ, Nat.Coprime b (Estimates.roughModulus X) →
      let E := modularEvents m (indexFinset m P X (Estimates.roughModulus X) b)
      ∀ S ∈ E.powerset, ModularFamily.Compatible S →
        (S.card : ℝ) ≤ 26 * Estimates.modularMass E →
        (ModularFamily.increment E S : ℝ) ≤ 2 * Estimates.modularMass E := by
  simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using
    increment_eventually_le_one_add_mul_mass m hm P 26 1 (by norm_num) (by norm_num)

end ErdosStraus.FixedNumeratorFamily
