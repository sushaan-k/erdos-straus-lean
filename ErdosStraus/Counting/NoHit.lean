import ErdosStraus.Counting.BinomialMoments
import ErdosStraus.Estimates.BrunHooley

/-!
# Theorem 5.2: probability of no event

For a finite family of congruence events, counted over a common period, the proportion of
residues lying in no event is at most `exp(-μ + Δ/(1-2δ))` when `δ ≤ 1/4`, and hence at
most `exp(-μ + 2Δ)`. Here `μ` is the total mass, `δ` bounds every neighbourhood mass and
`Δ` is the sum of `P(A_i ∩ A_j)` over unordered dependent pairs. The proof is the
conditioning argument of Theorem 5.2, with probabilities replaced by counts.
-/

namespace ErdosStraus.Conditioning

open Classical
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]

/-! ## Independence of events with coprime moduli -/

/-- The number of `n ∈ A` lying in every event of `H` and in no event of `S`. -/
noncomputable def mixedCount (A : Finset α) (hit : ι → α → Prop)
    (H S : Finset ι) : ℝ :=
  ((A.filter (fun n => (∀ i ∈ H, hit i n) ∧ ∀ j ∈ S, ¬hit j n)).card : ℝ)

omit [DecidableEq α] [DecidableEq ι] in
theorem mixedCount_empty (A : Finset α) (hit : ι → α → Prop) (H : Finset ι) :
    mixedCount A hit H ∅ = RoughEstimates.intersectionCount A hit H := by
  simp [mixedCount, RoughEstimates.intersectionCount]

omit [DecidableEq α] in
theorem mixedCount_partition (A : Finset α) (hit : ι → α → Prop)
    (H S : Finset ι) (j : ι) :
    mixedCount A hit H S =
      mixedCount A hit H (insert j S) + mixedCount A hit (insert j H) S := by
  let F := A.filter (fun n => (∀ i ∈ H, hit i n) ∧ ∀ k ∈ S, ¬hit k n)
  have hcard := Finset.card_filter_add_card_filter_not (s := F) (p := fun n => hit j n)
  have hyes : F.filter (fun n => hit j n) =
      A.filter (fun n => (∀ i ∈ insert j H, hit i n) ∧ ∀ k ∈ S, ¬hit k n) := by
    ext n
    simp only [F, Finset.mem_filter, Finset.forall_mem_insert]
    tauto
  have hno : F.filter (fun n => ¬hit j n) =
      A.filter (fun n => (∀ i ∈ H, hit i n) ∧ ∀ k ∈ insert j S, ¬hit k n) := by
    ext n
    simp only [F, Finset.mem_filter, Finset.forall_mem_insert]
    tauto
  rw [hyes, hno] at hcard
  unfold mixedCount
  exact_mod_cast hcard.symm.trans (Nat.add_comm _ _)

omit [DecidableEq α] in
theorem mixedCount_factor_of_intersections (A : Finset α) (hit : ι → α → Prop)
    (S H K : Finset ι) (c : ℝ)
    (hfactor : ∀ U ⊆ S,
      RoughEstimates.intersectionCount A hit (H ∪ U) =
        c * RoughEstimates.intersectionCount A hit (K ∪ U)) :
    mixedCount A hit H S = c * mixedCount A hit K S := by
  induction S using Finset.induction_on generalizing H K with
  | empty =>
    simpa only [mixedCount_empty, Finset.union_empty] using hfactor ∅ (by simp)
  | @insert j S hj ih =>
    have hbase : mixedCount A hit H S = c * mixedCount A hit K S :=
      ih H K (fun U hU => hfactor U (hU.trans (Finset.subset_insert _ _)))
    have hhit : mixedCount A hit (insert j H) S = c * mixedCount A hit (insert j K) S := by
      apply ih
      intro U hU
      have h := hfactor (insert j U) (Finset.insert_subset_insert j hU)
      simpa only [Finset.union_insert, Finset.insert_union] using h
    have hleft := mixedCount_partition A hit H S j
    have hright := mixedCount_partition A hit K S j
    calc
      _ = mixedCount A hit H S - mixedCount A hit (insert j H) S :=
        (eq_sub_iff_add_eq).mpr hleft.symm
      _ = _ := by rw [hbase, hhit, hright]; ring

open ModularFamily ErdosStraus.Arithmetic

theorem period_union (H U : Finset Event) :
    period (H ∪ U) = Nat.lcm (period H) (period U) := by
  apply Nat.dvd_antisymm
  · apply congruenceLcm_dvd_of_forall_modulus_dvd
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    have hi' : i ∈ H ∪ U := by simpa using hi
    rcases Finset.mem_union.mp hi' with hiH | hiU
    · exact (modulus_dvd_period hiH).trans (Nat.dvd_lcm_left _ _)
    · exact (modulus_dvd_period hiU).trans (Nat.dvd_lcm_right _ _)
  · exact Nat.lcm_dvd (period_dvd_of_subset Finset.subset_union_left)
      (period_dvd_of_subset Finset.subset_union_right)

theorem period_coprime_of_cross (H U : Finset Event)
    (hH : ∀ i ∈ H, 0 < i.modulus) (hU : ∀ j ∈ U, 0 < j.modulus)
    (hcross : ∀ i ∈ H, ∀ j ∈ U, Nat.Coprime i.modulus j.modulus) :
    Nat.Coprime (period H) (period U) := by
  apply Nat.Coprime.symm
  apply base_coprime_period H (period_pos U hU) hH
  intro i hi
  exact (base_coprime_period U (hH i hi) hU (hcross i hi)).symm

theorem compatible_union_of_cross (H U : Finset Event)
    (hcross : ∀ i ∈ H, ∀ j ∈ U, Nat.Coprime i.modulus j.modulus) :
    Compatible (H ∪ U) ↔ Compatible H ∧ Compatible U := by
  constructor
  · intro h
    exact ⟨fun i hi j hj => h i (Finset.mem_union_left _ hi) j
      (Finset.mem_union_left _ hj), fun i hi j hj => h i (Finset.mem_union_right _ hi) j
        (Finset.mem_union_right _ hj)⟩
  · rintro ⟨hH, hU⟩ i hi j hj
    rcases Finset.mem_union.mp hi with hiH | hiU <;>
      rcases Finset.mem_union.mp hj with hjH | hjU
    · exact hH i hiH j hjH
    · simp [residueCompatible, (hcross i hiH j hjU).gcd_eq_one, Nat.ModEq, Nat.mod_one]
    · simp [residueCompatible, (hcross j hjH i hiU).symm.gcd_eq_one, Nat.ModEq, Nat.mod_one]
    · exact hU i hiU j hjU

/-- The density `1/L_H` of the common solutions of the congruences in `H`, or `0` when
`H` is incompatible. -/
noncomputable def commonDensity (H : Finset Event) : ℝ :=
  if Compatible H then (weight H : ℝ) else 0

theorem commonDensity_union_of_cross (H U : Finset Event)
    (hH : ∀ i ∈ H, 0 < i.modulus) (hU : ∀ j ∈ U, 0 < j.modulus)
    (hcross : ∀ i ∈ H, ∀ j ∈ U, Nat.Coprime i.modulus j.modulus) :
    commonDensity (H ∪ U) = commonDensity H * commonDensity U := by
  rw [commonDensity, compatible_union_of_cross H U hcross]
  by_cases hHC : Compatible H <;> by_cases hUC : Compatible U
  · simp only [hHC, hUC, and_self, if_true, commonDensity]
    rw [weight, weight, weight, period_union,
      (period_coprime_of_cross H U hH hU hcross).lcm_eq_mul]
    push_cast
    ring
  · simp [hHC, hUC, commonDensity]
  · simp [hHC, hUC, commonDensity]
  · simp [hHC, hUC, commonDensity]

theorem intersectionCount_eq_period_mul_density (E H : Finset Event)
    (hE : ∀ i ∈ E, 0 < i.modulus) (hHE : H ⊆ E) :
    RoughEstimates.intersectionCount (Finset.range (period E)) (fun i n => i.Hits n) H =
      (period E : ℝ) * commonDensity H := by
  by_cases hC : Compatible H
  · have hcount := subset_common_period_count E H hE hHE hC
    have hcountR : RoughEstimates.intersectionCount (Finset.range (period E))
        (fun i n => i.Hits n) H =
          (period E : ℝ) / period H := by
      have hR := congrArg (fun n : ℕ => (n : ℝ)) hcount
      have he : RoughEstimates.intersectionCount (Finset.range (period E))
          (fun i n => i.Hits n) H =
            (eventSubsetCommonHitCount (Finset.range (period E)) (fun n i => i.Hits n) H : ℝ) := by
        unfold RoughEstimates.intersectionCount eventSubsetCommonHitCount
        congr 2; ext n; simp only [Finset.mem_filter]
      rw [he]
      have hpH : (period H : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (period_pos H (fun i hi => hE i (hHE hi))).ne'
      rw [Nat.cast_div (period_dvd_of_subset hHE) hpH] at hR
      exact hR
    rw [hcountR]
    simp [commonDensity, hC, weight, div_eq_mul_inv]
  · have hzero : RoughEstimates.intersectionCount (Finset.range (period E))
        (fun i n => i.Hits n) H = 0 := by
      unfold RoughEstimates.intersectionCount
      simp only [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro n _ hn
      exact hC (compatible_of_common_hit hn)
    rw [hzero]
    simp [commonDensity, hC]

/-- Events of `H` whose moduli are coprime to those of `S` are independent of the events
of `S`. -/
theorem mixedCount_independent_of_coprime_complement (E H S : Finset Event)
    (hE : ∀ i ∈ E, 0 < i.modulus) (hHE : H ⊆ E) (hSE : S ⊆ E)
    (hcross : ∀ i ∈ H, ∀ j ∈ S, Nat.Coprime i.modulus j.modulus) :
    mixedCount (Finset.range (period E)) (fun i n => i.Hits n) H S =
      commonDensity H * mixedCount (Finset.range (period E)) (fun i n => i.Hits n) ∅ S := by
  apply mixedCount_factor_of_intersections
  intro U hUS
  rw [Finset.empty_union, intersectionCount_eq_period_mul_density E (H ∪ U) hE
    (Finset.union_subset hHE (hUS.trans hSE)),
    intersectionCount_eq_period_mul_density E U hE (hUS.trans hSE),
    commonDensity_union_of_cross H U (fun i hi => hE i (hHE hi))
      (fun i hi => hE i (hSE (hUS hi)))
      (fun i hi j hj => hcross i hi j (hUS hj))]
  ring

theorem period_singleton (i : Event) : period {i} = i.modulus := by
  rw [show ({i} : Finset Event) = insert i ∅ by simp, period_insert]
  simp [period, rows, congruenceLcm]

theorem period_pair (i j : Event) : period {i, j} = Nat.lcm i.modulus j.modulus := by
  rw [period_insert, period_singleton]

theorem compatible_pair (i j : Event) :
    Compatible {i, j} ↔ i.residue ≡ j.residue [MOD Nat.gcd i.modulus j.modulus] := by
  constructor
  · intro h
    exact h i (Finset.mem_insert_self _ _) j (by simp)
  · intro h x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Nat.ModEq.refl _
    · exact h
    · simpa only [residueCompatible, Nat.gcd_comm] using h.symm
    · exact Nat.ModEq.refl _

theorem commonDensity_pair (i j : Event) :
    commonDensity {i, j} = Estimates.modularPairMass i j := by
  unfold commonDensity Estimates.modularPairMass
  rw [compatible_pair]
  split_ifs <;> simp [weight, period_pair]

end ErdosStraus.Conditioning

/-! ## The conditioning argument -/

namespace ErdosStraus.Conditioning

open Classical ModularFamily
open scoped BigOperators

section Counting

variable {α ι : Type*} [DecidableEq ι] (A : Finset α) (hit : ι → α → Prop)

omit [DecidableEq ι] in
theorem mixedCount_nonneg (H S : Finset ι) : 0 ≤ mixedCount A hit H S :=
  Nat.cast_nonneg _

omit [DecidableEq ι] in
theorem mixedCount_anti {H S T : Finset ι} (hTS : T ⊆ S) :
    mixedCount A hit H S ≤ mixedCount A hit H T := by
  unfold mixedCount
  refine Nat.cast_le.mpr (Finset.card_le_card (fun n hn => ?_))
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.1, fun j hj => hn.2.2 j (hTS hj)⟩

/-- The union bound for the elements that avoid `T` but hit some event of `D`. -/
theorem mixedCount_sub_union_le (H T D : Finset ι) :
    mixedCount A hit H T - mixedCount A hit H (T ∪ D) ≤
      ∑ j ∈ D, mixedCount A hit (insert j H) T := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert j D hj ih =>
    rw [Finset.sum_insert hj, Finset.union_insert,
      mixedCount_partition A hit H (T ∪ D) j] at *
    have hmono := mixedCount_anti A hit (H := insert j H) (Finset.subset_union_left (s₁ := T) (s₂ := D))
    linarith [mixedCount_partition A hit H (T ∪ D) j]

end Counting

/-- The number of `0 ≤ n < L_E` lying in every event of `H` and in no event of `S`. -/
noncomputable abbrev periodCount (E H S : Finset Event) : ℝ :=
  mixedCount (Finset.range (period E)) (fun i n => i.Hits n) H S

theorem commonDensity_singleton (i : Event) :
    commonDensity {i} = Estimates.modularEventMass i := by
  have hC : Compatible {i} := by
    intro x hx y hy
    rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy]
    exact Nat.ModEq.refl _
  simp [commonDensity, hC, weight, period_singleton, Estimates.modularEventMass]

theorem modularPairMass_comm (i j : Event) :
    Estimates.modularPairMass i j = Estimates.modularPairMass j i := by
  unfold Estimates.modularPairMass
  rw [Nat.gcd_comm, Nat.lcm_comm]
  by_cases h : i.residue ≡ j.residue [MOD Nat.gcd j.modulus i.modulus]
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

theorem modularPairMass_nonneg (i j : Event) : 0 ≤ Estimates.modularPairMass i j := by
  unfold Estimates.modularPairMass
  split_ifs <;> positivity

theorem modularDependent_comm {i j : Event} :
    Estimates.modularDependent i j ↔ Estimates.modularDependent j i := by
  unfold Estimates.modularDependent
  rw [Nat.coprime_comm, ne_comm]

theorem coprime_of_not_dependent {i j : Event} (hij : i ≠ j)
    (h : ¬Estimates.modularDependent i j) : Nat.Coprime i.modulus j.modulus := by
  by_contra hc
  exact h ⟨hij, hc⟩

section Model

variable (E : Finset Event) (hpos : ∀ i ∈ E, 0 < i.modulus)
include hpos

theorem periodCount_hit_eq {i : Event} (hi : i ∈ E) {S : Finset Event} (hS : S ⊆ E)
    (hcross : ∀ j ∈ S, Nat.Coprime i.modulus j.modulus) :
    periodCount E {i} S = Estimates.modularEventMass i * periodCount E ∅ S := by
  rw [periodCount, mixedCount_independent_of_coprime_complement E {i} S hpos
    (Finset.singleton_subset_iff.mpr hi) hS
    (fun x hx j hj => (Finset.mem_singleton.mp hx) ▸ hcross j hj),
    commonDensity_singleton]

theorem periodCount_pair_eq {i j : Event} (hi : i ∈ E) (hj : j ∈ E)
    {S : Finset Event} (hS : S ⊆ E)
    (hcross : ∀ k ∈ S, Nat.Coprime i.modulus k.modulus ∧
      Nat.Coprime j.modulus k.modulus) :
    periodCount E {i, j} S = Estimates.modularPairMass i j * periodCount E ∅ S := by
  rw [periodCount, mixedCount_independent_of_coprime_complement E {i, j} S hpos
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption) hS, commonDensity_pair]
  intro x hx k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact (hcross k hk).1
  · exact (hcross k hk).2

omit hpos in
theorem periodCount_empty_empty :
    periodCount E ∅ ∅ = period E := by
  simp [periodCount, mixedCount]

variable (δ : ℝ) (hδ : ∀ i ∈ E, Estimates.modularNeighbourMass E i ≤ δ) (hδ4 : δ ≤ 1 / 4)
include hδ hδ4

omit hpos hδ4 in
theorem dependent_mass_le {i : Event} (hi : i ∈ E) {D : Finset Event}
    (hD : D ⊆ E.filter (Estimates.modularDependent i)) :
    ∑ j ∈ D, Estimates.modularEventMass j ≤ δ :=
  (Finset.sum_le_sum_of_subset_of_nonneg hD
    (fun j _ _ => Estimates.modularEventMass_nonneg j)).trans (hδ i hi)

/-- `P(A_i | B_S) ≤ 2/q_i` for `i ∉ S`, where `B_S` is the set of residues lying in
no event of `S`. -/
theorem hit_le_two_mass :
    ∀ S ⊆ E, ∀ i ∈ E, i ∉ S →
      periodCount E {i} S ≤ 2 * Estimates.modularEventMass i * periodCount E ∅ S := by
  intro S
  induction' hn : S.card using Nat.strong_induction_on with n ih generalizing S
  intro hS i hi hiS
  set D := S.filter (Estimates.modularDependent i)
  set T := S.filter (fun j => ¬Estimates.modularDependent i j)
  have hTS : T ⊆ S := Finset.filter_subset _ _
  have hunion : T ∪ D = S := by
    rw [Finset.union_comm]; exact Finset.filter_union_filter_not_eq _ _
  have hcrossT : ∀ j ∈ T, Nat.Coprime i.modulus j.modulus := by
    intro j hj
    obtain ⟨hjS, hnd⟩ := Finset.mem_filter.mp hj
    exact coprime_of_not_dependent (fun h => hiS (h ▸ hjS)) hnd
  have hw := Estimates.modularEventMass_nonneg i
  have hstep : periodCount E {i} S ≤ Estimates.modularEventMass i * periodCount E ∅ T := by
    rw [← periodCount_hit_eq E hpos hi (hTS.trans hS) hcrossT]
    exact mixedCount_anti _ _ hTS
  have hT2 : periodCount E ∅ T ≤ 2 * periodCount E ∅ S := by
    by_cases hDe : D = ∅
    · have : T = S := by rw [← hunion, hDe, Finset.union_empty]
      rw [this]; linarith [mixedCount_nonneg (Finset.range (period E))
        (fun i n => i.Hits n) ∅ S]
    · have hlt : T.card < n := by
        rw [← hn]
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hTS, fun hTeq => hDe ?_⟩
        apply Finset.eq_empty_of_forall_notMem
        intro j hj
        have hjT : j ∈ T := hTeq ▸ (Finset.mem_filter.mp hj).1
        exact (Finset.mem_filter.mp hjT).2 (Finset.mem_filter.mp hj).2
      have hbound := mixedCount_sub_union_le (Finset.range (period E))
        (fun i n => i.Hits n) ∅ T D
      rw [hunion] at hbound
      have hterm : ∀ j ∈ D, periodCount E (insert j ∅) T ≤
          2 * Estimates.modularEventMass j * periodCount E ∅ T := by
        intro j hj
        have hjS := (Finset.mem_filter.mp hj).1
        exact ih T.card hlt T rfl (hTS.trans hS) j (hS hjS)
          (fun hjT => (Finset.mem_filter.mp hjT).2 (Finset.mem_filter.mp hj).2)
      have hsum := Finset.sum_le_sum hterm
      rw [← Finset.sum_mul, ← Finset.mul_sum] at hsum
      have hmass := dependent_mass_le E δ hδ hi
        (D := D) (Finset.filter_subset_filter _ hS)
      have hT0 := mixedCount_nonneg (Finset.range (period E)) (fun i n => i.Hits n) ∅ T
      have : 2 * (∑ j ∈ D, Estimates.modularEventMass j) * periodCount E ∅ T ≤
          1 / 2 * periodCount E ∅ T := by
        apply mul_le_mul_of_nonneg_right _ hT0; linarith
      change periodCount E ∅ T - periodCount E ∅ S ≤
        ∑ j ∈ D, periodCount E (insert j ∅) T at hbound
      linarith
  calc periodCount E {i} S ≤ Estimates.modularEventMass i * periodCount E ∅ T := hstep
    _ ≤ Estimates.modularEventMass i * (2 * periodCount E ∅ S) :=
      mul_le_mul_of_nonneg_left hT2 hw
    _ = _ := by ring

/-- `P(B_D | B_T) ≥ 1 - 2δ` when the events of `D` have total mass at most `δ`. -/
theorem avoid_union_ge {T D : Finset Event} (hT : T ⊆ E) (hD : D ⊆ E)
    (hdisj : Disjoint T D) (hmass : ∑ j ∈ D, Estimates.modularEventMass j ≤ δ) :
    (1 - 2 * δ) * periodCount E ∅ T ≤ periodCount E ∅ (T ∪ D) := by
  have hbound := mixedCount_sub_union_le (Finset.range (period E))
    (fun i n => i.Hits n) ∅ T D
  have hterm : ∀ j ∈ D, periodCount E (insert j ∅) T ≤
      2 * Estimates.modularEventMass j * periodCount E ∅ T := fun j hj =>
    hit_le_two_mass E hpos δ hδ hδ4 T hT j (hD hj)
      (fun hjT => Finset.disjoint_left.mp hdisj hjT hj)
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul, ← Finset.mul_sum] at hsum
  have hT0 := mixedCount_nonneg (Finset.range (period E)) (fun i n => i.Hits n) ∅ T
  change periodCount E ∅ T - periodCount E ∅ (T ∪ D) ≤
    ∑ j ∈ D, periodCount E (insert j ∅) T at hbound
  nlinarith [mul_le_mul_of_nonneg_right hmass hT0]

/-- `P(A_i | B_S) ≥ 1/q_i - (1-2δ)⁻¹ ∑_{j ∈ S, j ∼ i} P(A_i ∩ A_j)` for `i ∉ S`. -/
theorem hit_ge_mass_sub_pairs (S : Finset Event) (hS : S ⊆ E) {i : Event} (hi : i ∈ E)
    (hiS : i ∉ S) :
    periodCount E ∅ S * (Estimates.modularEventMass i - (1 - 2 * δ)⁻¹ *
      ∑ j ∈ S.filter (Estimates.modularDependent i), Estimates.modularPairMass i j) ≤
      periodCount E {i} S := by
  set D := S.filter (Estimates.modularDependent i)
  set T := S.filter (fun j => ¬Estimates.modularDependent i j)
  have hTS : T ⊆ S := Finset.filter_subset _ _
  have hunion : T ∪ D = S := by
    rw [Finset.union_comm]; exact Finset.filter_union_filter_not_eq _ _
  have hcrossT : ∀ j ∈ T, Nat.Coprime i.modulus j.modulus := by
    intro j hj
    obtain ⟨hjS, hnd⟩ := Finset.mem_filter.mp hj
    exact coprime_of_not_dependent (fun h => hiS (h ▸ hjS)) hnd
  have hc : 0 < 1 - 2 * δ := by linarith
  set c := (1 - 2 * δ)⁻¹
  have hpair : ∀ j ∈ D, periodCount E (insert j {i}) T ≤
      Estimates.modularPairMass i j * (c * periodCount E ∅ T) := by
    intro j hj
    obtain ⟨hjS, hdep⟩ := Finset.mem_filter.mp hj
    have hjT : j ∉ T := fun hjT => (Finset.mem_filter.mp hjT).2 hdep
    set Ej := T.filter (Estimates.modularDependent j)
    set T0 := T.filter (fun k => ¬Estimates.modularDependent j k)
    have hT0T : T0 ⊆ T := Finset.filter_subset _ _
    have hcross0 : ∀ k ∈ T0, Nat.Coprime j.modulus k.modulus ∧
        Nat.Coprime i.modulus k.modulus := by
      intro k hk
      obtain ⟨hkT, hnd⟩ := Finset.mem_filter.mp hk
      exact ⟨coprime_of_not_dependent (fun h => hjT (h ▸ hkT)) hnd, hcrossT k hkT⟩
    have hle : periodCount E (insert j {i}) T ≤
        Estimates.modularPairMass i j * periodCount E ∅ T0 := by
      calc periodCount E (insert j {i}) T ≤ periodCount E (insert j {i}) T0 :=
            mixedCount_anti _ _ hT0T
        _ = Estimates.modularPairMass j i * periodCount E ∅ T0 :=
            periodCount_pair_eq E hpos (hS hjS) hi (hT0T.trans (hTS.trans hS)) hcross0
        _ = _ := by rw [modularPairMass_comm]
    have hunion0 : T0 ∪ Ej = T := by
      rw [Finset.union_comm]; exact Finset.filter_union_filter_not_eq _ _
    have hge := avoid_union_ge E hpos δ hδ hδ4 (T := T0) (D := Ej)
      (hT0T.trans (hTS.trans hS)) ((Finset.filter_subset _ _).trans (hTS.trans hS))
      (Finset.disjoint_filter_filter_not _ _ _ |>.symm)
      (dependent_mass_le E δ hδ (hS hjS)
        (Finset.filter_subset_filter _ (hTS.trans hS)))
    rw [hunion0] at hge
    have hT0c : periodCount E ∅ T0 ≤ c * periodCount E ∅ T := by
      rw [show c * periodCount E ∅ T = periodCount E ∅ T / (1 - 2 * δ) by
        simp only [c]; ring]
      exact (le_div_iff₀ hc).mpr (by linarith)
    exact hle.trans (mul_le_mul_of_nonneg_left hT0c (modularPairMass_nonneg i j))
  have hbound := mixedCount_sub_union_le (Finset.range (period E))
    (fun i n => i.Hits n) {i} T D
  rw [hunion] at hbound
  change periodCount E {i} T - periodCount E {i} S ≤
    ∑ j ∈ D, periodCount E (insert j {i}) T at hbound
  have hsum := Finset.sum_le_sum hpair
  rw [← Finset.sum_mul] at hsum
  have hhitT := periodCount_hit_eq E hpos hi (hTS.trans hS) hcrossT
  have hlower : periodCount E ∅ T *
      (Estimates.modularEventMass i - c * ∑ j ∈ D, Estimates.modularPairMass i j) ≤
      periodCount E {i} S := by
    nlinarith
  have hST : periodCount E ∅ S ≤ periodCount E ∅ T := mixedCount_anti _ _ hTS
  by_cases hx : 0 ≤ Estimates.modularEventMass i - c * ∑ j ∈ D, Estimates.modularPairMass i j
  · exact (mul_le_mul_of_nonneg_right hST hx).trans hlower
  · push Not at hx
    exact (mul_nonpos_of_nonneg_of_nonpos (mixedCount_nonneg _ _ _ _) hx.le).trans
      (mixedCount_nonneg _ _ _ _)

omit hpos hδ hδ4 in
theorem dependencyMass_insert {a : Event} {S : Finset Event} (ha : a ∉ S) :
    Estimates.modularDependencyMass (insert a S) =
      Estimates.modularDependencyMass S +
        2 * ∑ j ∈ S.filter (Estimates.modularDependent a), Estimates.modularPairMass a j := by
  unfold Estimates.modularDependencyMass
  have hself : ¬Estimates.modularDependent a a := fun h => h.1 rfl
  rw [Finset.sum_insert ha, Finset.filter_insert, if_neg hself]
  have hrest : ∀ b ∈ S,
      (∑ j ∈ (insert a S).filter (Estimates.modularDependent b), Estimates.modularPairMass b j) =
        (∑ j ∈ S.filter (Estimates.modularDependent b), Estimates.modularPairMass b j) +
          if Estimates.modularDependent b a then Estimates.modularPairMass b a else 0 := by
    intro b hb
    rw [Finset.filter_insert]
    split_ifs with hba
    · rw [Finset.sum_insert (fun h => ha (Finset.mem_filter.mp h).1)]; ring
    · simp
  rw [Finset.sum_congr rfl hrest, Finset.sum_add_distrib, ← Finset.sum_filter]
  have hswap : (∑ b ∈ S.filter (fun b => Estimates.modularDependent b a),
      Estimates.modularPairMass b a) =
      ∑ j ∈ S.filter (Estimates.modularDependent a), Estimates.modularPairMass a j := by
    apply Finset.sum_congr
    · ext b; simp only [Finset.mem_filter, modularDependent_comm (i := b)]
    · intro b _; exact modularPairMass_comm b a
  rw [hswap]; ring

omit hpos hδ hδ4 in
theorem modularMass_insert {a : Event} {S : Finset Event} (ha : a ∉ S) :
    Estimates.modularMass (insert a S) = Estimates.modularMass S + Estimates.modularEventMass a := by
  unfold Estimates.modularMass; rw [Finset.sum_insert ha]; ring

/-- The chain rule: for `S ⊆ E`, the number of residues in one period lying in no event
of `S` is at most `L_E exp(-μ_S + Δ_S/(1-2δ))`, where `2Δ_S = modularDependencyMass S`. -/
theorem avoid_le_exp (S : Finset Event) (hS : S ⊆ E) :
    periodCount E ∅ S ≤ period E * Real.exp (-Estimates.modularMass S +
      (1 - 2 * δ)⁻¹ * (Estimates.modularDependencyMass S / 2)) := by
  induction S using Finset.induction_on with
  | empty =>
    simp [periodCount_empty_empty, Estimates.modularMass, Estimates.modularDependencyMass]
  | @insert a S ha ih =>
    have hSE : S ⊆ E := (Finset.subset_insert a S).trans hS
    have haE : a ∈ E := hS (Finset.mem_insert_self a S)
    have hpart := mixedCount_partition (Finset.range (period E)) (fun i n => i.Hits n) ∅ S a
    change periodCount E ∅ S = periodCount E ∅ (insert a S) + periodCount E {a} S at hpart
    have hlow := hit_ge_mass_sub_pairs E hpos δ hδ hδ4 S hSE haE ha
    set x := Estimates.modularEventMass a - (1 - 2 * δ)⁻¹ *
      ∑ j ∈ S.filter (Estimates.modularDependent a), Estimates.modularPairMass a j
    have hS0 := mixedCount_nonneg (Finset.range (period E)) (fun i n => i.Hits n) ∅ S
    have hstep : periodCount E ∅ (insert a S) ≤ periodCount E ∅ S * Real.exp (-x) := by
      have := mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (-x)] :
        1 - x ≤ Real.exp (-x)) hS0
      nlinarith
    calc periodCount E ∅ (insert a S) ≤ periodCount E ∅ S * Real.exp (-x) := hstep
      _ ≤ period E * Real.exp (-Estimates.modularMass S +
            (1 - 2 * δ)⁻¹ * (Estimates.modularDependencyMass S / 2)) * Real.exp (-x) :=
          mul_le_mul_of_nonneg_right (ih hSE) (Real.exp_pos _).le
      _ = _ := by
          rw [mul_assoc, ← Real.exp_add, modularMass_insert ha, dependencyMass_insert ha]
          congr 2
          simp only [x]; ring

end Model

theorem noHitProbability_period_eq_periodCount (E : Finset Event) :
    Estimates.modularNoHitProbability (period E) E = periodCount E ∅ E / period E := by
  unfold Estimates.modularNoHitProbability periodCount mixedCount
  congr 3
  ext n; simp

/-- Counting over any common period gives the same proportion as counting over `L_E`. -/
theorem noHitProbability_eq_period (L : ℕ) (E : Finset Event) (hL : 0 < L)
    (hperiod : ∀ i ∈ E, 0 < i.modulus ∧ i.modulus ∣ L) :
    Estimates.modularNoHitProbability L E = Estimates.modularNoHitProbability (period E) E := by
  set P := period E
  have hP : 0 < P := period_pos E (fun i hi => (hperiod i hi).1)
  have hPL : P ∣ L := ErdosStraus.Arithmetic.congruenceLcm_dvd_of_forall_modulus_dvd _ _ (by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact (hperiod i (by simpa using hi)).2)
  obtain ⟨k, rfl⟩ := hPL
  let p : ℕ → Prop := fun n => ∀ event ∈ E, ¬event.Hits n
  have hper : Function.Periodic p P := by
    intro n
    apply propext
    refine forall₂_congr (fun i hi => ?_)
    have hshift : n + P ≡ n [MOD i.modulus] :=
      ((Nat.modEq_iff_dvd' (Nat.le_add_right n P)).mpr
        (by simpa using modulus_dvd_period hi)).symm
    simp only [Estimates.ModularEvent.Hits]
    exact not_congr ⟨fun h => hshift.symm.trans h, fun h => hshift.trans h⟩
  have hcount : ∀ k : ℕ, ((Finset.range (P * k)).filter p).card =
      k * ((Finset.range P).filter p).card := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, Finset.range_eq_Ico, ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _)
        (Nat.le_add_right _ _), Finset.filter_union, Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
        ← Finset.range_eq_Ico, ih, Nat.filter_Ico_card_eq_of_periodic _ _ p hper,
        Nat.count_eq_card_filter_range]
      ring
  unfold Estimates.modularNoHitProbability
  have hk : 0 < k := Nat.pos_of_mul_pos_left hL
  rw [hcount k]
  push_cast
  field_simp
  ring

/-- Theorem 5.2 for one family: if every neighbourhood mass is at most `δ ≤ 1/4`, then
over any common period `L` the proportion of residues lying in no event is at most
`exp(-μ + Δ/(1-2δ))`, where `2Δ = modularDependencyMass E`. -/
theorem noHit_le_exp_conditioning (L : ℕ) (E : Finset Event) (δ : ℝ) (hL : 0 < L)
    (hperiod : ∀ i ∈ E, 0 < i.modulus ∧ i.modulus ∣ L)
    (hδ : ∀ i ∈ E, Estimates.modularNeighbourMass E i ≤ δ) (hδ4 : δ ≤ 1 / 4) :
    Estimates.modularNoHitProbability L E ≤ Real.exp (-Estimates.modularMass E +
      (Estimates.modularDependencyMass E / 2) / (1 - 2 * δ)) := by
  have hpos : ∀ i ∈ E, 0 < i.modulus := fun i hi => (hperiod i hi).1
  have hP : (0 : ℝ) < period E := by exact_mod_cast period_pos E hpos
  rw [noHitProbability_eq_period L E hL hperiod, noHitProbability_period_eq_periodCount,
    div_le_iff₀ hP, mul_comm, div_eq_inv_mul (Estimates.modularDependencyMass E / 2)]
  exact avoid_le_exp E hpos δ hδ hδ4 E le_rfl

/-- Theorem 5.2 in the form `P(W = 0) ≤ exp(-μ + 2Δ)`, using `1/(1-2δ) ≤ 2`. -/
theorem noHit_le_exp_dependency (L : ℕ) (E : Finset Event) (δ : ℝ) (hL : 0 < L)
    (hperiod : ∀ i ∈ E, 0 < i.modulus ∧ i.modulus ∣ L)
    (hδ : ∀ i ∈ E, Estimates.modularNeighbourMass E i ≤ δ) (hδ4 : δ ≤ 1 / 4) :
    Estimates.modularNoHitProbability L E ≤
      Real.exp (-Estimates.modularMass E + Estimates.modularDependencyMass E) := by
  apply (noHit_le_exp_conditioning L E δ hL hperiod hδ hδ4).trans
  apply Real.exp_le_exp.mpr
  have hdep : 0 ≤ Estimates.modularDependencyMass E :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => modularPairMass_nonneg i j))
  have hc : 1 / 2 ≤ 1 - 2 * δ := by linarith
  have : (Estimates.modularDependencyMass E / 2) / (1 - 2 * δ) ≤ Estimates.modularDependencyMass E := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

end ErdosStraus.Conditioning
