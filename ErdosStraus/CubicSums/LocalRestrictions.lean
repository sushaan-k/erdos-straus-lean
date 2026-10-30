import ErdosStraus.CubicSums.Reindexing
import ErdosStraus.Estimates.SquarefreeCounts
import ErdosStraus.CubicSums.DivisorIdentity

/-!
# Proposition 4.3: divisor sums with local restrictions

Fix a modulus `M` and residues `a_M`, `u` prime to `M`, and put
`𝔐(L) = ∑_{a ≤ L, a ≡ a_M} #{h ∈ Λ_int(a) : h ≡ u (mod M)}/(4a-1)`. We prove the estimate (10),
`𝔐(L) = 𝔖(M)/(24 φ(M)²) · (log L)³ + O_M((log L)²)`, uniformly in `a_M` and `u`. In the Möbius
decomposition of `H(N) = ∑_{a ≤ N, a ≡ a_M} #{h ∣ a² : h ≡ u}/a` exactly `φ(M)` residue triples
occur for each `k` prime to `M`, so (9) and the bounds for the sum over `k` from the proof of
Lemma 4.1 give the cubic asymptotic of `H`. Removing the divisors `1, a, a²` and replacing
`1/(4a)` by `1/(4a-1)` then passes from `H/4` to `𝔐`.
-/

namespace ErdosStraus.DivisorEstimates

open scoped BigOperators

/-! ## Admissible residue triples -/

theorem localCompositeCongruences_iff_zmod (M aM u k : ℕ) (t : (ℕ × ℕ) × ℕ) :
    localCompositeCongruences M aM u k t ↔
      (k : ZMod M) ^ 2 * t.1.1 * t.1.2 * t.2 = aM ∧
        (k : ZMod M) ^ 2 * (t.1.1 : ZMod M) ^ 2 * t.2 = u := by
  change (k ^ 2 * t.1.1 * t.1.2 * t.2 ≡ aM [MOD M] ∧
    k ^ 2 * t.1.1 ^ 2 * t.2 ≡ u [MOD M]) ↔ _
  rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_natCast_iff]
  push_cast
  rfl

theorem localCompositeCongruences_coprime {M aM u k : ℕ} {t : (ℕ × ℕ) × ℕ}
    (ha : Nat.Coprime aM M) (ht : localCompositeCongruences M aM u k t) :
    Nat.Coprime k M ∧ Nat.Coprime t.1.1 M ∧
      Nat.Coprime t.1.2 M ∧ Nat.Coprime t.2 M := by
  have h : Nat.Coprime (k ^ 2 * t.1.1 * t.1.2 * t.2) M := by
    rw [Nat.coprime_iff_gcd_eq_one]
    calc
      _ = M.gcd (k ^ 2 * t.1.1 * t.1.2 * t.2) := Nat.gcd_comm _ _
      _ = ((k ^ 2 * t.1.1 * t.1.2 * t.2) % M).gcd M := Nat.gcd_rec _ _
      _ = (aM % M).gcd M := by rw [ht.1]
      _ = M.gcd aM := (Nat.gcd_rec _ _).symm
      _ = 1 := ha.symm.gcd_eq_one
  simp only [Nat.coprime_mul_iff_left, Nat.coprime_pow_left_iff (by decide : 0 < 2)] at h
  tauto

theorem localResidueTripleClasses_eq_empty {M aM u k : ℕ}
    (ha : Nat.Coprime aM M) (hk : ¬ Nat.Coprime k M) :
    localResidueTripleClasses M aM u k = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  exact hk (localCompositeCongruences_coprime ha (Finset.mem_filter.mp ht).2).1

/-- For a unit `v` modulo `M`, the residue triple `(v, a_M v u⁻¹, u k⁻² v⁻²)`, which solves
`localCompositeCongruences M aM u k`. -/
noncomputable def localClassOfUnit {M aM u k : ℕ}
    (hk : Nat.Coprime k M) (ha : Nat.Coprime aM M) (hu : Nat.Coprime u M)
    (v : (ZMod M)ˣ) : (ℕ × ℕ) × ℕ :=
  ((v.val.val, ((ZMod.unitOfCoprime aM ha * v * (ZMod.unitOfCoprime u hu)⁻¹).val).val),
    ((ZMod.unitOfCoprime u hu * ((ZMod.unitOfCoprime k hk) ^ 2 * v ^ 2)⁻¹).val).val)

theorem localClassOfUnit_mem {M aM u k : ℕ} (hM : 0 < M)
    (hk : Nat.Coprime k M) (ha : Nat.Coprime aM M) (hu : Nat.Coprime u M)
    (v : (ZMod M)ˣ) :
    localClassOfUnit hk ha hu v ∈ localResidueTripleClasses M aM u k := by
  classical
  let _ : NeZero M := ⟨hM.ne'⟩
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (ZMod.val_lt _), Finset.mem_range.mpr (ZMod.val_lt _)⟩,
      Finset.mem_range.mpr (ZMod.val_lt _)⟩
  · apply (localCompositeCongruences_iff_zmod _ _ _ _ _).mpr
    dsimp only [localClassOfUnit]
    simp only [ZMod.natCast_zmod_val]
    constructor
    · change ((ZMod.unitOfCoprime k hk : (ZMod M)ˣ) : ZMod M) ^ 2 *
        (v : ZMod M) *
        ((ZMod.unitOfCoprime aM ha * v * (ZMod.unitOfCoprime u hu)⁻¹ : (ZMod M)ˣ) : ZMod M) *
        ((ZMod.unitOfCoprime u hu * ((ZMod.unitOfCoprime k hk) ^ 2 * v ^ 2)⁻¹ : (ZMod M)ˣ) : ZMod M) =
        (ZMod.unitOfCoprime aM ha : (ZMod M)ˣ)
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
      congr 1
      simp [pow_two, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
    · change ((ZMod.unitOfCoprime k hk : (ZMod M)ˣ) : ZMod M) ^ 2 *
        (v : ZMod M) ^ 2 *
        ((ZMod.unitOfCoprime u hu * ((ZMod.unitOfCoprime k hk) ^ 2 * v ^ 2)⁻¹ : (ZMod M)ˣ) : ZMod M) =
        (ZMod.unitOfCoprime u hu : (ZMod M)ˣ)
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
        ← Units.val_mul, ← Units.val_mul]
      congr 1
      simp [pow_two, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]

theorem localCompositeCongruences_unique {M aM u k : ℕ}
    (hk : Nat.Coprime k M) (ha : Nat.Coprime aM M)
    {t r : (ℕ × ℕ) × ℕ}
    (ht : localCompositeCongruences M aM u k t)
    (hr : localCompositeCongruences M aM u k r)
    (hx : (t.1.1 : ZMod M) = r.1.1) :
    (t.1.2 : ZMod M) = r.1.2 ∧ (t.2 : ZMod M) = r.2 := by
  obtain ⟨_hk, htx, hty, hte⟩ := localCompositeCongruences_coprime ha ht
  obtain ⟨ht1, ht2⟩ := (localCompositeCongruences_iff_zmod _ _ _ _ _).mp ht
  obtain ⟨hr1, hr2⟩ := (localCompositeCongruences_iff_zmod _ _ _ _ _).mp hr
  have hunit : IsUnit ((k : ZMod M) ^ 2 * (t.1.1 : ZMod M) ^ 2) :=
    ((ZMod.isUnit_iff_coprime _ _).mpr hk).pow 2 |>.mul
      (((ZMod.isUnit_iff_coprime _ _).mpr htx).pow 2)
  have he : (t.2 : ZMod M) = r.2 := hunit.mul_left_cancel (by
    rw [ht2, hx, hr2])
  refine ⟨?_, he⟩
  have hp : IsUnit ((k : ZMod M) ^ 2 * t.1.1 * t.2) :=
    (((ZMod.isUnit_iff_coprime _ _).mpr hk).pow 2 |>.mul
      ((ZMod.isUnit_iff_coprime _ _).mpr htx)).mul
        ((ZMod.isUnit_iff_coprime _ _).mpr hte)
  apply hp.mul_left_cancel
  calc
    _ = (k : ZMod M) ^ 2 * t.1.1 * t.1.2 * t.2 := by ring
    _ = aM := ht1
    _ = (k : ZMod M) ^ 2 * r.1.1 * r.1.2 * r.2 := hr1.symm
    _ = _ := by rw [hx, he]; ring

/-- For `k`, `a_M`, `u` prime to `M` there are exactly `φ(M)` residue triples: the first
coordinate is any unit, and it determines the other two. -/
theorem localResidueTripleClasses_card {M aM u k : ℕ} (hM : 0 < M)
    (hk : Nat.Coprime k M) (ha : Nat.Coprime aM M) (hu : Nat.Coprime u M) :
    (localResidueTripleClasses M aM u k).card = Nat.totient M := by
  classical
  let _ : NeZero M := ⟨hM.ne'⟩
  have hcard : (Finset.univ : Finset (ZMod M)ˣ).card =
      (localResidueTripleClasses M aM u k).card := by
    apply Finset.card_bij (fun v _ => localClassOfUnit hk ha hu v)
    · intro v hv
      exact localClassOfUnit_mem hM hk ha hu v
    · intro v hv w hw heq
      apply Units.ext
      have hh := congrArg (fun t : (ℕ × ℕ) × ℕ => t.1.1) heq
      change v.val.val = w.val.val at hh
      exact ZMod.val_injective M hh
    · intro t ht
      have ht' := (Finset.mem_filter.mp ht).2
      obtain ⟨_hk, hx, _hy, _he⟩ := localCompositeCongruences_coprime ha ht'
      let v := ZMod.unitOfCoprime t.1.1 hx
      refine ⟨v, Finset.mem_univ _, ?_⟩
      have htbox := (Finset.mem_filter.mp ht).1
      obtain ⟨htxy, hte⟩ := Finset.mem_product.mp htbox
      obtain ⟨htx, hty⟩ := Finset.mem_product.mp htxy
      have hvr := localClassOfUnit_mem hM hk ha hu v
      have hvbox := (Finset.mem_filter.mp hvr).1
      obtain ⟨hvxy, hve⟩ := Finset.mem_product.mp hvbox
      obtain ⟨hvx, hvy⟩ := Finset.mem_product.mp hvxy
      have hvxEq : (localClassOfUnit hk ha hu v).1.1 = t.1.1 := by
        exact ZMod.val_natCast_of_lt (Finset.mem_range.mp htx)
      obtain ⟨hyEq, heEq⟩ := localCompositeCongruences_unique hk ha
        (Finset.mem_filter.mp hvr).2 ht' (by rw [hvxEq])
      have hyNat := congrArg ZMod.val hyEq
      have heNat := congrArg ZMod.val heEq
      rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hvy),
        ZMod.val_natCast_of_lt (Finset.mem_range.mp hty)] at hyNat
      rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hve),
        ZMod.val_natCast_of_lt (Finset.mem_range.mp hte)] at heNat
      exact Prod.ext (Prod.ext hvxEq hyNat) heNat
  rw [← hcard, Finset.card_univ, ZMod.card_units_eq_totient]

section

attribute [local instance] Classical.propDecidable

/-! ## The Möbius sum over residue triples -/

theorem residueHarmonicTriple_of_lt_one (M b₁ b₂ b₃ : ℕ) {T : ℝ} (hT : T < 1) :
    residueHarmonicTriple M b₁ b₂ b₃ T = 0 := by
  simp [residueHarmonicTriple, residueHarmonicTransform, Nat.floor_eq_zero.mpr hT]

/-- Only the terms with `k ≤ √N` and `(k, M) = 1` survive in the Möbius decomposition. -/
theorem local_square_divisor_reciprocal_sqrt_reindex
    (N M aM u : ℕ) (hM : 0 < M) (ha : Nat.Coprime aM M) :
    (∑ a ∈ (Finset.Icc 1 N).filter (fun a => Estimates.congMod a aM M),
      ∑ _h ∈ (a ^ 2).divisors.filter (fun h => Estimates.congMod h u M),
        (1 : ℝ) / (a : ℝ)) =
      ∑ k ∈ (Finset.Icc 1 (Nat.sqrt N)).filter (fun k => Nat.Coprime k M),
        ((ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2) *
          ∑ r ∈ localResidueTripleClasses M aM u k,
            residueHarmonicTriple M r.1.1 r.1.2 r.2 ((N : ℝ) / (k : ℝ) ^ 2) := by
  classical
  rw [local_square_divisor_reciprocal_eq_residue_harmonic_triples N M aM u hM]
  have hs : Finset.Icc 1 (Nat.sqrt N) ⊆ Finset.Icc 1 N := by
    intro k hk
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,
      (Finset.mem_Icc.mp hk).2.trans (Nat.sqrt_le_self N)⟩
  rw [← Finset.sum_subset hs (by
    intro k hk hkn
    have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
    have hklarge : Nat.sqrt N < k := by
      have h := Finset.mem_Icc.mp hk
      simp only [Finset.mem_Icc, not_and_or, not_le] at hkn
      omega
    have hpow : (N : ℝ) < (k : ℝ) ^ 2 := by
      exact_mod_cast Nat.sqrt_lt'.mp hklarge
    have hquot : (N : ℝ) / (k : ℝ) ^ 2 < 1 :=
      (div_lt_one (by positivity)).mpr hpow
    simp only [residueHarmonicTriple_of_lt_one _ _ _ _ hquot,
      Finset.sum_const_zero, mul_zero])]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hcop : Nat.Coprime k M
  · exact (if_pos hcop).symm
  · rw [if_neg hcop, localResidueTripleClasses_eq_empty ha hcop]
    simp only [Finset.sum_empty, mul_zero]

/-- The estimate (9) summed over the `φ(M)` residue triples. -/
theorem abs_local_residue_triple_sum_sub_main_le
    {M aM u k : ℕ} (hM : 0 < M) (hk : Nat.Coprime k M)
    (ha : Nat.Coprime aM M) (hu : Nat.Coprime u M) {T : ℝ} (hT : 1 ≤ T) :
    |(∑ r ∈ localResidueTripleClasses M aM u k,
        residueHarmonicTriple M r.1.1 r.1.2 r.2 T) -
      (Nat.totient M : ℝ) * (Real.log T) ^ 3 / (6 * (M : ℝ) ^ 3)| ≤
        40 * (Nat.totient M : ℝ) * (1 + Real.log T) ^ 2 := by
  classical
  have hcard := localResidueTripleClasses_card hM hk ha hu
  calc
    _ = |∑ r ∈ localResidueTripleClasses M aM u k,
        (residueHarmonicTriple M r.1.1 r.1.2 r.2 T -
          (Real.log T) ^ 3 / (6 * (M : ℝ) ^ 3))| := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, hcard]
      congr 1
      ring
    _ ≤ ∑ r ∈ localResidueTripleClasses M aM u k,
        |residueHarmonicTriple M r.1.1 r.1.2 r.2 T -
          (Real.log T) ^ 3 / (6 * (M : ℝ) ^ 3)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ localResidueTripleClasses M aM u k,
        40 * (1 + Real.log T) ^ 2 := by
      exact Finset.sum_le_sum (fun r _ => abs_residueHarmonicTriple_sub_main_le _ _ _ _ hM hT)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, hcard]; ring

/-- `H(N) = φ(M)/(6M³) ∑_{k ≤ √N, (k,M)=1} μ(k)/k² (log(N/k²))³ + O(φ(M) (1 + log N)²)`. -/
theorem abs_local_square_divisor_reciprocal_sub_log_sum_le
    (N M aM u : ℕ) (hN : 1 ≤ N) (hM : 0 < M)
    (ha : Nat.Coprime aM M) (hu : Nat.Coprime u M) :
    |(∑ a ∈ (Finset.Icc 1 N).filter (fun a => Estimates.congMod a aM M),
      ∑ _h ∈ (a ^ 2).divisors.filter (fun h => Estimates.congMod h u M),
        (1 : ℝ) / (a : ℝ)) -
      (Nat.totient M : ℝ) / (6 * (M : ℝ) ^ 3) *
        ∑ k ∈ (Finset.Icc 1 (Nat.sqrt N)).filter (fun k => Nat.Coprime k M),
          (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
            (Real.log ((N : ℝ) / (k : ℝ) ^ 2)) ^ 3| ≤
      (40 * (Nat.totient M : ℝ) * (Real.pi ^ 2 / 6)) * (1 + Real.log N) ^ 2 := by
  classical
  rw [local_square_divisor_reciprocal_sqrt_reindex N M aM u hM ha,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ (Finset.Icc 1 (Nat.sqrt N)).filter (fun k => Nat.Coprime k M),
        |((ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2) *
          ∑ r ∈ localResidueTripleClasses M aM u k,
            residueHarmonicTriple M r.1.1 r.1.2 r.2 ((N : ℝ) / (k : ℝ) ^ 2) -
          (Nat.totient M : ℝ) / (6 * (M : ℝ) ^ 3) *
            ((ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
              (Real.log ((N : ℝ) / (k : ℝ) ^ 2)) ^ 3)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ (Finset.Icc 1 (Nat.sqrt N)).filter (fun k => Nat.Coprime k M),
        (40 * (Nat.totient M : ℝ) * (1 + Real.log N) ^ 2) * (1 / (k : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hkI, hkcop⟩ := Finset.mem_filter.mp hk
      have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (Finset.mem_Icc.mp hkI).1
      have hk1 : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr (Finset.mem_Icc.mp hkI).1
      have hkpow : (k : ℝ) ^ 2 ≤ N := by
        exact_mod_cast Nat.le_sqrt'.mp (Finset.mem_Icc.mp hkI).2
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hquot : 1 ≤ (N : ℝ) / (k : ℝ) ^ 2 :=
        (le_div_iff₀ (sq_pos_of_pos hkpos)).mpr (by simpa)
      have hquotN : (N : ℝ) / (k : ℝ) ^ 2 ≤ N :=
        div_le_self (Nat.cast_nonneg _) (by nlinarith)
      have hlog : Real.log ((N : ℝ) / (k : ℝ) ^ 2) ≤ Real.log N :=
        Real.log_le_log (zero_lt_one.trans_le hquot) hquotN
      have hlog0 := Real.log_nonneg hquot
      have hc := abs_local_residue_triple_sum_sub_main_le hM hkcop ha hu hquot
      have hpow : (1 + Real.log ((N : ℝ) / (k : ℝ) ^ 2)) ^ 2 ≤
          (1 + Real.log N) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      have hc' := hc.trans (mul_le_mul_of_nonneg_left hpow
        (by positivity : 0 ≤ 40 * (Nat.totient M : ℝ)))
      have he : ((ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2) *
          ∑ r ∈ localResidueTripleClasses M aM u k,
            residueHarmonicTriple M r.1.1 r.1.2 r.2 ((N : ℝ) / (k : ℝ) ^ 2) -
          (Nat.totient M : ℝ) / (6 * (M : ℝ) ^ 3) *
            ((ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
              (Real.log ((N : ℝ) / (k : ℝ) ^ 2)) ^ 3) =
          ((ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2) *
            ((∑ r ∈ localResidueTripleClasses M aM u k,
              residueHarmonicTriple M r.1.1 r.1.2 r.2 ((N : ℝ) / (k : ℝ) ^ 2)) -
              (Nat.totient M : ℝ) * (Real.log ((N : ℝ) / (k : ℝ) ^ 2)) ^ 3 /
                (6 * (M : ℝ) ^ 3)) := by ring
      rw [he, abs_mul]
      have hh := mul_le_mul (abs_moebius_div_sq_le k) hc' (abs_nonneg _)
        (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg (k : ℝ)))
      convert hh using 1
      ring
    _ = (40 * (Nat.totient M : ℝ) * (1 + Real.log N) ^ 2) *
        ∑ k ∈ (Finset.Icc 1 (Nat.sqrt N)).filter (fun k => Nat.Coprime k M),
          (1 : ℝ) / (k : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (40 * (Nat.totient M : ℝ) * (1 + Real.log N) ^ 2) * (Real.pi ^ 2 / 6) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← hasSum_zeta_two.tsum_eq]
      exact Summable.sum_le_tsum _ (fun k _ => by positivity) hasSum_zeta_two.summable
    _ = _ := by ring

end

/-! ## The reciprocal sum `H(N)` -/

/-- The sum `H_{M,c}` in the proof of Proposition 4.3:
`H(N) = ∑_{a ≤ N, a ≡ a_M} #{h ∣ a² : h ≡ u (mod M)}/a`. -/
noncomputable def localReciprocalMass (N M aM u : ℕ) : ℝ := by
  classical
  exact ∑ a ∈ (Finset.Icc 1 N).filter (fun a => Estimates.congMod a aM M),
    ∑ h ∈ (a ^ 2).divisors.filter (fun h => Estimates.congMod h u M), (1 : ℝ) / a

/-- `κ_M = φ(M)/(6M³) · ζ(2)⁻¹ ∏_{p ∣ M} (1 - p⁻²)⁻¹`, the coefficient of `(log N)³`
in `H(N)`. -/
noncomputable def localReciprocalMainCoefficient (M : ℕ) : ℝ :=
  (Nat.totient M : ℝ) / (6 * (M : ℝ) ^ 3) * restrictedMoebiusSquareConstant M

/-- The constant `E_M` in `|H(N) - κ_M (log N)³| ≤ E_M (1 + log N)²`. -/
noncomputable def localReciprocalErrorConstant (M : ℕ) : ℝ :=
  40 * (Nat.totient M : ℝ) * (Real.pi ^ 2 / 6) +
    ((Nat.totient M : ℝ) / (6 * (M : ℝ) ^ 3)) *
      (6 * logReciprocalSqConstant + 4)

theorem localReciprocalErrorConstant_nonneg (M : ℕ) :
    0 ≤ localReciprocalErrorConstant M := by
  unfold localReciprocalErrorConstant
  have hh := logReciprocalSqConstant_nonneg
  positivity

/-- `|H(N) - κ_M (log N)³| ≤ E_M (1 + log N)²` for `N ≥ 1`, uniformly in `a_M` and `u`
prime to `M`. -/
theorem abs_localReciprocalMass_sub_main_le (N M aM u : ℕ)
    (hN : 1 ≤ N) (hM : 0 < M) (ha : Nat.Coprime aM M) (hu : Nat.Coprime u M) :
    |localReciprocalMass N M aM u -
      localReciprocalMainCoefficient M * (Real.log N) ^ 3| ≤
      localReciprocalErrorConstant M * (1 + Real.log N) ^ 2 := by
  classical
  let c : ℝ := (Nat.totient M : ℝ) / (6 * (M : ℝ) ^ 3)
  let S : ℝ := ∑ k ∈ (Finset.Icc 1 (Nat.sqrt N)).filter (fun k => Nat.Coprime k M),
    (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
      (Real.log ((N : ℝ) / (k : ℝ) ^ 2)) ^ 3
  have h₁ := abs_local_square_divisor_reciprocal_sub_log_sum_le N M aM u hN hM ha hu
  change |localReciprocalMass N M aM u - c * S| ≤ _ at h₁
  have h₂ := abs_restricted_moebius_log_cube_sqrt_sub_main_le M hM
    (show (1 : ℝ) ≤ N by exact_mod_cast hN)
  simp only [Real.nat_floor_real_sqrt_eq_nat_sqrt] at h₂
  change |S - restrictedMoebiusSquareConstant M * (Real.log N) ^ 3| ≤ _ at h₂
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hshape : (Real.log (N : ℝ)) ^ 2 ≤ (1 + Real.log N) ^ 2 := by nlinarith
  have h₂' := mul_le_mul_of_nonneg_left h₂ hc
  have hshape' := mul_le_mul_of_nonneg_left hshape
    (show 0 ≤ c * (6 * logReciprocalSqConstant + 4) by
      have hh := logReciprocalSqConstant_nonneg
      positivity)
  have ht := abs_add_le (localReciprocalMass N M aM u - c * S)
    (c * (S - restrictedMoebiusSquareConstant M * (Real.log N) ^ 3))
  rw [abs_mul, abs_of_nonneg hc] at ht
  have he : localReciprocalMass N M aM u - c * S +
      c * (S - restrictedMoebiusSquareConstant M * (Real.log N) ^ 3) =
      localReciprocalMass N M aM u -
        localReciprocalMainCoefficient M * (Real.log N) ^ 3 := by
    unfold localReciprocalMainCoefficient
    dsimp [c]
    ring
  rw [he] at ht
  unfold localReciprocalErrorConstant
  dsimp [c] at h₂' hshape'
  nlinarith only [ht, h₁, h₂', hshape']

/-- The same estimate at a real cutoff `L ≥ 1`, with a larger constant. -/
theorem abs_localReciprocalMass_real_sub_main_le (M aM u : ℕ)
    (hM : 0 < M) (ha : Nat.Coprime aM M) (hu : Nat.Coprime u M)
    {L : ℝ} (hL : 1 ≤ L) :
    |localReciprocalMass ⌊L⌋₊ M aM u -
      localReciprocalMainCoefficient M * (Real.log L) ^ 3| ≤
      (localReciprocalErrorConstant M + 3 * |localReciprocalMainCoefficient M|) *
        (1 + Real.log L) ^ 2 := by
  let N := ⌊L⌋₊
  have hN : 1 ≤ N := Nat.floor_pos.mpr hL
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hNL : (N : ℝ) ≤ L := Nat.floor_le hLp.le
  have hLN : L < (N : ℝ) + 1 := Nat.lt_floor_add_one L
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlogle : Real.log (N : ℝ) ≤ Real.log L := Real.log_le_log hNp hNL
  have hlogdiff : Real.log L - Real.log (N : ℝ) ≤ 1 := by
    have hh := Real.log_le_log hLp (show L ≤ 2 * (N : ℝ) by linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hNp)] at hh
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hlog2
    linarith
  have hnat := abs_localReciprocalMass_sub_main_le N M aM u hN hM ha hu
  have hshape : (1 + Real.log (N : ℝ)) ^ 2 ≤ (1 + Real.log L) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hnat' := hnat.trans (mul_le_mul_of_nonneg_left hshape
    (localReciprocalErrorConstant_nonneg M))
  have hcubes := abs_cube_sub_cube_le hlogN hlogle
  have hcubes' : |(Real.log (N : ℝ)) ^ 3 - (Real.log L) ^ 3| ≤
      3 * (Real.log L) ^ 2 := hcubes.trans (by
    have hh := mul_le_mul_of_nonneg_left hlogdiff
      (show 0 ≤ 3 * (Real.log L) ^ 2 by positivity)
    simpa only [mul_one] using hh)
  have hmain : |localReciprocalMainCoefficient M * (Real.log (N : ℝ)) ^ 3 -
      localReciprocalMainCoefficient M * (Real.log L) ^ 3| ≤
      (3 * |localReciprocalMainCoefficient M|) * (1 + Real.log L) ^ 2 := by
    rw [← mul_sub, abs_mul]
    calc
      _ ≤ |localReciprocalMainCoefficient M| * (3 * (Real.log L) ^ 2) :=
        mul_le_mul_of_nonneg_left hcubes' (abs_nonneg _)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left
          (show (Real.log L) ^ 2 ≤ (1 + Real.log L) ^ 2 by nlinarith)
          (show 0 ≤ 3 * |localReciprocalMainCoefficient M| by positivity)
        nlinarith only [hh]
  have ht := abs_add_le (localReciprocalMass N M aM u -
    localReciprocalMainCoefficient M * (Real.log (N : ℝ)) ^ 3)
    (localReciprocalMainCoefficient M * (Real.log (N : ℝ)) ^ 3 -
      localReciprocalMainCoefficient M * (Real.log L) ^ 3)
  have he : localReciprocalMass N M aM u -
      localReciprocalMainCoefficient M * (Real.log (N : ℝ)) ^ 3 +
      (localReciprocalMainCoefficient M * (Real.log (N : ℝ)) ^ 3 -
        localReciprocalMainCoefficient M * (Real.log L) ^ 3) =
      localReciprocalMass N M aM u -
        localReciprocalMainCoefficient M * (Real.log L) ^ 3 := by ring
  rw [he] at ht
  nlinarith only [ht, hnat', hmain]

/-- `H(L)/(log L)³ → κ_M`. -/
theorem localReciprocalMass_real_cubic_limit (M aM u : ℕ)
    (hM : 0 < M) (ha : Nat.Coprime aM M) (hu : Nat.Coprime u M) :
    Filter.Tendsto (fun L : ℝ => localReciprocalMass ⌊L⌋₊ M aM u /
      (Real.log L) ^ 3) Filter.atTop (nhds (localReciprocalMainCoefficient M)) := by
  let C := 4 * (localReciprocalErrorConstant M + 3 * |localReciprocalMainCoefficient M|)
  have hC : 0 ≤ C := by
    dsimp [C]
    have hh := localReciprocalErrorConstant_nonneg M
    positivity
  have hlim : Filter.Tendsto (fun L : ℝ => C / Real.log L) Filter.atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul C
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm' _ hlim
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with L hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hL
  have hlog : 1 ≤ Real.log L := by
    have hh := Real.log_le_log (Real.exp_pos 1) hL
    simpa only [Real.log_exp] using hh
  have hlogp : 0 < Real.log L := by linarith
  have h := abs_localReciprocalMass_real_sub_main_le M aM u hM ha hu hL1
  have hshape : (1 + Real.log L) ^ 2 ≤ 4 * (Real.log L) ^ 2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hshape
    (show 0 ≤ localReciprocalErrorConstant M + 3 * |localReciprocalMainCoefficient M| by
      have hh := localReciprocalErrorConstant_nonneg M
      positivity)
  have hbound : |localReciprocalMass ⌊L⌋₊ M aM u -
      localReciprocalMainCoefficient M * (Real.log L) ^ 3| ≤ C * (Real.log L) ^ 2 := by
    dsimp [C]
    nlinarith only [h, hh]
  rw [Real.norm_eq_abs]
  have he : localReciprocalMass ⌊L⌋₊ M aM u / (Real.log L) ^ 3 -
      localReciprocalMainCoefficient M =
      (localReciprocalMass ⌊L⌋₊ M aM u -
        localReciprocalMainCoefficient M * (Real.log L) ^ 3) / (Real.log L) ^ 3 := by
    field_simp
  rw [he, abs_div, abs_of_pos (pow_pos hlogp 3)]
  calc
    _ ≤ (C * (Real.log L) ^ 2) / (Real.log L) ^ 3 :=
      div_le_div_of_nonneg_right hbound (pow_nonneg hlogp.le _)
    _ = C / Real.log L := by field_simp

/-! ## The leading coefficient -/

/-- `φ(M)/(24M³) · ζ(2)⁻¹ ∏_{p ∣ M} (1 - p⁻²)⁻¹ = 𝔖(M)/(24 φ(M)²)`, where
`𝔖(M) = ζ(2)⁻¹ ∏_{p ∣ M} (1 - p⁻¹)³/(1 - p⁻²)`. -/
theorem local_coefficient_euler_factor (M : ℕ) (hM : 0 < M) :
    (Nat.totient M : ℝ) / (24 * (M : ℝ) ^ 3) *
        restrictedMoebiusSquareConstant M =
      ((1 / (Real.pi ^ 2 / 6)) *
        ∏ p ∈ M.primeFactors,
          ((1 - (p : ℝ)⁻¹) ^ 3 / (1 - ((p : ℝ) ^ 2)⁻¹))) /
        (24 * (Nat.totient M : ℝ) ^ 2) := by
  have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hφne : (Nat.totient M : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hM).ne'
  have hφ : (Nat.totient M : ℝ) = (M : ℝ) *
      ∏ p ∈ M.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors M)
    simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub,
      Rat.cast_one, Rat.cast_inv] using h
  have hprod : (∏ p ∈ M.primeFactors, (1 - (p : ℝ)⁻¹)) =
      (Nat.totient M : ℝ) / M := by
    apply (eq_div_iff hMne).mpr
    rw [mul_comm, ← hφ]
  have heuler : (∏ p ∈ M.primeFactors,
      ((1 - (p : ℝ)⁻¹) ^ 3 / (1 - ((p : ℝ) ^ 2)⁻¹))) =
      (∏ p ∈ M.primeFactors, (1 - (p : ℝ)⁻¹)) ^ 3 *
        ∏ p ∈ M.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ := by
    simp only [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_pow]
  rw [heuler, hprod]
  unfold restrictedMoebiusSquareConstant
  generalize (1 / (Real.pi ^ 2 / 6)) = C
  generalize (∏ p ∈ M.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹) = E
  field_simp [hMne, hφne]

/-- `κ_M/4 = 𝔖(M)/(24 φ(M)²)`. -/
theorem localReciprocalMainCoefficient_quarter (M : ℕ) (hM : 0 < M) :
    localReciprocalMainCoefficient M / 4 =
      ((1 / (Real.pi ^ 2 / 6)) *
        ∏ p ∈ M.primeFactors,
          ((1 - (p : ℝ)⁻¹) ^ 3 / (1 - ((p : ℝ) ^ 2)⁻¹))) /
        (24 * (Nat.totient M : ℝ) ^ 2) := by
  rw [← local_coefficient_euler_factor M hM]
  unfold localReciprocalMainCoefficient
  ring

section

attribute [local instance] Classical.propDecidable

/-! ## Removing the divisors `1, a, a²` -/

/-- `#{h ∣ a² : h ≡ u (mod M)}`. -/
noncomputable def localFullFiber (M u a : ℕ) : ℝ := by
  classical
  exact (((a ^ 2).divisors.filter (fun h => Estimates.congMod h u M)).card : ℝ)

/-- `#{h ∈ Λ_int(a) : h ≡ u (mod M)}`. -/
noncomputable def localInteriorFiber (M u a : ℕ) : ℝ := by
  classical
  exact (((a ^ 2).divisors.filter
    (fun h => Estimates.congMod h u M ∧ h ≠ 1 ∧ h ≠ a ∧ h ≠ a ^ 2)).card : ℝ)

/-- `𝔐(L) = ∑_{a ≤ L, a ≡ a_M} #{h ∈ Λ_int(a) : h ≡ u (mod M)}/(4a-1)`. -/
noncomputable def localInteriorMass (L : ℝ) (M aM u : ℕ) : ℝ := by
  classical
  exact ∑ a ∈ (Finset.Icc 1 ⌊L⌋₊).filter (fun a => Estimates.congMod a aM M),
    localInteriorFiber M u a / (4 * (a : ℝ) - 1)

theorem local_fiber_bounds (M u a : ℕ) :
    0 ≤ localInteriorFiber M u a ∧ localInteriorFiber M u a ≤ localFullFiber M u a ∧
      localFullFiber M u a ≤ ((a ^ 2).divisors.card : ℝ) ∧
      localFullFiber M u a - localInteriorFiber M u a ≤ 3 := by
  classical
  let s := (a ^ 2).divisors.filter (fun h => Estimates.congMod h u M)
  have he : s \ {1, a, a ^ 2} = (a ^ 2).divisors.filter
      (fun h => Estimates.congMod h u M ∧ h ≠ 1 ∧ h ≠ a ∧ h ≠ a ^ 2) := by
    ext h
    simp [s]
    tauto
  have hi := Finset.card_le_card (Finset.sdiff_subset (s := s) (t := {1, a, a ^ 2}))
  have hf := Finset.card_le_card (Finset.filter_subset (fun h => Estimates.congMod h u M)
    (a ^ 2).divisors)
  have hb := Finset.card_le_card_sdiff_add_card (s := s) (t := {1, a, a ^ 2})
  have ht : ({1, a, a ^ 2} : Finset ℕ).card ≤ 3 := Finset.card_le_three
  rw [he] at hi hb
  unfold localFullFiber localInteriorFiber
  dsimp [s] at hi hb
  refine ⟨by positivity, by exact_mod_cast hi, by exact_mod_cast hf, ?_⟩
  have hh : ((a ^ 2).divisors.filter (fun h => Estimates.congMod h u M)).card ≤
      ((a ^ 2).divisors.filter
        (fun h => Estimates.congMod h u M ∧ h ≠ 1 ∧ h ≠ a ∧ h ≠ a ^ 2)).card + 3 := by
    simpa only [ne_eq] using hb.trans (Nat.add_le_add_left ht _)
  exact_mod_cast (show (((a ^ 2).divisors.filter (fun h => Estimates.congMod h u M)).card : ℤ) -
    ((a ^ 2).divisors.filter
      (fun h => Estimates.congMod h u M ∧ h ≠ 1 ∧ h ≠ a ∧ h ≠ a ^ 2)).card ≤ 3 by omega)

/-- Removing `1, a, a²` and replacing `1/(4a)` by `1/(4a-1)` changes the term of `a` by at
most `τ(a²)/a² + 1/a`. -/
theorem abs_local_interior_term_sub_quarter_reciprocal_le (M u a : ℕ) (ha : 1 ≤ a) :
    |localInteriorFiber M u a / (4 * (a : ℝ) - 1) - localFullFiber M u a / (4 * (a : ℝ))| ≤
      ((a ^ 2).divisors.card : ℝ) / (a : ℝ) ^ 2 + 1 / (a : ℝ) := by
  obtain ⟨hi0, hif, hft, hdiff⟩ := local_fiber_bounds M u a
  have hf0 : 0 ≤ localFullFiber M u a := hi0.trans hif
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hap : (0 : ℝ) < a := by linarith
  have hden : 0 < 4 * (a : ℝ) - 1 := by linarith
  have hcoef : 0 ≤ 1 / (4 * (a : ℝ) - 1) - 1 / (4 * (a : ℝ)) ∧
      1 / (4 * (a : ℝ) - 1) - 1 / (4 * (a : ℝ)) ≤ 1 / (a : ℝ) ^ 2 := by
    have he : 1 / (4 * (a : ℝ) - 1) - 1 / (4 * (a : ℝ)) =
        1 / ((4 * (a : ℝ) - 1) * (4 * (a : ℝ))) := by
      field_simp
      ring
    rw [he]
    constructor
    · positivity
    · apply one_div_le_one_div_of_le (sq_pos_of_pos hap)
      nlinarith
  have hfull : |localFullFiber M u a / (4 * (a : ℝ) - 1) -
      localFullFiber M u a / (4 * (a : ℝ))| ≤ ((a ^ 2).divisors.card : ℝ) / (a : ℝ) ^ 2 := by
    have he : localFullFiber M u a / (4 * (a : ℝ) - 1) -
        localFullFiber M u a / (4 * (a : ℝ)) = localFullFiber M u a *
        (1 / (4 * (a : ℝ) - 1) - 1 / (4 * (a : ℝ))) := by ring
    rw [he, abs_of_nonneg (mul_nonneg hf0 hcoef.1)]
    calc
      _ ≤ localFullFiber M u a * (1 / (a : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hcoef.2 hf0
      _ ≤ ((a ^ 2).divisors.card : ℝ) * (1 / (a : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hft (by positivity)
      _ = _ := by ring
  have hboundary : |localInteriorFiber M u a / (4 * (a : ℝ) - 1) -
      localFullFiber M u a / (4 * (a : ℝ) - 1)| ≤ 1 / (a : ℝ) := by
    rw [← sub_div, abs_div, abs_of_pos hden, abs_of_nonpos (sub_nonpos.mpr hif)]
    have hdiff' : -(localInteriorFiber M u a - localFullFiber M u a) ≤ 3 := by linarith
    calc
      _ ≤ 3 / (4 * (a : ℝ) - 1) := div_le_div_of_nonneg_right hdiff' hden.le
      _ ≤ 1 / (a : ℝ) := (div_le_div_iff₀ hden hap).mpr (by nlinarith)
  have ht := abs_add_le
    (localInteriorFiber M u a / (4 * (a : ℝ) - 1) - localFullFiber M u a / (4 * (a : ℝ) - 1))
    (localFullFiber M u a / (4 * (a : ℝ) - 1) - localFullFiber M u a / (4 * (a : ℝ)))
  have he : localInteriorFiber M u a / (4 * (a : ℝ) - 1) - localFullFiber M u a / (4 * (a : ℝ) - 1) +
      (localFullFiber M u a / (4 * (a : ℝ) - 1) - localFullFiber M u a / (4 * (a : ℝ))) =
      localInteriorFiber M u a / (4 * (a : ℝ) - 1) - localFullFiber M u a / (4 * (a : ℝ)) := by ring
  rw [he] at ht
  linarith

theorem localReciprocalMass_eq_sum_fiber (N M aM u : ℕ) :
    localReciprocalMass N M aM u =
      ∑ a ∈ (Finset.Icc 1 N).filter (fun a => Estimates.congMod a aM M),
        localFullFiber M u a / (a : ℝ) := by
  classical
  unfold localReciprocalMass localFullFiber
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-- `|𝔐(L) - H(L)/4| ≤ ζ(2)³ + 1 + log L`, using `∑_a τ(a²)/a² ≤ ζ(2)³`. -/
theorem abs_localInteriorMass_sub_quarter_reciprocal_le (M aM u : ℕ)
    {L : ℝ} (hL : 1 ≤ L) :
    |localInteriorMass L M aM u - localReciprocalMass ⌊L⌋₊ M aM u / 4| ≤
      (Real.pi ^ 2 / 6) ^ 3 + 1 + Real.log L := by
  classical
  rw [localReciprocalMass_eq_sum_fiber, Finset.sum_div]
  unfold localInteriorMass
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a ∈ (Finset.Icc 1 ⌊L⌋₊).filter (fun a => Estimates.congMod a aM M),
        |localInteriorFiber M u a / (4 * (a : ℝ) - 1) - localFullFiber M u a / (a : ℝ) / 4| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ (Finset.Icc 1 ⌊L⌋₊).filter (fun a => Estimates.congMod a aM M),
        (((a ^ 2).divisors.card : ℝ) / (a : ℝ) ^ 2 + 1 / (a : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      (convert abs_local_interior_term_sub_quarter_reciprocal_le M u a
        (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1 using 1; congr 1; ring_nf)
    _ ≤ ∑ a ∈ Finset.Icc 1 ⌊L⌋₊,
        (((a ^ 2).divisors.card : ℝ) / (a : ℝ) ^ 2 + 1 / (a : ℝ)) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by
        intro a ha hnot
        positivity)
    _ = (∑ a ∈ Finset.Icc 1 ⌊L⌋₊, ((a ^ 2).divisors.card : ℝ) / (a : ℝ) ^ 2) +
        (harmonic ⌊L⌋₊ : ℝ) := by
      rw [Finset.sum_add_distrib]
      congr 1
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
    _ ≤ _ := by
      have h₁ := square_divisor_reciprocal_square_sum_le ⌊L⌋₊
      have h₂ := harmonic_floor_le_one_add_log L hL
      linarith

/-- `𝔐(L)/(log L)³ → κ_M/4`. -/
theorem localInteriorMass_cubic_limit (M aM u : ℕ)
    (hM : 0 < M) (ha : Nat.Coprime aM M) (hu : Nat.Coprime u M) :
    Filter.Tendsto (fun L : ℝ => localInteriorMass L M aM u / (Real.log L) ^ 3)
      Filter.atTop (nhds (localReciprocalMainCoefficient M / 4)) := by
  let B : ℝ := (Real.pi ^ 2 / 6) ^ 3
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hlim : Filter.Tendsto (fun L : ℝ => (B + 2) / Real.log L)
      Filter.atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul (B + 2)
  have herror : Filter.Tendsto (fun L : ℝ =>
      localInteriorMass L M aM u / (Real.log L) ^ 3 -
        (localReciprocalMass ⌊L⌋₊ M aM u / (Real.log L) ^ 3) / 4)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with L hL
    have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hL
    have hlog : 1 ≤ Real.log L := by
      have hh := Real.log_le_log (Real.exp_pos 1) hL
      simpa only [Real.log_exp] using hh
    have hlogp : 0 < Real.log L := by linarith
    have h := abs_localInteriorMass_sub_quarter_reciprocal_le M aM u hL1
    have hbound : |localInteriorMass L M aM u - localReciprocalMass ⌊L⌋₊ M aM u / 4| ≤
        (B + 2) * (Real.log L) ^ 2 := by
      change _ ≤ B + 1 + Real.log L at h
      have hs : 1 ≤ (Real.log L) ^ 2 := by nlinarith
      have hb := mul_le_mul_of_nonneg_left hs hB
      nlinarith
    rw [Real.norm_eq_abs]
    have he : localInteriorMass L M aM u / (Real.log L) ^ 3 -
        (localReciprocalMass ⌊L⌋₊ M aM u / (Real.log L) ^ 3) / 4 =
        (localInteriorMass L M aM u - localReciprocalMass ⌊L⌋₊ M aM u / 4) /
          (Real.log L) ^ 3 := by ring
    rw [he, abs_div, abs_of_pos (pow_pos hlogp 3)]
    calc
      _ ≤ ((B + 2) * (Real.log L) ^ 2) / (Real.log L) ^ 3 :=
        div_le_div_of_nonneg_right hbound (pow_nonneg hlogp.le _)
      _ = (B + 2) / Real.log L := by field_simp
  have hmain := (localReciprocalMass_real_cubic_limit M aM u hM ha hu).div_const 4
  have hh := herror.add hmain
  simpa only [sub_add_cancel, zero_add] using hh

/-- The estimate (10) of Proposition 4.3 for reduced `a_M` and `u`:
`|𝔐(L) - (κ_M/4) (log L)³| ≤ C (log L)²` for `L ≥ e`, with `C` depending only on `M`. -/
theorem localInteriorMass_cubic_remainder_uniform (M : ℕ) (hM : 0 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ aM u : ℕ, Nat.Coprime aM M → Nat.Coprime u M →
      ∀ L : ℝ, Real.exp 1 ≤ L →
      |localInteriorMass L M aM u -
        (localReciprocalMainCoefficient M / 4) * (Real.log L) ^ 3| ≤
        C * (Real.log L) ^ 2 := by
  let E := localReciprocalErrorConstant M + 3 * |localReciprocalMainCoefficient M|
  let B : ℝ := (Real.pi ^ 2 / 6) ^ 3
  have hE : 0 ≤ E := by
    have hh := localReciprocalErrorConstant_nonneg M
    dsimp [E]
    positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨E + B + 2, by positivity, ?_⟩
  intro aM u ha hu L hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hL
  have hlog : 1 ≤ Real.log L := by
    have hh := Real.log_le_log (Real.exp_pos 1) hL
    simpa only [Real.log_exp] using hh
  have hcor := abs_localInteriorMass_sub_quarter_reciprocal_le M aM u hL1
  have hcor' : |localInteriorMass L M aM u - localReciprocalMass ⌊L⌋₊ M aM u / 4| ≤
      (B + 2) * (Real.log L) ^ 2 := by
    change _ ≤ B + 1 + Real.log L at hcor
    have hs : 1 ≤ (Real.log L) ^ 2 := by nlinarith
    have hb := mul_le_mul_of_nonneg_left hs hB
    nlinarith
  have hrec := abs_localReciprocalMass_real_sub_main_le M aM u hM ha hu hL1
  change _ ≤ E * (1 + Real.log L) ^ 2 at hrec
  have hs := mul_le_mul_of_nonneg_left
    (show (1 + Real.log L) ^ 2 ≤ 4 * (Real.log L) ^ 2 by nlinarith) hE
  have hrec' : |localReciprocalMass ⌊L⌋₊ M aM u / 4 -
      (localReciprocalMainCoefficient M / 4) * (Real.log L) ^ 3| ≤
      E * (Real.log L) ^ 2 := by
    have he : localReciprocalMass ⌊L⌋₊ M aM u / 4 -
        (localReciprocalMainCoefficient M / 4) * (Real.log L) ^ 3 =
        (localReciprocalMass ⌊L⌋₊ M aM u -
          localReciprocalMainCoefficient M * (Real.log L) ^ 3) / 4 := by ring
    rw [he, abs_div]
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    calc
      _ ≤ E * (1 + Real.log L) ^ 2 := hrec
      _ ≤ E * (4 * (Real.log L) ^ 2) := hs
      _ = _ := by ring
  have ht := abs_add_le (localInteriorMass L M aM u - localReciprocalMass ⌊L⌋₊ M aM u / 4)
    (localReciprocalMass ⌊L⌋₊ M aM u / 4 -
      (localReciprocalMainCoefficient M / 4) * (Real.log L) ^ 3)
  have he : localInteriorMass L M aM u - localReciprocalMass ⌊L⌋₊ M aM u / 4 +
      (localReciprocalMass ⌊L⌋₊ M aM u / 4 -
        (localReciprocalMainCoefficient M / 4) * (Real.log L) ^ 3) =
      localInteriorMass L M aM u -
        (localReciprocalMainCoefficient M / 4) * (Real.log L) ^ 3 := by ring
  rw [he] at ht
  nlinarith only [ht, hcor', hrec']

end

end ErdosStraus.DivisorEstimates
