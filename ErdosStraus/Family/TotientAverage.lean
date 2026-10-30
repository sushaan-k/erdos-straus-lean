import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.NumberTheory.Bertrand
import ErdosStraus.Estimates.RoughProducts
import ErdosStraus.Family.ExactDivisors
import ErdosStraus.Family.TotientExpansion
import ErdosStraus.Estimates.TotientSums
import ErdosStraus.Estimates.SquarefreeCounts

/-!
# Lemma 6.1: average of `1/φ` in progressions

Let `U₀ = Y₀/s`, `U₁ = H/s²` and `L_s = log(U₁/U₀)`. For squarefree odd `d ≤ U`,
`(a, d) = 1` and squarefree `s ≤ S₀` with `(s, m) = (sm, d) = 1`, the sum of `1/φ(r)` over
squarefree `r ∈ (U₀, U₁]` with `(r, sm) = 1` and `r ≡ a (mod d)` is
`≍_m (1/d)(φ(s)/s) L_s`, uniformly in all these parameters. With `M = s rad(m)`, the lower
bound comes from the Möbius calculation of Lemma 3.2 and the upper bound from (18),
also proved here; both error terms are `o((1/d)(φ(s)/s) L_s)` because `3η < λ`.
-/

/-! ## The sums `∑ 1/φ(m s r)` -/

namespace ErdosStraus.FixedNumeratorFamily

open Classical Filter
open scoped BigOperators

/-- The radical `rad(m) = ∏_{p ∣ m} p`. -/
noncomputable def numeratorRadical (m : ℕ) : ℕ := ∏ p ∈ m.primeFactors, p

theorem numeratorRadical_pos (m : ℕ) : 0 < numeratorRadical m := by
  unfold numeratorRadical
  exact Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)

theorem numeratorRadical_dvd (m : ℕ) : numeratorRadical m ∣ m := Nat.prod_primeFactors_dvd m

theorem numeratorRadical_primeFactors (m : ℕ) :
    (numeratorRadical m).primeFactors = m.primeFactors := by
  unfold numeratorRadical
  exact Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors hp)

theorem numeratorRadical_squarefree (m : ℕ) : Squarefree (numeratorRadical m) := by
  have hprod : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → Squarefree (∏ p ∈ S, p) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert p S hp ih =>
      intro hprime
      rw [Finset.prod_insert hp]
      have hcop : Nat.Coprime p (∏ q ∈ S, q) := Nat.Coprime.prod_right (by
        intro q hq
        exact (Nat.coprime_primes (hprime p (Finset.mem_insert_self _ _))
          (hprime q (Finset.mem_insert_of_mem hq))).mpr
            (by intro heq; exact hp (heq ▸ hq)))
      apply (Nat.squarefree_mul hcop).mpr
      exact ⟨(Nat.prime_iff.mp (hprime p (Finset.mem_insert_self _ _))).squarefree,
        ih (fun q hq => hprime q (Finset.mem_insert_of_mem hq))⟩
  exact hprod m.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)

theorem coprime_numeratorRadical_iff {m n : ℕ} (hm : 0 < m) :
    Nat.Coprime n (numeratorRadical m) ↔ Nat.Coprime n m := by
  constructor
  · intro h
    exact Estimates.coprime_of_primeFactors_subset_right hm.ne'
      (by rw [numeratorRadical_primeFactors]) h
  · intro h
    exact h.coprime_dvd_right (numeratorRadical_dvd m)

/-- The squarefree `r ∈ (U₀, U₁]` with `(r, s m) = 1` and `r ≡ a (mod d)`. -/
noncomputable def numeratorRRange (m : ℕ) (P : Params) (X : ℝ) (d a s : ℕ) : Finset ℕ :=
  (Estimates.natWindow (phiProgressionU0 P s X) (phiProgressionU1 P s X)).filter
    (fun r => Squarefree r ∧ Nat.Coprime r (s * m) ∧ Estimates.congMod r a d)

/-- The sum `∑ 1/φ(m s r)` over `numeratorRRange m P X d a s`. -/
noncomputable def numeratorPhiAverage (m : ℕ) (P : Params) (X : ℝ) (d a s : ℕ) : ℝ :=
  ∑ r ∈ numeratorRRange m P X d a s, (1 : ℝ) / Nat.totient (m * s * r)

theorem numeratorPhiAverage_eq_normalized (m : ℕ) (P : Params) (X : ℝ) (d a s : ℕ)
    (hsm : Nat.Coprime s m) :
    numeratorPhiAverage m P X d a s =
      (1 / ((Nat.totient m : ℝ) * Nat.totient s)) *
        ∑ r ∈ numeratorRRange m P X d a s, (1 : ℝ) / Nat.totient r := by
  unfold numeratorPhiAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hcop := (Finset.mem_filter.mp hr).2.2.1
  have hmsr : Nat.Coprime (m * s) r := by simpa [Nat.mul_comm] using hcop.symm
  rw [Nat.totient_mul hmsr, Nat.totient_mul hsm.symm]
  push_cast
  ring

/-- Lower bound of Lemma 6.1 in the form `∑_r 1/φ(m s r) ≫_m L_s/(s d)`, uniformly in
`s`, `d` and the reduced residue `a`. -/
theorem numeratorPhiAverage_lower (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ, 0 < d → Squarefree d → (d : ℝ) ≤ UScale X → Nat.Coprime a d →
        1 ≤ s → Squarefree s → (s : ℝ) ≤ SScale P X → Nat.Coprime s m →
        Nat.Coprime (s * m) d →
        c * (slantLogLength P s X / ((s : ℝ) * d)) ≤ numeratorPhiAverage m P X d a s := by
  let R := numeratorRadical m
  have hR : 0 < R := numeratorRadical_pos m
  have hφm : (0 : ℝ) < Nat.totient m := by exact_mod_cast Nat.totient_pos.mpr hm
  have hφR : (0 : ℝ) < Nat.totient R := by exact_mod_cast Nat.totient_pos.mpr hR
  obtain ⟨c₀, Xbase, hc₀, hbound⟩ :=
    Estimates.ordinary_squarefree_progression_coprime_density_lower_long
      (P.lam - P.η) P.θ (P.θ - P.lam - P.η) (P.η + 1)
      (by linarith [P.η_add_σ_lt_lam, P.σ_pos]) (by linarith [P.lam_add_η_lt_θ])
  let c : ℝ := c₀ * (Nat.totient R : ℝ) / ((R : ℝ) * Nat.totient m)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, max (max Xbase (R : ℝ)) (Real.exp 1), hc, ?_⟩
  intro X hX d a s hd hdsq hdU ha hs hssq hsS hsm hsmd
  have hXe : Real.exp 1 ≤ X := (le_max_right _ _).trans hX
  have hX1 : 1 < X := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hXe
  have hXp : 0 < X := zero_lt_one.trans hX1
  have hXbase : Xbase ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hRX : (R : ℝ) ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  have hspos : 0 < s := hs
  have hsR : (0 : ℝ) < s := by exact_mod_cast hspos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have hφs : (0 : ℝ) < Nat.totient s := by exact_mod_cast Nat.totient_pos.mpr hspos
  have hsRad : Nat.Coprime s R := hsm.coprime_dvd_right (numeratorRadical_dvd m)
  have hsRsq : Squarefree (s * R) := (Nat.squarefree_mul hsRad).mpr
    ⟨hssq, numeratorRadical_squarefree m⟩
  have hsRd : Nat.Coprime (s * R) d := hsmd.coprime_dvd_left
    (Nat.mul_dvd_mul_left s (numeratorRadical_dvd m))
  have hMscale : ((s * R : ℕ) : ℝ) ≤ X ^ (P.η + 1) := by
    rw [Real.rpow_add hXp, Real.rpow_one]
    exact_mod_cast mul_le_mul hsS hRX (Nat.cast_nonneg R)
      (Real.rpow_nonneg hXp.le P.η)
  have hU0 := phiProgressionU0_ge_rpow_lam_sub_eta P hX1.le hs hsS
  have hU1 := phiProgressionU1_le_rpow_theta P hXp hs
  have hU01 := phiProgressionU0_lt_U1_of_s_le_SScale P hX1 hs hsS
  have hU01one := (one_le_phiProgressionU0 P hX1.le hs hsS).trans hU01.le
  have hratio := phiProgression_ratio_ge_rpow_theta_sub_lam_sub_eta P hX1.le hs hsS
  have hbare := hbound X hXbase (s * R) d a hd hsRsq hdsq hsRd ha hMscale hdU
    _ _ hU0 hU01 hU01one hU1 hratio
  have hcop (r : ℕ) : Nat.Coprime r (s * R) ↔ Nat.Coprime r (s * m) := by
    simp only [Nat.coprime_mul_iff_right, coprime_numeratorRadical_iff hm, R]
  have hbareEq : Estimates.sqfRecip X (s * R) d a (phiProgressionU0 P s X)
      (phiProgressionU1 P s X) =
        ∑ r ∈ numeratorRRange m P X d a s, (1 : ℝ) / (r : ℝ) := by
    unfold Estimates.sqfRecip numeratorRRange
    simp_rw [hcop]
  rw [hbareEq, Nat.totient_mul hsRad, Nat.cast_mul,
    log_phiProgressionU1_div_U0_eq_slantLogLength P hXp hspos] at hbare
  have hweight : (∑ r ∈ numeratorRRange m P X d a s, (1 : ℝ) / (r : ℝ)) ≤
      ∑ r ∈ numeratorRRange m P X d a s, (1 : ℝ) / Nat.totient r := by
    apply Finset.sum_le_sum
    intro r hr
    have hrsq := (Finset.mem_filter.mp hr).2.1
    have hrpos : 0 < r := Nat.pos_of_ne_zero hrsq.ne_zero
    apply one_div_le_one_div_of_le (by exact_mod_cast Nat.totient_pos.mpr hrpos)
    exact_mod_cast Nat.totient_le r
  have hnorm := mul_le_mul_of_nonneg_left (hbare.trans hweight)
    (show 0 ≤ 1 / ((Nat.totient m : ℝ) * Nat.totient s) by positivity)
  rw [← numeratorPhiAverage_eq_normalized m P X d a s hsm] at hnorm
  apply le_trans _ hnorm
  apply le_of_eq
  dsimp [c]
  push_cast
  field_simp

end ErdosStraus.FixedNumeratorFamily

namespace ErdosStraus.FixedNumeratorFamily

open Classical
open scoped BigOperators

/-- `∑_r 1/r ≫_m (φ(s)/s) L_s` over squarefree `r ∈ (U₀, U₁]` with `(r, s m) = 1`. -/
theorem numeratorReciprocalAverage_lower (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X → ∀ s : ℕ,
      1 ≤ s → Squarefree s → (s : ℝ) ≤ SScale P X → Nat.Coprime s m →
      c * ((Nat.totient s : ℝ) / s) * slantLogLength P s X ≤
        ∑ r ∈ numeratorRRange m P X 1 0 s, (1 : ℝ) / r := by
  let R := numeratorRadical m
  have hR : 0 < R := numeratorRadical_pos m
  have hφR : (0 : ℝ) < Nat.totient R := by exact_mod_cast Nat.totient_pos.mpr hR
  obtain ⟨c₀, Xbase, hc₀, hbound⟩ :=
    Estimates.ordinary_squarefree_progression_coprime_density_lower_long
      (P.lam - P.η) P.θ (P.θ - P.lam - P.η) (P.η + 1)
      (by linarith [P.η_add_σ_lt_lam, P.σ_pos]) (by linarith [P.lam_add_η_lt_θ])
  refine ⟨c₀ * (Nat.totient R : ℝ) / R,
    max (max Xbase (R : ℝ)) (Real.exp 1), by positivity, ?_⟩
  intro X hX s hs hssq hsS hsm
  have hXe : Real.exp 1 ≤ X := (le_max_right _ _).trans hX
  have hX1 : 1 < X := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hXe
  have hXp : 0 < X := zero_lt_one.trans hX1
  have hXbase : Xbase ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hRX : (R : ℝ) ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  have hsRad : Nat.Coprime s R := hsm.coprime_dvd_right (numeratorRadical_dvd m)
  have hsRsq : Squarefree (s * R) := (Nat.squarefree_mul hsRad).mpr
    ⟨hssq, numeratorRadical_squarefree m⟩
  have hMscale : ((s * R : ℕ) : ℝ) ≤ X ^ (P.η + 1) := by
    rw [Real.rpow_add hXp, Real.rpow_one]
    exact_mod_cast mul_le_mul hsS hRX (Nat.cast_nonneg R)
      (Real.rpow_nonneg hXp.le P.η)
  have hU0 := phiProgressionU0_ge_rpow_lam_sub_eta P hX1.le hs hsS
  have hU1 := phiProgressionU1_le_rpow_theta P hXp hs
  have hU01 := phiProgressionU0_lt_U1_of_s_le_SScale P hX1 hs hsS
  have hU01one := (one_le_phiProgressionU0 P hX1.le hs hsS).trans hU01.le
  have hratio := phiProgression_ratio_ge_rpow_theta_sub_lam_sub_eta P hX1.le hs hsS
  have hdU : (1 : ℝ) ≤ UScale X := by
    unfold UScale
    exact one_le_pow₀ ((Real.le_log_iff_exp_le hXp).mpr hXe)
  have hbare := hbound X hXbase (s * R) 1 0 (by norm_num) hsRsq
    (by norm_num) (Nat.coprime_one_right _) (Nat.coprime_one_right _)
    hMscale (by simpa using hdU)
    _ _ hU0 hU01 hU01one hU1 hratio
  have hcop (r : ℕ) : Nat.Coprime r (s * R) ↔ Nat.Coprime r (s * m) := by
    simp only [Nat.coprime_mul_iff_right, coprime_numeratorRadical_iff hm, R]
  have heq : Estimates.sqfRecip X (s * R) 1 0 (phiProgressionU0 P s X)
      (phiProgressionU1 P s X) =
        ∑ r ∈ numeratorRRange m P X 1 0 s, (1 : ℝ) / r := by
    unfold Estimates.sqfRecip numeratorRRange
    simp_rw [hcop]
  rw [heq, Nat.totient_mul hsRad, Nat.cast_mul,
    log_phiProgressionU1_div_U0_eq_slantLogLength P hXp hs] at hbare
  convert hbare using 1
  push_cast
  field_simp

end ErdosStraus.FixedNumeratorFamily

/-! ## Upper bound through `phiProgressionAverage` -/

namespace ErdosStraus.FixedNumeratorFamily

open scoped BigOperators

theorem numeratorPhiAverage_le_ordinary (m : ℕ) (P : Params) (X : ℝ) (d a s : ℕ)
    (hsm : Nat.Coprime s m) :
    numeratorPhiAverage m P X d a s ≤
      (1 / ((Nat.totient m : ℝ) * Nat.totient s)) * phiProgressionAverage P X d a s := by
  classical
  rw [numeratorPhiAverage_eq_normalized m P X d a s hsm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold phiProgressionAverage
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr
    obtain ⟨hrW, hrSq, hrCop, hrCong⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨hrW, hrSq, (Nat.coprime_mul_iff_right.mp hrCop).1, hrCong⟩
  · intro r hr hnot
    positivity

theorem numeratorPhiAverage_upper (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ, 0 < d → (d : ℝ) ≤ UScale X → Nat.Coprime a d →
        1 ≤ s → (s : ℝ) ≤ SScale P X → Nat.Coprime s d → Nat.Coprime s m →
        numeratorPhiAverage m P X d a s ≤
          C * (slantLogLength P s X / ((s : ℝ) * d)) := by
  obtain ⟨C, X₀, hC, hupper⟩ := ProgressionEstimates.phiProgressionAverage_small_upper P
  have hφm : (0 : ℝ) < Nat.totient m := by exact_mod_cast Nat.totient_pos.mpr hm
  refine ⟨C / Nat.totient m, X₀, div_pos hC hφm, ?_⟩
  intro X hX d a s hd hdU ha hs hsS hsd hsm
  have hφs : (Nat.totient s : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hs).ne'
  have hu := hupper X hX d a s hd hdU ha hs hsd hsS
  calc
    numeratorPhiAverage m P X d a s ≤
        (1 / ((Nat.totient m : ℝ) * Nat.totient s)) * phiProgressionAverage P X d a s :=
      numeratorPhiAverage_le_ordinary m P X d a s hsm
    _ ≤ (1 / ((Nat.totient m : ℝ) * Nat.totient s)) *
        (C * phiProgressionAverageShape P X d s) :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    _ = _ := by
      unfold phiProgressionAverageShape
      field_simp [hφm.ne', hφs]

end ErdosStraus.FixedNumeratorFamily

/-! ## The bound (18) -/

namespace ErdosStraus.ProgressionEstimates

open Classical Finset DivisorEstimates
open scoped BigOperators

theorem coprime_multiples_reciprocal (d a M k : ℕ) (hd : 0 < d) (hk : 0 < k)
    (hM : Squarefree M) (hdM : Nat.Coprime d M) (hkcop : Nat.Coprime k (d * M))
    {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    |(∑ n ∈ (((Estimates.natWindow A B).filter (fun n => n ≡ a [MOD d])).filter
        (fun n => Nat.Coprime n M)).filter (fun n => k ∣ n), (1 : ℝ) / n) -
      ((Nat.totient M : ℝ) / (M * d)) * Real.log (B / A) / k| ≤
      12 * (M.divisors.card : ℝ) / A := by
  have hkD := (Nat.coprime_mul_iff_right.mp hkcop).1
  have hkM := (Nat.coprime_mul_iff_right.mp hkcop).2
  have hqM : Nat.Coprime (d * k) M := (hdM.symm.mul_right hkM.symm).symm
  have hset : (((Estimates.natWindow A B).filter (fun n => n ≡ a [MOD d])).filter
        (fun n => Nat.Coprime n M)).filter (fun n => k ∣ n) =
      ((Estimates.natWindow A B).filter
        (fun n => n ≡ Nat.chineseRemainder hkD.symm a 0 [MOD d * k])).filter
        (fun n => Nat.Coprime n M) := by
    rw [PrimeEstimates.natWindow_eq_Ioc_floor hA.le]
    have he : Ioc ⌊A⌋₊ ⌊B⌋₊ = Ico (⌊A⌋₊ + 1) (⌊B⌋₊ + 1) := by
      ext n
      simp only [mem_Ioc, mem_Ico]
      omega
    rw [he, ← SieveEstimates.progression_multiples_eq_single_class
      (⌊A⌋₊ + 1) (⌊B⌋₊ + 1) d a k hkD.symm]
    ext n
    simp only [mem_filter]
    tauto
  rw [hset]
  have h := coprime_reciprocal_progression (d * k)
    (Nat.chineseRemainder hkD.symm a 0) M (Nat.mul_pos hd hk) hM hqM hA hAB
  rw [Nat.cast_mul] at h
  have he : ((Nat.totient M : ℝ) / (M * (d * k))) * Real.log (B / A) =
      ((Nat.totient M : ℝ) / (M * d)) * Real.log (B / A) / k := by
    ring
  rwa [he] at h

theorem coprime_multiples_empty (A B : ℝ) (d a M k : ℕ) (ha : Nat.Coprime a d)
    (hk : ¬Nat.Coprime k (d * M)) :
    (((Estimates.natWindow A B).filter (fun n => n ≡ a [MOD d])).filter
      (fun n => Nat.Coprime n M)).filter (fun n => k ∣ n) = ∅ := by
  apply filter_eq_empty_iff.mpr
  intro n hn hkn
  obtain ⟨hn, hnM⟩ := mem_filter.mp hn
  have hmod := (mem_filter.mp hn).2
  have hnD : Nat.Coprime n d := by
    rw [Nat.coprime_iff_gcd_eq_one, hmod.gcd_eq]
    exact ha
  exact hk (Nat.coprime_mul_iff_right.mpr
    ⟨hnD.coprime_dvd_left hkn, hnM.coprime_dvd_left hkn⟩)

/-- The expansion `1/φ(n) = n⁻¹ ∑_{k ∣ n} γ(k)`, summed over a progression. -/
theorem totient_reciprocal_divisor_sum {A B : ℝ} (d a M : ℕ) :
    (∑ n ∈ ((Estimates.natWindow A B).filter (fun n => n ≡ a [MOD d])).filter
      (fun n => Nat.Coprime n M), (1 : ℝ) / Nat.totient n) =
    ∑ k ∈ Icc 1 ⌊B⌋₊, gamma k *
      ∑ n ∈ (((Estimates.natWindow A B).filter (fun n => n ≡ a [MOD d])).filter
        (fun n => Nat.Coprime n M)).filter (fun n => k ∣ n), (1 : ℝ) / n := by
  let S := ((Estimates.natWindow A B).filter (fun n => n ≡ a [MOD d])).filter
    (fun n => Nat.Coprime n M)
  have he (n : ℕ) (hn : n ∈ S) : (1 : ℝ) / Nat.totient n =
      ∑ k ∈ Icc 1 ⌊B⌋₊, if k ∣ n then gamma k / n else 0 := by
    have hnI := (mem_filter.mp (mem_filter.mp hn).1).1
    have hn0 := (mem_Icc.mp (mem_filter.mp hnI).1).1
    have hnB := (mem_Icc.mp (mem_filter.mp hnI).1).2
    have hnpos : 0 < n := hn0
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hnpos.ne'
    have hdiv : (1 : ℝ) / Nat.totient n = (∑ k ∈ n.divisors, gamma k) / n := by
      rw [← gamma_divisor_sum n hn0]
      rw [div_right_comm, div_self hnR]
    rw [hdiv, sum_div]
    have hsub : n.divisors ⊆ Icc 1 ⌊B⌋₊ := fun k hk => mem_Icc.mpr
      ⟨Nat.pos_of_mem_divisors hk, (Nat.divisor_le hk).trans hnB⟩
    rw [← sum_subset hsub]
    · apply sum_congr rfl
      intro k hk
      rw [if_pos (Nat.dvd_of_mem_divisors hk)]
    · intro k _ hnot
      have hnd : ¬k ∣ n := fun h => hnot (Nat.mem_divisors.mpr ⟨h, hnpos.ne'⟩)
      exact if_neg hnd
  change (∑ n ∈ S, _) = _
  rw [sum_congr rfl he, sum_comm]
  apply sum_congr rfl
  intro k hk
  rw [← sum_filter]
  simp only [mul_sum]
  apply sum_congr rfl
  intro n hn
  ring

theorem totient_reciprocal_progression_error (d a M : ℕ) (hd : 0 < d)
    (ha : Nat.Coprime a d) (hM : Squarefree M) (hdM : Nat.Coprime d M)
    {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    |(∑ n ∈ ((Estimates.natWindow A B).filter (fun n => n ≡ a [MOD d])).filter
        (fun n => Nat.Coprime n M), (1 : ℝ) / Nat.totient n) -
      (((Nat.totient M : ℝ) / (M * d)) * Real.log (B / A)) *
        ∑ k ∈ (Icc 1 ⌊B⌋₊).filter (fun k => Nat.Coprime k (d * M)), gamma k / k| ≤
      (12 * (M.divisors.card : ℝ) / A) * ∑ k ∈ Icc 1 ⌊B⌋₊, gamma k := by
  rw [totient_reciprocal_divisor_sum, sum_filter, mul_sum, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ k ∈ Icc 1 ⌊B⌋₊, (12 * (M.divisors.card : ℝ) / A) * gamma k := by
      apply sum_le_sum
      intro k hk
      by_cases hcop : Nat.Coprime k (d * M)
      · rw [if_pos hcop]
        have hi := coprime_multiples_reciprocal d a M k hd (mem_Icc.mp hk).1
          hM hdM hcop hA hAB
        have he : gamma k *
            (∑ n ∈ (((Estimates.natWindow A B).filter (fun n => n ≡ a [MOD d])).filter
              (fun n => Nat.Coprime n M)).filter (fun n => k ∣ n), (1 : ℝ) / n) -
            ((Nat.totient M : ℝ) / (M * d) * Real.log (B / A)) * (gamma k / k) =
            gamma k * ((∑ n ∈ (((Estimates.natWindow A B).filter (fun n => n ≡ a [MOD d])).filter
              (fun n => Nat.Coprime n M)).filter (fun n => k ∣ n), (1 : ℝ) / n) -
              ((Nat.totient M : ℝ) / (M * d)) * Real.log (B / A) / k) := by ring
        rw [he, abs_mul, abs_of_nonneg (gamma_nonneg k)]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hi (gamma_nonneg k)
      · rw [if_neg hcop, coprime_multiples_empty A B d a M k ha hcop]
        simp only [sum_empty, mul_zero, sub_zero, abs_zero]
        exact mul_nonneg (div_nonneg (by positivity) hA.le) (gamma_nonneg k)
    _ = _ := (mul_sum ..).symm

/-- (18): for `1 ≤ A < B`, squarefree `M` and `(a, d) = (d, M) = 1`,
`∑_{A<n≤B, n≡a (d), (n,M)=1} 1/φ(n) ≤ C_γ φ(M)/(Md) log(B/A) + 36 C_γ τ(M) log(2B)/A`. -/
theorem totient_reciprocal_progression_upper (d a M : ℕ) (hd : 0 < d)
    (ha : Nat.Coprime a d) (hM : Squarefree M) (hdM : Nat.Coprime d M)
    {A B : ℝ} (hA : 1 ≤ A) (hAB : A < B) :
    (∑ n ∈ ((Estimates.natWindow A B).filter (fun n => n ≡ a [MOD d])).filter
        (fun n => Nat.Coprime n M), (1 : ℝ) / Nat.totient n) ≤
      gammaConstant * ((Nat.totient M : ℝ) / (M * d)) * Real.log (B / A) +
        36 * gammaConstant * (M.divisors.card : ℝ) * Real.log (2 * B) / A := by
  have hAp : 0 < A := by linarith
  have hB : 1 ≤ B := hA.trans hAB.le
  have hmain : 0 ≤ ((Nat.totient M : ℝ) / (M * d)) * Real.log (B / A) := by
    apply mul_nonneg (by positivity)
    exact Real.log_nonneg ((one_le_div hAp).mpr hAB.le)
  have hcoeff : (∑ k ∈ (Icc 1 ⌊B⌋₊).filter (fun k => Nat.Coprime k (d * M)),
      gamma k / k) ≤ gammaConstant := by
    apply le_trans _ (gamma_div_sum_le ⌊B⌋₊)
    exact sum_le_sum_of_subset_of_nonneg (filter_subset ..)
      (fun k _ _ => div_nonneg (gamma_nonneg k) (Nat.cast_nonneg k))
  have hgamma : (∑ k ∈ Icc 1 ⌊B⌋₊, gamma k) ≤
      3 * gammaConstant * Real.log (2 * B) := by
    apply (gamma_sum_le _).trans
    convert mul_le_mul_of_nonneg_left (harmonic_floor_le_three_log B hB)
      gammaConstant_pos.le using 1
    ring
  have herr := (abs_le.mp (totient_reciprocal_progression_error d a M hd ha hM hdM hAp hAB)).2
  have hc := mul_le_mul_of_nonneg_left hcoeff hmain
  have hg := mul_le_mul_of_nonneg_left hgamma
    (show 0 ≤ 12 * (M.divisors.card : ℝ) / A by positivity)
  have he : (12 * (M.divisors.card : ℝ) / A) *
      (3 * gammaConstant * Real.log (2 * B)) =
      36 * gammaConstant * (M.divisors.card : ℝ) * Real.log (2 * B) / A := by ring
  rw [he] at hg
  nlinarith

end ErdosStraus.ProgressionEstimates

/-! ## Proof of Lemma 6.1 -/

namespace ErdosStraus.FixedNumeratorFamily

open Classical Filter
open scoped BigOperators

/-! ### Divisor count against totient for squarefree moduli -/

/-- For squarefree `s`, `φ(s) = ∏_{p ∣ s} (p - 1)`. -/
theorem totient_eq_prod_primeFactors_of_squarefree {s : ℕ} (hs : Squarefree s) :
    (Nat.totient s : ℝ) = ∏ p ∈ s.primeFactors, ((p : ℝ) - 1) := by
  have h := Nat.totient_mul_prod_primeFactors s
  rw [Nat.prod_primeFactors_of_squarefree hs] at h
  have h' : Nat.totient s = ∏ p ∈ s.primeFactors, (p - 1) :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hs.ne_zero) (h.trans (mul_comm _ _))
  rw [h', Nat.cast_prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]

/-- `τ(s)/φ(s) = ∏_{p ∣ s} 2/(p-1)` for squarefree `s`. -/
theorem divisor_card_div_totient_eq_prod {s : ℕ} (hs : Squarefree s) :
    (s.divisors.card : ℝ) / Nat.totient s =
      ∏ p ∈ s.primeFactors, (2 : ℝ) / ((p : ℝ) - 1) := by
  rw [ProgressionEstimates.squarefree_card_divisors hs,
    totient_eq_prod_primeFactors_of_squarefree hs, Finset.prod_div_distrib,
    Finset.prod_const]
  push_cast
  rfl

/-- Over a finite set of primes, `∏ 2/(p-1) ≤ 2`: only the factor at `p = 2` exceeds one. -/
theorem prod_two_div_pred_le_two (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∏ p ∈ S, (2 : ℝ) / ((p : ℝ) - 1) ≤ 2 := by
  have hle : ∏ p ∈ S, (2 : ℝ) / ((p : ℝ) - 1) ≤
      ∏ p ∈ S, (if p = 2 then (2 : ℝ) else 1) := by
    apply Finset.prod_le_prod
    · intro p hp
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
      exact div_nonneg (by norm_num) (by linarith)
    · intro p hp
      split_ifs with hp2
      · subst hp2
        norm_num
      · have h3 : (3 : ℝ) ≤ p := by
          have := (hS p hp).two_le
          exact_mod_cast (show 3 ≤ p by omega)
        rw [div_le_one (by linarith)]
        linarith
  refine hle.trans ?_
  rw [Finset.prod_ite_eq']
  split_ifs <;> norm_num

/-- `τ(s)/φ(s) ≤ 2` for squarefree `s`. -/
theorem divisor_card_div_totient_le_two {s : ℕ} (hs : Squarefree s) :
    (s.divisors.card : ℝ) / Nat.totient s ≤ 2 := by
  rw [divisor_card_div_totient_eq_prod hs]
  exact prod_two_div_pred_le_two _ fun p hp => Nat.prime_of_mem_primeFactors hp

/-- `τ(s) ≤ 2φ(s)` for squarefree `s`. -/
theorem divisor_card_le_two_mul_totient {s : ℕ} (hs : Squarefree s) :
    (s.divisors.card : ℝ) ≤ 2 * Nat.totient s := by
  have hφ : (0 : ℝ) < Nat.totient s := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hs.ne_zero)
  have h := divisor_card_div_totient_le_two hs
  rwa [div_le_iff₀ hφ] at h

/-! ### The conductor `M = s·rad(m)` -/

/-- `M = s·rad(m)` is squarefree when `s` is squarefree and `(s,m) = 1`. -/
theorem numeratorConductor_squarefree {m s : ℕ} (hs : Squarefree s) (hsm : Nat.Coprime s m) :
    Squarefree (s * numeratorRadical m) :=
  (Nat.squarefree_mul (hsm.coprime_dvd_right (numeratorRadical_dvd m))).mpr
    ⟨hs, numeratorRadical_squarefree m⟩

/-- `(M,d) = 1` when `(sm,d) = 1`. -/
theorem numeratorConductor_coprime {m s d : ℕ} (hsmd : Nat.Coprime (s * m) d) :
    Nat.Coprime (s * numeratorRadical m) d :=
  hsmd.coprime_dvd_left (Nat.mul_dvd_mul_left s (numeratorRadical_dvd m))

/-- `(r,M) = 1` if and only if `(r,sm) = 1`. -/
theorem coprime_numeratorConductor_iff {m s r : ℕ} (hm : 0 < m) :
    Nat.Coprime r (s * numeratorRadical m) ↔ Nat.Coprime r (s * m) := by
  simp only [Nat.coprime_mul_iff_right, coprime_numeratorRadical_iff hm]

/-- `τ(M) = τ(s)τ(rad m)`. -/
theorem numeratorConductor_divisor_card {m s : ℕ} (hsm : Nat.Coprime s m) :
    (s * numeratorRadical m).divisors.card =
      s.divisors.card * (numeratorRadical m).divisors.card :=
  Nat.Coprime.card_divisors_mul (hsm.coprime_dvd_right (numeratorRadical_dvd m))

/-- `φ(M)/M = (φ(s)/s)(φ(rad m)/rad m)`. -/
theorem numeratorConductor_totient_ratio {m s : ℕ} (hsm : Nat.Coprime s m) :
    (Nat.totient (s * numeratorRadical m) : ℝ) / ((s * numeratorRadical m : ℕ) : ℝ) =
      ((Nat.totient s : ℝ) / s) *
        ((Nat.totient (numeratorRadical m) : ℝ) / numeratorRadical m) := by
  rw [Nat.totient_mul (hsm.coprime_dvd_right (numeratorRadical_dvd m))]
  push_cast
  exact mul_div_mul_comm _ _ _ _

/-- `φ(rad m)/rad m > 0`. -/
theorem numeratorRadical_totient_ratio_pos (m : ℕ) :
    0 < (Nat.totient (numeratorRadical m) : ℝ) / numeratorRadical m := by
  have hR := numeratorRadical_pos m
  have hφ : (0 : ℝ) < Nat.totient (numeratorRadical m) := by
    exact_mod_cast Nat.totient_pos.mpr hR
  have hR' : (0 : ℝ) < numeratorRadical m := by exact_mod_cast hR
  exact div_pos hφ hR'

/-- `φ(M)/M ≍_m φ(s)/s`:
`(φ(rad m)/rad m)·(φ(s)/s) ≤ φ(M)/M ≤ φ(s)/s`. -/
theorem numeratorConductor_totient_ratio_bounds {m s : ℕ} (hsm : Nat.Coprime s m) :
    ((Nat.totient (numeratorRadical m) : ℝ) / numeratorRadical m) *
          ((Nat.totient s : ℝ) / s) ≤
        (Nat.totient (s * numeratorRadical m) : ℝ) / ((s * numeratorRadical m : ℕ) : ℝ) ∧
      (Nat.totient (s * numeratorRadical m) : ℝ) / ((s * numeratorRadical m : ℕ) : ℝ) ≤
        (Nat.totient s : ℝ) / s := by
  rw [numeratorConductor_totient_ratio hsm]
  have hR : (0 : ℝ) < numeratorRadical m := by exact_mod_cast numeratorRadical_pos m
  have hRle : (Nat.totient (numeratorRadical m) : ℝ) / numeratorRadical m ≤ 1 :=
    (div_le_one hR).mpr (by exact_mod_cast Nat.totient_le _)
  have hs : (0 : ℝ) ≤ (Nat.totient s : ℝ) / s := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  exact ⟨(mul_comm _ _).le, mul_le_of_le_one_right hs hRle⟩

/-! ### The two displays -/

/-- The squarefree summation set with `(r,M) = 1` is the one with `(r,sm) = 1`. -/
theorem numeratorWindow_squarefree_filter_eq (m s d a : ℕ) (hm : 0 < m) (A B : ℝ) :
    (((Estimates.natWindow A B).filter (fun n => n ≡ a [MOD d])).filter
        (fun n => Nat.Coprime n (s * numeratorRadical m))).filter Squarefree =
      (Estimates.natWindow A B).filter
        (fun r => Squarefree r ∧ Nat.Coprime r (s * m) ∧ Estimates.congMod r a d) := by
  ext r
  simp only [Finset.mem_filter, coprime_numeratorConductor_iff hm]
  constructor
  · rintro ⟨⟨⟨hw, hc⟩, hcop⟩, hsq⟩
    exact ⟨hw, hsq, hcop, hc⟩
  · rintro ⟨hw, hsq, hcop, hc⟩
    exact ⟨⟨⟨hw, hc⟩, hcop⟩, hsq⟩

/-- The progression summation set with `(r,M) = 1` is the one with `(r,sm) = 1`. -/
theorem numeratorWindow_filter_eq (m s d a : ℕ) (hm : 0 < m) (A B : ℝ) :
    ((Estimates.natWindow A B).filter (fun n => n ≡ a [MOD d])).filter
        (fun n => Nat.Coprime n (s * numeratorRadical m)) =
      (Estimates.natWindow A B).filter
        (fun r => Nat.Coprime r (s * m) ∧ Estimates.congMod r a d) := by
  ext r
  simp only [Finset.mem_filter, coprime_numeratorConductor_iff hm]
  constructor
  · rintro ⟨⟨hw, hc⟩, hcop⟩
    exact ⟨hw, hcop, hc⟩
  · rintro ⟨hw, hcop, hc⟩
    exact ⟨⟨hw, hc⟩, hcop⟩

/-- The lower display: for `1 ≤ A < B` and `M = s·rad(m)`,
`∑_{A<r≤B, r≡a (d), (r,sm)=1} μ²(r)/r = κ(M,d)φ(M)/(Md)·log(B/A) + O(τ(s)/√A)`,
with error at most `28 τ(rad m) τ(s)/√A`, uniformly in `d`, `a`, `s`. -/
theorem numerator_squarefree_reciprocal_error (m : ℕ) (hm : 0 < m) (d a s : ℕ) (hd : 0 < d)
    (ha : Nat.Coprime a d) (hs : Squarefree s) (hsm : Nat.Coprime s m)
    (hsmd : Nat.Coprime (s * m) d) {A B : ℝ} (hA : 1 ≤ A) (hAB : A < B) :
    |(∑ r ∈ (Estimates.natWindow A B).filter
          (fun r => Squarefree r ∧ Nat.Coprime r (s * m) ∧ Estimates.congMod r a d),
          (1 : ℝ) / r) -
        ProgressionEstimates.coprimeKappa (s * numeratorRadical m) d *
            (Nat.totient (s * numeratorRadical m) : ℝ) /
            (((s * numeratorRadical m : ℕ) : ℝ) * d) * Real.log (B / A)| ≤
      28 * ((numeratorRadical m).divisors.card : ℝ) * s.divisors.card / Real.sqrt A := by
  have h := ProgressionEstimates.coprime_squarefree_reciprocal_error d a
    (s * numeratorRadical m) hd ha (numeratorConductor_squarefree hs hsm)
    (numeratorConductor_coprime hsmd).symm hA hAB
  rw [numeratorWindow_squarefree_filter_eq m s d a hm, numeratorConductor_divisor_card hsm] at h
  refine h.trans_eq ?_
  push_cast
  ring

/-- (18) with `M = s·rad(m)`: for `1 ≤ A < B`,
`∑_{A<r≤B, r≡a (d), (r,sm)=1} 1/φ(r) ≤ C_γ φ(M)/(Md)·log(B/A) + 36 C_γ τ(rad m)τ(s) log(2B)/A`. -/
theorem numerator_totient_reciprocal_upper (m : ℕ) (hm : 0 < m) (d a s : ℕ) (hd : 0 < d)
    (ha : Nat.Coprime a d) (hs : Squarefree s) (hsm : Nat.Coprime s m)
    (hsmd : Nat.Coprime (s * m) d) {A B : ℝ} (hA : 1 ≤ A) (hAB : A < B) :
    (∑ r ∈ (Estimates.natWindow A B).filter
          (fun r => Nat.Coprime r (s * m) ∧ Estimates.congMod r a d),
          (1 : ℝ) / Nat.totient r) ≤
      DivisorEstimates.gammaConstant *
          ((Nat.totient (s * numeratorRadical m) : ℝ) /
            (((s * numeratorRadical m : ℕ) : ℝ) * d)) * Real.log (B / A) +
        36 * DivisorEstimates.gammaConstant * ((numeratorRadical m).divisors.card : ℝ) *
          s.divisors.card * Real.log (2 * B) / A := by
  have h := ProgressionEstimates.totient_reciprocal_progression_upper d a
    (s * numeratorRadical m) hd ha (numeratorConductor_squarefree hs hsm)
    (numeratorConductor_coprime hsmd).symm hA hAB
  rw [numeratorWindow_filter_eq m s d a hm, numeratorConductor_divisor_card hsm] at h
  refine h.trans_eq ?_
  push_cast
  ring

/-- Discarding squarefreeness only enlarges the sum of `1/φ(r)`. -/
theorem numerator_squarefree_totient_le (m s d a : ℕ) (A B : ℝ) :
    (∑ r ∈ (Estimates.natWindow A B).filter
          (fun r => Squarefree r ∧ Nat.Coprime r (s * m) ∧ Estimates.congMod r a d),
          (1 : ℝ) / Nat.totient r) ≤
      ∑ r ∈ (Estimates.natWindow A B).filter
          (fun r => Nat.Coprime r (s * m) ∧ Estimates.congMod r a d),
          (1 : ℝ) / Nat.totient r := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr
    obtain ⟨hw, _, hc, hcong⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨hw, hc, hcong⟩
  · intro r _ _
    positivity

/-! ### Scale comparisons -/

/-- `s/√U₀ ≤ X^{(3η-λ)/2}` for `s ≤ S₀ = X^η`. -/
theorem nat_div_sqrt_phiProgressionU0_le (P : Params) {X : ℝ} {s : ℕ} (hX : 1 ≤ X)
    (hs : 1 ≤ s) (hsS : (s : ℝ) ≤ SScale P X) :
    (s : ℝ) / Real.sqrt (phiProgressionU0 P s X) ≤ X ^ ((3 * P.η - P.lam) / 2) := by
  have hX0 : 0 < X := by linarith
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hY : 0 < X ^ P.lam := Real.rpow_pos_of_pos hX0 _
  have h3 : (s : ℝ) ^ 3 ≤ X ^ (3 * P.η) := by
    have h := pow_le_pow_left₀ hsR.le hsS 3
    have he : (SScale P X) ^ 3 = X ^ (3 * P.η) := by
      unfold SScale
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
      congr 1
      push_cast
      ring
    rwa [he] at h
  have hsq : (s : ℝ) ^ 2 / phiProgressionU0 P s X ≤ X ^ (3 * P.η - P.lam) := by
    unfold phiProgressionU0 Y0Scale
    rw [Real.rpow_sub hX0, div_div_eq_mul_div]
    calc (s : ℝ) ^ 2 * s / X ^ P.lam = (s : ℝ) ^ 3 / X ^ P.lam := by ring
      _ ≤ X ^ (3 * P.η) / X ^ P.lam := div_le_div_of_nonneg_right h3 hY.le
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_div (sq_nonneg (s : ℝ)), Real.sqrt_sq hsR.le,
    Real.sqrt_eq_rpow (X ^ (3 * P.η - P.lam)), ← Real.rpow_mul hX0.le, mul_one_div] at h

/-- `s/U₀ ≤ X^{2η-λ}` for `s ≤ S₀ = X^η`. -/
theorem nat_div_phiProgressionU0_le (P : Params) {X : ℝ} {s : ℕ} (hX : 1 ≤ X)
    (hs : 1 ≤ s) (hsS : (s : ℝ) ≤ SScale P X) :
    (s : ℝ) / phiProgressionU0 P s X ≤ X ^ (2 * P.η - P.lam) := by
  have hX0 : 0 < X := by linarith
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hY : 0 < X ^ P.lam := Real.rpow_pos_of_pos hX0 _
  have h2 : (s : ℝ) ^ 2 ≤ X ^ (2 * P.η) := by
    have h := pow_le_pow_left₀ hsR.le hsS 2
    have he : (SScale P X) ^ 2 = X ^ (2 * P.η) := by
      unfold SScale
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
      congr 1
      push_cast
      ring
    rwa [he] at h
  unfold phiProgressionU0 Y0Scale
  rw [Real.rpow_sub hX0, div_div_eq_mul_div]
  calc (s : ℝ) * s / X ^ P.lam = (s : ℝ) ^ 2 / X ^ P.lam := by ring
    _ ≤ X ^ (2 * P.η) / X ^ P.lam := div_le_div_of_nonneg_right h2 hY.le

/-- `log(2U₁) ≤ (1+θ) log X` for `X ≥ 2`. -/
theorem log_two_mul_phiProgressionU1_le (P : Params) {X : ℝ} {s : ℕ} (hX : 2 ≤ X)
    (hs : 1 ≤ s) :
    Real.log (2 * phiProgressionU1 P s X) ≤ (1 + P.θ) * Real.log X := by
  have hX0 : 0 < X := by linarith
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hU1 : 0 < phiProgressionU1 P s X := by
    unfold phiProgressionU1 HScale
    exact div_pos (Real.rpow_pos_of_pos hX0 _) (pow_pos hsR 2)
  rw [Real.log_mul (by norm_num) hU1.ne']
  have h1 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  have h2 : Real.log (phiProgressionU1 P s X) ≤ P.θ * Real.log X := by
    rw [← Real.log_rpow hX0]
    exact Real.log_le_log hU1 (phiProgressionU1_le_rpow_theta P hX0 hs)
  linarith

/-! ### Relative errors -/

/-- The lower error divided by `φ(s)L_s/(sd)` is `O_m(dX^{(3η-λ)/2}/log X)`, uniformly
in `d` and squarefree `s ≤ S₀`. -/
theorem numerator_lower_relative_error_rate (m : ℕ) (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → ∀ d s : ℕ, 0 < d → Squarefree s →
      (s : ℝ) ≤ SScale P X →
      (28 * ((numeratorRadical m).divisors.card : ℝ) * s.divisors.card /
          Real.sqrt (phiProgressionU0 P s X)) /
        ((Nat.totient s : ℝ) * slantLogLength P s X / ((s : ℝ) * d)) ≤
      C * ((d : ℝ) * X ^ ((3 * P.η - P.lam) / 2) / Real.log X) := by
  have hc₀ : 0 < P.θ - P.lam - P.η := by linarith [P.lam_add_η_lt_θ]
  have hτR : (0 : ℝ) < ((numeratorRadical m).divisors.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr
      ⟨1, Nat.one_mem_divisors.mpr (numeratorRadical_pos m).ne'⟩
  refine ⟨56 * ((numeratorRadical m).divisors.card : ℝ) / (P.θ - P.lam - P.η),
    Real.exp 1, div_pos (mul_pos (by norm_num) hτR) hc₀, ?_⟩
  intro X hX d s hd hs hsS
  have hX1 : 1 ≤ X := le_trans (Real.one_lt_exp_iff.mpr one_pos).le hX
  have hX0 : 0 < X := by linarith
  have hlog : 1 ≤ Real.log X := by rw [Real.le_log_iff_exp_le hX0]; exact hX
  have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs.ne_zero
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hφs : (0 : ℝ) < Nat.totient s := by exact_mod_cast Nat.totient_pos.mpr hs1
  have hL := slantLogLength_ge_theta_sub_lam_sub_eta_mul_log P hX1 hs1 hsS
  have hc₀log : 0 < (P.θ - P.lam - P.η) * Real.log X := mul_pos hc₀ (by linarith)
  have hLpos : 0 < slantLogLength P s X := lt_of_lt_of_le hc₀log hL
  have hN : 0 < (Nat.totient s : ℝ) * slantLogLength P s X / ((s : ℝ) * d) := by positivity
  rw [div_le_iff₀ hN]
  have hU0 : 0 < phiProgressionU0 P s X :=
    lt_of_lt_of_le one_pos (one_le_phiProgressionU0 P hX1 hs1 hsS)
  have hsqrt : 0 < Real.sqrt (phiProgressionU0 P s X) := Real.sqrt_pos.mpr hU0
  have hK := nat_div_sqrt_phiProgressionU0_le P hX1 hs1 hsS
  have hXa : 0 < X ^ ((3 * P.η - P.lam) / 2) := Real.rpow_pos_of_pos hX0 _
  have hinv : 1 / Real.sqrt (phiProgressionU0 P s X) ≤
      X ^ ((3 * P.η - P.lam) / 2) / s := by
    rw [div_le_div_iff₀ hsqrt hsR]
    have := (div_le_iff₀ hsqrt).mp hK
    linarith
  have hτs := divisor_card_le_two_mul_totient hs
  have hratio : 1 ≤ slantLogLength P s X / ((P.θ - P.lam - P.η) * Real.log X) :=
    (one_le_div hc₀log).mpr hL
  calc
    28 * ((numeratorRadical m).divisors.card : ℝ) * s.divisors.card /
          Real.sqrt (phiProgressionU0 P s X) =
        (28 * ((numeratorRadical m).divisors.card : ℝ)) * s.divisors.card *
          (1 / Real.sqrt (phiProgressionU0 P s X)) := by ring
    _ ≤ (28 * ((numeratorRadical m).divisors.card : ℝ)) * (2 * Nat.totient s) *
          (X ^ ((3 * P.η - P.lam) / 2) / s) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hτs (by positivity)) hinv
        (by positivity) (by positivity)
    _ = 56 * ((numeratorRadical m).divisors.card : ℝ) * Nat.totient s *
          X ^ ((3 * P.η - P.lam) / 2) / s := by ring
    _ ≤ 56 * ((numeratorRadical m).divisors.card : ℝ) * Nat.totient s *
          X ^ ((3 * P.η - P.lam) / 2) / s *
          (slantLogLength P s X / ((P.θ - P.lam - P.η) * Real.log X)) :=
      le_mul_of_one_le_right (by positivity) hratio
    _ = 56 * ((numeratorRadical m).divisors.card : ℝ) / (P.θ - P.lam - P.η) *
          ((d : ℝ) * X ^ ((3 * P.η - P.lam) / 2) / Real.log X) *
          ((Nat.totient s : ℝ) * slantLogLength P s X / ((s : ℝ) * d)) := by
      field_simp

/-- The upper error divided by `φ(s)L_s/(sd)` is `O_m(dX^{2η-λ})`, uniformly in `d`
and squarefree `s ≤ S₀`. -/
theorem numerator_upper_relative_error_rate (m : ℕ) (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → ∀ d s : ℕ, 0 < d → Squarefree s →
      (s : ℝ) ≤ SScale P X →
      (36 * DivisorEstimates.gammaConstant * ((numeratorRadical m).divisors.card : ℝ) *
          s.divisors.card * Real.log (2 * phiProgressionU1 P s X) /
          phiProgressionU0 P s X) /
        ((Nat.totient s : ℝ) * slantLogLength P s X / ((s : ℝ) * d)) ≤
      C * ((d : ℝ) * X ^ (2 * P.η - P.lam)) := by
  have hc₀ : 0 < P.θ - P.lam - P.η := by linarith [P.lam_add_η_lt_θ]
  have hτR : (0 : ℝ) < ((numeratorRadical m).divisors.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr
      ⟨1, Nat.one_mem_divisors.mpr (numeratorRadical_pos m).ne'⟩
  have hγ := DivisorEstimates.gammaConstant_pos
  have hθ : 0 < 1 + P.θ := by linarith [P.θ_pos]
  refine ⟨72 * DivisorEstimates.gammaConstant * ((numeratorRadical m).divisors.card : ℝ) *
      (1 + P.θ) / (P.θ - P.lam - P.η), Real.exp 1, by positivity, ?_⟩
  intro X hX d s hd hs hsS
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hX2 : 2 ≤ X := he2.trans hX
  have hX1 : 1 < X := by linarith
  have hX0 : 0 < X := by linarith
  have hlog : 1 ≤ Real.log X := by rw [Real.le_log_iff_exp_le hX0]; exact hX
  have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs.ne_zero
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hφs : (0 : ℝ) < Nat.totient s := by exact_mod_cast Nat.totient_pos.mpr hs1
  have hL := slantLogLength_ge_theta_sub_lam_sub_eta_mul_log P hX1.le hs1 hsS
  have hc₀log : 0 < (P.θ - P.lam - P.η) * Real.log X := mul_pos hc₀ (by linarith)
  have hLpos : 0 < slantLogLength P s X := lt_of_lt_of_le hc₀log hL
  have hN : 0 < (Nat.totient s : ℝ) * slantLogLength P s X / ((s : ℝ) * d) := by positivity
  rw [div_le_iff₀ hN]
  have hU0one := one_le_phiProgressionU0 P hX1.le hs1 hsS
  have hU0 : 0 < phiProgressionU0 P s X := lt_of_lt_of_le one_pos hU0one
  have hU01 := phiProgressionU0_lt_U1_of_s_le_SScale P hX1 hs1 hsS
  have hlog2U1 : 0 ≤ Real.log (2 * phiProgressionU1 P s X) :=
    Real.log_nonneg (by linarith)
  have hlogU1 := log_two_mul_phiProgressionU1_le P hX2 hs1
  have hK := nat_div_phiProgressionU0_le P hX1.le hs1 hsS
  have hXb : 0 < X ^ (2 * P.η - P.lam) := Real.rpow_pos_of_pos hX0 _
  have hinv : 1 / phiProgressionU0 P s X ≤ X ^ (2 * P.η - P.lam) / s := by
    rw [div_le_div_iff₀ hU0 hsR]
    have := (div_le_iff₀ hU0).mp hK
    linarith
  have hτs := divisor_card_le_two_mul_totient hs
  have hratio : 1 ≤ slantLogLength P s X / ((P.θ - P.lam - P.η) * Real.log X) :=
    (one_le_div hc₀log).mpr hL
  calc
    36 * DivisorEstimates.gammaConstant * ((numeratorRadical m).divisors.card : ℝ) *
          s.divisors.card * Real.log (2 * phiProgressionU1 P s X) /
          phiProgressionU0 P s X =
        (36 * DivisorEstimates.gammaConstant * ((numeratorRadical m).divisors.card : ℝ)) *
          s.divisors.card * Real.log (2 * phiProgressionU1 P s X) *
          (1 / phiProgressionU0 P s X) := by ring
    _ ≤ (36 * DivisorEstimates.gammaConstant * ((numeratorRadical m).divisors.card : ℝ)) *
          (2 * Nat.totient s) * ((1 + P.θ) * Real.log X) *
          (X ^ (2 * P.η - P.lam) / s) :=
      mul_le_mul
        (mul_le_mul (mul_le_mul_of_nonneg_left hτs (by positivity)) hlogU1 hlog2U1
          (by positivity))
        hinv (by positivity) (by positivity)
    _ = 72 * DivisorEstimates.gammaConstant * ((numeratorRadical m).divisors.card : ℝ) *
          (1 + P.θ) * Nat.totient s * Real.log X * X ^ (2 * P.η - P.lam) / s := by ring
    _ ≤ 72 * DivisorEstimates.gammaConstant * ((numeratorRadical m).divisors.card : ℝ) *
          (1 + P.θ) * Nat.totient s * Real.log X * X ^ (2 * P.η - P.lam) / s *
          (slantLogLength P s X / ((P.θ - P.lam - P.η) * Real.log X)) :=
      le_mul_of_one_le_right (by positivity) hratio
    _ = 72 * DivisorEstimates.gammaConstant * ((numeratorRadical m).divisors.card : ℝ) *
          (1 + P.θ) / (P.θ - P.lam - P.η) * ((d : ℝ) * X ^ (2 * P.η - P.lam)) *
          ((Nat.totient s : ℝ) * slantLogLength P s X / ((s : ℝ) * d)) := by
      field_simp

/-- Both relative errors tend to zero: for every `ε > 0`, eventually in `X`, uniformly
for `d ≤ U = (log X)^8` and squarefree `s ≤ S₀ = X^η`, each error divided by
`φ(s)L_s/(sd)` is at most `ε`. This uses `3η < λ`. -/
theorem numerator_relative_errors_vanish (m : ℕ) (P : Params) {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ d s : ℕ, 0 < d → (d : ℝ) ≤ UScale X → Squarefree s →
      (s : ℝ) ≤ SScale P X →
      (28 * ((numeratorRadical m).divisors.card : ℝ) * s.divisors.card /
            Real.sqrt (phiProgressionU0 P s X)) /
          ((Nat.totient s : ℝ) * slantLogLength P s X / ((s : ℝ) * d)) ≤ ε ∧
        (36 * DivisorEstimates.gammaConstant * ((numeratorRadical m).divisors.card : ℝ) *
            s.divisors.card * Real.log (2 * phiProgressionU1 P s X) /
            phiProgressionU0 P s X) /
          ((Nat.totient s : ℝ) * slantLogLength P s X / ((s : ℝ) * d)) ≤ ε := by
  obtain ⟨C₁, X₁, hC₁, h₁⟩ := numerator_lower_relative_error_rate m P
  obtain ⟨C₂, X₂, hC₂, h₂⟩ := numerator_upper_relative_error_rate m P
  have hκ : 0 < (P.lam - 3 * P.η) / 4 := by linarith [P.three_η_lt_lam]
  obtain ⟨X₃, hU⟩ := Estimates.eventually_UScale_le_rpow hκ
  have hdecay := tendsto_rpow_neg_atTop hκ
  obtain ⟨X₄, h₄⟩ := Filter.eventually_atTop.mp
    ((tendsto_order.1 hdecay).2 (ε / C₁) (div_pos hε hC₁))
  obtain ⟨X₅, h₅⟩ := Filter.eventually_atTop.mp
    ((tendsto_order.1 hdecay).2 (ε / C₂) (div_pos hε hC₂))
  refine ⟨max (max (max X₁ X₂) (max X₃ X₄)) (max X₅ (Real.exp 1)), ?_⟩
  intro X hX d s hd hdU hs hsS
  have hX₁ : X₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) hX)
  have hX₂ : X₂ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) hX)
  have hX₃ : X₃ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (le_max_left _ _) hX)
  have hX₄ : X₄ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_trans (le_max_left _ _) hX)
  have hX₅ : X₅ ≤ X := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX)
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX)
  have hX1 : 1 ≤ X := le_trans (Real.one_lt_exp_iff.mpr one_pos).le hXe
  have hX0 : 0 < X := by linarith
  have hlog : 1 ≤ Real.log X := by rw [Real.le_log_iff_exp_le hX0]; exact hXe
  have hdX : (d : ℝ) ≤ X ^ ((P.lam - 3 * P.η) / 4) := hdU.trans (hU X hX₃)
  have hpow₁ : X ^ ((P.lam - 3 * P.η) / 4) * X ^ ((3 * P.η - P.lam) / 2) =
      X ^ (-((P.lam - 3 * P.η) / 4)) := by
    rw [← Real.rpow_add hX0]
    congr 1
    ring
  have hpow₂ : X ^ ((P.lam - 3 * P.η) / 4) * X ^ (2 * P.η - P.lam) ≤
      X ^ (-((P.lam - 3 * P.η) / 4)) := by
    rw [← Real.rpow_add hX0]
    apply Real.rpow_le_rpow_of_exponent_le hX1
    linarith [P.three_η_lt_lam, P.η_pos]
  constructor
  · refine (h₁ X hX₁ d s hd hs hsS).trans ?_
    calc
      C₁ * ((d : ℝ) * X ^ ((3 * P.η - P.lam) / 2) / Real.log X) ≤
          C₁ * ((d : ℝ) * X ^ ((3 * P.η - P.lam) / 2)) :=
        mul_le_mul_of_nonneg_left
          (div_le_self (by positivity) hlog) hC₁.le
      _ ≤ C₁ * (X ^ ((P.lam - 3 * P.η) / 4) * X ^ ((3 * P.η - P.lam) / 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hdX (Real.rpow_pos_of_pos hX0 _).le) hC₁.le
      _ = C₁ * X ^ (-((P.lam - 3 * P.η) / 4)) := by rw [hpow₁]
      _ ≤ C₁ * (ε / C₁) := mul_le_mul_of_nonneg_left (h₄ X hX₄).le hC₁.le
      _ = ε := by field_simp
  · refine (h₂ X hX₂ d s hd hs hsS).trans ?_
    calc
      C₂ * ((d : ℝ) * X ^ (2 * P.η - P.lam)) ≤
          C₂ * (X ^ ((P.lam - 3 * P.η) / 4) * X ^ (2 * P.η - P.lam)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hdX (Real.rpow_pos_of_pos hX0 _).le) hC₂.le
      _ ≤ C₂ * X ^ (-((P.lam - 3 * P.η) / 4)) := mul_le_mul_of_nonneg_left hpow₂ hC₂.le
      _ ≤ C₂ * (ε / C₂) := mul_le_mul_of_nonneg_left (h₅ X hX₅).le hC₂.le
      _ = ε := by field_simp

/-! ### The two bounds of the lemma -/

/-- Lower bound of Lemma 6.1:
`∑_{U₀<r≤U₁, r squarefree, (r,sm)=1, r≡a (d)} 1/φ(r) ≫_m (1/d)(φ(s)/s) log(U₁/U₀)`,
uniformly for `d ≤ U`, `(a,d) = 1`, squarefree `s ≤ S₀`, `(s,m) = (sm,d) = 1`. -/
theorem reciprocalTotient_lower_printed (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ, 0 < d → (d : ℝ) ≤ UScale X → Nat.Coprime a d →
        Squarefree s → (s : ℝ) ≤ SScale P X → Nat.Coprime s m → Nat.Coprime (s * m) d →
        c * ((1 / (d : ℝ)) * ((Nat.totient s : ℝ) / s) *
            Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)) ≤
          ∑ r ∈ (Estimates.natWindow (phiProgressionU0 P s X) (phiProgressionU1 P s X)).filter
              (fun r => Squarefree r ∧ Nat.Coprime r (s * m) ∧ Estimates.congMod r a d),
            (1 : ℝ) / Nat.totient r := by
  have hρ := numeratorRadical_totient_ratio_pos m
  have hκ₀ : (0 : ℝ) < 1 / (Real.pi ^ 2 / 6) := by positivity
  obtain ⟨X₀, hvan⟩ := numerator_relative_errors_vanish m P
    (ε := 1 / (Real.pi ^ 2 / 6) *
      ((Nat.totient (numeratorRadical m) : ℝ) / numeratorRadical m) / 2) (by positivity)
  refine ⟨1 / (Real.pi ^ 2 / 6) *
      ((Nat.totient (numeratorRadical m) : ℝ) / numeratorRadical m) / 2,
    max X₀ (Real.exp 1), by positivity, ?_⟩
  intro X hX d a s hd hdU ha hs hsS hsm hsmd
  have hXe : Real.exp 1 ≤ X := (le_max_right _ _).trans hX
  have hX1 : 1 < X := (Real.one_lt_exp_iff.mpr one_pos).trans_le hXe
  have hX0 : 0 < X := zero_lt_one.trans hX1
  have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs.ne_zero
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hφs : (0 : ℝ) < Nat.totient s := by exact_mod_cast Nat.totient_pos.mpr hs1
  have hU0 := one_le_phiProgressionU0 P hX1.le hs1 hsS
  have hU01 := phiProgressionU0_lt_U1_of_s_le_SScale P hX1 hs1 hsS
  have hLeq := log_phiProgressionU1_div_U0_eq_slantLogLength P hX0 hs1
  have hLpos : 0 < slantLogLength P s X := by
    rw [← hLeq]
    exact Real.log_pos ((one_lt_div (by linarith)).mpr hU01)
  have hN : 0 < (Nat.totient s : ℝ) * slantLogLength P s X / ((s : ℝ) * d) := by positivity
  obtain ⟨hE1, -⟩ := hvan X ((le_max_left _ _).trans hX) d s hd hdU hs hsS
  rw [div_le_iff₀ hN] at hE1
  have h3 := numerator_squarefree_reciprocal_error m hm d a s hd ha hs hsm hsmd hU0 hU01
  rw [hLeq] at h3
  have hS1 := (abs_le.mp h3).1
  obtain ⟨hratio, -⟩ := numeratorConductor_totient_ratio_bounds hsm
  have hκ := (ProgressionEstimates.coprimeKappa_bounds (s * numeratorRadical m) d).1
  have hM : (0 : ℝ) ≤ (Nat.totient (s * numeratorRadical m) : ℝ) /
      ((s * numeratorRadical m : ℕ) : ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hmain : 1 / (Real.pi ^ 2 / 6) *
        ((Nat.totient (numeratorRadical m) : ℝ) / numeratorRadical m) *
        ((Nat.totient s : ℝ) * slantLogLength P s X / ((s : ℝ) * d)) ≤
      ProgressionEstimates.coprimeKappa (s * numeratorRadical m) d *
          (Nat.totient (s * numeratorRadical m) : ℝ) /
          (((s * numeratorRadical m : ℕ) : ℝ) * d) * slantLogLength P s X := by
    have hcoef : 1 / (Real.pi ^ 2 / 6) *
          (((Nat.totient (numeratorRadical m) : ℝ) / numeratorRadical m) *
            ((Nat.totient s : ℝ) / s) / d) ≤
        ProgressionEstimates.coprimeKappa (s * numeratorRadical m) d *
          ((Nat.totient (s * numeratorRadical m) : ℝ) /
            ((s * numeratorRadical m : ℕ) : ℝ) / d) :=
      mul_le_mul hκ (div_le_div_of_nonneg_right hratio hdR.le) (by positivity)
        (hκ₀.le.trans hκ)
    calc
      _ = 1 / (Real.pi ^ 2 / 6) *
            (((Nat.totient (numeratorRadical m) : ℝ) / numeratorRadical m) *
              ((Nat.totient s : ℝ) / s) / d) * slantLogLength P s X := by ring
      _ ≤ ProgressionEstimates.coprimeKappa (s * numeratorRadical m) d *
            ((Nat.totient (s * numeratorRadical m) : ℝ) /
              ((s * numeratorRadical m : ℕ) : ℝ) / d) * slantLogLength P s X :=
        mul_le_mul_of_nonneg_right hcoef hLpos.le
      _ = _ := by ring
  have hweight :
      (∑ r ∈ (Estimates.natWindow (phiProgressionU0 P s X) (phiProgressionU1 P s X)).filter
          (fun r => Squarefree r ∧ Nat.Coprime r (s * m) ∧ Estimates.congMod r a d),
          (1 : ℝ) / r) ≤
        ∑ r ∈ (Estimates.natWindow (phiProgressionU0 P s X) (phiProgressionU1 P s X)).filter
          (fun r => Squarefree r ∧ Nat.Coprime r (s * m) ∧ Estimates.congMod r a d),
          (1 : ℝ) / Nat.totient r := by
    apply Finset.sum_le_sum
    intro r hr
    have hrpos : 0 < r := Nat.pos_of_ne_zero (Finset.mem_filter.mp hr).2.1.ne_zero
    apply one_div_le_one_div_of_le (by exact_mod_cast Nat.totient_pos.mpr hrpos)
    exact_mod_cast Nat.totient_le r
  rw [hLeq]
  calc
    _ = 1 / (Real.pi ^ 2 / 6) *
          ((Nat.totient (numeratorRadical m) : ℝ) / numeratorRadical m) *
          ((Nat.totient s : ℝ) * slantLogLength P s X / ((s : ℝ) * d)) -
        1 / (Real.pi ^ 2 / 6) *
          ((Nat.totient (numeratorRadical m) : ℝ) / numeratorRadical m) / 2 *
          ((Nat.totient s : ℝ) * slantLogLength P s X / ((s : ℝ) * d)) := by ring
    _ ≤ _ := sub_le_sub hmain hE1
    _ ≤ _ := by linarith
    _ ≤ _ := hweight

/-- Upper bound of Lemma 6.1:
`∑_{U₀<r≤U₁, r squarefree, (r,sm)=1, r≡a (d)} 1/φ(r) ≪_m (1/d)(φ(s)/s) log(U₁/U₀)`,
uniformly for `d ≤ U`, `(a,d) = 1`, squarefree `s ≤ S₀`, `(s,m) = (sm,d) = 1`. -/
theorem reciprocalTotient_upper_printed (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ, 0 < d → (d : ℝ) ≤ UScale X → Nat.Coprime a d →
        Squarefree s → (s : ℝ) ≤ SScale P X → Nat.Coprime s m → Nat.Coprime (s * m) d →
        (∑ r ∈ (Estimates.natWindow (phiProgressionU0 P s X) (phiProgressionU1 P s X)).filter
            (fun r => Squarefree r ∧ Nat.Coprime r (s * m) ∧ Estimates.congMod r a d),
            (1 : ℝ) / Nat.totient r) ≤
          C * ((1 / (d : ℝ)) * ((Nat.totient s : ℝ) / s) *
            Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)) := by
  have hγ := DivisorEstimates.gammaConstant_pos
  obtain ⟨X₀, hvan⟩ := numerator_relative_errors_vanish m P (ε := 1) one_pos
  refine ⟨DivisorEstimates.gammaConstant + 1, max X₀ (Real.exp 1), by linarith, ?_⟩
  intro X hX d a s hd hdU ha hs hsS hsm hsmd
  have hXe : Real.exp 1 ≤ X := (le_max_right _ _).trans hX
  have hX1 : 1 < X := (Real.one_lt_exp_iff.mpr one_pos).trans_le hXe
  have hX0 : 0 < X := zero_lt_one.trans hX1
  have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs.ne_zero
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hφs : (0 : ℝ) < Nat.totient s := by exact_mod_cast Nat.totient_pos.mpr hs1
  have hU0 := one_le_phiProgressionU0 P hX1.le hs1 hsS
  have hU01 := phiProgressionU0_lt_U1_of_s_le_SScale P hX1 hs1 hsS
  have hLeq := log_phiProgressionU1_div_U0_eq_slantLogLength P hX0 hs1
  have hLpos : 0 < slantLogLength P s X := by
    rw [← hLeq]
    exact Real.log_pos ((one_lt_div (by linarith)).mpr hU01)
  have hN : 0 < (Nat.totient s : ℝ) * slantLogLength P s X / ((s : ℝ) * d) := by positivity
  obtain ⟨-, hE2⟩ := hvan X ((le_max_left _ _).trans hX) d s hd hdU hs hsS
  rw [div_le_iff₀ hN, one_mul] at hE2
  have h4 := numerator_totient_reciprocal_upper m hm d a s hd ha hs hsm hsmd hU0 hU01
  rw [hLeq] at h4
  have hsub := numerator_squarefree_totient_le m s d a
    (phiProgressionU0 P s X) (phiProgressionU1 P s X)
  obtain ⟨-, hratio⟩ := numeratorConductor_totient_ratio_bounds hsm
  have hmain : DivisorEstimates.gammaConstant *
        ((Nat.totient (s * numeratorRadical m) : ℝ) /
          (((s * numeratorRadical m : ℕ) : ℝ) * d)) * slantLogLength P s X ≤
      DivisorEstimates.gammaConstant *
        ((Nat.totient s : ℝ) * slantLogLength P s X / ((s : ℝ) * d)) := by
    calc
      _ = DivisorEstimates.gammaConstant *
            ((Nat.totient (s * numeratorRadical m) : ℝ) /
              ((s * numeratorRadical m : ℕ) : ℝ) * slantLogLength P s X / d) := by ring
      _ ≤ DivisorEstimates.gammaConstant *
            ((Nat.totient s : ℝ) / s * slantLogLength P s X / d) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hratio hLpos.le) hdR.le)
          hγ.le
      _ = _ := by ring
  rw [hLeq]
  calc
    _ ≤ _ := hsub
    _ ≤ _ := h4
    _ ≤ DivisorEstimates.gammaConstant *
          ((Nat.totient s : ℝ) * slantLogLength P s X / ((s : ℝ) * d)) +
        (Nat.totient s : ℝ) * slantLogLength P s X / ((s : ℝ) * d) := add_le_add hmain hE2
    _ = _ := by ring

/-- Lower bound `numeratorPhiAverage = ∑ 1/φ(msr) ≫_m L_s/(sd)`. -/
theorem numeratorPhiAverage_lower_printed (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ, 0 < d → (d : ℝ) ≤ UScale X → Nat.Coprime a d →
        Squarefree s → (s : ℝ) ≤ SScale P X → Nat.Coprime s m → Nat.Coprime (s * m) d →
        c * (slantLogLength P s X / ((s : ℝ) * d)) ≤ numeratorPhiAverage m P X d a s := by
  obtain ⟨c, X₀, hc, h⟩ := reciprocalTotient_lower_printed m hm P
  have hφm : (0 : ℝ) < Nat.totient m := by exact_mod_cast Nat.totient_pos.mpr hm
  refine ⟨c / Nat.totient m, max X₀ 1, div_pos hc hφm, ?_⟩
  intro X hX d a s hd hdU ha hs hsS hsm hsmd
  have hX0 : 0 < X := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hX)
  have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs.ne_zero
  have hφs : (0 : ℝ) < Nat.totient s := by exact_mod_cast Nat.totient_pos.mpr hs1
  have hb := h X ((le_max_left _ _).trans hX) d a s hd hdU ha hs hsS hsm hsmd
  rw [log_phiProgressionU1_div_U0_eq_slantLogLength P hX0 hs1] at hb
  rw [numeratorPhiAverage_eq_normalized m P X d a s hsm]
  have hn := mul_le_mul_of_nonneg_left hb
    (show (0 : ℝ) ≤ 1 / ((Nat.totient m : ℝ) * Nat.totient s) by positivity)
  refine le_trans (le_of_eq ?_) hn
  field_simp

/-- Upper bound `numeratorPhiAverage = ∑ 1/φ(msr) ≪_m L_s/(sd)`. -/
theorem numeratorPhiAverage_upper_printed (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ, 0 < d → (d : ℝ) ≤ UScale X → Nat.Coprime a d →
        Squarefree s → (s : ℝ) ≤ SScale P X → Nat.Coprime s m → Nat.Coprime (s * m) d →
        numeratorPhiAverage m P X d a s ≤ C * (slantLogLength P s X / ((s : ℝ) * d)) := by
  obtain ⟨C, X₀, hC, h⟩ := reciprocalTotient_upper_printed m hm P
  have hφm : (0 : ℝ) < Nat.totient m := by exact_mod_cast Nat.totient_pos.mpr hm
  refine ⟨C / Nat.totient m, max X₀ 1, div_pos hC hφm, ?_⟩
  intro X hX d a s hd hdU ha hs hsS hsm hsmd
  have hX0 : 0 < X := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hX)
  have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs.ne_zero
  have hφs : (0 : ℝ) < Nat.totient s := by exact_mod_cast Nat.totient_pos.mpr hs1
  have hb := h X ((le_max_left _ _).trans hX) d a s hd hdU ha hs hsS hsm hsmd
  rw [log_phiProgressionU1_div_U0_eq_slantLogLength P hX0 hs1] at hb
  rw [numeratorPhiAverage_eq_normalized m P X d a s hsm]
  have hn := mul_le_mul_of_nonneg_left hb
    (show (0 : ℝ) ≤ 1 / ((Nat.totient m : ℝ) * Nat.totient s) by positivity)
  refine le_trans hn (le_of_eq ?_)
  field_simp

/-- Lemma 6.1: for squarefree odd `d ≤ U`, `(a,d) = 1`, and squarefree `s ≤ S₀` with
`(s,m) = (sm,d) = 1`,
`∑_{U₀<r≤U₁, r squarefree, (r,sm)=1, r≡a (d)} 1/φ(r) ≍_m (1/d)(φ(s)/s) log(U₁/U₀)`. -/
theorem reciprocalTotient_asymp_printed (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ, Squarefree d → Odd d → (d : ℝ) ≤ UScale X → Nat.Coprime a d →
        Squarefree s → (s : ℝ) ≤ SScale P X → Nat.Coprime s m → Nat.Coprime (s * m) d →
        c * ((1 / (d : ℝ)) * ((Nat.totient s : ℝ) / s) *
            Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)) ≤
          (∑ r ∈ (Estimates.natWindow (phiProgressionU0 P s X) (phiProgressionU1 P s X)).filter
              (fun r => Squarefree r ∧ Nat.Coprime r (s * m) ∧ Estimates.congMod r a d),
            (1 : ℝ) / Nat.totient r) ∧
        (∑ r ∈ (Estimates.natWindow (phiProgressionU0 P s X) (phiProgressionU1 P s X)).filter
            (fun r => Squarefree r ∧ Nat.Coprime r (s * m) ∧ Estimates.congMod r a d),
            (1 : ℝ) / Nat.totient r) ≤
          C * ((1 / (d : ℝ)) * ((Nat.totient s : ℝ) / s) *
            Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)) := by
  obtain ⟨c, X₁, hc, hl⟩ := reciprocalTotient_lower_printed m hm P
  obtain ⟨C, X₂, hC, hu⟩ := reciprocalTotient_upper_printed m hm P
  refine ⟨c, C, max X₁ X₂, hc, hC, ?_⟩
  intro X hX d a s hd _hodd hdU ha hs hsS hsm hsmd
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  exact ⟨hl X ((le_max_left _ _).trans hX) d a s hd0 hdU ha hs hsS hsm hsmd,
    hu X ((le_max_right _ _).trans hX) d a s hd0 hdU ha hs hsS hsm hsmd⟩

/-- Lemma 6.1 for `numeratorPhiAverage = ∑ 1/φ(msr) = (φ(m)φ(s))⁻¹ ∑ 1/φ(r)`: under the
hypotheses of the lemma, `numeratorPhiAverage ≍_m L_s/(sd)`. -/
theorem numeratorPhiAverage_asymp_printed (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ, Squarefree d → Odd d → (d : ℝ) ≤ UScale X → Nat.Coprime a d →
        Squarefree s → (s : ℝ) ≤ SScale P X → Nat.Coprime s m → Nat.Coprime (s * m) d →
        c * (slantLogLength P s X / ((s : ℝ) * d)) ≤ numeratorPhiAverage m P X d a s ∧
          numeratorPhiAverage m P X d a s ≤ C * (slantLogLength P s X / ((s : ℝ) * d)) := by
  obtain ⟨c, X₁, hc, hl⟩ := numeratorPhiAverage_lower_printed m hm P
  obtain ⟨C, X₂, hC, hu⟩ := numeratorPhiAverage_upper_printed m hm P
  refine ⟨c, C, max X₁ X₂, hc, hC, ?_⟩
  intro X hX d a s hd _hodd hdU ha hs hsS hsm hsmd
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  exact ⟨hl X ((le_max_left _ _).trans hX) d a s hd0 hdU ha hs hsS hsm hsmd,
    hu X ((le_max_right _ _).trans hX) d a s hd0 hdU ha hs hsS hsm hsmd⟩

end ErdosStraus.FixedNumeratorFamily
