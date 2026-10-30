import ErdosStraus.Estimates.DivisorMoments
import ErdosStraus.Family.ExactDivisors

/-!
# Upper bounds for `∑ 1/φ(r)` in progressions

The expansion `1/φ(r) = r⁻¹ ∑_{k ∣ r} γ(k)` with `γ(k) = μ²(k)/φ(k) ≥ 0` gives the upper
bound (18), the upper half of Lemma 6.1, and the bound `≪ (log X)²/D` in the proof of
Theorem 6.3. The coefficients are nonnegative, so every divisor `k` is kept, also those with
`k > A`, where `(A, B]` is the range of summation.
-/

open scoped BigOperators

namespace ErdosStraus
namespace ProgressionEstimates

/-- The squarefree `n ∈ [1, N]`. -/
noncomputable def squarefreeRange (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter Squarefree

/-- For squarefree `n`, `γ(n) = 1/φ(n)`. -/
theorem phiGamma_eq_reciprocal_totient {n : ℕ} (hn : Squarefree n) :
    phiGamma n = (1 : ℝ) / Nat.totient n := by
  classical
  have hphi : Nat.totient n = ∏ p ∈ n.primeFactors, (p - 1) := by
    rw [Nat.totient_eq_div_primeFactors_mul, Nat.prod_primeFactors_of_squarefree hn,
      Nat.div_self (Nat.pos_of_ne_zero hn.ne_zero), one_mul]
  rw [phiGamma_eq_primeFactorProduct hn.ne_zero, hphi, Nat.cast_prod]
  simp only [one_div, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]

/-- For a set `S` of squarefree `n ≤ N`,
`∑_{n ∈ S} 1/φ(n) = ∑_{k ≤ N} (γ(k)/k) ∑_{n ∈ S, k ∣ n} 1/(n/k)`. -/
theorem reciprocal_totient_sum_eq_quotient_sum
    (S : Finset ℕ) (N : ℕ)
    (hS : ∀ n ∈ S, Squarefree n ∧ n ≤ N) :
    (∑ n ∈ S, (1 : ℝ) / Nat.totient n) =
      ∑ k ∈ squarefreeRange N, (phiGamma k / (k : ℝ)) *
        ∑ n ∈ S.filter (fun n => k ∣ n), (1 : ℝ) / ((n / k : ℕ) : ℝ) := by
  classical
  have hinner (n : ℕ) (hn : n ∈ S) :
      (1 : ℝ) / Nat.totient n =
        ∑ k ∈ squarefreeRange N,
          if k ∣ n then (phiGamma k / (k : ℝ)) /
            ((n / k : ℕ) : ℝ) else 0 := by
    rw [one_div_totient_eq_one_div_nat_mul_phiGamma_sum (hS n hn).1,
      Finset.mul_sum]
    have hsub : n.divisors ⊆ squarefreeRange N := by
      intro k hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨Nat.pos_of_mem_divisors hk, le_trans (Nat.divisor_le hk) (hS n hn).2⟩,
        (hS n hn).1.squarefree_of_dvd (Nat.dvd_of_mem_divisors hk)⟩
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro k hk
      have hdvd := Nat.dvd_of_mem_divisors hk
      rw [if_pos hdvd]
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hk).ne'
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (hS n hn).1.ne_zero
      have hsplit : (k : ℝ) * ((n / k : ℕ) : ℝ) = n := by
        exact_mod_cast Nat.mul_div_cancel' hdvd
      have hq0 : ((n / k : ℕ) : ℝ) ≠ 0 := by
        intro h
        rw [h, mul_zero] at hsplit
        exact hn0 hsplit.symm
      field_simp [hk0, hn0, hq0]
      linear_combination phiGamma k * hsplit
    · intro k hk hnot
      have hnd : ¬ k ∣ n := by
        intro hd
        exact hnot (Nat.mem_divisors.mpr ⟨hd, (hS n hn).1.ne_zero⟩)
      simp [hnd]
  calc
    (∑ n ∈ S, (1 : ℝ) / Nat.totient n) =
        ∑ n ∈ S, ∑ k ∈ squarefreeRange N,
          if k ∣ n then (phiGamma k / (k : ℝ)) /
            ((n / k : ℕ) : ℝ) else 0 := Finset.sum_congr rfl hinner
    _ = ∑ k ∈ squarefreeRange N, ∑ n ∈ S,
          if k ∣ n then (phiGamma k / (k : ℝ)) /
            ((n / k : ℕ) : ℝ) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      split_ifs <;> simp [div_eq_mul_inv]

/-- `n ↦ n/k` is injective on the multiples of `k`, so the quotient sum is a sum over
the image. -/
theorem quotient_sum_eq_image (S : Finset ℕ) {k : ℕ} :
    (∑ n ∈ S.filter (fun n => k ∣ n), (1 : ℝ) / ((n / k : ℕ) : ℝ)) =
      ∑ t ∈ (S.filter (fun n => k ∣ n)).image (fun n => n / k),
        (1 : ℝ) / (t : ℝ) := by
  classical
  rw [Finset.sum_image]
  intro n hn m hm hnm
  have hn' := Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2
  have hm' := Nat.mul_div_cancel' (Finset.mem_filter.mp hm).2
  rw [show n / k = m / k from hnm] at hn'
  exact hn'.symm.trans hm'

/-- For `S ⊆ [1, N]`, `∑_{n ∈ S, k ∣ n} 1/(n/k) ≤ H_N`. -/
theorem quotient_sum_le_harmonic (S : Finset ℕ) (N k : ℕ)
    (hk : 0 < k) (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    (∑ n ∈ S.filter (fun n => k ∣ n), (1 : ℝ) / ((n / k : ℕ) : ℝ)) ≤
      (harmonic N : ℝ) := by
  classical
  rw [quotient_sum_eq_image S, harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hnS, hdvd⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_Icc.mpr
      ⟨Nat.div_pos (Nat.le_of_dvd (hS n hnS).1 hdvd) hk,
        le_trans (Nat.div_le_self n k) (hS n hnS).2⟩
  · intro t ht _
    exact inv_nonneg.mpr (Nat.cast_nonneg t)

/-- `∑_{n ≤ N, n squarefree} 1/φ(n) ≤ (∑_{k ≤ N} γ(k)/k) H_N`. -/
theorem squarefree_reciprocal_totient_sum_le_harmonic (N : ℕ) :
    (∑ n ∈ squarefreeRange N, (1 : ℝ) / Nat.totient n) ≤
      phiGammaDivSum N * (harmonic N : ℝ) := by
  classical
  rw [reciprocal_totient_sum_eq_quotient_sum (squarefreeRange N) N (by
    intro n hn
    exact ⟨(Finset.mem_filter.mp hn).2,
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2⟩)]
  calc
    _ ≤ ∑ k ∈ squarefreeRange N, (phiGamma k / (k : ℝ)) * (harmonic N : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left
      · apply quotient_sum_le_harmonic
        · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
        · intro n hn
          exact Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
      · exact div_nonneg (phiGamma_nonneg k) (Nat.cast_nonneg k)
    _ = (∑ k ∈ squarefreeRange N, phiGamma k / (k : ℝ)) * (harmonic N : ℝ) :=
      (Finset.sum_mul ..).symm
    _ ≤ phiGammaDivSum N * (harmonic N : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Estimates.harmonic_nonneg_real N)
      unfold phiGammaDivSum squarefreeRange
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
        (fun k _ _ => div_nonneg (phiGamma_nonneg k) (Nat.cast_nonneg k))

/-- `∑_{k ≤ N} γ(k) ≤ (∑_{k ≤ N} γ(k)/k) H_N`. -/
theorem squarefree_gamma_sum_le_harmonic (N : ℕ) :
    (∑ k ∈ squarefreeRange N, phiGamma k) ≤
      phiGammaDivSum N * (harmonic N : ℝ) := by
  classical
  calc
    _ = ∑ n ∈ squarefreeRange N, (1 : ℝ) / Nat.totient n := by
      apply Finset.sum_congr rfl
      intro n hn
      exact phiGamma_eq_reciprocal_totient (Finset.mem_filter.mp hn).2
    _ ≤ _ := squarefree_reciprocal_totient_sum_le_harmonic N

/-- For `S ⊆ (A, B]` in a reduced class `a (mod d)` and every `k ≥ 1`,
`∑_{n ∈ S, k ∣ n} 1/(n/k) ≤ k/A + (1/d) log(B/A)`, also when `k > A`. -/
theorem quotient_progression_sum_le_log
    (S : Finset ℕ) {k d a : ℕ} {A B : ℝ}
    (hk : 0 < k) (hd : 0 < d) (ha : Nat.Coprime a d)
    (hA : 0 < A) (hAB : A < B)
    (hS : ∀ n ∈ S, A < (n : ℝ) ∧ (n : ℝ) ≤ B ∧ Estimates.congMod n a d) :
    (∑ n ∈ S.filter (fun n => k ∣ n), (1 : ℝ) / ((n / k : ℕ) : ℝ)) ≤
      (k : ℝ) / A + (1 / (d : ℝ)) * Real.log (B / A) := by
  classical
  let T := (S.filter (fun n => k ∣ n)).image (fun n => n / k)
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hlog : Real.log ((B / (k : ℝ)) / (A / (k : ℝ))) = Real.log (B / A) := by
    congr 1
    field_simp
  have hbound (b : ℕ) (hb : k * b ≡ 1 [MOD d]) :
      (∑ t ∈ T, (1 : ℝ) / (t : ℝ)) ≤
        (k : ℝ) / A + (1 / (d : ℝ)) * Real.log (B / A) := by
    have hraw := Estimates.finset_recip_cong_le_log d (a * b) hd
      (A / (k : ℝ)) (div_pos hA hkR) T (B / (k : ℝ))
      ((div_lt_div_iff_of_pos_right hkR).mpr hAB)
    have hsplit (n : ℕ) (hn : n ∈ S.filter (fun n => k ∣ n)) :
        (k : ℝ) * ((n / k : ℕ) : ℝ) = n := by
      exact_mod_cast Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2
    have hlo : ∀ t ∈ T, A / (k : ℝ) < (t : ℝ) := by
      intro t ht
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
      rw [div_lt_iff₀ hkR]
      simpa [mul_comm, hsplit n hn] using (hS n (Finset.mem_filter.mp hn).1).1
    have hhi : ∀ t ∈ T, (t : ℝ) ≤ B / (k : ℝ) := by
      intro t ht
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
      rw [le_div_iff₀ hkR]
      simpa [mul_comm, hsplit n hn] using (hS n (Finset.mem_filter.mp hn).1).2.1
    have hcong : ∀ t ∈ T, Estimates.congMod t (a * b) d := by
      intro t ht
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
      have hmul : k * (n / k) ≡ a [MOD d] := by
        rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2]
        exact (hS n (Finset.mem_filter.mp hn).1).2.2
      have hright := hmul.mul_right b
      have hleft := hb.mul_right (n / k)
      apply Nat.ModEq.trans (show n / k ≡ (k * b) * (n / k) [MOD d] from ?_) ?_
      · simpa [Nat.mul_assoc] using hleft.symm
      · simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hright
    have hfinal := hraw hlo hhi hcong
    rw [hlog] at hfinal
    convert hfinal using 1
    field_simp
  rw [quotient_sum_eq_image S]
  by_cases hT : T.Nonempty
  · obtain ⟨t, ht⟩ := hT
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
    have hnd : Nat.Coprime n d := by
      rw [Nat.coprime_iff_gcd_eq_one,
        (show n ≡ a [MOD d] from (hS n (Finset.mem_filter.mp hn).1).2.2).gcd_eq]
      exact ha
    have hkd := hnd.coprime_dvd_left (Finset.mem_filter.mp hn).2
    by_cases hd1 : d = 1
    · subst d
      exact hbound 0 (by simp [Nat.ModEq])
    · have hd2 : 1 < d := by omega
      obtain ⟨b, -, hb⟩ := Nat.exists_mul_mod_eq_one_of_coprime hkd hd2
      apply hbound b
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt hd2] using hb
  · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    change (∑ t ∈ T, (1 : ℝ) / (t : ℝ)) ≤ _
    rw [he, Finset.sum_empty]
    apply add_nonneg
    · positivity
    · exact mul_nonneg (by positivity) (Real.log_nonneg ((one_le_div hA).mpr hAB.le))

/-- For a set `S` of squarefree `n ≤ N` in `(A, B]` with `n ≡ a (mod d)`, `(a,d) = 1`,
`∑_{n ∈ S} 1/φ(n) ≤ (∑_{k ≤ N} γ(k)/k)(H_N/A + (1/d) log(B/A))`. -/
theorem squarefree_reciprocal_totient_progression_le
    (S : Finset ℕ) (N d a : ℕ) {A B : ℝ}
    (hd : 0 < d) (ha : Nat.Coprime a d) (hA : 0 < A) (hAB : A < B)
    (hS : ∀ n ∈ S, Squarefree n ∧ n ≤ N ∧ A < (n : ℝ) ∧
      (n : ℝ) ≤ B ∧ Estimates.congMod n a d) :
    (∑ n ∈ S, (1 : ℝ) / Nat.totient n) ≤
      phiGammaDivSum N * ((harmonic N : ℝ) / A +
        (1 / (d : ℝ)) * Real.log (B / A)) := by
  classical
  rw [reciprocal_totient_sum_eq_quotient_sum S N (by
    intro n hn
    exact ⟨(hS n hn).1, (hS n hn).2.1⟩)]
  have hmain :
      (∑ k ∈ squarefreeRange N, phiGamma k / (k : ℝ)) ≤ phiGammaDivSum N := by
    unfold squarefreeRange phiGammaDivSum
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
      (fun k _ _ => div_nonneg (phiGamma_nonneg k) (Nat.cast_nonneg k))
  have hlog : 0 ≤ (1 / (d : ℝ)) * Real.log (B / A) :=
    mul_nonneg (by positivity) (Real.log_nonneg ((one_le_div hA).mpr hAB.le))
  calc
    _ ≤ ∑ k ∈ squarefreeRange N, (phiGamma k / (k : ℝ)) *
          ((k : ℝ) / A + (1 / (d : ℝ)) * Real.log (B / A)) := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left
      · exact quotient_progression_sum_le_log S
          (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1 hd ha hA hAB
          (fun n hn => (hS n hn).2.2)
      · exact div_nonneg (phiGamma_nonneg k) (Nat.cast_nonneg k)
    _ = (∑ k ∈ squarefreeRange N, phiGamma k) / A +
          (∑ k ∈ squarefreeRange N, phiGamma k / (k : ℝ)) *
            ((1 / (d : ℝ)) * Real.log (B / A)) := by
      rw [Finset.sum_div, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have hk0 : (k : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1)
      field_simp [hk0]
    _ ≤ (phiGammaDivSum N * (harmonic N : ℝ)) / A +
          phiGammaDivSum N * ((1 / (d : ℝ)) * Real.log (B / A)) :=
      add_le_add (div_le_div_of_nonneg_right (squarefree_gamma_sum_le_harmonic N) hA.le)
        (mul_le_mul_of_nonneg_right hmain hlog)
    _ = _ := by ring

/-- An absolute `C` with `∑_{n ∈ S} 1/φ(n) ≤ C((1 + log B)/A + (1/d) log(B/A))` for
every finite set `S` of squarefree `n ∈ (A, B]` with `n ≡ a (mod d)`, `(a,d) = 1`. -/
theorem exists_reciprocal_totient_progression_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ) (d a : ℕ) (A B : ℝ),
      0 < d → Nat.Coprime a d → 0 < A → A < B → 1 ≤ B →
      (∀ n ∈ S, Squarefree n ∧ A < (n : ℝ) ∧ (n : ℝ) ≤ B ∧
        Estimates.congMod n a d) →
      (∑ n ∈ S, (1 : ℝ) / Nat.totient n) ≤
        C * ((1 + Real.log B) / A + (1 / (d : ℝ)) * Real.log (B / A)) := by
  classical
  obtain ⟨C, hC, hbound⟩ := PhiGammaDivSummableBound_concrete
  refine ⟨C, hC, ?_⟩
  intro S d a A B hd ha hA hAB hB hS
  have hN : ∀ n ∈ S, Squarefree n ∧ n ≤ ⌊B⌋₊ ∧ A < (n : ℝ) ∧
      (n : ℝ) ≤ B ∧ Estimates.congMod n a d := by
    intro n hn
    exact ⟨(hS n hn).1, Nat.le_floor (hS n hn).2.2.1, (hS n hn).2⟩
  have hh := harmonic_floor_le_one_add_log B hB
  have hshape : 0 ≤ (harmonic ⌊B⌋₊ : ℝ) / A +
      (1 / (d : ℝ)) * Real.log (B / A) := by
    apply add_nonneg (div_nonneg (Estimates.harmonic_nonneg_real _) hA.le)
    exact mul_nonneg (by positivity) (Real.log_nonneg ((one_le_div hA).mpr hAB.le))
  calc
    _ ≤ phiGammaDivSum ⌊B⌋₊ * ((harmonic ⌊B⌋₊ : ℝ) / A +
          (1 / (d : ℝ)) * Real.log (B / A)) :=
      squarefree_reciprocal_totient_progression_le S ⌊B⌋₊ d a hd ha hA hAB hN
    _ ≤ C * ((harmonic ⌊B⌋₊ : ℝ) / A +
          (1 / (d : ℝ)) * Real.log (B / A)) :=
      mul_le_mul_of_nonneg_right (hbound _) hshape
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add_left (div_le_div_of_nonneg_right hh hA.le) _) hC.le

/-- `phiProgressionAverage ≤ C((1 + log U₁)/U₀ + (1/d) log(U₁/U₀))`; the modulus `d` need
not be squarefree or odd. -/
theorem phiProgressionAverage_le_main_add_error :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Params) (X : ℝ) (d a s : ℕ),
      0 < d → Nat.Coprime a d → 0 < phiProgressionU0 P s X →
      phiProgressionU0 P s X < phiProgressionU1 P s X →
      1 ≤ phiProgressionU1 P s X →
      phiProgressionAverage P X d a s ≤
        C * ((1 + Real.log (phiProgressionU1 P s X)) / phiProgressionU0 P s X +
          (1 / (d : ℝ)) *
            Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)) := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_reciprocal_totient_progression_constant
  refine ⟨C, hC, ?_⟩
  intro P X d a s hd ha hA hAB hB
  apply hbound _ d a _ _ hd ha hA hAB hB
  intro n hn
  obtain ⟨hnW, hnS, hnCop, hnCong⟩ := Finset.mem_filter.mp hn
  obtain ⟨hnI, hnA⟩ := Finset.mem_filter.mp hnW
  exact ⟨hnS, hnA, (Nat.le_floor_iff (by linarith)).mp
    (Finset.mem_Icc.mp hnI).2, hnCong⟩

/-- A form of (18): with the condition `(n, M) = 1`, splitting into the `φ(M)` classes
modulo `Md` gives the main term `C φ(M)/(Md) log(B/A)` and the error term
`C φ(M)(1 + log B)/A`. -/
theorem exists_coprime_reciprocal_totient_progression_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ) (M d a : ℕ) (A B : ℝ),
      0 < M → 0 < d → Nat.Coprime M d → Nat.Coprime a d →
      0 < A → A < B → 1 ≤ B →
      (∀ n ∈ S, Squarefree n ∧ A < (n : ℝ) ∧ (n : ℝ) ≤ B ∧
        Estimates.congMod n a d ∧ Nat.Coprime n M) →
      (∑ n ∈ S, (1 : ℝ) / Nat.totient n) ≤
        C * (Nat.totient M : ℝ) * ((1 + Real.log B) / A +
          (1 / ((M * d : ℕ) : ℝ)) * Real.log (B / A)) := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_reciprocal_totient_progression_constant
  refine ⟨C, hC, ?_⟩
  intro S M d a A B hM hd hMd ha hA hAB hB hS
  let R := Estimates.crtCoprimeProgressionResidues M d a
  let T : ℕ → Finset ℕ := fun b => S.filter (fun n => Estimates.congMod n b (M * d))
  have hcover : S ⊆ R.biUnion T := by
    intro n hn
    obtain ⟨b, hb, hnb⟩ := Estimates.crtCoprimeProgressionResidues_cover hM hd
      (hS n hn).2.2.2.2 (hS n hn).2.2.2.1
    exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_filter.mpr ⟨hn, hnb⟩⟩
  have hsum : (∑ n ∈ S, (1 : ℝ) / Nat.totient n) ≤
      ∑ b ∈ R, ∑ n ∈ T b, (1 : ℝ) / Nat.totient n := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg hcover (by
      intro n _ _
      positivity)).trans (Estimates.finset_sum_biUnion_le_sum R T _ (by
        intro b _ n _
        positivity))
  calc
    _ ≤ ∑ b ∈ R, ∑ n ∈ T b, (1 : ℝ) / Nat.totient n := hsum
    _ ≤ ∑ _b ∈ R, C * ((1 + Real.log B) / A +
          (1 / ((M * d : ℕ) : ℝ)) * Real.log (B / A)) := by
      apply Finset.sum_le_sum
      intro b hb
      have hbR := (Finset.mem_filter.mp hb).2
      have hbd : Nat.Coprime b d := Estimates.coprime_of_congMod_left hbR.2 ha
      apply hbound (T b) (M * d) b A B (Nat.mul_pos hM hd)
        (hbR.1.mul_right hbd) hA hAB hB
      intro n hn
      obtain ⟨hnS, hnCong⟩ := Finset.mem_filter.mp hn
      exact ⟨(hS n hnS).1, (hS n hnS).2.1, (hS n hnS).2.2.1, hnCong⟩
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul,
        show R.card = Nat.totient M from
          Estimates.crtCoprimeProgressionResidues_card_eq_totient hM hd hMd]
      ring

/-- If `sd ≤ U₀`, then `phiProgressionAverage ≪ (1/d)(φ(s)/s) L_s`, with a constant
depending only on the parameters. -/
theorem phiProgressionAverage_le_shape (P : Params) :
    ∃ K : ℝ, 0 < K ∧ ∀ (X : ℝ) (d a s : ℕ),
      Real.exp 1 ≤ X → 0 < d → Nat.Coprime a d → 1 ≤ s →
      Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
      ((s * d : ℕ) : ℝ) ≤ phiProgressionU0 P s X →
      phiProgressionAverage P X d a s ≤ K * phiProgressionAverageShape P X d s := by
  classical
  obtain ⟨C, hC, hupper⟩ := exists_coprime_reciprocal_totient_progression_constant
  let κ := P.θ - P.lam - P.η
  have hκ : 0 < κ := by dsimp [κ]; linarith [P.lam_add_η_lt_θ]
  refine ⟨C * (2 * P.θ + 1) / κ, div_pos (mul_pos hC (by linarith [P.θ_pos])) hκ, ?_⟩
  intro X d a s hXe hd ha hs hsd hsS hsdA
  have hX1 : 1 < X := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hXe
  have hXp : 0 < X := zero_lt_one.trans hX1
  have hsN : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hsN
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hsdR : (0 : ℝ) < ((s * d : ℕ) : ℝ) := by positivity
  have hA1 := one_le_phiProgressionU0 P hX1.le hs hsS
  have hA : 0 < phiProgressionU0 P s X := zero_lt_one.trans_le hA1
  have hAB := phiProgressionU0_lt_U1_of_s_le_SScale P hX1 hs hsS
  have hB1 : 1 ≤ phiProgressionU1 P s X := hA1.trans hAB.le
  have hlog1 : 1 ≤ Real.log X := (Real.le_log_iff_exp_le hXp).mpr hXe
  have hlogB : Real.log (phiProgressionU1 P s X) ≤ P.θ * Real.log X := by
    calc
      _ ≤ Real.log (X ^ P.θ) := Real.log_le_log
        (zero_lt_one.trans_le hB1) (phiProgressionU1_le_rpow_theta P hXp hs)
      _ = _ := Real.log_rpow hXp _
  have hlogBA : Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) ≤
      P.θ * Real.log X := by
    rw [log_phiProgressionU1_div_U0_eq_slantLogLength P hXp hsN]
    exact (slantLogLength_le_theta_sub_lam_mul_log P hX1.le hs).trans
      (by nlinarith [P.lam_pos])
  have hlogL : Real.log X ≤ slantLogLength P s X / κ := by
    rw [le_div_iff₀ hκ]
    simpa [κ, mul_comm] using
      slantLogLength_ge_theta_sub_lam_sub_eta_mul_log P hX1.le hs hsS
  have hraw : phiProgressionAverage P X d a s ≤ C * (Nat.totient s : ℝ) *
      ((1 + Real.log (phiProgressionU1 P s X)) / phiProgressionU0 P s X +
        (1 / ((s * d : ℕ) : ℝ)) *
          Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)) := by
    apply hupper _ s d a _ _ hsN hd hsd ha hA hAB hB1
    intro n hn
    obtain ⟨hnW, hnS, hnCop, hnCong⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnI, hnA⟩ := Finset.mem_filter.mp hnW
    exact ⟨hnS, hnA, (Nat.le_floor_iff (by linarith)).mp
      (Finset.mem_Icc.mp hnI).2, hnCong, hnCop⟩
  have hnum : 0 ≤ 1 + Real.log (phiProgressionU1 P s X) :=
    add_nonneg zero_le_one (Real.log_nonneg hB1)
  calc
    _ ≤ C * (Nat.totient s : ℝ) *
          ((1 + Real.log (phiProgressionU1 P s X)) / phiProgressionU0 P s X +
            (1 / ((s * d : ℕ) : ℝ)) *
              Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)) := hraw
    _ ≤ C * (Nat.totient s : ℝ) *
          (((P.θ + 1) * Real.log X) / ((s * d : ℕ) : ℝ) +
            (1 / ((s * d : ℕ) : ℝ)) * (P.θ * Real.log X)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Nat.cast_nonneg _))
      apply add_le_add
      · exact (div_le_div_of_nonneg_left hnum hsdR hsdA).trans
          (div_le_div_of_nonneg_right (by nlinarith) hsdR.le)
      · exact mul_le_mul_of_nonneg_left hlogBA (by positivity)
    _ = (C * (Nat.totient s : ℝ) * (2 * P.θ + 1) / ((s * d : ℕ) : ℝ)) *
          Real.log X := by ring
    _ ≤ (C * (Nat.totient s : ℝ) * (2 * P.θ + 1) / ((s * d : ℕ) : ℝ)) *
          (slantLogLength P s X / κ) := by
      exact mul_le_mul_of_nonneg_left hlogL
        (div_nonneg (mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg _))
          (by linarith [P.θ_pos])) hsdR.le)
    _ = _ := by
      unfold phiProgressionAverageShape
      rw [Nat.cast_mul]
      ring

/-- Eventually `sd ≤ U₀` for `d ≤ U` and `s ≤ S₀`; this uses `2η < λ`, which follows
from `3η < λ`. -/
theorem smallModulus_mul_le_phiProgressionU0 (P : Params) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ s d : ℕ,
      1 ≤ s → (s : ℝ) ≤ SScale P X → (d : ℝ) ≤ UScale X →
      ((s * d : ℕ) : ℝ) ≤ phiProgressionU0 P s X := by
  have hδ : 0 < P.lam - 2 * P.η := by linarith [P.three_η_lt_lam, P.η_pos]
  obtain ⟨XU, hU⟩ := Estimates.eventually_UScale_le_rpow hδ
  refine ⟨max XU (Real.exp 1), ?_⟩
  intro X hX s d hs hsS hdU
  have hXe : Real.exp 1 ≤ X := (le_max_right _ _).trans hX
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hXe
  have hX1 : 1 ≤ X := (by norm_num : (1 : ℝ) ≤ Real.exp 1).trans hXe
  calc
    ((s * d : ℕ) : ℝ) = (s : ℝ) * (d : ℝ) := Nat.cast_mul ..
    _ ≤ SScale P X * X ^ (P.lam - 2 * P.η) :=
      mul_le_mul hsS (hdU.trans (hU X ((le_max_left _ _).trans hX)))
        (Nat.cast_nonneg _) (Real.rpow_pos_of_pos hXp P.η).le
    _ = X ^ (P.lam - P.η) := by
      unfold SScale
      rw [← Real.rpow_add hXp]
      congr 1
      ring
    _ ≤ _ := phiProgressionU0_ge_rpow_lam_sub_eta P hX1 hs hsS

/-- Upper half of Lemma 6.1 with `(r,s) = 1`: for `d ≤ U`, `(a,d) = (s,d) = 1` and
`s ≤ S₀`, `phiProgressionAverage ≪ (1/d)(φ(s)/s) L_s`; `d` need not be squarefree or odd. -/
theorem phiProgressionAverage_small_upper (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ, 0 < d → (d : ℝ) ≤ UScale X → Nat.Coprime a d →
        1 ≤ s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
        phiProgressionAverage P X d a s ≤ C * phiProgressionAverageShape P X d s := by
  obtain ⟨C, hC, hupper⟩ := phiProgressionAverage_le_shape P
  obtain ⟨XE, hE⟩ := smallModulus_mul_le_phiProgressionU0 P
  refine ⟨C, max XE (Real.exp 1), hC, ?_⟩
  intro X hX d a s hd hdU ha hs hsd hsS
  exact hupper X d a s ((le_max_right _ _).trans hX) hd ha hs hsd hsS
    (hE X ((le_max_left _ _).trans hX) s d hs hsS hdU)

/-- For `d ≤ YU`, `phiProgressionAverage ≪ (log X)/d`: the error term `(1 + log U₁)/U₀`
is absorbed using `η + σ < λ`. -/
theorem phiProgressionAverage_wide_upper (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ, 0 < d → Nat.Coprime a d → 1 ≤ s →
        (s : ℝ) ≤ SScale P X → (d : ℝ) ≤ YScale P X * UScale X →
        phiProgressionAverage P X d a s ≤ (C / (d : ℝ)) * Real.log X := by
  obtain ⟨C, hC, hupper⟩ := phiProgressionAverage_le_main_add_error
  obtain ⟨XE, hE⟩ := wideModulus_le_phiProgressionU0_eventually P
  refine ⟨C * (2 * P.θ + 1), max XE (Real.exp 1),
    mul_pos hC (by linarith [P.θ_pos]), ?_⟩
  intro X hX d a s hd ha hs hsS hdW
  have hXe : Real.exp 1 ≤ X := (le_max_right _ _).trans hX
  have hX1 : 1 < X := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hXe
  have hXp : 0 < X := zero_lt_one.trans hX1
  have hlog1 : 1 ≤ Real.log X := (Real.le_log_iff_exp_le hXp).mpr hXe
  have hlog : 0 ≤ Real.log X := zero_le_one.trans hlog1
  have hA1 := one_le_phiProgressionU0 P hX1.le hs hsS
  have hA : 0 < phiProgressionU0 P s X := zero_lt_one.trans_le hA1
  have hAB := phiProgressionU0_lt_U1_of_s_le_SScale P hX1 hs hsS
  have hB1 : 1 ≤ phiProgressionU1 P s X := hA1.trans hAB.le
  have hdp : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdA := hE X ((le_max_left _ _).trans hX) s d hs hsS hdW
  have hlogB : Real.log (phiProgressionU1 P s X) ≤ P.θ * Real.log X := by
    calc
      _ ≤ Real.log (X ^ P.θ) := Real.log_le_log
        (zero_lt_one.trans_le hB1) (phiProgressionU1_le_rpow_theta P hXp hs)
      _ = _ := Real.log_rpow hXp _
  have hlogBA : Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) ≤
      P.θ * Real.log X := by
    rw [log_phiProgressionU1_div_U0_eq_slantLogLength P hXp
      (lt_of_lt_of_le Nat.zero_lt_one hs)]
    exact (slantLogLength_le_theta_sub_lam_mul_log P hX1.le hs).trans
      (by nlinarith [P.lam_pos])
  have hnum : 0 ≤ 1 + Real.log (phiProgressionU1 P s X) :=
    add_nonneg zero_le_one (Real.log_nonneg hB1)
  calc
    _ ≤ C * ((1 + Real.log (phiProgressionU1 P s X)) / phiProgressionU0 P s X +
          (1 / (d : ℝ)) * Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)) :=
      hupper P X d a s hd ha hA hAB hB1
    _ ≤ C * (((P.θ + 1) * Real.log X) / (d : ℝ) +
          (1 / (d : ℝ)) * (P.θ * Real.log X)) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply add_le_add
      · exact (div_le_div_of_nonneg_left hnum hdp hdA).trans
          (div_le_div_of_nonneg_right (by nlinarith) hdp.le)
      · exact mul_le_mul_of_nonneg_left hlogBA (by positivity)
    _ = _ := by ring

/-- `∑_{s ≤ S₀, s squarefree} 1/φ(s) ≪ log X`, as in (5). -/
theorem exactDivisorSRange_reciprocal_totient_upper (P : Params) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, Real.exp 1 ≤ X →
      (∑ s ∈ exactDivisorSRange P X, (1 : ℝ) / Nat.totient s) ≤ C * Real.log X := by
  classical
  obtain ⟨C, hC, hbound⟩ := PhiGammaDivSummableBound_concrete
  refine ⟨C * (P.η + 1), mul_pos hC (by linarith [P.η_pos]), ?_⟩
  intro X hXe
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hXe
  have hX1 : 1 ≤ X := (by norm_num : (1 : ℝ) ≤ Real.exp 1).trans hXe
  have hS1 : 1 ≤ SScale P X := Real.one_le_rpow hX1 P.η_pos.le
  have hlog1 : 1 ≤ Real.log X := (Real.le_log_iff_exp_le hXp).mpr hXe
  have hh : (harmonic ⌊SScale P X⌋₊ : ℝ) ≤ (P.η + 1) * Real.log X := by
    calc
      _ ≤ 1 + Real.log (SScale P X) := harmonic_floor_le_one_add_log _ hS1
      _ = 1 + P.η * Real.log X := by rw [log_SScale P hXp]
      _ ≤ _ := by nlinarith
  calc
    _ ≤ phiGammaDivSum ⌊SScale P X⌋₊ * (harmonic ⌊SScale P X⌋₊ : ℝ) :=
      squarefree_reciprocal_totient_sum_le_harmonic _
    _ ≤ C * (harmonic ⌊SScale P X⌋₊ : ℝ) :=
      mul_le_mul_of_nonneg_right (hbound _) (Estimates.harmonic_nonneg_real _)
    _ ≤ C * ((P.η + 1) * Real.log X) := mul_le_mul_of_nonneg_left hh hC.le
    _ = _ := by ring

/-- The sum `∑_{s ≤ S₀, (s,D)=1} φ(s)⁻¹ ∑_r 1/φ(r)` in the proof of Theorem 6.3 is
`≪ (log X)²/D` for every `0 < D ≤ YU`; `D` need not be squarefree or odd. -/
theorem exactDivisorMPhiTensorFiberCoprime_wide_upper (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 0 < D → (D : ℝ) ≤ YScale P X * UScale X →
        ∀ a : ℕ → ℕ,
          (∀ s ∈ exactDivisorSRange P X, Nat.Coprime s D → Nat.Coprime (a s) D) →
          exactDivisorMPhiTensorFiberCoprime P X D a ≤
            (C / (D : ℝ)) * (Real.log X) ^ 2 := by
  classical
  obtain ⟨C₁, X₁, hC₁, h₁⟩ := phiProgressionAverage_wide_upper P
  obtain ⟨C₂, hC₂, h₂⟩ := exactDivisorSRange_reciprocal_totient_upper P
  refine ⟨C₁ * C₂, max X₁ (Real.exp 1), mul_pos hC₁ hC₂, ?_⟩
  intro X hX D hD hDW a ha
  have hXe : Real.exp 1 ≤ X := (le_max_right _ _).trans hX
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hXe
  have hlog : 0 ≤ Real.log X := Real.log_nonneg
    ((by norm_num : (1 : ℝ) ≤ Real.exp 1).trans hXe)
  have hDp : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  unfold exactDivisorMPhiTensorFiberCoprime
  calc
    _ ≤ ∑ s ∈ exactDivisorSRange P X,
          ((1 : ℝ) / Nat.totient s) * ((C₁ / (D : ℝ)) * Real.log X) := by
      apply Finset.sum_le_sum
      intro s hs
      split_ifs with hsD
      · have hsI := Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1
        have hsS : (s : ℝ) ≤ SScale P X :=
          (Nat.le_floor_iff (Real.rpow_pos_of_pos hXp P.η).le).mp hsI.2
        exact mul_le_mul_of_nonneg_left
          (h₁ X ((le_max_left _ _).trans hX) D (a s) s hD (ha s hs hsD)
            hsI.1 hsS hDW) (by positivity)
      · positivity
    _ = ((C₁ / (D : ℝ)) * Real.log X) *
          (∑ s ∈ exactDivisorSRange P X, (1 : ℝ) / Nat.totient s) := by
      rw [← Finset.sum_mul, mul_comm]
    _ ≤ ((C₁ / (D : ℝ)) * Real.log X) * (C₂ * Real.log X) :=
      mul_le_mul_of_nonneg_left (h₂ X hXe) (mul_nonneg (div_nonneg hC₁.le hDp.le) hlog)
    _ = _ := by ring

end ProgressionEstimates
end ErdosStraus
