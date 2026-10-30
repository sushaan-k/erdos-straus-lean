import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic
import ErdosStraus.Family.TotientExpansion

/-! # Reciprocal totient sums

Put `γ(k) = μ²(k)/φ(k)` and `C_γ = ∑_{k ≥ 1} γ(k)/k`. Using `n/φ(n) = ∑_{k ∣ n} γ(k)` and
the identity `∑_{n ≤ T} (f ⋆ g)(n)/n = ∑_{d ≤ T} (f(d)/d) ∑_{x ≤ T/d} g(x)/x`, this file
proves `∑_{n ≤ N} 1/φ(n) ≤ C_γ H_N` and `∑_{k ≤ N} γ(k) ≤ C_γ H_N`, which give two of the
estimates (5) of Section 3, and the consequence `M/φ(M) ≤ 3 C_γ log(2M)`.
-/

namespace ErdosStraus.DivisorEstimates

open scoped BigOperators

/-- `∑_{n ≤ T} (∑_{d ∣ n} f(d) g(n/d))/n = ∑_{d ≤ T} (f(d)/d) ∑_{x ≤ T/d} g(x)/x`. -/
theorem reciprocal_divisor_convolution_sum_eq (T : ℝ) (f g : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊T⌋₊,
      (∑ d ∈ n.divisors, f d * g (n / d)) / (n : ℝ)) =
      ∑ d ∈ Finset.Icc 1 ⌊T⌋₊, (f d / (d : ℝ)) *
        ∑ x ∈ Finset.Icc 1 ⌊T / (d : ℝ)⌋₊, g x / (x : ℝ) := by
  classical
  let S := (Finset.Icc 1 ⌊T⌋₊).sigma (fun n => n.divisors)
  let R := (Finset.Icc 1 ⌊T⌋₊).sigma (fun d => Finset.Icc 1 ⌊T / (d : ℝ)⌋₊)
  have hmap : ∀ nd ∈ S, (⟨nd.2, nd.1 / nd.2⟩ : Sigma (fun _ : ℕ => ℕ)) ∈ R := by
    intro nd hnd
    obtain ⟨hn, hd⟩ := Finset.mem_sigma.mp hnd
    have hnpos : 0 < nd.1 := (Finset.mem_Icc.mp hn).1
    have hdpos : 0 < nd.2 := Nat.pos_of_mem_divisors hd
    have hdvd := Nat.dvd_of_mem_divisors hd
    have hdle : nd.2 ≤ nd.1 := Nat.le_of_dvd hnpos hdvd
    have hnp : (0 : ℝ) < nd.1 := Nat.cast_pos.mpr hnpos
    have hdp : (0 : ℝ) < nd.2 := Nat.cast_pos.mpr hdpos
    have hT : 0 ≤ T := zero_le_one.trans (Nat.floor_pos.mp
      (hnpos.trans_le (Finset.mem_Icc.mp hn).2))
    have hnT : (nd.1 : ℝ) ≤ T := (Nat.le_floor_iff hT).mp (Finset.mem_Icc.mp hn).2
    have hprod : (nd.1 : ℝ) = (nd.2 : ℝ) * ((nd.1 / nd.2 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' hdvd).symm
    apply Finset.mem_sigma.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨hdpos, hdle.trans (Finset.mem_Icc.mp hn).2⟩
    · apply Finset.mem_Icc.mpr
      constructor
      · exact Nat.div_pos hdle hdpos
      · apply (Nat.le_floor_iff (div_nonneg hT hdp.le)).mpr
        apply (le_div_iff₀ hdp).mpr
        nlinarith only [hnT, hprod]
  have hinj : ∀ nd ∈ S, ∀ me ∈ S,
      (⟨nd.2, nd.1 / nd.2⟩ : Sigma (fun _ : ℕ => ℕ)) = ⟨me.2, me.1 / me.2⟩ → nd = me := by
    intro nd hnd me hme heq
    have hd : nd.2 = me.2 := congrArg Sigma.fst heq
    have hq : nd.1 / nd.2 = me.1 / me.2 := by
      exact congrArg (fun x : Sigma (fun _ : ℕ => ℕ) => x.2) heq
    have hn : nd.1 = me.1 := by
      calc
        _ = nd.2 * (nd.1 / nd.2) := (Nat.mul_div_cancel'
          (Nat.dvd_of_mem_divisors (Finset.mem_sigma.mp hnd).2)).symm
        _ = me.2 * (me.1 / me.2) := congrArg₂ (· * ·) hd hq
        _ = _ := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors (Finset.mem_sigma.mp hme).2)
    exact Sigma.ext hn (by simpa using hd)
  have hsurj : ∀ dx ∈ R, ∃ nd ∈ S,
      (⟨nd.2, nd.1 / nd.2⟩ : Sigma (fun _ : ℕ => ℕ)) = dx := by
    intro dx hdx
    obtain ⟨hd, hx⟩ := Finset.mem_sigma.mp hdx
    have hdp : (0 : ℝ) < dx.1 := Nat.cast_pos.mpr (Finset.mem_Icc.mp hd).1
    have hxp : (0 : ℝ) < dx.2 := Nat.cast_pos.mpr (Finset.mem_Icc.mp hx).1
    have hquot : 0 ≤ T / (dx.1 : ℝ) := zero_le_one.trans (Nat.floor_pos.mp
      ((Finset.mem_Icc.mp hx).1.trans (Finset.mem_Icc.mp hx).2))
    have hxT : (dx.2 : ℝ) ≤ T / (dx.1 : ℝ) :=
      (Nat.le_floor_iff hquot).mp (Finset.mem_Icc.mp hx).2
    have hpT : ((dx.1 * dx.2 : ℕ) : ℝ) ≤ T := by
      have hh := (le_div_iff₀ hdp).mp hxT
      push_cast
      nlinarith only [hh]
    have hT : 0 ≤ T := (show 0 ≤ ((dx.1 * dx.2 : ℕ) : ℝ) by positivity).trans hpT
    refine ⟨⟨dx.1 * dx.2, dx.1⟩, Finset.mem_sigma.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (Finset.mem_Icc.mp hd).1
        (Finset.mem_Icc.mp hx).1, (Nat.le_floor_iff hT).mpr hpT⟩
    · exact Nat.mem_divisors.mpr ⟨dvd_mul_right _ _, Nat.mul_ne_zero
        (Nat.ne_of_gt (Finset.mem_Icc.mp hd).1) (Nat.ne_of_gt (Finset.mem_Icc.mp hx).1)⟩
    · exact Sigma.ext rfl (by simp [Nat.mul_div_right dx.2 (Finset.mem_Icc.mp hd).1])
  have heq : (∑ nd ∈ S, f nd.2 * g (nd.1 / nd.2) / (nd.1 : ℝ)) =
      ∑ dx ∈ R, f dx.1 / (dx.1 : ℝ) * (g dx.2 / (dx.2 : ℝ)) := by
    apply Finset.sum_bij (fun nd _ => ⟨nd.2, nd.1 / nd.2⟩) hmap hinj
      (fun dx hdx => by
        obtain ⟨nd, hnd, he⟩ := hsurj dx hdx
        exact ⟨nd, hnd, he⟩)
    intro nd hnd
    have hn : (nd.1 : ℝ) = (nd.2 : ℝ) * ((nd.1 / nd.2 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel'
        (Nat.dvd_of_mem_divisors (Finset.mem_sigma.mp hnd).2)).symm
    dsimp only
    rw [hn]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  calc
    _ = ∑ nd ∈ S, f nd.2 * g (nd.1 / nd.2) / (nd.1 : ℝ) := by
      simp_rw [Finset.sum_div]
      exact Finset.sum_sigma' _ _ _
    _ = _ := heq
    _ = _ := by
      dsimp [R]
      simp_rw [Finset.mul_sum]
      exact (Finset.sum_sigma' (Finset.Icc 1 ⌊T⌋₊)
        (fun d => Finset.Icc 1 ⌊T / (d : ℝ)⌋₊)
        (fun d x => f d / (d : ℝ) * (g x / (x : ℝ)))).symm

/-! ## The function `γ` -/

section

open Classical
attribute [local instance] Classical.propDecidable

/-- `γ(n) = μ²(n)/φ(n)`. -/
noncomputable def gamma (n : ℕ) : ℝ := if Squarefree n then 1 / Nat.totient n else 0

theorem gamma_nonneg (n : ℕ) : 0 ≤ gamma n := by
  unfold gamma
  split_ifs <;> positivity

theorem gamma_le_phiGamma (n : ℕ) : gamma n ≤ phiGamma n := by
  by_cases hn : Squarefree n
  · simp only [gamma, if_pos hn, ProgressionEstimates.phiGamma_eq_reciprocal_totient hn]
    exact le_rfl
  · simp only [gamma, if_neg hn]
    exact phiGamma_nonneg n

/-- `n/φ(n) = ∑_{k ∣ n} γ(k)`. -/
theorem gamma_divisor_sum (n : ℕ) (hn : 0 < n) :
    (n : ℝ) / Nat.totient n = ∑ d ∈ n.divisors, gamma d := by
  have hsum : (∑ d ∈ n.divisors, gamma d) =
      ∏ p ∈ n.primeFactors, (1 + (1 : ℝ) / ((p : ℝ) - 1)) := by
    simp_rw [gamma]
    rw [← Finset.sum_filter, Nat.sum_divisors_filter_squarefree hn.ne']
    rw [Nat.factors_eq]
    simp_rw [add_comm (1 : ℝ)]
    rw [Finset.prod_add]
    simp only [Finset.prod_const_one, mul_one]
    apply Finset.sum_congr rfl
    intro S hS
    have hsub := Finset.mem_powerset.mp hS
    have hprime : ∀ p ∈ S, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors (hsub hp)
    have hsq : Squarefree (∏ p ∈ S, p) := Estimates.finite_prime_product_squarefree S hprime
    rw [S.prod_val]
    change (1 : ℝ) / Nat.totient (∏ p ∈ S, p) = _
    apply (ProgressionEstimates.phiGamma_eq_reciprocal_totient hsq).symm.trans
    change phiGammaAF (∏ p ∈ S, p) = _
    rw [phiGammaAF_multiplicative.map_prod_of_subset_primeFactors n S hsub]
    exact Finset.prod_congr rfl (fun p hp => phiGammaAF_apply_prime (hprime p hp))
  rw [hsum]
  have h := one_div_totient_eq_one_div_nat_mul_prime_product hn
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hprod : (∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹) =
      ∏ p ∈ n.primeFactors, (1 + (1 : ℝ) / ((p : ℝ) - 1)) :=
    Finset.prod_congr rfl (fun _ hp => primeFactor_one_sub_inv_inv_eq_one_add_inv_pred hp)
  rw [hprod] at h
  have hm := congrArg (fun r : ℝ => (n : ℝ) * r) h
  simpa only [mul_one_div, ← mul_assoc, mul_one_div_cancel hnR, one_mul] using hm

theorem gamma_div_summable : Summable (fun n : ℕ => gamma n / n) := by
  obtain ⟨C, _hC, hbound⟩ := PhiGammaDivSummableBound_concrete
  apply summable_of_sum_range_le (fun n => div_nonneg (gamma_nonneg n) (Nat.cast_nonneg n))
  intro N
  have hs : (∑ n ∈ Finset.range N, gamma n / n) ≤ phiGammaDivSum N := by
    apply (Finset.sum_le_sum (fun n _ =>
      div_le_div_of_nonneg_right (gamma_le_phiGamma n) (Nat.cast_nonneg n))).trans
    unfold phiGammaDivSum
    have he : (∑ n ∈ Finset.range N, phiGamma n / n) =
        ∑ n ∈ (Finset.range N).filter (fun n => n ≠ 0), phiGamma n / n := by
      symm
      apply Finset.sum_subset (Finset.filter_subset ..)
      intro n hn hnot
      have hn0 : n = 0 := by simpa only [Finset.mem_filter, hn, true_and, not_not] using hnot
      simp [hn0]
    rw [he]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      have h := Finset.mem_filter.mp hn
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero h.2, (Finset.mem_range.mp h.1).le⟩
    · intro n _ _
      exact div_nonneg (phiGamma_nonneg n) (Nat.cast_nonneg n)
  exact hs.trans (hbound N)

/-- `C_γ = ∑_{n ≥ 1} γ(n)/n`. -/
noncomputable def gammaConstant : ℝ := ∑' n : ℕ, gamma n / n

theorem gammaConstant_pos : 0 < gammaConstant := by
  have h := Summable.le_tsum gamma_div_summable 1 (fun n _ =>
    div_nonneg (gamma_nonneg n) (Nat.cast_nonneg n))
  have h1 : gamma 1 / (1 : ℕ) = (1 : ℝ) := by simp [gamma]
  rw [h1] at h
  exact zero_lt_one.trans_le h

theorem gamma_div_sum_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, gamma n / n) ≤ gammaConstant :=
  Summable.sum_le_tsum _ (fun n _ => div_nonneg (gamma_nonneg n) (Nat.cast_nonneg n))
    gamma_div_summable

/-- `∑_{n ≤ N} 1/φ(n) ≤ C_γ H_N`. -/
theorem reciprocal_totient_sum_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / Nat.totient n) ≤
      gammaConstant * (harmonic N : ℝ) := by
  have he := reciprocal_divisor_convolution_sum_eq (N : ℝ) gamma (fun _ => 1)
  simp only [Nat.floor_natCast, mul_one] at he
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      (1 : ℝ) / Nat.totient n = (∑ d ∈ n.divisors, gamma d) / n := by
    rw [← gamma_divisor_sum n (Finset.mem_Icc.mp hn).1]
    have hn0 : (n : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1)
    have hφ : (Nat.totient n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Nat.totient_pos.mpr (Finset.mem_Icc.mp hn).1).ne'
    field_simp [hn0, hφ]
  rw [Finset.sum_congr rfl hterm, he]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 N, (gamma d / (d : ℝ)) * (harmonic N : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (gamma_nonneg d) (Nat.cast_nonneg d))
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · apply Finset.Icc_subset_Icc le_rfl
        have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
        have hquot : (N : ℝ) / d ≤ N := div_le_self (Nat.cast_nonneg _) hd1
        simpa using Nat.floor_mono hquot
      · intro n _ _
        positivity
    _ = (∑ d ∈ Finset.Icc 1 N, gamma d / d) * (harmonic N : ℝ) :=
      (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (gamma_div_sum_le N)
      (Estimates.harmonic_nonneg_real N)

theorem gamma_sum_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, gamma n) ≤ gammaConstant * (harmonic N : ℝ) := by
  apply (Finset.sum_le_sum (fun n _ => show gamma n ≤ (1 : ℝ) / Nat.totient n by
    unfold gamma; split_ifs; exact le_rfl; positivity)).trans
  exact reciprocal_totient_sum_le N

theorem harmonic_floor_le_three_log (T : ℝ) (hT : 1 ≤ T) :
    (harmonic ⌊T⌋₊ : ℝ) ≤ 3 * Real.log (2 * T) := by
  have ht := harmonic_floor_le_one_add_log T hT
  have hlogT := Real.log_nonneg hT
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : T ≠ 0)]
  linarith

/-- `M/φ(M) ≤ 3 C_γ log(2M)`. -/
theorem totient_ratio_le_log (M : ℕ) (hM : 0 < M) :
    (M : ℝ) / Nat.totient M ≤ 3 * gammaConstant * Real.log (2 * M) := by
  rw [gamma_divisor_sum M hM]
  have hsub : M.divisors ⊆ Finset.Icc 1 M := fun d hd =>
    Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.divisor_le hd⟩
  apply (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun d _ _ => gamma_nonneg d)).trans
  have hh := harmonic_floor_le_three_log (M : ℝ) (by exact_mod_cast hM)
  simp only [Nat.floor_natCast] at hh
  apply (gamma_sum_le M).trans
  convert mul_le_mul_of_nonneg_left hh gammaConstant_pos.le using 1
  ring

end

end ErdosStraus.DivisorEstimates
