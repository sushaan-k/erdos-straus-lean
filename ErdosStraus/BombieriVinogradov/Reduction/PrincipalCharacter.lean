import ErdosStraus.BombieriVinogradov.Reduction.PartialSummation

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

/-!
# The principal character and the prime number theorem

For `y ≤ N`, the sum `∑_{n ≤ y, (n,q)=1} Λ(n)` differs from `ψ(y)` only on prime
powers `p^k` with `p ∣ q`, which contribute at most `log₂ q (log₂ N + 1) log N`.
So the principal-character term in the partial-summation bound for primes in
progressions reduces to modulus one. There the prime number theorem with error
`O(x exp(-c (log x)^(1/10)))`, together with the bound `2 / log 2` for the total
variation of the Abel kernel and for `|∑_{2 ≤ n ≤ y} 1/log n - li(y)|`, gives
`O(N / (log N)^A)` for every `A > 0`.
-/

namespace BombieriVinogradov

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology
noncomputable section

/-- The integers `n ≤ N` with `Λ(n) ≠ 0` and `gcd(n, q) > 1`. -/
def principalBadLambdaSupport (q N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun n =>
    ArithmeticFunction.vonMangoldt n ≠ 0 ∧ ¬ n.Coprime q

/-- The prime powers `p^k` with `p ∣ q` and `1 ≤ k ≤ log₂ N + 1`. -/
def principalBadPrimePowers (q N : ℕ) : Finset ℕ :=
  q.primeFactors.biUnion fun p =>
    (Finset.range (Nat.log2 N + 1)).image fun k => p ^ (k + 1)

/-- A prime power `n = p^k ≤ N` with `gcd(n, q) > 1` has `p ∣ q` and `k ≤ log₂ N`. -/
theorem principalBadLambdaSupport_subset_primePowers
    {q : ℕ} (hq : 0 < q) (N : ℕ) :
    principalBadLambdaSupport q N ⊆ principalBadPrimePowers q N := by
  intro n hn
  rw [principalBadLambdaSupport, Finset.mem_filter] at hn
  have hnN : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hn.1)
  obtain ⟨p, k, hp, hk, hpow⟩ :=
    (isPrimePow_nat_iff n).mp
      (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hn.2.1)
  have hgcd : n.gcd q ≠ 1 := by
    simpa [Nat.coprime_iff_gcd_eq_one] using hn.2.2
  obtain ⟨r, hr, hrg⟩ := Nat.exists_prime_and_dvd hgcd
  have hrn : r ∣ n := hrg.trans (Nat.gcd_dvd_left n q)
  have hrq : r ∣ q := hrg.trans (Nat.gcd_dvd_right n q)
  have hrp : r ∣ p := by
    rw [← hpow] at hrn
    exact hr.dvd_of_dvd_pow hrn
  have hr_eq : r = p := (Nat.dvd_prime hp).mp hrp |>.resolve_left hr.ne_one
  have hklog : k ≤ Nat.log2 N := by
    rw [Nat.log2_eq_log_two]
    apply Nat.le_log_of_pow_le Nat.one_lt_two
    calc
      2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
      _ = n := hpow
      _ ≤ N := hnN
  rw [principalBadPrimePowers, Finset.mem_biUnion]
  refine ⟨p, Nat.mem_primeFactors.mpr ⟨hp, ?_, hq.ne'⟩, Finset.mem_image.mpr ?_⟩
  · simpa [hr_eq] using hrq
  · refine ⟨k - 1, Finset.mem_range.mpr (by omega), ?_⟩
    rw [Nat.sub_add_cancel hk, hpow]

/-- `#{n ≤ N : Λ(n) ≠ 0, gcd(n, q) > 1} ≤ ω(q) (log₂ N + 1)`. -/
theorem card_principalBadLambdaSupport_le
    {q : ℕ} (hq : 0 < q) (N : ℕ) :
    (principalBadLambdaSupport q N).card ≤
      q.primeFactors.card * (Nat.log2 N + 1) := by
  calc
    (principalBadLambdaSupport q N).card ≤ (principalBadPrimePowers q N).card :=
      Finset.card_le_card (principalBadLambdaSupport_subset_primePowers hq N)
    _ ≤ ∑ p ∈ q.primeFactors,
        ((Finset.range (Nat.log2 N + 1)).image fun k => p ^ (k + 1)).card := by
      unfold principalBadPrimePowers
      exact Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ q.primeFactors, (Nat.log2 N + 1) := by
      exact Finset.sum_le_sum fun _ _ =>
        Finset.card_image_le.trans_eq (Finset.card_range _)
    _ = _ := by simp [Nat.mul_add]

/-- `∑_{n ≤ y, gcd(n, q) > 1} Λ(n)`, the part of `ψ(y)` removed by the principal
character mod `q`. -/
def principalBadLambdaMass (y q : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (y + 1),
    if n.Coprime q then 0 else lambdaNatCoeff n

/-- `∑_{n ≤ y} Λ(n) = ∑_{n ≤ y, (n,q)=1} Λ(n) + ∑_{n ≤ y, (n,q)>1} Λ(n)`. -/
theorem coprimeLambdaPrefix_one_eq_add_badMass (y q : ℕ) :
    coprimeLambdaPrefix y 1 =
      coprimeLambdaPrefix y q + principalBadLambdaMass y q := by
  unfold coprimeLambdaPrefix principalBadLambdaMass
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hone : n.Coprime 1 := Nat.coprime_one_right n
  by_cases h : n.Coprime q
  · simp only [if_pos hone, if_pos h, add_zero]
  · simp only [if_pos hone, if_neg h, zero_add]

private lemma lambda_norm_le_log_of_le_global
    {n N : ℕ} (hn : n ≤ N) (hN : 2 ≤ N) :
    ‖lambdaNatCoeff n‖ ≤ Real.log (N : ℝ) := by
  exact BombieriVinogradov.lambda_norm_le_log_of_le hn hN

/-- For `y ≤ N`, `∑_{n ≤ y, (n,q)>1} Λ(n) ≤ ω(q) (log₂ N + 1) log N`. -/
theorem norm_principalBadLambdaMass_le_omega
    {y N q : ℕ} (hq : 0 < q) (hy : y ≤ N) (hN : 2 ≤ N) :
    ‖principalBadLambdaMass y q‖ ≤
      (q.primeFactors.card : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) := by
  unfold principalBadLambdaMass
  calc
    _ ≤ ∑ n ∈ Finset.range (y + 1),
        ‖if n.Coprime q then 0 else lambdaNatCoeff n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (y + 1),
        if n ∈ principalBadLambdaSupport q N then Real.log (N : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      have hnN : n ≤ N :=
        (Nat.le_of_lt_succ (Finset.mem_range.mp hn)).trans hy
      have hlog : 0 ≤ Real.log (N : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
      by_cases hc : n.Coprime q
      · simp only [if_pos hc, norm_zero]
        split_ifs <;> positivity
      · by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
        · simp only [if_neg hc, lambdaNatCoeff, hΛ, Complex.ofReal_zero, norm_zero]
          split_ifs <;> positivity
        · rw [if_neg hc, if_pos]
          · exact lambda_norm_le_log_of_le_global hnN hN
          · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
              (Nat.lt_succ_iff.mpr hnN), hΛ, hc⟩
    _ ≤ ((principalBadLambdaSupport q N).card : ℝ) * Real.log (N : ℝ) := by
      rw [← Finset.sum_filter]
      calc
        (∑ _n ∈ (Finset.range (y + 1)).filter
            (fun n => n ∈ principalBadLambdaSupport q N), Real.log (N : ℝ)) =
            (((Finset.range (y + 1)).filter
              (fun n => n ∈ principalBadLambdaSupport q N)).card : ℝ) *
              Real.log (N : ℝ) := by simp
        _ ≤ ((principalBadLambdaSupport q N).card : ℝ) * Real.log (N : ℝ) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast Finset.card_le_card (by
              intro n hn
              exact (Finset.mem_filter.mp hn).2)
          · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    _ ≤ (q.primeFactors.card : ℝ) * (Nat.log2 N + 1 : ℝ) *
        Real.log (N : ℝ) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_principalBadLambdaSupport_le hq N
      · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))

/-- The same bound with `ω(q)` replaced by `log₂ q`. -/
theorem norm_principalBadLambdaMass_le_log2
    {y N q : ℕ} (hq : 0 < q) (hy : y ≤ N) (hN : 2 ≤ N) :
    ‖principalBadLambdaMass y q‖ ≤
      (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) := by
  refine (norm_principalBadLambdaMass_le_omega hq hy hN).trans ?_
  gcongr
  exact_mod_cast card_primeFactors_le_log2 hq

/-- For `y ≤ N`,
`|∑_{n ≤ y, (n,q)=1} Λ(n) - y| ≤ |ψ(y) - y| + log₂ q (log₂ N + 1) log N`. -/
theorem norm_principalLambdaMainError_le_global_add_bad
    {y N q : ℕ} (hq : 0 < q) (hy : y ≤ N) (hN : 2 ≤ N) :
    ‖principalLambdaMainError y q‖ ≤
      ‖principalLambdaMainError y 1‖ +
        (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) := by
  have hid : principalLambdaMainError y q =
      principalLambdaMainError y 1 - principalBadLambdaMass y q := by
    unfold principalLambdaMainError
    rw [coprimeLambdaPrefix_one_eq_add_badMass y q]
    ring
  rw [hid]
  exact (norm_sub_le _ _).trans
    (add_le_add le_rfl (norm_principalBadLambdaMass_le_log2 hq hy hN))

/-- The same comparison after taking the maximum over `y ≤ N`. -/
theorem principalLambdaPrefixMaxError_le_global_add_bad
    {N q : ℕ} (hq : 0 < q) (hN : 2 ≤ N) :
    principalLambdaPrefixMaxError N q ≤
      principalLambdaPrefixMaxError N 1 +
        (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) := by
  unfold principalLambdaPrefixMaxError
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  refine (norm_principalLambdaMainError_le_global_add_bad hq
    (Nat.le_of_lt_succ (Finset.mem_range.mp hy)) hN).trans ?_
  exact add_le_add
    (Finset.le_max'
      ((Finset.range (N + 1)).image
        (fun y => ‖principalLambdaMainError y 1‖)) _
      (Finset.mem_image.mpr ⟨y, hy, rfl⟩)) le_rfl

/-- The partial-summation bound for primes in progressions mod `q`, with the
principal-character term replaced by
`max_{y ≤ N} |ψ(y) - y| + log₂ q (log₂ N + 1) log N`. -/
theorem primeAPPrefixMaxError_le_characters_global
    {N q : ℕ} (hq : 0 < q) (hN : 2 ≤ N) :
    BombieriVinogradov.primeAPPrefixMaxError N q ≤
      discreteAbelAmplifierPrefixMax N *
        ((q.totient : ℝ)⁻¹ *
            (principalLambdaPrefixMaxError N 1 +
              (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) +
              ∑ χ ∈ nonprincipalCharacters q,
                lambdaCharacterPrefixMaxAmplitude N q χ) +
          lambdaPrimePowerCorrectionPrefixMaxError N q) +
      (q.totient : ℝ)⁻¹ * liDiscretePrefixMaxError N := by
  refine (primeAPPrefixMaxError_le_characters hq).trans ?_
  have hA : 0 ≤ discreteAbelAmplifierPrefixMax N := by
    have h0 : 0 ≤ discreteAbelAmplifier 0 := by unfold discreteAbelAmplifier; positivity
    exact h0.trans (by
      unfold discreteAbelAmplifierPrefixMax
      exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨0, by simp, rfl⟩))
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ hA
    apply add_le_add _ le_rfl
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by positivity))
    exact add_le_add
      (principalLambdaPrefixMaxError_le_global_add_bad hq hN) le_rfl
  · exact le_rfl

end

end BombieriVinogradov

namespace BombieriVinogradov

open Classical Finset Filter Set
open scoped BigOperators ArithmeticFunction Topology
noncomputable section

/-- At modulus one the coprime sum is `ψ(y)`. -/
theorem coprimeLambdaPrefix_one_eq_psi (y : ℕ) :
    coprimeLambdaPrefix y 1 = (Chebyshev.psi (y : ℝ) : ℂ) := by
  rw [coprimeLambdaPrefix, Chebyshev.psi_eq_sum_range]
  push_cast
  simp [lambdaNatCoeff]

theorem norm_principalLambdaMainError_one_eq_psi_sub (y : ℕ) :
    ‖principalLambdaMainError y 1‖ =
      |Chebyshev.psi (y : ℝ) - (y : ℝ)| := by
  rw [principalLambdaMainError, coprimeLambdaPrefix_one_eq_psi]
  rw [← Complex.ofReal_natCast]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem principalLambdaPrefixMaxError_one_eq_psi_prefixMax (N : ℕ) :
    principalLambdaPrefixMaxError N 1 =
      ((Finset.range (N + 1)).image
        (fun (y : ℕ) => |Chebyshev.psi (y : ℝ) - (y : ℝ)|)).max'
          (Finset.image_nonempty.mpr ⟨0, by simp⟩) := by
  unfold principalLambdaPrefixMaxError
  simp_rw [norm_principalLambdaMainError_one_eq_psi_sub]

/-! ## The Abel kernel and the logarithmic integral -/

/-- The Abel main term telescopes to `∑_{2 ≤ n ≤ y} 1 / log n`. -/
theorem discreteAbelLiMain_eq_sum_reciprocalLogWeight (y : ℕ) :
    discreteAbelLiMain y =
      ∑ n ∈ Finset.range (y + 1), reciprocalLogWeight n := by
  induction y with
  | zero => simp [discreteAbelLiMain, reciprocalLogWeight]
  | succ y ih =>
      rw [discreteAbelLiMain, Finset.sum_range_succ]
      rw [show (y + 1 + 1 : ℕ) = (y + 1) + 1 by omega,
        Finset.sum_range_succ, ← ih]
      unfold discreteAbelLiMain
      norm_num
      ring

private lemma reciprocalLog_integral_unit_bounds (n : ℕ) (hn : 2 ≤ n) :
    1 / Real.log (n + 1 : ℝ) ≤
        ∫ t in (n : ℝ)..(n + 1 : ℝ), 1 / Real.log t ∧
      (∫ t in (n : ℝ)..(n + 1 : ℝ), 1 / Real.log t) ≤
        1 / Real.log (n : ℝ) := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnn : (n : ℝ) ≤ n + 1 := by norm_num
  have hint :=
    BombieriVinogradov.inv_log_intervalIntegrable_of_two_le
      hnreal hnn
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  constructor
  · calc
      1 / Real.log (n + 1 : ℝ) =
          ∫ _t in (n : ℝ)..(n + 1 : ℝ), 1 / Real.log (n + 1 : ℝ) := by
            simp [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ ∫ t in (n : ℝ)..(n + 1 : ℝ), 1 / Real.log t := by
        apply intervalIntegral.integral_mono_on hnn intervalIntegrable_const hint
        intro t ht
        apply one_div_le_one_div_of_le (Real.log_pos (by linarith [ht.1]))
        exact Real.log_le_log (by linarith [ht.1]) ht.2
  · calc
      (∫ t in (n : ℝ)..(n + 1 : ℝ), 1 / Real.log t) ≤
          ∫ _t in (n : ℝ)..(n + 1 : ℝ), 1 / Real.log (n : ℝ) := by
        apply intervalIntegral.integral_mono_on hnn hint intervalIntegrable_const
        intro t ht
        apply one_div_le_one_div_of_le hlogn
        exact Real.log_le_log (by linarith) ht.1
      _ = 1 / Real.log (n : ℝ) := by
        simp [intervalIntegral.integral_const, smul_eq_mul]

/-- For `y ≥ 2`,
`1 / log y ≤ ∑_{2 ≤ n ≤ y} 1 / log n - ∫_2^y dt / log t ≤ 1 / log 2`. -/
theorem discreteAbelLiMain_sub_integral_bounds {y : ℕ} (hy : 2 ≤ y) :
    1 / Real.log (y : ℝ) ≤ discreteAbelLiMain y -
        ∫ t in (2 : ℝ)..(y : ℝ), 1 / Real.log t ∧
      discreteAbelLiMain y -
          ∫ t in (2 : ℝ)..(y : ℝ), 1 / Real.log t ≤
        1 / Real.log 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hy
  induction k with
  | zero =>
      rw [discreteAbelLiMain_eq_sum_reciprocalLogWeight]
      norm_num [reciprocalLogWeight, Finset.sum_range_succ]
  | succ k ih =>
      let n : ℕ := 2 + k
      have hn : 2 ≤ n := by omega
      have hb := reciprocalLog_integral_unit_bounds n hn
      have hint₁ :=
        BombieriVinogradov.inv_log_intervalIntegrable
          (show (2 : ℝ) ≤ n by exact_mod_cast hn)
      have hint₂ :=
        BombieriVinogradov.inv_log_intervalIntegrable_of_two_le
          (show (2 : ℝ) ≤ n by exact_mod_cast hn) (show (n : ℝ) ≤ n + 1 by norm_num)
      have ih' := ih (by omega)
      rw [discreteAbelLiMain_eq_sum_reciprocalLogWeight,
        show 2 + (k + 1) = n + 1 by omega, Finset.sum_range_succ]
      norm_num only [Nat.cast_add, Nat.cast_one]
      rw [← intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂]
      change 1 / Real.log (n : ℝ) ≤ discreteAbelLiMain n -
          ∫ t in (2 : ℝ)..(n : ℝ), 1 / Real.log t ∧
        discreteAbelLiMain n -
            ∫ t in (2 : ℝ)..(n : ℝ), 1 / Real.log t ≤
          1 / Real.log 2 at ih'
      rw [← discreteAbelLiMain_eq_sum_reciprocalLogWeight n]
      have hw : reciprocalLogWeight (n + 1) = 1 / Real.log (n + 1 : ℝ) := by
        simp [reciprocalLogWeight, show 2 ≤ n + 1 by omega]
      rw [hw]
      constructor
      · linarith only [ih'.1, hb.2]
      · linarith only [ih'.2, hb.1]

/-- For `y ≥ 2`, `|∑_{2 ≤ n ≤ y} 1 / log n - li(y)| ≤ 2 / log 2`. -/
theorem liDiscreteError_le_two_div_log_two
    {y : ℕ} (hy : 2 ≤ y) :
    liDiscreteError y ≤ 2 / Real.log 2 := by
  have hb := discreteAbelLiMain_sub_integral_bounds hy
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  rw [liDiscreteError,
    BombieriVinogradov.logIntegral,
    BombieriVinogradov.shiftedLogIntegral]
  rw [abs_le]
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have htwo : 0 < 2 / Real.log 2 := div_pos (by norm_num) hlog
  have hrel : 2 / Real.log 2 = 2 * (1 / Real.log 2) := by ring
  constructor
  · linarith only [hb.1, one_div_pos.mpr hlogy]
  · linarith only [hb.2, hrel, htwo]

/-- A bound for `|∑_{2 ≤ n ≤ y} 1 / log n - li(y)|` valid for every `y`,
including `y = 0, 1`. -/
noncomputable def globalLiDiscreteErrorBound : ℝ :=
  max (liDiscreteError 0)
    (max (liDiscreteError 1) (2 / Real.log 2))

theorem liDiscreteError_le_bound (y : ℕ) :
    liDiscreteError y ≤ globalLiDiscreteErrorBound := by
  by_cases hy : 2 ≤ y
  · exact (liDiscreteError_le_two_div_log_two hy).trans
      (le_max_of_le_right (le_max_right _ _))
  · interval_cases y
    · exact le_max_left _ _
    · exact le_max_of_le_right (le_max_left _ _)

theorem liDiscretePrefixMaxError_le_bound (N : ℕ) :
    liDiscretePrefixMaxError N ≤ globalLiDiscreteErrorBound := by
  unfold liDiscretePrefixMaxError
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, _hy, rfl⟩
  exact liDiscreteError_le_bound y

private lemma reciprocalLogWeight_nonneg (n : ℕ) : 0 ≤ reciprocalLogWeight n := by
  unfold reciprocalLogWeight
  split_ifs with hn
  · exact inv_nonneg.mpr (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
  · rfl

private lemma reciprocalLogWeight_succ_le {n : ℕ} (hn : 2 ≤ n) :
    reciprocalLogWeight (n + 1) ≤ reciprocalLogWeight n := by
  simp only [reciprocalLogWeight, if_pos hn, if_pos (show 2 ≤ n + 1 by omega)]
  apply inv_anti₀
  · exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  · exact Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) (by norm_num)

/-- The total variation of the Abel kernel `1 / log n` is at most `2 / log 2`:
after its jump at `n = 2` the weight is nonnegative and decreasing. -/
theorem discreteAbelAmplifier_le_two_div_log_two (y : ℕ) :
    discreteAbelAmplifier y ≤ 2 / Real.log 2 := by
  by_cases hy : y < 2
  · interval_cases y <;> norm_num [discreteAbelAmplifier, reciprocalLogWeight] <;> positivity
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ y by omega)
    induction k with
    | zero =>
        norm_num [discreteAbelAmplifier, reciprocalLogWeight, Finset.sum_range_succ]
        have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
        rw [abs_of_pos hlog]
        rw [div_eq_mul_inv]
        linarith
    | succ k ih =>
        let n : ℕ := 2 + k
        have hn : 2 ≤ n := by omega
        have hmono := reciprocalLogWeight_succ_le hn
        have hnon := reciprocalLogWeight_nonneg n
        have hnons := reciprocalLogWeight_nonneg (n + 1)
        rw [show 2 + (k + 1) = n + 1 by omega]
        unfold discreteAbelAmplifier
        rw [Finset.sum_range_succ, abs_of_nonneg hnons,
          abs_of_nonneg (sub_nonneg.mpr hmono)]
        have ih' := ih (by omega)
        change discreteAbelAmplifier n ≤ 2 / Real.log 2 at ih'
        unfold discreteAbelAmplifier at ih'
        rw [abs_of_nonneg hnon] at ih'
        linarith [ih']

theorem discreteAbelAmplifierPrefixMax_le_two_div_log_two (N : ℕ) :
    discreteAbelAmplifierPrefixMax N ≤ 2 / Real.log 2 := by
  unfold discreteAbelAmplifierPrefixMax
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, _hy, rfl⟩
  exact discreteAbelAmplifier_le_two_div_log_two y

/-! ## The modulus-one term -/

private lemma eventually_log_rpow_le_sqrt (A : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, Real.log x ^ A ≤ Real.sqrt x := by
  have h :=
    (isLittleO_log_rpow_rpow_atTop A (show (0 : ℝ) < 1 / 2 by norm_num)).bound
      (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [h, Filter.eventually_gt_atTop (1 : ℝ)] with x hx hx1
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1.le) A),
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) (1 / 2 : ℝ)),
    one_mul, ← Real.sqrt_eq_rpow] at hx
  exact hx

private lemma eventually_sqrt_le_div_log_rpow (A : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, Real.sqrt x ≤ x / Real.log x ^ A := by
  filter_upwards [eventually_log_rpow_le_sqrt A,
    Filter.eventually_gt_atTop (1 : ℝ)] with x hlog hx
  have hx0 : 0 ≤ x := by linarith
  have hl0 : 0 < Real.log x ^ A :=
    Real.rpow_pos_of_pos (Real.log_pos hx) A
  rw [le_div_iff₀ hl0]
  calc
    Real.sqrt x * Real.log x ^ A ≤ Real.sqrt x * Real.sqrt x :=
      mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg x)
    _ = x := Real.mul_self_sqrt hx0

private lemma eventually_log_rpow_mul_exp_le_one
    (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    ∀ᶠ x : ℝ in Filter.atTop,
      Real.log x ^ A * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)) ≤ 1 := by
  have hp : (0 : ℝ) < 1 / 10 := by norm_num
  have hsmall :=
    Real.tendsto_log_atTop.eventually
      ((isLittleO_log_rpow_atTop hp).bound (div_pos hc hA))
  filter_upwards [hsmall, Filter.eventually_gt_atTop (Real.exp 1)] with x hx hxlarge
  have hexp1 : 1 < x := by
    have : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    linarith
  have hlog : 0 < Real.log x := Real.log_pos hexp1
  have hlogone : 1 < Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) hxlarge
  have hpow0 : 0 ≤ Real.log x ^ (1 / 10 : ℝ) :=
    Real.rpow_nonneg hlog.le _
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hlogone.le),
    Real.norm_eq_abs, abs_of_nonneg hpow0] at hx
  have hscaled : A * Real.log (Real.log x) ≤
      c * Real.log x ^ (1 / 10 : ℝ) := by
    calc
      A * Real.log (Real.log x) ≤
          A * ((c / A) * Real.log x ^ (1 / 10 : ℝ)) :=
        mul_le_mul_of_nonneg_left hx hA.le
      _ = c * Real.log x ^ (1 / 10 : ℝ) := by field_simp
  rw [Real.rpow_def_of_pos hlog, ← Real.exp_add]
  calc
    Real.exp (Real.log (Real.log x) * A +
        -c * Real.log x ^ (1 / 10 : ℝ)) ≤ Real.exp 0 := by
      rw [Real.exp_le_exp]
      nlinarith
    _ = 1 := Real.exp_zero

/-- The factor `(1/2)^(1/10)` accounts for `log y ≥ (log N) / 2` when `y > √N`. -/
private lemma eventually_half_log_exp_le_inv_log_rpow
    (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    ∀ᶠ x : ℝ in Filter.atTop,
      Real.exp (-(c * (1 / 2 : ℝ) ^ (1 / 10 : ℝ)) *
          Real.log x ^ (1 / 10 : ℝ)) ≤ (Real.log x ^ A)⁻¹ := by
  have hd : 0 < c * (1 / 2 : ℝ) ^ (1 / 10 : ℝ) := by positivity
  filter_upwards [eventually_log_rpow_mul_exp_le_one A
    (c * (1 / 2 : ℝ) ^ (1 / 10 : ℝ)) hA hd,
    Filter.eventually_gt_atTop 1] with x hx hx1
  have hlogpow : 0 < Real.log x ^ A :=
    Real.rpow_pos_of_pos (Real.log_pos hx1) A
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hlogpow).2
  simpa [mul_comm] using hx

/-- `max_{y ≤ N} |ψ(y) - y| ≤ K N / (log N)^A` for large `N`. For `y ≤ √N` this
follows from `ψ(y) ≪ y`, and for `y > √N` from `MediumPNT`. -/
theorem principalLambdaPrefixMaxError_one_eventually_le (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        principalLambdaPrefixMaxError N 1 ≤
          K * (N : ℝ) / Real.log N ^ A := by
  obtain ⟨c, hc, hmedium⟩ := MediumPNT
  rw [Asymptotics.isBigO_iff'] at hmedium
  obtain ⟨M, hM, hmedium⟩ := hmedium
  let d : ℝ := c * (1 / 2 : ℝ) ^ (1 / 10 : ℝ)
  let Ksmall : ℝ := Real.log 4 + 5
  have hKsmall : 0 < Ksmall := by dsimp [Ksmall]; positivity
  let K : ℝ := M + Ksmall
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  have hmediumNat : ∀ᶠ y : ℕ in Filter.atTop,
      |Chebyshev.psi (y : ℝ) - (y : ℝ)| ≤
        M * ((y : ℝ) * Real.exp (-c * Real.log y ^ (1 / 10 : ℝ))) := by
    have h := tendsto_natCast_atTop_atTop.eventually hmedium
    filter_upwards [h] with y hy
    have hnonneg : 0 ≤ (y : ℝ) *
        Real.exp (-c * Real.log y ^ (1 / 10 : ℝ)) := by positivity
    simpa [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hy
  rw [Filter.eventually_atTop] at hmediumNat
  obtain ⟨Y, hY⟩ := hmediumNat
  have hsqrtNat := tendsto_natCast_atTop_atTop.eventually
    (eventually_sqrt_le_div_log_rpow A)
  have hexpNat := tendsto_natCast_atTop_atTop.eventually
    (eventually_half_log_exp_le_inv_log_rpow A c hA hc)
  filter_upwards [hsqrtNat, hexpNat,
    Filter.eventually_ge_atTop (max (Y * Y) 2)] with N hsqrtPay hexpPay hNlarge
  rw [principalLambdaPrefixMaxError_one_eq_psi_prefixMax]
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hyRange, rfl⟩
  have hyN : y ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hyRange)
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hNlarge
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hN2)
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hbudget0 : 0 ≤ (N : ℝ) / Real.log N ^ A := by positivity
  by_cases hsmall : (y : ℝ) ≤ Real.sqrt N
  · have hpsi := Chebyshev.psi_le_const_mul_self (x := (y : ℝ)) (by positivity)
    have herr : |Chebyshev.psi (y : ℝ) - (y : ℝ)| ≤ Ksmall * (y : ℝ) := by
      rw [abs_sub_comm]
      calc
        |(y : ℝ) - Chebyshev.psi (y : ℝ)| ≤
            |(y : ℝ)| + |Chebyshev.psi (y : ℝ)| := abs_sub _ _
        _ = (y : ℝ) + Chebyshev.psi (y : ℝ) := by
          rw [abs_of_nonneg (by positivity), abs_of_nonneg (Chebyshev.psi_nonneg _)]
        _ ≤ Ksmall * (y : ℝ) := by dsimp [Ksmall]; linarith
    calc
      |Chebyshev.psi (y : ℝ) - (y : ℝ)| ≤ Ksmall * (y : ℝ) := herr
      _ ≤ Ksmall * Real.sqrt N := mul_le_mul_of_nonneg_left hsmall hKsmall.le
      _ ≤ Ksmall * ((N : ℝ) / Real.log N ^ A) :=
        mul_le_mul_of_nonneg_left hsqrtPay hKsmall.le
      _ ≤ K * (N : ℝ) / Real.log N ^ A := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right (by dsimp [K]; linarith [hM])
          (by positivity)
  · have hsqrty : Real.sqrt N < y := lt_of_not_ge hsmall
    have hyY : Y ≤ y := by
      by_contra hyY
      have hylt : y < Y := Nat.lt_of_not_ge hyY
      have hySq : y * y < Y * Y := Nat.mul_self_lt_mul_self hylt
      have hYSqN : Y * Y ≤ N := le_trans (le_max_left _ _) hNlarge
      have hySqN : y * y < N := lt_of_lt_of_le hySq hYSqN
      have : (y : ℝ) < Real.sqrt N :=
        (Real.lt_sqrt (show 0 ≤ (y : ℝ) by positivity)).mpr (by
          norm_num [pow_two]
          exact_mod_cast hySqN)
      linarith
    have hpnt := hY y hyY
    have hlogLower : (1 / 2 : ℝ) * Real.log N ≤ Real.log y := by
      have hlogsqrt := Real.log_le_log (Real.sqrt_pos.2 hNpos) hsqrty.le
      rw [Real.log_sqrt hNpos.le] at hlogsqrt
      linarith
    have hhalf0 : 0 ≤ (1 / 2 : ℝ) * Real.log N := by positivity
    have hpowLower :
        (1 / 2 : ℝ) ^ (1 / 10 : ℝ) * Real.log N ^ (1 / 10 : ℝ) ≤
          Real.log y ^ (1 / 10 : ℝ) := by
      calc
        (1 / 2 : ℝ) ^ (1 / 10 : ℝ) * Real.log N ^ (1 / 10 : ℝ) =
            ((1 / 2 : ℝ) * Real.log N) ^ (1 / 10 : ℝ) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
        _ ≤ Real.log y ^ (1 / 10 : ℝ) :=
          Real.rpow_le_rpow hhalf0 hlogLower (by norm_num)
    have hexpCompare :
        Real.exp (-c * Real.log y ^ (1 / 10 : ℝ)) ≤
          Real.exp (-d * Real.log N ^ (1 / 10 : ℝ)) := by
      rw [Real.exp_le_exp]
      dsimp [d]
      nlinarith [mul_le_mul_of_nonneg_left hpowLower hc.le]
    calc
      |Chebyshev.psi (y : ℝ) - (y : ℝ)| ≤
          M * ((y : ℝ) * Real.exp (-c * Real.log y ^ (1 / 10 : ℝ))) := hpnt
      _ ≤ M * ((N : ℝ) * Real.exp (-d * Real.log N ^ (1 / 10 : ℝ))) := by
        gcongr
      _ ≤ M * ((N : ℝ) * (Real.log N ^ A)⁻¹) := by gcongr
      _ = M * (N : ℝ) / Real.log N ^ A := by rw [div_eq_mul_inv]; ring
      _ ≤ K * (N : ℝ) / Real.log N ^ A := by
        have hMK : M ≤ K := by dsimp [K]; linarith [hKsmall]
        rw [mul_div_assoc, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right hMK hbudget0

/-- The modulus-one terms of the partial-summation bound are `O(N / (log N)^A)`
for every `A > 0`: the total variation of the Abel kernel and
`|∑_{2 ≤ n ≤ y} 1 / log n - li(y)|` are bounded by constants, and
`max_{y ≤ N} |ψ(y) - y|` is bounded by the previous theorem. -/
theorem globalPartialSummationBound :
    GlobalPartialSummationBound := by
  intro A hA
  obtain ⟨K, hK, hprefix⟩ :=
    principalLambdaPrefixMaxError_one_eventually_le A hA
  let D : ℝ := 2 / Real.log 2
  have hD : 0 < D := by dsimp [D]; positivity
  let B : ℝ := globalLiDiscreteErrorBound
  have hB : 0 ≤ B := by
    dsimp [B, globalLiDiscreteErrorBound]
    exact (abs_nonneg _).trans (le_max_left _ _)
  let C : ℝ := D * K + B + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hsqrtNat := tendsto_natCast_atTop_atTop.eventually
    (eventually_sqrt_le_div_log_rpow A)
  filter_upwards [hprefix, hsqrtNat, Filter.eventually_ge_atTop 2] with N hprefix hsqrtPay hN
  intro _hNarg
  have hbudgetNonneg : 0 ≤ (N : ℝ) / Real.log N ^ A := by positivity
  have hbudgetOne : 1 ≤ (N : ℝ) / Real.log N ^ A := by
    calc
      (1 : ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.mpr (by
        exact_mod_cast (show 1 ≤ N by omega))
      _ ≤ (N : ℝ) / Real.log N ^ A := hsqrtPay
  have hprincipalNonneg : 0 ≤ principalLambdaPrefixMaxError N 1 := by
    unfold principalLambdaPrefixMaxError
    have hm := Finset.max'_mem
      ((Finset.range (N + 1)).image (fun y => ‖principalLambdaMainError y 1‖))
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)
    rcases Finset.mem_image.mp hm with ⟨y, _hy, heq⟩
    rw [← heq]
    exact norm_nonneg _
  unfold globalPartialSummationError
  calc
    discreteAbelAmplifierPrefixMax N * principalLambdaPrefixMaxError N 1 +
        liDiscretePrefixMaxError N ≤
      D * (K * (N : ℝ) / Real.log N ^ A) + B := by
        apply add_le_add
        · calc
            discreteAbelAmplifierPrefixMax N * principalLambdaPrefixMaxError N 1 ≤
                D * principalLambdaPrefixMaxError N 1 :=
              mul_le_mul_of_nonneg_right
                (discreteAbelAmplifierPrefixMax_le_two_div_log_two N)
                hprincipalNonneg
            _ ≤ D * (K * (N : ℝ) / Real.log N ^ A) :=
              mul_le_mul_of_nonneg_left hprefix hD.le
        · exact liDiscretePrefixMaxError_le_bound N
    _ ≤ (D * K + B) * ((N : ℝ) / Real.log N ^ A) := by
      rw [add_mul, mul_assoc, mul_div_assoc]
      have hBpay : B ≤ B * ((N : ℝ) / Real.log N ^ A) := by
        nth_rewrite 1 [← mul_one B]
        exact mul_le_mul_of_nonneg_left hbudgetOne hB
      linarith
    _ ≤ C * (N : ℝ) / Real.log N ^ A := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)

end

end BombieriVinogradov
