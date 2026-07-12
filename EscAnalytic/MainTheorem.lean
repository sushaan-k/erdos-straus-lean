import EscAnalytic.CertificateAssembly

/-!
# Closed main theorem

This downstream module connects the exact actual-family estimates proved in
`IncrementEstimates` to the rough/smooth exceptional-count carriers.  It is kept
downstream to avoid a cycle through `Assembly` and `CertificateAssembly`.
-/

namespace EscAnalytic

open Classical

/-- The actual rough reduced exceptional count inherits the fully concrete
`exp(-c (log N)^(3/4))` estimate. -/
theorem actualPaperFamily_roughReducedExceptionalGeTwo_saving
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ α c : ℝ, 0 < α ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let X := paperOptimizationScale α N
        (reducedExceptionalCountGeTwo ⌊zScale X⌋₊ N : ℝ) ≤
          3 * (N : ℝ) * Real.exp (-c *
            (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4)) := by
  rcases actualPaperFamily_reducedExceptionalGeTwo_saving P with
    ⟨α, c, hα, hc, hred⟩
  refine ⟨α, c, hα, hc, ?_⟩
  filter_upwards [hred] with N hredN
  dsimp only at hredN ⊢
  let X := paperOptimizationScale α N
  let Pz := Inputs.roughModulus X
  have hbridge :
      reducedExceptionalCountGeTwo ⌊zScale X⌋₊ N ≤
        EscLeanChecks.reducedBaseExceptionalCountGeTwo N Pz := by
    apply reducedExceptionalCountGeTwo_le_reducedBaseExceptionalCountGeTwo
    intro p hp hdiv
    exact Inputs.prime_dvd_roughModulus_le_floor_zScale X hp hdiv
  have hbridgeR :
      (reducedExceptionalCountGeTwo ⌊zScale X⌋₊ N : ℝ) ≤
        (EscLeanChecks.reducedBaseExceptionalCountGeTwo N Pz : ℝ) := by
    exact_mod_cast hbridge
  exact hbridgeR.trans (by simpa [X, Pz] using hredN)

/-- Sharpened rough-large fibering: only smooth parts whose quotient ambient
scale remains above `sqrt N` can occur. -/
theorem roughLargeCount_le_sum_reduced_large_quotient (z N : ℕ) :
    roughLargeCount z N ≤
      ∑ s ∈ (Finset.Icc 1 N).filter (fun s => Nat.sqrt N < N / s),
        reducedExceptionalCountGeTwo z (N / s) := by
  classical
  set R : Finset ℕ :=
    (Finset.Icc 2 N).filter
      (fun n => EscLeanChecks.esExceptional n ∧
        ¬ roughPart z n ≤ Nat.sqrt N) with hR
  let smoothParts :=
    (Finset.Icc 1 N).filter (fun s => Nat.sqrt N < N / s)
  have hmem : ∀ n ∈ R, smoothPart z n ∈ smoothParts := by
    intro n hn
    rw [hR, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨h2, hN⟩, _hex, hrough⟩ := hn
    have hnpos : 0 < n := by omega
    have hspos : 1 ≤ smoothPart z n := smooth_pos
    have hsle : smoothPart z n ≤ N := le_trans (smooth_le hnpos) hN
    have hfactor := smooth_mul_rough z hnpos.ne'
    have hrough_le : roughPart z n ≤ N / smoothPart z n := by
      rw [Nat.le_div_iff_mul_le (by exact smooth_pos)]
      calc
        roughPart z n * smoothPart z n =
            smoothPart z n * roughPart z n := Nat.mul_comm _ _
        _ = n := hfactor
        _ ≤ N := hN
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hspos, hsle⟩,
        lt_of_not_ge hrough |>.trans_le hrough_le⟩
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun n => smoothPart z n) (s := R) (t := smoothParts) hmem
  have hRex : ∀ n ∈ R, EscLeanChecks.esExceptional n := by
    intro n hn
    rw [hR, Finset.mem_filter] at hn
    exact hn.2.1
  have hRrange : ∀ n ∈ R, 2 ≤ n ∧ n ≤ N := by
    intro n hn
    rw [hR, Finset.mem_filter, Finset.mem_Icc] at hn
    exact hn.1
  rw [show roughLargeCount z N = R.card from rfl, hfib]
  apply Finset.sum_le_sum
  intro s hs
  unfold reducedExceptionalCountGeTwo
  apply Finset.card_le_card_of_injOn (fun n => roughPart z n)
  · intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnR, hfeq⟩ := hn
    obtain ⟨h2, hN⟩ := hRrange n hnR
    have hnpos : 0 < n := by omega
    have hroughLarge : ¬ roughPart z n ≤ Nat.sqrt N := by
      rw [hR, Finset.mem_filter] at hnR
      exact hnR.2.2
    have hNtwo : 2 ≤ N := h2.trans hN
    have hNpos : 0 < N := lt_of_lt_of_le (by omega : 0 < 2) hNtwo
    have hsqrtPos : 0 < Nat.sqrt N := Nat.sqrt_pos.2 hNpos
    have hroughTwo : 2 ≤ roughPart z n := by omega
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hroughTwo, ?_⟩, roughPart_isRough z n,
      exceptional_lift hnpos (hRex n hnR)⟩
    have hfactor := smooth_mul_rough z hnpos.ne'
    rw [Nat.le_div_iff_mul_le (by rw [← hfeq]; exact smooth_pos), ← hfeq]
    calc
      roughPart z n * smoothPart z n =
          smoothPart z n * roughPart z n := Nat.mul_comm _ _
      _ = n := hfactor
      _ ≤ N := hN
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
    obtain ⟨haR, hfa⟩ := ha
    obtain ⟨hbR, hfb⟩ := hb
    have hapos : 0 < a := by have := (hRrange a haR).1; omega
    have hbpos : 0 < b := by have := (hRrange b hbR).1; omega
    have hra := smooth_mul_rough z hapos.ne'
    have hrb := smooth_mul_rough z hbpos.ne'
    rw [← hra, ← hrb, hfa, hfb]
    exact congrArg (fun t => s * t) hab

noncomputable def optimizationRoughCutoff (α : ℝ) (N : ℕ) : ℕ :=
  ⌊zScale (paperOptimizationScale α N)⌋₊

theorem optimizationRoughCutoff_mono
    {α : ℝ} (hα : 0 < α) {M N : ℕ}
    (hM : 1 ≤ M) (hMN : M ≤ N) :
    optimizationRoughCutoff α M ≤ optimizationRoughCutoff α N := by
  have hN : 1 ≤ N := hM.trans hMN
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : Real.log (M : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one hMreal) (by exact_mod_cast hMN)
  have hzM : zScale (paperOptimizationScale α M) =
      α ^ 4 * Real.log (M : ℝ) := by
    apply z_eq_alpha4_LN (Real.log_nonneg hMreal)
    simp [paperOptimizationScale]
  have hzN : zScale (paperOptimizationScale α N) =
      α ^ 4 * Real.log (N : ℝ) := by
    apply z_eq_alpha4_LN (Real.log_nonneg hNreal)
    simp [paperOptimizationScale]
  unfold optimizationRoughCutoff
  apply Nat.floor_mono
  rw [hzM, hzN]
  exact mul_le_mul_of_nonneg_left hlog (pow_nonneg hα.le 4)

theorem reducedExceptionalCountGeTwo_antitone_cutoff
    {zSmall zBig M : ℕ} (hz : zSmall ≤ zBig) :
    reducedExceptionalCountGeTwo zBig M ≤
      reducedExceptionalCountGeTwo zSmall M := by
  classical
  unfold reducedExceptionalCountGeTwo
  apply Finset.card_le_card
  intro m hm
  rw [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
  refine ⟨hm.1, ?_, hm.2.2⟩
  intro p hp hpSmall hpm
  exact hm.2.1 p hp (hpSmall.trans hz) hpm

/-- Apply the reduced estimate at the varying quotient scale `M=N/s` in every
rough-large fiber. -/
theorem actualPaperFamily_roughLarge_le_reducedSavingSum
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ α c : ℝ, 0 < α ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        (roughLargeCount (optimizationRoughCutoff α N) N : ℝ) ≤
          ∑ s ∈ (Finset.Icc 1 N).filter
              (fun s => Nat.sqrt N < N / s),
            3 * ((N / s : ℕ) : ℝ) *
              Real.exp (-c *
                (Real.log ((N / s : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)) := by
  rcases actualPaperFamily_roughReducedExceptionalGeTwo_saving P with
    ⟨α, c, hα, hc, hred⟩
  refine ⟨α, c, hα, hc, ?_⟩
  rcases Filter.eventually_atTop.1 hred with ⟨T, hT⟩
  filter_upwards [Filter.eventually_ge_atTop (max 1 (T * T))] with N hN
  have hNone : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hTT : T * T ≤ N := le_trans (le_max_right _ _) hN
  have hTsqrt : T ≤ Nat.sqrt N := (Nat.le_sqrt).2 hTT
  have hrough := roughLargeCount_le_sum_reduced_large_quotient
    (optimizationRoughCutoff α N) N
  have hroughR :
      (roughLargeCount (optimizationRoughCutoff α N) N : ℝ) ≤
        ∑ s ∈ (Finset.Icc 1 N).filter (fun s => Nat.sqrt N < N / s),
          (reducedExceptionalCountGeTwo
            (optimizationRoughCutoff α N) (N / s) : ℝ) := by
    exact_mod_cast hrough
  refine hroughR.trans ?_
  apply Finset.sum_le_sum
  intro s hs
  have hsData := Finset.mem_filter.mp hs
  have hsIcc := Finset.mem_Icc.mp hsData.1
  let M := N / s
  have hMlarge : Nat.sqrt N < M := hsData.2
  have hTM : T ≤ M := hTsqrt.trans hMlarge.le
  have hMone : 1 ≤ M := le_trans (by omega : 1 ≤ Nat.sqrt N + 1)
    (Nat.succ_le_iff.mpr hMlarge)
  have hMN : M ≤ N := Nat.div_le_self N s
  have hcut : optimizationRoughCutoff α M ≤
      optimizationRoughCutoff α N :=
    optimizationRoughCutoff_mono hα hMone hMN
  have hmono := reducedExceptionalCountGeTwo_antitone_cutoff
    (M := M) hcut
  have hmonoR :
      (reducedExceptionalCountGeTwo (optimizationRoughCutoff α N) M : ℝ) ≤
        (reducedExceptionalCountGeTwo (optimizationRoughCutoff α M) M : ℝ) := by
    exact_mod_cast hmono
  have hredM := hT M hTM
  exact hmonoR.trans (by
    simpa [optimizationRoughCutoff, M] using hredM)

/-- The varying quotient saving can be pulled out at the square-root scale;
the remaining divisor sum is harmonic. -/
theorem largeQuotientSavingSum_le_harmonic
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    (∑ s ∈ (Finset.Icc 1 N).filter
        (fun s => Nat.sqrt N < N / s),
      3 * ((N / s : ℕ) : ℝ) *
        Real.exp (-c *
          (Real.log ((N / s : ℕ) : ℝ)) ^ ((3 : ℝ) / 4))) ≤
      (3 * (N : ℝ) *
        Real.exp (-(c * ((1 : ℝ) / 2) ^ ((3 : ℝ) / 4)) *
          (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4))) *
        (1 + Real.log (N : ℝ)) := by
  classical
  let q : ℝ := (3 : ℝ) / 4
  let E : ℝ := Real.exp (-(c * ((1 : ℝ) / 2) ^ q) *
    (Real.log (N : ℝ)) ^ q)
  have hpoint : ∀ s ∈ (Finset.Icc 1 N).filter
      (fun s => Nat.sqrt N < N / s),
      3 * ((N / s : ℕ) : ℝ) *
          Real.exp (-c * (Real.log ((N / s : ℕ) : ℝ)) ^ q) ≤
        (3 * (N : ℝ) * E) * (s : ℝ)⁻¹ := by
    intro s hs
    obtain ⟨hsIcc, hlarge⟩ := Finset.mem_filter.mp hs
    obtain ⟨hs1, _hsN⟩ := Finset.mem_Icc.mp hsIcc
    let M := N / s
    have hMpos : 0 < M := by
      have : 0 < Nat.sqrt N + 1 := Nat.succ_pos _
      omega
    have hNlt : N < M * M := by
      have hsqrtSucc : Nat.sqrt N + 1 ≤ M := by omega
      exact (Nat.lt_succ_sqrt N).trans_le
        (Nat.mul_le_mul hsqrtSucc hsqrtSucc)
    have hlog : (1 / 2 : ℝ) * Real.log (N : ℝ) ≤
        Real.log (M : ℝ) := by
      have hNposR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
      have hMposR : (0 : ℝ) < M := by exact_mod_cast hMpos
      have hlog' : Real.log (N : ℝ) ≤ Real.log ((M : ℝ) * M) :=
        Real.log_le_log hNposR (by exact_mod_cast hNlt.le)
      rw [Real.log_mul hMposR.ne' hMposR.ne'] at hlog'
      linarith
    have hlogN0 : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hN)
    have hbase0 : 0 ≤ (1 / 2 : ℝ) * Real.log (N : ℝ) :=
      mul_nonneg (by norm_num) hlogN0
    have hrpow :
        ((1 / 2 : ℝ) * Real.log (N : ℝ)) ^ q ≤
          (Real.log (M : ℝ)) ^ q :=
      Real.rpow_le_rpow hbase0 hlog (by norm_num [q])
    have hsplit :
        ((1 / 2 : ℝ) * Real.log (N : ℝ)) ^ q =
          ((1 / 2 : ℝ) ^ q) * (Real.log (N : ℝ)) ^ q := by
      rw [Real.mul_rpow (by norm_num) hlogN0]
    have hexp :
        Real.exp (-c * (Real.log (M : ℝ)) ^ q) ≤ E := by
      apply Real.exp_le_exp.mpr
      dsimp [E]
      calc
        -c * (Real.log (M : ℝ)) ^ q ≤
            -c * (((1 / 2 : ℝ) * Real.log (N : ℝ)) ^ q) :=
          mul_le_mul_of_nonpos_left hrpow (by linarith)
        _ = -(c * ((1 / 2 : ℝ) ^ q)) *
            (Real.log (N : ℝ)) ^ q := by rw [hsplit]; ring
    have hdiv : ((N / s : ℕ) : ℝ) ≤ (N : ℝ) * (s : ℝ)⁻¹ := by
      simpa [div_eq_mul_inv] using
        (Nat.cast_div_le : ((N / s : ℕ) : ℝ) ≤ (N : ℝ) / (s : ℝ))
    have hnonneg : 0 ≤ ((N / s : ℕ) : ℝ) := Nat.cast_nonneg _
    calc
      3 * ((N / s : ℕ) : ℝ) *
          Real.exp (-c * (Real.log ((N / s : ℕ) : ℝ)) ^ q)
          ≤ 3 * ((N / s : ℕ) : ℝ) * E :=
            mul_le_mul_of_nonneg_left hexp (mul_nonneg (by norm_num) hnonneg)
      _ ≤ 3 * ((N : ℝ) * (s : ℝ)⁻¹) * E :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hdiv (by norm_num)) (Real.exp_pos _).le
      _ = (3 * (N : ℝ) * E) * (s : ℝ)⁻¹ := by ring
  calc
    (∑ s ∈ (Finset.Icc 1 N).filter
        (fun s => Nat.sqrt N < N / s),
      3 * ((N / s : ℕ) : ℝ) *
        Real.exp (-c *
          (Real.log ((N / s : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)))
        ≤ ∑ s ∈ (Finset.Icc 1 N).filter
            (fun s => Nat.sqrt N < N / s),
          (3 * (N : ℝ) * E) * (s : ℝ)⁻¹ := by
            simpa [q] using Finset.sum_le_sum hpoint
    _ ≤ ∑ s ∈ Finset.Icc 1 N,
          (3 * (N : ℝ) * E) * (s : ℝ)⁻¹ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.filter_subset _ _
            · intro s _hs _hnot
              positivity
    _ = (3 * (N : ℝ) * E) * (harmonic N : ℝ) := by
          rw [harmonic_eq_sum_Icc, Rat.cast_sum]
          simp_rw [Rat.cast_inv, Rat.cast_natCast]
          rw [Finset.mul_sum]
    _ ≤ (3 * (N : ℝ) * E) * (1 + Real.log (N : ℝ)) := by
          apply mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N)
          positivity
    _ = (3 * (N : ℝ) *
        Real.exp (-(c * ((1 : ℝ) / 2) ^ ((3 : ℝ) / 4)) *
          (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4))) *
        (1 + Real.log (N : ℝ)) := by rfl

/-- The rough-large range itself has the paper's stretched-exponential
saving, after the harmonic factor is absorbed into the exponent. -/
theorem actualPaperFamily_roughLarge_saving
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ α c C : ℝ, 0 < α ∧ 0 < c ∧ 0 < C ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        (roughLargeCount (optimizationRoughCutoff α N) N : ℝ) ≤
          C * ((N : ℝ) * saving c N) := by
  rcases actualPaperFamily_roughLarge_le_reducedSavingSum P with
    ⟨α, c₀, hα, hc₀, hsum⟩
  let c₁ : ℝ := c₀ * ((1 : ℝ) / 2) ^ ((3 : ℝ) / 4)
  have hc₁ : 0 < c₁ := by
    dsimp [c₁]
    positivity
  rcases log_absorb hc₁ (Ce := 9) (C₁ := 1) (by norm_num) (by norm_num) with
    ⟨c, hc, C, hC, habsorb⟩
  refine ⟨α, c, C, hα, hc, hC, ?_⟩
  filter_upwards [hsum, Filter.eventually_ge_atTop 3] with N hsumN hN
  have hN1 : 1 ≤ N := by omega
  have hlarge := largeQuotientSavingSum_le_harmonic hc₀ hN1
  have hlogLower : (2 : ℝ) / 3 ≤ Real.log (N : ℝ) :=
    log_ge_of_three_le hN
  have honeLog : 1 + Real.log (N : ℝ) ≤ 3 * Real.log (N : ℝ) := by
    linarith
  have hnonneg : 0 ≤ 3 * (N : ℝ) * saving c₁ N := by
    unfold saving
    positivity
  calc
    (roughLargeCount (optimizationRoughCutoff α N) N : ℝ)
        ≤ ∑ s ∈ (Finset.Icc 1 N).filter
            (fun s => Nat.sqrt N < N / s),
          3 * ((N / s : ℕ) : ℝ) *
            Real.exp (-c₀ *
              (Real.log ((N / s : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)) := hsumN
    _ ≤ (3 * (N : ℝ) * saving c₁ N) *
          (1 + Real.log (N : ℝ)) := by
        simpa [saving, c₁] using hlarge
    _ ≤ (3 * (N : ℝ) * saving c₁ N) *
          (3 * Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_left honeLog hnonneg
    _ = 9 * Real.log (N : ℝ) *
          (1 * ((N : ℝ) * saving c₁ N)) := by ring
    _ ≤ C * ((N : ℝ) * saving c N) := by
      simpa using habsorb N hN

/-- The optimization cutoff is eventually below the manuscript's Rankin
cutoff `(log N)^4`. -/
theorem optimizationRoughCutoff_le_zNatScale_eventually
    (α : ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      optimizationRoughCutoff α N ≤ zNatScale N := by
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ N : ℕ in Filter.atTop,
      max 1 (α ^ 4) ≤ Real.log (N : ℝ) :=
    (Filter.tendsto_atTop.1 hlog) (max 1 (α ^ 4))
  filter_upwards [hevent] with N hL
  have hL1 : 1 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hL
  have hα4L : α ^ 4 ≤ Real.log (N : ℝ) := (le_max_right _ _).trans hL
  have hL0 : 0 ≤ Real.log (N : ℝ) := zero_le_one.trans hL1
  have hscale : zScale (paperOptimizationScale α N) =
      α ^ 4 * Real.log (N : ℝ) := by
    apply z_eq_alpha4_LN hL0
    simp [paperOptimizationScale]
  have hreal : α ^ 4 * Real.log (N : ℝ) ≤
      (Real.log (N : ℝ)) ^ 4 := by
    have hLsq : 1 ≤ (Real.log (N : ℝ)) ^ 2 :=
      one_le_pow₀ hL1 (n := 2)
    have hL2nonneg : 0 ≤ (Real.log (N : ℝ)) ^ 2 := sq_nonneg _
    calc
      α ^ 4 * Real.log (N : ℝ) ≤
          Real.log (N : ℝ) * Real.log (N : ℝ) :=
        mul_le_mul_of_nonneg_right hα4L hL0
      _ = (Real.log (N : ℝ)) ^ 2 := by ring
      _ = (Real.log (N : ℝ)) ^ 2 * 1 := by ring
      _ ≤ (Real.log (N : ℝ)) ^ 2 * (Real.log (N : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hLsq hL2nonneg
      _ = (Real.log (N : ℝ)) ^ 4 := by ring
  unfold optimizationRoughCutoff zNatScale
  apply le_max_of_le_right
  apply Nat.floor_mono
  rw [hscale]
  exact hreal

/-- The smooth range at the optimization cutoff inherits the cited Rankin/de
Bruijn polynomial estimate at the larger manuscript cutoff. -/
theorem optimizationSmoothRange_polynomial_bound
    (α : ℝ) :
    ∃ θ C : ℝ, 0 < θ ∧ θ < 1 ∧ 0 < C ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        (smoothRangeCount (optimizationRoughCutoff α N) N : ℝ) ≤
          C * (N : ℝ) ^ θ := by
  rcases rankin_mathlibSmoothNumbersUpTo_zNatScale_bound with
    ⟨θ, C, hθ0, hθ1, hC, hrankin⟩
  refine ⟨θ, C, hθ0, hθ1, hC, ?_⟩
  filter_upwards [optimizationRoughCutoff_le_zNatScale_eventually α,
      Filter.eventually_ge_atTop 3] with N hcut hN
  have hsmooth := smoothRangeCount_le_sum_smoothPsi
    (optimizationRoughCutoff α N) N
  calc
    (smoothRangeCount (optimizationRoughCutoff α N) N : ℝ)
        ≤ ∑ m ∈ Finset.Icc 1 (Nat.sqrt N),
            smoothPsi ((N / m : ℕ) : ℝ)
              (optimizationRoughCutoff α N : ℝ) := hsmooth
    _ ≤ ∑ m ∈ Finset.Icc 1 (Nat.sqrt N),
          ((Nat.smoothNumbersUpTo (N / m)
            (zNatScale N + 1)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro m _hm
      calc
        smoothPsi ((N / m : ℕ) : ℝ)
            (optimizationRoughCutoff α N : ℝ)
            ≤ ((Nat.smoothNumbersUpTo (N / m)
              (optimizationRoughCutoff α N + 1)).card : ℝ) :=
          smoothPsi_nat_le_smoothNumbersUpTo
            (optimizationRoughCutoff α N) (N / m)
        _ ≤ ((Nat.smoothNumbersUpTo (N / m)
              (zNatScale N + 1)).card : ℝ) := by
          exact_mod_cast smoothNumbersUpTo_card_mono le_rfl
            (Nat.add_le_add_right hcut 1)
    _ ≤ C * (N : ℝ) ^ θ := hrankin N hN

theorem saving_le_saving_of_le
    {c d : ℝ} (hdc : d ≤ c) {N : ℕ} (hN : 1 ≤ N) :
    saving c N ≤ saving d N := by
  unfold saving
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hpow : 0 ≤ (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4) :=
    Real.rpow_nonneg hlog _
  nlinarith

/-- Final paper theorem: the actual exceptional count satisfies the claimed
stretched-exponential bound from the registered analytic inputs used upstream.
The dependency audit records those inputs explicitly. -/
theorem actualPaperFamily_exceptionalCount_mainBound
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    IsMainBound exceptionalCount := by
  rcases actualPaperFamily_roughLarge_saving P with
    ⟨α, cr, Cr, hα, hcr, hCr, hrough⟩
  rcases optimizationSmoothRange_polynomial_bound α with
    ⟨θ, Cs, hθ0, hθ1, hCs, hsmoothPoly⟩
  rcases poly_absorb hθ0 hθ1 hCs with
    ⟨cs, hcs, Cs', hCs', hsmoothAbsorb⟩
  let c := min cr cs
  have hc : 0 < c := lt_min hcr hcs
  let Clarge := Cr + Cs'
  have hClarge : 0 < Clarge := add_pos hCr hCs'
  have hlarge : ∀ᶠ N : ℕ in Filter.atTop,
      (exceptionalCount N : ℝ) ≤
        Clarge * ((N : ℝ) * saving c N) := by
    filter_upwards [hrough, hsmoothPoly, Filter.eventually_ge_atTop 3] with
      N hroughN hsmoothN hN
    have hN1 : 1 ≤ N := by omega
    have hsmoothSave :
        (smoothRangeCount (optimizationRoughCutoff α N) N : ℝ) ≤
          Cs' * ((N : ℝ) * saving cs N) :=
      hsmoothN.trans (hsmoothAbsorb N hN)
    have hroughMono :
        Cr * ((N : ℝ) * saving cr N) ≤
          Cr * ((N : ℝ) * saving c N) := by
      apply mul_le_mul_of_nonneg_left _ hCr.le
      apply mul_le_mul_of_nonneg_left
        (saving_le_saving_of_le (min_le_left _ _) hN1)
      positivity
    have hsmoothMono :
        Cs' * ((N : ℝ) * saving cs N) ≤
          Cs' * ((N : ℝ) * saving c N) := by
      apply mul_le_mul_of_nonneg_left _ hCs'.le
      apply mul_le_mul_of_nonneg_left
        (saving_le_saving_of_le (min_le_right _ _) hN1)
      positivity
    have hsplit := exceptionalCount_eq_smoothRange_add_roughLarge
      (optimizationRoughCutoff α N) N
    have hsplitR : (exceptionalCount N : ℝ) =
        (smoothRangeCount (optimizationRoughCutoff α N) N : ℝ) +
          (roughLargeCount (optimizationRoughCutoff α N) N : ℝ) := by
      exact_mod_cast hsplit
    rw [hsplitR]
    calc
      (smoothRangeCount (optimizationRoughCutoff α N) N : ℝ) +
          (roughLargeCount (optimizationRoughCutoff α N) N : ℝ)
          ≤ Cs' * ((N : ℝ) * saving cs N) +
              Cr * ((N : ℝ) * saving cr N) :=
        add_le_add hsmoothSave hroughN
      _ ≤ Cs' * ((N : ℝ) * saving c N) +
            Cr * ((N : ℝ) * saving c N) :=
        add_le_add hsmoothMono hroughMono
      _ = Clarge * ((N : ℝ) * saving c N) := by
        dsimp [Clarge]
        ring
  rcases Filter.eventually_atTop.1 hlarge with ⟨T, hT⟩
  rcases finite_initial_saving_bound exceptionalCount hc T with
    ⟨Cinit, hCinit, hinit⟩
  refine ⟨c, hc, max Clarge Cinit, lt_of_lt_of_le hClarge
    (le_max_left _ _), ?_⟩
  intro N hN
  by_cases hTN : T ≤ N
  · have h := hT N hTN
    calc
      (exceptionalCount N : ℝ)
          ≤ Clarge * ((N : ℝ) * saving c N) := h
      _ ≤ max Clarge Cinit * ((N : ℝ) * saving c N) := by
        apply mul_le_mul_of_nonneg_right (le_max_left _ _)
        unfold saving
        positivity
      _ = max Clarge Cinit * (N : ℝ) * saving c N := by ring
  · have h := hinit N hN (lt_of_not_ge hTN)
    calc
      (exceptionalCount N : ℝ)
          ≤ Cinit * ((N : ℝ) * saving c N) := h
      _ ≤ max Clarge Cinit * ((N : ℝ) * saving c N) := by
        apply mul_le_mul_of_nonneg_right (le_max_right _ _)
        unfold saving
        positivity
      _ = max Clarge Cinit * (N : ℝ) * saving c N := by ring

theorem actualPaperFamily_primeExceptionalCount_mainBound
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    IsMainBound primeExceptionalCount :=
  prime_exceptional_of_main (actualPaperFamily_exceptionalCount_mainBound P)

theorem actualPaperFamily_primeExceptionalCount_primePi_saving
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      (primeExceptionalCount N : ℝ) ≤
        C * (primePi N : ℝ) * saving c N :=
  prime_exceptional_le_primePi_saving
    (actualPaperFamily_exceptionalCount_mainBound P)

theorem actualPaperFamily_primeExceptional_relativeDensityZero
    (P : Params) [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    Filter.Tendsto
      (fun N : ℕ => (primeExceptionalCount N : ℝ) / (primePi N : ℝ))
      Filter.atTop (nhds 0) :=
  prime_exceptional_relative_density_zero_of_main
    (actualPaperFamily_exceptionalCount_mainBound P)

/-- Closed explicit-parameter form of the paper's main theorem, supplied by
the corrected positive-window YU route. -/
theorem actualPaperFamily_exceptionalCount_mainBound_explicit :
    IsMainBound exceptionalCount := by
  letI : Fact (PhiProgressionGammaQuotientUpperYU Params.explicit) :=
    ⟨explicit_PhiProgressionGammaQuotientUpperYU_of_standard_ordinarySquarefree⟩
  exact actualPaperFamily_exceptionalCount_mainBound Params.explicit

end EscAnalytic
