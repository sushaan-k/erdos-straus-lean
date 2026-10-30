import ErdosStraus.Estimates.Mertens

/-! # Lemma 3.4: rough reciprocal sums over an initial segment

For `X^a ≤ x ≤ X^b` and `M ≤ X^{C₀}`, the sum of `1/n` over squarefree `n ≤ x` coprime to
`P(z) M` is `≍ log X / log z`, uniformly for `z` a fixed multiple of `zScale X = (log X)^4`.
The lower bound removes the coprimality conditions one modulus at a time through
`n = (n, D) · n/(n, D)`. The upper bound compares the products `∏ (1 + 1/p)` over `p ≤ x`
and over `p ≤ z`, using Mertens' estimate from Lemma 3.1.
-/

namespace ErdosStraus.RoughReciprocal

open Classical Estimates Filter
open scoped BigOperators

/-- The squarefree `n ∈ [1, N]` coprime to `B`. -/
noncomputable def squarefreeSupport (N B : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => Squarefree n ∧ Nat.Coprime n B)

/-- `∑ 1/n` over the squarefree `n ∈ [1, N]` coprime to `B`. -/
noncomputable def squarefreeRecip (N B : ℕ) : ℝ :=
  ∑ n ∈ squarefreeSupport N B, (1 : ℝ) / n

/-- `∑_{d ∣ B} 1/d`. -/
noncomputable def divisorRecip (B : ℕ) : ℝ :=
  ∑ d ∈ B.divisors, (1 : ℝ) / d

theorem squarefreeRecip_nonneg (N B : ℕ) : 0 ≤ squarefreeRecip N B :=
  Finset.sum_nonneg (by intro n _; positivity)

/-- Adding the condition `(n, D) = 1` loses at most the factor `∑_{d ∣ D} 1/d`: the map
`n ↦ ((n, D), n/(n, D))` is injective, and for squarefree `n` the second coordinate is
squarefree and coprime to `D`. -/
theorem remove_modulus (N B D : ℕ) (hD : 0 < D) :
    squarefreeRecip N B ≤ divisorRecip D * squarefreeRecip N (B * D) := by
  let S := squarefreeSupport N B
  let T := squarefreeSupport N (B * D)
  let f : ℕ → ℕ × ℕ := fun n => (Nat.gcd n D, n / Nat.gcd n D)
  let w : ℕ × ℕ → ℝ := fun t => (1 / (t.1 : ℝ)) * (1 / (t.2 : ℝ))
  have hmem : ∀ n ∈ S, f n ∈ D.divisors.product T := by
    intro n hn
    obtain ⟨hnI, hsq, hcop⟩ := Finset.mem_filter.mp hn
    have hnN := Finset.mem_Icc.mp hnI
    have hnpos : 0 < n := hnN.1
    have hgpos := Nat.gcd_pos_of_pos_left D hnpos
    have hqpos : 0 < n / Nat.gcd n D :=
      Nat.div_pos (Nat.gcd_le_left D hnpos) hgpos
    have hqd : n / Nat.gcd n D ∣ n := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n D)
    apply Finset.mem_product.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n D, hD.ne'⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨hqpos, (Nat.div_le_self n _).trans hnN.2⟩,
        hsq.squarefree_of_dvd hqd, ?_⟩⟩
    exact Nat.coprime_mul_iff_right.mpr
      ⟨hcop.coprime_dvd_left hqd, Nat.coprime_div_gcd_of_squarefree hsq hD.ne'⟩
  have hinj : Set.InjOn f (S : Set ℕ) := by
    intro n _ m _ h
    have hg := congrArg Prod.fst h
    have hq := congrArg Prod.snd h
    change Nat.gcd n D = Nat.gcd m D at hg
    change n / Nat.gcd n D = m / Nat.gcd m D at hq
    calc
      n = Nat.gcd n D * (n / Nat.gcd n D) := by
        rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left n D)]
      _ = Nat.gcd m D * (m / Nat.gcd m D) := congrArg₂ (· * ·) hg hq
      _ = m := by rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left m D)]
  have heq : (∑ n ∈ S, (1 : ℝ) / n) = ∑ t ∈ S.image f, w t := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    have hgpos := Nat.gcd_pos_of_pos_left D hnpos
    have hqpos := Nat.div_pos (Nat.gcd_le_left D hnpos) hgpos
    have hnprod : n = Nat.gcd n D * (n / Nat.gcd n D) := by
      rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left n D)]
    have hnR : (n : ℝ) = (Nat.gcd n D : ℝ) * (n / Nat.gcd n D : ℕ) := by
      exact_mod_cast hnprod
    dsimp [w, f]
    rw [hnR]
    exact one_div_mul_one_div _ _ |>.symm
  calc
    squarefreeRecip N B = ∑ t ∈ S.image f, w t := heq
    _ ≤ ∑ t ∈ D.divisors.product T, w t := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro t ht
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
        exact hmem n hn
      · intro t _ _
        dsimp [w]
        positivity
    _ = divisorRecip D * squarefreeRecip N (B * D) := by
      unfold divisorRecip squarefreeRecip
      change (∑ t ∈ D.divisors ×ˢ T, w t) = _
      rw [Finset.sum_product, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]

theorem harmonic_le_two_mul_squarefreeRecip (N : ℕ) :
    (harmonic N : ℝ) ≤ 2 * squarefreeRecip N 1 := by
  have h := harmonic_le_squarefree_mul_square_recip N
  have hs := square_recip_sum_le_two_for_coprime_lower N
  have hnonneg : 0 ≤ ∑ n ∈ (Finset.Icc 1 N).filter Squarefree, (1 : ℝ) / n :=
    Finset.sum_nonneg (by intro n _; positivity)
  have hle := h.trans (mul_le_mul_of_nonneg_left hs hnonneg)
  simpa [squarefreeRecip, squarefreeSupport, mul_comm] using hle

/-- `∑ 1/n` over squarefree `n ≤ x` coprime to `P(z) M`, where `P(z)` is the
product of the primes `≤ z`. -/
noncomputable def initialAt (z x : ℝ) (M : ℕ) : ℝ :=
  squarefreeRecip ⌊x⌋₊ (primeProductBelow z * M)

theorem primeProduct_mono {z w : ℝ} (hzw : z ≤ w) :
    primeProductBelow z ∣ primeProductBelow w := by
  unfold primeProductBelow
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  obtain ⟨hpI, hpP⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hpI).1, (Finset.mem_Icc.mp hpI).2.trans (Nat.floor_mono hzw)⟩, hpP⟩

theorem squarefree_dvd_primeProduct {N n : ℕ} (hn : Squarefree n) (hN : n ≤ N) :
    n ∣ primeProductBelow (N : ℝ) := by
  rw [← Nat.prod_primeFactors_of_squarefree hn]
  unfold primeProductBelow
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).two_le, ?_⟩,
    Nat.prime_of_mem_primeFactors hp⟩
  simpa using (Nat.le_of_dvd (Nat.pos_of_ne_zero hn.ne_zero)
    (Nat.dvd_of_mem_primeFactors hp)).trans hN

theorem divisorRecip_primeProduct_lower (z : ℝ) (hz : 0 ≤ z) :
    Real.log z ≤ 2 * divisorRecip (primeProductBelow z) := by
  have h := harmonic_le_two_mul_squarefreeRecip ⌊z⌋₊
  have hsub : squarefreeRecip ⌊z⌋₊ 1 ≤ divisorRecip (primeProductBelow z) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨hnI, hsq, _⟩ := Finset.mem_filter.mp hn
      apply Nat.mem_divisors.mpr
      refine ⟨?_, (primeProductBelow_pos z).ne'⟩
      exact (squarefree_dvd_primeProduct hsq (Finset.mem_Icc.mp hnI).2).trans
        (primeProduct_mono (Nat.floor_le hz))
    · intro n _ _
      positivity
  exact (log_le_harmonic_floor z hz).trans (h.trans (by linarith))

theorem divisorRecip_primeProduct_upper_of_mertens
    (hMertens : PrimeRecipSharpMertensUpperBound) :
    ∃ C Z₀ : ℝ, 0 < C ∧ 2 ≤ Z₀ ∧ ∀ z : ℝ, Z₀ ≤ z →
      divisorRecip (primeProductBelow z) ≤ C * Real.log z := by
  obtain ⟨K, Z₀, hK⟩ := hMertens
  refine ⟨Real.exp K, max Z₀ 2, Real.exp_pos _, le_max_right _ _, ?_⟩
  intro z hz
  have hz2 : 2 ≤ z := (le_max_right Z₀ 2).trans hz
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  calc
    divisorRecip (primeProductBelow z) ≤
        Real.exp (∑ p ∈ (primeProductBelow z).primeFactors, (p : ℝ)⁻¹) :=
      divisor_recip_sum_le_exp_primeFactor_recip_sum_of_squarefree
        (primeProductBelow_squarefree z)
    _ ≤ Real.exp (Real.log (Real.log z) + K) := by
      apply Real.exp_le_exp.mpr
      rw [primeProductBelow_primeFactors_eq]
      exact hK z ((le_max_left _ _).trans hz)
    _ = Real.exp K * Real.log z := by
      rw [Real.exp_add, Real.exp_log hlogz]
      ring

theorem squarefreeRecip_mul_small_product_le (N : ℕ) (z : ℝ)
    (hz : z ≤ (N : ℝ)) :
    squarefreeRecip N (primeProductBelow z) * divisorRecip (primeProductBelow z) ≤
      divisorRecip (primeProductBelow (N : ℝ)) := by
  let A := (primeProductBelow z).primeFactors
  let B := (primeProductBelow (N : ℝ)).primeFactors
  let Q := ∏ p ∈ B \ A, p
  have hAB : A ⊆ B := Nat.primeFactors_mono (primeProduct_mono hz)
    (primeProductBelow_pos (N : ℝ)).ne'
  have hprimes : ∀ p ∈ B \ A, Nat.Prime p := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1
  have hQsq : Squarefree Q := finite_prime_product_squarefree _ hprimes
  have hQpf : Q.primeFactors = B \ A := Nat.primeFactors_prod hprimes
  have hsub : squarefreeSupport N (primeProductBelow z) ⊆ Q.divisors := by
    intro n hn
    obtain ⟨hnI, hsq, hcop⟩ := Finset.mem_filter.mp hn
    apply Nat.mem_divisors.mpr
    refine ⟨?_, hQsq.ne_zero⟩
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    apply Finset.prod_dvd_prod_of_subset
    intro p hp
    apply Finset.mem_sdiff.mpr
    constructor
    · exact (Nat.primeFactors_mono
        (squarefree_dvd_primeProduct hsq (Finset.mem_Icc.mp hnI).2)
        (primeProductBelow_pos (N : ℝ)).ne') hp
    · intro hpA
      have hdiv := Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hpA)
      rw [hcop.gcd_eq_one] at hdiv
      exact (Nat.prime_of_mem_primeFactors hp).not_dvd_one hdiv
  have hmass : squarefreeRecip N (primeProductBelow z) ≤ divisorRecip Q :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro n _ _; positivity)
  have heq : divisorRecip Q * divisorRecip (primeProductBelow z) =
      divisorRecip (primeProductBelow (N : ℝ)) := by
    simp only [divisorRecip,
      divisor_recip_sum_eq_primeFactorProduct_one_add_inv hQsq,
      divisor_recip_sum_eq_primeFactorProduct_one_add_inv (primeProductBelow_squarefree z),
      divisor_recip_sum_eq_primeFactorProduct_one_add_inv
        (primeProductBelow_squarefree (N : ℝ)), hQpf]
    exact Finset.prod_sdiff hAB
  exact (mul_le_mul_of_nonneg_right hmass (Finset.sum_nonneg
    (by intro n _; positivity))).trans_eq heq

theorem squarefreeRecip_upper_of_mertens
    (hMertens : PrimeRecipSharpMertensUpperBound) :
    ∃ C Z₀ : ℝ, 0 < C ∧ 2 ≤ Z₀ ∧ ∀ (z : ℝ) (N : ℕ),
      Z₀ ≤ (N : ℝ) → 1 < z → z ≤ (N : ℝ) →
      squarefreeRecip N (primeProductBelow z) ≤ C * Real.log N / Real.log z := by
  obtain ⟨C, Z₀, hC, hZ₀, hu⟩ := divisorRecip_primeProduct_upper_of_mertens hMertens
  refine ⟨2 * C, Z₀, by positivity, hZ₀, ?_⟩
  intro z N hN hz hzN
  have hlogz := Real.log_pos hz
  have hl := divisorRecip_primeProduct_lower z (by linarith)
  have hprod := squarefreeRecip_mul_small_product_le N z hzN
  have hmass := squarefreeRecip_nonneg N (primeProductBelow z)
  have hglobal := hu N hN
  apply (le_div_iff₀ hlogz).2
  nlinarith

theorem auxiliary_divisorRecip_bounded (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ M : ℕ, (M : ℝ) ≤ X ^ C₀ →
      divisorRecip (auxiliaryTailModulus X M) ≤ Real.exp 1 := by
  refine ⟨max (Real.exp (Real.exp 1)) (Real.exp (max 2 (C₀ + 1))), ?_⟩
  intro X hX M hM
  have hXee := (le_max_left _ _).trans hX
  have hXpos : 0 < X := (Real.exp_pos _).trans_le hXee
  have hlogX : Real.exp 1 ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).2 hXee
  have hlogXpos : 0 < Real.log X := (Real.exp_pos 1).trans_le hlogX
  have hloglog : 1 ≤ Real.log (Real.log X) :=
    (Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le hlogX)).2 hlogX
  have hXexp2 : Real.exp 2 ≤ X :=
    (Real.exp_le_exp.mpr (le_max_left 2 (C₀ + 1))).trans ((le_max_right _ _).trans hX)
  have hXexp1 : Real.exp 1 ≤ X :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hXexp2
  have hzpos : 0 < zScale X := by unfold zScale; positivity
  have hlogz : 1 ≤ Real.log (zScale X) := by
    unfold zScale
    rw [Real.log_pow]
    norm_num
    linarith
  let q : ℝ := ((⌊zScale X⌋₊ + 1 : ℕ) : ℝ)
  have hzq : zScale X ≤ q := by
    simpa [q, Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (zScale X)).le
  have hlogq : 1 ≤ Real.log q :=
    hlogz.trans (Real.log_le_log hzpos hzq)
  have hcard := auxiliaryTailModulus_card_le_log_div_log
    X M hXexp1
  have hlogM := log_natCast_add_one_le_add_one_mul_log_of_natCast_le_rpow M hXexp2 hC₀ hM
  have hlogMnonneg : 0 ≤ Real.log ((M : ℝ) + 1) :=
    Real.log_nonneg (by norm_cast; omega)
  have hcard' : ((auxiliaryTailModulus X M).primeFactors.card : ℝ) ≤
      (C₀ + 1) * Real.log X := by
    apply hcard.trans
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hlogq)).2
    nlinarith
  have hcoeff : ((C₀ + 1) * Real.log X) / zScale X ≤ 1 := by
    have h := two_mul_C_add_one_mul_log_div_zScale_le_eps
      (C := C₀) (eps := 2) (by simpa using (le_max_right _ _).trans hX)
      hC₀ (by norm_num)
    have h' : 2 * (((C₀ + 1) * Real.log X) / zScale X) ≤ 2 := by
      convert h using 1
      ring
    linarith
  have hsum : (∑ p ∈ (auxiliaryTailModulus X M).primeFactors, (p : ℝ)⁻¹) ≤ 1 := by
    calc
      _ ≤ ∑ _p ∈ (auxiliaryTailModulus X M).primeFactors, (zScale X)⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        have hpq : q ≤ (p : ℝ) := by
          dsimp [q]
          exact_mod_cast auxiliaryTailModulus_succ_floor_zScale_le_prime hp
        exact inv_anti₀ hzpos (hzq.trans hpq)
      _ = ((auxiliaryTailModulus X M).primeFactors.card : ℝ) / zScale X := by
        simp [div_eq_mul_inv]
      _ ≤ ((C₀ + 1) * Real.log X) / zScale X :=
        div_le_div_of_nonneg_right hcard' hzpos.le
      _ ≤ 1 := hcoeff
  have hsq : Squarefree (auxiliaryTailModulus X M) := by
    unfold auxiliaryTailModulus
    apply finite_prime_product_squarefree
    intro p hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  exact (divisor_recip_sum_le_exp_primeFactor_recip_sum_of_squarefree hsq).trans
    (Real.exp_le_exp.mpr hsum)

theorem initialAt_eq_tail (X z x : ℝ) {M : ℕ} (hM : 0 < M)
    (hz : zScale X ≤ z) :
    initialAt z x M = squarefreeRecip ⌊x⌋₊
      (primeProductBelow z * auxiliaryTailModulus X M) := by
  unfold initialAt squarefreeRecip squarefreeSupport
  congr 1
  ext n
  simp only [Finset.mem_filter, Nat.coprime_mul_iff_right]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro hcop
  have hrough : Nat.Coprime n (roughModulus X) :=
    hcop.coprime_dvd_right (primeProduct_mono hz)
  simpa [auxiliaryModulus_eq_self_of_pos hM] using
    coprime_auxiliaryModulus_iff_coprime_tail_of_coprime_rough (M := M) hrough

theorem initialAt_lower_of_product_bounds (X z x C : ℝ) (M : ℕ)
    (hM : 0 < M) (hz : zScale X ≤ z) (hx : 0 ≤ x)
    (hC : 0 < C) (hz1 : 1 < z)
    (hsmall : divisorRecip (primeProductBelow z) ≤ C * Real.log z)
    (htail : divisorRecip (auxiliaryTailModulus X M) ≤ Real.exp 1) :
    Real.log x / (2 * C * Real.exp 1 * Real.log z) ≤ initialAt z x M := by
  have hmass := squarefreeRecip_nonneg ⌊x⌋₊ (primeProductBelow z)
  have hmain : 0 ≤ initialAt z x M := squarefreeRecip_nonneg _ _
  have hlogz := Real.log_pos hz1
  have h₁ := remove_modulus ⌊x⌋₊ 1 (primeProductBelow z) (primeProductBelow_pos z)
  simp only [one_mul] at h₁
  have h₂ := remove_modulus ⌊x⌋₊ (primeProductBelow z)
    (auxiliaryTailModulus X M) (auxiliaryTailModulus_pos X M)
  rw [← initialAt_eq_tail X z x hM hz] at h₂
  have hHN := (log_le_harmonic_floor x hx).trans
    (harmonic_le_two_mul_squarefreeRecip ⌊x⌋₊)
  have hcost : Real.log x ≤ (2 * C * Real.exp 1 * Real.log z) * initialAt z x M := by
    calc
      Real.log x ≤ 2 * squarefreeRecip ⌊x⌋₊ 1 := hHN
      _ ≤ 2 * (divisorRecip (primeProductBelow z) *
          squarefreeRecip ⌊x⌋₊ (primeProductBelow z)) := by gcongr
      _ ≤ 2 * ((C * Real.log z) *
          (divisorRecip (auxiliaryTailModulus X M) * initialAt z x M)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul hsmall h₂ hmass (by positivity)
      _ ≤ 2 * ((C * Real.log z) * (Real.exp 1 * initialAt z x M)) := by
        gcongr
      _ = _ := by ring
  apply (div_le_iff₀ (by positivity)).2
  simpa [mul_comm] using hcost

theorem scaled_cutoff_eventually (A₀ a : ℝ) (hA₀ : 1 ≤ A₀) (ha : 0 < a) :
    ∀ᶠ X : ℝ in Filter.atTop,
      1 < A₀ * zScale X ∧ zScale X ≤ A₀ * zScale X ∧
        A₀ * zScale X ≤ UScale X ∧ A₀ * zScale X + 1 ≤ X ^ a := by
  have hzTop : Filter.Tendsto zScale Filter.atTop Filter.atTop :=
    (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop
  have hpow := (tendsto_rpow_atTop (by linarith : 0 < a / 2)).eventually
    (Filter.eventually_ge_atTop (A₀ + 1))
  obtain ⟨XU, hU⟩ := eventually_UScale_le_rpow (δ := a / 2) (by linarith)
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 2),
    Filter.eventually_ge_atTop XU, hzTop.eventually (Filter.eventually_ge_atTop A₀),
    hpow] with X hX hXU hA hpow
  have hXpos : 0 < X := (Real.exp_pos 2).trans_le hX
  have hlogX : 2 ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).2 hX
  have hz : 1 < zScale X := by
    unfold zScale
    nlinarith [sq_nonneg ((Real.log X) ^ 2 - 4)]
  have hzpos := hz.le.trans_lt' zero_lt_one
  have hbase : zScale X ≤ A₀ * zScale X := by nlinarith
  have hUeq : zScale X * zScale X = UScale X := by unfold zScale UScale; ring
  have hzU : zScale X ≤ UScale X := by rw [← hUeq]; nlinarith
  refine ⟨hz.trans_le hbase, hbase, ?_, ?_⟩
  · rw [← hUeq]
    exact mul_le_mul_of_nonneg_right hA hzpos.le
  · calc
      A₀ * zScale X + 1 ≤ (A₀ + 1) * UScale X := by nlinarith
      _ ≤ X ^ (a / 2) * X ^ (a / 2) :=
        mul_le_mul hpow (hU X hXU) (by unfold UScale; positivity)
          (Real.rpow_nonneg hXpos.le _)
      _ = X ^ a := by
        rw [← Real.rpow_add hXpos]
        congr 1
        ring

/-- Lemma 3.4 at `z = A₀ · zScale X`, assuming the Mertens bound
`∑_{p ≤ z} 1/p ≤ log log z + O(1)`. The constants `c, C` do not depend on `A₀`; only `X₀`
does. -/
theorem initial_two_sided_of_mertens
    (hMertens : PrimeRecipSharpMertensUpperBound)
    (a b C₀ : ℝ) (ha : 0 < a) (hab : a ≤ b) (hC₀ : 0 ≤ C₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ A₀ : ℝ, 1 ≤ A₀ → ∃ X₀ : ℝ, 1 < X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → ∀ M : ℕ, 0 < M → (M : ℝ) ≤ X ^ C₀ →
      ∀ x : ℝ, X ^ a ≤ x → x ≤ X ^ b →
        c * (Real.log X / Real.log (A₀ * zScale X)) ≤
            initialAt (A₀ * zScale X) x M ∧
          initialAt (A₀ * zScale X) x M ≤
            C * (Real.log X / Real.log (A₀ * zScale X)) := by
  obtain ⟨D, Z₀, hD, hZ₀, hprod⟩ := divisorRecip_primeProduct_upper_of_mertens hMertens
  obtain ⟨E, ZE, hE, hZE, hupper⟩ := squarefreeRecip_upper_of_mertens hMertens
  obtain ⟨XT, hT⟩ := auxiliary_divisorRecip_bounded C₀ hC₀
  refine ⟨a / (2 * D * Real.exp 1), E * b, by positivity,
    mul_pos hE (ha.trans_le hab), ?_⟩
  intro A₀ hA₀
  have hzTop : Filter.Tendsto zScale Filter.atTop Filter.atTop :=
    (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop
  have hevent : ∀ᶠ X : ℝ in Filter.atTop,
      Real.exp 2 ≤ X ∧ XT ≤ X ∧ max Z₀ ZE ≤ zScale X ∧
        (1 < A₀ * zScale X ∧ zScale X ≤ A₀ * zScale X ∧
          A₀ * zScale X ≤ UScale X ∧ A₀ * zScale X + 1 ≤ X ^ a) := by
    filter_upwards [Filter.eventually_ge_atTop (Real.exp 2), Filter.eventually_ge_atTop XT,
      hzTop.eventually (Filter.eventually_ge_atTop (max Z₀ ZE)),
      scaled_cutoff_eventually A₀ a hA₀ ha] with X hX hXT hz hscale
    exact ⟨hX, hXT, hz, hscale⟩
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max X₁ 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro X hX M hM hMX x hx hxupper
  have hlarge := hX₁ X ((le_max_left _ _).trans hX)
  obtain ⟨hXexp, hXT, hzbound, hz1, hzbase, hzU, hzcut⟩ := hlarge
  have hXpos : 0 < X := (Real.exp_pos 2).trans_le hXexp
  have hxpos : 0 < x := (Real.rpow_pos_of_pos hXpos a).trans_le hx
  have hlogz := Real.log_pos hz1
  have hzD : Z₀ ≤ A₀ * zScale X :=
    ((le_max_left Z₀ ZE).trans hzbound).trans hzbase
  have hzE : ZE ≤ A₀ * zScale X :=
    ((le_max_right Z₀ ZE).trans hzbound).trans hzbase
  have hfloor : A₀ * zScale X ≤ (⌊x⌋₊ : ℝ) := by
    have hlt := Nat.lt_floor_add_one x
    linarith
  have hNpos : 0 < ⌊x⌋₊ := by exact_mod_cast (lt_trans zero_lt_one (hz1.trans_le hfloor))
  have hlogx_lower : a * Real.log X ≤ Real.log x := by
    simpa only [Real.log_rpow hXpos] using
      Real.log_le_log (Real.rpow_pos_of_pos hXpos a) hx
  have hlogx_upper : Real.log x ≤ b * Real.log X := by
    simpa only [Real.log_rpow hXpos] using Real.log_le_log hxpos hxupper
  have hlower := initialAt_lower_of_product_bounds X (A₀ * zScale X) x D M hM
    hzbase hxpos.le hD hz1 (hprod _ hzD) (hT X hXT M hMX)
  refine ⟨?_, ?_⟩
  · calc
      (a / (2 * D * Real.exp 1)) * (Real.log X / Real.log (A₀ * zScale X)) =
          (a * Real.log X) / (2 * D * Real.exp 1 * Real.log (A₀ * zScale X)) := by ring
      _ ≤ Real.log x / (2 * D * Real.exp 1 * Real.log (A₀ * zScale X)) :=
        div_le_div_of_nonneg_right hlogx_lower (by positivity)
      _ ≤ initialAt (A₀ * zScale X) x M := hlower
  · have hdrop : initialAt (A₀ * zScale X) x M ≤
        squarefreeRecip ⌊x⌋₊ (primeProductBelow (A₀ * zScale X)) := by
      unfold initialAt squarefreeRecip
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        obtain ⟨hnI, hnS, hnC⟩ := Finset.mem_filter.mp hn
        exact Finset.mem_filter.mpr ⟨hnI, hnS,
          hnC.coprime_dvd_right (dvd_mul_right _ M)⟩
      · intro n _ _
        positivity
    calc
      initialAt (A₀ * zScale X) x M ≤
          squarefreeRecip ⌊x⌋₊ (primeProductBelow (A₀ * zScale X)) := hdrop
      _ ≤ E * Real.log ⌊x⌋₊ / Real.log (A₀ * zScale X) :=
        hupper _ _ (hzE.trans hfloor) hz1 hfloor
      _ ≤ E * Real.log x / Real.log (A₀ * zScale X) := by
        apply div_le_div_of_nonneg_right _ hlogz.le
        apply mul_le_mul_of_nonneg_left _ hE.le
        exact Real.log_le_log (by exact_mod_cast hNpos) (Nat.floor_le hxpos.le)
      _ ≤ E * (b * Real.log X) / Real.log (A₀ * zScale X) := by
        gcongr
      _ = (E * b) * (Real.log X / Real.log (A₀ * zScale X)) := by ring

/-- Mertens' bound `∑_{p ≤ z} 1/p ≤ log log z + O(1)` (Lemma 3.1). -/
theorem prime_reciprocal_mertens : PrimeRecipSharpMertensUpperBound :=
  PrimeRecipSharpMertensUpperBound_of_nat
    (PrimeRecipSharpMertensNatUpperBound_of_natRealConstant
      (natRealMertens_of_mertensDefect
        PrimeEstimates.Mertens.sharp_upper))

/-- Lemma 3.4 at `z = A₀ · zScale X`. -/
theorem initial_two_sided (a b C₀ : ℝ) (ha : 0 < a) (hab : a ≤ b) (hC₀ : 0 ≤ C₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ A₀ : ℝ, 1 ≤ A₀ → ∃ X₀ : ℝ, 1 < X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → ∀ M : ℕ, 0 < M → (M : ℝ) ≤ X ^ C₀ →
      ∀ x : ℝ, X ^ a ≤ x → x ≤ X ^ b →
        c * (Real.log X / Real.log (A₀ * zScale X)) ≤
            initialAt (A₀ * zScale X) x M ∧
          initialAt (A₀ * zScale X) x M ≤
            C * (Real.log X / Real.log (A₀ * zScale X)) :=
  initial_two_sided_of_mertens prime_reciprocal_mertens a b C₀ ha hab hC₀

theorem initialAt_zScale_eq_roughInitial (X σ : ℝ) (M : ℕ) :
    initialAt (zScale X) (X ^ σ) (auxiliaryModulus M) = roughInitial X M σ := by
  unfold initialAt squarefreeRecip squarefreeSupport roughInitial
  congr 1
  ext n
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Nat.coprime_mul_iff_right, roughModulus]

/-- Lemma 3.4 for `roughInitial X M σ`, that is, at `z = zScale X`, `x = X^σ` and the
modulus `max 1 M`. -/
theorem roughInitial_two_sided (σ C₀ : ℝ) (hσ : 0 < σ) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ M : ℕ, (M : ℝ) ≤ X ^ C₀ →
        0 < Real.log X ∧ 0 < Real.log (zScale X) ∧
          0 < Real.log X / Real.log (zScale X) ∧
          0 ≤ roughInitial X M σ ∧
          c * (Real.log X / Real.log (zScale X)) ≤ roughInitial X M σ ∧
          roughInitial X M σ ≤ C * (Real.log X / Real.log (zScale X)) ∧
          |roughInitial X M σ| ≤ C * (Real.log X / Real.log (zScale X)) := by
  obtain ⟨c, C, hc, hC, h⟩ := initial_two_sided σ σ (max C₀ 0) hσ le_rfl
    (le_max_right _ _)
  obtain ⟨X₁, _, hX₁⟩ := h 1 le_rfl
  refine ⟨c, C, max X₁ (Real.exp 2), hc, hC, ?_⟩
  intro X hX M hM
  have hXX := (le_max_left X₁ _).trans hX
  have hXe := (le_max_right X₁ _).trans hX
  have hX1 : 1 < X := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).trans_le hXe
  have haux : (auxiliaryModulus M : ℝ) ≤ X ^ max C₀ 0 := by
    simp only [auxiliaryModulus, Nat.cast_max, Nat.cast_one]
    apply max_le
    · exact Real.one_le_rpow hX1.le (le_max_right _ _)
    · exact hM.trans (Real.rpow_le_rpow_of_exponent_le hX1.le (le_max_left _ _))
  have hb := hX₁ X hXX (auxiliaryModulus M) (auxiliaryModulus_pos M) haux
    (X ^ σ) le_rfl le_rfl
  simp only [one_mul, initialAt_zScale_eq_roughInitial] at hb
  have hlogX := Real.log_pos hX1
  have hlogz := log_zScale_pos_of_exp_two_le hXe
  have hn := roughInitial_nonneg X M σ
  exact ⟨hlogX, hlogz, div_pos hlogX hlogz, hn, hb.1, hb.2,
    by simpa [abs_of_nonneg hn] using hb.2⟩

end ErdosStraus.RoughReciprocal
