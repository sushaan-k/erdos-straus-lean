import ErdosStraus.BombieriVinogradov.PNT.ZetaBounds

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

/-!
# The Dirichlet series for `L(s, χ)` and `L'(s, χ)` on `re s > 0`

For a nonprincipal Dirichlet character `χ` modulo `q`, the partial sums of
`∑ χ(n) n^{-s}` and `-∑ χ(n) log n · n^{-s}` converge locally uniformly on `re s > 0`
to `L(s, χ)` and `L'(s, χ)`. The proof is Abel summation with `‖∑_{n<N} χ(n)‖ ≤ q`
and a total variation bound for the weights, followed by the identity theorem.
The last section integrates `L'(s, χ)` along horizontal segments.
-/

section

/-! ## Character sums and Abel summation -/

open Complex Finset

namespace BombieriVinogradov.WeakStrip

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
lemma character_norm_le_one (χ : DirichletCharacter ℂ q) (n : ℕ) : ‖χ n‖ ≤ 1 := by
  exact DirichletCharacter.norm_le_one χ (n : ZMod q)

lemma sum_one_period_eq_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∑ n ∈ range q, χ n = 0 := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
      rw [← Fin.sum_univ_eq_sum_range]
      calc
        ∑ i : Fin (q + 1), χ (i : ℕ) =
            ∑ i : Fin (q + 1), χ ((ZMod.finEquiv (q + 1)) i) := by
          apply Finset.sum_congr rfl
          intro i _
          congr 1
          apply ZMod.val_injective
          rw [ZMod.val_natCast_of_lt i.isLt]
          rfl
        _ = ∑ a : ZMod (q + 1), χ a :=
          Equiv.sum_comp (ZMod.finEquiv (q + 1)).toEquiv χ
        _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ

lemma sum_aligned_period_eq_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (k : ℕ) :
    ∑ i ∈ range q, χ (k * q + i) = 0 := by
  have hterm (i : ℕ) : χ (k * q + i) = χ i := by
    simp only [ZMod.natCast_self, mul_zero, zero_add]
  simpa only [hterm] using sum_one_period_eq_zero χ hχ

lemma sum_mul_period_eq_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∀ k : ℕ, ∑ i ∈ range (k * q), χ i = 0 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, sum_range_add, ih, zero_add]
      simpa [Nat.add_comm] using sum_aligned_period_eq_zero χ hχ k

/-- `‖∑_{n<N} χ(n)‖ ≤ q` for a nonprincipal character `χ` modulo `q`. -/
lemma norm_sum_range_character_le_modulus (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ range N, χ n‖ ≤ q := by
  have hq : 0 < q := NeZero.pos q
  have hN : N = (N / q) * q + N % q := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod N q).symm
  rw [hN, sum_range_add, sum_mul_period_eq_zero χ hχ, zero_add]
  have hshift (i : ℕ) : χ (((N / q) * q + i : ℕ)) = χ i := by
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
  simp_rw [hshift]
  calc
    ‖∑ i ∈ range (N % q), χ i‖ ≤ ∑ i ∈ range (N % q), ‖χ i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ range (N % q), (1 : ℝ) := sum_le_sum fun i _ => character_norm_le_one χ i
    _ = ((N % q : ℕ) : ℝ) := by simp
    _ ≤ q := by exact_mod_cast (Nat.le_of_lt (Nat.mod_lt N hq))

omit [NeZero q] in
/-- Abel summation over `[m, n)` against the prefix sums of `χ`. -/
lemma abel_Ico (χ : DirichletCharacter ℂ q) (f : ℕ → ℂ) {m n : ℕ} (hmn : m < n) :
    ∑ i ∈ Ico m n, f i * χ i =
      f (n - 1) * (∑ i ∈ range n, χ i) - f m * (∑ i ∈ range m, χ i) -
        ∑ i ∈ Ico m (n - 1), (f (i + 1) - f i) * (∑ j ∈ range (i + 1), χ j) := by
  simpa only [smul_eq_mul] using Finset.sum_Ico_by_parts f (fun i : ℕ => χ i) hmn

omit [NeZero q] in
lemma dirichlet_cpow_abel_Ico (χ : DirichletCharacter ℂ q) (s : ℂ) {m n : ℕ}
    (hmn : m < n) :
    ∑ k ∈ Ico m n, (k : ℂ) ^ (-s) * χ k =
      (n - 1 : ℕ) ^ (-s) * (∑ k ∈ range n, χ k) -
        (m : ℂ) ^ (-s) * (∑ k ∈ range m, χ k) -
        ∑ k ∈ Ico m (n - 1),
          (((k + 1 : ℕ) : ℂ) ^ (-s) - (k : ℂ) ^ (-s)) *
            (∑ j ∈ range (k + 1), χ j) := by
  exact abel_Ico χ (fun k : ℕ => (k : ℂ) ^ (-s)) hmn

end BombieriVinogradov.WeakStrip

end

section

/-!
## Total variation of the weights `x^{-s}` and `-log x · x^{-s}`

Each difference `w(k + 1) - w(k)` is bounded by `∫_k^{k+1} ‖w'(x)‖ dx`, so no monotonicity
of the complex weights is needed.
-/

open Complex Finset Set MeasureTheory

namespace BombieriVinogradov.AbelWeight

/-- The weight `x ↦ x^{-s}` on the positive reals. -/
noncomputable def cpowWeight (s : ℂ) (x : ℝ) : ℂ := (x : ℂ) ^ (-s)

/-- The derivative `-s x^{-s-1}` of `cpowWeight s` in `x`. -/
noncomputable def cpowWeightDeriv (s : ℂ) (x : ℝ) : ℂ :=
  (-s) * (x : ℂ) ^ (-s - 1)

lemma hasDerivAt_cpowWeight (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (cpowWeight s) (cpowWeightDeriv s x) x := by
  have h := (@HasDerivAt.cpow_const _ _ _ (-s) (hasDerivAt_id (x : ℂ))
    (Or.inl (by simpa [Complex.slitPlane] using hx))).comp_ofReal
  convert! h using 1; simp [cpowWeightDeriv]

lemma norm_cpowWeightDeriv (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖cpowWeightDeriv s x‖ = ‖s‖ * x ^ (-s.re - 1) := by
  rw [cpowWeightDeriv, norm_mul, norm_neg,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma norm_cpowWeight_succ_sub_le_integral (s : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    ‖cpowWeight s (k + 1) - cpowWeight s k‖ ≤
      ∫ x in (k : ℝ)..(k + 1 : ℝ), ‖s‖ * x ^ (-s.re - 1) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hkle : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
  have hpos : ∀ x ∈ uIcc (k : ℝ) (k + 1 : ℝ), 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hkle] at hx
    exact hk0.trans_le hx.1
  have hder : ∀ x ∈ uIcc (k : ℝ) (k + 1 : ℝ),
      HasDerivAt (cpowWeight s) (cpowWeightDeriv s x) x :=
    fun x hx => hasDerivAt_cpowWeight s (hpos x hx)
  have heq : cpowWeightDeriv s = fun x => (-s) * cpowWeight (s + 1) x := by
    funext x
    unfold cpowWeightDeriv cpowWeight
    rw [show -(s + 1) = -s - 1 by ring]
  have hcont : ContinuousOn (cpowWeightDeriv s) (uIcc (k : ℝ) (k + 1 : ℝ)) := by
    intro x hx
    rw [heq]
    exact (continuousAt_const.mul
      (hasDerivAt_cpowWeight (s + 1) (hpos x hx)).continuousAt).continuousWithinAt
  have hint : IntervalIntegrable (cpowWeightDeriv s) volume (k : ℝ) (k + 1 : ℝ) :=
    hcont.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
  calc
    ‖cpowWeight s (k + 1) - cpowWeight s k‖ =
        ‖∫ x in (k : ℝ)..(k + 1 : ℝ), cpowWeightDeriv s x‖ := by rw [hFTC]
    _ ≤ ∫ x in (k : ℝ)..(k + 1 : ℝ), ‖cpowWeightDeriv s x‖ :=
      intervalIntegral.norm_integral_le_integral_norm hkle
    _ = ∫ x in (k : ℝ)..(k + 1 : ℝ), ‖s‖ * x ^ (-s.re - 1) := by
      apply intervalIntegral.integral_congr
      intro x hx
      change ‖cpowWeightDeriv s x‖ = ‖s‖ * x ^ (-s.re - 1)
      exact norm_cpowWeightDeriv s (hpos x hx)

lemma norm_cpowWeight_succ_sub_le (s : ℂ) (hs : 0 < s.re) {k : ℕ} (hk : 1 ≤ k) :
    ‖cpowWeight s (k + 1) - cpowWeight s k‖ ≤
      (‖s‖ / s.re) * ((k : ℝ) ^ (-s.re) - (k + 1 : ℝ) ^ (-s.re)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  calc
    ‖cpowWeight s (k + 1) - cpowWeight s k‖ ≤
        ∫ x in (k : ℝ)..(k + 1 : ℝ), ‖s‖ * x ^ (-s.re - 1) :=
      norm_cpowWeight_succ_sub_le_integral s hk
    _ = ‖s‖ * (((k + 1 : ℝ) ^ (-s.re) - (k : ℝ) ^ (-s.re)) / (-s.re)) := by
      rw [intervalIntegral.integral_const_mul, integral_rpow]
      · congr 1
        ring_nf
      · right
        constructor
        · linarith
        · rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ k)]
          exact fun h0 => (not_le_of_gt hk0) h0.1
    _ = (‖s‖ / s.re) * ((k : ℝ) ^ (-s.re) - (k + 1 : ℝ) ^ (-s.re)) := by
      field_simp
      ring

/-- The total variation of `k ↦ k^{-s}` on `[m, n]`, by telescoping. -/
lemma sum_norm_cpowWeight_sub_le_sub (s : ℂ) (hs : 0 < s.re) {m n : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∑ k ∈ Ico m n, ‖cpowWeight s (k + 1) - cpowWeight s k‖ ≤
      (‖s‖ / s.re) * ((m : ℝ) ^ (-s.re) - (n : ℝ) ^ (-s.re)) := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
      rw [sum_Ico_succ_top hmn]
      calc
        _ ≤ (‖s‖ / s.re) * ((m : ℝ) ^ (-s.re) - (n : ℝ) ^ (-s.re)) +
            (‖s‖ / s.re) * ((n : ℝ) ^ (-s.re) - (n + 1 : ℝ) ^ (-s.re)) :=
          add_le_add ih (norm_cpowWeight_succ_sub_le s hs (hm.trans hmn))
        _ = _ := by
          norm_num [Nat.cast_add, Nat.cast_one, add_comm]
          ring

/-- The total variation of `k ↦ k^{-s}` on `[m, n]` is at most `(‖s‖ / re s) m^{-re s}`. -/
lemma sum_norm_cpowWeight_sub_le (s : ℂ) (hs : 0 < s.re) {m n : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∑ k ∈ Ico m n, ‖cpowWeight s (k + 1) - cpowWeight s k‖ ≤
      (‖s‖ / s.re) * (m : ℝ) ^ (-s.re) := by
  refine (sum_norm_cpowWeight_sub_le_sub s hs hm hmn).trans ?_
  have hc : 0 ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) hs.le
  have hn : 0 ≤ (n : ℝ) ^ (-s.re) := Real.rpow_nonneg (by positivity) _
  nlinarith

/-- The weight `x ↦ -log x · x^{-s}`, the derivative of `x^{-s}` in `s`, with the real
logarithm. -/
noncomputable def logCpowWeight (s : ℂ) (x : ℝ) : ℂ :=
  -(Real.log x : ℂ) * cpowWeight s x

/-- The derivative `(s log x - 1) x^{-s-1}` of `logCpowWeight s` in `x`. -/
noncomputable def logCpowWeightDeriv (s : ℂ) (x : ℝ) : ℂ :=
  (s * (Real.log x : ℂ) - 1) * (x : ℂ) ^ (-s - 1)

lemma hasDerivAt_logCpowWeight (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (logCpowWeight s) (logCpowWeightDeriv s x) x := by
  have hlog : HasDerivAt (fun y : ℝ => (Real.log y : ℂ)) ((x : ℂ)⁻¹) x := by
    simpa [Complex.ofReal_inv] using (Real.hasDerivAt_log hx.ne').ofReal_comp
  have hpow := hasDerivAt_cpowWeight s hx
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hmul : (x⁻¹ : ℂ) * cpowWeight s x = (x : ℂ) ^ (-s - 1) := by
    rw [← Complex.cpow_neg_one]
    unfold cpowWeight
    rw [← Complex.cpow_add _ _ hxC]
    congr 1
    ring
  have hderiv :
      -((x : ℂ)⁻¹) * cpowWeight s x +
          (-(Real.log x : ℂ)) * cpowWeightDeriv s x =
        logCpowWeightDeriv s x := by
    change -((x : ℂ)⁻¹) * cpowWeight s x +
        (-(Real.log x : ℂ)) * ((-s) * (x : ℂ) ^ (-s - 1)) =
      (s * (Real.log x : ℂ) - 1) * (x : ℂ) ^ (-s - 1)
    rw [show -((x : ℂ)⁻¹) * cpowWeight s x =
      -(((x : ℂ)⁻¹) * cpowWeight s x) by ring, hmul]
    ring
  change HasDerivAt
    (fun y : ℝ => -(Real.log y : ℂ) * cpowWeight s y)
    (logCpowWeightDeriv s x) x
  rw [← hderiv]
  exact hlog.neg.mul hpow

lemma norm_logCpowWeightDeriv_le (s : ℂ) {x : ℝ} (hx : 1 ≤ x) :
    ‖logCpowWeightDeriv s x‖ ≤
      (1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [logCpowWeightDeriv, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  simp only [neg_re, sub_re, one_re]
  have hc : ‖s * (Real.log x : ℂ) - 1‖ ≤ ‖s‖ * Real.log x + 1 := by
    calc
      _ ≤ ‖s * (Real.log x : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖s‖ * Real.log x + 1 := by
        rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hlog, norm_one]
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hx0.le _)

/-- A primitive of `-(1 + ‖s‖ log x) x^{-σ-1}`, where `σ = re s`. Its value at `m ≥ 1`
bounds the total variation of `logCpowWeight s` on `[m, ∞)`. -/
noncomputable def logVariationBudget (s : ℂ) (x : ℝ) : ℝ :=
  x ^ (-s.re) *
    (1 / s.re + ‖s‖ * (Real.log x / s.re + 1 / s.re ^ 2))

lemma hasDerivAt_logVariationBudget (s : ℂ) (hs : 0 < s.re) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (logVariationBudget s)
      (-(1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1)) x := by
  have hp := Real.hasDerivAt_rpow_const (x := x) (p := -s.re) (Or.inl hx.ne')
  have hl := Real.hasDerivAt_log hx.ne'
  have ha : HasDerivAt
      (fun y : ℝ => 1 / s.re + ‖s‖ * (Real.log y / s.re + 1 / s.re ^ 2))
      (‖s‖ * (x⁻¹ / s.re)) x := by
    convert ((hl.div_const s.re).add_const (1 / s.re ^ 2)).const_mul ‖s‖ |>.const_add
      (1 / s.re) using 1
  have hxp : x * x ^ (-s.re - 1) = x ^ (-s.re) := by
    calc
      x * x ^ (-s.re - 1) = x ^ (-s.re - 1) * x := mul_comm _ _
      _ = x ^ (-s.re - 1) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ ((-s.re - 1) + 1) := (Real.rpow_add hx _ _).symm
      _ = x ^ (-s.re) := by ring_nf
  have hderiv :
      -s.re * x ^ (-s.re - 1) *
          (1 / s.re + ‖s‖ * (Real.log x / s.re + 1 / s.re ^ 2)) +
        x ^ (-s.re) * (‖s‖ * (x⁻¹ / s.re)) =
      -(1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1) := by
    rw [← hxp]
    field_simp [hs.ne', hx.ne']
    ring
  change HasDerivAt
    (fun y : ℝ => y ^ (-s.re) *
      (1 / s.re + ‖s‖ * (Real.log y / s.re + 1 / s.re ^ 2)))
    (-(1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1)) x
  rw [← hderiv]
  exact hp.mul ha

lemma norm_logCpowWeight_succ_sub_le (s : ℂ) (hs : 0 < s.re) {k : ℕ} (hk : 1 ≤ k) :
    ‖logCpowWeight s (k + 1) - logCpowWeight s k‖ ≤
      logVariationBudget s k - logVariationBudget s (k + 1) := by
  have hkle : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
  have hone : ∀ x ∈ uIcc (k : ℝ) (k + 1 : ℝ), 1 ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hkle] at hx
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    exact hk1.trans hx.1
  have hpos : ∀ x ∈ uIcc (k : ℝ) (k + 1 : ℝ), 0 < x :=
    fun x hx => zero_lt_one.trans_le (hone x hx)
  have hder : ∀ x ∈ uIcc (k : ℝ) (k + 1 : ℝ),
      HasDerivAt (logCpowWeight s) (logCpowWeightDeriv s x) x :=
    fun x hx => hasDerivAt_logCpowWeight s (hpos x hx)
  have hint : IntervalIntegrable (logCpowWeightDeriv s) volume (k : ℝ) (k + 1 : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hlog := ((Real.hasDerivAt_log (hpos x hx).ne').ofReal_comp).continuousAt
    have hpow := (hasDerivAt_cpowWeight (s + 1) (hpos x hx)).continuousAt
    have heq : logCpowWeightDeriv s =
        fun y : ℝ => (s * (Real.log y : ℂ) - 1) * cpowWeight (s + 1) y := by
      funext y
      unfold logCpowWeightDeriv cpowWeight
      congr 1
      ring_nf
    rw [heq]
    exact (((continuousAt_const.mul hlog).sub continuousAt_const).mul hpow).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
  have hi : IntervalIntegrable
      (fun x : ℝ => (1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1))
      volume (k : ℝ) (k + 1 : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    exact ((continuousAt_const.add (continuousAt_const.mul
      (Real.hasDerivAt_log (hpos x hx).ne').continuousAt)).mul
      (Real.hasDerivAt_rpow_const (Or.inl (hpos x hx).ne')).continuousAt).continuousWithinAt
  have hmajor :
      ‖∫ x in (k : ℝ)..(k + 1 : ℝ), logCpowWeightDeriv s x‖ ≤
        ∫ x in (k : ℝ)..(k + 1 : ℝ),
          (1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1) := by
    refine (intervalIntegral.norm_integral_le_integral_norm hkle).trans ?_
    apply intervalIntegral.integral_mono_on hkle
    · exact hint.norm
    · exact hi
    · intro x hx
      apply norm_logCpowWeightDeriv_le s
      apply hone x
      rwa [Set.uIcc_of_le hkle]
  have hprim :
      (∫ x in (k : ℝ)..(k + 1 : ℝ),
          (1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1)) =
        logVariationBudget s k - logVariationBudget s (k + 1) := by
    have hd : ∀ x ∈ uIcc (k : ℝ) (k + 1 : ℝ),
        HasDerivAt (fun y => -logVariationBudget s y)
          ((1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1)) x := by
      intro x hx
      have hneg := (hasDerivAt_logVariationBudget s hs (hpos x hx)).neg
      have hderiv :
          (1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1) =
            -(-(1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1)) := by ring
      rw [hderiv]
      change HasDerivAt (-logVariationBudget s)
        (-(-(1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1))) x
      exact hneg
    convert intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi using 1; ring
  rw [← hFTC]
  exact hmajor.trans_eq hprim

lemma sum_norm_logCpowWeight_sub_le_sub (s : ℂ) (hs : 0 < s.re) {m n : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∑ k ∈ Ico m n, ‖logCpowWeight s (k + 1) - logCpowWeight s k‖ ≤
      logVariationBudget s m - logVariationBudget s n := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
      rw [sum_Ico_succ_top hmn]
      calc
        _ ≤ (logVariationBudget s m - logVariationBudget s n) +
            (logVariationBudget s n - logVariationBudget s (n + 1)) :=
          add_le_add ih (norm_logCpowWeight_succ_sub_le s hs (hm.trans hmn))
        _ = _ := by
          norm_num [Nat.cast_add]

lemma sum_norm_logCpowWeight_sub_le (s : ℂ) (hs : 0 < s.re) {m n : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∑ k ∈ Ico m n, ‖logCpowWeight s (k + 1) - logCpowWeight s k‖ ≤
      logVariationBudget s m := by
  refine (sum_norm_logCpowWeight_sub_le_sub s hs hm hmn).trans ?_
  have hn : 0 ≤ logVariationBudget s n := by
    unfold logVariationBudget
    positivity
  linarith

end BombieriVinogradov.AbelWeight

end

section

/-!
## The series for `L(s, χ)`

The limit is taken over the partial sums `∑_{n<N} χ(n) n^{-s}` in their natural order,
since the series need not converge absolutely when `0 < re s ≤ 1`.
-/

open Complex Finset Filter Set
open scoped Topology

namespace BombieriVinogradov.LValueSeries

open BombieriVinogradov.WeakStrip BombieriVinogradov.AbelWeight
variable {q : ℕ} [NeZero q]

lemma character_nat_zero_of_ne_one
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : χ (0 : ℕ) = 0 := by
  have hq1 : q ≠ 1 := by
    intro h
    subst q
    exact hχ (Subsingleton.elim _ _)
  have hq0 : q ≠ 0 := NeZero.ne q
  let : Fact (1 < q) :=
    ⟨Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hq0, hq1⟩⟩
  simpa only [Nat.cast_zero] using
    (MulChar.map_nonunit χ (a := (0 : ZMod q)) not_isUnit_zero)

lemma cpowWeight_nat_eq (s : ℂ) (k : ℕ) :
    cpowWeight s k = (k : ℂ) ^ (-s) := by
  unfold cpowWeight
  norm_num

/-- Abel summation bound for `∑_{m ≤ k < n} χ(k) k^{-s}`. -/
lemma norm_sum_Ico_cpowWeight_character_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re)
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    ‖∑ k ∈ Ico m n, cpowWeight s k * χ k‖ ≤
      q * (‖cpowWeight s (n - 1 : ℕ)‖ + ‖cpowWeight s m‖ +
        (‖s‖ / s.re) * (m : ℝ) ^ (-s.re)) := by
  have hab := dirichlet_cpow_abel_Ico χ s hmn
  simp_rw [← cpowWeight_nat_eq] at hab
  rw [hab]
  calc
    _ ≤ ‖cpowWeight s (n - 1 : ℕ) * (∑ k ∈ range n, χ k)‖ +
          ‖cpowWeight s m * (∑ k ∈ range m, χ k)‖ +
          ‖∑ k ∈ Ico m (n - 1),
            (cpowWeight s (k + 1 : ℕ) - cpowWeight s k) *
              (∑ j ∈ range (k + 1), χ j)‖ := by
      exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ ‖cpowWeight s (n - 1 : ℕ)‖ * q + ‖cpowWeight s m‖ * q +
          ∑ k ∈ Ico m (n - 1),
            (‖cpowWeight s (k + 1 : ℕ) - cpowWeight s k‖ * q) := by
      gcongr
      · rw [norm_mul]
        gcongr
        exact norm_sum_range_character_le_modulus χ hχ n
      · rw [norm_mul]
        gcongr
        exact norm_sum_range_character_le_modulus χ hχ m
      · refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul]
        gcongr
        exact norm_sum_range_character_le_modulus χ hχ (k + 1)
    _ = q * (‖cpowWeight s (n - 1 : ℕ)‖ + ‖cpowWeight s m‖ +
          ∑ k ∈ Ico m (n - 1),
            ‖cpowWeight s (k + 1 : ℕ) - cpowWeight s k‖) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ q * (‖cpowWeight s (n - 1 : ℕ)‖ + ‖cpowWeight s m‖ +
          (‖s‖ / s.re) * (m : ℝ) ^ (-s.re)) := by
      gcongr
      simpa only [Nat.pred_eq_sub_one, Nat.cast_add, Nat.cast_one] using
        sum_norm_cpowWeight_sub_le s hs hm (Nat.le_pred_of_lt hmn)

lemma tendsto_norm_cpowWeight_nat_atTop (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => ‖cpowWeight s n‖) atTop (𝓝 0) := by
  have hp : Tendsto (fun x : ℝ => x ^ (-s.re)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hs
  have hn := hp.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have heq : (fun n : ℕ => ‖cpowWeight s n‖) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-s.re)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
    rw [cpowWeight, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
    simp
  exact (tendsto_congr' heq).2 hn

lemma tendsto_cpowVariationBudget_nat_atTop (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => (‖s‖ / s.re) * (n : ℝ) ^ (-s.re)) atTop (𝓝 0) := by
  simpa using (((tendsto_rpow_neg_atTop hs).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (‖s‖ / s.re))

/-- The partial sums of `∑ χ(n) n^{-s}` are Cauchy for `re s > 0`. -/
lemma cauchySeq_sum_range_cpowWeight_character
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    CauchySeq (fun n : ℕ => ∑ k ∈ range n, cpowWeight s k * χ k) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  let δ : ℝ := ε / (3 * q)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hq)
  have he := (tendsto_norm_cpowWeight_nat_atTop s hs).eventually
    (Metric.ball_mem_nhds (x := (0 : ℝ)) hδ)
  have hb := (tendsto_cpowVariationBudget_nat_atTop s hs).eventually
    (Metric.ball_mem_nhds (x := (0 : ℝ)) hδ)
  rw [eventually_atTop] at he hb
  rcases he with ⟨Ne, hNe⟩
  rcases hb with ⟨Nb, hNb⟩
  -- Treat `m < n`; the case `n < m` follows by symmetry.
  have hdist (m n : ℕ) (hm : max 1 (max Ne Nb) ≤ m) (hmn : m < n) :
      dist (∑ k ∈ range m, cpowWeight s k * χ k)
        (∑ k ∈ range n, cpowWeight s k * χ k) < ε := by
    have hm1 : 1 ≤ m := (le_max_left 1 (max Ne Nb)).trans hm
    have hmE : Ne ≤ m := (le_max_of_le_right (le_max_left Ne Nb)).trans hm
    have hmB : Nb ≤ m := (le_max_of_le_right (le_max_right Ne Nb)).trans hm
    have hgm : ‖cpowWeight s m‖ < δ := by
      simpa [Real.dist_eq] using hNe m hmE
    have hbm : (‖s‖ / s.re) * (m : ℝ) ^ (-s.re) < δ := by
      have := hNb m hmB
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
      exact this
    have hpredE : Ne ≤ n - 1 := hmE.trans (Nat.le_pred_of_lt hmn)
    have hgpred : ‖cpowWeight s (n - 1 : ℕ)‖ < δ := by
      simpa [Real.dist_eq] using hNe (n - 1) hpredE
    rw [dist_eq, ← norm_neg, neg_sub, ← Finset.sum_Ico_eq_sub _ hmn.le]
    calc
      _ ≤ q * (‖cpowWeight s (n - 1 : ℕ)‖ + ‖cpowWeight s m‖ +
          (‖s‖ / s.re) * (m : ℝ) ^ (-s.re)) :=
        norm_sum_Ico_cpowWeight_character_le χ hχ s hs hm1 hmn
      _ < q * (δ + δ + δ) :=
        mul_lt_mul_of_pos_left (by linarith only [hgpred, hgm, hbm]) hq
      _ = ε := by dsimp [δ]; field_simp; ring
  refine ⟨max 1 (max Ne Nb), ?_⟩
  intro m hm n hn
  rcases lt_trichotomy m n with hmn | rfl | hnm
  · exact hdist m n hm hmn
  · simp [hε]
  · simpa only [dist_comm] using hdist n m hn hnm

lemma exists_tendsto_sum_range_cpowWeight_character
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    ∃ L : ℂ, Tendsto (fun n : ℕ => ∑ k ∈ range n, cpowWeight s k * χ k)
      atTop (𝓝 L) :=
  cauchySeq_tendsto_of_complete (cauchySeq_sum_range_cpowWeight_character χ hχ s hs)

/-- The limit of the partial sums `∑_{n<N} χ(n) n^{-s}` for `re s > 0`. -/
noncomputable def orderedValueSeries
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) : ℂ :=
  Classical.choose (exists_tendsto_sum_range_cpowWeight_character χ hχ s hs)

lemma tendsto_sum_range_orderedValueSeries
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => ∑ k ∈ range n, cpowWeight s k * χ k) atTop
      (𝓝 (orderedValueSeries χ hχ s hs)) :=
  Classical.choose_spec (exists_tendsto_sum_range_cpowWeight_character χ hχ s hs)

/-- The error after `m` terms is at most `q (1 + ‖s‖ / σ) m^{-σ}`, where `σ = re s`. -/
lemma norm_orderedValueSeries_sub_sum_range_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re)
    {m : ℕ} (hm : 1 ≤ m) :
    ‖orderedValueSeries χ hχ s hs - ∑ k ∈ range m, cpowWeight s k * χ k‖ ≤
      q * ((m : ℝ) ^ (-s.re) + (‖s‖ / s.re) * (m : ℝ) ^ (-s.re)) := by
  let P : ℕ → ℂ := fun n => ∑ k ∈ range n, cpowWeight s k * χ k
  have hP : Tendsto P atTop (𝓝 (orderedValueSeries χ hχ s hs)) := by
    simpa only [P] using tendsto_sum_range_orderedValueSeries χ hχ s hs
  have hleft : Tendsto (fun n => ‖P (n + 1) - P m‖) atTop
      (𝓝 ‖orderedValueSeries χ hχ s hs - P m‖) :=
    ((hP.comp (tendsto_add_atTop_nat 1)).sub_const (P m)).norm
  have hright : Tendsto
      (fun n : ℕ => q * (‖cpowWeight s n‖ + ‖cpowWeight s m‖ +
        (‖s‖ / s.re) * (m : ℝ) ^ (-s.re))) atTop
      (𝓝 (q * ((m : ℝ) ^ (-s.re) +
        (‖s‖ / s.re) * (m : ℝ) ^ (-s.re)))) := by
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
    have hwm : ‖cpowWeight s m‖ = (m : ℝ) ^ (-s.re) := by
      rw [cpowWeight, Complex.norm_cpow_eq_rpow_re_of_pos hm0]
      simp
    simpa only [zero_add, hwm, add_assoc] using
      ((tendsto_norm_cpowWeight_nat_atTop s hs).add_const
        (‖cpowWeight s m‖ + (‖s‖ / s.re) * (m : ℝ) ^ (-s.re))).const_mul (q : ℝ)
  refine le_of_tendsto_of_tendsto hleft hright ?_
  filter_upwards [eventually_ge_atTop m] with n hn
  have hmn : m < n + 1 := Nat.lt_succ_of_le hn
  have htail := norm_sum_Ico_cpowWeight_character_le χ hχ s hs hm hmn
  rw [Finset.sum_Ico_eq_sub _ hmn.le] at htail
  simpa only [P, Nat.add_sub_cancel] using htail

/-- The half-plane `re s > 0`. -/
def rightHalfPlane : Set ℂ := {s | 0 < s.re}

/-- The partial sum `∑_{n<N} χ(n) n^{-s}` as a function of `s`. -/
noncomputable def valuePartialSum (χ : DirichletCharacter ℂ q) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ range N, cpowWeight s n * χ n

/-- `orderedValueSeries` as a function on `ℂ`, set to `0` where `re s ≤ 0`. -/
noncomputable def orderedValueFunction
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) : ℂ :=
  if hs : 0 < s.re then orderedValueSeries χ hχ s hs else 0

lemma orderedValueFunction_eq (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s : ℂ) (hs : 0 < s.re) :
    orderedValueFunction χ hχ s = orderedValueSeries χ hχ s hs := by
  simp only [orderedValueFunction, dif_pos hs]

/-- The tail bound `q m^{-δ} (1 + M / δ)`, valid uniformly for `δ ≤ re s` and `‖s‖ ≤ M`. -/
noncomputable def compactValueTailMajorant (q : ℕ) (δ M : ℝ) (m : ℕ) : ℝ :=
  q * (m : ℝ) ^ (-δ) * (1 + M / δ)

private lemma tendsto_compactValueTailMajorant (q : ℕ) {δ M : ℝ} (hδ : 0 < δ) :
    Tendsto (compactValueTailMajorant q δ M) atTop (𝓝 0) := by
  have hp := (tendsto_rpow_neg_atTop hδ).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  unfold compactValueTailMajorant
  simpa [mul_assoc] using (hp.const_mul (q : ℝ)).mul_const (1 + M / δ)

private lemma compact_uniform_value_tail
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ rightHalfPlane) :
    TendstoUniformlyOn (valuePartialSum χ) (orderedValueFunction χ hχ) atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp [Metric.tendstoUniformlyOn_iff]
  obtain ⟨smin, hsmin, hmin⟩ := hK.exists_isMinOn hKne continuous_re.continuousOn
  let δ : ℝ := smin.re
  have hδ : 0 < δ := hKU hsmin
  have hδK : ∀ s ∈ K, δ ≤ s.re := hmin
  obtain ⟨smax, hsmax, hmax⟩ := hK.exists_isMaxOn hKne continuous_norm.continuousOn
  let M : ℝ := ‖smax‖
  have hM : 0 ≤ M := norm_nonneg smax
  have hMK : ∀ s ∈ K, ‖s‖ ≤ M := hmax
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hmaj := (tendsto_compactValueTailMajorant q hδ (M := M)).eventually
    (Metric.ball_mem_nhds (x := (0 : ℝ)) hε)
  rw [eventually_atTop] at hmaj
  obtain ⟨N, hN⟩ := hmaj
  filter_upwards [eventually_ge_atTop (max 1 N)] with n hn
  intro s hsK
  have hn1 : 1 ≤ n := (le_max_left 1 N).trans hn
  have hnN : N ≤ n := (le_max_right 1 N).trans hn
  have htail := norm_orderedValueSeries_sub_sum_range_le χ hχ s (hKU hsK) hn1
  rw [orderedValueFunction_eq χ hχ s (hKU hsK), dist_eq]
  change ‖orderedValueSeries χ hχ s (hKU hsK) - valuePartialSum χ n s‖ < ε
  refine htail.trans_lt ?_
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hpow : (n : ℝ) ^ (-s.re) ≤ (n : ℝ) ^ (-δ) :=
    Real.rpow_le_rpow_of_exponent_le hnR (neg_le_neg (hδK s hsK))
  have hdiv : ‖s‖ / s.re ≤ M / δ :=
    div_le_div₀ hM (hMK s hsK) hδ (hδK s hsK)
  have hbound : q * ((n : ℝ) ^ (-s.re) +
      (‖s‖ / s.re) * (n : ℝ) ^ (-s.re)) ≤ compactValueTailMajorant q δ M n := by
    unfold compactValueTailMajorant
    have hp0 : 0 ≤ (n : ℝ) ^ (-s.re) := Real.rpow_nonneg (by positivity) _
    have hpδ0 : 0 ≤ (n : ℝ) ^ (-δ) := Real.rpow_nonneg (by positivity) _
    have hd0 : 0 ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) (hKU hsK).le
    calc
      _ ≤ q * ((n : ℝ) ^ (-δ) + (M / δ) * (n : ℝ) ^ (-δ)) := by gcongr
      _ = _ := by ring
  have hnon : 0 ≤ compactValueTailMajorant q δ M n := by
    unfold compactValueTailMajorant
    positivity
  exact hbound.trans_lt (by
    have := hN n hnN
    simpa [Real.dist_eq, abs_of_nonneg hnon] using this)

/-- The partial sums converge locally uniformly on `re s > 0`. -/
theorem tendstoLocallyUniformlyOn_valuePartialSum
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    TendstoLocallyUniformlyOn (valuePartialSum χ) (orderedValueFunction χ hχ)
      atTop rightHalfPlane := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact]
  · intro K hKU hK
    exact compact_uniform_value_tail χ hχ hK hKU
  · exact continuous_re.isOpen_preimage _ isOpen_Ioi

private lemma differentiable_valuePartialSum
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    Differentiable ℂ (valuePartialSum χ N) := by
  unfold valuePartialSum
  apply Differentiable.fun_sum
  intro n hn
  rcases n with _ | n
  · rw [character_nat_zero_of_ne_one χ hχ]
    simp
  · apply Differentiable.mul
    · unfold cpowWeight
      exact Differentiable.const_cpow (by fun_prop)
        (Or.inl (by exact_mod_cast Nat.succ_ne_zero n))
    · fun_prop

/-- The limit is holomorphic on `re s > 0`. -/
theorem differentiableOn_orderedValueFunction
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    DifferentiableOn ℂ (orderedValueFunction χ hχ) rightHalfPlane := by
  exact (tendstoLocallyUniformlyOn_valuePartialSum χ hχ).differentiableOn
    (Eventually.of_forall fun N =>
      (differentiable_valuePartialSum χ hχ N).differentiableOn)
    (continuous_re.isOpen_preimage _ isOpen_Ioi)

/-- For `re s > 1` the limit is `L(s, χ)`, by absolute convergence. -/
lemma orderedValueSeries_eq_LFunction
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 1 < s.re) :
    orderedValueSeries χ hχ s (by linarith) = χ.LFunction s := by
  have habs : LSeries.abscissaOfAbsConv (fun n : ℕ => χ n) < s.re := by
    refine (LSeries.abscissaOfAbsConv_le_of_le_const ?_).trans_lt ?_
    · exact ⟨1, fun n _ => χ.norm_le_one n⟩
    · exact_mod_cast hs
  have hsum := (LSeriesSummable_of_abscissaOfAbsConv_lt_re habs).LSeriesHasSum
  have hterm (n : ℕ) : LSeries.term (fun k : ℕ => χ k) s n = cpowWeight s n * χ n := by
    rcases n with _ | n
    · rw [LSeries.term_zero, character_nat_zero_of_ne_one χ hχ]
      simp
    · rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), cpowWeight_nat_eq, cpow_neg]
      ring
  have hseries : Tendsto (fun n : ℕ => ∑ k ∈ range n, cpowWeight s k * χ k) atTop
      (𝓝 (χ.LFunction s)) := by
    rw [χ.LFunction_eq_LSeries hs]
    exact (hsum.congr_fun fun n => (hterm n).symm).tendsto_sum_nat
  exact tendsto_nhds_unique
    (tendsto_sum_range_orderedValueSeries χ hχ s (by linarith)) hseries

/-- For `re s > 0` the series `∑ χ(n) n^{-s}` converges to `L(s, χ)`, by the identity
theorem. -/
theorem orderedValueSeries_eq_LFunction_of_re_pos
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    orderedValueSeries χ hχ s hs = χ.LFunction s := by
  let U : Set ℂ := rightHalfPlane
  have hUopen : IsOpen U := continuous_re.isOpen_preimage _ isOpen_Ioi
  have hF : AnalyticOnNhd ℂ (orderedValueFunction χ hχ) U :=
    (differentiableOn_orderedValueFunction χ hχ).analyticOnNhd hUopen
  have hL : AnalyticOnNhd ℂ χ.LFunction U :=
    (χ.differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ |>.mono
      (subset_univ U)
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have htwo : (2 : ℂ) ∈ U := by norm_num [U, rightHalfPlane]
  have hevent : orderedValueFunction χ hχ =ᶠ[𝓝 (2 : ℂ)] χ.LFunction := by
    filter_upwards [eventually_of_mem
      ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
        (by norm_num : (1 : ℝ) < (2 : ℂ).re)) (fun z hz => hz)] with z hz
    rw [orderedValueFunction_eq χ hχ z (lt_trans zero_lt_one hz)]
    exact orderedValueSeries_eq_LFunction χ hχ z hz
  have hall := hF.eqOn_of_preconnected_of_eventuallyEq hL hpre htwo hevent
  exact (orderedValueFunction_eq χ hχ s hs).symm.trans (hall hs)

end BombieriVinogradov.LValueSeries

end

section

/-!
## The series for `L'(s, χ)`

The same argument with the weight `-log x · x^{-s}` in place of `x^{-s}`.
-/

open Complex Finset Filter Set
open scoped Topology

namespace BombieriVinogradov.LDerivSeries

open BombieriVinogradov.WeakStrip BombieriVinogradov.AbelWeight
variable {q : ℕ} [NeZero q]

/-- On positive integers the real and complex logarithms agree. -/
lemma logCpowWeight_nat_eq (s : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    logCpowWeight s k = -(Complex.log (k : ℂ)) * (k : ℂ) ^ (-s) := by
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hcast : ((k : ℝ) : ℂ) = (k : ℂ) := by norm_num
  rw [logCpowWeight, cpowWeight, Complex.ofReal_log hk0, hcast]

omit [NeZero q] in
lemma logCpowWeight_abel_Ico (χ : DirichletCharacter ℂ q) (s : ℂ)
    {m n : ℕ} (_hm : 1 ≤ m) (hmn : m < n) :
    ∑ k ∈ Ico m n, logCpowWeight s k * χ k =
      logCpowWeight s (n - 1 : ℕ) * (∑ k ∈ range n, χ k) -
        logCpowWeight s m * (∑ k ∈ range m, χ k) -
        ∑ k ∈ Ico m (n - 1),
          (logCpowWeight s (k + 1 : ℕ) - logCpowWeight s k) *
            (∑ j ∈ range (k + 1), χ j) := by
  exact abel_Ico χ (fun k : ℕ => logCpowWeight s k) hmn

/-- Abel summation bound for `∑_{m ≤ k < n} χ(k) log k · k^{-s}`. -/
lemma norm_sum_Ico_logCpowWeight_character_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re)
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    ‖∑ k ∈ Ico m n, logCpowWeight s k * χ k‖ ≤
      q * (‖logCpowWeight s (n - 1 : ℕ)‖ + ‖logCpowWeight s m‖ +
        logVariationBudget s m) := by
  rw [logCpowWeight_abel_Ico χ s hm hmn]
  calc
    _ ≤ ‖logCpowWeight s (n - 1 : ℕ) * (∑ k ∈ range n, χ k)‖ +
          ‖logCpowWeight s m * (∑ k ∈ range m, χ k)‖ +
          ‖∑ k ∈ Ico m (n - 1),
            (logCpowWeight s (k + 1 : ℕ) - logCpowWeight s k) *
              (∑ j ∈ range (k + 1), χ j)‖ := by
      exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ ‖logCpowWeight s (n - 1 : ℕ)‖ * q +
          ‖logCpowWeight s m‖ * q +
          ∑ k ∈ Ico m (n - 1),
            (‖logCpowWeight s (k + 1 : ℕ) - logCpowWeight s k‖ * q) := by
      gcongr
      · rw [norm_mul]
        gcongr
        exact norm_sum_range_character_le_modulus χ hχ n
      · rw [norm_mul]
        gcongr
        exact norm_sum_range_character_le_modulus χ hχ m
      · refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul]
        gcongr
        exact norm_sum_range_character_le_modulus χ hχ (k + 1)
    _ = q * (‖logCpowWeight s (n - 1 : ℕ)‖ + ‖logCpowWeight s m‖ +
          ∑ k ∈ Ico m (n - 1),
            ‖logCpowWeight s (k + 1 : ℕ) - logCpowWeight s k‖) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ q * (‖logCpowWeight s (n - 1 : ℕ)‖ + ‖logCpowWeight s m‖ +
          logVariationBudget s m) := by
      gcongr
      simpa only [Nat.pred_eq_sub_one, Nat.cast_add, Nat.cast_one] using
        sum_norm_logCpowWeight_sub_le s hs hm (Nat.le_pred_of_lt hmn)

lemma tendsto_norm_logCpowWeight_nat_atTop (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => ‖logCpowWeight s n‖) atTop (𝓝 0) := by
  have hreal : Tendsto (fun x : ℝ => Real.log x / x ^ s.re) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hs).tendsto_div_nhds_zero
  have hnat := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have heq : (fun n : ℕ => ‖logCpowWeight s n‖) =ᶠ[atTop]
      (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ s.re) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    rw [logCpowWeight, norm_mul, norm_neg, norm_real,
      Real.norm_eq_abs, abs_of_nonneg hlog, cpowWeight,
      Complex.norm_cpow_eq_rpow_re_of_pos hn0]
    simp only [neg_re]
    rw [div_eq_mul_inv, ← Real.rpow_neg hn0.le]
  exact (tendsto_congr' heq).2 hnat

lemma tendsto_logVariationBudget_nat_atTop (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => logVariationBudget s n) atTop (𝓝 0) := by
  have hp : Tendsto (fun x : ℝ => x ^ (-s.re)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hs
  have hl : Tendsto (fun x : ℝ => Real.log x / x ^ s.re) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hs).tendsto_div_nhds_zero
  have hcomb : Tendsto
      (fun x : ℝ => (1 / s.re + ‖s‖ / s.re ^ 2) * x ^ (-s.re) +
        (‖s‖ / s.re) * (Real.log x / x ^ s.re)) atTop (𝓝 0) := by
    simpa using
      ((hp.const_mul (1 / s.re + ‖s‖ / s.re ^ 2)).add
        (hl.const_mul (‖s‖ / s.re)))
  have hnat := hcomb.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have heq : (fun n : ℕ => logVariationBudget s n) =ᶠ[atTop]
      (fun n : ℕ => (1 / s.re + ‖s‖ / s.re ^ 2) * (n : ℝ) ^ (-s.re) +
        (‖s‖ / s.re) * (Real.log n / (n : ℝ) ^ s.re)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hdiv : Real.log (n : ℝ) / (n : ℝ) ^ s.re =
        Real.log (n : ℝ) * (n : ℝ) ^ (-s.re) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hn0.le]
    rw [logVariationBudget, hdiv]
    field_simp [hs.ne']
    ring
  exact (tendsto_congr' heq).2 hnat

/-- The partial sums of `-∑ χ(n) log n · n^{-s}` are Cauchy for `re s > 0`. -/
lemma cauchySeq_sum_range_logCpowWeight_character
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    CauchySeq (fun n : ℕ => ∑ k ∈ range n, logCpowWeight s k * χ k) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  let δ : ℝ := ε / (3 * q)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hq)
  have he := (tendsto_norm_logCpowWeight_nat_atTop s hs).eventually
    (Metric.ball_mem_nhds (x := (0 : ℝ)) hδ)
  have hb := (tendsto_logVariationBudget_nat_atTop s hs).eventually
    (Metric.ball_mem_nhds (x := (0 : ℝ)) hδ)
  rw [eventually_atTop] at he hb
  rcases he with ⟨Ne, hNe⟩
  rcases hb with ⟨Nb, hNb⟩
  -- Treat `m < n`; the case `n < m` follows by symmetry.
  have hdist (m n : ℕ) (hm : max 1 (max Ne Nb) ≤ m) (hmn : m < n) :
      dist (∑ k ∈ range m, logCpowWeight s k * χ k)
        (∑ k ∈ range n, logCpowWeight s k * χ k) < ε := by
    have hm1 : 1 ≤ m := (le_max_left 1 (max Ne Nb)).trans hm
    have hmE : Ne ≤ m := (le_max_of_le_right (le_max_left Ne Nb)).trans hm
    have hmB : Nb ≤ m := (le_max_of_le_right (le_max_right Ne Nb)).trans hm
    have hgm : ‖logCpowWeight s m‖ < δ := by
      simpa [Real.dist_eq] using hNe m hmE
    have hbm : logVariationBudget s m < δ := by
      have := hNb m hmB
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by unfold logVariationBudget; positivity)] at this
      exact this
    have hpredE : Ne ≤ n - 1 := hmE.trans (Nat.le_pred_of_lt hmn)
    have hgpred : ‖logCpowWeight s (n - 1 : ℕ)‖ < δ := by
      simpa [Real.dist_eq] using hNe (n - 1) hpredE
    rw [dist_eq, ← norm_neg, neg_sub, ← Finset.sum_Ico_eq_sub _ hmn.le]
    calc
      _ ≤ q * (‖logCpowWeight s (n - 1 : ℕ)‖ + ‖logCpowWeight s m‖ +
          logVariationBudget s m) :=
        norm_sum_Ico_logCpowWeight_character_le χ hχ s hs hm1 hmn
      _ < q * (δ + δ + δ) :=
        mul_lt_mul_of_pos_left (by linarith only [hgpred, hgm, hbm]) hq
      _ = ε := by dsimp [δ]; field_simp; ring
  refine ⟨max 1 (max Ne Nb), ?_⟩
  intro m hm n hn
  rcases lt_trichotomy m n with hmn | rfl | hnm
  · exact hdist m n hm hmn
  · simp [hε]
  · simpa only [dist_comm] using hdist n m hn hnm

lemma exists_tendsto_sum_range_logCpowWeight_character
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    ∃ L : ℂ, Tendsto (fun n : ℕ => ∑ k ∈ range n, logCpowWeight s k * χ k)
      atTop (𝓝 L) :=
  cauchySeq_tendsto_of_complete
    (cauchySeq_sum_range_logCpowWeight_character χ hχ s hs)

/-- The limit of the partial sums `-∑_{n<N} χ(n) log n · n^{-s}` for `re s > 0`. -/
noncomputable def orderedLogDerivativeSeries
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) : ℂ :=
  Classical.choose (exists_tendsto_sum_range_logCpowWeight_character χ hχ s hs)

lemma tendsto_sum_range_orderedLogDerivativeSeries
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => ∑ k ∈ range n, logCpowWeight s k * χ k) atTop
      (𝓝 (orderedLogDerivativeSeries χ hχ s hs)) :=
  Classical.choose_spec (exists_tendsto_sum_range_logCpowWeight_character χ hχ s hs)

/-- Tail bound for the series for `L'(s, χ)` after `m` terms. -/
lemma norm_orderedLogDerivativeSeries_sub_sum_range_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re)
    {m : ℕ} (hm : 1 ≤ m) :
    ‖orderedLogDerivativeSeries χ hχ s hs -
        ∑ k ∈ range m, logCpowWeight s k * χ k‖ ≤
      q * (‖logCpowWeight s m‖ + logVariationBudget s m) := by
  let P : ℕ → ℂ := fun n => ∑ k ∈ range n, logCpowWeight s k * χ k
  have hP : Tendsto P atTop (𝓝 (orderedLogDerivativeSeries χ hχ s hs)) := by
    simpa only [P] using tendsto_sum_range_orderedLogDerivativeSeries χ hχ s hs
  have hleft : Tendsto (fun n => ‖P (n + 1) - P m‖) atTop
      (𝓝 ‖orderedLogDerivativeSeries χ hχ s hs - P m‖) :=
    ((hP.comp (tendsto_add_atTop_nat 1)).sub_const (P m)).norm
  have hright : Tendsto
      (fun n : ℕ => q * (‖logCpowWeight s n‖ + ‖logCpowWeight s m‖ +
        logVariationBudget s m)) atTop
      (𝓝 (q * (‖logCpowWeight s m‖ + logVariationBudget s m))) := by
    simpa only [zero_add, add_assoc] using
      ((tendsto_norm_logCpowWeight_nat_atTop s hs).add_const
        (‖logCpowWeight s m‖ + logVariationBudget s m)).const_mul (q : ℝ)
  refine le_of_tendsto_of_tendsto hleft hright ?_
  filter_upwards [eventually_ge_atTop m] with n hn
  have hmn : m < n + 1 := Nat.lt_succ_of_le hn
  have htail := norm_sum_Ico_logCpowWeight_character_le χ hχ s hs hm hmn
  rw [Finset.sum_Ico_eq_sub _ hmn.le] at htail
  simpa only [P, Nat.add_sub_cancel] using htail

/-- For `re s > 1` the limit is `L'(s, χ)`, by absolute convergence. -/
lemma orderedLogDerivativeSeries_eq_deriv_LFunction
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 1 < s.re) :
    orderedLogDerivativeSeries χ hχ s (by linarith) = deriv χ.LFunction s := by
  have habs : LSeries.abscissaOfAbsConv (fun n : ℕ => χ n) < s.re := by
    refine (LSeries.abscissaOfAbsConv_le_of_le_const ?_).trans_lt ?_
    · exact ⟨1, fun n _ => χ.norm_le_one n⟩
    · exact_mod_cast hs
  have hsum := (LSeriesSummable_logMul_of_lt_re habs).LSeriesHasSum
  have hterm (n : ℕ) :
      -(LSeries.term (LSeries.logMul (fun k : ℕ => χ k)) s n) =
        logCpowWeight s n * χ n := by
    rcases n with _ | n
    · simp [logCpowWeight, cpowWeight]
    · rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n),
        logCpowWeight_nat_eq s (Nat.succ_pos n), cpow_neg]
      dsimp only [LSeries.logMul]
      ring
  have hordered := tendsto_sum_range_orderedLogDerivativeSeries χ hχ s (by linarith)
  have hseries : Tendsto
      (fun n : ℕ => ∑ k ∈ range n, logCpowWeight s k * χ k) atTop
      (𝓝 (deriv χ.LFunction s)) := by
    have hderiv : deriv χ.LFunction s =
        -LSeries (LSeries.logMul (fun n : ℕ => χ n)) s :=
      (DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs).trans
        (LSeries_deriv habs)
    have hsum' : HasSum (fun n : ℕ => logCpowWeight s n * χ n)
        (deriv χ.LFunction s) := by
      rw [hderiv]
      exact hsum.neg.congr_fun fun n => (hterm n).symm
    exact hsum'.tendsto_sum_nat
  exact tendsto_nhds_unique hordered hseries

end BombieriVinogradov.LDerivSeries

end

section

/-!
## Identification with `L'(s, χ)` on `re s > 0`

The partial sums converge locally uniformly on `re s > 0`, so their limit is holomorphic
there, and the identity theorem identifies it with `L'(s, χ)`.
-/

open Complex Finset Filter Set
open scoped Topology

namespace BombieriVinogradov.LDerivContinuation

open BombieriVinogradov.LDerivSeries BombieriVinogradov.AbelWeight
variable {q : ℕ} [NeZero q]

/-- The half-plane `re s > 0`. -/
def rightHalfPlane : Set ℂ := {s | 0 < s.re}

/-- The partial sum `-∑_{n<N} χ(n) log n · n^{-s}` as an entire function of `s`. -/
noncomputable def derivativePartialSum (χ : DirichletCharacter ℂ q) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ range N, logCpowWeight s n * χ n

/-- `orderedLogDerivativeSeries` as a function on `ℂ`, set to `0` where `re s ≤ 0`. -/
noncomputable def orderedDerivativeFunction
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) : ℂ :=
  if hs : 0 < s.re then orderedLogDerivativeSeries χ hχ s hs else 0

lemma orderedDerivativeFunction_eq (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s : ℂ) (hs : 0 < s.re) :
    orderedDerivativeFunction χ hχ s = orderedLogDerivativeSeries χ hχ s hs := by
  simp only [orderedDerivativeFunction, dif_pos hs]

private lemma norm_logCpowWeight_le {δ : ℝ}
    {s : ℂ} (hre : δ ≤ s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖logCpowWeight s n‖ ≤ Real.log n / (n : ℝ) ^ δ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  rw [logCpowWeight, norm_mul, norm_neg, norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlog, cpowWeight, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
  simp only [neg_re]
  rw [div_eq_mul_inv, ← Real.rpow_neg hn0.le]
  gcongr

private lemma logVariationBudget_le {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    {s : ℂ} (hre : δ ≤ s.re) (hnorm : ‖s‖ ≤ M) {n : ℕ} (hn : 1 ≤ n) :
    logVariationBudget s n ≤
      (1 / δ + M / δ ^ 2) * (n : ℝ) ^ (-δ) +
        (M / δ) * (Real.log n / (n : ℝ) ^ δ) := by
  have hre0 : 0 < s.re := hδ.trans_le hre
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hpow : (n : ℝ) ^ (-s.re) ≤ (n : ℝ) ^ (-δ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hre)
  have hinv : 1 / s.re ≤ 1 / δ := by
    exact one_div_le_one_div_of_le hδ hre
  have hnormdiv : ‖s‖ / s.re ≤ M / δ := by
    exact div_le_div₀ hM hnorm hδ hre
  have hnormdiv2 : ‖s‖ / s.re ^ 2 ≤ M / δ ^ 2 :=
    div_le_div₀ hM hnorm (sq_pos_of_pos hδ) ((sq_le_sq₀ hδ.le hre0.le).2 hre)
  rw [logVariationBudget]
  have hid : Real.log (n : ℝ) / (n : ℝ) ^ δ =
      Real.log (n : ℝ) * (n : ℝ) ^ (-δ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hn0.le]
  rw [hid]
  calc
    _ = (1 / s.re + ‖s‖ / s.re ^ 2) * (n : ℝ) ^ (-s.re) +
          (‖s‖ / s.re) * (Real.log n * (n : ℝ) ^ (-s.re)) := by
        field_simp [hre0.ne']
        ring
    _ ≤ (1 / δ + M / δ ^ 2) * (n : ℝ) ^ (-δ) +
          (M / δ) * (Real.log n * (n : ℝ) ^ (-δ)) := by
        gcongr
    _ = _ := by ring

/-- A bound on the tail of the derivative series, uniform for `δ ≤ re s` and `‖s‖ ≤ M`. -/
noncomputable def compactTailMajorant (q : ℕ) (δ M : ℝ) (n : ℕ) : ℝ :=
  q * (Real.log n / (n : ℝ) ^ δ +
    (1 / δ + M / δ ^ 2) * (n : ℝ) ^ (-δ) +
    (M / δ) * (Real.log n / (n : ℝ) ^ δ))

private lemma tendsto_compactTailMajorant (q : ℕ) {δ M : ℝ} (hδ : 0 < δ) :
    Tendsto (compactTailMajorant q δ M) atTop (𝓝 0) := by
  have hp : Tendsto (fun x : ℝ => x ^ (-δ)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hδ
  have hl : Tendsto (fun x : ℝ => Real.log x / x ^ δ) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hδ).tendsto_div_nhds_zero
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hpn := hp.comp hn
  have hln := hl.comp hn
  unfold compactTailMajorant
  convert (((hln.add (hpn.const_mul (1 / δ + M / δ ^ 2))).add
    (hln.const_mul (M / δ))).const_mul (q : ℝ)) using 1 <;> simp

private lemma compact_uniform_tail
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ rightHalfPlane) :
    TendstoUniformlyOn (derivativePartialSum χ) (orderedDerivativeFunction χ hχ) atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp [Metric.tendstoUniformlyOn_iff]
  obtain ⟨smin, hsmin, hmin⟩ :=
    hK.exists_isMinOn hKne continuous_re.continuousOn
  let δ : ℝ := smin.re
  have hδ : 0 < δ := hKU hsmin
  have hδK : ∀ s ∈ K, δ ≤ s.re := hmin
  obtain ⟨smax, hsmax, hmax⟩ :=
    hK.exists_isMaxOn hKne continuous_norm.continuousOn
  let M : ℝ := ‖smax‖
  have hM : 0 ≤ M := norm_nonneg smax
  have hMK : ∀ s ∈ K, ‖s‖ ≤ M := hmax
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hmaj := (tendsto_compactTailMajorant q hδ (M := M)).eventually
    (gt_mem_nhds hε)
  rw [eventually_atTop] at hmaj
  obtain ⟨N, hN⟩ := hmaj
  filter_upwards [eventually_ge_atTop (max 1 N)] with n hn
  intro s hs
  have hn1 : 1 ≤ n := (le_max_left 1 N).trans hn
  have hnN : N ≤ n := (le_max_right 1 N).trans hn
  have htail := norm_orderedLogDerivativeSeries_sub_sum_range_le χ hχ s
    (hKU hs) hn1
  rw [orderedDerivativeFunction_eq χ hχ s (hKU hs)]
  rw [dist_eq]
  change ‖orderedLogDerivativeSeries χ hχ s (hKU hs) - derivativePartialSum χ n s‖ < ε
  refine htail.trans_lt ?_
  have hweight := norm_logCpowWeight_le (hδK s hs) hn1
  have hbudget := logVariationBudget_le hδ hM (hδK s hs) (hMK s hs) hn1
  have hbound : q * (‖logCpowWeight s n‖ + logVariationBudget s n) ≤
      compactTailMajorant q δ M n := by
    unfold compactTailMajorant
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
    simpa only [add_assoc] using add_le_add hweight hbudget
  exact hbound.trans_lt (hN n hnN)

/-- The partial sums converge locally uniformly on `re s > 0`. -/
theorem tendstoLocallyUniformlyOn_derivativePartialSum
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    TendstoLocallyUniformlyOn (derivativePartialSum χ)
      (orderedDerivativeFunction χ hχ) atTop rightHalfPlane := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact]
  · intro K hKU hK
    exact compact_uniform_tail χ hχ hK hKU
  · exact continuous_re.isOpen_preimage _ isOpen_Ioi

omit [NeZero q] in
private lemma differentiable_derivativePartialSum
    (χ : DirichletCharacter ℂ q) (N : ℕ) :
    Differentiable ℂ (derivativePartialSum χ N) := by
  unfold derivativePartialSum
  apply Differentiable.fun_sum
  intro n hn
  apply Differentiable.mul
  · rcases n with _ | n
    · simp [logCpowWeight, cpowWeight]
    · unfold logCpowWeight cpowWeight
      apply Differentiable.const_mul
      exact Differentiable.const_cpow (by fun_prop) (Or.inl (by
        exact_mod_cast Nat.succ_ne_zero n))
  · fun_prop

/-- The limit is holomorphic on `re s > 0`. -/
theorem differentiableOn_orderedDerivativeFunction
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    DifferentiableOn ℂ (orderedDerivativeFunction χ hχ) rightHalfPlane := by
  exact (tendstoLocallyUniformlyOn_derivativePartialSum χ hχ).differentiableOn
    (Eventually.of_forall fun N => (differentiable_derivativePartialSum χ N).differentiableOn)
    (continuous_re.isOpen_preimage _ isOpen_Ioi)

/-- For `re s > 0` the series `-∑ χ(n) log n · n^{-s}` converges to `L'(s, χ)`, by the
identity theorem. -/
theorem orderedLogDerivativeSeries_eq_deriv_LFunction_of_re_pos
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    orderedLogDerivativeSeries χ hχ s hs = deriv χ.LFunction s := by
  let U : Set ℂ := rightHalfPlane
  have hUopen : IsOpen U := continuous_re.isOpen_preimage _ isOpen_Ioi
  have hF : AnalyticOnNhd ℂ (orderedDerivativeFunction χ hχ) U :=
    (differentiableOn_orderedDerivativeFunction χ hχ).analyticOnNhd hUopen
  have hL : AnalyticOnNhd ℂ (deriv χ.LFunction) U :=
    ((χ.differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ).deriv.mono
      (subset_univ U)
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have htwo : (2 : ℂ) ∈ U := by norm_num [U, rightHalfPlane]
  have hevent : orderedDerivativeFunction χ hχ =ᶠ[𝓝 (2 : ℂ)] deriv χ.LFunction := by
    filter_upwards [(continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    rw [orderedDerivativeFunction_eq χ hχ z (lt_trans zero_lt_one hz)]
    exact orderedLogDerivativeSeries_eq_deriv_LFunction χ hχ z hz
  have hall := hF.eqOn_of_preconnected_of_eventuallyEq hL hpre htwo hevent
  exact (orderedDerivativeFunction_eq χ hχ s hs).symm.trans (hall hs)

end BombieriVinogradov.LDerivContinuation

end

section

/-! ## Horizontal integrals of `L'(s, χ)` -/

open Complex Set

namespace BombieriVinogradov.WeakStripDifference

variable {q : ℕ} [NeZero q]

/-- `∫_{σ₁}^{σ₂} L'(σ + it, χ) dσ = L(σ₂ + it, χ) - L(σ₁ + it, χ)` for nonprincipal `χ`. -/
theorem integral_deriv_LFunction_eq_sub
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (σ₁ σ₂ t : ℝ) :
    (∫ σ in σ₁..σ₂, deriv χ.LFunction (σ + t * I)) =
      χ.LFunction (σ₂ + t * I) - χ.LFunction (σ₁ + t * I) := by
  have diff : ∀ σ : ℝ, DifferentiableAt ℂ χ.LFunction (σ + t * I) := by
    intro σ
    exact χ.differentiable_LFunction hχ (σ + t * I)
  apply intervalIntegral.integral_deriv_eq_sub'
  · exact deriv_fun_re diff
  · intro σ _
    exact (diff σ).restrictScalars ℝ |>.comp σ
      (DifferentiableAt.add_const (c := t * I) (differentiableAt_ofReal σ))
  · have hderiv : Continuous (deriv χ.LFunction) :=
      ((χ.differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ).deriv.continuous
    exact hderiv.continuousOn.comp
      (continuous_ofReal.continuousOn.add continuousOn_const) (mapsTo_image _ _)

end BombieriVinogradov.WeakStripDifference

end
