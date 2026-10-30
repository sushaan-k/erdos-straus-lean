import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import ErdosStraus.Estimates.Progressions

/-!
# Harmonic sums in residue classes

For `T ≥ 1`, `j ≥ 0` and `M ≥ 1` we prove
`∑_{n ≤ T, n ≡ b (mod M)} (log (T/n))^j / n = (log T)^{j+1} / ((j+1) M) + O((log T)^j)`
with an absolute implied constant, first for `M = 1` by comparing the sum with an integral
and then by partial summation. Iterating this gives the estimate (9) from the proof of
Lemma 4.1, again uniformly in `M` and the residue classes:
`∑_{xyz ≤ T, x ≡ b₁, y ≡ b₂, z ≡ b₃ (mod M)} 1/(xyz) = (log T)^3 / (6 M^3) + O((1 + log T)^2)`.
-/

namespace ErdosStraus.DivisorEstimates

open scoped BigOperators
open Set MeasureTheory

/-! ## Logarithmic moments -/

/-- `logMoment j T = ∑_{1 ≤ n ≤ T} (log T - log n)^j / n`. -/
noncomputable def logMoment (j : ℕ) (T : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊T⌋₊, (Real.log T - Real.log (n : ℝ)) ^ j / (n : ℝ)

theorem logMoment_integral (j : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ x in (1 : ℝ)..T, (Real.log T - Real.log x) ^ j / x) =
      (Real.log T) ^ (j + 1) / (j + 1 : ℝ) := by
  have hpos : ∀ x ∈ Set.uIcc (1 : ℝ) T, 0 < x := by
    rw [Set.uIcc_of_le hT]
    intro x hx
    exact zero_lt_one.trans_le hx.1
  have hder : ∀ x ∈ Set.uIcc (1 : ℝ) T,
      HasDerivAt (fun x : ℝ => -(Real.log T - Real.log x) ^ (j + 1) / (j + 1 : ℝ))
        ((Real.log T - Real.log x) ^ j / x) x := by
    intro x hx
    have hd₀ := (Real.hasDerivAt_log (ne_of_gt (hpos x hx))).const_sub (Real.log T)
    have hd := ((hd₀.pow (j + 1)).neg).div_const (j + 1 : ℝ)
    refine hd.congr_deriv ?_
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp [ne_of_gt (hpos x hx), show (j : ℝ) + 1 ≠ 0 by positivity]
  have hc : ContinuousOn (fun x : ℝ => (Real.log T - Real.log x) ^ j / x)
      (Set.uIcc (1 : ℝ) T) := by
    apply ContinuousOn.div
    · exact (continuousOn_const.sub (Real.continuousOn_log.mono
        (fun x hx => ne_of_gt (hpos x hx)))).pow j
    · exact continuousOn_id
    · intro x hx
      exact ne_of_gt (hpos x hx)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hc.intervalIntegrable
  simpa [neg_div] using hi

theorem logMoment_antitone (j : ℕ) {T : ℝ} (_hT : 1 ≤ T) :
    AntitoneOn (fun x : ℝ => (Real.log T - Real.log x) ^ j / x) (Set.Icc 1 T) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := zero_lt_one.trans_le hx.1
  have hy0 : 0 < y := zero_lt_one.trans_le hy.1
  have hnny : 0 ≤ Real.log T - Real.log y := sub_nonneg.mpr
    (Real.log_le_log hy0 hy.2)
  have hn : Real.log T - Real.log y ≤ Real.log T - Real.log x :=
    sub_le_sub_left (Real.log_le_log hx0 hxy) _
  calc
    _ ≤ (Real.log T - Real.log y) ^ j / x :=
      div_le_div_of_nonneg_left (pow_nonneg hnny _) hx0 hxy
    _ ≤ _ := div_le_div_of_nonneg_right (pow_le_pow_left₀ hnny hn j) hx0.le

/-- For `f` nonnegative and antitone on `[1, T]`, the sum `∑_{1 ≤ n ≤ T} f n` differs from
`∫_1^T f` by at most `f 1`. -/
theorem abs_sum_Icc_floor_sub_integral_le {f : ℝ → ℝ} {T : ℝ} (hT : 1 ≤ T)
    (hf : AntitoneOn f (Set.Icc 1 T)) (hnn : ∀ x ∈ Set.Icc 1 T, 0 ≤ f x) :
    |(∑ n ∈ Finset.Icc 1 ⌊T⌋₊, f n) - ∫ x in (1 : ℝ)..T, f x| ≤ f 1 := by
  let N := ⌊T⌋₊
  have hN : 1 ≤ N := Nat.floor_pos.mpr hT
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNT : (N : ℝ) ≤ T := Nat.floor_le (zero_le_one.trans hT)
  have hTN : T < (N : ℝ) + 1 := Nat.lt_floor_add_one T
  have hf1 : 0 ≤ f 1 := hnn 1 ⟨le_rfl, hT⟩
  have ha1N : AntitoneOn f (Set.uIcc 1 (N : ℝ)) := by
    rw [Set.uIcc_of_le hN1]
    exact hf.mono (Set.Icc_subset_Icc le_rfl hNT)
  have haNT : AntitoneOn f (Set.uIcc (N : ℝ) T) := by
    rw [Set.uIcc_of_le hNT]
    exact hf.mono (Set.Icc_subset_Icc hN1 le_rfl)
  have hupper : (∑ n ∈ Finset.Icc 1 N, f n) ≤
      f 1 + ∫ x in (1 : ℝ)..(N : ℝ), f x := by
    rw [← Finset.sum_erase_add (Finset.Icc 1 N) (fun n : ℕ => f n)
      (Finset.left_mem_Icc.mpr hN), add_comm]
    simp only [Finset.Icc_erase_left, Nat.cast_one]
    apply add_le_add_right
    have hshift : AntitoneOn (fun x : ℝ => f (x - 1))
        (Set.Icc (2 : ℝ) ((N + 1 : ℕ) : ℝ)) := by
      intro x hx y hy hxy
      rcases hx with ⟨hx1, hx2⟩
      rcases hy with ⟨hy1, hy2⟩
      push_cast at hx2 hy2
      apply hf
      · constructor <;> linarith
      · constructor <;> linarith
      · linarith
    have hh := hshift.sum_le_integral_Ico (show 2 ≤ N + 1 by omega)
    have he : (∑ n ∈ Finset.Ico 2 (N + 1), f (((n + 1 : ℕ) : ℝ) - 1)) =
        ∑ n ∈ Finset.Ico 2 (N + 1), f n := by
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    rw [he] at hh
    have hi : (∫ x in (2 : ℕ)..((N + 1 : ℕ) : ℝ), f (x - 1)) =
        ∫ x in (1 : ℝ)..(N : ℝ), f x := by
      rw [intervalIntegral.integral_comp_sub_right]
      norm_num
    rwa [hi] at hh
  have hlower : (∫ x in (1 : ℝ)..(N : ℝ), f x) ≤
      ∑ n ∈ Finset.Icc 1 N, f n := by
    have ha : AntitoneOn f (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
      simpa only [Nat.cast_one] using hf.mono (Set.Icc_subset_Icc le_rfl hNT)
    have hh := ha.integral_le_sum_Ico hN
    norm_num only [Nat.cast_one] at hh
    apply hh.trans
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.Ico_subset_Icc_self
    intro n hn hn'
    have hni := Finset.mem_Icc.mp hn
    exact hnn n ⟨by exact_mod_cast hni.1,
      (Nat.cast_le.mpr hni.2).trans hNT⟩
  have htail0 : 0 ≤ ∫ x in (N : ℝ)..T, f x :=
    intervalIntegral.integral_nonneg hNT (fun x hx =>
      hnn x ⟨hN1.trans hx.1, hx.2⟩)
  have htail : (∫ x in (N : ℝ)..T, f x) ≤ f 1 := by
    have hh := intervalIntegral.integral_mono_on hNT haNT.intervalIntegrable
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f 1) volume N T)
      (fun x hx => hf ⟨le_rfl, hT⟩ ⟨hN1.trans hx.1, hx.2⟩ (hN1.trans hx.1))
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hh
    exact hh.trans (by nlinarith)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ha1N.intervalIntegrable haNT.intervalIntegrable
  change |(∑ n ∈ Finset.Icc 1 N, f n) - ∫ x in (1 : ℝ)..T, f x| ≤ _
  rw [abs_le]
  constructor <;> linarith

/-- `∑_{n ≤ T} (log (T/n))^j / n = (log T)^{j+1} / (j+1) + O((log T)^j)`. -/
theorem abs_logMoment_sub_main_le (j : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    |logMoment j T - (Real.log T) ^ (j + 1) / (j + 1 : ℝ)| ≤
      (Real.log T) ^ j := by
  have h := abs_sum_Icc_floor_sub_integral_le hT (logMoment_antitone j hT) (by
    intro x hx
    have hx0 : 0 < x := zero_lt_one.trans_le hx.1
    exact div_nonneg (pow_nonneg (sub_nonneg.mpr (Real.log_le_log hx0 hx.2)) _)
      hx0.le)
  rw [logMoment_integral j hT] at h
  simpa only [logMoment, Real.log_one, sub_zero, div_one] using h

end ErdosStraus.DivisorEstimates

/-! ## The triple harmonic sum -/

namespace ErdosStraus.DivisorEstimates

open scoped BigOperators

/-- `harmonicTransform f T = ∑_{1 ≤ n ≤ T} f (T/n) / n`. -/
noncomputable def harmonicTransform (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊T⌋₊, f (T / (n : ℝ)) / (n : ℝ)

theorem quotient_mem_one_T {T : ℝ} (hT : 1 ≤ T) {n : ℕ}
    (hn : n ∈ Finset.Icc 1 ⌊T⌋₊) : 1 ≤ T / (n : ℝ) ∧ T / (n : ℝ) ≤ T := by
  have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Finset.mem_Icc.mp hn).1
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hnT : (n : ℝ) ≤ T :=
    (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le (zero_le_one.trans hT))
  constructor
  · exact (le_div_iff₀ hnpos).mpr (by simpa using hnT)
  · exact (div_le_iff₀ hnpos).mpr (le_mul_of_one_le_right (zero_le_one.trans hT) hn1)

theorem harmonicTransform_log_pow (j : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    harmonicTransform (fun u => (Real.log u) ^ j) T = logMoment j T := by
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  dsimp only
  rw [Real.log_div (ne_of_gt (zero_lt_one.trans_le hT)) (ne_of_gt hnpos)]

theorem harmonicTransform_add (f g : ℝ → ℝ) (T : ℝ) :
    harmonicTransform (fun u => f u + g u) T =
      harmonicTransform f T + harmonicTransform g T := by
  simp [harmonicTransform, add_div, Finset.sum_add_distrib]

theorem harmonicTransform_const_mul (f : ℝ → ℝ) (c T : ℝ) :
    harmonicTransform (fun u => c * f u) T = c * harmonicTransform f T := by
  simp [harmonicTransform, mul_div_assoc, Finset.mul_sum]

theorem harmonicTransform_div_const (f : ℝ → ℝ) (c T : ℝ) :
    harmonicTransform (fun u => f u / c) T = harmonicTransform f T / c := by
  simp only [harmonicTransform, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem abs_harmonicTransform_sub_le (f g R : ℝ → ℝ) {T : ℝ} (hT : 1 ≤ T)
    (hbound : ∀ u : ℝ, 1 ≤ u → u ≤ T → |f u - g u| ≤ R u) :
    |harmonicTransform f T - harmonicTransform g T| ≤ harmonicTransform R T := by
  unfold harmonicTransform
  rw [← Finset.sum_sub_distrib]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum _)
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  rw [← sub_div, abs_div, abs_of_pos hnpos]
  exact div_le_div_of_nonneg_right
    (hbound _ (quotient_mem_one_T hT hn).1 (quotient_mem_one_T hT hn).2) hnpos.le

theorem logMoment_upper (j : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    logMoment j T ≤ (Real.log T) ^ (j + 1) / (j + 1 : ℝ) + (Real.log T) ^ j := by
  have h := (abs_le.mp (abs_logMoment_sub_main_le j hT)).2
  linarith

/-- `∑_{xy ≤ T} 1/(xy)`, written as `∑_{n ≤ T} (∑_{m ≤ T/n} 1/m) / n`. -/
noncomputable def harmonicDouble (T : ℝ) : ℝ :=
  harmonicTransform (logMoment 0) T

/-- `∑_{xyz ≤ T} 1/(xyz)`, written as `∑_{n ≤ T} harmonicDouble (T/n) / n`. -/
noncomputable def harmonicTriple (T : ℝ) : ℝ :=
  harmonicTransform harmonicDouble T

/-- `∑_{xy ≤ T} 1/(xy) = (log T)^2/2 + O(1 + log T)`. -/
theorem abs_harmonicDouble_sub_main_le {T : ℝ} (hT : 1 ≤ T) :
    |harmonicDouble T - (Real.log T) ^ 2 / 2| ≤ 1 + 2 * Real.log T := by
  have htrans := abs_harmonicTransform_sub_le (logMoment 0) Real.log (fun _ => 1) hT (by
    intro u hu _
    simpa using abs_logMoment_sub_main_le 0 hu)
  have hlog := harmonicTransform_log_pow 1 hT
  simp only [pow_one] at hlog
  have hconst := harmonicTransform_log_pow 0 hT
  simp only [pow_zero] at hconst
  rw [hlog, hconst] at htrans
  have hm := abs_logMoment_sub_main_le 1 hT
  norm_num only [Nat.cast_one, Nat.cast_ofNat, one_add_one_eq_two, pow_one] at hm
  have h₀ := logMoment_upper 0 hT
  norm_num at h₀
  have hh := abs_add_le (harmonicDouble T - logMoment 1 T)
    (logMoment 1 T - (Real.log T) ^ 2 / 2)
  have he : harmonicDouble T - logMoment 1 T +
      (logMoment 1 T - (Real.log T) ^ 2 / 2) =
      harmonicDouble T - (Real.log T) ^ 2 / 2 := by ring
  rw [he] at hh
  change |harmonicDouble T - logMoment 1 T| ≤ logMoment 0 T at htrans
  linarith

/-- The estimate (9) with `M = 1`:
`|∑_{xyz ≤ T} 1/(xyz) - (log T)^3/6| ≤ 4 (1 + log T)^2`. -/
theorem abs_harmonicTriple_sub_main_le {T : ℝ} (hT : 1 ≤ T) :
    |harmonicTriple T - (Real.log T) ^ 3 / 6| ≤
      4 * (1 + Real.log T) ^ 2 := by
  have htrans := abs_harmonicTransform_sub_le harmonicDouble
    (fun u => (Real.log u) ^ 2 / 2) (fun u => 1 + 2 * Real.log u) hT (by
      intro u hu _
      exact abs_harmonicDouble_sub_main_le hu)
  have he₂ : harmonicTransform (fun u => (Real.log u) ^ 2 / 2) T =
      logMoment 2 T / 2 := by
    rw [harmonicTransform_div_const, harmonicTransform_log_pow 2 hT]
  have heR : harmonicTransform (fun u => 1 + 2 * Real.log u) T =
      logMoment 0 T + 2 * logMoment 1 T := by
    rw [harmonicTransform_add, harmonicTransform_const_mul]
    have h₀ := harmonicTransform_log_pow 0 hT
    have h₁ := harmonicTransform_log_pow 1 hT
    simpa using congrArg₂ (fun x y : ℝ => x + 2 * y) h₀ h₁
  rw [he₂, heR] at htrans
  change |harmonicTriple T - logMoment 2 T / 2| ≤
    logMoment 0 T + 2 * logMoment 1 T at htrans
  have hm := abs_logMoment_sub_main_le 2 hT
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at hm
  have hhalf : |logMoment 2 T / 2 - (Real.log T) ^ 3 / 6| ≤ (Real.log T) ^ 2 / 2 := by
    have he : logMoment 2 T / 2 - (Real.log T) ^ 3 / 6 =
        (logMoment 2 T - (Real.log T) ^ 3 / 3) / 2 := by ring
    rw [he, abs_div]
    norm_num
    linarith
  have h₀ := logMoment_upper 0 hT
  have h₁ := logMoment_upper 1 hT
  norm_num at h₀ h₁
  have hh := abs_add_le (harmonicTriple T - logMoment 2 T / 2)
    (logMoment 2 T / 2 - (Real.log T) ^ 3 / 6)
  have he : harmonicTriple T - logMoment 2 T / 2 +
      (logMoment 2 T / 2 - (Real.log T) ^ 3 / 6) =
      harmonicTriple T - (Real.log T) ^ 3 / 6 := by ring
  rw [he] at hh
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  nlinarith

/-! ## Logarithmic moments in residue classes -/

/-- Partial summation: if every partial sum of `a` has absolute value at most `E` and `f` is
nonnegative and nonincreasing, then `|∑_{i < N} f i * a i| ≤ E * f 0`. -/
theorem abs_weighted_sum_le_of_abs_prefix_le (a f : ℕ → ℝ) (N : ℕ) (E : ℝ)
    (hN : 0 < N)
    (hprefix : ∀ k ≤ N, |∑ i ∈ Finset.range k, a i| ≤ E)
    (hf : ∀ i < N, 0 ≤ f i)
    (hmono : ∀ i, i + 1 < N → f (i + 1) ≤ f i) :
    |∑ i ∈ Finset.range N, f i * a i| ≤ E * f 0 := by
  have hlast : N - 1 < N := by omega
  have heq := Finset.sum_range_by_parts f a N
  simp only [smul_eq_mul] at heq
  rw [heq]
  have htel : ∀ n : ℕ, (∑ i ∈ Finset.range n, (f i - f (i + 1))) = f 0 - f n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  calc
    _ ≤ |f (N - 1) * ∑ i ∈ Finset.range N, a i| +
        |∑ i ∈ Finset.range (N - 1),
          (f (i + 1) - f i) * ∑ j ∈ Finset.range (i + 1), a j| := abs_sub _ _
    _ ≤ f (N - 1) * E +
        ∑ i ∈ Finset.range (N - 1), (f i - f (i + 1)) * E := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg (hf _ hlast)]
        exact mul_le_mul_of_nonneg_left (hprefix N le_rfl) (hf _ hlast)
      · apply le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum _)
        intro i hi
        have hiN : i + 1 < N := by have hh := Finset.mem_range.mp hi; omega
        rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr (hmono i hiN))]
        have he : -(f (i + 1) - f i) = f i - f (i + 1) := by ring
        rw [he]
        exact mul_le_mul_of_nonneg_left (hprefix (i + 1) (by omega))
          (sub_nonneg.mpr (hmono i hiN))
    _ = E * f 0 := by rw [← Finset.sum_mul, htel]; ring

/-- `∑_{1 ≤ n ≤ T, n ≡ b (mod M)} (log T - log n)^j / n`. -/
noncomputable def residueLogMoment (M b j : ℕ) (T : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 ⌊T⌋₊).filter (fun n => n ≡ b [MOD M]),
    (Real.log T - Real.log (n : ℝ)) ^ j / (n : ℝ)

theorem abs_residueLogMoment_sub_density_le (M b j : ℕ) (hM : 0 < M)
    {T : ℝ} (hT : 1 ≤ T) :
    |residueLogMoment M b j T - (1 / (M : ℝ)) * logMoment j T| ≤
      2 * (Real.log T) ^ j := by
  classical
  let N := ⌊T⌋₊
  let α : ℝ := 1 / (M : ℝ)
  let a : ℕ → ℝ := fun i => (if (1 + i) ≡ b [MOD M] then 1 else 0) - α
  let f : ℕ → ℝ := fun i =>
    (Real.log T - Real.log ((1 + i : ℕ) : ℝ)) ^ j / ((1 + i : ℕ) : ℝ)
  have hshift (g : ℕ → ℝ) (k : ℕ) :
      (∑ i ∈ Finset.range k, g (1 + i)) = ∑ n ∈ Finset.Ico 1 (1 + k), g n := by
    simpa only [Nat.zero_add, Nat.add_comm k 1, Nat.Ico_zero_eq_range] using
      Finset.sum_Ico_add g 0 k 1
  have hprefix : ∀ k ≤ N, |∑ i ∈ Finset.range k, a i| ≤ 2 := by
    intro k hk
    have hc := SieveEstimates.abs_Ico_modEq_card_sub_length 1 (1 + k) b (by omega) hM
    have he : (∑ i ∈ Finset.range k, a i) =
        (((Finset.Ico 1 (1 + k)).filter (fun n => n ≡ b [MOD M])).card : ℝ) -
          (k : ℝ) / (M : ℝ) := by
      simp only [a, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      rw [hshift (fun n => if n ≡ b [MOD M] then (1 : ℝ) else 0)]
      simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
        Finset.card_range]
      dsimp [α]
      ring
    rw [he]
    convert hc using 1
    push_cast
    ring_nf
  have hf : ∀ i < N, 0 ≤ f i := by
    intro i hi
    have hn : ((1 + i : ℕ) : ℝ) ≤ T :=
      (Nat.cast_le.mpr (by omega : 1 + i ≤ ⌊T⌋₊)).trans (Nat.floor_le (zero_le_one.trans hT))
    have hpos : (0 : ℝ) < ((1 + i : ℕ) : ℝ) := by positivity
    exact div_nonneg (pow_nonneg (sub_nonneg.mpr (Real.log_le_log hpos hn)) _) hpos.le
  have hmono : ∀ i, i + 1 < N → f (i + 1) ≤ f i := by
    intro i hi
    apply logMoment_antitone j hT
    · constructor
      · exact_mod_cast (show 1 ≤ 1 + i by omega)
      · exact (Nat.cast_le.mpr (by omega : 1 + i ≤ ⌊T⌋₊)).trans
          (Nat.floor_le (zero_le_one.trans hT))
    · constructor
      · exact_mod_cast (show 1 ≤ 1 + (i + 1) by omega)
      · exact (Nat.cast_le.mpr (by omega : 1 + (i + 1) ≤ ⌊T⌋₊)).trans
          (Nat.floor_le (zero_le_one.trans hT))
    · exact_mod_cast (show 1 + i ≤ 1 + (i + 1) by omega)
  have h := abs_weighted_sum_le_of_abs_prefix_le a f N 2 (Nat.floor_pos.mpr hT)
    hprefix hf hmono
  have heq : (∑ i ∈ Finset.range N, f i * a i) =
      residueLogMoment M b j T - α * logMoment j T := by
    simp only [a, f, mul_sub, Finset.sum_sub_distrib]
    rw [hshift (fun n => (Real.log T - Real.log (n : ℝ)) ^ j / (n : ℝ) *
      (if n ≡ b [MOD M] then (1 : ℝ) else 0)),
      hshift (fun n => (Real.log T - Real.log (n : ℝ)) ^ j / (n : ℝ) * α)]
    have hI : Finset.Ico 1 (1 + N) = Finset.Icc 1 N := by
      ext n
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [hI]
    unfold residueLogMoment logMoment
    have hleft :
        (∑ n ∈ Finset.Icc 1 N,
          (Real.log T - Real.log (n : ℝ)) ^ j / (n : ℝ) *
            (if n ≡ b [MOD M] then 1 else 0)) =
        ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n ≡ b [MOD M]),
          (Real.log T - Real.log (n : ℝ)) ^ j / (n : ℝ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      split_ifs <;> simp
    rw [hleft, ← Finset.sum_mul]
    ring
  rw [heq] at h
  simpa [f, α] using h

/-- The display before (9) in the proof of Lemma 4.1:
`∑_{n ≤ T, n ≡ b (mod M)} (log (T/n))^j / n = (log T)^{j+1} / ((j+1) M) + O((log T)^j)`,
with remainder at most `3 (log T)^j` uniformly in `b` and `M`. -/
theorem abs_residueLogMoment_sub_main_le (M b j : ℕ) (hM : 0 < M)
    {T : ℝ} (hT : 1 ≤ T) :
    |residueLogMoment M b j T -
        (Real.log T) ^ (j + 1) / ((j + 1 : ℝ) * (M : ℝ))| ≤
      3 * (Real.log T) ^ j := by
  have h₀ := abs_residueLogMoment_sub_density_le M b j hM hT
  have h₁ := abs_logMoment_sub_main_le j hT
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := zero_lt_one.trans_le hM1
  have hα : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
  have hα1 : (1 : ℝ) / (M : ℝ) ≤ 1 := (div_le_one hMpos).mpr hM1
  have hh := abs_add_le (residueLogMoment M b j T - (1 / (M : ℝ)) * logMoment j T)
    ((1 / (M : ℝ)) * (logMoment j T - (Real.log T) ^ (j + 1) / (j + 1 : ℝ)))
  have he : residueLogMoment M b j T - (1 / (M : ℝ)) * logMoment j T +
      (1 / (M : ℝ)) * (logMoment j T - (Real.log T) ^ (j + 1) / (j + 1 : ℝ)) =
      residueLogMoment M b j T -
        (Real.log T) ^ (j + 1) / ((j + 1 : ℝ) * (M : ℝ)) := by
    field_simp
    ring
  rw [he, abs_mul, abs_of_nonneg hα] at hh
  have hn : 0 ≤ (Real.log T) ^ j := pow_nonneg (Real.log_nonneg hT) _
  have hm := (mul_le_mul_of_nonneg_left h₁ hα).trans
    (mul_le_of_le_one_left hn hα1)
  linarith

/-! ## The triple harmonic sum in residue classes -/

/-- `∑_{1 ≤ n ≤ T, n ≡ b (mod M)} f (T/n) / n`. -/
noncomputable def residueHarmonicTransform (M b : ℕ) (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 ⌊T⌋₊).filter (fun n => n ≡ b [MOD M]),
    f (T / (n : ℝ)) / (n : ℝ)

theorem residueHarmonicTransform_log_pow (M b j : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    residueHarmonicTransform M b (fun u => (Real.log u) ^ j) T =
      residueLogMoment M b j T := by
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  dsimp only
  rw [Real.log_div (ne_of_gt (zero_lt_one.trans_le hT)) (ne_of_gt hnpos)]

theorem residueHarmonicTransform_add (M b : ℕ) (f g : ℝ → ℝ) (T : ℝ) :
    residueHarmonicTransform M b (fun u => f u + g u) T =
      residueHarmonicTransform M b f T + residueHarmonicTransform M b g T := by
  simp [residueHarmonicTransform, add_div, Finset.sum_add_distrib]

theorem residueHarmonicTransform_const_mul (M b : ℕ) (f : ℝ → ℝ) (c T : ℝ) :
    residueHarmonicTransform M b (fun u => c * f u) T =
      c * residueHarmonicTransform M b f T := by
  simp [residueHarmonicTransform, mul_div_assoc, Finset.mul_sum]

theorem residueHarmonicTransform_div_const (M b : ℕ) (f : ℝ → ℝ) (c T : ℝ) :
    residueHarmonicTransform M b (fun u => f u / c) T =
      residueHarmonicTransform M b f T / c := by
  simp only [residueHarmonicTransform, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem abs_residueHarmonicTransform_sub_le (M b : ℕ) (f g R : ℝ → ℝ)
    {T : ℝ} (hT : 1 ≤ T)
    (hbound : ∀ u : ℝ, 1 ≤ u → u ≤ T → |f u - g u| ≤ R u) :
    |residueHarmonicTransform M b f T - residueHarmonicTransform M b g T| ≤
      residueHarmonicTransform M b R T := by
  unfold residueHarmonicTransform
  rw [← Finset.sum_sub_distrib]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum _)
  intro n hn
  have hnI := (Finset.mem_filter.mp hn).1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hnI).1
  rw [← sub_div, abs_div, abs_of_pos hnpos]
  exact div_le_div_of_nonneg_right
    (hbound _ (quotient_mem_one_T hT hnI).1 (quotient_mem_one_T hT hnI).2) hnpos.le

theorem residueLogMoment_upper (M b j : ℕ) (hM : 0 < M) {T : ℝ} (hT : 1 ≤ T) :
    residueLogMoment M b j T ≤
      (Real.log T) ^ (j + 1) / ((j + 1 : ℝ) * (M : ℝ)) + 3 * (Real.log T) ^ j := by
  have h := (abs_le.mp (abs_residueLogMoment_sub_main_le M b j hM hT)).2
  linarith

/-- `∑_{xy ≤ T, x ≡ b₁, y ≡ b₂ (mod M)} 1/(xy)`. -/
noncomputable def residueHarmonicDouble (M b₁ b₂ : ℕ) (T : ℝ) : ℝ :=
  residueHarmonicTransform M b₁ (residueLogMoment M b₂ 0) T

/-- `∑_{xyz ≤ T, x ≡ b₁, y ≡ b₂, z ≡ b₃ (mod M)} 1/(xyz)`; see
`residueHarmonicTriple_eq_nested_sum`. -/
noncomputable def residueHarmonicTriple (M b₁ b₂ b₃ : ℕ) (T : ℝ) : ℝ :=
  residueHarmonicTransform M b₁ (residueHarmonicDouble M b₂ b₃) T

theorem residueHarmonicTriple_eq_nested_sum (M b₁ b₂ b₃ : ℕ) (T : ℝ) :
    residueHarmonicTriple M b₁ b₂ b₃ T =
      ∑ x ∈ (Finset.Icc 1 ⌊T⌋₊).filter (fun x => x ≡ b₁ [MOD M]),
        ∑ y ∈ (Finset.Icc 1 ⌊T / (x : ℝ)⌋₊).filter (fun y => y ≡ b₂ [MOD M]),
          ∑ z ∈ (Finset.Icc 1 ⌊T / (x : ℝ) / (y : ℝ)⌋₊).filter
            (fun z => z ≡ b₃ [MOD M]),
            (1 : ℝ) / ((x : ℝ) * (y : ℝ) * (z : ℝ)) := by
  simp only [residueHarmonicTriple, residueHarmonicDouble, residueHarmonicTransform,
    residueLogMoment, pow_zero, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem abs_residueHarmonicDouble_sub_main_le (M b₁ b₂ : ℕ) (hM : 0 < M)
    {T : ℝ} (hT : 1 ≤ T) :
    |residueHarmonicDouble M b₁ b₂ T - (Real.log T) ^ 2 / (2 * (M : ℝ) ^ 2)| ≤
      9 * (1 + Real.log T) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have htrans := abs_residueHarmonicTransform_sub_le M b₁
    (residueLogMoment M b₂ 0) (fun u => Real.log u / (M : ℝ)) (fun _ => 3) hT (by
      intro u hu _
      simpa using abs_residueLogMoment_sub_main_le M b₂ 0 hM hu)
  have he₁ : residueHarmonicTransform M b₁ (fun u => Real.log u / (M : ℝ)) T =
      residueLogMoment M b₁ 1 T / (M : ℝ) := by
    rw [residueHarmonicTransform_div_const]
    exact congrArg (fun x : ℝ => x / (M : ℝ)) (by
      simpa using residueHarmonicTransform_log_pow M b₁ 1 hT)
  have he₃ : residueHarmonicTransform M b₁ (fun _ => (3 : ℝ)) T =
      3 * residueLogMoment M b₁ 0 T := by
    have he : (fun _ : ℝ => (3 : ℝ)) = fun u => 3 * (Real.log u) ^ 0 := by funext; simp
    rw [he, residueHarmonicTransform_const_mul, residueHarmonicTransform_log_pow M b₁ 0 hT]
  rw [he₁, he₃] at htrans
  have hm := abs_residueLogMoment_sub_main_le M b₁ 1 hM hT
  norm_num only [Nat.cast_one, Nat.cast_ofNat, one_add_one_eq_two, pow_one] at hm
  have hmain : |residueLogMoment M b₁ 1 T / (M : ℝ) -
      (Real.log T) ^ 2 / (2 * (M : ℝ) ^ 2)| ≤ 3 * Real.log T := by
    have he : residueLogMoment M b₁ 1 T / (M : ℝ) -
        (Real.log T) ^ 2 / (2 * (M : ℝ) ^ 2) =
      (residueLogMoment M b₁ 1 T - (Real.log T) ^ 2 / (2 * (M : ℝ))) / (M : ℝ) := by
      field_simp
    rw [he, abs_div, abs_of_pos hMpos]
    have hh := div_le_div_of_nonneg_right hm hMpos.le
    exact hh.trans (div_le_self (mul_nonneg (by norm_num) (Real.log_nonneg hT)) hM1)
  have h₀ := residueLogMoment_upper M b₁ 0 hM hT
  norm_num at h₀
  have h₀' : residueLogMoment M b₁ 0 T ≤ Real.log T + 3 :=
    h₀.trans (add_le_add_left (div_le_self (Real.log_nonneg hT) hM1) 3)
  have hh := abs_add_le (residueHarmonicDouble M b₁ b₂ T - residueLogMoment M b₁ 1 T / M)
    (residueLogMoment M b₁ 1 T / M - (Real.log T) ^ 2 / (2 * (M : ℝ) ^ 2))
  have he : residueHarmonicDouble M b₁ b₂ T - residueLogMoment M b₁ 1 T / M +
      (residueLogMoment M b₁ 1 T / M - (Real.log T) ^ 2 / (2 * (M : ℝ) ^ 2)) =
      residueHarmonicDouble M b₁ b₂ T - (Real.log T) ^ 2 / (2 * (M : ℝ) ^ 2) := by ring
  rw [he] at hh
  change |residueHarmonicDouble M b₁ b₂ T - residueLogMoment M b₁ 1 T / M| ≤ _ at htrans
  have hlog := Real.log_nonneg hT
  nlinarith

/-- The estimate (9): the sum of `1/(xyz)` over `xyz ≤ T` in fixed residue classes mod `M`
is `(log T)³/(6M³) + O((1 + log T)²)`, uniformly in `M` and the three classes. -/
theorem abs_residueHarmonicTriple_sub_main_le (M b₁ b₂ b₃ : ℕ) (hM : 0 < M)
    {T : ℝ} (hT : 1 ≤ T) :
    |residueHarmonicTriple M b₁ b₂ b₃ T -
        (Real.log T) ^ 3 / (6 * (M : ℝ) ^ 3)| ≤
      40 * (1 + Real.log T) ^ 2 := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have htrans := abs_residueHarmonicTransform_sub_le M b₁
    (residueHarmonicDouble M b₂ b₃)
    (fun u => (Real.log u) ^ 2 / (2 * (M : ℝ) ^ 2))
    (fun u => 9 * (1 + Real.log u)) hT (by
      intro u hu _
      exact abs_residueHarmonicDouble_sub_main_le M b₂ b₃ hM hu)
  have he₂ : residueHarmonicTransform M b₁
      (fun u => (Real.log u) ^ 2 / (2 * (M : ℝ) ^ 2)) T =
      residueLogMoment M b₁ 2 T / (2 * (M : ℝ) ^ 2) := by
    rw [residueHarmonicTransform_div_const, residueHarmonicTransform_log_pow M b₁ 2 hT]
  have heR : residueHarmonicTransform M b₁ (fun u => 9 * (1 + Real.log u)) T =
      9 * (residueLogMoment M b₁ 0 T + residueLogMoment M b₁ 1 T) := by
    rw [residueHarmonicTransform_const_mul, residueHarmonicTransform_add]
    have h₀ := residueHarmonicTransform_log_pow M b₁ 0 hT
    have h₁ := residueHarmonicTransform_log_pow M b₁ 1 hT
    simpa using congrArg₂ (fun x y : ℝ => 9 * (x + y)) h₀ h₁
  rw [he₂, heR] at htrans
  change |residueHarmonicTriple M b₁ b₂ b₃ T - residueLogMoment M b₁ 2 T / (2 * (M : ℝ) ^ 2)| ≤
    9 * (residueLogMoment M b₁ 0 T + residueLogMoment M b₁ 1 T) at htrans
  have hm := abs_residueLogMoment_sub_main_le M b₁ 2 hM hT
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at hm
  have hmain : |residueLogMoment M b₁ 2 T / (2 * (M : ℝ) ^ 2) -
      (Real.log T) ^ 3 / (6 * (M : ℝ) ^ 3)| ≤ 3 * (Real.log T) ^ 2 := by
    have he : residueLogMoment M b₁ 2 T / (2 * (M : ℝ) ^ 2) -
        (Real.log T) ^ 3 / (6 * (M : ℝ) ^ 3) =
      (residueLogMoment M b₁ 2 T - (Real.log T) ^ 3 / (3 * (M : ℝ))) /
        (2 * (M : ℝ) ^ 2) := by field_simp; ring
    rw [he, abs_div, abs_of_pos (by positivity : 0 < 2 * (M : ℝ) ^ 2)]
    exact (div_le_div_of_nonneg_right hm (by positivity)).trans
      (div_le_self (by positivity) (by nlinarith : 1 ≤ 2 * (M : ℝ) ^ 2))
  have h₀ := residueLogMoment_upper M b₁ 0 hM hT
  have h₁ := residueLogMoment_upper M b₁ 1 hM hT
  norm_num at h₀ h₁
  have h₀' : residueLogMoment M b₁ 0 T ≤ Real.log T + 3 :=
    h₀.trans (add_le_add_left (div_le_self (Real.log_nonneg hT) hM1) 3)
  have h₁' : residueLogMoment M b₁ 1 T ≤ (Real.log T) ^ 2 / 2 + 3 * Real.log T := by
    apply h₁.trans
    apply add_le_add_left
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num : (0 : ℝ) < 2)
    nlinarith
  have hh := abs_add_le
    (residueHarmonicTriple M b₁ b₂ b₃ T - residueLogMoment M b₁ 2 T / (2 * (M : ℝ) ^ 2))
    (residueLogMoment M b₁ 2 T / (2 * (M : ℝ) ^ 2) - (Real.log T) ^ 3 / (6 * (M : ℝ) ^ 3))
  have he : residueHarmonicTriple M b₁ b₂ b₃ T - residueLogMoment M b₁ 2 T / (2 * (M : ℝ) ^ 2) +
      (residueLogMoment M b₁ 2 T / (2 * (M : ℝ) ^ 2) - (Real.log T) ^ 3 / (6 * (M : ℝ) ^ 3)) =
      residueHarmonicTriple M b₁ b₂ b₃ T - (Real.log T) ^ 3 / (6 * (M : ℝ) ^ 3) := by ring
  rw [he] at hh
  have hlog := Real.log_nonneg hT
  nlinarith

end ErdosStraus.DivisorEstimates
