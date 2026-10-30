import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic
import Mathlib.Data.Int.CardIntervalMod

/-!
# Finite partial summation

Discrete forms of the Abel summation used in Section 3. A nonnegative decreasing weight
preserves inequalities between prefix sums, which bounds `∑ 1/n` over a set of integers
with a linear counting bound. The weighted sum `∑_{m<k≤n} u_k c_k` is bounded by the prefix
sums of `c`; this is the summation by parts that deduces Lemma 3.8 from Theorem 3.7.
The file also proves `∑_{L ≤ n ≤ U} 1/n ≤ 1/L + log(U/L)`.
-/

namespace ErdosStraus.SieveEstimates

open scoped BigOperators

/-- If every prefix sum of `a` is at most the corresponding prefix sum of `b`, and `f` is
nonnegative and decreasing on `[0, N)`, then `∑_{i<N} f_i a_i ≤ ∑_{i<N} f_i b_i`. -/
theorem sum_mul_le_of_prefix_sum_le (a b f : ℕ → ℝ) (N : ℕ)
    (hprefix : ∀ k ≤ N, ∑ i ∈ Finset.range k, a i ≤ ∑ i ∈ Finset.range k, b i)
    (hf : ∀ i < N, 0 ≤ f i)
    (hmono : ∀ i, i + 1 < N → f (i + 1) ≤ f i) :
    ∑ i ∈ Finset.range N, f i * a i ≤ ∑ i ∈ Finset.range N, f i * b i := by
  by_cases hN : N = 0
  · simp [hN]
  have hlast : N - 1 < N := by omega
  have hsum : ∑ i ∈ Finset.range N, f i * (a i - b i) ≤ 0 := by
    have heq := Finset.sum_range_by_parts f (fun i => a i - b i) N
    simp only [smul_eq_mul] at heq
    rw [heq]
    have hfirst : f (N - 1) * (∑ i ∈ Finset.range N, (a i - b i)) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos (hf _ hlast)
      rw [Finset.sum_sub_distrib, sub_nonpos]
      exact hprefix N le_rfl
    have hrest : 0 ≤ ∑ i ∈ Finset.range (N - 1),
        (f (i + 1) - f i) * ∑ j ∈ Finset.range (i + 1), (a j - b j) := by
      apply Finset.sum_nonneg
      intro i hi
      have hiN : i + 1 < N := by have := Finset.mem_range.mp hi; omega
      apply mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hmono i hiN))
      rw [Finset.sum_sub_distrib, sub_nonpos]
      exact hprefix (i + 1) (by omega)
    linarith
  simp only [mul_sub, Finset.sum_sub_distrib, sub_nonpos] at hsum
  exact hsum

/-- If `#{i < k : p (L + i)} ≤ kα + B` for every `k ≤ N`, then
`∑_{i<N, p (L+i)} 1/(L+i) ≤ α ∑_{i<N} 1/(L+i) + B/L`. -/
theorem reciprocal_sum_le_of_prefix_count_le (p : ℕ → Prop) [DecidablePred p]
    (L N : ℕ) (hL : 0 < L) (α B : ℝ) (hB : 0 ≤ B)
    (hcount : ∀ k ≤ N,
      (∑ i ∈ Finset.range k, if p (L + i) then (1 : ℝ) else 0) ≤ (k : ℝ) * α + B) :
    (∑ i ∈ Finset.range N, if p (L + i) then (1 : ℝ) / (L + i : ℕ) else 0) ≤
      α * (∑ i ∈ Finset.range N, (1 : ℝ) / (L + i : ℕ)) + B / (L : ℝ) := by
  classical
  let a : ℕ → ℝ := fun i => if p (L + i) then 1 else 0
  let b : ℕ → ℝ := fun i => α + if i = 0 then B else 0
  let f : ℕ → ℝ := fun i => 1 / ((L + i : ℕ) : ℝ)
  have hprefix : ∀ k ≤ N, ∑ i ∈ Finset.range k, a i ≤ ∑ i ∈ Finset.range k, b i := by
    intro k hk
    by_cases hk0 : k = 0
    · simp [hk0]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      simpa [a, b, Finset.sum_add_distrib, Finset.mem_range.mpr hkpos] using hcount k hk
  have hf : ∀ i < N, 0 ≤ f i := by intro i hi; dsimp [f]; positivity
  have hmono : ∀ i, i + 1 < N → f (i + 1) ≤ f i := by
    intro i hi
    apply one_div_le_one_div_of_le
    · exact_mod_cast (show 0 < L + i by omega)
    · exact_mod_cast (show L + i ≤ L + (i + 1) by omega)
  have h := sum_mul_le_of_prefix_sum_le a b f N hprefix hf hmono
  have hleft : (∑ i ∈ Finset.range N, f i * a i) =
      ∑ i ∈ Finset.range N, if p (L + i) then (1 : ℝ) / (L + i : ℕ) else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [f, a]
    split_ifs <;> ring
  rw [hleft] at h
  calc
    _ ≤ ∑ i ∈ Finset.range N, f i * b i := h
    _ ≤ α * (∑ i ∈ Finset.range N, (1 : ℝ) / (L + i : ℕ)) + B / (L : ℝ) := by
      simp only [b, mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul]
      have hterm : (∑ i ∈ Finset.range N, f i * if i = 0 then B else 0) ≤ B / (L : ℝ) := by
        by_cases hN : N = 0
        · simp [hN, div_nonneg hB (Nat.cast_nonneg L)]
        · simp [Finset.mem_range.mpr (Nat.pos_of_ne_zero hN), f]
          ring_nf
          exact le_rfl
      dsimp [f] at hterm ⊢
      nlinarith only [hterm]

/-- If `#{L ≤ n < V : p n} ≤ (V - L)α + B` for all `L ≤ V ≤ U`, then
`∑_{L ≤ n < U, p n} 1/n ≤ α ∑_{L ≤ n < U} 1/n + B/L`. -/
theorem reciprocal_Ico_le_of_count_le (p : ℕ → Prop) [DecidablePred p]
    (L U : ℕ) (hL : 0 < L) (hLU : L ≤ U) (α B : ℝ) (hB : 0 ≤ B)
    (hcount : ∀ V, L ≤ V → V ≤ U →
      (((Finset.Ico L V).filter p).card : ℝ) ≤ ((V : ℝ) - (L : ℝ)) * α + B) :
    (∑ n ∈ (Finset.Ico L U).filter p, (1 : ℝ) / (n : ℝ)) ≤
      α * (∑ n ∈ Finset.Ico L U, (1 : ℝ) / (n : ℝ)) + B / (L : ℝ) := by
  classical
  have hshift (g : ℕ → ℝ) (k : ℕ) :
      (∑ i ∈ Finset.range k, g (L + i)) = ∑ n ∈ Finset.Ico L (L + k), g n := by
    simpa only [Nat.zero_add, Nat.add_comm k L, Nat.Ico_zero_eq_range] using
      Finset.sum_Ico_add g 0 k L
  have hprefix : ∀ k ≤ U - L,
      (∑ i ∈ Finset.range k, if p (L + i) then (1 : ℝ) else 0) ≤ (k : ℝ) * α + B := by
    intro k hk
    rw [hshift (fun n => if p n then (1 : ℝ) else 0)]
    rw [← Finset.sum_filter]
    have h := hcount (L + k) (by omega) (by omega)
    simpa using h
  have h := reciprocal_sum_le_of_prefix_count_le p L (U - L) hL α B hB hprefix
  rw [hshift (fun n => if p n then (1 : ℝ) / (n : ℝ) else 0),
    hshift (fun n => (1 : ℝ) / (n : ℝ)), Nat.add_sub_of_le hLU,
    ← Finset.sum_filter] at h
  exact h

theorem sum_Icc_reciprocal_le_log (L U : ℕ) (hL : 0 < L) (hLU : L ≤ U) :
    (∑ n ∈ Finset.Icc L U, (1 : ℝ) / (n : ℝ)) ≤
      1 / (L : ℝ) + Real.log ((U : ℝ) / (L : ℝ)) := by
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  induction U, hLU using Nat.le_induction with
  | base => simp [ne_of_gt hLR]
  | succ U hLU ih =>
    have hUR : 0 < (U : ℝ) := by exact_mod_cast (lt_of_lt_of_le hL hLU)
    have hU1R : 0 < ((U + 1 : ℕ) : ℝ) := by positivity
    have hincr : (1 : ℝ) / ((U + 1 : ℕ) : ℝ) ≤
        Real.log (((U + 1 : ℕ) : ℝ) / (U : ℝ)) := by
      have h := Real.one_sub_inv_le_log_of_pos (div_pos hU1R hUR)
      have heq : 1 - (((U + 1 : ℕ) : ℝ) / (U : ℝ))⁻¹ =
          1 / ((U + 1 : ℕ) : ℝ) := by
        push_cast
        field_simp
        ring
      rwa [heq] at h
    rw [Finset.sum_Icc_succ_top (hLU.trans (Nat.le_succ U))]
    have hlog : Real.log ((U : ℝ) / (L : ℝ)) +
        Real.log (((U + 1 : ℕ) : ℝ) / (U : ℝ)) =
        Real.log (((U + 1 : ℕ) : ℝ) / (L : ℝ)) := by
      rw [← Real.log_mul (ne_of_gt (div_pos hUR hLR)) (ne_of_gt (div_pos hU1R hUR))]
      congr 1
      field_simp
    linarith

theorem sum_Ico_reciprocal_le_log (L U : ℕ) (hL : 0 < L) (hLU : L ≤ U) :
    (∑ n ∈ Finset.Ico L U, (1 : ℝ) / (n : ℝ)) ≤
      1 / (L : ℝ) + Real.log ((U : ℝ) / (L : ℝ)) := by
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Icc_self)
    (fun n _ _ => by positivity)).trans (sum_Icc_reciprocal_le_log L U hL hLU)

end ErdosStraus.SieveEstimates

/-! ## Summation by parts on `(m, n]` -/

namespace ErdosStraus.PrimeEstimates

open scoped BigOperators
open Finset

/-- Summation by parts on `(m, n]` with the partial sums `∑_{m<j≤k} c_j`. -/
theorem sum_Ioc_mul_eq_partial (c u : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    (∑ k ∈ Ioc m n, u k * c k) =
      u n * (∑ k ∈ Ioc m n, c k) +
        ∑ k ∈ Ico (m + 1) n,
          (u k - u (k + 1)) * (∑ j ∈ Ioc m k, c j) := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
      rcases eq_or_lt_of_le hmn with rfl | hmn'
      · simp
      rw [Finset.sum_Ioc_succ_top hmn, Finset.sum_Ioc_succ_top hmn,
        Finset.sum_Ico_succ_top (by omega), ih]
      ring

theorem sum_Ico_weight_differences (u : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    (∑ k ∈ Ico m n, (u k - u (k + 1))) = u m - u n := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih => rw [Finset.sum_Ico_succ_top hmn, ih]; ring

theorem sum_Ioc_eq_prefix_sub (c : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    (∑ j ∈ Ioc m n, c j) =
      (∑ j ∈ Icc 0 n, c j) - (∑ j ∈ Icc 0 m, c j) := by
  have hsplit : (∑ j ∈ Icc 0 n, c j) =
      (∑ j ∈ Icc 0 m, c j) + (∑ j ∈ Ioc m n, c j) := by
    rw [← Finset.add_sum_Ioc_eq_sum_Icc (f := c) (Nat.zero_le n),
      ← Finset.add_sum_Ioc_eq_sum_Icc (f := c) (Nat.zero_le m),
      ← Finset.sum_Ioc_consecutive c (Nat.zero_le m) hmn]
    ring
  linarith

/-- Summation by parts on `(m, n]` with the prefix sums `∑_{j≤k} c_j`. -/
theorem sum_Ioc_mul_eq_global_partial (c u : ℕ → ℝ) {m n : ℕ} (hmn : m < n) :
    (∑ k ∈ Ioc m n, u k * c k) =
      u n * (∑ k ∈ Icc 0 n, c k) -
        u (m + 1) * (∑ k ∈ Icc 0 m, c k) +
          ∑ k ∈ Ico (m + 1) n,
            (u k - u (k + 1)) * (∑ j ∈ Icc 0 k, c j) := by
  rw [sum_Ioc_mul_eq_partial c u hmn.le, sum_Ioc_eq_prefix_sub c hmn.le]
  have hlocal : (∑ k ∈ Ico (m + 1) n,
      (u k - u (k + 1)) * ∑ j ∈ Ioc m k, c j) =
      ∑ k ∈ Ico (m + 1) n,
        (u k - u (k + 1)) *
          ((∑ j ∈ Icc 0 k, c j) - ∑ j ∈ Icc 0 m, c j) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [sum_Ioc_eq_prefix_sub c (by have := (Finset.mem_Ico.mp hk).1; omega)]
  rw [hlocal]
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [sum_Ico_weight_differences u (by omega)]
  ring

/-- If `u` is nonnegative and decreasing on `(m, n]` and `|∑_{j≤k} c_j| ≤ E_k` for
`m ≤ k ≤ n`, then `|∑_{m<k≤n} u_k c_k|` is at most
`u_n E_n + u_{m+1} E_m + ∑_{m<k<n} (u_k - u_{k+1}) E_k`. -/
theorem abs_sum_Ioc_mul_le_of_global (c u E : ℕ → ℝ) {m n : ℕ}
    (hmn : m < n) (hun : 0 ≤ u n) (hum : 0 ≤ u (m + 1))
    (hdec : ∀ k ∈ Ico (m + 1) n, u (k + 1) ≤ u k)
    (hprefix : ∀ k ∈ Icc m n, |∑ j ∈ Icc 0 k, c j| ≤ E k) :
    |∑ k ∈ Ioc m n, u k * c k| ≤
      u n * E n + u (m + 1) * E m +
        ∑ k ∈ Ico (m + 1) n, (u k - u (k + 1)) * E k := by
  rw [sum_Ioc_mul_eq_global_partial c u hmn]
  calc
    |u n * (∑ k ∈ Icc 0 n, c k) -
        u (m + 1) * (∑ k ∈ Icc 0 m, c k) +
          ∑ k ∈ Ico (m + 1) n,
            (u k - u (k + 1)) * (∑ j ∈ Icc 0 k, c j)| ≤
      (|u n * (∑ k ∈ Icc 0 n, c k)| +
        |u (m + 1) * (∑ k ∈ Icc 0 m, c k)|) +
          |∑ k ∈ Ico (m + 1) n,
            (u k - u (k + 1)) * (∑ j ∈ Icc 0 k, c j)| :=
      (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ _ := by
      apply add_le_add
      · apply add_le_add
        · rw [abs_mul, abs_of_nonneg hun]
          exact mul_le_mul_of_nonneg_left
            (hprefix n (Finset.mem_Icc.mpr ⟨hmn.le, le_rfl⟩)) hun
        · rw [abs_mul, abs_of_nonneg hum]
          exact mul_le_mul_of_nonneg_left
            (hprefix m (Finset.mem_Icc.mpr ⟨le_rfl, hmn.le⟩)) hum
      · apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        have hd : 0 ≤ u k - u (k + 1) := sub_nonneg.mpr (hdec k hk)
        rw [abs_mul, abs_of_nonneg hd]
        exact mul_le_mul_of_nonneg_left
          (hprefix k (Finset.mem_Icc.mpr
            ⟨by have := (Finset.mem_Ico.mp hk).1; omega,
              (Finset.mem_Ico.mp hk).2.le⟩)) hd

/-- With `E_k = k` the bound of `abs_sum_Ioc_mul_le_of_global` telescopes:
`n u_n + m u_{m+1} + ∑_{m < k < n} k (u_k - u_{k+1}) = 2m u_{m+1} + ∑_{m < k ≤ n} u_k`. -/
theorem global_partial_linear_coefficient (u : ℕ → ℝ) {m n : ℕ} (hmn : m < n) :
    (n : ℝ) * u n + (m : ℝ) * u (m + 1) +
      (∑ k ∈ Ico (m + 1) n, (k : ℝ) * (u k - u (k + 1))) =
        2 * m * u (m + 1) + ∑ k ∈ Ioc m n, u k := by
  have hstart : m + 1 ≤ n := hmn
  clear hmn
  induction n, hstart using Nat.le_induction with
  | base =>
      simp only [Ico_self, sum_empty, Nat.Ioc_succ_singleton, sum_singleton,
        Nat.cast_add, Nat.cast_one]
      ring
  | succ n hstart ih =>
      rw [Finset.sum_Ico_succ_top hstart,
        Finset.sum_Ioc_succ_top (by omega)]
      push_cast
      nlinarith [ih]

/-- If `u` is nonnegative and decreasing on `(m, n]` and every partial sum
`∑_{m < j ≤ k} c_j` has absolute value at most `E`, then
`|∑_{m < k ≤ n} u_k c_k| ≤ u_{m+1} E`. -/
theorem abs_sum_Ioc_mul_le_of_partial (c u : ℕ → ℝ) {m n : ℕ} {E : ℝ}
    (hmn : m < n) (hu : 0 ≤ u n)
    (hdec : ∀ k ∈ Ico (m + 1) n, u (k + 1) ≤ u k)
    (hpartial : ∀ k ∈ Ioc m n, |∑ j ∈ Ioc m k, c j| ≤ E) :
    |∑ k ∈ Ioc m n, u k * c k| ≤ u (m + 1) * E := by
  rw [sum_Ioc_mul_eq_partial c u hmn.le]
  calc
    |u n * (∑ k ∈ Ioc m n, c k) +
        ∑ k ∈ Ico (m + 1) n,
          (u k - u (k + 1)) * (∑ j ∈ Ioc m k, c j)| ≤
        |u n * (∑ k ∈ Ioc m n, c k)| +
          |∑ k ∈ Ico (m + 1) n,
            (u k - u (k + 1)) * (∑ j ∈ Ioc m k, c j)| := abs_add_le _ _
    _ ≤ u n * E +
        ∑ k ∈ Ico (m + 1) n, (u k - u (k + 1)) * E := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg hu]
        exact mul_le_mul_of_nonneg_left
          (hpartial n (Finset.mem_Ioc.mpr ⟨hmn, le_rfl⟩)) hu
      · apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        have hd : 0 ≤ u k - u (k + 1) := sub_nonneg.mpr (hdec k hk)
        rw [abs_mul, abs_of_nonneg hd]
        exact mul_le_mul_of_nonneg_left
          (hpartial k (Finset.mem_Ioc.mpr
            ⟨by have := (Finset.mem_Ico.mp hk).1; omega,
              (Finset.mem_Ico.mp hk).2.le⟩)) hd
    _ = u (m + 1) * E := by
      rw [← Finset.sum_mul, sum_Ico_weight_differences u (by omega)]
      ring

theorem abs_sum_Ioc_le_two_of_prefix (c : ℕ → ℝ) {m n : ℕ} {E : ℝ}
    (hmn : m ≤ n)
    (hprefix : ∀ k ∈ Icc m n, |∑ j ∈ Icc 0 k, c j| ≤ E) :
    |∑ j ∈ Ioc m n, c j| ≤ 2 * E := by
  rw [sum_Ioc_eq_prefix_sub c hmn]
  exact (abs_sub _ _).trans (by
    have hn := hprefix n (Finset.mem_Icc.mpr ⟨hmn, le_rfl⟩)
    have hm := hprefix m (Finset.mem_Icc.mpr ⟨le_rfl, hmn⟩)
    linarith)

end ErdosStraus.PrimeEstimates
