import ErdosStraus.BombieriVinogradov.Reduction.ConductorSplit

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

/-!
# The Type I sums in Vaughan's identity

For a primitive character `χ` mod `q > 1`, every sum of `χ` over an interval has absolute
value at most `2q`, and partial summation gives
`|∑_{m ≤ M} log(m) χ(m)| ≤ 4 q log(M + 1)`. Applying these bounds to the Type I part of
Vaughan's identity, written as short sums over `d ≤ u` and `e ≤ v` of character sums over
`m`, gives
`max_{y ≤ N} |∑_{n ≤ y} TypeI(n; u, v) χ(n)| ≤ 4 u q log(N + 1) + 2 u v q log(v + 1)`.
Averaging over moduli `2 ≤ q ≤ Q` then bounds the Type I mean by
`6 Q² (u log(N + 1) + u v log(v + 1))`.
-/

/-! ## Sums of a primitive character -/

namespace BombieriVinogradov

open Finset
open scoped BigOperators
noncomputable section

theorem primitiveCharacter_ne_one {q : ℕ} (hq : 1 < q)
    (χ : PrimitiveCharacter q) : χ.1 ≠ 1 := by
  let : NeZero q := ⟨by omega⟩
  intro hχ
  have hc : χ.1.conductor = 1 :=
    (DirichletCharacter.eq_one_iff_conductor_eq_one).mp hχ
  have hp : χ.1.conductor = q := χ.2
  omega

theorem primitiveCharacter_sum_zmod_eq_zero {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ : PrimitiveCharacter q) :
    ∑ a : ZMod q, χ.1 a = 0 := by
  exact MulChar.sum_eq_zero_of_ne_one (primitiveCharacter_ne_one hq χ)

theorem primitiveCharacter_sum_range_period_eq_zero {q : ℕ} (hq : 1 < q)
    (χ : PrimitiveCharacter q) :
    ∑ n ∈ range q, χ.1 (n : ZMod q) = 0 := by
  let : NeZero q := ⟨by omega⟩
  rw [← sum_zmod_eq_sum_range]
  exact primitiveCharacter_sum_zmod_eq_zero hq χ

private theorem sum_range_mul_period_eq_zero {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) (q : ℕ) (hperiod : ∀ k n, f (k * q + n) = f n)
    (hzero : ∑ n ∈ range q, f n = 0) :
    ∀ k : ℕ, ∑ n ∈ range (k * q), f n = 0 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, sum_range_add, ih, zero_add]
      rw [← hzero]
      exact Finset.sum_congr rfl fun n _ => hperiod k n

/-- `|∑_{n < M} χ(n)| ≤ q`, since the sum of `χ` over each full period vanishes. -/
theorem primitiveCharacter_prefix_norm_le {q M : ℕ} (hq : 1 < q)
    (χ : PrimitiveCharacter q) :
    ‖∑ n ∈ range M, χ.1 (n : ZMod q)‖ ≤ q := by
  have hperiod : ∀ k n : ℕ,
      χ.1 ((k * q + n : ℕ) : ZMod q) = χ.1 (n : ZMod q) := by
    intro k n
    congr 1
    simp
  have hblocks : ∀ k : ℕ,
      ∑ n ∈ range (k * q), χ.1 (n : ZMod q) = 0 :=
    sum_range_mul_period_eq_zero (fun n : ℕ => χ.1 (n : ZMod q)) q hperiod
      (primitiveCharacter_sum_range_period_eq_zero hq χ)
  rw [← Nat.div_add_mod M q, Nat.mul_comm q (M / q), sum_range_add,
    hblocks, zero_add]
  calc
    ‖∑ n ∈ range (M % q), χ.1 (((M / q) * q + n : ℕ) : ZMod q)‖
        ≤ ∑ n ∈ range (M % q), ‖χ.1 (((M / q) * q + n : ℕ) : ZMod q)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ range (M % q), (1 : ℝ) := by
      exact sum_le_sum fun n _ => DirichletCharacter.norm_le_one χ.1 _
    _ = (M % q : ℕ) := by simp
    _ ≤ q := by
      exact_mod_cast Nat.le_of_lt (Nat.mod_lt M (by omega))

/-- `|∑_{A ≤ n < B} χ(n)| ≤ 2q`, as a difference of two prefix sums. -/
theorem primitiveCharacter_interval_norm_le_two_mul {q A B : ℕ} (hq : 1 < q)
    (χ : PrimitiveCharacter q) :
    ‖∑ n ∈ Ico A B, χ.1 (n : ZMod q)‖ ≤ 2 * q := by
  by_cases hAB : A ≤ B
  · rw [sum_Ico_eq_sub _ hAB]
    calc
      ‖(∑ n ∈ range B, χ.1 (n : ZMod q)) -
          ∑ n ∈ range A, χ.1 (n : ZMod q)‖
          ≤ ‖∑ n ∈ range B, χ.1 (n : ZMod q)‖ +
              ‖∑ n ∈ range A, χ.1 (n : ZMod q)‖ := norm_sub_le _ _
      _ ≤ q + q := add_le_add
        (primitiveCharacter_prefix_norm_le hq χ)
        (primitiveCharacter_prefix_norm_le hq χ)
      _ = 2 * q := by ring
  · rw [Finset.Ico_eq_empty (by omega)]
    simp

private theorem finite_summation_by_parts (f : ℕ → ℂ) (w : ℕ → ℂ) (M : ℕ) :
    (∑ k ∈ range M, w k * f k) =
      w M * (∑ k ∈ range M, f k) +
        ∑ k ∈ range M,
          (w k - w (k + 1)) * (∑ j ∈ range (k + 1), f j) := by
  induction M with
  | zero => simp
  | succ M ih =>
      simp only [sum_range_succ, ih]
      ring

private theorem shifted_prefix_eq_Ico (f : ℕ → ℂ) (N : ℕ) :
    (∑ k ∈ range N, f (k + 1)) = ∑ m ∈ Ico 1 (N + 1), f m := by
  simpa [Nat.add_comm] using (Finset.sum_Ico_add f 0 N 1)

/-- Partial summation gives `|∑_{k < M} log(k + 1) χ(k + 1)| ≤ 4 q log(M + 1)`. The
constant `4` comes from bounding the shifted prefix sums by `2q`. -/
theorem primitiveCharacter_logWeight_range_norm_le {q M : ℕ} (hq : 1 < q)
    (χ : PrimitiveCharacter q) :
    ‖∑ k ∈ range M,
        (Real.log (k + 1) : ℂ) * χ.1 ((k + 1 : ℕ) : ZMod q)‖
      ≤ 4 * q * Real.log (M + 1) := by
  let f : ℕ → ℂ := fun k => χ.1 ((k + 1 : ℕ) : ZMod q)
  let w : ℕ → ℂ := fun k => (Real.log (k + 1) : ℂ)
  let S : ℕ → ℂ := fun n => ∑ k ∈ range n, f k
  have hS (n : ℕ) : ‖S n‖ ≤ 2 * q := by
    change ‖∑ k ∈ range n, χ.1 ((k + 1 : ℕ) : ZMod q)‖ ≤ 2 * q
    rw [shifted_prefix_eq_Ico (fun m : ℕ => χ.1 (m : ZMod q)) n]
    exact primitiveCharacter_interval_norm_le_two_mul hq χ
  have hwmono (k : ℕ) : Real.log (k + 1) ≤ Real.log (k + 2) := by
    apply Real.strictMonoOn_log.monotoneOn
    · change 0 < (k : ℝ) + 1
      positivity
    · change 0 < (k : ℝ) + 2
      positivity
    · exact_mod_cast (by omega : k + 1 ≤ k + 2)
  have htel (N : ℕ) :
      (∑ k ∈ range N,
          (Real.log (k + 2) - Real.log (k + 1))) = Real.log (N + 1) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      Finset.sum_range_sub (fun k : ℕ => Real.log ((k : ℝ) + 1)) N
  have hlognonneg (n : ℕ) : 0 ≤ Real.log ((n : ℝ) + 1) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
    exact Real.log_natCast_nonneg (n + 1)
  rw [show (∑ k ∈ range M,
      (Real.log (k + 1) : ℂ) * χ.1 ((k + 1 : ℕ) : ZMod q)) =
      ∑ k ∈ range M, w k * f k by rfl,
    finite_summation_by_parts f w M]
  calc
    ‖w M * S M + ∑ k ∈ range M, (w k - w (k + 1)) * S (k + 1)‖
        ≤ ‖w M * S M‖ +
            ‖∑ k ∈ range M, (w k - w (k + 1)) * S (k + 1)‖ :=
      norm_add_le _ _
    _ ≤ Real.log (M + 1) * (2 * q) +
          ∑ k ∈ range M,
            (Real.log (k + 2) - Real.log (k + 1)) * (2 * q) := by
      apply add_le_add
      · rw [norm_mul, show ‖w M‖ = Real.log (M + 1) by
          simp [w, abs_of_nonneg (hlognonneg M)]]
        exact mul_le_mul_of_nonneg_left (hS M) (hlognonneg M)
      · refine le_trans (norm_sum_le _ _) ?_
        apply sum_le_sum
        intro k hk
        rw [norm_mul]
        have habs : ‖w k - w (k + 1)‖ =
            Real.log (k + 2) - Real.log (k + 1) := by
          have hwk1 : w (k + 1) = (Real.log ((k : ℝ) + 2) : ℂ) := by
            simp only [w, Nat.cast_add, Nat.cast_one]
            congr 2; ring
          rw [show w k = (Real.log ((k : ℝ) + 1) : ℂ) by rfl, hwk1,
            ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          rw [abs_of_nonpos (sub_nonpos.mpr (hwmono k))]
          ring
        rw [habs]
        exact mul_le_mul_of_nonneg_left (hS (k + 1)) (sub_nonneg.mpr (hwmono k))
    _ = Real.log (M + 1) * (2 * q) + Real.log (M + 1) * (2 * q) := by
      rw [← sum_mul, htel]
    _ = 4 * q * Real.log (M + 1) := by ring

/-- `|∑_{1 ≤ m ≤ M} log(m) χ(m)| ≤ 4 q log(M + 1)` for `χ` primitive mod `q > 1`. -/
theorem primitiveCharacter_logWeight_Icc_norm_le {q M : ℕ} (hq : 1 < q)
    (χ : PrimitiveCharacter q) :
    ‖∑ m ∈ Icc 1 M, (Real.log m : ℂ) * χ.1 (m : ZMod q)‖
      ≤ 4 * q * Real.log (M + 1) := by
  have hsets : Icc 1 M = Ico 1 (M + 1) := by
    simpa using (Finset.Ico_succ_right_eq_Icc (1 : ℕ) M).symm
  rw [hsets, ← shifted_prefix_eq_Ico
    (fun m : ℕ => (Real.log m : ℂ) * χ.1 (m : ZMod q)) M]
  simpa only [Nat.cast_add, Nat.cast_one] using
    primitiveCharacter_logWeight_range_norm_le hq χ

end

end BombieriVinogradov

/-!
## Type I sums

The Type I prefix sum is the difference of a sum over `d ≤ u` and a sum over pairs
`d ≤ u`, `e ≤ v`. Each is bounded by Cauchy–Schwarz over the short variables.
-/

namespace BombieriVinogradov

open Classical Finset
open scoped BigOperators ArithmeticFunction ComplexConjugate
noncomputable section

private lemma moebius_complex_norm_le_one (d : ℕ) :
    ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> simp [h]

private lemma shortRange_card_le (y u : ℕ) :
    (vaughanTypeIShortRange y u).card ≤ u := by
  calc
    (vaughanTypeIShortRange y u).card ≤ (Finset.Icc 1 u).card := by
      apply Finset.card_le_card
      intro d hd
      exact Finset.mem_Icc.mpr
        ⟨(mem_vaughanTypeIShortRange.mp hd).1,
          (mem_vaughanTypeIShortRange.mp hd).2.2⟩
    _ ≤ u := by simp [Nat.card_Icc]

private lemma log_div_succ_le_log_succ {y N d : ℕ} (hy : y ≤ N) :
    Real.log (y / d + 1 : ℕ) ≤ Real.log (N + 1 : ℕ) := by
  apply Real.strictMonoOn_log.monotoneOn
  · show (0 : ℝ) < (y / d + 1 : ℕ)
    positivity
  · show (0 : ℝ) < (N + 1 : ℕ)
    positivity
  · exact_mod_cast Nat.succ_le_succ ((Nat.div_le_self y d).trans hy)

private lemma vonMangoldt_le_log_succ {e v : ℕ} (he : 0 < e) (hev : e ≤ v) :
    ArithmeticFunction.vonMangoldt e ≤ Real.log (v + 1 : ℕ) := by
  have hmem : e ∈ e.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, he.ne'⟩
  calc
    ArithmeticFunction.vonMangoldt e ≤
        ∑ r ∈ e.divisors, ArithmeticFunction.vonMangoldt r := by
      exact Finset.single_le_sum
        (s := e.divisors) (f := fun r => ArithmeticFunction.vonMangoldt r)
        (fun r _ => ArithmeticFunction.vonMangoldt_nonneg) hmem
    _ = Real.log (e : ℝ) := ArithmeticFunction.vonMangoldt_sum
    _ ≤ Real.log (v + 1 : ℕ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · show (0 : ℝ) < (e : ℕ)
        positivity
      · show (0 : ℝ) < (v + 1 : ℕ)
        positivity
      · exact_mod_cast hev.trans (Nat.le_succ v)

/-- For `y ≤ N`, `|∑_{d ≤ min(y, u)} μ(d) χ(d) ∑_{m ≤ y/d} log(m) χ(m)|` is at most
`4 u q log(N + 1)`. -/
theorem norm_vaughanTypeIFirstLong_le_elementaryCauchy
    {N y u q : ℕ} (hy : y ≤ N) (hq : 1 < q)
    (χ : PrimitiveCharacter q) :
    ‖vaughanTypeIFirstLong (fun _ => 1) y u q χ‖ ≤
      4 * u * q * Real.log (N + 1 : ℕ) := by
  let D := vaughanTypeIShortRange y u
  let A : ℕ → ℂ := fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ.1 (d : ZMod q)
  let B : ℕ → ℂ := fun d =>
    ∑ m ∈ Finset.Icc 1 (y / d),
      (Real.log (m : ℝ) : ℂ) * χ.1 (m : ZMod q)
  have hA : (∑ d ∈ D, ‖A d‖ ^ 2) ≤ (u : ℝ) := by
    calc
      _ ≤ ∑ _d ∈ D, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        apply pow_le_one₀ (norm_nonneg _)
        simp only [A, norm_mul]
        calc
          ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ *
              ‖χ.1 (d : ZMod q)‖ ≤ 1 * 1 :=
            mul_le_mul (moebius_complex_norm_le_one d) (χ.1.norm_le_one _)
              (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      _ = (D.card : ℕ) := by simp
      _ ≤ (u : ℝ) := by exact_mod_cast shortRange_card_le y u
  let L := Real.log (N + 1 : ℕ)
  have hBpoint (d : ℕ) : ‖B d‖ ≤ 4 * q * L := by
    calc
      ‖B d‖ ≤ 4 * q * Real.log (y / d + 1 : ℕ) := by
        simpa [B, Nat.cast_add, Nat.cast_one] using
          (primitiveCharacter_logWeight_Icc_norm_le (M := y / d) hq χ)
      _ ≤ 4 * q * L := by
        apply mul_le_mul_of_nonneg_left (log_div_succ_le_log_succ hy)
        positivity
  have hB : (∑ d ∈ D, ‖B d‖ ^ 2) ≤ (u : ℝ) * (4 * q * L) ^ 2 := by
    calc
      _ ≤ ∑ _d ∈ D, (4 * q * L) ^ 2 := by
        apply Finset.sum_le_sum
        intro d hd
        exact pow_le_pow_left₀ (norm_nonneg _) (hBpoint d) 2
      _ = (D.card : ℕ) * (4 * q * L) ^ 2 := by simp
      _ ≤ (u : ℝ) * (4 * q * L) ^ 2 := by
        gcongr
        exact_mod_cast shortRange_card_le y u
  have hc := finiteComplexCauchy D A B
  have hid : vaughanTypeIFirstLong (fun _ => 1) y u q χ =
      ∑ d ∈ D, A d * B d := by
    unfold vaughanTypeIFirstLong
    simp only [one_mul, D, A, B]
  rw [← hid] at hc
  have hsquare : ‖vaughanTypeIFirstLong (fun _ => 1) y u q χ‖ ^ 2 ≤
      (4 * u * q * L) ^ 2 := by
    calc
      _ ≤ (∑ d ∈ D, ‖A d‖ ^ 2) * (∑ d ∈ D, ‖B d‖ ^ 2) := hc
      _ ≤ (u : ℝ) * ((u : ℝ) * (4 * q * L) ^ 2) := by gcongr
      _ = (4 * u * q * L) ^ 2 := by ring
  have ht : 0 ≤ 4 * (u : ℝ) * q * L := by
    dsimp [L]
    positivity
  exact (sq_le_sq₀ (norm_nonneg _) ht).mp hsquare

/-- `|∑_{d ≤ min(y, u)} ∑_{e ≤ min(y, v)} μ(d) Λ(e) χ(d) χ(e) ∑_{m ≤ y/(d e)} χ(m)|`
is at most `2 u v q log(v + 1)`. -/
theorem norm_vaughanTypeIMiddleLong_le_elementaryCauchy
    {N y u v q : ℕ} (_hy : y ≤ N) (hq : 1 < q)
    (χ : PrimitiveCharacter q) :
    ‖vaughanTypeIMiddleLong (fun _ => 1) y u v q χ‖ ≤
      2 * u * v * q * Real.log (v + 1 : ℕ) := by
  let D := vaughanTypeIShortRange y u
  let E := vaughanTypeIShortRange y v
  let R := D ×ˢ E
  have hcard : R.card ≤ u * v := by
    rw [show R.card = D.card * E.card by simp [R]]
    exact Nat.mul_le_mul (shortRange_card_le y u) (shortRange_card_le y v)
  let A : ℕ × ℕ → ℂ := fun de =>
    ((((ArithmeticFunction.moebius de.1 : ℤ) : ℂ) *
      (ArithmeticFunction.vonMangoldt de.2 : ℂ)) *
      χ.1 (de.1 : ZMod q) * χ.1 (de.2 : ZMod q))
  let B : ℕ × ℕ → ℂ := fun de =>
    ∑ m ∈ Finset.Icc 1 (y / (de.1 * de.2)), χ.1 (m : ZMod q)
  let L := Real.log (v + 1 : ℕ)
  have hApoint (de : ℕ × ℕ) (hde : de ∈ R) : ‖A de‖ ≤ L := by
    have he := mem_vaughanTypeIShortRange.mp (Finset.mem_product.mp hde).2
    simp only [A, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := de.2)
    rw [abs_of_nonneg hΛ0]
    calc
      _ ≤ 1 * L * 1 * 1 := by
        gcongr
        · exact moebius_complex_norm_le_one de.1
        · exact vonMangoldt_le_log_succ he.1 he.2.2
        · exact χ.1.norm_le_one _
        · exact χ.1.norm_le_one _
      _ = L := by ring
  have hA : (∑ de ∈ R, ‖A de‖ ^ 2) ≤
      ((u : ℝ) * v) * L ^ 2 := by
    calc
      _ ≤ ∑ _de ∈ R, L ^ 2 := by
        apply Finset.sum_le_sum
        intro de hde
        exact pow_le_pow_left₀ (norm_nonneg _) (hApoint de hde) 2
      _ = (R.card : ℕ) * L ^ 2 := by simp
      _ ≤ ((u : ℝ) * v) * L ^ 2 := by
        gcongr
        exact_mod_cast hcard
  have hBpoint (de : ℕ × ℕ) : ‖B de‖ ≤ 2 * q := by
    have hset : Finset.Ico 1 (y / (de.1 * de.2) + 1) =
        Finset.Icc 1 (y / (de.1 * de.2)) := by ext m; simp
    change ‖∑ m ∈ Finset.Icc 1 (y / (de.1 * de.2)),
      χ.1 (m : ZMod q)‖ ≤ 2 * q
    rw [← hset]
    exact primitiveCharacter_interval_norm_le_two_mul (A := 1)
      (B := y / (de.1 * de.2) + 1) hq χ
  have hB : (∑ de ∈ R, ‖B de‖ ^ 2) ≤
      ((u : ℝ) * v) * (2 * (q : ℝ)) ^ 2 := by
    calc
      _ ≤ ∑ _de ∈ R, (2 * (q : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro de hde
        exact pow_le_pow_left₀ (norm_nonneg _) (hBpoint de) 2
      _ = (R.card : ℕ) * (2 * (q : ℝ)) ^ 2 := by simp
      _ ≤ ((u : ℝ) * v) * (2 * (q : ℝ)) ^ 2 := by
        gcongr
        exact_mod_cast hcard
  have hc := finiteComplexCauchy R A B
  have hid : vaughanTypeIMiddleLong (fun _ => 1) y u v q χ =
      ∑ de ∈ R, A de * B de := by
    unfold vaughanTypeIMiddleLong
    simp only [one_mul, R, D, E, A, B, Finset.sum_product]
  rw [← hid] at hc
  have hsquare : ‖vaughanTypeIMiddleLong (fun _ => 1) y u v q χ‖ ^ 2 ≤
      (2 * u * v * q * L) ^ 2 := by
    calc
      _ ≤ (∑ de ∈ R, ‖A de‖ ^ 2) * (∑ de ∈ R, ‖B de‖ ^ 2) := hc
      _ ≤ (((u : ℝ) * v) * L ^ 2) * (((u : ℝ) * v) * (2 * q) ^ 2) := by gcongr
      _ = (2 * u * v * q * L) ^ 2 := by ring
  have ht : 0 ≤ 2 * (u : ℝ) * v * q * L := by
    dsimp [L]
    positivity
  exact (sq_le_sq₀ (norm_nonneg _) ht).mp hsquare

/-- For `χ` primitive mod `q > 1`,
`max_{y ≤ N} |∑_{n ≤ y} TypeI(n; u, v) χ(n)| ≤ 4 u q log(N + 1) + 2 u v q log(v + 1)`. -/
theorem primitivePrefixAmplitude_vaughanTypeI_le_elementaryCauchy
    (N u v q : ℕ) (hq : 1 < q) (χ : PrimitiveCharacter q) :
    primitivePrefixAmplitude
        (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N q χ ≤
      4 * u * q * Real.log (N + 1 : ℕ) +
        2 * u * v * q * Real.log (v + 1 : ℕ) := by
  let K : ℝ := 4 * u * q * Real.log (N + 1 : ℕ) +
    2 * u * v * q * Real.log (v + 1 : ℕ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  change Real.sqrt (primitiveCharacterPrefixMaxSquare
    (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) 0 N q χ) ≤ K
  rw [← Real.sqrt_sq hK]
  apply Real.sqrt_le_sqrt
  unfold primitiveCharacterPrefixMaxSquare
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  have hyN : y ≤ N := by simpa [Finset.mem_range] using hy
  rw [show vaughanTypeICoeff vaughanUnitIntegerCoeff u v =
    vaughanTypeILongCoeff vaughanUnitIntegerCoeff u v by rfl]
  rw [primitiveCharacterPrefixSquare_typeI_eq_long]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  calc
    ‖vaughanTypeILongPrefix (fun n => vaughanUnitIntegerCoeff n) y u v q χ‖ ≤
        ‖vaughanTypeIFirstLong (fun _ => 1) y u q χ‖ +
          ‖vaughanTypeIMiddleLong (fun _ => 1) y u v q χ‖ := by
      exact norm_sub_le _ _
    _ ≤ K := add_le_add
      (norm_vaughanTypeIFirstLong_le_elementaryCauchy hyN hq χ)
      (norm_vaughanTypeIMiddleLong_le_elementaryCauchy hyN hq χ)

private theorem primitiveCharacter_card_le_totient_elementary
    (q : ℕ) (hq : 0 < q) :
    Fintype.card (PrimitiveCharacter q) ≤ q.totient := by
  exact primitiveCharacter_card_le_totient_basic q hq

/-- For `S ⊆ [2, Q]`,
`∑_{q ∈ S} φ(q)⁻¹ ∑_χ max_{y ≤ N} |∑_{n ≤ y} TypeI(n; u, v) χ(n)|` is at most
`6 Q² (u log(N + 1) + u v log(v + 1))`, with `χ` primitive mod `q`. -/
theorem apNormalizedPrimitiveMeanOn_vaughanTypeI_le_elementaryCauchy
    (N Q u v : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 2 Q) :
    apNormalizedPrimitiveMeanOn
        (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N S ≤
      6 * (Q : ℝ) ^ 2 *
        ((u : ℝ) * Real.log (N + 1 : ℕ) +
          (u : ℝ) * v * Real.log (v + 1 : ℕ)) := by
  let X : ℝ := (u : ℝ) * Real.log (N + 1 : ℕ) +
    (u : ℝ) * v * Real.log (v + 1 : ℕ)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  unfold apNormalizedPrimitiveMeanOn
  calc
    _ ≤ ∑ _q ∈ S, 6 * (Q : ℝ) * X := by
      apply Finset.sum_le_sum
      intro q hqS
      have hqI := Finset.mem_Icc.mp (hS hqS)
      have hq0 : 0 < q := by omega
      have hφ : 0 < (q.totient : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hq0
      have hamp (χ : PrimitiveCharacter q) :
          primitivePrefixAmplitude
              (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N q χ ≤
            6 * (q : ℝ) * X := by
        refine (primitivePrefixAmplitude_vaughanTypeI_le_elementaryCauchy
          N u v q (by omega) χ).trans ?_
        dsimp [X]
        have hfirst6 :
            4 * (u : ℝ) * q * Real.log (N + 1 : ℕ) ≤
              6 * q * ((u : ℝ) * Real.log (N + 1 : ℕ)) := by
          calc
            4 * (u : ℝ) * q * Real.log (N + 1 : ℕ) =
                4 * ((u : ℝ) * q * Real.log (N + 1 : ℕ)) := by ring
            _ ≤ 6 * ((u : ℝ) * q * Real.log (N + 1 : ℕ)) :=
              mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
            _ = 6 * q * ((u : ℝ) * Real.log (N + 1 : ℕ)) := by ring
        have hmiddle6 :
            2 * (u : ℝ) * v * q * Real.log (v + 1 : ℕ) ≤
              6 * q * ((u : ℝ) * v * Real.log (v + 1 : ℕ)) := by
          calc
            2 * (u : ℝ) * v * q * Real.log (v + 1 : ℕ) =
                2 * ((u : ℝ) * v * q * Real.log (v + 1 : ℕ)) := by ring
            _ ≤ 6 * ((u : ℝ) * v * q * Real.log (v + 1 : ℕ)) :=
              mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
            _ = 6 * q * ((u : ℝ) * v * Real.log (v + 1 : ℕ)) := by ring
        calc
          4 * (u : ℝ) * q * Real.log (N + 1 : ℕ) +
              2 * (u : ℝ) * v * q * Real.log (v + 1 : ℕ) ≤
            6 * q * ((u : ℝ) * Real.log (N + 1 : ℕ)) +
              6 * q * ((u : ℝ) * v * Real.log (v + 1 : ℕ)) :=
                add_le_add hfirst6 hmiddle6
          _ = 6 * q * ((u : ℝ) * Real.log (N + 1 : ℕ) +
              (u : ℝ) * v * Real.log (v + 1 : ℕ)) := by ring
      calc
        ((q.totient : ℝ)⁻¹) *
            ∑ χ : PrimitiveCharacter q,
              primitivePrefixAmplitude
                (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N q χ ≤
          ((q.totient : ℝ)⁻¹) *
            ∑ _χ : PrimitiveCharacter q, 6 * (q : ℝ) * X := by
              gcongr with χ
              exact hamp χ
        _ = ((q.totient : ℝ)⁻¹) *
            (Fintype.card (PrimitiveCharacter q) : ℝ) * (6 * q * X) := by simp; ring
        _ ≤ 1 * (6 * q * X) := by
          apply mul_le_mul_of_nonneg_right
          · rw [inv_mul_le_one₀ hφ]
            exact_mod_cast primitiveCharacter_card_le_totient_elementary q hq0
          · positivity
        _ ≤ 6 * Q * X := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by exact_mod_cast hqI.2) (by norm_num)) hX
    _ = (S.card : ℕ) * (6 * (Q : ℝ) * X) := by simp
    _ ≤ (Q : ℝ) * (6 * (Q : ℝ) * X) := by
      gcongr
      exact_mod_cast (Finset.card_le_card hS).trans (by simp [Nat.card_Icc])
    _ = 6 * (Q : ℝ) ^ 2 *
        ((u : ℝ) * Real.log (N + 1 : ℕ) +
          (u : ℝ) * v * Real.log (v + 1 : ℕ)) := by dsimp [X]; ring

/-- The same bound for the mean over the high conductors. -/
theorem highConductorVaughanTypeIMean_le_elementaryCauchy
    (N Q C u v : ℕ) :
    highConductorVaughanTypeIMean N Q C u v ≤
      6 * (Q : ℝ) ^ 2 *
        ((u : ℝ) * Real.log (N + 1 : ℕ) +
          (u : ℝ) * v * Real.log (v + 1 : ℕ)) := by
  unfold highConductorVaughanTypeIMean
  apply apNormalizedPrimitiveMeanOn_vaughanTypeI_le_elementaryCauchy
  intro q hq
  exact (Finset.mem_filter.mp hq).1

end

end BombieriVinogradov
