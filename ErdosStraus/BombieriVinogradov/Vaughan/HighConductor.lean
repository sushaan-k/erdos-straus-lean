import ErdosStraus.BombieriVinogradov.Vaughan.TypeTwo
import ErdosStraus.BombieriVinogradov.Vaughan.TypeOne

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

/-!
# The high-conductor terms of Vaughan's identity

Let `Q = ⌊√N / (log N)^B⌋` and `R = ⌊(log N)^C⌋`. With `B = 3A + 200`, `C = 2(A + 50)`
and Vaughan cutoffs `u = v = R`, the Type I, Type II and small parts of Vaughan's
identity for `Λ`, summed over the primitive characters of conductor `R < d ≤ Q`,
contribute `O(N / (log N)^A)`. The small part is bounded by Cauchy–Schwarz over the
conductors and the large sieve. Together with the Siegel–Walfisz bound for the
conductors `d ≤ R`, this gives the Bombieri–Vinogradov theorem.
-/

namespace BombieriVinogradov

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology
noncomputable section

/-- The high-conductor bound for all `A`, `C`, `B`: with `Q = ⌊√N / (log N)^B⌋` and
`R = ⌊(log N)^C⌋`, there are Vaughan cutoffs `u(N)`, `v(N)` such that the Type I, Type II
and small parts over the conductors `R < d ≤ Q`, times the weight
`4 · discreteAbelAmplifierPrefixMax N · H(Q)²` with `H(Q) = ∑_{n ≤ Q} 1/n`, are
`O(N / (log N)^A)`. The cutoffs may depend on `N`, since the Type II bound contains the
term `N / √(u + 1)`. -/
def UniformHighConductorBound : Prop :=
  ∀ A C B : ℕ, ∃ u v : ℕ → ℕ, ∃ K : ℝ, 0 < K ∧
    ∀ᶠ N : ℕ in Filter.atTop,
      let Q := BombieriVinogradov.modulusCutoff N (B : ℝ)
      4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 *
          (highConductorVaughanTypeIMean N Q C (u N) (v N) +
            highConductorVaughanTypeIIMean N Q C (u N) (v N) +
            highConductorVaughanSmallMean N Q C (v N)) ≤
        K * (N : ℝ) / Real.log N ^ A

/-- The same high-conductor bound, where for each `A` the exponents `B ≥ A + 3` and `C`
may be chosen first, and then the cutoffs `u(N)`, `v(N)` and the constant. -/
def HighConductorBound : Prop :=
  ∀ A : ℕ, ∃ B C : ℕ, A + 3 ≤ B ∧
    ∃ u v : ℕ → ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let Q := BombieriVinogradov.modulusCutoff N (B : ℝ)
        4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 *
            (highConductorVaughanTypeIMean N Q C (u N) (v N) +
              highConductorVaughanTypeIIMean N Q C (u N) (v N) +
              highConductorVaughanSmallMean N Q C (v N)) ≤
          K * (N : ℝ) / Real.log N ^ A

private theorem modulusCutoff_le_margin
    (A B N : ℕ) (hAB : A + 3 ≤ B) (hN : 3 ≤ N) :
    (BombieriVinogradov.modulusCutoff N (B : ℝ) : ℝ) ≤
      Real.sqrt N / Real.log N ^ (A + 3) := by
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have he1 : Real.exp 1 < (3 : ℝ) :=
      Real.exp_one_lt_d9.trans (by norm_num)
    exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
      (he1.trans_le (by exact_mod_cast hN)) |>.le
  have hlog0 : 0 ≤ Real.log (N : ℝ) := by positivity
  have hpow : Real.log (N : ℝ) ^ ((A + 3 : ℕ) : ℝ) ≤
      Real.log (N : ℝ) ^ (B : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le hlog (by exact_mod_cast hAB)
  calc
    (BombieriVinogradov.modulusCutoff N (B : ℝ) : ℝ) ≤
        (N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ (B : ℝ) := by
      exact Nat.floor_le (div_nonneg
        (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg hlog0 _))
    _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) /
        Real.log N ^ ((A + 3 : ℕ) : ℝ) := by
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hlog) _) hpow
    _ = Real.sqrt N / Real.log N ^ (A + 3) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_natCast]

/-- The Bombieri–Vinogradov theorem from the bounds for low and high conductors: for
each `A` there is `B` with
`∑_{q ≤ √N / (log N)^B} max_{y ≤ N} max_{(a,q)=1} |π(y;q,a) - li(y)/φ(q)| ≪ N / (log N)^A`. -/
theorem sum_primeAPPrefixMaxError_le_of_low_high
    (hlow : LowConductorBound)
    (hhigh : HighConductorBound) :
    ∀ A : ℕ, ∃ B : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        (∑ q ∈ Finset.Icc 1
            (BombieriVinogradov.modulusCutoff N (B : ℝ)),
          BombieriVinogradov.primeAPPrefixMaxError N q) ≤
          K * (N : ℝ) / Real.log N ^ A := by
  intro A
  obtain ⟨B, C, hAB, u, v, KH, hKH, hhighN⟩ := hhigh A
  obtain ⟨KL, hKL, hlowN⟩ := hlow A C B
  refine ⟨B, KL + KH + 180, by positivity, ?_⟩
  filter_upwards [hlowN, hhighN, elementaryTerms_le_div_log_pow A,
    eventually_ge_atTop (3 : ℕ)] with N hLN hHN helem hN
  let Q := BombieriVinogradov.modulusCutoff N (B : ℝ)
  have hcut : (Q : ℝ) ≤ Real.sqrt N / Real.log N ^ (A + 3) := by
    simpa [Q] using modulusCutoff_le_margin A B N hAB hN
  exact bvSum_le_of_conductor_bounds A B C N Q (u N) (v N) KL KH
    (by omega) rfl hLN hHN (helem Q hcut)

/-! ## The square sum of the small part -/

/-- `⌊N^{1/3}⌋`, an upper bound for the cutoff `v` of the small part `n ≤ v` of
Vaughan's identity. -/
def vaughanSmallCutoff (N : ℕ) : ℕ :=
  Nat.floor ((N : ℝ) ^ (1 / 3 : ℝ))

lemma vaughanSmallCutoff_le (N : ℕ) :
    vaughanSmallCutoff N ≤ N := by
  rcases N with _ | N
  · simp [vaughanSmallCutoff]
  · have hbase : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ N + 1 by omega)
    have hrpow : ((N + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      simpa using (Real.rpow_le_rpow_of_exponent_le hbase (by norm_num : (1 / 3 : ℝ) ≤ 1))
    have hfloor : (vaughanSmallCutoff (N + 1) : ℝ) ≤
        ((N + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) := by
      exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    exact_mod_cast (hfloor.trans hrpow)

lemma vaughanSmallCutoff_cast_le_sqrt (N : ℕ) :
    (vaughanSmallCutoff N : ℝ) ≤ Real.sqrt N := by
  rcases N with _ | N
  · simp [vaughanSmallCutoff]
  · have hbase : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ N + 1 by omega)
    have hrpow : ((N + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) ≤
        ((N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le hbase (by norm_num : (1 / 3 : ℝ) ≤ (1 / 2 : ℝ))
    have hfloor : (vaughanSmallCutoff (N + 1) : ℝ) ≤
        ((N + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) := by
      exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    calc
      (vaughanSmallCutoff (N + 1) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) := hfloor
      _ ≤ ((N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) := hrpow
      _ = Real.sqrt (N + 1 : ℕ) := by rw [Real.sqrt_eq_rpow]

lemma highConductorSet_subset_Icc_one (N Q C : ℕ) :
    highConductorSet N Q C ⊆ Finset.Icc 1 Q := by
  intro d hd
  have hd' := (Finset.mem_filter.mp hd).1
  have hd2 := (Finset.mem_Icc.mp hd').1
  exact Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hd').2⟩

/-- The prefix-maximal large sieve bound for the square sum of the small part
`n ≤ v` of Vaughan's identity over the conductors `R < d ≤ Q`. -/
theorem primitivePrefixSquareSumOn_small_le (N Q C v : ℕ) (hQ : 0 < Q) :
    primitivePrefixSquareSumOn
        (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N
        (highConductorSet N Q C) ≤
      (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) * primitiveLargeSieveConstant N Q *
        ((v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ) ^ 2) := by
  have hsq : primitivePrefixSquareSumOn
      (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N (highConductorSet N Q C) ≤
      (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) * primitiveLargeSieveConstant N Q *
        ∑ n ∈ Finset.Icc (1 : ℤ) N,
          ‖vaughanSmallCoeff vaughanUnitIntegerCoeff v n‖ ^ 2 := by
    unfold primitivePrefixSquareSumOn
    refine (Finset.sum_le_sum_of_subset_of_nonneg
      (highConductorSet_subset_Icc_one N Q C) ?_).trans ?_
    · intro d hd hnot
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun ψ hψ =>
        primitiveCharacterPrefixMaxSquare_nonneg _ _ _ _ _)
    · simpa using weighted_primitive_prefix_maximal
        (vaughanSmallCoeff vaughanUnitIntegerCoeff v) 0 N Q hQ
  refine hsq.trans ?_
  apply mul_le_mul_of_nonneg_left
  · simpa using vaughanSmallCoeff_energy_le_v_mul_log_sq
      vaughanUnitIntegerCoeff N v 1 (by norm_num) (by
        intro n hn
        simp [vaughanUnitIntegerCoeff])
  · unfold primitiveLargeSieveConstant
    positivity

/-- For `Q² ≤ N` and `v ≤ √N`, the weighted square sum of the small part is
`O(N √N (log N)^10)`. The ten logarithms come from `H(Q)⁴` in the squared weight (four),
`∑_{R < d ≤ Q} 1/d` (one), the prefix maximum (two), the large sieve constant (one)
and `∑_{n ≤ N} |a(n)|²` for the small part (two). -/
theorem smallPart_weightedSquareSum_le_log
    (N Q R C v : ℕ) (hN : 8 ≤ N) (hQpos : 0 < Q) (hQsq : Q ^ 2 ≤ N)
    (hvN : v ≤ N) (hvSqrt : (v : ℝ) ≤ Real.sqrt N) :
    (4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2) ^ 2 *
        (3 * highConductorHarmonicFactor Q R *
          primitivePrefixSquareSumOn
            (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N (highConductorSet N Q C)) ≤
      497664 * (15 + 4 / Real.log 2) * (N : ℝ) * Real.sqrt N *
        Real.log (N : ℝ) ^ 10 := by
  let cLS : ℝ := 15 + 4 / Real.log 2
  let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have he1 : Real.exp 1 < (3 : ℝ) :=
      Real.exp_one_lt_d9.trans (by norm_num)
    exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
      (he1.trans_le (by exact_mod_cast (show 3 ≤ N by omega))) |>.le
  have hlogPos : 0 < Real.log (N : ℝ) :=
    lt_of_lt_of_le zero_lt_one hlog
  have hQone : 1 ≤ Q := hQpos
  have hQle : Q ≤ N := by
    calc
      Q = Q * 1 := by simp
      _ ≤ Q * Q := Nat.mul_le_mul_left Q (Nat.succ_le_iff.mpr hQpos)
      _ = Q ^ 2 := by ring
      _ ≤ N := hQsq
  have hH : conductorHarmonicFactor Q ≤ 2 * Real.log (N : ℝ) := by
    have hlogQ : Real.log (Q : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by exact_mod_cast hQpos) (by exact_mod_cast hQle)
    exact (conductorHarmonicFactor_le Q).trans (by linarith)
  have hH0 : 0 ≤ conductorHarmonicFactor Q := conductorHarmonicFactor_nonneg Q
  have hHH : highConductorHarmonicFactor Q R ≤ 2 * Real.log (N : ℝ) :=
    (highConductorHarmonicFactor_le Q R).trans hH
  have hHH0 : 0 ≤ highConductorHarmonicFactor Q R := by
    unfold highConductorHarmonicFactor
    positivity
  have habel : discreteAbelAmplifierPrefixMax N ≤ 3 := by
    refine (discreteAbelAmplifierPrefixMax_le_two_inv_log_two N).trans ?_
    have htwo : (2 / 3 : ℝ) < Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    rw [mul_inv_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    linarith
  have hP : P ^ 2 ≤ 144 * conductorHarmonicFactor Q ^ 4 := by
    have hP1 : P ≤ 12 * conductorHarmonicFactor Q ^ 2 := by
      dsimp [P]
      nlinarith [habel, sq_nonneg (conductorHarmonicFactor Q)]
    have hP0 : 0 ≤ P := by
      dsimp [P]
      exact mul_nonneg
        (mul_nonneg (by norm_num) (discreteAbelAmplifierPrefixMax_nonneg N))
        (sq_nonneg _)
    calc
      P ^ 2 ≤ (12 * conductorHarmonicFactor Q ^ 2) ^ 2 :=
        pow_le_pow_left₀ hP0 hP1 2
      _ = 144 * conductorHarmonicFactor Q ^ 4 := by ring
  have hHpow4 : conductorHarmonicFactor Q ^ 4 ≤ (2 * Real.log (N : ℝ)) ^ 4 := by
    exact pow_le_pow_left₀ (conductorHarmonicFactor_nonneg Q) hH 4
  have hlog2N : (Nat.log2 N : ℝ) ≤ 2 * Real.log (N : ℝ) :=
    natLog2_cast_le_two_log (by omega)
  have hlog2N1 : ((Nat.log2 N + 1 : ℕ) : ℝ) ≤ 3 * Real.log (N : ℝ) := by
    push_cast
    linarith only [hlog2N, hlog]
  have hlog2Sq : (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) ≤ 9 * Real.log (N : ℝ) ^ 2 := by
    calc
      (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) ≤ (3 * Real.log (N : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hlog2N1 2
      _ = 9 * Real.log (N : ℝ) ^ 2 := by ring
  have hlogv : Real.log ((v + 1 : ℕ) : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    have hv1 : v + 1 ≤ N + 1 := Nat.succ_le_succ hvN
    have hlogvN1 : Real.log ((v + 1 : ℕ) : ℝ) ≤ Real.log (N + 1 : ℕ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hv1)
    have hN1 : N + 1 ≤ N * N := by
      have hN2 : 2 ≤ N := by omega
      calc
        N + 1 ≤ 2 * N := by omega
        _ ≤ N * N := by nlinarith
    have hlogN1 : Real.log (N + 1 : ℕ) ≤ 2 * Real.log (N : ℝ) := by
      calc
        Real.log (N + 1 : ℕ) ≤ Real.log (N * N : ℕ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast hN1)
        _ = 2 * Real.log (N : ℝ) := by
          rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
          ring
    exact hlogvN1.trans hlogN1
  have hvLogSq : (v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ) ^ 2 ≤
      4 * Real.sqrt N * Real.log (N : ℝ) ^ 2 := by
    have hlogvSq : Real.log ((v + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * Real.log (N : ℝ) ^ 2 := by
      have hlogv0 : 0 ≤ Real.log ((v + 1 : ℕ) : ℝ) := by
        exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ v + 1 by omega))
      calc
        Real.log ((v + 1 : ℕ) : ℝ) ^ 2 ≤ (2 * Real.log (N : ℝ)) ^ 2 :=
          pow_le_pow_left₀ hlogv0 hlogv 2
        _ = 4 * Real.log (N : ℝ) ^ 2 := by ring
    calc
      (v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ) ^ 2 ≤
          Real.sqrt N * Real.log ((v + 1 : ℕ) : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hvSqrt (sq_nonneg _)
      _ ≤ Real.sqrt N * (4 * Real.log (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hlogvSq (Real.sqrt_nonneg _)
      _ = 4 * Real.sqrt N * Real.log (N : ℝ) ^ 2 := by ring
  have hPLC : primitiveLargeSieveConstant N Q ≤ cLS * (N : ℝ) * Real.log (N : ℝ) := by
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hQsqR : (Q : ℝ) ^ 2 ≤ (N : ℝ) := by exact_mod_cast hQsq
    have hQsq1 : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := by exact_mod_cast (one_le_pow₀ hQone)
    have hceil := (Nat.ceil_lt_add_one
      (div_nonneg (Real.log_nonneg hQsq1) hlog2.le)).le
    have hlogQ := Real.log_le_log (by positivity : (0 : ℝ) < (Q : ℝ) ^ 2) hQsqR
    have hcoef :
        2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12 ≤
          (4 / Real.log 2) * Real.log (N : ℝ) + 14 := by
      have hquot := (div_le_div_iff_of_pos_right hlog2).2 hlogQ
      have hquot0 : 0 ≤ Real.log (N : ℝ) / Real.log 2 := by positivity
      calc
        _ ≤ 4 * (Real.log (N : ℝ) / Real.log 2) + 14 := by
          linarith only [hceil, hquot, hquot0]
        _ = _ := by ring
    unfold primitiveLargeSieveConstant
    calc
      (N : ℝ) +
          (2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) * (Q : ℝ) ^ 2
          ≤ (N : ℝ) + ((4 / Real.log 2) * Real.log (N : ℝ) + 14) * N := by
            gcongr
      _ ≤ cLS * (N : ℝ) * Real.log (N : ℝ) := by
        dsimp [cLS]
        nlinarith only [mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hlog)]
  have hPLC0 : 0 ≤ primitiveLargeSieveConstant N Q := by
    unfold primitiveLargeSieveConstant
    positivity
  have hsq := primitivePrefixSquareSumOn_small_le N Q C v hQpos
  calc
    P ^ 2 * (3 * highConductorHarmonicFactor Q R *
        primitivePrefixSquareSumOn
          (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N (highConductorSet N Q C))
        ≤ P ^ 2 * (3 * highConductorHarmonicFactor Q R *
          ((((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) * primitiveLargeSieveConstant N Q *
            ((v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ) ^ 2))) := by
              gcongr
    _ ≤ (144 * (2 * Real.log (N : ℝ)) ^ 4) *
        (3 * (2 * Real.log (N : ℝ)) *
          (9 * Real.log (N : ℝ) ^ 2 * (cLS * (N : ℝ) * Real.log (N : ℝ)) *
            (4 * Real.sqrt N * Real.log (N : ℝ) ^ 2))) := by
              have hPlog := hP.trans (mul_le_mul_of_nonneg_left hHpow4 (by norm_num))
              gcongr
    _ = 497664 * cLS * (N : ℝ) * Real.sqrt N * Real.log (N : ℝ) ^ 10 := by ring

/-- If eventually `v(N) ≤ ⌊N^{1/3}⌋`, then the weighted square sum of the small part
is at most `(K₀ N / (log N)^(A+κ))²` for all large `N`. -/
theorem smallPart_weightedSquareSum_le_sq
    (cutoff : ℕ → ℕ)
    (hcutoff : ∀ᶠ N : ℕ in Filter.atTop,
      cutoff N ≤ vaughanSmallCutoff N)
    (A κ B C : ℕ) :
    ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let Q := BombieriVinogradov.modulusCutoff N (B : ℝ)
        let R := logConductorThreshold N C
        let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
        let X := (N : ℝ) / Real.log N ^ (A + κ)
        P ^ 2 * (3 * highConductorHarmonicFactor Q R *
            primitivePrefixSquareSumOn
              (vaughanSmallCoeff vaughanUnitIntegerCoeff
                (cutoff N)) N
              (highConductorSet N Q C)) ≤ (K₀ * X) ^ 2 := by
  let M : ℝ := 497664 * (15 + 4 / Real.log 2)
  let K₀ : ℝ := Real.sqrt M + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hK : M ≤ K₀ ^ 2 := by
    dsimp [K₀]
    nlinarith only [Real.sq_sqrt hM, Real.sqrt_nonneg M]
  refine ⟨K₀, by positivity, ?_⟩
  filter_upwards [hcutoff, eventually_ge_atTop (8 : ℕ),
    log_pow_le_sqrt_eventually (10 + 2 * (A + κ)),
    log_pow_le_sqrt_eventually B] with N hcut hN hlogPay hcutGrow
  dsimp only
  let Q := BombieriVinogradov.modulusCutoff N (B : ℝ)
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hQone : 1 ≤ Q := by
    dsimp [Q, BombieriVinogradov.modulusCutoff]
    have hdenPos : 0 < Real.log (N : ℝ) ^ (B : ℝ) := by
      simpa [Real.rpow_natCast] using pow_pos hlogPos B
    have hcutGrow' : Real.log (N : ℝ) ^ (B : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
      simpa [Real.sqrt_eq_rpow, Real.rpow_natCast] using hcutGrow
    apply Nat.le_floor
    simpa only [Nat.cast_one] using (one_le_div₀ hdenPos).2 hcutGrow'
  have hQpos : 0 < Q := by omega
  have hQsq : Q ^ 2 ≤ N := by
    simpa [Q] using BombieriVinogradov.modulusCutoff_sq_le
      N (B : ℝ) (by omega) (by positivity : 0 ≤ (B : ℝ))
  have hvN := hcut.trans (vaughanSmallCutoff_le N)
  have hvSqrt : (cutoff N : ℝ) ≤ Real.sqrt N :=
    (Nat.cast_le.mpr hcut).trans (vaughanSmallCutoff_cast_le_sqrt N)
  have htop := smallPart_weightedSquareSum_le_log N Q
    (logConductorThreshold N C) C (cutoff N) hN hQpos hQsq hvN hvSqrt
  have hlogDiv : Real.log (N : ℝ) ^ 10 ≤
      Real.sqrt N / Real.log N ^ (2 * (A + κ)) := by
    apply (le_div_iff₀ (pow_pos hlogPos _)).2
    simpa only [pow_add] using hlogPay
  refine htop.trans ?_
  calc
    M * (N : ℝ) * Real.sqrt N * Real.log (N : ℝ) ^ 10
        ≤ M * (N : ℝ) * Real.sqrt N *
          (Real.sqrt N / Real.log N ^ (2 * (A + κ))) := by gcongr
    _ = M * ((N : ℝ) ^ 2 / Real.log N ^ (2 * (A + κ))) := by
      calc
        _ = M * ((N : ℝ) * (Real.sqrt N * Real.sqrt N) /
            Real.log N ^ (2 * (A + κ))) := by ring
        _ = _ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg N)]; ring
    _ ≤ K₀ ^ 2 * ((N : ℝ) ^ 2 / Real.log N ^ (2 * (A + κ))) := by gcongr
    _ = (K₀ * ((N : ℝ) / Real.log N ^ (A + κ))) ^ 2 := by ring

/-! ## From square sums to normalized means -/

lemma highConductorSet_eq_interval (N Q C : ℕ)
    (hR : 1 ≤ logConductorThreshold N C) :
    highConductorSet N Q C =
      Finset.Icc (logConductorThreshold N C + 1) Q := by
  ext d
  simp only [highConductorSet, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨-, hdQ⟩, hRd⟩
    exact ⟨Nat.add_one_le_iff.mpr hRd, hdQ⟩
  · rintro ⟨hRd, hdQ⟩
    exact ⟨⟨by omega, hdQ⟩, Nat.add_one_le_iff.mp hRd⟩

/-- Cauchy–Schwarz over the conductors `R < d ≤ Q`: if `P² · 3 H · S ≤ Z²`, where `S` is
the square sum of `a` and `H = ∑_{R < d ≤ Q} 1/d`, then `P` times the normalized mean
of `a` is at most `Z`. Here `P` may be negative. -/
theorem apNormalizedPrimitiveMeanOn_high_le_of_sq
    (a : ℤ → ℂ) (N Q C : ℕ) (P Z : ℝ)
    (hR : 1 ≤ logConductorThreshold N C) (hZ : 0 ≤ Z)
    (hP2 : P ^ 2 * (3 * highConductorHarmonicFactor Q
        (logConductorThreshold N C) *
        primitivePrefixSquareSumOn a N (highConductorSet N Q C)) ≤ Z ^ 2) :
    P * apNormalizedPrimitiveMeanOn a N (highConductorSet N Q C) ≤ Z := by
  have hcard : ∀ d ∈ Finset.Icc (logConductorThreshold N C + 1) Q,
      Fintype.card (PrimitiveCharacter d) ≤ d.totient := by
    intro d hd
    exact card_primitiveCharacter_le_totient d (by
      have hdR := (Finset.mem_Icc.mp hd).1
      omega)
  have hc := apNormalizedPrimitiveMeanOn_high_sq_le a N Q
    (logConductorThreshold N C) hcard
  rw [← highConductorSet_eq_interval N Q C hR] at hc
  have hw := mul_le_mul_of_nonneg_left hc (sq_nonneg P)
  apply le_of_sq_le_sq _ hZ
  nlinarith only [hw, hP2,
    sq_nonneg (P * apNormalizedPrimitiveMeanOn a N (highConductorSet N Q C))]

/-- For `Q = ⌊√N / (log N)^B⌋`, the weight `4 · discreteAbelAmplifierPrefixMax N · H(Q)²`
is at most `48 (log N)²`, also when `Q = 0`. -/
theorem abelConductorWeight_le_log_sq (B N : ℕ) (hN : 3 ≤ N) :
    let Q := BombieriVinogradov.modulusCutoff N (B : ℝ)
    4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 ≤
      48 * Real.log (N : ℝ) ^ 2 := by
  dsimp only
  let Q := BombieriVinogradov.modulusCutoff N (B : ℝ)
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have he1 : Real.exp 1 < (3 : ℝ) :=
      Real.exp_one_lt_d9.trans (by norm_num)
    exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
      (he1.trans_le (by exact_mod_cast hN)) |>.le
  have habel : discreteAbelAmplifierPrefixMax N ≤ 3 := by
    refine (discreteAbelAmplifierPrefixMax_le_two_inv_log_two N).trans ?_
    have htwo : (2 / 3 : ℝ) < Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    rw [mul_inv_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    linarith
  by_cases hQ0 : Q = 0
  · simp [Q, hQ0, conductorHarmonicFactor]
    exact pow_nonneg (zero_le_one.trans hlog) 2
  · have hQpos : 0 < Q := Nat.pos_of_ne_zero hQ0
    have hQsq : Q ^ 2 ≤ N := by
      simpa [Q] using BombieriVinogradov.modulusCutoff_sq_le
        N (B : ℝ) (by omega) (by positivity : 0 ≤ (B : ℝ))
    have hQle : Q ≤ N := by
      calc
        Q = Q * 1 := by simp
        _ ≤ Q * Q := Nat.mul_le_mul_left Q (Nat.succ_le_iff.mpr hQpos)
        _ = Q ^ 2 := by ring
        _ ≤ N := hQsq
    have hlogQ : Real.log (Q : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by exact_mod_cast hQpos) (by exact_mod_cast hQle)
    have hH : conductorHarmonicFactor Q ≤ 2 * Real.log (N : ℝ) :=
      (conductorHarmonicFactor_le Q).trans (by linarith)
    have hH0 : 0 ≤ conductorHarmonicFactor Q := conductorHarmonicFactor_nonneg Q
    calc
      _ ≤ 4 * 3 * (2 * Real.log (N : ℝ)) ^ 2 := by gcongr
      _ = 48 * Real.log (N : ℝ) ^ 2 := by ring

set_option maxHeartbeats 3000000 in
/-- The bound for the weighted square sum of the small part, restated. -/
theorem smallPart_weightedSquareSum_le_sq'
    (cutoff : ℕ → ℕ)
    (hcutoff : ∀ᶠ N : ℕ in Filter.atTop,
      cutoff N ≤ vaughanSmallCutoff N)
    (A κ B C : ℕ) :
    ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let Q := BombieriVinogradov.modulusCutoff N (B : ℝ)
        let R := logConductorThreshold N C
        let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
        let X := (N : ℝ) / Real.log N ^ (A + κ)
        P ^ 2 * (3 * highConductorHarmonicFactor Q R *
            primitivePrefixSquareSumOn
              (vaughanSmallCoeff vaughanUnitIntegerCoeff
                (cutoff N)) N
              (highConductorSet N Q C)) ≤ (K₀ * X) ^ 2 := by
  exact smallPart_weightedSquareSum_le_sq cutoff hcutoff A κ B C

/-! ## The bound at `B = 3A + 200`, `C = 2(A + 50)` and `u = v = R` -/

set_option maxHeartbeats 2400000

/-- The exponent `B = 3A + 200` in `Q = ⌊√N / (log N)^B⌋`. -/
def highConductorModulusExponent (A : ℕ) : ℕ := 3 * A + 200

/-- The exponent `C = 2(A + 50)` in the conductor threshold `R = ⌊(log N)^C⌋`. -/
def highConductorThresholdExponent (A : ℕ) : ℕ :=
  2 * (A + 50)

/-- The Vaughan cutoffs `u = v = R = ⌊(log N)^C⌋`. -/
def highConductorVaughanCutoff (A N : ℕ) : ℕ :=
  logConductorThreshold N (highConductorThresholdExponent A)

private theorem chosenTypeII_logPower_le_threshold_eventually (A : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      Real.log (N : ℝ) ^ (2 * (A + 49)) ≤
        (highConductorVaughanCutoff A N : ℝ) := by
  filter_upwards [eventually_ge_atTop (9 : ℕ)] with N hN
  let x : ℝ := Real.log (N : ℝ)
  let t : ℕ := A + 49
  have hx2 : 2 ≤ x := by
    dsimp [x]
    have he1 : Real.exp 1 < (3 : ℝ) :=
      Real.exp_one_lt_d9.trans (by norm_num)
    have he10 : 0 < Real.exp (1 : ℝ) := Real.exp_pos 1
    have h9 : Real.exp 2 < (9 : ℝ) := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith
    have hexp : Real.exp 2 < (N : ℝ) := h9.trans_le (by exact_mod_cast hN)
    exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2 hexp |>.le
  have hx0 : 0 ≤ x := hx2.trans' (by norm_num)
  have hxpow2 : 2 ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 2)]
  have hfloor := Nat.sub_one_lt_floor (x ^ (2 * (t + 1)))
  have hhalf : x ^ (2 * t) ≤ x ^ (2 * (t + 1)) - 1 := by
    rw [show 2 * (t + 1) = 2 * t + 2 by omega, pow_add]
    have hbase : 1 ≤ x ^ (2 * t) := one_le_pow₀ (by linarith)
    nlinarith [pow_nonneg hx0 (2 * t)]
  have hcast : x ^ (2 * t) ≤ (Nat.floor (x ^ (2 * (t + 1))) : ℝ) :=
    hhalf.trans hfloor.le
  simpa [highConductorVaughanCutoff,
    highConductorThresholdExponent, highConductorModulusExponent,
    logConductorThreshold, x, t, Nat.cast_ofNat] using hcast

/-- At most `(log₂ N + 1)²` dyadic rectangles are active in the Type II sum. -/
theorem highConductorVaughanCutoff_activeCard_le (A N : ℕ) :
    (vaughanTypeIIActiveCanonicalRectangles N
        (highConductorVaughanCutoff A N)
        (highConductorVaughanCutoff A N)).card ≤ (Nat.log2 N + 1) ^ 2 := by
  simpa [Nat.log2_eq_log_two] using
    card_vaughanTypeIIActiveCanonicalRectangles_le N
      (highConductorVaughanCutoff A N)
      (highConductorVaughanCutoff A N)

/-- The Type II part over the conductors `R < d ≤ Q` contributes `O(N / (log N)^A)`.
The loss `(log N)^19` from the weight, the number of rectangles and the large sieve
is absorbed by `√R ≥ (log N)^(A+49)` and `Q √N ≤ N / (log N)^B`. -/
theorem highConductorBound_typeII (A : ℕ) :
    let B := 3 * A + 200
    let C := 2 * (A + 50)
    let u : ℕ → ℕ := fun N => logConductorThreshold N C
    let v : ℕ → ℕ := fun N => logConductorThreshold N C
    ∃ K : ℝ, 0 < K ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let Q := BombieriVinogradov.modulusCutoff N (B : ℝ)
        4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 *
            highConductorVaughanTypeIIMean N Q C (u N) (v N) ≤
          K * (N : ℝ) / Real.log N ^ A := by
  dsimp only
  let K : ℝ := 1000000000000000000
  refine ⟨K, by norm_num [K], ?_⟩
  filter_upwards [eventually_ge_atTop (9 : ℕ),
    chosenTypeII_logPower_le_threshold_eventually A,
    log_pow_le_sqrt_eventually (3 * A + 200),
    log_pow_le_sqrt_eventually (2 * (3 * A + 200))] with N hN hRlower hQgrow hCgrow
  let B : ℕ := 3 * A + 200
  let C : ℕ := 2 * (A + 50)
  let R : ℕ := logConductorThreshold N C
  let Q := BombieriVinogradov.modulusCutoff N (B : ℝ)
  let x : ℝ := Real.log (N : ℝ)
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have he1 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
    exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
      (he1.trans_le (by exact_mod_cast (show 3 ≤ N by omega))) |>.le
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hRpow : x ^ (2 * (A + 49)) ≤ (R : ℝ) := by
    simpa [R, C, highConductorVaughanCutoff,
      highConductorThresholdExponent,
      highConductorModulusExponent, x] using hRlower
  have hRpos : 0 < R := by
    exact_mod_cast (lt_of_lt_of_le (pow_pos hx0 _) hRpow)
  have hsRpos : 0 < Real.sqrt (R : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hRpos)
  have hsR : x ^ (A + 49) ≤ Real.sqrt (R : ℝ) := by
    have hsRsq : Real.sqrt (R : ℝ) ^ 2 = R := Real.sq_sqrt (by positivity)
    have hp : (x ^ (A + 49)) ^ 2 = x ^ (2 * (A + 49)) := by
      rw [← pow_mul]
      congr 1
      omega
    have hp0 : 0 ≤ x ^ (A + 49) := pow_nonneg hx0.le _
    exact (sq_le_sq₀ hp0 hsRpos.le).mp (by simpa only [hp, hsRsq] using hRpow)
  have hQone : 1 ≤ Q := by
    dsimp [Q, BombieriVinogradov.modulusCutoff]
    have hden : 0 < x ^ B := pow_pos hx0 _
    have hgrow : x ^ B ≤ Real.sqrt N := by
      simpa [B, x] using hQgrow
    have hratio : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) / x ^ B := by
      rw [← Real.sqrt_eq_rpow]
      exact (one_le_div₀ hden).2 hgrow
    exact Nat.le_floor (by
      simpa [x, Real.rpow_natCast] using hratio)
  have hQpos : 0 < Q := by omega
  have hQsq : Q ^ 2 ≤ N := by
    simpa [Q] using BombieriVinogradov.modulusCutoff_sq_le
      N (B : ℝ) (by omega) (by positivity : 0 ≤ (B : ℝ))
  have hQleN : Q ≤ N := by
    calc
      Q ≤ Q ^ 2 := by nlinarith
      _ ≤ N := hQsq
  have hQleHalf : Q ≤ N / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    by_cases hQsmall : Q ≤ 1
    · omega
    · calc
        Q * 2 ≤ Q * Q := Nat.mul_le_mul_left Q (by omega)
        _ ≤ N := by simpa only [pow_two] using hQsq
  have hRltN : R < N := by
    have hRreal : (R : ℝ) ≤ Real.sqrt N := by
      calc
        (R : ℝ) ≤ Real.log (N : ℝ) ^ C := by
          dsimp [R, logConductorThreshold]
          exact Nat.floor_le (pow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _)
        _ ≤ Real.sqrt N := by
          have hpowmono : x ^ C ≤ x ^ (2 * (3 * A + 200)) := by
            apply pow_le_pow_right₀ hx1
            dsimp [C]
            omega
          exact hpowmono.trans (by simpa [x] using hCgrow)
    have hsSq : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
    have hslt : Real.sqrt N < (N : ℝ) := by
      nlinarith [Real.sqrt_nonneg (N : ℝ), show (1 : ℝ) < N by exact_mod_cast (show 1 < N by omega)]
    exact_mod_cast hRreal.trans_lt hslt
  have haggregate := apNormalizedVaughanTypeIIMeanOn_high_le
    N Q C R R hN hRpos hQleHalf hRltN hRltN
  have hindexNat :
      (dyadicConductorBlocks N Q C hRpos).index.card ≤ Nat.log2 N + 1 :=
    dyadicConductorBlocks_index_card_le N Q C hRpos hQleN
  have hactiveNat :
      (vaughanTypeIIActiveCanonicalRectangles N R R).card ≤ (Nat.log2 N + 1) ^ 2 := by
    simpa [R, C, highConductorVaughanCutoff,
      highConductorThresholdExponent, highConductorModulusExponent] using
      highConductorVaughanCutoff_activeCard_le A N
  have hlog2 : (Nat.log2 N : ℝ) ≤ 2 * x := by
    simpa [x] using natLog2_cast_le_two_log (show 2 ≤ N by omega)
  have hlog2one : ((Nat.log2 N + 1 : ℕ) : ℝ) ≤ 3 * x := by
    push_cast
    linarith
  have hactive :
      ((vaughanTypeIIActiveCanonicalRectangles N R R).card : ℝ) ≤ 9 * x ^ 2 := by
    calc
      _ ≤ (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) := by exact_mod_cast hactiveNat
      _ ≤ (3 * x) ^ 2 := pow_le_pow_left₀ (by positivity) hlog2one 2
      _ = 9 * x ^ 2 := by ring
  have hindex :
      (((dyadicConductorBlocks N Q C hRpos).index.card : ℕ) : ℝ) ≤ 3 * x := by
    have hc : (((dyadicConductorBlocks N Q C hRpos).index.card : ℕ) : ℝ) ≤
        ((Nat.log2 N + 1 : ℕ) : ℝ) := by exact_mod_cast hindexNat
    exact hc.trans hlog2one
  have hlog4 : Real.log (4 * N + 4 : ℕ) ≤ 3 * x := by
    have hpoly : 4 * N + 4 ≤ N * N := by nlinarith
    calc
      Real.log (4 * N + 4 : ℕ) ≤ Real.log (N * N : ℕ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hpoly)
      _ = 2 * x := by rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]; ring
      _ ≤ 3 * x := by nlinarith
  have hQpay : (Q : ℝ) * Real.sqrt N ≤ (N : ℝ) / x ^ B := by
    have hq : (Q : ℝ) ≤ Real.sqrt N / x ^ B := by
      calc
        (Q : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ (B : ℝ) :=
          Nat.floor_le (by positivity)
        _ = Real.sqrt N / x ^ B := by
          rw [Real.sqrt_eq_rpow, Real.rpow_natCast]
    have hs : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
    calc
      (Q : ℝ) * Real.sqrt N ≤ (Real.sqrt N / x ^ B) * Real.sqrt N :=
        mul_le_mul_of_nonneg_right hq (Real.sqrt_nonneg _)
      _ = (Real.sqrt N * Real.sqrt N) / x ^ B := by ring
      _ = (N : ℝ) / x ^ B := by rw [← pow_two, hs]
  have hRinv : (N : ℝ) / R ≤ (N : ℝ) / x ^ (A + 49) := by
    have hsRq : Real.sqrt (R : ℝ) ^ 2 = (R : ℝ) := Real.sq_sqrt (by positivity)
    have hsRleR : Real.sqrt (R : ℝ) ≤ (R : ℝ) := by
      nlinarith [Real.sqrt_nonneg (R : ℝ), show (1 : ℝ) ≤ R by exact_mod_cast hRpos]
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hx0 _) (hsR.trans hsRleR)
  have hRsqrt : (N : ℝ) / Real.sqrt (R + 1 : ℕ) ≤
      (N : ℝ) / x ^ (A + 49) := by
    have hsmono : Real.sqrt (R : ℝ) ≤ Real.sqrt (R + 1 : ℕ) := Real.sqrt_le_sqrt (by norm_num)
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hx0 _) (hsR.trans hsmono)
  have hbracket :
      2 * (N : ℝ) / R +
          (((dyadicConductorBlocks N Q C hRpos).index.card : ℕ) : ℝ) *
            ((N : ℝ) / Real.sqrt (R + 1 : ℕ) + (N : ℝ) / Real.sqrt (R + 1 : ℕ)) +
          2 * (Q : ℝ) * Real.sqrt N ≤
        10 * (N : ℝ) / x ^ (A + 48) := by
    have hpow48 : x ^ (A + 48) ≤ x ^ (A + 49) :=
      pow_le_pow_right₀ hx1 (by omega)
    have hden49 : 0 < x ^ (A + 49) := pow_pos hx0 _
    have hden48 : 0 < x ^ (A + 48) := pow_pos hx0 _
    have hsmall : (N : ℝ) / x ^ (A + 49) ≤ (N : ℝ) / x ^ (A + 48) :=
      div_le_div_of_nonneg_left (by positivity) hden48 hpow48
    have hBden : x ^ (A + 48) ≤ x ^ B := by
      dsimp [B]
      exact pow_le_pow_right₀ hx1 (by omega)
    have hqsmall : (N : ℝ) / x ^ B ≤ (N : ℝ) / x ^ (A + 48) :=
      div_le_div_of_nonneg_left (by positivity) hden48 hBden
    let T : ℝ := (N : ℝ) / x ^ (A + 48)
    have hfirst : 2 * (N : ℝ) / R ≤ 2 * T := by
      dsimp [T]
      calc
        2 * (N : ℝ) / R = 2 * ((N : ℝ) / R) := by ring
        _ ≤ 2 * ((N : ℝ) / x ^ (A + 48)) :=
          mul_le_mul_of_nonneg_left (hRinv.trans hsmall) (by norm_num)
    have hsum : (N : ℝ) / Real.sqrt (R + 1 : ℕ) +
        (N : ℝ) / Real.sqrt (R + 1 : ℕ) ≤ 2 * ((N : ℝ) / x ^ (A + 49)) := by
      exact add_le_add hRsqrt hRsqrt |>.trans_eq (by ring)
    have hmiddle0 :
        (((dyadicConductorBlocks N Q C hRpos).index.card : ℕ) : ℝ) *
          ((N : ℝ) / Real.sqrt (R + 1 : ℕ) + (N : ℝ) / Real.sqrt (R + 1 : ℕ)) ≤
        (3 * x) * (2 * ((N : ℝ) / x ^ (A + 49))) := by
      exact mul_le_mul hindex hsum (by positivity) (by positivity)
    have hcancel : (3 * x) * (2 * ((N : ℝ) / x ^ (A + 49))) = 6 * T := by
      dsimp [T]
      rw [show A + 49 = (A + 48) + 1 by omega, pow_succ]
      field_simp
      ring
    have hmiddle :
        (((dyadicConductorBlocks N Q C hRpos).index.card : ℕ) : ℝ) *
          ((N : ℝ) / Real.sqrt (R + 1 : ℕ) + (N : ℝ) / Real.sqrt (R + 1 : ℕ)) ≤
        6 * T := hmiddle0.trans_eq hcancel
    have hthird : 2 * (Q : ℝ) * Real.sqrt N ≤ 2 * T := by
      dsimp [T]
      nlinarith [hQpay, hqsmall]
    calc
      2 * (N : ℝ) / R +
          (((dyadicConductorBlocks N Q C hRpos).index.card : ℕ) : ℝ) *
            ((N : ℝ) / Real.sqrt (R + 1 : ℕ) + (N : ℝ) / Real.sqrt (R + 1 : ℕ)) +
          2 * (Q : ℝ) * Real.sqrt N ≤ 2 * T + 6 * T + 2 * T :=
        add_le_add (add_le_add hfirst hmiddle) hthird
      _ = 10 * (N : ℝ) / x ^ (A + 48) := by dsimp [T]; ring
  have hmean : highConductorVaughanTypeIIMean N Q C R R ≤
      (9 * x ^ 2) * (1000000 * (3 * x) ^ 15) *
        (10 * (N : ℝ) / x ^ (A + 48)) := by
    change apNormalizedVaughanTypeIIMeanOn N R R (highConductorSet N Q C) ≤ _
    exact haggregate.trans (by gcongr)
  have houter :
      4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 ≤
        48 * x ^ 2 :=
    abelConductorWeight_le_log_sq B N (by omega)
  have hnonneg : 0 ≤ highConductorVaughanTypeIIMean N Q C R R := by
    unfold highConductorVaughanTypeIIMean apNormalizedPrimitiveMeanOn
    exact Finset.sum_nonneg fun d hd =>
      mul_nonneg (inv_nonneg.mpr (by positivity))
        (Finset.sum_nonneg fun ψ hψ => primitivePrefixAmplitude_nonneg _ _ _ _)
  calc
    4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 *
        highConductorVaughanTypeIIMean N Q C R R ≤
      (48 * x ^ 2) * ((9 * x ^ 2) * (1000000 * (3 * x) ^ 15) *
        (10 * (N : ℝ) / x ^ (A + 48))) :=
      mul_le_mul houter hmean hnonneg (by positivity)
    _ ≤ K * (N : ℝ) / x ^ A := by
      dsimp [K]
      have hconst : (61987278240000000 : ℝ) ≤ 1000000000000000000 := by norm_num
      have hpow : x ^ A ≤ x ^ (A + 29) := pow_le_pow_right₀ hx1 (by omega)
      have hdiv : (N : ℝ) / x ^ (A + 29) ≤ (N : ℝ) / x ^ A :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hx0 A) hpow
      calc
        (48 * x ^ 2) * (9 * x ^ 2 * (1000000 * (3 * x) ^ 15) *
            (10 * (N : ℝ) / x ^ (A + 48))) =
            61987278240000000 * ((N : ℝ) / x ^ (A + 29)) := by
              rw [show A + 48 = (A + 29) + 19 by omega, pow_add]
              field_simp
              ring
        _ ≤ 61987278240000000 * ((N : ℝ) / x ^ A) :=
          mul_le_mul_of_nonneg_left hdiv (by norm_num)
        _ ≤ 1000000000000000000 * ((N : ℝ) / x ^ A) :=
          mul_le_mul_of_nonneg_right hconst (by positivity)
        _ = 1000000000000000000 * (N : ℝ) / x ^ A := by ring

/-- The Type I part over the conductors `R < d ≤ Q` contributes `O(N / (log N)^A)`:
its elementary bound `6 Q² (u log(N+1) + u v log(v+1))` is `O(N (log N)^(2C+1-2B))`. -/
theorem highConductorBound_typeI (A : ℕ) :
    let B := 3 * A + 200
    let C := 2 * (A + 50)
    let u : ℕ → ℕ := fun N => logConductorThreshold N C
    let v : ℕ → ℕ := fun N => logConductorThreshold N C
    ∃ K : ℝ, 0 < K ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let Q := BombieriVinogradov.modulusCutoff N (B : ℝ)
        4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 *
            highConductorVaughanTypeIMean N Q C (u N) (v N) ≤
          K * (N : ℝ) / Real.log N ^ A := by
  dsimp only
  refine ⟨2000, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (9 : ℕ),
    log_pow_le_sqrt_eventually (2 * (A + 50))] with N hN hCgrow
  let B : ℕ := 3 * A + 200
  let C : ℕ := 2 * (A + 50)
  let R : ℕ := logConductorThreshold N C
  let Q := BombieriVinogradov.modulusCutoff N (B : ℝ)
  let x : ℝ := Real.log (N : ℝ)
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have he1 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
    exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
      (he1.trans_le (by exact_mod_cast (show 3 ≤ N by omega))) |>.le
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hRcast : (R : ℝ) ≤ x ^ C := by
    dsimp [R, logConductorThreshold]
    exact Nat.floor_le (pow_nonneg hx0.le _)
  have hRC : (0 : ℝ) ≤ R := by positivity
  have hRleN : R ≤ N := by
    have hRsqrt : (R : ℝ) ≤ Real.sqrt N := hRcast.trans (by simpa [C, x] using hCgrow)
    have hsSq : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
    have hsle : Real.sqrt N ≤ (N : ℝ) := by
      nlinarith [Real.sqrt_nonneg (N : ℝ), show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega)]
    exact_mod_cast hRsqrt.trans hsle
  have hlogN1 : Real.log (N + 1 : ℕ) ≤ 2 * x := by
    have hpoly : N + 1 ≤ N * N := by nlinarith
    calc
      Real.log (N + 1 : ℕ) ≤ Real.log (N * N : ℕ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hpoly)
      _ = 2 * x := by rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]; ring
  have hlogR1 : Real.log (R + 1 : ℕ) ≤ 2 * x := by
    exact (Real.log_le_log (by positivity) (by exact_mod_cast Nat.succ_le_succ hRleN)).trans hlogN1
  have hRCone : (1 : ℝ) ≤ x ^ C := one_le_pow₀ hx1
  have hcore :
      (R : ℝ) * Real.log (N + 1 : ℕ) +
          (R : ℝ) * R * Real.log (R + 1 : ℕ) ≤
        4 * x ^ (2 * C + 1) := by
    have hRmajor : (R : ℝ) ≤ (x ^ C) ^ 2 :=
      hRcast.trans (by nlinarith only [hRCone])
    have hR2 : (R : ℝ) ^ 2 ≤ (x ^ C) ^ 2 :=
      pow_le_pow_left₀ hRC hRcast 2
    calc
      _ = (R : ℝ) * Real.log (N + 1 : ℕ) +
          (R : ℝ) ^ 2 * Real.log (R + 1 : ℕ) := by ring
      _ ≤ (x ^ C) ^ 2 * (2 * x) + (x ^ C) ^ 2 * (2 * x) := by
        apply add_le_add
        · exact mul_le_mul hRmajor hlogN1 (by positivity) (sq_nonneg _)
        · exact mul_le_mul hR2 hlogR1 (by positivity) (sq_nonneg _)
      _ = 4 * x ^ (2 * C + 1) := by
        rw [show 2 * C + 1 = C + C + 1 by omega, pow_succ, pow_add]
        ring
  have hQcast : (Q : ℝ) ≤ Real.sqrt N / x ^ B := by
    calc
      (Q : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ (B : ℝ) :=
        Nat.floor_le (by positivity)
      _ = Real.sqrt N / x ^ B := by
        rw [Real.sqrt_eq_rpow, Real.rpow_natCast]
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  have hQsq : (Q : ℝ) ^ 2 ≤ (N : ℝ) / x ^ (2 * B) := by
    have hsSq : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
    have hden : 0 < x ^ B := pow_pos hx0 _
    have hsquared := pow_le_pow_left₀ hQ0 hQcast 2
    calc
      (Q : ℝ) ^ 2 ≤ (Real.sqrt N / x ^ B) ^ 2 := hsquared
      _ = (N : ℝ) / x ^ (2 * B) := by
        rw [div_pow, hsSq, ← pow_mul, show B * 2 = 2 * B by omega]
  have hmean := highConductorVaughanTypeIMean_le_elementaryCauchy N Q C R R
  have hmean' : highConductorVaughanTypeIMean N Q C R R ≤
      24 * ((N : ℝ) / x ^ (2 * B)) * x ^ (2 * C + 1) := by
    calc
      _ ≤ 6 * (Q : ℝ) ^ 2 *
          ((R : ℝ) * Real.log (N + 1 : ℕ) +
            (R : ℝ) * R * Real.log (R + 1 : ℕ)) := hmean
      _ ≤ 6 * ((N : ℝ) / x ^ (2 * B)) * (4 * x ^ (2 * C + 1)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hQsq (by norm_num)) hcore
          (by positivity) (by positivity)
      _ = 24 * ((N : ℝ) / x ^ (2 * B)) * x ^ (2 * C + 1) := by ring
  have houter :
      4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 ≤
        48 * x ^ 2 :=
    abelConductorWeight_le_log_sq B N (by omega)
  have hscale : ((N : ℝ) / x ^ (2 * B)) * x ^ (2 * C + 3) ≤
      (N : ℝ) / x ^ A := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (pow_pos hx0 _) (pow_pos hx0 _)]
    have hexp : 2 * C + 3 + A ≤ 2 * B := by dsimp [B, C]; omega
    calc
      (N : ℝ) * x ^ (2 * C + 3) * x ^ A = (N : ℝ) * x ^ (2 * C + 3 + A) := by rw [pow_add]; ring
      _ ≤ (N : ℝ) * x ^ (2 * B) := by
        gcongr
  have hnonneg : 0 ≤ highConductorVaughanTypeIMean N Q C R R := by
    unfold highConductorVaughanTypeIMean apNormalizedPrimitiveMeanOn
    exact Finset.sum_nonneg fun d hd => mul_nonneg (inv_nonneg.mpr (by positivity))
      (Finset.sum_nonneg fun ψ hψ => primitivePrefixAmplitude_nonneg _ _ _ _)
  calc
    4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 *
        highConductorVaughanTypeIMean N Q C R R ≤
      (48 * x ^ 2) * (24 * ((N : ℝ) / x ^ (2 * B)) * x ^ (2 * C + 1)) :=
        mul_le_mul houter hmean' hnonneg (by positivity)
    _ = 1152 * (((N : ℝ) / x ^ (2 * B)) * x ^ (2 * C + 3)) := by ring
    _ ≤ 2000 * (N : ℝ) / x ^ A := by
      calc
        _ ≤ 1152 * ((N : ℝ) / x ^ A) := mul_le_mul_of_nonneg_left hscale (by norm_num)
        _ ≤ 2000 * ((N : ℝ) / x ^ A) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ = _ := by ring

theorem eventually_logConductorThreshold_le (A : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      logConductorThreshold N (2 * (A + 50)) ≤
        vaughanSmallCutoff N := by
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    log_pow_le_sqrt_eventually (3 * (2 * (A + 50)))] with N hN hlog
  let x : ℝ := Real.log (N : ℝ)
  let C : ℕ := 2 * (A + 50)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hsqrtSq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hN0
  have hsqrt : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hpow : x ^ (3 * C) ≤ Real.sqrt (N : ℝ) := by
    simpa [x, C] using hlog
  have hcub : (x ^ C) ^ 3 ≤ (N : ℝ) := by
    rw [← pow_mul]
    have heq : C * 3 = 3 * C := by omega
    rw [heq]
    exact hpow.trans hsqrt
  have hrpow : x ^ C ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
    have hcub' : (x ^ C) ^ (3 : ℝ) ≤ (N : ℝ) := by
      simpa [Real.rpow_natCast] using hcub
    have h := (Real.le_rpow_inv_iff_of_pos
      (pow_nonneg hx0 C) hN0 (by norm_num : (0 : ℝ) < 3)).2 hcub'
    simpa [one_div] using h
  unfold logConductorThreshold vaughanSmallCutoff
  exact Nat.floor_mono (by simpa [x, C] using hrpow)

/-- The small part `n ≤ v` with `v = R` contributes `O(N / (log N)^A)`, by the bound
for its square sum and Cauchy–Schwarz over the conductors `R < d ≤ Q`. -/
theorem highConductorBound_small (A : ℕ) :
    let B := 3 * A + 200
    let C := 2 * (A + 50)
    let v : ℕ → ℕ := fun N => logConductorThreshold N C
    ∃ K : ℝ, 0 < K ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let Q := BombieriVinogradov.modulusCutoff N (B : ℝ)
        let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
        P * highConductorVaughanSmallMean N Q C (v N) ≤
          K * (N : ℝ) / Real.log N ^ A := by
  dsimp only
  let B : ℕ := 3 * A + 200
  let C : ℕ := 2 * (A + 50)
  let v : ℕ → ℕ := fun N => logConductorThreshold N C
  have hv : ∀ᶠ N : ℕ in Filter.atTop,
      v N ≤ vaughanSmallCutoff N := by
    simpa [v, C] using eventually_logConductorThreshold_le A
  obtain ⟨K₀, hK₀, hsmallK⟩ :=
    smallPart_weightedSquareSum_le_sq' v hv A 0 B C
  refine ⟨K₀, hK₀, ?_⟩
  filter_upwards [hsmallK, eventually_ge_atTop (9 : ℕ)] with N hsmallE hN9
  dsimp only at hsmallE ⊢
  let Q := BombieriVinogradov.modulusCutoff N (B : ℝ)
  let R := logConductorThreshold N C
  let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
  have hR : 0 < R := by
    dsimp [R, logConductorThreshold]
    have hlog : 1 < Real.log (N : ℝ) := by
      have h9 : Real.exp 1 < (9 : ℝ) := by
        nlinarith [Real.exp_one_lt_d9]
      exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
        (h9.trans_le (by exact_mod_cast hN9))
    have hpow : 1 < Real.log (N : ℝ) ^ C := by
      have hC : 0 < C := by dsimp [C]; omega
      exact one_lt_pow₀ hlog hC.ne'
    exact Nat.floor_pos.mpr hpow.le
  have hsmall : P * highConductorVaughanSmallMean N Q C (v N) ≤
      K₀ * ((N : ℝ) / Real.log N ^ A) := by
    apply apNormalizedPrimitiveMeanOn_high_le_of_sq
      _ N Q C P _ hR (by positivity)
    simpa only [Nat.add_zero] using hsmallE
  calc
    P * highConductorVaughanSmallMean N Q C (v N) ≤
        K₀ * ((N : ℝ) / Real.log N ^ A) := hsmall
    _ = K₀ * (N : ℝ) / Real.log N ^ A := by ring

/-- The high-conductor bound with chosen exponents holds, with `B = 3A + 200`,
`C = 2(A + 50)` and `u = v = ⌊(log N)^C⌋`. -/
theorem highConductorBound :
    HighConductorBound := by
  intro A
  obtain ⟨K₁, hK₁, hI⟩ := highConductorBound_typeI A
  obtain ⟨K₂, hK₂, hII⟩ := highConductorBound_typeII A
  obtain ⟨K₀, hK₀, hsmall⟩ := highConductorBound_small A
  let B : ℕ := 3 * A + 200
  let C : ℕ := 2 * (A + 50)
  let u : ℕ → ℕ := fun N => logConductorThreshold N C
  let v : ℕ → ℕ := fun N => logConductorThreshold N C
  refine ⟨B, C, by dsimp [B]; omega, u, v, K₁ + K₂ + K₀, by positivity, ?_⟩
  filter_upwards [hI, hII, hsmall] with N hIN hIIN hsmallN
  dsimp only at hIN hIIN hsmallN ⊢
  let Q := BombieriVinogradov.modulusCutoff N (B : ℝ)
  let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
  have hI' : P * highConductorVaughanTypeIMean N Q C (u N) (v N) ≤
      K₁ * (N : ℝ) / Real.log N ^ A := by
    simpa only [P, Q, B, C, u, v] using hIN
  have hII' : P * highConductorVaughanTypeIIMean N Q C (u N) (v N) ≤
      K₂ * (N : ℝ) / Real.log N ^ A := by
    simpa only [P, Q, B, C, u, v] using hIIN
  have hsmall' : P * highConductorVaughanSmallMean N Q C (v N) ≤
      K₀ * (N : ℝ) / Real.log N ^ A := by
    simpa only [P, Q, B, C, v] using hsmallN
  calc
    P * (highConductorVaughanTypeIMean N Q C (u N) (v N) +
        highConductorVaughanTypeIIMean N Q C (u N) (v N) +
        highConductorVaughanSmallMean N Q C (v N)) =
      P * highConductorVaughanTypeIMean N Q C (u N) (v N) +
        P * highConductorVaughanTypeIIMean N Q C (u N) (v N) +
        P * highConductorVaughanSmallMean N Q C (v N) := by ring
    _ ≤ K₁ * (N : ℝ) / Real.log N ^ A +
        K₂ * (N : ℝ) / Real.log N ^ A +
        K₀ * (N : ℝ) / Real.log N ^ A := add_le_add (add_le_add hI' hII') hsmall'
    _ = (K₁ + K₂ + K₀) * (N : ℝ) / Real.log N ^ A := by ring

end

end BombieriVinogradov
