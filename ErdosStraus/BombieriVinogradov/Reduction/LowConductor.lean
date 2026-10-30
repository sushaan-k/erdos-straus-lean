import ErdosStraus.BombieriVinogradov.Vaughan.HighConductor

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

namespace BombieriVinogradov

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology
noncomputable section

/-!
# Bombieri–Vinogradov from the Siegel–Walfisz theorem

Let `R = ⌊(log N)^C⌋`. If every nonprincipal primitive character `ψ` of conductor
`2 ≤ d ≤ R` satisfies `max_{y ≤ N} |∑_{n ≤ y} Λ(n) ψ(n)| ≪_D N / (log N)^D`, then the
conductors `d ≤ R` and the modulus-one terms contribute `O(N / (log N)^A)` to the
Bombieri–Vinogradov sum: the weights over these conductors total `O((log N)^(C+2))`,
and the modulus-one terms are bounded by the prime number theorem. With the bound for
the conductors `d > R`, this proves the Bombieri–Vinogradov theorem from the
Siegel–Walfisz bound.
-/

/-- The Siegel–Walfisz bound for primitive characters of small conductor: for all `C`
and `D` there is `K` such that, for large `N`, every nonprincipal primitive character
`ψ` of conductor `2 ≤ d ≤ ⌊(log N)^C⌋` has
`max_{y ≤ N} |∑_{n ≤ y} Λ(n) ψ(n)| ≤ K N / (log N)^D`. For `d ≥ 2` a primitive
character is automatically nonprincipal. -/
def PrimitiveSiegelWalfisz : Prop :=
  ∀ C D : ℕ, ∃ K : ℝ, 0 < K ∧
    ∀ᶠ N : ℕ in Filter.atTop, 2 ≤ N →
      ∀ d ∈ Finset.Icc 2 (logConductorThreshold N C),
        ∀ ψ : PrimitiveCharacter d, ψ.1 ≠ 1 →
          primitivePrefixAmplitude vonMangoldtIntegerCoeff N d ψ ≤
            K * (N : ℝ) / Real.log (N : ℝ) ^ D

lemma primitiveCharacter_ne_one_of_two_le
    {d : ℕ} (hd : 2 ≤ d) (ψ : PrimitiveCharacter d) : ψ.1 ≠ 1 := by
  let : NeZero d := ⟨by omega⟩
  intro h
  have hc : ψ.1.conductor = 1 := by rw [h, DirichletCharacter.conductor_one]
  rw [primitive_conductor ψ] at hc
  omega

/-- The weights of the low conductors satisfy
`∑_{2 ≤ d ≤ min(Q, R)} #{ψ primitive mod d} ∑_{q ≤ Q, d ∣ q} 1/φ(q) ≤ R H_Q²`,
where `R = ⌊(log N)^C⌋` and `H_Q = ∑_{e ≤ Q} 1/e`. -/
theorem lowConductorArithmeticMass_le_explicit (N Q C : ℕ) :
    lowConductorArithmeticMass N Q C ≤
      (logConductorThreshold N C : ℝ) * conductorHarmonicFactor Q ^ 2 := by
  unfold lowConductorArithmeticMass
  have hterm : ∀ d ∈ lowConductorSet N Q C,
      directConductorWeight Q d * Fintype.card (PrimitiveCharacter d) ≤
        conductorHarmonicFactor Q ^ 2 := by
    intro d hd
    have hd2 : 2 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
    have hφ : (0 : ℝ) < d.totient := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < d)
    have hcard : (Fintype.card (PrimitiveCharacter d) : ℝ) ≤ d.totient := by
      exact_mod_cast card_primitiveCharacter_le_totient d (by omega : 0 < d)
    calc
      directConductorWeight Q d * Fintype.card (PrimitiveCharacter d) ≤
          (conductorHarmonicFactor Q ^ 2 / (d.totient : ℝ)) *
            Fintype.card (PrimitiveCharacter d) := by
              gcongr
              exact directConductorWeight_le Q d
      _ ≤ conductorHarmonicFactor Q ^ 2 := by
        rw [div_mul_eq_mul_div]
        exact (div_le_iff₀ hφ).2 (by
          nlinarith [sq_nonneg (conductorHarmonicFactor Q)])
  calc
    (∑ d ∈ lowConductorSet N Q C,
      directConductorWeight Q d * Fintype.card (PrimitiveCharacter d)) ≤
        ∑ _d ∈ lowConductorSet N Q C, conductorHarmonicFactor Q ^ 2 :=
          Finset.sum_le_sum hterm
    _ = (lowConductorSet N Q C).card * conductorHarmonicFactor Q ^ 2 := by simp
    _ ≤ (logConductorThreshold N C : ℝ) * conductorHarmonicFactor Q ^ 2 := by
      gcongr
      refine (Finset.card_le_card (show lowConductorSet N Q C ⊆
        Finset.Icc 1 (logConductorThreshold N C) from ?_)).trans ?_
      · intro d hd
        rcases Finset.mem_filter.mp hd with ⟨hdI, hdR⟩
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hdI).1.trans' (by omega), hdR⟩
      · simp

private lemma one_le_log_of_eight_le {N : ℕ} (hN : 8 ≤ N) :
    1 ≤ Real.log (N : ℝ) := by
  have h8 : (1 : ℝ) < Real.log 8 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
    nlinarith [Real.log_two_gt_d9]
  exact h8.le.trans (Real.strictMonoOn_log.monotoneOn
    (show (8 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (N : ℝ) ∈ Set.Ioi 0 by
      change 0 < (N : ℝ)
      exact_mod_cast (by omega : 0 < N)) (by exact_mod_cast hN))

private lemma principalLambdaPrefixMaxError_one_nonneg (N : ℕ) :
    0 ≤ principalLambdaPrefixMaxError N 1 := by
  unfold principalLambdaPrefixMaxError
  exact (norm_nonneg (principalLambdaMainError 0 1)).trans
    (Finset.le_max'
      ((Finset.range (N + 1)).image (fun y => ‖principalLambdaMainError y 1‖)) _
      (Finset.mem_image.mpr
        ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ N), rfl⟩))

private lemma liDiscretePrefixMaxError_nonneg (N : ℕ) :
    0 ≤ liDiscretePrefixMaxError N := by
  unfold liDiscretePrefixMaxError
  have hli0 : 0 ≤ liDiscreteError 0 := by
    unfold liDiscreteError
    exact abs_nonneg _
  exact hli0.trans
    (Finset.le_max'
      ((Finset.range (N + 1)).image liDiscreteError) _
      (Finset.mem_image.mpr
        ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ N), rfl⟩))

/-- The modulus-one terms, weighted by `1/φ(q)` and summed over `q ≤ Q`, are at most
`H_Q²` times their value at `q = 1`, since `∑_{q ≤ Q} 1/φ(q) ≤ H_Q²`. -/
theorem principalGlobal_add_chebyshevToLi_le_qOne
    (N Q : ℕ) :
    discreteAbelAmplifierPrefixMax N * principalGlobalPhysical N Q +
        chebyshevToLiPhysical N Q ≤
      conductorHarmonicFactor Q ^ 2 * globalPartialSummationError N := by
  unfold principalGlobalPhysical chebyshevToLiPhysical globalPartialSummationError
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hsum := sum_inv_totient_le_harmonic_sq Q
  have hprincipal := principalLambdaPrefixMaxError_one_nonneg N
  have hcheb := liDiscretePrefixMaxError_nonneg N
  have habel := discreteAbelAmplifierPrefixMax_nonneg N
  nlinarith [mul_nonneg habel hprincipal]

private theorem modulusCutoff_le_self_eventually (B : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      BombieriVinogradov.modulusCutoff N (B : ℝ) ≤ N := by
  filter_upwards [eventually_ge_atTop (8 : ℕ)] with N hN
  have hlog : 1 ≤ Real.log (N : ℝ) := one_le_log_of_eight_le hN
  have hden : 1 ≤ Real.log (N : ℝ) ^ (B : ℝ) :=
    Real.one_le_rpow hlog (by positivity)
  have hsqrt : Real.sqrt (N : ℝ) ≤ N := by
    have h1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    exact (Real.sqrt_le_iff).2 ⟨by positivity, by nlinarith⟩
  unfold BombieriVinogradov.modulusCutoff
  apply Nat.floor_le_of_le
  calc
    (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ (B : ℝ) ≤
        (N : ℝ) ^ (1 / 2 : ℝ) := div_le_self (Real.rpow_nonneg (by positivity) _) hden
    _ = Real.sqrt (N : ℝ) := by rw [Real.sqrt_eq_rpow]
    _ ≤ N := hsqrt

private theorem low_scalar_envelopes (C B : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      let Q := BombieriVinogradov.modulusCutoff N (B : ℝ)
      lowConductorArithmeticMass N Q C ≤ 4 * Real.log N ^ (C + 2) ∧
      conductorHarmonicFactor Q ^ 2 ≤ 4 * Real.log N ^ 2 := by
  filter_upwards [modulusCutoff_le_self_eventually B,
    eventually_ge_atTop (8 : ℕ)] with N hQN hN
  let Q := BombieriVinogradov.modulusCutoff N (B : ℝ)
  have hlog : 1 ≤ Real.log (N : ℝ) := one_le_log_of_eight_le hN
  have hlogQ : Real.log (Q : ℝ) ≤ Real.log (N : ℝ) := by
    by_cases hQ : Q = 0
    · rw [hQ, Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg
        (show (1 : ℝ) ≤ N by exact_mod_cast (by omega : 1 ≤ N))
    · exact Real.log_le_log (by positivity) (by exact_mod_cast hQN)
  have hH : conductorHarmonicFactor Q ≤ 2 * Real.log N :=
    (conductorHarmonicFactor_le Q).trans (by linarith)
  have hH0 := conductorHarmonicFactor_nonneg Q
  have hR : (logConductorThreshold N C : ℝ) ≤ Real.log N ^ C := by
    unfold logConductorThreshold
    exact_mod_cast Nat.floor_le (pow_nonneg (by positivity) C)
  have hpow0 : 0 ≤ Real.log N ^ C := pow_nonneg (by positivity) C
  constructor
  · refine (lowConductorArithmeticMass_le_explicit N Q C).trans ?_
    calc
      (logConductorThreshold N C : ℝ) * conductorHarmonicFactor Q ^ 2 ≤
          Real.log N ^ C * (2 * Real.log N) ^ 2 := by gcongr
      _ = 4 * Real.log N ^ (C + 2) := by rw [pow_add]; ring
  · nlinarith

/-- The Siegel–Walfisz bound for primitive characters of small conductor and the prime
number theorem bound for the modulus-one terms give the bound for small conductors:
the low-conductor and modulus-one terms are `O(N / (log N)^A)` for every `A`. -/
theorem lowConductorBound_of_siegelWalfisz
    (hSW : PrimitiveSiegelWalfisz)
    (hPNT : GlobalPartialSummationBound) :
    LowConductorBound := by
  intro A C B
  obtain ⟨KS, hKS, hSN⟩ := hSW C (A + C + 5)
  obtain ⟨KP, hKP, hPN⟩ := hPNT (A + 3) (by positivity)
  refine ⟨32 * KS + 4 * KP, by positivity, ?_⟩
  filter_upwards [hSN, hPN, low_scalar_envelopes C B,
    eventually_ge_atTop (8 : ℕ)] with N hS hP henv hN
  dsimp only at henv ⊢
  let Q := BombieriVinogradov.modulusCutoff N (B : ℝ)
  have hlog : 1 ≤ Real.log (N : ℝ) := one_le_log_of_eight_le hN
  have hlog0 : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  have hX0 : 0 ≤ KS * (N : ℝ) / Real.log N ^ (A + C + 5) := by positivity
  have hlowPoint : ∀ d ∈ lowConductorSet N Q C, ∀ ψ : PrimitiveCharacter d,
      primitivePrefixAmplitude vonMangoldtIntegerCoeff N d ψ ≤
        KS * (N : ℝ) / Real.log N ^ (A + C + 5) := by
    intro d hd ψ
    apply hS (by omega) d
    · exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1,
        (Finset.mem_filter.mp hd).2⟩
    · exact primitiveCharacter_ne_one_of_two_le
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1 ψ
  have hlow := lowConductorPhysical_le_of_primitivePrefix N Q C _ hX0 hlowPoint
  have hglobal := principalGlobal_add_chebyshevToLi_le_qOne N Q
  have hP' : globalPartialSummationError N ≤
      KP * (N : ℝ) / Real.log N ^ (A + 3) := by
    convert hP (by omega) using 1
    rw [← Real.rpow_natCast]
    norm_num
  have hglobal0 : 0 ≤ globalPartialSummationError N := by
    exact add_nonneg
      (mul_nonneg (discreteAbelAmplifierPrefixMax_nonneg N)
        (principalLambdaPrefixMaxError_one_nonneg N))
      (liDiscretePrefixMaxError_nonneg N)
  have habel4 : discreteAbelAmplifierPrefixMax N ≤ 4 := by
    refine (discreteAbelAmplifierPrefixMax_le_two_inv_log_two N).trans ?_
    have hlt : (1 / 2 : ℝ) < Real.log 2 := Real.log_two_gt_d9.trans' (by norm_num)
    have hinv : (Real.log 2)⁻¹ < 2 := by
      rw [inv_eq_one_div, one_div_lt (Real.log_pos (by norm_num)) (by norm_num)]
      norm_num
      exact hlt
    linarith
  have hlowPay :
      2 * discreteAbelAmplifierPrefixMax N * lowConductorPhysical N Q C ≤
        32 * KS * (N : ℝ) / Real.log N ^ A := by
    have hlow0 : 0 ≤ lowConductorPhysical N Q C := by
      unfold lowConductorPhysical directConductorMeanOn
      apply Finset.sum_nonneg
      intro d hd
      apply mul_nonneg
      · unfold directConductorWeight
        positivity
      · exact Finset.sum_nonneg fun ψ _ =>
          primitivePrefixAmplitude_nonneg vonMangoldtIntegerCoeff N d ψ
    calc
      _ ≤ 2 * 4 * lowConductorPhysical N Q C := by gcongr
      _ ≤ 2 * 4 *
          (4 * Real.log N ^ (C + 2) *
            (KS * (N : ℝ) / Real.log N ^ (A + C + 5))) := by
              gcongr
              exact hlow.trans (mul_le_mul_of_nonneg_right henv.1 hX0)
      _ ≤ 32 * KS * (N : ℝ) / Real.log N ^ A := by
        rw [pow_add, pow_add]
        field_simp
        have hpowAC : 0 ≤ Real.log (N : ℝ) ^ (A + C) := by positivity
        have hlog3 : 1 ≤ Real.log (N : ℝ) ^ 3 := by
          exact one_le_pow₀ hlog
        have hpowmul : Real.log (N : ℝ) ^ C * Real.log (N : ℝ) ^ A =
            Real.log (N : ℝ) ^ (A + C) := by
          rw [← pow_add]
          congr 1
          omega
        calc
          2 * 4 ^ 2 * Real.log (N : ℝ) ^ C * Real.log (N : ℝ) ^ A =
              32 * (Real.log (N : ℝ) ^ C * Real.log (N : ℝ) ^ A) := by ring
          _ = 32 * Real.log (N : ℝ) ^ (A + C) := by rw [hpowmul]
          _ ≤ 32 * (Real.log (N : ℝ) ^ 3 * Real.log (N : ℝ) ^ (A + C)) := by
            have hh : Real.log (N : ℝ) ^ (A + C) ≤
                Real.log (N : ℝ) ^ 3 * Real.log (N : ℝ) ^ (A + C) := by
              simpa using mul_le_mul_of_nonneg_right hlog3 hpowAC
            exact mul_le_mul_of_nonneg_left hh (by norm_num)
          _ = Real.log (N : ℝ) ^ 3 * Real.log (N : ℝ) ^ (A + C) * 32 := by ring
  have hglobalPay :
      discreteAbelAmplifierPrefixMax N * principalGlobalPhysical N Q +
          chebyshevToLiPhysical N Q ≤
        4 * KP * (N : ℝ) / Real.log N ^ A := by
    calc
      _ ≤ conductorHarmonicFactor Q ^ 2 * globalPartialSummationError N := hglobal
      _ ≤ (4 * Real.log N ^ 2) *
          (KP * (N : ℝ) / Real.log N ^ (A + 3)) := by
            exact mul_le_mul henv.2 hP' hglobal0 (by positivity)
      _ ≤ 4 * KP * (N : ℝ) / Real.log N ^ A := by
        rw [pow_add]
        field_simp
        exact hlog
  change 2 * discreteAbelAmplifierPrefixMax N * lowConductorPhysical N Q C +
      discreteAbelAmplifierPrefixMax N * principalGlobalPhysical N Q +
      chebyshevToLiPhysical N Q ≤ _
  calc
    _ = (2 * discreteAbelAmplifierPrefixMax N * lowConductorPhysical N Q C) +
        (discreteAbelAmplifierPrefixMax N * principalGlobalPhysical N Q +
          chebyshevToLiPhysical N Q) := by ring
    _ ≤ 32 * KS * (N : ℝ) / Real.log N ^ A +
        4 * KP * (N : ℝ) / Real.log N ^ A := add_le_add hlowPay hglobalPay
    _ = (32 * KS + 4 * KP) * (N : ℝ) / Real.log N ^ A := by ring

/-! ## Bounds at each endpoint `y ≤ N` -/

/-- A bound `B` for `|∑_{1 ≤ n ≤ y} a(n) ψ(n)|` at every `y ≤ N` bounds the maximum
over `y ≤ N`. The empty sum at `y = 0` gives `B ≥ 0`. -/
theorem primitivePrefixAmplitude_le_of_pointwise_integerPrefix
    (a : ℤ → ℂ) (N q : ℕ) (ψ : PrimitiveCharacter q) (B : ℝ)
    (hpointwise : ∀ y : ℕ, y ≤ N →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) (y : ℤ),
        a n * ψ.1 (n : ZMod q)‖ ≤ B) :
    primitivePrefixAmplitude a N q ψ ≤ B := by
  have hB : 0 ≤ B := by
    have h0 := hpointwise 0 (Nat.zero_le N)
    simpa using h0
  have hmax : primitiveCharacterPrefixMaxSquare a 0 N q ψ ≤ B ^ 2 := by
    unfold primitiveCharacterPrefixMaxSquare
    apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
    have hyN : y ≤ N := by
      simpa [Finset.mem_range] using hy
    unfold primitiveCharacterPrefixSquare
    simp only [zero_add]
    exact pow_le_pow_left₀ (norm_nonneg _) (hpointwise y hyN) 2
  exact (sq_le_sq₀ (primitivePrefixAmplitude_nonneg a N q ψ) hB).mp
    ((primitivePrefixAmplitude_sq a N q ψ).trans_le hmax)

/-- The case `a = Λ`, with the sums `∑_{n ≤ y} Λ(n) ψ(n)` taken over the natural
numbers; they agree with the sums over `[1, y] ⊆ ℤ` since `Λ(0) = 0`. -/
theorem primitivePrefixAmplitude_vonMangoldt_le
    (N q : ℕ) (ψ : PrimitiveCharacter q) (B : ℝ)
    (hpointwise : ∀ y : ℕ, y ≤ N →
      ‖lambdaCharacterPrefix y q ψ.1‖ ≤ B) :
    primitivePrefixAmplitude vonMangoldtIntegerCoeff N q ψ ≤ B := by
  apply primitivePrefixAmplitude_le_of_pointwise_integerPrefix
  intro y hy
  rw [← lambdaCharacterPrefix_eq_integerInterval]
  exact hpointwise y hy

/-- The Siegel–Walfisz bound for primitive characters of small conductor follows from
the bound `|∑_{n ≤ y} Λ(n) ψ(n)| ≤ K N / (log N)^D` at each `y ≤ N`. -/
theorem primitiveSiegelWalfisz_of_pointwise
    (hpointwise :
      ∀ C D : ℕ, ∃ K : ℝ, 0 < K ∧
        ∀ᶠ N : ℕ in Filter.atTop, 2 ≤ N →
          ∀ d ∈ Finset.Icc 2 (logConductorThreshold N C),
            ∀ ψ : PrimitiveCharacter d, ψ.1 ≠ 1 →
              ∀ y : ℕ, y ≤ N →
                ‖lambdaCharacterPrefix y d ψ.1‖ ≤
                  K * (N : ℝ) / Real.log (N : ℝ) ^ D) :
    PrimitiveSiegelWalfisz := by
  intro C D
  obtain ⟨K, hK, hN⟩ := hpointwise C D
  refine ⟨K, hK, ?_⟩
  filter_upwards [hN] with N hN
  intro hN2 d hd ψ hψ
  exact primitivePrefixAmplitude_vonMangoldt_le
    N d ψ (K * (N : ℝ) / Real.log (N : ℝ) ^ D)
    (hN hN2 d hd ψ hψ)

/-! ## The Bombieri–Vinogradov theorem -/

/-- The bound for small conductors implies the Bombieri–Vinogradov theorem, since the
conductors `d > ⌊(log N)^C⌋` are handled by `highConductorBound`. -/
theorem standard_form_of_lowConductorBound
    (hlow : LowConductorBound) :
    BombieriVinogradov.StandardForm := by
  have hnat := sum_primeAPPrefixMaxError_le_of_low_high
    hlow highConductorBound
  intro A hA
  let An : ℕ := Nat.ceil A
  obtain ⟨B, K, hK, hN⟩ := hnat An
  refine ⟨(B : ℝ), by positivity, K, hK, ?_⟩
  filter_upwards [hN, eventually_ge_atTop (3 : ℕ)] with N hBN hN3
  intro _hN2
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    exact ((Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
      (Real.exp_one_lt_three.trans_le (by exact_mod_cast hN3))).le
  have hAceil : A ≤ (An : ℝ) := Nat.le_ceil A
  have hpow : Real.log (N : ℝ) ^ A ≤ Real.log (N : ℝ) ^ An := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hlog hAceil
  -- Pass from the exponent `⌈A⌉` to `A`, using `(log N)^A ≤ (log N)^⌈A⌉`.
  calc
    _ ≤ K * (N : ℝ) / Real.log (N : ℝ) ^ An := hBN
    _ ≤ K * (N : ℝ) / Real.log (N : ℝ) ^ A :=
      div_le_div_of_nonneg_left (mul_nonneg hK.le (by positivity))
        (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hlog) A) hpow

/-- The Siegel–Walfisz bound for primitive characters of small conductor and the prime
number theorem bound for the modulus-one terms imply the Bombieri–Vinogradov theorem. -/
theorem standard_form_of_nonprincipalPrimitivePsi_lowOnly
    (hSW : PrimitiveSiegelWalfisz)
    (hPNT : GlobalPartialSummationBound) :
    BombieriVinogradov.StandardForm := by
  exact standard_form_of_lowConductorBound
    (lowConductorBound_of_siegelWalfisz hSW hPNT)

end

end BombieriVinogradov

namespace BombieriVinogradov

/-- The Siegel–Walfisz bound for nonprincipal primitive characters of conductor at most
`(log N)^C` implies the Bombieri–Vinogradov theorem; the modulus-one terms are bounded
by the prime number theorem. -/
theorem standard_form_of_nonprincipalPrimitivePsi
    (hSW : PrimitiveSiegelWalfisz) :
    BombieriVinogradov.StandardForm :=
  standard_form_of_nonprincipalPrimitivePsi_lowOnly
    hSW globalPartialSummationBound

end BombieriVinogradov
