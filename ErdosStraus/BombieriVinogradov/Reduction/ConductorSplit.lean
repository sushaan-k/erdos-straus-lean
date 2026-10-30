import ErdosStraus.BombieriVinogradov.Reduction.PrincipalCharacter

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

/-!
# Bombieri–Vinogradov by primitive conductor

By character orthogonality and partial summation against `1/log n`, the sum
`∑_{q ≤ Q} max_{y ≤ N} max_{(a,q)=1} |π(y;q,a) - li(y)/φ(q)|` is bounded by sums of
`max_{y ≤ N} |∑_{n ≤ y} Λ(n) ψ(n)|` over primitive characters `ψ`, split at the
conductor `R = ⌊(log N)^C⌋`, plus elementary terms of size `O(Q √N (log N)³)`.
The main result `bvSum_le_of_conductor_bounds` gives the bound `≪ N / (log N)^A`
from two inputs: the prime number theorem with a Siegel–Walfisz bound for
conductors `d ≤ R`, and a bound for Vaughan's decomposition over conductors `d > R`.
The file ends with a dyadic decomposition of the conductors `d > R`.
-/

namespace BombieriVinogradov

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology
noncomputable section

/-- The conductor threshold `R = ⌊(log N)^C⌋`. -/
def logConductorThreshold (N C : ℕ) : ℕ :=
  Nat.floor (Real.log (N : ℝ) ^ C)

/-- The low conductors `2 ≤ d ≤ Q` with `d ≤ R`. -/
def lowConductorSet (N Q C : ℕ) : Finset ℕ :=
  (Finset.Icc 2 Q).filter fun d => d ≤ logConductorThreshold N C

/-- The high conductors `2 ≤ d ≤ Q` with `d > R`. -/
def highConductorSet (N Q C : ℕ) : Finset ℕ :=
  (Finset.Icc 2 Q).filter fun d => logConductorThreshold N C < d

lemma lowConductorSet_disjoint_highConductorSet (N Q C : ℕ) :
    Disjoint (lowConductorSet N Q C) (highConductorSet N Q C) := by
  apply Finset.disjoint_left.2
  intro d hdL hdH
  simp only [lowConductorSet, highConductorSet, Finset.mem_filter] at hdL hdH
  omega

lemma lowConductorSet_union_highConductorSet (N Q C : ℕ) :
    lowConductorSet N Q C ∪ highConductorSet N Q C = Finset.Icc 2 Q := by
  ext d
  simp only [lowConductorSet, highConductorSet, Finset.mem_union,
    Finset.mem_filter]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro h
    by_cases hd : d ≤ logConductorThreshold N C
    · exact Or.inl ⟨h, hd⟩
    · exact Or.inr ⟨h, by omega⟩

/-- `∑_{d ∈ S} w_Q(d) ∑_ψ max_{y ≤ N} |∑_{n ≤ y} a(n) ψ(n)|`, where `ψ` runs over the
primitive characters mod `d` and `w_Q(d) = ∑_{q ≤ Q, d ∣ q} 1/φ(q)`. -/
def directConductorMeanOn (a : ℤ → ℂ) (N Q : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ d ∈ S, directConductorWeight Q d *
    ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ

/-- The conductor sum for `Λ` over the low conductors. -/
def lowConductorPhysical (N Q C : ℕ) : ℝ :=
  directConductorMeanOn vonMangoldtIntegerCoeff N Q (lowConductorSet N Q C)

/-- The conductor sum for `Λ` over the high conductors. -/
def highConductorPhysical (N Q C : ℕ) : ℝ :=
  directConductorMeanOn vonMangoldtIntegerCoeff N Q (highConductorSet N Q C)

/-- The conductor sum over `2 ≤ d ≤ Q` is the sum of its low and high parts. -/
theorem directConductorMean_low_high (a : ℤ → ℂ) (N Q C : ℕ) :
    (∑ d ∈ Finset.Icc 2 Q, directConductorWeight Q d *
      ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ) =
      directConductorMeanOn a N Q (lowConductorSet N Q C) +
        directConductorMeanOn a N Q (highConductorSet N Q C) := by
  unfold directConductorMeanOn
  rw [← Finset.sum_union (lowConductorSet_disjoint_highConductorSet N Q C)]
  rw [lowConductorSet_union_highConductorSet]

/-- `∑ w_Q(d) · #{ψ primitive mod d}` over the low conductors `d`. -/
def lowConductorArithmeticMass (N Q C : ℕ) : ℝ :=
  ∑ d ∈ lowConductorSet N Q C,
    directConductorWeight Q d * Fintype.card (PrimitiveCharacter d)

/-- A pointwise bound `X` for the primitive character sums of `Λ` at low conductors
bounds the low-conductor sum by `X` times `lowConductorArithmeticMass`. -/
theorem lowConductorPhysical_le_of_primitivePrefix
    (N Q C : ℕ) (X : ℝ)
    (_hX : 0 ≤ X)
    (hSW : ∀ d ∈ lowConductorSet N Q C,
      ∀ ψ : PrimitiveCharacter d,
        primitivePrefixAmplitude vonMangoldtIntegerCoeff N d ψ ≤ X) :
    lowConductorPhysical N Q C ≤ lowConductorArithmeticMass N Q C * X := by
  unfold lowConductorPhysical directConductorMeanOn lowConductorArithmeticMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro d hd
  have hw : 0 ≤ directConductorWeight Q d := by
    unfold directConductorWeight
    exact Finset.sum_nonneg fun _ _ => by positivity
  calc
    directConductorWeight Q d *
        (∑ ψ : PrimitiveCharacter d,
          primitivePrefixAmplitude vonMangoldtIntegerCoeff N d ψ) ≤
        directConductorWeight Q d *
          (∑ _ψ : PrimitiveCharacter d, X) := by
            exact mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum fun ψ _ => hSW d hd ψ) hw
    _ = (directConductorWeight Q d *
          Fintype.card (PrimitiveCharacter d)) * X := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
            ring

/-- `∑_{d ∈ S} φ(d)⁻¹ ∑_ψ max_{y ≤ N} |∑_{n ≤ y} a(n) ψ(n)|`, with `ψ` primitive
mod `d`. -/
def apNormalizedPrimitiveMeanOn
    (a : ℤ → ℂ) (N : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ d ∈ S, ((d.totient : ℝ)⁻¹) *
    ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ

/-- `∑_{d ∈ S} (d/φ(d)) ∑_ψ max_{y ≤ N} |∑_{n ≤ y} a(n) ψ(n)|²`, with `ψ` primitive
mod `d`; this is the sum controlled by the large sieve. -/
def primitivePrefixSquareSumOn
    (a : ℤ → ℂ) (N : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ d ∈ S, ((d : ℝ) / (d.totient : ℝ)) *
    ∑ ψ : PrimitiveCharacter d,
      primitiveCharacterPrefixMaxSquare a 0 N d ψ

/-- The harmonic tail `∑_{R < d ≤ Q} 1/d`. -/
def highConductorHarmonicFactor (Q R : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc (R + 1) Q, ((d : ℝ)⁻¹)

/-- Cauchy–Schwarz with weights `1/d` over `R < d ≤ Q`. Removing the conductors
`d ≤ R` only shortens the harmonic sum `∑ 1/d`; it does not give a factor `R⁻¹`. -/
theorem apNormalizedPrimitiveMeanOn_high_sq_le
    (a : ℤ → ℂ) (N Q R : ℕ)
    (hcard : ∀ d ∈ Finset.Icc (R + 1) Q,
      Fintype.card (PrimitiveCharacter d) ≤ d.totient) :
    apNormalizedPrimitiveMeanOn a N (Finset.Icc (R + 1) Q) ^ 2 ≤
      highConductorHarmonicFactor Q R *
        primitivePrefixSquareSumOn a N (Finset.Icc (R + 1) Q) := by
  let T : ℕ → ℝ := fun d => ((d.totient : ℝ)⁻¹) *
    ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ
  let B : ℕ → ℝ := fun d => ((d : ℝ) / (d.totient : ℝ)) *
    ∑ ψ : PrimitiveCharacter d,
      primitiveCharacterPrefixMaxSquare a 0 N d ψ
  have hTB (d : ℕ) (hd : d ∈ Finset.Icc (R + 1) Q) :
      (d : ℝ) * T d ^ 2 ≤ B d := by
    have hd0 : 0 < d := by
      have := (Finset.mem_Icc.mp hd).1
      omega
    have hφ : (0 : ℝ) < d.totient := by
      exact_mod_cast Nat.totient_pos.mpr hd0
    let A : PrimitiveCharacter d → ℝ := fun ψ => primitivePrefixAmplitude a N d ψ
    have hs := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (PrimitiveCharacter d))) (f := A)
    have hs' : (∑ ψ : PrimitiveCharacter d, A ψ) ^ 2 ≤
        (d.totient : ℝ) * ∑ ψ : PrimitiveCharacter d, A ψ ^ 2 := by
      refine hs.trans ?_
      gcongr
      exact_mod_cast hcard d hd
    have hamp : (∑ ψ : PrimitiveCharacter d, A ψ ^ 2) =
        ∑ ψ : PrimitiveCharacter d,
          primitiveCharacterPrefixMaxSquare a 0 N d ψ := by
      apply Finset.sum_congr rfl
      intro ψ hψ
      exact primitivePrefixAmplitude_sq a N d ψ
    dsimp [T, B]
    rw [hamp] at hs'
    rw [div_eq_mul_inv]
    field_simp
    nlinarith
  have hsplit : apNormalizedPrimitiveMeanOn a N (Finset.Icc (R + 1) Q) =
      ∑ d ∈ Finset.Icc (R + 1) Q,
        (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ) * T d) := by
    unfold apNormalizedPrimitiveMeanOn
    apply Finset.sum_congr rfl
    intro d hd
    have hd0N : 0 < d := by
      have := (Finset.mem_Icc.mp hd).1
      omega
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd0N
    have hsne : Real.sqrt (d : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hd0
    dsimp [T]
    field_simp
  rw [hsplit]
  refine (Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc (R + 1) Q)
    (fun d => (Real.sqrt (d : ℝ))⁻¹)
    (fun d => Real.sqrt (d : ℝ) * T d)).trans ?_
  have hfirst :
      (∑ d ∈ Finset.Icc (R + 1) Q, (Real.sqrt (d : ℝ))⁻¹ ^ 2) =
        highConductorHarmonicFactor Q R := by
    unfold highConductorHarmonicFactor
    apply Finset.sum_congr rfl
    intro d hd
    rw [inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ d)]
  rw [hfirst]
  apply mul_le_mul_of_nonneg_left
  · unfold primitivePrefixSquareSumOn
    apply Finset.sum_le_sum
    intro d hd
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ d)]
    exact hTB d hd
  · unfold highConductorHarmonicFactor
    positivity

theorem highConductorHarmonicFactor_le (Q R : ℕ) :
    highConductorHarmonicFactor Q R ≤ conductorHarmonicFactor Q := by
  unfold highConductorHarmonicFactor conductorHarmonicFactor
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc_left (by omega)
  · intro d hd hnot
    positivity

/-- The normalized mean over high conductors of the Type I part of Vaughan's
identity for `Λ`. -/
def highConductorVaughanTypeIMean (N Q C u v : ℕ) : ℝ :=
  apNormalizedPrimitiveMeanOn
    (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N
    (highConductorSet N Q C)

/-- The normalized mean over high conductors of the Type II part of Vaughan's
identity for `Λ`. -/
def highConductorVaughanTypeIIMean (N Q C u v : ℕ) : ℝ :=
  apNormalizedPrimitiveMeanOn
    (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N
    (highConductorSet N Q C)

/-- The normalized mean over high conductors of the part `n ≤ v` of Vaughan's
identity for `Λ`. -/
def highConductorVaughanSmallMean (N Q C v : ℕ) : ℝ :=
  apNormalizedPrimitiveMeanOn
    (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N
    (highConductorSet N Q C)

/-- The five terms bounding the Bombieri–Vinogradov sum: nonprincipal characters,
the principal character mod 1, prime powers `p^k` with `p ∣ q`, prime powers
`p^k` with `k ≥ 2`, and the change from the partial summation main term to `li`. -/
structure BVErrorTerms where
  nonprincipal : ℝ
  principal : ℝ
  principalBad : ℝ
  primePower : ℝ
  chebyshevToLi : ℝ

/-- `abel · (nonprincipal + principal + principalBad + primePower) + chebyshevToLi`,
where `abel` is the partial summation factor. -/
def BVErrorTerms.total (P : BVErrorTerms) (abel : ℝ) : ℝ :=
  abel * (P.nonprincipal + P.principal + P.principalBad + P.primePower) +
    P.chebyshevToLi

/-- `∑_{q ≤ Q} φ(q)⁻¹ ∑_{χ ≠ χ₀} max_{y ≤ N} |∑_{n ≤ y} Λ(n) χ(n)|`. -/
def nonprincipalLambdaPhysical (N Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
    ∑ χ ∈ nonprincipalCharacters q,
      lambdaCharacterPrefixMaxAmplitude N q χ

/-- `∑_{q ≤ Q} φ(q)⁻¹ max_{y ≤ N} |ψ(y) - y|`. -/
def principalGlobalPhysical (N Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
    principalLambdaPrefixMaxError N 1

/-- `∑_{q ≤ Q} φ(q)⁻¹ log₂ q (log₂ N + 1) log N`, which bounds the contribution of
the prime powers `p^k ≤ N` with `p ∣ q`. -/
def principalBadPhysical (N Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
    ((Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ))

/-- `∑_{q ≤ Q} max_{y ≤ N} max_{(a,q)=1} |ψ(y;q,a) - θ(y;q,a)|`. -/
def primePowerPhysical (N Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, lambdaPrimePowerCorrectionPrefixMaxError N q

/-- `∑_{q ≤ Q} φ(q)⁻¹ max_{y ≤ N} |M(y) - li(y)|`, where `M(y)` is the main term `y`
after partial summation against `1/log n`. -/
def chebyshevToLiPhysical (N Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
    liDiscretePrefixMaxError N

/-- The five terms at `N` and `Q`. -/
def bvErrorTerms (N Q : ℕ) : BVErrorTerms where
  nonprincipal := nonprincipalLambdaPhysical N Q
  principal := principalGlobalPhysical N Q
  principalBad := principalBadPhysical N Q
  primePower := primePowerPhysical N Q
  chebyshevToLi := chebyshevToLiPhysical N Q

/-- `∑_{q ≤ Q} max_{y ≤ N} max_{(a,q)=1} |π(y;q,a) - li(y)/φ(q)|` is at most the
total of the five terms. The proof uses only character orthogonality and partial
summation. -/
theorem sum_primeAPPrefixMaxError_le_errorTerms
    (N Q : ℕ) (hN : 2 ≤ N) :
    (∑ q ∈ Finset.Icc 1 Q,
      BombieriVinogradov.primeAPPrefixMaxError N q) ≤
      (bvErrorTerms N Q).total
        (discreteAbelAmplifierPrefixMax N) := by
  have hsplit :
      (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
        (principalLambdaPrefixMaxError N 1 +
          (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) +
          ∑ χ ∈ nonprincipalCharacters q,
            lambdaCharacterPrefixMaxAmplitude N q χ)) =
        nonprincipalLambdaPhysical N Q + principalGlobalPhysical N Q +
          principalBadPhysical N Q := by
    unfold nonprincipalLambdaPhysical principalGlobalPhysical principalBadPhysical
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q,
        (discreteAbelAmplifierPrefixMax N *
          ((q.totient : ℝ)⁻¹ *
              (principalLambdaPrefixMaxError N 1 +
                (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) +
                ∑ χ ∈ nonprincipalCharacters q,
                  lambdaCharacterPrefixMaxAmplitude N q χ) +
            lambdaPrimePowerCorrectionPrefixMaxError N q) +
          (q.totient : ℝ)⁻¹ * liDiscretePrefixMaxError N) := by
          apply Finset.sum_le_sum
          intro q hq
          exact primeAPPrefixMaxError_le_characters_global
            (Finset.mem_Icc.mp hq).1 hN
    _ = (bvErrorTerms N Q).total
        (discreteAbelAmplifierPrefixMax N) := by
          change _ =
            discreteAbelAmplifierPrefixMax N *
                (nonprincipalLambdaPhysical N Q + principalGlobalPhysical N Q +
                  principalBadPhysical N Q + primePowerPhysical N Q) +
              chebyshevToLiPhysical N Q
          unfold primePowerPhysical chebyshevToLiPhysical
          rw [Finset.sum_add_distrib, ← Finset.mul_sum,
            Finset.sum_add_distrib, hsplit]

end

end BombieriVinogradov

namespace BombieriVinogradov

open Filter

theorem log_pow_le_sqrt_eventually (k : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      Real.log (N : ℝ) ^ k ≤ Real.sqrt N := by
  have hR := (Real.isLittleO_pow_log_id_atTop (n := 2 * k)).eventuallyLE
  have hN := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hR
  filter_upwards [hN, eventually_ge_atTop (2 : ℕ)] with N hlog hN2
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ N by omega))
  apply Real.le_sqrt_of_sq_le
  simp only [id, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog0 _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ N)] at hlog
  rw [mul_comm, pow_mul] at hlog
  exact hlog

end BombieriVinogradov

/-! ## From nonprincipal characters to primitive conductors -/

namespace BombieriVinogradov

open Classical Finset
open scoped BigOperators ArithmeticFunction
noncomputable section

/-- The sum over `0 ≤ n ≤ y` equals the sum over the integers `1 ≤ n ≤ y`, since
`Λ(0) = 0`. -/
theorem lambdaCharacterPrefix_eq_integerInterval
    (y q : ℕ) (χ : DirichletCharacter ℂ q) :
    lambdaCharacterPrefix y q χ =
      ∑ n ∈ Finset.Icc (1 : ℤ) (y : ℤ),
        vonMangoldtIntegerCoeff n * χ (n : ZMod q) := by
  have hrange : Finset.range (y + 1) = insert 0 (Finset.Icc 1 y) := by
    ext n
    simp
    omega
  have hnatInt :
      (∑ n ∈ Finset.Icc 1 y, lambdaNatCoeff n * χ (n : ZMod q)) =
        ∑ n ∈ Finset.Icc (1 : ℤ) (y : ℤ),
          vonMangoldtIntegerCoeff n * χ (n : ZMod q) := by
    refine Finset.sum_bij (fun n _ => (n : ℤ)) ?_ ?_ ?_ ?_
    · intro n hn
      have h := Finset.mem_Icc.mp hn
      exact Finset.mem_Icc.mpr ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    · intro a₁ ha₁ a₂ ha₂ h
      exact_mod_cast h
    · intro z hz
      have hz' := Finset.mem_Icc.mp hz
      have hz0 : 0 ≤ z := by omega
      refine ⟨z.toNat, Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
      · simpa using Int.toNat_le_toNat hz'.1
      · rw [← Int.ofNat_le]
        simpa [Int.toNat_of_nonneg hz0] using hz'.2
      · exact Int.toNat_of_nonneg hz0
    · intro n hn
      simp [lambdaNatCoeff, vonMangoldtIntegerCoeff]
  unfold lambdaCharacterPrefix
  rw [hrange, Finset.sum_insert]
  · simpa [lambdaNatCoeff] using hnatInt
  · simp

theorem norm_lambdaCharacterPrefix_sq_le_characterPrefixMaxSquare
    (N y q : ℕ) (hy : y ≤ N) (χ : DirichletCharacter ℂ q) :
    ‖lambdaCharacterPrefix y q χ‖ ^ 2 ≤
      characterPrefixMaxSquare χ vonMangoldtIntegerCoeff 0 N := by
  rw [lambdaCharacterPrefix_eq_integerInterval]
  unfold characterPrefixMaxSquare
  apply Finset.le_max'
  refine Finset.mem_image.mpr ⟨y, ?_, ?_⟩
  · simpa [Finset.mem_range] using hy
  · unfold characterPrefixSquare
    norm_num

theorem lambdaCharacterPrefixMaxAmplitude_le
    (N q : ℕ) (χ : DirichletCharacter ℂ q) :
    lambdaCharacterPrefixMaxAmplitude N q χ ≤
      nonprincipalPrefixAmplitude vonMangoldtIntegerCoeff N q χ := by
  unfold lambdaCharacterPrefixMaxAmplitude
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  have hyN : y ≤ N := by simpa [Finset.mem_range] using hy
  exact Real.le_sqrt_of_sq_le
    (norm_lambdaCharacterPrefix_sq_le_characterPrefixMaxSquare N y q hyN χ)

theorem nonprincipalLambdaPhysical_le_directAllCharacterMean (N Q : ℕ) :
    nonprincipalLambdaPhysical N Q ≤
      directAllCharacterMean vonMangoldtIntegerCoeff N Q := by
  unfold nonprincipalLambdaPhysical directAllCharacterMean
  apply Finset.sum_le_sum
  intro q hq
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum fun χ hχ =>
      lambdaCharacterPrefixMaxAmplitude_le N q χ
  · positivity

/-- The nonprincipal sum for `Λ` is at most twice the low- and high-conductor sums,
plus twice the error from replacing each character by the primitive character
inducing it. -/
theorem lambdaToLowHighConductorConnector
    (N Q C : ℕ) :
    nonprincipalLambdaPhysical N Q ≤
      2 * (lowConductorPhysical N Q C + highConductorPhysical N Q C) +
        2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q := by
  calc
    nonprincipalLambdaPhysical N Q ≤
        directAllCharacterMean vonMangoldtIntegerCoeff N Q :=
      nonprincipalLambdaPhysical_le_directAllCharacterMean N Q
    _ ≤ 2 * (∑ d ∈ Finset.Icc 2 Q, directConductorWeight Q d *
          ∑ ψ : PrimitiveCharacter d,
            primitivePrefixAmplitude vonMangoldtIntegerCoeff N d ψ) +
        2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q :=
      directAllCharacterMean_le_conductor vonMangoldtIntegerCoeff N Q
    _ = 2 * (lowConductorPhysical N Q C + highConductorPhysical N Q C) +
        2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q := by
      rw [directConductorMean_low_high vonMangoldtIntegerCoeff N Q C]
      rfl

end

end BombieriVinogradov

namespace BombieriVinogradov

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology
noncomputable section

/-! ## Elementary terms -/

lemma reciprocalLogWeight_nonneg (n : ℕ) : 0 ≤ reciprocalLogWeight n := by
  unfold reciprocalLogWeight
  split_ifs
  · positivity
  · exact le_rfl

lemma reciprocalLogWeight_antitone_of_two_le
    {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    reciprocalLogWeight n ≤ reciprocalLogWeight m := by
  have hn : 2 ≤ n := hm.trans hmn
  simp only [reciprocalLogWeight, if_pos hm, if_pos hn]
  have hmlog : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlog : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < m by omega))
      (by exact_mod_cast hmn)
  simpa only [one_div] using one_div_le_one_div_of_le hmlog hlog

/-- For `y ≥ 2` the partial summation factor for the weight `1/log n` (zero for
`n < 2`) equals `2 / log 2`: the weight jumps to `1/log 2` at `n = 2` and then
decreases. -/
theorem discreteAbelAmplifier_eq_two_inv_log_two
    {y : ℕ} (hy : 2 ≤ y) :
    discreteAbelAmplifier y = 2 * (Real.log 2)⁻¹ := by
  induction y, hy using Nat.le_induction with
  | base =>
      have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      simp [discreteAbelAmplifier, reciprocalLogWeight, Finset.sum_range_succ,
        abs_of_pos hlog]
      have harg : Real.log ((1 : ℝ) + 1) = Real.log 2 := by norm_num
      rw [harg, abs_of_pos hlog]
      ring
  | succ y hy ih =>
      have hmono : reciprocalLogWeight (y + 1) ≤ reciprocalLogWeight y :=
        reciprocalLogWeight_antitone_of_two_le hy (Nat.le_succ y)
      have hy0 := reciprocalLogWeight_nonneg y
      have hys0 := reciprocalLogWeight_nonneg (y + 1)
      unfold discreteAbelAmplifier at ih ⊢
      rw [abs_of_nonneg hy0] at ih
      rw [Finset.sum_range_succ, abs_of_nonneg hys0,
        abs_of_nonneg (sub_nonneg.mpr hmono)]
      linarith only [ih]

/-- The partial summation factor is at most `2 / log 2` uniformly in `N`. -/
theorem discreteAbelAmplifierPrefixMax_le_two_inv_log_two (N : ℕ) :
    discreteAbelAmplifierPrefixMax N ≤ 2 * (Real.log 2)⁻¹ := by
  unfold discreteAbelAmplifierPrefixMax
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  by_cases h2 : 2 ≤ y
  · exact (discreteAbelAmplifier_eq_two_inv_log_two h2).le
  · have hlog : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
    interval_cases y <;>
      norm_num [discreteAbelAmplifier, reciprocalLogWeight, hlog]

private lemma nonprincipalCharacters_card_le_totient
    {q : ℕ} (hq : 0 < q) :
    ((nonprincipalCharacters q).card : ℝ) ≤ q.totient := by
  have hchars : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    have horth := charOrthSum hq (1 : ZMod q) 1
    have hc : ((Fintype.card (DirichletCharacter ℂ q) : ℕ) : ℂ) =
        (q.totient : ℂ) := by simpa using horth
    exact_mod_cast hc
  exact_mod_cast (Finset.card_le_card (Finset.erase_subset _ _)).trans_eq
    (by simpa using hchars)

theorem principalBadPhysical_le_explicit (N Q : ℕ) :
    principalBadPhysical N Q ≤
      (Q : ℝ) * (Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N := by
  unfold principalBadPhysical
  calc
    _ ≤ ∑ _q ∈ Finset.Icc 1 Q,
        (Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N := by
      apply Finset.sum_le_sum
      intro q hq
      have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
      have hφ : (1 : ℝ) ≤ q.totient := by
        exact_mod_cast Nat.totient_pos.mpr hq0
      have hinv : ((q.totient : ℝ)⁻¹) ≤ 1 := by
        have hi := (inv_le_inv₀ (lt_of_lt_of_le (by norm_num) hφ)
          (by norm_num : (0 : ℝ) < 1)).2 hφ
        simpa using hi
      have hlogq : (Nat.log2 q : ℝ) ≤ Nat.log2 Q := by
        exact_mod_cast (by
          rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
          exact Nat.log_mono_right (Finset.mem_Icc.mp hq).2)
      have hrest : 0 ≤ (Nat.log2 N + 1 : ℝ) * Real.log N := by positivity
      calc
        ((q.totient : ℝ)⁻¹) *
            ((Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N) ≤
            1 * ((Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N) := by
          gcongr
        _ ≤ (Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N := by
          nlinarith
    _ = ((Finset.Icc 1 Q).card : ℝ) *
        ((Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N) := by simp
    _ ≤ (Q : ℝ) *
        ((Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N) := by
      gcongr
      simp
    _ = _ := by ring

theorem primePowerPhysical_le_explicit (N Q : ℕ) :
    primePowerPhysical N Q ≤
      (Q : ℝ) * primePowerCorrectionExplicitBound N := by
  exact sum_lambdaPrimePowerCorrectionPrefixMaxError_le N Q

/-- Replacing `χ` mod `q` by the primitive character inducing it changes each sum
`∑_{n ≤ y} Λ(n) χ(n)`, `y ≤ N`, by at most `2 log₂ q (log₂ N + 1) log N`. -/
theorem vonMangoldt_conductorErrorAmplitude_le
    {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q) (N : ℕ) :
    conductorErrorAmplitude χ vonMangoldtIntegerCoeff N ≤
      2 * (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N := by
  have hs := vonMangoldt_conductorErrorPrefixMaxSquare_le hq χ N
  rw [← conductorErrorAmplitude_sq] at hs
  have hx := conductorErrorAmplitude_nonneg χ vonMangoldtIntegerCoeff N
  have hC : 0 ≤ 2 * (Nat.log2 q : ℝ) *
      (Nat.log2 N + 1 : ℝ) * Real.log N := by positivity
  nlinarith

/-- Summed over `q ≤ Q` and `χ ≠ χ₀` with weight `1/φ(q)`, the change-of-conductor
error for `Λ` is at most `2 Q log₂ Q (log₂ N + 1) log N`. -/
theorem directConductorCorrectionMean_vonMangoldt_le (N Q : ℕ) :
    directConductorCorrectionMean vonMangoldtIntegerCoeff N Q ≤
      (Q : ℝ) *
        (2 * (Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N) := by
  unfold directConductorCorrectionMean
  let C : ℝ :=
    2 * (Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ ∑ _q ∈ Finset.Icc 1 Q, C := by
      apply Finset.sum_le_sum
      intro q hq
      have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
      have hφ : (0 : ℝ) < q.totient := by
        exact_mod_cast Nat.totient_pos.mpr hq0
      have hchar := nonprincipalCharacters_card_le_totient hq0
      have hqlog : (Nat.log2 q : ℝ) ≤ Nat.log2 Q := by
        exact_mod_cast (by
          rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
          exact Nat.log_mono_right (Finset.mem_Icc.mp hq).2)
      have hpoly :
          2 * (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N ≤ C := by
        dsimp [C]
        gcongr
      calc
        ((q.totient : ℝ)⁻¹) *
            (∑ χ ∈ nonprincipalCharacters q,
              conductorErrorAmplitude χ vonMangoldtIntegerCoeff N) ≤
            ((q.totient : ℝ)⁻¹) *
              (∑ _χ ∈ nonprincipalCharacters q, C) := by
          gcongr with χ hχ
          exact (vonMangoldt_conductorErrorAmplitude_le hq0 χ N).trans hpoly
        _ = ((q.totient : ℝ)⁻¹) *
              (((nonprincipalCharacters q).card : ℝ) * C) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((q.totient : ℝ)⁻¹) * ((q.totient : ℝ) * C) := by
          gcongr
        _ = C := by field_simp
    _ = ((Finset.Icc 1 Q).card : ℝ) * C := by simp
    _ ≤ (Q : ℝ) * C := by
      gcongr
      simp
    _ = _ := by rfl

/-! ## The elementary terms are `O(N / (log N)^A)` -/

/-- The partial summation factor times the sum of the terms from primes dividing
`q`, from prime powers `p^k` with `k ≥ 2`, and from the change of conductor. -/
def elementaryTerms (N Q : ℕ) : ℝ :=
  discreteAbelAmplifierPrefixMax N *
    (principalBadPhysical N Q + primePowerPhysical N Q +
      2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q)

lemma natLog2_cast_le_two_log {n : ℕ} (hn : 2 ≤ n) :
    (Nat.log2 n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
  have hp : 2 ^ Nat.log2 n ≤ n := Nat.log2_self_le (by omega)
  have hpR : (0 : ℝ) < (2 : ℝ) ^ Nat.log2 n := by positivity
  have hnR : (0 : ℝ) < n := by positivity
  have hlog := Real.strictMonoOn_log.monotoneOn hpR hnR (by exact_mod_cast hp)
  rw [Real.log_pow] at hlog
  have htwo : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  nlinarith

lemma natSqrt_cast_le_realSqrt (n : ℕ) :
    (n.sqrt : ℝ) ≤ Real.sqrt n := by
  apply Real.le_sqrt_of_sq_le
  exact_mod_cast (show n.sqrt ^ 2 ≤ n by simpa [pow_two] using Nat.sqrt_le n)

theorem mul_sqrt_add_one_mul_log_pow_le (A k : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ Q : ℕ,
      (Q : ℝ) ≤ Real.sqrt N / Real.log N ^ (A + k) →
      (Q : ℝ) * (Real.sqrt N + 1) * Real.log N ^ k ≤
        2 * (N : ℝ) / Real.log N ^ A := by
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with N hN Q hQ
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < N by omega))
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := Real.one_le_sqrt.mpr (by
    exact_mod_cast (show 1 ≤ N by omega))
  have hs2 : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
  have hden : 0 < Real.log (N : ℝ) ^ (A + k) := pow_pos hlog _
  have hQ' : (Q : ℝ) * Real.log (N : ℝ) ^ (A + k) ≤ Real.sqrt N :=
    (le_div_iff₀ hden).mp hQ
  have hmain : (Q : ℝ) * Real.sqrt N * Real.log N ^ k ≤
      (N : ℝ) / Real.log N ^ A := by
    apply (le_div_iff₀ (pow_pos hlog A)).2
    calc
      (Q : ℝ) * Real.sqrt N * Real.log N ^ k * Real.log N ^ A =
          Real.sqrt N * ((Q : ℝ) * Real.log N ^ (A + k)) := by
            rw [pow_add]
            ring
      _ ≤ Real.sqrt N * Real.sqrt N := by gcongr
      _ = (N : ℝ) := by rw [← sq, hs2]
  have hsmall : (Q : ℝ) * 1 * Real.log N ^ k ≤
      (Q : ℝ) * Real.sqrt N * Real.log N ^ k := by gcongr
  calc
    (Q : ℝ) * (Real.sqrt N + 1) * Real.log N ^ k =
        (Q : ℝ) * Real.sqrt N * Real.log N ^ k +
          (Q : ℝ) * 1 * Real.log N ^ k := by ring
    _ ≤ (N : ℝ) / Real.log N ^ A + (N : ℝ) / Real.log N ^ A :=
      add_le_add hmain (hsmall.trans hmain)
    _ = 2 * (N : ℝ) / Real.log N ^ A := by ring

/-- For `Q ≤ N` the elementary terms are `O(Q √N (log N)³)`. -/
theorem elementaryTerms_le :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ Q : ℕ, Q ≤ N →
      elementaryTerms N Q ≤
        90 * (Q : ℝ) * (Real.sqrt N + 1) * Real.log N ^ 3 := by
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with N hN Q hQN
  by_cases hQzero : Q = 0
  · subst Q
    simp [elementaryTerms, principalBadPhysical, primePowerPhysical,
      directConductorCorrectionMean]
  have hQpos : 0 < Q := Nat.pos_of_ne_zero hQzero
  have hQone : (1 : ℝ) ≤ Q := by exact_mod_cast hQpos
  have hNR : (0 : ℝ) < N := by positivity
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have hexp : Real.exp 1 < (N : ℝ) := by
      calc
        Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
        _ ≤ (N : ℝ) := by exact_mod_cast hN
    exact ((Real.lt_log_iff_exp_lt hNR).2 hexp).le
  have hlog0 : 0 ≤ Real.log (N : ℝ) := by linarith
  have hlog2N := natLog2_cast_le_two_log (show 2 ≤ N by omega)
  have hpp := primePowerPhysical_le_explicit N Q
  have hbad := principalBadPhysical_le_explicit N Q
  have hcond := directConductorCorrectionMean_vonMangoldt_le N Q
  have hsqrt := natSqrt_cast_le_realSqrt N
  have habel := discreteAbelAmplifierPrefixMax_le_two_inv_log_two N
  have hab3 : discreteAbelAmplifierPrefixMax N ≤ 3 := by
    refine habel.trans ?_
    have htwo : (2 / 3 : ℝ) < Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    rw [mul_inv_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    linarith
  have hlogQ : (Nat.log2 Q : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    by_cases hQ2 : 2 ≤ Q
    · have hlogmono : Real.log (Q : ℝ) ≤ Real.log (N : ℝ) :=
        Real.strictMonoOn_log.monotoneOn
          (by change (0 : ℝ) < (Q : ℝ); exact_mod_cast hQpos)
          hNR (by exact_mod_cast hQN)
      linarith [natLog2_cast_le_two_log hQ2]
    · have hQle : Q ≤ 1 := by omega
      have hlog2Q : Nat.log2 Q = 0 := by interval_cases Q; rfl
      rw [hlog2Q]
      norm_num
      exact hlog0
  have hL : (Nat.log2 N + 1 : ℝ) ≤ 3 * Real.log N := by linarith
  let X : ℝ := (Q : ℝ) * (Real.sqrt N + 1) * Real.log N ^ 3
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hbad' : principalBadPhysical N Q ≤ 6 * X := by
    refine hbad.trans ?_
    dsimp [X]
    calc
      (Q : ℝ) * (Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N
          ≤ (Q : ℝ) * (2 * Real.log N) * (3 * Real.log N) * Real.log N := by
            gcongr
      _ ≤ 6 * ((Q : ℝ) * (Real.sqrt N + 1) * Real.log N ^ 3) := by
            have hs : 1 ≤ Real.sqrt (N : ℝ) + 1 := by
              linarith [Real.sqrt_nonneg (N : ℝ)]
            calc
              (Q : ℝ) * (2 * Real.log N) * (3 * Real.log N) * Real.log N =
                  (6 * (Q : ℝ) * Real.log N ^ 3) * 1 := by ring
              _ ≤ (6 * (Q : ℝ) * Real.log N ^ 3) *
                    (Real.sqrt N + 1) :=
                mul_le_mul_of_nonneg_left hs (by positivity)
              _ = 6 * ((Q : ℝ) * (Real.sqrt N + 1) * Real.log N ^ 3) := by ring
  have hcond' : 2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q ≤
      12 * X := by
    have hc := mul_le_mul_of_nonneg_left hcond (by norm_num : (0 : ℝ) ≤ 2)
    refine hc.trans ?_
    dsimp [X]
    calc
      2 * ((Q : ℝ) *
          (2 * (Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N))
          ≤ 2 * ((Q : ℝ) *
            (2 * (2 * Real.log N) * (3 * Real.log N) * Real.log N)) := by
              gcongr
      _ ≤ 12 * ((Q : ℝ) * (Real.sqrt N + 1) * Real.log N ^ 3) := by
              have hs : 2 ≤ Real.sqrt (N : ℝ) + 1 := by
                have hsN : 1 ≤ Real.sqrt (N : ℝ) :=
                  Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ N by omega))
                linarith
              calc
                2 * ((Q : ℝ) *
                    (2 * (2 * Real.log N) * (3 * Real.log N) * Real.log N)) =
                    (12 * (Q : ℝ) * Real.log N ^ 3) * 2 := by ring
                _ ≤ (12 * (Q : ℝ) * Real.log N ^ 3) *
                      (Real.sqrt N + 1) :=
                  mul_le_mul_of_nonneg_left hs (by positivity)
                _ = 12 * ((Q : ℝ) * (Real.sqrt N + 1) * Real.log N ^ 3) := by ring
  have hpp' : primePowerPhysical N Q ≤ 6 * X := by
    refine hpp.trans ?_
    unfold primePowerCorrectionExplicitBound
    change (Q : ℝ) * (((N.sqrt + 1 : ℕ) : ℝ) *
      (Nat.log2 N + 1 : ℝ) * Real.log N) ≤ 6 * X
    dsimp [X]
    have hsN : ((N.sqrt + 1 : ℕ) : ℝ) ≤ Real.sqrt N + 1 := by
      norm_num
      linarith
    calc
      (Q : ℝ) * (((N.sqrt + 1 : ℕ) : ℝ) *
          (Nat.log2 N + 1 : ℝ) * Real.log N)
          ≤ (Q : ℝ) * ((Real.sqrt N + 1) *
            (3 * Real.log N) * Real.log N) := by gcongr
      _ ≤ 6 * ((Q : ℝ) * (Real.sqrt N + 1) * Real.log N ^ 3) := by
            have := mul_nonneg (show (0 : ℝ) ≤ (Q : ℝ) * (Real.sqrt N + 1) by positivity)
              (sq_nonneg (Real.log N))
            nlinarith
  unfold elementaryTerms
  have hins : principalBadPhysical N Q + primePowerPhysical N Q +
      2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q ≤ 30 * X := by
    calc
      _ ≤ 6 * X + 6 * X + 12 * X := add_le_add (add_le_add hbad' hpp') hcond'
      _ ≤ 30 * X := by nlinarith [hX0]
  have hins0 : 0 ≤ principalBadPhysical N Q + primePowerPhysical N Q +
      2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q := by
    have hb0 : 0 ≤ principalBadPhysical N Q := by
      unfold principalBadPhysical
      positivity
    have hp0 : 0 ≤ primePowerPhysical N Q := by
      unfold primePowerPhysical
      apply Finset.sum_nonneg
      intro q hq
      unfold lambdaPrimePowerCorrectionPrefixMaxError
      exact Finset.le_max' _ 0 (Finset.mem_insert_self 0 _)
    have hc0 : 0 ≤ directConductorCorrectionMean vonMangoldtIntegerCoeff N Q := by
      unfold directConductorCorrectionMean
      apply Finset.sum_nonneg
      intro q hq
      exact mul_nonneg (by positivity)
        (Finset.sum_nonneg fun χ _ => conductorErrorAmplitude_nonneg χ _ _)
    positivity
  calc
    discreteAbelAmplifierPrefixMax N *
        (principalBadPhysical N Q + primePowerPhysical N Q +
          2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q)
        ≤ 3 * (30 * X) := mul_le_mul hab3 hins hins0 (by norm_num)
    _ = 90 * (Q : ℝ) * (Real.sqrt N + 1) * Real.log N ^ 3 := by
      dsimp [X]
      ring

/-- For `Q ≤ √N / (log N)^(A+3)` the elementary terms are `O(N / (log N)^A)`. -/
theorem elementaryTerms_le_div_log_pow (A : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ Q : ℕ,
      (Q : ℝ) ≤ Real.sqrt N / Real.log N ^ (A + 3) →
      elementaryTerms N Q ≤
        180 * (N : ℝ) / Real.log N ^ A := by
  filter_upwards [elementaryTerms_le,
    mul_sqrt_add_one_mul_log_pow_le A 3, eventually_ge_atTop (3 : ℕ)] with
      N helem hterms hN Q hQ
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have hNR : (0 : ℝ) < N := by positivity
    have hexp : Real.exp 1 < (N : ℝ) := by
      calc
        Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
        _ ≤ (N : ℝ) := by exact_mod_cast hN
    exact ((Real.lt_log_iff_exp_lt hNR).2 hexp).le
  have hden : 1 ≤ Real.log N ^ (A + 3) := one_le_pow₀ hlog
  have hsqrt0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hcut : Real.sqrt N / Real.log N ^ (A + 3) ≤ Real.sqrt N :=
    div_le_self hsqrt0 hden
  have hsqrtN : Real.sqrt (N : ℝ) ≤ N :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by
      exact_mod_cast (show 1 ≤ N by omega)))
  have hQNreal : (Q : ℝ) ≤ N := hQ.trans (hcut.trans hsqrtN)
  have hQN : Q ≤ N := by exact_mod_cast hQNreal
  calc
    elementaryTerms N Q ≤
        90 * (Q : ℝ) * (Real.sqrt N + 1) * Real.log N ^ 3 :=
      helem Q hQN
    _ ≤ 90 * (2 * (N : ℝ) / Real.log N ^ A) := by
      have hm := mul_le_mul_of_nonneg_left (hterms Q hQ) (by norm_num : (0 : ℝ) ≤ 90)
      simpa [mul_assoc] using hm
    _ = 180 * (N : ℝ) / Real.log N ^ A := by ring

/-! ## Reduction to low and high conductors -/

/-- The bound for small conductors: for all `A`, `B`, `C` and `Q = ⌊√N / (log N)^B⌋`,
the low-conductor sum, the term `|ψ(y) - y|` and the change to `li` are
`O(N / (log N)^A)`. It follows from the Siegel–Walfisz theorem for primitive
characters and the prime number theorem. -/
def LowConductorBound : Prop :=
  ∀ A C B : ℕ, ∃ K : ℝ, 0 < K ∧
    ∀ᶠ N : ℕ in Filter.atTop,
      let Q := BombieriVinogradov.modulusCutoff N (B : ℝ)
      2 * discreteAbelAmplifierPrefixMax N * lowConductorPhysical N Q C +
          discreteAbelAmplifierPrefixMax N * principalGlobalPhysical N Q +
          chebyshevToLiPhysical N Q ≤
        K * (N : ℝ) / Real.log N ^ A

private lemma amplitude_three_piece
    {x a b c : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : x ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2)) :
    x ≤ 2 * (a + b + c) := by
  nlinarith [sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)]

/-- By Vaughan's identity, the normalized mean of `Λ` over any set of conductors is
at most twice the sum of the means of its Type I, Type II and small parts. -/
theorem apNormalizedPrimitiveMeanOn_vaughan_le
    (N : ℕ) (S : Finset ℕ) (u v : ℕ) :
    apNormalizedPrimitiveMeanOn vonMangoldtIntegerCoeff N S ≤
      2 * (apNormalizedPrimitiveMeanOn
          (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N S +
        apNormalizedPrimitiveMeanOn
          (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N S +
        apNormalizedPrimitiveMeanOn
          (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N S) := by
  unfold apNormalizedPrimitiveMeanOn
  calc
    _ ≤ ∑ q ∈ S, ((q.totient : ℝ)⁻¹) *
        ∑ χ : PrimitiveCharacter q,
          2 * (primitivePrefixAmplitude
              (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N q χ +
            primitivePrefixAmplitude
              (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N q χ +
            primitivePrefixAmplitude
              (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N q χ) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro χ hχ
        apply amplitude_three_piece
        · exact primitivePrefixAmplitude_nonneg _ _ _ _
        · exact primitivePrefixAmplitude_nonneg _ _ _ _
        · exact primitivePrefixAmplitude_nonneg _ _ _ _
        · exact primitivePrefixAmplitude_nonneg _ _ _ _
        · rw [primitivePrefixAmplitude_sq, primitivePrefixAmplitude_sq,
            primitivePrefixAmplitude_sq, primitivePrefixAmplitude_sq]
          exact primitiveCharacterPrefixMaxSquare_le_three _ _ _ _ N q χ
            (fun n _ => (vaughanLambdaCoeff_unit_eq n).symm.trans
              (vaughanLambdaCoeff_eq vaughanUnitIntegerCoeff u v n))
      · positivity
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      ring_nf

/-- On any set of conductors, the weighted conductor sum is at most `H(Q)²` times the
normalized mean, where `H(Q) = ∑_{e ≤ Q} 1/e`. -/
theorem directConductorMeanOn_le_apNormalizedPrimitiveMeanOn
    (a : ℤ → ℂ) (N Q : ℕ) (S : Finset ℕ) :
    directConductorMeanOn a N Q S ≤
      conductorHarmonicFactor Q ^ 2 * apNormalizedPrimitiveMeanOn a N S := by
  unfold directConductorMeanOn apNormalizedPrimitiveMeanOn
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  calc
    directConductorWeight Q d *
        (∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ) ≤
      (conductorHarmonicFactor Q ^ 2 / (d.totient : ℝ)) *
        (∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ) :=
      mul_le_mul_of_nonneg_right (directConductorWeight_le Q d)
        (Finset.sum_nonneg fun ψ _ => primitivePrefixAmplitude_nonneg a N d ψ)
    _ = conductorHarmonicFactor Q ^ 2 *
        (((d.totient : ℝ)⁻¹) *
          ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ) := by
      rw [div_eq_mul_inv]
      ring

/-- The high-conductor sum for `Λ` is at most `2 H(Q)²` times the sum of the
high-conductor means of the three parts of Vaughan's identity. -/
theorem highConductorPhysical_le_vaughanHybrid
    (N Q C u v : ℕ) :
    highConductorPhysical N Q C ≤
      2 * conductorHarmonicFactor Q ^ 2 *
        (highConductorVaughanTypeIMean N Q C u v +
          highConductorVaughanTypeIIMean N Q C u v +
          highConductorVaughanSmallMean N Q C v) := by
  refine (directConductorMeanOn_le_apNormalizedPrimitiveMeanOn
    vonMangoldtIntegerCoeff N Q (highConductorSet N Q C)).trans ?_
  have hv := mul_le_mul_of_nonneg_left
    (apNormalizedPrimitiveMeanOn_vaughan_le N (highConductorSet N Q C) u v)
    (sq_nonneg (conductorHarmonicFactor Q))
  unfold highConductorVaughanTypeIMean highConductorVaughanTypeIIMean
    highConductorVaughanSmallMean
  nlinarith only [hv]

/-- The Bombieri–Vinogradov bound at a single `N`, with `Q = ⌊√N / (log N)^B⌋`: if
the low-conductor terms are at most `K_L N / (log N)^A`, the high-conductor Vaughan
terms at most `K_H N / (log N)^A` and the elementary terms at most
`180 N / (log N)^A`, then the Bombieri–Vinogradov sum is at most
`(K_L + K_H + 180) N / (log N)^A`. -/
theorem bvSum_le_of_conductor_bounds
    (A : ℕ) (B C N Q u v : ℕ) (KL KH : ℝ)
    (hN : 2 ≤ N)
    (hQ : Q = BombieriVinogradov.modulusCutoff N (B : ℝ))
    (hlow :
      2 * discreteAbelAmplifierPrefixMax N * lowConductorPhysical N Q C +
          discreteAbelAmplifierPrefixMax N * principalGlobalPhysical N Q +
          chebyshevToLiPhysical N Q ≤
        KL * (N : ℝ) / Real.log N ^ A)
    (hhigh :
      4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 *
          (highConductorVaughanTypeIMean N Q C u v +
            highConductorVaughanTypeIIMean N Q C u v +
            highConductorVaughanSmallMean N Q C v) ≤
        KH * (N : ℝ) / Real.log N ^ A)
    (helem : elementaryTerms N Q ≤
      180 * (N : ℝ) / Real.log N ^ A) :
    (∑ q ∈ Finset.Icc 1
        (BombieriVinogradov.modulusCutoff N (B : ℝ)),
      BombieriVinogradov.primeAPPrefixMaxError N q) ≤
      (KL + KH + 180) * (N : ℝ) / Real.log N ^ A := by
  subst Q
  let Q := BombieriVinogradov.modulusCutoff N (B : ℝ)
  have habel : 0 ≤ discreteAbelAmplifierPrefixMax N := by
    have h0 : 0 ≤ discreteAbelAmplifier 0 := by unfold discreteAbelAmplifier; positivity
    exact h0.trans (by
      unfold discreteAbelAmplifierPrefixMax
      exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨0, by simp, rfl⟩))
  have hconnector := lambdaToLowHighConductorConnector N Q C
  have hhighPhysical := highConductorPhysical_le_vaughanHybrid N Q C u v
  have hpacket := sum_primeAPPrefixMaxError_le_errorTerms N Q hN
  have hnon :
      discreteAbelAmplifierPrefixMax N * nonprincipalLambdaPhysical N Q ≤
        2 * discreteAbelAmplifierPrefixMax N *
            (lowConductorPhysical N Q C + highConductorPhysical N Q C) +
          discreteAbelAmplifierPrefixMax N *
            (2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q) := by
    have hscaled := mul_le_mul_of_nonneg_left hconnector habel
    nlinarith only [hscaled]
  have hhigh' :
      2 * discreteAbelAmplifierPrefixMax N * highConductorPhysical N Q C ≤
        KH * (N : ℝ) / Real.log N ^ A := by
    refine (mul_le_mul_of_nonneg_left hhighPhysical
      (mul_nonneg (by norm_num) habel)).trans ?_
    change 2 * discreteAbelAmplifierPrefixMax N *
        (2 * conductorHarmonicFactor Q ^ 2 *
          (highConductorVaughanTypeIMean N Q C u v +
            highConductorVaughanTypeIIMean N Q C u v +
            highConductorVaughanSmallMean N Q C v)) ≤ _
    nlinarith only [hhigh]
  have htotal :
      (bvErrorTerms N Q).total
          (discreteAbelAmplifierPrefixMax N) ≤
        (KL + KH + 180) * (N : ℝ) / Real.log N ^ A := by
    unfold BVErrorTerms.total bvErrorTerms
    calc
      _ ≤ (2 * discreteAbelAmplifierPrefixMax N * lowConductorPhysical N Q C +
            discreteAbelAmplifierPrefixMax N * principalGlobalPhysical N Q +
            chebyshevToLiPhysical N Q) +
          (2 * discreteAbelAmplifierPrefixMax N * highConductorPhysical N Q C) +
          discreteAbelAmplifierPrefixMax N *
            (principalBadPhysical N Q + primePowerPhysical N Q +
              2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q) := by
        nlinarith only [hnon]
      _ ≤ KL * (N : ℝ) / Real.log N ^ A +
          KH * (N : ℝ) / Real.log N ^ A +
          180 * (N : ℝ) / Real.log N ^ A :=
        add_le_add (add_le_add hlow hhigh') (by
          simpa [elementaryTerms] using helem)
      _ = (KL + KH + 180) * (N : ℝ) / Real.log N ^ A := by ring
  exact hpacket.trans htotal

end

end BombieriVinogradov

namespace BombieriVinogradov

open Classical Finset
open scoped BigOperators
noncomputable section

/-! ## Dyadic blocks of high conductors -/

/-- A partition of the high conductors into blocks `cell i`, `i ∈ index`, with
`0 < i ≤ d` for `d ∈ cell i`, `∑ 1/i ≤ 2/R` and `∑ i ≤ 2Q`. -/
structure ConductorBlockPartition (N Q C : ℕ) where
  index : Finset ℕ
  cell : ℕ → Finset ℕ
  lower_pos : ∀ i ∈ index, 0 < i
  levels : ∀ i ∈ index, ∀ d ∈ cell i, i ≤ d
  pairwise : (↑index : Set ℕ).PairwiseDisjoint cell
  cover : index.biUnion cell = highConductorSet N Q C
  inv_lower_sum_le : (∑ i ∈ index, (i : ℝ)⁻¹) ≤
    2 / (logConductorThreshold N C : ℝ)
  lower_sum_le : (∑ i ∈ index, (i : ℝ)) ≤ 2 * (Q : ℝ)

private def dyadicDepth (R Q : ℕ) : ℕ := Nat.log 2 (Q / R) + 1

private def dyadicLowers (R Q : ℕ) : Finset ℕ :=
  if R < Q then
    (Finset.range (dyadicDepth R Q)).image fun j => R * 2 ^ j
  else ∅

private def dyadicCell (N Q C i : ℕ) : Finset ℕ :=
  (highConductorSet N Q C).filter fun d => i < d ∧ d ≤ 2 * i

private lemma exists_dyadic_exponent_of_mem {R Q i : ℕ}
    (hi : i ∈ dyadicLowers R Q) :
    ∃ j ∈ Finset.range (dyadicDepth R Q), R * 2 ^ j = i := by
  by_cases hRQ : R < Q
  · exact Finset.mem_image.mp (by simpa [dyadicLowers, hRQ] using hi)
  · simp [dyadicLowers, hRQ] at hi

private lemma sum_two_pow (k : ℕ) :
    ∑ j ∈ Finset.range k, (2 : ℕ) ^ j = 2 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have hk : 0 < 2 ^ k := pow_pos (by omega) _
      rw [pow_succ]
      omega

private lemma sum_inv_two_pow_le_two (k : ℕ) :
    (∑ j ∈ Finset.range k, ((2 : ℝ) ^ j)⁻¹) ≤ 2 := by
  rw [show (∑ j ∈ Finset.range k, ((2 : ℝ) ^ j)⁻¹) =
      ∑ j ∈ Finset.range k, ((2 : ℝ)⁻¹) ^ j by
    apply Finset.sum_congr rfl
    intro j hj
    simp]
  rw [geom_sum_eq (by norm_num : (2 : ℝ)⁻¹ ≠ 1)]
  have hp : 0 ≤ ((2 : ℝ)⁻¹) ^ k := by positivity
  norm_num
  linarith

private lemma dyadicLower_injective (R : ℕ) (hR : 0 < R) :
    Function.Injective (fun j => R * 2 ^ j) := by
  intro i j hij
  have : 2 ^ i = 2 ^ j := by
    exact Nat.eq_of_mul_eq_mul_left (by omega) hij
  exact (pow_right_injective₀ (by norm_num : (0 : ℕ) < 2)
    (by norm_num : (2 : ℕ) ≠ 1)) this

private lemma dyadic_cover_aux (R Q d : ℕ) (hR : 0 < R) (hRd : R < d)
    (hdQ : d ≤ Q) :
    ∃ j < dyadicDepth R Q, R * 2 ^ j < d ∧ d ≤ 2 * (R * 2 ^ j) := by
  let x := (d - 1) / R
  have hx : 0 < x := by
    dsimp [x]
    exact Nat.div_pos (by omega) hR
  let j := Nat.log 2 x
  have hlo : R * 2 ^ j < d := by
    have hp : 2 ^ j ≤ x := Nat.pow_log_le_self 2 (Nat.ne_of_gt hx)
    have hmul : R * 2 ^ j ≤ d - 1 := by
      calc
        R * 2 ^ j ≤ R * x := Nat.mul_le_mul_left R hp
        _ ≤ d - 1 := Nat.mul_div_le _ _
    omega
  have hhi : d ≤ 2 * (R * 2 ^ j) := by
    have hxlt : x < 2 ^ (j + 1) := by
      simpa [j] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) x
    have hdiv : d - 1 < R * 2 ^ (j + 1) := by
      have := Nat.lt_mul_of_div_lt hxlt hR
      simpa [x, mul_comm] using this
    rw [pow_succ] at hdiv
    calc
      d ≤ R * (2 ^ j * 2) := by omega
      _ = 2 * (R * 2 ^ j) := by ring
  have hj : j < dyadicDepth R Q := by
    have hxQ : x ≤ Q / R := Nat.div_le_div_right (by omega)
    have hlog := Nat.log_mono_right (b := 2) hxQ
    dsimp [dyadicDepth]
    omega
  exact ⟨j, hj, hlo, hhi⟩

private lemma dyadic_cells_pairwise (N Q C R : ℕ) (_hR : 0 < R) :
    (↑(dyadicLowers R Q) : Set ℕ).PairwiseDisjoint (dyadicCell N Q C) := by
  intro i hi j hj hij
  change Disjoint (dyadicCell N Q C i) (dyadicCell N Q C j)
  rw [Finset.disjoint_left]
  intro d hdi hdj
  simp only [dyadicCell, Finset.mem_filter] at hdi hdj
  rcases exists_dyadic_exponent_of_mem hi with ⟨a, ha, rfl⟩
  rcases exists_dyadic_exponent_of_mem hj with ⟨b, hb, hab⟩
  subst j
  have hab' : a ≠ b := by
    intro h
    subst b
    exact hij rfl
  rcases lt_or_gt_of_ne hab' with hablt | hbalt
  · have hp : 2 ^ (a + 1) ≤ 2 ^ b :=
      (pow_right_strictMono₀ (by norm_num : (1 : ℕ) < 2)).monotone (by omega)
    rw [pow_succ] at hp
    have : 2 * (R * 2 ^ a) ≤ R * 2 ^ b := by
      nlinarith
    omega
  · have hp : 2 ^ (b + 1) ≤ 2 ^ a :=
      (pow_right_strictMono₀ (by norm_num : (1 : ℕ) < 2)).monotone (by omega)
    rw [pow_succ] at hp
    have : 2 * (R * 2 ^ b) ≤ R * 2 ^ a := by
      nlinarith
    omega

/-- The dyadic blocks `i < d ≤ 2i` of the high conductors, with `i = R 2^j` for
`0 ≤ j ≤ log₂ ⌊Q/R⌋`. -/
noncomputable def dyadicConductorBlocks
    (N Q C : ℕ) (hR : 0 < logConductorThreshold N C) :
    ConductorBlockPartition N Q C := by
  let R := logConductorThreshold N C
  let I := dyadicLowers R Q
  let cell := dyadicCell N Q C
  refine
    { index := I
      cell := cell
      lower_pos := ?_
      levels := ?_
      pairwise := ?_
      cover := ?_
      inv_lower_sum_le := ?_
      lower_sum_le := ?_ }
  · intro i hi
    rcases exists_dyadic_exponent_of_mem hi with ⟨j, hj, rfl⟩
    exact Nat.mul_pos hR (pow_pos (by norm_num) _)
  · intro i hi d hd
    exact (Finset.mem_filter.mp hd).2.1.le
  · exact dyadic_cells_pairwise N Q C R hR
  · ext d
    constructor
    · intro hd
      rw [Finset.mem_biUnion] at hd
      rcases hd with ⟨i, hi, hdi⟩
      exact (Finset.mem_filter.mp hdi).1
    · intro hd
      have hmem := Finset.mem_filter.mp hd
      have hRd : R < d := hmem.2
      have hdQ : d ≤ Q := (Finset.mem_Icc.mp hmem.1).2
      rcases dyadic_cover_aux R Q d hR hRd hdQ with ⟨j, hj, hlo, hhi⟩
      rw [Finset.mem_biUnion]
      refine ⟨R * 2 ^ j, ?_, ?_⟩
      · have hRQ : R < Q := hRd.trans_le hdQ
        simp only [I, dyadicLowers, if_pos hRQ]
        exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩
      · exact Finset.mem_filter.mpr ⟨hd, hlo, hhi⟩
  · by_cases hRQ : R < Q
    · change (∑ i ∈ dyadicLowers R Q, (i : ℝ)⁻¹) ≤ 2 / (R : ℝ)
      rw [dyadicLowers, if_pos hRQ]
      rw [Finset.sum_image (f := fun i : ℕ => ((i : ℝ)⁻¹))
        (dyadicLower_injective R hR).injOn]
      rw [show (∑ j ∈ Finset.range (dyadicDepth R Q), ((R * 2 ^ j : ℕ) : ℝ)⁻¹) =
        (R : ℝ)⁻¹ * ∑ j ∈ Finset.range (dyadicDepth R Q), ((2 : ℝ) ^ j)⁻¹ by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        push_cast
        rw [mul_inv]]
      have := sum_inv_two_pow_le_two (dyadicDepth R Q)
      have hRreal : (0 : ℝ) ≤ (R : ℝ)⁻¹ := by positivity
      calc
        (R : ℝ)⁻¹ * ∑ j ∈ Finset.range (dyadicDepth R Q), ((2 : ℝ) ^ j)⁻¹ ≤
            (R : ℝ)⁻¹ * 2 := mul_le_mul_of_nonneg_left this hRreal
        _ = 2 / (R : ℝ) := by ring
    · simp [I, dyadicLowers, hRQ, div_nonneg]
  · by_cases hRQ : R < Q
    · change (∑ i ∈ dyadicLowers R Q, (i : ℝ)) ≤ 2 * (Q : ℝ)
      rw [dyadicLowers, if_pos hRQ]
      rw [Finset.sum_image (f := fun i : ℕ => (i : ℝ))
        (dyadicLower_injective R hR).injOn]
      push_cast
      rw [← Finset.mul_sum]
      norm_cast
      rw [sum_two_pow]
      have hdiv : R * (Q / R) ≤ Q := Nat.mul_div_le Q R
      have hqdiv : Q / R ≠ 0 := by
        exact Nat.ne_of_gt (Nat.div_pos hRQ.le hR)
      have hp := Nat.pow_log_le_self 2 hqdiv
      have hpow : 2 ^ dyadicDepth R Q ≤ 2 * (Q / R) := by
        dsimp [dyadicDepth]
        rw [pow_succ]
        simpa [mul_comm] using Nat.mul_le_mul_left 2 hp
      have : R * (2 ^ dyadicDepth R Q - 1) ≤ 2 * Q := by
        calc
          R * (2 ^ dyadicDepth R Q - 1) ≤ R * 2 ^ dyadicDepth R Q :=
            Nat.mul_le_mul_left R (Nat.sub_le _ _)
          _ ≤ R * (2 * (Q / R)) := Nat.mul_le_mul_left R hpow
          _ = 2 * (R * (Q / R)) := by ring
          _ ≤ 2 * Q := Nat.mul_le_mul_left 2 hdiv
      exact_mod_cast this
    · simp [I, dyadicLowers, hRQ]

/-- Each dyadic block with lower endpoint `i` lies in `(i, 2i]`. -/
theorem dyadicConductorBlocks_cell_subset_Ioc
    (N Q C : ℕ) (hR : 0 < logConductorThreshold N C) (i : ℕ) :
    (dyadicConductorBlocks N Q C hR).cell i ⊆
      Finset.Ioc i (2 * i) := by
  intro d hd
  change d ∈ dyadicCell N Q C i at hd
  exact Finset.mem_Ioc.mpr (Finset.mem_filter.mp hd).2

/-- For `Q ≤ N` there are at most `log₂ N + 1` dyadic blocks. -/
theorem dyadicConductorBlocks_index_card_le
    (N Q C : ℕ) (hR : 0 < logConductorThreshold N C) (hQ : Q ≤ N) :
    (dyadicConductorBlocks N Q C hR).index.card ≤ Nat.log2 N + 1 := by
  unfold dyadicConductorBlocks
  dsimp only
  unfold dyadicLowers dyadicDepth
  split_ifs with hRQ
  · calc
      (Finset.image (fun j => logConductorThreshold N C * 2 ^ j)
          (Finset.range (Nat.log 2 (Q / logConductorThreshold N C) + 1))).card ≤
          (Finset.range (Nat.log 2 (Q / logConductorThreshold N C) + 1)).card :=
        Finset.card_image_le
      _ = Nat.log 2 (Q / logConductorThreshold N C) + 1 := by simp
      _ ≤ Nat.log2 N + 1 := by
        rw [Nat.log2_eq_log_two]
        gcongr
        exact (Nat.div_le_self Q _).trans hQ
  · simp

end

end BombieriVinogradov
