import ErdosStraus.BombieriVinogradov.Vaughan.Bilinear

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

/-!
# Character orthogonality for primes in progressions

For `(a, q) = 1`, orthogonality of Dirichlet characters gives
`ψ(y; q, a) - y/φ(q) = (ψ(y, χ₀) - y)/φ(q) + (1/φ(q)) ∑_{χ ≠ χ₀} χ̄(a) ψ(y, χ)`,
so the maximal error over `y ≤ N` and reduced residues `a` is at most
`(max_{y ≤ N} |ψ(y, χ₀) - y| + ∑_{χ ≠ χ₀} max_{y ≤ N} |ψ(y, χ)|)/φ(q)`.
Grouping characters by conductor, the mean
`∑_{q ≤ Q} (1/φ(q)) ∑_{χ ≠ χ₀} max_{y ≤ N} |∑_{n ≤ y} a(n) χ(n)|` is at most twice
the same sum over primitive characters of conductor `d ≥ 2`, weighted by
`∑_{q ≤ Q, d ∣ q} 1/φ(q)`, plus twice the error from replacing `χ` by the
primitive character inducing it.
-/

namespace BombieriVinogradov

open Classical Finset
open scoped BigOperators ArithmeticFunction
noncomputable section

/-- The coefficient `1`, used to specialize Vaughan's identity to `Λ`. -/
def vaughanUnitIntegerCoeff (_ : ℤ) : ℂ := 1

lemma vaughanLambdaCoeff_unit_eq (n : ℤ) :
    vaughanLambdaCoeff vaughanUnitIntegerCoeff n = vonMangoldtIntegerCoeff n := by
  simp [vaughanLambdaCoeff, vaughanUnitIntegerCoeff, vonMangoldtIntegerCoeff]

end

end BombieriVinogradov

namespace BombieriVinogradov

open Classical Finset
open scoped BigOperators
noncomputable section

/-- `max_{y ≤ N} |∑_{1 ≤ n ≤ y} b(n) χ(n)|`, the square root of
`characterPrefixMaxSquare χ b 0 N`. -/
def nonprincipalPrefixAmplitude
    (b : ℤ → ℂ) (N q : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  Real.sqrt (characterPrefixMaxSquare χ b 0 N)

lemma nonprincipalPrefixAmplitude_nonneg
    (b : ℤ → ℂ) (N q : ℕ) (χ : DirichletCharacter ℂ q) :
    0 ≤ nonprincipalPrefixAmplitude b N q χ := Real.sqrt_nonneg _

lemma nonprincipalPrefixAmplitude_sq
    (b : ℤ → ℂ) (N q : ℕ) (χ : DirichletCharacter ℂ q) :
    nonprincipalPrefixAmplitude b N q χ ^ 2 =
      characterPrefixMaxSquare χ b 0 N := by
  apply Real.sq_sqrt
  unfold characterPrefixMaxSquare
  let V := (Finset.range (N + 1)).image
    (fun y => characterPrefixSquare χ b 0 y)
  have hm : V.max' (Finset.image_nonempty.mpr ⟨0, by simp⟩) ∈ V :=
    Finset.max'_mem V _
  rcases Finset.mem_image.mp hm with ⟨y, hy, heq⟩
  rw [← heq]
  unfold characterPrefixSquare
  positivity

end

end BombieriVinogradov

/-! ## Orthogonality for `Λ` in residue classes -/

namespace BombieriVinogradov

open Classical Finset
open scoped BigOperators ArithmeticFunction
noncomputable section

/-- `Λ(n)` as a complex number. -/
def lambdaNatCoeff (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ)

/-- `ψ(y; q, a) = ∑_{n ≤ y, n ≡ a (mod q)} Λ(n)`. -/
def lambdaAPPrefix (y q a : ℕ) : ℂ :=
  ∑ n ∈ (Finset.range (y + 1)).filter
      (fun n : ℕ => (n : ZMod q) = (a : ZMod q)),
    lambdaNatCoeff n

/-- `∑_{n ≤ y, (n, q) = 1} Λ(n)`. -/
def coprimeLambdaPrefix (y q : ℕ) : ℂ :=
  ∑ n ∈ (Finset.range (y + 1)).filter (fun n => n.Coprime q), lambdaNatCoeff n

/-- `ψ(y, χ) = ∑_{n ≤ y} Λ(n) χ(n)` for a character `χ` modulo `q`. -/
def lambdaCharacterPrefix (y q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.range (y + 1), lambdaNatCoeff n * χ (n : ZMod q)

/-- Character orthogonality: for `(a, q) = 1`,
`ψ(y; q, a) = (1/φ(q)) ∑_χ χ̄(a) ψ(y, χ)`. -/
theorem lambdaAPPrefix_eq_character_average
    {q a : ℕ} (hq : 0 < q) (ha : a.Coprime q) (y : ℕ) :
    lambdaAPPrefix y q a =
      (q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          star (χ (a : ZMod q)) * lambdaCharacterPrefix y q χ := by
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr hq))
  have hau : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 ha
  unfold lambdaAPPrefix lambdaCharacterPrefix
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  have hfactor :
      (∑ χ : DirichletCharacter ℂ q,
        (q.totient : ℂ)⁻¹ *
          (star (χ (a : ZMod q)) * (lambdaNatCoeff n * χ (n : ZMod q)))) =
        (q.totient : ℂ)⁻¹ * lambdaNatCoeff n *
          ∑ χ : DirichletCharacter ℂ q,
            χ (n : ZMod q) * star (χ (a : ZMod q)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    ring
  rw [hfactor, charOrthSum hq]
  by_cases heq : (n : ZMod q) = (a : ZMod q)
  · have hnu : IsUnit (n : ZMod q) := heq ▸ hau
    simp [heq, hau]
    field_simp
  · simp [heq]

/-- For the principal character, `ψ(y, χ₀) = ∑_{n ≤ y, (n, q) = 1} Λ(n)`. -/
theorem lambdaCharacterPrefix_one (y q : ℕ) :
    lambdaCharacterPrefix y q (1 : DirichletCharacter ℂ q) =
      coprimeLambdaPrefix y q := by
  rw [lambdaCharacterPrefix, coprimeLambdaPrefix, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  change lambdaNatCoeff n * (if IsUnit (n : ZMod q) then 1 else 0) =
    if n.Coprime q then lambdaNatCoeff n else 0
  simp only [ZMod.isUnit_iff_coprime, mul_ite, mul_one, mul_zero]

/-- The principal error `ψ(y, χ₀) - y = ∑_{n ≤ y, (n, q) = 1} Λ(n) - y`. -/
def principalLambdaMainError (y q : ℕ) : ℂ :=
  coprimeLambdaPrefix y q - (y : ℂ)

/-- The error `ψ(y; q, a) - y/φ(q)`. -/
def lambdaAPMainError (y q a : ℕ) : ℂ :=
  lambdaAPPrefix y q a - (q.totient : ℂ)⁻¹ * (y : ℂ)

/-- For `(a, q) = 1`, `ψ(y; q, a) - y/φ(q)` splits into the principal error
`(ψ(y, χ₀) - y)/φ(q)` and `(1/φ(q)) ∑_{χ ≠ χ₀} χ̄(a) ψ(y, χ)`. -/
theorem lambdaAPMainError_eq_principal_add_nonprincipal
    {q a : ℕ} (hq : 0 < q) (ha : a.Coprime q) (y : ℕ) :
    lambdaAPMainError y q a =
      (q.totient : ℂ)⁻¹ * principalLambdaMainError y q +
      (q.totient : ℂ)⁻¹ *
        ∑ χ ∈ nonprincipalCharacters q,
          star (χ (a : ZMod q)) * lambdaCharacterPrefix y q χ := by
  rw [lambdaAPMainError, lambdaAPPrefix_eq_character_average hq ha,
    sum_allCharacters_eq_principal_add_nonprincipal,
    lambdaCharacterPrefix_one]
  have hau : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 ha
  have hone : (1 : DirichletCharacter ℂ q) (a : ZMod q) = 1 := by
    change (if IsUnit (a : ZMod q) then 1 else 0) = 1
    simp [hau]
  rw [hone, star_one, one_mul]
  unfold principalLambdaMainError
  ring

/-- For `(a, q) = 1`,
`|ψ(y; q, a) - y/φ(q)| ≤ (|ψ(y, χ₀) - y| + ∑_{χ ≠ χ₀} |ψ(y, χ)|)/φ(q)`. -/
theorem norm_lambdaAPMainError_le_principal_add_nonprincipal
    {q a : ℕ} (hq : 0 < q) (ha : a.Coprime q) (y : ℕ) :
    ‖lambdaAPMainError y q a‖ ≤
      (q.totient : ℝ)⁻¹ *
        (‖principalLambdaMainError y q‖ +
          ∑ χ ∈ nonprincipalCharacters q, ‖lambdaCharacterPrefix y q χ‖) := by
  rw [lambdaAPMainError_eq_principal_add_nonprincipal hq ha]
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr hq
  calc
    _ ≤ ‖(q.totient : ℂ)⁻¹ * principalLambdaMainError y q‖ +
        ‖(q.totient : ℂ)⁻¹ *
          ∑ χ ∈ nonprincipalCharacters q,
            star (χ (a : ZMod q)) * lambdaCharacterPrefix y q χ‖ :=
      norm_add_le _ _
    _ = (q.totient : ℝ)⁻¹ * ‖principalLambdaMainError y q‖ +
        (q.totient : ℝ)⁻¹ *
          ‖∑ χ ∈ nonprincipalCharacters q,
            star (χ (a : ZMod q)) * lambdaCharacterPrefix y q χ‖ := by
      simp
    _ ≤ (q.totient : ℝ)⁻¹ * ‖principalLambdaMainError y q‖ +
        (q.totient : ℝ)⁻¹ *
          ∑ χ ∈ nonprincipalCharacters q,
            ‖star (χ (a : ZMod q)) * lambdaCharacterPrefix y q χ‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (q.totient : ℝ)⁻¹ * ‖principalLambdaMainError y q‖ +
        (q.totient : ℝ)⁻¹ *
          ∑ χ ∈ nonprincipalCharacters q, ‖lambdaCharacterPrefix y q χ‖ := by
      gcongr with χ hχ
      rw [norm_mul, norm_star]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (χ.norm_le_one (a : ZMod q))
    _ = _ := by ring

/-- `max_{y ≤ N} |ψ(y, χ₀) - y|`. -/
def principalLambdaPrefixMaxError (N q : ℕ) : ℝ :=
  ((Finset.range (N + 1)).image
    (fun y => ‖principalLambdaMainError y q‖)).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- `max_{y ≤ N} |ψ(y, χ)|`. -/
def lambdaCharacterPrefixMaxAmplitude
    (N q : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  ((Finset.range (N + 1)).image
    (fun y => ‖lambdaCharacterPrefix y q χ‖)).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- `max_{y ≤ N} max_{0 ≤ a < q, (a, q) = 1} |ψ(y; q, a) - y/φ(q)|`, with `0`
adjoined so that the maximum is over a nonempty set. -/
def lambdaAPPrefixMaxError (N q : ℕ) : ℝ :=
  (insert 0 (((Finset.range (N + 1)).product
    (BombieriVinogradov.unitResidues q)).image
      (fun p => ‖lambdaAPMainError p.1 q p.2‖))).max' (by simp)

/-- The maximal error modulo `q` is at most
`(max_{y ≤ N} |ψ(y, χ₀) - y| + ∑_{χ ≠ χ₀} max_{y ≤ N} |ψ(y, χ)|)/φ(q)`. -/
theorem lambdaAPPrefixMaxError_le_character_majorant
    {q N : ℕ} (hq : 0 < q) :
    lambdaAPPrefixMaxError N q ≤
      (q.totient : ℝ)⁻¹ *
        (principalLambdaPrefixMaxError N q +
          ∑ χ ∈ nonprincipalCharacters q,
            lambdaCharacterPrefixMaxAmplitude N q χ) := by
  have hprincipal (y : ℕ) (hy : y ∈ Finset.range (N + 1)) :
      ‖principalLambdaMainError y q‖ ≤ principalLambdaPrefixMaxError N q := by
    unfold principalLambdaPrefixMaxError
    exact Finset.le_max'
      ((Finset.range (N + 1)).image (fun y => ‖principalLambdaMainError y q‖)) _
      (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  have hcharacter (y : ℕ) (hy : y ∈ Finset.range (N + 1))
      (χ : DirichletCharacter ℂ q) :
      ‖lambdaCharacterPrefix y q χ‖ ≤ lambdaCharacterPrefixMaxAmplitude N q χ := by
    unfold lambdaCharacterPrefixMaxAmplitude
    exact Finset.le_max'
      ((Finset.range (N + 1)).image (fun y => ‖lambdaCharacterPrefix y q χ‖)) _
      (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  unfold lambdaAPPrefixMaxError
  apply Finset.max'_le
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_image] at hz
  rcases hz with rfl | ⟨p, hp, rfl⟩
  · have hzero : 0 ∈ Finset.range (N + 1) := by simp
    exact mul_nonneg (inv_nonneg.mpr (by positivity))
      (add_nonneg ((norm_nonneg _).trans (hprincipal 0 hzero))
        (Finset.sum_nonneg fun χ _ =>
          (norm_nonneg _).trans (hcharacter 0 hzero χ)))
  · rcases Finset.mem_product.mp hp with ⟨hyN, haq⟩
    have haCoprime : p.2.Coprime q := by
      have h := haq
      simp [BombieriVinogradov.unitResidues] at h
      exact h.2
    refine (norm_lambdaAPMainError_le_principal_add_nonprincipal
      hq haCoprime p.1).trans ?_
    apply mul_le_mul_of_nonneg_left
    · exact add_le_add (hprincipal p.1 hyN)
        (Finset.sum_le_sum fun χ _ => hcharacter p.1 hyN χ)
    · exact inv_nonneg.mpr (by positivity)

end

end BombieriVinogradov

/-! ## Reduction of the character mean to primitive characters -/

namespace BombieriVinogradov

open Classical Finset
open scoped BigOperators
noncomputable section

/-- `max_{y ≤ N} |∑_{1 ≤ n ≤ y} a(n) χ(n)|` for a primitive character `χ`
modulo `q`. -/
def primitivePrefixAmplitude (a : ℤ → ℂ) (N q : ℕ)
    (χ : PrimitiveCharacter q) : ℝ :=
  Real.sqrt (primitiveCharacterPrefixMaxSquare a 0 N q χ)

lemma primitivePrefixAmplitude_nonneg (a : ℤ → ℂ) (N q : ℕ)
    (χ : PrimitiveCharacter q) : 0 ≤ primitivePrefixAmplitude a N q χ :=
  Real.sqrt_nonneg _

lemma primitivePrefixAmplitude_sq (a : ℤ → ℂ) (N q : ℕ)
    (χ : PrimitiveCharacter q) :
    primitivePrefixAmplitude a N q χ ^ 2 =
      primitiveCharacterPrefixMaxSquare a 0 N q χ := by
  apply Real.sq_sqrt
  exact primitiveCharacterPrefixMaxSquare_nonneg a 0 N q χ

/-- `∑_{q ≤ Q} (1/φ(q)) ∑_{χ ≠ χ₀ (mod q)} max_{y ≤ N} |∑_{1 ≤ n ≤ y} a(n) χ(n)|`. -/
def directAllCharacterMean (a : ℤ → ℂ) (N Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
    ∑ χ ∈ nonprincipalCharacters q, nonprincipalPrefixAmplitude a N q χ

/-- Regrouping by conductor: with `χ*` the primitive character inducing `χ`,
`∑_{q ≤ Q} (1/φ(q)) ∑_{χ ≠ χ₀} F(χ*)` equals
`∑_{2 ≤ d ≤ Q} (∑_{q ≤ Q, d ∣ q} 1/φ(q)) ∑_{χ' primitive mod d} F(χ')`. -/
theorem direct_sum_nonprincipal_by_conductor
    (Q : ℕ) (F : (d : ℕ) → PrimitiveCharacter d → ℝ) :
    (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
      ∑ χ ∈ nonprincipalCharacters q,
        F χ.conductor (conductorPrimitiveCharacter χ)) =
      ∑ d ∈ Finset.Icc 2 Q, directConductorWeight Q d *
        ∑ ψ : PrimitiveCharacter d, F d ψ := by
  calc
    _ = ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
        ∑ d ∈ nonprincipalConductors q, ∑ ψ : PrimitiveCharacter d, F d ψ := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [sum_nonprincipal_by_conductor (Finset.mem_Icc.mp hq).1 F]
    _ = ∑ q ∈ Finset.Icc 1 Q, ∑ d ∈ Finset.Icc 2 Q,
        if d ∣ q then ((q.totient : ℝ)⁻¹) *
          ∑ ψ : PrimitiveCharacter d, F d ψ else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum, ← Finset.sum_filter]
      apply Finset.sum_subset
      · intro d hd
        have hd' := Finset.mem_filter.mp hd
        have hddiv : d ∣ q := (Nat.mem_divisors.mp hd'.1).1
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hd'.2, (Nat.le_of_dvd (Finset.mem_Icc.mp hq).1 hddiv).trans
          (Finset.mem_Icc.mp hq).2⟩, hddiv⟩
      · intro d hdQ hdnot
        simp only [Finset.mem_filter] at hdQ
        exfalso
        apply hdnot
        rw [nonprincipalConductors, Finset.mem_filter]
        exact ⟨Nat.mem_divisors.mpr ⟨hdQ.2,
          Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩,
          (Finset.mem_Icc.mp hdQ.1).1⟩
    _ = ∑ d ∈ Finset.Icc 2 Q, ∑ q ∈ Finset.Icc 1 Q,
        if d ∣ q then ((q.totient : ℝ)⁻¹) *
          ∑ ψ : PrimitiveCharacter d, F d ψ else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [directConductorWeight, Finset.sum_filter, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hdq : d ∣ q <;> simp [hdq]

/-- `max_{y ≤ N} |∑_{1 ≤ n ≤ y} (a(n) χ(n) - a(n) χ*(n))|`, where `χ*` is the
primitive character inducing `χ`. -/
def conductorErrorAmplitude {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℤ → ℂ) (N : ℕ) : ℝ :=
  Real.sqrt (conductorErrorPrefixMaxSquare χ a 0 N)

lemma conductorErrorAmplitude_sq {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℤ → ℂ) (N : ℕ) :
    conductorErrorAmplitude χ a N ^ 2 =
      conductorErrorPrefixMaxSquare χ a 0 N := by
  apply Real.sq_sqrt
  unfold conductorErrorPrefixMaxSquare
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨0, by simp, by simp [conductorErrorPrefixSquare]⟩

lemma conductorErrorAmplitude_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℤ → ℂ) (N : ℕ) : 0 ≤ conductorErrorAmplitude χ a N :=
  Real.sqrt_nonneg _

private lemma amplitude_two_piece
    {x a b : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : x ^ 2 ≤ 2 * (a ^ 2 + b ^ 2)) : x ≤ 2 * (a + b) := by
  nlinarith [sq_nonneg (a + b)]

lemma nonprincipalAmplitude_le_conductor
    {q : ℕ} (χ : DirichletCharacter ℂ q) (a : ℤ → ℂ) (N : ℕ) :
    nonprincipalPrefixAmplitude a N q χ ≤
      2 * (primitivePrefixAmplitude a N χ.conductor
        (conductorPrimitiveCharacter χ) + conductorErrorAmplitude χ a N) := by
  apply amplitude_two_piece
  · exact nonprincipalPrefixAmplitude_nonneg _ _ _ _
  · exact primitivePrefixAmplitude_nonneg _ _ _ _
  · exact conductorErrorAmplitude_nonneg _ _ _
  · rw [nonprincipalPrefixAmplitude_sq, primitivePrefixAmplitude_sq,
      conductorErrorAmplitude_sq]
    apply characterPrefixMaxSquare_le_conductor_add_error

/-- The mean of `conductorErrorAmplitude` with the same weights as
`directAllCharacterMean`. -/
def directConductorCorrectionMean (a : ℤ → ℂ) (N Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
    ∑ χ ∈ nonprincipalCharacters q, conductorErrorAmplitude χ a N

/-- The character mean is at most twice the same mean over primitive characters
of conductor `d ≥ 2`, weighted by `∑_{q ≤ Q, d ∣ q} 1/φ(q)`, plus twice the
correction mean. -/
theorem directAllCharacterMean_le_conductor
    (a : ℤ → ℂ) (N Q : ℕ) :
    directAllCharacterMean a N Q ≤
      2 * (∑ d ∈ Finset.Icc 2 Q, directConductorWeight Q d *
        ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ) +
      2 * directConductorCorrectionMean a N Q := by
  unfold directAllCharacterMean directConductorCorrectionMean
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
        ∑ χ ∈ nonprincipalCharacters q,
          2 * (primitivePrefixAmplitude a N χ.conductor
            (conductorPrimitiveCharacter χ) + conductorErrorAmplitude χ a N) := by
      gcongr with q hq χ hχ
      exact nonprincipalAmplitude_le_conductor χ a N
    _ = 2 * (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
        ∑ χ ∈ nonprincipalCharacters q,
          primitivePrefixAmplitude a N χ.conductor
            (conductorPrimitiveCharacter χ)) +
        2 * (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
          ∑ χ ∈ nonprincipalCharacters q, conductorErrorAmplitude χ a N) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      ring_nf
    _ = _ := by
      rw [direct_sum_nonprincipal_by_conductor]

end

end BombieriVinogradov

namespace BombieriVinogradov

open Classical Finset
open scoped BigOperators ArithmeticFunction
noncomputable section

theorem card_primitiveCharacter_le_totient (q : ℕ) :
    0 < q → Fintype.card (PrimitiveCharacter q) ≤ q.totient := by
  intro hq
  exact primitiveCharacter_card_le_totient_basic q hq

end

end BombieriVinogradov
