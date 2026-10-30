import ErdosStraus.BombieriVinogradov.LargeSieve.PrimitiveCharacters

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

/-!
# The large sieve for primitive characters

This file proves the Bombieri–Davenport inequality
`∑_{q ≤ Q} (q/φ(q)) ∑_{χ primitive mod q} |∑_{M < n ≤ M+N} b(n) χ(n)|²
  ≤ (N + (2⌈log₂ Q²⌉ + 12) Q²) ∑_{M < n ≤ M+N} |b(n)|²`.
Each primitive character is expanded in additive characters through its Gauss sum, and the
additive large sieve is applied at the reduced fractions `a/q` with `q ≤ Q`. The file also
proves the maximal version, with the inner sum maximized over the initial segments
`(M, M + y]`, `y ≤ N`, at the cost of a factor `(Nat.log2 N + 1)²`.
-/

namespace BombieriVinogradov

open scoped BigOperators
open Classical
noncomputable section

/-! ## Gauss sums and reduced fractions -/

/-- The residues `0 ≤ a < q` coprime to `q`. -/
def reducedResidues (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter fun a => Nat.Coprime a q

@[simp]
theorem mem_reducedResidues {q a : ℕ} :
    a ∈ reducedResidues q ↔ a < q ∧ Nat.Coprime a q := by
  simp [reducedResidues]

/-- The twisted Gauss sum `∑_a χ(a) e(an/q)` as a sum over the reduced residues mod `q`. -/
theorem primitive_gaussSum_mulShift_eq_sum_reducedResidues {q : ℕ} [NeZero q]
    (χ : PrimitiveCharacter q) (n : ℤ) :
    gaussSum χ.1 ((primitiveGaussAddChar q).mulShift (n : ZMod q)) =
      ∑ a ∈ reducedResidues q,
        χ.1 (a : ZMod q) * charReal ((n : ℝ) * (a : ℝ) / (q : ℝ)) := by
  have hq : 0 < q := NeZero.pos q
  rw [gaussSum_primitiveGaussAddChar_mulShift]
  rw [sum_zmod_eq_sum_range]
  have hperiod : ∀ a ∈ Finset.range q,
      charReal ((((n : ZMod q).val : ℝ) * (((a : ZMod q).val : ℝ)) / (q : ℝ))) =
        charReal ((n : ℝ) * (a : ℝ) / (q : ℝ)) := by
    intro a ha
    have haval : (a : ZMod q).val = a := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha)]
    rw [haval]
    exact (charReal_zmod_eq hq
      (m := n) (n := (n : ZMod q).val) (ZMod.natCast_zmod_val (n : ZMod q)).symm a).symm
  calc
    ∑ a ∈ Finset.range q,
        χ.1 (a : ZMod q) *
          charReal ((((n : ZMod q).val : ℝ) * (((a : ZMod q).val : ℝ)) / (q : ℝ))) =
        ∑ a ∈ Finset.range q,
          χ.1 (a : ZMod q) * charReal ((n : ℝ) * (a : ℝ) / (q : ℝ)) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [hperiod a ha]
    _ = ∑ a ∈ reducedResidues q,
          χ.1 (a : ZMod q) * charReal ((n : ℝ) * (a : ℝ) / (q : ℝ)) := by
            rw [reducedResidues, Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro a ha
            by_cases hcop : Nat.Coprime a q
            · simp [hcop]
            · have hnonunit : ¬ IsUnit (a : ZMod q) := by
                simpa [ZMod.isUnit_iff_coprime] using hcop
              simp [hcop, χ.1.map_nonunit hnonunit]

/-- For primitive `χ` mod `q`, `∑_{(a,q)=1} χ(a) e(an/q) = χ⁻¹(n) τ(χ)`. -/
theorem sum_reducedResidues_eq_invChar_mul_gaussSum {q : ℕ} [NeZero q]
    (χ : PrimitiveCharacter q) (n : ℤ) :
    (∑ a ∈ reducedResidues q,
        χ.1 (a : ZMod q) * charReal ((n : ℝ) * (a : ℝ) / (q : ℝ))) =
      χ.1⁻¹ (n : ZMod q) * gaussSum χ.1 (primitiveGaussAddChar q) := by
  rw [← primitive_gaussSum_mulShift_eq_sum_reducedResidues χ n]
  exact gaussSum_mulShift_of_isPrimitive (primitiveGaussAddChar q) χ.2 (n : ZMod q)

/-- The pairs `(q, a)` with `1 ≤ q ≤ Q`, `0 ≤ a < q` and `gcd(a, q) = 1`. -/
def reducedFareyIndices (Q : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 Q).product (Finset.range Q)).filter fun qa =>
    qa.2 < qa.1 ∧ Nat.Coprime qa.2 qa.1

@[simp]
theorem mem_reducedFareyIndices {Q q a : ℕ} :
    (q, a) ∈ reducedFareyIndices Q ↔
      1 ≤ q ∧ q ≤ Q ∧ a < q ∧ Nat.Coprime a q := by
  simp [reducedFareyIndices]
  omega

/-- The fraction `a/q` attached to the pair `(q, a)`. -/
def reducedFareyPoint (qa : ℕ × ℕ) : ℝ :=
  (qa.2 : ℝ) / (qa.1 : ℝ)

@[simp]
theorem reducedFareyPoint_pair (q a : ℕ) :
    reducedFareyPoint (q, a) = (a : ℝ) / (q : ℝ) :=
  rfl

theorem reducedFareyPoint_mem_rationalPoints {Q : ℕ} {qa : ℕ × ℕ}
    (hqa : qa ∈ reducedFareyIndices Q) :
    reducedFareyPoint qa ∈ rationalPoints Q := by
  rcases qa with ⟨q, a⟩
  obtain ⟨hq, hqQ, haq, _⟩ := mem_reducedFareyIndices.mp hqa
  rw [reducedFareyPoint_pair]
  refine Finset.mem_biUnion.mpr ⟨q, Finset.mem_Icc.mpr ⟨hq, hqQ⟩, ?_⟩
  exact Finset.mem_image.mpr ⟨a, Finset.mem_range.mpr haq, rfl⟩

/-- A reduced fraction `a/q` determines `q` and `a`. -/
theorem reducedFareyPoint_injOn (Q : ℕ) :
    Set.InjOn reducedFareyPoint (reducedFareyIndices Q : Set (ℕ × ℕ)) := by
  rintro ⟨q₁, a₁⟩ h₁ ⟨q₂, a₂⟩ h₂ hpoint
  change (q₁, a₁) ∈ reducedFareyIndices Q at h₁
  change (q₂, a₂) ∈ reducedFareyIndices Q at h₂
  obtain ⟨hq₁, _, _, hcop₁⟩ := mem_reducedFareyIndices.mp h₁
  obtain ⟨hq₂, _, _, hcop₂⟩ := mem_reducedFareyIndices.mp h₂
  have hq₁0 : (q₁ : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq₁)
  have hq₂0 : (q₂ : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq₂)
  have hcrossR : (a₁ : ℝ) * (q₂ : ℝ) = (a₂ : ℝ) * (q₁ : ℝ) :=
    (div_eq_div_iff hq₁0 hq₂0).mp hpoint
  have hcross : a₁ * q₂ = a₂ * q₁ := by exact_mod_cast hcrossR
  -- From `a₁ q₂ = a₂ q₁` and coprimality, `q₁ ∣ q₂` and `q₂ ∣ q₁`.
  have hq₁dvdq₂ : q₁ ∣ q₂ := by
    apply hcop₁.symm.dvd_of_dvd_mul_left
    refine ⟨a₂, ?_⟩
    calc
      a₁ * q₂ = a₂ * q₁ := hcross
      _ = q₁ * a₂ := Nat.mul_comm _ _
  have hq₂dvdq₁ : q₂ ∣ q₁ := by
    apply hcop₂.symm.dvd_of_dvd_mul_left
    refine ⟨a₁, ?_⟩
    calc
      a₂ * q₁ = a₁ * q₂ := hcross.symm
      _ = q₂ * a₁ := Nat.mul_comm _ _
  have hq : q₁ = q₂ := Nat.dvd_antisymm hq₁dvdq₂ hq₂dvdq₁
  subst q₂
  have ha : a₁ = a₂ :=
    Nat.mul_right_cancel hq₁ hcross
  subst a₂
  rfl

/-- The reduced fractions `a/q` with `1 ≤ q ≤ Q`, as a set of reals. -/
def reducedFareyPoints (Q : ℕ) : Finset ℝ :=
  (reducedFareyIndices Q).image reducedFareyPoint

theorem reducedFareyPoints_subset_rationalPoints (Q : ℕ) :
    reducedFareyPoints Q ⊆ rationalPoints Q := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨qa, hqa, rfl⟩
  exact reducedFareyPoint_mem_rationalPoints hqa

theorem sum_reducedFareyPoints_eq_sum_indices {Q : ℕ} {β : Type*}
    [AddCommMonoid β] (f : ℝ → β) :
    (∑ x ∈ reducedFareyPoints Q, f x) =
      ∑ qa ∈ reducedFareyIndices Q, f (reducedFareyPoint qa) := by
  exact Finset.sum_image (reducedFareyPoint_injOn Q)

theorem reducedFareyPoints_wellSpaced (Q : ℕ) (hQ : 0 < Q) :
    wellSpacedReal (reducedFareyPoints Q) (1 / (Q : ℝ) ^ 2) := by
  intro x hx y hy hxy
  exact rationalPoints_wellSpaced Q hQ
    (reducedFareyPoints_subset_rationalPoints Q hx)
    (reducedFareyPoints_subset_rationalPoints Q hy) hxy

/-- The additive large sieve at the reduced fractions `a/q`, `1 ≤ q ≤ Q`, each taken once:
`∑_{(q,a)} |∑_n b(n) e(na/q)|² ≤ largeSieveBound N Q⁻² ∑_n |b(n)|²`. -/
theorem largeSieveReducedFareyIndices (M : ℤ) (N Q : ℕ) (hQ : 0 < Q)
    (b : ℤ → ℂ) :
    (∑ qa ∈ reducedFareyIndices Q,
        ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
          (charReal ((n : ℝ) * reducedFareyPoint qa) : ℂ) * b n‖ ^ 2)
      ≤ largeSieveBound N (1 / (Q : ℝ) ^ 2) *
          ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by
  rw [← sum_reducedFareyPoints_eq_sum_indices (f := fun x =>
    ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
      (charReal ((n : ℝ) * x) : ℂ) * b n‖ ^ 2)]
  exact largeSievePrimal_wellSpaced M N (by positivity)
    (reducedFareyPoints Q) (reducedFareyPoints_wellSpaced Q hQ) b

/-! ## The large sieve inequality -/

/-- Bessel's inequality for the primitive characters mod `q`, from the orthogonality of
all characters mod `q`. -/
theorem character_reducedResidues_bessel {q : ℕ} [NeZero q] (c : ℕ → ℂ) :
    (∑ χ : PrimitiveCharacter q,
        ‖∑ a ∈ reducedResidues q, c a * χ.1 (a : ZMod q)‖ ^ 2) ≤
      (q.totient : ℝ) * ∑ a ∈ reducedResidues q, ‖c a‖ ^ 2 := by
  classical
  have hsum (χ : DirichletCharacter ℂ q) :
      (∑ x : ZMod q, c x.val * χ x) =
        ∑ a ∈ reducedResidues q, c a * χ (a : ZMod q) := by
    rw [sum_zmod_eq_sum_range, reducedResidues, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha)]
    by_cases hcop : Nat.Coprime a q
    · simp [hcop]
    · have hnonunit : ¬ IsUnit (a : ZMod q) := by
        simpa only [ZMod.isUnit_iff_coprime] using hcop
      simp [hcop, χ.map_nonunit hnonunit]
  have hparseval := charParseval_units (fun x : ZMod q => star (c x.val))
  simp_rw [← star_mul, ← star_sum, norm_star] at hparseval
  rw [unitsSum_eq_reducedFracs] at hparseval
  have henergy :
      (∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
        ‖c (a : ZMod q).val‖ ^ 2) =
      ∑ a ∈ reducedResidues q, ‖c a‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [ZMod.val_natCast,
      Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)]
  simp_rw [hsum] at hparseval
  rw [henergy] at hparseval
  exact (sum_primitive_le_sum_all
    (fun χ => ‖∑ a ∈ reducedResidues q, c a * χ (a : ZMod q)‖ ^ 2)
    (fun _ => sq_nonneg _)).trans_eq hparseval

/-- Expansion of a primitive character sum in additive characters:
`τ(χ⁻¹) ∑_n b(n) χ(n) = ∑_{(a,q)=1} χ⁻¹(a) ∑_n b(n) e(an/q)`. -/
theorem primitive_interval_gauss_inversion {q : ℕ} [NeZero q]
    (χ : PrimitiveCharacter q) (b : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    gaussSum χ.1⁻¹ (primitiveGaussAddChar q) *
        (∑ n ∈ Finset.Icc (M + 1) (M + N), b n * χ.1 (n : ZMod q)) =
      ∑ a ∈ reducedResidues q, χ.1⁻¹ (a : ZMod q) *
        (∑ n ∈ Finset.Icc (M + 1) (M + N),
          (charReal ((n : ℝ) * (a : ℝ) / (q : ℝ)) : ℂ) * b n) := by
  let χi : PrimitiveCharacter q :=
    ⟨χ.1⁻¹, by change χ.1⁻¹.conductor = q; rw [DirichletCharacter.conductor_inv]; exact χ.2⟩
  calc
    gaussSum χ.1⁻¹ (primitiveGaussAddChar q) *
        (∑ n ∈ Finset.Icc (M + 1) (M + N), b n * χ.1 (n : ZMod q))
        = ∑ n ∈ Finset.Icc (M + 1) (M + N),
            b n * (χi.1⁻¹ (n : ZMod q) *
              gaussSum χi.1 (primitiveGaussAddChar q)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n hn
            simp [χi]
            ring
    _ = ∑ n ∈ Finset.Icc (M + 1) (M + N), b n *
          (∑ a ∈ reducedResidues q,
            χi.1 (a : ZMod q) *
              charReal ((n : ℝ) * (a : ℝ) / (q : ℝ))) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [sum_reducedResidues_eq_invChar_mul_gaussSum χi n]
    _ = ∑ n ∈ Finset.Icc (M + 1) (M + N),
          ∑ a ∈ reducedResidues q,
            b n * (χi.1 (a : ZMod q) *
              charReal ((n : ℝ) * (a : ℝ) / (q : ℝ))) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [Finset.mul_sum]
    _ = ∑ a ∈ reducedResidues q, χ.1⁻¹ (a : ZMod q) *
          (∑ n ∈ Finset.Icc (M + 1) (M + N),
            (charReal ((n : ℝ) * (a : ℝ) / (q : ℝ)) : ℂ) * b n) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n hn
            simp [χi]
            ring

/-- `χ ↦ χ⁻¹` as a permutation of the primitive characters mod `q`. -/
noncomputable def primitiveCharacterInvEquiv (q : ℕ) :
    PrimitiveCharacter q ≃ PrimitiveCharacter q where
  toFun χ := ⟨χ.1⁻¹, by change χ.1⁻¹.conductor = q; rw [DirichletCharacter.conductor_inv]; exact χ.2⟩
  invFun χ := ⟨χ.1⁻¹, by change χ.1⁻¹.conductor = q; rw [DirichletCharacter.conductor_inv]; exact χ.2⟩
  left_inv χ := by ext; simp
  right_inv χ := by ext; simp

/-- The inequality for a single modulus:
`(q/φ(q)) ∑_{χ primitive} |∑_n b(n) χ(n)|² ≤ ∑_{(a,q)=1} |∑_n b(n) e(an/q)|²`. -/
theorem weighted_primitive_modulus_le_reduced {q : ℕ} [NeZero q]
    (b : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
            b n * χ.1 (n : ZMod q)‖ ^ 2 ≤
      ∑ a ∈ reducedResidues q,
        ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
          (charReal ((n : ℝ) * (a : ℝ) / (q : ℝ)) : ℂ) * b n‖ ^ 2 := by
  let A : ℕ → ℂ := fun a =>
    ∑ n ∈ Finset.Icc (M + 1) (M + N),
      (charReal ((n : ℝ) * (a : ℝ) / (q : ℝ)) : ℂ) * b n
  have hB := character_reducedResidues_bessel (q := q) A
  have hterm : ∀ χ : PrimitiveCharacter q,
      (q : ℝ) * ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
        b n * χ.1 (n : ZMod q)‖ ^ 2 =
      ‖∑ a ∈ reducedResidues q, A a * χ.1⁻¹ (a : ZMod q)‖ ^ 2 := by
    intro χ
    have hi := primitive_interval_gauss_inversion χ b M N
    have hn := primitive_gaussSum_norm_sq
      (⟨χ.1⁻¹, by change χ.1⁻¹.conductor = q; rw [DirichletCharacter.conductor_inv]; exact χ.2⟩ : PrimitiveCharacter q)
    have hiNorm := congrArg (fun z : ℂ => ‖z‖ ^ 2) hi
    simp only [norm_mul] at hiNorm
    calc
      (q : ℝ) * ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
          b n * χ.1 (n : ZMod q)‖ ^ 2 =
          ‖gaussSum χ.1⁻¹ (primitiveGaussAddChar q)‖ ^ 2 *
            ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
              b n * χ.1 (n : ZMod q)‖ ^ 2 := by rw [hn]
      _ = ‖∑ a ∈ reducedResidues q, χ.1⁻¹ (a : ZMod q) * A a‖ ^ 2 := by
        convert hiNorm using 1; ring
      _ = ‖∑ a ∈ reducedResidues q, A a * χ.1⁻¹ (a : ZMod q)‖ ^ 2 := by
        congr 2
        apply Finset.sum_congr rfl
        intro a ha
        ring
  have hsum :
      (q : ℝ) * ∑ χ : PrimitiveCharacter q,
          ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
            b n * χ.1 (n : ZMod q)‖ ^ 2 ≤
        (q.totient : ℝ) * ∑ a ∈ reducedResidues q, ‖A a‖ ^ 2 := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ χ : PrimitiveCharacter q,
          ‖∑ a ∈ reducedResidues q, A a * χ.1⁻¹ (a : ZMod q)‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro χ hχ
            exact hterm χ
      _ ≤ _ := by
        have hle :
            (∑ χ : PrimitiveCharacter q,
              ‖∑ a ∈ reducedResidues q, A a * χ.1⁻¹ (a : ZMod q)‖ ^ 2) =
              ∑ χ : PrimitiveCharacter q,
                ‖∑ a ∈ reducedResidues q, A a * χ.1 (a : ZMod q)‖ ^ 2 := by
          exact Fintype.sum_equiv
            (primitiveCharacterInvEquiv q) _ _ (fun χ => by rfl)
        rw [hle]
        exact hB
  have hφ : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  calc
    ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖∑ n ∈ Finset.Icc (M + 1) (M + N), b n * χ.1 (n : ZMod q)‖ ^ 2
        = ((q : ℝ) * ∑ χ : PrimitiveCharacter q,
          ‖∑ n ∈ Finset.Icc (M + 1) (M + N), b n * χ.1 (n : ZMod q)‖ ^ 2) /
            (q.totient : ℝ) := by ring
    _ ≤ ((q.totient : ℝ) * ∑ a ∈ reducedResidues q, ‖A a‖ ^ 2) /
          (q.totient : ℝ) := (div_le_div_iff_of_pos_right hφ).mpr hsum
    _ = ∑ a ∈ reducedResidues q, ‖A a‖ ^ 2 := by field_simp
    _ = _ := rfl

theorem sum_reducedResidues_eq_sum_reducedFareyIndices
    {β : Type*} [AddCommMonoid β] (Q : ℕ) (f : ℕ × ℕ → β) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ reducedResidues q, f (q, a)) =
      ∑ qa ∈ reducedFareyIndices Q, f qa := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij (fun x _ => (x.1, x.2)) ?_ ?_ ?_ ?_
  · intro x hx
    rcases x with ⟨q, a⟩
    simp only [Finset.mem_sigma] at hx
    rw [mem_reducedFareyIndices]
    rcases Finset.mem_Icc.mp hx.1 with ⟨hq1, hqQ⟩
    rcases mem_reducedResidues.mp hx.2 with ⟨haq, hcop⟩
    exact ⟨hq1, hqQ, haq, hcop⟩
  · intro x hx y hy hxy
    rcases x with ⟨q, a⟩
    rcases y with ⟨r, b⟩
    cases hxy
    rfl
  · intro qa hqa
    rcases qa with ⟨q, a⟩
    rw [mem_reducedFareyIndices] at hqa
    refine ⟨⟨q, a⟩, ?_, rfl⟩
    simp only [Finset.mem_sigma]
    exact ⟨Finset.mem_Icc.mpr ⟨hqa.1, hqa.2.1⟩,
      mem_reducedResidues.mpr ⟨hqa.2.2.1, hqa.2.2.2⟩⟩
  · intro x hx
    rfl

theorem interval_additive_energy_reindex (b : ℤ → ℂ) (M : ℤ) (N Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ reducedResidues q,
      ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
        (charReal ((n : ℝ) * (a : ℝ) / (q : ℝ)) : ℂ) * b n‖ ^ 2) =
      ∑ qa ∈ reducedFareyIndices Q,
        ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
          (charReal ((n : ℝ) * reducedFareyPoint qa) : ℂ) * b n‖ ^ 2 := by
  simpa only [reducedFareyPoint, mul_div_assoc] using
    sum_reducedResidues_eq_sum_reducedFareyIndices Q (fun qa =>
      ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
        (charReal ((n : ℝ) * (qa.2 : ℝ) / (qa.1 : ℝ)) : ℂ) * b n‖ ^ 2)

/-- The Bombieri–Davenport inequality
`∑_{q ≤ Q} (q/φ(q)) ∑_{χ primitive mod q} |∑_{M < n ≤ M+N} b(n) χ(n)|²
  ≤ largeSieveBound N Q⁻² ∑_{M < n ≤ M+N} |b(n)|²`. -/
theorem weighted_primitive_bombieri_davenport (b : ℤ → ℂ) (M : ℤ)
    (N Q : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
            b n * χ.1 (n : ZMod q)‖ ^ 2) ≤
      largeSieveBound N (1 / (Q : ℝ) ^ 2) *
        ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ reducedResidues q,
        ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
          (charReal ((n : ℝ) * (a : ℝ) / (q : ℝ)) : ℂ) * b n‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      let : NeZero q := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
      exact weighted_primitive_modulus_le_reduced b M N
    _ = ∑ qa ∈ reducedFareyIndices Q,
        ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
          (charReal ((n : ℝ) * reducedFareyPoint qa) : ℂ) * b n‖ ^ 2 := by
      exact interval_additive_energy_reindex b M N Q
    _ ≤ _ := largeSieveReducedFareyIndices M N Q hQ b

/-- The Bombieri–Davenport inequality with the constant `N + (2⌈log₂ Q²⌉ + 12) Q²`
written out. -/
theorem weighted_primitive_bombieri_davenport_explicit (b : ℤ → ℂ) (M : ℤ)
    (N Q : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
            b n * χ.1 (n : ZMod q)‖ ^ 2) ≤
      ((N : ℝ) +
        (2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
          (Q : ℝ) ^ 2) *
        ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by
  have h := weighted_primitive_bombieri_davenport b M N Q hQ
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hOneDiv : 1 / (1 / (Q : ℝ) ^ 2) = (Q : ℝ) ^ 2 := by
    field_simp [hQr]
  have hDivide (x : ℝ) : x / (1 / (Q : ℝ) ^ 2) = x * (Q : ℝ) ^ 2 := by
    field_simp [hQr]
  convert h using 1
  dsimp [largeSieveBound]
  rw [hOneDiv, hDivide]

/-!
## The maximal large sieve

Here `|∑_{M < n ≤ M+N} b(n) χ(n)|²` is replaced by its maximum over the initial segments
`(M, M + y]`, `y ≤ N`. If each initial segment is a disjoint union of at most `L` blocks, and
the blocks together carry at most `D` times the mass `∑_n |b(n)|²`, then applying the large
sieve to each block gives the maximal inequality with an extra factor `L D`
(the Rademacher–Menshov argument).
-/

/-- The constant `N + (2⌈log₂ Q²⌉ + 12) Q²` in the large sieve for primitive characters. -/
def primitiveLargeSieveConstant (N Q : ℕ) : ℝ :=
  (N : ℝ) +
    (2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
      (Q : ℝ) ^ 2

theorem weighted_primitive_bombieri_davenport_explicit' (b : ℤ → ℂ) (M : ℤ)
    (N Q : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
            b n * χ.1 (n : ZMod q)‖ ^ 2) ≤
      primitiveLargeSieveConstant N Q *
        ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by
  simpa [primitiveLargeSieveConstant] using
    weighted_primitive_bombieri_davenport_explicit b M N Q hQ

theorem primitiveLargeSieveConstant_mono_left {N₁ N₂ Q : ℕ} (hN : N₁ ≤ N₂) :
    primitiveLargeSieveConstant N₁ Q ≤ primitiveLargeSieveConstant N₂ Q := by
  unfold primitiveLargeSieveConstant
  gcongr

theorem norm_finset_sum_sq_le_card_mul_sum_norm_sq
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (z : ι → ℂ) :
    ‖∑ i ∈ s, z i‖ ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, ‖z i‖ ^ 2 := by
  calc
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ (∑ i ∈ s, ‖z i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s z) 2
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖z i‖ ^ 2 := by
      simpa [mul_comm] using
        Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖z i‖) (fun _ => (1 : ℝ))

open scoped ComplexConjugate in
/-- The Cauchy–Schwarz inequality for finite sums of complex numbers. -/
theorem finiteComplexCauchy
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → ℂ) :
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤
      (∑ i ∈ s, ‖a i‖ ^ 2) * (∑ i ∈ s, ‖b i‖ ^ 2) := by
  let x : EuclideanSpace ℂ ↥s := WithLp.toLp 2 (fun i => conj (a i.1))
  let y : EuclideanSpace ℂ ↥s := WithLp.toLp 2 (fun i => b i.1)
  have hi : inner ℂ x y = ∑ i ∈ s, a i * b i := by
    rw [PiLp.inner_apply]
    simp only [x, y, RCLike.inner_apply]
    rw [Finset.sum_subtype s (fun i => by rfl)]
    apply Finset.sum_congr rfl
    intro i hi
    simp
    ring
  have hx : ‖x‖ ^ 2 = ∑ i ∈ s, ‖a i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ i : ↥s, ‖conj (a i.1)‖ ^ 2) = _
    simp only [Complex.norm_conj]
    rw [Finset.sum_subtype s (fun i => by rfl)]
  have hy : ‖y‖ ^ 2 = ∑ i ∈ s, ‖b i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ i : ↥s, ‖b i.1‖ ^ 2) = _
    rw [Finset.sum_subtype s (fun i => by rfl)]
  have h := norm_inner_le_norm (𝕜 := ℂ) x y
  rw [hi] at h
  have hsq := pow_le_pow_left₀ (norm_nonneg (∑ i ∈ s, a i * b i)) h 2
  rw [mul_pow, hx, hy] at hsq
  exact hsq

/-- `|∑_{M < n ≤ M+y} b(n) χ(n)|²`. -/
def primitiveCharacterPrefixSquare (b : ℤ → ℂ) (M : ℤ) (y q : ℕ)
    (χ : PrimitiveCharacter q) : ℝ :=
  ‖∑ n ∈ Finset.Icc (M + 1) (M + y), b n * χ.1 (n : ZMod q)‖ ^ 2

/-- `max_{0 ≤ y ≤ N} |∑_{M < n ≤ M+y} b(n) χ(n)|²`. -/
def primitiveCharacterPrefixMaxSquare (b : ℤ → ℂ) (M : ℤ) (N q : ℕ)
    (χ : PrimitiveCharacter q) : ℝ :=
  ((Finset.range (N + 1)).image
      (fun y => primitiveCharacterPrefixSquare b M y q χ)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

theorem primitiveCharacterPrefixSquare_le_max (b : ℤ → ℂ) (M : ℤ)
    {N y q : ℕ} (hy : y ≤ N) (χ : PrimitiveCharacter q) :
    primitiveCharacterPrefixSquare b M y q χ ≤
      primitiveCharacterPrefixMaxSquare b M N q χ := by
  unfold primitiveCharacterPrefixMaxSquare
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨y, by simpa [Finset.mem_range] using hy, rfl⟩

theorem primitiveCharacterPrefixMaxSquare_nonneg
    (b : ℤ → ℂ) (M : ℤ) (N d : ℕ) (ψ : PrimitiveCharacter d) :
    0 ≤ primitiveCharacterPrefixMaxSquare b M N d ψ := by
  unfold primitiveCharacterPrefixMaxSquare
  have h := Finset.le_max'
    ((Finset.range (N + 1)).image
      (fun y => primitiveCharacterPrefixSquare b M y d ψ))
    (primitiveCharacterPrefixSquare b M 0 d ψ)
    (Finset.mem_image.mpr ⟨0, by simp, rfl⟩)
  simpa [primitiveCharacterPrefixSquare] using h

/-- The maximal large sieve from a block decomposition. Block `i` is the interval
`(blockStart i, blockStart i + blockLength i]`, of length at most `N`. If each initial segment
`(M, M + y]`, `y ≤ N`, is the disjoint union of the at most `L` blocks in `prefixBlocks y`, and
`∑_i ∑_{n ∈ block i} |b(n)|² ≤ D ∑_{M < n ≤ M+N} |b(n)|²`, then
`∑_{q ≤ Q} (q/φ(q)) ∑_{χ primitive mod q} max_{y ≤ N} |∑_{M < n ≤ M+y} b(n) χ(n)|²`
is at most `L D (N + (2⌈log₂ Q²⌉ + 12) Q²) ∑_{M < n ≤ M+N} |b(n)|²`. -/
theorem weighted_primitive_prefix_maximal_of_interval_decomposition
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ℤ → ℂ) (M : ℤ) (N Q L D : ℕ) (hQ : 0 < Q)
    (blockStart : ι → ℤ) (blockLength : ι → ℕ)
    (prefixBlocks : ℕ → Finset ι)
    (hdecomp : ∀ y ∈ Finset.range (N + 1), ∀ f : ℤ → ℂ,
      (∑ n ∈ Finset.Icc (M + 1) (M + y), f n) =
        ∑ i ∈ prefixBlocks y,
          ∑ n ∈ Finset.Icc (blockStart i + 1)
            (blockStart i + blockLength i), f n)
    (hcard : ∀ y ∈ Finset.range (N + 1), (prefixBlocks y).card ≤ L)
    (hlength : ∀ i, blockLength i ≤ N)
    (hoverlap :
      (∑ i : ι, ∑ n ∈ Finset.Icc (blockStart i + 1)
          (blockStart i + blockLength i), ‖b n‖ ^ 2) ≤
        (D : ℝ) * ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare b M N q χ) ≤
      (L : ℝ) * (D : ℝ) * primitiveLargeSieveConstant N Q *
        ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by
  have hmax : ∀ q : ℕ, ∀ χ : PrimitiveCharacter q,
      primitiveCharacterPrefixMaxSquare b M N q χ ≤
        (L : ℝ) * ∑ i : ι,
          ‖∑ n ∈ Finset.Icc (blockStart i + 1)
            (blockStart i + blockLength i),
              b n * χ.1 (n : ZMod q)‖ ^ 2 := by
    intro q χ
    unfold primitiveCharacterPrefixMaxSquare
    apply Finset.max'_le
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    unfold primitiveCharacterPrefixSquare
    rw [hdecomp y hy (fun n => b n * χ.1 (n : ZMod q))]
    let z : ι → ℂ := fun i =>
      ∑ n ∈ Finset.Icc (blockStart i + 1)
        (blockStart i + blockLength i), b n * χ.1 (n : ZMod q)
    calc
      ‖∑ i ∈ prefixBlocks y, z i‖ ^ 2 ≤
          ((prefixBlocks y).card : ℝ) *
            ∑ i ∈ prefixBlocks y, ‖z i‖ ^ 2 :=
        norm_finset_sum_sq_le_card_mul_sum_norm_sq (prefixBlocks y) z
      _ ≤ (L : ℝ) * ∑ i ∈ prefixBlocks y, ‖z i‖ ^ 2 := by
        gcongr
        exact_mod_cast hcard y hy
      _ ≤ (L : ℝ) * ∑ i : ι, ‖z i‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_univ_sum_of_nonneg (fun i => sq_nonneg ‖z i‖)
        · positivity
  have hblocks :
      (∑ i : ι, ∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            ‖∑ n ∈ Finset.Icc (blockStart i + 1)
              (blockStart i + blockLength i),
                b n * χ.1 (n : ZMod q)‖ ^ 2) ≤
        primitiveLargeSieveConstant N Q *
          ∑ i : ι, ∑ n ∈ Finset.Icc (blockStart i + 1)
            (blockStart i + blockLength i), ‖b n‖ ^ 2 := by
    calc
      _ ≤ ∑ i : ι, primitiveLargeSieveConstant (blockLength i) Q *
          ∑ n ∈ Finset.Icc (blockStart i + 1)
            (blockStart i + blockLength i), ‖b n‖ ^ 2 := by
        exact Finset.sum_le_sum fun i _ =>
          weighted_primitive_bombieri_davenport_explicit'
            b (blockStart i) (blockLength i) Q hQ
      _ ≤ ∑ i : ι, primitiveLargeSieveConstant N Q *
          ∑ n ∈ Finset.Icc (blockStart i + 1)
            (blockStart i + blockLength i), ‖b n‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right
          (primitiveLargeSieveConstant_mono_left (hlength i))
          (Finset.sum_nonneg fun n hn => sq_nonneg ‖b n‖)
      _ = _ := by rw [Finset.mul_sum]
  calc
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare b M N q χ)
      ≤ ∑ q ∈ Finset.Icc 1 Q,
          ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ : PrimitiveCharacter q,
              ((L : ℝ) * ∑ i : ι,
                ‖∑ n ∈ Finset.Icc (blockStart i + 1)
                  (blockStart i + blockLength i),
                    b n * χ.1 (n : ZMod q)‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro q hq
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum fun χ _ => hmax q χ
        · positivity
    _ = (L : ℝ) * ∑ i : ι, ∑ q ∈ Finset.Icc 1 Q,
          ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ : PrimitiveCharacter q,
              ‖∑ n ∈ Finset.Icc (blockStart i + 1)
                (blockStart i + blockLength i),
                  b n * χ.1 (n : ZMod q)‖ ^ 2 := by
        -- Exchange the sum over blocks with the sums over `q` and `χ`.
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm (s := Finset.univ) (t := Finset.Icc 1 Q)]
        apply Finset.sum_congr rfl
        intro q hq
        rw [Finset.sum_comm]
        simp only [mul_left_comm]
    _ ≤ (L : ℝ) * (primitiveLargeSieveConstant N Q *
          ∑ i : ι, ∑ n ∈ Finset.Icc (blockStart i + 1)
            (blockStart i + blockLength i), ‖b n‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hblocks (by positivity)
    _ ≤ (L : ℝ) * (primitiveLargeSieveConstant N Q *
          ((D : ℝ) * ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2)) := by
        gcongr
        · unfold primitiveLargeSieveConstant
          positivity
    _ = (L : ℝ) * (D : ℝ) * primitiveLargeSieveConstant N Q *
          ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by ring

/-- The case `L = D = Nat.log2 N + 1`, which is what aligned dyadic blocks give. -/
theorem weighted_primitive_prefix_maximal_of_dyadic_decomposition
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ℤ → ℂ) (M : ℤ) (N Q : ℕ) (hQ : 0 < Q)
    (blockStart : ι → ℤ) (blockLength : ι → ℕ)
    (prefixBlocks : ℕ → Finset ι)
    (hdecomp : ∀ y ∈ Finset.range (N + 1), ∀ f : ℤ → ℂ,
      (∑ n ∈ Finset.Icc (M + 1) (M + y), f n) =
        ∑ i ∈ prefixBlocks y,
          ∑ n ∈ Finset.Icc (blockStart i + 1)
            (blockStart i + blockLength i), f n)
    (hcard : ∀ y ∈ Finset.range (N + 1),
      (prefixBlocks y).card ≤ Nat.log2 N + 1)
    (hlength : ∀ i, blockLength i ≤ N)
    (hoverlap :
      (∑ i : ι, ∑ n ∈ Finset.Icc (blockStart i + 1)
          (blockStart i + blockLength i), ‖b n‖ ^ 2) ≤
        ((Nat.log2 N + 1 : ℕ) : ℝ) *
          ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare b M N q χ) ≤
      (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) *
        primitiveLargeSieveConstant N Q *
          ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by
  have h := weighted_primitive_prefix_maximal_of_interval_decomposition
    b M N Q (Nat.log2 N + 1) (Nat.log2 N + 1) hQ
    blockStart blockLength prefixBlocks hdecomp hcard hlength hoverlap
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h

end

end BombieriVinogradov

/-!
## Aligned dyadic blocks

Writing `y ≤ N` in binary splits `(0, y]` into at most `Nat.log2 N + 1` blocks
`(j 2^k, (j + 1) 2^k]`. At each scale `k` these blocks are disjoint, so the decomposition
has `L = D = Nat.log2 N + 1` and the maximal inequality holds with no further hypotheses.
-/

namespace BombieriVinogradov

open scoped BigOperators
open Classical

lemma sum_Ioc_nat_eq_sum_Icc_int (M : ℤ) (a b : ℕ) (f : ℤ → ℂ) :
    (∑ n ∈ Finset.Ioc a b, f (M + n)) = ∑ n ∈ Finset.Icc (M + a + 1) (M + b), f n := by
  refine Finset.sum_bij (fun (n : ℕ) _ => M + (n : ℤ)) ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨han, hnb⟩ := Finset.mem_Ioc.mp hn
    rw [Finset.mem_Icc]
    omega
  · intro n1 _ n2 _ h
    omega
  · intro n hn
    obtain ⟨han, hnb⟩ := Finset.mem_Icc.mp hn
    refine ⟨(n - M).toNat, ?_, ?_⟩
    · rw [Finset.mem_Ioc]
      omega
    · omega
  · intro n hn
    rfl

lemma sum_Ioc_telescope_eq (y L : ℕ) (f : ℕ → ℂ) :
    (∑ k ∈ Finset.range L,
        ∑ n ∈ Finset.Ioc ((y / 2^(k+1)) * 2^(k+1)) ((y / 2^k) * 2^k), f n) =
      ∑ n ∈ Finset.Ioc ((y / 2^L) * 2^L) y, f n := by
  induction' L with L ih
  · simp
  · rw [Finset.sum_range_succ, ih, add_comm]
    have h1 : (y / 2^(L+1)) * 2^(L+1) ≤ (y / 2^L) * 2^L := by
      calc
        (y / 2^(L+1)) * 2^(L+1) = (y / (2^L * 2)) * (2^L * 2) := by rw [pow_succ]
        _ = (y / 2^L / 2) * (2 * 2^L) := by rw [Nat.div_div_eq_div_mul, mul_comm (2^L) 2]
        _ = ((y / 2^L / 2) * 2) * 2^L := by rw [mul_assoc]
        _ ≤ (y / 2^L) * 2^L := Nat.mul_le_mul_right (2^L) (Nat.div_mul_le_self (y / 2^L) 2)
    have h2 : (y / 2^L) * 2^L ≤ y := Nat.div_mul_le_self y (2^L)
    rw [← Finset.sum_Ioc_consecutive f h1 h2]

lemma div_mod_two_eq (y k : ℕ) :
    (y / 2^k) = 2 * (y / 2^(k+1)) + (y / 2^k) % 2 := by
  have H1 : y / 2^(k+1) = (y / 2^k) / 2 := by
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
  rw [H1]
  exact (Nat.div_add_mod (y / 2^k) 2).symm

/-- Binary expansion of `y ≤ N`: `(0, y]` is the disjoint union, over the binary digits `k`
of `y` equal to `1`, of the blocks `(2j 2^k, (2j + 1) 2^k]` with `j = ⌊y / 2^(k+1)⌋`. -/
lemma decomp_eq (y N : ℕ) (hy : y ≤ N) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Ioc 0 y, f n) =
      ∑ k ∈ (Finset.range (Nat.log2 N + 1)).filter (fun k => (y / 2^k) % 2 = 1),
        ∑ n ∈ Finset.Ioc ((2 * (y / 2^(k+1))) * 2^k) ((2 * (y / 2^(k+1))) * 2^k + 2^k), f n := by
  have hL : y < 2^(Nat.log2 N + 1) := by
    calc
      y ≤ N := hy
      _ < 2^(Nat.log2 N + 1) := Nat.lt_log2_self
  have h_div_L : y / 2^(Nat.log2 N + 1) = 0 := Nat.div_eq_of_lt hL
  have h_eq1 := sum_Ioc_telescope_eq y (Nat.log2 N + 1) f
  rw [h_div_L] at h_eq1
  simp only [zero_mul] at h_eq1
  rw [← h_eq1]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (Nat.log2 N + 1)) (fun k => (y / 2^k) % 2 = 1)]
  have h_zero : ∑ k ∈ (Finset.range (Nat.log2 N + 1)).filter (fun k => ¬((y / 2^k) % 2 = 1)),
      ∑ n ∈ Finset.Ioc ((y / 2^(k+1)) * 2^(k+1)) ((y / 2^k) * 2^k), f n = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk1 : (y / 2^k) % 2 = 0 := by
      have h_mod := Nat.mod_lt (y / 2^k) (by decide : 0 < 2)
      have h_not := Finset.mem_filter.mp hk |>.2
      omega
    have hk2 : (y / 2^k) * 2^k = (y / 2^(k+1)) * 2^(k+1) := by
      calc
        (y / 2^k) * 2^k = (2 * (y / 2^(k+1)) + 0) * 2^k := by rw [div_mod_two_eq y k, hk1]
        _ = 2 * (y / 2^(k+1)) * 2^k := by rw [add_zero]
        _ = (y / 2^(k+1)) * (2 * 2^k) := by ring
        _ = (y / 2^(k+1)) * 2^(k+1) := by rw [pow_succ, mul_comm 2 (2^k)]
    rw [hk2, Finset.Ioc_eq_empty_of_le (le_refl _)]
    simp
  rw [h_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  have hk1 : (y / 2^k) % 2 = 1 := Finset.mem_filter.mp hk |>.2
  have hk2 : (y / 2^k) * 2^k = (2 * (y / 2^(k+1))) * 2^k + 2^k := by
    calc
      (y / 2^k) * 2^k = (2 * (y / 2^(k+1)) + 1) * 2^k := by rw [div_mod_two_eq y k, hk1]
      _ = (2 * (y / 2^(k+1))) * 2^k + 2^k := by ring
  have hk3 : (y / 2^(k+1)) * 2^(k+1) = (2 * (y / 2^(k+1))) * 2^k := by
    calc
      (y / 2^(k+1)) * 2^(k+1) = (y / 2^(k+1)) * (2 * 2^k) := by rw [pow_succ, mul_comm (2^k) 2]
      _ = 2 * (y / 2^(k+1)) * 2^k := by ring
  rw [hk2, hk3]

lemma decomp_j_lt (y N k : ℕ) (hy : y ≤ N) : 2 * (y / 2^(k+1)) < N + 1 := by
  have hbit := div_mod_two_eq y k
  have hquotient := Nat.div_le_self y (2^k)
  omega

lemma sum_biUnion_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (S : ι → Finset ℤ) (h_disj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j))
    (T : Finset ℤ) (h_sub : ∀ i ∈ s, S i ⊆ T) (c : ℤ → ℝ) (hc : ∀ n ∈ T, 0 ≤ c n) :
    (∑ i ∈ s, ∑ n ∈ S i, c n) ≤ ∑ n ∈ T, c n := by
  rw [← Finset.sum_biUnion h_disj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    have ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    exact h_sub i hi hxi
  · intro x hx hnx
    exact hc x hx

/-- The maximal large sieve for primitive characters:
`∑_{q ≤ Q} (q/φ(q)) ∑_{χ primitive mod q} max_{y ≤ N} |∑_{M < n ≤ M+y} b(n) χ(n)|²`
is at most `(Nat.log2 N + 1)² (N + (2⌈log₂ Q²⌉ + 12) Q²) ∑_{M < n ≤ M+N} |b(n)|²`. -/
theorem weighted_primitive_prefix_maximal
    (b : ℤ → ℂ) (M : ℤ) (N Q : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare b M N q χ) ≤
      (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) *
        primitiveLargeSieveConstant N Q *
          ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by
  let ι := Fin (Nat.log2 N + 1) × Fin (N + 1)
  let blockStart : ι → ℤ := fun i => M + (i.2.val * 2^i.1.val : ℕ)
  let blockLength : ι → ℕ := fun i => if (i.2.val * 2^i.1.val + 2^i.1.val : ℕ) ≤ N then 2^i.1.val else 0
  let prefixBlocks : ℕ → Finset ι := fun y =>
    if hy : y ≤ N then
      ((Finset.range (Nat.log2 N + 1)).filter (fun k => (y / 2^k) % 2 = 1)).attach
        |>.image fun ⟨k, hk⟩ =>
          have hk_lt : k < Nat.log2 N + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hk |>.1)
          ⟨⟨k, hk_lt⟩, ⟨2 * (y / 2^(k+1)), decomp_j_lt y N k hy⟩⟩
    else ∅

  have hdecomp : ∀ y ∈ Finset.range (N + 1), ∀ f : ℤ → ℂ,
    (∑ n ∈ Finset.Icc (M + 1) (M + y), f n) =
      ∑ i ∈ prefixBlocks y,
        ∑ n ∈ Finset.Icc (blockStart i + 1) (blockStart i + blockLength i), f n := by
    intro y hy f
    have hy2 : y ≤ N := by rw [Finset.mem_range] at hy; omega
    have H1 : (∑ n ∈ Finset.Icc (M + 1) (M + y), f n) = ∑ n ∈ Finset.Ioc 0 y, f (M + n) := by
      simpa only [Nat.cast_zero, add_zero] using (sum_Ioc_nat_eq_sum_Icc_int M 0 y f).symm
    rw [H1]
    have H2 := decomp_eq y N hy2 (fun n => f (M + n))
    rw [H2]
    dsimp [prefixBlocks]
    rw [dif_pos hy2]
    rw [Finset.sum_image]
    · rw [← Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro ⟨k, hk⟩ _
      have hk1 : (y / 2^k) % 2 = 1 := Finset.mem_filter.mp hk |>.2
      have hk2 : 2 * (y / 2^(k+1)) * 2^k + 2^k ≤ N := by
        have H : y / 2^k = 2 * (y / 2^(k+1)) + 1 := by
          simpa only [hk1] using div_mod_two_eq y k
        have H2_eq : 2 * (y / 2^(k+1)) * 2^k + 2^k = (y / 2^k) * 2^k := by
          calc
            2 * (y / 2^(k+1)) * 2^k + 2^k = (2 * (y / 2^(k+1)) + 1) * 2^k := by ring
            _ = (y / 2^k) * 2^k := by rw [← H]
        rw [H2_eq]
        exact (Nat.div_mul_le_self y (2^k)).trans hy2
      dsimp [blockStart, blockLength]
      rw [if_pos hk2]
      have h_sum := sum_Ioc_nat_eq_sum_Icc_int M (2 * (y / 2 ^ (k + 1)) * 2 ^ k)
        (2 * (y / 2 ^ (k + 1)) * 2 ^ k + 2 ^ k) f
      push_cast at h_sum
      simpa only [Nat.cast_pow, Nat.cast_ofNat, add_assoc] using h_sum
    · intro ⟨a, ha⟩ _ ⟨b, hb⟩ _ hab
      injection hab with h_eq
      injection h_eq with h_eq2
      ext
      exact h_eq2

  have hcard : ∀ y ∈ Finset.range (N + 1), (prefixBlocks y).card ≤ Nat.log2 N + 1 := by
    intro y _
    dsimp [prefixBlocks]
    split_ifs
    · apply le_trans Finset.card_image_le
      apply le_trans Finset.card_attach.le
      apply le_trans (Finset.card_filter_le _ _)
      exact (Finset.card_range _).le
    · simp

  have hlength : ∀ i, blockLength i ≤ N := by
    intro i
    dsimp [blockLength]
    split_ifs with h
    · omega
    · omega

  have hoverlap : (∑ i : ι, ∑ n ∈ Finset.Icc (blockStart i + 1) (blockStart i + blockLength i), ‖b n‖ ^ 2) ≤
        ((Nat.log2 N + 1 : ℕ) : ℝ) * ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    have H : (∑ k : Fin (Nat.log2 N + 1), ∑ j : Fin (N + 1),
      ∑ n ∈ Finset.Icc (blockStart (k, j) + 1) (blockStart (k, j) + blockLength (k, j)), ‖b n‖ ^ 2) ≤
      ∑ k : Fin (Nat.log2 N + 1), ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      -- At scale `k`, block `a` ends before block `b > a` starts.
      have hblockEnd_le_start (a b : ℕ) (hab : a < b) :
          (a : ℤ) * 2 ^ k.val + 2 ^ k.val ≤ (b : ℤ) * 2 ^ k.val := by
        have hsucc : a + 1 ≤ b := hab
        have hscaled := Nat.mul_le_mul_right (2 ^ k.val) hsucc
        exact_mod_cast (show a * 2 ^ k.val + 2 ^ k.val ≤ b * 2 ^ k.val by
          simpa only [Nat.add_mul, one_mul] using hscaled)
      apply sum_biUnion_le (Finset.univ) (fun j => Finset.Icc (blockStart (k, j) + 1) (blockStart (k, j) + blockLength (k, j)))
      · intro j1 _ j2 _ hneq
        dsimp [blockStart, blockLength]
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [Finset.mem_Icc] at hx1 hx2
        split_ifs at hx1 hx2 with h1 h2
        · push_cast at hx1 hx2
          have hlt : j1.val < j2.val ∨ j2.val < j1.val := by
            have : j1.val ≠ j2.val := by intro hh; apply hneq; ext; exact hh
            omega
          cases hlt with
          | inl h_lt =>
            have hsep := hblockEnd_le_start j1.val j2.val h_lt
            omega
          | inr h_lt =>
            have hsep := hblockEnd_le_start j2.val j1.val h_lt
            omega
        · omega
        · omega
        · omega
      · intro j _
        dsimp [blockStart, blockLength]
        split_ifs with h
        · intro x hx
          rw [Finset.mem_Icc] at hx ⊢
          push_cast at hx
          have h1 : 0 ≤ (j.val : ℤ) * (2 ^ k.val : ℤ) := by positivity
          have h2z : (j.val : ℤ) * (2 ^ k.val : ℤ) + (2 ^ k.val : ℤ) ≤ (N : ℤ) := by
            exact_mod_cast h
          omega
        · intro x hx
          rw [Finset.mem_Icc] at hx
          omega
      · intro x _
        positivity
    simpa [Finset.sum_const, nsmul_eq_mul] using H

  exact weighted_primitive_prefix_maximal_of_dyadic_decomposition b M N Q hQ blockStart blockLength prefixBlocks hdecomp hcard hlength hoverlap

end BombieriVinogradov
