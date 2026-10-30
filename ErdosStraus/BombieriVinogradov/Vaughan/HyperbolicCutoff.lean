import ErdosStraus.BombieriVinogradov.Reduction.Orthogonality
import ErdosStraus.BombieriVinogradov.Vaughan.PerronKernel

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

/-!
# The hyperbolic cutoff in Vaughan's Type II sum

The Type II prefix sum with cutoff `d e m ≤ y` splits over the `O(log² N)` dyadic
rectangles in `(d, e)` that meet the hyperbola, so its maximal prefix is at most
the sum of the maximal prefixes on these rectangles.  On a rectangle the sharp
cutoff `m n ≤ Y` is replaced by the damped arctangent Perron kernel at
`Y + 1/2`, whose Perron integral splits into four rank-one products bounded by
the weighted primitive large sieve.  The resulting bound for the weighted mean
of maximal prefixes is `rectangularSharpPrefixMaxMean_le`.
-/

/-! ## Dyadic decomposition of the Type II sum -/

namespace BombieriVinogradov

open Classical Finset
open scoped BigOperators ArithmeticFunction
noncomputable section

/-- The canonical dyadic rectangles `(k, l)` with `2^k 2^l ≤ N`; the others cannot
meet the hyperbola `d e m ≤ N` with `m ≥ 1`. -/
def vaughanTypeIIActiveCanonicalRectangles (N u v : ℕ) : Finset (ℕ × ℕ) :=
  (vaughanCanonicalDyadicRectangles N u v).filter
    (fun kl => 2 ^ kl.1 * 2 ^ kl.2 ≤ N)

@[simp] theorem mem_vaughanTypeIIActiveCanonicalRectangles {N u v : ℕ}
    {kl : ℕ × ℕ} :
    kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v ↔
      kl ∈ vaughanCanonicalDyadicRectangles N u v ∧
        2 ^ kl.1 * 2 ^ kl.2 ≤ N := by
  simp [vaughanTypeIIActiveCanonicalRectangles]

/-- The maximum over `y ≤ N` of the squared Type II block on the dyadic
rectangle `(k, l)`, with the cutoff `d e m ≤ y` kept exact. -/
def vaughanCanonicalCollectedPrefixMaxSquare
    (N u v k l q : ℕ) (χ : PrimitiveCharacter q) : ℝ :=
  ((Finset.range (N + 1)).image (fun y =>
      ‖vaughanTypeIICanonicalBilinearBlock (fun _ => 1)
        y N u v k l q χ‖ ^ 2)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

private lemma primitiveCharacterPrefixSquare_typeII_eq_full
    (y u v q : ℕ) (χ : PrimitiveCharacter q) :
    primitiveCharacterPrefixSquare
        (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) 0 y q χ =
      ‖vaughanTypeIIFullPrefix (fun _ => 1) y u v q χ‖ ^ 2 := by
  unfold primitiveCharacterPrefixSquare vaughanTypeIIFullPrefix
  simp only [zero_add]
  have hsum := sum_Ioc_nat_eq_sum_Icc_int 0 0 y
    (fun z => vaughanTypeIICoeff vaughanUnitIntegerCoeff u v z *
      χ.1 (z : ZMod q))
  have hset : Finset.Ioc 0 y = Finset.Icc 1 y := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hset] at hsum
  have hsum' :
      (∑ x ∈ Finset.Icc (1 : ℤ) y,
        vaughanTypeIICoeff vaughanUnitIntegerCoeff u v x * χ.1 (x : ZMod q)) =
      ∑ n ∈ Finset.Icc 1 y,
        vaughanTypeIICoeff vaughanUnitIntegerCoeff u v (n : ℤ) *
          χ.1 ((n : ℤ) : ZMod q) := by
    simpa using hsum.symm
  rw [hsum']
  have hterms :
      (∑ n ∈ Finset.Icc 1 y,
        vaughanTypeIICoeff vaughanUnitIntegerCoeff u v (n : ℤ) *
          χ.1 ((n : ℤ) : ZMod q)) =
      ∑ n ∈ Finset.Icc 1 y,
        1 * χ.1 (n : ZMod q) * vaughanTypeIIFullAt n u v := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [vaughanTypeIICoeff, vaughanUnitIntegerCoeff, one_mul,
      Int.toNat_natCast, vaughanTypeII, vaughanTypeIIFullAt_eq_vaughanThird,
      Int.cast_natCast]
    ring
  rw [hterms]

lemma vaughanTypeIICanonicalBilinearBlock_eq_zero_of_inactive
    {y N u v k l q : ℕ} (χ : PrimitiveCharacter q) (hyN : y ≤ N)
    (hinactive : N < 2 ^ k * 2 ^ l) :
    vaughanTypeIICanonicalBilinearBlock (fun _ => 1)
      y N u v k l q χ = 0 := by
  unfold vaughanTypeIICanonicalBilinearBlock
  apply Finset.sum_eq_zero
  intro d hd
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro e he
  apply mul_eq_zero_of_right
  have hde : N < d * e := by
    have hdk : 2 ^ k ≤ d := (vaughanCanonicalDyadicBlock_pow_bounds hd).1
    have hel : 2 ^ l ≤ e := (vaughanCanonicalDyadicBlock_pow_bounds he).1
    exact hinactive.trans_le (Nat.mul_le_mul hdk hel)
  have hdiv : y / (d * e) = 0 := Nat.div_eq_of_lt (hyN.trans_lt hde)
  simp [hdiv]

/-- For `y ≤ N`, the Type II prefix sum up to `y` is the sum of its blocks over
the dyadic rectangles with `2^k 2^l ≤ N`. -/
theorem vaughanTypeIIFullPrefix_eq_sum_active_canonical
    (y N u v q : ℕ) (χ : PrimitiveCharacter q) (hyN : y ≤ N) :
    vaughanTypeIIFullPrefix (fun _ => 1) y u v q χ =
      ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
        vaughanTypeIICanonicalBilinearBlock (fun _ => 1)
          y N u v kl.1 kl.2 q χ := by
  rw [vaughanTypeIIFullPrefix_eq_sum_canonical_bilinear
    (fun _ => 1) y N u v q χ hyN]
  rw [← Finset.sum_product (f := fun kl : ℕ × ℕ =>
    vaughanTypeIICanonicalBilinearBlock (fun _ => 1) y N u v kl.1 kl.2 q χ)]
  rw [vaughanTypeIIActiveCanonicalRectangles, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro kl hkl
  by_cases hactive : 2 ^ kl.1 * 2 ^ kl.2 ≤ N
  · simp [hactive]
  · rw [if_neg hactive]
    exact vaughanTypeIICanonicalBilinearBlock_eq_zero_of_inactive χ hyN
      (Nat.lt_of_not_ge hactive)

/-- The maximal Type II prefix for a primitive character is at most the sum,
over the rectangles meeting the hyperbola, of the maximal prefixes on each
rectangle. -/
theorem primitivePrefixAmplitude_vaughanTypeII_le_sum
    (N u v q : ℕ) (χ : PrimitiveCharacter q) :
    primitivePrefixAmplitude
        (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N q χ ≤
      ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
        Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare
          N u v kl.1 kl.2 q χ) := by
  let R : ℝ := ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
    Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare
      N u v kl.1 kl.2 q χ)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  change Real.sqrt (primitiveCharacterPrefixMaxSquare
    (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) 0 N q χ) ≤ R
  rw [← Real.sqrt_sq hR]
  apply Real.sqrt_le_sqrt
  unfold primitiveCharacterPrefixMaxSquare
  apply Finset.max'_le
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  have hyN : y ≤ N := by simpa [Finset.mem_range] using hy
  rw [primitiveCharacterPrefixSquare_typeII_eq_full]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  rw [vaughanTypeIIFullPrefix_eq_sum_active_canonical y N u v q χ hyN]
  calc
    ‖∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
        vaughanTypeIICanonicalBilinearBlock (fun _ => 1)
          y N u v kl.1 kl.2 q χ‖
      ≤ ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
          ‖vaughanTypeIICanonicalBilinearBlock (fun _ => 1)
            y N u v kl.1 kl.2 q χ‖ := norm_sum_le _ _
    _ ≤ R := by
      dsimp [R]
      apply Finset.sum_le_sum
      intro kl hkl
      rw [← Real.sqrt_sq (norm_nonneg _)]
      apply Real.sqrt_le_sqrt
      unfold vaughanCanonicalCollectedPrefixMaxSquare
      apply Finset.le_max'
      exact Finset.mem_image.mpr ⟨y, by simp [hyN], rfl⟩

theorem card_vaughanTypeIIActiveCanonicalRectangles_le (N u v : ℕ) :
    (vaughanTypeIIActiveCanonicalRectangles N u v).card ≤
      (Nat.log 2 N + 1) ^ 2 := by
  exact (Finset.card_filter_le _ _).trans
    (card_vaughanCanonicalDyadicRectangles_le N u v)

end

end BombieriVinogradov

namespace BombieriVinogradov

open Classical Finset
open scoped BigOperators
noncomputable section

/-!
## Rank-one rectangles

On a rectangle `(Ma, Ma + Na] × (Mb, Mb + Nb]`, the weighted primitive mean of
`|∑ a_m χ(m)| |∑ b_n χ(n)|` is bounded by Cauchy–Schwarz and the weighted
primitive large sieve applied to each factor.
-/

/-- `∑_{q ∈ S} (q / φ(q)) ∑_χ |∑_m a_m χ(m)| |∑_n b_n χ(n)|`, over primitive `χ`
mod `q`, with `m ∈ (Ma, Ma + Na]` and `n ∈ (Mb, Mb + Nb]`. -/
def rankOneRectangularWeightedPrimitiveMean
    (a b : ℤ → ℂ) (Ma Mb : ℤ) (Na Nb : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
    ∑ χ : PrimitiveCharacter q,
      ‖∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
          a m * χ.1 (m : ZMod q)‖ *
        ‖∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
          b n * χ.1 (n : ZMod q)‖

lemma rankOneRectangularWeightedPrimitiveMean_nonneg
    (a b : ℤ → ℂ) (Ma Mb : ℤ) (Na Nb : ℕ) (S : Finset ℕ) :
    0 ≤ rankOneRectangularWeightedPrimitiveMean a b Ma Mb Na Nb S := by
  unfold rankOneRectangularWeightedPrimitiveMean
  positivity

/-- The square of the rank-one mean is at most the product of the two weighted
primitive large sieve bounds, by Cauchy–Schwarz over the pairs `(q, χ)`. -/
theorem rankOneRectangularWeightedPrimitiveMean_sq_le
    (a b : ℤ → ℂ) (Ma Mb : ℤ) (Na Nb Q : ℕ) (hQ : 0 < Q)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q) :
    rankOneRectangularWeightedPrimitiveMean a b Ma Mb Na Nb S ^ 2 ≤
      (largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
        ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖a m‖ ^ 2) *
      (largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
        ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖b n‖ ^ 2) := by
  let w : ℕ → ℝ := fun q => (q : ℝ) / (q.totient : ℝ)
  let A : (q : ℕ) → PrimitiveCharacter q → ℝ := fun q χ =>
    ‖∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), a m * χ.1 (m : ZMod q)‖
  let B : (q : ℕ) → PrimitiveCharacter q → ℝ := fun q χ =>
    ‖∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), b n * χ.1 (n : ZMod q)‖
  let T := S.sigma (fun q => (Finset.univ : Finset (PrimitiveCharacter q)))
  have hflat : rankOneRectangularWeightedPrimitiveMean a b Ma Mb Na Nb S =
      ∑ x ∈ T, (Real.sqrt (w x.1)) * A x.1 x.2 *
        ((Real.sqrt (w x.1)) * B x.1 x.2) := by
    unfold rankOneRectangularWeightedPrimitiveMean
    dsimp [T]
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    have hw : 0 ≤ w q := by dsimp [w]; positivity
    calc
      ((q : ℝ) / (q.totient : ℝ)) * (A q χ * B q χ) =
          (Real.sqrt (w q) * Real.sqrt (w q)) * (A q χ * B q χ) := by
            rw [Real.mul_self_sqrt hw]
      _ = Real.sqrt (w q) * A q χ * (Real.sqrt (w q) * B q χ) := by ring
  rw [hflat]
  refine (Finset.sum_mul_sq_le_sq_mul_sq T
    (fun x => Real.sqrt (w x.1) * A x.1 x.2)
    (fun x => Real.sqrt (w x.1) * B x.1 x.2)).trans ?_
  have hsquare_flat (F : (q : ℕ) → PrimitiveCharacter q → ℝ) :
      (∑ x ∈ T, (Real.sqrt (w x.1) * F x.1 x.2) ^ 2) =
        ∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q, F q χ ^ 2 := by
    dsimp [T]
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    have hw : 0 ≤ w q := by dsimp [w]; positivity
    rw [mul_pow, Real.sq_sqrt hw]
  have hlarge (c : ℤ → ℂ) (M : ℤ) (L : ℕ) :
      (∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q,
        ‖∑ n ∈ Finset.Icc (M + 1) (M + L), c n * χ.1 (n : ZMod q)‖ ^ 2) ≤
      largeSieveBound L (1 / (Q : ℝ) ^ 2) *
        ∑ n ∈ Finset.Icc (M + 1) (M + L), ‖c n‖ ^ 2 := by
    calc
      _ ≤
          ∑ q ∈ Finset.Icc 1 Q,
            w q * ∑ χ : PrimitiveCharacter q,
              ‖∑ n ∈ Finset.Icc (M + 1) (M + L), c n * χ.1 (n : ZMod q)‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hS
        intro q hq hnot
        exact mul_nonneg (by dsimp [w]; positivity)
          (Finset.sum_nonneg fun χ hχ => sq_nonneg _)
      _ ≤ _ := by
        simpa [w] using weighted_primitive_bombieri_davenport c M L Q hQ
  rw [hsquare_flat A, hsquare_flat B]
  apply mul_le_mul
  · exact hlarge a Ma Na
  · exact hlarge b Mb Nb
  · exact Finset.sum_nonneg fun q hq => mul_nonneg (by dsimp [w]; positivity)
      (Finset.sum_nonneg fun χ hχ => sq_nonneg _)
  · unfold largeSieveBound
    positivity

/-- Square-root form of `rankOneRectangularWeightedPrimitiveMean_sq_le`. -/
theorem rankOneRectangularWeightedPrimitiveMean_le
    (a b : ℤ → ℂ) (Ma Mb : ℤ) (Na Nb Q : ℕ) (hQ : 0 < Q)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q) :
    rankOneRectangularWeightedPrimitiveMean a b Ma Mb Na Nb S ≤
      Real.sqrt (largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
        ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖a m‖ ^ 2) *
      Real.sqrt (largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
        ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖b n‖ ^ 2) := by
  have hs := rankOneRectangularWeightedPrimitiveMean_sq_le
    a b Ma Mb Na Nb Q hQ S hS
  have hA : 0 ≤ largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
      ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖a m‖ ^ 2 := by
    unfold largeSieveBound
    positivity
  have hB : 0 ≤ largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
      ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖b n‖ ^ 2 := by
    unfold largeSieveBound
    positivity
  have hright : 0 ≤
      Real.sqrt (largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
        ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖a m‖ ^ 2) *
      Real.sqrt (largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
        ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖b n‖ ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  apply (sq_le_sq₀ (rankOneRectangularWeightedPrimitiveMean_nonneg
    a b Ma Mb Na Nb S) hright).mp
  rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]
  exact hs

/-!
## Sine and cosine twists

Twisting a coefficient sequence by `sin(t x)` or `cos(t x)`, with `|x| ≤ L`,
multiplies its `ℓ²` norm squared by at most `min(1, L |t|)²` or `1`.
-/

theorem log_div_int_mul_eq_sub_log_sub_log
    {y : ℝ} {m n : ℤ} (hy : 0 < y) (hm : 0 < m) (hn : 0 < n) :
    Real.log (y / ((m * n : ℤ) : ℝ)) =
      (Real.log y - Real.log (m : ℝ)) - Real.log (n : ℝ) := by
  rw [Real.log_div hy.ne' (by positivity : (((m * n : ℤ) : ℝ) ≠ 0))]
  rw [show (((m * n : ℤ) : ℝ) = (m : ℝ) * (n : ℝ)) by norm_num]
  rw [Real.log_mul (by positivity : (m : ℝ) ≠ 0) (by positivity : (n : ℝ) ≠ 0)]
  ring

/-- The twisted coefficient `a_m sin(t (log y - log m))`. -/
def leftSinTwist (a : ℤ → ℂ) (y t : ℝ) (m : ℤ) : ℂ :=
  a m * (Real.sin (t * (Real.log y - Real.log (m : ℝ))) : ℂ)

/-- The twisted coefficient `a_m cos(t (log y - log m))`. -/
def leftCosTwist (a : ℤ → ℂ) (y t : ℝ) (m : ℤ) : ℂ :=
  a m * (Real.cos (t * (Real.log y - Real.log (m : ℝ))) : ℂ)

/-- The twisted coefficient `b_n sin(t log n)`. -/
def rightSinTwist (b : ℤ → ℂ) (t : ℝ) (n : ℤ) : ℂ :=
  b n * (Real.sin (t * Real.log (n : ℝ)) : ℂ)

/-- The twisted coefficient `b_n cos(t log n)`. -/
def rightCosTwist (b : ℤ → ℂ) (t : ℝ) (n : ℤ) : ℂ :=
  b n * (Real.cos (t * Real.log (n : ℝ)) : ℂ)

/-- The rectangular character sum `∑_{m, n} a_m b_n χ(m n) sin(t log(y / (m n))) / t`
(with value `log(y / (m n))` at `t = 0`). -/
def rectangularKernelCharacterSum
    (a b : ℤ → ℂ) (y t : ℝ) (Ma Mb : ℤ) (Na Nb q : ℕ)
    (χ : PrimitiveCharacter q) : ℂ :=
  ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
    ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
      a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
        (truncatedPerronIntegrand (Real.log (y / ((m * n : ℤ) : ℝ))) t : ℂ)

/-- Uses `|sin x| ≤ min(1, |x|)`. -/
theorem sum_norm_sq_leftSinTwist_le
    (a : ℤ → ℂ) (y t L : ℝ) (s : Finset ℤ)
    (hL : 0 ≤ L) (hlog : ∀ m ∈ s, |Real.log y - Real.log (m : ℝ)| ≤ L) :
    ∑ m ∈ s, ‖leftSinTwist a y t m‖ ^ 2 ≤
      (min 1 (L * |t|)) ^ 2 * ∑ m ∈ s, ‖a m‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  simp only [leftSinTwist, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have hs1 : |Real.sin (t * (Real.log y - Real.log (m : ℝ)))| ≤ 1 :=
    Real.abs_sin_le_one _
  have hsL : |Real.sin (t * (Real.log y - Real.log (m : ℝ)))| ≤ L * |t| := by
    calc
      |Real.sin (t * (Real.log y - Real.log (m : ℝ)))| ≤
          |t * (Real.log y - Real.log (m : ℝ))| := Real.abs_sin_le_abs
      _ = |t| * |Real.log y - Real.log (m : ℝ)| := abs_mul _ _
      _ ≤ |t| * L := mul_le_mul_of_nonneg_left (hlog m hm) (abs_nonneg t)
      _ = L * |t| := by ring
  have hs : |Real.sin (t * (Real.log y - Real.log (m : ℝ)))| ≤ min 1 (L * |t|) :=
    le_min hs1 hsL
  have hmin : 0 ≤ min 1 (L * |t|) :=
    le_min (by norm_num) (mul_nonneg hL (abs_nonneg t))
  have hs2 : |Real.sin (t * (Real.log y - Real.log (m : ℝ)))| ^ 2 ≤
      min 1 (L * |t|) ^ 2 := (sq_le_sq₀ (abs_nonneg _) hmin).2 hs
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hs2 (sq_nonneg ‖a m‖)

theorem sum_norm_sq_leftCosTwist_le
    (a : ℤ → ℂ) (y t : ℝ) (s : Finset ℤ) :
    ∑ m ∈ s, ‖leftCosTwist a y t m‖ ^ 2 ≤ ∑ m ∈ s, ‖a m‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro m hm
  simp only [leftCosTwist, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have hc := Real.abs_cos_le_one (t * (Real.log y - Real.log (m : ℝ)))
  have hc2 : |Real.cos (t * (Real.log y - Real.log (m : ℝ)))| ^ 2 ≤ 1 := by
    nlinarith [abs_nonneg (Real.cos (t * (Real.log y - Real.log (m : ℝ))))]
  simpa using mul_le_mul_of_nonneg_left hc2 (sq_nonneg ‖a m‖)

theorem sum_norm_sq_rightSinTwist_le
    (b : ℤ → ℂ) (t L : ℝ) (s : Finset ℤ)
    (hL : 0 ≤ L) (hlog : ∀ n ∈ s, |Real.log (n : ℝ)| ≤ L) :
    ∑ n ∈ s, ‖rightSinTwist b t n‖ ^ 2 ≤
      (min 1 (L * |t|)) ^ 2 * ∑ n ∈ s, ‖b n‖ ^ 2 := by
  -- At `y = 1`, the left sine twist differs only by a sign.
  simpa [leftSinTwist, rightSinTwist, mul_neg, Real.sin_neg] using
    sum_norm_sq_leftSinTwist_le b 1 t L s hL (by simpa using hlog)

theorem sum_norm_sq_rightCosTwist_le
    (b : ℤ → ℂ) (t : ℝ) (s : Finset ℤ) :
    ∑ n ∈ s, ‖rightCosTwist b t n‖ ^ 2 ≤ ∑ n ∈ s, ‖b n‖ ^ 2 := by
  -- Cosine is even, so the left twist at `y = 1` is the right twist.
  simpa [leftCosTwist, rightCosTwist, mul_neg, Real.cos_neg] using
    sum_norm_sq_leftCosTwist_le b 1 t s

theorem abs_log_int_le_log
    {M : ℕ} (_hM : 1 ≤ M) {n : ℤ} (hn1 : 1 ≤ n) (hnM : n ≤ (M : ℤ)) :
    |Real.log (n : ℝ)| ≤ Real.log (M : ℝ) := by
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnMreal : (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hnM
  rw [abs_of_nonneg (Real.log_nonneg hnreal)]
  exact Real.log_le_log (by positivity) hnMreal

/-- The lower bound `1/2 ≤ y` is needed: it gives `y / m ≥ M⁻²`. -/
theorem abs_log_div_int_le_two_log
    {M : ℕ} (hM : 3 ≤ M) {y : ℝ} (hy0 : 1 / 2 ≤ y)
    (hyM : y ≤ (M : ℝ) + 1 / 2) {m : ℤ} (hm1 : 1 ≤ m) (hmM : m ≤ (M : ℤ)) :
    |Real.log y - Real.log (m : ℝ)| ≤ 2 * Real.log (M : ℝ) := by
  have hMr : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMrpos : 0 < (M : ℝ) := lt_of_lt_of_le (by norm_num) hMr

  have hmreal1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmrealM : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
  have hmrealpos : 0 < (m : ℝ) := lt_of_lt_of_le (by norm_num) hmreal1
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num) hy0
  have hloRatio : 1 / (M : ℝ) ^ 2 ≤ y / (m : ℝ) := by
    apply (le_div_iff₀ hmrealpos).2
    have hmHalf : (m : ℝ) / (M : ℝ) ^ 2 ≤ 1 / 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos hMrpos)).2
      nlinarith [hmrealM]
    calc
      (1 / (M : ℝ) ^ 2) * (m : ℝ) = (m : ℝ) / (M : ℝ) ^ 2 := by ring
      _ ≤ 1 / 2 := hmHalf
      _ ≤ y := hy0
  have hhiRatio : y / (m : ℝ) ≤ (M : ℝ) ^ 2 := by
    apply (div_le_iff₀ hmrealpos).2
    have hMsq : (M : ℝ) + 1 / 2 ≤ (M : ℝ) ^ 2 := by nlinarith
    have hySq : y ≤ (M : ℝ) ^ 2 := hyM.trans hMsq
    calc
      y ≤ (M : ℝ) ^ 2 := hySq
      _ = (M : ℝ) ^ 2 * 1 := by ring
      _ ≤ (M : ℝ) ^ 2 * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hmreal1 (sq_nonneg (M : ℝ))
  have hlogLo : -2 * Real.log (M : ℝ) ≤ Real.log (y / (m : ℝ)) := by
    have h := Real.log_le_log (by positivity : 0 < 1 / (M : ℝ) ^ 2) hloRatio
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one, zero_sub,
      Real.log_pow] at h
    simpa [two_mul] using h
  have hlogHi : Real.log (y / (m : ℝ)) ≤ 2 * Real.log (M : ℝ) := by
    have h := Real.log_le_log (by positivity : 0 < y / (m : ℝ)) hhiRatio
    rw [Real.log_pow] at h
    simpa [two_mul] using h
  rw [← Real.log_div hypos.ne' hmrealpos.ne']
  exact (abs_le).2 ⟨by simpa only [neg_mul] using hlogLo, hlogHi⟩

theorem sum_norm_sq_rightSinTwist_Icc_le
    (b : ℤ → ℂ) (t : ℝ) (Mb : ℤ) (Nb M : ℕ)
    (hM : 1 ≤ M)
    (hn1 : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 1 ≤ n)
    (hnM : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), n ≤ (M : ℤ)) :
    ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖rightSinTwist b t n‖ ^ 2 ≤
      (min 1 (Real.log (M : ℝ) * |t|)) ^ 2 *
        ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖b n‖ ^ 2 := by
  apply sum_norm_sq_rightSinTwist_le
  · exact Real.log_nonneg (by exact_mod_cast hM)
  · intro n hn
    exact abs_log_int_le_log hM (hn1 n hn) (hnM n hn)

end

end BombieriVinogradov

/-!
## The damped Perron kernel on a rectangle

The damped kernel sum is `1/2` times a rank-one product plus `1/π` times an
integral over `t > 0` of truncated Perron sums.  With `y = Y + 1/2` and
`ε = M⁻²` it differs from the sum over `m n ≤ Y` by at most `8 / (π M)` times
the `ℓ¹` mass of the coefficients.
-/

namespace BombieriVinogradov

open Classical Finset MeasureTheory Set
open scoped BigOperators
noncomputable section

/-- The rectangular character sum weighted by the damped arctangent kernel
`1/2 + arctan(log(y / (m n)) / ε) / π`. -/
def rectangularSmoothedKernelCharacterSum
    (a b : ℤ → ℂ) (ε y : ℝ) (Ma Mb : ℤ) (Na Nb q : ℕ)
    (χ : PrimitiveCharacter q) : ℂ :=
  ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
    ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
      a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
        (dampedArctanPerronKernel ε
          (Real.log (y / ((m * n : ℤ) : ℝ))) : ℂ)

/-- The rectangular character sum restricted to the hyperbola `m n ≤ Y`. -/
def rectangularSharpHyperbolicCharacterSum
    (a b : ℤ → ℂ) (Y : ℕ) (Ma Mb : ℤ) (Na Nb q : ℕ)
    (χ : PrimitiveCharacter q) : ℂ :=
  ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
    ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
      a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
        (if m * n ≤ (Y : ℤ) then 1 else 0)

/-- The right-hand side of `rankOneRectangularWeightedPrimitiveMean_le`. -/
def rankOneRectangularLSRHS
    (a b : ℤ → ℂ) (Ma Mb : ℤ) (Na Nb Q : ℕ) : ℝ :=
  Real.sqrt (largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
    ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖a m‖ ^ 2) *
  Real.sqrt (largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
    ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖b n‖ ^ 2)

/-- `(∑_m |a_m|) (∑_n |b_n|)` over the rectangle. -/
def rectangularCoefficientL1
    (a b : ℤ → ℂ) (Ma Mb : ℤ) (Na Nb : ℕ) : ℝ :=
  (∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖a m‖) *
  (∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖b n‖)

/-- `∑_{q ∈ S} (q / φ(q))` times the number of primitive characters mod `q`. -/
def weightedPrimitiveFamilyMass (S : Finset ℕ) : ℝ :=
  ∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) * Fintype.card (PrimitiveCharacter q)

/-- For `ε > 0` the damped kernel sum equals `1/2` times the rank-one product plus
`(1/π) ∫_0^∞ e^{-εt}` times the truncated Perron sum, and this integrand is
integrable. -/
theorem rectangularDampedPerron_integrable_formula
    (a b : ℤ → ℂ) (ε y : ℝ) (hε : 0 < ε)
    (Ma Mb : ℤ) (Na Nb : ℕ) :
    ∀ q (χ : PrimitiveCharacter q),
      IntegrableOn (fun t : ℝ => (Real.exp (-ε * t) : ℂ) *
        rectangularKernelCharacterSum a b y t Ma Mb Na Nb q χ) (Set.Ioi 0) ∧
      rectangularSmoothedKernelCharacterSum a b ε y Ma Mb Na Nb q χ =
        (1 / 2 : ℂ) *
          ((∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), a m * χ.1 (m : ZMod q)) *
            (∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), b n * χ.1 (n : ZMod q))) +
        (1 / Real.pi : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
          (Real.exp (-ε * t) : ℂ) *
            rectangularKernelCharacterSum a b y t Ma Mb Na Nb q χ := by
  let sM := Finset.Icc (Ma + 1) (Ma + Na)
  let sN := Finset.Icc (Mb + 1) (Mb + Nb)
  have hscalarInt : ∀ m n : ℤ, Integrable (fun t : ℝ =>
      Real.exp (-ε * t) *
        truncatedPerronIntegrand (Real.log (y / ((m * n : ℤ) : ℝ))) t)
      (volume.restrict (Set.Ioi 0)) := by
    intro m n
    have he : Integrable (fun t : ℝ => Real.exp (-ε * t)) (volume.restrict (Set.Ioi 0)) :=
      integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hε) 0
    apply he.mul_bdd
    · exact (continuous_truncatedPerronIntegrand_right
        (Real.log (y / ((m * n : ℤ) : ℝ)))).aestronglyMeasurable
    · filter_upwards with t
      simpa [Real.norm_eq_abs] using abs_truncatedPerronIntegrand_le
        (Real.log (y / ((m * n : ℤ) : ℝ))) t
  have htermInt : ∀ q (χ : PrimitiveCharacter q) (m : ℤ), m ∈ sM →
      ∀ n ∈ sN,
      Integrable (fun t : ℝ =>
        (Real.exp (-ε * t) : ℂ) *
          (a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
            (truncatedPerronIntegrand
              (Real.log (y / ((m * n : ℤ) : ℝ))) t : ℂ)))
        (volume.restrict (Set.Ioi 0)) := by
    intro q χ m hm' n hn'
    have hg : Integrable (fun t : ℝ =>
        (Real.exp (-ε * t) : ℂ) *
          (truncatedPerronIntegrand (Real.log (y / ((m * n : ℤ) : ℝ))) t : ℂ))
        (volume.restrict (Set.Ioi 0)) := by
      have hs := (hscalarInt m n).ofReal (𝕜 := ℂ)
      convert hs using 1
      funext t
      rw [← Complex.ofReal_mul]
      rfl
    convert hg.mul_const (a m * b n * χ.1 ((m * n : ℤ) : ZMod q)) using 1;
      funext t; ring
  let F : (q : ℕ) → PrimitiveCharacter q → ℝ → ℂ := fun q χ t =>
    (Real.exp (-ε * t) : ℂ) *
      rectangularKernelCharacterSum a b y t Ma Mb Na Nb q χ
  have hFint : ∀ q (χ : PrimitiveCharacter q), IntegrableOn (F q χ) (Set.Ioi 0) := by
    intro q χ
    unfold F rectangularKernelCharacterSum
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum sM fun m hm' =>
      integrable_finsetSum sN (htermInt q χ m hm')
  have hkernel : ∀ q (χ : PrimitiveCharacter q),
      rectangularSmoothedKernelCharacterSum a b ε y Ma Mb Na Nb q χ =
        (1 / 2 : ℂ) *
          ((∑ m ∈ sM, a m * χ.1 (m : ZMod q)) *
            (∑ n ∈ sN, b n * χ.1 (n : ZMod q))) +
        (1 / Real.pi : ℂ) * ∫ t in Set.Ioi (0 : ℝ), F q χ t := by
    intro q χ
    unfold rectangularSmoothedKernelCharacterSum
    have hi : (∫ t in Set.Ioi (0 : ℝ), F q χ t) =
        ∑ m ∈ sM, ∑ n ∈ sN,
          a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
            (∫ t in Set.Ioi (0 : ℝ),
              (Real.exp (-ε * t) *
                truncatedPerronIntegrand
                  (Real.log (y / ((m * n : ℤ) : ℝ))) t : ℂ)) := by
      unfold F rectangularKernelCharacterSum
      simp_rw [Finset.mul_sum]
      rw [integral_finsetSum sM]
      · apply Finset.sum_congr rfl
        intro m hm'
        rw [integral_finsetSum sN]
        · apply Finset.sum_congr rfl
          intro n hn'
          rw [← MeasureTheory.integral_const_mul]
          congr 1
          funext t
          push_cast
          ring
        · intro n hn'
          exact htermInt q χ m hm' n hn'
      · intro m hm'
        exact integrable_finsetSum sN (htermInt q χ m hm')
    rw [hi]
    have hprod :
        ((∑ m ∈ sM, a m * χ.1 (m : ZMod q)) *
          (∑ n ∈ sN, b n * χ.1 (n : ZMod q))) =
        ∑ m ∈ sM, ∑ n ∈ sN,
          (a m * χ.1 (m : ZMod q)) * (b n * χ.1 (n : ZMod q)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m hm'
      rw [Finset.mul_sum]
    rw [hprod]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm'
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn'
    rw [dampedArctanPerronKernel_eq_half_add_integral _ _ hε]
    rw [Int.cast_mul, map_mul]
    have hcast :
        ((∫ t in Set.Ioi (0 : ℝ), Real.exp (-ε * t) *
          truncatedPerronIntegrand (Real.log (y / ((m * n : ℤ) : ℝ))) t : ℝ) : ℂ) =
        ∫ t in Set.Ioi (0 : ℝ),
          (Real.exp (-ε * t) * truncatedPerronIntegrand
            (Real.log (y / ((m * n : ℤ) : ℝ))) t : ℂ) := by
      simpa only [Complex.ofRealCLM_apply, ← Complex.ofReal_mul] using
        (Complex.ofRealCLM.integral_comp_comm (hscalarInt m n)).symm
    have hformula :
        ((1 / 2 + (1 / Real.pi) *
          ∫ t in Set.Ioi (0 : ℝ), Real.exp (-ε * t) *
            truncatedPerronIntegrand (Real.log (y / ((m * n : ℤ) : ℝ))) t : ℝ) : ℂ) =
          (1 / 2 : ℂ) + (1 / Real.pi : ℂ) *
            ((∫ t in Set.Ioi (0 : ℝ), Real.exp (-ε * t) *
              truncatedPerronIntegrand (Real.log (y / ((m * n : ℤ) : ℝ))) t : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hformula]
    rw [hcast]
    ring
  exact fun q χ => ⟨hFint q χ, hkernel q χ⟩

/-- If the `ℓ²` norms squared of `c` and `d` are at most `u²` and `v²` times those of
`a` and `b`, the rank-one mean of `(c, d)` is at most `u v` times the large sieve
bound for `(a, b)`. -/
theorem rankOneRectangularWeightedPrimitiveMean_le_scaled_energy
    (a b c d : ℤ → ℂ) (Ma Mb : ℤ) (Na Nb Q : ℕ)
    (hQ : 0 < Q) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hc : ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖c m‖ ^ 2 ≤
      u ^ 2 * ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖a m‖ ^ 2)
    (hd : ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖d n‖ ^ 2 ≤
      v ^ 2 * ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖b n‖ ^ 2) :
    rankOneRectangularWeightedPrimitiveMean c d Ma Mb Na Nb S ≤
      (u * v) * rankOneRectangularLSRHS a b Ma Mb Na Nb Q := by
  have hsqrt (K A C r : ℝ) (hK : 0 ≤ K) (hr : 0 ≤ r)
      (hC : C ≤ r ^ 2 * A) : Real.sqrt (K * C) ≤ r * Real.sqrt (K * A) := by
    calc
      Real.sqrt (K * C) ≤ Real.sqrt (K * (r ^ 2 * A)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hC hK)
      _ = r * Real.sqrt (K * A) := by
        rw [show K * (r ^ 2 * A) = r ^ 2 * (K * A) by ring,
          Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr]
  refine (rankOneRectangularWeightedPrimitiveMean_le c d Ma Mb Na Nb Q hQ S hS).trans ?_
  unfold rankOneRectangularLSRHS
  calc
    _ ≤ (u * Real.sqrt (largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
          ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖a m‖ ^ 2)) *
        (v * Real.sqrt (largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
          ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖b n‖ ^ 2)) :=
      mul_le_mul (hsqrt _ _ _ _ (by unfold largeSieveBound; positivity) hu hc)
        (hsqrt _ _ _ _ (by unfold largeSieveBound; positivity) hv hd)
        (Real.sqrt_nonneg _) (mul_nonneg hu (Real.sqrt_nonneg _))
    _ = _ := by ring

theorem dampedPerron_weighted_norm_integrable
    (S : Finset ℕ) (w : ℕ → ℝ)
    (F : (q : ℕ) → PrimitiveCharacter q → ℝ → ℂ) (μ : Measure ℝ)
    (hF : ∀ q χ, Integrable (F q χ) μ) :
    Integrable (fun t => ∑ q ∈ S, w q * ∑ χ, ‖F q χ t‖) μ :=
  integrable_finsetSum S fun q _ =>
    (integrable_finsetSum Finset.univ fun χ _ => (hF q χ).norm).const_mul _

theorem dampedPerron_weighted_norm_integral_le
    (S : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ q ∈ S, 0 ≤ w q)
    (F : (q : ℕ) → PrimitiveCharacter q → ℝ → ℂ) (μ : Measure ℝ)
    (hF : ∀ q χ, Integrable (F q χ) μ) :
    (∑ q ∈ S, w q * ∑ χ, ‖∫ t, F q χ t ∂μ‖) ≤
      ∫ t, (∑ q ∈ S, w q * ∑ χ, ‖F q χ t‖) ∂μ := by
  calc
    _ ≤ ∑ q ∈ S, w q * ∑ χ, ∫ t, ‖F q χ t‖ ∂μ :=
      Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun χ _ => norm_integral_le_integral_norm _) (hw q hq)
    _ = _ := by
      rw [integral_finsetSum S]
      · apply Finset.sum_congr rfl
        intro q hq
        rw [integral_const_mul, integral_finsetSum Finset.univ]
        exact fun χ _ => (hF q χ).norm
      · exact fun q _ =>
          (integrable_finsetSum Finset.univ fun χ _ => (hF q χ).norm).const_mul _

theorem dampedPerron_weighted_norm_add_le
    (S : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ q ∈ S, 0 ≤ w q)
    (D I : (q : ℕ) → PrimitiveCharacter q → ℂ)
    (p r : ℝ) (hp : 0 ≤ p) (hr : 0 ≤ r) :
    (∑ q ∈ S, w q * ∑ χ, ‖(p : ℂ) * D q χ + (r : ℂ) * I q χ‖) ≤
      p * (∑ q ∈ S, w q * ∑ χ, ‖D q χ‖) +
        r * (∑ q ∈ S, w q * ∑ χ, ‖I q χ‖) := by
  calc
    _ ≤ ∑ q ∈ S, w q * ∑ χ, (p * ‖D q χ‖ + r * ‖I q χ‖) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (hw q hq)
      apply Finset.sum_le_sum
      intro χ hχ
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hp, abs_of_nonneg hr] using
        norm_add_le ((p : ℂ) * D q χ) ((r : ℂ) * I q χ)
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add, mul_left_comm]

/-- If `G ≤ (K_{L₁} + K_{L₂}) R` on `t > 0`, where `K_L(t) = e^{-εt} min(1, L t) / t`,
then `∫_0^∞ G ≤ (L₁ + L₂ + 2 log(1/ε) + 2) R`. -/
theorem dampedPerron_integral_le_two_majorants
    {ε L₁ L₂ R : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hR : 0 ≤ R)
    {G : ℝ → ℝ} (hGint : IntegrableOn G (Set.Ioi 0))
    (hG : ∀ t ∈ Set.Ioi (0 : ℝ), G t ≤
      (dampedPerronMajorantIntegrand ε L₁ t +
        dampedPerronMajorantIntegrand ε L₂ t) * R) :
    (∫ t in Set.Ioi (0 : ℝ), G t) ≤
      ((L₁ + Real.log (1 / ε) + 1) + (L₂ + Real.log (1 / ε) + 1)) * R := by
  have h₁ := dampedPerronMajorant_integrableOn_Ioi hε hL₁
  have h₂ := dampedPerronMajorant_integrableOn_Ioi hε hL₂
  calc
    (∫ t in Set.Ioi (0 : ℝ), G t) ≤
        ∫ t in Set.Ioi (0 : ℝ),
          (dampedPerronMajorantIntegrand ε L₁ t +
            dampedPerronMajorantIntegrand ε L₂ t) * R :=
      setIntegral_mono_on hGint ((h₁.add h₂).mul_const R) measurableSet_Ioi hG
    _ = ((∫ t in Set.Ioi (0 : ℝ), dampedPerronMajorantIntegrand ε L₁ t) +
          (∫ t in Set.Ioi (0 : ℝ), dampedPerronMajorantIntegrand ε L₂ t)) * R := by
      rw [integral_mul_const, integral_add h₁ h₂]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (add_le_add (dampedPerronMajorant_integral_Ioi_le hε hε1 hL₁)
        (dampedPerronMajorant_integral_Ioi_le hε hε1 hL₂)) hR

/-- Replacing the cutoff `m n ≤ Y` by the damped kernel at `Y + 1/2` with
`ε = M⁻²` costs at most `8 / (π M)` times the `ℓ¹` mass of the coefficients. -/
theorem rectangularSharpHyperbolicCharacterSum_norm_le_smoothed
    (a b : ℤ → ℂ) (Y M : ℕ) (Ma Mb : ℤ) (Na Nb : ℕ)
    (hM : 1 ≤ M) (hYM : Y ≤ M)
    (hmnPos : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
      ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 0 < m * n)
    (q : ℕ) (χ : PrimitiveCharacter q) :
    ‖rectangularSharpHyperbolicCharacterSum a b Y Ma Mb Na Nb q χ‖ ≤
      ‖rectangularSmoothedKernelCharacterSum a b (1 / (M : ℝ) ^ 2)
        (BombieriVinogradov.perronHalfStep Y)
        Ma Mb Na Nb q χ‖ +
      (8 / (Real.pi * (M : ℝ))) * rectangularCoefficientL1 a b Ma Mb Na Nb := by
  let ε : ℝ := 1 / (M : ℝ) ^ 2
  let E : ℝ := 8 / (Real.pi * (M : ℝ))
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have herror : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
      ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
        |(if m * n ≤ (Y : ℤ) then 1 else 0 : ℝ) -
            dampedArctanPerronKernel ε
              (Real.log (BombieriVinogradov.perronHalfStep Y /
                ((m * n : ℤ) : ℝ)))| ≤ E := by
    intro m hm n hn
    have hp := hmnPos m hm n hn
    let k : ℕ := (m * n).toNat
    have hkZ : (k : ℤ) = m * n := by
      exact Int.toNat_of_nonneg (le_of_lt hp)
    have hk0 : k ≠ 0 := by
      intro hk
      have : (m * n : ℤ) = 0 := by simpa [hk] using hkZ.symm
      omega
    have hkcut : k ≤ Y ↔ m * n ≤ (Y : ℤ) := by
      constructor
      · intro h
        rw [← hkZ]
        exact_mod_cast h
      · intro h
        rw [← hkZ] at h
        exact_mod_cast h
    have hh := abs_halfStepIndicator_sub_dampedArctanPerronKernel_le
      (ε := ε) (n := k) (Y := Y) (M := M) hε hk0 hM hYM
    have hconst : 8 * ε * (M : ℝ) / Real.pi = E := by
      dsimp [ε, E]
      field_simp [Real.pi_ne_zero, hMr.ne']
    have hkR : (k : ℝ) = ((m * n : ℤ) : ℝ) := by exact_mod_cast hkZ
    calc
      |(if m * n ≤ (Y : ℤ) then 1 else 0 : ℝ) -
          dampedArctanPerronKernel ε
            (Real.log (BombieriVinogradov.perronHalfStep Y /
              ((m * n : ℤ) : ℝ)))| ≤ 8 * ε * (M : ℝ) / Real.pi := by
            rw [hkR] at hh
            simpa only [hkcut] using hh
      _ = E := hconst
  have hχ : ∀ q (χ : PrimitiveCharacter q) (z : ZMod q), ‖χ.1 z‖ ≤ 1 := by
    intro q χ z
    exact DirichletCharacter.norm_le_one χ.1 z
  have hpoint : ∀ q (χ : PrimitiveCharacter q)
      (m : ℤ) (_ : m ∈ Finset.Icc (Ma + 1) (Ma + Na))
      (n : ℤ) (_ : n ∈ Finset.Icc (Mb + 1) (Mb + Nb)),
      ‖a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
          (if m * n ≤ (Y : ℤ) then 1 else 0) -
        a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
          (dampedArctanPerronKernel ε
            (Real.log (BombieriVinogradov.perronHalfStep Y /
              ((m * n : ℤ) : ℝ))) : ℂ)‖ ≤
        E * ‖a m‖ * ‖b n‖ := by
    intro q χ m hm n hn
    rw [← mul_sub]
    simp only [norm_mul]
    have hc := hχ q χ ((m * n : ℤ) : ZMod q)
    have he := herror m hm n hn
    have hE : 0 ≤ E := by
      dsimp [E]
      positivity
    have hreal :
        ‖(if m * n ≤ (Y : ℤ) then 1 else 0 : ℂ) -
            (dampedArctanPerronKernel ε
              (Real.log (BombieriVinogradov.perronHalfStep Y /
                ((m * n : ℤ) : ℝ))) : ℂ)‖ =
          |(if m * n ≤ (Y : ℤ) then 1 else 0 : ℝ) -
            dampedArctanPerronKernel ε
              (Real.log (BombieriVinogradov.perronHalfStep Y /
                ((m * n : ℤ) : ℝ)))| := by
      by_cases hcut : m * n ≤ (Y : ℤ)
      · simp only [if_pos hcut, ← Complex.ofReal_one, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]
      · simp only [if_neg hcut, ← Complex.ofReal_zero, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]
    calc
      ‖a m‖ * ‖b n‖ * ‖χ.1 ((m * n : ℤ) : ZMod q)‖ *
          ‖(if m * n ≤ (Y : ℤ) then 1 else 0 : ℂ) -
            (dampedArctanPerronKernel ε
              (Real.log (BombieriVinogradov.perronHalfStep Y /
                ((m * n : ℤ) : ℝ))) : ℂ)‖ =
        ‖a m‖ * ‖b n‖ * ‖χ.1 ((m * n : ℤ) : ZMod q)‖ *
          |(if m * n ≤ (Y : ℤ) then 1 else 0 : ℝ) -
            dampedArctanPerronKernel ε
              (Real.log (BombieriVinogradov.perronHalfStep Y /
                ((m * n : ℤ) : ℝ)))| := by rw [hreal]
      _ ≤
          ‖a m‖ * ‖b n‖ * 1 * E := by
            gcongr
      _ = E * ‖a m‖ * ‖b n‖ := by ring
  let A := rectangularSharpHyperbolicCharacterSum a b Y Ma Mb Na Nb q χ
  let B := rectangularSmoothedKernelCharacterSum a b ε
    (BombieriVinogradov.perronHalfStep Y) Ma Mb Na Nb q χ
  change ‖A‖ ≤ ‖B‖ + E * rectangularCoefficientL1 a b Ma Mb Na Nb
  calc
    ‖A‖ = ‖B + (A - B)‖ := by congr 1; ring
    _ ≤ ‖B‖ + ‖A - B‖ := norm_add_le _ _
    _ ≤ ‖B‖ + E * rectangularCoefficientL1 a b Ma Mb Na Nb := by
      apply add_le_add le_rfl
      dsimp [A, B, rectangularSharpHyperbolicCharacterSum,
        rectangularSmoothedKernelCharacterSum]
      simp only [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
            ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), E * ‖a m‖ * ‖b n‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => hpoint q χ m hm n hn))
        _ = E * rectangularCoefficientL1 a b Ma Mb Na Nb := by
          simp only [rectangularCoefficientL1, Finset.mul_sum, Finset.sum_mul, mul_assoc]
          rw [Finset.sum_comm]

end

end BombieriVinogradov

/-!
## Separating the phase `y`

Expanding `sin(t log y - t log m - t log n)` writes the truncated Perron sum as
four rank-one products whose coefficients do not depend on `y`.  So `y` may be
chosen separately for each primitive character.
-/

namespace BombieriVinogradov

open Classical Finset
open scoped BigOperators
noncomputable section

/-- The twisted coefficient `a_m cos(t log m)`. -/
def phaseCosTwist (a : ℤ → ℂ) (t : ℝ) (m : ℤ) : ℂ :=
  a m * (Real.cos (t * Real.log (m : ℝ)) : ℂ)

/-- The twisted coefficient `a_m sin(t log m)`. -/
def phaseSinTwist (a : ℤ → ℂ) (t : ℝ) (m : ℤ) : ℂ :=
  a m * (Real.sin (t * Real.log (m : ℝ)) : ℂ)

/-- `(∑_m a_m χ(m)) (∑_n b_n χ(n))` over the rectangle. -/
def phaseRankOneCharacterProduct
    (a b : ℤ → ℂ) (Ma Mb : ℤ) (Na Nb q : ℕ)
    (χ : PrimitiveCharacter q) : ℂ :=
  (∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), a m * χ.1 (m : ZMod q)) *
    (∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), b n * χ.1 (n : ZMod q))

/-- `∑_{m, n} a_m b_n χ(m n) sin(t log(y / (m n))) / t` over the rectangle. -/
def dampedLogRectangularCharacterSum
    (a b : ℤ → ℂ) (y t : ℝ) (Ma Mb : ℤ) (Na Nb q : ℕ)
    (χ : PrimitiveCharacter q) : ℂ :=
  ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
    ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
      a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
        (Real.sin (t * Real.log (y / ((m * n : ℤ) : ℝ))) / t : ℂ)

/-- One term of `dampedLogRectangularCharacterSum`, expanded by the addition
formula for `sin(A - B - C)`. -/
theorem damped_log_term_eq_four_rankOne
    (a b : ℤ → ℂ) {y t : ℝ} {m n : ℤ} {q : ℕ}
    (χ : PrimitiveCharacter q) (hy : 0 < y) (hm : 0 < m) (hn : 0 < n)
    (_ht : 0 < t) :
    a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
        (Real.sin (t * Real.log (y / ((m * n : ℤ) : ℝ))) / t : ℂ) =
      (1 / (t : ℂ)) *
        (((Real.sin (t * Real.log y) : ℂ) *
              (phaseCosTwist a t m * χ.1 (m : ZMod q)) *
              (phaseCosTwist b t n * χ.1 (n : ZMod q))) -
          ((Real.cos (t * Real.log y) : ℂ) *
              (phaseSinTwist a t m * χ.1 (m : ZMod q)) *
              (phaseCosTwist b t n * χ.1 (n : ZMod q))) -
          ((Real.cos (t * Real.log y) : ℂ) *
              (phaseCosTwist a t m * χ.1 (m : ZMod q)) *
              (phaseSinTwist b t n * χ.1 (n : ZMod q))) -
          ((Real.sin (t * Real.log y) : ℂ) *
              (phaseSinTwist a t m * χ.1 (m : ZMod q)) *
              (phaseSinTwist b t n * χ.1 (n : ZMod q)))) := by
  rw [log_div_int_mul_eq_sub_log_sub_log hy hm hn]
  rw [show t * ((Real.log y - Real.log (m : ℝ)) - Real.log (n : ℝ)) =
      t * Real.log y - t * Real.log (m : ℝ) - t * Real.log (n : ℝ) by ring]
  rw [Real.sin_sub, Real.sin_sub, Real.cos_sub]
  simp only [phaseCosTwist, phaseSinTwist]
  rw [Int.cast_mul, map_mul]
  push_cast
  field_simp
  ring

/-- `dampedLogRectangularCharacterSum` as a combination of four rank-one products
with `y`-independent coefficients. -/
theorem dampedLogRectangularCharacterSum_eq_four_rankOne
    (a b : ℤ → ℂ) {y t : ℝ} (hy : 0 < y) (ht : 0 < t)
    (Ma Mb : ℤ) (Na Nb q : ℕ) (χ : PrimitiveCharacter q)
    (hm : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), 0 < m)
    (hn : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 0 < n) :
    dampedLogRectangularCharacterSum a b y t Ma Mb Na Nb q χ =
      (1 / (t : ℂ)) *
        (((Real.sin (t * Real.log y) : ℂ) *
            phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseCosTwist b t)
              Ma Mb Na Nb q χ) -
          ((Real.cos (t * Real.log y) : ℂ) *
            phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseCosTwist b t)
              Ma Mb Na Nb q χ) -
          ((Real.cos (t * Real.log y) : ℂ) *
            phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseSinTwist b t)
              Ma Mb Na Nb q χ) -
          ((Real.sin (t * Real.log y) : ℂ) *
            phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseSinTwist b t)
              Ma Mb Na Nb q χ)) := by
  have hprod (c d : ℤ → ℂ) :
      phaseRankOneCharacterProduct c d Ma Mb Na Nb q χ =
        ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
          ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
            (c m * χ.1 (m : ZMod q)) * (d n * χ.1 (n : ZMod q)) := by
    unfold phaseRankOneCharacterProduct
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hmm
    rw [Finset.mul_sum]
  unfold dampedLogRectangularCharacterSum
  calc
    (∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
        ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
          a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
            (Real.sin (t * Real.log (y / ((m * n : ℤ) : ℝ))) / t : ℂ)) =
      ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
        ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
          (1 / (t : ℂ)) *
            (((Real.sin (t * Real.log y) : ℂ) *
                (phaseCosTwist a t m * χ.1 (m : ZMod q)) *
                (phaseCosTwist b t n * χ.1 (n : ZMod q))) -
              ((Real.cos (t * Real.log y) : ℂ) *
                (phaseSinTwist a t m * χ.1 (m : ZMod q)) *
                (phaseCosTwist b t n * χ.1 (n : ZMod q))) -
              ((Real.cos (t * Real.log y) : ℂ) *
                (phaseCosTwist a t m * χ.1 (m : ZMod q)) *
                (phaseSinTwist b t n * χ.1 (n : ZMod q))) -
              ((Real.sin (t * Real.log y) : ℂ) *
                (phaseSinTwist a t m * χ.1 (m : ZMod q)) *
                (phaseSinTwist b t n * χ.1 (n : ZMod q)))) := by
        apply Finset.sum_congr rfl
        intro m hmm
        apply Finset.sum_congr rfl
        intro n hnn
        exact damped_log_term_eq_four_rankOne a b χ hy (hm m hmm) (hn n hnn) ht
    _ = _ := by
      rw [hprod, hprod, hprod, hprod]
      simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
      ring_nf

/-- Triangle inequality for the four-product expansion; `y` enters only through
`|sin(t log y)|` and `|cos(t log y)|`. -/
theorem norm_dampedLogRectangularCharacterSum_le_four_rankOne
    (a b : ℤ → ℂ) {y t : ℝ} (hy : 0 < y) (ht : 0 < t)
    (Ma Mb : ℤ) (Na Nb q : ℕ) (χ : PrimitiveCharacter q)
    (hm : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), 0 < m)
    (hn : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 0 < n) :
    ‖dampedLogRectangularCharacterSum a b y t Ma Mb Na Nb q χ‖ ≤
      (1 / t) *
        (|Real.sin (t * Real.log y)| *
            ‖phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseCosTwist b t)
              Ma Mb Na Nb q χ‖ +
          |Real.cos (t * Real.log y)| *
            ‖phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseCosTwist b t)
              Ma Mb Na Nb q χ‖ +
          |Real.cos (t * Real.log y)| *
            ‖phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseSinTwist b t)
              Ma Mb Na Nb q χ‖ +
          |Real.sin (t * Real.log y)| *
            ‖phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseSinTwist b t)
              Ma Mb Na Nb q χ‖) := by
  rw [dampedLogRectangularCharacterSum_eq_four_rankOne a b hy ht Ma Mb Na Nb q χ hm hn]
  rw [norm_mul]
  simp only [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have norm_four_sub_le (u v w z : ℂ) :
      ‖u - v - w - z‖ ≤ ‖u‖ + ‖v‖ + ‖w‖ + ‖z‖ := by
    calc
      ‖u - v - w - z‖ ≤ ‖u - v - w‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ (‖u - v‖ + ‖w‖) + ‖z‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ ‖u‖ + ‖v‖ + ‖w‖ + ‖z‖ :=
        add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
    norm_four_sub_le
      ((Real.sin (t * Real.log y) : ℂ) *
        phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseCosTwist b t)
          Ma Mb Na Nb q χ)
      ((Real.cos (t * Real.log y) : ℂ) *
        phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseCosTwist b t)
          Ma Mb Na Nb q χ)
      ((Real.cos (t * Real.log y) : ℂ) *
        phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseSinTwist b t)
          Ma Mb Na Nb q χ)
      ((Real.sin (t * Real.log y) : ℂ) *
        phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseSinTwist b t)
          Ma Mb Na Nb q χ)

theorem abs_sin_log_halfstep_le
    {M : ℕ} (hM : 3 ≤ M) {y t : ℝ}
    (hy0 : 1 / 2 ≤ y) (hyM : y ≤ (M : ℝ) + 1 / 2) (ht : 0 < t) :
    |Real.sin (t * Real.log y)| ≤ min 1 (2 * Real.log (M : ℝ) * t) := by
  have hlog : |Real.log y| ≤ 2 * Real.log (M : ℝ) := by
    have h := abs_log_div_int_le_two_log hM hy0 hyM (m := (1 : ℤ)) (by norm_num)
      (by exact_mod_cast (le_trans (by norm_num) hM))
    simpa using h
  apply le_min (Real.abs_sin_le_one _)
  calc
    |Real.sin (t * Real.log y)| ≤ |t * Real.log y| := Real.abs_sin_le_abs
    _ = t * |Real.log y| := by rw [abs_mul, abs_of_pos ht]
    _ ≤ t * (2 * Real.log (M : ℝ)) := mul_le_mul_of_nonneg_left hlog ht.le
    _ = 2 * Real.log (M : ℝ) * t := by ring

/-- The four-product bound with a phase `Y q χ ∈ [1/2, M + 1/2]` chosen for each
primitive character, using `|sin(t log y)| ≤ min(1, 2 t log M)` and `|cos| ≤ 1`. -/
theorem norm_dampedLogRectangularCharacterSum_le_of_selector
    (a b : ℤ → ℂ) {M : ℕ} (hM : 3 ≤ M)
    (Y : (q : ℕ) → PrimitiveCharacter q → ℝ) {t : ℝ} (ht : 0 < t)
    (Ma Mb : ℤ) (Na Nb q : ℕ) (χ : PrimitiveCharacter q)
    (hY0 : ∀ q χ, 1 / 2 ≤ Y q χ)
    (hYM : ∀ q χ, Y q χ ≤ (M : ℝ) + 1 / 2)
    (hm1 : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), 1 ≤ m)
    (_hmM : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), m ≤ (M : ℤ))
    (hn1 : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 1 ≤ n)
    (_hnM : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), n ≤ (M : ℤ)) :
    ‖dampedLogRectangularCharacterSum a b (Y q χ) t Ma Mb Na Nb q χ‖ ≤
      (1 / t) *
        (min 1 (2 * Real.log (M : ℝ) * t) *
            ‖phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseCosTwist b t)
              Ma Mb Na Nb q χ‖ +
          ‖phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseCosTwist b t)
              Ma Mb Na Nb q χ‖ +
          ‖phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseSinTwist b t)
              Ma Mb Na Nb q χ‖ +
          min 1 (2 * Real.log (M : ℝ) * t) *
            ‖phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseSinTwist b t)
              Ma Mb Na Nb q χ‖) := by
  have hbase := norm_dampedLogRectangularCharacterSum_le_four_rankOne
    a b (lt_of_lt_of_le (by norm_num) (hY0 q χ)) ht Ma Mb Na Nb q χ
    (fun m hm => lt_of_lt_of_le (by norm_num) (hm1 m hm))
    (fun n hn => lt_of_lt_of_le (by norm_num) (hn1 n hn))
  refine hbase.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hs := abs_sin_log_halfstep_le hM (hY0 q χ) (hYM q χ) ht
  have hc := Real.abs_cos_le_one (t * Real.log (Y q χ))
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · exact mul_le_mul_of_nonneg_right hs (norm_nonneg
          (phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseCosTwist b t)
            Ma Mb Na Nb q χ))
      · simpa using mul_le_mul_of_nonneg_right hc (norm_nonneg
          (phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseCosTwist b t)
            Ma Mb Na Nb q χ))
    · simpa using mul_le_mul_of_nonneg_right hc (norm_nonneg
        (phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseSinTwist b t)
          Ma Mb Na Nb q χ))
  · exact mul_le_mul_of_nonneg_right hs (norm_nonneg
      (phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseSinTwist b t)
        Ma Mb Na Nb q χ))

theorem sum_norm_sq_phaseSinTwist_Icc_le
    (a : ℤ → ℂ) (t : ℝ) (Ma : ℤ) (Na M : ℕ)
    (hM : 1 ≤ M)
    (hm1 : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), 1 ≤ m)
    (hmM : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), m ≤ (M : ℤ)) :
    ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖phaseSinTwist a t m‖ ^ 2 ≤
      (min 1 (Real.log (M : ℝ) * |t|)) ^ 2 *
        ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖a m‖ ^ 2 := by
  simpa only [phaseSinTwist, rightSinTwist] using
    sum_norm_sq_rightSinTwist_Icc_le a t Ma Na M hM hm1 hmM

theorem sum_norm_sq_phaseCosTwist_le
    (a : ℤ → ℂ) (t : ℝ) (s : Finset ℤ) :
    ∑ m ∈ s, ‖phaseCosTwist a t m‖ ^ 2 ≤ ∑ m ∈ s, ‖a m‖ ^ 2 := by
  simpa only [phaseCosTwist, rightCosTwist] using sum_norm_sq_rightCosTwist_le a t s

/-- `∑_{q ∈ S} (q / φ(q)) ∑_χ |∑_{m, n} a_m b_n χ(m n) sin(t log(Y_χ / (m n))) / t|`,
with a phase `Y_χ = Y q χ` for each primitive character. -/
def selectorDampedLogRectangularWeightedMean
    (a b : ℤ → ℂ) (Y : (q : ℕ) → PrimitiveCharacter q → ℝ) (t : ℝ)
    (Ma Mb : ℤ) (Na Nb : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
    ∑ χ : PrimitiveCharacter q,
      ‖dampedLogRectangularCharacterSum a b (Y q χ) t Ma Mb Na Nb q χ‖

/-- With a phase chosen for each character, the weighted mean is bounded by the
four rank-one means of the `y`-independent twisted coefficients. -/
theorem selectorDampedLogRectangularWeightedMean_le_four_rankOne
    (a b : ℤ → ℂ) {M : ℕ} (hM : 3 ≤ M)
    (Y : (q : ℕ) → PrimitiveCharacter q → ℝ) {t : ℝ} (ht : 0 < t)
    (Ma Mb : ℤ) (Na Nb : ℕ) (S : Finset ℕ)
    (hY0 : ∀ q χ, 1 / 2 ≤ Y q χ)
    (hYM : ∀ q χ, Y q χ ≤ (M : ℝ) + 1 / 2)
    (hm1 : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), 1 ≤ m)
    (hmM : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), m ≤ (M : ℤ))
    (hn1 : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 1 ≤ n)
    (hnM : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), n ≤ (M : ℤ)) :
    selectorDampedLogRectangularWeightedMean a b Y t Ma Mb Na Nb S ≤
      (1 / t) *
        (min 1 (2 * Real.log (M : ℝ) * t) *
            rankOneRectangularWeightedPrimitiveMean
              (phaseCosTwist a t) (phaseCosTwist b t) Ma Mb Na Nb S +
          rankOneRectangularWeightedPrimitiveMean
              (phaseSinTwist a t) (phaseCosTwist b t) Ma Mb Na Nb S +
          rankOneRectangularWeightedPrimitiveMean
              (phaseCosTwist a t) (phaseSinTwist b t) Ma Mb Na Nb S +
          min 1 (2 * Real.log (M : ℝ) * t) *
            rankOneRectangularWeightedPrimitiveMean
              (phaseSinTwist a t) (phaseSinTwist b t) Ma Mb Na Nb S) := by
  let d : ℝ := min 1 (2 * Real.log (M : ℝ) * t)
  have hmean (c e : ℤ → ℂ) :
      (∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖phaseRankOneCharacterProduct c e Ma Mb Na Nb q χ‖) =
        rankOneRectangularWeightedPrimitiveMean c e Ma Mb Na Nb S := by
    unfold phaseRankOneCharacterProduct rankOneRectangularWeightedPrimitiveMean
    simp only [norm_mul]
  unfold selectorDampedLogRectangularWeightedMean
  calc
    (∑ q ∈ S, (q : ℝ) / (q.totient : ℝ) *
        ∑ χ : PrimitiveCharacter q,
          ‖dampedLogRectangularCharacterSum a b (Y q χ) t Ma Mb Na Nb q χ‖) ≤
      ∑ q ∈ S, (q : ℝ) / (q.totient : ℝ) *
        ∑ χ : PrimitiveCharacter q, (1 / t) *
          (d * ‖phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseCosTwist b t)
                Ma Mb Na Nb q χ‖ +
            ‖phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseCosTwist b t)
                Ma Mb Na Nb q χ‖ +
            ‖phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseSinTwist b t)
                Ma Mb Na Nb q χ‖ +
            d * ‖phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseSinTwist b t)
                Ma Mb Na Nb q χ‖) := by
        apply Finset.sum_le_sum
        intro q hq
        apply mul_le_mul_of_nonneg_left
        · apply Finset.sum_le_sum
          intro χ hχ
          simpa only [d] using
            norm_dampedLogRectangularCharacterSum_le_of_selector
              a b hM Y ht Ma Mb Na Nb q χ hY0 hYM hm1 hmM hn1 hnM
        · positivity
    _ = _ := by
      rw [← hmean (phaseCosTwist a t) (phaseCosTwist b t),
        ← hmean (phaseSinTwist a t) (phaseCosTwist b t),
        ← hmean (phaseCosTwist a t) (phaseSinTwist b t),
        ← hmean (phaseSinTwist a t) (phaseSinTwist b t)]
      simp only [Finset.mul_sum]
      dsimp only [d]
      ring_nf
      simp_rw [Finset.sum_add_distrib]
      simp_rw [Finset.mul_sum]
      ring_nf

end

end BombieriVinogradov

/-! ## Weighted means with a cutoff for each character -/

namespace BombieriVinogradov

open Classical Finset MeasureTheory Set
open scoped BigOperators
noncomputable section

/-- Weighted mean of the damped kernel sums at the half-steps `Y q χ + 1/2`, with
`ε = M⁻²`.  In the Perron integral the four rank-one products lose the factors
`min(1, 2t log M)`, `min(1, t log M)`, `min(1, t log M)`, `min(1, 2t log M)`, and
integrating gives `14 log M + 4`. -/
theorem selectorRectangularSmoothedKernelWeightedPrimitiveMean_le
    (a b : ℤ → ℂ) (Y : (q : ℕ) → PrimitiveCharacter q → ℕ)
    (Ma Mb : ℤ) (Na Nb Q M : ℕ)
    (hQ : 0 < Q) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hM : 3 ≤ M)
    (hYM : ∀ q χ, Y q χ ≤ M)
    (hm1 : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), 1 ≤ m)
    (hmM : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), m ≤ (M : ℤ))
    (hn1 : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 1 ≤ n)
    (hnM : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), n ≤ (M : ℤ)) :
    (∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        ‖rectangularSmoothedKernelCharacterSum a b (1 / (M : ℝ) ^ 2)
          (BombieriVinogradov.perronHalfStep (Y q χ))
          Ma Mb Na Nb q χ‖) ≤
      (1 / 2 + (14 * Real.log (M : ℝ) + 4) / Real.pi) *
        rankOneRectangularLSRHS a b Ma Mb Na Nb Q := by
  classical
  let ε : ℝ := 1 / (M : ℝ) ^ 2
  let L := Real.log (M : ℝ)
  let R := rankOneRectangularLSRHS a b Ma Mb Na Nb Q
  let y := fun q χ => BombieriVinogradov.perronHalfStep (Y q χ)
  let w := fun q : ℕ => (q : ℝ) / (q.totient : ℝ)
  let F := fun q χ t => (Real.exp (-ε * t) : ℂ) *
    rectangularKernelCharacterSum a b (y q χ) t Ma Mb Na Nb q χ
  have hM1 : 1 ≤ M := by omega
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]; exact (div_le_one (by positivity)).2 (one_le_pow₀ hMr)
  have hL : 0 ≤ L := Real.log_nonneg hMr
  have hR : 0 ≤ R := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hw : ∀ q ∈ S, 0 ≤ w q := by intros; dsimp [w]; positivity
  have hy0 : ∀ q χ, 1 / 2 ≤ y q χ := by
    intro q χ
    dsimp [y, BombieriVinogradov.perronHalfStep]
    linarith [Nat.cast_nonneg (α := ℝ) (Y q χ)]
  have hyM : ∀ q χ, y q χ ≤ (M : ℝ) + 1 / 2 := by
    intro q χ
    dsimp [y, BombieriVinogradov.perronHalfStep]
    have hy : (Y q χ : ℝ) ≤ M := by exact_mod_cast hYM q χ
    linarith
  have hF : ∀ q χ, IntegrableOn (F q χ) (Ioi 0) := fun q χ =>
    (rectangularDampedPerron_integrable_formula a b ε (y q χ) hε Ma Mb Na Nb q χ).1
  let G := fun t => ∑ q ∈ S, w q * ∑ χ, ‖F q χ t‖
  have hG := dampedPerron_weighted_norm_integrable S w F (volume.restrict (Ioi 0)) hF
  -- Bound the four rank-one means of the `y`-independent twists by the large sieve.
  have hmajor : ∀ t ∈ Ioi (0 : ℝ), G t ≤
      (dampedPerronMajorantIntegrand ε (2 * L) t +
        dampedPerronMajorantIntegrand ε L t) * (2 * R) := by
    intro t ht
    change 0 < t at ht
    let s := min 1 (L * t)
    let d := min 1 (2 * L * t)
    have hs : 0 ≤ s := le_min (by norm_num) (mul_nonneg hL ht.le)
    have hd : 0 ≤ d := le_min (by norm_num) (by positivity)
    have hs1 : s ≤ 1 := min_le_left _ _
    have hsa := sum_norm_sq_phaseSinTwist_Icc_le a t Ma Na M hM1 hm1 hmM
    have hsb := sum_norm_sq_phaseSinTwist_Icc_le b t Mb Nb M hM1 hn1 hnM
    rw [abs_of_pos ht] at hsa hsb
    have hca := sum_norm_sq_phaseCosTwist_le a t (Finset.Icc (Ma + 1) (Ma + Na))
    have hcb := sum_norm_sq_phaseCosTwist_le b t (Finset.Icc (Mb + 1) (Mb + Nb))
    have ls := fun c d => rankOneRectangularWeightedPrimitiveMean_le_scaled_energy
      a b c d Ma Mb Na Nb Q hQ S hS
    have hcc : rankOneRectangularWeightedPrimitiveMean
        (phaseCosTwist a t) (phaseCosTwist b t) Ma Mb Na Nb S ≤ R := by
      simpa using ls (phaseCosTwist a t) (phaseCosTwist b t) 1 1
        (by norm_num) (by norm_num) (by simpa using hca) (by simpa using hcb)
    have hsc : rankOneRectangularWeightedPrimitiveMean
        (phaseSinTwist a t) (phaseCosTwist b t) Ma Mb Na Nb S ≤ s * R := by
      simpa using ls (phaseSinTwist a t) (phaseCosTwist b t) s 1 hs
        (by norm_num) hsa (by simpa using hcb)
    have hcs : rankOneRectangularWeightedPrimitiveMean
        (phaseCosTwist a t) (phaseSinTwist b t) Ma Mb Na Nb S ≤ s * R := by
      simpa using ls (phaseCosTwist a t) (phaseSinTwist b t) 1 s
        (by norm_num) hs (by simpa using hca) hsb
    have hss : rankOneRectangularWeightedPrimitiveMean
        (phaseSinTwist a t) (phaseSinTwist b t) Ma Mb Na Nb S ≤ R := by
      refine (ls (phaseSinTwist a t) (phaseSinTwist b t) s s hs hs hsa hsb).trans ?_
      exact mul_le_of_le_one_left hR (by nlinarith)
    have hb := selectorDampedLogRectangularWeightedMean_le_four_rankOne
      a b hM y ht Ma Mb Na Nb S hy0 hyM hm1 hmM hn1 hnM
    have hbound : selectorDampedLogRectangularWeightedMean a b y t Ma Mb Na Nb S ≤
        (1 / t) * ((d + s) * (2 * R)) := by
      refine hb.trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ ≤ d * R + s * R + s * R + d * R :=
          add_le_add (add_le_add (add_le_add
            (mul_le_mul_of_nonneg_left hcc hd) hsc) hcs)
            (mul_le_mul_of_nonneg_left hss hd)
        _ = _ := by ring
    have hident : G t = Real.exp (-ε * t) *
        selectorDampedLogRectangularWeightedMean a b y t Ma Mb Na Nb S := by
      dsimp only [G, F, selectorDampedLogRectangularWeightedMean]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      simp only [rectangularKernelCharacterSum, dampedLogRectangularCharacterSum,
        truncatedPerronIntegrand, if_neg (ne_of_gt ht), Complex.ofReal_div]
      dsimp only [w]
      simp only [Finset.mul_sum, mul_left_comm]
    rw [hident]
    refine (mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le).trans_eq ?_
    simp only [dampedPerronMajorantIntegrand, if_neg (ne_of_gt ht)]
    dsimp [d, s]
    ring
  have hint := dampedPerron_integral_le_two_majorants hε hε1
    (by positivity : 0 ≤ 2 * L) hL (by positivity : 0 ≤ 2 * R) hG hmajor
  have hlog : Real.log (1 / ε) = 2 * L := by
    simp [ε, L, Real.log_pow]
  rw [hlog] at hint
  have hint' : (∑ q ∈ S, w q * ∑ χ, ‖∫ t in Ioi (0 : ℝ), F q χ t‖) ≤
      (14 * L + 4) * R := by
    refine (dampedPerron_weighted_norm_integral_le S w hw F
      (volume.restrict (Ioi 0)) hF).trans (hint.trans_eq ?_)
    ring
  -- Apply the Perron identity before taking norms.
  have hadd := dampedPerron_weighted_norm_add_le S w hw
    (fun q χ => (∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), a m * χ.1 (m : ZMod q)) *
      (∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), b n * χ.1 (n : ZMod q)))
    (fun q χ => ∫ t in Ioi (0 : ℝ), F q χ t) (1 / 2) (1 / Real.pi)
    (by positivity) (by positivity)
  have hbase := rankOneRectangularWeightedPrimitiveMean_le a b Ma Mb Na Nb Q hQ S hS
  simp only [norm_mul] at hadd
  change _ ≤ (1 / 2) * rankOneRectangularWeightedPrimitiveMean a b Ma Mb Na Nb S +
    (1 / Real.pi) * (∑ q ∈ S, w q * ∑ χ, ‖∫ t in Ioi (0 : ℝ), F q χ t‖) at hadd
  calc
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      congr 1
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [(rectangularDampedPerron_integrable_formula a b ε (y q χ) hε
        Ma Mb Na Nb q χ).2]
      simp only [F, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    _ ≤ _ := hadd
    _ ≤ (1 / 2) * R + (1 / Real.pi) * ((14 * L + 4) * R) :=
      add_le_add (mul_le_mul_of_nonneg_left hbase (by positivity))
        (mul_le_mul_of_nonneg_left hint' (by positivity))
    _ = (1 / 2 + (14 * L + 4) / Real.pi) * R := by ring

private theorem selectorRectangularSharpHyperbolicWeightedPrimitiveMean_le_smoothed
    (a b : ℤ → ℂ) (Y : (q : ℕ) → PrimitiveCharacter q → ℕ)
    (M : ℕ) (Ma Mb : ℤ) (Na Nb : ℕ) (S : Finset ℕ)
    (hM : 1 ≤ M)
    (hYM : ∀ q χ, Y q χ ≤ M)
    (hmnPos : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
      ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 0 < m * n)
    (_hmnM : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
      ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), m * n ≤ (M : ℤ)) :
    (∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        ‖rectangularSharpHyperbolicCharacterSum a b (Y q χ) Ma Mb Na Nb q χ‖) ≤
      (∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖rectangularSmoothedKernelCharacterSum a b (1 / (M : ℝ) ^ 2)
            (BombieriVinogradov.perronHalfStep (Y q χ))
            Ma Mb Na Nb q χ‖) +
      (8 / (Real.pi * (M : ℝ))) *
        rectangularCoefficientL1 a b Ma Mb Na Nb * weightedPrimitiveFamilyMass S := by
  let ε : ℝ := 1 / (M : ℝ) ^ 2
  let E : ℝ := 8 / (Real.pi * (M : ℝ))
  have hsingle := fun q χ => rectangularSharpHyperbolicCharacterSum_norm_le_smoothed
    a b (Y q χ) M Ma Mb Na Nb hM (hYM q χ) hmnPos q χ
  unfold weightedPrimitiveFamilyMass
  change _ ≤ _ + E * rectangularCoefficientL1 a b Ma Mb Na Nb * _
  calc
    ∑ q ∈ S, (q : ℝ) / (q.totient : ℝ) *
        ∑ χ : PrimitiveCharacter q,
          ‖rectangularSharpHyperbolicCharacterSum a b (Y q χ) Ma Mb Na Nb q χ‖ ≤
      ∑ q ∈ S, (q : ℝ) / (q.totient : ℝ) *
        ∑ χ : PrimitiveCharacter q,
          (‖rectangularSmoothedKernelCharacterSum a b ε
              (BombieriVinogradov.perronHalfStep (Y q χ))
              Ma Mb Na Nb q χ‖ + E * rectangularCoefficientL1 a b Ma Mb Na Nb) := by
        apply Finset.sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun χ _ => hsingle q χ) (by positivity)
    _ = ∑ q ∈ S, (q : ℝ) / (q.totient : ℝ) *
          ∑ χ : PrimitiveCharacter q,
            ‖rectangularSmoothedKernelCharacterSum a b ε
              (BombieriVinogradov.perronHalfStep (Y q χ))
              Ma Mb Na Nb q χ‖ +
        E * rectangularCoefficientL1 a b Ma Mb Na Nb *
          ∑ q ∈ S, (q : ℝ) / (q.totient : ℝ) * Fintype.card (PrimitiveCharacter q) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ, mul_add]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

/-- Weighted primitive mean of the sharp hyperbolic sums with a cutoff `Y q χ ≤ M`
for each character.  Smoothing at `Y + 1/2` costs `8 / (π M)` times the `ℓ¹` mass
of the coefficients. -/
theorem selectorRectangularSharpHyperbolicWeightedPrimitiveMean_le
    (a b : ℤ → ℂ) (Y : (q : ℕ) → PrimitiveCharacter q → ℕ)
    (Ma Mb : ℤ) (Na Nb Q M : ℕ)
    (hQ : 0 < Q) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hM : 3 ≤ M)
    (hYM : ∀ q χ, Y q χ ≤ M)
    (hm1 : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), 1 ≤ m)
    (hmM : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), m ≤ (M : ℤ))
    (hn1 : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 1 ≤ n)
    (hnM : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), n ≤ (M : ℤ))
    (hmnPos : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
      ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 0 < m * n)
    (hmnM : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
      ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), m * n ≤ (M : ℤ)) :
    (∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        ‖rectangularSharpHyperbolicCharacterSum a b (Y q χ) Ma Mb Na Nb q χ‖) ≤
      (1 / 2 + (14 * Real.log (M : ℝ) + 4) / Real.pi) *
          rankOneRectangularLSRHS a b Ma Mb Na Nb Q +
        (8 / (Real.pi * (M : ℝ))) *
          rectangularCoefficientL1 a b Ma Mb Na Nb * weightedPrimitiveFamilyMass S := by
  have hsharp := selectorRectangularSharpHyperbolicWeightedPrimitiveMean_le_smoothed
    a b Y M Ma Mb Na Nb S (by omega) hYM hmnPos hmnM
  have hsmoothed := selectorRectangularSmoothedKernelWeightedPrimitiveMean_le
    a b Y Ma Mb Na Nb Q M hQ S hS hM hYM hm1 hmM hn1 hnM
  calc
    (∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        ‖rectangularSharpHyperbolicCharacterSum a b (Y q χ) Ma Mb Na Nb q χ‖) ≤
      (∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖rectangularSmoothedKernelCharacterSum a b (1 / (M : ℝ) ^ 2)
            (BombieriVinogradov.perronHalfStep (Y q χ))
            Ma Mb Na Nb q χ‖) +
      (8 / (Real.pi * (M : ℝ))) *
        rectangularCoefficientL1 a b Ma Mb Na Nb * weightedPrimitiveFamilyMass S := hsharp
    _ ≤ (1 / 2 + (14 * Real.log (M : ℝ) + 4) / Real.pi) *
          rankOneRectangularLSRHS a b Ma Mb Na Nb Q +
        (8 / (Real.pi * (M : ℝ))) *
          rectangularCoefficientL1 a b Ma Mb Na Nb * weightedPrimitiveFamilyMass S := by
      gcongr

end

end BombieriVinogradov

/-!
## Maximal prefixes on a rectangle

The maximum is over cutoffs `Y ≤ H`, while the support and the damping are
measured at a scale `M ≥ H`.
-/

namespace BombieriVinogradov

open Classical Finset
open scoped BigOperators
noncomputable section

/-- `max_{Y ≤ H} |∑_{m n ≤ Y} a_m b_n χ(m n)|²` over the rectangle. -/
def rectangularSharpHyperbolicPrefixMaxSquareUpTo
    (a b : ℤ → ℂ) (H : ℕ) (Ma Mb : ℤ) (Na Nb q : ℕ)
    (χ : PrimitiveCharacter q) : ℝ :=
  ((Finset.range (H + 1)).image fun Y =>
      ‖rectangularSharpHyperbolicCharacterSum a b Y Ma Mb Na Nb q χ‖ ^ 2).max'
    (by simp)

/-- `max_{Y ≤ H} |∑_{m n ≤ Y} a_m b_n χ(m n)|` over the rectangle. -/
def rectangularSharpHyperbolicPrefixMaxAmplitudeUpTo
    (a b : ℤ → ℂ) (H : ℕ) (Ma Mb : ℤ) (Na Nb q : ℕ)
    (χ : PrimitiveCharacter q) : ℝ :=
  Real.sqrt (rectangularSharpHyperbolicPrefixMaxSquareUpTo a b H Ma Mb Na Nb q χ)

/-- `∑_{q ∈ S} (q / φ(q)) ∑_χ max_{Y ≤ H} |∑_{m n ≤ Y} a_m b_n χ(m n)|`, over
primitive `χ` mod `q`. -/
def rectangularSharpHyperbolicPrefixMaxWeightedPrimitiveMeanUpTo
    (a b : ℤ → ℂ) (H : ℕ) (Ma Mb : ℤ) (Na Nb : ℕ)
    (S : Finset ℕ) : ℝ :=
  ∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
    ∑ χ : PrimitiveCharacter q,
      rectangularSharpHyperbolicPrefixMaxAmplitudeUpTo a b H Ma Mb Na Nb q χ

theorem exists_rectangularSharpHyperbolicPrefixMaxAmplitudeUpTo_eq
    (a b : ℤ → ℂ) (H : ℕ) (Ma Mb : ℤ) (Na Nb q : ℕ)
    (χ : PrimitiveCharacter q) :
    ∃ Y ≤ H,
      rectangularSharpHyperbolicPrefixMaxAmplitudeUpTo a b H Ma Mb Na Nb q χ =
        ‖rectangularSharpHyperbolicCharacterSum a b Y Ma Mb Na Nb q χ‖ := by
  let values : Finset ℝ :=
    (Finset.range (H + 1)).image fun Y =>
      ‖rectangularSharpHyperbolicCharacterSum a b Y Ma Mb Na Nb q χ‖ ^ 2
  have hvalues : values.Nonempty := by
    dsimp [values]
    simp
  have hmax := Finset.max'_mem values hvalues
  rw [Finset.mem_image] at hmax
  obtain ⟨Y, hYrange, hYmax⟩ := hmax
  refine ⟨Y, ?_, ?_⟩
  · simpa [Finset.mem_range] using hYrange
  · unfold rectangularSharpHyperbolicPrefixMaxAmplitudeUpTo
    unfold rectangularSharpHyperbolicPrefixMaxSquareUpTo
    change Real.sqrt (values.max' hvalues) = _
    rw [← hYmax]
    exact Real.sqrt_sq (norm_nonneg _)

/-- The weighted primitive mean of maximal sharp hyperbolic prefixes on a
rectangle, for `H ≤ M`.  Choosing a maximizing `Y ≤ H` for each character
reduces it to `selectorRectangularSharpHyperbolicWeightedPrimitiveMean_le`. -/
theorem rectangularSharpPrefixMaxMean_le
    (a b : ℤ → ℂ) (Ma Mb : ℤ) (Na Nb Q H M : ℕ)
    (hQ : 0 < Q) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hM : 3 ≤ M) (hHM : H ≤ M)
    (hm1 : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), 1 ≤ m)
    (hmM : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), m ≤ (M : ℤ))
    (hn1 : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 1 ≤ n)
    (hnM : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), n ≤ (M : ℤ))
    (hmnPos : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
      ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 0 < m * n)
    (hmnM : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
      ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), m * n ≤ (M : ℤ)) :
    rectangularSharpHyperbolicPrefixMaxWeightedPrimitiveMeanUpTo
        a b H Ma Mb Na Nb S ≤
      (1 / 2 + (14 * Real.log (M : ℝ) + 4) / Real.pi) *
          rankOneRectangularLSRHS a b Ma Mb Na Nb Q +
        (8 / (Real.pi * (M : ℝ))) *
          rectangularCoefficientL1 a b Ma Mb Na Nb * weightedPrimitiveFamilyMass S := by
  choose Y hYH hYattain using fun q χ =>
    exists_rectangularSharpHyperbolicPrefixMaxAmplitudeUpTo_eq
      a b H Ma Mb Na Nb q χ
  have hYM : ∀ q χ, Y q χ ≤ M := fun q χ => (hYH q χ).trans hHM
  unfold rectangularSharpHyperbolicPrefixMaxWeightedPrimitiveMeanUpTo
  simp_rw [hYattain]
  exact selectorRectangularSharpHyperbolicWeightedPrimitiveMean_le
    a b Y Ma Mb Na Nb Q M hQ S hS hM hYM hm1 hmM hn1 hnM hmnPos hmnM

end

end BombieriVinogradov

/-! ## The weighted mass of the primitive family -/

namespace BombieriVinogradov

open Finset

private theorem primitiveCharacter_card_le_totient_mass (q : ℕ) (hq : 0 < q) :
    Fintype.card (PrimitiveCharacter q) ≤ q.totient := by
  exact primitiveCharacter_card_le_totient_basic q hq

private theorem sum_Icc_one_cast (Q : ℕ) :
    (∑ q ∈ Icc 1 Q, (q : ℝ)) = (Q : ℝ) * ((Q : ℝ) + 1) / 2 := by
  induction Q with
  | zero => simp
  | succ Q ih =>
      rw [sum_Icc_succ_top (by omega : 1 ≤ Q + 1), ih]
      push_cast
      ring

/-- There are at most `φ(q)` primitive characters mod `q`, so the weighted mass of
`S ⊆ [1, Q]` is at most `∑_{q ≤ Q} q = Q (Q + 1) / 2`. -/
theorem weightedPrimitiveFamilyMass_le_triangular
    (Q : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 Q) :
    weightedPrimitiveFamilyMass S ≤ (Q : ℝ) * ((Q : ℝ) + 1) / 2 := by
  have hterm : ∀ q ∈ S,
      ((q : ℝ) / (q.totient : ℝ)) * Fintype.card (PrimitiveCharacter q) ≤ (q : ℝ) := by
    intro q hq
    have hq1 : 1 ≤ q := (mem_Icc.mp (hS hq)).1
    have hq0 : 0 < q := by omega
    have htot : 0 < (q.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hq0
    have hcard : (Fintype.card (PrimitiveCharacter q) : ℝ) ≤ (q.totient : ℝ) := by
      exact_mod_cast primitiveCharacter_card_le_totient_mass q hq0
    calc
      _ ≤ ((q : ℝ) / (q.totient : ℝ)) * (q.totient : ℝ) :=
        mul_le_mul_of_nonneg_left hcard (by positivity)
      _ = (q : ℝ) := div_mul_cancel₀ _ htot.ne'
  unfold weightedPrimitiveFamilyMass
  calc
    (∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) * Fintype.card (PrimitiveCharacter q)) ≤
        ∑ q ∈ S, (q : ℝ) := by
          exact sum_le_sum fun q hq => hterm q hq
    _ ≤ ∑ q ∈ Icc 1 Q, (q : ℝ) := by
      exact sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => Nat.cast_nonneg _)
    _ = (Q : ℝ) * ((Q : ℝ) + 1) / 2 := sum_Icc_one_cast Q

end BombieriVinogradov
