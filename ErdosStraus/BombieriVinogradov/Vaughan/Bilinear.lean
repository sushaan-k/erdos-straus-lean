import ErdosStraus.BombieriVinogradov.Reduction.Primitive
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import ErdosStraus.BombieriVinogradov.Statement

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

/-! # Bilinear form of Vaughan's Type II sum

For `y ≤ N` the twisted Type II sum
`∑_{1 ≤ n ≤ y} b(n) χ(n) ∑_{d ∣ n, d > u} ∑_{e ∣ n/d, e > v} μ(d) Λ(e)`
splits into at most `(log₂ N + 1)²` dyadic rectangles in `(d, e)`. On each rectangle the
substitution `n = d e m` and grouping by `t = e m` give a bilinear form in `d` and `t` whose
coefficients do not depend on `χ`. The file also proves `∑_{t ≤ X} τ(t)² ≤ 27 X log³(X + 1)`,
which controls the size of these coefficients.
-/

/-! ## Dyadic decomposition -/

namespace BombieriVinogradov

open Classical Finset
open scoped BigOperators ArithmeticFunction
noncomputable section

/-- The integers `d` with `1 ≤ d ≤ N` and `u < d`. -/
def vaughanTypeIIRange (N u : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun d => u < d)

@[simp] theorem mem_vaughanTypeIIRange {N u d : ℕ} :
    d ∈ vaughanTypeIIRange N u ↔ 0 < d ∧ d ≤ N ∧ u < d := by
  simp [vaughanTypeIIRange, Nat.succ_le_iff, and_assoc]

/-- The dyadic levels `⌊log₂ d⌋` of the `d` with `u < d ≤ N`. -/
def vaughanCanonicalDyadicBases (N u : ℕ) : Finset ℕ :=
  (vaughanTypeIIRange N u).image (Nat.log 2)

/-- The dyadic block of the `d` with `u < d ≤ N` and `2^k ≤ d < 2^(k+1)`. -/
def vaughanCanonicalDyadicBlock (N u k : ℕ) : Finset ℕ :=
  (vaughanTypeIIRange N u).filter (fun d => Nat.log 2 d = k)

@[simp] theorem mem_vaughanCanonicalDyadicBlock {N u k d : ℕ} :
    d ∈ vaughanCanonicalDyadicBlock N u k ↔
      0 < d ∧ d ≤ N ∧ u < d ∧ Nat.log 2 d = k := by
  simp [vaughanCanonicalDyadicBlock, and_assoc]

theorem mem_vaughanCanonicalDyadicBases_iff {N u k : ℕ} :
    k ∈ vaughanCanonicalDyadicBases N u ↔
      ∃ d ∈ vaughanCanonicalDyadicBlock N u k, True := by
  simp [vaughanCanonicalDyadicBases, vaughanCanonicalDyadicBlock]

theorem vaughanCanonicalDyadicBlock_pow_bounds {N u k d : ℕ}
    (hd : d ∈ vaughanCanonicalDyadicBlock N u k) :
    2 ^ k ≤ d ∧ d < 2 ^ (k + 1) := by
  have hpos : 0 < d := (mem_vaughanCanonicalDyadicBlock.mp hd).1
  have hlog : Nat.log 2 d = k :=
    (mem_vaughanCanonicalDyadicBlock.mp hd).2.2.2
  exact (Nat.log_eq_iff (Or.inr ⟨by omega, hpos.ne'⟩)).mp hlog

/-- The dyadic blocks partition `u < d ≤ N`. -/
theorem sum_vaughanCanonicalDyadicBlock {M : Type*} [AddCommMonoid M]
    (N u : ℕ) (f : ℕ → M) :
    (∑ k ∈ vaughanCanonicalDyadicBases N u,
      ∑ d ∈ vaughanCanonicalDyadicBlock N u k, f d) =
        ∑ d ∈ vaughanTypeIIRange N u, f d := by
  exact Finset.sum_fiberwise_of_maps_to
    (fun d hd => Finset.mem_image.mpr ⟨d, hd, rfl⟩) f

/-- At most `log₂ N + 1` dyadic blocks are nonempty, uniformly in `u`. -/
theorem card_vaughanCanonicalDyadicBases_le (N u : ℕ) :
    (vaughanCanonicalDyadicBases N u).card ≤ Nat.log 2 N + 1 := by
  calc
    (vaughanCanonicalDyadicBases N u).card ≤
        (Finset.range (Nat.log 2 N + 1)).card := by
      apply Finset.card_le_card
      intro k hk
      rw [Finset.mem_range]
      rw [vaughanCanonicalDyadicBases, Finset.mem_image] at hk
      obtain ⟨d, hd, rfl⟩ := hk
      have hdN : d ≤ N := (mem_vaughanTypeIIRange.mp hd).2.1
      exact Nat.lt_succ_of_le (Nat.log_monotone hdN)
    _ = Nat.log 2 N + 1 := Finset.card_range _

/-- The pairs `(k, l)` of dyadic levels for `d` and `e`. -/
def vaughanCanonicalDyadicRectangles (N u v : ℕ) : Finset (ℕ × ℕ) :=
  vaughanCanonicalDyadicBases N u ×ˢ vaughanCanonicalDyadicBases N v

theorem card_vaughanCanonicalDyadicRectangles_le (N u v : ℕ) :
    (vaughanCanonicalDyadicRectangles N u v).card ≤ (Nat.log 2 N + 1) ^ 2 := by
  rw [vaughanCanonicalDyadicRectangles, Finset.card_product, pow_two]
  exact Nat.mul_le_mul (card_vaughanCanonicalDyadicBases_le N u)
    (card_vaughanCanonicalDyadicBases_le N v)

/-- The Type II factor `∑_{d ∣ n, d > u} ∑_{e ∣ n/d, e > v} μ(d) Λ(e)`, as a complex number. -/
def vaughanTypeIIFullAt (n u v : ℕ) : ℂ :=
  ∑ d ∈ n.divisors.filter (fun d => u < d),
    ∑ e ∈ (n / d).divisors.filter (fun e => v < e),
      vaughanMoebiusCoeff d * vaughanMangoldtCoeff e

theorem vaughanTypeIIFullAt_eq_vaughanThird (n u v : ℕ) :
    vaughanTypeIIFullAt n u v = (vaughanThird n u v : ℂ) := by
  unfold vaughanTypeIIFullAt vaughanThird
    vaughanMoebiusCoeff vaughanMangoldtCoeff
  push_cast
  rfl

/-- For `1 ≤ n ≤ N` the nested divisor sum is a sum over the rectangle
`u < d ≤ N`, `v < e ≤ N` restricted to `d e ∣ n`. -/
theorem vaughanTypeIIFullAt_eq_bounded_rectangular {n N u v : ℕ}
    (hn : 0 < n) (hnN : n ≤ N) :
    vaughanTypeIIFullAt n u v =
      ∑ d ∈ vaughanTypeIIRange N u,
        ∑ e ∈ vaughanTypeIIRange N v,
          if d * e ∣ n then
            vaughanMoebiusCoeff d * vaughanMangoldtCoeff e else 0 := by
  unfold vaughanTypeIIFullAt
  have hdset : n.divisors.filter (fun d => u < d) =
      (vaughanTypeIIRange N u).filter (fun d => d ∣ n) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdn, _⟩, hud⟩
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
      exact ⟨mem_vaughanTypeIIRange.mpr
        ⟨hdpos, (Nat.le_of_dvd hn hdn).trans hnN, hud⟩, hdn⟩
    · rintro ⟨hd, hdn⟩
      exact ⟨⟨hdn, hn.ne'⟩,
        (mem_vaughanTypeIIRange.mp hd).2.2⟩
  rw [hdset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdn : d ∣ n
  · simp only [if_pos hdn]
    have hdpos : 0 < d := (mem_vaughanTypeIIRange.mp hd).1
    have hndpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hdpos
    have heset : (n / d).divisors.filter (fun e => v < e) =
        (vaughanTypeIIRange N v).filter (fun e => d * e ∣ n) := by
      ext e
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hed, _⟩, hve⟩
        have hmul : d * e ∣ n := (Nat.dvd_div_iff_mul_dvd hdn).mp hed
        have hepos : 0 < e := Nat.pos_of_dvd_of_pos hed hndpos
        have hen : e ≤ n := Nat.le_of_dvd hn ((dvd_mul_left e d).trans hmul)
        exact ⟨mem_vaughanTypeIIRange.mpr ⟨hepos, hen.trans hnN, hve⟩, hmul⟩
      · rintro ⟨he, hmul⟩
        have hed : e ∣ n / d := (Nat.dvd_div_iff_mul_dvd hdn).mpr hmul
        exact ⟨⟨hed, hndpos.ne'⟩,
          (mem_vaughanTypeIIRange.mp he).2.2⟩
    rw [heset, Finset.sum_filter]
  · have hde : ∀ e : ℕ, ¬ d * e ∣ n := by
      intro e h
      exact hdn ((dvd_mul_right d e).trans h)
    simp [hdn, hde]

/-- For `1 ≤ n ≤ N` the Type II factor splits over the dyadic rectangles in `(d, e)`. -/
theorem vaughanTypeIIFullAt_eq_sum_canonical_blocks {n N u v : ℕ}
    (hn : 0 < n) (hnN : n ≤ N) :
    vaughanTypeIIFullAt n u v =
      ∑ k ∈ vaughanCanonicalDyadicBases N u,
        ∑ l ∈ vaughanCanonicalDyadicBases N v,
          ∑ d ∈ vaughanCanonicalDyadicBlock N u k,
            ∑ e ∈ vaughanCanonicalDyadicBlock N v l,
              if d * e ∣ n then
                vaughanMoebiusCoeff d * vaughanMangoldtCoeff e else 0 := by
  rw [vaughanTypeIIFullAt_eq_bounded_rectangular hn hnN]
  rw [← sum_vaughanCanonicalDyadicBlock N u (fun d =>
    ∑ e ∈ vaughanTypeIIRange N v,
      if d * e ∣ n then
        vaughanMoebiusCoeff d * vaughanMangoldtCoeff e else 0)]
  apply Finset.sum_congr rfl
  intro k hk
  -- Split the `e`-sum into dyadic blocks, then swap the `d` and `e` sums back.
  rw [Finset.sum_comm, ← sum_vaughanCanonicalDyadicBlock N v]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_comm

/-- The part of `∑_{1 ≤ n ≤ y} b(n) χ(n) ∑_{d e ∣ n} μ(d) Λ(e)` with `d` in the dyadic block
`k` and `e` in the dyadic block `l`. -/
def vaughanTypeIICanonicalBlockPrefix
    (b : ℕ → ℂ) (y N u v k l q : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y,
    b n * χ.1 (n : ZMod q) *
      ∑ d ∈ vaughanCanonicalDyadicBlock N u k,
        ∑ e ∈ vaughanCanonicalDyadicBlock N v l,
          if d * e ∣ n then
            vaughanMoebiusCoeff d * vaughanMangoldtCoeff e else 0

/-- The bilinear form
`∑_d μ(d) χ(d) ∑_e Λ(e) χ(e) ∑_{1 ≤ m ≤ y/(d e)} b(d e m) χ(m)` over one dyadic rectangle. -/
def vaughanTypeIICanonicalBilinearBlock
    (b : ℕ → ℂ) (y N u v k l q : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  ∑ d ∈ vaughanCanonicalDyadicBlock N u k,
    (vaughanMoebiusCoeff d * χ.1 (d : ZMod q)) *
      ∑ e ∈ vaughanCanonicalDyadicBlock N v l,
        (vaughanMangoldtCoeff e * χ.1 (e : ZMod q)) *
          ∑ m ∈ Finset.Icc 1 (y / (d * e)),
            b (d * e * m) * χ.1 (m : ZMod q)

/-- On each dyadic rectangle, the substitution `n = d e m` and `χ(d e m) = χ(d) χ(e) χ(m)`
turn the twisted sum into the bilinear form. -/
theorem vaughanTypeIICanonicalBlockPrefix_eq_bilinear
    (b : ℕ → ℂ) (y N u v k l q : ℕ) (χ : PrimitiveCharacter q) :
    vaughanTypeIICanonicalBlockPrefix b y N u v k l q χ =
      vaughanTypeIICanonicalBilinearBlock b y N u v k l q χ := by
  unfold vaughanTypeIICanonicalBlockPrefix vaughanTypeIICanonicalBilinearBlock
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  have hdpos : 0 < d := (mem_vaughanCanonicalDyadicBlock.mp hd).1
  have hepos : 0 < e := (mem_vaughanCanonicalDyadicBlock.mp he).1
  have hkpos : 0 < d * e := Nat.mul_pos hdpos hepos
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  rw [sum_multiples_Icc_reindex
    (fun n => b n * χ.1 (n : ZMod q) *
      (vaughanMoebiusCoeff d * vaughanMangoldtCoeff e)) hkpos]
  apply Finset.sum_congr rfl
  intro m hm
  have hcast : ((d * e * m : ℕ) : ZMod q) =
      (d : ZMod q) * (e : ZMod q) * (m : ZMod q) := by
    simp only [Nat.cast_mul]
  rw [hcast, map_mul, map_mul]
  ring

/-- The twisted Type II sum
`∑_{1 ≤ n ≤ y} b(n) χ(n) ∑_{d ∣ n, d > u} ∑_{e ∣ n/d, e > v} μ(d) Λ(e)`. -/
def vaughanTypeIIFullPrefix
    (b : ℕ → ℂ) (y u v q : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y,
    b n * χ.1 (n : ZMod q) * vaughanTypeIIFullAt n u v

/-- For `y ≤ N` the twisted Type II sum is the sum, over the dyadic rectangles `(k, l)`, of
the bilinear forms `vaughanTypeIICanonicalBilinearBlock`. The hypothesis `y ≤ N` ensures
`d, e ≤ N` for every divisor of `n ≤ y`. -/
theorem vaughanTypeIIFullPrefix_eq_sum_canonical_bilinear
    (b : ℕ → ℂ) (y N u v q : ℕ) (χ : PrimitiveCharacter q) (hyN : y ≤ N) :
    vaughanTypeIIFullPrefix b y u v q χ =
      ∑ k ∈ vaughanCanonicalDyadicBases N u,
        ∑ l ∈ vaughanCanonicalDyadicBases N v,
          vaughanTypeIICanonicalBilinearBlock b y N u v k l q χ := by
  calc
    vaughanTypeIIFullPrefix b y u v q χ =
        ∑ n ∈ Finset.Icc 1 y,
          b n * χ.1 (n : ZMod q) *
            (∑ k ∈ vaughanCanonicalDyadicBases N u,
              ∑ l ∈ vaughanCanonicalDyadicBases N v,
                ∑ d ∈ vaughanCanonicalDyadicBlock N u k,
                  ∑ e ∈ vaughanCanonicalDyadicBlock N v l,
                    if d * e ∣ n then
                      vaughanMoebiusCoeff d * vaughanMangoldtCoeff e else 0) := by
      unfold vaughanTypeIIFullPrefix
      apply Finset.sum_congr rfl
      intro n hn
      rw [vaughanTypeIIFullAt_eq_sum_canonical_blocks
        (Finset.mem_Icc.mp hn).1 ((Finset.mem_Icc.mp hn).2.trans hyN)]
    _ = ∑ k ∈ vaughanCanonicalDyadicBases N u,
          ∑ l ∈ vaughanCanonicalDyadicBases N v,
            vaughanTypeIICanonicalBlockPrefix b y N u v k l q χ := by
      unfold vaughanTypeIICanonicalBlockPrefix
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
    _ = ∑ k ∈ vaughanCanonicalDyadicBases N u,
          ∑ l ∈ vaughanCanonicalDyadicBases N v,
            vaughanTypeIICanonicalBilinearBlock b y N u v k l q χ := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      exact vaughanTypeIICanonicalBlockPrefix_eq_bilinear b y N u v k l q χ

end

end BombieriVinogradov

/-! ## Grouping the inner sum by `t = e m` -/

namespace BombieriVinogradov

open Classical Finset
open scoped BigOperators
noncomputable section

/-- The coefficient of `χ(t)` after grouping by `t = e m`: the sum of `β(e) c(d t)` over the
pairs `(e, m)` with `e ∈ ES`, `1 ≤ m ≤ y/(d e)` and `e m = t`. -/
def vaughanBilinearTensorCoeff
    (β : ℕ → ℂ) (c : ℕ → ℂ) (y d : ℕ) (ES : Finset ℕ) (t : ℤ) : ℂ :=
  ∑ e ∈ ES, ∑ m ∈ Finset.Icc 1 (y / (d * e)),
    if ((e * m : ℕ) : ℤ) = t then β e * c (d * t.toNat) else 0

/-- The bilinear form
`∑_{d ∈ DS} α(d) χ(d) ∑_{e ∈ ES} β(e) χ(e) ∑_{1 ≤ m ≤ y/(d e)} c(d e m) χ(m)`. -/
def vaughanBilinearBlockOn
    (α β : ℕ → ℂ) (c : ℕ → ℂ) (y : ℕ) (DS ES : Finset ℕ)
    (q : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  ∑ d ∈ DS, (α d * χ.1 (d : ZMod q)) *
    ∑ e ∈ ES, (β e * χ.1 (e : ZMod q)) *
      ∑ m ∈ Finset.Icc 1 (y / (d * e)),
        c (d * e * m) * χ.1 (m : ZMod q)

/-- For fixed `d`, the inner sum over `e` and `m` is `∑_{1 ≤ t ≤ y} a_d(t) χ(t)`, where the
coefficients `a_d(t)` do not depend on `χ`. -/
theorem vaughanBilinearInner_eq_tensor
    (β : ℕ → ℂ) (c : ℕ → ℂ) (y d : ℕ) (ES : Finset ℕ)
    (q : ℕ) (χ : PrimitiveCharacter q) (hd : 0 < d)
    (hES : ∀ e ∈ ES, 0 < e) :
    (∑ e ∈ ES, (β e * χ.1 (e : ZMod q)) *
        ∑ m ∈ Finset.Icc 1 (y / (d * e)),
          c (d * e * m) * χ.1 (m : ZMod q)) =
      ∑ t ∈ Finset.Icc (1 : ℤ) y,
        vaughanBilinearTensorCoeff β c y d ES t * χ.1 (t : ZMod q) := by
  unfold vaughanBilinearTensorCoeff
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  have hepos : 0 < e := hES e he
  have hde : 0 < d * e := Nat.mul_pos hd hepos
  have hmI := Finset.mem_Icc.mp hm
  have hem_le : e * m ≤ y := by
    have hdem : d * e * m ≤ y := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        (Nat.le_div_iff_mul_le hde).mp hmI.2
    exact (Nat.le_mul_of_pos_left (e * m) hd).trans
      (by simpa [mul_assoc] using hdem)
  have hem_pos : 0 < e * m := Nat.mul_pos hepos hmI.1
  have hsingle :
      (∑ t ∈ Finset.Icc (1 : ℤ) y,
        (if ((e * m : ℕ) : ℤ) = t then β e * c (d * t.toNat) else 0) *
          χ.1 (t : ZMod q)) =
        (β e * c (d * (e * m))) * χ.1 ((e * m : ℕ) : ZMod q) := by
    have hem_mem : ((e * m : ℕ) : ℤ) ∈ Finset.Icc (1 : ℤ) y :=
      Finset.mem_Icc.mpr
        ⟨by exact_mod_cast hem_pos, by exact_mod_cast hem_le⟩
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq, if_pos hem_mem]
    simp only [Int.toNat_natCast, Int.cast_natCast]
  rw [hsingle]
  rw [show ((e * m : ℕ) : ZMod q) =
    (e : ZMod q) * (m : ZMod q) by simp only [Nat.cast_mul], map_mul]
  ring_nf

theorem vaughanBilinearBlockOn_eq_tensor
    (α β : ℕ → ℂ) (c : ℕ → ℂ) (y : ℕ) (DS ES : Finset ℕ)
    (q : ℕ) (χ : PrimitiveCharacter q)
    (hDS : ∀ d ∈ DS, 0 < d) (hES : ∀ e ∈ ES, 0 < e) :
    vaughanBilinearBlockOn α β c y DS ES q χ =
      ∑ d ∈ DS, (α d * χ.1 (d : ZMod q)) *
        ∑ t ∈ Finset.Icc (1 : ℤ) y,
          vaughanBilinearTensorCoeff β c y d ES t * χ.1 (t : ZMod q) := by
  unfold vaughanBilinearBlockOn
  apply Finset.sum_congr rfl
  intro d hd
  rw [vaughanBilinearInner_eq_tensor β c y d ES q χ (hDS d hd) hES]

/-- The large sieve constant for sequences of length `y` and moduli up to `Q`, namely
`largeSieveBound` at spacing `δ = 1/Q²`. -/
def vaughanBilinearLargeSieveConstant (y Q : ℕ) : ℝ :=
  largeSieveBound y (1 / (Q : ℝ) ^ 2)

theorem vaughanBilinearLargeSieveConstant_eq_explicit
    (y Q : ℕ) (hQ : 0 < Q) :
    vaughanBilinearLargeSieveConstant y Q =
      (y : ℝ) +
        (2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
          (Q : ℝ) ^ 2 := by
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hOneDiv : 1 / (1 / (Q : ℝ) ^ 2) = (Q : ℝ) ^ 2 := by
    field_simp [hQr]
  have hDivide (x : ℝ) : x / (1 / (Q : ℝ) ^ 2) = x * (Q : ℝ) ^ 2 := by
    field_simp [hQr]
  unfold vaughanBilinearLargeSieveConstant largeSieveBound
  rw [hOneDiv, hDivide]

end

end BombieriVinogradov

namespace BombieriVinogradov

open Classical Finset
open scoped BigOperators ArithmeticFunction
noncomputable section

/-- The `e ∈ ES` with `e m = t` for some `1 ≤ m ≤ y/(d e)`. -/
def vaughanTensorFiber (y d : ℕ) (ES : Finset ℕ) (t : ℤ) : Finset ℕ :=
  ES.filter fun e => ∃ m ∈ Finset.Icc 1 (y / (d * e)), ((e * m : ℕ) : ℤ) = t

private theorem tensor_inner_sum_eq_indicator
    (z : ℂ) (y d e : ℕ) (t : ℤ) (he : 0 < e) :
    (∑ m ∈ Finset.Icc 1 (y / (d * e)),
      if ((e * m : ℕ) : ℤ) = t then z else 0) =
      if ∃ m ∈ Finset.Icc 1 (y / (d * e)), ((e * m : ℕ) : ℤ) = t then z else 0 := by
  by_cases h : ∃ m ∈ Finset.Icc 1 (y / (d * e)), ((e * m : ℕ) : ℤ) = t
  · obtain ⟨m, hm, hmt⟩ := h
    rw [if_pos ⟨m, hm, hmt⟩]
    rw [Finset.sum_eq_single m]
    · simp [hmt]
    · intro m' hm' hne
      rw [if_neg]
      intro hm't
      apply hne
      apply Nat.eq_of_mul_eq_mul_left he
      exact_mod_cast hm't.trans hmt.symm
    · intro hmnot
      exact False.elim (hmnot hm)
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro m hm
    rw [if_neg]
    exact fun hmt => h ⟨m, hm, hmt⟩

/-- Since `m = t/e` is determined by `e`, the coefficient at `t` with `β = Λ` is a sum of
`Λ(e) b(d t)` over the fibre of `t`. -/
theorem vaughanBilinearTensorCoeff_eq_fiber
    (b : ℕ → ℂ) (y d : ℕ) (ES : Finset ℕ) (t : ℤ)
    (hES : ∀ e ∈ ES, 0 < e) :
    vaughanBilinearTensorCoeff vaughanMangoldtCoeff b y d ES t =
      ∑ e ∈ vaughanTensorFiber y d ES t,
        vaughanMangoldtCoeff e * b (d * t.toNat) := by
  unfold vaughanBilinearTensorCoeff vaughanTensorFiber
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  rw [tensor_inner_sum_eq_indicator
    (vaughanMangoldtCoeff e * b (d * t.toNat)) y d e t (hES e he)]

end

end BombieriVinogradov

/-! ## The second moment of the divisor function

The map `(a, b) ↦ (gcd(a, b), a/gcd(a, b), b/gcd(a, b))` sends pairs of divisors of `t`
injectively to triples `(g, u, v)` with `g u v ∣ t`. Hence
`∑_{t ≤ X} τ(t)² ≤ X (∑_{m ≤ X} 1/m)³ ≤ 27 X log³(X + 1)`.
-/

namespace BombieriVinogradov

open Finset
open scoped BigOperators ArithmeticFunction

/-- `∑_{1 ≤ t ≤ X} τ(t)²`, indexed by integers `t`. -/
noncomputable def divisorSquarePrefix (X : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc (1 : ℤ) X, ((t.toNat.divisors.card : ℝ) ^ 2)

/-- The bound `∑_{t ≤ X} τ(t)² ≤ C X log³(X + 1)` for every `X`. -/
def DivisorSquareMomentBound (C : ℝ) : Prop :=
  ∀ X : ℕ, divisorSquarePrefix X ≤
    C * (X : ℝ) * Real.log (X + 1 : ℕ) ^ 3

end BombieriVinogradov

section

open Finset

namespace BombieriVinogradov

noncomputable section

/-- The harmonic number `∑_{1 ≤ m ≤ x} 1/m`. -/
noncomputable def harmonicReal (x : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 x, (m : ℝ)⁻¹

@[simp]
theorem harmonicReal_zero : harmonicReal 0 = 0 := by
  simp [harmonicReal]

theorem harmonicReal_eq_harmonic (m : ℕ) :
    harmonicReal m = (harmonic m : ℝ) := by
  rw [harmonicReal, harmonic_eq_sum_Icc, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Rat.cast_inv, Rat.cast_natCast]

theorem harmonicReal_le_one_add_log (m : ℕ) :
    harmonicReal m ≤ 1 + Real.log m := by
  rw [harmonicReal_eq_harmonic]
  exact harmonic_le_one_add_log m

end

end BombieriVinogradov

end

namespace BombieriVinogradov

open Finset
open scoped BigOperators
open BombieriVinogradov
noncomputable section

private def divisorTripleSupport (X t : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 X).product ((Finset.Icc 1 X).product (Finset.Icc 1 X))).filter
    fun guv => guv.1 * guv.2.1 * guv.2.2 ∣ t

private def divisorPairToTriple (ab : ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let g := Nat.gcd ab.1 ab.2
  (g, ab.1 / g, ab.2 / g)

private lemma divisorPairToTriple_injective :
    Function.Injective divisorPairToTriple := by
  intro ab₁ ab₂ h
  rcases ab₁ with ⟨a₁, b₁⟩
  rcases ab₂ with ⟨a₂, b₂⟩
  dsimp [divisorPairToTriple] at h ⊢
  have hg : Nat.gcd a₁ b₁ = Nat.gcd a₂ b₂ := by
    simpa using congrArg Prod.fst h
  have hu : a₁ / Nat.gcd a₁ b₁ = a₂ / Nat.gcd a₂ b₂ := by
    simpa [hg] using congrArg (fun x => x.2.1) h
  have hv : b₁ / Nat.gcd a₁ b₁ = b₂ / Nat.gcd a₂ b₂ := by
    simpa [hg] using congrArg (fun x => x.2.2) h
  have ha : a₁ = a₂ := by
    have hmul :
        Nat.gcd a₁ b₁ * (a₁ / Nat.gcd a₁ b₁) =
          Nat.gcd a₂ b₂ * (a₂ / Nat.gcd a₂ b₂) := by
      simpa [hg] using congrArg (fun n => Nat.gcd a₁ b₁ * n) hu
    calc
      a₁ = Nat.gcd a₁ b₁ * (a₁ / Nat.gcd a₁ b₁) := by
        symm
        exact Nat.mul_div_cancel' (Nat.gcd_dvd_left a₁ b₁)
      _ = Nat.gcd a₂ b₂ * (a₂ / Nat.gcd a₂ b₂) := hmul
      _ = a₂ := by
        exact Nat.mul_div_cancel' (Nat.gcd_dvd_left a₂ b₂)
  have hb : b₁ = b₂ := by
    have hmul :
        Nat.gcd a₁ b₁ * (b₁ / Nat.gcd a₁ b₁) =
          Nat.gcd a₂ b₂ * (b₂ / Nat.gcd a₂ b₂) := by
      simpa [hg] using congrArg (fun n => Nat.gcd a₁ b₁ * n) hv
    calc
      b₁ = Nat.gcd a₁ b₁ * (b₁ / Nat.gcd a₁ b₁) := by
        symm
        exact Nat.mul_div_cancel' (Nat.gcd_dvd_right a₁ b₁)
      _ = Nat.gcd a₂ b₂ * (b₂ / Nat.gcd a₂ b₂) := hmul
      _ = b₂ := by
        exact Nat.mul_div_cancel' (Nat.gcd_dvd_right a₂ b₂)
  simp [ha, hb]

private lemma divisorPairToTriple_mem
    {X t a b : ℕ} (ht : 0 < t) (htX : t ≤ X)
    (ha : a ∈ t.divisors) (hb : b ∈ t.divisors) :
    divisorPairToTriple (a, b) ∈ divisorTripleSupport X t := by
  have hadvd : a ∣ t := (Nat.mem_divisors.mp ha).1
  have hbdvd : b ∣ t := (Nat.mem_divisors.mp hb).1
  have hapos : 0 < a := Nat.pos_of_dvd_of_pos hadvd ht
  have hbpos : 0 < b := Nat.pos_of_dvd_of_pos hbdvd ht
  let g := Nat.gcd a b
  let u := a / g
  let v := b / g
  have hgpos : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_left b hapos
  have hugt : 0 < u := by
    dsimp [u]
    exact Nat.div_pos (Nat.gcd_le_left b hapos) hgpos
  have hvgt : 0 < v := by
    dsimp [v]
    exact Nat.div_pos (Nat.gcd_le_right a hbpos) hgpos
  have hgle : g ≤ t := Nat.le_of_dvd ht (Nat.dvd_trans (Nat.gcd_dvd_left a b) hadvd)
  have hule : u ≤ t := by
    dsimp [u]
    exact (Nat.div_le_self a g).trans (Nat.le_of_dvd ht hadvd)
  have hvle : v ≤ t := by
    dsimp [v]
    exact (Nat.div_le_self b g).trans (Nat.le_of_dvd ht hbdvd)
  have hlcm : Nat.lcm a b = g * u * v := by
    have hmul : g * Nat.lcm a b = g * (g * u * v) := by
      calc
        g * Nat.lcm a b = a * b := by
          dsimp [g]
          exact Nat.gcd_mul_lcm a b
        _ = (g * u) * (g * v) := by
          dsimp [g, u, v]
          rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left a b),
            Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)]
        _ = g * (g * u * v) := by ring
    exact Nat.eq_of_mul_eq_mul_left hgpos hmul
  change (g, u, v) ∈ divisorTripleSupport X t
  refine Finset.mem_filter.mpr ?_
  constructor
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hgpos, hgle.trans htX⟩,
        Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨hugt, hule.trans htX⟩,
            Finset.mem_Icc.mpr ⟨hvgt, hvle.trans htX⟩⟩⟩
  · change g * u * v ∣ t
    rw [← hlcm]
    exact Nat.lcm_dvd hadvd hbdvd

private lemma divisorSquarePrefix_term_le_tripleCount
    {X t : ℕ} (ht : 0 < t) (htX : t ≤ X) :
    ((t.divisors.card : ℝ) ^ 2) ≤
      ∑ g ∈ Finset.Icc 1 X, ∑ u ∈ Finset.Icc 1 X, ∑ v ∈ Finset.Icc 1 X,
        if g * u * v ∣ t then (1 : ℝ) else 0 := by
  let S : Finset (ℕ × ℕ) := t.divisors.product t.divisors
  let T : Finset (ℕ × ℕ × ℕ) := divisorTripleSupport X t
  have himage : S.image divisorPairToTriple ⊆ T := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨ab, hab, rfl⟩
    rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
    exact divisorPairToTriple_mem ht htX ha hb
  have hcard : S.card ≤ T.card := by
    calc
      S.card = (S.image divisorPairToTriple).card := by
        symm
        exact Finset.card_image_of_injective S divisorPairToTriple_injective
      _ ≤ T.card := Finset.card_le_card himage
  have hsum :
      ((T.card : ℕ) : ℝ) =
        ∑ g ∈ Finset.Icc 1 X, ∑ u ∈ Finset.Icc 1 X, ∑ v ∈ Finset.Icc 1 X,
          if g * u * v ∣ t then (1 : ℝ) else 0 := by
    dsimp [T, divisorTripleSupport]
    simp only [Finset.card_filter, Finset.sum_product, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
  calc
    ((t.divisors.card : ℝ) ^ 2) = (S.card : ℝ) := by
      simp [S, Finset.card_product, pow_two]
    _ ≤ (T.card : ℝ) := by exact_mod_cast hcard
    _ = ∑ g ∈ Finset.Icc 1 X, ∑ u ∈ Finset.Icc 1 X, ∑ v ∈ Finset.Icc 1 X,
          if g * u * v ∣ t then (1 : ℝ) else 0 := hsum

theorem harmonicReal_le_three_log_add_one (X : ℕ) :
    harmonicReal X ≤ 3 * Real.log (X + 1 : ℕ) := by
  cases X with
  | zero => simp [harmonicReal_zero]
  | succ n =>
      have h1 : harmonicReal (n + 1) ≤ 1 + Real.log (n + 1 : ℕ) :=
        harmonicReal_le_one_add_log (n + 1)
      have hlog : Real.log (n + 1 : ℕ) ≤ Real.log (n + 2 : ℕ) := by
        apply Real.log_le_log
        · positivity
        · exact_mod_cast Nat.succ_le_succ (Nat.le_succ n)
      have htwoThird : (2 / 3 : ℝ) ≤ Real.log (n + 2 : ℕ) := by
        have hbase : (2 / 3 : ℝ) ≤ Real.log (2 : ℝ) := by
          have : (2 * (1 : ℝ) / (1 + 2)) ≤ Real.log (1 + (1 : ℝ)) :=
            Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)
          norm_num at this
          simpa using this
        have hmono : Real.log (2 : ℝ) ≤ Real.log (n + 2 : ℕ) := by
          apply Real.log_le_log
          · norm_num
          · exact_mod_cast (show (2 : ℕ) ≤ n + 2 by omega)
        exact hbase.trans hmono
      have hone : (1 : ℝ) ≤ (3 / 2 : ℝ) * Real.log (n + 2 : ℕ) := by
        nlinarith
      have hmain : 1 + Real.log (n + 1 : ℕ) ≤ 3 * Real.log (n + 2 : ℕ) := by
        have : 1 + Real.log (n + 1 : ℕ) ≤
            (3 / 2 : ℝ) * Real.log (n + 2 : ℕ) + Real.log (n + 2 : ℕ) := by
          linarith
        linarith
      exact h1.trans hmain

private theorem sum_dvd_indicator_Icc'
    (R e : ℕ) (he : 0 < e) :
    (∑ r ∈ Finset.Icc 1 R, if e ∣ r then (1 : ℝ) else 0) = (R / e : ℕ) := by
  exact BombieriVinogradov.sum_dvd_indicator_Icc R e he

theorem sum_Icc_int_toNat_eq_sum_Icc
    {F : ℕ → ℝ} (X : ℕ) :
    (∑ t ∈ Finset.Icc (1 : ℤ) X, F t.toNat) =
      ∑ n ∈ Finset.Icc 1 X, F n := by
  refine Finset.sum_bij (fun t _ => t.toNat) ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_Icc]
    constructor
    · have htpos : 0 < t := lt_of_lt_of_le Int.zero_lt_one (Finset.mem_Icc.mp ht).1
      have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg htpos.le
      have : (1 : ℤ) ≤ (t.toNat : ℤ) := by
        simpa [htcast] using (Finset.mem_Icc.mp ht).1
      exact_mod_cast this
    · have htpos : 0 < t := lt_of_lt_of_le Int.zero_lt_one (Finset.mem_Icc.mp ht).1
      have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg htpos.le
      exact_mod_cast htcast.trans_le (Finset.mem_Icc.mp ht).2
  · intro t₁ ht₁ t₂ ht₂ h
    have ht₁pos : 0 < t₁ := lt_of_lt_of_le Int.zero_lt_one (Finset.mem_Icc.mp ht₁).1
    have ht₂pos : 0 < t₂ := lt_of_lt_of_le Int.zero_lt_one (Finset.mem_Icc.mp ht₂).1
    exact Int.toNat_of_nonneg ht₁pos.le ▸ Int.toNat_of_nonneg ht₂pos.le ▸ by
      exact_mod_cast h
  · intro n hn
    refine ⟨(n : ℤ), ?_, by simp⟩
    simpa [Finset.mem_Icc] using hn
  · intro t ht
    simp

private theorem divisorSquarePrefix_eq_nat (X : ℕ) :
    divisorSquarePrefix X =
      ∑ t ∈ Finset.Icc 1 X, ((t.divisors.card : ℝ) ^ 2) := by
  unfold divisorSquarePrefix
  simpa using sum_Icc_int_toNat_eq_sum_Icc
    (F := fun t => ((t.divisors.card : ℝ) ^ 2)) X

private theorem divisorSquarePrefix_le_cube_harmonic (X : ℕ) :
    divisorSquarePrefix X ≤ (X : ℝ) * harmonicReal X ^ 3 := by
  rw [divisorSquarePrefix_eq_nat]
  calc
    (∑ t ∈ Finset.Icc 1 X, ((t.divisors.card : ℝ) ^ 2)) ≤
        ∑ t ∈ Finset.Icc 1 X,
          ∑ g ∈ Finset.Icc 1 X, ∑ u ∈ Finset.Icc 1 X, ∑ v ∈ Finset.Icc 1 X,
            if g * u * v ∣ t then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro t ht
      exact divisorSquarePrefix_term_le_tripleCount
        (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2
    _ = ∑ g ∈ Finset.Icc 1 X, ∑ u ∈ Finset.Icc 1 X, ∑ v ∈ Finset.Icc 1 X,
          ∑ t ∈ Finset.Icc 1 X, if g * u * v ∣ t then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g hg
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_comm]
    _ = ∑ g ∈ Finset.Icc 1 X, ∑ u ∈ Finset.Icc 1 X, ∑ v ∈ Finset.Icc 1 X,
          ((X / (g * u * v) : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro g hg
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      have hgpos : 0 < g := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hg).1
      have hupos : 0 < u := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hu).1
      have hvpos : 0 < v := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hv).1
      exact sum_dvd_indicator_Icc' X (g * u * v)
        (Nat.mul_pos (Nat.mul_pos hgpos hupos) hvpos)
    _ ≤ ∑ g ∈ Finset.Icc 1 X, ∑ u ∈ Finset.Icc 1 X, ∑ v ∈ Finset.Icc 1 X,
          (X : ℝ) * (g : ℝ)⁻¹ * (u : ℝ)⁻¹ * (v : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro g hg
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      have hgR : (0 : ℝ) < g := by exact_mod_cast (Finset.mem_Icc.mp hg).1
      have huR : (0 : ℝ) < u := by exact_mod_cast (Finset.mem_Icc.mp hu).1
      have hvR : (0 : ℝ) < v := by exact_mod_cast (Finset.mem_Icc.mp hv).1
      have hdiv : ((X / (g * u * v) : ℕ) : ℝ) ≤ (X : ℝ) / (g * u * v) := by
        simpa [Nat.cast_mul, mul_assoc] using
          (Nat.cast_div_le (α := ℝ) (m := X) (n := g * u * v))
      have hfac :
          (X : ℝ) / (g * u * v) =
            (X : ℝ) * (g : ℝ)⁻¹ * (u : ℝ)⁻¹ * (v : ℝ)⁻¹ := by
        field_simp [hgR.ne', huR.ne', hvR.ne']
      calc
        ((X / (g * u * v) : ℕ) : ℝ) ≤ (X : ℝ) / (g * u * v) := hdiv
        _ = (X : ℝ) * (g : ℝ)⁻¹ * (u : ℝ)⁻¹ * (v : ℝ)⁻¹ := hfac
    _ = (X : ℝ) * harmonicReal X ^ 3 := by
      -- The triple sum factors as the cube of the harmonic number.
      simp only [← Finset.mul_sum, ← Finset.sum_mul, harmonicReal]
      ring

/-- `∑_{t ≤ X} τ(t)² ≤ 27 X log³(X + 1)`. -/
theorem divisorSquareMomentBound_27 :
    DivisorSquareMomentBound 27 := by
  intro X
  have hH : harmonicReal X ≤ 3 * Real.log (X + 1 : ℕ) :=
    harmonicReal_le_three_log_add_one X
  have hH0 : 0 ≤ harmonicReal X := by
    unfold harmonicReal
    positivity
  have hpow : harmonicReal X ^ 3 ≤ (3 * Real.log (X + 1 : ℕ)) ^ 3 :=
    pow_le_pow_left₀ hH0 hH 3
  have hX0 : 0 ≤ (X : ℝ) := by positivity
  calc
    divisorSquarePrefix X ≤ (X : ℝ) * harmonicReal X ^ 3 :=
      divisorSquarePrefix_le_cube_harmonic X
    _ ≤ (X : ℝ) * (3 * Real.log (X + 1 : ℕ)) ^ 3 :=
      mul_le_mul_of_nonneg_left hpow hX0
    _ = 27 * (X : ℝ) * Real.log (X + 1 : ℕ) ^ 3 := by ring

end

end BombieriVinogradov

namespace BombieriVinogradov

open Classical Finset
open scoped BigOperators ArithmeticFunction
noncomputable section

/-- The factor `c(Q) = 2⌈log₂ Q²⌉ + 12` in the large sieve constant `y + c(Q) Q²`. -/
def primitiveBilinearQFactor (Q : ℕ) : ℝ :=
  2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12

lemma one_le_primitiveBilinearQFactor (Q : ℕ) :
    1 ≤ primitiveBilinearQFactor Q := by
  unfold primitiveBilinearQFactor
  have h : 0 ≤ (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) := by
    positivity
  linarith

end

end BombieriVinogradov
