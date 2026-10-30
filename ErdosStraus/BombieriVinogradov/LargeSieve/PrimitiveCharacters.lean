import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.NumberTheory.SelbergSieve
import ErdosStraus.BombieriVinogradov.Vaughan.Identity
import ErdosStraus.BombieriVinogradov.LargeSieve.Multiplicative
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

/-!
# Primitive Dirichlet characters and Gauss sums

For a primitive Dirichlet character `χ` modulo `q` the Gauss sum satisfies `‖τ(χ)‖² = q`,
so the root number of `χ` has norm one. The file also proves Parseval's identity over the
characters modulo `q`, `∑_χ |∑_x conj(χ(x)) T(x)|² = φ(q) ∑_{(x,q)=1} |T(x)|²`, and
writes each character as the one induced by the primitive character modulo its conductor.
-/

namespace BombieriVinogradov

open Finset Real
open scoped Classical
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.omega

/-- The reduced residues `0 ≤ l < q` with `(l, q) = 1`.
For `q = 1` this is `{0}`, and for `q = 0` it is empty. -/
def unitResidues (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun l => l.Coprime q)

end BombieriVinogradov

namespace BombieriVinogradov

open Finset
open scoped BigOperators
open Classical
open BombieriVinogradov
noncomputable section

set_option maxHeartbeats 4000000

/-! ## Fourier analysis on `ZMod q` -/

/-- `e(m/q)` depends only on the residue of `m` modulo `q`. -/
lemma charReal_periodic_zmod {q : ℕ} (hq : 0 < q) {m n : ℤ}
    (hmn : m ≡ n [ZMOD (q : ℤ)]) :
    charReal ((m : ℝ) / (q : ℝ)) = charReal ((n : ℝ) / (q : ℝ)) := by
  rcases (Int.modEq_iff_add_fac.mp hmn) with ⟨t, ht⟩
  have hm : m = n - (q : ℤ) * t := by omega
  calc
    charReal ((m : ℝ) / (q : ℝ)) = charReal (((n : ℝ) / (q : ℝ)) + (-(t : ℝ))) := by
      congr 1
      rw [hm]
      norm_num
      field_simp [show (q : ℝ) ≠ 0 by exact_mod_cast hq.ne']
      ring
    _ = charReal ((n : ℝ) / (q : ℝ)) := by
      simpa using charReal_periodic_int ((n : ℝ) / (q : ℝ)) (-t)

lemma cast_mul_sum {α : Type*} (s : Finset α) (c : ℝ) (f : α → ℝ) :
    (c : ℂ) * (∑ x ∈ s, (f x : ℂ)) = (algebraMap ℝ ℂ) (c * ∑ x ∈ s, f x) := by
  calc
    (c : ℂ) * (∑ x ∈ s, (f x : ℂ)) = ∑ x ∈ s, (c : ℂ) * (f x : ℂ) := by
      rw [Finset.mul_sum]
    _ = ∑ x ∈ s, ((c * f x : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro x hx
      norm_num
    _ = ((∑ x ∈ s, (c * f x : ℝ)) : ℂ) := by
      simp
    _ = (algebraMap ℝ ℂ) (c * ∑ x ∈ s, f x) := by
      rw [show (∑ x ∈ s, ((c * f x : ℝ) : ℂ)) =
          (algebraMap ℝ ℂ) (∑ x ∈ s, (c * f x : ℝ)) by
            exact (map_sum (algebraMap ℝ ℂ) (fun x => c * f x) s).symm]
      congr 1
      rw [Finset.mul_sum]

lemma zmodSum_eq_rangeSum {q : ℕ} [NeZero q] {M : Type*} [AddCommMonoid M] (f : ZMod q → M) :
    (∑ a : ZMod q, f a) = ∑ r ∈ Finset.range q, f (r : ZMod q) := by
  exact zmod_sum_range f

/-- Parseval's identity on `ZMod q`:
`∑_a |∑_x e(a x/q) z(x)|² = q ∑_x |z(x)|²`. -/
lemma zmodParseval_zmod {q : ℕ} [NeZero q] (z : ZMod q → ℂ) :
    (∑ a : ZMod q, ‖∑ x : ZMod q, charReal ((a.val : ℝ) * (x.val : ℝ) / (q : ℝ)) * z x‖ ^ 2) =
      (q : ℝ) * ∑ x : ZMod q, ‖z x‖ ^ 2 := by
  let z' : ℕ → ℂ := fun r => z (r : ZMod q)
  have hL : (∑ a : ZMod q, ‖∑ x : ZMod q, charReal ((a.val : ℝ) * (x.val : ℝ) / (q : ℝ)) * z x‖ ^ 2)
      = ∑ a ∈ Finset.range q, ‖∑ r ∈ Finset.range q, charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z' r‖ ^ 2 := by
    rw [zmodSum_eq_rangeSum]
    apply Finset.sum_congr rfl
    intro a ha
    have haq : (a : ZMod q).val = a := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha)]
    rw [haq]
    congr 1
    rw [zmodSum_eq_rangeSum]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    have hrq : (r : ZMod q).val = r := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]
    rw [hrq]
  have hR : (q : ℝ) * ∑ x : ZMod q, ‖z x‖ ^ 2 = (q : ℝ) * ∑ r ∈ Finset.range q, ‖z' r‖ ^ 2 := by
    congr 1
    rw [zmodSum_eq_rangeSum]
  have hP := zmodParseval (NeZero.pos q) z'
  have hP2 : (∑ a ∈ Finset.range q, ‖∑ r ∈ Finset.range q, charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z' r‖ ^ 2)
      = (q : ℝ) * ∑ r ∈ Finset.range q, ‖z' r‖ ^ 2 := by
    have hc : ((∑ a ∈ Finset.range q, ‖∑ r ∈ Finset.range q, charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z' r‖ ^ 2 : ℝ) : ℂ)
        = (algebraMap ℝ ℂ) ((q : ℝ) * (∑ r ∈ Finset.range q, ‖z' r‖ ^ 2)) := by
      calc
        ((∑ a ∈ Finset.range q, ‖∑ r ∈ Finset.range q, charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z' r‖ ^ 2 : ℝ) : ℂ)
            = (q : ℂ) * (∑ r ∈ Finset.range q, ((‖z' r‖ ^ 2 : ℝ) : ℂ)) := by
              simpa [map_sum] using hP
        _ = (algebraMap ℝ ℂ) ((q : ℝ) * (∑ r ∈ Finset.range q, ‖z' r‖ ^ 2)) := by
              exact cast_mul_sum (Finset.range q) (q : ℝ) (fun r => ‖z' r‖ ^ 2)
    exact Complex.ofReal_inj.mp hc
  calc
    (∑ a : ZMod q, ‖∑ x : ZMod q, charReal ((a.val : ℝ) * (x.val : ℝ) / (q : ℝ)) * z x‖ ^ 2)
        = ∑ a ∈ Finset.range q, ‖∑ r ∈ Finset.range q, charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z' r‖ ^ 2 := hL
    _ = (q : ℝ) * ∑ r ∈ Finset.range q, ‖z' r‖ ^ 2 := hP2
    _ = (q : ℝ) * ∑ x : ZMod q, ‖z x‖ ^ 2 := hR.symm

/-! ## Orthogonality of Dirichlet characters -/

lemma dirichletChar_norm_unit {q : ℕ} (χ : DirichletCharacter ℂ q) {a : ZMod q} (ha : IsUnit a) :
    ‖χ a‖ = 1 := by
  have : Fintype (ZMod q)ˣ := Fintype.ofFinite _
  let n : ℕ := Fintype.card (ZMod q)ˣ
  have hn : n ≠ 0 := ne_of_gt (Fintype.card_pos (α := (ZMod q)ˣ))
  have hpow_u : ha.unit ^ n = 1 := pow_card_eq_one (G := (ZMod q)ˣ) (x := ha.unit)
  have hspec : (a : ZMod q) = (ha.unit : ZMod q) := ha.unit_spec.symm
  have hpow_l : a ^ n = 1 := by
    rw [hspec]
    simpa using congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hpow_u
  have hpow_χ : (χ a) ^ n = 1 := by
    rw [← map_pow, hpow_l, map_one]
  exact Complex.norm_eq_one_of_pow_eq_one hpow_χ hn

lemma charNormSq_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (∑ a : ZMod q, ‖χ a‖ ^ 2) = (q.totient : ℝ) := by
  calc
    (∑ a : ZMod q, ‖χ a‖ ^ 2) = ∑ a : ZMod q, (if IsUnit a then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : IsUnit a
      · have hnorm : ‖χ a‖ = 1 := dirichletChar_norm_unit χ h
        simp [h, hnorm]
      · have h0 : χ a = 0 := χ.map_nonunit h
        simp [h, h0]
    _ = (q.totient : ℝ) := by
      -- the number of units of `ZMod q` is `φ(q)`
      rw [Finset.sum_boole]
      have hcard : (Finset.univ.filter (fun a : ZMod q => IsUnit a)).card = q.totient := by
        -- units of `ZMod q` as a subtype correspond to `(ZMod q)ˣ`
        rw [← Fintype.card_subtype]
        refine (Fintype.card_congr ?_).trans (ZMod.card_units_eq_totient q)
        refine ⟨fun x => x.2.unit, fun u => ⟨(u : ZMod q), ⟨u, rfl⟩⟩, ?_, ?_⟩
        · intro x
          apply Subtype.ext
          exact x.2.unit_spec.symm
        · intro u
          ext
          rfl
      simp [hcard]

/-- Orthogonality of the characters modulo `q`:
`∑_χ conj(χ(a)) χ(b) = φ(q)` if `a = b` is a unit, and `0` otherwise. -/
lemma charOrthSum_star {q : ℕ} [NeZero q] (a b : ZMod q) :
    (∑ χ : DirichletCharacter ℂ q, star (χ a) * χ b) =
      if IsUnit a ∧ IsUnit b ∧ a = b then (q.totient : ℂ) else 0 := by
  -- conjugate the relation `∑_χ χ(a) conj(χ(b)) = φ(q) [a = b unit]`
  calc
    (∑ χ : DirichletCharacter ℂ q, star (χ a) * χ b)
        = star (∑ χ : DirichletCharacter ℂ q, χ a * star (χ b)) := by
          change (∑ χ : DirichletCharacter ℂ q, star (χ a) * χ b) =
            (starRingEnd ℂ) (∑ χ : DirichletCharacter ℂ q, χ a * star (χ b))
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro χ hχ
          change star (χ a) * χ b = star (χ a * star (χ b))
          rw [star_mul, star_star]
          ring
    _ = if IsUnit a ∧ IsUnit b ∧ a = b then (q.totient : ℂ) else 0 := by
          rw [charOrthSum (Nat.pos_of_ne_zero (NeZero.ne q)) a b]
          -- `φ(q)` and `0` are real, hence fixed by conjugation
          split_ifs <;> simp

/-- Parseval over the characters modulo `q`:
`∑_χ |∑_x conj(χ(x)) T(x)|² = φ(q) ∑_{x unit} |T(x)|²`. -/
lemma charParseval_units {q : ℕ} [NeZero q] (T : ZMod q → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ x : ZMod q, star (χ x) * T x‖ ^ 2) =
      (q.totient : ℝ) * ∑ x : ZMod q, (if IsUnit x then ‖T x‖ ^ 2 else 0) := by
  have hC : (∑ χ : DirichletCharacter ℂ q, (‖∑ x : ZMod q, star (χ x) * T x‖ ^ 2 : ℂ)) =
      (q.totient : ℂ) * (∑ x : ZMod q, (if IsUnit x then (‖T x‖ ^ 2 : ℂ) else 0)) := by
    calc
      (∑ χ : DirichletCharacter ℂ q, (‖∑ x : ZMod q, star (χ x) * T x‖ ^ 2 : ℂ))
          = ∑ x : ZMod q, ∑ y : ZMod q,
              T x * star (T y) * (∑ χ : DirichletCharacter ℂ q, star (χ x) * χ y) := by
            -- expand the squares and swap the sums
            calc
              (∑ χ : DirichletCharacter ℂ q, (‖∑ x : ZMod q, star (χ x) * T x‖ ^ 2 : ℂ))
                  = ∑ χ : DirichletCharacter ℂ q, ∑ x : ZMod q, ∑ y : ZMod q,
                      (star (χ x) * T x) * star (star (χ y) * T y) := by
                    apply Finset.sum_congr rfl
                    intro χ hχ
                    exact normSq_sum_eq_sum_mul_star (Finset.univ)
                      (fun x : ZMod q => star (χ x) * T x)
              _ = ∑ x : ZMod q, ∑ y : ZMod q,
                    T x * star (T y) * (∑ χ : DirichletCharacter ℂ q, star (χ x) * χ y) := by
                    rw [Finset.sum_comm]
                    apply Finset.sum_congr rfl
                    intro x hx
                    rw [Finset.sum_comm]
                    apply Finset.sum_congr rfl
                    intro y hy
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro χ hχ
                    rw [star_mul, star_star]
                    ring
      _ = ∑ x : ZMod q, ∑ y : ZMod q,
            T x * star (T y) * (if IsUnit x ∧ IsUnit y ∧ x = y then (q.totient : ℂ) else 0) := by
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro y hy
            exact congrArg (fun t : ℂ => T x * star (T y) * t) (charOrthSum_star x y)
      _ = ∑ x : ZMod q, T x * star (T x) * (if IsUnit x then (q.totient : ℂ) else 0) := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hx' : IsUnit x
            · rw [Finset.sum_eq_single x]
              · simp [hx']
              · intro y hy hxy
                have hfalse : ¬ (IsUnit x ∧ IsUnit y ∧ x = y) := by
                  intro h
                  exact hxy (h.2.2.symm)
                simp [hfalse]
              · intro hnx
                exact False.elim (hnx (Finset.mem_univ x))
            · simp [hx']
      _ = (q.totient : ℂ) * ∑ x : ZMod q, (if IsUnit x then (‖T x‖ ^ 2 : ℂ) else 0) := by
            have h1 : (∑ x : ZMod q, T x * star (T x) * (if IsUnit x then (q.totient : ℂ) else 0)) =
                ∑ x : ZMod q, (if IsUnit x then T x * star (T x) * (q.totient : ℂ) else 0) := by
              apply Finset.sum_congr rfl
              intro x hx
              by_cases h : IsUnit x <;> simp [h]
            have h2 : (∑ x : ZMod q, (if IsUnit x then T x * star (T x) * (q.totient : ℂ) else 0)) =
                (q.totient : ℂ) * ∑ x : ZMod q, (if IsUnit x then (‖T x‖ ^ 2 : ℂ) else 0) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x hx
              by_cases h : IsUnit x
              · have hmul : T x * star (T x) = (‖T x‖ ^ 2 : ℂ) := by
                  have hc := Complex.mul_conj (T x)
                  rw [Complex.normSq_eq_norm_sq] at hc
                  simpa using hc
                simp [h]
                change T x * star (T x) * (q.totient : ℂ) = (q.totient : ℂ) * (‖T x‖ ^ 2 : ℂ)
                rw [hmul]
                ring
              · simp [h]
            exact h1.trans h2
  -- pass from `ℂ` back to `ℝ`
  exact Complex.ofReal_inj.mp (by
    calc
      ((∑ χ : DirichletCharacter ℂ q, ‖∑ x : ZMod q, star (χ x) * T x‖ ^ 2 : ℝ) : ℂ)
          = ∑ χ : DirichletCharacter ℂ q, (‖∑ x : ZMod q, star (χ x) * T x‖ ^ 2 : ℂ) := by
            simp
      _ = (q.totient : ℂ) * (∑ x : ZMod q, (if IsUnit x then (‖T x‖ ^ 2 : ℂ) else 0)) := hC
      _ = (algebraMap ℝ ℂ) ((q.totient : ℝ) * ∑ x : ZMod q, (if IsUnit x then ‖T x‖ ^ 2 else 0)) := by
            have hmid : (q.totient : ℂ) * (∑ x : ZMod q, (((if IsUnit x then ‖T x‖ ^ 2 else 0 : ℝ) : ℂ))) =
                (algebraMap ℝ ℂ) ((q.totient : ℝ) * ∑ x : ZMod q, (if IsUnit x then ‖T x‖ ^ 2 else 0)) := by
              simp
            calc
              (q.totient : ℂ) * (∑ x : ZMod q, (if IsUnit x then (‖T x‖ ^ 2 : ℂ) else 0))
                  = (q.totient : ℂ) * (∑ x : ZMod q, (((if IsUnit x then ‖T x‖ ^ 2 else 0 : ℝ) : ℂ))) := by
                    congr 1
                    apply Finset.sum_congr rfl
                    intro x hx
                    by_cases h : IsUnit x <;> simp [h]
              _ = (algebraMap ℝ ℂ) ((q.totient : ℝ) * ∑ x : ZMod q, (if IsUnit x then ‖T x‖ ^ 2 else 0)) := hmid)

lemma unitsSum_eq_reducedFracs {q : ℕ} [NeZero q] (T : ZMod q → ℂ) :
    (∑ x : ZMod q, (if IsUnit x then ‖T x‖ ^ 2 else 0)) =
      ∑ r ∈ (Finset.range q).filter (fun r => r.Coprime q), ‖T (r : ZMod q)‖ ^ 2 := by
  calc
    (∑ x : ZMod q, (if IsUnit x then ‖T x‖ ^ 2 else 0))
        = ∑ r ∈ Finset.range q,
            (if IsUnit (r : ZMod q) then ‖T (r : ZMod q)‖ ^ 2 else 0) := by
          rw [zmodSum_eq_rangeSum (f := fun x : ZMod q =>
            if IsUnit x then ‖T x‖ ^ 2 else 0)]
    _ = ∑ r ∈ (Finset.range q).filter (fun r => r.Coprime q), ‖T (r : ZMod q)‖ ^ 2 := by
          rw [← Finset.sum_filter]
          have hext : (Finset.range q).filter (fun r : ℕ => IsUnit (r : ZMod q)) =
              (Finset.range q).filter (fun r : ℕ => r.Coprime q) := by
            ext r
            constructor
            · intro h
              rw [Finset.mem_filter] at h ⊢
              exact ⟨h.1, (ZMod.isUnit_iff_coprime r q).1 h.2⟩
            · intro h
              rw [Finset.mem_filter] at h ⊢
              exact ⟨h.1, (ZMod.isUnit_iff_coprime r q).2 h.2⟩
          rw [hext]

end

end BombieriVinogradov

section

open Complex Finset ZMod

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/-! ## Gauss sums of primitive characters

Mathlib's `gaussSum_mul_gaussSum_eq_card` is stated over a finite field. For a
primitive character `χ` modulo an arbitrary `N`, Fourier inversion on `ZMod N`
(`ZMod.dft_dft`) gives `τ(χ) τ(χ⁻¹) = χ(-1) N`, and hence `‖τ(χ)‖² = N`.
-/

private lemma primitive_gaussSum_mul_inv_eq_card
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    gaussSum χ stdAddChar * gaussSum χ⁻¹ stdAddChar = χ (-1) * N := by
  have hDFT := congrFun (ZMod.dft_dft (χ : ZMod N → ℂ)) 1
  rw [ZMod.dft_apply] at hDFT
  simp_rw [hχ.fourierTransform_eq_inv_mul_gaussSum] at hDFT
  have hsum :
      (∑ j : ZMod N, stdAddChar (-j) * (χ⁻¹ (-j) * gaussSum χ stdAddChar)) =
        gaussSum χ stdAddChar * gaussSum χ⁻¹ stdAddChar := by
    calc
      _ = ∑ j : ZMod N, χ⁻¹ j * stdAddChar j * gaussSum χ stdAddChar := by
        refine Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ fun j ↦ ?_
        simp only [Equiv.neg_apply]
        ring
      _ = (∑ j : ZMod N, χ⁻¹ j * stdAddChar j) * gaussSum χ stdAddChar := by
        rw [Finset.sum_mul]
      _ = gaussSum χ⁻¹ stdAddChar * gaussSum χ stdAddChar := rfl
      _ = _ := mul_comm _ _
  have hDFT' :
      (∑ j : ZMod N, stdAddChar (-j) * (χ⁻¹ (-j) * gaussSum χ stdAddChar)) =
        (N : ℂ) * χ (-1) := by
    simpa [smul_eq_mul] using hDFT
  rw [hsum] at hDFT'
  simpa [mul_comm] using hDFT'

private lemma primitive_norm_gaussSum_sq
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ stdAddChar‖ ^ 2 = N := by
  let g := gaussSum χ stdAddChar
  have hstar : star g = χ (-1) * gaussSum χ⁻¹ stdAddChar := by
    rw [show star g = gaussSum χ⁻¹ stdAddChar⁻¹ by
      exact star_gaussSum_eq χ stdAddChar]
    rw [AddChar.inv_mulShift]
    simpa using
      (gaussSum_mulShift_eq χ⁻¹ stdAddChar (-1 : (ZMod N)ˣ))
  have hprod := primitive_gaussSum_mul_inv_eq_card hχ
  have hnormSq : Complex.normSq g = N := by
    apply Complex.ofReal_injective
    rw [Complex.normSq_eq_conj_mul_self]
    change star g * g = (N : ℂ)
    rw [hstar]
    calc
      χ (-1) * gaussSum χ⁻¹ stdAddChar * g =
          χ (-1) * (g * gaussSum χ⁻¹ stdAddChar) := by ring
      _ = χ (-1) * (χ (-1) * N) := by rw [hprod]
      _ = (χ (-1) * χ (-1)) * N := by ring
      _ = N := by rw [← map_mul]; norm_num
  rw [Complex.sq_norm, hnormSq]

/-- The root number `τ(χ) / (i^κ √N)` of a primitive character `χ`, where `χ(-1) = (-1)^κ`,
has norm one. -/
theorem IsPrimitive.norm_rootNumber {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    ‖χ.rootNumber‖ = 1 := by
  rcases eq_or_ne N 1 with rfl | _hN
  · rw [rootNumber_modOne, norm_one]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  have hgauss_sq : ‖gaussSum χ stdAddChar‖ ^ 2 = (N : ℝ) :=
    primitive_norm_gaussSum_sq hχ
  have hgauss : ‖gaussSum χ stdAddChar‖ = Real.sqrt N := by
    nlinarith [Real.sq_sqrt (le_of_lt hNpos), norm_nonneg (gaussSum χ stdAddChar),
      Real.sqrt_nonneg (N : ℝ)]
  have hcpow : (N : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt N : ℂ) := by
    calc
      (N : ℂ) ^ (1 / 2 : ℂ) = (N : ℂ) ^ ((1 / 2 : ℝ) : ℂ) := by norm_num
      _ = (((N : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) :=
        (Complex.ofReal_cpow (le_of_lt hNpos) (1 / 2 : ℝ)).symm
      _ = (Real.sqrt N : ℂ) := by rw [Real.sqrt_eq_rpow]
  rw [rootNumber, norm_div, norm_div, norm_pow, Complex.norm_I, one_pow, hcpow,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), hgauss]
  field_simp [Real.sqrt_ne_zero'.mpr hNpos]

end DirichletCharacter

end

/-! ## Primitive characters of a fixed modulus

`PrimitiveCharacter q` is the finite type of primitive characters modulo `q`.
Every character modulo `q` is induced by the primitive character modulo its
conductor.
-/

namespace BombieriVinogradov

open scoped BigOperators
open Classical
noncomputable section

/-- Primitive complex Dirichlet characters modulo `q`, as a subtype of
`DirichletCharacter ℂ q`. -/
abbrev PrimitiveCharacter (q : ℕ) :=
  {χ : DirichletCharacter ℂ q // χ.IsPrimitive}

noncomputable instance (q : ℕ) : Fintype (PrimitiveCharacter q) :=
  Fintype.ofFinite _

theorem primitiveCharacter_card_le_totient_basic (q : ℕ) (hq : 0 < q) :
    Fintype.card (PrimitiveCharacter q) ≤ q.totient := by
  let : NeZero q := ⟨hq.ne'⟩
  calc
    Fintype.card (PrimitiveCharacter q) ≤
        Fintype.card (DirichletCharacter ℂ q) := Fintype.card_subtype_le _
    _ = q.totient := by
      rw [← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

/-- The primitive characters modulo `q`, as a finset of all characters modulo `q`. -/
noncomputable def primitiveCharacters (q : ℕ) :
    Finset (DirichletCharacter ℂ q) :=
  Finset.univ.filter DirichletCharacter.IsPrimitive

@[simp]
theorem mem_primitiveCharacters {q : ℕ} {χ : DirichletCharacter ℂ q} :
    χ ∈ primitiveCharacters q ↔ χ.IsPrimitive := by
  simp [primitiveCharacters]

@[simp]
theorem primitive_conductor {q : ℕ} (χ : PrimitiveCharacter q) :
    χ.1.conductor = q :=
  χ.2

/-- The primitive character modulo the conductor of `χ` that induces `χ`. -/
noncomputable def conductorPrimitiveCharacter {q : ℕ}
    (χ : DirichletCharacter ℂ q) : PrimitiveCharacter χ.conductor :=
  ⟨χ.primitiveCharacter, χ.primitiveCharacter_isPrimitive⟩

/-- Every character `χ` modulo `q` is induced by the primitive character modulo its
conductor. -/
theorem changeLevel_conductorPrimitiveCharacter {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    DirichletCharacter.changeLevel χ.conductor_dvd_level
      (conductorPrimitiveCharacter χ).1 = χ :=
  χ.changeLevel_primitiveCharacter

theorem sum_primitive_eq_filter {q : ℕ} {β : Type*} [AddCommMonoid β]
    (f : DirichletCharacter ℂ q → β) :
    (∑ χ : PrimitiveCharacter q, f χ.1) =
      ∑ χ ∈ primitiveCharacters q, f χ := by
  exact (Finset.sum_subtype (primitiveCharacters q)
    (fun χ => mem_primitiveCharacters) f).symm

theorem sum_primitive_le_sum_all {q : ℕ}
    (f : DirichletCharacter ℂ q → ℝ) (hf : ∀ χ, 0 ≤ f χ) :
    (∑ χ : PrimitiveCharacter q, f χ.1) ≤
      ∑ χ : DirichletCharacter ℂ q, f χ := by
  rw [sum_primitive_eq_filter]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun χ _ _ => hf χ)

/-! ## Gauss sums against `x ↦ e(x/q)` -/

/-- The primitive `q`-th root of unity `e(1/q)`. -/
private def primitiveGaussRoot (q : ℕ) : ℂ := charReal (1 / (q : ℝ))

private lemma primitiveGaussRoot_isPrimitiveRoot (q : ℕ) (hq : q ≠ 0) :
    IsPrimitiveRoot (primitiveGaussRoot q) q := by
  have h := Complex.isPrimitiveRoot_exp_of_isCoprime (1 : ℤ) q hq isCoprime_one_left
  convert h using 1
  dsimp [primitiveGaussRoot, charReal]
  congr 1
  norm_num
  ring

private lemma primitiveGaussRoot_pow (q : ℕ) (hq : q ≠ 0) :
    primitiveGaussRoot q ^ q = 1 :=
  (primitiveGaussRoot_isPrimitiveRoot q hq).pow_eq_one

/-- The additive character `x ↦ e(x/q) = exp(2πix/q)` on `ZMod q`. -/
noncomputable def primitiveGaussAddChar (q : ℕ) [NeZero q] : AddChar (ZMod q) ℂ :=
  AddChar.zmodChar q (primitiveGaussRoot_pow q (NeZero.ne q))

@[simp]
theorem primitiveGaussAddChar_apply (q : ℕ) [NeZero q] (a : ZMod q) :
    primitiveGaussAddChar q a = charReal ((a.val : ℝ) / (q : ℝ)) := by
  rw [primitiveGaussAddChar, AddChar.zmodChar_apply, primitiveGaussRoot]
  rw [← charReal_nat_mul a.val (1 / (q : ℝ))]
  congr 1
  exact mul_one_div (a.val : ℝ) (q : ℝ)

private theorem charReal_eq_of_int_modEq {q : ℕ} (hq : 0 < q) {m n : ℤ}
    (hmn : m ≡ n [ZMOD (q : ℤ)]) :
    charReal ((m : ℝ) / (q : ℝ)) = charReal ((n : ℝ) / (q : ℝ)) := by
  exact charReal_periodic_zmod hq hmn

private theorem primitiveGaussAddChar_mulShift_apply (q : ℕ) [NeZero q]
    (n : ℤ) (x : ZMod q) :
    (primitiveGaussAddChar q).mulShift (n : ZMod q) x =
      charReal ((n : ℝ) * (x.val : ℝ) / (q : ℝ)) := by
  rw [AddChar.mulShift_apply, primitiveGaussAddChar_apply]
  have heq : ((n : ZMod q) * x : ZMod q) =
      ((n * (x.val : ℤ) : ℤ) : ZMod q) := by
    calc
      (n : ZMod q) * x = (n : ZMod q) * ((x.val : ℤ) : ZMod q) := by
        rw [Int.cast_natCast, ZMod.natCast_zmod_val]
      _ = ((n * (x.val : ℤ) : ℤ) : ZMod q) := by
        exact (Int.cast_mul (α := ZMod q) n (x.val : ℤ)).symm
  have hmod : (((n : ZMod q) * x).val : ℤ) ≡ n * (x.val : ℤ) [ZMOD (q : ℤ)] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ q).1
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    exact heq
  have hmain := charReal_eq_of_int_modEq (NeZero.pos q) hmod
  convert hmain using 1 <;> norm_num [Int.cast_mul]

theorem sum_zmod_eq_sum_range {q : ℕ} [NeZero q] {M : Type*} [AddCommMonoid M]
    (f : ZMod q → M) :
    (∑ a : ZMod q, f a) = ∑ r ∈ Finset.range q, f (r : ZMod q) := by
  exact zmod_sum_range f

theorem zmod_fourier_energy {q : ℕ} [NeZero q] (z : ZMod q → ℂ) :
    (∑ a : ZMod q,
        ‖∑ x : ZMod q,
          charReal ((a.val : ℝ) * (x.val : ℝ) / (q : ℝ)) * z x‖ ^ 2) =
      (q : ℝ) * ∑ x : ZMod q, ‖z x‖ ^ 2 := by
  exact zmodParseval_zmod z

theorem dirichletCharacter_sum_norm_sq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (∑ a : ZMod q, ‖χ a‖ ^ 2) = (q.totient : ℝ) := by
  exact charNormSq_sum χ

theorem gaussSum_primitiveGaussAddChar_mulShift {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    gaussSum χ ((primitiveGaussAddChar q).mulShift a) =
      ∑ x : ZMod q,
        χ x * charReal ((a.val : ℝ) * (x.val : ℝ) / (q : ℝ)) := by
  unfold gaussSum
  apply Finset.sum_congr rfl
  intro x _
  have ha : ((a.val : ℤ) : ZMod q) = a := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [show (primitiveGaussAddChar q).mulShift a x =
      charReal ((a.val : ℝ) * (x.val : ℝ) / (q : ℝ)) by
    have h := primitiveGaussAddChar_mulShift_apply q (a.val : ℤ) x
    rw [ha] at h
    convert h using 1
    all_goals norm_num]

/-- For a primitive character `χ` modulo `q`, `|τ(χ)|² = q`. The proof applies Parseval
to `a ↦ τ(χ, x ↦ e(a x/q)) = χ⁻¹(a) τ(χ)`. -/
theorem primitive_gaussSum_norm_sq {q : ℕ} [NeZero q]
    (χ : PrimitiveCharacter q) :
    ‖gaussSum χ.1 (primitiveGaussAddChar q)‖ ^ 2 = (q : ℝ) := by
  have hP := zmod_fourier_energy (z := fun x => χ.1 x)
  have hL :
      (∑ a : ZMod q,
          ‖gaussSum χ.1 ((primitiveGaussAddChar q).mulShift a)‖ ^ 2) =
        (q : ℝ) * ∑ x : ZMod q, ‖χ.1 x‖ ^ 2 := by
    rw [← hP]
    apply Finset.sum_congr rfl
    intro a _
    rw [gaussSum_primitiveGaussAddChar_mulShift]
    congr 2
    apply Finset.sum_congr rfl
    intro x _
    rw [mul_comm]
  have hR :
      (∑ a : ZMod q,
          ‖gaussSum χ.1 ((primitiveGaussAddChar q).mulShift a)‖ ^ 2) =
        ‖gaussSum χ.1 (primitiveGaussAddChar q)‖ ^ 2 * (q.totient : ℝ) := by
    calc
      _ = ∑ a : ZMod q,
          ‖χ.1⁻¹ a * gaussSum χ.1 (primitiveGaussAddChar q)‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro a _
            rw [gaussSum_mulShift_of_isPrimitive
              (e := primitiveGaussAddChar q) χ.2 a]
      _ = ∑ a : ZMod q,
          ‖χ.1⁻¹ a‖ ^ 2 * ‖gaussSum χ.1 (primitiveGaussAddChar q)‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro a _
            rw [norm_mul]
            ring
      _ = ‖gaussSum χ.1 (primitiveGaussAddChar q)‖ ^ 2 *
          (∑ a : ZMod q, ‖χ.1⁻¹ a‖ ^ 2) := by
            rw [← Finset.sum_mul]
            ring
      _ = _ := by rw [dirichletCharacter_sum_norm_sq]
  have hEq :
      ‖gaussSum χ.1 (primitiveGaussAddChar q)‖ ^ 2 * (q.totient : ℝ) =
        (q : ℝ) * (q.totient : ℝ) := by
    rw [← hR, hL, dirichletCharacter_sum_norm_sq]
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  exact mul_right_cancel₀ hφ hEq

end

end BombieriVinogradov
