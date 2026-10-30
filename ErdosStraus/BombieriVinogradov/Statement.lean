import ErdosStraus.BombieriVinogradov.LargeSieve.PrimitiveCharacters
import ErdosStraus.BombieriVinogradov.PNT.MediumPNT
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.AlmostPrime

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

/-!
# Statement of the Bombieri–Vinogradov theorem

We define the logarithmic integral `li(x) = 2 / log 2 + ∫_2^x dt / log t`, the error
`E(x; q, l) = π(x; q, l) - li(x) / φ(q)` for primes in arithmetic progressions, and its
maximum over reduced residues `l` and endpoints `y ≤ x`. The proposition `StandardForm` is the
Bombieri–Vinogradov theorem: for every `A > 0` there is `B ≥ 0` with
`∑_{q ≤ N^{1/2} / (log N)^B} max_{y ≤ N} max_{(l,q)=1} |E(y; q, l)| ≪ N / (log N)^A`.
See Bombieri, *On the large sieve* (1965), and Halberstam–Richert, *Sieve Methods*, Chapter 9.
-/

section

/-! ## The logarithmic integral -/

open MeasureTheory intervalIntegral

namespace BombieriVinogradov

/-- The logarithmic integral `κ + ∫_2^x dt / log t` with additive constant `κ`. -/
noncomputable def shiftedLogIntegral (κ x : ℝ) : ℝ :=
  κ + ∫ t in (2 : ℝ)..x, 1 / Real.log t

lemma inv_log_intervalIntegrable_of_two_le
    {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume a b := by
  apply intervalIntegral.intervalIntegrable_one_div
  · intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact ne_of_gt (Real.log_pos (by linarith [ht.1]))
  · apply Real.continuousOn_log.mono
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [ht.1]

lemma inv_log_intervalIntegrable {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 x :=
  inv_log_intervalIntegrable_of_two_le (le_refl 2) hx

end BombieriVinogradov

end

section

/-! ## The modulus cutoff -/

open scoped Asymptotics BigOperators

namespace BombieriVinogradov

open Filter Finset

/-- The modulus cutoff `⌊N^{1/2} / (log N)^B⌋`. -/
noncomputable def modulusCutoff (N : ℕ) (B : ℝ) : ℕ :=
  Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ B)

end BombieriVinogradov

end

/-! ## Primes in arithmetic progressions -/

namespace BombieriVinogradov

open Real Finset Filter
open scoped Classical BigOperators

/-- The logarithmic integral `li(x) = 2 / log 2 + ∫_2^x dt / log t`. The constant `2 / log 2`
makes `li(x) ≥ x / log x` for `x ≥ 2`. -/
noncomputable def logIntegral (x : ℝ) : ℝ :=
  shiftedLogIntegral (2 / Real.log 2) x

/-- The number `π(x; q, l)` of primes `p ≤ x` with `p ≡ l (mod q)`. -/
def primesInAP (x q l : ℕ) : ℕ :=
  ((range (x + 1)).filter (fun p => p.Prime ∧ p ≡ l [MOD q])).card

/-- The error `E(x; q, l) = π(x; q, l) - li(x) / φ(q)`. -/
noncomputable def primeAPError (x q l : ℕ) : ℝ :=
  (primesInAP x q l : ℝ) - logIntegral x / Nat.totient q

/-- The maximum of `|E(x; q, l)|` over reduced residues `0 ≤ l < q`, and `0` when `q = 0`. -/
noncomputable def primeAPMaxError (x q : ℕ) : ℝ :=
  let S := BombieriVinogradov.unitResidues q
  if h : S.Nonempty then
    (S.image (fun l => |primeAPError x q l|)).max'
      (Finset.image_nonempty.mpr h)
  else 0

theorem abs_primeAPError_le_max {x q l : ℕ}
    (hl : l ∈ BombieriVinogradov.unitResidues q) :
    |primeAPError x q l| ≤ primeAPMaxError x q := by
  unfold primeAPMaxError
  dsimp only
  have hS : (BombieriVinogradov.unitResidues q).Nonempty := ⟨l, hl⟩
  rw [dif_pos hS]
  exact Finset.le_max' ((BombieriVinogradov.unitResidues q).image
    (fun l => |primeAPError x q l|)) _
    (Finset.mem_image.mpr ⟨l, hl, rfl⟩)

/-- The maximum `max_{y ≤ x} max_{(l,q)=1} |E(y; q, l)|` over integer endpoints `y`. -/
noncomputable def primeAPPrefixMaxError (x q : ℕ) : ℝ :=
  ((range (x + 1)).image (fun y => primeAPMaxError y q)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

theorem primeAPMaxError_le_prefixMaxError (x q : ℕ) :
    primeAPMaxError x q ≤ primeAPPrefixMaxError x q := by
  unfold primeAPPrefixMaxError
  exact Finset.le_max'
    ((range (x + 1)).image (fun y => primeAPMaxError y q)) _
    (Finset.mem_image.mpr ⟨x, by simp, rfl⟩)

theorem primeAPMaxError_nonneg (x q : ℕ) :
    0 ≤ primeAPMaxError x q := by
  by_cases hS : (BombieriVinogradov.unitResidues q).Nonempty
  · obtain ⟨l, hl⟩ := hS
    exact (abs_nonneg _).trans (abs_primeAPError_le_max hl)
  · simp [primeAPMaxError, hS]

theorem primeAPPrefixMaxError_nonneg (x q : ℕ) :
    0 ≤ primeAPPrefixMaxError x q :=
  (primeAPMaxError_nonneg x q).trans
    (primeAPMaxError_le_prefixMaxError x q)

/-- **The Bombieri–Vinogradov theorem.** For every `A > 0` there are `B ≥ 0` and `C > 0` such
that for all large `N`,
`∑_{1 ≤ q ≤ N^{1/2} / (log N)^B} max_{y ≤ N} max_{(l,q)=1} |E(y; q, l)| ≤ C N / (log N)^A`. -/
def StandardForm : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, 2 ≤ N →
        ∑ q ∈ Finset.Icc 1 (modulusCutoff N B),
          primeAPPrefixMaxError N q ≤
            C * (N : ℝ) / Real.log N ^ A

end BombieriVinogradov

section

open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace BombieriVinogradov

open Finset
open _root_.BombieriVinogradov
open BombieriVinogradov

theorem modulusCutoff_sq_le
    (N : ℕ) (B : ℝ) (hN : 3 ≤ N) (hB : 0 ≤ B) :
    modulusCutoff N B ^ 2 ≤ N := by
  have hNpos : (0 : ℝ) < N := by positivity
  have hlog : (1 : ℝ) ≤ Real.log N := by
    apply (Real.le_log_iff_exp_le hNpos).2
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hN)
  have hden : 1 ≤ Real.log N ^ B := Real.one_le_rpow hlog hB
  have hquot : (N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ B ≤
      (N : ℝ) ^ (1 / 2 : ℝ) :=
    div_le_self (Real.rpow_nonneg hNpos.le _) hden
  have hcut : (modulusCutoff N B : ℝ) ≤
      (N : ℝ) ^ (1 / 2 : ℝ) :=
    (Nat.floor_le (by positivity)).trans hquot
  have hsqR : (modulusCutoff N B : ℝ) ^ 2 ≤ (N : ℝ) := by
    calc
      (modulusCutoff N B : ℝ) ^ 2 ≤
          ((N : ℝ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hcut 2
      _ = (N : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
        norm_num
  exact_mod_cast hsqR

end BombieriVinogradov

end
