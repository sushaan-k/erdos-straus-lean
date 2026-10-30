import ErdosStraus.Estimates.Progressions
import ErdosStraus.Estimates.PartialSummation
import ErdosStraus.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.ZetaValues

/-! # Lemma 3.2: squarefree reciprocal sums in progressions

For squarefree `M ≤ X^{C₀}`, squarefree `D ≤ U = (log X)^8` with `(M, D) = (b, D) = 1`, and
`X^{a₀} ≤ U₀ < U₁ ≤ X^{b₀}` with `U₁/U₀ ≥ X^{c₀}`, this file proves
`∑_{U₀ < n ≤ U₁, n squarefree, (n, M) = 1, n ≡ b (mod D)} 1/n ≍ (1/D)(φ(M)/M) log(U₁/U₀)`,
and the bound (7) for reciprocal sums over one residue class. It also defines the sums over
squarefree `s ≤ X^η` and over odd divisors of `P(z)` that appear in Lemmas 3.3 and 6.4.
-/

namespace ErdosStraus.ProgressionEstimates

open scoped BigOperators

/-! ## Finite windows -/

/-- Partial summation from a lower bound for the number of `n ∈ [L, V)` satisfying `p`. -/
theorem reciprocal_Ico_ge_of_count_ge (p : ℕ → Prop) [DecidablePred p]
    (L U : ℕ) (hL : 0 < L) (hLU : L ≤ U) (α B : ℝ) (hB : 0 ≤ B)
    (hcount : ∀ V, L ≤ V → V ≤ U →
      ((V : ℝ) - (L : ℝ)) * α - B ≤ (((Finset.Ico L V).filter p).card : ℝ)) :
    α * (∑ n ∈ Finset.Ico L U, (1 : ℝ) / (n : ℝ)) - B / (L : ℝ) ≤
      ∑ n ∈ (Finset.Ico L U).filter p, (1 : ℝ) / (n : ℝ) := by
  classical
  have hcomp : ∀ V, L ≤ V → V ≤ U →
      (((Finset.Ico L V).filter (fun n => ¬ p n)).card : ℝ) ≤
        ((V : ℝ) - (L : ℝ)) * (1 - α) + B := by
    intro V hLV hVU
    have hc := hcount V hLV hVU
    have hpart := Finset.card_filter_add_card_filter_not
      (s := Finset.Ico L V) p
    have hpartR : (((Finset.Ico L V).filter p).card : ℝ) +
        (((Finset.Ico L V).filter (fun n => ¬ p n)).card : ℝ) =
        (V : ℝ) - (L : ℝ) := by
      have hh : (((Finset.Ico L V).filter p).card : ℝ) +
          (((Finset.Ico L V).filter (fun n => ¬ p n)).card : ℝ) =
          ((Finset.Ico L V).card : ℝ) := by exact_mod_cast hpart
      simpa [Nat.card_Ico, Nat.cast_sub hLV] using hh
    nlinarith
  have h := SieveEstimates.reciprocal_Ico_le_of_count_le (fun n => ¬ p n)
    L U hL hLU (1 - α) B hB hcomp
  have hpart : (∑ n ∈ (Finset.Ico L U).filter p, (1 : ℝ) / (n : ℝ)) +
      (∑ n ∈ (Finset.Ico L U).filter (fun n => ¬ p n), (1 : ℝ) / (n : ℝ)) =
      ∑ n ∈ Finset.Ico L U, (1 : ℝ) / (n : ℝ) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  nlinarith

theorem sum_Ico_reciprocal_ge_log (L U : ℕ) (hL : 0 < L) (hLU : L ≤ U) :
    Real.log ((U : ℝ) / (L : ℝ)) ≤
      ∑ n ∈ Finset.Ico L U, (1 : ℝ) / (n : ℝ) := by
  have hLR : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  induction U, hLU using Nat.le_induction with
  | base => simp [ne_of_gt hLR]
  | succ U hLU ih =>
    have hUR : (0 : ℝ) < U := Nat.cast_pos.mpr (hL.trans_le hLU)
    have hU1R : (0 : ℝ) < ((U + 1 : ℕ) : ℝ) := by positivity
    have hstep : Real.log (((U + 1 : ℕ) : ℝ) / (U : ℝ)) ≤ 1 / (U : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (div_pos hU1R hUR)
      have he : (((U + 1 : ℕ) : ℝ) / (U : ℝ)) - 1 = 1 / (U : ℝ) := by
        push_cast
        field_simp
        ring
      rwa [he] at h
    rw [Finset.sum_Ico_succ_top (by omega)]
    have hlog : Real.log ((U : ℝ) / (L : ℝ)) +
        Real.log (((U + 1 : ℕ) : ℝ) / (U : ℝ)) =
        Real.log (((U + 1 : ℕ) : ℝ) / (L : ℝ)) := by
      rw [← Real.log_mul (ne_of_gt (div_pos hUR hLR))
        (ne_of_gt (div_pos hU1R hUR))]
      congr 1
      field_simp
    linarith

theorem squarefree_coprime_progression_prefix_card_lower
    (L U D b M : ℕ) (hL : 0 < L) (hLU : L ≤ U)
    (hD : 0 < D) (hM : Squarefree M) (hDM : Nat.Coprime D M)
    (hb : Nat.Coprime b D) :
    ((U : ℝ) - (L : ℝ)) *
        (((Nat.totient M : ℝ) / (M : ℝ)) / (4 * (D : ℝ)) -
          (M.divisors.card : ℝ) / Real.sqrt (L : ℝ)) -
        2 * (M.divisors.card : ℝ) * (Real.sqrt (L : ℝ) + 2) ≤
      (((Finset.Ico L U).filter (fun n => n ≡ b [MOD D] ∧
        Nat.Coprime n M ∧ Squarefree n)).card : ℝ) := by
  classical
  have hLR : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hR : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr hLR
  have hsqL := Real.sq_sqrt hLR.le
  have hsqU := Real.sq_sqrt (Nat.cast_nonneg U : (0 : ℝ) ≤ U)
  have hcastK : ((Nat.sqrt U : ℕ) : ℝ) ≤ Real.sqrt (U : ℝ) := by
    have hsq : (((Nat.sqrt U : ℕ) : ℝ) ^ 2) ≤ (U : ℝ) := by
      exact_mod_cast Nat.sqrt_le' U
    nlinarith [Real.sqrt_nonneg (U : ℝ),
      (Nat.cast_nonneg (Nat.sqrt U) : (0 : ℝ) ≤ (Nat.sqrt U : ℝ))]
  have hroot : Real.sqrt (U : ℝ) ≤ Real.sqrt (L : ℝ) +
      ((U : ℝ) - (L : ℝ)) / (2 * Real.sqrt (L : ℝ)) := by
    have hh : Real.sqrt (U : ℝ) - Real.sqrt (L : ℝ) ≤
        ((U : ℝ) - (L : ℝ)) / (2 * Real.sqrt (L : ℝ)) := by
      rw [le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt (L : ℝ))]
      nlinarith [sq_nonneg (Real.sqrt (U : ℝ) - Real.sqrt (L : ℝ))]
    linarith
  have hcount := squarefree_coprime_progression_card_lower L U D b M (Nat.sqrt U + 1)
    hL hLU (by
      have hh := (Nat.lt_succ_sqrt' U).le
      simpa only [Nat.succ_eq_add_one] using hh.trans (Nat.le_add_right _ 1)) hD hM hDM hb
  simp only [Nat.cast_add, Nat.cast_one] at hcount
  have hset : ((((Finset.Ico L U).filter (fun n => n ≡ b [MOD D])).filter
      (fun n => Nat.Coprime n M)).filter Squarefree) =
      (Finset.Ico L U).filter (fun n => n ≡ b [MOD D] ∧
        Nat.Coprime n M ∧ Squarefree n) := by
    ext n
    simp only [Finset.mem_filter]
    tauto
  rw [hset] at hcount
  have hτ : (0 : ℝ) ≤ (M.divisors.card : ℝ) := Nat.cast_nonneg _
  have herror : 2 * (M.divisors.card : ℝ) *
      (((Nat.sqrt U : ℕ) : ℝ) + 1 + 1) ≤
        2 * (M.divisors.card : ℝ) * (Real.sqrt (L : ℝ) + 2) +
          ((U : ℝ) - (L : ℝ)) *
            ((M.divisors.card : ℝ) / Real.sqrt (L : ℝ)) := by
    have hm := mul_le_mul_of_nonneg_left (hcastK.trans hroot)
      (show 0 ≤ 2 * (M.divisors.card : ℝ) by positivity)
    have he : 2 * (M.divisors.card : ℝ) *
        (((U : ℝ) - (L : ℝ)) / (2 * Real.sqrt (L : ℝ))) =
        ((U : ℝ) - (L : ℝ)) *
          ((M.divisors.card : ℝ) / Real.sqrt (L : ℝ)) := by field_simp
    rw [mul_add, he] at hm
    linarith
  have hmain : (1 / 4 : ℝ) * (((U : ℝ) - (L : ℝ)) / (D : ℝ)) *
      ((Nat.totient M : ℝ) / (M : ℝ)) =
      ((U : ℝ) - (L : ℝ)) *
        (((Nat.totient M : ℝ) / (M : ℝ)) / (4 * (D : ℝ))) := by ring
  rw [hmain] at hcount
  nlinarith only [hcount, herror]

/-- Lower bound for the squarefree `n ∈ [L, U)` with `(n, M) = 1` and `n ≡ b (mod D)`.
The error `6 τ(M)/√L` depends only on `L`. -/
theorem squarefree_coprime_progression_reciprocal_lower
    (L U D b M : ℕ) (hL : 0 < L) (hLU : L ≤ U)
    (hD : 0 < D) (hM : Squarefree M) (hDM : Nat.Coprime D M)
    (hb : Nat.Coprime b D)
    (hlarge : 8 * (M.divisors.card : ℝ) * (D : ℝ) ≤
      ((Nat.totient M : ℝ) / (M : ℝ)) * Real.sqrt (L : ℝ)) :
    (((Nat.totient M : ℝ) / (M : ℝ)) / (8 * (D : ℝ))) *
        Real.log ((U : ℝ) / (L : ℝ)) -
        6 * (M.divisors.card : ℝ) / Real.sqrt (L : ℝ) ≤
      ∑ n ∈ (Finset.Ico L U).filter (fun n => n ≡ b [MOD D] ∧
        Nat.Coprime n M ∧ Squarefree n), (1 : ℝ) / (n : ℝ) := by
  classical
  let ρ : ℝ := (Nat.totient M : ℝ) / (M : ℝ)
  let τ : ℝ := M.divisors.card
  let R : ℝ := Real.sqrt (L : ℝ)
  have hLR : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hR : 0 < R := Real.sqrt_pos.mpr hLR
  have hR1 : 1 ≤ R := by
    have hL1 : (1 : ℝ) ≤ L := Nat.one_le_cast.mpr hL
    simpa [R] using Real.sqrt_le_sqrt hL1
  have hD0 : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hτ : 0 ≤ τ := Nat.cast_nonneg _
  have hcoeff : ρ / (8 * (D : ℝ)) ≤ ρ / (4 * (D : ℝ)) - τ / R := by
    change 8 * τ * (D : ℝ) ≤ ρ * R at hlarge
    rw [le_sub_iff_add_le]
    apply (le_div_iff₀ (by positivity : 0 < 4 * (D : ℝ))).mpr
    have hh : τ / R * (8 * (D : ℝ)) ≤ ρ := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hR).mpr
      nlinarith only [hlarge]
    have he : ρ / (8 * (D : ℝ)) * (4 * (D : ℝ)) = ρ / 2 := by field_simp; ring
    rw [add_mul, he]
    nlinarith
  have herror : (2 * τ * (R + 2)) / (L : ℝ) ≤ 6 * τ / R := by
    have hsq : R ^ 2 = (L : ℝ) := Real.sq_sqrt hLR.le
    apply (div_le_div_iff₀ hLR hR).mpr
    calc
      2 * τ * (R + 2) * R ≤ (6 * τ * R) * R :=
        mul_le_mul_of_nonneg_right (by nlinarith) hR.le
      _ = 6 * τ * (L : ℝ) := by rw [← hsq]; ring
  have hprefix : ∀ V, L ≤ V → V ≤ U →
      ((V : ℝ) - (L : ℝ)) * (ρ / (8 * (D : ℝ))) -
        2 * τ * (R + 2) ≤
        (((Finset.Ico L V).filter (fun n => n ≡ b [MOD D] ∧
          Nat.Coprime n M ∧ Squarefree n)).card : ℝ) := by
    intro V hLV hVU
    have h := squarefree_coprime_progression_prefix_card_lower L V D b M
      hL hLV hD hM hDM hb
    exact (sub_le_sub_right (mul_le_mul_of_nonneg_left hcoeff
      (sub_nonneg.mpr (Nat.cast_le.mpr hLV))) _).trans h
  have h := reciprocal_Ico_ge_of_count_ge
    (fun n => n ≡ b [MOD D] ∧ Nat.Coprime n M ∧ Squarefree n)
    L U hL hLU (ρ / (8 * (D : ℝ))) (2 * τ * (R + 2)) (by positivity) hprefix
  have hlog := mul_le_mul_of_nonneg_left (sum_Ico_reciprocal_ge_log L U hL hLU)
    (show 0 ≤ ρ / (8 * (D : ℝ)) by positivity)
  change ρ / (8 * (D : ℝ)) * _ - 6 * τ / R ≤ _
  linarith

/-! ## Long windows: the lower bound -/

section

open Filter

attribute [local instance] Classical.propDecidable

theorem natWindow_eq_Ico_floor_succ {A B : ℝ} (hA : 0 ≤ A) :
    Estimates.natWindow A B = Finset.Ico (⌊A⌋₊ + 1) (⌊B⌋₊ + 1) := by
  classical
  ext n
  simp only [Estimates.natWindow, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨hn1, hnB⟩, hnA⟩
    have hnA' := (Nat.floor_lt hA).mpr hnA
    omega
  · rintro ⟨hnA, hnB⟩
    have hnA' : ⌊A⌋₊ < n := by omega
    exact ⟨⟨by omega, by omega⟩, (Nat.floor_lt hA).mp hnA'⟩

/-- Squarefree reciprocal lower bound on a real window `(A, B]` with
`log(B/A) ≥ 4`: rounding `A` and `B` to integers costs at most `1` in
`log(B/A)`. -/
theorem squarefree_coprime_real_window_lower
    (A B : ℝ) (M D b : ℕ) (hA : 1 ≤ A) (hAB : A < B)
    (hD : 0 < D) (hM : Squarefree M) (hDM : Nat.Coprime D M)
    (hb : Nat.Coprime b D) (hlong : 4 ≤ Real.log (B / A))
    (hlarge : 192 * (M.divisors.card : ℝ) ^ 2 * (D : ℝ) ≤ Real.sqrt A) :
    (1 / 16 : ℝ) * (((1 : ℝ) / (D : ℝ)) *
      ((Nat.totient M : ℝ) / (M : ℝ)) * Real.log (B / A)) ≤
      ∑ n ∈ (Estimates.natWindow A B).filter
        (fun n => Squarefree n ∧ Nat.Coprime n M ∧ Estimates.congMod n b D),
          (1 : ℝ) / (n : ℝ) := by
  classical
  let L := ⌊A⌋₊ + 1
  let U := ⌊B⌋₊ + 1
  let ρ : ℝ := (Nat.totient M : ℝ) / (M : ℝ)
  let τ : ℝ := M.divisors.card
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hB0 : 0 < B := hA0.trans hAB
  have hL : 0 < L := by dsimp [L]; omega
  have hLU : L ≤ U := Nat.add_le_add_right (Nat.floor_mono hAB.le) 1
  have hLR : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hUR : (0 : ℝ) < U := Nat.cast_pos.mpr (hL.trans_le hLU)
  have hLA : A < (L : ℝ) := by simpa [L] using Nat.lt_floor_add_one A
  have hUB : B < (U : ℝ) := by simpa [U] using Nat.lt_floor_add_one B
  have hLA2 : (L : ℝ) ≤ 2 * A := by
    have hh := Nat.floor_le hA0.le
    dsimp [L]
    push_cast
    linarith
  have hR : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr hLR
  have hD0 : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hτ : 0 ≤ τ := Nat.cast_nonneg _
  have hdensity : 1 ≤ τ * ρ := one_le_divisor_card_mul_totient_density hM.ne_zero
  have hlarge' : 192 * τ * (D : ℝ) ≤ ρ * Real.sqrt (L : ℝ) := by
    calc
      _ ≤ (192 * τ * (D : ℝ)) * (τ * ρ) :=
        le_mul_of_one_le_right (by positivity) hdensity
      _ = ρ * (192 * τ ^ 2 * (D : ℝ)) := by ring
      _ ≤ ρ * Real.sqrt A := mul_le_mul_of_nonneg_left hlarge hρ
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hLA.le) hρ
  have hlarge8 : 8 * τ * (D : ℝ) ≤ ρ * Real.sqrt (L : ℝ) := by
    have hnn : 0 ≤ τ * (D : ℝ) := by positivity
    nlinarith
  have hrec := squarefree_coprime_progression_reciprocal_lower L U D b M hL hLU hD
    hM hDM hb hlarge8
  have herror : 6 * τ / Real.sqrt (L : ℝ) ≤ ρ / (32 * (D : ℝ)) := by
    apply (div_le_div_iff₀ hR (by positivity : 0 < 32 * (D : ℝ))).mpr
    nlinarith only [hlarge']
  have hratio : B / A ≤ ((U : ℝ) / (L : ℝ)) * 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hA0 hLR]
    nlinarith [mul_le_mul_of_nonneg_left hLA2 hB0.le]
  have hlog : Real.log (B / A) - 1 ≤ Real.log ((U : ℝ) / (L : ℝ)) := by
    have hh := Real.log_le_log (div_pos hB0 hA0) hratio
    rw [Real.log_mul (ne_of_gt (div_pos hUR hLR)) (by norm_num : (2 : ℝ) ≠ 0)] at hh
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hh ⊢
      exact hh
    linarith
  have hshape : 0 ≤ ρ / (D : ℝ) := by positivity
  have hmain : (1 / 16 : ℝ) * (((1 : ℝ) / (D : ℝ)) * ρ * Real.log (B / A)) ≤
      ρ / (8 * (D : ℝ)) * Real.log ((U : ℝ) / (L : ℝ)) -
        6 * τ / Real.sqrt (L : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hlog
      (show 0 ≤ ρ / (8 * (D : ℝ)) by positivity)
    have hr := mul_le_mul_of_nonneg_left hlong hshape
    have he1 : ρ / (8 * (D : ℝ)) = (ρ / (D : ℝ)) / 8 := by ring
    have he2 : ρ / (32 * (D : ℝ)) = (ρ / (D : ℝ)) / 32 := by ring
    rw [he1] at hm ⊢
    rw [he2] at herror
    have he3 : (1 / 16 : ℝ) * (((1 : ℝ) / (D : ℝ)) * ρ * Real.log (B / A)) =
        (ρ / (D : ℝ)) * Real.log (B / A) / 16 := by ring
    rw [he3]
    nlinarith only [hm, hr, herror, hshape]
  have hset : (Estimates.natWindow A B).filter
      (fun n => Squarefree n ∧ Nat.Coprime n M ∧ Estimates.congMod n b D) =
      (Finset.Ico L U).filter (fun n => n ≡ b [MOD D] ∧
        Nat.Coprime n M ∧ Squarefree n) := by
    rw [natWindow_eq_Ico_floor_succ hA0.le]
    ext n
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Estimates.congMod, Nat.ModEq]
    tauto
  rw [hset]
  exact hmain.trans hrec

theorem eventually_UScale_le_rpow_squarefree {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in atTop, UScale X ≤ X ^ δ := by
  have hsmall : ∀ᶠ X : ℝ in atTop,
      ‖Real.log X‖ ≤ (1 : ℝ) * ‖X ^ (δ / 8)‖ :=
    (isLittleO_log_rpow_atTop (by positivity : 0 < δ / 8)).def (by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with X hsmall hX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  have hrpow : 0 ≤ X ^ (δ / 8) := Real.rpow_nonneg hXp.le _
  have hh : Real.log X ≤ X ^ (δ / 8) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_nonneg hrpow, one_mul] using hsmall
  unfold UScale
  calc
    _ ≤ (X ^ (δ / 8)) ^ (8 : ℕ) := pow_le_pow_left₀ hlog hh 8
    _ = X ^ δ := by
      rw [← Real.rpow_natCast (X ^ (δ / 8)) 8, ← Real.rpow_mul hXp.le]
      congr 1
      ring

/-- Eventually `192 τ(M)² D ≤ √A` for all squarefree `M ≤ X^{C₀}`, all `D ≤ U` and all
`A ≥ X^a`, since `τ(M) ≪_ε M^ε`. -/
theorem eventually_squarefree_divisor_error_absorbed
    (a C₀ : ℝ) (ha : 0 < a) :
    ∀ᶠ X : ℝ in atTop, ∀ M D : ℕ, Squarefree M →
      (M : ℝ) ≤ X ^ C₀ → (D : ℝ) ≤ UScale X →
      ∀ A : ℝ, X ^ a ≤ A →
        192 * (M.divisors.card : ℝ) ^ 2 * (D : ℝ) ≤ Real.sqrt A := by
  let C₁ : ℝ := max C₀ 1
  let ε : ℝ := a / (16 * C₁)
  have hC₁ : 0 < C₁ := zero_lt_one.trans_le (le_max_right _ _)
  have hε : 0 < ε := div_pos ha (by positivity)
  obtain ⟨C, hC, hdiv⟩ := exists_squarefree_divisor_card_le_rpow hε
  have hpower : ∀ᶠ X : ℝ in atTop, 192 * C ^ 2 ≤ X ^ (a / 4) :=
    (tendsto_rpow_atTop (by positivity : 0 < a / 4)).eventually
      (eventually_ge_atTop (192 * C ^ 2))
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_UScale_le_rpow_squarefree (by positivity : 0 < a / 8), hpower]
      with X hX hU hpower
  intro M D hM hMX hDX A hA
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hM0 : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM.ne_zero)
  have hMC₁ : (M : ℝ) ≤ X ^ C₁ := hMX.trans
    (Real.rpow_le_rpow_of_exponent_le hX (le_max_left _ _))
  have hτε : (M.divisors.card : ℝ) ≤ C * X ^ (a / 16) := by
    calc
      _ ≤ C * (M : ℝ) ^ ε := hdiv M hM
      _ ≤ C * (X ^ C₁) ^ ε := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hM0.le hMC₁ hε.le) hC.le
      _ = C * X ^ (a / 16) := by
        rw [← Real.rpow_mul hXp.le]
        congr 2
        dsimp [ε]
        field_simp
  have hDpow : (D : ℝ) ≤ X ^ (a / 8) := hDX.trans hU
  have hprod : (M.divisors.card : ℝ) ^ 2 * (D : ℝ) ≤ C ^ 2 * X ^ (a / 4) := by
    calc
      _ ≤ (C * X ^ (a / 16)) ^ 2 * X ^ (a / 8) :=
        mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hτε 2) hDpow
          (Nat.cast_nonneg D) (by positivity)
      _ = C ^ 2 * X ^ (a / 4) := by
        rw [mul_pow]
        have he : (X ^ (a / 16)) ^ (2 : ℕ) = X ^ (a / 8) := by
          rw [← Real.rpow_natCast (X ^ (a / 16)) 2, ← Real.rpow_mul hXp.le]
          congr 1
          ring
        rw [he, mul_assoc, ← Real.rpow_add hXp]
        congr 2
        ring
  have hroot : X ^ (a / 2) ≤ Real.sqrt A := by
    have hAp : 0 ≤ A := (Real.rpow_nonneg hXp.le a).trans hA
    have hsq : (X ^ (a / 2)) ^ (2 : ℕ) = X ^ a := by
      rw [← Real.rpow_natCast (X ^ (a / 2)) 2, ← Real.rpow_mul hXp.le]
      congr 1
      ring
    have hrootA := Real.sq_sqrt hAp
    nlinarith [Real.sqrt_nonneg A, Real.rpow_nonneg hXp.le (a / 2)]
  calc
    _ = 192 * ((M.divisors.card : ℝ) ^ 2 * (D : ℝ)) := by ring
    _ ≤ 192 * (C ^ 2 * X ^ (a / 4)) :=
      mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = (192 * C ^ 2) * X ^ (a / 4) := by ring
    _ ≤ X ^ (a / 4) * X ^ (a / 4) :=
      mul_le_mul_of_nonneg_right hpower (Real.rpow_nonneg hXp.le _)
    _ = X ^ (a / 2) := by rw [← Real.rpow_add hXp]; congr 1; ring
    _ ≤ _ := hroot

/-- Lemma 3.2, lower bound in a progression:
for `X^{a₀} ≤ A < B ≤ X^{b₀}` with `B/A ≥ X^{c₀}`, squarefree `M ≤ X^{C₀}`,
and `D ≤ U` with `(M, D) = (b, D) = 1`,
`∑_{A < n ≤ B, n squarefree, (n, M) = 1, n ≡ b (mod D)} 1/n
  ≫ (1/D) (φ(M)/M) log(B/A)`. -/
theorem squarefree_reciprocal_progression_lower
    (a₀ b₀ c₀ C₀ : ℝ) (ha₀ : 0 < a₀) (hc₀ : 0 < c₀) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ M D b : ℕ, 0 < D → Squarefree M → Squarefree D →
        Nat.Coprime M D → Nat.Coprime b D →
        (M : ℝ) ≤ X ^ C₀ → (D : ℝ) ≤ UScale X →
        ∀ A B : ℝ, X ^ a₀ ≤ A → A < B → 1 ≤ B → B ≤ X ^ b₀ →
          X ^ c₀ ≤ B / A →
          c * (((1 : ℝ) / (D : ℝ)) *
            ((Nat.totient M : ℝ) / (M : ℝ)) * Real.log (B / A)) ≤
            ∑ n ∈ (Estimates.natWindow A B).filter
              (fun n => Squarefree n ∧ Nat.Coprime n M ∧ Estimates.congMod n b D),
                (1 : ℝ) / (n : ℝ) := by
  classical
  have herr := eventually_squarefree_divisor_error_absorbed a₀ C₀ ha₀
  have hlong : ∀ᶠ X : ℝ in atTop, 4 / c₀ ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4 / c₀))
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (1 : ℝ)).and (herr.and hlong))
  refine ⟨1 / 16, X₀, by norm_num, ?_⟩
  intro X hX M D b hD hM _hDs hMD hb hMX hDX A B hA hAB _hB _hBpow hratio
  obtain ⟨hX1, herrX, hlogX⟩ := hX₀ X hX
  have hXp : 0 < X := zero_lt_one.trans_le hX1
  have hA1 : 1 ≤ A := (Real.one_le_rpow hX1 ha₀.le).trans hA
  have hA0 : 0 < A := zero_lt_one.trans_le hA1
  have hB0 : 0 < B := hA0.trans hAB
  have hlogratio : 4 ≤ Real.log (B / A) := by
    have hlog := Real.log_le_log (Real.rpow_pos_of_pos hXp c₀) hratio
    rw [Real.log_rpow hXp] at hlog
    have hh := (div_le_iff₀ hc₀).mp hlogX
    nlinarith
  exact squarefree_coprime_real_window_lower A B M D b hA1 hAB hD hM hMD.symm hb
    hlogratio (herrX M D hM hMX hDX A hA)

end

/-! ## Upper bounds -/

section

attribute [local instance] Classical.propDecidable

theorem squarefree_coprime_progression_reciprocal_upper
    (L U D b M : ℕ) (hL : 0 < L) (hLU : L ≤ U)
    (hD : 0 < D) (hM : Squarefree M) (hDM : Nat.Coprime D M) :
    (∑ n ∈ (Finset.Ico L U).filter (fun n => n ≡ b [MOD D] ∧
        Nat.Coprime n M ∧ Squarefree n), (1 : ℝ) / (n : ℝ)) ≤
      (((Nat.totient M : ℝ) / (M : ℝ)) / (D : ℝ)) *
        (1 / (L : ℝ) + Real.log ((U : ℝ) / (L : ℝ))) +
      2 * (M.divisors.card : ℝ) / (L : ℝ) := by
  classical
  have hcount : ∀ V, L ≤ V → V ≤ U →
      (((Finset.Ico L V).filter (fun n => n ≡ b [MOD D] ∧
        Nat.Coprime n M ∧ Squarefree n)).card : ℝ) ≤
      ((V : ℝ) - (L : ℝ)) *
        (((Nat.totient M : ℝ) / (M : ℝ)) / (D : ℝ)) +
      2 * (M.divisors.card : ℝ) := by
    intro V hLV hVU
    have hc := (abs_le.mp (abs_coprime_progression_card_sub_totient_density
      L V D b M hLV hD hM hDM)).2
    have hcard : ((Finset.Ico L V).filter (fun n => n ≡ b [MOD D] ∧
        Nat.Coprime n M ∧ Squarefree n)).card ≤
      (((Finset.Ico L V).filter (fun n => n ≡ b [MOD D])).filter
        (fun n => Nat.Coprime n M)).card := by
      apply Finset.card_le_card
      intro n hn
      obtain ⟨hnI, hnD, hnM, hnS⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hnI, hnD⟩, hnM⟩
    have hcardR : (((Finset.Ico L V).filter (fun n => n ≡ b [MOD D] ∧
        Nat.Coprime n M ∧ Squarefree n)).card : ℝ) ≤
      ((((Finset.Ico L V).filter (fun n => n ≡ b [MOD D])).filter
        (fun n => Nat.Coprime n M)).card : ℝ) := by exact_mod_cast hcard
    have he : (((V : ℝ) - (L : ℝ)) / (D : ℝ)) *
        ((Nat.totient M : ℝ) / (M : ℝ)) =
      ((V : ℝ) - (L : ℝ)) *
        (((Nat.totient M : ℝ) / (M : ℝ)) / (D : ℝ)) := by ring
    rw [he] at hc
    linarith
  have h := SieveEstimates.reciprocal_Ico_le_of_count_le
    (fun n => n ≡ b [MOD D] ∧ Nat.Coprime n M ∧ Squarefree n)
    L U hL hLU (((Nat.totient M : ℝ) / (M : ℝ)) / (D : ℝ))
    (2 * (M.divisors.card : ℝ)) (by positivity) hcount
  exact h.trans (add_le_add_left (mul_le_mul_of_nonneg_left
    (SieveEstimates.sum_Ico_reciprocal_le_log L U hL hLU) (by positivity)) _)

theorem squarefree_coprime_real_window_upper
    (A B : ℝ) (M D b : ℕ) (hA : 1 ≤ A) (hAB : A < B)
    (hD : 0 < D) (hM : Squarefree M) (hDM : Nat.Coprime D M)
    (hlong : 1 ≤ Real.log (B / A))
    (hlarge : 4 * (M.divisors.card : ℝ) ^ 2 * (D : ℝ) ≤ A) :
    (∑ n ∈ (Estimates.natWindow A B).filter
      (fun n => Squarefree n ∧ Nat.Coprime n M ∧ Estimates.congMod n b D),
        (1 : ℝ) / (n : ℝ)) ≤
      4 * (((1 : ℝ) / (D : ℝ)) *
        ((Nat.totient M : ℝ) / (M : ℝ)) * Real.log (B / A)) := by
  classical
  let L := ⌊A⌋₊ + 1
  let U := ⌊B⌋₊ + 1
  let ρ : ℝ := (Nat.totient M : ℝ) / (M : ℝ)
  let τ : ℝ := M.divisors.card
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hB0 : 0 < B := hA0.trans hAB
  have hL : 0 < L := by dsimp [L]; omega
  have hLU : L ≤ U := Nat.add_le_add_right (Nat.floor_mono hAB.le) 1
  have hLR : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hUR : (0 : ℝ) < U := Nat.cast_pos.mpr (hL.trans_le hLU)
  have hLA : A < (L : ℝ) := by simpa [L] using Nat.lt_floor_add_one A
  have hUB : (U : ℝ) ≤ 2 * B := by
    have hh := Nat.floor_le hB0.le
    dsimp [U]
    push_cast
    linarith
  have hD0 : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hτ : 0 ≤ τ := Nat.cast_nonneg _
  have hdensity : 1 ≤ τ * ρ := one_le_divisor_card_mul_totient_density hM.ne_zero
  have hlarge' : 4 * τ * (D : ℝ) ≤ ρ * (L : ℝ) := by
    calc
      _ ≤ (4 * τ * (D : ℝ)) * (τ * ρ) :=
        le_mul_of_one_le_right (by positivity) hdensity
      _ = ρ * (4 * τ ^ 2 * (D : ℝ)) := by ring
      _ ≤ ρ * A := mul_le_mul_of_nonneg_left hlarge hρ
      _ ≤ _ := mul_le_mul_of_nonneg_left hLA.le hρ
  have herror : 2 * τ / (L : ℝ) ≤ ρ / (2 * (D : ℝ)) := by
    apply (div_le_div_iff₀ hLR (by positivity : 0 < 2 * (D : ℝ))).mpr
    nlinarith only [hlarge']
  have hratio : (U : ℝ) / (L : ℝ) ≤ (B / A) * 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hLR hA0]
    nlinarith [mul_le_mul_of_nonneg_left hLA.le hB0.le]
  have hlog : Real.log ((U : ℝ) / (L : ℝ)) ≤ Real.log (B / A) + 1 := by
    have hh := Real.log_le_log (div_pos hUR hLR) hratio
    rw [Real.log_mul (ne_of_gt (div_pos hB0 hA0)) (by norm_num : (2 : ℝ) ≠ 0)] at hh
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hh ⊢
      exact hh
    linarith
  have hLone : (1 : ℝ) / (L : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hLR).mpr
    linarith
  have hrec := squarefree_coprime_progression_reciprocal_upper L U D b M
    hL hLU hD hM hDM
  have hset : (Estimates.natWindow A B).filter
      (fun n => Squarefree n ∧ Nat.Coprime n M ∧ Estimates.congMod n b D) =
      (Finset.Ico L U).filter (fun n => n ≡ b [MOD D] ∧
        Nat.Coprime n M ∧ Squarefree n) := by
    rw [natWindow_eq_Ico_floor_succ hA0.le]
    ext n
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Estimates.congMod, Nat.ModEq]
    tauto
  rw [hset]
  apply hrec.trans
  change ρ / (D : ℝ) * (1 / (L : ℝ) + Real.log ((U : ℝ) / (L : ℝ))) +
    2 * τ / (L : ℝ) ≤ _
  have hmain := mul_le_mul_of_nonneg_left (add_le_add hLone hlog)
    (show 0 ≤ ρ / (D : ℝ) by positivity)
  have hlong' := mul_le_mul_of_nonneg_left hlong
    (show 0 ≤ ρ / (D : ℝ) by positivity)
  have he1 : ρ / (2 * (D : ℝ)) = (ρ / (D : ℝ)) / 2 := by ring
  have he2 : 4 * (((1 : ℝ) / (D : ℝ)) * ρ * Real.log (B / A)) =
    4 * (ρ / (D : ℝ)) * Real.log (B / A) := by ring
  rw [he1] at herror
  change _ ≤ 4 * (((1 : ℝ) / (D : ℝ)) * ρ * Real.log (B / A))
  rw [he2]
  have hshape : 0 ≤ ρ / (D : ℝ) := by positivity
  nlinarith only [hmain, hlong', herror, hshape]

end

section

open Filter

attribute [local instance] Classical.propDecidable

theorem eventually_squarefree_upper_error_absorbed
    (a C₀ s : ℝ) (hs : s < a) :
    ∀ᶠ X : ℝ in atTop, ∀ M D : ℕ, Squarefree M →
      (M : ℝ) ≤ X ^ C₀ → (D : ℝ) ≤ X ^ s * UScale X →
        4 * (M.divisors.card : ℝ) ^ 2 * (D : ℝ) ≤ X ^ a := by
  let δ := a - s
  let C₁ : ℝ := max C₀ 1
  let ε : ℝ := δ / (8 * C₁)
  have hδ : 0 < δ := sub_pos.mpr hs
  have hC₁ : 0 < C₁ := zero_lt_one.trans_le (le_max_right _ _)
  have hε : 0 < ε := div_pos hδ (by positivity)
  obtain ⟨C, hC, hdiv⟩ := exists_squarefree_divisor_card_le_rpow hε
  have hpower : ∀ᶠ X : ℝ in atTop, 4 * C ^ 2 ≤ X ^ (δ / 2) :=
    (tendsto_rpow_atTop (by positivity : 0 < δ / 2)).eventually
      (eventually_ge_atTop (4 * C ^ 2))
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_UScale_le_rpow_squarefree (by positivity : 0 < δ / 4), hpower]
      with X hX hU hpower
  intro M D hM hMX hDX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hM0 : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM.ne_zero)
  have hMC₁ : (M : ℝ) ≤ X ^ C₁ := hMX.trans
    (Real.rpow_le_rpow_of_exponent_le hX (le_max_left _ _))
  have hτε : (M.divisors.card : ℝ) ≤ C * X ^ (δ / 8) := by
    calc
      _ ≤ C * (M : ℝ) ^ ε := hdiv M hM
      _ ≤ C * (X ^ C₁) ^ ε := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hM0.le hMC₁ hε.le) hC.le
      _ = C * X ^ (δ / 8) := by
        rw [← Real.rpow_mul hXp.le]
        congr 2
        dsimp [ε]
        field_simp
  have hDpow : (D : ℝ) ≤ X ^ (s + δ / 4) := by
    calc
      _ ≤ X ^ s * UScale X := hDX
      _ ≤ X ^ s * X ^ (δ / 4) :=
        mul_le_mul_of_nonneg_left hU (Real.rpow_nonneg hXp.le _)
      _ = _ := (Real.rpow_add hXp _ _).symm
  have hprod : (M.divisors.card : ℝ) ^ 2 * (D : ℝ) ≤
      C ^ 2 * X ^ (s + δ / 2) := by
    calc
      _ ≤ (C * X ^ (δ / 8)) ^ 2 * X ^ (s + δ / 4) :=
        mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hτε 2) hDpow
          (Nat.cast_nonneg D) (by positivity)
      _ = C ^ 2 * X ^ (s + δ / 2) := by
        rw [mul_pow]
        have he : (X ^ (δ / 8)) ^ (2 : ℕ) = X ^ (δ / 4) := by
          rw [← Real.rpow_natCast (X ^ (δ / 8)) 2, ← Real.rpow_mul hXp.le]
          congr 1
          ring
        rw [he, mul_assoc, ← Real.rpow_add hXp]
        congr 2
        ring
  calc
    _ = 4 * ((M.divisors.card : ℝ) ^ 2 * (D : ℝ)) := by ring
    _ ≤ 4 * (C ^ 2 * X ^ (s + δ / 2)) :=
      mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = (4 * C ^ 2) * X ^ (s + δ / 2) := by ring
    _ ≤ X ^ (δ / 2) * X ^ (s + δ / 2) :=
      mul_le_mul_of_nonneg_right hpower (Real.rpow_nonneg hXp.le _)
    _ = X ^ a := by
      rw [← Real.rpow_add hXp]
      congr 1
      dsimp [δ]
      ring

theorem squarefree_reciprocal_progression_upper_wide
    (a₀ b₀ c₀ C₀ s : ℝ) (ha₀ : 0 < a₀) (hc₀ : 0 < c₀) (hs : s < a₀) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ M D b : ℕ, 0 < D → Squarefree M → Squarefree D →
        Nat.Coprime M D → Nat.Coprime b D →
        (M : ℝ) ≤ X ^ C₀ → (D : ℝ) ≤ X ^ s * UScale X →
        ∀ A B : ℝ, X ^ a₀ ≤ A → A < B → 1 ≤ B → B ≤ X ^ b₀ →
          X ^ c₀ ≤ B / A →
          (∑ n ∈ (Estimates.natWindow A B).filter
            (fun n => Squarefree n ∧ Nat.Coprime n M ∧ Estimates.congMod n b D),
              (1 : ℝ) / (n : ℝ)) ≤
          C * (((1 : ℝ) / (D : ℝ)) *
            ((Nat.totient M : ℝ) / (M : ℝ)) * Real.log (B / A)) := by
  classical
  have herr := eventually_squarefree_upper_error_absorbed a₀ C₀ s hs
  have hlong : ∀ᶠ X : ℝ in atTop, 1 / c₀ ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 / c₀))
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (1 : ℝ)).and (herr.and hlong))
  refine ⟨4, X₀, by norm_num, ?_⟩
  intro X hX M D b hD hM _hDs hMD _hb hMX hDX A B hA hAB _hB _hBpow hratio
  obtain ⟨hX1, herrX, hlogX⟩ := hX₀ X hX
  have hXp : 0 < X := zero_lt_one.trans_le hX1
  have hA1 : 1 ≤ A := (Real.one_le_rpow hX1 ha₀.le).trans hA
  have hlogratio : 1 ≤ Real.log (B / A) := by
    have hlog := Real.log_le_log (Real.rpow_pos_of_pos hXp c₀) hratio
    rw [Real.log_rpow hXp] at hlog
    have hh := (div_le_iff₀ hc₀).mp hlogX
    nlinarith
  exact squarefree_coprime_real_window_upper A B M D b hA1 hAB hD hM hMD.symm
    hlogratio ((herrX M D hM hMX hDX).trans hA)

/-- Lemma 3.2, upper bound in a progression. -/
theorem squarefree_reciprocal_progression_upper
    (a₀ b₀ c₀ C₀ : ℝ) (ha₀ : 0 < a₀) (hc₀ : 0 < c₀) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ M D b : ℕ, 0 < D → Squarefree M → Squarefree D →
        Nat.Coprime M D → Nat.Coprime b D →
        (M : ℝ) ≤ X ^ C₀ → (D : ℝ) ≤ UScale X →
        ∀ A B : ℝ, X ^ a₀ ≤ A → A < B → 1 ≤ B → B ≤ X ^ b₀ →
          X ^ c₀ ≤ B / A →
          (∑ n ∈ (Estimates.natWindow A B).filter
            (fun n => Squarefree n ∧ Nat.Coprime n M ∧ Estimates.congMod n b D),
              (1 : ℝ) / (n : ℝ)) ≤
          C * (((1 : ℝ) / (D : ℝ)) *
            ((Nat.totient M : ℝ) / (M : ℝ)) * Real.log (B / A)) := by
  simpa only [Real.rpow_zero, one_mul] using
    squarefree_reciprocal_progression_upper_wide
      a₀ b₀ c₀ C₀ 0 ha₀ hc₀ ha₀

end

end ErdosStraus.ProgressionEstimates

/-! ## The sums of Lemma 3.2 -/

namespace ErdosStraus.Estimates
open Filter Asymptotics
open scoped BigOperators Pointwise

/-- The number of divisors `τ(n)`. -/
def tau (n : ℕ) : ℕ := n.divisors.card

/-- The Basel constant `ζ(2) = π²/6`. -/
noncomputable def zeta2 : ℝ := Real.pi ^ 2 / 6

theorem zeta2_pos : 0 < zeta2 := by
  unfold zeta2
  positivity

/-- `sqfRecip X M D b U₀ U₁ = ∑_{U₀<n≤U₁, n squarefree, (n,M)=1, n≡b (mod D)} 1/n`, the sum
of Lemma 3.2. The argument `X` is not used. -/
noncomputable def sqfRecip (_X : ℝ) (M D b : ℕ) (U₀ U₁ : ℝ) : ℝ := by
  classical
  exact
    ∑ n ∈ (natWindow U₀ U₁).filter
        (fun n => Squarefree n ∧ Nat.Coprime n M ∧ congMod n b D),
      (1 : ℝ) / (n : ℝ)

/-- `∑_{U₀<n≤U₁, n≡b (mod D)} 1/n`, the left side of (7). -/
noncomputable def progressionRecip (D b : ℕ) (U₀ U₁ : ℝ) : ℝ := by
  classical
  exact
    ∑ n ∈ (natWindow U₀ U₁).filter (fun n => congMod n b D),
      (1 : ℝ) / (n : ℝ)

/-- The lower bound of Lemma 3.2 in a progression:
`sqfRecip X M D b U₀ U₁ ≫ (1/D)(φ(M)/M) log(U₁/U₀)` for squarefree `M ≤ X^{C₀}` and
`D ≤ U`, and for `X^{a₀} ≤ U₀ < U₁ ≤ X^{b₀}` with `U₁/U₀ ≥ X^{c₀}`. -/
def OrdinarySquarefreeProgressionCoprimeDensityLowerLong
    (a₀ b₀ c₀ C₀ : ℝ) : Prop :=
  ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ M D b : ℕ, 0 < D → Squarefree M → Squarefree D →
      Nat.Coprime M D → Nat.Coprime b D →
      (M : ℝ) ≤ X ^ C₀ → (D : ℝ) ≤ ErdosStraus.UScale X →
      ∀ U₀ U₁ : ℝ, X ^ a₀ ≤ U₀ → U₀ < U₁ → 1 ≤ U₁ → U₁ ≤ X ^ b₀ →
        X ^ c₀ ≤ U₁ / U₀ →
        c * (((1 : ℝ) / (D : ℝ)) *
          ((Nat.totient M : ℝ) / (M : ℝ)) * Real.log (U₁ / U₀)) ≤
          sqfRecip X M D b U₀ U₁

/-- The upper bound of Lemma 3.2 in a progression, in the same ranges. -/
def OrdinarySquarefreeProgressionCoprimeDensityUpperLong
    (a₀ b₀ c₀ C₀ : ℝ) : Prop :=
  ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ M D b : ℕ, 0 < D → Squarefree M → Squarefree D →
      Nat.Coprime M D → Nat.Coprime b D →
      (M : ℝ) ≤ X ^ C₀ → (D : ℝ) ≤ ErdosStraus.UScale X →
      ∀ U₀ U₁ : ℝ, X ^ a₀ ≤ U₀ → U₀ < U₁ → 1 ≤ U₁ → U₁ ≤ X ^ b₀ →
        X ^ c₀ ≤ U₁ / U₀ →
        sqfRecip X M D b U₀ U₁ ≤
          C * (((1 : ℝ) / (D : ℝ)) *
            ((Nat.totient M : ℝ) / (M : ℝ)) * Real.log (U₁ / U₀))

/-- Lemma 3.2, lower bound in a progression. -/
theorem ordinary_squarefree_progression_coprime_density_lower_long
    (a₀ b₀ c₀ C₀ : ℝ) (ha₀ : 0 < a₀) (hc₀ : 0 < c₀) :
    OrdinarySquarefreeProgressionCoprimeDensityLowerLong a₀ b₀ c₀ C₀ := by
  simpa only [OrdinarySquarefreeProgressionCoprimeDensityLowerLong, sqfRecip] using
    ErdosStraus.ProgressionEstimates.squarefree_reciprocal_progression_lower
      a₀ b₀ c₀ C₀ ha₀ hc₀

/-- Lemma 3.2, upper bound in a progression. -/
theorem ordinary_squarefree_progression_coprime_density_upper_long
    (a₀ b₀ c₀ C₀ : ℝ) (ha₀ : 0 < a₀) (hc₀ : 0 < c₀) :
    OrdinarySquarefreeProgressionCoprimeDensityUpperLong a₀ b₀ c₀ C₀ := by
  simpa only [OrdinarySquarefreeProgressionCoprimeDensityUpperLong, sqfRecip] using
    ErdosStraus.ProgressionEstimates.squarefree_reciprocal_progression_upper
      a₀ b₀ c₀ C₀ ha₀ hc₀

/-! ## Reciprocal sums over one residue class -/

theorem inv_add_le_inv_mul_log_add_div {y d : ℝ} (hy : 0 < y) (hd : 0 < d) :
    1 / (y + d) ≤ (1 / d) * Real.log ((y + d) / y) := by
  have hratio_pos : 0 < (y + d) / y := div_pos (add_pos hy hd) hy
  have hlog := Real.one_sub_inv_le_log_of_pos hratio_pos
  have hden : y + d ≠ 0 := ne_of_gt (add_pos hy hd)
  have hyne : y ≠ 0 := ne_of_gt hy
  have hdne : d ≠ 0 := ne_of_gt hd
  have hleft : 1 - ((y + d) / y)⁻¹ = d / (y + d) := by
    field_simp [hden, hyne]
    ring
  rw [hleft] at hlog
  have hmul :
      (1 / d) * (d / (y + d)) ≤ (1 / d) * Real.log ((y + d) / y) := by
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  convert hmul using 1
  field_simp [hdne, hden]

theorem congMod_add_le_of_lt {D n m b : ℕ}
    (hn : congMod n b D) (hm : congMod m b D) (hlt : n < m) :
    n + D ≤ m := by
  have hnm : n ≡ m [MOD D] := by
    exact Nat.ModEq.trans hn (Nat.ModEq.symm hm)
  exact Nat.ModEq.add_le_of_lt hnm hlt

/-- If `s` lies in `(U₀, U₁]` and in one residue class modulo `D`, then
`∑_{n ∈ s} 1/n ≤ 1/U₀ + D⁻¹ log(U₁/U₀)`: each term after the first is at most
`D⁻¹ log(n/(n - D))`. -/
theorem finset_recip_cong_le_log (D b : ℕ) (hD : 0 < D)
    (U₀ : ℝ) (hU₀ : 0 < U₀) (s : Finset ℕ) :
    ∀ U₁ : ℝ, U₀ < U₁ →
      (∀ n ∈ s, U₀ < (n : ℝ)) →
      (∀ n ∈ s, (n : ℝ) ≤ U₁) →
      (∀ n ∈ s, congMod n b D) →
      ∑ n ∈ s, (1 : ℝ) / (n : ℝ)
        ≤ 1 / U₀ + (1 / (D : ℝ)) * Real.log (U₁ / U₀) := by
  classical
  refine Finset.induction_on_max s ?h0 ?step
  · intro U₁ hU₁ _ _ _
    simp only [Finset.sum_empty]
    apply add_nonneg
    · exact div_nonneg zero_le_one hU₀.le
    · exact mul_nonneg (by positivity) (Real.log_nonneg ((one_le_div hU₀).mpr hU₁.le))
  · intro a t hall_lt ih U₁ hU₁ hlo hhi hcong
    have hat : a ∉ t := by
      intro ha
      exact (lt_irrefl a) (hall_lt a ha)
    have haU₀ : U₀ < (a : ℝ) := hlo a (Finset.mem_insert_self a t)
    have haU₁ : (a : ℝ) ≤ U₁ := hhi a (Finset.mem_insert_self a t)
    have hca : congMod a b D := hcong a (Finset.mem_insert_self a t)
    rw [Finset.sum_insert hat]
    by_cases ht_empty : t = ∅
    · subst ht_empty
      simp only [Finset.sum_empty, add_zero]
      have hfirst : (1 : ℝ) / (a : ℝ) ≤ 1 / U₀ := by
        simpa [one_div] using inv_anti₀ hU₀ haU₀.le
      exact le_trans hfirst
        (le_add_of_nonneg_right
          (mul_nonneg (by positivity) (Real.log_nonneg ((one_le_div hU₀).mpr hU₁.le))))
    · have ht_ne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr ht_empty
      rcases ht_ne with ⟨x, hx⟩
      have hxU₀ : U₀ < (x : ℝ) := hlo x (Finset.mem_insert_of_mem hx)
      have hcx : congMod x b D := hcong x (Finset.mem_insert_of_mem hx)
      have hx_add_le : x + D ≤ a := congMod_add_le_of_lt hcx hca (hall_lt x hx)
      have hD_le_a : D ≤ a := by omega
      have hx_le_a_sub : x ≤ a - D := by omega
      have hU₀_a_sub : U₀ < ((a - D : ℕ) : ℝ) := by
        exact lt_of_lt_of_le hxU₀ (by exact_mod_cast hx_le_a_sub)
      have ht_hi : ∀ n ∈ t, (n : ℝ) ≤ ((a - D : ℕ) : ℝ) := by
        intro n hn
        have hcn : congMod n b D := hcong n (Finset.mem_insert_of_mem hn)
        have hn_add_le : n + D ≤ a := congMod_add_le_of_lt hcn hca (hall_lt n hn)
        have hn_le : n ≤ a - D := by omega
        exact_mod_cast hn_le
      have ht_lo : ∀ n ∈ t, U₀ < (n : ℝ) := by
        intro n hn
        exact hlo n (Finset.mem_insert_of_mem hn)
      have ht_cong : ∀ n ∈ t, congMod n b D := by
        intro n hn
        exact hcong n (Finset.mem_insert_of_mem hn)
      have ih' := ih ((a - D : ℕ) : ℝ) hU₀_a_sub ht_lo ht_hi ht_cong
      have hDreal : 0 < (D : ℝ) := by exact_mod_cast hD
      have ha_sub_pos_nat : 0 < a - D := by
        have hxposR : (0 : ℝ) < x := lt_trans hU₀ hxU₀
        have hxpos : 0 < x := by exact_mod_cast hxposR
        omega
      have ha_sub_pos : 0 < ((a - D : ℕ) : ℝ) := by exact_mod_cast ha_sub_pos_nat
      have ha_eq : ((a : ℝ)) = ((a - D : ℕ) : ℝ) + (D : ℝ) := by
        rw [← Nat.cast_add, Nat.sub_add_cancel hD_le_a]
      have hlast :
          (1 : ℝ) / (a : ℝ)
            ≤ (1 / (D : ℝ)) * Real.log ((a : ℝ) / ((a - D : ℕ) : ℝ)) := by
        rw [ha_eq]
        exact inv_add_le_inv_mul_log_add_div ha_sub_pos hDreal
      have hmularg :
          (((a - D : ℕ) : ℝ) / U₀) * ((a : ℝ) / ((a - D : ℕ) : ℝ))
            = (a : ℝ) / U₀ := by
        calc
          (((a - D : ℕ) : ℝ) / U₀) * ((a : ℝ) / ((a - D : ℕ) : ℝ))
              = ((a : ℝ) / U₀)
                  * (((a - D : ℕ) : ℝ) / ((a - D : ℕ) : ℝ)) := by ring
          _ = (a : ℝ) / U₀ := by simp [ne_of_gt ha_sub_pos]
      have hsum_bound :
          (1 : ℝ) / (a : ℝ) + ∑ n ∈ t, (1 : ℝ) / (n : ℝ)
            ≤ 1 / U₀ + (1 / (D : ℝ)) * Real.log ((a : ℝ) / U₀) := by
        calc
          (1 : ℝ) / (a : ℝ) + ∑ n ∈ t, (1 : ℝ) / (n : ℝ)
              ≤ (1 / (D : ℝ)) * Real.log ((a : ℝ) / ((a - D : ℕ) : ℝ))
                  + (1 / U₀
                    + (1 / (D : ℝ)) * Real.log (((a - D : ℕ) : ℝ) / U₀)) := by
                exact add_le_add hlast ih'
          _ = 1 / U₀ + (1 / (D : ℝ))
                  * (Real.log (((a - D : ℕ) : ℝ) / U₀)
                    + Real.log ((a : ℝ) / ((a - D : ℕ) : ℝ))) := by
                ring
          _ = 1 / U₀ + (1 / (D : ℝ)) * Real.log ((a : ℝ) / U₀) := by
                congr 1
                rw [← Real.log_mul]
                · rw [hmularg]
                · exact div_ne_zero (ne_of_gt ha_sub_pos) (ne_of_gt hU₀)
                · have hapos : 0 < (a : ℝ) := lt_trans hU₀ haU₀
                  exact div_ne_zero (ne_of_gt hapos) (ne_of_gt ha_sub_pos)
      have hlog_mono : Real.log ((a : ℝ) / U₀) ≤ Real.log (U₁ / U₀) := by
        apply Real.log_le_log
        · exact div_pos (lt_trans hU₀ haU₀) hU₀
        · exact div_le_div_of_nonneg_right haU₁ hU₀.le
      exact le_trans hsum_bound
        (add_le_add_right (mul_le_mul_of_nonneg_left hlog_mono (by positivity)) _)

/-- The bound (7): `progressionRecip D b U₀ U₁ ≤ 1/U₀ + D⁻¹ log(U₁/U₀)`. -/
theorem progressionRecip_le_log_plus_inv (D b : ℕ) (hD : 0 < D)
    {U₀ U₁ : ℝ} (hU₀ : 0 < U₀) (hU₁ : U₀ < U₁) :
    progressionRecip D b U₀ U₁
      ≤ 1 / U₀ + (1 / (D : ℝ)) * Real.log (U₁ / U₀) := by
  classical
  unfold progressionRecip natWindow
  apply finset_recip_cong_le_log D b hD U₀ hU₀
  · exact hU₁
  · intro n hn
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
  · intro n hn
    have hnIcc : n ∈ Finset.Icc (1 : ℕ) ⌊U₁⌋₊ :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
    have hn_floor : n ≤ ⌊U₁⌋₊ := (Finset.mem_Icc.mp hnIcc).2
    exact (Nat.le_floor_iff (le_trans hU₀.le hU₁.le)).mp hn_floor
  · intro n hn
    exact (Finset.mem_filter.mp hn).2

theorem finset_sum_biUnion_le_sum
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : Finset α) (T : α → Finset β) (f : β → ℝ)
    (hf : ∀ r ∈ R, ∀ x ∈ T r, 0 ≤ f x) :
    ∑ x ∈ R.biUnion T, f x ≤ ∑ r ∈ R, ∑ x ∈ T r, f x := by
  classical
  revert hf
  refine Finset.induction_on R ?empty ?insert
  · intro _hf
    simp
  · intro a S ha ih hf
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hinter_nonneg :
        0 ≤ ∑ x ∈ T a ∩ S.biUnion T, f x := by
      apply Finset.sum_nonneg
      intro x hx
      exact hf a (Finset.mem_insert_self a S) x (Finset.mem_inter.mp hx).1
    have hunion_eq :
        ∑ x ∈ T a ∪ S.biUnion T, f x
          + ∑ x ∈ T a ∩ S.biUnion T, f x =
        ∑ x ∈ T a, f x + ∑ x ∈ S.biUnion T, f x := by
      exact Finset.sum_union_inter
    have hunion_le :
        ∑ x ∈ T a ∪ S.biUnion T, f x
          ≤ ∑ x ∈ T a, f x + ∑ x ∈ S.biUnion T, f x := by
      linarith
    have ih' :
        ∑ x ∈ S.biUnion T, f x ≤ ∑ r ∈ S, ∑ x ∈ T r, f x :=
      ih (by
        intro r hr x hx
        exact hf r (Finset.mem_insert_of_mem hr) x hx)
    exact le_trans hunion_le (add_le_add_right ih' _)

/-! ## Reduced residues modulo `MD` -/

/-- The residues `r < MD` with `(r, M) = 1` and `r ≡ b (mod D)`. -/
noncomputable def crtCoprimeProgressionResidues (M D b : ℕ) : Finset ℕ := by
  classical
  exact
    (Finset.range (M * D)).filter
      (fun r => Nat.Coprime r M ∧ congMod r b D)

theorem crtCoprimeProgressionResidues_cover
    {M D b n : ℕ} (hM : 0 < M) (hD : 0 < D)
    (hnM : Nat.Coprime n M) (hnD : congMod n b D) :
    ∃ r ∈ crtCoprimeProgressionResidues M D b,
      congMod n r (M * D) := by
  classical
  let Q : ℕ := M * D
  let r : ℕ := n % Q
  have hQ : 0 < Q := Nat.mul_pos hM hD
  have hr_range : r ∈ Finset.range Q := Finset.mem_range.mpr (Nat.mod_lt n hQ)
  have hrM : Nat.Coprime r M := by
    rw [Nat.coprime_iff_gcd_eq_one]
    calc
      r.gcd M = M.gcd r := Nat.gcd_comm r M
      _ = (r % M).gcd M := Nat.gcd_rec M r
      _ = (n % M).gcd M := by
            dsimp [r, Q]
            rw [Nat.mod_mul_right_mod]
      _ = M.gcd n := by rw [← Nat.gcd_rec M n]
      _ = n.gcd M := Nat.gcd_comm M n
      _ = 1 := hnM.gcd_eq_one
  have hrD : congMod r b D := by
    unfold congMod at hnD ⊢
    calc
      r % D = n % D := by
        dsimp [r, Q]
        rw [Nat.mod_mod_of_dvd n (Nat.dvd_mul_left D M)]
      _ = b % D := hnD
  have hr_mem : r ∈ crtCoprimeProgressionResidues M D b := by
    unfold crtCoprimeProgressionResidues
    have hr_range_MD : r ∈ Finset.range (M * D) := by
      simpa [Q] using hr_range
    exact Finset.mem_filter.mpr ⟨hr_range_MD, ⟨hrM, hrD⟩⟩
  refine ⟨r, hr_mem, ?_⟩
  unfold congMod
  dsimp [r, Q]
  rw [Nat.mod_mod]

theorem coprime_of_congMod_left
    {a r M : ℕ} (h : congMod r a M) (ha : Nat.Coprime a M) :
    Nat.Coprime r M := by
  rw [Nat.coprime_iff_gcd_eq_one]
  calc
    r.gcd M = M.gcd r := Nat.gcd_comm r M
    _ = (r % M).gcd M := Nat.gcd_rec M r
    _ = (a % M).gcd M := by rw [h]
    _ = M.gcd a := by rw [← Nat.gcd_rec M a]
    _ = a.gcd M := Nat.gcd_comm M a
    _ = 1 := ha.gcd_eq_one

/-- For `(M, D) = 1` there are exactly `φ(M)` such residues, by the Chinese remainder
theorem. -/
theorem crtCoprimeProgressionResidues_card_eq_totient
    {M D b : ℕ} (hM : 0 < M) (hD : 0 < D)
    (hMD : Nat.Coprime M D) :
    (crtCoprimeProgressionResidues M D b).card = Nat.totient M := by
  classical
  let S : Finset ℕ := (Finset.range M).filter (fun a => Nat.Coprime a M)
  have hS_card : S.card = Nat.totient M := by
    rw [Nat.totient_eq_card_coprime]
    apply congrArg Finset.card
    ext a
    simp [S, Nat.coprime_comm]
  have hcard :
      S.card = (crtCoprimeProgressionResidues M D b).card := by
    refine Finset.card_bij
      (fun a _ha => (Nat.chineseRemainder hMD a b : ℕ))
      ?mem ?inj ?surj
    · intro a ha
      have ha_lt : a < M := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
      have ha_coprime : Nat.Coprime a M := (Finset.mem_filter.mp ha).2
      have hk_lt :
          (Nat.chineseRemainder hMD a b : ℕ) < M * D :=
        Nat.chineseRemainder_lt_mul hMD a b hM.ne' hD.ne'
      have hkM : Nat.Coprime (Nat.chineseRemainder hMD a b : ℕ) M :=
        coprime_of_congMod_left
          (by
            unfold congMod
            exact (Nat.chineseRemainder hMD a b).prop.1)
          ha_coprime
      have hkD : congMod (Nat.chineseRemainder hMD a b : ℕ) b D := by
        unfold congMod
        exact (Nat.chineseRemainder hMD a b).prop.2
      unfold crtCoprimeProgressionResidues
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hk_lt, ⟨hkM, hkD⟩⟩
    · intro a₁ ha₁ a₂ ha₂ heq
      have ha₁_lt : a₁ < M := Finset.mem_range.mp (Finset.mem_filter.mp ha₁).1
      have ha₂_lt : a₂ < M := Finset.mem_range.mp (Finset.mem_filter.mp ha₂).1
      have h₁ : (Nat.chineseRemainder hMD a₁ b : ℕ) % M = a₁ % M :=
        (Nat.chineseRemainder hMD a₁ b).prop.1
      have h₂ : (Nat.chineseRemainder hMD a₂ b : ℕ) % M = a₂ % M :=
        (Nat.chineseRemainder hMD a₂ b).prop.1
      change (Nat.chineseRemainder hMD a₁ b : ℕ) =
        (Nat.chineseRemainder hMD a₂ b : ℕ) at heq
      rw [heq] at h₁
      have hmod : a₁ % M = a₂ % M := h₁.symm.trans h₂
      rwa [Nat.mod_eq_of_lt ha₁_lt, Nat.mod_eq_of_lt ha₂_lt] at hmod
    · intro r hr
      have hr' :
          r ∈ (Finset.range (M * D)).filter
            (fun r => Nat.Coprime r M ∧ congMod r b D) := by
        simpa [crtCoprimeProgressionResidues] using hr
      rcases Finset.mem_filter.mp hr' with
        ⟨hr_range, ⟨hr_coprime, hrD⟩⟩
      let a : ℕ := r % M
      have ha_lt : a < M := Nat.mod_lt r hM
      have haM : congMod a r M := by
        unfold congMod
        dsimp [a]
        rw [Nat.mod_mod]
      have ha_coprime : Nat.Coprime a M :=
        coprime_of_congMod_left haM hr_coprime
      have ha_mem : a ∈ S := by
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr ha_lt, ha_coprime⟩
      refine ⟨a, ha_mem, ?_⟩
      have hrM : r ≡ a [MOD M] := by
        unfold Nat.ModEq
        dsimp [a]
        rw [Nat.mod_mod]
      have hrD' : r ≡ b [MOD D] := by
        unfold Nat.ModEq
        exact hrD
      have huniq :
          r ≡ (Nat.chineseRemainder hMD a b : ℕ) [MOD M * D] :=
        Nat.chineseRemainder_modEq_unique hMD hrM hrD'
      have hr_lt : r < M * D := Finset.mem_range.mp hr_range
      have hk_lt :
          (Nat.chineseRemainder hMD a b : ℕ) < M * D :=
        Nat.chineseRemainder_lt_mul hMD a b hM.ne' hD.ne'
      unfold Nat.ModEq at huniq
      rw [Nat.mod_eq_of_lt hr_lt, Nat.mod_eq_of_lt hk_lt] at huniq
      exact huniq.symm
  exact hcard.symm.trans hS_card

/-! ## Sums over squarefree `s ≤ X^η` -/

/-- `∑_{s ≤ S, s squarefree} φ(s)/s²` with `S = X^η`, the first sum of Lemma 3.3 for
`M = 1`. -/
noncomputable def sAvgPhi (P : ErdosStraus.Params) (X : ℝ) : ℝ :=
  ∑ s ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.SScale P X⌋₊).filter (fun s => Squarefree s),
    (Nat.totient s : ℝ) / (s : ℝ) ^ 2

theorem sAvgPhi_nonneg (P : ErdosStraus.Params) (X : ℝ) : 0 ≤ sAvgPhi P X := by
  classical
  unfold sAvgPhi
  apply Finset.sum_nonneg
  intro s _hs
  exact div_nonneg (Nat.cast_nonneg _) (sq_nonneg (s : ℝ))

/-- `∑_{s ≤ S, s squarefree} 1/s` with `S = X^η`, the second sum of Lemma 3.3 for
`M = 1`. -/
noncomputable def sAvgRecip (P : ErdosStraus.Params) (X : ℝ) : ℝ :=
  ∑ s ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.SScale P X⌋₊).filter (fun s => Squarefree s),
    (1 : ℝ) / (s : ℝ)

theorem sAvgRecip_nonneg (P : ErdosStraus.Params) (X : ℝ) : 0 ≤ sAvgRecip P X := by
  classical
  unfold sAvgRecip
  apply Finset.sum_nonneg
  intro s _hs
  exact div_nonneg zero_le_one (Nat.cast_nonneg s)

theorem sAvgPhi_le_sAvgRecip (P : ErdosStraus.Params) (X : ℝ) :
    sAvgPhi P X ≤ sAvgRecip P X := by
  classical
  unfold sAvgPhi sAvgRecip
  apply Finset.sum_le_sum
  intro s hs
  have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊ErdosStraus.SScale P X⌋₊ :=
    (Finset.mem_filter.mp hs).1
  have hspos_nat : 0 < s :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hsIcc).1
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hspos_nat
  have htot_le_nat : Nat.totient s ≤ s := Nat.totient_le s
  have htot_le : (Nat.totient s : ℝ) ≤ (s : ℝ) := by exact_mod_cast htot_le_nat
  calc
    (Nat.totient s : ℝ) / (s : ℝ) ^ 2
        ≤ (s : ℝ) / (s : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right htot_le (sq_nonneg (s : ℝ))
    _ = (1 : ℝ) / (s : ℝ) := by
          field_simp [ne_of_gt hspos]

theorem sAvgRecip_le_harmonic_floor (P : ErdosStraus.Params) (X : ℝ) :
    sAvgRecip P X ≤ (harmonic ⌊ErdosStraus.SScale P X⌋₊ : ℝ) := by
  classical
  unfold sAvgRecip
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  simp_rw [one_div]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    exact (Finset.mem_filter.mp hs).1
  · intro s _hsBig _hsSmall
    exact inv_nonneg.mpr (Nat.cast_nonneg s)

/-- `sAvgRecip P X ≤ H_⌊S⌋ ≤ 1 + log S ≤ 2 log S` once `log S ≥ 2`. -/
theorem sAvgRecip_upper_log (P : ErdosStraus.Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      sAvgRecip P X ≤ C * Real.log (ErdosStraus.SScale P X) := by
  refine ⟨2, Real.exp (2 / P.η), by norm_num, ?_⟩
  intro X hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hlogX_ge : 2 / P.η ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hX
  have hlogS_eq : Real.log (ErdosStraus.SScale P X) = P.η * Real.log X := by
    unfold ErdosStraus.SScale
    rw [Real.log_rpow hXpos]
  have hlogS_ge_two : 2 ≤ Real.log (ErdosStraus.SScale P X) := by
    rw [hlogS_eq]
    calc
      (2 : ℝ) = P.η * (2 / P.η) := by field_simp [ne_of_gt P.η_pos]
      _ ≤ P.η * Real.log X := mul_le_mul_of_nonneg_left hlogX_ge P.η_pos.le
  have hSpos : 0 < ErdosStraus.SScale P X := Real.rpow_pos_of_pos hXpos P.η
  have hS_ge_one : 1 ≤ ErdosStraus.SScale P X := by
    apply (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 1) hSpos).mp
    simpa using le_trans (by norm_num : (0 : ℝ) ≤ 2) hlogS_ge_two
  have hharm : (harmonic ⌊ErdosStraus.SScale P X⌋₊ : ℝ)
      ≤ 1 + Real.log (ErdosStraus.SScale P X) :=
    harmonic_floor_le_one_add_log (ErdosStraus.SScale P X) hS_ge_one
  have hsum := sAvgRecip_le_harmonic_floor P X
  have htail : 1 + Real.log (ErdosStraus.SScale P X)
      ≤ 2 * Real.log (ErdosStraus.SScale P X) := by
    linarith
  exact le_trans hsum (le_trans hharm htail)

/-- `sAvgPhi P X ≪ log S`, since `φ(s) ≤ s`. -/
theorem sAvgPhi_upper_log (P : ErdosStraus.Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      sAvgPhi P X ≤ C * Real.log (ErdosStraus.SScale P X) := by
  rcases sAvgRecip_upper_log P with ⟨C, X₀, hC, hbound⟩
  refine ⟨C, X₀, hC, ?_⟩
  intro X hX
  exact le_trans (sAvgPhi_le_sAvgRecip P X) (hbound X hX)

/-! ## Odd divisors of `P(z)` -/

/-- `A_s = ∑_{d≤U, d∣P(z), d odd, (d,s)=1} 1/d`, the sum of Lemma 6.4 with `m = 1`. -/
noncomputable def smallDivisorWeight (X : ℝ) (s : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.UScale X⌋₊).filter
      (fun d => d ∣ roughModulus X ∧ Odd d ∧ Nat.Coprime d s),
    (1 : ℝ) / (d : ℝ)

/-- `∑_{s ≤ S, s squarefree} A_s/s`, the sum estimated in Lemma 6.4 (with `m = 1`). -/
noncomputable def smallDivisorAverage (P : ErdosStraus.Params) (X : ℝ) : ℝ :=
  ∑ s ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.SScale P X⌋₊).filter (fun s => Squarefree s),
    smallDivisorWeight X s / (s : ℝ)

/-- `∑_{s ≤ S, s squarefree, (s,d)=1} 1/s`, the inner sum after interchanging the sums in
Lemma 6.4. -/
noncomputable def sAvgRecipCoprime (P : ErdosStraus.Params) (X : ℝ) (d : ℕ) : ℝ :=
  ∑ s ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.SScale P X⌋₊).filter
      (fun s => Squarefree s ∧ Nat.Coprime s d),
    (1 : ℝ) / (s : ℝ)

/-- `∑_{d≤U, d∣P(z), d odd} φ(d)/d²`, the sum over `d` left after the interchange in
Lemma 6.4. -/
noncomputable def smallDivisorEulerSum (X : ℝ) : ℝ :=
  ∑ d ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.UScale X⌋₊).filter
      (fun d => d ∣ roughModulus X ∧ Odd d),
    (Nat.totient d : ℝ) / (d : ℝ) ^ 2

/-- The odd squarefree `d ≤ z = (log X)^4`. -/
noncomputable def oddSquarefreeEulerWitness (X : ℝ) : Finset ℕ :=
  (Finset.Icc (1 : ℕ) ⌊ErdosStraus.zScale X⌋₊).filter
    (fun d => Squarefree d ∧ Odd d)

/-- The odd squarefree `d ≤ Z`. -/
noncomputable def oddSquarefreeEulerWitnessNat (Z : ℕ) : Finset ℕ :=
  (Finset.Icc (1 : ℕ) Z).filter (fun d => Squarefree d ∧ Odd d)

theorem oddSquarefreeEulerWitnessNat_subset {Z Z' : ℕ} (hZZ' : Z ≤ Z') :
    oddSquarefreeEulerWitnessNat Z ⊆ oddSquarefreeEulerWitnessNat Z' := by
  intro d hd
  rw [oddSquarefreeEulerWitnessNat, Finset.mem_filter] at hd ⊢
  exact ⟨Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hd.1).1, le_trans (Finset.mem_Icc.mp hd.1).2 hZZ'⟩,
    hd.2⟩

theorem oddSquarefreeEulerWitnessNat_sum_mono {Z Z' : ℕ} (hZZ' : Z ≤ Z') :
    (∑ d ∈ oddSquarefreeEulerWitnessNat Z, (Nat.totient d : ℝ) / (d : ℝ) ^ 2)
      ≤ ∑ d ∈ oddSquarefreeEulerWitnessNat Z',
          (Nat.totient d : ℝ) / (d : ℝ) ^ 2 := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (oddSquarefreeEulerWitnessNat_subset hZZ')
    (by
      intro d _hdBig _hdSmall
      exact div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

theorem UScale_eq_zScale_sq (X : ℝ) :
    ErdosStraus.UScale X = ErdosStraus.zScale X ^ 2 := by
  unfold ErdosStraus.UScale ErdosStraus.zScale
  ring

theorem zScale_ge_one_of_exp_one_le {X : ℝ} (hX : Real.exp 1 ≤ X) :
    1 ≤ ErdosStraus.zScale X := by
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hlogX_ge_one : (1 : ℝ) ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hX
  unfold ErdosStraus.zScale
  calc
    (1 : ℝ) = (1 : ℝ) ^ (4 : ℕ) := by norm_num
    _ ≤ (Real.log X) ^ (4 : ℕ) :=
        pow_le_pow_left₀ zero_le_one hlogX_ge_one 4

/-- An odd squarefree `d ≤ z` divides `P(z)`, and `d ≤ z ≤ z² = U` when `z ≥ 1`. -/
theorem oddSquarefreeEulerWitness_subset_smallDivisorSupport (X : ℝ)
    (hz_ge_one : 1 ≤ ErdosStraus.zScale X) :
    oddSquarefreeEulerWitness X ⊆
      (Finset.Icc (1 : ℕ) ⌊ErdosStraus.UScale X⌋₊).filter
        (fun d => d ∣ roughModulus X ∧ Odd d) := by
  classical
  intro d hd
  have hdIcc : d ∈ Finset.Icc (1 : ℕ) ⌊ErdosStraus.zScale X⌋₊ :=
    (Finset.mem_filter.mp hd).1
  have hsqf : Squarefree d := (Finset.mem_filter.mp hd).2.1
  have hodd : Odd d := (Finset.mem_filter.mp hd).2.2
  have hd_ge_one : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
  have hd_le_floor_z : d ≤ ⌊ErdosStraus.zScale X⌋₊ :=
    (Finset.mem_Icc.mp hdIcc).2
  have hdiv : d ∣ roughModulus X := by
    unfold roughModulus
    exact squarefree_dvd_primeProductBelow_of_le_floor
      (ErdosStraus.zScale X) hsqf hd_le_floor_z
  have hz_nonneg : 0 ≤ ErdosStraus.zScale X := le_trans zero_le_one hz_ge_one
  have hd_le_z : (d : ℝ) ≤ ErdosStraus.zScale X := by
    exact le_trans (by exact_mod_cast hd_le_floor_z) (Nat.floor_le hz_nonneg)
  have hz_le_U : ErdosStraus.zScale X ≤ ErdosStraus.UScale X := by
    rw [UScale_eq_zScale_sq X]
    nlinarith
  have hd_le_floor_U : d ≤ ⌊ErdosStraus.UScale X⌋₊ :=
    Nat.le_floor (le_trans hd_le_z hz_le_U)
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hd_ge_one, hd_le_floor_U⟩, ⟨hdiv, hodd⟩⟩

end ErdosStraus.Estimates
