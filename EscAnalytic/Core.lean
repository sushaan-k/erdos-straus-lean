import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Order.Filter.AtTopBot
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Tactic

/-!
# Parameters and analytic scales

This module contains the manuscript's fixed real parameters and their
admissible inequalities, the `X`-indexed scales, and the linearized exact-divisor
data `e = r s²`, `ρ(e) = r s`.

This file is part of the *full-paper* formalization that builds on the cited
analytic background.  The currently consumed assumptions are exported explicitly
in `EscAnalytic/Inputs.lean` or sibling files; unused estimate interfaces are
kept as finite carriers with elementary fallbacks rather than axiom declarations.
Everything derived from the exported assumptions is proved in the downstream
modules.

Imports are restricted to the modules present in the local Mathlib cache.
-/

namespace EscAnalytic

open scoped BigOperators
open Filter

/-- The fixed real parameters `0 < η, σ, λ, θ, β < 1` of the saturated family,
together with the admissibility inequalities `(eq:param-conditions)`:
`3η < λ`, `η+σ < λ`, `λ+η < θ`, `2θ < β < 1-σ`. -/
structure Params where
  η : ℝ
  σ : ℝ
  lam : ℝ
  θ : ℝ
  β : ℝ
  η_pos : 0 < η
  σ_pos : 0 < σ
  lam_pos : 0 < lam
  θ_pos : 0 < θ
  β_pos : 0 < β
  β_lt_one : β < 1
  three_η_lt_lam : 3 * η < lam
  η_add_σ_lt_lam : η + σ < lam
  lam_add_η_lt_θ : lam + η < θ
  two_θ_lt_β : 2 * θ < β
  β_lt_one_sub_σ : β < 1 - σ

namespace Params

/-- The explicit admissible choice exhibited in the manuscript:
`η=1/100, σ=1/20, λ=1/10, θ=3/10, β=2/3`. -/
noncomputable def explicit : Params where
  η := 1 / 100
  σ := 1 / 20
  lam := 1 / 10
  θ := 3 / 10
  β := 2 / 3
  η_pos := by norm_num
  σ_pos := by norm_num
  lam_pos := by norm_num
  θ_pos := by norm_num
  β_pos := by norm_num
  β_lt_one := by norm_num
  three_η_lt_lam := by norm_num
  η_add_σ_lt_lam := by norm_num
  lam_add_η_lt_θ := by norm_num
  two_θ_lt_β := by norm_num
  β_lt_one_sub_σ := by norm_num

variable (P : Params)

/-- Consequence of the admissibility inequalities: `σ < λ` (conductor separation
forces `Y₀ = X^λ > X^σ = Y`). -/
theorem σ_lt_lam : P.σ < P.lam :=
  lt_of_le_of_lt (le_add_of_nonneg_left P.η_pos.le) P.η_add_σ_lt_lam

/-- `σ < θ`. -/
theorem σ_lt_θ : P.σ < P.θ := by
  have h1 : P.σ < P.lam := P.σ_lt_lam
  have h2 : P.lam < P.θ := lt_of_le_of_lt (le_add_of_nonneg_right P.η_pos.le) P.lam_add_η_lt_θ
  exact h1.trans h2

/-- `2σ < β`, hence the prime range `X^β < p ≤ X^{1-σ}` is nonempty for large `X`. -/
theorem two_σ_lt_β : 2 * P.σ < P.β := by
  have : P.σ < P.θ := P.σ_lt_θ
  have : 2 * P.σ < 2 * P.θ := by linarith
  linarith [P.two_θ_lt_β]

end Params

/-! ## `X`-indexed scales (sieve, conductor, prime ranges). -/

/-- Sieve threshold `z = (log X)^4`. -/
noncomputable def zScale (X : ℝ) : ℝ := (Real.log X) ^ 4
/-- `U = (log X)^8`, the cap on the small-prime medium part `d₋`. -/
noncomputable def UScale (X : ℝ) : ℝ := (Real.log X) ^ 8
/-- `S = X^η`, the cap on the square root `s`. -/
noncomputable def SScale (P : Params) (X : ℝ) : ℝ := X ^ P.η
/-- `Y₀ = X^λ`, lower scale for the squarefree part `r`. -/
noncomputable def Y0Scale (P : Params) (X : ℝ) : ℝ := X ^ P.lam
/-- `Y = X^σ`, cap on `d₋d₊`. -/
noncomputable def YScale (P : Params) (X : ℝ) : ℝ := X ^ P.σ
/-- `H = X^θ`, cap on the exact divisor `e`. -/
noncomputable def HScale (P : Params) (X : ℝ) : ℝ := X ^ P.θ

/-- For `X ≥ e`, the sieve scale satisfies `log z(X) ≤ 4 log X`.

This is the checked version of the routine scale comparison behind the
manuscript's `log z_N ≪ log N` bookkeeping. -/
theorem log_zScale_le_four_log {X : ℝ} (hX : Real.exp 1 ≤ X) :
    Real.log (zScale X) ≤ 4 * Real.log X := by
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hlogX_ge_one : (1 : ℝ) ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hX
  have hlogX_nonneg : 0 ≤ Real.log X := le_trans zero_le_one hlogX_ge_one
  have hlogZ : Real.log (zScale X) = 4 * Real.log (Real.log X) := by
    unfold zScale
    rw [Real.log_pow]
    ring
  rw [hlogZ]
  have hloglog_le : Real.log (Real.log X) ≤ Real.log X :=
    Real.log_le_self hlogX_nonneg
  nlinarith

/-- Conductor separation at the scale level: `Y = X^σ < X^λ = Y₀` for `X > 1`. -/
theorem YScale_lt_Y0Scale (P : Params) {X : ℝ} (hX : 1 < X) :
    YScale P X < Y0Scale P X := by
  unfold YScale Y0Scale
  exact Real.rpow_lt_rpow_left_iff hX |>.mpr P.σ_lt_lam

/-! ## Linearized exact-divisor data `e = r s²`, `ρ(e) = r s`. -/

/-- A linearized exact divisor `e = r·s²` with squarefree, coprime `r, s`
(`E_lin` membership data, `eq:rs-range` ranges applied separately). -/
structure ExactDivisor where
  r : ℕ
  s : ℕ
  r_squarefree : Squarefree r
  s_squarefree : Squarefree s
  coprime_rs : Nat.Coprime r s

namespace ExactDivisor

/-- The exact divisor `e = r s²`. -/
def e (E : ExactDivisor) : ℕ := E.r * E.s ^ 2
/-- The reduced conductor `ρ(e) = r s`. -/
def rho (E : ExactDivisor) : ℕ := E.r * E.s

/-- The reduced conductor is squarefree. -/
theorem rho_squarefree (E : ExactDivisor) : Squarefree E.rho := by
  unfold rho
  exact (Nat.squarefree_mul E.coprime_rs).mpr ⟨E.r_squarefree, E.s_squarefree⟩

/-- The exact divisor and its reduced conductor have the same prime support. -/
theorem prime_dvd_rho_iff_dvd_e (E : ExactDivisor) (p : ℕ) (hp : p.Prime) :
    p ∣ E.rho ↔ p ∣ E.e := by
  unfold rho e
  constructor
  · intro h
    rcases hp.dvd_mul.mp h with hr | hs
    · exact dvd_mul_of_dvd_left hr (E.s ^ 2)
    · have hsSq : E.s ∣ E.s ^ 2 := dvd_pow_self E.s (by norm_num)
      exact dvd_mul_of_dvd_right (hs.trans hsSq) E.r
  · intro h
    rcases hp.dvd_mul.mp h with hr | hsSq
    · exact dvd_mul_of_dvd_left hr E.s
    · exact dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow hsSq) E.r

/-- The squarefree decomposition determines the reduced conductor from the
exact divisor. -/
theorem rho_eq_of_e_eq (E F : ExactDivisor) (h : E.e = F.e) :
    E.rho = F.rho := by
  apply (Nat.Squarefree.ext_iff (rho_squarefree E) (rho_squarefree F)).2
  intro p hp
  rw [prime_dvd_rho_iff_dvd_e E p hp,
    prime_dvd_rho_iff_dvd_e F p hp, h]

/-- A positive reduced conductor removes the only zero-coordinate ambiguity in
the squarefree decomposition: the exact divisor is then determined by `e`. -/
theorem eq_of_e_eq_of_rho_pos (E F : ExactDivisor) (he : E.e = F.e)
    (hrho : 0 < E.rho) : E = F := by
  have hrhoEq : E.rho = F.rho := rho_eq_of_e_eq E F he
  have hEfactor : E.e = E.rho * E.s := by
    unfold e rho
    ring
  have hFfactor : F.e = F.rho * F.s := by
    unfold e rho
    ring
  have hsMul : E.rho * E.s = E.rho * F.s := by
    calc
      E.rho * E.s = E.e := hEfactor.symm
      _ = F.e := he
      _ = F.rho * F.s := hFfactor
      _ = E.rho * F.s := by rw [hrhoEq]
  have hs : E.s = F.s := Nat.eq_of_mul_eq_mul_left hrho hsMul
  have hsPos : 0 < E.s := Nat.pos_of_mul_pos_left hrho
  have hrMul : E.r * E.s = F.r * E.s := by
    calc
      E.r * E.s = E.rho := rfl
      _ = F.rho := hrhoEq
      _ = F.r * F.s := rfl
      _ = F.r * E.s := by rw [hs]
  have hr : E.r = F.r := Nat.eq_of_mul_eq_mul_right hsPos hrMul
  cases E
  cases F
  simp_all

/-- `ρ(e) ∣ e` is false in general, but `ρ(e)² = r²s²` and `e = r s²` give `ρ(e) ∣ e · s`;
the key divisibility used in the certificate is `e ∣ a²` once `ρ(e) ∣ a`. -/
theorem rho_sq_eq (E : ExactDivisor) : E.rho ^ 2 = E.r ^ 2 * E.s ^ 2 := by
  unfold rho; ring

/-- If `ρ(e) ∣ a` then `e ∣ a²` (the saturation step `ρ(e) ∣ aᵢ ⟹ e ∣ aᵢ²`). -/
theorem e_dvd_sq_of_rho_dvd (E : ExactDivisor) {a : ℕ} (h : E.rho ∣ a) : E.e ∣ a ^ 2 := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨E.r * k ^ 2, ?_⟩
  unfold e rho
  ring

/-- Positivity of the reduced conductor `ρ(e)=rs` from positivity of the two
linearized coordinates. -/
theorem rho_pos (E : ExactDivisor) (hr : 0 < E.r) (hs : 0 < E.s) :
    0 < E.rho := by
  unfold rho
  exact Nat.mul_pos hr hs

/-- The reciprocal `1/ρ(e)` factors as the product of the two reciprocal
coordinates.  This is the elementary exact-divisor identity behind the
`M₁` mass expansion. -/
theorem one_div_rho_cast_eq (E : ExactDivisor) (hr : 0 < E.r) (hs : 0 < E.s) :
    (1 : ℝ) / (E.rho : ℝ) = ((1 : ℝ) / (E.r : ℝ)) * ((1 : ℝ) / (E.s : ℝ)) := by
  have hrR : (E.r : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  have hsR : (E.s : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  unfold rho
  rw [Nat.cast_mul]
  field_simp [hrR, hsR]

/-- The reciprocal totient weight of the reduced conductor factors over the
coprime coordinates.  This is the elementary exact-divisor identity behind the
`M_φ` mass expansion. -/
theorem one_div_totient_rho_cast_eq
    (E : ExactDivisor) (hr : 0 < E.r) (hs : 0 < E.s) :
    (1 : ℝ) / (Nat.totient E.rho : ℝ) =
      ((1 : ℝ) / (Nat.totient E.r : ℝ)) *
        ((1 : ℝ) / (Nat.totient E.s : ℝ)) := by
  have htot_r : (Nat.totient E.r : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Nat.totient_pos.mpr hr)
  have htot_s : (Nat.totient E.s : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Nat.totient_pos.mpr hs)
  unfold rho
  rw [Nat.totient_mul E.coprime_rs, Nat.cast_mul]
  field_simp [htot_r, htot_s]

end ExactDivisor

end EscAnalytic
