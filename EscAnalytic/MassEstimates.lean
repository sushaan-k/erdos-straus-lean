import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Tactic
import EscAnalytic.Core
import EscAnalytic.Inputs
import EscAnalytic.MassTensor

/-!
# Concrete mass estimates

This file supplies the concrete `FactorAsymp` data used by
`EscAnalytic.MassTensor.mass_law`.  The resulting wrappers depend only on the
small-side estimates proved here and the named rough-sieve inputs in
`EscAnalytic.Inputs`.

`MassTensor.mass_law` proves `μ_b = sigmaSmall · roughFactor ≍ (log X)³` from

* `hSig : FactorAsymp sigmaSmall sigmaShape`, with
  `Σ_b ≍ (log X)² · log z`; and
* `hR : FactorAsymp roughFactor roughShape`, with the rough factor
  `≍ (log X)/(log z)`.

`MassTensor.roughFactor_asymp` already supplies `hR` from
`Inputs.rough_sqf_recip`, now a theorem over the standard rough-sieve input.
This file supplies the analogous datum for `hSig`.

## Proof structure

The manuscript's `Σ_b ≍ (log X)² · log z` is assembled as
`Σ_b ≍ log X · (∑_{s} A_s/s) ≍ log X · (log S · log z) ≍ (log X)² · log z`, where

* `log X` is the inner reduced `r`-progression length `log(H/(Y₀ s)) ≍ log X`
  (`lem:phi-progression-average`);
* `∑_s A_s/s ≍ log S · log z` is the averaged small-prime divisor sum
  (`lem:small-divisor-average`), itself split as `log S` (the
  squarefree-`s` average) times `log z` (the odd-divisor `A_s` average).

Of these three factors, the carrier-level versions used by the canonical
`smallDivisorAverage` wrapper are discharged in `Inputs`:

* the squarefree-conductor average `log S ≍ log X` is `Inputs.s_average_recip`
  (`lem:s-average`).  It is supplied by
  `sAvgRecip_asymp : FactorAsymp (Inputs.sAvgRecip P) logX`, using
  `log (SScale P X) = η · log X`.

The older fully factored API still lets callers thread the inner progression
length and odd-divisor average as explicit `FactorAsymp` hypotheses.  The
canonical fixed-slant `smallDivisorAverage` wrappers used by the public frontier
instead use the checked concrete carrier facts in `Inputs`.

We then:

1. give a reusable combinator `FactorAsymp.mul` for multiplying asymptotic data;
2. assemble `sigmaFactor_asymp : FactorAsymp sigmaSmallConcrete sigmaShape`
   from the cited `sAvgRecip_asymp` and the two threaded factors, after the
   algebraic shape identity `logX · logX · logZ = sigmaShape` is checked;
3. conclude `mass_law_from_inputs`, which **needs no `FactorAsymp sigmaSmall
   sigmaShape` and no `FactorAsymp roughFactor roughShape` hypothesis**: both are
   produced internally from checked carrier estimates plus `Inputs.rough_sqf_recip`
   (a theorem over the standard rough-sieve inputs).

This file declares no axioms.  The
only external inputs used by the no-argument standard mass wrappers are the two
standard rough-sieve inputs behind `rough_sqf_recip`: the one-sided
prime-reciprocal Mertens upper bound and the positive-range normalized
`z = (log X)^4` rough-count fundamental-lemma discrepancy estimate.  Wrappers
whose analytic estimates are explicit hypotheses are checked separately to have
no hidden project-axiom dependencies.

-/

namespace EscAnalytic

open Filter
open scoped BigOperators

/-! ## Reference shapes for the constituent factors of `Σ_b`. -/

/-- The reference shape `log X` (one factor of `(log X)²` in `Σ_b`). -/
noncomputable def logX (X : ℝ) : ℝ := Real.log X

/-- The reference shape `log z = log (zScale X)` (the small-divisor `A_s` factor of
`Σ_b`, `lem:small-divisor-average`, tex 1496–1538). -/
noncomputable def logZ (X : ℝ) : ℝ := Real.log (zScale X)

/-! ## A reusable product combinator for `FactorAsymp`.

If `f₁ ≍ g₁` and `f₂ ≍ g₂` (both `FactorAsymp`, both shapes eventually
nonnegative) then `f₁·f₂ ≍ g₁·g₂`.  The constants multiply and the threshold is
the max.  This is the algebraic engine that lets us build `Σ_b`'s asymptotic from
its three constituent factor-asymptotics, exactly mirroring `MassTensor.mass_law`'s
two-factor cancellation but for a *product* of shapes. -/

/-- The product of two `FactorAsymp` data, asymptotic to the product of the
shapes.  Requires the two shapes to be nonnegative beyond their thresholds (true
for `logX`, `logZ`, etc., for `X` large), supplied as `hg₁`, `hg₂`. -/
noncomputable def FactorAsymp.mul {f₁ g₁ f₂ g₂ : ℝ → ℝ}
    (h₁ : FactorAsymp f₁ g₁) (h₂ : FactorAsymp f₂ g₂)
    (hg₁ : ∀ X : ℝ, max h₁.X₀ h₂.X₀ ≤ X → 0 ≤ g₁ X)
    (hg₂ : ∀ X : ℝ, max h₁.X₀ h₂.X₀ ≤ X → 0 ≤ g₂ X) :
    FactorAsymp (fun X => f₁ X * f₂ X) (fun X => g₁ X * g₂ X) where
  c := h₁.c * h₂.c
  C := h₁.C * h₂.C
  X₀ := max h₁.X₀ h₂.X₀
  c_pos := mul_pos h₁.c_pos h₂.c_pos
  C_pos := mul_pos h₁.C_pos h₂.C_pos
  f_nonneg := fun X hX =>
    mul_nonneg (h₁.f_nonneg X (le_trans (le_max_left _ _) hX))
      (h₂.f_nonneg X (le_trans (le_max_right _ _) hX))
  sandwich := fun X hX => by
    have hX1 : h₁.X₀ ≤ X := le_trans (le_max_left _ _) hX
    have hX2 : h₂.X₀ ≤ X := le_trans (le_max_right _ _) hX
    obtain ⟨h1lo, h1hi⟩ := h₁.sandwich X hX1
    obtain ⟨h2lo, h2hi⟩ := h₂.sandwich X hX2
    have hf1 : 0 ≤ f₁ X := h₁.f_nonneg X hX1
    have hf2 : 0 ≤ f₂ X := h₂.f_nonneg X hX2
    have hgg1 : 0 ≤ g₁ X := hg₁ X hX
    have hgg2 : 0 ≤ g₂ X := hg₂ X hX
    refine ⟨?_, ?_⟩
    · -- lower: (c₁ c₂)(g₁ g₂) = (c₁ g₁)(c₂ g₂) ≤ f₁ f₂
      calc (h₁.c * h₂.c) * (g₁ X * g₂ X)
          = (h₁.c * g₁ X) * (h₂.c * g₂ X) := by ring
        _ ≤ f₁ X * f₂ X := by
            apply mul_le_mul h1lo h2lo
              (mul_nonneg h₂.c_pos.le hgg2) hf1
    · -- upper: f₁ f₂ ≤ (C₁ g₁)(C₂ g₂) = (C₁ C₂)(g₁ g₂)
      calc f₁ X * f₂ X
          ≤ (h₁.C * g₁ X) * (h₂.C * g₂ X) := by
            apply mul_le_mul h1hi h2hi hf2
              (mul_nonneg h₁.C_pos.le hgg1)
        _ = (h₁.C * h₂.C) * (g₁ X * g₂ X) := by ring

/-! ## The cited `log S ≍ log X` factor, fully discharged.

`Inputs.s_average_recip` gives `sAvgRecip P X ≍ log (SScale P X)`, and
`SScale P X = X^η` so `log (SScale P X) = η · log X` for `X > 1`.  Hence
`sAvgRecip ≍ log X` with the `η` folded into the constants.  This is a **real
proof** reducing one factor of `Σ_b` to a cited input. -/

/-- `log (SScale P X) = P.η · log X` for `X > 0`.  (`SScale P X = X^η`.) -/
theorem log_SScale (P : Params) {X : ℝ} (hX : 0 < X) :
    Real.log (SScale P X) = P.η * Real.log X := by
  unfold SScale
  rw [Real.log_rpow hX]

/-- `log (Y₀Scale P X) = λ · log X` for `X > 0`. -/
theorem log_Y0Scale (P : Params) {X : ℝ} (hX : 0 < X) :
    Real.log (Y0Scale P X) = P.lam * Real.log X := by
  unfold Y0Scale
  rw [Real.log_rpow hX]

/-- `log (HScale P X) = θ · log X` for `X > 0`. -/
theorem log_HScale (P : Params) {X : ℝ} (hX : 0 < X) :
    Real.log (HScale P X) = P.θ * Real.log X := by
  unfold HScale
  rw [Real.log_rpow hX]

/-- The logarithmic length of the inner `r` interval appearing in
`lem:phi-progression-average`: `log(H/(Y₀s))`. -/
noncomputable def slantLogLength (P : Params) (s : ℕ) (X : ℝ) : ℝ :=
  Real.log (HScale P X / (Y0Scale P X * (s : ℝ)))

/-- Exact scale formula for the slanted logarithmic length:
`log(H/(Y₀s)) = (θ - λ) log X - log s`. -/
theorem slantLogLength_eq_theta_sub_lam_mul_log_sub_log_nat
    (P : Params) {X : ℝ} {s : ℕ} (hX : 0 < X) (hs : 0 < s) :
    slantLogLength P s X =
      (P.θ - P.lam) * Real.log X - Real.log (s : ℝ) := by
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hHne : HScale P X ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hX P.θ)
  have hYne : Y0Scale P X ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hX P.lam)
  have hsne : (s : ℝ) ≠ 0 := ne_of_gt hsR
  have hden_ne : Y0Scale P X * (s : ℝ) ≠ 0 := mul_ne_zero hYne hsne
  unfold slantLogLength
  rw [Real.log_div hHne hden_ne, Real.log_mul hYne hsne]
  rw [log_HScale P hX, log_Y0Scale P hX]
  ring

/-- Uniform lower bound for the slanted log length on the paper's conductor
range `s ≤ S = X^η`. -/
theorem slantLogLength_ge_theta_sub_lam_sub_eta_mul_log
    (P : Params) {X : ℝ} {s : ℕ} (hX : 1 ≤ X) (hs : 1 ≤ s)
    (hsS : (s : ℝ) ≤ SScale P X) :
    (P.θ - P.lam - P.η) * Real.log X ≤ slantLogLength P s X := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hs_pos : 0 < (s : ℝ) := by exact_mod_cast hs_pos_nat
  have hlogs : Real.log (s : ℝ) ≤ P.η * Real.log X := by
    calc
      Real.log (s : ℝ) ≤ Real.log (SScale P X) :=
        Real.log_le_log hs_pos hsS
      _ = P.η * Real.log X := log_SScale P hXpos
  rw [slantLogLength_eq_theta_sub_lam_mul_log_sub_log_nat P hXpos hs_pos_nat]
  nlinarith

/-- Uniform upper bound for the slanted log length on `s ≥ 1`. -/
theorem slantLogLength_le_theta_sub_lam_mul_log
    (P : Params) {X : ℝ} {s : ℕ} (hX : 1 ≤ X) (hs : 1 ≤ s) :
    slantLogLength P s X ≤ (P.θ - P.lam) * Real.log X := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hs_ge_one : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hlog_s_nonneg : 0 ≤ Real.log (s : ℝ) := Real.log_nonneg hs_ge_one
  rw [slantLogLength_eq_theta_sub_lam_mul_log_sub_log_nat P hXpos hs_pos_nat]
  nlinarith

/-- The slanted logarithmic length is eventually at least one, uniformly on
the exact-divisor conductor range `1≤s≤S`. -/
theorem slantLogLength_ge_one_eventually (P : Params) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ s : ℕ, 1 ≤ s → (s : ℝ) ≤ SScale P X →
        (1 : ℝ) ≤ slantLogLength P s X := by
  let c : ℝ := P.θ - P.lam - P.η
  have hc : 0 < c := by
    dsimp [c]
    linarith [P.lam_add_η_lt_θ]
  refine ⟨max (Real.exp 1) (Real.exp (1 / c)), ?_⟩
  intro X hX s hs hsS
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_left _ _) hX
  have hXexp_c : Real.exp (1 / c) ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hlog_ge : 1 / c ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hXexp_c
  have hc_log_ge_one : (1 : ℝ) ≤ c * Real.log X := by
    have hmul := mul_le_mul_of_nonneg_left hlog_ge hc.le
    have hc_ne : c ≠ 0 := ne_of_gt hc
    field_simp [hc_ne] at hmul
    simpa [mul_comm] using hmul
  exact hc_log_ge_one.trans
    (by
      dsimp [c]
      exact slantLogLength_ge_theta_sub_lam_sub_eta_mul_log P hXone hs hsS)

/-- The lower endpoint `U₀=Y₀/s` in `lem:phi-progression-average`. -/
noncomputable def phiProgressionU0 (P : Params) (s : ℕ) (X : ℝ) : ℝ :=
  Y0Scale P X / (s : ℝ)

/-- The upper endpoint `U₁=H/s²` in `lem:phi-progression-average`. -/
noncomputable def phiProgressionU1 (P : Params) (s : ℕ) (X : ℝ) : ℝ :=
  HScale P X / (s : ℝ) ^ (2 : ℕ)

/-- The phi-progression window is a long ordinary-squarefree window.

For `s ≤ S=X^η`, the quotient of the upper and lower endpoints satisfies
`U₁/U₀ ≥ X^(θ-λ-η)`, matching the long-window hypothesis in
`lem:ordinary-sqf`. -/
theorem phiProgression_ratio_ge_rpow_theta_sub_lam_sub_eta
    (P : Params) {X : ℝ} {s : ℕ} (hX : 1 ≤ X) (hs : 1 ≤ s)
    (hsS : (s : ℝ) ≤ SScale P X) :
    X ^ (P.θ - P.lam - P.η) ≤
      phiProgressionU1 P s X / phiProgressionU0 P s X := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hs_pos : 0 < (s : ℝ) := by exact_mod_cast hs_pos_nat
  have hYpos : 0 < Y0Scale P X := Real.rpow_pos_of_pos hXpos P.lam
  have hHpos : 0 < HScale P X := Real.rpow_pos_of_pos hXpos P.θ
  have hSpos : 0 < SScale P X := Real.rpow_pos_of_pos hXpos P.η
  have hU0pos : 0 < phiProgressionU0 P s X := by
    unfold phiProgressionU0
    exact div_pos hYpos hs_pos
  have hsS_pos : 0 < SScale P X := hSpos
  calc
    X ^ (P.θ - P.lam - P.η)
        = X ^ P.θ / (X ^ P.lam * X ^ P.η) := by
          rw [← Real.rpow_add hXpos, ← Real.rpow_sub hXpos]
          ring_nf
    _ = HScale P X / (Y0Scale P X * SScale P X) := by
          unfold HScale Y0Scale SScale
          rfl
    _ ≤ HScale P X / (Y0Scale P X * (s : ℝ)) := by
          exact div_le_div_of_nonneg_left hHpos.le
            (mul_pos hYpos hs_pos) (mul_le_mul_of_nonneg_left hsS hYpos.le)
    _ = phiProgressionU1 P s X / phiProgressionU0 P s X := by
          unfold phiProgressionU1 phiProgressionU0
          field_simp [ne_of_gt hs_pos, ne_of_gt hYpos, ne_of_gt hU0pos,
            ne_of_gt hsS_pos]
          ring

/-- The lower endpoint `U₀=Y₀/s` stays above `X^(λ-η)` throughout the
paper's range `s ≤ S = X^η`. -/
theorem phiProgressionU0_ge_rpow_lam_sub_eta
    (P : Params) {X : ℝ} {s : ℕ} (hX : 1 ≤ X) (hs : 1 ≤ s)
    (hsS : (s : ℝ) ≤ SScale P X) :
    X ^ (P.lam - P.η) ≤ phiProgressionU0 P s X := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hs_pos : 0 < (s : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hs
  have hYpos : 0 ≤ Y0Scale P X := (Real.rpow_pos_of_pos hXpos P.lam).le
  unfold phiProgressionU0 Y0Scale SScale at *
  calc
    X ^ (P.lam - P.η) = X ^ P.lam / X ^ P.η := by
      rw [Real.rpow_sub hXpos]
    _ ≤ X ^ P.lam / (s : ℝ) := by
      exact div_le_div_of_nonneg_left hYpos hs_pos hsS

/-- The manuscript's wide tensor modulus range `D ≤ YU` is eventually below
`X^(λ-η)`, the lower endpoint scale of the fixed-`s` progression window.

This is the deterministic scale inequality behind the endpoint absorption in
`thm:tensor-e`; it uses only `η+σ<λ` and the polylogarithmic fact
`U=(log X)^8=o(X^δ)`. -/
theorem YScale_mul_UScale_le_rpow_lam_sub_eta_eventually (P : Params) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      YScale P X * UScale X ≤ X ^ (P.lam - P.η) := by
  let δ : ℝ := P.lam - P.η - P.σ
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith [P.η_add_σ_lt_lam]
  rcases Inputs.eventually_UScale_le_rpow hδ with ⟨XU, hU⟩
  refine ⟨max XU (Real.exp 1), ?_⟩
  intro X hX
  have hXU : XU ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hY_nonneg : 0 ≤ YScale P X :=
    (Real.rpow_pos_of_pos hXpos P.σ).le
  calc
    YScale P X * UScale X
        ≤ YScale P X * X ^ δ :=
          mul_le_mul_of_nonneg_left (hU X hXU) hY_nonneg
    _ = X ^ (P.lam - P.η) := by
          unfold YScale
          dsimp [δ]
          rw [← Real.rpow_add hXpos]
          ring_nf

/-- For every admissible `s`, the whole manuscript range `D≤YU` lies below
the fixed-`s` lower endpoint `U₀=Y₀/s`, eventually in `X`. -/
theorem wideModulus_le_phiProgressionU0_eventually (P : Params) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ s D : ℕ, 1 ≤ s → (s : ℝ) ≤ SScale P X →
        (D : ℝ) ≤ YScale P X * UScale X →
          (D : ℝ) ≤ phiProgressionU0 P s X := by
  rcases YScale_mul_UScale_le_rpow_lam_sub_eta_eventually P with
    ⟨XYU, hYU⟩
  refine ⟨max XYU (Real.exp 1), ?_⟩
  intro X hX s D hs hsS hDwide
  have hXYU : XYU ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe
  exact hDwide.trans ((hYU X hXYU).trans
    (phiProgressionU0_ge_rpow_lam_sub_eta P hXone hs hsS))

/-- Every admissible phi-progression window starts at or above one. -/
theorem one_le_phiProgressionU0
    (P : Params) {X : ℝ} {s : ℕ}
    (hXone : 1 ≤ X) (hs : 1 ≤ s) (hsS : (s : ℝ) ≤ SScale P X) :
    1 ≤ phiProgressionU0 P s X := by
  have hexp : 0 ≤ P.lam - P.η := by
    linarith [P.η_add_σ_lt_lam, P.σ_pos]
  exact (Real.one_le_rpow hXone hexp).trans
    (phiProgressionU0_ge_rpow_lam_sub_eta P hXone hs hsS)

/-- Uniform logarithmic envelope for the harmonic sum at the upper endpoint
of the actual phi-progression window. -/
theorem harmonic_floor_phiProgressionU1_le_log
    (P : Params) {X : ℝ} {s : ℕ}
    (hX : Real.exp 1 ≤ X) (hs : 1 ≤ s)
    (hsS : (s : ℝ) ≤ SScale P X) :
    ((harmonic ⌊phiProgressionU1 P s X⌋₊ : ℚ) : ℝ) ≤
      (P.θ + 1) * Real.log X := by
  have hXone : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hsposN : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hsposN
  have hU0one : 1 ≤ phiProgressionU0 P s X :=
    one_le_phiProgressionU0 P hXone hs hsS
  have hratio :=
    phiProgression_ratio_ge_rpow_theta_sub_lam_sub_eta
      P hXone hs hsS
  have hexp : 0 ≤ P.θ - P.lam - P.η := by
    linarith [P.lam_add_η_lt_θ]
  have hratio_one :
      1 ≤ phiProgressionU1 P s X / phiProgressionU0 P s X :=
    (Real.one_le_rpow hXone hexp).trans hratio
  have hU0pos : 0 < phiProgressionU0 P s X := lt_of_lt_of_le zero_lt_one hU0one
  have hU0leU1 : phiProgressionU0 P s X ≤ phiProgressionU1 P s X := by
    have := (le_div_iff₀ hU0pos).mp hratio_one
    simpa using this
  have hU1one : 1 ≤ phiProgressionU1 P s X := hU0one.trans hU0leU1
  have hh :=
    harmonic_floor_le_one_add_log (phiProgressionU1 P s X) hU1one
  have hHpos : 0 < HScale P X := Real.rpow_pos_of_pos hXpos P.θ
  have hsSqpos : 0 < (s : ℝ) ^ (2 : ℕ) := pow_pos hspos _
  have hlogU1 :
      Real.log (phiProgressionU1 P s X) ≤ P.θ * Real.log X := by
    unfold phiProgressionU1
    rw [Real.log_div (ne_of_gt hHpos) (ne_of_gt hsSqpos)]
    rw [log_HScale P hXpos]
    have hsoneR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    have hsSqOne : (1 : ℝ) ≤ (s : ℝ) ^ (2 : ℕ) := by nlinarith
    have hlogs : 0 ≤ Real.log ((s : ℝ) ^ (2 : ℕ)) :=
      Real.log_nonneg hsSqOne
    linarith
  have hlogone : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hX
  calc
    ((harmonic ⌊phiProgressionU1 P s X⌋₊ : ℚ) : ℝ)
        ≤ 1 + Real.log (phiProgressionU1 P s X) := hh
    _ ≤ 1 + P.θ * Real.log X := add_le_add_left hlogU1 1
    _ ≤ (P.θ + 1) * Real.log X := by nlinarith

/-- Squared form of the harmonic endpoint envelope. -/
theorem harmonic_floor_phiProgressionU1_sq_le_log_sq
    (P : Params) {X : ℝ} {s : ℕ}
    (hX : Real.exp 1 ≤ X) (hs : 1 ≤ s)
    (hsS : (s : ℝ) ≤ SScale P X) :
    ((harmonic ⌊phiProgressionU1 P s X⌋₊ : ℚ) : ℝ) ^ 2 ≤
      ((P.θ + 1) * Real.log X) ^ 2 := by
  have hh := harmonic_floor_phiProgressionU1_le_log P hX hs hsS
  have hleft :
      0 ≤ ((harmonic ⌊phiProgressionU1 P s X⌋₊ : ℚ) : ℝ) := by
    rw [Rat.cast_nonneg]
    rw [harmonic_eq_sum_Icc]
    apply Finset.sum_nonneg
    intro k _hk
    positivity
  exact pow_le_pow_left₀ hleft hh 2

/-- Reciprocal form of the polynomial lower-endpoint estimate. -/
theorem one_div_phiProgressionU0_le_rpow_neg_lam_sub_eta
    (P : Params) {X : ℝ} {s : ℕ}
    (hX : 1 ≤ X) (hs : 1 ≤ s)
    (hsS : (s : ℝ) ≤ SScale P X) :
    1 / phiProgressionU0 P s X ≤ X ^ (-(P.lam - P.η)) := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hpowpos : 0 < X ^ (P.lam - P.η) :=
    Real.rpow_pos_of_pos hXpos _
  have hU0 := phiProgressionU0_ge_rpow_lam_sub_eta P hX hs hsS
  calc
    1 / phiProgressionU0 P s X ≤ 1 / X ^ (P.lam - P.η) :=
      one_div_le_one_div_of_le hpowpos hU0
    _ = X ^ (-(P.lam - P.η)) := by
      rw [Real.rpow_neg hXpos.le]
      simp [one_div]

/-- Strengthened wide-modulus scale comparison needed for the CRT local-density
upper bound: if the endpoint margin `2η+σ<λ` holds, then the full CRT modulus
`sD` is eventually below the lower endpoint `U₀=Y₀/s` throughout
`s≤S`, `D≤YU`. -/
theorem wideModulus_mul_s_le_phiProgressionU0_eventually
    (P : Params) (hmargin : 2 * P.η + P.σ < P.lam) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ s D : ℕ, 1 ≤ s → (s : ℝ) ≤ SScale P X →
        (D : ℝ) ≤ YScale P X * UScale X →
          ((s * D : ℕ) : ℝ) ≤ phiProgressionU0 P s X := by
  let δ : ℝ := P.lam - 2 * P.η - P.σ
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith [hmargin]
  rcases Inputs.eventually_UScale_le_rpow hδ with ⟨XU, hU⟩
  refine ⟨max XU (Real.exp 1), ?_⟩
  intro X hX s D hs hsS hDwide
  have hXU : XU ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe
  have hlog_nonneg : 0 ≤ Real.log X := Real.log_nonneg hXone
  have hS_nonneg : 0 ≤ SScale P X :=
    (Real.rpow_pos_of_pos hXpos P.η).le
  have hY_nonneg : 0 ≤ YScale P X :=
    (Real.rpow_pos_of_pos hXpos P.σ).le
  have hU_nonneg : 0 ≤ UScale X := by
    unfold UScale
    exact pow_nonneg hlog_nonneg 8
  have hYU_nonneg : 0 ≤ YScale P X * UScale X :=
    mul_nonneg hY_nonneg hU_nonneg
  have hD_nonneg : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hprod_le_scale :
      ((s * D : ℕ) : ℝ) ≤ SScale P X * (YScale P X * UScale X) := by
    rw [Nat.cast_mul]
    exact mul_le_mul hsS hDwide hD_nonneg hS_nonneg
  have hscale :
      SScale P X * (YScale P X * UScale X) ≤ X ^ (P.lam - P.η) := by
    calc
      SScale P X * (YScale P X * UScale X)
          ≤ SScale P X * (YScale P X * X ^ δ) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hU X hXU) hY_nonneg) hS_nonneg
      _ = X ^ (P.lam - P.η) := by
            unfold SScale YScale
            dsimp [δ]
            rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos]
            ring_nf
  exact hprod_le_scale.trans
    (hscale.trans (phiProgressionU0_ge_rpow_lam_sub_eta P hXone hs hsS))

/-- The manuscript's explicit parameter choice satisfies the stronger CRT
endpoint margin needed for the wide-modulus `sD≤U₀` calculation. -/
theorem explicit_two_eta_add_sigma_lt_lam :
    2 * Params.explicit.η + Params.explicit.σ < Params.explicit.lam := by
  norm_num [Params.explicit]

/-- Explicit-parameter version of
`wideModulus_mul_s_le_phiProgressionU0_eventually`, with the auxiliary endpoint
margin discharged by the manuscript's fixed parameter values. -/
theorem wideModulus_mul_s_le_phiProgressionU0_eventually_explicit :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ s D : ℕ, 1 ≤ s → (s : ℝ) ≤ SScale Params.explicit X →
        (D : ℝ) ≤ YScale Params.explicit X * UScale X →
          ((s * D : ℕ) : ℝ) ≤ phiProgressionU0 Params.explicit s X :=
  wideModulus_mul_s_le_phiProgressionU0_eventually
    Params.explicit explicit_two_eta_add_sigma_lt_lam

/-- Fixed-`k` version of the lower-endpoint scale bound.  If the exposed
divisor satisfies `k ≤ X^κ`, then the quotient window begins at least at
`X^(λ-η-κ)`. -/
theorem phiProgressionU0_div_nat_ge_rpow_lam_sub_eta_sub
    (P : Params) {X κ : ℝ} {s k : ℕ} (hX : 1 ≤ X) (hs : 1 ≤ s)
    (hk : 1 ≤ k) (hsS : (s : ℝ) ≤ SScale P X)
    (hkX : (k : ℝ) ≤ X ^ κ) :
    X ^ (P.lam - P.η - κ) ≤ phiProgressionU0 P s X / (k : ℝ) := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hk_pos_nat : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hs_pos : 0 < (s : ℝ) := by exact_mod_cast hs_pos_nat
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos_nat
  have hYpos : 0 ≤ Y0Scale P X := (Real.rpow_pos_of_pos hXpos P.lam).le
  have hSpos : 0 ≤ SScale P X := (Real.rpow_pos_of_pos hXpos P.η).le
  have hden_le : (s : ℝ) * (k : ℝ) ≤ SScale P X * X ^ κ :=
    mul_le_mul hsS hkX hk_pos.le hSpos
  unfold phiProgressionU0 Y0Scale SScale at *
  calc
    X ^ (P.lam - P.η - κ) = X ^ P.lam / (X ^ P.η * X ^ κ) := by
      rw [← Real.rpow_add hXpos, ← Real.rpow_sub hXpos]
      ring_nf
    _ ≤ X ^ P.lam / ((s : ℝ) * (k : ℝ)) := by
      exact div_le_div_of_nonneg_left hYpos (mul_pos hs_pos hk_pos) hden_le
    _ = (X ^ P.lam / (s : ℝ)) / (k : ℝ) := by
      field_simp [ne_of_gt hs_pos, ne_of_gt hk_pos]

/-- The upper endpoint `U₁=H/s²` is always at most `X^θ` for `s≥1`.
This is the deterministic upper-scale side used when the phi-progression
window is passed to an ordinary squarefree progression estimate. -/
theorem phiProgressionU1_le_rpow_theta
    (P : Params) {X : ℝ} {s : ℕ} (hX : 0 < X) (hs : 1 ≤ s) :
    phiProgressionU1 P s X ≤ X ^ P.θ := by
  have hs_ge_one : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hs_sq_ge_one : (1 : ℝ) ≤ (s : ℝ) ^ (2 : ℕ) :=
    one_le_pow₀ hs_ge_one
  have hH_nonneg : 0 ≤ HScale P X :=
    (Real.rpow_pos_of_pos hX P.θ).le
  unfold phiProgressionU1 HScale
  calc
    X ^ P.θ / (s : ℝ) ^ (2 : ℕ)
        ≤ X ^ P.θ / 1 :=
          div_le_div_of_nonneg_left hH_nonneg (by norm_num) hs_sq_ge_one
    _ = X ^ P.θ := by ring

/-- Fixed-`k` upper-scale side: after dividing the phi-progression window by
any exposed divisor `k≥1`, the upper endpoint still lies below `X^θ`. -/
theorem phiProgressionU1_div_nat_le_rpow_theta
    (P : Params) {X : ℝ} {s k : ℕ} (hX : 0 < X) (hs : 1 ≤ s)
    (hk : 1 ≤ k) :
    phiProgressionU1 P s X / (k : ℝ) ≤ X ^ P.θ := by
  have hk_ge_one : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hU1_nonneg : 0 ≤ phiProgressionU1 P s X := by
    unfold phiProgressionU1
    exact div_nonneg (Real.rpow_pos_of_pos hX P.θ).le
      (sq_nonneg (s : ℝ))
  calc
    phiProgressionU1 P s X / (k : ℝ)
        ≤ phiProgressionU1 P s X / 1 :=
          div_le_div_of_nonneg_left hU1_nonneg (by norm_num) hk_ge_one
    _ = phiProgressionU1 P s X := by ring
    _ ≤ X ^ P.θ := phiProgressionU1_le_rpow_theta P hX hs

/-- If `k` lies below the actual upper endpoint `U₁=H/s²`, then the auxiliary
modulus `s*k` is at most `X^θ`.  This is the large-tail analogue of the
small-cutoff scale bound `s*k≤X^(η+κ)`. -/
theorem phiProgression_sk_le_rpow_theta_of_le_floor_U1
    (P : Params) {X : ℝ} {s k : ℕ} (hX : 0 < X) (hs : 1 ≤ s)
    (hk : k ≤ ⌊phiProgressionU1 P s X⌋₊) :
    ((s * k : ℕ) : ℝ) ≤ X ^ P.θ := by
  have hs_nonneg : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (Nat.zero_le s)
  have hs_ge_one : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hs_pos : (0 : ℝ) < (s : ℝ) := lt_of_lt_of_le zero_lt_one hs_ge_one
  have hU1_nonneg : 0 ≤ phiProgressionU1 P s X := by
    unfold phiProgressionU1
    exact div_nonneg (Real.rpow_pos_of_pos hX P.θ).le
      (sq_nonneg (s : ℝ))
  have hk_le_U1 : (k : ℝ) ≤ phiProgressionU1 P s X :=
    le_trans (by exact_mod_cast hk) (Nat.floor_le hU1_nonneg)
  have hmul :
      ((s * k : ℕ) : ℝ) ≤ (s : ℝ) * phiProgressionU1 P s X := by
    calc
      ((s * k : ℕ) : ℝ) = (s : ℝ) * (k : ℝ) := by norm_num
      _ ≤ (s : ℝ) * phiProgressionU1 P s X :=
          mul_le_mul_of_nonneg_left hk_le_U1 hs_nonneg
  have hendpoint :
      (s : ℝ) * phiProgressionU1 P s X ≤ X ^ P.θ := by
    have hH_nonneg : 0 ≤ X ^ P.θ := (Real.rpow_pos_of_pos hX P.θ).le
    unfold phiProgressionU1 HScale
    calc
      (s : ℝ) * (X ^ P.θ / (s : ℝ) ^ (2 : ℕ))
          = X ^ P.θ / (s : ℝ) := by
            field_simp [ne_of_gt hs_pos]
            ring
      _ ≤ X ^ P.θ / 1 :=
          div_le_div_of_nonneg_left hH_nonneg (by norm_num) hs_ge_one
      _ = X ^ P.θ := by ring
  exact le_trans hmul hendpoint

/-- If `k≤U₁`, the scaled quotient window still begins at least at
`X^(λ-θ)`.  This is the large-tail scale lower endpoint used when the ordinary
squarefree progression estimate is applied beyond the manuscript power cutoff. -/
theorem phiProgressionU0_div_nat_ge_rpow_lam_sub_theta_of_le_floor_U1
    (P : Params) {X : ℝ} {s k : ℕ} (hX : 1 ≤ X) (hs : 1 ≤ s)
    (hk_pos : 1 ≤ k) (hk : k ≤ ⌊phiProgressionU1 P s X⌋₊) :
    X ^ (P.lam - P.θ) ≤ phiProgressionU0 P s X / (k : ℝ) := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hk_pos_nat : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk_pos
  have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos_nat
  have hk_posR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos_nat
  have hsk_pos : (0 : ℝ) < ((s * k : ℕ) : ℝ) := by
    exact_mod_cast mul_pos hs_pos_nat hk_pos_nat
  have hden_le :
      ((s * k : ℕ) : ℝ) ≤ X ^ P.θ :=
    phiProgression_sk_le_rpow_theta_of_le_floor_U1 P hXpos hs hk
  have hY_nonneg : 0 ≤ X ^ P.lam := (Real.rpow_pos_of_pos hXpos P.lam).le
  calc
    X ^ (P.lam - P.θ) = X ^ P.lam / X ^ P.θ := by
      rw [Real.rpow_sub hXpos]
    _ ≤ X ^ P.lam / ((s * k : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left hY_nonneg hsk_pos hden_le
    _ = phiProgressionU0 P s X / (k : ℝ) := by
      unfold phiProgressionU0 Y0Scale
      rw [Nat.cast_mul]
      field_simp [ne_of_gt hs_pos, ne_of_gt hk_posR]

/-- Product form of the elementary power-scale bookkeeping used when the
ordinary squarefree progression estimate is applied after fixing a divisor. -/
theorem nat_cast_mul_le_rpow_add_of_le_rpow
    {X a b : ℝ} {m n : ℕ} (hX : 0 < X)
    (hm : (m : ℝ) ≤ X ^ a) (hn : (n : ℝ) ≤ X ^ b) :
    ((m * n : ℕ) : ℝ) ≤ X ^ (a + b) := by
  have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have ha_nonneg : 0 ≤ X ^ a := (Real.rpow_pos_of_pos hX a).le
  calc
    ((m * n : ℕ) : ℝ) = (m : ℝ) * (n : ℝ) := by norm_num
    _ ≤ X ^ a * X ^ b := mul_le_mul hm hn hn_nonneg ha_nonneg
    _ = X ^ (a + b) := by rw [← Real.rpow_add hX]

/-- In the small-divisor range `k≤X^κ`, the auxiliary squarefree modulus `s*k`
has size at most `X^(η+κ)`. -/
theorem phiProgression_sk_le_rpow_eta_add_kappa
    (P : Params) {X κ : ℝ} {s k : ℕ} (hX : 1 ≤ X)
    (hsS : (s : ℝ) ≤ SScale P X) (hkX : (k : ℝ) ≤ X ^ κ) :
    ((s * k : ℕ) : ℝ) ≤ X ^ (P.η + κ) := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hs_le : (s : ℝ) ≤ X ^ P.η := by
    simpa [SScale] using hsS
  exact nat_cast_mul_le_rpow_add_of_le_rpow hXpos hs_le hkX

/-- The manuscript's power cutoff for the small-divisor side of
`lem:phi-progression-average`: `K=⌊X^κ⌋₊`. -/
noncomputable def phiProgressionPowerCutoff
    (κ : ℝ) (X : ℝ) (_d _s : ℕ) : ℕ :=
  ⌊X ^ κ⌋₊

/-- A real number at least two has natural floor at least half its size. -/
theorem half_le_nat_floor_of_two_le {t : ℝ} (ht : 2 ≤ t) :
    t / 2 ≤ (⌊t⌋₊ : ℝ) := by
  have hsub : t - 1 < (⌊t⌋₊ : ℝ) := Nat.sub_one_lt_floor t
  have hhalf : t / 2 ≤ t - 1 := by linarith
  exact hhalf.trans hsub.le

/-- Explicit threshold ensuring that a positive real power is at least two. -/
theorem two_le_rpow_of_exp_log_two_div_le
    {X κ : ℝ} (hκ : 0 < κ)
    (hX : Real.exp (Real.log 2 / κ) ≤ X) :
    2 ≤ X ^ κ := by
  have hbase : 0 < Real.exp (Real.log 2 / κ) := Real.exp_pos _
  have hXpos : 0 < X := lt_of_lt_of_le hbase hX
  have hlog : Real.log 2 / κ ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hX
  have hmul := mul_le_mul_of_nonneg_left hlog hκ.le
  have hκne : κ ≠ 0 := ne_of_gt hκ
  have hlogpow : Real.log 2 ≤ κ * Real.log X := by
    convert hmul using 1
    · field_simp [hκne]
  rw [Real.rpow_def_of_pos hXpos]
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Negative powers of the natural floor of `X^κ` retain the expected power
saving, with only the explicit factor `2^a`. -/
theorem nat_floor_rpow_neg_le
    {X κ a : ℝ} (hκ : 0 < κ) (ha : 0 < a)
    (hX : Real.exp (Real.log 2 / κ) ≤ X) :
    ((⌊X ^ κ⌋₊ : ℕ) : ℝ) ^ (-a) ≤
      (2 : ℝ) ^ a * X ^ (-(κ * a)) := by
  have hpow2 : 2 ≤ X ^ κ :=
    two_le_rpow_of_exp_log_two_div_le hκ hX
  have hhalf : X ^ κ / 2 ≤ (⌊X ^ κ⌋₊ : ℝ) :=
    half_le_nat_floor_of_two_le hpow2
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hpowpos : 0 < X ^ κ := Real.rpow_pos_of_pos hXpos κ
  have hhalfpos : 0 < X ^ κ / 2 := div_pos hpowpos (by norm_num)
  have hneg : -a ≤ 0 := by linarith
  calc
    ((⌊X ^ κ⌋₊ : ℕ) : ℝ) ^ (-a)
        ≤ (X ^ κ / 2) ^ (-a) :=
          Real.rpow_le_rpow_of_nonpos hhalfpos hhalf hneg
    _ = (2 : ℝ) ^ a * X ^ (-(κ * a)) := by
      rw [div_eq_mul_inv,
        Real.mul_rpow (Real.rpow_nonneg hXpos.le κ)
          (by positivity : (0 : ℝ) ≤ 2⁻¹)]
      rw [← Real.rpow_mul hXpos.le]
      rw [Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      rw [inv_inv]
      rw [show κ * -a = -(κ * a) by ring]
      ring

/-- Membership in the power-cutoff small-divisor range gives the advertised
real inequality `k ≤ X^κ`. -/
theorem nat_cast_le_rpow_of_mem_Icc_phiProgressionPowerCutoff
    {X κ : ℝ} {d s k : ℕ} (hX : 0 ≤ X)
    (hk : k ∈ Finset.Icc (1 : ℕ) (phiProgressionPowerCutoff κ X d s)) :
    (k : ℝ) ≤ X ^ κ := by
  have hcut_nonneg : 0 ≤ X ^ κ := Real.rpow_nonneg hX κ
  have hk_floor : k ≤ phiProgressionPowerCutoff κ X d s :=
    (Finset.mem_Icc.mp hk).2
  exact le_trans (by exact_mod_cast hk_floor) (Nat.floor_le hcut_nonneg)

/-- The power cutoff itself is bounded by its defining real scale. -/
theorem nat_cast_phiProgressionPowerCutoff_le_rpow
    {X κ : ℝ} {d s : ℕ} (hX : 0 ≤ X) :
    (phiProgressionPowerCutoff κ X d s : ℝ) ≤ X ^ κ := by
  exact Nat.floor_le (Real.rpow_nonneg hX κ)

/-- Power-cutoff version of `phiProgression_sk_le_rpow_eta_add_kappa`. -/
theorem phiProgression_sk_le_rpow_eta_add_kappa_of_mem_powerCutoff
    (P : Params) {X κ : ℝ} {d s k : ℕ} (hX : 1 ≤ X)
    (hsS : (s : ℝ) ≤ SScale P X)
    (hk : k ∈ Finset.Icc (1 : ℕ) (phiProgressionPowerCutoff κ X d s)) :
    ((s * k : ℕ) : ℝ) ≤ X ^ (P.η + κ) := by
  exact phiProgression_sk_le_rpow_eta_add_kappa P hX hsS
    (nat_cast_le_rpow_of_mem_Icc_phiProgressionPowerCutoff
      (le_trans zero_le_one hX) hk)

/-- The full local modulus product `d*s*k` is bounded by the paper's polylog
progression scale times the small-divisor squarefree scale. -/
theorem phiProgression_dsk_le_UScale_mul_rpow_eta_add_kappa
    (P : Params) {X κ : ℝ} {d s k : ℕ}
    (hdU : (d : ℝ) ≤ UScale X)
    (hsk : ((s * k : ℕ) : ℝ) ≤ X ^ (P.η + κ)) :
    ((d * (s * k) : ℕ) : ℝ) ≤ UScale X * X ^ (P.η + κ) := by
  have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hsk_nonneg : 0 ≤ ((s * k : ℕ) : ℝ) := by
    exact_mod_cast Nat.zero_le (s * k)
  have hU_nonneg : 0 ≤ UScale X := by
    unfold UScale
    positivity
  calc
    ((d * (s * k) : ℕ) : ℝ) = (d : ℝ) * ((s * k : ℕ) : ℝ) := by norm_num
    _ ≤ UScale X * X ^ (P.η + κ) :=
      mul_le_mul hdU hsk hsk_nonneg hU_nonneg

/-- Cutoff-specialized version of the `d*s*k` scale bound. -/
theorem phiProgression_dsk_le_UScale_mul_rpow_eta_add_kappa_of_mem_powerCutoff
    (P : Params) {X κ : ℝ} {d s k : ℕ} (hX : 1 ≤ X)
    (hdU : (d : ℝ) ≤ UScale X) (hsS : (s : ℝ) ≤ SScale P X)
    (hk : k ∈ Finset.Icc (1 : ℕ) (phiProgressionPowerCutoff κ X d s)) :
    ((d * (s * k) : ℕ) : ℝ) ≤ UScale X * X ^ (P.η + κ) :=
  phiProgression_dsk_le_UScale_mul_rpow_eta_add_kappa P
    hdU
    (phiProgression_sk_le_rpow_eta_add_kappa_of_mem_powerCutoff P hX hsS hk)

/-- Power-cutoff version of the fixed-`k` lower-endpoint scale bound.  This is
the deterministic scale reduction used before applying a standard progression
estimate in the range `k≤X^κ`. -/
theorem phiProgressionU0_div_nat_ge_rpow_lam_sub_eta_sub_of_mem_powerCutoff
    (P : Params) {X κ : ℝ} {d s k : ℕ} (hX : 1 ≤ X) (hs : 1 ≤ s)
    (hsS : (s : ℝ) ≤ SScale P X)
    (hk : k ∈ Finset.Icc (1 : ℕ) (phiProgressionPowerCutoff κ X d s)) :
    X ^ (P.lam - P.η - κ) ≤ phiProgressionU0 P s X / (k : ℝ) := by
  have hX_nonneg : 0 ≤ X := le_trans (by norm_num : (0 : ℝ) ≤ 1) hX
  exact phiProgressionU0_div_nat_ge_rpow_lam_sub_eta_sub
    P hX hs (Finset.mem_Icc.mp hk).1 hsS
    (nat_cast_le_rpow_of_mem_Icc_phiProgressionPowerCutoff hX_nonneg hk)


/-- Multiplying an existing local modulus by a coprime factor cannot increase
the Euler density `φ(n)/n`.  This is the arithmetic density comparison used
after fixing a divisor `k` in the upper half of
`lem:phi-progression-average`. -/
theorem totient_mul_ratio_le_left_of_coprime
    {s k : ℕ} (hs : 0 < s) (hk : 0 < k) (hsk : Nat.Coprime s k) :
    (Nat.totient (s * k) : ℝ) / (s * k : ℝ) ≤
      (Nat.totient s : ℝ) / (s : ℝ) := by
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have htot_mul : Nat.totient (s * k) = Nat.totient s * Nat.totient k :=
    Nat.totient_mul hsk
  have htotk_le : (Nat.totient k : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.totient_le k
  have htotk_ratio_le_one : (Nat.totient k : ℝ) / (k : ℝ) ≤ 1 := by
    exact div_le_one_of_le₀ htotk_le hkR.le
  have hs_ratio_nonneg : 0 ≤ (Nat.totient s : ℝ) / (s : ℝ) := by
    exact div_nonneg (by exact_mod_cast Nat.zero_le (Nat.totient s)) hsR.le
  calc
    (Nat.totient (s * k) : ℝ) / (s * k : ℝ)
        = ((Nat.totient s : ℝ) / (s : ℝ)) *
            ((Nat.totient k : ℝ) / (k : ℝ)) := by
          rw [htot_mul]
          field_simp [ne_of_gt hsR, ne_of_gt hkR]
    _ ≤ ((Nat.totient s : ℝ) / (s : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left htotk_ratio_le_one hs_ratio_nonneg
    _ = (Nat.totient s : ℝ) / (s : ℝ) := by ring

/-- Weighted version of `totient_mul_ratio_le_left_of_coprime` in the shape
used by the local-density envelope: multiplying by the nonnegative progression
factor `1/d` and a nonnegative logarithmic length preserves the comparison. -/
theorem one_div_modulus_mul_totient_mul_ratio_log_le_left_of_coprime
    {d s k : ℕ} {L : ℝ}
    (hd : 0 < d) (hs : 0 < s) (hk : 0 < k)
    (hsk : Nat.Coprime s k) (hL : 0 ≤ L) :
    ((1 : ℝ) / (d : ℝ)) *
        ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) * L ≤
      ((1 : ℝ) / (d : ℝ)) *
        ((Nat.totient s : ℝ) / (s : ℝ)) * L := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hratio :=
    totient_mul_ratio_le_left_of_coprime (s := s) (k := k) hs hk hsk
  have hfactor_nonneg : 0 ≤ ((1 : ℝ) / (d : ℝ)) * L :=
    mul_nonneg (div_nonneg zero_le_one hdR.le) hL
  calc
    ((1 : ℝ) / (d : ℝ)) *
        ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) * L
        = (((1 : ℝ) / (d : ℝ)) * L) *
            ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) := by ring
    _ ≤ (((1 : ℝ) / (d : ℝ)) * L) *
          ((Nat.totient s : ℝ) / (s : ℝ)) :=
        mul_le_mul_of_nonneg_left hratio hfactor_nonneg
    _ = ((1 : ℝ) / (d : ℝ)) *
          ((Nat.totient s : ℝ) / (s : ℝ)) * L := by ring

/-- The divisor-count function is monotone under the square map. -/
theorem tau_le_tau_square (s : ℕ) :
    Inputs.tau s ≤ Inputs.tau (s ^ 2) := by
  classical
  unfold Inputs.tau
  apply Finset.card_le_card
  intro d hd
  rw [Nat.mem_divisors] at hd ⊢
  rcases hd with ⟨hds, hs_ne⟩
  exact ⟨by simpa [pow_two] using dvd_mul_of_dvd_left hds s,
    pow_ne_zero 2 hs_ne⟩

/-- Unconditional lower bound for the local totient density on a fixed `s`.

This is deliberately weaker than Mertens but strong enough for the wide tensor
endpoint: `s / φ(s) ≤ τ(s) ≤ τ(s²) ≪ s^(1/4)`. -/
theorem totient_ratio_ge_inv_tauSquareQuarterConstant_mul_rpow_neg_quarter
    {s : ℕ} (hs : 1 ≤ s) :
    (1 / Inputs.tauSquareQuarterConstant) *
        (s : ℝ) ^ (-((1 : ℝ) / 4)) ≤
      (Nat.totient s : ℝ) / (s : ℝ) := by
  have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos_nat
  have htot_pos_nat : 0 < Nat.totient s := Nat.totient_pos.mpr hs_pos_nat
  have htot_pos : (0 : ℝ) < (Nat.totient s : ℝ) := by exact_mod_cast htot_pos_nat
  have hC_pos : 0 < Inputs.tauSquareQuarterConstant := by
    dsimp [Inputs.tauSquareQuarterConstant]
    positivity
  have htau_le_sq : (Inputs.tau s : ℝ) ≤ (Inputs.tau (s ^ 2) : ℝ) := by
    exact_mod_cast tau_le_tau_square s
  have htau_sq :
      (Inputs.tau (s ^ 2) : ℝ) ≤
        Inputs.tauSquareQuarterConstant * (s : ℝ) ^ ((1 : ℝ) / 4) :=
    Inputs.tau_square_le_const_rpow_quarter hs
  have hratio_le :
      (s : ℝ) / (Nat.totient s : ℝ) ≤
        Inputs.tauSquareQuarterConstant * (s : ℝ) ^ ((1 : ℝ) / 4) :=
    (Inputs.div_totient_le_tau s hs_pos_nat).trans (htau_le_sq.trans htau_sq)
  have hleft_pos :
      0 < (s : ℝ) / (Nat.totient s : ℝ) :=
    div_pos hs_pos htot_pos
  have hright_pos :
      0 < Inputs.tauSquareQuarterConstant * (s : ℝ) ^ ((1 : ℝ) / 4) :=
    mul_pos hC_pos (Real.rpow_pos_of_pos hs_pos ((1 : ℝ) / 4))
  have hinv :
      (1 : ℝ) /
          (Inputs.tauSquareQuarterConstant * (s : ℝ) ^ ((1 : ℝ) / 4)) ≤
        (1 : ℝ) / ((s : ℝ) / (Nat.totient s : ℝ)) :=
    one_div_le_one_div_of_le hleft_pos hratio_le
  calc
    (1 / Inputs.tauSquareQuarterConstant) *
        (s : ℝ) ^ (-((1 : ℝ) / 4))
        =
      (1 : ℝ) /
          (Inputs.tauSquareQuarterConstant * (s : ℝ) ^ ((1 : ℝ) / 4)) := by
        rw [Real.rpow_neg hs_pos.le]
        field_simp [ne_of_gt hC_pos, ne_of_gt (Real.rpow_pos_of_pos hs_pos ((1 : ℝ) / 4))]
    _ ≤ (1 : ℝ) / ((s : ℝ) / (Nat.totient s : ℝ)) := hinv
    _ = (Nat.totient s : ℝ) / (s : ℝ) := by
        field_simp [ne_of_gt hs_pos, ne_of_gt htot_pos]

/-- The lower endpoint in `lem:phi-progression-average` is positive whenever
`X` and `s` are positive. -/
theorem phiProgressionU0_pos
    (P : Params) {X : ℝ} {s : ℕ} (hX : 0 < X) (hs : 0 < s) :
    0 < phiProgressionU0 P s X := by
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  unfold phiProgressionU0
  exact div_pos (Real.rpow_pos_of_pos hX P.lam) hsR

/-- Deterministic endpoint ordering for `lem:phi-progression-average`.
The paper's range condition `s ≤ X^η`, together with `λ+η<θ`, forces
`Y₀/s < H/s²` once `X>1`. -/
theorem phiProgressionU0_lt_U1_of_s_le_SScale
    (P : Params) {X : ℝ} {s : ℕ}
    (hX : 1 < X) (hs : 1 ≤ s) (hsS : (s : ℝ) ≤ SScale P X) :
    phiProgressionU0 P s X < phiProgressionU1 P s X := by
  have hXpos : 0 < X := lt_trans zero_lt_one hX
  have hspos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hspos_nat
  have hY0pos : 0 < Y0Scale P X := Real.rpow_pos_of_pos hXpos P.lam
  have hY0S_lt_H : Y0Scale P X * SScale P X < HScale P X := by
    unfold Y0Scale SScale HScale
    calc
      X ^ P.lam * X ^ P.η = X ^ (P.lam + P.η) := by
        rw [← Real.rpow_add hXpos]
      _ < X ^ P.θ :=
        Real.rpow_lt_rpow_of_exponent_lt hX P.lam_add_η_lt_θ
  have hY0s_lt_H : Y0Scale P X * (s : ℝ) < HScale P X :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hsS hY0pos.le) hY0S_lt_H
  have hs_sq_pos : 0 < (s : ℝ) ^ (2 : ℕ) := sq_pos_of_pos hspos
  unfold phiProgressionU0 phiProgressionU1
  calc
    Y0Scale P X / (s : ℝ)
        = (Y0Scale P X * (s : ℝ)) / (s : ℝ) ^ (2 : ℕ) := by
          field_simp [ne_of_gt hspos]
          ring
    _ < HScale P X / (s : ℝ) ^ (2 : ℕ) :=
        div_lt_div_of_pos_right hY0s_lt_H hs_sq_pos

/-- Removing the fixed-divisor scaling from the reciprocal lower endpoint. -/
theorem one_div_phiProgressionU0_div_nat
    (P : Params) {X : ℝ} {s k : ℕ}
    (hU0 : phiProgressionU0 P s X ≠ 0) (hk : 0 < k) :
    (1 : ℝ) / (phiProgressionU0 P s X / (k : ℝ)) =
      (k : ℝ) * (1 / phiProgressionU0 P s X) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  field_simp [hU0, hkR]

/-- The logarithmic quotient length is unchanged by the fixed-divisor scaling
`Uᵢ ↦ Uᵢ/k`. -/
theorem log_phiProgression_scaled_quotient_eq
    (P : Params) {X : ℝ} {s k : ℕ}
    (hU0 : phiProgressionU0 P s X ≠ 0) (hk : 0 < k) :
    Real.log
        ((phiProgressionU1 P s X / (k : ℝ)) /
          (phiProgressionU0 P s X / (k : ℝ))) =
      Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  congr 1
  field_simp [hU0, hkR]

/-- Common finite support for the reciprocal-`φ` progression in
`lem:phi-progression-average`. -/
noncomputable def phiProgressionSupport
    (P : Params) (X : ℝ) (d a s : ℕ) : Finset ℕ := by
  classical
  exact
    (Inputs.natWindow (phiProgressionU0 P s X)
      (phiProgressionU1 P s X)).filter
      (fun r => Squarefree r ∧ Nat.Coprime r s ∧ Inputs.congMod r a d)

/-- Divisor-sigma support associated to `phiProgressionSupport`: points are
ordered pairs `(r,k)` with `r` in the progression support and `k | r`. -/
noncomputable def phiProgressionDivisorSigmaSupport
    (P : Params) (X : ℝ) (d a s : ℕ) : Finset (Sigma fun _r : ℕ => ℕ) := by
  classical
  exact (phiProgressionSupport P X d a s).sigma (fun r => r.divisors)

/-- The bare reciprocal progression carrier used in the lower-bound half of
`lem:phi-progression-average`:
`∑_{U₀<r≤U₁, r squarefree, (r,s)=1, r≡a (mod d)} 1/r`. -/
noncomputable def phiProgressionBareAverage
    (P : Params) (X : ℝ) (d a s : ℕ) : ℝ := by
  classical
  exact
    ∑ r ∈ (Inputs.natWindow (phiProgressionU0 P s X)
        (phiProgressionU1 P s X)).filter
        (fun r => Squarefree r ∧ Nat.Coprime r s ∧ Inputs.congMod r a d),
      (1 : ℝ) / (r : ℝ)

/-- The `τ(r)/r` majorant carrier for the upper-bound half of
`lem:phi-progression-average`.  It is the exact finite support of the
reciprocal-`φ` progression, with the manuscript's elementary replacement
`r/φ(r) ≤ τ(r)` applied to each summand. -/
noncomputable def phiProgressionTauAverage
    (P : Params) (X : ℝ) (d a s : ℕ) : ℝ := by
  classical
  exact
    ∑ r ∈ (Inputs.natWindow (phiProgressionU0 P s X)
        (phiProgressionU1 P s X)).filter
        (fun r => Squarefree r ∧ Nat.Coprime r s ∧ Inputs.congMod r a d),
      (Inputs.tau r : ℝ) / (r : ℝ)

/-- Divisor-expanded form of the `τ(r)/r` majorant carrier.  This is the exact
finite-sum bookkeeping behind the upper-bound split in
`lem:phi-progression-average`; later estimates can interchange the `r`- and
`k`-sums from this form. -/
noncomputable def phiProgressionTauDivisorAverage
    (P : Params) (X : ℝ) (d a s : ℕ) : ℝ := by
  classical
  exact
    ∑ r ∈ (Inputs.natWindow (phiProgressionU0 P s X)
        (phiProgressionU1 P s X)).filter
        (fun r => Squarefree r ∧ Nat.Coprime r s ∧ Inputs.congMod r a d),
      ∑ _k ∈ r.divisors, (1 : ℝ) / (r : ℝ)

/-- Sigma-indexed form of the `τ(r)/r` majorant carrier.  This is the same
finite set as `phiProgressionTauDivisorAverage`, but with the divisor index
exposed as a first-class pair `(r,k)` for later support transformations. -/
noncomputable def phiProgressionTauSigmaAverage
    (P : Params) (X : ℝ) (d a s : ℕ) : ℝ := by
  classical
  exact
    ∑ x ∈ ((Inputs.natWindow (phiProgressionU0 P s X)
        (phiProgressionU1 P s X)).filter
        (fun r => Squarefree r ∧ Nat.Coprime r s ∧ Inputs.congMod r a d)).sigma
        (fun r => r.divisors),
      (1 : ℝ) / (x.1 : ℝ)

/-- Quotient-split form of the `τ(r)/r` upper carrier.  The same sigma support
is used, but the summand is written as `1/(k·t)` with `k = x.2` and
`t = x.1 / x.2`; the equality `x.1 = x.2 * (x.1 / x.2)` is proved below from
`x.2 ∈ x.1.divisors`. -/
noncomputable def phiProgressionTauQuotientAverage
    (P : Params) (X : ℝ) (d a s : ℕ) : ℝ := by
  classical
  exact
    ∑ x ∈ ((Inputs.natWindow (phiProgressionU0 P s X)
        (phiProgressionU1 P s X)).filter
        (fun r => Squarefree r ∧ Nat.Coprime r s ∧ Inputs.congMod r a d)).sigma
        (fun r => r.divisors),
      (1 : ℝ) / ((x.2 : ℝ) * ((x.1 / x.2 : ℕ) : ℝ))

/-- The manuscript's divisor-expansion weight
`γ(k)=∏_{p|k} 1/(p-1)`.  It is packaged as an arithmetic function so Mathlib's
squarefree prime-factor expansion lemmas can be used directly. -/
noncomputable def phiGammaAF : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p : ℕ => (1 : ℝ) / ((p : ℝ) - 1))

/-- Function form of the manuscript's `γ(k)` weight. -/
noncomputable def phiGamma (k : ℕ) : ℝ :=
  phiGammaAF k

/-- Squarefree kernel/radical of `k`, written as the product of distinct prime
factors. -/
noncomputable def primeRad (k : ℕ) : ℕ :=
  ∏ p ∈ k.primeFactors, p

/-- The reciprocal-`φ` progression carrier after applying the manuscript's
squarefree divisor expansion
`1/φ(r) = (1/r)∑_{k|r}γ(k)`. -/
noncomputable def phiProgressionGammaAverage
    (P : Params) (X : ℝ) (d a s : ℕ) : ℝ := by
  classical
  exact
    ∑ r ∈ (Inputs.natWindow (phiProgressionU0 P s X)
        (phiProgressionU1 P s X)).filter
        (fun r => Squarefree r ∧ Nat.Coprime r s ∧ Inputs.congMod r a d),
      (1 / (r : ℝ)) * ∑ k ∈ r.divisors, phiGamma k

/-- Sigma-indexed form of the manuscript's `γ(k)` expansion:
`∑_{r}\sum_{k|r} γ(k)/r`. -/
noncomputable def phiProgressionGammaSigmaAverage
    (P : Params) (X : ℝ) (d a s : ℕ) : ℝ := by
  classical
  exact
    ∑ x ∈ phiProgressionDivisorSigmaSupport P X d a s,
      phiGamma x.2 / (x.1 : ℝ)

/-- Quotient-split form of the `γ(k)` expansion after writing `r=k·t`. -/
noncomputable def phiProgressionGammaQuotientAverage
    (P : Params) (X : ℝ) (d a s : ℕ) : ℝ := by
  classical
  exact
    ∑ x ∈ phiProgressionDivisorSigmaSupport P X d a s,
      phiGamma x.2 / ((x.2 : ℝ) * ((x.1 / x.2 : ℕ) : ℝ))

/-- Small-divisor part of the quotient-split gamma carrier, cut at `K`.
This is the finite carrier used when the manuscript applies the ordinary
squarefree progression estimate after fixing `k`. -/
noncomputable def phiProgressionGammaSmallQuotientAverage
    (P : Params) (X : ℝ) (d a s K : ℕ) : ℝ := by
  classical
  exact
    ∑ x ∈ (phiProgressionDivisorSigmaSupport P X d a s).filter
        (fun x => x.2 ≤ K),
      phiGamma x.2 / ((x.2 : ℝ) * ((x.1 / x.2 : ℕ) : ℝ))

/-- Fixed-divisor fiber of the small gamma quotient carrier.  For a fixed
`k`, this is the part of the divisor expansion with exposed divisor `x.2 = k`;
the next analytic step compares this fiber to an ordinary squarefree reciprocal
progression in the quotient variable `t=x.1/k`. -/
noncomputable def phiProgressionGammaFixedKQuotientAverage
    (P : Params) (X : ℝ) (d a s k : ℕ) : ℝ := by
  classical
  exact
    ∑ x ∈ (phiProgressionDivisorSigmaSupport P X d a s).filter
        (fun x => x.2 = k),
      phiGamma x.2 / ((x.2 : ℝ) * ((x.1 / x.2 : ℕ) : ℝ))

/-- Reciprocal quotient carrier inside a fixed-divisor gamma fiber.  This is
the same finite fiber as `phiProgressionGammaFixedKQuotientAverage`, but with
the arithmetic weight `γ(k)/k` removed from the summand. -/
noncomputable def phiProgressionFixedKQuotientRecipFiber
    (P : Params) (X : ℝ) (d a s k : ℕ) : ℝ := by
  classical
  exact
    ∑ x ∈ (phiProgressionDivisorSigmaSupport P X d a s).filter
        (fun x => x.2 = k),
      (1 : ℝ) / ((x.1 / x.2 : ℕ) : ℝ)

/-- Fiber-summed form of the small gamma quotient carrier. -/
noncomputable def phiProgressionGammaSmallFiberSum
    (P : Params) (X : ℝ) (d a s K : ℕ) : ℝ := by
  classical
  exact
    ∑ k ∈ Finset.Icc (1 : ℕ) K,
      phiProgressionGammaFixedKQuotientAverage P X d a s k

/-- Small gamma carrier after factoring each fixed-divisor fiber as
`(γ(k)/k)` times a reciprocal quotient-fiber sum. -/
noncomputable def phiProgressionGammaSmallWeightedRecipFiberSum
    (P : Params) (X : ℝ) (d a s K : ℕ) : ℝ := by
  classical
  exact
    ∑ k ∈ Finset.Icc (1 : ℕ) K,
      (phiGamma k / (k : ℝ)) *
        phiProgressionFixedKQuotientRecipFiber P X d a s k

/-- Model small-gamma upper carrier after replacing every fixed-`k` quotient
fiber by the corresponding ordinary squarefree reciprocal progression carrier.
The function `B` chooses an inverse residue for each `k` modulo `d`. -/
noncomputable def phiProgressionGammaSmallSqfRecipModelSum
    (P : Params) (X : ℝ) (d a s K : ℕ) (B : ℕ → ℕ) : ℝ := by
  classical
  exact
    ∑ k ∈ Finset.Icc (1 : ℕ) K,
      (phiGamma k / (k : ℝ)) *
        Inputs.sqfRecip X (s * k) d (a * B k)
          (phiProgressionU0 P s X / (k : ℝ))
          (phiProgressionU1 P s X / (k : ℝ))

/-- A harmless global choice of inverse residue: if an inverse exists modulo
`d`, choose one, otherwise use `0`.  Later theorems only use the specification
on coprime pairs, where the inverse exists. -/
noncomputable def modInverseChoice (d k : ℕ) : ℕ := by
  classical
  exact if h : ∃ b : ℕ, k * b ≡ 1 [MOD d] then Classical.choose h else 0

/-- Specification of `modInverseChoice` whenever an inverse exists. -/
theorem modInverseChoice_spec {d k : ℕ}
    (h : ∃ b : ℕ, k * b ≡ 1 [MOD d]) :
    k * modInverseChoice d k ≡ 1 [MOD d] := by
  classical
  unfold modInverseChoice
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- A number coprime to a positive modulus has a multiplicative inverse modulo
that modulus.  The modulus-one edge case is handled separately. -/
theorem exists_mul_modEq_one_of_coprime
    {d k : ℕ} (hd : 0 < d) (hk : Nat.Coprime k d) :
    ∃ b : ℕ, k * b ≡ 1 [MOD d] := by
  classical
  by_cases hd_one : d = 1
  · subst d
    exact ⟨0, by simp [Nat.ModEq]⟩
  · have hd_gt_one : 1 < d :=
      lt_of_le_of_ne (Nat.succ_le_of_lt hd) (Ne.symm hd_one)
    obtain ⟨b, hb⟩ := Nat.exists_mul_emod_eq_one_of_coprime
      (k := d) (n := k) hk hd_gt_one
    refine ⟨b, ?_⟩
    rw [Nat.ModEq, hb, Nat.mod_eq_of_lt hd_gt_one]

/-- The chosen inverse is a genuine inverse for coprime pairs. -/
theorem modInverseChoice_coprime {d k : ℕ}
    (hd : 0 < d) (hk : Nat.Coprime k d) :
    k * modInverseChoice d k ≡ 1 [MOD d] :=
  modInverseChoice_spec (exists_mul_modEq_one_of_coprime hd hk)

/-- The chosen inverse residue is itself reduced modulo `d`. -/
theorem modInverseChoice_value_coprime {d k : ℕ}
    (hd : 0 < d) (hk : Nat.Coprime k d) :
    Nat.Coprime (modInverseChoice d k) d := by
  have hcong : k * modInverseChoice d k ≡ 1 [MOD d] :=
    modInverseChoice_coprime hd hk
  have hprod : Nat.Coprime (k * modInverseChoice d k) d := by
    rw [Nat.coprime_iff_gcd_eq_one]
    rw [hcong.gcd_eq]
    simp
  exact hprod.coprime_dvd_left (dvd_mul_left _ _)

/-- Canonical inverse-square residue used by the exact-divisor tensor model.

For positive `D` and `(s,D)=1`, this is `s⁻² (mod D)` using
`modInverseChoice`.  The zero-modulus branch is harmless and makes the reduced
residue lemma total in `D`. -/
noncomputable def exactDivisorInverseSquareResidue (D s : ℕ) : ℕ :=
  if D = 0 then 1 else (modInverseChoice D s) ^ (2 : ℕ)

/-- The canonical inverse-square residue is reduced modulo `D` whenever `s` is. -/
theorem exactDivisorInverseSquareResidue_coprime {D s : ℕ}
    (hsD : Nat.Coprime s D) :
    Nat.Coprime (exactDivisorInverseSquareResidue D s) D := by
  by_cases hD0 : D = 0
  · subst D
    simp [exactDivisorInverseSquareResidue]
  · have hDpos : 0 < D := Nat.pos_of_ne_zero hD0
    have hinv : Nat.Coprime (modInverseChoice D s) D :=
      modInverseChoice_value_coprime hDpos hsD
    simpa [exactDivisorInverseSquareResidue, hD0] using hinv

/-- Global selector form of the canonical inverse-square residue. -/
noncomputable def exactDivisorInverseSquareResidueSelector
    (_X : ℝ) (D s : ℕ) : ℕ :=
  exactDivisorInverseSquareResidue D s

/-- The canonical inverse-square selector satisfies the event bridge's reduced
residue side condition. -/
theorem exactDivisorInverseSquareResidueSelector_coprime
    (X : ℝ) (D s : ℕ) (hsD : Nat.Coprime s D) :
    Nat.Coprime (exactDivisorInverseSquareResidueSelector X D s) D :=
  exactDivisorInverseSquareResidue_coprime hsD

/-- Paper-shaped inverse-square residue selector with a fixed reduced multiplier.

For positive `D`, this is the class `c X D * s⁻² (mod D)`.  The zero-modulus
branch keeps the bridge total, so later event theorems do not need a separate
edge-case hypothesis just to feed the finite residue map. -/
noncomputable def exactDivisorTwistedInverseSquareResidueSelector
    (c : ℝ → ℕ → ℕ) (X : ℝ) (D s : ℕ) : ℕ :=
  if D = 0 then 1 else c X D * exactDivisorInverseSquareResidue D s

/-- The paper-shaped `c·s⁻²` selector is reduced modulo `D` whenever `c` is
reduced modulo every positive `D` and `s` is reduced modulo `D`. -/
theorem exactDivisorTwistedInverseSquareResidueSelector_coprime
    (c : ℝ → ℕ → ℕ)
    (hc : ∀ X D, 0 < D → Nat.Coprime (c X D) D)
    (X : ℝ) (D s : ℕ) (hsD : Nat.Coprime s D) :
    Nat.Coprime (exactDivisorTwistedInverseSquareResidueSelector c X D s) D := by
  by_cases hD0 : D = 0
  · subst D
    simp [exactDivisorTwistedInverseSquareResidueSelector]
  · have hDpos : 0 < D := Nat.pos_of_ne_zero hD0
    have hcD : Nat.Coprime (c X D) D := hc X D hDpos
    have hinv : Nat.Coprime (exactDivisorInverseSquareResidue D s) D :=
      exactDivisorInverseSquareResidue_coprime hsD
    simp [exactDivisorTwistedInverseSquareResidueSelector, hD0]
    rw [Nat.coprime_mul_iff_left]
    exact ⟨hcD, hinv⟩

/-- Coprime-restricted model small-gamma upper carrier.  Divisors `k` not
coprime to `d` cannot occur in the original fiber when `a` is reduced modulo
`d`; this model records only the residue classes for the occurring fibers. -/
noncomputable def phiProgressionGammaSmallSqfRecipCoprimeModelSum
    (P : Params) (X : ℝ) (d a s K : ℕ) (B : ℕ → ℕ) : ℝ := by
  classical
  exact
    ∑ k ∈ Finset.Icc (1 : ℕ) K,
      if Nat.Coprime k d then
        (phiGamma k / (k : ℝ)) *
          Inputs.sqfRecip X (s * k) d (a * B k)
            (phiProgressionU0 P s X / (k : ℝ))
            (phiProgressionU1 P s X / (k : ℝ))
      else 0

/-- Canonical-inverse version of the coprime-restricted model. -/
noncomputable def phiProgressionGammaSmallSqfRecipCoprimeInverseModelSum
    (P : Params) (X : ℝ) (d a s K : ℕ) : ℝ :=
  phiProgressionGammaSmallSqfRecipCoprimeModelSum P X d a s K
    (fun k => modInverseChoice d k)

/-- Admissible-divisor model small-gamma carrier.  The original fiber can only
contain divisors `k` coprime to both `d` and `s`; non-admissible `k` are
recorded as zero. -/
noncomputable def phiProgressionGammaSmallSqfRecipAdmissibleInverseModelSum
    (P : Params) (X : ℝ) (d a s K : ℕ) : ℝ := by
  classical
  exact
    ∑ k ∈ Finset.Icc (1 : ℕ) K,
      if Nat.Coprime k d ∧ Nat.Coprime k s then
        (phiGamma k / (k : ℝ)) *
          Inputs.sqfRecip X (s * k) d (a * modInverseChoice d k)
            (phiProgressionU0 P s X / (k : ℝ))
            (phiProgressionU1 P s X / (k : ℝ))
      else 0

/-- Elementary progression-envelope majorant for the admissible small-gamma
`sqfRecip` model.  This is the result of applying the unconditional endpoint
bound `sqfRecip_le_log_plus_inv` to each fixed `k`; the sharper manuscript step
is precisely to replace this envelope by the local-density
`φ(sk)/(sk)` estimate and then sum the convergent gamma weights. -/
noncomputable def phiProgressionGammaSmallAdmissibleElementaryEnvelopeSum
    (P : Params) (X : ℝ) (d s K : ℕ) : ℝ := by
  classical
  exact
    ∑ k ∈ Finset.Icc (1 : ℕ) K,
      if Nat.Coprime k d ∧ Nat.Coprime k s then
        (phiGamma k / (k : ℝ)) *
          (1 / (phiProgressionU0 P s X / (k : ℝ)) +
            (1 / (d : ℝ)) *
              Real.log
                ((phiProgressionU1 P s X / (k : ℝ)) /
                  (phiProgressionU0 P s X / (k : ℝ))))
      else 0

/-- Endpoint contribution in the normalized elementary fixed-`k` envelope.
This is the `1/(U₀/k)` part after cancelling the fixed-divisor scale. -/
noncomputable def phiProgressionGammaSmallAdmissibleElementaryEndpointEnvelopeSum
    (P : Params) (X : ℝ) (d s K : ℕ) : ℝ := by
  classical
  exact
    ∑ k ∈ Finset.Icc (1 : ℕ) K,
      if Nat.Coprime k d ∧ Nat.Coprime k s then
        phiGamma k * (1 / phiProgressionU0 P s X)
      else 0

/-- Logarithmic contribution in the normalized elementary fixed-`k` envelope.
This is the part carrying the common interval length `log(U₁/U₀)`. -/
noncomputable def phiProgressionGammaSmallAdmissibleElementaryLogEnvelopeSum
    (P : Params) (X : ℝ) (d s K : ℕ) : ℝ := by
  classical
  exact
    ∑ k ∈ Finset.Icc (1 : ℕ) K,
      if Nat.Coprime k d ∧ Nat.Coprime k s then
        (phiGamma k / (k : ℝ)) *
          ((1 / (d : ℝ)) *
            Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X))
      else 0

/-- Normalized split form of the elementary endpoint/log envelope.  The
scaled quotient window contributes only the endpoint factor `1/U₀` and the
common logarithmic length `log(U₁/U₀)`. -/
theorem phiProgressionGammaSmallAdmissibleElementaryEnvelopeSum_eq_endpoint_add_log
    (P : Params) (X : ℝ) (d s K : ℕ)
    (hU0 : phiProgressionU0 P s X ≠ 0) :
    phiProgressionGammaSmallAdmissibleElementaryEnvelopeSum P X d s K =
      phiProgressionGammaSmallAdmissibleElementaryEndpointEnvelopeSum P X d s K +
        phiProgressionGammaSmallAdmissibleElementaryLogEnvelopeSum P X d s K := by
  classical
  unfold phiProgressionGammaSmallAdmissibleElementaryEnvelopeSum
    phiProgressionGammaSmallAdmissibleElementaryEndpointEnvelopeSum
    phiProgressionGammaSmallAdmissibleElementaryLogEnvelopeSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
  · have hk_pos : 0 < k := (Finset.mem_Icc.mp hk).1
    have hkR_ne : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk_pos)
    rw [if_pos hadm, if_pos hadm, if_pos hadm]
    rw [one_div_phiProgressionU0_div_nat P hU0 hk_pos,
      log_phiProgression_scaled_quotient_eq P hU0 hk_pos]
    by_cases hdR : (d : ℝ) = 0
    · simp [hdR]
      field_simp [hkR_ne]
    · field_simp [hU0, hkR_ne, hdR]
      ring
  · simp [hadm]

/-- Finite admissible gamma coefficient attached to the endpoint part of the
elementary envelope. -/
noncomputable def phiProgressionGammaSmallAdmissibleGammaSum
    (d s K : ℕ) : ℝ := by
  classical
  exact
    ∑ k ∈ Finset.Icc (1 : ℕ) K,
      if Nat.Coprime k d ∧ Nat.Coprime k s then phiGamma k else 0

/-- Finite admissible `γ(k)/k` coefficient attached to the logarithmic part of
the elementary envelope. -/
noncomputable def phiProgressionGammaSmallAdmissibleGammaDivSum
    (d s K : ℕ) : ℝ := by
  classical
  exact
    ∑ k ∈ Finset.Icc (1 : ℕ) K,
      if Nat.Coprime k d ∧ Nat.Coprime k s then phiGamma k / (k : ℝ) else 0

/-- Full truncated `γ(k)/k` coefficient sum.  The admissible coefficient sum
in `lem:phi-progression-average` is a sub-sum of this nonnegative series. -/
noncomputable def phiGammaDivSum (K : ℕ) : ℝ := by
  classical
  exact ∑ k ∈ Finset.Icc (1 : ℕ) K, phiGamma k / (k : ℝ)

/-- One-dimensional large-tail coefficient sum for the pure
`2^ω(k)/k` majorant, truncated at the finite endpoint `N`.  This is the
coefficient side that remains after the large-divisor tail is separated from
the outer reciprocal progression carrier. -/
noncomputable def phiOmegaDivTailSum (K N : ℕ) : ℝ := by
  classical
  exact
    ∑ k ∈ (Finset.Icc (1 : ℕ) N).filter (fun k => ¬ k ≤ K),
      ((2 : ℝ) ^ Inputs.omega k) / (k : ℝ)

/-- The coefficient function `k ↦ 2^ω(k)/k²` used in the squarefree-reciprocal
large-tail reduction. -/
noncomputable def phiOmegaSqCoeff (k : ℕ) : ℝ :=
  ((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)

/-- One-dimensional large-tail coefficient sum for the squarefree-reciprocal
model after the fixed-`k` progression estimate has supplied one additional
factor `1/k`. -/
noncomputable def phiOmegaSqTailSum (K N : ℕ) : ℝ := by
  classical
  exact
    ∑ k ∈ (Finset.Icc (1 : ℕ) N).filter (fun k => ¬ k ≤ K),
      phiOmegaSqCoeff k

/-- Full truncated version of the one-dimensional square coefficient sum. -/
noncomputable def phiOmegaSqSum (N : ℕ) : ℝ := by
  classical
  exact ∑ k ∈ Finset.Icc (1 : ℕ) N, phiOmegaSqCoeff k

/-- Local-density coefficient sum for the large quotient-fiber tail after the
ordinary squarefree progression estimate is applied at fixed `k`.  The
remaining analytic summability is a one-dimensional tail with coefficient
`2^ω(k)/k²` and local density `φ(sk)/(sk)`. -/
noncomputable def phiProgressionOmegaLargeAdmissibleTotientCoeffSum
    (d s K N : ℕ) : ℝ := by
  classical
  exact
    ∑ k ∈ (Finset.Icc (1 : ℕ) N).filter (fun k => ¬ k ≤ K),
      if Nat.Coprime k d ∧ Nat.Coprime k s then
        (((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)) *
          ((Nat.totient (s * k) : ℝ) / (s * k : ℝ))
      else 0

/-- The endpoint envelope is the finite admissible gamma coefficient times the
common endpoint factor `1/U₀`. -/
theorem phiProgressionGammaSmallAdmissibleElementaryEndpointEnvelopeSum_eq_gammaSum_mul
    (P : Params) (X : ℝ) (d s K : ℕ) :
    phiProgressionGammaSmallAdmissibleElementaryEndpointEnvelopeSum P X d s K =
      phiProgressionGammaSmallAdmissibleGammaSum d s K *
        (1 / phiProgressionU0 P s X) := by
  classical
  unfold phiProgressionGammaSmallAdmissibleElementaryEndpointEnvelopeSum
    phiProgressionGammaSmallAdmissibleGammaSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
  · simp [hadm]
  · simp [hadm]

/-- The logarithmic envelope is the finite admissible `γ(k)/k` coefficient
times the common progression log factor. -/
theorem phiProgressionGammaSmallAdmissibleElementaryLogEnvelopeSum_eq_gammaDivSum_mul
    (P : Params) (X : ℝ) (d s K : ℕ) :
    phiProgressionGammaSmallAdmissibleElementaryLogEnvelopeSum P X d s K =
      phiProgressionGammaSmallAdmissibleGammaDivSum d s K *
        ((1 / (d : ℝ)) *
          Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)) := by
  classical
  unfold phiProgressionGammaSmallAdmissibleElementaryLogEnvelopeSum
    phiProgressionGammaSmallAdmissibleGammaDivSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
  · simp [hadm]
  · simp [hadm]

/-- Fully normalized coefficient form of the elementary fixed-`k` envelope. -/
theorem phiProgressionGammaSmallAdmissibleElementaryEnvelopeSum_eq_gammaSums
    (P : Params) (X : ℝ) (d s K : ℕ)
    (hU0 : phiProgressionU0 P s X ≠ 0) :
    phiProgressionGammaSmallAdmissibleElementaryEnvelopeSum P X d s K =
      phiProgressionGammaSmallAdmissibleGammaSum d s K *
          (1 / phiProgressionU0 P s X) +
        phiProgressionGammaSmallAdmissibleGammaDivSum d s K *
          ((1 / (d : ℝ)) *
            Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)) := by
  rw [phiProgressionGammaSmallAdmissibleElementaryEnvelopeSum_eq_endpoint_add_log
      P X d s K hU0,
    phiProgressionGammaSmallAdmissibleElementaryEndpointEnvelopeSum_eq_gammaSum_mul,
    phiProgressionGammaSmallAdmissibleElementaryLogEnvelopeSum_eq_gammaDivSum_mul]

/-- Large-divisor tail of the quotient-split gamma carrier, complementary to
`phiProgressionGammaSmallQuotientAverage`. -/
noncomputable def phiProgressionGammaLargeQuotientAverage
    (P : Params) (X : ℝ) (d a s K : ℕ) : ℝ := by
  classical
  exact
    ∑ x ∈ (phiProgressionDivisorSigmaSupport P X d a s).filter
        (fun x => ¬ x.2 ≤ K),
      phiGamma x.2 / ((x.2 : ℝ) * ((x.1 / x.2 : ℕ) : ℝ))

/-- Pure large-divisor tail majorant for the gamma quotient carrier, obtained
from the squarefree comparison `γ(k) ≤ 2^ω(k)/k`.  Bounding this carrier is the
analytic tail-summability problem left after the divisor split. -/
noncomputable def phiProgressionGammaLargeTailMajorant
    (P : Params) (X : ℝ) (d a s K : ℕ) : ℝ := by
  classical
  exact
    ∑ x ∈ (phiProgressionDivisorSigmaSupport P X d a s).filter
        (fun x => ¬ x.2 ≤ K),
      (((2 : ℝ) ^ Inputs.omega x.2) / (x.2 : ℝ)) /
        ((x.2 : ℝ) * ((x.1 / x.2 : ℕ) : ℝ))

/-- Outer-fiber form of the pure large-divisor tail majorant.  This is the
same finite carrier as `phiProgressionGammaLargeTailMajorant`, but written in
the paper's order: first fix the progression variable `r`, then sum over the
large exposed divisors `k|r`. -/
noncomputable def phiProgressionGammaLargeTailOuterMajorant
    (P : Params) (X : ℝ) (d a s K : ℕ) : ℝ := by
  classical
  exact
    ∑ r ∈ phiProgressionSupport P X d a s,
      (1 / (r : ℝ)) *
        ∑ k ∈ r.divisors.filter (fun k => ¬ k ≤ K),
          ((2 : ℝ) ^ Inputs.omega k) / (k : ℝ)

/-- Quotient-fiber form of the pure large-divisor tail majorant.  Keeping
`t=r/k` exposed leaves the summable one-dimensional coefficient
`2^ω(k)/k²` multiplying the same fixed-`k` reciprocal quotient fiber used on
the small-divisor side. -/
noncomputable def phiProgressionOmegaLargeWeightedRecipFiberSum
    (P : Params) (X : ℝ) (d a s K : ℕ) : ℝ := by
  classical
  exact
    ∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
        (fun k => ¬ k ≤ K),
      (((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)) *
        phiProgressionFixedKQuotientRecipFiber P X d a s k

/-- Admissible canonical-inverse squarefree-reciprocal model for the large
quotient-fiber tail.  The coefficient is the summable large-tail weight
`2^ω(k)/k²`; non-admissible fixed-divisor fibers are recorded as zero. -/
noncomputable def phiProgressionOmegaLargeSqfRecipAdmissibleInverseModelSum
    (P : Params) (X : ℝ) (d a s K : ℕ) : ℝ := by
  classical
  exact
    ∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
        (fun k => ¬ k ≤ K),
      if Nat.Coprime k d ∧ Nat.Coprime k s then
        (((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)) *
          Inputs.sqfRecip X (s * k) d (a * modInverseChoice d k)
            (phiProgressionU0 P s X / (k : ℝ))
            (phiProgressionU1 P s X / (k : ℝ))
      else 0

/-- The exact reciprocal-`φ` progression carrier in
`lem:phi-progression-average`:
`∑_{U₀<r≤U₁, r squarefree, (r,s)=1, r≡a (mod d)} 1/φ(r)`.

The interval is encoded with `Inputs.natWindow`, the project-wide carrier for
manuscript sums over `U₀ < n ≤ U₁`; the residue relation is
`Inputs.congMod`, the same elementary natural-number congruence used by the
other progression estimates. -/
noncomputable def phiProgressionAverage
    (P : Params) (X : ℝ) (d a s : ℕ) : ℝ := by
  classical
  exact
    ∑ r ∈ (Inputs.natWindow (phiProgressionU0 P s X)
        (phiProgressionU1 P s X)).filter
        (fun r => Squarefree r ∧ Nat.Coprime r s ∧ Inputs.congMod r a d),
      (1 : ℝ) / (Nat.totient r : ℝ)

/-- The expected main-term shape in `lem:phi-progression-average`:
`(1/d)·(φ(s)/s)·log(U₁/U₀)`, with the log-length represented by the existing
`slantLogLength` carrier. -/
noncomputable def phiProgressionAverageShape
    (P : Params) (X : ℝ) (d s : ℕ) : ℝ :=
  ((1 : ℝ) / (d : ℝ)) * ((Nat.totient s : ℝ) / (s : ℝ)) *
    slantLogLength P s X

/-- Foundation-only lower envelope for the progression shape, using the
checked divisor-subpower lower bound for `phi(s)/s`. -/
theorem phiProgressionAverageShape_lower_subpower
    (P : Params) {X : ℝ} {d s : ℕ}
    (hd : 0 < d) (hs : 1 ≤ s)
    (hL : 0 ≤ slantLogLength P s X) :
    ((1 : ℝ) / (d : ℝ)) *
        ((1 / Inputs.tauSquareQuarterConstant) *
          (s : ℝ) ^ (-((1 : ℝ) / 4))) *
        slantLogLength P s X ≤
      phiProgressionAverageShape P X d s := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hDinv : 0 ≤ (1 : ℝ) / (d : ℝ) :=
    div_nonneg zero_le_one hdR.le
  have htot :=
    totient_ratio_ge_inv_tauSquareQuarterConstant_mul_rpow_neg_quarter hs
  unfold phiProgressionAverageShape
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left htot hDinv) hL

/-! ## Unsieved exact-divisor mass carriers for `prop:M`.

The paper's linearized exact divisors are `e = r s²` with squarefree,
coprime `r,s`, `s ≤ S`, and `Y₀/s < r ≤ H/s²`.  The carriers below use the
same `phiProgressionSupport` as `lem:phi-progression-average`, specialized to
the trivial progression modulus.  The following equalities are the finite-sum
bookkeeping that turns the raw `ρ(e)` and `φ(ρ(e))` weights into the `s`-fibered
progression sums used in the proof of `prop:M`. -/

/-- Squarefree `s`-support for the unsieved exact-divisor mass. -/
noncomputable def exactDivisorSRange (P : Params) (X : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊).filter (fun s => Squarefree s)

/-- Pair support `(s,r)` for unsieved linearized exact divisors, using the
trivial residue class in the same slanted `r`-window as
`lem:phi-progression-average`. -/
noncomputable def exactDivisorMassSupport
    (P : Params) (X : ℝ) : Finset (Sigma fun _s : ℕ => ℕ) := by
  classical
  exact (exactDivisorSRange P X).sigma
    (fun s => phiProgressionSupport P X 1 0 s)

/-- Raw `M₁` finite carrier: sum of `1/ρ(e)=1/(rs)` over the linearized
exact-divisor support. -/
noncomputable def exactDivisorM1MassRaw (P : Params) (X : ℝ) : ℝ := by
  classical
  exact
    ∑ x ∈ exactDivisorMassSupport P X,
      (1 : ℝ) / ((x.2 * x.1 : ℕ) : ℝ)

/-- Fibered `M₁` carrier after the exact identity `1/ρ(e)=1/r · 1/s`. -/
noncomputable def exactDivisorM1MassFiber (P : Params) (X : ℝ) : ℝ := by
  classical
  exact
    ∑ s ∈ exactDivisorSRange P X,
      ((1 : ℝ) / (s : ℝ)) * phiProgressionBareAverage P X 1 0 s

/-- Raw `M_φ` finite carrier: sum of `1/φ(ρ(e))=1/φ(rs)` over the linearized
exact-divisor support. -/
noncomputable def exactDivisorMPhiMassRaw (P : Params) (X : ℝ) : ℝ := by
  classical
  exact
    ∑ x ∈ exactDivisorMassSupport P X,
      (1 : ℝ) / (Nat.totient (x.2 * x.1) : ℝ)

/-- Fibered `M_φ` carrier after the exact identity
`1/φ(ρ(e))=1/φ(r) · 1/φ(s)`. -/
noncomputable def exactDivisorMPhiMassFiber (P : Params) (X : ℝ) : ℝ := by
  classical
  exact
    ∑ s ∈ exactDivisorSRange P X,
      ((1 : ℝ) / (Nat.totient s : ℝ)) * phiProgressionAverage P X 1 0 s

/-- Main-term shape for the fibered `M_φ` carrier.  Replacing each
reciprocal-`φ` progression fiber by
`(φ(s)/s) * log(H/(Y₀s))` leaves the conductor weight `1/s`. -/
noncomputable def exactDivisorMPhiMassShape (P : Params) (X : ℝ) : ℝ := by
  classical
  exact
    ∑ s ∈ exactDivisorSRange P X,
      ((1 : ℝ) / (s : ℝ)) * slantLogLength P s X

/-- Main-term shape for the fibered `M₁` carrier.  Replacing each bare
squarefree progression fiber by `(φ(s)/s) * log(H/(Y₀s))` leaves the
conductor weight `φ(s)/s²`. -/
noncomputable def exactDivisorM1MassShape (P : Params) (X : ℝ) : ℝ := by
  classical
  exact
    ∑ s ∈ exactDivisorSRange P X,
      ((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) * slantLogLength P s X

/-! ### Tensorized exact-divisor fibers

The endpoint-safe exact-divisor tensorisation (`thm:tensor-e`) first proves a
fixed-`s` progression loss with modulus `D` and then sums over the squarefree
`s`-support.  The actual residue in the manuscript is `c s^{-2} (mod D)` when
`(s,D)=1`; the estimates used below are uniform in that residue, so we expose it
as an arbitrary selector `a : ℕ → ℕ`. -/

/-- `M₁` tensor fiber after the fixed-`s` congruence reduction. -/
noncomputable def exactDivisorM1TensorFiber
    (P : Params) (X : ℝ) (D : ℕ) (a : ℕ → ℕ) : ℝ := by
  classical
  exact
    ∑ s ∈ exactDivisorSRange P X,
      ((1 : ℝ) / (s : ℝ)) * phiProgressionBareAverage P X D (a s) s

/-- Manuscript-aligned `M₁` tensor fiber after the fixed-`s` congruence reduction.

As for the reciprocal-`φ` carrier, the reduced target class makes non-coprime
`s` fibers empty in `rs² ≡ c (mod D)`, so only `Nat.Coprime s D` fibers are
estimated. -/
noncomputable def exactDivisorM1TensorFiberCoprime
    (P : Params) (X : ℝ) (D : ℕ) (a : ℕ → ℕ) : ℝ := by
  classical
  exact
    ∑ s ∈ exactDivisorSRange P X,
      if Nat.Coprime s D then
        ((1 : ℝ) / (s : ℝ)) * phiProgressionBareAverage P X D (a s) s
      else 0

/-- `M_φ` tensor fiber after the fixed-`s` congruence reduction. -/
noncomputable def exactDivisorMPhiTensorFiber
    (P : Params) (X : ℝ) (D : ℕ) (a : ℕ → ℕ) : ℝ := by
  classical
  exact
    ∑ s ∈ exactDivisorSRange P X,
      ((1 : ℝ) / (Nat.totient s : ℝ)) * phiProgressionAverage P X D (a s) s

/-- Manuscript-aligned `M_φ` tensor fiber after the fixed-`s` congruence reduction.

In `thm:tensor-e`, when `(s,D)>1` and the target class is reduced modulo `D`,
the congruence `r s² ≡ c (mod D)` has no solutions.  This carrier records that
empty-fiber fact explicitly; only the coprime `s` fibers need the reciprocal-`φ`
progression estimate. -/
noncomputable def exactDivisorMPhiTensorFiberCoprime
    (P : Params) (X : ℝ) (D : ℕ) (a : ℕ → ℕ) : ℝ := by
  classical
  exact
    ∑ s ∈ exactDivisorSRange P X,
      if Nat.Coprime s D then
        ((1 : ℝ) / (Nat.totient s : ℝ)) * phiProgressionAverage P X D (a s) s
      else 0

/-- Summing the fixed-`s` endpoint-safe bare reciprocal progression loss gives
the `M₁/D` tensor bound.  This is the finite-sum layer of `thm:tensor-e`; the
fixed-`s` arithmetic progression estimate is the explicit hypothesis `hfiber`. -/
theorem exactDivisorM1TensorFiber_le_massShape_over_modulus
    (P : Params) (X : ℝ) (D : ℕ) (a : ℕ → ℕ) (K : ℝ) (hD : 0 < D)
    (hfiber : ∀ s ∈ exactDivisorSRange P X,
      phiProgressionBareAverage P X D (a s) s
        ≤ K * phiProgressionAverageShape P X D s) :
    exactDivisorM1TensorFiber P X D a
      ≤ (K / (D : ℝ)) * exactDivisorM1MassShape P X := by
  classical
  unfold exactDivisorM1TensorFiber exactDivisorM1MassShape
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
    (Finset.mem_filter.mp hs).1
  have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
  have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos_nat
  have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hscale_nonneg : 0 ≤ (1 : ℝ) / (s : ℝ) :=
    div_nonneg zero_le_one hs_pos.le
  calc
    ((1 : ℝ) / (s : ℝ)) * phiProgressionBareAverage P X D (a s) s
        ≤ ((1 : ℝ) / (s : ℝ)) *
            (K * phiProgressionAverageShape P X D s) :=
          mul_le_mul_of_nonneg_left (hfiber s hs) hscale_nonneg
    _ = (K / (D : ℝ)) *
          (((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) *
            slantLogLength P s X) := by
          unfold phiProgressionAverageShape
          ring_nf

/-- Manuscript-aligned coprime-`s` version of the `M₁` tensor summation.

Only coprime fibers are estimated; non-coprime fibers are zero by definition,
matching the reduced-class congruence in `thm:tensor-e`. -/
theorem exactDivisorM1TensorFiberCoprime_le_massShape_over_modulus
    (P : Params) (X : ℝ) (D : ℕ) (a : ℕ → ℕ) (K : ℝ)
    (hX : 1 ≤ X) (hD : 0 < D) (hK : 0 ≤ K)
    (hfiber : ∀ s ∈ exactDivisorSRange P X,
      Nat.Coprime s D →
      phiProgressionBareAverage P X D (a s) s
        ≤ K * phiProgressionAverageShape P X D s) :
    exactDivisorM1TensorFiberCoprime P X D a
      ≤ (K / (D : ℝ)) * exactDivisorM1MassShape P X := by
  classical
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hlog_nonneg : 0 ≤ Real.log X := Real.log_nonneg hX
  have hslant_coeff_nonneg : 0 ≤ (P.θ - P.lam - P.η) * Real.log X := by
    exact mul_nonneg (by linarith [P.lam_add_η_lt_θ]) hlog_nonneg
  have hS_nonneg : 0 ≤ SScale P X := (Real.rpow_pos_of_pos hXpos P.η).le
  unfold exactDivisorM1TensorFiberCoprime exactDivisorM1MassShape
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
    (Finset.mem_filter.mp hs).1
  have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
  have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
  have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos_nat
  have htot_nonneg : 0 ≤ (Nat.totient s : ℝ) := Nat.cast_nonneg _
  have hscale_nonneg : 0 ≤ ((s : ℝ)⁻¹) :=
    inv_nonneg.mpr hs_pos.le
  have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hKD_nonneg : 0 ≤ K / (D : ℝ) := div_nonneg hK hD_pos.le
  have hsS : (s : ℝ) ≤ SScale P X :=
    le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
  have hslant_nonneg : 0 ≤ slantLogLength P s X :=
    le_trans hslant_coeff_nonneg
      (slantLogLength_ge_theta_sub_lam_sub_eta_mul_log P hX hs_one hsS)
  by_cases hsD : Nat.Coprime s D
  · simp [hsD]
    rw [if_pos hsD]
    calc
      ((s : ℝ)⁻¹) * phiProgressionBareAverage P X D (a s) s
          ≤ ((s : ℝ)⁻¹) *
              (K * phiProgressionAverageShape P X D s) :=
            mul_le_mul_of_nonneg_left (hfiber s hs hsD) hscale_nonneg
      _ = (K / (D : ℝ)) *
            (((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) *
              slantLogLength P s X) := by
            unfold phiProgressionAverageShape
            ring_nf
  · simp [hsD]
    exact mul_nonneg hKD_nonneg
      (mul_nonneg (div_nonneg htot_nonneg (sq_nonneg (s : ℝ))) hslant_nonneg)

/-- Summing the fixed-`s` endpoint-safe reciprocal-`φ` progression loss gives
the `M_φ/D` tensor bound.  This is the finite-sum layer of `thm:tensor-e`; the
fixed-`s` arithmetic progression estimate is the explicit hypothesis `hfiber`. -/
theorem exactDivisorMPhiTensorFiber_le_massShape_over_modulus
    (P : Params) (X : ℝ) (D : ℕ) (a : ℕ → ℕ) (K : ℝ) (hD : 0 < D)
    (hfiber : ∀ s ∈ exactDivisorSRange P X,
      phiProgressionAverage P X D (a s) s
        ≤ K * phiProgressionAverageShape P X D s) :
    exactDivisorMPhiTensorFiber P X D a
      ≤ (K / (D : ℝ)) * exactDivisorMPhiMassShape P X := by
  classical
  unfold exactDivisorMPhiTensorFiber exactDivisorMPhiMassShape
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
    (Finset.mem_filter.mp hs).1
  have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
  have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos_nat
  have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have htot_pos_nat : 0 < Nat.totient s := Nat.totient_pos.mpr hs_pos_nat
  have htot_pos : 0 < (Nat.totient s : ℝ) := by exact_mod_cast htot_pos_nat
  have hscale_nonneg : 0 ≤ (1 : ℝ) / (Nat.totient s : ℝ) :=
    div_nonneg zero_le_one htot_pos.le
  calc
    ((1 : ℝ) / (Nat.totient s : ℝ)) * phiProgressionAverage P X D (a s) s
        ≤ ((1 : ℝ) / (Nat.totient s : ℝ)) *
            (K * phiProgressionAverageShape P X D s) :=
          mul_le_mul_of_nonneg_left (hfiber s hs) hscale_nonneg
    _ = (K / (D : ℝ)) *
          (((1 : ℝ) / (s : ℝ)) * slantLogLength P s X) := by
          unfold phiProgressionAverageShape
          ring_nf
          rw [mul_inv_cancel₀ (ne_of_gt htot_pos)]
          ring

/-- Manuscript-aligned coprime-`s` version of the reciprocal-`φ` tensor summation.

Only coprime fibers are estimated; non-coprime fibers are zero by definition,
matching the reduced-class congruence in `thm:tensor-e`. -/
theorem exactDivisorMPhiTensorFiberCoprime_le_massShape_over_modulus
    (P : Params) (X : ℝ) (D : ℕ) (a : ℕ → ℕ) (K : ℝ)
    (hX : 1 ≤ X) (hD : 0 < D) (hK : 0 ≤ K)
    (hfiber : ∀ s ∈ exactDivisorSRange P X,
      Nat.Coprime s D →
      phiProgressionAverage P X D (a s) s
        ≤ K * phiProgressionAverageShape P X D s) :
    exactDivisorMPhiTensorFiberCoprime P X D a
      ≤ (K / (D : ℝ)) * exactDivisorMPhiMassShape P X := by
  classical
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hlog_nonneg : 0 ≤ Real.log X := Real.log_nonneg hX
  have hslant_coeff_nonneg : 0 ≤ (P.θ - P.lam - P.η) * Real.log X := by
    exact mul_nonneg (by linarith [P.lam_add_η_lt_θ]) hlog_nonneg
  have hS_nonneg : 0 ≤ SScale P X := (Real.rpow_pos_of_pos hXpos P.η).le
  unfold exactDivisorMPhiTensorFiberCoprime exactDivisorMPhiMassShape
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
    (Finset.mem_filter.mp hs).1
  have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
  have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
  have hssqf : Squarefree s := (Finset.mem_filter.mp hs).2
  have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos_nat
  have htot_pos_nat : 0 < Nat.totient s := Nat.totient_pos.mpr hs_pos_nat
  have htot_pos : 0 < (Nat.totient s : ℝ) := by exact_mod_cast htot_pos_nat
  have hscale_nonneg : 0 ≤ ((Nat.totient s : ℝ)⁻¹) :=
    inv_nonneg.mpr htot_pos.le
  have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hKD_nonneg : 0 ≤ K / (D : ℝ) := div_nonneg hK hD_pos.le
  have hsS : (s : ℝ) ≤ SScale P X :=
    le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
  have hslant_nonneg : 0 ≤ slantLogLength P s X :=
    le_trans hslant_coeff_nonneg
      (slantLogLength_ge_theta_sub_lam_sub_eta_mul_log P hX hs_one hsS)
  by_cases hsD : Nat.Coprime s D
  · simp [hsD]
    rw [if_pos hsD]
    calc
      ((Nat.totient s : ℝ)⁻¹) * phiProgressionAverage P X D (a s) s
          ≤ ((Nat.totient s : ℝ)⁻¹) *
              (K * phiProgressionAverageShape P X D s) :=
            mul_le_mul_of_nonneg_left (hfiber s hs hsD) hscale_nonneg
      _ = (K / (D : ℝ)) *
            (((s : ℝ)⁻¹) * slantLogLength P s X) := by
            unfold phiProgressionAverageShape
            ring_nf
            rw [mul_inv_cancel₀ (ne_of_gt htot_pos)]
            ring
  · simp [hsD]
    exact mul_nonneg hKD_nonneg
      (mul_nonneg (inv_nonneg.mpr hs_pos.le) hslant_nonneg)

/-- Upgrade the `M₁` tensor summation bound from the main-term shape to the
actual fiber mass.  This is the final algebraic conversion in `thm:tensor-e`:
once `prop:M` supplies `c * massShape ≤ M₁`, the checked `massShape/D` tensor
sum becomes `M₁/D`. -/
theorem exactDivisorM1TensorFiber_le_massFiber_over_modulus
    (P : Params) (X : ℝ) (D : ℕ) (a : ℕ → ℕ) (K c : ℝ)
    (hD : 0 < D) (hK : 0 ≤ K) (hc : 0 < c)
    (hfiber : ∀ s ∈ exactDivisorSRange P X,
      phiProgressionBareAverage P X D (a s) s
        ≤ K * phiProgressionAverageShape P X D s)
    (hmass_lower : c * exactDivisorM1MassShape P X ≤ exactDivisorM1MassFiber P X) :
    exactDivisorM1TensorFiber P X D a
      ≤ (K / c) * (exactDivisorM1MassFiber P X / (D : ℝ)) := by
  have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have htensor :=
    exactDivisorM1TensorFiber_le_massShape_over_modulus P X D a K hD hfiber
  have hshape_le :
      exactDivisorM1MassShape P X ≤ exactDivisorM1MassFiber P X / c := by
    rw [le_div_iff₀ hc]
    simpa [mul_comm] using hmass_lower
  calc
    exactDivisorM1TensorFiber P X D a
        ≤ (K / (D : ℝ)) * exactDivisorM1MassShape P X := htensor
    _ ≤ (K / (D : ℝ)) * (exactDivisorM1MassFiber P X / c) := by
        exact mul_le_mul_of_nonneg_left hshape_le (div_nonneg hK hD_pos.le)
    _ = (K / c) * (exactDivisorM1MassFiber P X / (D : ℝ)) := by ring

/-- Upgrade the `M_φ` tensor summation bound from the main-term shape to the
actual fiber mass.  This is the reciprocal-`φ` half of the final algebraic
conversion in `thm:tensor-e`. -/
theorem exactDivisorMPhiTensorFiber_le_massFiber_over_modulus
    (P : Params) (X : ℝ) (D : ℕ) (a : ℕ → ℕ) (K c : ℝ)
    (hD : 0 < D) (hK : 0 ≤ K) (hc : 0 < c)
    (hfiber : ∀ s ∈ exactDivisorSRange P X,
      phiProgressionAverage P X D (a s) s
        ≤ K * phiProgressionAverageShape P X D s)
    (hmass_lower :
      c * exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X) :
    exactDivisorMPhiTensorFiber P X D a
      ≤ (K / c) * (exactDivisorMPhiMassFiber P X / (D : ℝ)) := by
  have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have htensor :=
    exactDivisorMPhiTensorFiber_le_massShape_over_modulus P X D a K hD hfiber
  have hshape_le :
      exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X / c := by
    rw [le_div_iff₀ hc]
    simpa [mul_comm] using hmass_lower
  calc
    exactDivisorMPhiTensorFiber P X D a
        ≤ (K / (D : ℝ)) * exactDivisorMPhiMassShape P X := htensor
    _ ≤ (K / (D : ℝ)) * (exactDivisorMPhiMassFiber P X / c) := by
        exact mul_le_mul_of_nonneg_left hshape_le (div_nonneg hK hD_pos.le)
    _ = (K / c) * (exactDivisorMPhiMassFiber P X / (D : ℝ)) := by ring

/-- Coprime-fiber version of the `M_φ` tensor summation bound.

This is the manuscript-aligned reciprocal-`φ` half of `thm:tensor-e`: reduced
classes force the non-coprime `s` fibers to be empty, so the fixed-`s`
progression estimate is needed only under `Nat.Coprime s D`. -/
theorem exactDivisorMPhiTensorFiberCoprime_le_massFiber_over_modulus
    (P : Params) (X : ℝ) (D : ℕ) (a : ℕ → ℕ) (K c : ℝ)
    (hX : 1 ≤ X) (hD : 0 < D) (hK : 0 ≤ K) (hc : 0 < c)
    (hfiber : ∀ s ∈ exactDivisorSRange P X,
      Nat.Coprime s D →
      phiProgressionAverage P X D (a s) s
        ≤ K * phiProgressionAverageShape P X D s)
    (hmass_lower :
      c * exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X) :
    exactDivisorMPhiTensorFiberCoprime P X D a
      ≤ (K / c) * (exactDivisorMPhiMassFiber P X / (D : ℝ)) := by
  have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have htensor :=
    exactDivisorMPhiTensorFiberCoprime_le_massShape_over_modulus
      P X D a K hX hD hK hfiber
  have hshape_le :
      exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X / c := by
    rw [le_div_iff₀ hc]
    simpa [mul_comm] using hmass_lower
  calc
    exactDivisorMPhiTensorFiberCoprime P X D a
        ≤ (K / (D : ℝ)) * exactDivisorMPhiMassShape P X := htensor
    _ ≤ (K / (D : ℝ)) * (exactDivisorMPhiMassFiber P X / c) := by
        exact mul_le_mul_of_nonneg_left hshape_le (div_nonneg hK hD_pos.le)
    _ = (K / c) * (exactDivisorMPhiMassFiber P X / (D : ℝ)) := by ring

/-- The raw `M₁` carrier equals its `s`-fibered progression form. -/
theorem exactDivisorM1MassRaw_eq_fiber (P : Params) (X : ℝ) :
    exactDivisorM1MassRaw P X = exactDivisorM1MassFiber P X := by
  classical
  unfold exactDivisorM1MassRaw exactDivisorM1MassFiber exactDivisorMassSupport
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro s hs
  unfold phiProgressionBareAverage phiProgressionSupport
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hspos : 0 < s :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
  have hssqf : Squarefree s := (Finset.mem_filter.mp hs).2
  have hwin :
      r ∈ Inputs.natWindow (phiProgressionU0 P s X)
        (phiProgressionU1 P s X) :=
    (Finset.mem_filter.mp hr).1
  have hdata := (Finset.mem_filter.mp hr).2
  have hrsqf : Squarefree r := hdata.1
  have hcop : Nat.Coprime r s := hdata.2.1
  have hrpos : 0 < r := by
    unfold Inputs.natWindow at hwin
    exact lt_of_lt_of_le Nat.zero_lt_one
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hwin).1).1
  let E : ExactDivisor :=
    { r := r
      s := s
      r_squarefree := hrsqf
      s_squarefree := hssqf
      coprime_rs := hcop }
  have hfactor := ExactDivisor.one_div_rho_cast_eq E hrpos hspos
  have hfactor' :
      (1 : ℝ) / ((r * s : ℕ) : ℝ) =
        ((1 : ℝ) / (r : ℝ)) * ((1 : ℝ) / (s : ℝ)) := by
    simpa [E, ExactDivisor.rho] using hfactor
  change (1 : ℝ) / ((r * s : ℕ) : ℝ) =
    ((1 : ℝ) / (s : ℝ)) * ((1 : ℝ) / (r : ℝ))
  rw [hfactor']
  ring

/-- The raw `M_φ` carrier equals its `s`-fibered reciprocal-`φ` progression
form. -/
theorem exactDivisorMPhiMassRaw_eq_fiber (P : Params) (X : ℝ) :
    exactDivisorMPhiMassRaw P X = exactDivisorMPhiMassFiber P X := by
  classical
  unfold exactDivisorMPhiMassRaw exactDivisorMPhiMassFiber exactDivisorMassSupport
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro s hs
  unfold phiProgressionAverage phiProgressionSupport
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hspos : 0 < s :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
  have hssqf : Squarefree s := (Finset.mem_filter.mp hs).2
  have hwin :
      r ∈ Inputs.natWindow (phiProgressionU0 P s X)
        (phiProgressionU1 P s X) :=
    (Finset.mem_filter.mp hr).1
  have hdata := (Finset.mem_filter.mp hr).2
  have hrsqf : Squarefree r := hdata.1
  have hcop : Nat.Coprime r s := hdata.2.1
  have hrpos : 0 < r := by
    unfold Inputs.natWindow at hwin
    exact lt_of_lt_of_le Nat.zero_lt_one
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hwin).1).1
  let E : ExactDivisor :=
    { r := r
      s := s
      r_squarefree := hrsqf
      s_squarefree := hssqf
      coprime_rs := hcop }
  have hfactor := ExactDivisor.one_div_totient_rho_cast_eq E hrpos hspos
  have hfactor' :
      (1 : ℝ) / (Nat.totient (r * s) : ℝ) =
        ((1 : ℝ) / (Nat.totient r : ℝ)) *
          ((1 : ℝ) / (Nat.totient s : ℝ)) := by
    simpa [E, ExactDivisor.rho] using hfactor
  change (1 : ℝ) / (Nat.totient (r * s) : ℝ) =
    ((1 : ℝ) / (Nat.totient s : ℝ)) *
      ((1 : ℝ) / (Nat.totient r : ℝ))
  rw [hfactor']
  ring

/-- Raw-mass version of `exactDivisorM1TensorFiber_le_massFiber_over_modulus`.
The raw and fibered `M₁` carriers are connected by
`exactDivisorM1MassRaw_eq_fiber`, so the tensor bound can be stated in the
paper's `M₁/D` form. -/
theorem exactDivisorM1TensorFiber_le_massRaw_over_modulus
    (P : Params) (X : ℝ) (D : ℕ) (a : ℕ → ℕ) (K c : ℝ)
    (hD : 0 < D) (hK : 0 ≤ K) (hc : 0 < c)
    (hfiber : ∀ s ∈ exactDivisorSRange P X,
      phiProgressionBareAverage P X D (a s) s
        ≤ K * phiProgressionAverageShape P X D s)
    (hmass_lower : c * exactDivisorM1MassShape P X ≤ exactDivisorM1MassFiber P X) :
    exactDivisorM1TensorFiber P X D a
      ≤ (K / c) * (exactDivisorM1MassRaw P X / (D : ℝ)) := by
  have h :=
    exactDivisorM1TensorFiber_le_massFiber_over_modulus P X D a K c
      hD hK hc hfiber hmass_lower
  simpa [exactDivisorM1MassRaw_eq_fiber P X] using h

/-- Raw-mass version of `exactDivisorMPhiTensorFiber_le_massFiber_over_modulus`.
The raw and fibered `M_φ` carriers are connected by
`exactDivisorMPhiMassRaw_eq_fiber`, so the tensor bound can be stated in the
paper's `M_φ/D` form. -/
theorem exactDivisorMPhiTensorFiber_le_massRaw_over_modulus
    (P : Params) (X : ℝ) (D : ℕ) (a : ℕ → ℕ) (K c : ℝ)
    (hD : 0 < D) (hK : 0 ≤ K) (hc : 0 < c)
    (hfiber : ∀ s ∈ exactDivisorSRange P X,
      phiProgressionAverage P X D (a s) s
        ≤ K * phiProgressionAverageShape P X D s)
    (hmass_lower :
      c * exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X) :
    exactDivisorMPhiTensorFiber P X D a
      ≤ (K / c) * (exactDivisorMPhiMassRaw P X / (D : ℝ)) := by
  have h :=
    exactDivisorMPhiTensorFiber_le_massFiber_over_modulus P X D a K c
      hD hK hc hfiber hmass_lower
  simpa [exactDivisorMPhiMassRaw_eq_fiber P X] using h

/-- Raw-mass version of the coprime-fiber reciprocal-`φ` tensor bound. -/
theorem exactDivisorMPhiTensorFiberCoprime_le_massRaw_over_modulus
    (P : Params) (X : ℝ) (D : ℕ) (a : ℕ → ℕ) (K c : ℝ)
    (hX : 1 ≤ X) (hD : 0 < D) (hK : 0 ≤ K) (hc : 0 < c)
    (hfiber : ∀ s ∈ exactDivisorSRange P X,
      Nat.Coprime s D →
      phiProgressionAverage P X D (a s) s
        ≤ K * phiProgressionAverageShape P X D s)
    (hmass_lower :
      c * exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X) :
    exactDivisorMPhiTensorFiberCoprime P X D a
      ≤ (K / c) * (exactDivisorMPhiMassRaw P X / (D : ℝ)) := by
  have h :=
    exactDivisorMPhiTensorFiberCoprime_le_massFiber_over_modulus
      P X D a K c hX hD hK hc hfiber hmass_lower
  simpa [exactDivisorMPhiMassRaw_eq_fiber P X] using h

/-- Paired raw-mass tensor form of `thm:tensor-e`.

This is the downstream-facing package used by the event-mass argument: the
bare and reciprocal-`φ` tensor fibers are both bounded by their corresponding
raw masses with the expected `1/D` loss.  The only remaining hypotheses are the
fixed-`s` progression estimates and the two lower mass-comparison constants. -/
theorem exactDivisorTensorFiber_le_massRaw_over_modulus_pair
    (P : Params) (X : ℝ) (D : ℕ) (a : ℕ → ℕ)
    (K₁ c₁ Kφ cφ : ℝ)
    (hD : 0 < D) (hK₁ : 0 ≤ K₁) (hc₁ : 0 < c₁)
    (hKφ : 0 ≤ Kφ) (hcφ : 0 < cφ)
    (hfiber₁ : ∀ s ∈ exactDivisorSRange P X,
      phiProgressionBareAverage P X D (a s) s
        ≤ K₁ * phiProgressionAverageShape P X D s)
    (hfiberφ : ∀ s ∈ exactDivisorSRange P X,
      phiProgressionAverage P X D (a s) s
        ≤ Kφ * phiProgressionAverageShape P X D s)
    (hmass₁_lower :
      c₁ * exactDivisorM1MassShape P X ≤ exactDivisorM1MassFiber P X)
    (hmassφ_lower :
      cφ * exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X) :
    exactDivisorM1TensorFiber P X D a
        ≤ (K₁ / c₁) * (exactDivisorM1MassRaw P X / (D : ℝ))
      ∧ exactDivisorMPhiTensorFiber P X D a
        ≤ (Kφ / cφ) * (exactDivisorMPhiMassRaw P X / (D : ℝ)) := by
  exact
    ⟨exactDivisorM1TensorFiber_le_massRaw_over_modulus
        P X D a K₁ c₁ hD hK₁ hc₁ hfiber₁ hmass₁_lower,
      exactDivisorMPhiTensorFiber_le_massRaw_over_modulus
        P X D a Kφ cφ hD hKφ hcφ hfiberφ hmassφ_lower⟩

/-- Paired raw-mass tensor form with the reciprocal-`φ` half stated on the
manuscript-aligned coprime carrier. -/
theorem exactDivisorTensorFiberCoprimeMPhi_le_massRaw_over_modulus_pair
    (P : Params) (X : ℝ) (D : ℕ) (a : ℕ → ℕ)
    (K₁ c₁ Kφ cφ : ℝ)
    (hX : 1 ≤ X) (hD : 0 < D) (hK₁ : 0 ≤ K₁) (hc₁ : 0 < c₁)
    (hKφ : 0 ≤ Kφ) (hcφ : 0 < cφ)
    (hfiber₁ : ∀ s ∈ exactDivisorSRange P X,
      phiProgressionBareAverage P X D (a s) s
        ≤ K₁ * phiProgressionAverageShape P X D s)
    (hfiberφ : ∀ s ∈ exactDivisorSRange P X,
      Nat.Coprime s D →
      phiProgressionAverage P X D (a s) s
        ≤ Kφ * phiProgressionAverageShape P X D s)
    (hmass₁_lower :
      c₁ * exactDivisorM1MassShape P X ≤ exactDivisorM1MassFiber P X)
    (hmassφ_lower :
      cφ * exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X) :
    exactDivisorM1TensorFiber P X D a
        ≤ (K₁ / c₁) * (exactDivisorM1MassRaw P X / (D : ℝ))
      ∧ exactDivisorMPhiTensorFiberCoprime P X D a
        ≤ (Kφ / cφ) * (exactDivisorMPhiMassRaw P X / (D : ℝ)) := by
  exact
    ⟨exactDivisorM1TensorFiber_le_massRaw_over_modulus
        P X D a K₁ c₁ hD hK₁ hc₁ hfiber₁ hmass₁_lower,
      exactDivisorMPhiTensorFiberCoprime_le_massRaw_over_modulus
        P X D a Kφ cφ hX hD hKφ hcφ hfiberφ hmassφ_lower⟩

/-- Paper-facing exact-divisor tensor output bundle.

This packages the two raw/fiber exact-divisor identities with the paired
endpoint-safe `M₁/D` and `M_φ/D` tensor bounds.  It is the current checked
surface for the finite-sum layer of `thm:tensor-e`: the fixed-`s` progression
losses and the two lower mass comparisons remain explicit hypotheses, while the
summation, raw-carrier conversion, and paired paper target are theorem-level
consequences. -/
theorem exactDivisorTensorPaperOutputs
    (P : Params) (X : ℝ) (D : ℕ) (a : ℕ → ℕ)
    (K₁ c₁ Kφ cφ : ℝ)
    (hD : 0 < D) (hK₁ : 0 ≤ K₁) (hc₁ : 0 < c₁)
    (hKφ : 0 ≤ Kφ) (hcφ : 0 < cφ)
    (hfiber₁ : ∀ s ∈ exactDivisorSRange P X,
      phiProgressionBareAverage P X D (a s) s
        ≤ K₁ * phiProgressionAverageShape P X D s)
    (hfiberφ : ∀ s ∈ exactDivisorSRange P X,
      phiProgressionAverage P X D (a s) s
        ≤ Kφ * phiProgressionAverageShape P X D s)
    (hmass₁_lower :
      c₁ * exactDivisorM1MassShape P X ≤ exactDivisorM1MassFiber P X)
    (hmassφ_lower :
      cφ * exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X) :
    exactDivisorM1MassRaw P X = exactDivisorM1MassFiber P X
      ∧ exactDivisorMPhiMassRaw P X = exactDivisorMPhiMassFiber P X
      ∧ exactDivisorM1TensorFiber P X D a
          ≤ (K₁ / c₁) * (exactDivisorM1MassRaw P X / (D : ℝ))
      ∧ exactDivisorMPhiTensorFiber P X D a
          ≤ (Kφ / cφ) * (exactDivisorMPhiMassRaw P X / (D : ℝ)) := by
  exact
    ⟨exactDivisorM1MassRaw_eq_fiber P X,
      exactDivisorMPhiMassRaw_eq_fiber P X,
      exactDivisorTensorFiber_le_massRaw_over_modulus_pair
        P X D a K₁ c₁ Kφ cφ hD hK₁ hc₁ hKφ hcφ
        hfiber₁ hfiberφ hmass₁_lower hmassφ_lower⟩

theorem exactDivisorMPhiMassShape_nonneg
    (P : Params) {X : ℝ} (hX : Real.exp 1 ≤ X) :
    0 ≤ exactDivisorMPhiMassShape P X := by
  classical
  unfold exactDivisorMPhiMassShape
  apply Finset.sum_nonneg
  intro s hs
  have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
    (Finset.mem_filter.mp hs).1
  have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
  have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hX
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hS_nonneg : 0 ≤ SScale P X := (Real.rpow_pos_of_pos hXpos P.η).le
  have hsS : (s : ℝ) ≤ SScale P X :=
    le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
  have hslant_nonneg :
      0 ≤ slantLogLength P s X := by
    have hlog_nonneg : 0 ≤ Real.log X := Real.log_nonneg hXone
    have hlower :=
      slantLogLength_ge_theta_sub_lam_sub_eta_mul_log P hXone hs_one hsS
    have hcoef_pos : 0 < P.θ - P.lam - P.η := by
      linarith [P.lam_add_η_lt_θ]
    nlinarith
  exact mul_nonneg (div_nonneg zero_le_one (by exact_mod_cast (Nat.zero_le s)))
    hslant_nonneg

theorem exactDivisorMPhiMassShape_lower_logX_sAvgRecip
    (P : Params) {X : ℝ} (hX : Real.exp 1 ≤ X) :
    (P.θ - P.lam - P.η) * logX X * Inputs.sAvgRecip P X
      ≤ exactDivisorMPhiMassShape P X := by
  classical
  unfold exactDivisorMPhiMassShape Inputs.sAvgRecip exactDivisorSRange
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
    (Finset.mem_filter.mp hs).1
  have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
  have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hX
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hS_nonneg : 0 ≤ SScale P X := (Real.rpow_pos_of_pos hXpos P.η).le
  have hsS : (s : ℝ) ≤ SScale P X :=
    le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
  have hslant :=
    slantLogLength_ge_theta_sub_lam_sub_eta_mul_log P hXone hs_one hsS
  have hs_nonneg : 0 ≤ (1 : ℝ) / (s : ℝ) :=
    div_nonneg zero_le_one (by exact_mod_cast (Nat.zero_le s))
  unfold logX
  calc
    ((P.θ - P.lam - P.η) * Real.log X) * ((1 : ℝ) / (s : ℝ))
        = ((1 : ℝ) / (s : ℝ)) * ((P.θ - P.lam - P.η) * Real.log X) := by ring
    _ ≤ ((1 : ℝ) / (s : ℝ)) * slantLogLength P s X :=
        mul_le_mul_of_nonneg_left hslant hs_nonneg

theorem exactDivisorMPhiMassShape_upper_logX_sAvgRecip
    (P : Params) {X : ℝ} (hX : Real.exp 1 ≤ X) :
    exactDivisorMPhiMassShape P X
      ≤ (P.θ - P.lam) * logX X * Inputs.sAvgRecip P X := by
  classical
  unfold exactDivisorMPhiMassShape Inputs.sAvgRecip exactDivisorSRange
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
    (Finset.mem_filter.mp hs).1
  have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hX
  have hslant :=
    slantLogLength_le_theta_sub_lam_mul_log P hXone hs_one
  have hs_nonneg : 0 ≤ (1 : ℝ) / (s : ℝ) :=
    div_nonneg zero_le_one (by exact_mod_cast (Nat.zero_le s))
  unfold logX
  calc
    ((1 : ℝ) / (s : ℝ)) * slantLogLength P s X
        ≤ ((1 : ℝ) / (s : ℝ)) * ((P.θ - P.lam) * Real.log X) :=
          mul_le_mul_of_nonneg_left hslant hs_nonneg
    _ = ((P.θ - P.lam) * Real.log X) * ((1 : ℝ) / (s : ℝ)) := by ring

theorem exactDivisorM1MassShape_nonneg
    (P : Params) {X : ℝ} (hX : Real.exp 1 ≤ X) :
    0 ≤ exactDivisorM1MassShape P X := by
  classical
  unfold exactDivisorM1MassShape
  apply Finset.sum_nonneg
  intro s hs
  have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
    (Finset.mem_filter.mp hs).1
  have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
  have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hX
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hS_nonneg : 0 ≤ SScale P X := (Real.rpow_pos_of_pos hXpos P.η).le
  have hsS : (s : ℝ) ≤ SScale P X :=
    le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
  have hslant_nonneg :
      0 ≤ slantLogLength P s X := by
    have hlog_nonneg : 0 ≤ Real.log X := Real.log_nonneg hXone
    have hlower :=
      slantLogLength_ge_theta_sub_lam_sub_eta_mul_log P hXone hs_one hsS
    have hcoef_pos : 0 < P.θ - P.lam - P.η := by
      linarith [P.lam_add_η_lt_θ]
    nlinarith
  have hcoef_nonneg :
      0 ≤ (Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ) :=
    div_nonneg (by exact_mod_cast Nat.zero_le (Nat.totient s))
      (sq_nonneg (s : ℝ))
  exact mul_nonneg hcoef_nonneg hslant_nonneg

theorem exactDivisorM1MassShape_lower_logX_sAvgPhi
    (P : Params) {X : ℝ} (hX : Real.exp 1 ≤ X) :
    (P.θ - P.lam - P.η) * logX X * Inputs.sAvgPhi P X
      ≤ exactDivisorM1MassShape P X := by
  classical
  unfold exactDivisorM1MassShape Inputs.sAvgPhi exactDivisorSRange
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
    (Finset.mem_filter.mp hs).1
  have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
  have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hX
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hS_nonneg : 0 ≤ SScale P X := (Real.rpow_pos_of_pos hXpos P.η).le
  have hsS : (s : ℝ) ≤ SScale P X :=
    le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
  have hslant :=
    slantLogLength_ge_theta_sub_lam_sub_eta_mul_log P hXone hs_one hsS
  have hcoef_nonneg :
      0 ≤ (Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ) :=
    div_nonneg (by exact_mod_cast Nat.zero_le (Nat.totient s))
      (sq_nonneg (s : ℝ))
  unfold logX
  calc
    ((P.θ - P.lam - P.η) * Real.log X) *
        ((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ))
        =
        ((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) *
          ((P.θ - P.lam - P.η) * Real.log X) := by ring
    _ ≤ ((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) *
          slantLogLength P s X :=
        mul_le_mul_of_nonneg_left hslant hcoef_nonneg

theorem exactDivisorM1MassShape_upper_logX_sAvgPhi
    (P : Params) {X : ℝ} (hX : Real.exp 1 ≤ X) :
    exactDivisorM1MassShape P X
      ≤ (P.θ - P.lam) * logX X * Inputs.sAvgPhi P X := by
  classical
  unfold exactDivisorM1MassShape Inputs.sAvgPhi exactDivisorSRange
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
    (Finset.mem_filter.mp hs).1
  have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hX
  have hslant :=
    slantLogLength_le_theta_sub_lam_mul_log P hXone hs_one
  have hcoef_nonneg :
      0 ≤ (Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ) :=
    div_nonneg (by exact_mod_cast Nat.zero_le (Nat.totient s))
      (sq_nonneg (s : ℝ))
  unfold logX
  calc
    ((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) *
        slantLogLength P s X
        ≤ ((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) *
          ((P.θ - P.lam) * Real.log X) :=
          mul_le_mul_of_nonneg_left hslant hcoef_nonneg
    _ = ((P.θ - P.lam) * Real.log X) *
          ((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) := by ring

/-- The exact paper-facing two-sided assertion of
`lem:phi-progression-average`, stated on the finite carrier above and uniformly
over the admissible squarefree odd modulus `d`, coprime residue class `a`, and
squarefree conductor `s`.

This is a theorem-level target, not an axiom.  It names the remaining
arithmetic progression average that still has to be proved from the manuscript's
Möbius-inversion, CRT, Euler-product, and partial-summation argument. -/
def PhiProgressionAverageTwoSided (P : Params) : Prop :=
  ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ d a s : ℕ,
      0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
      Nat.Coprime a d →
      1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
        c * phiProgressionAverageShape P X d s ≤
            phiProgressionAverage P X d a s ∧
          phiProgressionAverage P X d a s ≤
            C * phiProgressionAverageShape P X d s

/-- Exact ordinary-squarefree lower estimate needed for the lower half of
`lem:phi-progression-average`, specialized to the paper's moving interval and
moduli.

This is still a theorem-level target, not an axiom.  It states precisely the
ordinary squarefree progression input that the lower-bound half needs before the
elementary replacement `1/r ≤ 1/φ(r)` is applied. -/
def PhiProgressionSqfRecipLower (P : Params) : Prop :=
  ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ d a s : ℕ,
      0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
      Nat.Coprime a d →
      1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
        c * (((1 : ℝ) / (d : ℝ)) * ((Nat.totient s : ℝ) / (s : ℝ)) *
          Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X))
          ≤ Inputs.sqfRecip X s d a
            (phiProgressionU0 P s X) (phiProgressionU1 P s X)

/-- The exact reciprocal-`φ` progression carrier is nonnegative. -/
theorem phiProgressionAverage_nonneg
    (P : Params) (X : ℝ) (d a s : ℕ) :
    0 ≤ phiProgressionAverage P X d a s := by
  classical
  unfold phiProgressionAverage
  apply Finset.sum_nonneg
  intro r hr
  have hr_window :
      r ∈ Inputs.natWindow (phiProgressionU0 P s X)
        (phiProgressionU1 P s X) :=
    (Finset.mem_filter.mp hr).1
  have hr_pos_nat : 0 < r := by
    unfold Inputs.natWindow at hr_window
    exact lt_of_lt_of_le Nat.zero_lt_one
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hr_window).1).1
  have htot_pos : 0 < Nat.totient r := Nat.totient_pos.mpr hr_pos_nat
  exact div_nonneg zero_le_one (by exact_mod_cast htot_pos.le)

/-- The bare reciprocal progression carrier is nonnegative. -/
theorem phiProgressionBareAverage_nonneg
    (P : Params) (X : ℝ) (d a s : ℕ) :
    0 ≤ phiProgressionBareAverage P X d a s := by
  classical
  unfold phiProgressionBareAverage
  apply Finset.sum_nonneg
  intro r hr
  have hr_window :
      r ∈ Inputs.natWindow (phiProgressionU0 P s X)
        (phiProgressionU1 P s X) :=
    (Finset.mem_filter.mp hr).1
  have hr_pos_nat : 0 < r := by
    unfold Inputs.natWindow at hr_window
    exact lt_of_lt_of_le Nat.zero_lt_one
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hr_window).1).1
  exact div_nonneg zero_le_one (by exact_mod_cast hr_pos_nat.le)

/-- The reciprocal-`φ` exact-divisor tensor fiber is nonnegative. -/
theorem exactDivisorMPhiTensorFiber_nonneg
    (P : Params) (X : ℝ) (D : ℕ) (a : ℕ → ℕ) :
    0 ≤ exactDivisorMPhiTensorFiber P X D a := by
  classical
  unfold exactDivisorMPhiTensorFiber
  apply Finset.sum_nonneg
  intro s hs
  have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
    (Finset.mem_filter.mp hs).1
  have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
  have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have htot_pos_nat : 0 < Nat.totient s := Nat.totient_pos.mpr hs_pos_nat
  exact mul_nonneg
    (div_nonneg zero_le_one (by exact_mod_cast htot_pos_nat.le))
    (phiProgressionAverage_nonneg P X D (a s) s)

/-- The coprime reciprocal-`φ` exact-divisor tensor fiber is nonnegative. -/
theorem exactDivisorMPhiTensorFiberCoprime_nonneg
    (P : Params) (X : ℝ) (D : ℕ) (a : ℕ → ℕ) :
    0 ≤ exactDivisorMPhiTensorFiberCoprime P X D a := by
  classical
  unfold exactDivisorMPhiTensorFiberCoprime
  apply Finset.sum_nonneg
  intro s hs
  by_cases hsD : Nat.Coprime s D
  · rw [if_pos hsD]
    have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
      (Finset.mem_filter.mp hs).1
    have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
    have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
    have htot_pos_nat : 0 < Nat.totient s := Nat.totient_pos.mpr hs_pos_nat
    have htot_nonneg : (0 : ℝ) ≤ (Nat.totient s : ℝ) := by
      exact_mod_cast htot_pos_nat.le
    exact mul_nonneg
      (div_nonneg zero_le_one htot_nonneg)
      (phiProgressionAverage_nonneg P X D (a s) s)
  · rw [if_neg hsD]

/-- Concrete double-divisibility event carrier assembled from the prime-window
factor and the endpoint-safe exact-divisor tensor fiber.

This is the carrier shape used by the manuscript before the final `μ_b`
normalization: the tensor fiber contributes one `1/D`, and the exposed
`d_+ = D t` restriction contributes the second `1/D`. -/
noncomputable def exactDivisorEventDoubleCarrier
    (P : Params) (a : ℝ → ℕ → ℕ → ℕ) (X : ℝ) (D : ℕ) : ℝ :=
  (Inputs.primeRecipWindow P X / (D : ℝ)) *
    exactDivisorMPhiTensorFiberCoprime P X D (a X D)

/-- Concrete single-divisibility event carrier assembled from the prime-window
factor and the endpoint-safe exact-divisor tensor fiber. -/
noncomputable def exactDivisorEventSingleCarrier
    (P : Params) (a : ℝ → ℕ → ℕ → ℕ) (X : ℝ) (D : ℕ) : ℝ :=
  Inputs.primeRecipWindow P X *
    exactDivisorMPhiTensorFiberCoprime P X D (a X D)

/-- The concrete prime-window/tensor event carriers satisfy the assembled
`logCube/D²` and `logCube/D` bounds consumed by `prop:event-tensor`.

The hypotheses are exactly the three upstream estimates used in this algebraic
handoff: a logarithmic prime-window bound, a `1/D` exact-divisor tensor bound,
and a quadratic upper bound for the reciprocal-`φ` exact-divisor mass. -/
theorem exactDivisorEventCarriers_logCube_bound
    (P : Params) (a : ℝ → ℕ → ℕ → ℕ)
    (Cprime Ktensor cmass Cmass Xprime Xtensor Xmass : ℝ)
    (hCprime : 0 ≤ Cprime) (hKtensor : 0 ≤ Ktensor)
    (hcmass : 0 < cmass)
    (hprime : ∀ X : ℝ, Xprime ≤ X →
      Inputs.primeRecipWindow P X ≤ Cprime * Real.log X)
    (htensor : ∀ X : ℝ, Xtensor ≤ X → ∀ D : ℕ, 1 ≤ D →
      exactDivisorMPhiTensorFiberCoprime P X D (a X D) ≤
        (Ktensor / cmass) * (exactDivisorMPhiMassRaw P X / (D : ℝ)))
    (hmass : ∀ X : ℝ, Xmass ≤ X →
      exactDivisorMPhiMassRaw P X ≤ Cmass * logSq X) :
    ∀ X : ℝ, max (max Xprime Xtensor) (max Xmass (Real.exp 1)) ≤ X →
      ∀ D : ℕ, 1 ≤ D →
        exactDivisorEventDoubleCarrier P a X D
            ≤ (Cprime * (Ktensor / cmass) * Cmass) *
                (logCube X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P a X D
            ≤ (Cprime * (Ktensor / cmass) * Cmass) *
                (logCube X / (D : ℝ)) := by
  intro X hX D hD
  have hXp : Xprime ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXt : Xtensor ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXm : Xmass ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hXone : (1 : ℝ) ≤ X := le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe
  have hlog_nonneg : 0 ≤ Real.log X := Real.log_nonneg hXone
  have hD_one : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hD_pos : (0 : ℝ) < (D : ℝ) := lt_of_lt_of_le zero_lt_one hD_one
  have hD_nonneg : 0 ≤ (D : ℝ) := hD_pos.le
  have hD_sq_pos : (0 : ℝ) < (D : ℝ) ^ 2 := by positivity
  have hprime_nonneg : 0 ≤ Inputs.primeRecipWindow P X :=
    Inputs.primeRecipWindow_nonneg P X
  have htensor_nonneg : 0 ≤ exactDivisorMPhiTensorFiberCoprime P X D (a X D) :=
    exactDivisorMPhiTensorFiberCoprime_nonneg P X D (a X D)
  have hprime_le := hprime X hXp
  have htensor_le := htensor X hXt D hD
  have hmass_le := hmass X hXm
  have hKc_nonneg : 0 ≤ Ktensor / cmass := div_nonneg hKtensor hcmass.le
  have hprime_div_le :
      Inputs.primeRecipWindow P X / (D : ℝ) ≤
        (Cprime * Real.log X) / (D : ℝ) :=
    div_le_div_of_nonneg_right hprime_le hD_nonneg
  have hprime_div_nonneg :
      0 ≤ Inputs.primeRecipWindow P X / (D : ℝ) :=
    div_nonneg hprime_nonneg hD_nonneg
  have hCprime_log_div_nonneg :
      0 ≤ (Cprime * Real.log X) / (D : ℝ) :=
    div_nonneg (mul_nonneg hCprime hlog_nonneg) hD_nonneg
  have hCprime_log_nonneg : 0 ≤ Cprime * Real.log X :=
    mul_nonneg hCprime hlog_nonneg
  constructor
  · calc
      exactDivisorEventDoubleCarrier P a X D
          = (Inputs.primeRecipWindow P X / (D : ℝ)) *
              exactDivisorMPhiTensorFiberCoprime P X D (a X D) := rfl
      _ ≤ ((Cprime * Real.log X) / (D : ℝ)) *
            exactDivisorMPhiTensorFiberCoprime P X D (a X D) :=
          mul_le_mul_of_nonneg_right hprime_div_le htensor_nonneg
      _ ≤ ((Cprime * Real.log X) / (D : ℝ)) *
            ((Ktensor / cmass) * (exactDivisorMPhiMassRaw P X / (D : ℝ))) :=
          mul_le_mul_of_nonneg_left htensor_le hCprime_log_div_nonneg
      _ ≤ ((Cprime * Real.log X) / (D : ℝ)) *
            ((Ktensor / cmass) * ((Cmass * logSq X) / (D : ℝ))) := by
          have hmass_div :
              exactDivisorMPhiMassRaw P X / (D : ℝ) ≤
                (Cmass * logSq X) / (D : ℝ) :=
            div_le_div_of_nonneg_right hmass_le hD_nonneg
          have hmul := mul_le_mul_of_nonneg_left hmass_div hKc_nonneg
          exact mul_le_mul_of_nonneg_left hmul hCprime_log_div_nonneg
      _ = (Cprime * (Ktensor / cmass) * Cmass) *
            (logCube X / (D : ℝ) ^ 2) := by
          unfold logSq logCube
          field_simp [ne_of_gt hD_pos, ne_of_gt hD_sq_pos]
          ring
  · calc
      exactDivisorEventSingleCarrier P a X D
          = Inputs.primeRecipWindow P X *
              exactDivisorMPhiTensorFiberCoprime P X D (a X D) := rfl
      _ ≤ (Cprime * Real.log X) *
            exactDivisorMPhiTensorFiberCoprime P X D (a X D) :=
          mul_le_mul_of_nonneg_right hprime_le htensor_nonneg
      _ ≤ (Cprime * Real.log X) *
            ((Ktensor / cmass) * (exactDivisorMPhiMassRaw P X / (D : ℝ))) :=
          mul_le_mul_of_nonneg_left htensor_le hCprime_log_nonneg
      _ ≤ (Cprime * Real.log X) *
            ((Ktensor / cmass) * ((Cmass * logSq X) / (D : ℝ))) := by
          have hmass_div :
              exactDivisorMPhiMassRaw P X / (D : ℝ) ≤
                (Cmass * logSq X) / (D : ℝ) :=
            div_le_div_of_nonneg_right hmass_le hD_nonneg
          have hmul := mul_le_mul_of_nonneg_left hmass_div hKc_nonneg
          exact mul_le_mul_of_nonneg_left hmul hCprime_log_nonneg
      _ = (Cprime * (Ktensor / cmass) * Cmass) *
            (logCube X / (D : ℝ)) := by
          unfold logSq logCube
          field_simp [ne_of_gt hD_pos]
          ring

/-- Paper-range version of `exactDivisorEventCarriers_logCube_bound`.

The exact-divisor tensor theorem is only needed on the manuscript's admissible
modulus range: squarefree odd `D` with `D≤YU`.  This lemma keeps precisely that
range in the conclusion instead of upgrading it to an all-`D` statement. -/
theorem exactDivisorEventCarriers_logCube_bound_on_YU
    (P : Params) (a : ℝ → ℕ → ℕ → ℕ)
    (Cprime Ktensor cmass Cmass Xprime Xtensor Xmass : ℝ)
    (hCprime : 0 ≤ Cprime) (hKtensor : 0 ≤ Ktensor)
    (hcmass : 0 < cmass)
    (hprime : ∀ X : ℝ, Xprime ≤ X →
      Inputs.primeRecipWindow P X ≤ Cprime * Real.log X)
    (htensor : ∀ X : ℝ, Xtensor ≤ X → ∀ D : ℕ, 1 ≤ D →
      Squarefree D → Odd D → (D : ℝ) ≤ YScale P X * UScale X →
      exactDivisorMPhiTensorFiberCoprime P X D (a X D) ≤
        (Ktensor / cmass) * (exactDivisorMPhiMassRaw P X / (D : ℝ)))
    (hmass : ∀ X : ℝ, Xmass ≤ X →
      exactDivisorMPhiMassRaw P X ≤ Cmass * logSq X) :
    ∀ X : ℝ, max (max Xprime Xtensor) (max Xmass (Real.exp 1)) ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P a X D
            ≤ (Cprime * (Ktensor / cmass) * Cmass) *
                (logCube X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P a X D
            ≤ (Cprime * (Ktensor / cmass) * Cmass) *
                (logCube X / (D : ℝ)) := by
  intro X hX D hD hD_sqf hD_odd hDwide
  have hXp : Xprime ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXt : Xtensor ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXm : Xmass ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hXone : (1 : ℝ) ≤ X := le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe
  have hlog_nonneg : 0 ≤ Real.log X := Real.log_nonneg hXone
  have hD_one : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hD_pos : (0 : ℝ) < (D : ℝ) := lt_of_lt_of_le zero_lt_one hD_one
  have hD_nonneg : 0 ≤ (D : ℝ) := hD_pos.le
  have hD_sq_pos : (0 : ℝ) < (D : ℝ) ^ 2 := by positivity
  have hprime_nonneg : 0 ≤ Inputs.primeRecipWindow P X :=
    Inputs.primeRecipWindow_nonneg P X
  have htensor_nonneg : 0 ≤ exactDivisorMPhiTensorFiberCoprime P X D (a X D) :=
    exactDivisorMPhiTensorFiberCoprime_nonneg P X D (a X D)
  have hprime_le := hprime X hXp
  have htensor_le := htensor X hXt D hD hD_sqf hD_odd hDwide
  have hmass_le := hmass X hXm
  have hKc_nonneg : 0 ≤ Ktensor / cmass := div_nonneg hKtensor hcmass.le
  have hprime_div_le :
      Inputs.primeRecipWindow P X / (D : ℝ) ≤
        (Cprime * Real.log X) / (D : ℝ) :=
    div_le_div_of_nonneg_right hprime_le hD_nonneg
  have hprime_div_nonneg :
      0 ≤ Inputs.primeRecipWindow P X / (D : ℝ) :=
    div_nonneg hprime_nonneg hD_nonneg
  have hCprime_log_div_nonneg :
      0 ≤ (Cprime * Real.log X) / (D : ℝ) :=
    div_nonneg (mul_nonneg hCprime hlog_nonneg) hD_nonneg
  have hCprime_log_nonneg : 0 ≤ Cprime * Real.log X :=
    mul_nonneg hCprime hlog_nonneg
  constructor
  · calc
      exactDivisorEventDoubleCarrier P a X D
          = (Inputs.primeRecipWindow P X / (D : ℝ)) *
              exactDivisorMPhiTensorFiberCoprime P X D (a X D) := rfl
      _ ≤ ((Cprime * Real.log X) / (D : ℝ)) *
            exactDivisorMPhiTensorFiberCoprime P X D (a X D) :=
          mul_le_mul_of_nonneg_right hprime_div_le htensor_nonneg
      _ ≤ ((Cprime * Real.log X) / (D : ℝ)) *
            ((Ktensor / cmass) * (exactDivisorMPhiMassRaw P X / (D : ℝ))) :=
          mul_le_mul_of_nonneg_left htensor_le hCprime_log_div_nonneg
      _ ≤ ((Cprime * Real.log X) / (D : ℝ)) *
            ((Ktensor / cmass) * ((Cmass * logSq X) / (D : ℝ))) := by
          have hmass_div :
              exactDivisorMPhiMassRaw P X / (D : ℝ) ≤
                (Cmass * logSq X) / (D : ℝ) :=
            div_le_div_of_nonneg_right hmass_le hD_nonneg
          have hmul := mul_le_mul_of_nonneg_left hmass_div hKc_nonneg
          exact mul_le_mul_of_nonneg_left hmul hCprime_log_div_nonneg
      _ = (Cprime * (Ktensor / cmass) * Cmass) *
            (logCube X / (D : ℝ) ^ 2) := by
          unfold logSq logCube
          field_simp [ne_of_gt hD_pos, ne_of_gt hD_sq_pos]
          ring
  · calc
      exactDivisorEventSingleCarrier P a X D
          = Inputs.primeRecipWindow P X *
              exactDivisorMPhiTensorFiberCoprime P X D (a X D) := rfl
      _ ≤ (Cprime * Real.log X) *
            exactDivisorMPhiTensorFiberCoprime P X D (a X D) :=
          mul_le_mul_of_nonneg_right hprime_le htensor_nonneg
      _ ≤ (Cprime * Real.log X) *
            ((Ktensor / cmass) * (exactDivisorMPhiMassRaw P X / (D : ℝ))) :=
          mul_le_mul_of_nonneg_left htensor_le hCprime_log_nonneg
      _ ≤ (Cprime * Real.log X) *
            ((Ktensor / cmass) * ((Cmass * logSq X) / (D : ℝ))) := by
          have hmass_div :
              exactDivisorMPhiMassRaw P X / (D : ℝ) ≤
                (Cmass * logSq X) / (D : ℝ) :=
            div_le_div_of_nonneg_right hmass_le hD_nonneg
          have hmul := mul_le_mul_of_nonneg_left hmass_div hKc_nonneg
          exact mul_le_mul_of_nonneg_left hmul hCprime_log_nonneg
      _ = (Cprime * (Ktensor / cmass) * Cmass) *
            (logCube X / (D : ℝ)) := by
          unfold logSq logCube
          field_simp [ne_of_gt hD_pos]
          ring

/-- The `τ(r)/r` majorant carrier is nonnegative. -/
theorem phiProgressionTauAverage_nonneg
    (P : Params) (X : ℝ) (d a s : ℕ) :
    0 ≤ phiProgressionTauAverage P X d a s := by
  classical
  unfold phiProgressionTauAverage
  apply Finset.sum_nonneg
  intro r hr
  have hr_window :
      r ∈ Inputs.natWindow (phiProgressionU0 P s X)
        (phiProgressionU1 P s X) :=
    (Finset.mem_filter.mp hr).1
  have hr_pos_nat : 0 < r := by
    unfold Inputs.natWindow at hr_window
    exact lt_of_lt_of_le Nat.zero_lt_one
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hr_window).1).1
  exact div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hr_pos_nat.le)

/-- The `τ(r)/r` majorant is exactly the divisor-expanded carrier. -/
theorem phiProgressionTauAverage_eq_divisorAverage
    (P : Params) (X : ℝ) (d a s : ℕ) :
    phiProgressionTauAverage P X d a s =
      phiProgressionTauDivisorAverage P X d a s := by
  classical
  unfold phiProgressionTauAverage phiProgressionTauDivisorAverage Inputs.tau
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

/-- The divisor-expanded `τ(r)/r` carrier equals its sigma-indexed pair form. -/
theorem phiProgressionTauDivisorAverage_eq_sigmaAverage
    (P : Params) (X : ℝ) (d a s : ℕ) :
    phiProgressionTauDivisorAverage P X d a s =
      phiProgressionTauSigmaAverage P X d a s := by
  classical
  unfold phiProgressionTauDivisorAverage phiProgressionTauSigmaAverage
  exact Finset.sum_sigma'
    ((Inputs.natWindow (phiProgressionU0 P s X)
        (phiProgressionU1 P s X)).filter
        (fun r => Squarefree r ∧ Nat.Coprime r s ∧ Inputs.congMod r a d))
    (fun r => r.divisors)
    (fun r _k => (1 : ℝ) / (r : ℝ))

/-- The original `τ(r)/r` majorant carrier equals the sigma-indexed pair form. -/
theorem phiProgressionTauAverage_eq_sigmaAverage
    (P : Params) (X : ℝ) (d a s : ℕ) :
    phiProgressionTauAverage P X d a s =
      phiProgressionTauSigmaAverage P X d a s := by
  rw [phiProgressionTauAverage_eq_divisorAverage,
    phiProgressionTauDivisorAverage_eq_sigmaAverage]

/-- On the sigma support, the exposed divisor `k=x.2` really splits
`r=x.1` as `r = k·(r/k)`. -/
theorem phiProgressionTauSigma_mem_mul_div
    {S : Finset ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ S.sigma (fun r => r.divisors)) :
    x.2 * (x.1 / x.2) = x.1 := by
  have hxdiv : x.2 ∈ x.1.divisors := (Finset.mem_sigma.mp hx).2
  exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hxdiv)

/-- The exposed divisor `k=x.2` is positive on the sigma-divisor support. -/
theorem phiProgressionTauSigma_mem_divisor_pos
    {S : Finset ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ S.sigma (fun r => r.divisors)) :
    0 < x.2 := by
  have hxdiv : x.2 ∈ x.1.divisors := (Finset.mem_sigma.mp hx).2
  exact Nat.pos_of_mem_divisors hxdiv

/-- The quotient `t=x.1/x.2` is positive on the sigma-divisor support. -/
theorem phiProgressionTauSigma_mem_quotient_pos
    {S : Finset ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ S.sigma (fun r => r.divisors)) :
    0 < x.1 / x.2 := by
  have hxdiv : x.2 ∈ x.1.divisors := (Finset.mem_sigma.mp hx).2
  have hx1_ne : x.1 ≠ 0 := (Nat.mem_divisors.mp hxdiv).2
  have hsplit : x.2 * (x.1 / x.2) = x.1 :=
    phiProgressionTauSigma_mem_mul_div hx
  by_contra hnot
  have hquot_zero : x.1 / x.2 = 0 := Nat.eq_zero_of_not_pos hnot
  have hx1_zero : x.1 = 0 := by
    simpa [hquot_zero] using hsplit.symm
  exact hx1_ne hx1_zero

/-- Reconstructing `r=k·(r/k)` from a sigma-divisor point returns an element of
the original outer support. -/
theorem phiProgressionTauSigma_mem_reconstructed
    {S : Finset ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ S.sigma (fun r => r.divisors)) :
    x.2 * (x.1 / x.2) ∈ S := by
  have hx_outer : x.1 ∈ S := (Finset.mem_sigma.mp hx).1
  have hsplit : x.2 * (x.1 / x.2) = x.1 :=
    phiProgressionTauSigma_mem_mul_div hx
  simpa [hsplit] using hx_outer

/-- The generic sigma-support split, specialized to the exact
`lem:phi-progression-average` support. -/
theorem phiProgressionDivisorSigmaSupport_mem_mul_div
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    x.2 * (x.1 / x.2) = x.1 := by
  unfold phiProgressionDivisorSigmaSupport at hx
  exact phiProgressionTauSigma_mem_mul_div hx

/-- Reconstructing `r=k·(r/k)` from an exact phi-progression sigma point
returns an element of the original phi-progression support. -/
theorem phiProgressionDivisorSigmaSupport_mem_reconstructed_support
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    x.2 * (x.1 / x.2) ∈ phiProgressionSupport P X d a s := by
  unfold phiProgressionDivisorSigmaSupport at hx
  exact phiProgressionTauSigma_mem_reconstructed hx

/-- The outer coordinate `r=x.1` of a phi-progression sigma point lies in the
exact phi-progression support. -/
theorem phiProgressionDivisorSigmaSupport_outer_mem_support
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    x.1 ∈ phiProgressionSupport P X d a s := by
  unfold phiProgressionDivisorSigmaSupport at hx
  exact (Finset.mem_sigma.mp hx).1

/-- The exposed divisor `k=x.2` divides the outer coordinate `r=x.1`. -/
theorem phiProgressionDivisorSigmaSupport_divisor_dvd
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    x.2 ∣ x.1 := by
  unfold phiProgressionDivisorSigmaSupport at hx
  exact Nat.dvd_of_mem_divisors (Finset.mem_sigma.mp hx).2

/-- The quotient `t=x.1/x.2` divides the outer coordinate `r=x.1`. -/
theorem phiProgressionDivisorSigmaSupport_quotient_dvd
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    x.1 / x.2 ∣ x.1 :=
  Nat.div_dvd_of_dvd (phiProgressionDivisorSigmaSupport_divisor_dvd hx)

/-- The outer coordinate `r=x.1` is squarefree. -/
theorem phiProgressionDivisorSigmaSupport_outer_squarefree
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    Squarefree x.1 := by
  classical
  have hmem := phiProgressionDivisorSigmaSupport_outer_mem_support (P := P)
    (X := X) (d := d) (a := a) (s := s) hx
  unfold phiProgressionSupport at hmem
  exact (Finset.mem_filter.mp hmem).2.1

/-- The exposed divisor `k=x.2` is squarefree. -/
theorem phiProgressionDivisorSigmaSupport_divisor_squarefree
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    Squarefree x.2 :=
  (phiProgressionDivisorSigmaSupport_outer_squarefree hx).squarefree_of_dvd
    (phiProgressionDivisorSigmaSupport_divisor_dvd hx)

/-- The quotient `t=x.1/x.2` is squarefree. -/
theorem phiProgressionDivisorSigmaSupport_quotient_squarefree
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    Squarefree (x.1 / x.2) :=
  (phiProgressionDivisorSigmaSupport_outer_squarefree hx).squarefree_of_dvd
    (phiProgressionDivisorSigmaSupport_quotient_dvd hx)

/-- The outer coordinate `r=x.1` is coprime to the conductor `s`. -/
theorem phiProgressionDivisorSigmaSupport_outer_coprime_s
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    Nat.Coprime x.1 s := by
  classical
  have hmem := phiProgressionDivisorSigmaSupport_outer_mem_support (P := P)
    (X := X) (d := d) (a := a) (s := s) hx
  unfold phiProgressionSupport at hmem
  exact (Finset.mem_filter.mp hmem).2.2.1

/-- The exposed divisor `k=x.2` is coprime to the conductor `s`. -/
theorem phiProgressionDivisorSigmaSupport_divisor_coprime_s
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    Nat.Coprime x.2 s :=
  (phiProgressionDivisorSigmaSupport_outer_coprime_s hx).coprime_dvd_left
    (phiProgressionDivisorSigmaSupport_divisor_dvd hx)

/-- The quotient `t=x.1/x.2` is coprime to the conductor `s`. -/
theorem phiProgressionDivisorSigmaSupport_quotient_coprime_s
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    Nat.Coprime (x.1 / x.2) s :=
  (phiProgressionDivisorSigmaSupport_outer_coprime_s hx).coprime_dvd_left
    (phiProgressionDivisorSigmaSupport_quotient_dvd hx)

/-- If the residue class is admissible, the outer coordinate `r=x.1` is
coprime to the progression modulus `d`. -/
theorem phiProgressionDivisorSigmaSupport_outer_coprime_d
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (ha : Nat.Coprime a d)
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    Nat.Coprime x.1 d := by
  classical
  have hmem := phiProgressionDivisorSigmaSupport_outer_mem_support (P := P)
    (X := X) (d := d) (a := a) (s := s) hx
  have hcong : x.1 ≡ a [MOD d] := by
    unfold phiProgressionSupport at hmem
    exact (Finset.mem_filter.mp hmem).2.2.2
  rw [Nat.coprime_iff_gcd_eq_one]
  rw [hcong.gcd_eq]
  exact Nat.coprime_iff_gcd_eq_one.mp ha

/-- For admissible residue class `a`, the exposed divisor `k=x.2` is
coprime to the progression modulus `d`. -/
theorem phiProgressionDivisorSigmaSupport_divisor_coprime_d
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (ha : Nat.Coprime a d)
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    Nat.Coprime x.2 d :=
  (phiProgressionDivisorSigmaSupport_outer_coprime_d ha hx).coprime_dvd_left
    (phiProgressionDivisorSigmaSupport_divisor_dvd hx)

/-- For admissible residue class `a`, the quotient `t=x.1/x.2` is coprime
to the progression modulus `d`. -/
theorem phiProgressionDivisorSigmaSupport_quotient_coprime_d
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (ha : Nat.Coprime a d)
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    Nat.Coprime (x.1 / x.2) d :=
  (phiProgressionDivisorSigmaSupport_outer_coprime_d ha hx).coprime_dvd_left
    (phiProgressionDivisorSigmaSupport_quotient_dvd hx)

/-- The reconstructed quotient product lies in the exact natural window
`U₀ < k·t ≤ U₁`. -/
theorem phiProgressionDivisorSigmaSupport_reconstructed_mem_window
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    x.2 * (x.1 / x.2) ∈
      Inputs.natWindow (phiProgressionU0 P s X) (phiProgressionU1 P s X) := by
  classical
  have hmem := phiProgressionDivisorSigmaSupport_mem_reconstructed_support (P := P)
    (X := X) (d := d) (a := a) (s := s) hx
  unfold phiProgressionSupport at hmem
  exact (Finset.mem_filter.mp hmem).1

/-- The reconstructed quotient product is squarefree. -/
theorem phiProgressionDivisorSigmaSupport_reconstructed_squarefree
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    Squarefree (x.2 * (x.1 / x.2)) := by
  classical
  have hmem := phiProgressionDivisorSigmaSupport_mem_reconstructed_support (P := P)
    (X := X) (d := d) (a := a) (s := s) hx
  unfold phiProgressionSupport at hmem
  exact (Finset.mem_filter.mp hmem).2.1

/-- In the squarefree quotient split `r=k·t`, the divisor `k` and quotient
`t` are coprime. -/
theorem phiProgressionDivisorSigmaSupport_divisor_coprime_quotient
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    Nat.Coprime x.2 (x.1 / x.2) :=
  Nat.coprime_of_squarefree_mul
    (phiProgressionDivisorSigmaSupport_reconstructed_squarefree hx)

/-- In the quotient split `r=k·t`, the quotient `t` is coprime to `s·k`. -/
theorem phiProgressionDivisorSigmaSupport_quotient_coprime_s_mul_divisor
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    Nat.Coprime (x.1 / x.2) (s * x.2) :=
  Nat.Coprime.mul_right
    (phiProgressionDivisorSigmaSupport_quotient_coprime_s hx)
    (phiProgressionDivisorSigmaSupport_divisor_coprime_quotient hx).symm

/-- For admissible residue class `a`, the quotient `t` is coprime to `s·d`. -/
theorem phiProgressionDivisorSigmaSupport_quotient_coprime_s_mul_d
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (ha : Nat.Coprime a d)
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    Nat.Coprime (x.1 / x.2) (s * d) :=
  Nat.Coprime.mul_right
    (phiProgressionDivisorSigmaSupport_quotient_coprime_s hx)
    (phiProgressionDivisorSigmaSupport_quotient_coprime_d ha hx)

/-- For admissible residue class `a`, the quotient `t` is coprime to
`s·d·k`, the combined local modulus attached to the quotient split. -/
theorem phiProgressionDivisorSigmaSupport_quotient_coprime_s_mul_d_mul_divisor
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (ha : Nat.Coprime a d)
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    Nat.Coprime (x.1 / x.2) ((s * d) * x.2) :=
  Nat.Coprime.mul_right
    (phiProgressionDivisorSigmaSupport_quotient_coprime_s_mul_d ha hx)
    (phiProgressionDivisorSigmaSupport_divisor_coprime_quotient hx).symm

/-- The reconstructed quotient product remains coprime to the conductor `s`. -/
theorem phiProgressionDivisorSigmaSupport_reconstructed_coprime_s
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    Nat.Coprime (x.2 * (x.1 / x.2)) s := by
  classical
  have hmem := phiProgressionDivisorSigmaSupport_mem_reconstructed_support (P := P)
    (X := X) (d := d) (a := a) (s := s) hx
  unfold phiProgressionSupport at hmem
  exact (Finset.mem_filter.mp hmem).2.2.1

/-- The reconstructed quotient product satisfies the original residue condition. -/
theorem phiProgressionDivisorSigmaSupport_reconstructed_cong
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    Inputs.congMod (x.2 * (x.1 / x.2)) a d := by
  classical
  have hmem := phiProgressionDivisorSigmaSupport_mem_reconstructed_support (P := P)
    (X := X) (d := d) (a := a) (s := s) hx
  unfold phiProgressionSupport at hmem
  exact (Finset.mem_filter.mp hmem).2.2.2

/-- For admissible residue class `a`, the exposed divisor `k=x.2` has a
modular inverse modulo `d`.  The statement is existential so that the modulus
`d=1` edge case is handled uniformly. -/
theorem phiProgressionDivisorSigmaSupport_divisor_mod_inverse
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hd : 0 < d)
    (ha : Nat.Coprime a d)
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    ∃ b : ℕ, x.2 * b ≡ 1 [MOD d] := by
  classical
  by_cases hd_one : d = 1
  · subst d
    exact ⟨0, by simp [Nat.ModEq]⟩
  · have hd_gt_one : 1 < d := by
      exact lt_of_le_of_ne (Nat.succ_le_of_lt hd) (Ne.symm hd_one)
    obtain ⟨b, hb⟩ := Nat.exists_mul_emod_eq_one_of_coprime
      (k := d) (n := x.2)
      (phiProgressionDivisorSigmaSupport_divisor_coprime_d ha hx) hd_gt_one
    refine ⟨b, ?_⟩
    rw [Nat.ModEq, hb, Nat.mod_eq_of_lt hd_gt_one]

/-- If `b` is an inverse of the exposed divisor `k=x.2` modulo `d`, then the
quotient `t=x.1/x.2` lies in the residue class `a·b` modulo `d`. -/
theorem phiProgressionDivisorSigmaSupport_quotient_cong_of_divisor_inverse
    {P : Params} {X : ℝ} {d a s b : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hb : x.2 * b ≡ 1 [MOD d])
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    Inputs.congMod (x.1 / x.2) (a * b) d := by
  classical
  have hrt : x.2 * (x.1 / x.2) ≡ a [MOD d] :=
    phiProgressionDivisorSigmaSupport_reconstructed_cong hx
  have hright :
      (x.2 * b) * (x.1 / x.2) ≡ a * b [MOD d] := by
    have hmul := hrt.mul_right b
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  have hleft :
      (x.2 * b) * (x.1 / x.2) ≡ x.1 / x.2 [MOD d] := by
    have hmul := hb.mul_right (x.1 / x.2)
    simpa [Nat.mul_assoc] using hmul
  exact hleft.symm.trans hright

/-- The quotient split supplies an explicit residue class for
`t=x.1/x.2`, namely `a` multiplied by some inverse of `k=x.2` modulo `d`. -/
theorem phiProgressionDivisorSigmaSupport_exists_quotient_inverse_residue
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hd : 0 < d)
    (ha : Nat.Coprime a d)
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    ∃ b : ℕ,
      x.2 * b ≡ 1 [MOD d] ∧ Inputs.congMod (x.1 / x.2) (a * b) d := by
  classical
  obtain ⟨b, hb⟩ :=
    phiProgressionDivisorSigmaSupport_divisor_mod_inverse (P := P) (X := X)
      (d := d) (a := a) (s := s) (x := x) hd ha hx
  exact ⟨b, hb,
    phiProgressionDivisorSigmaSupport_quotient_cong_of_divisor_inverse
      (P := P) (X := X) (d := d) (a := a) (s := s) (b := b) (x := x) hb hx⟩

/-- If `k*t` lies in a natural window and `k>0`, then `t` lies in the
corresponding scaled quotient window. -/
theorem natWindow_divisor_quotient_mem
    {U₀ U₁ : ℝ} {k t : ℕ} (hk : 0 < k)
    (hkt : k * t ∈ Inputs.natWindow U₀ U₁) :
    t ∈ Inputs.natWindow (U₀ / (k : ℝ)) (U₁ / (k : ℝ)) := by
  classical
  unfold Inputs.natWindow at hkt ⊢
  rcases Finset.mem_filter.mp hkt with ⟨hIcc, hlo⟩
  rcases Finset.mem_Icc.mp hIcc with ⟨hkt_one, hkt_floor⟩
  have hkt_pos : 0 < k * t := lt_of_lt_of_le Nat.zero_lt_one hkt_one
  have ht_pos : 0 < t := pos_of_mul_pos_right hkt_pos (Nat.zero_le k)
  have ht_one : 1 ≤ t := Nat.succ_le_of_lt ht_pos
  have hkR_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hU₁_one : (1 : ℝ) ≤ U₁ := by
    rw [← Nat.one_le_floor_iff]
    exact le_trans hkt_one hkt_floor
  have hU₁_nonneg : 0 ≤ U₁ := le_trans zero_le_one hU₁_one
  have hkt_le_U₁ : ((k * t : ℕ) : ℝ) ≤ U₁ :=
    le_trans (by exact_mod_cast hkt_floor) (Nat.floor_le hU₁_nonneg)
  have ht_le_scaled : (t : ℝ) ≤ U₁ / (k : ℝ) := by
    rw [le_div_iff₀ hkR_pos]
    simpa [Nat.cast_mul, mul_comm] using hkt_le_U₁
  have ht_floor : t ≤ ⌊U₁ / (k : ℝ)⌋₊ := Nat.le_floor ht_le_scaled
  have hlo_scaled : U₀ / (k : ℝ) < (t : ℝ) := by
    rw [div_lt_iff₀ hkR_pos]
    simpa [Nat.cast_mul, mul_comm] using hlo
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨ht_one, ht_floor⟩, hlo_scaled⟩

/-- The fixed-divisor quotient fiber is bounded by the unrestricted quotient
reciprocal window after dropping congruence, squarefreeness, and coprimality.
This is the finite-carrier form of the manuscript's large-`k` simplification
before the harmonic/logarithmic interval estimate is applied. -/
theorem phiProgressionFixedKQuotientRecipFiber_le_unrestrictedProgressionRecip
    (P : Params) (X : ℝ) (d a s k : ℕ) (hk : 0 < k) :
    phiProgressionFixedKQuotientRecipFiber P X d a s k ≤
      Inputs.progressionRecip 1 0
        (phiProgressionU0 P s X / (k : ℝ))
        (phiProgressionU1 P s X / (k : ℝ)) := by
  classical
  let F :=
    (phiProgressionDivisorSigmaSupport P X d a s).filter
      (fun x => x.2 = k)
  let T :=
    (Inputs.natWindow (phiProgressionU0 P s X / (k : ℝ))
      (phiProgressionU1 P s X / (k : ℝ))).filter
      (fun t => Inputs.congMod t 0 1)
  let q : (Sigma fun _r : ℕ => ℕ) → ℕ := fun x => x.1 / x.2
  have hsource_image :
      (∑ x ∈ F, (1 : ℝ) / ((q x : ℕ) : ℝ)) =
        ∑ t ∈ F.image q, (1 : ℝ) / (t : ℝ) := by
    rw [Finset.sum_image]
    intro x hx y hy hxy
    have hxbase : x ∈ phiProgressionDivisorSigmaSupport P X d a s :=
      (Finset.mem_filter.mp hx).1
    have hybase : y ∈ phiProgressionDivisorSigmaSupport P X d a s :=
      (Finset.mem_filter.mp hy).1
    have hxk : x.2 = k := (Finset.mem_filter.mp hx).2
    have hyk : y.2 = k := (Finset.mem_filter.mp hy).2
    have hxsplit : x.2 * (x.1 / x.2) = x.1 :=
      phiProgressionDivisorSigmaSupport_mem_mul_div hxbase
    have hysplit : y.2 * (y.1 / y.2) = y.1 :=
      phiProgressionDivisorSigmaSupport_mem_mul_div hybase
    rcases x with ⟨xr, xk⟩
    rcases y with ⟨yr, yk⟩
    simp only at hxk hyk hxy hxsplit hysplit ⊢
    subst xk
    subst yk
    have hfirst : xr = yr := by
      calc
        xr = k * (xr / k) := hxsplit.symm
        _ = k * (yr / k) := by
          have hquot : xr / k = yr / k := by simpa [q] using hxy
          rw [hquot]
        _ = yr := hysplit
    subst yr
    rfl
  have hsubset : F.image q ⊆ T := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨x, hx, rfl⟩
    have hxbase : x ∈ phiProgressionDivisorSigmaSupport P X d a s :=
      (Finset.mem_filter.mp hx).1
    have hxk : x.2 = k := (Finset.mem_filter.mp hx).2
    have hwindow :
        x.1 / x.2 ∈
          Inputs.natWindow (phiProgressionU0 P s X / (k : ℝ))
            (phiProgressionU1 P s X / (k : ℝ)) := by
      have hkt :
          k * (x.1 / x.2) ∈
            Inputs.natWindow (phiProgressionU0 P s X)
              (phiProgressionU1 P s X) := by
        simpa [hxk] using
          phiProgressionDivisorSigmaSupport_reconstructed_mem_window
            (P := P) (X := X) (d := d) (a := a) (s := s) (x := x) hxbase
      exact natWindow_divisor_quotient_mem (U₀ := phiProgressionU0 P s X)
        (U₁ := phiProgressionU1 P s X) (k := k) (t := x.1 / x.2) hk hkt
    have hcong : Inputs.congMod (x.1 / x.2) 0 1 := by
      unfold Inputs.congMod
      exact Nat.mod_one (x.1 / x.2)
    exact Finset.mem_filter.mpr ⟨hwindow, hcong⟩
  have hnonneg :
      ∀ t ∈ T, t ∉ F.image q →
        0 ≤ (1 : ℝ) / (t : ℝ) := by
    intro t _ht _hnot
    exact div_nonneg zero_le_one (Nat.cast_nonneg t)
  have hmain :
      (∑ x ∈ F, (1 : ℝ) / ((q x : ℕ) : ℝ)) ≤
        ∑ t ∈ T, (1 : ℝ) / (t : ℝ) := by
    rw [hsource_image]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
  simpa [phiProgressionFixedKQuotientRecipFiber, Inputs.progressionRecip, F, T, q]
    using hmain

/-- Modulus-preserving version of the fixed-`k` quotient containment.  Given
an inverse `b` of `k` modulo `d`, every quotient lies in the single residue
class `a*b (mod d)`. -/
theorem phiProgressionFixedKQuotientRecipFiber_le_progressionRecip_of_inverse
    (P : Params) (X : ℝ) (d a s k b : ℕ) (hk : 0 < k)
    (hb : k * b ≡ 1 [MOD d]) :
    phiProgressionFixedKQuotientRecipFiber P X d a s k ≤
      Inputs.progressionRecip d (a * b)
        (phiProgressionU0 P s X / (k : ℝ))
        (phiProgressionU1 P s X / (k : ℝ)) := by
  classical
  let F :=
    (phiProgressionDivisorSigmaSupport P X d a s).filter
      (fun x => x.2 = k)
  let T :=
    (Inputs.natWindow (phiProgressionU0 P s X / (k : ℝ))
      (phiProgressionU1 P s X / (k : ℝ))).filter
      (fun t => Inputs.congMod t (a * b) d)
  let q : (Sigma fun _r : ℕ => ℕ) → ℕ := fun x => x.1 / x.2
  have hsource_image :
      (∑ x ∈ F, (1 : ℝ) / ((q x : ℕ) : ℝ)) =
        ∑ t ∈ F.image q, (1 : ℝ) / (t : ℝ) := by
    rw [Finset.sum_image]
    intro x hx y hy hxy
    have hxbase : x ∈ phiProgressionDivisorSigmaSupport P X d a s :=
      (Finset.mem_filter.mp hx).1
    have hybase : y ∈ phiProgressionDivisorSigmaSupport P X d a s :=
      (Finset.mem_filter.mp hy).1
    have hxk : x.2 = k := (Finset.mem_filter.mp hx).2
    have hyk : y.2 = k := (Finset.mem_filter.mp hy).2
    have hxsplit : x.2 * (x.1 / x.2) = x.1 :=
      phiProgressionDivisorSigmaSupport_mem_mul_div hxbase
    have hysplit : y.2 * (y.1 / y.2) = y.1 :=
      phiProgressionDivisorSigmaSupport_mem_mul_div hybase
    rcases x with ⟨xr, xk⟩
    rcases y with ⟨yr, yk⟩
    simp only at hxk hyk hxy hxsplit hysplit ⊢
    subst xk
    subst yk
    have hfirst : xr = yr := by
      calc
        xr = k * (xr / k) := hxsplit.symm
        _ = k * (yr / k) := by
          have hquot : xr / k = yr / k := by simpa [q] using hxy
          rw [hquot]
        _ = yr := hysplit
    subst yr
    rfl
  have hsubset : F.image q ⊆ T := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨x, hx, rfl⟩
    have hxbase : x ∈ phiProgressionDivisorSigmaSupport P X d a s :=
      (Finset.mem_filter.mp hx).1
    have hxk : x.2 = k := (Finset.mem_filter.mp hx).2
    have hwindow :
        x.1 / x.2 ∈
          Inputs.natWindow (phiProgressionU0 P s X / (k : ℝ))
            (phiProgressionU1 P s X / (k : ℝ)) := by
      have hkt :
          k * (x.1 / x.2) ∈
            Inputs.natWindow (phiProgressionU0 P s X)
              (phiProgressionU1 P s X) := by
        simpa [hxk] using
          phiProgressionDivisorSigmaSupport_reconstructed_mem_window
            (P := P) (X := X) (d := d) (a := a) (s := s) (x := x) hxbase
      exact natWindow_divisor_quotient_mem (U₀ := phiProgressionU0 P s X)
        (U₁ := phiProgressionU1 P s X) (k := k) (t := x.1 / x.2) hk hkt
    have hcong : Inputs.congMod (x.1 / x.2) (a * b) d :=
      phiProgressionDivisorSigmaSupport_quotient_cong_of_divisor_inverse
        (P := P) (X := X) (d := d) (a := a) (s := s) (b := b)
        (x := x) (by simpa [hxk] using hb) hxbase
    exact Finset.mem_filter.mpr ⟨hwindow, hcong⟩
  have hnonneg :
      ∀ t ∈ T, t ∉ F.image q →
        0 ≤ (1 : ℝ) / (t : ℝ) := by
    intro t _ht _hnot
    exact div_nonneg zero_le_one (Nat.cast_nonneg t)
  have hmain :
      (∑ x ∈ F, (1 : ℝ) / ((q x : ℕ) : ℝ)) ≤
        ∑ t ∈ T, (1 : ℝ) / (t : ℝ) := by
    rw [hsource_image]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
  simpa [phiProgressionFixedKQuotientRecipFiber, Inputs.progressionRecip, F, T, q]
    using hmain

/-- Modulus-preserving fixed-`k` containment using the canonical inverse when
`k` is coprime to the progression modulus. -/
theorem phiProgressionFixedKQuotientRecipFiber_le_progressionRecip_of_coprime
    (P : Params) (X : ℝ) (d a s k : ℕ) (hd : 0 < d) (hk : 0 < k)
    (hkd : Nat.Coprime k d) :
    phiProgressionFixedKQuotientRecipFiber P X d a s k ≤
      Inputs.progressionRecip d (a * modInverseChoice d k)
        (phiProgressionU0 P s X / (k : ℝ))
        (phiProgressionU1 P s X / (k : ℝ)) :=
  phiProgressionFixedKQuotientRecipFiber_le_progressionRecip_of_inverse
    P X d a s k (modInverseChoice d k) hk
      (modInverseChoice_coprime hd hkd)

/-- The sigma-indexed `τ(r)/r` carrier is exactly the quotient-split
`1/(k·t)` carrier on the same support. -/
theorem phiProgressionTauSigmaAverage_eq_quotientAverage
    (P : Params) (X : ℝ) (d a s : ℕ) :
    phiProgressionTauSigmaAverage P X d a s =
      phiProgressionTauQuotientAverage P X d a s := by
  classical
  unfold phiProgressionTauSigmaAverage phiProgressionTauQuotientAverage
  apply Finset.sum_congr rfl
  intro x hx
  have hsplit : x.2 * (x.1 / x.2) = x.1 :=
    phiProgressionTauSigma_mem_mul_div hx
  have hden :
      (x.2 : ℝ) * ((x.1 / x.2 : ℕ) : ℝ) = (x.1 : ℝ) := by
    rw [← Nat.cast_mul, hsplit]
  rw [hden]

/-- The original `τ(r)/r` majorant carrier is exactly the quotient-split
sigma carrier `∑_{r,k|r} 1/(k·(r/k))`. -/
theorem phiProgressionTauAverage_eq_quotientAverage
    (P : Params) (X : ℝ) (d a s : ℕ) :
    phiProgressionTauAverage P X d a s =
      phiProgressionTauQuotientAverage P X d a s := by
  rw [phiProgressionTauAverage_eq_sigmaAverage,
    phiProgressionTauSigmaAverage_eq_quotientAverage]

/-- The arithmetic function `γ(k)=∏_{p|k}1/(p-1)` is multiplicative. -/
theorem phiGammaAF_multiplicative :
    phiGammaAF.IsMultiplicative := by
  unfold phiGammaAF
  exact ArithmeticFunction.IsMultiplicative.prodPrimeFactors
    (R := ℝ) (fun p : ℕ => (1 : ℝ) / ((p : ℝ) - 1))

/-- At a prime, the `γ` arithmetic function has the expected local value. -/
theorem phiGammaAF_apply_prime {p : ℕ} (hp : Nat.Prime p) :
    phiGammaAF p = (1 : ℝ) / ((p : ℝ) - 1) := by
  unfold phiGammaAF
  rw [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors]
  simp

/-- Product form of `γ(k)` over the prime factors of a nonzero `k`. -/
theorem phiGamma_eq_primeFactorProduct {k : ℕ} (hk : k ≠ 0) :
    phiGamma k = ∏ p ∈ k.primeFactors, (1 : ℝ) / ((p : ℝ) - 1) := by
  unfold phiGamma phiGammaAF
  exact ArithmeticFunction.prodPrimeFactors_apply (R := ℝ)
    (f := fun p : ℕ => (1 : ℝ) / ((p : ℝ) - 1)) hk

/-- The manuscript's `γ(k)` weight is nonnegative. -/
theorem phiGamma_nonneg (k : ℕ) :
    0 ≤ phiGamma k := by
  by_cases hk : k = 0
  · simp [phiGamma, phiGammaAF, hk]
  · rw [phiGamma_eq_primeFactorProduct hk]
    apply Finset.prod_nonneg
    intro p hp
    have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hp_gt_one : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.one_lt
    exact div_nonneg zero_le_one (sub_nonneg.mpr hp_gt_one.le)

/-- Every nonzero gamma weight is at most one: each prime-local factor
`1/(p-1)` is bounded by `1`. -/
theorem phiGamma_le_one_of_ne_zero {k : ℕ} (hk : k ≠ 0) :
    phiGamma k ≤ 1 := by
  rw [phiGamma_eq_primeFactorProduct hk]
  calc
    (∏ p ∈ k.primeFactors, (1 : ℝ) / ((p : ℝ) - 1))
        ≤ ∏ _p ∈ k.primeFactors, (1 : ℝ) := by
          apply Finset.prod_le_prod
          · intro p hp
            have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
            have hp_gt_one : (1 : ℝ) < (p : ℝ) := by
              exact_mod_cast hpPrime.one_lt
            exact div_nonneg zero_le_one (sub_nonneg.mpr hp_gt_one.le)
          · intro p hp
            have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
            have hp_two : (2 : ℝ) ≤ (p : ℝ) := by
              exact_mod_cast hpPrime.two_le
            have hp_pred_ge_one : (1 : ℝ) ≤ (p : ℝ) - 1 := by
              linarith
            simpa [one_div] using inv_le_one_of_one_le₀ hp_pred_ge_one
    _ = 1 := by simp

/-- Local comparison used in the Euler-product majorant for `γ(k)`: each
prime factor contributes at most `2/p`. -/
theorem phiGamma_le_two_pow_omega_div_primeRad {k : ℕ} (hk : k ≠ 0) :
    phiGamma k ≤ ((2 : ℝ) ^ Inputs.omega k) / (primeRad k : ℝ) := by
  rw [phiGamma_eq_primeFactorProduct hk]
  have hprod :
      (∏ p ∈ k.primeFactors, (1 : ℝ) / ((p : ℝ) - 1)) ≤
        ∏ p ∈ k.primeFactors, (2 : ℝ) / (p : ℝ) := by
    apply Finset.prod_le_prod
    · intro p hp
      have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
      have hp_gt_one : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.one_lt
      exact div_nonneg (by norm_num) (sub_nonneg.mpr hp_gt_one.le)
    · intro p hp
      have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
      have hp_ge_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpPrime.two_le
      have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
      have hden_pos : 0 < (p : ℝ) - 1 := by linarith
      rw [div_le_div_iff₀ hden_pos hp_pos]
      nlinarith
  refine le_trans hprod ?_
  unfold primeRad Inputs.omega
  rw [Finset.prod_div_distrib]
  simp [Finset.prod_const, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- Divided form of `phiGamma_le_two_pow_omega_div_primeRad`, matching the
coefficient series `∑ γ(k)/k`. -/
theorem phiGamma_div_nat_le_two_pow_omega_div_primeRad_mul_nat
    {k : ℕ} (hk : k ≠ 0) :
    phiGamma k / (k : ℝ) ≤
      ((2 : ℝ) ^ Inputs.omega k) / ((primeRad k : ℝ) * (k : ℝ)) := by
  have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  calc
    phiGamma k / (k : ℝ)
        ≤ (((2 : ℝ) ^ Inputs.omega k) / (primeRad k : ℝ)) / (k : ℝ) :=
          div_le_div_of_nonneg_right
            (phiGamma_le_two_pow_omega_div_primeRad hk) hk_nonneg
    _ = ((2 : ℝ) ^ Inputs.omega k) / ((primeRad k : ℝ) * (k : ℝ)) := by
          field_simp [hk]

/-- The finite admissible gamma coefficient is nonnegative. -/
theorem phiProgressionGammaSmallAdmissibleGammaSum_nonneg
    (d s K : ℕ) :
    0 ≤ phiProgressionGammaSmallAdmissibleGammaSum d s K := by
  classical
  unfold phiProgressionGammaSmallAdmissibleGammaSum
  apply Finset.sum_nonneg
  intro k hk
  by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
  · rw [if_pos hadm]
    exact phiGamma_nonneg k
  · rw [if_neg hadm]

/-- Crude endpoint coefficient bound for the admissible gamma sum.  This is
the deterministic coefficient estimate behind the endpoint part of the
elementary progression envelope. -/
theorem phiProgressionGammaSmallAdmissibleGammaSum_le_nat
    (d s K : ℕ) :
    phiProgressionGammaSmallAdmissibleGammaSum d s K ≤ (K : ℝ) := by
  classical
  unfold phiProgressionGammaSmallAdmissibleGammaSum
  calc
    (∑ k ∈ Finset.Icc (1 : ℕ) K,
        if Nat.Coprime k d ∧ Nat.Coprime k s then phiGamma k else 0)
        ≤ ∑ _k ∈ Finset.Icc (1 : ℕ) K, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
          · rw [if_pos hadm]
            exact
              phiGamma_le_one_of_ne_zero
                (ne_of_gt (Finset.mem_Icc.mp hk).1)
          · rw [if_neg hadm]
            norm_num
    _ = ((Finset.Icc (1 : ℕ) K).card : ℝ) := by simp
    _ = (K : ℝ) := by
          have hcard : (Finset.Icc (1 : ℕ) K).card = K := by
            rw [Nat.card_Icc]
            omega
          exact_mod_cast hcard

/-- Power-cutoff endpoint coefficient bound:
`∑_{k≤X^κ} γ(k) ≤ X^κ`. -/
theorem phiProgressionGammaSmallAdmissibleGammaSum_le_rpow_powerCutoff
    {X κ : ℝ} {d s : ℕ} (hX : 0 ≤ X) :
    phiProgressionGammaSmallAdmissibleGammaSum d s
        (phiProgressionPowerCutoff κ X d s) ≤ X ^ κ :=
  le_trans (phiProgressionGammaSmallAdmissibleGammaSum_le_nat d s
    (phiProgressionPowerCutoff κ X d s))
    (nat_cast_phiProgressionPowerCutoff_le_rpow (d := d) (s := s) hX)

/-- Endpoint coefficient after dividing by the lower endpoint, using only the
power cutoff and the deterministic lower scale `U₀ ≥ X^(λ-η)`. -/
theorem
    phiProgressionGammaSmallAdmissibleGammaSum_mul_inv_U0_le_rpow_mul_inv_lower
    (P : Params) {X κ : ℝ} {d s : ℕ} (hX : 1 ≤ X) (hs : 1 ≤ s)
    (hsS : (s : ℝ) ≤ SScale P X) :
    phiProgressionGammaSmallAdmissibleGammaSum d s
          (phiProgressionPowerCutoff κ X d s) *
        (1 / phiProgressionU0 P s X) ≤
      X ^ κ * (1 / X ^ (P.lam - P.η)) := by
  have hX_nonneg : 0 ≤ X := le_trans (by norm_num : (0 : ℝ) ≤ 1) hX
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hgamma :
      phiProgressionGammaSmallAdmissibleGammaSum d s
          (phiProgressionPowerCutoff κ X d s) ≤ X ^ κ :=
    phiProgressionGammaSmallAdmissibleGammaSum_le_rpow_powerCutoff
      (d := d) (s := s) (κ := κ) hX_nonneg
  have hU0_lower :
      X ^ (P.lam - P.η) ≤ phiProgressionU0 P s X :=
    phiProgressionU0_ge_rpow_lam_sub_eta P hX hs hsS
  have hden_pos : 0 < X ^ (P.lam - P.η) :=
    Real.rpow_pos_of_pos hXpos (P.lam - P.η)
  have hU0_nonneg : 0 ≤ phiProgressionU0 P s X :=
    le_trans hden_pos.le hU0_lower
  have hinvU0_nonneg : 0 ≤ 1 / phiProgressionU0 P s X :=
    div_nonneg zero_le_one hU0_nonneg
  have hinv_le :
      1 / phiProgressionU0 P s X ≤ 1 / X ^ (P.lam - P.η) :=
    one_div_le_one_div_of_le hden_pos hU0_lower
  calc
    phiProgressionGammaSmallAdmissibleGammaSum d s
          (phiProgressionPowerCutoff κ X d s) *
        (1 / phiProgressionU0 P s X)
        ≤ X ^ κ * (1 / phiProgressionU0 P s X) :=
          mul_le_mul_of_nonneg_right hgamma hinvU0_nonneg
    _ ≤ X ^ κ * (1 / X ^ (P.lam - P.η)) :=
          mul_le_mul_of_nonneg_left hinv_le (Real.rpow_nonneg hX_nonneg κ)

/-- The finite admissible `γ(k)/k` coefficient is nonnegative. -/
theorem phiProgressionGammaSmallAdmissibleGammaDivSum_nonneg
    (d s K : ℕ) :
    0 ≤ phiProgressionGammaSmallAdmissibleGammaDivSum d s K := by
  classical
  unfold phiProgressionGammaSmallAdmissibleGammaDivSum
  apply Finset.sum_nonneg
  intro k hk
  by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
  · have hk_pos : 0 < k := (Finset.mem_Icc.mp hk).1
    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos.le
    rw [if_pos hadm]
    exact div_nonneg (phiGamma_nonneg k) hk_nonneg
  · rw [if_neg hadm]

/-- The admissible `γ(k)/k` coefficient is bounded by the full truncated
nonnegative coefficient series. -/
theorem phiProgressionGammaSmallAdmissibleGammaDivSum_le_phiGammaDivSum
    (d s K : ℕ) :
    phiProgressionGammaSmallAdmissibleGammaDivSum d s K ≤ phiGammaDivSum K := by
  classical
  unfold phiProgressionGammaSmallAdmissibleGammaDivSum phiGammaDivSum
  apply Finset.sum_le_sum
  intro k hk
  by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
  · rw [if_pos hadm]
  · rw [if_neg hadm]
    have hk_pos : 0 < k := (Finset.mem_Icc.mp hk).1
    exact div_nonneg (phiGamma_nonneg k) (by exact_mod_cast hk_pos.le)

/-- One-dimensional boundedness target for the gamma coefficient series. -/
def PhiGammaDivSummableBound : Prop :=
  ∃ Cgamma : ℝ, 0 < Cgamma ∧ ∀ K : ℕ, phiGammaDivSum K ≤ Cgamma

/-- Standard `Summable` formulation of the one-dimensional gamma coefficient
series. -/
def PhiGammaDivSummableSeries : Prop :=
  Summable (fun k : ℕ => phiGamma k / (k : ℝ))

/-- Euler-product-shaped majorant for the gamma coefficient series.  Its local
prime-power mass is summable with local size `2/(p(p-1))`. -/
noncomputable def phiGammaDivEulerMajorant (k : ℕ) : ℝ :=
  if k = 0 then 0
  else ((2 : ℝ) ^ Inputs.omega k) / ((primeRad k : ℝ) * (k : ℝ))

/-- Standard `Summable` target for the Euler-product-shaped majorant. -/
def PhiGammaDivEulerMajorantSummable : Prop :=
  Summable phiGammaDivEulerMajorant

/-- On a positive prime power, the `γ` weight is just the single local factor
`1/(p-1)`. -/
theorem phiGamma_prime_pow_succ {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    phiGamma (p ^ (e + 1)) = (1 : ℝ) / ((p : ℝ) - 1) := by
  rw [phiGamma_eq_primeFactorProduct (pow_ne_zero (e + 1) hp.ne_zero)]
  rw [Nat.primeFactors_pow p (Nat.succ_ne_zero e)]
  simp [hp.primeFactors]

/-- Exact positive-exponent local mass in the Euler product for the coefficient
series `∑ γ(k)/k`. -/
theorem phiGamma_primePowerDiv_positive_tsum {p : ℕ} (hp : Nat.Prime p) :
    (∑' e : ℕ, phiGamma (p ^ (e + 1)) / ((p ^ (e + 1) : ℕ) : ℝ)) =
      (1 : ℝ) / (((p : ℝ) - 1) ^ 2) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_one_lt : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp_pred_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp_inv_nonneg : 0 ≤ (1 : ℝ) / (p : ℝ) :=
    div_nonneg zero_le_one hp_pos.le
  have hp_inv_lt_one : (1 : ℝ) / (p : ℝ) < 1 := by
    rw [div_lt_one hp_pos]
    exact hp_one_lt
  calc
    (∑' e : ℕ, phiGamma (p ^ (e + 1)) / ((p ^ (e + 1) : ℕ) : ℝ))
        = ∑' e : ℕ,
            ((1 : ℝ) / ((p : ℝ) - 1)) * ((1 : ℝ) / (p : ℝ)) ^ (e + 1) := by
          apply tsum_congr
          intro e
          rw [phiGamma_prime_pow_succ hp e]
          rw [Nat.cast_pow]
          field_simp [ne_of_gt hp_pos, ne_of_gt hp_pred_pos]
    _ = ((1 : ℝ) / ((p : ℝ) - 1)) *
          ∑' e : ℕ, ((1 : ℝ) / (p : ℝ)) ^ (e + 1) := by
          rw [tsum_mul_left]
    _ = ((1 : ℝ) / ((p : ℝ) - 1)) *
          (((1 : ℝ) / (p : ℝ)) * ∑' e : ℕ, ((1 : ℝ) / (p : ℝ)) ^ e) := by
          congr 1
          rw [← tsum_mul_left]
          apply tsum_congr
          intro e
          rw [pow_succ']
    _ = ((1 : ℝ) / ((p : ℝ) - 1)) *
          (((1 : ℝ) / (p : ℝ)) * (1 - (1 : ℝ) / (p : ℝ))⁻¹) := by
          rw [tsum_geometric_of_lt_one hp_inv_nonneg hp_inv_lt_one]
    _ = (1 : ℝ) / (((p : ℝ) - 1) ^ 2) := by
          field_simp [ne_of_gt hp_pos, ne_of_gt hp_pred_pos]
          ring

/-- Summability of the positive-exponent local prime-power mass in the Euler
product for the coefficient series `∑ γ(k)/k`. -/
theorem phiGamma_primePowerDiv_positive_summable {p : ℕ} (hp : Nat.Prime p) :
    Summable (fun e : ℕ =>
      phiGamma (p ^ (e + 1)) / ((p ^ (e + 1) : ℕ) : ℝ)) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_one_lt : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp_pred_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp_inv_nonneg : 0 ≤ (1 : ℝ) / (p : ℝ) :=
    div_nonneg zero_le_one hp_pos.le
  have hp_inv_lt_one : (1 : ℝ) / (p : ℝ) < 1 := by
    rw [div_lt_one hp_pos]
    exact hp_one_lt
  have hgeom : Summable (fun e : ℕ => ((1 : ℝ) / (p : ℝ)) ^ e) :=
    summable_geometric_of_lt_one hp_inv_nonneg hp_inv_lt_one
  have hshift :
      Summable (fun e : ℕ => ((1 : ℝ) / (p : ℝ)) ^ (e + 1)) := by
    simpa [pow_succ'] using hgeom.mul_left ((1 : ℝ) / (p : ℝ))
  refine hshift.mul_left ((1 : ℝ) / ((p : ℝ) - 1)) |>.congr ?_
  intro e
  rw [phiGamma_prime_pow_succ hp e]
  rw [Nat.cast_pow]
  field_simp [ne_of_gt hp_pos, ne_of_gt hp_pred_pos]

/-- Norm-summability of the positive-exponent local prime-power mass. -/
theorem phiGamma_primePowerDiv_positive_norm_summable {p : ℕ} (hp : Nat.Prime p) :
    Summable (fun e : ℕ =>
      ‖phiGamma (p ^ (e + 1)) / ((p ^ (e + 1) : ℕ) : ℝ)‖) := by
  simpa only [Real.norm_eq_abs] using
    (phiGamma_primePowerDiv_positive_summable hp).abs

/-- Norm-summability of the full local prime-power mass, including the
`e = 0` Euler factor. -/
theorem phiGamma_primePowerDiv_norm_summable {p : ℕ} (hp : Nat.Prime p) :
    Summable (fun e : ℕ =>
      ‖phiGamma (p ^ e) / ((p ^ e : ℕ) : ℝ)‖) := by
  have htail := phiGamma_primePowerDiv_positive_norm_summable hp
  exact (_root_.summable_nat_add_iff
    (f := fun e : ℕ => ‖phiGamma (p ^ e) / ((p ^ e : ℕ) : ℝ)‖) 1).1 htail

/-- The coefficient function `k ↦ γ(k)/k` used in the logarithmic part of
`lem:phi-progression-average`. -/
noncomputable def phiGammaDivCoeff (k : ℕ) : ℝ :=
  phiGamma k / (k : ℝ)

/-- The coefficient function has Euler factor `1` at `k = 1`. -/
theorem phiGammaDivCoeff_one :
    phiGammaDivCoeff 1 = 1 := by
  unfold phiGammaDivCoeff
  rw [phiGamma_eq_primeFactorProduct (by norm_num : (1 : ℕ) ≠ 0)]
  simp

/-- The coefficient function is multiplicative on coprime arguments. -/
theorem phiGammaDivCoeff_mul_of_coprime {m n : ℕ}
    (h : Nat.Coprime m n) :
    phiGammaDivCoeff (m * n) =
      phiGammaDivCoeff m * phiGammaDivCoeff n := by
  unfold phiGammaDivCoeff
  rw [show phiGamma (m * n) = phiGamma m * phiGamma n by
    exact phiGammaAF_multiplicative.map_mul_of_coprime h]
  rw [Nat.cast_mul]
  by_cases hm : (m : ℝ) = 0
  · have hmnat : m = 0 := by exact_mod_cast hm
    subst m
    simp
  · by_cases hn : (n : ℝ) = 0
    · have hnnat : n = 0 := by exact_mod_cast hn
      subst n
      simp
    · field_simp [hm, hn]

/-- The local prime-power Euler factor for `phiGammaDivCoeff` is norm-summable. -/
theorem phiGammaDivCoeff_primePower_norm_summable {p : ℕ} (hp : Nat.Prime p) :
    Summable (fun e : ℕ => ‖phiGammaDivCoeff (p ^ e)‖) := by
  simpa [phiGammaDivCoeff] using phiGamma_primePowerDiv_norm_summable hp

/-- The local Euler factor for the coefficient function `k ↦ γ(k)/k`. -/
noncomputable def phiGammaDivCoeffLocalFactor (p : ℕ) : ℝ :=
  (1 : ℝ) + (1 : ℝ) / (((p : ℝ) - 1) ^ 2)

/-- Exact local Euler factor for the coefficient function `k ↦ γ(k)/k`. -/
theorem phiGammaDivCoeff_primePower_tsum {p : ℕ} (hp : Nat.Prime p) :
    (∑' e : ℕ, phiGammaDivCoeff (p ^ e)) = phiGammaDivCoeffLocalFactor p := by
  have hsum : Summable (fun e : ℕ => phiGammaDivCoeff (p ^ e)) :=
    (phiGammaDivCoeff_primePower_norm_summable hp).of_norm
  rw [tsum_eq_zero_add hsum]
  simp only [pow_zero]
  rw [phiGammaDivCoeff_one]
  have htail :
      (∑' e : ℕ, phiGammaDivCoeff (p ^ (e + 1))) =
        (1 : ℝ) / (((p : ℝ) - 1) ^ 2) := by
    simpa [phiGammaDivCoeff] using phiGamma_primePowerDiv_positive_tsum hp
  rw [htail]
  rfl

/-- Finite Euler-product expansion for the exact coefficient function
`k ↦ γ(k)/k`, over the numbers whose prime factors lie in `s`. -/
theorem phiGammaDivCoeff_finiteEulerProduct (s : Finset ℕ) :
    Summable (fun m : Nat.factoredNumbers s => ‖phiGammaDivCoeff m‖) ∧
      HasSum (fun m : Nat.factoredNumbers s => phiGammaDivCoeff m)
        (∏ p ∈ s with p.Prime, ∑' e : ℕ, phiGammaDivCoeff (p ^ e)) := by
  exact EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := phiGammaDivCoeff)
    phiGammaDivCoeff_one
    (fun {m n} h => phiGammaDivCoeff_mul_of_coprime h)
    (fun {p} hp => phiGammaDivCoeff_primePower_norm_summable hp)
    s

/-- Finite Euler-product expansion with the local factors evaluated explicitly. -/
theorem phiGammaDivCoeff_finiteEulerProduct_localFactors (s : Finset ℕ) :
    Summable (fun m : Nat.factoredNumbers s => ‖phiGammaDivCoeff m‖) ∧
      HasSum (fun m : Nat.factoredNumbers s => phiGammaDivCoeff m)
        (∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
          phiGammaDivCoeffLocalFactor p) := by
  rcases phiGammaDivCoeff_finiteEulerProduct s with ⟨hsum, hhas⟩
  refine ⟨hsum, ?_⟩
  have hprod :
      (∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
          ∑' e : ℕ, phiGammaDivCoeff (p ^ e)) =
        (∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
          phiGammaDivCoeffLocalFactor p) := by
    exact Finset.prod_congr rfl (by
      intro p hp
      exact phiGammaDivCoeff_primePower_tsum (Finset.mem_filter.mp hp).2)
  rw [← hprod]
  exact hhas

/-- The coefficient function `k ↦ γ(k)/k` is nonnegative. -/
theorem phiGammaDivCoeff_nonneg (k : ℕ) :
    0 ≤ phiGammaDivCoeff k := by
  unfold phiGammaDivCoeff
  exact div_nonneg (phiGamma_nonneg k) (Nat.cast_nonneg k)

/-- Every `1 ≤ k ≤ K` has all its prime factors in the finite set of primes
below `K+1`. -/
theorem mem_factoredNumbers_primesBelow_succ_of_pos_le
    {K k : ℕ} (hk_pos : 1 ≤ k) (hk_le : k ≤ K) :
    k ∈ Nat.factoredNumbers ((K + 1).primesBelow) := by
  rw [Nat.mem_factoredNumbers']
  intro p hp hpdvd
  rw [Nat.mem_primesBelow]
  have hp_le_k : p ≤ k := Nat.le_of_dvd (Nat.succ_le_iff.mp hk_pos) hpdvd
  exact ⟨lt_of_le_of_lt (le_trans hp_le_k hk_le) (Nat.lt_succ_self K), hp⟩

/-- The truncated coefficient sum is bounded by the finite Euler product over
the primes below the truncation point. -/
theorem phiGammaDivSum_le_finiteEulerProduct (K : ℕ) :
    phiGammaDivSum K ≤
      ∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) ((K + 1).primesBelow),
        phiGammaDivCoeffLocalFactor p := by
  classical
  let primes : Finset ℕ := (K + 1).primesBelow
  let S : Finset {k : ℕ // k ∈ Finset.Icc (1 : ℕ) K} := (Finset.Icc (1 : ℕ) K).attach
  let f : {k : ℕ // k ∈ Finset.Icc (1 : ℕ) K} → Nat.factoredNumbers primes :=
    fun k => ⟨k.1, by
      have hk := Finset.mem_Icc.mp k.2
      exact mem_factoredNumbers_primesBelow_succ_of_pos_le
        (K := K) (k := k.1) hk.1 hk.2⟩
  have hinj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y := by
    intro x _hx y _hy hxy
    apply Subtype.ext
    exact congrArg (fun z : Nat.factoredNumbers primes => (z : ℕ)) hxy
  have hsum_image :
      (∑ x in S, phiGammaDivCoeff (f x)) =
        ∑ m in S.image f, phiGammaDivCoeff m := by
    rw [Finset.sum_image]
    exact hinj
  have hsource :
      phiGammaDivSum K = ∑ x in S, phiGammaDivCoeff (f x) := by
    unfold phiGammaDivSum phiGammaDivCoeff
    change (∑ k ∈ Finset.Icc (1 : ℕ) K, phiGamma k / (k : ℝ)) =
      ∑ x in (Finset.Icc (1 : ℕ) K).attach, phiGamma x.1 / ((x.1 : ℕ) : ℝ)
    rw [← Finset.sum_attach]
  rcases phiGammaDivCoeff_finiteEulerProduct_localFactors primes with ⟨hsum_norm, hhas⟩
  have hsum : Summable (fun m : Nat.factoredNumbers primes => phiGammaDivCoeff m) :=
    hsum_norm.of_norm
  have hpartial :
      (∑ m in S.image f, phiGammaDivCoeff m) ≤
        ∑' m : Nat.factoredNumbers primes, phiGammaDivCoeff m :=
    sum_le_tsum (S.image f)
      (fun m _hm => phiGammaDivCoeff_nonneg m)
      hsum
  calc
    phiGammaDivSum K = ∑ x in S, phiGammaDivCoeff (f x) := hsource
    _ = ∑ m in S.image f, phiGammaDivCoeff m := hsum_image
    _ ≤ ∑' m : Nat.factoredNumbers primes, phiGammaDivCoeff m := hpartial
    _ = ∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) primes,
        phiGammaDivCoeffLocalFactor p := hhas.tsum_eq
    _ = ∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) ((K + 1).primesBelow),
        phiGammaDivCoeffLocalFactor p := by rfl

/-- Each local coefficient Euler factor is nonnegative. -/
theorem phiGammaDivCoeffLocalFactor_nonneg (p : ℕ) :
    0 ≤ phiGammaDivCoeffLocalFactor p := by
  unfold phiGammaDivCoeffLocalFactor
  positivity

/-- The finite coefficient Euler product is bounded by the exponential of the
finite prime-local square sum. -/
theorem finiteEulerProduct_le_exp_primePredSqSum (s : Finset ℕ) :
    (∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
        phiGammaDivCoeffLocalFactor p) ≤
      Real.exp
        (∑ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
          (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) := by
  classical
  calc
    (∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
        phiGammaDivCoeffLocalFactor p)
        ≤ ∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
            Real.exp ((1 : ℝ) / (((p : ℝ) - 1) ^ 2)) := by
          apply Finset.prod_le_prod
          · intro p _hp
            exact phiGammaDivCoeffLocalFactor_nonneg p
          · intro p _hp
            unfold phiGammaDivCoeffLocalFactor
            simpa [one_div, add_comm] using
              Real.add_one_le_exp ((((p : ℝ) - 1) ^ 2)⁻¹)
    _ = Real.exp
        (∑ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
          (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) := by
          rw [Real.exp_sum]

/-- Prime-local square summability target underlying the Euler product for the
`γ(k)/k` coefficient series. -/
def PhiGammaPrimePredSqSummable : Prop :=
  Summable (fun p : Nat.Primes => (1 : ℝ) / (((p : ℝ) - 1) ^ 2))

/-- The prime-local square series is summable, by comparison with
`∑_{p} p^{-2}`. -/
theorem phiGamma_primePredSqSummable :
    PhiGammaPrimePredSqSummable := by
  have hsq : Summable (fun p : Nat.Primes => (1 : ℝ) / ((p : ℝ) ^ 2)) := by
    have hsq' : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-2 : ℝ)) :=
      Nat.Primes.summable_rpow.mpr (by norm_num)
    convert hsq' using 1
    ext p
    rw [Real.rpow_neg (by positivity)]
    norm_num
  refine (hsq.mul_left 4).of_nonneg_of_le ?_ ?_
  · intro p
    positivity
  · intro p
    have hp_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
    have hpred_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hmain :
        (1 : ℝ) / (((p : ℝ) - 1) ^ 2) ≤ 4 / ((p : ℝ) ^ 2) := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hpred_pos) (sq_pos_of_pos hp_pos)]
      nlinarith [sq_nonneg ((p : ℝ) - 2)]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmain

/-- A finite prime-local square sum is bounded by the corresponding infinite
summable series over `Nat.Primes`. -/
theorem primePredSqFiniteSum_le_tsum (s : Finset ℕ) :
    (∑ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
          (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) ≤
      ∑' p : Nat.Primes, (1 : ℝ) / (((p : ℝ) - 1) ^ 2) := by
  classical
  let S : Finset ℕ := Finset.filter (fun p : ℕ => Nat.Prime p) s
  let f : {p : ℕ // p ∈ S} → Nat.Primes :=
    fun p => ⟨p.1, (Finset.mem_filter.mp p.2).2⟩
  have hinj : ∀ x ∈ S.attach, ∀ y ∈ S.attach, f x = f y → x = y := by
    intro x _hx y _hy hxy
    apply Subtype.ext
    exact congrArg (fun z : Nat.Primes => (z : ℕ)) hxy
  have hsum_image :
      (∑ x in S.attach, (1 : ℝ) / (((f x : ℕ) : ℝ) - 1) ^ 2) =
        ∑ p in S.attach.image f, (1 : ℝ) / ((((p : ℕ) : ℝ) - 1) ^ 2) := by
    rw [Finset.sum_image]
    exact hinj
  have hsource :
      (∑ p in S, (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) =
        ∑ x in S.attach, (1 : ℝ) / (((f x : ℕ) : ℝ) - 1) ^ 2 := by
    change (∑ p in S, (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) =
      ∑ x in S.attach, (1 : ℝ) / (((x.1 : ℝ) - 1) ^ 2)
    rw [← Finset.sum_attach]
  have hpartial :
      (∑ p in S.attach.image f, (1 : ℝ) / ((((p : ℕ) : ℝ) - 1) ^ 2)) ≤
        ∑' p : Nat.Primes, (1 : ℝ) / (((p : ℝ) - 1) ^ 2) := by
    exact sum_le_tsum (S.attach.image f)
      (fun p _hp => by positivity)
      phiGamma_primePredSqSummable
  calc
    (∑ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
          (1 : ℝ) / (((p : ℝ) - 1) ^ 2))
        = ∑ p in S, (1 : ℝ) / (((p : ℝ) - 1) ^ 2) := by rfl
    _ = ∑ x in S.attach, (1 : ℝ) / (((f x : ℕ) : ℝ) - 1) ^ 2 := hsource
    _ = ∑ p in S.attach.image f, (1 : ℝ) / ((((p : ℕ) : ℝ) - 1) ^ 2) := hsum_image
    _ ≤ ∑' p : Nat.Primes, (1 : ℝ) / (((p : ℝ) - 1) ^ 2) := hpartial

/-- The finite coefficient Euler product is uniformly bounded by the exponential
of the global prime-local square mass. -/
theorem finiteEulerProduct_le_exp_primePredSqTsum (s : Finset ℕ) :
    (∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
        phiGammaDivCoeffLocalFactor p) ≤
      Real.exp (∑' p : Nat.Primes, (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) := by
  calc
    (∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
        phiGammaDivCoeffLocalFactor p)
        ≤ Real.exp
            (∑ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
              (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) :=
          finiteEulerProduct_le_exp_primePredSqSum s
    _ ≤ Real.exp (∑' p : Nat.Primes, (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) :=
          Real.exp_le_exp.mpr (primePredSqFiniteSum_le_tsum s)

/-- The truncated coefficient sums are uniformly bounded by the global
prime-local square mass. -/
theorem phiGammaDivSum_le_exp_primePredSqTsum (K : ℕ) :
    phiGammaDivSum K ≤
      Real.exp (∑' p : Nat.Primes, (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) := by
  calc
    phiGammaDivSum K
        ≤ ∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) ((K + 1).primesBelow),
            phiGammaDivCoeffLocalFactor p :=
          phiGammaDivSum_le_finiteEulerProduct K
    _ ≤ Real.exp (∑' p : Nat.Primes, (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) :=
          finiteEulerProduct_le_exp_primePredSqTsum ((K + 1).primesBelow)

/-- Concrete bounded-partial-sums theorem for the coefficient series
`∑ γ(k)/k`, obtained from the finite Euler product and prime-local square
summability. -/
theorem PhiGammaDivSummableBound_concrete :
    PhiGammaDivSummableBound := by
  refine ⟨Real.exp (∑' p : Nat.Primes,
    (1 : ℝ) / (((p : ℝ) - 1) ^ 2)), Real.exp_pos _, ?_⟩
  intro K
  exact phiGammaDivSum_le_exp_primePredSqTsum K

/-- The gamma coefficient series is termwise bounded by its Euler-product
majorant. -/
theorem phiGamma_div_nat_le_phiGammaDivEulerMajorant (k : ℕ) :
    phiGamma k / (k : ℝ) ≤ phiGammaDivEulerMajorant k := by
  by_cases hk : k = 0
  · simp [phiGammaDivEulerMajorant, hk, phiGamma, phiGammaAF]
  · simpa [phiGammaDivEulerMajorant, hk] using
      phiGamma_div_nat_le_two_pow_omega_div_primeRad_mul_nat (k := k) hk

/-- Summability of the Euler-product majorant implies summability of the
original gamma coefficient series. -/
theorem PhiGammaDivSummableSeries_of_eulerMajorantSummable
    (h : PhiGammaDivEulerMajorantSummable) :
    PhiGammaDivSummableSeries := by
  exact h.of_nonneg_of_le
    (fun k => div_nonneg (phiGamma_nonneg k) (Nat.cast_nonneg k))
    (fun k => phiGamma_div_nat_le_phiGammaDivEulerMajorant k)

/-- The standard `Summable` formulation implies the bounded-partial-sums target
used by the paper-facing coefficient bridge. -/
theorem PhiGammaDivSummableBound_of_summableSeries
    (h : PhiGammaDivSummableSeries) :
    PhiGammaDivSummableBound := by
  refine ⟨(∑' k : ℕ, phiGamma k / (k : ℝ)) + 1, ?_, ?_⟩
  · have htsum_nonneg :
        0 ≤ ∑' k : ℕ, phiGamma k / (k : ℝ) :=
      tsum_nonneg fun k =>
        div_nonneg (phiGamma_nonneg k) (Nat.cast_nonneg k)
    linarith
  · intro K
    unfold phiGammaDivSum
    have hpartial :
        (∑ k ∈ Finset.Icc (1 : ℕ) K, phiGamma k / (k : ℝ)) ≤
          ∑' k : ℕ, phiGamma k / (k : ℝ) :=
      sum_le_tsum (Finset.Icc (1 : ℕ) K)
        (fun k _hk =>
          div_nonneg (phiGamma_nonneg k) (Nat.cast_nonneg k))
        h
    linarith

/-- The normalized endpoint part of the elementary envelope is nonnegative once
the lower endpoint is positive. -/
theorem phiProgressionGammaSmallAdmissibleElementaryEndpointEnvelopeSum_nonneg
    (P : Params) (X : ℝ) (d s K : ℕ)
    (hU0 : 0 < phiProgressionU0 P s X) :
    0 ≤ phiProgressionGammaSmallAdmissibleElementaryEndpointEnvelopeSum
      P X d s K := by
  rw [phiProgressionGammaSmallAdmissibleElementaryEndpointEnvelopeSum_eq_gammaSum_mul]
  exact mul_nonneg
    (phiProgressionGammaSmallAdmissibleGammaSum_nonneg d s K)
    (div_nonneg zero_le_one hU0.le)

/-- The interval log `log(U₁/U₀)` is nonnegative under the paper's endpoint
ordering. -/
theorem log_phiProgressionU1_div_U0_nonneg
    (P : Params) (X : ℝ) (s : ℕ)
    (hU0 : 0 < phiProgressionU0 P s X)
    (hU01 : phiProgressionU0 P s X ≤ phiProgressionU1 P s X) :
    0 ≤ Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) := by
  have hratio : (1 : ℝ) ≤
      phiProgressionU1 P s X / phiProgressionU0 P s X :=
    (one_le_div hU0).mpr hU01
  exact Real.log_nonneg hratio

/-- The normalized logarithmic part of the elementary envelope is nonnegative
under the paper's endpoint and modulus positivity assumptions. -/
theorem phiProgressionGammaSmallAdmissibleElementaryLogEnvelopeSum_nonneg
    (P : Params) (X : ℝ) (d s K : ℕ)
    (hd : 0 < d)
    (hU0 : 0 < phiProgressionU0 P s X)
    (hU01 : phiProgressionU0 P s X ≤ phiProgressionU1 P s X) :
    0 ≤ phiProgressionGammaSmallAdmissibleElementaryLogEnvelopeSum P X d s K := by
  rw [phiProgressionGammaSmallAdmissibleElementaryLogEnvelopeSum_eq_gammaDivSum_mul]
  have hdR : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.le
  exact mul_nonneg
    (phiProgressionGammaSmallAdmissibleGammaDivSum_nonneg d s K)
    (mul_nonneg (div_nonneg zero_le_one hdR)
      (log_phiProgressionU1_div_U0_nonneg P X s hU0 hU01))

/-- The elementary endpoint/log envelope is nonnegative under the deterministic
paper endpoint assumptions. -/
theorem phiProgressionGammaSmallAdmissibleElementaryEnvelopeSum_nonneg
    (P : Params) (X : ℝ) (d s K : ℕ)
    (hd : 0 < d)
    (hU0 : 0 < phiProgressionU0 P s X)
    (hU01 : phiProgressionU0 P s X ≤ phiProgressionU1 P s X) :
    0 ≤ phiProgressionGammaSmallAdmissibleElementaryEnvelopeSum P X d s K := by
  rw [phiProgressionGammaSmallAdmissibleElementaryEnvelopeSum_eq_endpoint_add_log
      P X d s K (ne_of_gt hU0)]
  exact add_nonneg
    (phiProgressionGammaSmallAdmissibleElementaryEndpointEnvelopeSum_nonneg
      P X d s K hU0)
    (phiProgressionGammaSmallAdmissibleElementaryLogEnvelopeSum_nonneg
      P X d s K hd hU0 hU01)

/-- For squarefree `k`, the gamma weight has the large-divisor comparison used
in the tail of `lem:phi-progression-average`: `γ(k) ≤ 2^ω(k)/k`. -/
theorem phiGamma_le_two_pow_omega_div_nat_of_squarefree
    {k : ℕ} (hk : Squarefree k) :
    phiGamma k ≤ ((2 : ℝ) ^ Inputs.omega k) / (k : ℝ) := by
  rw [phiGamma_eq_primeFactorProduct hk.ne_zero]
  calc
    (∏ p ∈ k.primeFactors, (1 : ℝ) / ((p : ℝ) - 1))
        ≤ ∏ p ∈ k.primeFactors, (2 : ℝ) / (p : ℝ) := by
          apply Finset.prod_le_prod
          · intro p hp
            have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
            have hp_gt_one : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.one_lt
            exact div_nonneg zero_le_one (sub_nonneg.mpr hp_gt_one.le)
          · intro p hp
            have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
            have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
            have hp_gt_one : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.one_lt
            have hp_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpPrime.two_le
            have hp_pred_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
            rw [div_le_div_iff₀ hp_pred_pos hp_pos]
            nlinarith
    _ = ((2 : ℝ) ^ Inputs.omega k) / (k : ℝ) := by
          rw [Finset.prod_div_distrib, Finset.prod_const]
          have hprod_cast :
              (∏ p ∈ k.primeFactors, (p : ℝ)) = (k : ℝ) := by
            rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hk]
          rw [hprod_cast]
          simp [Inputs.omega]

/-- For squarefree `k`, every local gamma factor is at most one, hence
`γ(k) ≤ 1`. -/
theorem phiGamma_le_one_of_squarefree {k : ℕ} (hk : Squarefree k) :
    phiGamma k ≤ 1 := by
  rw [phiGamma_eq_primeFactorProduct hk.ne_zero]
  calc
    (∏ p ∈ k.primeFactors, (1 : ℝ) / ((p : ℝ) - 1))
        ≤ ∏ _p ∈ k.primeFactors, (1 : ℝ) := by
          apply Finset.prod_le_prod
          · intro p hp
            have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
            have hp_gt_one : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.one_lt
            exact div_nonneg zero_le_one (sub_nonneg.mpr hp_gt_one.le)
          · intro p hp
            have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
            have hp_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpPrime.two_le
            have hp_pred_ge_one : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
            simpa [one_div] using inv_le_one_of_one_le₀ hp_pred_ge_one
    _ = 1 := by simp

/-- For squarefree `r`, expanding the Euler product
`∏_{p|r}(1+1/(p-1))` gives the manuscript's divisor sum `∑_{k|r} γ(k)`. -/
theorem phiGamma_divisor_sum_eq_prime_product {r : ℕ} (hr : Squarefree r) :
    ∑ k ∈ r.divisors, phiGamma k =
      ∏ p ∈ r.primeFactors, (1 + (1 : ℝ) / ((p : ℝ) - 1)) := by
  have h :=
    phiGammaAF_multiplicative.prodPrimeFactors_one_add_of_squarefree
      (n := r) hr
  unfold phiGamma
  rw [← h]
  apply Finset.prod_congr rfl
  intro p hp
  rw [phiGammaAF_apply_prime (Nat.prime_of_mem_primeFactors hp)]

/-- Real Euler-product form of `1/φ(r)` for positive `r`. -/
theorem one_div_totient_eq_one_div_nat_mul_prime_product {r : ℕ} (hr : 0 < r) :
    (1 : ℝ) / (Nat.totient r : ℝ) =
      (1 / (r : ℝ)) *
        ∏ p ∈ r.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hprod := Inputs.totient_div_eq_totientPrimeFactorProduct (n := r) hr
  have hprod_unfold :
      (Nat.totient r : ℝ) / (r : ℝ) =
        ∏ p ∈ r.primeFactors, (1 - (p : ℝ)⁻¹) := by
    simpa [Inputs.totientPrimeFactorProduct] using hprod
  have hr_ne : (r : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  have hphi_pos : (0 : ℝ) < (Nat.totient r : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hr
  have hprod_ne : (∏ p ∈ r.primeFactors, (1 - (p : ℝ)⁻¹)) ≠ 0 := by
    rw [← hprod_unfold]
    exact div_ne_zero (ne_of_gt hphi_pos) hr_ne
  calc
    (1 : ℝ) / (Nat.totient r : ℝ)
        = (1 / (r : ℝ)) *
            ((Nat.totient r : ℝ) / (r : ℝ))⁻¹ := by
              field_simp [hr_ne, ne_of_gt hphi_pos]
    _ = (1 / (r : ℝ)) *
          (∏ p ∈ r.primeFactors, (1 - (p : ℝ)⁻¹))⁻¹ := by
              rw [hprod_unfold]
    _ = (1 / (r : ℝ)) *
          ∏ p ∈ r.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
              rw [Finset.prod_inv_distrib]

/-- For prime factors of `r`, the local factor `(1-1/p)⁻¹` is
`1+1/(p-1)`. -/
theorem primeFactor_one_sub_inv_inv_eq_one_add_inv_pred
    {r p : ℕ} (hp : p ∈ r.primeFactors) :
    (1 - (p : ℝ)⁻¹)⁻¹ = 1 + (1 : ℝ) / ((p : ℝ) - 1) := by
  have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_gt_one : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.one_lt
  have hp_ne : (p : ℝ) ≠ 0 := by positivity
  have hp_pred_ne : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp_gt_one.ne'
  field_simp [hp_ne, hp_pred_ne]

/-- Exact squarefree divisor expansion used in the upper half of
`lem:phi-progression-average`:
`1/φ(r) = (1/r) ∑_{k|r} γ(k)`. -/
theorem one_div_totient_eq_one_div_nat_mul_phiGamma_sum
    {r : ℕ} (hr : Squarefree r) :
    (1 : ℝ) / (Nat.totient r : ℝ) =
      (1 / (r : ℝ)) * ∑ k ∈ r.divisors, phiGamma k := by
  have hr_pos : 0 < r := Nat.pos_of_ne_zero hr.ne_zero
  rw [one_div_totient_eq_one_div_nat_mul_prime_product hr_pos]
  congr 1
  calc
    (∏ p ∈ r.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹)
        = ∏ p ∈ r.primeFactors, (1 + (1 : ℝ) / ((p : ℝ) - 1)) := by
            apply Finset.prod_congr rfl
            intro p hp
            exact primeFactor_one_sub_inv_inv_eq_one_add_inv_pred hp
    _ = ∑ k ∈ r.divisors, phiGamma k :=
            (phiGamma_divisor_sum_eq_prime_product hr).symm

/-- The exact reciprocal-`φ` progression carrier equals the manuscript's
`γ(k)` divisor-expanded carrier on the same finite support. -/
theorem phiProgressionAverage_eq_gammaAverage
    (P : Params) (X : ℝ) (d a s : ℕ) :
    phiProgressionAverage P X d a s =
      phiProgressionGammaAverage P X d a s := by
  classical
  unfold phiProgressionAverage phiProgressionGammaAverage
  apply Finset.sum_congr rfl
  intro r hr
  have hr_sqf : Squarefree r := (Finset.mem_filter.mp hr).2.1
  rw [one_div_totient_eq_one_div_nat_mul_phiGamma_sum hr_sqf]

/-- The manuscript's `γ(k)` divisor-expanded carrier equals its sigma-indexed
form over pairs `(r,k)` with `k | r`. -/
theorem phiProgressionGammaAverage_eq_sigmaAverage
    (P : Params) (X : ℝ) (d a s : ℕ) :
    phiProgressionGammaAverage P X d a s =
      phiProgressionGammaSigmaAverage P X d a s := by
  classical
  unfold phiProgressionGammaAverage phiProgressionGammaSigmaAverage
    phiProgressionDivisorSigmaSupport phiProgressionSupport
  let S :=
    (Inputs.natWindow (phiProgressionU0 P s X)
      (phiProgressionU1 P s X)).filter
      (fun r => Squarefree r ∧ Nat.Coprime r s ∧ Inputs.congMod r a d)
  have hinner :
      (∑ r ∈ S, (1 / (r : ℝ)) * ∑ k ∈ r.divisors, phiGamma k) =
        ∑ r ∈ S, ∑ k ∈ r.divisors, phiGamma k / (r : ℝ) := by
    apply Finset.sum_congr rfl
    intro r _hr
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  calc
    (∑ r ∈ S, (1 / (r : ℝ)) * ∑ k ∈ r.divisors, phiGamma k)
        = ∑ r ∈ S, ∑ k ∈ r.divisors, phiGamma k / (r : ℝ) := hinner
    _ = ∑ x ∈ S.sigma (fun r => r.divisors), phiGamma x.2 / (x.1 : ℝ) := by
          exact Finset.sum_sigma' S (fun r => r.divisors)
            (fun r k => phiGamma k / (r : ℝ))

/-- The reciprocal-`φ` progression carrier equals the sigma-indexed
`γ(k)/r` expansion used before the small/large divisor split in the manuscript. -/
theorem phiProgressionAverage_eq_gammaSigmaAverage
    (P : Params) (X : ℝ) (d a s : ℕ) :
    phiProgressionAverage P X d a s =
      phiProgressionGammaSigmaAverage P X d a s := by
  rw [phiProgressionAverage_eq_gammaAverage,
    phiProgressionGammaAverage_eq_sigmaAverage]

/-- The sigma-indexed `γ(k)/r` expansion equals its quotient-split form
`γ(k)/(k·(r/k))` on the same support. -/
theorem phiProgressionGammaSigmaAverage_eq_quotientAverage
    (P : Params) (X : ℝ) (d a s : ℕ) :
    phiProgressionGammaSigmaAverage P X d a s =
      phiProgressionGammaQuotientAverage P X d a s := by
  classical
  unfold phiProgressionGammaSigmaAverage phiProgressionGammaQuotientAverage
  apply Finset.sum_congr rfl
  intro x hx
  have hsplit : x.2 * (x.1 / x.2) = x.1 :=
    phiProgressionDivisorSigmaSupport_mem_mul_div hx
  have hden :
      (x.2 : ℝ) * ((x.1 / x.2 : ℕ) : ℝ) = (x.1 : ℝ) := by
    rw [← Nat.cast_mul, hsplit]
  rw [hden]

/-- The reciprocal-`φ` progression carrier equals the exact quotient-split
`γ(k)/(k·t)` carrier obtained by writing `r=k·t`. -/
theorem phiProgressionAverage_eq_gammaQuotientAverage
    (P : Params) (X : ℝ) (d a s : ℕ) :
    phiProgressionAverage P X d a s =
      phiProgressionGammaQuotientAverage P X d a s := by
  rw [phiProgressionAverage_eq_gammaSigmaAverage,
    phiProgressionGammaSigmaAverage_eq_quotientAverage]

/-- The exact gamma-quotient carrier is nonnegative. -/
theorem phiProgressionGammaQuotientAverage_nonneg
    (P : Params) (X : ℝ) (d a s : ℕ) :
    0 ≤ phiProgressionGammaQuotientAverage P X d a s := by
  classical
  unfold phiProgressionGammaQuotientAverage
  apply Finset.sum_nonneg
  intro x hx
  have hk_pos : (0 : ℝ) < (x.2 : ℝ) := by
    exact_mod_cast phiProgressionTauSigma_mem_divisor_pos hx
  have ht_pos : (0 : ℝ) < ((x.1 / x.2 : ℕ) : ℝ) := by
    exact_mod_cast phiProgressionTauSigma_mem_quotient_pos hx
  exact div_nonneg (phiGamma_nonneg x.2) (mul_pos hk_pos ht_pos).le

/-- The quotient-split gamma carrier is exactly the sum of its small- and
large-divisor parts for any cutoff `K`. -/
theorem phiProgressionGammaQuotientAverage_eq_small_add_large
    (P : Params) (X : ℝ) (d a s K : ℕ) :
    phiProgressionGammaQuotientAverage P X d a s =
      phiProgressionGammaSmallQuotientAverage P X d a s K +
        phiProgressionGammaLargeQuotientAverage P X d a s K := by
  classical
  unfold phiProgressionGammaQuotientAverage
    phiProgressionGammaSmallQuotientAverage
    phiProgressionGammaLargeQuotientAverage
  rw [Finset.sum_filter_add_sum_filter_not]

/-- The small gamma quotient carrier is exactly the sum of its fixed-divisor
fibers `1 ≤ k ≤ K`. -/
theorem phiProgressionGammaSmallFiberSum_eq_smallQuotientAverage
    (P : Params) (X : ℝ) (d a s K : ℕ) :
    phiProgressionGammaSmallFiberSum P X d a s K =
      phiProgressionGammaSmallQuotientAverage P X d a s K := by
  classical
  unfold phiProgressionGammaSmallFiberSum
    phiProgressionGammaFixedKQuotientAverage
    phiProgressionGammaSmallQuotientAverage
  rw [Finset.sum_fiberwise_eq_sum_filter]
  apply Finset.sum_congr
  · ext x
    constructor
    · intro hx
      have hxbase : x ∈ phiProgressionDivisorSigmaSupport P X d a s :=
        (Finset.mem_filter.mp hx).1
      have hxrange : x.2 ∈ Finset.Icc (1 : ℕ) K :=
        (Finset.mem_filter.mp hx).2
      exact Finset.mem_filter.mpr ⟨hxbase, (Finset.mem_Icc.mp hxrange).2⟩
    · intro hx
      have hxbase : x ∈ phiProgressionDivisorSigmaSupport P X d a s :=
        (Finset.mem_filter.mp hx).1
      have hxK : x.2 ≤ K := (Finset.mem_filter.mp hx).2
      have hxpos : 0 < x.2 :=
        phiProgressionTauSigma_mem_divisor_pos hxbase
      exact Finset.mem_filter.mpr
        ⟨hxbase, Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hxpos, hxK⟩⟩
  · intro x _hx
    rfl

/-- A fixed gamma fiber factors into its arithmetic coefficient `γ(k)/k` times
the reciprocal quotient fiber. -/
theorem phiProgressionGammaFixedKQuotientAverage_eq_weight_mul_recipFiber
    (P : Params) (X : ℝ) (d a s k : ℕ) (hk : 0 < k) :
    phiProgressionGammaFixedKQuotientAverage P X d a s k =
      (phiGamma k / (k : ℝ)) *
        phiProgressionFixedKQuotientRecipFiber P X d a s k := by
  classical
  unfold phiProgressionGammaFixedKQuotientAverage
    phiProgressionFixedKQuotientRecipFiber
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hxk : x.2 = k := (Finset.mem_filter.mp hx).2
  have ht_pos : (0 : ℝ) < ((x.1 / x.2 : ℕ) : ℝ) := by
    exact_mod_cast
      phiProgressionTauSigma_mem_quotient_pos (Finset.mem_filter.mp hx).1
  have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have ht_ne : ((x.1 / x.2 : ℕ) : ℝ) ≠ 0 := ne_of_gt ht_pos
  subst k
  field_simp [hk_ne, ht_ne]

/-- The small fiber-summed gamma carrier equals the weighted sum of reciprocal
quotient fibers. -/
theorem phiProgressionGammaSmallFiberSum_eq_weightedRecipFiberSum
    (P : Params) (X : ℝ) (d a s K : ℕ) :
    phiProgressionGammaSmallFiberSum P X d a s K =
      phiProgressionGammaSmallWeightedRecipFiberSum P X d a s K := by
  classical
  unfold phiProgressionGammaSmallFiberSum
    phiProgressionGammaSmallWeightedRecipFiberSum
  apply Finset.sum_congr rfl
  intro k hk
  exact phiProgressionGammaFixedKQuotientAverage_eq_weight_mul_recipFiber
    P X d a s k (Finset.mem_Icc.mp hk).1

/-- The quotient reciprocal fiber for a fixed `k` embeds into the ordinary
squarefree reciprocal progression carrier with the scaled window and inverse
residue class.  This is the checked carrier version of the manuscript step
"fix `k`, write `r = kt`, and estimate the resulting progression in `t`." -/
theorem phiProgressionFixedKQuotientRecipFiber_le_sqfRecip_of_inverse
    (P : Params) (X : ℝ) (d a s k b : ℕ)
    (hk : 0 < k) (hb : k * b ≡ 1 [MOD d]) :
    phiProgressionFixedKQuotientRecipFiber P X d a s k ≤
      Inputs.sqfRecip X (s * k) d (a * b)
        (phiProgressionU0 P s X / (k : ℝ))
        (phiProgressionU1 P s X / (k : ℝ)) := by
  classical
  let F :=
    (phiProgressionDivisorSigmaSupport P X d a s).filter
      (fun x => x.2 = k)
  let T :=
    (Inputs.natWindow (phiProgressionU0 P s X / (k : ℝ))
      (phiProgressionU1 P s X / (k : ℝ))).filter
      (fun t => Squarefree t ∧ Nat.Coprime t (s * k) ∧
        Inputs.congMod t (a * b) d)
  let q : (Sigma fun _r : ℕ => ℕ) → ℕ := fun x => x.1 / x.2
  have hsource_image :
      (∑ x ∈ F, (1 : ℝ) / ((q x : ℕ) : ℝ)) =
        ∑ t ∈ F.image q, (1 : ℝ) / (t : ℝ) := by
    rw [Finset.sum_image]
    intro x hx y hy hxy
    have hxbase : x ∈ phiProgressionDivisorSigmaSupport P X d a s :=
      (Finset.mem_filter.mp hx).1
    have hybase : y ∈ phiProgressionDivisorSigmaSupport P X d a s :=
      (Finset.mem_filter.mp hy).1
    have hxk : x.2 = k := (Finset.mem_filter.mp hx).2
    have hyk : y.2 = k := (Finset.mem_filter.mp hy).2
    have hxsplit : x.2 * (x.1 / x.2) = x.1 :=
      phiProgressionDivisorSigmaSupport_mem_mul_div hxbase
    have hysplit : y.2 * (y.1 / y.2) = y.1 :=
      phiProgressionDivisorSigmaSupport_mem_mul_div hybase
    rcases x with ⟨xr, xk⟩
    rcases y with ⟨yr, yk⟩
    simp only at hxk hyk hxy hxsplit hysplit ⊢
    subst xk
    subst yk
    have hfirst : xr = yr := by
      calc
        xr = k * (xr / k) := hxsplit.symm
        _ = k * (yr / k) := by
          have hquot : xr / k = yr / k := by simpa [q] using hxy
          rw [hquot]
        _ = yr := hysplit
    subst yr
    rfl
  have hsubset : F.image q ⊆ T := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨x, hx, rfl⟩
    have hxbase : x ∈ phiProgressionDivisorSigmaSupport P X d a s :=
      (Finset.mem_filter.mp hx).1
    have hxk : x.2 = k := (Finset.mem_filter.mp hx).2
    have hwindow :
        x.1 / x.2 ∈
          Inputs.natWindow (phiProgressionU0 P s X / (k : ℝ))
            (phiProgressionU1 P s X / (k : ℝ)) := by
      have hkt :
          k * (x.1 / x.2) ∈
            Inputs.natWindow (phiProgressionU0 P s X)
              (phiProgressionU1 P s X) := by
        simpa [hxk] using
          phiProgressionDivisorSigmaSupport_reconstructed_mem_window
            (P := P) (X := X) (d := d) (a := a) (s := s) (x := x) hxbase
      exact natWindow_divisor_quotient_mem (U₀ := phiProgressionU0 P s X)
        (U₁ := phiProgressionU1 P s X) (k := k) (t := x.1 / x.2) hk hkt
    have hsqf : Squarefree (x.1 / x.2) :=
      phiProgressionDivisorSigmaSupport_quotient_squarefree hxbase
    have hcop : Nat.Coprime (x.1 / x.2) (s * k) := by
      simpa [hxk] using
        phiProgressionDivisorSigmaSupport_quotient_coprime_s_mul_divisor hxbase
    have hcong : Inputs.congMod (x.1 / x.2) (a * b) d := by
      exact phiProgressionDivisorSigmaSupport_quotient_cong_of_divisor_inverse
        (P := P) (X := X) (d := d) (a := a) (s := s) (b := b) (x := x)
        (by simpa [hxk] using hb) hxbase
    exact Finset.mem_filter.mpr ⟨hwindow, hsqf, hcop, hcong⟩
  have hnonneg :
      ∀ t ∈ T, t ∉ F.image q →
        0 ≤ (1 : ℝ) / (t : ℝ) := by
    intro t _ht _hnot
    exact div_nonneg zero_le_one (Nat.cast_nonneg t)
  have hmain :
      (∑ x ∈ F, (1 : ℝ) / ((q x : ℕ) : ℝ)) ≤
        ∑ t ∈ T, (1 : ℝ) / (t : ℝ) := by
    rw [hsource_image]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
  simpa [phiProgressionFixedKQuotientRecipFiber, Inputs.sqfRecip, F, T, q] using hmain

/-- If the residue class `a` is reduced modulo `d`, then a fixed-divisor fiber
with `k` not coprime to `d` is empty. -/
theorem phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_coprime_d
    (P : Params) (X : ℝ) (d a s k : ℕ)
    (ha : Nat.Coprime a d) (hk : ¬ Nat.Coprime k d) :
    phiProgressionFixedKQuotientRecipFiber P X d a s k = 0 := by
  classical
  unfold phiProgressionFixedKQuotientRecipFiber
  apply Finset.sum_eq_zero
  intro x hx
  have hxbase : x ∈ phiProgressionDivisorSigmaSupport P X d a s :=
    (Finset.mem_filter.mp hx).1
  have hxk : x.2 = k := (Finset.mem_filter.mp hx).2
  exfalso
  exact hk (by
    simpa [hxk] using
      phiProgressionDivisorSigmaSupport_divisor_coprime_d
        (P := P) (X := X) (d := d) (a := a) (s := s) (x := x) ha hxbase)

/-- A fixed-divisor fiber with `k` not coprime to `s` is empty, because the
outer variable is already coprime to `s` and `k | r`. -/
theorem phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_coprime_s
    (P : Params) (X : ℝ) (d a s k : ℕ)
    (hk : ¬ Nat.Coprime k s) :
    phiProgressionFixedKQuotientRecipFiber P X d a s k = 0 := by
  classical
  unfold phiProgressionFixedKQuotientRecipFiber
  apply Finset.sum_eq_zero
  intro x hx
  have hxbase : x ∈ phiProgressionDivisorSigmaSupport P X d a s :=
    (Finset.mem_filter.mp hx).1
  have hxk : x.2 = k := (Finset.mem_filter.mp hx).2
  exfalso
  exact hk (by
    simpa [hxk] using
      phiProgressionDivisorSigmaSupport_divisor_coprime_s
        (P := P) (X := X) (d := d) (a := a) (s := s) (x := x) hxbase)

/-- A fixed-divisor fiber with nonsquarefree `k` is empty, because every
occurring exposed divisor divides the squarefree outer variable `r`. -/
theorem phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_squarefree
    (P : Params) (X : ℝ) (d a s k : ℕ)
    (hk : ¬ Squarefree k) :
    phiProgressionFixedKQuotientRecipFiber P X d a s k = 0 := by
  classical
  unfold phiProgressionFixedKQuotientRecipFiber
  apply Finset.sum_eq_zero
  intro x hx
  have hxbase : x ∈ phiProgressionDivisorSigmaSupport P X d a s :=
    (Finset.mem_filter.mp hx).1
  have hxk : x.2 = k := (Finset.mem_filter.mp hx).2
  exfalso
  exact hk (by
    simpa [hxk] using
      phiProgressionDivisorSigmaSupport_divisor_squarefree
        (P := P) (X := X) (d := d) (a := a) (s := s) (x := x) hxbase)

/-- The weighted quotient-fiber small carrier is bounded by the model sum of
ordinary squarefree reciprocal progression carriers, once inverse residues have
been chosen for every `1 ≤ k ≤ K`. -/
theorem phiProgressionGammaSmallWeightedRecipFiberSum_le_sqfRecipModelSum
    (P : Params) (X : ℝ) (d a s K : ℕ) (B : ℕ → ℕ)
    (hB : ∀ k ∈ Finset.Icc (1 : ℕ) K, k * B k ≡ 1 [MOD d]) :
    phiProgressionGammaSmallWeightedRecipFiberSum P X d a s K ≤
      phiProgressionGammaSmallSqfRecipModelSum P X d a s K B := by
  classical
  unfold phiProgressionGammaSmallWeightedRecipFiberSum
    phiProgressionGammaSmallSqfRecipModelSum
  apply Finset.sum_le_sum
  intro k hk
  have hk_pos : 0 < k := (Finset.mem_Icc.mp hk).1
  have hcoef_nonneg : 0 ≤ phiGamma k / (k : ℝ) :=
    div_nonneg (phiGamma_nonneg k) (by exact_mod_cast hk_pos.le)
  exact mul_le_mul_of_nonneg_left
    (phiProgressionFixedKQuotientRecipFiber_le_sqfRecip_of_inverse
      P X d a s k (B k) hk_pos (hB k hk))
    hcoef_nonneg

/-- The weighted quotient-fiber small carrier is bounded by the
coprime-restricted squarefree-reciprocal model.  This removes the artificial
requirement of choosing inverse residues for `k` that cannot occur in the
original reduced residue class. -/
theorem phiProgressionGammaSmallWeightedRecipFiberSum_le_coprimeSqfRecipModelSum
    (P : Params) (X : ℝ) (d a s K : ℕ) (B : ℕ → ℕ)
    (ha : Nat.Coprime a d)
    (hB : ∀ k ∈ Finset.Icc (1 : ℕ) K,
      Nat.Coprime k d → k * B k ≡ 1 [MOD d]) :
    phiProgressionGammaSmallWeightedRecipFiberSum P X d a s K ≤
      phiProgressionGammaSmallSqfRecipCoprimeModelSum P X d a s K B := by
  classical
  unfold phiProgressionGammaSmallWeightedRecipFiberSum
    phiProgressionGammaSmallSqfRecipCoprimeModelSum
  apply Finset.sum_le_sum
  intro k hk
  by_cases hkd : Nat.Coprime k d
  · rw [if_pos hkd]
    have hk_pos : 0 < k := (Finset.mem_Icc.mp hk).1
    have hcoef_nonneg : 0 ≤ phiGamma k / (k : ℝ) :=
      div_nonneg (phiGamma_nonneg k) (by exact_mod_cast hk_pos.le)
    exact mul_le_mul_of_nonneg_left
      (phiProgressionFixedKQuotientRecipFiber_le_sqfRecip_of_inverse
        P X d a s k (B k) hk_pos (hB k hk hkd))
      hcoef_nonneg
  · rw [if_neg hkd,
      phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_coprime_d
        P X d a s k ha hkd,
      mul_zero]

/-- Canonical-inverse version of the coprime-restricted model bound. -/
theorem phiProgressionGammaSmallWeightedRecipFiberSum_le_coprimeInverseSqfRecipModelSum
    (P : Params) (X : ℝ) (d a s K : ℕ)
    (hd : 0 < d) (ha : Nat.Coprime a d) :
    phiProgressionGammaSmallWeightedRecipFiberSum P X d a s K ≤
      phiProgressionGammaSmallSqfRecipCoprimeInverseModelSum P X d a s K := by
  classical
  unfold phiProgressionGammaSmallSqfRecipCoprimeInverseModelSum
  exact
    phiProgressionGammaSmallWeightedRecipFiberSum_le_coprimeSqfRecipModelSum
      P X d a s K (fun k => modInverseChoice d k) ha
      (fun k _hk hkd => modInverseChoice_coprime hd hkd)

/-- The weighted quotient-fiber small carrier is bounded by the admissible
canonical-inverse model, where only divisors coprime to both `d` and `s` remain.
This matches the manuscript's vanishing of the forbidden fixed-`k` fibers. -/
theorem phiProgressionGammaSmallWeightedRecipFiberSum_le_admissibleInverseSqfRecipModelSum
    (P : Params) (X : ℝ) (d a s K : ℕ)
    (hd : 0 < d) (ha : Nat.Coprime a d) :
    phiProgressionGammaSmallWeightedRecipFiberSum P X d a s K ≤
      phiProgressionGammaSmallSqfRecipAdmissibleInverseModelSum P X d a s K := by
  classical
  unfold phiProgressionGammaSmallWeightedRecipFiberSum
    phiProgressionGammaSmallSqfRecipAdmissibleInverseModelSum
  apply Finset.sum_le_sum
  intro k hk
  by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
  · simp only [if_pos hadm]
    have hk_pos : 0 < k := (Finset.mem_Icc.mp hk).1
    have hcoef_nonneg : 0 ≤ phiGamma k / (k : ℝ) :=
      div_nonneg (phiGamma_nonneg k) (by exact_mod_cast hk_pos.le)
    exact mul_le_mul_of_nonneg_left
      (phiProgressionFixedKQuotientRecipFiber_le_sqfRecip_of_inverse
        P X d a s k (modInverseChoice d k) hk_pos
        (modInverseChoice_coprime hd hadm.1))
      hcoef_nonneg
  · rw [if_neg hadm]
    by_cases hkd : Nat.Coprime k d
    · have hks : ¬ Nat.Coprime k s := by
        intro hks
        exact hadm ⟨hkd, hks⟩
      rw [phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_coprime_s
        P X d a s k hks, mul_zero]
    · rw [phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_coprime_d
        P X d a s k ha hkd, mul_zero]

/-- The large quotient-fiber tail is bounded by its admissible
squarefree-reciprocal model.  This is the large-`k` analogue of the small-side
fixed-divisor reduction: after exposing `r=k t`, every occurring admissible
fiber embeds into the ordinary squarefree progression in `t`, and forbidden
fibers vanish. -/
theorem phiProgressionOmegaLargeWeightedRecipFiberSum_le_admissibleInverseSqfRecipModelSum
    (P : Params) (X : ℝ) (d a s K : ℕ)
    (hd : 0 < d) (ha : Nat.Coprime a d) :
    phiProgressionOmegaLargeWeightedRecipFiberSum P X d a s K ≤
      phiProgressionOmegaLargeSqfRecipAdmissibleInverseModelSum
        P X d a s K := by
  classical
  unfold phiProgressionOmegaLargeWeightedRecipFiberSum
    phiProgressionOmegaLargeSqfRecipAdmissibleInverseModelSum
  apply Finset.sum_le_sum
  intro k hk
  have hkIcc :
      k ∈ Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊ :=
    (Finset.mem_filter.mp hk).1
  have hk_pos : 0 < k := (Finset.mem_Icc.mp hkIcc).1
  have hcoef_nonneg :
      0 ≤ ((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2) :=
    div_nonneg
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Inputs.omega k))
      (sq_nonneg (k : ℝ))
  by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
  · simp only [if_pos hadm]
    exact mul_le_mul_of_nonneg_left
      (phiProgressionFixedKQuotientRecipFiber_le_sqfRecip_of_inverse
        P X d a s k (modInverseChoice d k) hk_pos
        (modInverseChoice_coprime hd hadm.1))
      hcoef_nonneg
  · rw [if_neg hadm]
    by_cases hkd : Nat.Coprime k d
    · have hks : ¬ Nat.Coprime k s := by
        intro hks
        exact hadm ⟨hkd, hks⟩
      rw [phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_coprime_s
        P X d a s k hks, mul_zero]
    · rw [phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_coprime_d
        P X d a s k ha hkd, mul_zero]

/-- Applying the unconditional elementary progression upper bound to each
admissible fixed-`k` squarefree reciprocal carrier bounds the admissible model
by its elementary endpoint/log envelope. -/
theorem phiProgressionGammaSmallSqfRecipAdmissibleInverseModelSum_le_elementaryEnvelope
    (P : Params) (X : ℝ) (d a s K : ℕ)
    (hd : 0 < d)
    (hU0 : 0 < phiProgressionU0 P s X)
    (hU01 : phiProgressionU0 P s X < phiProgressionU1 P s X) :
    phiProgressionGammaSmallSqfRecipAdmissibleInverseModelSum P X d a s K ≤
      phiProgressionGammaSmallAdmissibleElementaryEnvelopeSum P X d s K := by
  classical
  unfold phiProgressionGammaSmallSqfRecipAdmissibleInverseModelSum
    phiProgressionGammaSmallAdmissibleElementaryEnvelopeSum
  apply Finset.sum_le_sum
  intro k hk
  by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
  · have hk_pos_nat : 0 < k := (Finset.mem_Icc.mp hk).1
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos_nat
    have hscaled0 : 0 < phiProgressionU0 P s X / (k : ℝ) :=
      div_pos hU0 hk_pos
    have hscaled01 :
        phiProgressionU0 P s X / (k : ℝ) <
          phiProgressionU1 P s X / (k : ℝ) :=
      div_lt_div_of_pos_right hU01 hk_pos
    have hcoef_nonneg : 0 ≤ phiGamma k / (k : ℝ) :=
      div_nonneg (phiGamma_nonneg k) hk_pos.le
    rw [if_pos hadm, if_pos hadm]
    exact
      mul_le_mul_of_nonneg_left
        (Inputs.sqfRecip_le_log_plus_inv X (s * k) d
          (a * modInverseChoice d k) hd hscaled0 hscaled01)
        hcoef_nonneg
  · simp [hadm]

/-- The large gamma tail is bounded by the pure `2^ω(k)/k` tail majorant. -/
theorem phiProgressionGammaLargeQuotientAverage_le_tailMajorant
    (P : Params) (X : ℝ) (d a s K : ℕ) :
    phiProgressionGammaLargeQuotientAverage P X d a s K ≤
      phiProgressionGammaLargeTailMajorant P X d a s K := by
  classical
  unfold phiProgressionGammaLargeQuotientAverage
    phiProgressionGammaLargeTailMajorant
  apply Finset.sum_le_sum
  intro x hx
  have hxbase : x ∈ phiProgressionDivisorSigmaSupport P X d a s :=
    (Finset.mem_filter.mp hx).1
  have hk_sqf : Squarefree x.2 :=
    phiProgressionDivisorSigmaSupport_divisor_squarefree
      (P := P) (X := X) (d := d) (a := a) (s := s) (x := x) hxbase
  have hk_pos : (0 : ℝ) < (x.2 : ℝ) := by
    exact_mod_cast phiProgressionTauSigma_mem_divisor_pos hxbase
  have ht_pos : (0 : ℝ) < ((x.1 / x.2 : ℕ) : ℝ) := by
    exact_mod_cast phiProgressionTauSigma_mem_quotient_pos hxbase
  have hden_nonneg : 0 ≤ (x.2 : ℝ) * ((x.1 / x.2 : ℕ) : ℝ) :=
    (mul_pos hk_pos ht_pos).le
  exact div_le_div_of_nonneg_right
    (phiGamma_le_two_pow_omega_div_nat_of_squarefree hk_sqf) hden_nonneg

/-- On each sigma-support point, the denominator in the pure tail majorant is
the original outer variable `r`. -/
theorem phiProgressionGammaLargeTailMajorant_term_eq_coeff_mul_inv_outer
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    (((2 : ℝ) ^ Inputs.omega x.2) / (x.2 : ℝ)) /
        ((x.2 : ℝ) * ((x.1 / x.2 : ℕ) : ℝ)) =
      (((2 : ℝ) ^ Inputs.omega x.2) / (x.2 : ℝ)) *
        (1 / (x.1 : ℝ)) := by
  have hsplit : x.2 * (x.1 / x.2) = x.1 :=
    phiProgressionDivisorSigmaSupport_mem_mul_div hx
  have hden :
      (x.2 : ℝ) * ((x.1 / x.2 : ℕ) : ℝ) = (x.1 : ℝ) := by
    rw [← Nat.cast_mul, hsplit]
  rw [hden]
  ring

/-- On each sigma-support point, the pure tail summand can also be written in
quotient-fiber form with coefficient `2^ω(k)/k²` and reciprocal quotient
variable `1/t`, where `r=k t`. -/
theorem phiProgressionGammaLargeTailMajorant_term_eq_omega_sqCoeff_mul_quotient_inv
    {P : Params} {X : ℝ} {d a s : ℕ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ phiProgressionDivisorSigmaSupport P X d a s) :
    (((2 : ℝ) ^ Inputs.omega x.2) / (x.2 : ℝ)) /
        ((x.2 : ℝ) * ((x.1 / x.2 : ℕ) : ℝ)) =
      (((2 : ℝ) ^ Inputs.omega x.2) / ((x.2 : ℝ) ^ 2)) *
        (1 / ((x.1 / x.2 : ℕ) : ℝ)) := by
  have hk_pos : (0 : ℝ) < (x.2 : ℝ) := by
    exact_mod_cast phiProgressionTauSigma_mem_divisor_pos hx
  have ht_pos : (0 : ℝ) < ((x.1 / x.2 : ℕ) : ℝ) := by
    exact_mod_cast phiProgressionTauSigma_mem_quotient_pos hx
  field_simp [ne_of_gt hk_pos, ne_of_gt ht_pos]
  ring

/-- The pure large-tail majorant is exactly its outer-fiber form: fix `r` in
the progression support and then sum the coefficient tail over large divisors
`k|r`. -/
theorem phiProgressionGammaLargeTailMajorant_eq_outerMajorant
    (P : Params) (X : ℝ) (d a s K : ℕ) :
    phiProgressionGammaLargeTailMajorant P X d a s K =
      phiProgressionGammaLargeTailOuterMajorant P X d a s K := by
  classical
  unfold phiProgressionGammaLargeTailMajorant
    phiProgressionGammaLargeTailOuterMajorant phiProgressionDivisorSigmaSupport
  have hfilter :
      ((phiProgressionSupport P X d a s).sigma (fun r => r.divisors)).filter
          (fun x : Sigma fun _r : ℕ => ℕ => ¬ x.2 ≤ K) =
        (phiProgressionSupport P X d a s).sigma
          (fun r => r.divisors.filter (fun k => ¬ k ≤ K)) := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨hxbase, hxlarge⟩
      exact Finset.mem_sigma.mpr
        ⟨(Finset.mem_sigma.mp hxbase).1,
          Finset.mem_filter.mpr ⟨(Finset.mem_sigma.mp hxbase).2, hxlarge⟩⟩
    · intro hx
      rcases Finset.mem_sigma.mp hx with ⟨hxr, hxk⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_sigma.mpr ⟨hxr, (Finset.mem_filter.mp hxk).1⟩,
          (Finset.mem_filter.mp hxk).2⟩
  rw [hfilter, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hxbase :
      Sigma.mk r k ∈ phiProgressionDivisorSigmaSupport P X d a s := by
    unfold phiProgressionDivisorSigmaSupport
    exact Finset.mem_sigma.mpr ⟨hr, (Finset.mem_filter.mp hk).1⟩
  have hterm :=
    phiProgressionGammaLargeTailMajorant_term_eq_coeff_mul_inv_outer
      (P := P) (X := X) (d := d) (a := a) (s := s) (x := Sigma.mk r k)
      hxbase
  simpa [mul_comm, mul_left_comm, mul_assoc] using hterm

/-- The pure large-tail majorant is exactly the quotient-fiber weighted sum
with coefficient `2^ω(k)/k²`.  This is the finite carrier identity behind the
summable-coefficient tail estimate in the upper half of
`lem:phi-progression-average`. -/
theorem phiProgressionGammaLargeTailMajorant_eq_omegaWeightedRecipFiberSum
    (P : Params) (X : ℝ) (d a s K : ℕ) :
    phiProgressionGammaLargeTailMajorant P X d a s K =
      phiProgressionOmegaLargeWeightedRecipFiberSum P X d a s K := by
  classical
  let B := phiProgressionDivisorSigmaSupport P X d a s
  let T :=
    (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
      (fun k => ¬ k ≤ K)
  let tailTerm : (Sigma fun _r : ℕ => ℕ) → ℝ := fun x =>
    (((2 : ℝ) ^ Inputs.omega x.2) / (x.2 : ℝ)) /
      ((x.2 : ℝ) * ((x.1 / x.2 : ℕ) : ℝ))
  let fiberTerm : (Sigma fun _r : ℕ => ℕ) → ℝ := fun x =>
    (((2 : ℝ) ^ Inputs.omega x.2) / ((x.2 : ℝ) ^ 2)) *
      (1 / ((x.1 / x.2 : ℕ) : ℝ))
  have hweighted :
      phiProgressionOmegaLargeWeightedRecipFiberSum P X d a s K =
        ∑ k ∈ T, ∑ x ∈ B.filter (fun x => x.2 = k), fiberTerm x := by
    unfold phiProgressionOmegaLargeWeightedRecipFiberSum
      phiProgressionFixedKQuotientRecipFiber
    dsimp [B, T, fiberTerm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have hxk : x.2 = k := (Finset.mem_filter.mp hx).2
    subst k
    rfl
  have hfiber :
      (∑ k ∈ T, ∑ x ∈ B.filter (fun x => x.2 = k), fiberTerm x) =
        ∑ x ∈ B.filter (fun x => x.2 ∈ T), fiberTerm x := by
    exact Finset.sum_fiberwise_eq_sum_filter B T (fun x => x.2) fiberTerm
  have hfilter :
      B.filter (fun x => x.2 ∈ T) =
        B.filter (fun x => ¬ x.2 ≤ K) := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨hxbase, hxT⟩
      exact Finset.mem_filter.mpr ⟨hxbase, (Finset.mem_filter.mp hxT).2⟩
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨hxbase, hxlarge⟩
      have hx_outer :
          x.1 ∈ phiProgressionSupport P X d a s :=
        phiProgressionDivisorSigmaSupport_outer_mem_support
          (P := P) (X := X) (d := d) (a := a) (s := s) hxbase
      have hx_window :
          x.1 ∈ Inputs.natWindow (phiProgressionU0 P s X)
            (phiProgressionU1 P s X) := by
        unfold phiProgressionSupport at hx_outer
        exact (Finset.mem_filter.mp hx_outer).1
      have hx_icc :
          x.1 ∈ Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊ := by
        unfold Inputs.natWindow at hx_window
        exact (Finset.mem_filter.mp hx_window).1
      have hx1_pos : 0 < x.1 :=
        lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hx_icc).1
      have hx2_pos : 0 < x.2 :=
        phiProgressionTauSigma_mem_divisor_pos hxbase
      have hx2_le_x1 : x.2 ≤ x.1 :=
        Nat.le_of_dvd hx1_pos
          (phiProgressionDivisorSigmaSupport_divisor_dvd hxbase)
      exact Finset.mem_filter.mpr
        ⟨hxbase,
          Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr
                ⟨Nat.succ_le_of_lt hx2_pos,
                  le_trans hx2_le_x1 (Finset.mem_Icc.mp hx_icc).2⟩,
              hxlarge⟩⟩
  calc
    phiProgressionGammaLargeTailMajorant P X d a s K
        = ∑ x ∈ B.filter (fun x => ¬ x.2 ≤ K), tailTerm x := by
            rfl
    _ = ∑ x ∈ B.filter (fun x => ¬ x.2 ≤ K), fiberTerm x := by
          apply Finset.sum_congr rfl
          intro x hx
          exact
            phiProgressionGammaLargeTailMajorant_term_eq_omega_sqCoeff_mul_quotient_inv
              (P := P) (X := X) (d := d) (a := a) (s := s) (x := x)
              (Finset.mem_filter.mp hx).1
    _ = ∑ x ∈ B.filter (fun x => x.2 ∈ T), fiberTerm x := by rw [hfilter]
    _ = ∑ k ∈ T, ∑ x ∈ B.filter (fun x => x.2 = k), fiberTerm x := hfiber.symm
    _ = phiProgressionOmegaLargeWeightedRecipFiberSum P X d a s K := hweighted.symm

/-- The original pure large-tail majorant reduces to the admissible
squarefree-reciprocal model with the summable coefficient `2^ω(k)/k²`. -/
theorem phiProgressionGammaLargeTailMajorant_le_omegaLargeSqfRecipAdmissibleInverseModelSum
    (P : Params) (X : ℝ) (d a s K : ℕ)
    (hd : 0 < d) (ha : Nat.Coprime a d) :
    phiProgressionGammaLargeTailMajorant P X d a s K ≤
      phiProgressionOmegaLargeSqfRecipAdmissibleInverseModelSum
        P X d a s K := by
  rw [phiProgressionGammaLargeTailMajorant_eq_omegaWeightedRecipFiberSum]
  exact
    phiProgressionOmegaLargeWeightedRecipFiberSum_le_admissibleInverseSqfRecipModelSum
      P X d a s K hd ha

/-- The outer-fiber large-tail majorant is bounded by a one-dimensional
coefficient tail times the bare reciprocal progression carrier.  The only
support fact used is that every exposed divisor `k|r` is at most the finite
endpoint `⌊U₁⌋₊` of the progression window. -/
theorem phiProgressionGammaLargeTailOuterMajorant_le_tailSum_mul_bareAverage
    (P : Params) (X : ℝ) (d a s K : ℕ) :
    phiProgressionGammaLargeTailOuterMajorant P X d a s K ≤
      phiOmegaDivTailSum K ⌊phiProgressionU1 P s X⌋₊ *
        phiProgressionBareAverage P X d a s := by
  classical
  let S := phiProgressionSupport P X d a s
  let T :=
    (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
      (fun k => ¬ k ≤ K)
  let coeff : ℕ → ℝ := fun k => ((2 : ℝ) ^ Inputs.omega k) / (k : ℝ)
  have hinner :
      ∀ r ∈ S,
        (∑ k ∈ r.divisors.filter (fun k => ¬ k ≤ K), coeff k) ≤
          ∑ k ∈ T, coeff k := by
    intro r hr
    have hr_window :
        r ∈ Inputs.natWindow (phiProgressionU0 P s X)
          (phiProgressionU1 P s X) := by
      dsimp [S] at hr
      unfold phiProgressionSupport at hr
      exact (Finset.mem_filter.mp hr).1
    have hr_icc :
        r ∈ Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊ := by
      unfold Inputs.natWindow at hr_window
      exact (Finset.mem_filter.mp hr_window).1
    refine Finset.sum_le_sum_of_subset_of_nonneg ?hsubset ?hnonneg
    · intro k hk
      rcases Finset.mem_filter.mp hk with ⟨hkdiv, hklarge⟩
      have hk_pos : 0 < k := Nat.pos_of_mem_divisors hkdiv
      have hr_pos : 0 < r :=
        lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hr_icc).1
      have hk_le_r : k ≤ r :=
        Nat.le_of_dvd hr_pos (Nat.dvd_of_mem_divisors hkdiv)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr
            ⟨Nat.succ_le_of_lt hk_pos,
              le_trans hk_le_r (Finset.mem_Icc.mp hr_icc).2⟩,
          hklarge⟩
    · intro k hk _hnot
      exact div_nonneg
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Inputs.omega k))
        (Nat.cast_nonneg k)
  have hsum :
      (∑ r ∈ S,
          (1 / (r : ℝ)) *
            ∑ k ∈ r.divisors.filter (fun k => ¬ k ≤ K), coeff k) ≤
        ∑ r ∈ S, (1 / (r : ℝ)) * ∑ k ∈ T, coeff k := by
    apply Finset.sum_le_sum
    intro r hr
    have hr_nonneg : 0 ≤ (1 : ℝ) / (r : ℝ) :=
      div_nonneg zero_le_one (Nat.cast_nonneg r)
    exact mul_le_mul_of_nonneg_left (hinner r hr) hr_nonneg
  have hfactor :
      (∑ r ∈ S, (1 / (r : ℝ)) * ∑ k ∈ T, coeff k) =
        (∑ k ∈ T, coeff k) * ∑ r ∈ S, (1 / (r : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    ring
  calc
    phiProgressionGammaLargeTailOuterMajorant P X d a s K
        = ∑ r ∈ S,
            (1 / (r : ℝ)) *
              ∑ k ∈ r.divisors.filter (fun k => ¬ k ≤ K), coeff k := by
            rfl
    _ ≤ ∑ r ∈ S, (1 / (r : ℝ)) * ∑ k ∈ T, coeff k := hsum
    _ = (∑ k ∈ T, coeff k) * ∑ r ∈ S, (1 / (r : ℝ)) := hfactor
    _ = phiOmegaDivTailSum K ⌊phiProgressionU1 P s X⌋₊ *
          phiProgressionBareAverage P X d a s := by
          rfl

/-- The quotient-split `τ(r)/r` carrier is nonnegative. -/
theorem phiProgressionTauQuotientAverage_nonneg
    (P : Params) (X : ℝ) (d a s : ℕ) :
    0 ≤ phiProgressionTauQuotientAverage P X d a s := by
  classical
  unfold phiProgressionTauQuotientAverage
  apply Finset.sum_nonneg
  intro x hx
  have hk_pos : (0 : ℝ) < (x.2 : ℝ) := by
    exact_mod_cast phiProgressionTauSigma_mem_divisor_pos hx
  have ht_pos : (0 : ℝ) < ((x.1 / x.2 : ℕ) : ℝ) := by
    exact_mod_cast phiProgressionTauSigma_mem_quotient_pos hx
  exact div_nonneg zero_le_one (mul_pos hk_pos ht_pos).le

/-- On the exact quotient support, the sharper gamma carrier is pointwise
bounded by the coarser `τ(r)/r` quotient carrier because `γ(k) ≤ 1` for
squarefree divisors `k`. -/
theorem phiProgressionGammaQuotientAverage_le_tauQuotientAverage
    (P : Params) (X : ℝ) (d a s : ℕ) :
    phiProgressionGammaQuotientAverage P X d a s ≤
      phiProgressionTauQuotientAverage P X d a s := by
  classical
  unfold phiProgressionGammaQuotientAverage phiProgressionTauQuotientAverage
    phiProgressionDivisorSigmaSupport phiProgressionSupport
  apply Finset.sum_le_sum
  intro x hx
  have hk_pos : (0 : ℝ) < (x.2 : ℝ) := by
    exact_mod_cast phiProgressionTauSigma_mem_divisor_pos hx
  have ht_pos : (0 : ℝ) < ((x.1 / x.2 : ℕ) : ℝ) := by
    exact_mod_cast phiProgressionTauSigma_mem_quotient_pos hx
  have hden_nonneg : 0 ≤ (x.2 : ℝ) * ((x.1 / x.2 : ℕ) : ℝ) :=
    (mul_pos hk_pos ht_pos).le
  have hk_sqf : Squarefree x.2 := by
    exact phiProgressionDivisorSigmaSupport_divisor_squarefree
      (P := P) (X := X) (d := d) (a := a) (s := s) (x := x) hx
  exact div_le_div_of_nonneg_right (phiGamma_le_one_of_squarefree hk_sqf) hden_nonneg

/-- Pointwise comparison behind the lower-bound half of
`lem:phi-progression-average`: since `φ(r) ≤ r`, one has `1/r ≤ 1/φ(r)` for
positive `r`. -/
theorem one_div_nat_le_one_div_totient {r : ℕ} (hr : 0 < r) :
    (1 : ℝ) / (r : ℝ) ≤ (1 : ℝ) / (Nat.totient r : ℝ) := by
  have htot_pos_nat : 0 < Nat.totient r := Nat.totient_pos.mpr hr
  have htot_pos : (0 : ℝ) < (Nat.totient r : ℝ) := by exact_mod_cast htot_pos_nat
  have htot_le_nat : Nat.totient r ≤ r := Nat.totient_le r
  have htot_le : (Nat.totient r : ℝ) ≤ (r : ℝ) := by exact_mod_cast htot_le_nat
  exact one_div_le_one_div_of_le htot_pos htot_le

/-- The paper's lower-bound reduction
`∑ 1/r ≤ ∑ 1/φ(r)` on the exact reciprocal-progression support. -/
theorem phiProgressionBareAverage_le_phiProgressionAverage
    (P : Params) (X : ℝ) (d a s : ℕ) :
    phiProgressionBareAverage P X d a s ≤
      phiProgressionAverage P X d a s := by
  classical
  unfold phiProgressionBareAverage phiProgressionAverage
  apply Finset.sum_le_sum
  intro r hr
  have hr_window :
      r ∈ Inputs.natWindow (phiProgressionU0 P s X)
        (phiProgressionU1 P s X) :=
    (Finset.mem_filter.mp hr).1
  have hr_pos_nat : 0 < r := by
    unfold Inputs.natWindow at hr_window
    exact lt_of_lt_of_le Nat.zero_lt_one
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hr_window).1).1
  exact one_div_nat_le_one_div_totient hr_pos_nat

/-- The bare reciprocal carrier in `lem:phi-progression-average` is exactly the
ordinary squarefree reciprocal progression carrier from `Inputs`, with the
extra coprimality modulus specialized to `s`. -/
theorem phiProgressionBareAverage_eq_sqfRecip
    (P : Params) (X : ℝ) (d a s : ℕ) :
    phiProgressionBareAverage P X d a s =
      Inputs.sqfRecip X s d a
        (phiProgressionU0 P s X) (phiProgressionU1 P s X) := by
  rfl

/-- The bare phi-progression carrier is dominated by the unrestricted
progression reciprocal window after dropping the squarefree and coprimality
conditions. -/
theorem phiProgressionBareAverage_le_progressionRecip
    (P : Params) (X : ℝ) (d a s : ℕ) :
    phiProgressionBareAverage P X d a s ≤
      Inputs.progressionRecip d a
        (phiProgressionU0 P s X) (phiProgressionU1 P s X) := by
  rw [phiProgressionBareAverage_eq_sqfRecip]
  exact Inputs.sqfRecip_le_progressionRecip X s d a
    (phiProgressionU0 P s X) (phiProgressionU1 P s X)

/-- Algebraic identification of the logarithmic interval length:
`log((H/s²)/(Y₀/s)) = log(H/(Y₀s))`. -/
theorem log_phiProgressionU1_div_U0_eq_slantLogLength
    (P : Params) {X : ℝ} {s : ℕ} (hX : 0 < X) (hs : 0 < s) :
    Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) =
      slantLogLength P s X := by
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hs)
  have hY0_pos : 0 < Y0Scale P X := Real.rpow_pos_of_pos hX P.lam
  have hY0_ne : Y0Scale P X ≠ 0 := ne_of_gt hY0_pos
  unfold phiProgressionU1 phiProgressionU0 slantLogLength
  congr 1
  field_simp [hsR, hY0_ne]
  ring

/-- The ordinary-progression upper bound applied to the exact bare carrier
inside `lem:phi-progression-average`.  This is the formal version of using
`eq:ordinary-progression-coprime-upper` before the missing lower-bound and
Euler-product refinements are inserted. -/
theorem phiProgressionBareAverage_le_log_plus_inv
    (P : Params) (X : ℝ) (d a s : ℕ)
    (hd : 0 < d)
    (hU0 : 0 < phiProgressionU0 P s X)
    (hU01 : phiProgressionU0 P s X < phiProgressionU1 P s X) :
    phiProgressionBareAverage P X d a s ≤
      1 / phiProgressionU0 P s X +
        (1 / (d : ℝ)) *
          Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) := by
  rw [phiProgressionBareAverage_eq_sqfRecip]
  exact Inputs.sqfRecip_le_log_plus_inv X s d a hd hU0 hU01

/-- Same upper bound with the manuscript's named `slantLogLength` carrier. -/
theorem phiProgressionBareAverage_le_slantLog_plus_inv
    (P : Params) {X : ℝ} {d a s : ℕ}
    (hX : 0 < X) (hd : 0 < d) (hs : 0 < s)
    (hU0 : 0 < phiProgressionU0 P s X)
    (hU01 : phiProgressionU0 P s X < phiProgressionU1 P s X) :
    phiProgressionBareAverage P X d a s ≤
      1 / phiProgressionU0 P s X +
        (1 / (d : ℝ)) * slantLogLength P s X := by
  simpa [log_phiProgressionU1_div_U0_eq_slantLogLength P hX hs] using
    phiProgressionBareAverage_le_log_plus_inv P X d a s hd hU0 hU01

/-- Endpoint-absorbed fixed-`s` bare progression upper bound.

This is the checked algebra in `thm:tensor-e`: once the modulus lies below the
lower endpoint and the interval has logarithmic length at least one, the
elementary endpoint term `1/U₀` is absorbed into the main `D^{-1}` logarithmic
term. -/
theorem phiProgressionBareAverage_le_two_over_modulus_mul_slantLog
    (P : Params) {X : ℝ} {d a s : ℕ}
    (hX : 0 < X) (hd : 0 < d) (hs : 0 < s)
    (hU0 : 0 < phiProgressionU0 P s X)
    (hU01 : phiProgressionU0 P s X < phiProgressionU1 P s X)
    (hdU0 : (d : ℝ) ≤ phiProgressionU0 P s X)
    (hslant_one : (1 : ℝ) ≤ slantLogLength P s X) :
    phiProgressionBareAverage P X d a s
      ≤ 2 * ((1 : ℝ) / (d : ℝ) * slantLogLength P s X) := by
  have hbase :=
    phiProgressionBareAverage_le_slantLog_plus_inv
      (P := P) (X := X) (d := d) (a := a) (s := s)
      hX hd hs hU0 hU01
  have hd_pos_real : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hDinv_nonneg : 0 ≤ (1 : ℝ) / (d : ℝ) :=
    div_nonneg zero_le_one hd_pos_real.le
  have hendpoint_le_invD :
      (1 : ℝ) / phiProgressionU0 P s X ≤ (1 : ℝ) / (d : ℝ) := by
    exact one_div_le_one_div_of_le hd_pos_real hdU0
  have hinvD_le_main :
      (1 : ℝ) / (d : ℝ) ≤
        (1 : ℝ) / (d : ℝ) * slantLogLength P s X := by
    calc
      (1 : ℝ) / (d : ℝ) = (1 : ℝ) / (d : ℝ) * 1 := by ring
      _ ≤ (1 : ℝ) / (d : ℝ) * slantLogLength P s X :=
          mul_le_mul_of_nonneg_left hslant_one hDinv_nonneg
  have hsum :
      (1 : ℝ) / phiProgressionU0 P s X +
          (1 : ℝ) / (d : ℝ) * slantLogLength P s X
        ≤ 2 * ((1 : ℝ) / (d : ℝ) * slantLogLength P s X) := by
    nlinarith [hendpoint_le_invD.trans hinvD_le_main]
  exact hbase.trans hsum

/-- Wide-modulus eventual specialization of the endpoint-absorbed fixed-`s`
bare progression bound for the manuscript range `D≤YU`. -/
theorem phiProgressionBareAverage_le_two_over_modulus_mul_slantLog_of_wideModulus
    (P : Params) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ, 0 < d → 1 ≤ s →
        (s : ℝ) ≤ SScale P X →
        (d : ℝ) ≤ YScale P X * UScale X →
          phiProgressionBareAverage P X d a s
            ≤ 2 * ((1 : ℝ) / (d : ℝ) * slantLogLength P s X) := by
  rcases wideModulus_le_phiProgressionU0_eventually P with ⟨Xwide, hwide⟩
  rcases slantLogLength_ge_one_eventually P with ⟨Xslant, hslant⟩
  refine ⟨max (max Xwide Xslant) (Real.exp 1), ?_⟩
  intro X hX d a s hd hs hsS hdwide
  have hXwide : Xwide ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXslant : Xslant ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe
  have hXgtone : (1 : ℝ) < X :=
    lt_of_lt_of_le (by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)) hXe
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hU0pos : 0 < phiProgressionU0 P s X :=
    phiProgressionU0_pos P hXpos hs_pos
  have hU01 : phiProgressionU0 P s X < phiProgressionU1 P s X :=
    phiProgressionU0_lt_U1_of_s_le_SScale P hXgtone hs hsS
  have hdU0 : (d : ℝ) ≤ phiProgressionU0 P s X :=
    hwide X hXwide s d hs hsS hdwide
  have hslant_one : (1 : ℝ) ≤ slantLogLength P s X :=
    hslant X hXslant s hs hsS
  exact
    phiProgressionBareAverage_le_two_over_modulus_mul_slantLog
      (P := P) (X := X) (d := d) (a := a) (s := s)
      hXpos hd hs_pos hU0pos hU01 hdU0 hslant_one

/-- Wide-modulus fixed-`s` ordinary squarefree upper with the local density
factor.  This discharges the finite CRT/counting and endpoint-absorption part of
the `M₁` tensor fiber in the manuscript range `D≤YU`, assuming the endpoint
margin `2η+σ<λ` needed to put the CRT modulus `sD` below `U₀`. -/
theorem phiProgressionBareAverage_le_two_mul_shape_of_wideModulus
    (P : Params) (hmargin : 2 * P.η + P.σ < P.lam) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ, 0 < d → Squarefree d → 1 ≤ s → Squarefree s →
        Nat.Coprime s d →
        (s : ℝ) ≤ SScale P X →
        (d : ℝ) ≤ YScale P X * UScale X →
          phiProgressionBareAverage P X d a s
            ≤ 2 * phiProgressionAverageShape P X d s := by
  rcases wideModulus_mul_s_le_phiProgressionU0_eventually P hmargin with
    ⟨Xwide, hwide⟩
  rcases slantLogLength_ge_one_eventually P with ⟨Xslant, hslant⟩
  refine ⟨max (max Xwide Xslant) (Real.exp 1), ?_⟩
  intro X hX d a s hd hd_sqf hs hs_sqf hsd hsS hdwide
  have hXwide : Xwide ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXslant : Xslant ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe
  have hXgtone : (1 : ℝ) < X :=
    lt_of_lt_of_le (by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)) hXe
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hU0pos : 0 < phiProgressionU0 P s X :=
    phiProgressionU0_pos P hXpos hs_pos
  have hU01 : phiProgressionU0 P s X < phiProgressionU1 P s X :=
    phiProgressionU0_lt_U1_of_s_le_SScale P hXgtone hs hsS
  have hmod_le : ((s * d : ℕ) : ℝ) ≤ phiProgressionU0 P s X :=
    hwide X hXwide s d hs hsS hdwide
  have hslant_one : (1 : ℝ) ≤ slantLogLength P s X :=
    hslant X hXslant s hs hsS
  have hlog_one :
      (1 : ℝ) ≤ Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) := by
    simpa [log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos]
      using hslant_one
  have hsqf :
      Inputs.sqfRecip X s d a (phiProgressionU0 P s X) (phiProgressionU1 P s X)
        ≤ 2 * (((1 : ℝ) / (d : ℝ)) *
          ((Nat.totient s : ℝ) / (s : ℝ)) *
          Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)) :=
    Inputs.sqfRecip_le_totient_crt_density_of_endpoint
      X s d a hs_pos hd hsd hU0pos hU01 hmod_le hlog_one
  simpa [phiProgressionBareAverage_eq_sqfRecip, phiProgressionAverageShape,
    log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos] using hsqf

/-- Explicit-parameter version of the wide-modulus bare progression bound, with
the CRT endpoint margin discharged from the manuscript's fixed parameter
choice. -/
theorem phiProgressionBareAverage_le_two_mul_shape_of_wideModulus_explicit :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ, 0 < d → Squarefree d → 1 ≤ s → Squarefree s →
        Nat.Coprime s d →
        (s : ℝ) ≤ SScale Params.explicit X →
        (d : ℝ) ≤ YScale Params.explicit X * UScale X →
          phiProgressionBareAverage Params.explicit X d a s
            ≤ 2 * phiProgressionAverageShape Params.explicit X d s :=
  phiProgressionBareAverage_le_two_mul_shape_of_wideModulus
    Params.explicit explicit_two_eta_add_sigma_lt_lam

/-- Tensor-summed `M₁` wide-modulus bound with all nonstandard fiber hypotheses
discharged by the CRT endpoint calculation.  The remaining assumptions are the
paper-facing structural ones: squarefree modulus and the endpoint margin
`2η+σ<λ`. -/
theorem exactDivisorM1TensorFiberCoprime_le_massShape_over_modulus_of_wideModulus
    (P : Params) (hmargin : 2 * P.η + P.σ < P.lam) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D →
        (D : ℝ) ≤ YScale P X * UScale X →
        ∀ a : ℕ → ℕ,
          exactDivisorM1TensorFiberCoprime P X D a
            ≤ (2 / (D : ℝ)) * exactDivisorM1MassShape P X := by
  rcases phiProgressionBareAverage_le_two_mul_shape_of_wideModulus P hmargin with
    ⟨Xfiber, hfiber⟩
  refine ⟨max Xfiber (Real.exp 1), ?_⟩
  intro X hX D hD hDsqf hDwide a
  have hXfiber : Xfiber ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe
  have hDpos : 0 < D := lt_of_lt_of_le Nat.zero_lt_one hD
  exact
    exactDivisorM1TensorFiberCoprime_le_massShape_over_modulus
      P X D a 2 hXone hDpos (by norm_num)
      (by
        intro s hs hsD
        have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
          (Finset.mem_filter.mp hs).1
        have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
        have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
        have hs_sqf : Squarefree s := (Finset.mem_filter.mp hs).2
        have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
        have hS_nonneg : 0 ≤ SScale P X :=
          (Real.rpow_pos_of_pos hXpos P.η).le
        have hsS : (s : ℝ) ≤ SScale P X :=
          le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
        exact
          hfiber X hXfiber D (a s) s hDpos hDsqf hs_one hs_sqf hsD hsS hDwide)

/-- Explicit-parameter version of the tensor-summed `M₁` wide-modulus bound,
with the auxiliary CRT endpoint margin discharged from the manuscript's fixed
parameter values. -/
theorem
    exactDivisorM1TensorFiberCoprime_le_massShape_over_modulus_of_wideModulus_explicit :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D →
        (D : ℝ) ≤ YScale Params.explicit X * UScale X →
        ∀ a : ℕ → ℕ,
          exactDivisorM1TensorFiberCoprime Params.explicit X D a
            ≤ (2 / (D : ℝ)) * exactDivisorM1MassShape Params.explicit X :=
  exactDivisorM1TensorFiberCoprime_le_massShape_over_modulus_of_wideModulus
    Params.explicit explicit_two_eta_add_sigma_lt_lam

/-- If the bare reciprocal progression carrier has the lower bound from
partial summation, then the reciprocal-`φ` carrier has the same lower bound.
This isolates the manuscript sentence "Since `1/φ(r) ≥ 1/r`, this proves the
lower bound." -/
theorem phiProgressionAverage_lower_of_bare_lower
    {P : Params} {X : ℝ} {d a s : ℕ} {c : ℝ}
    (hbare : c * phiProgressionAverageShape P X d s ≤
      phiProgressionBareAverage P X d a s) :
    c * phiProgressionAverageShape P X d s ≤
      phiProgressionAverage P X d a s :=
  le_trans hbare (phiProgressionBareAverage_le_phiProgressionAverage P X d a s)

/-- Pointwise upper-bound reduction behind `lem:phi-progression-average`:
`1/φ(r) = (r/φ(r))·1/r ≤ τ(r)/r`. -/
theorem one_div_totient_le_tau_div_nat {r : ℕ} (hr : 0 < r) :
    (1 : ℝ) / (Nat.totient r : ℝ) ≤ (Inputs.tau r : ℝ) / (r : ℝ) := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hphi_pos_nat : 0 < Nat.totient r := Nat.totient_pos.mpr hr
  have hphi_pos : (0 : ℝ) < (Nat.totient r : ℝ) := by exact_mod_cast hphi_pos_nat
  have hratio : (r : ℝ) / (Nat.totient r : ℝ) ≤ (Inputs.tau r : ℝ) :=
    Inputs.div_totient_le_tau r hr
  have hmul :
      ((r : ℝ) / (Nat.totient r : ℝ)) * ((1 : ℝ) / (r : ℝ)) ≤
        (Inputs.tau r : ℝ) * ((1 : ℝ) / (r : ℝ)) :=
    mul_le_mul_of_nonneg_right hratio (div_nonneg zero_le_one hr_pos.le)
  calc
    (1 : ℝ) / (Nat.totient r : ℝ)
        = ((r : ℝ) / (Nat.totient r : ℝ)) * ((1 : ℝ) / (r : ℝ)) := by
            field_simp [ne_of_gt hr_pos, ne_of_gt hphi_pos]
    _ ≤ (Inputs.tau r : ℝ) * ((1 : ℝ) / (r : ℝ)) := hmul
    _ = (Inputs.tau r : ℝ) / (r : ℝ) := by ring

/-- The reciprocal-`φ` progression carrier is bounded by the `τ(r)/r`
majorant on the identical support. -/
theorem phiProgressionAverage_le_tauAverage
    (P : Params) (X : ℝ) (d a s : ℕ) :
    phiProgressionAverage P X d a s ≤
      phiProgressionTauAverage P X d a s := by
  classical
  unfold phiProgressionAverage phiProgressionTauAverage
  apply Finset.sum_le_sum
  intro r hr
  have hr_window :
      r ∈ Inputs.natWindow (phiProgressionU0 P s X)
        (phiProgressionU1 P s X) :=
    (Finset.mem_filter.mp hr).1
  have hr_pos_nat : 0 < r := by
    unfold Inputs.natWindow at hr_window
    exact lt_of_lt_of_le Nat.zero_lt_one
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hr_window).1).1
  exact one_div_totient_le_tau_div_nat hr_pos_nat

/-- Lower half of `lem:phi-progression-average`, isolated on the bare
reciprocal carrier. -/
def PhiProgressionBareLower (P : Params) : Prop :=
  ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ d a s : ℕ,
      0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
      Nat.Coprime a d →
      1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
        c * phiProgressionAverageShape P X d s ≤
          phiProgressionBareAverage P X d a s

/-- The ordinary-squarefree lower estimate on the exact moving interval gives
the bare lower half of `lem:phi-progression-average`.

All work here is bookkeeping: identify the bare carrier with `Inputs.sqfRecip`
and rewrite `log(U₁/U₀)` as the named slanted length. -/
theorem PhiProgressionBareLower_of_sqfRecipLower
    {P : Params} (h : PhiProgressionSqfRecipLower P) :
    PhiProgressionBareLower P := by
  rcases h with ⟨c, Xbase, hc, hlower⟩
  refine ⟨c, max Xbase 1, hc, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  have hXbase : Xbase ≤ X := le_trans (le_max_left Xbase 1) hX
  have hXone : (1 : ℝ) ≤ X := le_trans (le_max_right Xbase 1) hX
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hsqf :
      c * (((1 : ℝ) / (d : ℝ)) * ((Nat.totient s : ℝ) / (s : ℝ)) *
          Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X))
        ≤ Inputs.sqfRecip X s d a
          (phiProgressionU0 P s X) (phiProgressionU1 P s X) :=
    hlower X hXbase d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS
  simpa [phiProgressionBareAverage_eq_sqfRecip,
    phiProgressionAverageShape,
    log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos] using hsqf

/-- Dyadic anchor used in the counting proof of
`lem:phi-progression-average`, starting from the moving lower endpoint
`U₀=Y₀/s`. -/
noncomputable def phiProgressionDyadicAnchor
    (P : Params) (X : ℝ) (s k : ℕ) : ℝ :=
  phiProgressionU0 P s X * (2 : ℝ) ^ k

/-- Exact squarefree/coprime reduced-progression support on the dyadic block
`(T,2T]`, where `T = phiProgressionDyadicAnchor P X s k`. -/
noncomputable def phiProgressionDyadicSqfSupport
    (P : Params) (X : ℝ) (d a s k : ℕ) : Finset ℕ := by
  classical
  let T := phiProgressionDyadicAnchor P X s k
  exact
    (Inputs.natWindow T (2 * T)).filter
      (fun r => Squarefree r ∧ Nat.Coprime r s ∧ Inputs.congMod r a d)

/-- Count-level main-term shape for the dyadic block in the proof of
`lem:phi-progression-average`: block length `T`, progression density `1/d`,
and local coprime squarefree density `φ(s)/s`. -/
noncomputable def phiProgressionDyadicSqfCountShape
    (P : Params) (X : ℝ) (d s k : ℕ) : ℝ :=
  phiProgressionDyadicAnchor P X s k *
    (((1 : ℝ) / (d : ℝ)) * ((Nat.totient s : ℝ) / (s : ℝ)))

/-- Dyadic-count lower target corresponding to the manuscript's Mobius/CRT
counting paragraph in `lem:phi-progression-average`.

This is a theorem-level target, not an axiom.  It isolates the finite counting
claim that remains before the lower reciprocal estimate can be obtained by
dyadic partial summation. -/
def PhiProgressionDyadicSqfCountLower (P : Params) : Prop :=
  ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ d a s : ℕ,
      0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
      Nat.Coprime a d →
      1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
        ∀ k : ℕ,
          0 < phiProgressionDyadicAnchor P X s k →
          2 * phiProgressionDyadicAnchor P X s k ≤ phiProgressionU1 P s X →
            c * phiProgressionDyadicSqfCountShape P X d s k ≤
              ((phiProgressionDyadicSqfSupport P X d a s k).card : ℝ)

/-- On a dyadic block `(T,2T]`, the reciprocal sum is at least the count divided
by `2T`.  This is the finite partial-summation inequality used to pass
from dyadic counts to reciprocal mass. -/
theorem phiProgressionDyadicSqfCount_div_upper_le_sqfRecip
    (P : Params) (X : ℝ) (d a s k : ℕ)
    (hT : 0 < phiProgressionDyadicAnchor P X s k) :
    ((phiProgressionDyadicSqfSupport P X d a s k).card : ℝ) /
        (2 * phiProgressionDyadicAnchor P X s k) ≤
      Inputs.sqfRecip X s d a
        (phiProgressionDyadicAnchor P X s k)
        (2 * phiProgressionDyadicAnchor P X s k) := by
  classical
  let T := phiProgressionDyadicAnchor P X s k
  have hTpos : 0 < T := hT
  have h2Tpos : 0 < 2 * T := by positivity
  have h2Tnonneg : 0 ≤ 2 * T := h2Tpos.le
  let S : Finset ℕ :=
    (Inputs.natWindow T (2 * T)).filter
      (fun r => Squarefree r ∧ Nat.Coprime r s ∧ Inputs.congMod r a d)
  have hsupport : phiProgressionDyadicSqfSupport P X d a s k = S := by
    simp [phiProgressionDyadicSqfSupport, T]
  rw [hsupport]
  have hconst :
      ((S.card : ℝ) / (2 * T)) =
        ∑ _r ∈ S, (1 : ℝ) / (2 * T) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  calc
    (S.card : ℝ) / (2 * T)
        = ∑ _r ∈ S, (1 : ℝ) / (2 * T) := hconst
    _ ≤ ∑ r ∈ S, (1 : ℝ) / (r : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr_window : r ∈ Inputs.natWindow T (2 * T) :=
        (Finset.mem_filter.mp hr).1
      have hr_icc : r ∈ Finset.Icc (1 : ℕ) ⌊2 * T⌋₊ := by
        unfold Inputs.natWindow at hr_window
        exact (Finset.mem_filter.mp hr_window).1
      have hr_one : 1 ≤ r := (Finset.mem_Icc.mp hr_icc).1
      have hr_pos_nat : 0 < r := lt_of_lt_of_le Nat.zero_lt_one hr_one
      have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr_pos_nat
      have hr_floor : r ≤ ⌊2 * T⌋₊ := (Finset.mem_Icc.mp hr_icc).2
      have hr_le : (r : ℝ) ≤ 2 * T :=
        le_trans (by exact_mod_cast hr_floor) (Nat.floor_le h2Tnonneg)
      exact one_div_le_one_div_of_le hr_pos hr_le
    _ = Inputs.sqfRecip X s d a T (2 * T) := by
      rfl

/-- On a dyadic block `(T,2T]`, the reciprocal carrier is bounded above by
the block count divided by the lower endpoint.  Together with an ordinary
squarefree reciprocal lower bound, this gives the count lower bound needed by
the dyadic partial-summation bridge. -/
theorem phiProgressionDyadicSqfRecip_le_count_div_lower
    (P : Params) (X : ℝ) (d a s k : ℕ)
    (hT : 0 < phiProgressionDyadicAnchor P X s k) :
      Inputs.sqfRecip X s d a
        (phiProgressionDyadicAnchor P X s k)
        (2 * phiProgressionDyadicAnchor P X s k) ≤
      ((phiProgressionDyadicSqfSupport P X d a s k).card : ℝ) /
        phiProgressionDyadicAnchor P X s k := by
  classical
  let T := phiProgressionDyadicAnchor P X s k
  have hTpos : 0 < T := hT
  let S : Finset ℕ :=
    (Inputs.natWindow T (2 * T)).filter
      (fun r => Squarefree r ∧ Nat.Coprime r s ∧ Inputs.congMod r a d)
  have hsupport : phiProgressionDyadicSqfSupport P X d a s k = S := by
    simp [phiProgressionDyadicSqfSupport, T]
  have hconst :
      ∑ _r ∈ S, (1 : ℝ) / T = ((S.card : ℝ) / T) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hsupport]
  calc
    Inputs.sqfRecip X s d a T (2 * T)
        = ∑ r ∈ S, (1 : ℝ) / (r : ℝ) := by
          rfl
    _ ≤ ∑ _r ∈ S, (1 : ℝ) / T := by
      apply Finset.sum_le_sum
      intro r hr
      have hr_window : r ∈ Inputs.natWindow T (2 * T) :=
        (Finset.mem_filter.mp hr).1
      have hr_gt : T < (r : ℝ) := by
        unfold Inputs.natWindow at hr_window
        exact (Finset.mem_filter.mp hr_window).2
      exact one_div_le_one_div_of_le hTpos hr_gt.le
    _ = (S.card : ℝ) / T := hconst

/-- Count lower bound on one dyadic block gives the reciprocal lower bound on
that same block.  This is the first checked step toward the full
dyadic-partial-summation proof of the lower half of
`lem:phi-progression-average`. -/
theorem phiProgressionDyadicSqfBlockRecipLower_of_countLower
    {P : Params} {X : ℝ} {d a s k : ℕ} {c : ℝ}
    (hT : 0 < phiProgressionDyadicAnchor P X s k)
    (hcount :
      c * phiProgressionDyadicSqfCountShape P X d s k ≤
        ((phiProgressionDyadicSqfSupport P X d a s k).card : ℝ)) :
    (c / 2) *
        (((1 : ℝ) / (d : ℝ)) * ((Nat.totient s : ℝ) / (s : ℝ))) ≤
      Inputs.sqfRecip X s d a
        (phiProgressionDyadicAnchor P X s k)
        (2 * phiProgressionDyadicAnchor P X s k) := by
  let T := phiProgressionDyadicAnchor P X s k
  have hTpos : 0 < T := hT
  have hden_nonneg : 0 ≤ 2 * T := by positivity
  have hbridge :=
    phiProgressionDyadicSqfCount_div_upper_le_sqfRecip P X d a s k hT
  calc
    (c / 2) *
        (((1 : ℝ) / (d : ℝ)) * ((Nat.totient s : ℝ) / (s : ℝ)))
        = (c * phiProgressionDyadicSqfCountShape P X d s k) / (2 * T) := by
          have hT_ne :
              phiProgressionDyadicAnchor P X s k ≠ 0 :=
            ne_of_gt hT
          unfold phiProgressionDyadicSqfCountShape
          dsimp [T]
          field_simp [hT_ne]
          ring_nf
          simp [hT_ne]
    _ ≤ ((phiProgressionDyadicSqfSupport P X d a s k).card : ℝ) / (2 * T) :=
        div_le_div_of_nonneg_right hcount hden_nonneg
    _ ≤ Inputs.sqfRecip X s d a
          (phiProgressionDyadicAnchor P X s k)
          (2 * phiProgressionDyadicAnchor P X s k) := hbridge

/-- A dyadic squarefree reciprocal block inside the moving
`lem:phi-progression-average` interval is bounded by the full squarefree
reciprocal carrier.  This is the finite support-inclusion step needed before
dyadic block lower bounds can be summed into the full lower estimate. -/
theorem phiProgressionDyadicSqfRecip_le_full_sqfRecip
    {P : Params} {X : ℝ} {d a s k : ℕ}
    (hT : 0 < phiProgressionDyadicAnchor P X s k)
    (hleft :
      phiProgressionU0 P s X ≤ phiProgressionDyadicAnchor P X s k)
    (hright :
      2 * phiProgressionDyadicAnchor P X s k ≤ phiProgressionU1 P s X) :
    Inputs.sqfRecip X s d a
        (phiProgressionDyadicAnchor P X s k)
        (2 * phiProgressionDyadicAnchor P X s k) ≤
      Inputs.sqfRecip X s d a
        (phiProgressionU0 P s X) (phiProgressionU1 P s X) := by
  classical
  unfold Inputs.sqfRecip
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    have hn_window :
        n ∈ Inputs.natWindow (phiProgressionDyadicAnchor P X s k)
          (2 * phiProgressionDyadicAnchor P X s k) :=
      (Finset.mem_filter.mp hn).1
    have hn_filters := (Finset.mem_filter.mp hn).2
    have hn_full_window :
        n ∈ Inputs.natWindow (phiProgressionU0 P s X)
          (phiProgressionU1 P s X) := by
      unfold Inputs.natWindow at hn_window ⊢
      have hn_icc :
          n ∈ Finset.Icc (1 : ℕ)
            ⌊2 * phiProgressionDyadicAnchor P X s k⌋₊ :=
        (Finset.mem_filter.mp hn_window).1
      have hn_lower_block :
          phiProgressionDyadicAnchor P X s k < (n : ℝ) :=
        (Finset.mem_filter.mp hn_window).2
      have hn_lower_full :
          phiProgressionU0 P s X < (n : ℝ) :=
        lt_of_le_of_lt hleft hn_lower_block
      have h2T_nonneg :
          0 ≤ 2 * phiProgressionDyadicAnchor P X s k := by
        positivity
      have hn_le_floor_block :
          n ≤ ⌊2 * phiProgressionDyadicAnchor P X s k⌋₊ :=
        (Finset.mem_Icc.mp hn_icc).2
      have hn_le_block_upper :
          (n : ℝ) ≤ 2 * phiProgressionDyadicAnchor P X s k :=
        le_trans (by exact_mod_cast hn_le_floor_block) (Nat.floor_le h2T_nonneg)
      have hn_le_full_upper :
          (n : ℝ) ≤ phiProgressionU1 P s X :=
        le_trans hn_le_block_upper hright
      have hn_floor_full :
          n ≤ ⌊phiProgressionU1 P s X⌋₊ :=
        Nat.le_floor hn_le_full_upper
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn_icc).1, hn_floor_full⟩,
          hn_lower_full⟩
    exact Finset.mem_filter.mpr ⟨hn_full_window, hn_filters⟩
  · intro n _hn_big _hn_small
    exact div_nonneg zero_le_one (Nat.cast_nonneg n)

/-- A count lower bound on an admissible dyadic block gives a lower bound for
the full moving squarefree reciprocal carrier.  This is the checked local
bridge from the manuscript's dyadic counting paragraph into the exact
`PhiProgressionSqfRecipLower` carrier. -/
theorem phiProgressionDyadicSqfBlockRecipLower_full_of_countLower
    {P : Params} {X : ℝ} {d a s k : ℕ} {c : ℝ}
    (hT : 0 < phiProgressionDyadicAnchor P X s k)
    (hleft :
      phiProgressionU0 P s X ≤ phiProgressionDyadicAnchor P X s k)
    (hright :
      2 * phiProgressionDyadicAnchor P X s k ≤ phiProgressionU1 P s X)
    (hcount :
      c * phiProgressionDyadicSqfCountShape P X d s k ≤
        ((phiProgressionDyadicSqfSupport P X d a s k).card : ℝ)) :
    (c / 2) *
        (((1 : ℝ) / (d : ℝ)) * ((Nat.totient s : ℝ) / (s : ℝ))) ≤
      Inputs.sqfRecip X s d a
        (phiProgressionU0 P s X) (phiProgressionU1 P s X) := by
  exact
    (phiProgressionDyadicSqfBlockRecipLower_of_countLower
      (P := P) (X := X) (d := d) (a := a) (s := s) (k := k) (c := c)
      hT hcount).trans
      (phiProgressionDyadicSqfRecip_le_full_sqfRecip
        (P := P) (X := X) (d := d) (a := a) (s := s) (k := k)
        hT hleft hright)

/-- Doubling the phi-progress dyadic anchor advances the dyadic index. -/
theorem two_mul_phiProgressionDyadicAnchor
    (P : Params) (X : ℝ) (s k : ℕ) :
    2 * phiProgressionDyadicAnchor P X s k =
      phiProgressionDyadicAnchor P X s (k + 1) := by
  unfold phiProgressionDyadicAnchor
  rw [pow_succ]
  ring

/-- The zeroth phi-progress dyadic anchor is the moving lower endpoint `U₀`. -/
theorem phiProgressionDyadicAnchor_zero
    (P : Params) (X : ℝ) (s : ℕ) :
    phiProgressionDyadicAnchor P X s 0 = phiProgressionU0 P s X := by
  unfold phiProgressionDyadicAnchor
  simp

/-- The phi-progress dyadic anchor is monotone in the dyadic index. -/
theorem phiProgressionDyadicAnchor_mono
    {P : Params} {X : ℝ} {s j k : ℕ}
    (hU0 : 0 < phiProgressionU0 P s X) (hjk : j ≤ k) :
    phiProgressionDyadicAnchor P X s j ≤
      phiProgressionDyadicAnchor P X s k := by
  unfold phiProgressionDyadicAnchor
  have hpow : (2 : ℝ) ^ j ≤ 2 ^ k :=
    pow_le_pow_right₀ (by norm_num) hjk
  exact mul_le_mul_of_nonneg_left hpow hU0.le

/-- The dyadic squarefree supports used in the lower half of
`lem:phi-progression-average` are pairwise disjoint. -/
theorem phiProgressionDyadicSqfSupport_pairwiseDisjoint
    (P : Params) (X : ℝ) (d a s : ℕ)
    (hU0 : 0 < phiProgressionU0 P s X) (K : Finset ℕ) :
    Set.PairwiseDisjoint (↑K)
      (fun k => phiProgressionDyadicSqfSupport P X d a s k) := by
  classical
  have key : ∀ j k : ℕ, j < k →
      Disjoint (phiProgressionDyadicSqfSupport P X d a s j)
        (phiProgressionDyadicSqfSupport P X d a s k) := by
    intro j k hlt
    rw [Finset.disjoint_left]
    intro n hnj hnk
    have hwinj :
        n ∈ Inputs.natWindow (phiProgressionDyadicAnchor P X s j)
          (2 * phiProgressionDyadicAnchor P X s j) :=
      (Finset.mem_filter.mp hnj).1
    have hwink :
        n ∈ Inputs.natWindow (phiProgressionDyadicAnchor P X s k)
          (2 * phiProgressionDyadicAnchor P X s k) :=
      (Finset.mem_filter.mp hnk).1
    have hnj_icc :
        n ∈ Finset.Icc (1 : ℕ)
          ⌊2 * phiProgressionDyadicAnchor P X s j⌋₊ := by
      unfold Inputs.natWindow at hwinj
      exact (Finset.mem_filter.mp hwinj).1
    have h2j_nonneg :
        0 ≤ 2 * phiProgressionDyadicAnchor P X s j := by
      unfold phiProgressionDyadicAnchor
      positivity
    have hn_le_upper_j :
        (n : ℝ) ≤ 2 * phiProgressionDyadicAnchor P X s j :=
      le_trans
        (by exact_mod_cast (Finset.mem_Icc.mp hnj_icc).2)
        (Nat.floor_le h2j_nonneg)
    have hk_lower :
        phiProgressionDyadicAnchor P X s k < (n : ℝ) := by
      unfold Inputs.natWindow at hwink
      exact (Finset.mem_filter.mp hwink).2
    rw [two_mul_phiProgressionDyadicAnchor] at hn_le_upper_j
    have hmono :
        phiProgressionDyadicAnchor P X s (j + 1) ≤
          phiProgressionDyadicAnchor P X s k :=
      phiProgressionDyadicAnchor_mono hU0 (by omega)
    have hn_le_anchor_k :
        (n : ℝ) ≤ phiProgressionDyadicAnchor P X s k :=
      le_trans hn_le_upper_j hmono
    exact absurd hk_lower (not_lt.mpr hn_le_anchor_k)
  intro j _hj k _hk hjk
  rcases lt_or_gt_of_ne hjk with h | h
  · exact key j k h
  · exact (key k j h).symm

/-- Full squarefree/coprime progression support on the moving interval in
`lem:phi-progression-average`. -/
noncomputable def phiProgressionFullSqfSupport
    (P : Params) (X : ℝ) (d a s : ℕ) : Finset ℕ := by
  classical
  exact
    (Inputs.natWindow (phiProgressionU0 P s X)
      (phiProgressionU1 P s X)).filter
      (fun n => Squarefree n ∧ Nat.Coprime n s ∧ Inputs.congMod n a d)

/-- The union of the first complete phi-progress dyadic squarefree blocks lies
inside the full moving squarefree reciprocal carrier. -/
theorem biUnion_phiProgressionDyadicSqfSupport_subset_full
    {P : Params} {X : ℝ} {d a s N : ℕ}
    (hU0 : 0 < phiProgressionU0 P s X)
    (hreach : phiProgressionDyadicAnchor P X s N ≤
      phiProgressionU1 P s X) :
    (Finset.range N).biUnion
        (fun k => phiProgressionDyadicSqfSupport P X d a s k)
      ⊆
        phiProgressionFullSqfSupport P X d a s := by
  classical
  intro n hn
  rw [Finset.mem_biUnion] at hn
  rcases hn with ⟨k, hk, hnk⟩
  have hk_lt : k < N := Finset.mem_range.mp hk
  have hwin :
      n ∈ Inputs.natWindow (phiProgressionDyadicAnchor P X s k)
        (2 * phiProgressionDyadicAnchor P X s k) :=
    (Finset.mem_filter.mp hnk).1
  have hfilters := (Finset.mem_filter.mp hnk).2
  have hn_full_window :
      n ∈ Inputs.natWindow (phiProgressionU0 P s X)
        (phiProgressionU1 P s X) := by
    unfold Inputs.natWindow at hwin ⊢
    have hn_icc :
        n ∈ Finset.Icc (1 : ℕ)
          ⌊2 * phiProgressionDyadicAnchor P X s k⌋₊ :=
      (Finset.mem_filter.mp hwin).1
    have hn_lower_block :
        phiProgressionDyadicAnchor P X s k < (n : ℝ) :=
      (Finset.mem_filter.mp hwin).2
    have hzero_le :
        phiProgressionU0 P s X ≤ phiProgressionDyadicAnchor P X s k := by
      rw [← phiProgressionDyadicAnchor_zero P X s]
      exact phiProgressionDyadicAnchor_mono hU0 (Nat.zero_le k)
    have hn_lower_full :
        phiProgressionU0 P s X < (n : ℝ) :=
      lt_of_le_of_lt hzero_le hn_lower_block
    have h2k_nonneg :
        0 ≤ 2 * phiProgressionDyadicAnchor P X s k := by
      unfold phiProgressionDyadicAnchor
      positivity
    have hn_le_floor_block :
        n ≤ ⌊2 * phiProgressionDyadicAnchor P X s k⌋₊ :=
      (Finset.mem_Icc.mp hn_icc).2
    have hn_le_block_upper :
        (n : ℝ) ≤ 2 * phiProgressionDyadicAnchor P X s k :=
      le_trans (by exact_mod_cast hn_le_floor_block) (Nat.floor_le h2k_nonneg)
    have hnext_le :
        phiProgressionDyadicAnchor P X s (k + 1) ≤
          phiProgressionDyadicAnchor P X s N :=
      phiProgressionDyadicAnchor_mono hU0 (by omega)
    rw [two_mul_phiProgressionDyadicAnchor] at hn_le_block_upper
    have hn_le_full_upper :
        (n : ℝ) ≤ phiProgressionU1 P s X :=
      le_trans hn_le_block_upper (le_trans hnext_le hreach)
    have hn_floor_full :
        n ≤ ⌊phiProgressionU1 P s X⌋₊ :=
      Nat.le_floor hn_le_full_upper
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn_icc).1, hn_floor_full⟩,
        hn_lower_full⟩
  exact Finset.mem_filter.mpr ⟨hn_full_window, hfilters⟩

/-- Lower dyadic partial summation at block-reciprocal altitude for the
phi-progression squarefree carrier: the reciprocal mass of the first complete
dyadic blocks is contained in the full moving window. -/
theorem phiProgressionDyadicSqfRecipRangeSum_le_full_sqfRecip
    {P : Params} {X : ℝ} {d a s N : ℕ}
    (hU0 : 0 < phiProgressionU0 P s X)
    (hreach : phiProgressionDyadicAnchor P X s N ≤
      phiProgressionU1 P s X) :
    ∑ k ∈ Finset.range N,
        Inputs.sqfRecip X s d a
          (phiProgressionDyadicAnchor P X s k)
          (2 * phiProgressionDyadicAnchor P X s k)
      ≤
        Inputs.sqfRecip X s d a
          (phiProgressionU0 P s X) (phiProgressionU1 P s X) := by
  classical
  have hsub :=
    biUnion_phiProgressionDyadicSqfSupport_subset_full
      (P := P) (X := X) (d := d) (a := a) (s := s) (N := N)
      hU0 hreach
  have hdisj :=
    phiProgressionDyadicSqfSupport_pairwiseDisjoint P X d a s hU0
      (Finset.range N)
  calc
    ∑ k ∈ Finset.range N,
        Inputs.sqfRecip X s d a
          (phiProgressionDyadicAnchor P X s k)
          (2 * phiProgressionDyadicAnchor P X s k)
        = ∑ k ∈ Finset.range N,
            ∑ n ∈ phiProgressionDyadicSqfSupport P X d a s k,
              (1 : ℝ) / (n : ℝ) := by
          apply Finset.sum_congr rfl
          intro k _hk
          simp [Inputs.sqfRecip, phiProgressionDyadicSqfSupport]
    _ = ∑ n ∈ (Finset.range N).biUnion
          (fun k => phiProgressionDyadicSqfSupport P X d a s k),
          (1 : ℝ) / (n : ℝ) := by
          rw [Finset.sum_biUnion hdisj]
    _ ≤ ∑ n ∈ phiProgressionFullSqfSupport P X d a s,
          (1 : ℝ) / (n : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro n _ _
          exact div_nonneg zero_le_one (Nat.cast_nonneg n)
    _ =
        Inputs.sqfRecip X s d a
          (phiProgressionU0 P s X) (phiProgressionU1 P s X) := by
          simp [Inputs.sqfRecip, phiProgressionFullSqfSupport]

/-- If every complete dyadic block has the count lower bound, then the sum of
the corresponding dyadic reciprocal lower bounds is contained in the full
moving squarefree reciprocal carrier.  This is the multi-block version of the
local count-to-reciprocal bridge. -/
theorem phiProgressionDyadicSqfCountLower_rangeSum_le_full_sqfRecip
    {P : Params} {X : ℝ} {d a s N : ℕ} {c : ℝ}
    (hU0 : 0 < phiProgressionU0 P s X)
    (hreach : phiProgressionDyadicAnchor P X s N ≤
      phiProgressionU1 P s X)
    (hcount : ∀ k ∈ Finset.range N,
      c * phiProgressionDyadicSqfCountShape P X d s k ≤
        ((phiProgressionDyadicSqfSupport P X d a s k).card : ℝ)) :
    ∑ _k ∈ Finset.range N,
        (c / 2) *
          (((1 : ℝ) / (d : ℝ)) * ((Nat.totient s : ℝ) / (s : ℝ))) ≤
      Inputs.sqfRecip X s d a
        (phiProgressionU0 P s X) (phiProgressionU1 P s X) := by
  have hblocks :
      ∑ _k ∈ Finset.range N,
          (c / 2) *
            (((1 : ℝ) / (d : ℝ)) * ((Nat.totient s : ℝ) / (s : ℝ))) ≤
        ∑ k ∈ Finset.range N,
          Inputs.sqfRecip X s d a
            (phiProgressionDyadicAnchor P X s k)
            (2 * phiProgressionDyadicAnchor P X s k) := by
    apply Finset.sum_le_sum
    intro k hk
    have hT : 0 < phiProgressionDyadicAnchor P X s k := by
      unfold phiProgressionDyadicAnchor
      positivity
    exact
      phiProgressionDyadicSqfBlockRecipLower_of_countLower
        (P := P) (X := X) (d := d) (a := a) (s := s) (k := k) (c := c)
        hT (hcount k hk)
  exact hblocks.trans
    (phiProgressionDyadicSqfRecipRangeSum_le_full_sqfRecip
      (P := P) (X := X) (d := d) (a := a) (s := s) (N := N)
      hU0 hreach)

/-- Log-length form of the dyadic lower bridge.  Once the complete dyadic
blocks cover a fixed positive fraction of `log(U₁/U₀)`, the count lower bound
on those blocks gives the exact squarefree reciprocal lower carrier used in
`PhiProgressionSqfRecipLower`. -/
theorem phiProgressionDyadicSqfCountLower_logShape_le_full_sqfRecip
    {P : Params} {X : ℝ} {d a s N : ℕ} {c cφ : ℝ}
    (hU0 : 0 < phiProgressionU0 P s X)
    (hreach : phiProgressionDyadicAnchor P X s N ≤
      phiProgressionU1 P s X)
    (hlogBlocks :
      cφ * Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) ≤
        (N : ℝ) * (c / 2))
    (hcount : ∀ k ∈ Finset.range N,
      c * phiProgressionDyadicSqfCountShape P X d s k ≤
        ((phiProgressionDyadicSqfSupport P X d a s k).card : ℝ)) :
    cφ *
        (((1 : ℝ) / (d : ℝ)) * ((Nat.totient s : ℝ) / (s : ℝ)) *
          Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)) ≤
      Inputs.sqfRecip X s d a
        (phiProgressionU0 P s X) (phiProgressionU1 P s X) := by
  let B : ℝ := ((1 : ℝ) / (d : ℝ)) * ((Nat.totient s : ℝ) / (s : ℝ))
  let L : ℝ := Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (div_nonneg zero_le_one (Nat.cast_nonneg d))
      (div_nonneg (Nat.cast_nonneg (Nat.totient s)) (Nat.cast_nonneg s))
  have hscaled : B * (cφ * L) ≤ B * ((N : ℝ) * (c / 2)) :=
    mul_le_mul_of_nonneg_left (by simpa [L] using hlogBlocks) hB_nonneg
  have hsum :
      cφ * (B * L) ≤
        ∑ _k ∈ Finset.range N, (c / 2) * B := by
    calc
      cφ * (B * L) = B * (cφ * L) := by ring
      _ ≤ B * ((N : ℝ) * (c / 2)) := hscaled
      _ = ∑ _k ∈ Finset.range N, (c / 2) * B := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  exact hsum.trans
    (by
      simpa [B] using
        phiProgressionDyadicSqfCountLower_rangeSum_le_full_sqfRecip
          (P := P) (X := X) (d := d) (a := a) (s := s) (N := N) (c := c)
          hU0 hreach hcount)

/-- Deterministic block-count target for the dyadic proof of the lower half of
`lem:phi-progression-average`: the first complete dyadic blocks inside
`(U₀,U₁]` are numerous enough to cover a fixed fraction of the logarithmic
length.  The remaining proof of this target is elementary dyadic/log
bookkeeping, not an additional analytic input. -/
def PhiProgressionDyadicBlockLogCover (P : Params) : Prop :=
  ∃ β X₀ : ℝ, 0 < β ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ s : ℕ,
      1 ≤ s → Squarefree s → (s : ℝ) ≤ SScale P X →
        ∃ N : ℕ,
          phiProgressionDyadicAnchor P X s N ≤ phiProgressionU1 P s X ∧
            β * Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) ≤
              (N : ℝ)

/-- The dyadic blocks in the phi-progress interval cover a fixed fraction of
the logarithmic length.  This discharges the remaining elementary dyadic/log
bookkeeping needed by the count-to-reciprocal bridge. -/
theorem PhiProgressionDyadicBlockLogCover_concrete (P : Params) :
    PhiProgressionDyadicBlockLogCover P := by
  let α : ℝ := P.θ - P.lam - P.η
  have hα : 0 < α := by
    dsimp [α]
    linarith [P.lam_add_η_lt_θ]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine
    ⟨1 / (2 * Real.log 2),
      max (Real.exp 1) (Real.exp (2 * Real.log 2 / α + 1)),
      by positivity, ?_⟩
  intro X hX s hs_one _hs_sqf hsS
  have hXexp1 : Real.exp 1 ≤ X :=
    le_trans (le_max_left _ _) hX
  have hXexp_big : Real.exp (2 * Real.log 2 / α + 1) ≤ X :=
    le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXexp1
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hXgtone : (1 : ℝ) < X :=
    lt_of_lt_of_le (by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)) hXexp1
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hU0 : 0 < phiProgressionU0 P s X :=
    phiProgressionU0_pos P hXpos hs_pos
  have hU01 : phiProgressionU0 P s X < phiProgressionU1 P s X :=
    phiProgressionU0_lt_U1_of_s_le_SScale P hXgtone hs_one hsS
  have hU1 : 0 < phiProgressionU1 P s X := lt_trans hU0 hU01
  let L : ℝ := Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)
  let q : ℝ := L / Real.log 2
  let N : ℕ := ⌊q⌋₊
  have hlogX_big : 2 * Real.log 2 / α + 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hXexp_big
  have hL_eq_slant : L = slantLogLength P s X := by
    dsimp [L]
    exact log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos
  have hL_ge_alpha_log :
      α * Real.log X ≤ L := by
    rw [hL_eq_slant]
    simpa [α] using
      slantLogLength_ge_theta_sub_lam_sub_eta_mul_log P hXone hs_one hsS
  have hL_ge_two_log2 : 2 * Real.log 2 ≤ L := by
    have hstep : 2 * Real.log 2 + α ≤ α * Real.log X := by
      calc
        2 * Real.log 2 + α
            = α * (2 * Real.log 2 / α + 1) := by
                field_simp [ne_of_gt hα]
        _ ≤ α * Real.log X := mul_le_mul_of_nonneg_left hlogX_big hα.le
    linarith
  have hL_nonneg : 0 ≤ L := le_trans (by positivity) hL_ge_two_log2
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hL_nonneg hlog2.le
  have hfloor_le : (N : ℝ) ≤ q := by
    dsimp [N]
    exact Nat.floor_le hq_nonneg
  have hlt_floor : q < (N : ℝ) + 1 := by
    dsimp [N]
    exact Nat.lt_floor_add_one q
  have hq_ge_two : (2 : ℝ) ≤ q := by
    dsimp [q]
    rw [le_div_iff₀ hlog2]
    simpa using hL_ge_two_log2
  have hhalf_le_floor : (1 / (2 * Real.log 2)) * L ≤ (N : ℝ) := by
    have hhalf_le : q / 2 ≤ q - 1 := by linarith
    have hfloor_lower : q - 1 ≤ (N : ℝ) := by linarith
    calc
      (1 / (2 * Real.log 2)) * L = q / 2 := by
        dsimp [q]
        ring_nf
      _ ≤ q - 1 := hhalf_le
      _ ≤ (N : ℝ) := hfloor_lower
  have hpow2 : (2 : ℝ) ^ N = Real.exp ((N : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hratio_exp :
      phiProgressionU1 P s X / phiProgressionU0 P s X = Real.exp L := by
    dsimp [L]
    rw [Real.exp_log (div_pos hU1 hU0)]
  have hpow_le_ratio :
      (2 : ℝ) ^ N ≤ phiProgressionU1 P s X / phiProgressionU0 P s X := by
    rw [hpow2, hratio_exp]
    apply Real.exp_le_exp.mpr
    have : (N : ℝ) * Real.log 2 ≤ q * Real.log 2 :=
      mul_le_mul_of_nonneg_right hfloor_le hlog2.le
    calc
      (N : ℝ) * Real.log 2 ≤ q * Real.log 2 := this
      _ = L := by
          dsimp [q]
          field_simp [ne_of_gt hlog2]
  have hreach : phiProgressionDyadicAnchor P X s N ≤ phiProgressionU1 P s X := by
    unfold phiProgressionDyadicAnchor
    calc
      phiProgressionU0 P s X * (2 : ℝ) ^ N
          ≤ phiProgressionU0 P s X *
              (phiProgressionU1 P s X / phiProgressionU0 P s X) :=
            mul_le_mul_of_nonneg_left hpow_le_ratio hU0.le
      _ = phiProgressionU1 P s X := by
          field_simp [ne_of_gt hU0]
  exact ⟨N, hreach, by simpa [L] using hhalf_le_floor⟩

/-- Dyadic-count formulation of the lower half of
`lem:phi-progression-average`.

If the squarefree progression count lower bound holds on each complete dyadic
block and the complete blocks cover a fixed fraction of the log-length, then
the paper-facing squarefree reciprocal lower estimate follows with no further
analytic input. -/
theorem PhiProgressionSqfRecipLower_of_dyadic_countLower_and_blockLogCover
    {P : Params}
    (hcountLower : PhiProgressionDyadicSqfCountLower P)
    (hcover : PhiProgressionDyadicBlockLogCover P) :
    PhiProgressionSqfRecipLower P := by
  rcases hcountLower with ⟨c, Xcount, hc, hcountLower⟩
  rcases hcover with ⟨β, Xcover, hβ, hcover⟩
  refine ⟨β * c / 2, max (max Xcount Xcover) (Real.exp 1), by positivity, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  have hXcount : Xcount ≤ X :=
    le_trans (le_trans (le_max_left Xcount Xcover)
      (le_max_left (max Xcount Xcover) (Real.exp 1))) hX
  have hXcover : Xcover ≤ X :=
    le_trans (le_trans (le_max_right Xcount Xcover)
      (le_max_left (max Xcount Xcover) (Real.exp 1))) hX
  have hXexp : Real.exp 1 ≤ X :=
    le_trans (le_max_right (max Xcount Xcover) (Real.exp 1)) hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hXexp
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hU0 : 0 < phiProgressionU0 P s X :=
    phiProgressionU0_pos P hXpos hs_pos
  rcases hcover X hXcover s hs_one hs_sqf hsS with ⟨N, hreach, hNlog⟩
  have hcount : ∀ k ∈ Finset.range N,
      c * phiProgressionDyadicSqfCountShape P X d s k ≤
        ((phiProgressionDyadicSqfSupport P X d a s k).card : ℝ) := by
    intro k hk
    have hT : 0 < phiProgressionDyadicAnchor P X s k := by
      unfold phiProgressionDyadicAnchor
      positivity
    have hk_lt : k < N := Finset.mem_range.mp hk
    have hright :
        2 * phiProgressionDyadicAnchor P X s k ≤
          phiProgressionU1 P s X := by
      rw [two_mul_phiProgressionDyadicAnchor]
      exact (phiProgressionDyadicAnchor_mono hU0 (by omega)).trans hreach
    exact
      hcountLower X hXcount d a s hd_pos hd_sqf hd_odd hdU ha_coprime
        hs_one hs_sqf hs_coprime hsS k hT hright
  have hlogBlocks :
      (β * c / 2) *
          Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) ≤
        (N : ℝ) * (c / 2) := by
    have hc2_nonneg : 0 ≤ c / 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hNlog hc2_nonneg
    calc
      (β * c / 2) *
          Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)
          =
        (β * Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)) *
          (c / 2) := by ring
      _ ≤ (N : ℝ) * (c / 2) := hmul
  simpa [mul_assoc] using
    phiProgressionDyadicSqfCountLower_logShape_le_full_sqfRecip
      (P := P) (X := X) (d := d) (a := a) (s := s) (N := N)
      (c := c) (cφ := β * c / 2)
      hU0 hreach hlogBlocks hcount

/-- Upper half of `lem:phi-progression-average`, isolated on the
`τ(r)/r` majorant carrier. -/
def PhiProgressionTauUpper (P : Params) : Prop :=
  ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ d a s : ℕ,
      0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
      Nat.Coprime a d →
      1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
        phiProgressionTauAverage P X d a s ≤
          C * phiProgressionAverageShape P X d s

/-- Upper half of `lem:phi-progression-average` after the exact quotient split
`r = k·t` in the `τ(r)/r` majorant.  This is the form that the manuscript's
divisor-interchange estimate naturally has to bound. -/
def PhiProgressionTauQuotientUpper (P : Params) : Prop :=
  ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ d a s : ℕ,
      0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
      Nat.Coprime a d →
      1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
        phiProgressionTauQuotientAverage P X d a s ≤
          C * phiProgressionAverageShape P X d s

/-- Upper half of `lem:phi-progression-average` in the manuscript's sharper
divisor-expansion form
`1/φ(r) = (1/r)∑_{k|r} γ(k)`, after writing `r=k·t`.  This is the natural
target for the small/large `k` split: small `k` uses the ordinary squarefree
progression estimate with `M=sk`, and large `k` uses the tail of
`∑ γ(k)/k`. -/
def PhiProgressionGammaQuotientUpper (P : Params) : Prop :=
  ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ d a s : ℕ,
      0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
      Nat.Coprime a d →
      1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
        phiProgressionGammaQuotientAverage P X d a s ≤
          C * phiProgressionAverageShape P X d s

/-- Upper half of `lem:phi-progression-average` on the exact tensor modulus
range `d≤YU`.  This is the range needed by `thm:tensor-e`; it deliberately
does not collapse to the older polylogarithmic-modulus target. -/
def PhiProgressionGammaQuotientUpperYU (P : Params) : Prop :=
  ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ d a s : ℕ,
      0 < d → Squarefree d → Odd d →
      (d : ℝ) ≤ YScale P X * UScale X →
      Nat.Coprime a d →
      1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
        phiProgressionGammaQuotientAverage P X d a s ≤
          C * phiProgressionAverageShape P X d s

/-- Small/large-divisor form of the gamma quotient upper estimate.

The cutoff is left as an explicit function of `(X,d,s)`: the manuscript's
analytic proof is free to choose the most convenient split point, while this
definition records exactly what the two resulting estimates must prove. -/
def PhiProgressionGammaSplitUpper (P : Params) : Prop :=
  ∃ K : ℝ → ℕ → ℕ → ℕ, ∃ Csmall Clarge X₀ : ℝ,
    0 < Csmall ∧ 0 < Clarge ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          phiProgressionGammaSmallQuotientAverage P X d a s (K X d s) ≤
              Csmall * phiProgressionAverageShape P X d s ∧
            phiProgressionGammaLargeQuotientAverage P X d a s (K X d s) ≤
              Clarge * phiProgressionAverageShape P X d s

/-- Tail-majorant version of the small/large gamma split.  The small part is
still the exact gamma carrier; the large part is the checked
`2^ω(k)/k` majorant. -/
def PhiProgressionGammaSplitTailMajorantUpper (P : Params) : Prop :=
  ∃ K : ℝ → ℕ → ℕ → ℕ, ∃ Csmall Ctail X₀ : ℝ,
    0 < Csmall ∧ 0 < Ctail ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          phiProgressionGammaSmallQuotientAverage P X d a s (K X d s) ≤
              Csmall * phiProgressionAverageShape P X d s ∧
            phiProgressionGammaLargeTailMajorant P X d a s (K X d s) ≤
              Ctail * phiProgressionAverageShape P X d s

/-- Fiber-summed version of the tail-majorant gamma split.  This is the form
closest to the manuscript's proof: the small side is first partitioned by fixed
divisor `k`, and the large side is the checked `2^ω(k)/k` tail majorant. -/
def PhiProgressionGammaFiberTailMajorantUpper (P : Params) : Prop :=
  ∃ K : ℝ → ℕ → ℕ → ℕ, ∃ Csmall Ctail X₀ : ℝ,
    0 < Csmall ∧ 0 < Ctail ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          phiProgressionGammaSmallFiberSum P X d a s (K X d s) ≤
              Csmall * phiProgressionAverageShape P X d s ∧
            phiProgressionGammaLargeTailMajorant P X d a s (K X d s) ≤
              Ctail * phiProgressionAverageShape P X d s

/-- Weighted reciprocal-fiber version of the gamma split.  This is the
post-factorization form of the manuscript's small-divisor argument: the small
side is a weighted sum of quotient reciprocal fibers with coefficients
`γ(k)/k`, and the large side is the checked `2^ω(k)/k` tail majorant. -/
def PhiProgressionGammaWeightedRecipTailMajorantUpper (P : Params) : Prop :=
  ∃ K : ℝ → ℕ → ℕ → ℕ, ∃ Csmall Ctail X₀ : ℝ,
    0 < Csmall ∧ 0 < Ctail ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          phiProgressionGammaSmallWeightedRecipFiberSum P X d a s (K X d s) ≤
              Csmall * phiProgressionAverageShape P X d s ∧
            phiProgressionGammaLargeTailMajorant P X d a s (K X d s) ≤
              Ctail * phiProgressionAverageShape P X d s

/-- Weighted reciprocal-fiber gamma split on the tensor modulus range `d≤YU`. -/
def PhiProgressionGammaWeightedRecipTailMajorantUpperYU (P : Params) : Prop :=
  ∃ K : ℝ → ℕ → ℕ → ℕ, ∃ Csmall Ctail X₀ : ℝ,
    0 < Csmall ∧ 0 < Ctail ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d →
        (d : ℝ) ≤ YScale P X * UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          phiProgressionGammaSmallWeightedRecipFiberSum P X d a s (K X d s) ≤
              Csmall * phiProgressionAverageShape P X d s ∧
            phiProgressionGammaLargeTailMajorant P X d a s (K X d s) ≤
              Ctail * phiProgressionAverageShape P X d s

/-- `sqfRecip`-model version of the gamma split.  The small side has been
reduced all the way to ordinary squarefree reciprocal progression carriers
after fixing `k` and choosing inverse residue classes modulo `d`; the large
side remains the checked `2^ω(k)/k` tail majorant. -/
def PhiProgressionGammaSqfRecipModelTailMajorantUpper (P : Params) : Prop :=
  ∃ K : ℝ → ℕ → ℕ → ℕ, ∃ B : ℝ → ℕ → ℕ → ℕ → ℕ → ℕ,
  ∃ Csmall Ctail X₀ : ℝ,
    0 < Csmall ∧ 0 < Ctail ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          (∀ k ∈ Finset.Icc (1 : ℕ) (K X d s),
              k * B X d a s k ≡ 1 [MOD d]) ∧
          phiProgressionGammaSmallSqfRecipModelSum P X d a s (K X d s)
              (B X d a s) ≤
              Csmall * phiProgressionAverageShape P X d s ∧
            phiProgressionGammaLargeTailMajorant P X d a s (K X d s) ≤
              Ctail * phiProgressionAverageShape P X d s

/-- Canonical coprime-inverse `sqfRecip`-model version of the gamma split.
This is the same small-divisor reduction as
`PhiProgressionGammaSqfRecipModelTailMajorantUpper`, but it no longer asks the
analytic estimate to choose inverse residues for non-occurring divisors. -/
def PhiProgressionGammaSqfRecipCoprimeInverseTailMajorantUpper
    (P : Params) : Prop :=
  ∃ K : ℝ → ℕ → ℕ → ℕ, ∃ Csmall Ctail X₀ : ℝ,
    0 < Csmall ∧ 0 < Ctail ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          phiProgressionGammaSmallSqfRecipCoprimeInverseModelSum
              P X d a s (K X d s) ≤
              Csmall * phiProgressionAverageShape P X d s ∧
            phiProgressionGammaLargeTailMajorant P X d a s (K X d s) ≤
              Ctail * phiProgressionAverageShape P X d s

/-- Admissible canonical-inverse `sqfRecip`-model version of the gamma split.
Only divisors `k` coprime to both `d` and `s` remain in the small side; all
other fixed-divisor fibers are formally proved empty. -/
def PhiProgressionGammaSqfRecipAdmissibleInverseTailMajorantUpper
    (P : Params) : Prop :=
  ∃ K : ℝ → ℕ → ℕ → ℕ, ∃ Csmall Ctail X₀ : ℝ,
    0 < Csmall ∧ 0 < Ctail ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          phiProgressionGammaSmallSqfRecipAdmissibleInverseModelSum
              P X d a s (K X d s) ≤
              Csmall * phiProgressionAverageShape P X d s ∧
            phiProgressionGammaLargeTailMajorant P X d a s (K X d s) ≤
              Ctail * phiProgressionAverageShape P X d s

/-- Paper-shaped ordinary-density version of the admissible gamma split.

This is the exact small-`k` input used in the manuscript after writing `r=k t`:
each fixed-`k` squarefree reciprocal carrier is bounded with the
`φ(sk)/(sk)` local-density saving, and the finite coefficient sum
`∑_{k≤K} γ(k)/k` is bounded separately. -/
def PhiProgressionFixedKOrdinaryDensityUpperForCutoff
    (P : Params) (K : ℝ → ℕ → ℕ → ℕ) : Prop :=
  ∃ Csqf X₀ : ℝ, 0 < Csqf ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ d a s : ℕ,
      0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
      Nat.Coprime a d →
      1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
        ∀ k ∈ Finset.Icc (1 : ℕ) (K X d s),
          Nat.Coprime k d ∧ Nat.Coprime k s →
            Inputs.sqfRecip X (s * k) d (a * modInverseChoice d k)
              (phiProgressionU0 P s X / (k : ℝ))
              (phiProgressionU1 P s X / (k : ℝ)) ≤
              Csqf * (((1 : ℝ) / (d : ℝ)) *
                ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) *
                Real.log (phiProgressionU1 P s X /
                  phiProgressionU0 P s X))

/-- Manuscript-aligned bounded small-`k` ordinary-density target, with the cutoff
fixed to `K=⌊X^κ⌋₊`.

The inequalities `0<κ` and `η+κ<λ` record the usable range of the standard
ordinary progression estimate after the deterministic scale reduction
`U₀/k ≥ X^(λ-η-κ)`. -/
def PhiProgressionFixedKOrdinaryDensityUpperForPowerCutoff
    (P : Params) (κ : ℝ) : Prop :=
  0 < κ ∧ P.η + κ < P.lam ∧
    ∃ Csqf X₀ : ℝ, 0 < Csqf ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          ∀ k ∈ Finset.Icc (1 : ℕ) (phiProgressionPowerCutoff κ X d s),
            Nat.Coprime k d ∧ Nat.Coprime k s →
              Inputs.sqfRecip X (s * k) d (a * modInverseChoice d k)
                (phiProgressionU0 P s X / (k : ℝ))
                (phiProgressionU1 P s X / (k : ℝ)) ≤
                Csqf * (((1 : ℝ) / (d : ℝ)) *
                  ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) *
                  Real.log (phiProgressionU1 P s X /
                    phiProgressionU0 P s X))

/-- Manuscript-aligned bounded small-`k` ordinary-density target restricted to the
only fixed divisors that occur in the divisor expansion: squarefree `k`.

This matches the manuscript more closely than the older all-`k` interface,
because the exposed divisor `k` divides a squarefree outer variable `r`. -/
def PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff
    (P : Params) (κ : ℝ) : Prop :=
  0 < κ ∧ P.η + κ < P.lam ∧
    ∃ Csqf X₀ : ℝ, 0 < Csqf ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          ∀ k ∈ Finset.Icc (1 : ℕ) (phiProgressionPowerCutoff κ X d s),
            Squarefree k → Nat.Coprime k d ∧ Nat.Coprime k s →
              Inputs.sqfRecip X (s * k) d (a * modInverseChoice d k)
                (phiProgressionU0 P s X / (k : ℝ))
                (phiProgressionU1 P s X / (k : ℝ)) ≤
                Csqf * (((1 : ℝ) / (d : ℝ)) *
                  ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) *
                  Real.log (phiProgressionU1 P s X /
                    phiProgressionU0 P s X))

/-- Squarefree fixed-`k` ordinary-density target on the tensor modulus range
`d≤YU`.  This is the small-`k` upper estimate actually needed by the
exact-divisor tensor. -/
def PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoffYU
    (P : Params) (κ : ℝ) : Prop :=
  0 < κ ∧ P.η + κ < P.lam ∧
    ∃ Csqf X₀ : ℝ, 0 < Csqf ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d →
        (d : ℝ) ≤ YScale P X * UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          ∀ k ∈ Finset.Icc (1 : ℕ) (phiProgressionPowerCutoff κ X d s),
            Squarefree k → Nat.Coprime k d ∧ Nat.Coprime k s →
              Inputs.sqfRecip X (s * k) d (a * modInverseChoice d k)
                (phiProgressionU0 P s X / (k : ℝ))
                (phiProgressionU1 P s X / (k : ℝ)) ≤
                Csqf * (((1 : ℝ) / (d : ℝ)) *
                  ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) *
                  Real.log (phiProgressionU1 P s X /
                    phiProgressionU0 P s X))

/-- Manuscript-aligned non-progression lower half of `lem:ordinary-sqf`.

This is the displayed coprime squarefree reciprocal estimate with `D=1`, including
the manuscript's long-window hypothesis `U₁/U₀ ≥ X^c₀`.  It is intentionally
separate from the stronger reduced-progression lower target used by
`lem:phi-progression-average`. -/
def OrdinarySquarefreeCoprimeDensityLowerLong
    (a₀ b₀ c₀ C₀ : ℝ) : Prop :=
  ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ M : ℕ, Squarefree M →
      (M : ℝ) ≤ X ^ C₀ →
      ∀ U₀ U₁ : ℝ, X ^ a₀ ≤ U₀ → U₀ < U₁ → 1 ≤ U₁ → U₁ ≤ X ^ b₀ →
        X ^ c₀ ≤ U₁ / U₀ →
        c * (((Nat.totient M : ℝ) / (M : ℝ)) *
          Real.log (U₁ / U₀)) ≤
          Inputs.sqfRecip X M 1 0 U₀ U₁

/-- Generic cited-theorem-shaped ordinary squarefree progression lower bound
with an auxiliary coprimality modulus `M`.

This is the lower-half ordinary squarefree reciprocal content used before the
elementary comparison `1/r ≤ 1/φ(r)` in `lem:phi-progression-average`. -/
def OrdinarySquarefreeProgressionCoprimeDensityLower
    (a₀ b₀ C₀ : ℝ) : Prop :=
  ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ M D b : ℕ, 0 < D → Squarefree M → Squarefree D →
      Nat.Coprime M D → Nat.Coprime b D →
      (M : ℝ) ≤ X ^ C₀ → (D : ℝ) ≤ UScale X →
      ∀ U₀ U₁ : ℝ, X ^ a₀ ≤ U₀ → U₀ < U₁ → U₁ ≤ X ^ b₀ →
        c * (((1 : ℝ) / (D : ℝ)) *
          ((Nat.totient M : ℝ) / (M : ℝ)) * Real.log (U₁ / U₀)) ≤
          Inputs.sqfRecip X M D b U₀ U₁

/-- Manuscript-aligned long-window version of the ordinary squarefree progression
lower bound.

Unlike the older generic target above, this includes the manuscript hypothesis
`U₁/U₀ ≥ X^c₀` from `lem:ordinary-sqf`. -/
def OrdinarySquarefreeProgressionCoprimeDensityLowerLong
    (a₀ b₀ c₀ C₀ : ℝ) : Prop :=
  ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ M D b : ℕ, 0 < D → Squarefree M → Squarefree D →
      Nat.Coprime M D → Nat.Coprime b D →
      (M : ℝ) ≤ X ^ C₀ → (D : ℝ) ≤ UScale X →
      ∀ U₀ U₁ : ℝ, X ^ a₀ ≤ U₀ → U₀ < U₁ → 1 ≤ U₁ → U₁ ≤ X ^ b₀ →
        X ^ c₀ ≤ U₁ / U₀ →
        c * (((1 : ℝ) / (D : ℝ)) *
          ((Nat.totient M : ℝ) / (M : ℝ)) * Real.log (U₁ / U₀)) ≤
          Inputs.sqfRecip X M D b U₀ U₁

/-- The progression long-window lower estimate specializes to the
non-progression `D=1` lower estimate used by the exact-divisor `M₁` mass. -/
theorem OrdinarySquarefreeCoprimeDensityLowerLong_of_progression_long
    {a₀ b₀ c₀ C₀ : ℝ}
    (h :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong a₀ b₀ c₀ C₀) :
    OrdinarySquarefreeCoprimeDensityLowerLong a₀ b₀ c₀ C₀ := by
  rcases h with ⟨c, X₀, hc, hbound⟩
  refine ⟨c, max X₀ (Real.exp 1), hc, ?_⟩
  intro X hX M hM hMscale U₀ U₁ hU₀ hU₀₁ hU₁one hU₁ hratio
  have hXbase : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hXexp
  have hlogX_ge_one : (1 : ℝ) ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hXexp
  have hlogX_nonneg : 0 ≤ Real.log X := le_trans zero_le_one hlogX_ge_one
  have hDpos : 0 < (1 : ℕ) := by norm_num
  have hDsqf : Squarefree (1 : ℕ) := by simp
  have hMD : Nat.Coprime M (1 : ℕ) := Nat.coprime_one_right M
  have hb : Nat.Coprime (0 : ℕ) (1 : ℕ) := Nat.coprime_one_right 0
  have hDscale : ((1 : ℕ) : ℝ) ≤ UScale X := by
    unfold UScale
    have hpow2 : (1 : ℝ) ≤ (Real.log X) ^ 2 := by nlinarith
    have hpow4 : (1 : ℝ) ≤ (Real.log X) ^ 4 := by
      nlinarith [mul_le_mul hpow2 hpow2 zero_le_one (by nlinarith : 0 ≤ (Real.log X) ^ 2)]
    have hpow8 : (1 : ℝ) ≤ (Real.log X) ^ 8 := by
      nlinarith [mul_le_mul hpow4 hpow4 zero_le_one (by nlinarith : 0 ≤ (Real.log X) ^ 4)]
    simpa [pow_succ] using hpow8
  simpa using
    hbound X hXbase M 1 0 hDpos hM hDsqf hMD hb hMscale hDscale
      U₀ U₁ hU₀ hU₀₁ hU₁one hU₁ hratio

/-- The wide ordinary squarefree progression lower estimate also supplies the
small-`k` power-cutoff range.

This is the lower-bound analogue of
`OrdinarySquarefreeProgressionCoprimeDensityUpper_small_of_wide`: from
`η+κ < λ < θ`, the conductor bound `M≤X^(η+κ)` is stronger than `M≤X^θ`,
and the lower endpoint bound `U₀≥X^(λ-η-κ)` is stronger than
`U₀≥X^(λ-θ)`. -/
theorem OrdinarySquarefreeProgressionCoprimeDensityLower_small_of_wide
    {P : Params} {κ : ℝ}
    (hκ_range : P.η + κ < P.lam)
    (hwide :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.θ) P.θ P.θ) :
    OrdinarySquarefreeProgressionCoprimeDensityLower
      (P.lam - P.η - κ) P.θ (P.η + κ) := by
  rcases hwide with ⟨c, Xbase, hc, hbound⟩
  refine ⟨c, max Xbase (Real.exp 1), hc, ?_⟩
  intro X hX M D b hD_pos hM_sqf hD_sqf hMD_coprime hb_coprime
    hM_scale hD_scale U₀ U₁ hU0 hU01 hU1
  have hXbase : Xbase ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXexp
  have hlam_lt_theta : P.lam < P.θ :=
    lt_of_le_of_lt (le_add_of_nonneg_right P.η_pos.le) P.lam_add_η_lt_θ
  have hetaκ_le_theta : P.η + κ ≤ P.θ :=
    le_of_lt (hκ_range.trans hlam_lt_theta)
  have hM_scale_wide : (M : ℝ) ≤ X ^ P.θ :=
    hM_scale.trans
      (Real.rpow_le_rpow_of_exponent_le hXone hetaκ_le_theta)
  have hlower_exp : P.lam - P.θ ≤ P.lam - P.η - κ := by
    linarith [hetaκ_le_theta]
  have hU0_wide : X ^ (P.lam - P.θ) ≤ U₀ :=
    (Real.rpow_le_rpow_of_exponent_le hXone hlower_exp).trans hU0
  exact
    hbound X hXbase M D b hD_pos hM_sqf hD_sqf hMD_coprime
      hb_coprime hM_scale_wide hD_scale U₀ U₁ hU0_wide hU01 hU1

/-- Long-window version of
`OrdinarySquarefreeProgressionCoprimeDensityLower_small_of_wide`.

The exponent monotonicity is identical to the no-long-window bridge; the
additional ratio hypothesis is preserved unchanged. -/
theorem OrdinarySquarefreeProgressionCoprimeDensityLowerLong_small_of_wide
    {P : Params} {κ c₀ : ℝ}
    (hκ_range : P.η + κ < P.lam)
    (hwide :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.θ) P.θ c₀ P.θ) :
    OrdinarySquarefreeProgressionCoprimeDensityLowerLong
      (P.lam - P.η - κ) P.θ c₀ (P.η + κ) := by
  rcases hwide with ⟨c, Xbase, hc, hbound⟩
  refine ⟨c, max Xbase (Real.exp 1), hc, ?_⟩
  intro X hX M D b hD_pos hM_sqf hD_sqf hMD_coprime hb_coprime
    hM_scale hD_scale U₀ U₁ hU0 hU01 hU1 hratio
  have hXbase : Xbase ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXexp
  have hlam_lt_theta : P.lam < P.θ :=
    lt_of_le_of_lt (le_add_of_nonneg_right P.η_pos.le) P.lam_add_η_lt_θ
  have hetaκ_le_theta : P.η + κ ≤ P.θ :=
    le_of_lt (hκ_range.trans hlam_lt_theta)
  have hM_scale_wide : (M : ℝ) ≤ X ^ P.θ :=
    hM_scale.trans
      (Real.rpow_le_rpow_of_exponent_le hXone hetaκ_le_theta)
  have hlower_exp : P.lam - P.θ ≤ P.lam - P.η - κ := by
    linarith [hetaκ_le_theta]
  have hU0_wide : X ^ (P.lam - P.θ) ≤ U₀ :=
    (Real.rpow_le_rpow_of_exponent_le hXone hlower_exp).trans hU0
  exact
    hbound X hXbase M D b hD_pos hM_sqf hD_sqf hMD_coprime
      hb_coprime hM_scale_wide hD_scale U₀ U₁ hU0_wide hU01 hU1 hratio

/-- The wide ordinary squarefree progression lower estimate specializes to the
bare `M₁` conductor scale `M≤X^η`. -/
theorem OrdinarySquarefreeProgressionCoprimeDensityLower_eta_of_wide
    {P : Params}
    (hwide :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.θ) P.θ P.θ) :
    OrdinarySquarefreeProgressionCoprimeDensityLower
      (P.lam - P.η) P.θ P.η := by
  have heta_range : P.η + (0 : ℝ) < P.lam := by
    linarith [P.η_add_σ_lt_lam, P.σ_pos]
  simpa using
    (OrdinarySquarefreeProgressionCoprimeDensityLower_small_of_wide
      (P := P) (κ := 0) heta_range hwide)

/-- Long-window specialization of the wide ordinary squarefree progression
lower estimate to the bare `M₁` conductor scale `M≤X^η`. -/
theorem OrdinarySquarefreeProgressionCoprimeDensityLowerLong_eta_of_wide
    {P : Params} {c₀ : ℝ}
    (hwide :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.θ) P.θ c₀ P.θ) :
    OrdinarySquarefreeProgressionCoprimeDensityLowerLong
      (P.lam - P.η) P.θ c₀ P.η := by
  have heta_range : P.η + (0 : ℝ) < P.lam := by
    linarith [P.η_add_σ_lt_lam, P.σ_pos]
  simpa using
    (OrdinarySquarefreeProgressionCoprimeDensityLowerLong_small_of_wide
      (P := P) (κ := 0) (c₀ := c₀) heta_range hwide)

/-- The generic ordinary squarefree reciprocal lower bound implies the dyadic
count lower target used by the checked phi-progression lower bridge.

The only extra work is deterministic: specialize the ordinary estimate to
`(T,2T]`, use `log(2T/T)=log 2`, and compare the reciprocal sum to
`card/T`. -/
theorem PhiProgressionDyadicSqfCountLower_of_ordinary
    {P : Params}
    (hordinary :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.η) P.θ P.η) :
    PhiProgressionDyadicSqfCountLower P := by
  rcases hordinary with ⟨c, Xbase, hc, hbound⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨c * Real.log 2, max Xbase (Real.exp 1), mul_pos hc hlog2, ?_⟩
  intro X hX d a s hd_pos hd_sqf _hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS k hT hright
  let T := phiProgressionDyadicAnchor P X s k
  have hXbase : Xbase ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXexp
  have hXgtone : (1 : ℝ) < X :=
    lt_of_lt_of_le (by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)) hXexp
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hU0_pos : 0 < phiProgressionU0 P s X :=
    phiProgressionU0_pos P hXpos hs_pos
  have hU0_scale :
      X ^ (P.lam - P.η) ≤ phiProgressionU0 P s X :=
    phiProgressionU0_ge_rpow_lam_sub_eta P hXone hs_one hsS
  have hU0_le_T : phiProgressionU0 P s X ≤ T := by
    rw [← phiProgressionDyadicAnchor_zero P X s]
    exact phiProgressionDyadicAnchor_mono hU0_pos (Nat.zero_le k)
  have hT_scale : X ^ (P.lam - P.η) ≤ T := hU0_scale.trans hU0_le_T
  have hT_one : (1 : ℝ) ≤ T :=
    (one_le_phiProgressionU0 P hXone hs_one hsS).trans hU0_le_T
  have hU1_scale :
      phiProgressionU1 P s X ≤ X ^ P.θ :=
    phiProgressionU1_le_rpow_theta P hXpos hs_one
  have h2T_scale : 2 * T ≤ X ^ P.θ := hright.trans hU1_scale
  have hT_lt_2T : T < 2 * T := by nlinarith [hT]
  have hratio : (2 * T) / T = 2 := by
    field_simp [ne_of_gt hT]
  have hrecip_lower :
      c * (((1 : ℝ) / (d : ℝ)) *
          ((Nat.totient s : ℝ) / (s : ℝ)) *
          Real.log ((2 * T) / T)) ≤
        Inputs.sqfRecip X s d a T (2 * T) := by
    exact hbound X hXbase s d a hd_pos hs_sqf hd_sqf hs_coprime
      ha_coprime hsS hdU T (2 * T) hT_scale hT_lt_2T h2T_scale
  have hrecip_count :
      Inputs.sqfRecip X s d a T (2 * T) ≤
        ((phiProgressionDyadicSqfSupport P X d a s k).card : ℝ) / T :=
    phiProgressionDyadicSqfRecip_le_count_div_lower
      (P := P) (X := X) (d := d) (a := a) (s := s) (k := k) hT
  have hmain :
      c * (((1 : ℝ) / (d : ℝ)) *
          ((Nat.totient s : ℝ) / (s : ℝ)) *
          Real.log ((2 * T) / T)) ≤
        ((phiProgressionDyadicSqfSupport P X d a s k).card : ℝ) / T :=
    hrecip_lower.trans hrecip_count
  have hmul := mul_le_mul_of_nonneg_right hmain hT.le
  calc
    (c * Real.log 2) * phiProgressionDyadicSqfCountShape P X d s k
        = (c * (((1 : ℝ) / (d : ℝ)) *
          ((Nat.totient s : ℝ) / (s : ℝ)) *
          Real.log ((2 * T) / T))) * T := by
          rw [hratio]
          unfold phiProgressionDyadicSqfCountShape
          dsimp [T]
          ring
    _ ≤ (((phiProgressionDyadicSqfSupport P X d a s k).card : ℝ) / T) * T :=
        hmul
    _ = ((phiProgressionDyadicSqfSupport P X d a s k).card : ℝ) := by
        field_simp [ne_of_gt hT]

/-- The generic ordinary squarefree lower bound supplies the exact lower
squarefree reciprocal target for `lem:phi-progression-average`.

The proof is only deterministic phi-scale bookkeeping: the conductor is
`M=s`, it is squarefree and coprime to `d`, it has size `≤X^η`, and the moving
interval lies between `X^(λ-η)` and `X^θ`. -/
theorem PhiProgressionSqfRecipLower_of_ordinary
    {P : Params}
    (hordinary :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.η) P.θ P.η) :
    PhiProgressionSqfRecipLower P := by
  rcases hordinary with ⟨c, Xbase, hc, hbound⟩
  refine ⟨c, max Xbase (Real.exp 1), hc, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  have hXbase : Xbase ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXexp
  have hXgtone : (1 : ℝ) < X :=
    lt_of_lt_of_le (by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)) hXexp
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hM_scale : (s : ℝ) ≤ X ^ P.η := by
    simpa [SScale] using hsS
  have hU0_scale :
      X ^ (P.lam - P.η) ≤ phiProgressionU0 P s X :=
    phiProgressionU0_ge_rpow_lam_sub_eta P hXone hs_one hsS
  have hU1_scale :
      phiProgressionU1 P s X ≤ X ^ P.θ :=
    phiProgressionU1_le_rpow_theta P hXpos hs_one
  have hU01 :
      phiProgressionU0 P s X < phiProgressionU1 P s X :=
    phiProgressionU0_lt_U1_of_s_le_SScale P hXgtone hs_one hsS
  have hU0_one : (1 : ℝ) ≤ phiProgressionU0 P s X :=
    one_le_phiProgressionU0 P hXone hs_one hsS
  exact
    hbound X hXbase s d a hd_pos hs_sqf hd_sqf hs_coprime ha_coprime
      hM_scale hdU
      (phiProgressionU0 P s X) (phiProgressionU1 P s X)
      hU0_scale hU01 hU1_scale

/-- Manuscript-aligned long-window ordinary squarefree lower bound supplies the
exact lower squarefree reciprocal target for `lem:phi-progression-average`.

The additional manuscript hypothesis `U₁/U₀ ≥ X^c₀` is discharged by the checked
phi-window ratio estimate with `c₀ = θ-λ-η`. -/
theorem PhiProgressionSqfRecipLower_of_ordinary_long
    {P : Params}
    (hordinary :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η) :
    PhiProgressionSqfRecipLower P := by
  rcases hordinary with ⟨c, Xbase, hc, hbound⟩
  refine ⟨c, max Xbase (Real.exp 1), hc, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  have hXbase : Xbase ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXexp
  have hXgtone : (1 : ℝ) < X :=
    lt_of_lt_of_le (by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)) hXexp
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hM_scale : (s : ℝ) ≤ X ^ P.η := by
    simpa [SScale] using hsS
  have hU0_scale :
      X ^ (P.lam - P.η) ≤ phiProgressionU0 P s X :=
    phiProgressionU0_ge_rpow_lam_sub_eta P hXone hs_one hsS
  have hU1_scale :
      phiProgressionU1 P s X ≤ X ^ P.θ :=
    phiProgressionU1_le_rpow_theta P hXpos hs_one
  have hU01 :
      phiProgressionU0 P s X < phiProgressionU1 P s X :=
    phiProgressionU0_lt_U1_of_s_le_SScale P hXgtone hs_one hsS
  have hU0_one : (1 : ℝ) ≤ phiProgressionU0 P s X :=
    one_le_phiProgressionU0 P hXone hs_one hsS
  have hratio :
      X ^ (P.θ - P.lam - P.η) ≤
        phiProgressionU1 P s X / phiProgressionU0 P s X :=
    phiProgression_ratio_ge_rpow_theta_sub_lam_sub_eta P hXone hs_one hsS
  exact
    hbound X hXbase s d a hd_pos hs_sqf hd_sqf hs_coprime ha_coprime
      hM_scale hdU
      (phiProgressionU0 P s X) (phiProgressionU1 P s X)
      hU0_scale hU01 (hU0_one.trans hU01.le) hU1_scale hratio

/-- Generic cited-theorem-shaped ordinary squarefree progression upper bound
with an auxiliary coprimality modulus `M`.

This is the paper's `ordinary_progression_coprime_upper` content stripped of
the phi-specific moving scales: squarefree terms in a reduced class modulo
`D`, coprime to a squarefree auxiliary modulus `M`, have the local-density
saving `φ(M)/M`. -/
def OrdinarySquarefreeProgressionCoprimeDensityUpper
    (a₀ b₀ C₀ : ℝ) : Prop :=
  ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ M D b : ℕ, 0 < D → Squarefree M → Squarefree D →
      Nat.Coprime M D → Nat.Coprime b D →
      (M : ℝ) ≤ X ^ C₀ → (D : ℝ) ≤ UScale X →
      ∀ U₀ U₁ : ℝ, X ^ a₀ ≤ U₀ → U₀ < U₁ → U₁ ≤ X ^ b₀ →
        Inputs.sqfRecip X M D b U₀ U₁ ≤
          C * (((1 : ℝ) / (D : ℝ)) *
            ((Nat.totient M : ℝ) / (M : ℝ)) * Real.log (U₁ / U₀))

/-- Manuscript-aligned long-window version of the ordinary squarefree progression
upper bound, including the manuscript hypothesis `U₁/U₀ ≥ X^c₀`. -/
def OrdinarySquarefreeProgressionCoprimeDensityUpperLong
    (a₀ b₀ c₀ C₀ : ℝ) : Prop :=
  ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ M D b : ℕ, 0 < D → Squarefree M → Squarefree D →
      Nat.Coprime M D → Nat.Coprime b D →
      (M : ℝ) ≤ X ^ C₀ → (D : ℝ) ≤ UScale X →
      ∀ U₀ U₁ : ℝ, X ^ a₀ ≤ U₀ → U₀ < U₁ → 1 ≤ U₁ → U₁ ≤ X ^ b₀ →
        X ^ c₀ ≤ U₁ / U₀ →
        Inputs.sqfRecip X M D b U₀ U₁ ≤
          C * (((1 : ℝ) / (D : ℝ)) *
            ((Nat.totient M : ℝ) / (M : ℝ)) * Real.log (U₁ / U₀))

/-- Ordinary squarefree progression upper bound with the tensor modulus range
`D≤YU`.  This is the paper-facing cited input needed for the reciprocal-`φ`
half of `thm:tensor-e`; the older target only allowed `D≤U`. -/
def OrdinarySquarefreeProgressionCoprimeDensityUpperYU
    (P : Params) (a₀ b₀ C₀ : ℝ) : Prop :=
  ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ M D b : ℕ, 0 < D → Squarefree M → Squarefree D →
      Nat.Coprime M D → Nat.Coprime b D →
      (M : ℝ) ≤ X ^ C₀ → (D : ℝ) ≤ YScale P X * UScale X →
      ∀ U₀ U₁ : ℝ, X ^ a₀ ≤ U₀ → U₀ < U₁ → 1 ≤ U₁ → U₁ ≤ X ^ b₀ →
        X ^ (P.θ - P.lam - P.η) ≤ U₁ / U₀ →
        Inputs.sqfRecip X M D b U₀ U₁ ≤
          C * (((1 : ℝ) / (D : ℝ)) *
            ((Nat.totient M : ℝ) / (M : ℝ)) * Real.log (U₁ / U₀))

/-- Local wrapper for the cited long-window ordinary squarefree progression
lower theorem. -/
theorem OrdinarySquarefreeProgressionCoprimeDensityLowerLong_of_standard
    (a₀ b₀ c₀ C₀ : ℝ) (ha₀ : 0 < a₀) (hc₀ : 0 < c₀) :
    OrdinarySquarefreeProgressionCoprimeDensityLowerLong a₀ b₀ c₀ C₀ := by
  simpa [OrdinarySquarefreeProgressionCoprimeDensityLowerLong,
    Inputs.OrdinarySquarefreeProgressionCoprimeDensityLowerLong] using
    Inputs.ordinary_squarefree_progression_coprime_density_lower_long a₀ b₀ c₀ C₀ ha₀ hc₀

/-- Local wrapper for the cited long-window ordinary squarefree progression
upper theorem. -/
theorem OrdinarySquarefreeProgressionCoprimeDensityUpperLong_of_standard
    (a₀ b₀ c₀ C₀ : ℝ) (ha₀ : 0 < a₀) (hc₀ : 0 < c₀) :
    OrdinarySquarefreeProgressionCoprimeDensityUpperLong a₀ b₀ c₀ C₀ := by
  simpa [OrdinarySquarefreeProgressionCoprimeDensityUpperLong,
    Inputs.OrdinarySquarefreeProgressionCoprimeDensityUpperLong] using
    Inputs.ordinary_squarefree_progression_coprime_density_upper_long
      a₀ b₀ c₀ C₀ ha₀ hc₀

/-- Local wrapper for the cited tensor-range ordinary squarefree progression
upper theorem. -/
theorem OrdinarySquarefreeProgressionCoprimeDensityUpperYU_of_standard
    (P : Params) (a₀ b₀ C₀ : ℝ)
    (ha₀ : 0 < a₀) (hmod : P.σ < a₀) :
    OrdinarySquarefreeProgressionCoprimeDensityUpperYU P a₀ b₀ C₀ := by
  simpa [OrdinarySquarefreeProgressionCoprimeDensityUpperYU,
    Inputs.OrdinarySquarefreeProgressionCoprimeDensityUpperYU] using
    Inputs.ordinary_squarefree_progression_coprime_density_upper_yu
      P a₀ b₀ C₀ ha₀ hmod

/-- Restrict a tensor-range squarefree progression estimate to the smaller
polylogarithmic modulus range. -/
theorem OrdinarySquarefreeProgressionCoprimeDensityUpperLong_of_YU
    {P : Params} {a₀ b₀ C₀ : ℝ}
    (hYU : OrdinarySquarefreeProgressionCoprimeDensityUpperYU P a₀ b₀ C₀) :
    OrdinarySquarefreeProgressionCoprimeDensityUpperLong
      a₀ b₀ (P.θ - P.lam - P.η) C₀ := by
  rcases hYU with ⟨C, Xbase, hC, hbound⟩
  refine ⟨C, max Xbase (Real.exp 1), hC, ?_⟩
  intro X hX M D b hD_pos hM_sqf hD_sqf hMD hb
    hM_scale hD_scale U₀ U₁ hU₀ hU₀₁ hU₁_one hU₁ hratio
  have hXbase : Xbase ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXexp
  have hYone : (1 : ℝ) ≤ YScale P X := by
    unfold YScale
    exact Real.one_le_rpow hXone P.σ_pos.le
  have hU_nonneg : 0 ≤ UScale X := by
    unfold UScale
    positivity
  have hDwide : (D : ℝ) ≤ YScale P X * UScale X :=
    hD_scale.trans (by
      calc
        UScale X = 1 * UScale X := by ring
        _ ≤ YScale P X * UScale X :=
          mul_le_mul_of_nonneg_right hYone hU_nonneg)
  exact hbound X hXbase M D b hD_pos hM_sqf hD_sqf hMD hb
    hM_scale hDwide U₀ U₁ hU₀ hU₀₁ hU₁_one hU₁ hratio

/-- The specialized reciprocal squarefree lower carrier obtained directly from
the cited ordinary-squarefree progression theorem. -/
theorem PhiProgressionSqfRecipLower_of_standard_ordinarySquarefree
    (P : Params) :
    PhiProgressionSqfRecipLower P :=
  PhiProgressionSqfRecipLower_of_ordinary_long
    (OrdinarySquarefreeProgressionCoprimeDensityLowerLong_of_standard
      (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η
      (by linarith [P.η_add_σ_lt_lam, P.σ_pos])
      (by linarith [P.lam_add_η_lt_θ]))

/-- Deterministic CRT/totient proof of the paper-shaped ordinary-squarefree
upper estimate in ranges where the lower endpoint dominates the CRT modulus.

The hypothesis `C₀ < a₀` is the exact exponent margin needed to absorb the
polylogarithmic `D≤UScale X` factor into the lower endpoint.  This theorem is
therefore an unconditional replacement for the ordinary-squarefree upper input
only in such margin ranges; without that margin the endpoint term exposed by the
finite CRT/totient argument remains visible. -/
theorem OrdinarySquarefreeProgressionCoprimeDensityUpperLong_of_crt_endpoint_margin
    {a₀ b₀ c₀ C₀ : ℝ}
    (hmargin : C₀ < a₀) (hc₀ : 0 < c₀) :
    OrdinarySquarefreeProgressionCoprimeDensityUpperLong a₀ b₀ c₀ C₀ := by
  rcases Inputs.eventually_UScale_le_rpow (sub_pos.mpr hmargin) with
    ⟨Xscale, hscale⟩
  refine ⟨2, max (max Xscale (Real.exp 1)) (Real.exp (1 / c₀)), by norm_num, ?_⟩
  intro X hX M D b hD hM hDsqf hMD hb hMscale hDscale U₀ U₁ hU₀ hU₀₁ _hU₁one hU₁ hratio
  have hXscale : Xscale ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXexp1 : Real.exp 1 ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXexp_c : Real.exp (1 / c₀) ≤ X :=
    le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hXexp1
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXexp1
  have hlogX_nonneg : 0 ≤ Real.log X := by
    rw [Real.log_nonneg_iff hXpos]
    exact hXone
  have hU₀pos : 0 < U₀ :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos a₀) hU₀
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM.ne_zero
  have hUscale_nonneg : 0 ≤ UScale X := by
    unfold UScale
    exact pow_nonneg hlogX_nonneg 8
  have hD_nonneg : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hprod_le_scale : ((M * D : ℕ) : ℝ) ≤ X ^ C₀ * UScale X := by
    rw [Nat.cast_mul]
    exact mul_le_mul hMscale hDscale hD_nonneg
      (Real.rpow_pos_of_pos hXpos C₀).le
  have hUscale_le : UScale X ≤ X ^ (a₀ - C₀) := hscale X hXscale
  have hprod_le_power : ((M * D : ℕ) : ℝ) ≤ X ^ a₀ := by
    calc
      ((M * D : ℕ) : ℝ) ≤ X ^ C₀ * UScale X := hprod_le_scale
      _ ≤ X ^ C₀ * X ^ (a₀ - C₀) :=
          mul_le_mul_of_nonneg_left hUscale_le
            (Real.rpow_pos_of_pos hXpos C₀).le
      _ = X ^ a₀ := by
          rw [← Real.rpow_add hXpos]
          ring_nf
  have hmod_le : ((M * D : ℕ) : ℝ) ≤ U₀ := hprod_le_power.trans hU₀
  have hlogX_ge : 1 / c₀ ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hXexp_c
  have hlogX_c_ge_one : (1 : ℝ) ≤ c₀ * Real.log X := by
    have hmul := mul_le_mul_of_nonneg_left hlogX_ge hc₀.le
    have hc₀_ne : c₀ ≠ 0 := ne_of_gt hc₀
    field_simp [hc₀_ne] at hmul
    simpa [mul_comm] using hmul
  have hpow_pos : 0 < X ^ c₀ := Real.rpow_pos_of_pos hXpos c₀
  have hratio_pos : 0 < U₁ / U₀ := div_pos (lt_trans hU₀pos hU₀₁) hU₀pos
  have hlog_pow : Real.log (X ^ c₀) = c₀ * Real.log X := by
    rw [Real.log_rpow hXpos]
  have hlog_mono : Real.log (X ^ c₀) ≤ Real.log (U₁ / U₀) :=
    Real.log_le_log hpow_pos hratio
  have hlog_one : (1 : ℝ) ≤ Real.log (U₁ / U₀) := by
    exact hlogX_c_ge_one.trans (by simpa [hlog_pow] using hlog_mono)
  exact
    Inputs.sqfRecip_le_totient_crt_density_of_endpoint
      X M D b hMpos hD hMD hU₀pos hU₀₁ hmod_le hlog_one

/-- The wide ordinary squarefree progression upper estimate also supplies the
small-`k` power-cutoff range.

The only work is monotonicity in the two power exponents: from
`η+κ < λ < θ`, the conductor bound `M≤X^(η+κ)` is stronger than `M≤X^θ`,
and the lower endpoint bound `U₀≥X^(λ-η-κ)` is stronger than
`U₀≥X^(λ-θ)`. -/
theorem OrdinarySquarefreeProgressionCoprimeDensityUpper_small_of_wide
    {P : Params} {κ : ℝ}
    (hκ_range : P.η + κ < P.lam)
    (hwide :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    OrdinarySquarefreeProgressionCoprimeDensityUpper
      (P.lam - P.η - κ) P.θ (P.η + κ) := by
  rcases hwide with ⟨C, Xbase, hC, hbound⟩
  refine ⟨C, max Xbase (Real.exp 1), hC, ?_⟩
  intro X hX M D b hD_pos hM_sqf hD_sqf hMD_coprime hb_coprime
    hM_scale hD_scale U₀ U₁ hU0 hU01 hU1
  have hXbase : Xbase ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXexp
  have hlam_lt_theta : P.lam < P.θ :=
    lt_of_le_of_lt (le_add_of_nonneg_right P.η_pos.le) P.lam_add_η_lt_θ
  have hetaκ_le_theta : P.η + κ ≤ P.θ :=
    le_of_lt (hκ_range.trans hlam_lt_theta)
  have hM_scale_wide : (M : ℝ) ≤ X ^ P.θ :=
    hM_scale.trans
      (Real.rpow_le_rpow_of_exponent_le hXone hetaκ_le_theta)
  have hlower_exp : P.lam - P.θ ≤ P.lam - P.η - κ := by
    linarith [hetaκ_le_theta]
  have hU0_wide : X ^ (P.lam - P.θ) ≤ U₀ :=
    (Real.rpow_le_rpow_of_exponent_le hXone hlower_exp).trans hU0
  exact
    hbound X hXbase M D b hD_pos hM_sqf hD_sqf hMD_coprime
      hb_coprime hM_scale_wide hD_scale U₀ U₁ hU0_wide hU01 hU1

/-- Long-window version of
`OrdinarySquarefreeProgressionCoprimeDensityUpper_small_of_wide`.

The exponent monotonicity is identical to the no-long-window bridge; the
additional ratio hypothesis is preserved unchanged. -/
theorem OrdinarySquarefreeProgressionCoprimeDensityUpperLong_small_of_wide
    {P : Params} {κ c₀ : ℝ}
    (hκ_range : P.η + κ < P.lam)
    (hwide :
      OrdinarySquarefreeProgressionCoprimeDensityUpperLong
        (P.lam - P.θ) P.θ c₀ P.θ) :
    OrdinarySquarefreeProgressionCoprimeDensityUpperLong
      (P.lam - P.η - κ) P.θ c₀ (P.η + κ) := by
  rcases hwide with ⟨C, Xbase, hC, hbound⟩
  refine ⟨C, max Xbase (Real.exp 1), hC, ?_⟩
  intro X hX M D b hD_pos hM_sqf hD_sqf hMD_coprime hb_coprime
    hM_scale hD_scale U₀ U₁ hU0 hU01 hU1 hratio
  have hXbase : Xbase ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXexp
  have hlam_lt_theta : P.lam < P.θ :=
    lt_of_le_of_lt (le_add_of_nonneg_right P.η_pos.le) P.lam_add_η_lt_θ
  have hetaκ_le_theta : P.η + κ ≤ P.θ :=
    le_of_lt (hκ_range.trans hlam_lt_theta)
  have hM_scale_wide : (M : ℝ) ≤ X ^ P.θ :=
    hM_scale.trans
      (Real.rpow_le_rpow_of_exponent_le hXone hetaκ_le_theta)
  have hlower_exp : P.lam - P.θ ≤ P.lam - P.η - κ := by
    linarith [hetaκ_le_theta]
  have hU0_wide : X ^ (P.lam - P.θ) ≤ U₀ :=
    (Real.rpow_le_rpow_of_exponent_le hXone hlower_exp).trans hU0
  exact
    hbound X hXbase M D b hD_pos hM_sqf hD_sqf hMD_coprime
      hb_coprime hM_scale_wide hD_scale U₀ U₁ hU0_wide hU01 hU1 hratio

/-- Tensor-range version of
`OrdinarySquarefreeProgressionCoprimeDensityUpper_small_of_wide`. -/
theorem OrdinarySquarefreeProgressionCoprimeDensityUpperYU_small_of_wide
    {P : Params} {κ : ℝ}
    (hκ_range : P.η + κ < P.lam)
    (hwide :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ) :
    OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
      (P.lam - P.η - κ) P.θ (P.η + κ) := by
  rcases hwide with ⟨C, Xbase, hC, hbound⟩
  refine ⟨C, max Xbase (Real.exp 1), hC, ?_⟩
  intro X hX M D b hD_pos hM_sqf hD_sqf hMD_coprime hb_coprime
    hM_scale hD_scale U₀ U₁ hU0 hU01 hU1
  have hXbase : Xbase ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXexp
  have hlam_lt_theta : P.lam < P.θ :=
    lt_of_le_of_lt (le_add_of_nonneg_right P.η_pos.le) P.lam_add_η_lt_θ
  have hetaκ_le_theta : P.η + κ ≤ P.θ :=
    le_of_lt (hκ_range.trans hlam_lt_theta)
  have hM_scale_wide : (M : ℝ) ≤ X ^ P.θ :=
    hM_scale.trans
      (Real.rpow_le_rpow_of_exponent_le hXone hetaκ_le_theta)
  have hlower_exp : P.lam - P.θ ≤ P.lam - P.η - κ := by
    linarith [hetaκ_le_theta]
  have hU0_wide : X ^ (P.lam - P.θ) ≤ U₀ :=
    (Real.rpow_le_rpow_of_exponent_le hXone hlower_exp).trans hU0
  exact
    hbound X hXbase M D b hD_pos hM_sqf hD_sqf hMD_coprime
      hb_coprime hM_scale_wide hD_scale U₀ U₁ hU0_wide hU01 hU1

/-- The wide ordinary squarefree progression upper estimate specializes to the
bare `M₁` conductor scale `M≤X^η`. -/
theorem OrdinarySquarefreeProgressionCoprimeDensityUpper_eta_of_wide
    {P : Params}
    (hwide :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    OrdinarySquarefreeProgressionCoprimeDensityUpper
      (P.lam - P.η) P.θ P.η := by
  have heta_range : P.η + (0 : ℝ) < P.lam := by
    linarith [P.η_add_σ_lt_lam, P.σ_pos]
  simpa using
    (OrdinarySquarefreeProgressionCoprimeDensityUpper_small_of_wide
      (P := P) (κ := 0) heta_range hwide)

/-- Long-window version of
`OrdinarySquarefreeProgressionCoprimeDensityUpper_eta_of_wide`.  The extra
ratio hypothesis is preserved through the same exponent-monotonicity bridge. -/
theorem OrdinarySquarefreeProgressionCoprimeDensityUpperLong_eta_of_wide
    {P : Params} {c₀ : ℝ}
    (hwide :
      OrdinarySquarefreeProgressionCoprimeDensityUpperLong
        (P.lam - P.θ) P.θ c₀ P.θ) :
    OrdinarySquarefreeProgressionCoprimeDensityUpperLong
      (P.lam - P.η) P.θ c₀ P.η := by
  have heta_range : P.η + (0 : ℝ) < P.lam := by
    linarith [P.η_add_σ_lt_lam, P.σ_pos]
  simpa using
    (OrdinarySquarefreeProgressionCoprimeDensityUpperLong_small_of_wide
      (P := P) (κ := 0) heta_range hwide)

/-- The generic ordinary squarefree progression upper bound supplies the
manuscript-aligned squarefree fixed-`k` target at the common power cutoff.

All hypotheses passed to the generic estimate are deterministic consequences
of the manuscript's phi-progression range: `M=s*k` is squarefree and coprime to
`d`, `M≤X^(η+κ)`, the quotient interval starts beyond `X^(λ-η-κ)`, and its
upper endpoint is at most `X^θ`. -/
theorem
    PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff_of_ordinary
    {P : Params} {κ : ℝ}
    (hκ_pos : 0 < κ) (hκ_range : P.η + κ < P.lam)
    (hordinary :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.η - κ) P.θ (P.η + κ)) :
    PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff P κ := by
  rcases hordinary with ⟨Csqf, Xbase, hCsqf, hbound⟩
  refine ⟨hκ_pos, hκ_range, Csqf, max Xbase (Real.exp 1), hCsqf, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS k hk hk_sqf hadm
  have hXbase : Xbase ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXexp
  have hXgtone : (1 : ℝ) < X :=
    lt_of_lt_of_le (by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)) hXexp
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hk_one : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk_pos_nat : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk_one
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos_nat
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hsk_coprime : Nat.Coprime s k := hadm.2.symm
  have hM_sqf : Squarefree (s * k) :=
    (Nat.squarefree_mul hsk_coprime).mpr ⟨hs_sqf, hk_sqf⟩
  have hM_coprime_d : Nat.Coprime (s * k) d :=
    hs_coprime.mul hadm.1
  have hb_coprime_d : Nat.Coprime (a * modInverseChoice d k) d :=
    ha_coprime.mul (modInverseChoice_value_coprime hd_pos hadm.1)
  have hM_scale :
      ((s * k : ℕ) : ℝ) ≤ X ^ (P.η + κ) :=
    phiProgression_sk_le_rpow_eta_add_kappa_of_mem_powerCutoff
      P hXone hsS hk
  have hU0_scale :
      X ^ (P.lam - P.η - κ) ≤
        phiProgressionU0 P s X / (k : ℝ) :=
    phiProgressionU0_div_nat_ge_rpow_lam_sub_eta_sub_of_mem_powerCutoff
      P hXone hs_one hsS hk
  have hU1_scale :
      phiProgressionU1 P s X / (k : ℝ) ≤ X ^ P.θ :=
    phiProgressionU1_div_nat_le_rpow_theta P hXpos hs_one hk_one
  have hU01 :
      phiProgressionU0 P s X / (k : ℝ) <
        phiProgressionU1 P s X / (k : ℝ) :=
    div_lt_div_of_pos_right
      (phiProgressionU0_lt_U1_of_s_le_SScale P hXgtone hs_one hsS)
      hk_pos
  have hU0_one :
      (1 : ℝ) ≤ phiProgressionU0 P s X / (k : ℝ) :=
    (Real.one_le_rpow hXone (by linarith [hκ_range])).trans hU0_scale
  have hU1_one :
      (1 : ℝ) ≤ phiProgressionU1 P s X / (k : ℝ) :=
    hU0_one.trans hU01.le
  have hU0_pos : 0 < phiProgressionU0 P s X :=
    phiProgressionU0_pos P hXpos hs_pos
  have hlog_arg :
      (phiProgressionU1 P s X / (k : ℝ)) /
          (phiProgressionU0 P s X / (k : ℝ)) =
        phiProgressionU1 P s X / phiProgressionU0 P s X := by
    field_simp [ne_of_gt hk_pos, ne_of_gt hU0_pos]
  have hratio_base :
      X ^ (P.θ - P.lam - P.η) ≤
        phiProgressionU1 P s X / phiProgressionU0 P s X :=
    phiProgression_ratio_ge_rpow_theta_sub_lam_sub_eta P hXone hs_one hsS
  have hratio :
      X ^ (P.θ - P.lam - P.η) ≤
        (phiProgressionU1 P s X / (k : ℝ)) /
          (phiProgressionU0 P s X / (k : ℝ)) := by
    rw [hlog_arg]
    exact hratio_base
  have hraw :=
    hbound X hXbase (s * k) d (a * modInverseChoice d k)
      hd_pos hM_sqf hd_sqf hM_coprime_d hb_coprime_d
      hM_scale hdU
      (phiProgressionU0 P s X / (k : ℝ))
      (phiProgressionU1 P s X / (k : ℝ))
      hU0_scale hU01 hU1_scale
  simpa [Nat.cast_mul, hlog_arg] using hraw

/-- The wide-modulus ordinary squarefree progression upper bound supplies the
paper's squarefree fixed-`k` target on the same tensor modulus range. -/
theorem
    PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoffYU_of_ordinaryYU
    {P : Params} {κ : ℝ}
    (hκ_pos : 0 < κ) (hκ_range : P.η + κ < P.lam)
    (hordinary :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.η - κ) P.θ (P.η + κ)) :
    PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoffYU P κ := by
  rcases hordinary with ⟨Csqf, Xbase, hCsqf, hbound⟩
  refine ⟨hκ_pos, hκ_range, Csqf, max Xbase (Real.exp 1), hCsqf, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdYU ha_coprime
    hs_one hs_sqf hs_coprime hsS k hk hk_sqf hadm
  have hXbase : Xbase ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXexp
  have hXgtone : (1 : ℝ) < X :=
    lt_of_lt_of_le (by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)) hXexp
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hk_one : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk_pos_nat : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk_one
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos_nat
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hsk_coprime : Nat.Coprime s k := hadm.2.symm
  have hM_sqf : Squarefree (s * k) :=
    (Nat.squarefree_mul hsk_coprime).mpr ⟨hs_sqf, hk_sqf⟩
  have hM_coprime_d : Nat.Coprime (s * k) d :=
    hs_coprime.mul hadm.1
  have hb_coprime_d : Nat.Coprime (a * modInverseChoice d k) d :=
    ha_coprime.mul (modInverseChoice_value_coprime hd_pos hadm.1)
  have hM_scale :
      ((s * k : ℕ) : ℝ) ≤ X ^ (P.η + κ) :=
    phiProgression_sk_le_rpow_eta_add_kappa_of_mem_powerCutoff
      P hXone hsS hk
  have hU0_scale :
      X ^ (P.lam - P.η - κ) ≤
        phiProgressionU0 P s X / (k : ℝ) :=
    phiProgressionU0_div_nat_ge_rpow_lam_sub_eta_sub_of_mem_powerCutoff
      P hXone hs_one hsS hk
  have hU1_scale :
      phiProgressionU1 P s X / (k : ℝ) ≤ X ^ P.θ :=
    phiProgressionU1_div_nat_le_rpow_theta P hXpos hs_one hk_one
  have hU01 :
      phiProgressionU0 P s X / (k : ℝ) <
        phiProgressionU1 P s X / (k : ℝ) :=
    div_lt_div_of_pos_right
      (phiProgressionU0_lt_U1_of_s_le_SScale P hXgtone hs_one hsS)
      hk_pos
  have hU0_one :
      (1 : ℝ) ≤ phiProgressionU0 P s X / (k : ℝ) :=
    (Real.one_le_rpow hXone (by linarith [hκ_range])).trans hU0_scale
  have hU1_one :
      (1 : ℝ) ≤ phiProgressionU1 P s X / (k : ℝ) :=
    hU0_one.trans hU01.le
  have hU0_pos : 0 < phiProgressionU0 P s X :=
    phiProgressionU0_pos P hXpos hs_pos
  have hlog_arg :
      (phiProgressionU1 P s X / (k : ℝ)) /
          (phiProgressionU0 P s X / (k : ℝ)) =
        phiProgressionU1 P s X / phiProgressionU0 P s X := by
    field_simp [ne_of_gt hk_pos, ne_of_gt hU0_pos]
  have hratio_base :
      X ^ (P.θ - P.lam - P.η) ≤
        phiProgressionU1 P s X / phiProgressionU0 P s X :=
    phiProgression_ratio_ge_rpow_theta_sub_lam_sub_eta P hXone hs_one hsS
  have hratio :
      X ^ (P.θ - P.lam - P.η) ≤
        (phiProgressionU1 P s X / (k : ℝ)) /
          (phiProgressionU0 P s X / (k : ℝ)) := by
    rw [hlog_arg]
    exact hratio_base
  have hraw :=
    hbound X hXbase (s * k) d (a * modInverseChoice d k)
      hd_pos hM_sqf hd_sqf hM_coprime_d hb_coprime_d
      hM_scale hdYU
      (phiProgressionU0 P s X / (k : ℝ))
      (phiProgressionU1 P s X / (k : ℝ))
      hU0_scale hU01 hU1_one hU1_scale hratio
  simpa [Nat.cast_mul, hlog_arg] using hraw

/-- Long-window version of
`PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff_of_ordinary`.

This consumes the manuscript-aligned ordinary-squarefree progression upper target,
including `U₁/U₀ ≥ X^c₀`, and discharges that hypothesis from the checked
phi-window ratio estimate. -/
theorem
    PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff_of_ordinary_long
    {P : Params} {κ : ℝ}
    (hκ_pos : 0 < κ) (hκ_range : P.η + κ < P.lam)
    (hordinary :
      OrdinarySquarefreeProgressionCoprimeDensityUpperLong
        (P.lam - P.η - κ) P.θ (P.θ - P.lam - P.η) (P.η + κ)) :
    PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff P κ := by
  rcases hordinary with ⟨Csqf, Xbase, hCsqf, hbound⟩
  refine ⟨hκ_pos, hκ_range, Csqf, max Xbase (Real.exp 1), hCsqf, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS k hk hk_sqf hadm
  have hXbase : Xbase ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXexp
  have hXgtone : (1 : ℝ) < X :=
    lt_of_lt_of_le (by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)) hXexp
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hk_one : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk_pos_nat : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk_one
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos_nat
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hsk_coprime : Nat.Coprime s k := hadm.2.symm
  have hM_sqf : Squarefree (s * k) :=
    (Nat.squarefree_mul hsk_coprime).mpr ⟨hs_sqf, hk_sqf⟩
  have hM_coprime_d : Nat.Coprime (s * k) d :=
    hs_coprime.mul hadm.1
  have hb_coprime_d : Nat.Coprime (a * modInverseChoice d k) d :=
    ha_coprime.mul (modInverseChoice_value_coprime hd_pos hadm.1)
  have hM_scale :
      ((s * k : ℕ) : ℝ) ≤ X ^ (P.η + κ) :=
    phiProgression_sk_le_rpow_eta_add_kappa_of_mem_powerCutoff
      P hXone hsS hk
  have hU0_scale :
      X ^ (P.lam - P.η - κ) ≤
        phiProgressionU0 P s X / (k : ℝ) :=
    phiProgressionU0_div_nat_ge_rpow_lam_sub_eta_sub_of_mem_powerCutoff
      P hXone hs_one hsS hk
  have hU1_scale :
      phiProgressionU1 P s X / (k : ℝ) ≤ X ^ P.θ :=
    phiProgressionU1_div_nat_le_rpow_theta P hXpos hs_one hk_one
  have hU01 :
      phiProgressionU0 P s X / (k : ℝ) <
        phiProgressionU1 P s X / (k : ℝ) :=
    div_lt_div_of_pos_right
      (phiProgressionU0_lt_U1_of_s_le_SScale P hXgtone hs_one hsS)
      hk_pos
  have hU0_one :
      (1 : ℝ) ≤ phiProgressionU0 P s X / (k : ℝ) :=
    (Real.one_le_rpow hXone (by linarith [hκ_range])).trans hU0_scale
  have hU1_one :
      (1 : ℝ) ≤ phiProgressionU1 P s X / (k : ℝ) :=
    hU0_one.trans hU01.le
  have hU0_pos : 0 < phiProgressionU0 P s X :=
    phiProgressionU0_pos P hXpos hs_pos
  have hratio_base :
      X ^ (P.θ - P.lam - P.η) ≤
        phiProgressionU1 P s X / phiProgressionU0 P s X :=
    phiProgression_ratio_ge_rpow_theta_sub_lam_sub_eta P hXone hs_one hsS
  have hlog_arg :
      (phiProgressionU1 P s X / (k : ℝ)) /
          (phiProgressionU0 P s X / (k : ℝ)) =
        phiProgressionU1 P s X / phiProgressionU0 P s X := by
    field_simp [ne_of_gt hk_pos, ne_of_gt hU0_pos]
  have hratio :
      X ^ (P.θ - P.lam - P.η) ≤
        (phiProgressionU1 P s X / (k : ℝ)) /
          (phiProgressionU0 P s X / (k : ℝ)) := by
    rw [hlog_arg]
    exact hratio_base
  have hraw :=
    hbound X hXbase (s * k) d (a * modInverseChoice d k)
      hd_pos hM_sqf hd_sqf hM_coprime_d hb_coprime_d
      hM_scale hdU
      (phiProgressionU0 P s X / (k : ℝ))
      (phiProgressionU1 P s X / (k : ℝ))
      hU0_scale hU01 hU1_one hU1_scale hratio
  simpa [Nat.cast_mul, hlog_arg] using hraw

/-- CRT/totient endpoint-margin discharge of the manuscript-aligned fixed-`k`
ordinary-density upper target.

This is the exact composition of the finite CRT/totient upper layer with the
phi-progression bookkeeping.  The remaining hypothesis is only the exponent
margin saying that the lower endpoint `X^(λ-η-κ)` dominates the total conductor
scale `X^(η+κ)` up to the polylogarithmic `D≤UScale X` factor. -/
theorem
    PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff_of_crt_endpoint_margin
    {P : Params} {κ : ℝ}
    (hκ_pos : 0 < κ) (hκ_range : P.η + κ < P.lam)
    (hmargin : P.η + κ < P.lam - P.η - κ) :
    PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff P κ :=
  PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff_of_ordinary_long
    hκ_pos hκ_range
    (OrdinarySquarefreeProgressionCoprimeDensityUpperLong_of_crt_endpoint_margin
      hmargin (by linarith [P.lam_add_η_lt_θ]))

/-- Same fixed-`k` CRT/totient endpoint-margin route, with the exponent margin
written in the symmetric form `2(η+κ)<λ`. -/
theorem
    PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff_of_crt_endpoint_double_margin
    {P : Params} {κ : ℝ}
    (hκ_pos : 0 < κ) (hκ_range : P.η + κ < P.lam)
    (hdouble : 2 * (P.η + κ) < P.lam) :
    PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff P κ :=
  PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff_of_crt_endpoint_margin
    hκ_pos hκ_range (by linarith [hdouble])

/-- Explicit-parameter CRT/totient discharge of the paper's bounded small-`k`
ordinary-density upper target at the cutoff `κ=σ/2`.

This removes the ordinary-squarefree upper estimate from the small-`k` side of
the explicit-parameter phi-progression route.  The only arithmetic input used
is the finite CRT/totient endpoint bound; the needed exponent margin is the
checked numerical inequality `2η+σ<λ` for `Params.explicit`, equivalently
`2(η+σ/2)<λ`. -/
theorem
    PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff_explicit_sigma_half :
    PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff
      Params.explicit (Params.explicit.σ / 2) :=
  PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff_of_crt_endpoint_double_margin
    (P := Params.explicit) (κ := Params.explicit.σ / 2)
    (by norm_num [Params.explicit])
    (by norm_num [Params.explicit])
    (by norm_num [Params.explicit])

/-- The paper's bounded small-`k` ordinary-density target supplies the generic
cutoff-indexed interface at the concrete power cutoff `⌊X^κ⌋₊`. -/
theorem PhiProgressionFixedKOrdinaryDensityUpperForCutoff_of_powerCutoff
    {P : Params} {κ : ℝ}
    (h : PhiProgressionFixedKOrdinaryDensityUpperForPowerCutoff P κ) :
    PhiProgressionFixedKOrdinaryDensityUpperForCutoff P
      (phiProgressionPowerCutoff κ) := by
  rcases h with ⟨_hκ_pos, _hκ_range, Csqf, X₀, hCsqf, hbound⟩
  exact ⟨Csqf, X₀, hCsqf, hbound⟩

/-- Pointwise fixed-`k` version of the ordinary-density squarefree progression
estimate used in the upper half of `lem:phi-progression-average`.

This removes the artificial cutoff function from the remaining analytic target:
the estimate is stated directly for each admissible divisor `k`. -/
def PhiProgressionFixedKOrdinaryDensityUpper
    (P : Params) : Prop :=
  ∃ Csqf X₀ : ℝ, 0 < Csqf ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ d a s : ℕ,
      0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
      Nat.Coprime a d →
      1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
        ∀ k : ℕ, 1 ≤ k →
          Nat.Coprime k d ∧ Nat.Coprime k s →
            Inputs.sqfRecip X (s * k) d (a * modInverseChoice d k)
              (phiProgressionU0 P s X / (k : ℝ))
              (phiProgressionU1 P s X / (k : ℝ)) ≤
              Csqf * (((1 : ℝ) / (d : ℝ)) *
                ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) *
                Real.log (phiProgressionU1 P s X /
                  phiProgressionU0 P s X))

/-- The pointwise fixed-`k` ordinary-density estimate supplies the older
cutoff-indexed interface for every cutoff. -/
theorem PhiProgressionFixedKOrdinaryDensityUpperForCutoff_of_pointwise
    {P : Params}
    (h : PhiProgressionFixedKOrdinaryDensityUpper P) :
    ∀ K : ℝ → ℕ → ℕ → ℕ,
      PhiProgressionFixedKOrdinaryDensityUpperForCutoff P K := by
  rcases h with ⟨Csqf, X₀, hCsqf, hbound⟩
  intro K
  refine ⟨Csqf, X₀, hCsqf, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS k hk hadm
  exact hbound X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS k (Finset.mem_Icc.mp hk).1 hadm

/-- The pointwise fixed-`k` ordinary-density estimate supplies the manuscript's
bounded power-cutoff small-`k` interface. -/
theorem PhiProgressionFixedKOrdinaryDensityUpperForPowerCutoff_of_pointwise
    {P : Params} {κ : ℝ}
    (hκ_pos : 0 < κ) (hκ_range : P.η + κ < P.lam)
    (h : PhiProgressionFixedKOrdinaryDensityUpper P) :
    PhiProgressionFixedKOrdinaryDensityUpperForPowerCutoff P κ := by
  rcases h with ⟨Csqf, X₀, hCsqf, hbound⟩
  refine ⟨hκ_pos, hκ_range, Csqf, X₀, hCsqf, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS k hk hadm
  exact hbound X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS k (Finset.mem_Icc.mp hk).1 hadm

/-- Fixed-cutoff gamma coefficient bound for the ordinary-density split. -/
def PhiProgressionGammaCoefficientBoundForCutoff
    (P : Params) (K : ℝ → ℕ → ℕ → ℕ) : Prop :=
  ∃ Cgamma X₀ : ℝ, 0 < Cgamma ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ d a s : ℕ,
      0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
      Nat.Coprime a d →
      1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
        phiProgressionGammaSmallAdmissibleGammaDivSum d s (K X d s) ≤
          Cgamma

/-- A uniform bound for the one-dimensional full gamma coefficient series
implies every fixed-cutoff admissible coefficient bound. -/
theorem PhiProgressionGammaCoefficientBoundForCutoff_of_phiGammaDivSummableBound
    {P : Params} {K : ℝ → ℕ → ℕ → ℕ}
    (hcoeff : PhiGammaDivSummableBound) :
    PhiProgressionGammaCoefficientBoundForCutoff P K := by
  rcases hcoeff with ⟨Cgamma, hCgamma, hbound⟩
  refine ⟨Cgamma, 0, hCgamma, ?_⟩
  intro X _hX d _a s _hd_pos _hd_sqf _hd_odd _hdU _ha_coprime
    _hs_one _hs_sqf _hs_coprime _hsS
  exact le_trans
    (phiProgressionGammaSmallAdmissibleGammaDivSum_le_phiGammaDivSum
      d s (K X d s))
    (hbound (K X d s))

/-- Large-tail part of the ordinary-density gamma split, with the cutoff chosen
by the analytic input. -/
def PhiProgressionGammaLargeTailMajorantUpperCore
    (P : Params) : Prop :=
  ∃ K : ℝ → ℕ → ℕ → ℕ, ∃ Ctail X₀ : ℝ,
    0 < Ctail ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          phiProgressionGammaLargeTailMajorant P X d a s (K X d s) ≤
            Ctail * phiProgressionAverageShape P X d s

/-- Large-tail analytic target after the checked quotient-fiber reduction:
bound the admissible squarefree-reciprocal model with coefficient
`2^ω(k)/k²`.  This is closer to the cited progression-estimate interface than
the raw divisor-tail carrier. -/
def PhiProgressionOmegaLargeSqfRecipAdmissibleInverseModelUpperCore
    (P : Params) : Prop :=
  ∃ K : ℝ → ℕ → ℕ → ℕ, ∃ Ctail X₀ : ℝ,
    0 < Ctail ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          phiProgressionOmegaLargeSqfRecipAdmissibleInverseModelSum
              P X d a s (K X d s) ≤
            Ctail * phiProgressionAverageShape P X d s

/-- One-dimensional coefficient target for the large squarefree-reciprocal
model after the fixed-`k` ordinary-density estimate has supplied the local
factor `φ(sk)/(sk)`. -/
def PhiProgressionOmegaLargeTotientCoeffBoundCore
    (P : Params) : Prop :=
  ∃ K : ℝ → ℕ → ℕ → ℕ, ∃ Comega X₀ : ℝ,
    0 < Comega ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          phiProgressionOmegaLargeAdmissibleTotientCoeffSum d s
              (K X d s) ⌊phiProgressionU1 P s X⌋₊ ≤
            Comega * ((Nat.totient s : ℝ) / (s : ℝ))

/-- Pure one-dimensional coefficient target for the squarefree-reciprocal
large tail.  The local-density dependence on `s` is supplied by
`totient_mul_ratio_le_left_of_coprime`. -/
def PhiOmegaSqTailBound : Prop :=
  ∃ Comega : ℝ, 0 < Comega ∧
    ∀ K N : ℕ, phiOmegaSqTailSum K N ≤ Comega

/-- The square coefficient has Euler factor `1` at `k = 1`. -/
theorem phiOmegaSqCoeff_one :
    phiOmegaSqCoeff 1 = 1 := by
  unfold phiOmegaSqCoeff Inputs.omega
  simp

/-- The square coefficient is multiplicative on coprime arguments. -/
theorem phiOmegaSqCoeff_mul_of_coprime {m n : ℕ}
    (h : Nat.Coprime m n) :
    phiOmegaSqCoeff (m * n) =
      phiOmegaSqCoeff m * phiOmegaSqCoeff n := by
  unfold phiOmegaSqCoeff Inputs.omega
  by_cases hm : (m : ℝ) = 0
  · have hmnat : m = 0 := by exact_mod_cast hm
    subst m
    simp
  · by_cases hn : (n : ℝ) = 0
    · have hnnat : n = 0 := by exact_mod_cast hn
      subst n
      simp
    · rw [h.primeFactors_mul]
      rw [Finset.card_union_of_disjoint h.disjoint_primeFactors]
      rw [pow_add, Nat.cast_mul]
      field_simp [hm, hn]
      ring

/-- The square coefficient is nonnegative. -/
theorem phiOmegaSqCoeff_nonneg (k : ℕ) :
    0 ≤ phiOmegaSqCoeff k := by
  unfold phiOmegaSqCoeff
  exact div_nonneg
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Inputs.omega k))
    (sq_nonneg (k : ℝ))

/-- The squarefree-divisor count `2^omega(k)` is bounded by the full divisor
count.  This is the finite combinatorial input needed to control the endpoint
part of the large-quotient tail. -/
theorem two_pow_omega_le_tau {k : ℕ} (hk : 0 < k) :
    2 ^ Inputs.omega k ≤ Inputs.tau k := by
  have hk0 : k ≠ 0 := ne_of_gt hk
  unfold Inputs.omega Inputs.tau
  rw [Nat.card_divisors hk0]
  rw [← Finset.prod_const]
  apply Finset.prod_le_prod'
  intro p hp
  have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ k := Nat.dvd_of_mem_primeFactors hp
  have hfac : 0 < k.factorization p :=
    hpprime.factorization_pos_of_dvd hk0 hpdvd
  omega

/-- A checked quarter-power envelope for `tau(k)`, obtained by embedding the
divisors of `k` into those of `k^2` and applying the existing divisor-growth
estimate. -/
theorem tau_le_square_quarter_envelope {k : ℕ} (hk : 1 ≤ k) :
    ((Inputs.tau k : ℕ) : ℝ) ≤
      Inputs.tauSquareQuarterConstant * (k : ℝ) ^ ((1 : ℝ) / 4) := by
  have hk0 : k ≠ 0 := by omega
  have hk2 : k ^ 2 ≠ 0 := pow_ne_zero 2 hk0
  have hsubset : k.divisors ⊆ (k ^ 2).divisors :=
    Nat.divisors_subset_of_dvd hk2
      (dvd_pow_self k (by norm_num : 2 ≠ 0))
  have hcard : Inputs.tau k ≤ Inputs.tau (k ^ 2) := by
    unfold Inputs.tau
    exact Finset.card_le_card hsubset
  have hcardR :
      ((Inputs.tau k : ℕ) : ℝ) ≤ ((Inputs.tau (k ^ 2) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  exact hcardR.trans (Inputs.tau_square_le_const_rpow_quarter hk)

/-- Pointwise `k^(-7/4)` envelope for the square coefficient. -/
theorem phiOmegaSqCoeff_le_quarter_tail {k : ℕ} (hk : 1 ≤ k) :
    phiOmegaSqCoeff k ≤
      Inputs.tauSquareQuarterConstant * (k : ℝ) ^ (-(7 : ℝ) / 4) := by
  have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hkRpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
  have homegaR :
      (((2 ^ Inputs.omega k : ℕ) : ℝ)) ≤ (Inputs.tau k : ℕ) := by
    exact_mod_cast two_pow_omega_le_tau hkpos
  have htau := tau_le_square_quarter_envelope hk
  have homegaReal :
      (2 : ℝ) ^ Inputs.omega k = (((2 ^ Inputs.omega k : ℕ) : ℝ)) := by
    norm_num
  unfold phiOmegaSqCoeff
  have hdiv :
      ((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2) ≤
        (Inputs.tauSquareQuarterConstant * (k : ℝ) ^ ((1 : ℝ) / 4)) /
          ((k : ℝ) ^ 2) :=
    div_le_div_of_nonneg_right (by
      rw [homegaReal]
      exact homegaR.trans htau) (sq_nonneg (k : ℝ))
  calc
    (2 : ℝ) ^ Inputs.omega k / (k : ℝ) ^ 2
        ≤ (Inputs.tauSquareQuarterConstant * (k : ℝ) ^ ((1 : ℝ) / 4)) /
            ((k : ℝ) ^ 2) := hdiv
    _ = Inputs.tauSquareQuarterConstant * (k : ℝ) ^ (-(7 : ℝ) / 4) := by
      rw [mul_div_assoc]
      congr 1
      rw [show ((k : ℝ) ^ 2) = (k : ℝ) ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_sub hkRpos]
      norm_num

/-- Arbitrary-subpower version of the square-coefficient envelope.  This lets
the eventual tail exponent be chosen inside whatever strict parameter margin
the manuscript provides, rather than imposing an artificial fixed relation
between `eta` and `sigma`. -/
theorem phiOmegaSqCoeff_subpower_envelope (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k →
      phiOmegaSqCoeff k ≤ C * (k : ℝ) ^ (-(2 - ε)) := by
  rcases Inputs.tauSquareSubpowerBound_unconditional ε hε with
    ⟨C, hC, hTauSq⟩
  refine ⟨C, hC, ?_⟩
  intro k hk
  have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hkRpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
  have homegaR :
      (((2 ^ Inputs.omega k : ℕ) : ℝ)) ≤ (Inputs.tau k : ℕ) := by
    exact_mod_cast two_pow_omega_le_tau hkpos
  have htauSq :
      ((Inputs.tau k : ℕ) : ℝ) ≤ ((Inputs.tau (k ^ 2) : ℕ) : ℝ) := by
    exact_mod_cast tau_le_tau_square k
  have htau := (homegaR.trans htauSq).trans (hTauSq k hk)
  have homegaReal :
      (2 : ℝ) ^ Inputs.omega k = (((2 ^ Inputs.omega k : ℕ) : ℝ)) := by
    norm_num
  unfold phiOmegaSqCoeff
  have hdiv :
      ((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2) ≤
        (C * (k : ℝ) ^ ε) / ((k : ℝ) ^ 2) :=
    div_le_div_of_nonneg_right (by
      rw [homegaReal]
      exact htau) (sq_nonneg (k : ℝ))
  calc
    (2 : ℝ) ^ Inputs.omega k / (k : ℝ) ^ 2
        ≤ (C * (k : ℝ) ^ ε) / ((k : ℝ) ^ 2) := hdiv
    _ = C * (k : ℝ) ^ (-(2 - ε)) := by
      rw [mul_div_assoc]
      congr 1
      rw [show ((k : ℝ) ^ 2) = (k : ℝ) ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_sub hkRpos]
      congr 1
      ring

/-- Integral comparison for the numerical `k^(-7/4)` tail. -/
theorem rpow_seven_quarters_tail_le (K N : ℕ) (hK : 1 ≤ K) :
    (∑ k ∈ (Finset.Icc (1 : ℕ) N).filter (fun k => ¬ k ≤ K),
      (k : ℝ) ^ (-(7 : ℝ) / 4)) ≤
      (4 : ℝ) / 3 * (K : ℝ) ^ (-(3 : ℝ) / 4) := by
  classical
  have hset :
      (Finset.Icc (1 : ℕ) N).filter (fun k => ¬ k ≤ K) =
        Finset.Icc (K + 1) N := by
    ext k
    simp [Finset.mem_Icc]
    omega
  rw [hset]
  by_cases hKN : K ≤ N
  · let f : ℝ → ℝ := fun x => x ^ (-(7 : ℝ) / 4)
    have hKreal : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    have hKpos : (0 : ℝ) < (K : ℝ) := lt_of_lt_of_le zero_lt_one hKreal
    have hNpos : (0 : ℝ) < (N : ℝ) :=
      lt_of_lt_of_le hKpos (by exact_mod_cast hKN)
    have hanti : AntitoneOn f (Set.Icc (K : ℝ) (N : ℝ)) := by
      intro x hx y _hy hxy
      exact Real.rpow_le_rpow_of_nonpos
        (lt_of_lt_of_le hKpos hx.1) hxy (by norm_num)
    have hsumint :
        (∑ i ∈ Finset.Ico K N, f ((i + 1 : ℕ) : ℝ)) ≤
          ∫ x in (K : ℝ)..(N : ℝ), f x := by
      simpa using AntitoneOn.sum_le_integral_Ico hKN hanti
    have hsum_eq :
        (∑ k ∈ Finset.Icc (K + 1) N, (k : ℝ) ^ (-(7 : ℝ) / 4)) =
          ∑ i ∈ Finset.Ico K N, f ((i + 1 : ℕ) : ℝ) := by
      let e : ℕ ↪ ℕ := ⟨Nat.succ, fun _a _b h => Nat.succ.inj h⟩
      have hmap : (Finset.Ico K N).map e = Finset.Icc (K + 1) N := by
        ext m
        simp [e, Nat.succ_eq_add_one, Finset.mem_Ico, Finset.mem_Icc]
        constructor
        · intro h
          omega
        · intro h
          refine ⟨m - 1, ?_, by omega⟩
          omega
      rw [← hmap]
      simp [e, f]
    have hzero_not : (0 : ℝ) ∉ Set.uIcc (K : ℝ) (N : ℝ) := by
      rw [Set.uIcc_of_le (by exact_mod_cast hKN)]
      intro h
      linarith [h.1]
    have hintegral :
        (∫ x in (K : ℝ)..(N : ℝ), f x) =
          (4 : ℝ) / 3 * ((K : ℝ) ^ (-(3 : ℝ) / 4) -
            (N : ℝ) ^ (-(3 : ℝ) / 4)) := by
      unfold f
      have hpow := integral_rpow
        (a := (K : ℝ)) (b := (N : ℝ)) (r := (-(7 : ℝ) / 4))
        (Or.inr ⟨by norm_num, hzero_not⟩)
      rw [hpow]
      ring
    have hNpow : 0 ≤ (N : ℝ) ^ (-(3 : ℝ) / 4) :=
      Real.rpow_nonneg hNpos.le _
    calc
      (∑ k ∈ Finset.Icc (K + 1) N, (k : ℝ) ^ (-(7 : ℝ) / 4))
          = ∑ i ∈ Finset.Ico K N, f ((i + 1 : ℕ) : ℝ) := hsum_eq
      _ ≤ ∫ x in (K : ℝ)..(N : ℝ), f x := hsumint
      _ = (4 : ℝ) / 3 * ((K : ℝ) ^ (-(3 : ℝ) / 4) -
            (N : ℝ) ^ (-(3 : ℝ) / 4)) := hintegral
      _ ≤ (4 : ℝ) / 3 * (K : ℝ) ^ (-(3 : ℝ) / 4) := by nlinarith
  · have hempty : Finset.Icc (K + 1) N = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro k hk
      have hklo := (Finset.mem_Icc.mp hk).1
      have hKk : K ≤ k := by omega
      have hkN := (Finset.mem_Icc.mp hk).2
      exact hKN (hKk.trans hkN)
    rw [hempty]
    simp
    positivity

/-- Quantitative decay of the square-coefficient tail.  This is the missing
finite estimate behind the large-quotient absorption: the tail is
`O(K^(-3/4))`, uniformly in its finite upper endpoint. -/
theorem phiOmegaSqTailSum_le_quarter_decay (K N : ℕ) (hK : 1 ≤ K) :
    phiOmegaSqTailSum K N ≤
      (Inputs.tauSquareQuarterConstant * ((4 : ℝ) / 3)) *
        (K : ℝ) ^ (-(3 : ℝ) / 4) := by
  classical
  let T := (Finset.Icc (1 : ℕ) N).filter (fun k => ¬ k ≤ K)
  have hC : 0 ≤ Inputs.tauSquareQuarterConstant := by
    unfold Inputs.tauSquareQuarterConstant
    positivity
  calc
    phiOmegaSqTailSum K N
        ≤ ∑ k ∈ T, Inputs.tauSquareQuarterConstant *
            (k : ℝ) ^ (-(7 : ℝ) / 4) := by
          unfold phiOmegaSqTailSum T
          apply Finset.sum_le_sum
          intro k hk
          exact phiOmegaSqCoeff_le_quarter_tail
            (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
    _ = Inputs.tauSquareQuarterConstant *
          (∑ k ∈ T, (k : ℝ) ^ (-(7 : ℝ) / 4)) := by
          rw [Finset.mul_sum]
    _ ≤ Inputs.tauSquareQuarterConstant *
          ((4 : ℝ) / 3 * (K : ℝ) ^ (-(3 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left (rpow_seven_quarters_tail_le K N hK) hC
    _ = (Inputs.tauSquareQuarterConstant * ((4 : ℝ) / 3)) *
          (K : ℝ) ^ (-(3 : ℝ) / 4) := by ring

/-- Manuscript-scale form of the quantitative tail estimate at the power
cutoff `K=floor(X^κ)`. -/
theorem phiOmegaSqTailSum_powerCutoff_le_quarter_saving
    {X κ : ℝ} (hκ : 0 < κ)
    (hX : Real.exp (Real.log 2 / κ) ≤ X) (N d s : ℕ) :
    phiOmegaSqTailSum (phiProgressionPowerCutoff κ X d s) N ≤
      (Inputs.tauSquareQuarterConstant * ((4 : ℝ) / 3) *
          (2 : ℝ) ^ ((3 : ℝ) / 4)) *
        X ^ (-(κ * ((3 : ℝ) / 4))) := by
  have hpow2 : 2 ≤ X ^ κ :=
    two_le_rpow_of_exp_log_two_div_le hκ hX
  have hhalf : X ^ κ / 2 ≤ (⌊X ^ κ⌋₊ : ℝ) :=
    half_le_nat_floor_of_two_le hpow2
  have hhalf_one : (1 : ℝ) ≤ X ^ κ / 2 := by linarith
  have hKreal : (1 : ℝ) ≤ (⌊X ^ κ⌋₊ : ℝ) := hhalf_one.trans hhalf
  have hK : 1 ≤ phiProgressionPowerCutoff κ X d s := by
    unfold phiProgressionPowerCutoff
    exact_mod_cast hKreal
  have hdecay :=
    phiOmegaSqTailSum_le_quarter_decay
      (phiProgressionPowerCutoff κ X d s) N hK
  have hfloor :
      ((phiProgressionPowerCutoff κ X d s : ℕ) : ℝ) ^
          (-(3 : ℝ) / 4) ≤
        (2 : ℝ) ^ ((3 : ℝ) / 4) *
          X ^ (-(κ * ((3 : ℝ) / 4))) := by
    unfold phiProgressionPowerCutoff
    convert nat_floor_rpow_neg_le hκ
      (by norm_num : (0 : ℝ) < (3 : ℝ) / 4) hX using 1 <;> ring
  have hC :
      0 ≤ Inputs.tauSquareQuarterConstant * ((4 : ℝ) / 3) := by
    unfold Inputs.tauSquareQuarterConstant
    positivity
  calc
    phiOmegaSqTailSum (phiProgressionPowerCutoff κ X d s) N
        ≤ (Inputs.tauSquareQuarterConstant * ((4 : ℝ) / 3)) *
            ((phiProgressionPowerCutoff κ X d s : ℕ) : ℝ) ^
              (-(3 : ℝ) / 4) := hdecay
    _ ≤ (Inputs.tauSquareQuarterConstant * ((4 : ℝ) / 3)) *
          ((2 : ℝ) ^ ((3 : ℝ) / 4) *
            X ^ (-(κ * ((3 : ℝ) / 4)))) :=
      mul_le_mul_of_nonneg_left hfloor hC
    _ = (Inputs.tauSquareQuarterConstant * ((4 : ℝ) / 3) *
          (2 : ℝ) ^ ((3 : ℝ) / 4)) *
        X ^ (-(κ * ((3 : ℝ) / 4))) := by ring

/-- For the manuscript's explicit parameters, the logarithmic tail saving
absorbs both the polylogarithmic progression modulus and the quarter-power
loss from the local totient density. -/
theorem explicit_phiOmegaSqTail_mul_modulus_conductor_quarter_bounded :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d s N : ℕ, 1 ≤ d → (d : ℝ) ≤ UScale X →
        1 ≤ s → (s : ℝ) ≤ SScale Params.explicit X →
          phiOmegaSqTailSum
              (phiProgressionPowerCutoff (Params.explicit.σ / 2) X d s) N *
              (d : ℝ) * (s : ℝ) ^ ((1 : ℝ) / 4) ≤ C := by
  let δ : ℝ := 1 / 100
  let Ct : ℝ := Inputs.tauSquareQuarterConstant * ((4 : ℝ) / 3) *
    (2 : ℝ) ^ ((3 : ℝ) / 4)
  have hδ : 0 < δ := by norm_num [δ]
  rcases Inputs.eventually_UScale_le_rpow hδ with ⟨XU, hU⟩
  refine ⟨Ct,
    max (max XU (Real.exp (Real.log 2 / (Params.explicit.σ / 2)))) (Real.exp 1),
    ?_, ?_⟩
  · dsimp [Ct, Inputs.tauSquareQuarterConstant]
    positivity
  intro X hX d s N hd hdU hs hsS
  have hXU : XU ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXcut : Real.exp (Real.log 2 / (Params.explicit.σ / 2)) ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X := le_trans (by norm_num) hXe
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have htail := phiOmegaSqTailSum_powerCutoff_le_quarter_saving
    (d := d) (s := s) (by norm_num [Params.explicit]) hXcut N
  have hdX : (d : ℝ) ≤ X ^ δ := hdU.trans (hU X hXU)
  have hsX : (s : ℝ) ≤ X ^ Params.explicit.η := by
    simpa [SScale] using hsS
  have hsnonneg : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  have hsquarter :
      (s : ℝ) ^ ((1 : ℝ) / 4) ≤
        X ^ (Params.explicit.η * ((1 : ℝ) / 4)) := by
    calc
      (s : ℝ) ^ ((1 : ℝ) / 4)
          ≤ (X ^ Params.explicit.η) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow hsnonneg hsX (by norm_num)
      _ = X ^ (Params.explicit.η * ((1 : ℝ) / 4)) := by
        rw [Real.rpow_mul hXpos.le]
  have hCt : 0 ≤ Ct := by
    dsimp [Ct, Inputs.tauSquareQuarterConstant]
    positivity
  have hdnonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hsqnonneg : 0 ≤ (s : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg hsnonneg _
  calc
    phiOmegaSqTailSum (phiProgressionPowerCutoff (Params.explicit.σ / 2) X d s) N *
          (d : ℝ) * (s : ℝ) ^ ((1 : ℝ) / 4)
      ≤ (Ct * X ^ (-((Params.explicit.σ / 2) * ((3 : ℝ) / 4)))) *
          (d : ℝ) * (s : ℝ) ^ ((1 : ℝ) / 4) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right htail hdnonneg) hsqnonneg
    _ ≤ (Ct * X ^ (-((Params.explicit.σ / 2) * ((3 : ℝ) / 4)))) *
          (X ^ δ) * (X ^ (Params.explicit.η * ((1 : ℝ) / 4))) := by
        have hfirst :
            0 ≤ Ct * X ^ (-((Params.explicit.σ / 2) * ((3 : ℝ) / 4))) :=
          mul_nonneg hCt (Real.rpow_nonneg hXpos.le _)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hdX hfirst) hsquarter hsqnonneg
          (mul_nonneg hfirst (Real.rpow_nonneg hXpos.le δ))
    _ = Ct * X ^ (δ + Params.explicit.η * ((1 : ℝ) / 4) -
          (Params.explicit.σ / 2) * ((3 : ℝ) / 4)) := by
        rw [show Ct * X ^ (-((Params.explicit.σ / 2) * ((3 : ℝ) / 4))) * X ^ δ *
            X ^ (Params.explicit.η * ((1 : ℝ) / 4)) =
          Ct * (X ^ (-((Params.explicit.σ / 2) * ((3 : ℝ) / 4))) * X ^ δ *
            X ^ (Params.explicit.η * ((1 : ℝ) / 4))) by ring]
        rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos]
        congr 1
        ring
    _ ≤ Ct * 1 := by
      apply mul_le_mul_of_nonneg_left _ hCt
      have hexp : δ + Params.explicit.η * ((1 : ℝ) / 4) -
          (Params.explicit.σ / 2) * ((3 : ℝ) / 4) ≤ 0 := by
        norm_num [δ, Params.explicit]
      simpa using Real.rpow_le_rpow_of_exponent_le hXone hexp
    _ = Ct := by ring

/-- For the explicit manuscript parameters, the harmonic endpoint term is
uniformly bounded after multiplication by the modulus and the quarter-power
conductor loss required by the local totient density. -/
theorem explicit_harmonic_endpoint_mul_modulus_conductor_quarter_bounded :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d s : ℕ, 1 ≤ d → (d : ℝ) ≤ UScale X →
        1 ≤ s → (s : ℝ) ≤ SScale Params.explicit X →
          ((1 / phiProgressionU0 Params.explicit s X) *
              ((harmonic ⌊phiProgressionU1 Params.explicit s X⌋₊ : ℚ) : ℝ) ^ 2) *
              (d : ℝ) * (s : ℝ) ^ ((1 : ℝ) / 4) ≤ C := by
  let δ : ℝ := 1 / 100
  let C : ℝ := (Params.explicit.θ + 1) ^ 2
  have hδ : 0 < δ := by norm_num [δ]
  rcases Inputs.eventually_UScale_le_rpow hδ with ⟨XU, hUbound⟩
  refine ⟨C, max XU (Real.exp 1), ?_, ?_⟩
  · norm_num [C, Params.explicit]
  intro X hX d s hd hdU hs hsS
  have hXU : XU ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X := le_trans (by norm_num) hXe
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hlogone : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hXe
  have hinv := one_div_phiProgressionU0_le_rpow_neg_lam_sub_eta
    Params.explicit hXone hs hsS
  have hh := harmonic_floor_phiProgressionU1_sq_le_log_sq
    Params.explicit hXe hs hsS
  have hU := hUbound X hXU
  have hlogpow : (Real.log X) ^ 2 ≤ UScale X := by
    unfold UScale
    exact pow_le_pow_right₀ hlogone (by norm_num)
  have hsnonneg : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  have hsX : (s : ℝ) ≤ X ^ Params.explicit.η := by
    simpa [SScale] using hsS
  have hsquarter :
      (s : ℝ) ^ ((1 : ℝ) / 4) ≤
        X ^ (Params.explicit.η * ((1 : ℝ) / 4)) := by
    calc
      (s : ℝ) ^ ((1 : ℝ) / 4)
          ≤ (X ^ Params.explicit.η) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow hsnonneg hsX (by norm_num)
      _ = X ^ (Params.explicit.η * ((1 : ℝ) / 4)) := by
        rw [Real.rpow_mul hXpos.le]
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hUnonneg : 0 ≤ UScale X := by
    unfold UScale
    positivity
  have hdnonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hsqnonneg : 0 ≤ (s : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg hsnonneg _
  have hmain :
      (1 / phiProgressionU0 Params.explicit s X) *
          ((harmonic ⌊phiProgressionU1 Params.explicit s X⌋₊ : ℚ) : ℝ) ^ 2 ≤
        C * X ^ (-(Params.explicit.lam - Params.explicit.η)) * UScale X := by
    calc
      (1 / phiProgressionU0 Params.explicit s X) *
          ((harmonic ⌊phiProgressionU1 Params.explicit s X⌋₊ : ℚ) : ℝ) ^ 2
        ≤ X ^ (-(Params.explicit.lam - Params.explicit.η)) *
            ((Params.explicit.θ + 1) * Real.log X) ^ 2 := by
          exact mul_le_mul hinv hh (by positivity)
            (Real.rpow_nonneg hXpos.le _)
      _ = C * X ^ (-(Params.explicit.lam - Params.explicit.η)) *
            (Real.log X) ^ 2 := by
          dsimp [C]
          ring
      _ ≤ C * X ^ (-(Params.explicit.lam - Params.explicit.η)) * UScale X := by
          exact mul_le_mul_of_nonneg_left hlogpow
            (mul_nonneg hC (Real.rpow_nonneg hXpos.le _))
  calc
    ((1 / phiProgressionU0 Params.explicit s X) *
          ((harmonic ⌊phiProgressionU1 Params.explicit s X⌋₊ : ℚ) : ℝ) ^ 2) *
          (d : ℝ) * (s : ℝ) ^ ((1 : ℝ) / 4)
      ≤ (C * X ^ (-(Params.explicit.lam - Params.explicit.η)) * UScale X) *
          (d : ℝ) * (s : ℝ) ^ ((1 : ℝ) / 4) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hmain hdnonneg) hsqnonneg
    _ ≤ (C * X ^ (-(Params.explicit.lam - Params.explicit.η)) * UScale X) *
          UScale X * X ^ (Params.explicit.η * ((1 : ℝ) / 4)) := by
        have hf :
            0 ≤ C * X ^ (-(Params.explicit.lam - Params.explicit.η)) * UScale X :=
          mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hXpos.le _)) hUnonneg
        exact mul_le_mul (mul_le_mul_of_nonneg_left hdU hf) hsquarter hsqnonneg
          (mul_nonneg hf hUnonneg)
    _ ≤ (C * X ^ (-(Params.explicit.lam - Params.explicit.η)) * X ^ δ) *
          X ^ δ * X ^ (Params.explicit.η * ((1 : ℝ) / 4)) := by
        have hbase :
            0 ≤ C * X ^ (-(Params.explicit.lam - Params.explicit.η)) :=
          mul_nonneg hC (Real.rpow_nonneg hXpos.le _)
        have hpowδ : 0 ≤ X ^ δ := Real.rpow_nonneg hXpos.le δ
        have hUU : UScale X * UScale X ≤ X ^ δ * X ^ δ :=
          mul_le_mul hU hU hUnonneg hpowδ
        have hcore :
            (C * X ^ (-(Params.explicit.lam - Params.explicit.η))) *
                (UScale X * UScale X) ≤
              (C * X ^ (-(Params.explicit.lam - Params.explicit.η))) *
                (X ^ δ * X ^ δ) :=
          mul_le_mul_of_nonneg_left hUU hbase
        rw [show (C * X ^ (-(Params.explicit.lam - Params.explicit.η)) * UScale X) *
            UScale X * X ^ (Params.explicit.η * ((1 : ℝ) / 4)) =
          (C * X ^ (-(Params.explicit.lam - Params.explicit.η))) *
            (UScale X * UScale X) *
              X ^ (Params.explicit.η * ((1 : ℝ) / 4)) by ring]
        rw [show (C * X ^ (-(Params.explicit.lam - Params.explicit.η)) * X ^ δ) *
            X ^ δ * X ^ (Params.explicit.η * ((1 : ℝ) / 4)) =
          (C * X ^ (-(Params.explicit.lam - Params.explicit.η))) *
            (X ^ δ * X ^ δ) *
              X ^ (Params.explicit.η * ((1 : ℝ) / 4)) by ring]
        exact mul_le_mul_of_nonneg_right hcore (Real.rpow_nonneg hXpos.le _)
    _ = C * X ^ (2 * δ + Params.explicit.η * ((1 : ℝ) / 4) -
          (Params.explicit.lam - Params.explicit.η)) := by
        rw [show (C * X ^ (-(Params.explicit.lam - Params.explicit.η)) * X ^ δ) *
            X ^ δ * X ^ (Params.explicit.η * ((1 : ℝ) / 4)) =
          C * (X ^ (-(Params.explicit.lam - Params.explicit.η)) * X ^ δ * X ^ δ *
            X ^ (Params.explicit.η * ((1 : ℝ) / 4))) by ring]
        rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos,
          ← Real.rpow_add hXpos]
        congr 1
        ring
    _ ≤ C * 1 := by
      apply mul_le_mul_of_nonneg_left _ hC
      have hexp :
          2 * δ + Params.explicit.η * ((1 : ℝ) / 4) -
            (Params.explicit.lam - Params.explicit.η) ≤ 0 := by
        norm_num [δ, Params.explicit]
      simpa using Real.rpow_le_rpow_of_exponent_le hXone hexp
    _ = C := by ring

/-- The endpoint term remains uniformly absorbable on the full tensor range
`d ≤ YU` for the explicit manuscript parameters. -/
theorem explicit_harmonic_endpoint_mul_wideModulus_conductor_quarter_bounded :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d s : ℕ, 1 ≤ d →
        (d : ℝ) ≤ YScale Params.explicit X * UScale X →
        1 ≤ s → (s : ℝ) ≤ SScale Params.explicit X →
          ((1 / phiProgressionU0 Params.explicit s X) *
              ((harmonic ⌊phiProgressionU1 Params.explicit s X⌋₊ : ℚ) : ℝ) ^ 2) *
              (d : ℝ) * (s : ℝ) ^ ((1 : ℝ) / 4) ≤ C := by
  let δ : ℝ := 1 / 100
  let C : ℝ := (Params.explicit.θ + 1) ^ 2
  have hδ : 0 < δ := by norm_num [δ]
  rcases Inputs.eventually_UScale_le_rpow hδ with ⟨XU, hUbound⟩
  refine ⟨C, max XU (Real.exp 1), ?_, ?_⟩
  · norm_num [C, Params.explicit]
  intro X hX d s hd hdYU hs hsS
  have hXU : XU ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X := le_trans (by norm_num) hXe
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hlogone : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hXe
  have hinv := one_div_phiProgressionU0_le_rpow_neg_lam_sub_eta
    Params.explicit hXone hs hsS
  have hh := harmonic_floor_phiProgressionU1_sq_le_log_sq
    Params.explicit hXe hs hsS
  have hU := hUbound X hXU
  have hlogpow : (Real.log X) ^ 2 ≤ UScale X := by
    unfold UScale
    exact pow_le_pow_right₀ hlogone (by norm_num)
  have hsnonneg : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  have hsX : (s : ℝ) ≤ X ^ Params.explicit.η := by
    simpa [SScale] using hsS
  have hsquarter :
      (s : ℝ) ^ ((1 : ℝ) / 4) ≤
        X ^ (Params.explicit.η * ((1 : ℝ) / 4)) := by
    calc
      (s : ℝ) ^ ((1 : ℝ) / 4)
          ≤ (X ^ Params.explicit.η) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow hsnonneg hsX (by norm_num)
      _ = X ^ (Params.explicit.η * ((1 : ℝ) / 4)) := by
        rw [Real.rpow_mul hXpos.le]
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hUnonneg : 0 ≤ UScale X := by unfold UScale; positivity
  have hYnonneg : 0 ≤ YScale Params.explicit X := by
    unfold YScale
    positivity
  have hYUpow :
      YScale Params.explicit X * UScale X ≤
        X ^ (Params.explicit.σ + δ) := by
    calc
      YScale Params.explicit X * UScale X
          ≤ YScale Params.explicit X * X ^ δ :=
        mul_le_mul_of_nonneg_left hU hYnonneg
      _ = X ^ (Params.explicit.σ + δ) := by
        unfold YScale
        rw [← Real.rpow_add hXpos]
  have hdnonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hsqnonneg : 0 ≤ (s : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg hsnonneg _
  have hmain :
      (1 / phiProgressionU0 Params.explicit s X) *
          ((harmonic ⌊phiProgressionU1 Params.explicit s X⌋₊ : ℚ) : ℝ) ^ 2 ≤
        C * X ^ (-(Params.explicit.lam - Params.explicit.η)) * UScale X := by
    calc
      (1 / phiProgressionU0 Params.explicit s X) *
          ((harmonic ⌊phiProgressionU1 Params.explicit s X⌋₊ : ℚ) : ℝ) ^ 2
        ≤ X ^ (-(Params.explicit.lam - Params.explicit.η)) *
            ((Params.explicit.θ + 1) * Real.log X) ^ 2 :=
          mul_le_mul hinv hh (by positivity) (Real.rpow_nonneg hXpos.le _)
      _ = C * X ^ (-(Params.explicit.lam - Params.explicit.η)) *
            (Real.log X) ^ 2 := by
          dsimp [C]
          ring
      _ ≤ C * X ^ (-(Params.explicit.lam - Params.explicit.η)) * UScale X :=
        mul_le_mul_of_nonneg_left hlogpow
          (mul_nonneg hC (Real.rpow_nonneg hXpos.le _))
  calc
    ((1 / phiProgressionU0 Params.explicit s X) *
          ((harmonic ⌊phiProgressionU1 Params.explicit s X⌋₊ : ℚ) : ℝ) ^ 2) *
          (d : ℝ) * (s : ℝ) ^ ((1 : ℝ) / 4)
      ≤ (C * X ^ (-(Params.explicit.lam - Params.explicit.η)) * UScale X) *
          (d : ℝ) * (s : ℝ) ^ ((1 : ℝ) / 4) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hmain hdnonneg) hsqnonneg
    _ ≤ (C * X ^ (-(Params.explicit.lam - Params.explicit.η)) * UScale X) *
          (X ^ (Params.explicit.σ + δ)) *
            X ^ (Params.explicit.η * ((1 : ℝ) / 4)) := by
        have hf :
            0 ≤ C * X ^ (-(Params.explicit.lam - Params.explicit.η)) * UScale X :=
          mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hXpos.le _)) hUnonneg
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hdYU.trans hYUpow) hf)
          hsquarter hsqnonneg
          (mul_nonneg hf (Real.rpow_nonneg hXpos.le _))
    _ ≤ (C * X ^ (-(Params.explicit.lam - Params.explicit.η)) * X ^ δ) *
          X ^ (Params.explicit.σ + δ) *
            X ^ (Params.explicit.η * ((1 : ℝ) / 4)) := by
        have hbase : 0 ≤ C * X ^ (-(Params.explicit.lam - Params.explicit.η)) :=
          mul_nonneg hC (Real.rpow_nonneg hXpos.le _)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hU hbase)
            (Real.rpow_nonneg hXpos.le _))
          (Real.rpow_nonneg hXpos.le _)
    _ = C * X ^ (2 * δ + Params.explicit.σ +
          Params.explicit.η * ((1 : ℝ) / 4) -
            (Params.explicit.lam - Params.explicit.η)) := by
        rw [show (C * X ^ (-(Params.explicit.lam - Params.explicit.η)) * X ^ δ) *
            X ^ (Params.explicit.σ + δ) *
              X ^ (Params.explicit.η * ((1 : ℝ) / 4)) =
          C * (X ^ (-(Params.explicit.lam - Params.explicit.η)) * X ^ δ *
            X ^ (Params.explicit.σ + δ) *
              X ^ (Params.explicit.η * ((1 : ℝ) / 4))) by ring]
        rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos,
          ← Real.rpow_add hXpos]
        congr 1
        ring
    _ ≤ C * 1 := by
      apply mul_le_mul_of_nonneg_left _ hC
      have hexp :
          2 * δ + Params.explicit.σ + Params.explicit.η * ((1 : ℝ) / 4) -
            (Params.explicit.lam - Params.explicit.η) ≤ 0 := by
        norm_num [δ, Params.explicit]
      simpa using Real.rpow_le_rpow_of_exponent_le hXone hexp
    _ = C := by ring

/-- The logarithmic part of the large-quotient tail is fully absorbed for the
manuscript's explicit parameter choice. -/
theorem explicit_phiOmegaSqTailLogAbsorption_components :
    0 < Params.explicit.σ / 2 ∧
      Params.explicit.η + Params.explicit.σ / 2 < Params.explicit.lam ∧
      ∃ Comega X₀ : ℝ, 0 < Comega ∧ ∀ X : ℝ, X₀ ≤ X →
        ∀ d a s : ℕ,
          0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
          Nat.Coprime a d →
          1 ≤ s → Squarefree s → Nat.Coprime s d →
          (s : ℝ) ≤ SScale Params.explicit X →
            phiOmegaSqTailSum
                (phiProgressionPowerCutoff (Params.explicit.σ / 2) X d s)
                ⌊phiProgressionU1 Params.explicit s X⌋₊ *
                Real.log (phiProgressionU1 Params.explicit s X /
                  phiProgressionU0 Params.explicit s X) ≤
              Comega * phiProgressionAverageShape Params.explicit X d s := by
  rcases explicit_phiOmegaSqTail_mul_modulus_conductor_quarter_bounded with
    ⟨C, Xc, hC, hscalar⟩
  let Ctau := Inputs.tauSquareQuarterConstant
  refine ⟨(by norm_num [Params.explicit]), ?_, C * Ctau,
    max Xc (Real.exp 1), mul_pos hC ?_, ?_⟩
  · norm_num [Params.explicit]
  · dsimp [Ctau, Inputs.tauSquareQuarterConstant]
    positivity
  intro X hX d a s hd _hd_sqf _hd_odd hdU _ha hs _hs_sqf _hsd hsS
  have hXc : Xc ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X := le_trans (by norm_num) hXe
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hsposN : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hsRpos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hsposN
  have hdRpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  let K := phiProgressionPowerCutoff (Params.explicit.σ / 2) X d s
  let N := ⌊phiProgressionU1 Params.explicit s X⌋₊
  let L := Real.log (phiProgressionU1 Params.explicit s X /
    phiProgressionU0 Params.explicit s X)
  have hsc := hscalar X hXc d s N (by omega) hdU hs hsS
  have hsqpos : 0 < (s : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_pos_of_pos hsRpos _
  have htail_le_div :
      phiOmegaSqTailSum K N ≤
        C / ((d : ℝ) * (s : ℝ) ^ ((1 : ℝ) / 4)) := by
    apply (le_div_iff₀ (mul_pos hdRpos hsqpos)).2
    simpa [K, N, mul_assoc] using hsc
  have htail_le :
      phiOmegaSqTailSum K N ≤
        C * ((1 : ℝ) / (d : ℝ)) *
          (s : ℝ) ^ (-((1 : ℝ) / 4)) := by
    calc
      phiOmegaSqTailSum K N
          ≤ C / ((d : ℝ) * (s : ℝ) ^ ((1 : ℝ) / 4)) := htail_le_div
      _ = C * ((1 : ℝ) / (d : ℝ)) *
          (s : ℝ) ^ (-((1 : ℝ) / 4)) := by
        rw [Real.rpow_neg hsRpos.le]
        field_simp [ne_of_gt hdRpos, ne_of_gt hsqpos]
  have hLnonneg : 0 ≤ L := by
    dsimp [L]
    rw [log_phiProgressionU1_div_U0_eq_slantLogLength
      Params.explicit hXpos hsposN]
    exact (slantLogLength_ge_theta_sub_lam_sub_eta_mul_log
      Params.explicit hXone hs hsS).trans'
        (mul_nonneg (by norm_num [Params.explicit]) (Real.log_nonneg hXone))
  have hmul := mul_le_mul_of_nonneg_right htail_le hLnonneg
  have hshape0 := phiProgressionAverageShape_lower_subpower
    Params.explicit hd hs (by
      simpa [L, log_phiProgressionU1_div_U0_eq_slantLogLength
        Params.explicit hXpos hsposN] using hLnonneg)
  have hshape :
      ((1 : ℝ) / (d : ℝ)) *
          ((1 / Ctau) * (s : ℝ) ^ (-((1 : ℝ) / 4))) * L ≤
        phiProgressionAverageShape Params.explicit X d s := by
    simpa [Ctau, L, log_phiProgressionU1_div_U0_eq_slantLogLength
      Params.explicit hXpos hsposN] using hshape0
  calc
    phiOmegaSqTailSum K N * L
      ≤ (C * ((1 : ℝ) / (d : ℝ)) *
          (s : ℝ) ^ (-((1 : ℝ) / 4))) * L := hmul
    _ = (C * Ctau) *
        (((1 : ℝ) / (d : ℝ)) *
          ((1 / Ctau) * (s : ℝ) ^ (-((1 : ℝ) / 4))) * L) := by
      dsimp [Ctau, Inputs.tauSquareQuarterConstant]
      field_simp
      ring
    _ ≤ (C * Ctau) * phiProgressionAverageShape Params.explicit X d s :=
      mul_le_mul_of_nonneg_left hshape
        (mul_nonneg hC.le (by
          dsimp [Ctau, Inputs.tauSquareQuarterConstant]
          positivity))

/-- The endpoint coefficient tail `sum 2^omega(k)/k` is bounded by the
checked harmonic-square divisor estimate. -/
theorem phiOmegaDivTailSum_le_harmonic_sq (K N : ℕ) :
    phiOmegaDivTailSum K N ≤ ((harmonic N : ℚ) : ℝ) ^ 2 := by
  classical
  let T := (Finset.Icc (1 : ℕ) N).filter (fun k => ¬ k ≤ K)
  calc
    phiOmegaDivTailSum K N
        ≤ ∑ k ∈ T, ((Inputs.tau k : ℕ) : ℝ) / (k : ℝ) := by
          unfold phiOmegaDivTailSum T
          apply Finset.sum_le_sum
          intro k hk
          have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one
            (Finset.mem_Icc.mp ((Finset.mem_filter.mp hk).1)).1
          exact div_le_div_of_nonneg_right
            (by exact_mod_cast two_pow_omega_le_tau hkpos)
            (Nat.cast_nonneg k)
    _ ≤ ∑ k ∈ Finset.Icc (1 : ℕ) N,
            ((Inputs.tau k : ℕ) : ℝ) / (k : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro k _hkIcc _hknot
            exact div_nonneg (by exact_mod_cast Nat.zero_le (Inputs.tau k))
              (Nat.cast_nonneg k)
    _ ≤ ((harmonic N : ℚ) : ℝ) ^ 2 :=
      Inputs.tau_div_self_sum_le_harmonic_sq N

/-- On a positive prime power, the square coefficient is a geometric term with
ratio `1/p²`. -/
theorem phiOmegaSqCoeff_prime_pow_succ {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    phiOmegaSqCoeff (p ^ (e + 1)) =
      (2 : ℝ) * (((1 : ℝ) / ((p : ℝ) ^ 2)) ^ (e + 1)) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  unfold phiOmegaSqCoeff Inputs.omega
  rw [Nat.primeFactors_pow p (Nat.succ_ne_zero e)]
  rw [hp.primeFactors]
  simp only [Finset.card_singleton, pow_one]
  rw [Nat.cast_pow]
  field_simp [ne_of_gt hp_pos]
  ring

/-- Exact positive-exponent local mass for the square coefficient. -/
theorem phiOmegaSqCoeff_primePower_positive_tsum {p : ℕ} (hp : Nat.Prime p) :
    (∑' e : ℕ, phiOmegaSqCoeff (p ^ (e + 1))) =
      (2 : ℝ) / (((p : ℝ) ^ 2) - 1) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp_sq_pos : (0 : ℝ) < (p : ℝ) ^ 2 := sq_pos_of_pos hp_pos
  have hp_sq_gt_one : (1 : ℝ) < (p : ℝ) ^ 2 := by nlinarith
  have hr_nonneg : 0 ≤ (1 : ℝ) / ((p : ℝ) ^ 2) :=
    div_nonneg zero_le_one hp_sq_pos.le
  have hr_lt_one : (1 : ℝ) / ((p : ℝ) ^ 2) < 1 := by
    rw [div_lt_one hp_sq_pos]
    exact hp_sq_gt_one
  calc
    (∑' e : ℕ, phiOmegaSqCoeff (p ^ (e + 1)))
        = ∑' e : ℕ,
            (2 : ℝ) * (((1 : ℝ) / ((p : ℝ) ^ 2)) ^ (e + 1)) := by
          apply tsum_congr
          intro e
          exact phiOmegaSqCoeff_prime_pow_succ hp e
    _ = (2 : ℝ) *
          ∑' e : ℕ, (((1 : ℝ) / ((p : ℝ) ^ 2)) ^ (e + 1)) := by
          rw [tsum_mul_left]
    _ = (2 : ℝ) *
          (((1 : ℝ) / ((p : ℝ) ^ 2)) *
            ∑' e : ℕ, (((1 : ℝ) / ((p : ℝ) ^ 2)) ^ e)) := by
          congr 1
          rw [← tsum_mul_left]
          apply tsum_congr
          intro e
          rw [pow_succ']
    _ = (2 : ℝ) *
          (((1 : ℝ) / ((p : ℝ) ^ 2)) *
            (1 - (1 : ℝ) / ((p : ℝ) ^ 2))⁻¹) := by
          rw [tsum_geometric_of_lt_one hr_nonneg hr_lt_one]
    _ = (2 : ℝ) / (((p : ℝ) ^ 2) - 1) := by
          field_simp [ne_of_gt hp_sq_pos, ne_of_gt (by linarith : (0 : ℝ) < (p : ℝ) ^ 2 - 1)]

/-- Summability of the positive-exponent local square-coefficient mass. -/
theorem phiOmegaSqCoeff_primePower_positive_summable {p : ℕ} (hp : Nat.Prime p) :
    Summable (fun e : ℕ => phiOmegaSqCoeff (p ^ (e + 1))) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp_sq_pos : (0 : ℝ) < (p : ℝ) ^ 2 := sq_pos_of_pos hp_pos
  have hp_sq_gt_one : (1 : ℝ) < (p : ℝ) ^ 2 := by nlinarith
  have hr_nonneg : 0 ≤ (1 : ℝ) / ((p : ℝ) ^ 2) :=
    div_nonneg zero_le_one hp_sq_pos.le
  have hr_lt_one : (1 : ℝ) / ((p : ℝ) ^ 2) < 1 := by
    rw [div_lt_one hp_sq_pos]
    exact hp_sq_gt_one
  have hgeom : Summable (fun e : ℕ => ((1 : ℝ) / ((p : ℝ) ^ 2)) ^ e) :=
    summable_geometric_of_lt_one hr_nonneg hr_lt_one
  have hshift :
      Summable (fun e : ℕ => ((1 : ℝ) / ((p : ℝ) ^ 2)) ^ (e + 1)) := by
    refine (hgeom.mul_left ((1 : ℝ) / ((p : ℝ) ^ 2))).congr ?_
    intro e
    rw [pow_succ]
    ring
  refine hshift.mul_left (2 : ℝ) |>.congr ?_
  intro e
  exact (phiOmegaSqCoeff_prime_pow_succ hp e).symm

/-- Norm-summability of the local prime-power square coefficient. -/
theorem phiOmegaSqCoeff_primePower_norm_summable {p : ℕ} (hp : Nat.Prime p) :
    Summable (fun e : ℕ => ‖phiOmegaSqCoeff (p ^ e)‖) := by
  have htail := (phiOmegaSqCoeff_primePower_positive_summable hp).abs
  exact (_root_.summable_nat_add_iff
    (f := fun e : ℕ => ‖phiOmegaSqCoeff (p ^ e)‖) 1).1 htail

/-- The local Euler factor for `k ↦ 2^ω(k)/k²`. -/
noncomputable def phiOmegaSqCoeffLocalFactor (p : ℕ) : ℝ :=
  (1 : ℝ) + (2 : ℝ) / (((p : ℝ) ^ 2) - 1)

/-- Exact local Euler factor for the square coefficient. -/
theorem phiOmegaSqCoeff_primePower_tsum {p : ℕ} (hp : Nat.Prime p) :
    (∑' e : ℕ, phiOmegaSqCoeff (p ^ e)) = phiOmegaSqCoeffLocalFactor p := by
  have hsum : Summable (fun e : ℕ => phiOmegaSqCoeff (p ^ e)) :=
    (phiOmegaSqCoeff_primePower_norm_summable hp).of_norm
  rw [tsum_eq_zero_add hsum]
  simp only [pow_zero]
  rw [phiOmegaSqCoeff_one]
  have htail :
      (∑' e : ℕ, phiOmegaSqCoeff (p ^ (e + 1))) =
        (2 : ℝ) / (((p : ℝ) ^ 2) - 1) :=
    phiOmegaSqCoeff_primePower_positive_tsum hp
  rw [htail]
  rfl

/-- Finite Euler-product expansion for the square coefficient. -/
theorem phiOmegaSqCoeff_finiteEulerProduct (s : Finset ℕ) :
    Summable (fun m : Nat.factoredNumbers s => ‖phiOmegaSqCoeff m‖) ∧
      HasSum (fun m : Nat.factoredNumbers s => phiOmegaSqCoeff m)
        (∏ p ∈ s with p.Prime, ∑' e : ℕ, phiOmegaSqCoeff (p ^ e)) := by
  exact EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := phiOmegaSqCoeff)
    phiOmegaSqCoeff_one
    (fun {m n} h => phiOmegaSqCoeff_mul_of_coprime h)
    (fun {p} hp => phiOmegaSqCoeff_primePower_norm_summable hp)
    s

/-- Finite Euler-product expansion with local square-coefficient factors
evaluated explicitly. -/
theorem phiOmegaSqCoeff_finiteEulerProduct_localFactors (s : Finset ℕ) :
    Summable (fun m : Nat.factoredNumbers s => ‖phiOmegaSqCoeff m‖) ∧
      HasSum (fun m : Nat.factoredNumbers s => phiOmegaSqCoeff m)
        (∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
          phiOmegaSqCoeffLocalFactor p) := by
  rcases phiOmegaSqCoeff_finiteEulerProduct s with ⟨hsum, hhas⟩
  refine ⟨hsum, ?_⟩
  have hprod :
      (∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
          ∑' e : ℕ, phiOmegaSqCoeff (p ^ e)) =
        (∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
          phiOmegaSqCoeffLocalFactor p) := by
    exact Finset.prod_congr rfl (by
      intro p hp
      exact phiOmegaSqCoeff_primePower_tsum (Finset.mem_filter.mp hp).2)
  rw [← hprod]
  exact hhas

/-- The full truncated square-coefficient sum is bounded by the finite Euler
product over the primes below the truncation point. -/
theorem phiOmegaSqSum_le_finiteEulerProduct (N : ℕ) :
    phiOmegaSqSum N ≤
      ∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) ((N + 1).primesBelow),
        phiOmegaSqCoeffLocalFactor p := by
  classical
  let primes : Finset ℕ := (N + 1).primesBelow
  let S : Finset {k : ℕ // k ∈ Finset.Icc (1 : ℕ) N} := (Finset.Icc (1 : ℕ) N).attach
  let f : {k : ℕ // k ∈ Finset.Icc (1 : ℕ) N} → Nat.factoredNumbers primes :=
    fun k => ⟨k.1, by
      have hk := Finset.mem_Icc.mp k.2
      exact mem_factoredNumbers_primesBelow_succ_of_pos_le
        (K := N) (k := k.1) hk.1 hk.2⟩
  have hinj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y := by
    intro x _hx y _hy hxy
    apply Subtype.ext
    exact congrArg (fun z : Nat.factoredNumbers primes => (z : ℕ)) hxy
  have hsum_image :
      (∑ x in S, phiOmegaSqCoeff (f x)) =
        ∑ m in S.image f, phiOmegaSqCoeff m := by
    rw [Finset.sum_image]
    exact hinj
  have hsource :
      phiOmegaSqSum N = ∑ x in S, phiOmegaSqCoeff (f x) := by
    unfold phiOmegaSqSum
    change (∑ k ∈ Finset.Icc (1 : ℕ) N, phiOmegaSqCoeff k) =
      ∑ x in (Finset.Icc (1 : ℕ) N).attach, phiOmegaSqCoeff x.1
    rw [← Finset.sum_attach]
  rcases phiOmegaSqCoeff_finiteEulerProduct_localFactors primes with ⟨hsum_norm, hhas⟩
  have hsum : Summable (fun m : Nat.factoredNumbers primes => phiOmegaSqCoeff m) :=
    hsum_norm.of_norm
  have hpartial :
      (∑ m in S.image f, phiOmegaSqCoeff m) ≤
        ∑' m : Nat.factoredNumbers primes, phiOmegaSqCoeff m :=
    sum_le_tsum (S.image f)
      (fun m _hm => phiOmegaSqCoeff_nonneg m)
      hsum
  calc
    phiOmegaSqSum N = ∑ x in S, phiOmegaSqCoeff (f x) := hsource
    _ = ∑ m in S.image f, phiOmegaSqCoeff m := hsum_image
    _ ≤ ∑' m : Nat.factoredNumbers primes, phiOmegaSqCoeff m := hpartial
    _ = ∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) primes,
        phiOmegaSqCoeffLocalFactor p := hhas.tsum_eq
    _ = ∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) ((N + 1).primesBelow),
        phiOmegaSqCoeffLocalFactor p := by rfl

/-- Each prime local square-coefficient Euler factor is nonnegative. -/
theorem phiOmegaSqCoeffLocalFactor_nonneg {p : ℕ} (hp : Nat.Prime p) :
    0 ≤ phiOmegaSqCoeffLocalFactor p := by
  unfold phiOmegaSqCoeffLocalFactor
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hsqminus_pos : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  exact add_nonneg zero_le_one
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hsqminus_pos.le)

/-- The finite square-coefficient Euler product is bounded by the exponential
of twice the finite prime-local square sum. -/
theorem finiteOmegaSqEulerProduct_le_exp_two_primePredSqSum (s : Finset ℕ) :
    (∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
        phiOmegaSqCoeffLocalFactor p) ≤
      Real.exp
        (2 * ∑ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
          (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) := by
  classical
  calc
    (∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
        phiOmegaSqCoeffLocalFactor p)
        ≤ ∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
            Real.exp (2 * ((1 : ℝ) / (((p : ℝ) - 1) ^ 2))) := by
          apply Finset.prod_le_prod
          · intro p hp
            exact phiOmegaSqCoeffLocalFactor_nonneg (Finset.mem_filter.mp hp).2
          · intro p hp
            have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2
            have hp_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpPrime.two_le
            have hpred_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
            have hsqminus_pos : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
            have hden_le : ((p : ℝ) - 1) ^ 2 ≤ (p : ℝ) ^ 2 - 1 := by nlinarith
            have hfrac_le :
                (2 : ℝ) / ((p : ℝ) ^ 2 - 1) ≤
                  2 * ((1 : ℝ) / (((p : ℝ) - 1) ^ 2)) := by
              have hdiv :
                  (2 : ℝ) / ((p : ℝ) ^ 2 - 1) ≤
                    2 / (((p : ℝ) - 1) ^ 2) :=
                div_le_div_of_nonneg_left
                  (by norm_num : (0 : ℝ) ≤ 2) (sq_pos_of_pos hpred_pos) hden_le
              simpa [div_eq_mul_inv] using hdiv
            calc
              phiOmegaSqCoeffLocalFactor p
                  = 1 + (2 : ℝ) / ((p : ℝ) ^ 2 - 1) := by
                    rfl
              _ ≤ 1 + 2 * ((1 : ℝ) / (((p : ℝ) - 1) ^ 2)) :=
                    add_le_add_left hfrac_le 1
              _ ≤ Real.exp (2 * ((1 : ℝ) / (((p : ℝ) - 1) ^ 2))) :=
                    by simpa [div_eq_mul_inv, add_comm] using
                      Real.add_one_le_exp
                        (2 * ((((p : ℝ) - 1) ^ 2)⁻¹))
    _ = Real.exp
        (∑ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
          2 * ((1 : ℝ) / (((p : ℝ) - 1) ^ 2))) := by
          rw [Real.exp_sum]
    _ = Real.exp
        (2 * ∑ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
          (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) := by
          rw [Finset.mul_sum]

/-- The finite square-coefficient Euler product is uniformly bounded by the
global prime-local square mass. -/
theorem finiteOmegaSqEulerProduct_le_exp_two_primePredSqTsum (s : Finset ℕ) :
    (∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
        phiOmegaSqCoeffLocalFactor p) ≤
      Real.exp (2 * ∑' p : Nat.Primes,
        (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) := by
  calc
    (∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
        phiOmegaSqCoeffLocalFactor p)
        ≤ Real.exp
            (2 * ∑ p in Finset.filter (fun p : ℕ => Nat.Prime p) s,
              (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) :=
          finiteOmegaSqEulerProduct_le_exp_two_primePredSqSum s
    _ ≤ Real.exp (2 * ∑' p : Nat.Primes,
          (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) :=
          Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left (primePredSqFiniteSum_le_tsum s)
              (by norm_num : (0 : ℝ) ≤ 2))

/-- The truncated square-coefficient sums are uniformly bounded by the global
prime-local square mass. -/
theorem phiOmegaSqSum_le_exp_two_primePredSqTsum (N : ℕ) :
    phiOmegaSqSum N ≤
      Real.exp (2 * ∑' p : Nat.Primes,
        (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) := by
  calc
    phiOmegaSqSum N
        ≤ ∏ p in Finset.filter (fun p : ℕ => Nat.Prime p) ((N + 1).primesBelow),
            phiOmegaSqCoeffLocalFactor p :=
          phiOmegaSqSum_le_finiteEulerProduct N
    _ ≤ Real.exp (2 * ∑' p : Nat.Primes,
          (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) :=
          finiteOmegaSqEulerProduct_le_exp_two_primePredSqTsum ((N + 1).primesBelow)

/-- The large-tail square coefficient sum is bounded by the corresponding full
truncated coefficient sum. -/
theorem phiOmegaSqTailSum_le_phiOmegaSqSum (K N : ℕ) :
    phiOmegaSqTailSum K N ≤ phiOmegaSqSum N := by
  classical
  unfold phiOmegaSqTailSum phiOmegaSqSum
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset (fun k : ℕ => ¬ k ≤ K) (Finset.Icc (1 : ℕ) N))
    (fun k _hkIcc _hknot => phiOmegaSqCoeff_nonneg k)

/-- Concrete bounded-partial-sums theorem for the square coefficient
`∑ 2^ω(k)/k²`, obtained from the finite Euler product and prime-local square
summability. -/
theorem PhiOmegaSqTailBound_concrete :
    PhiOmegaSqTailBound := by
  refine ⟨Real.exp (2 * ∑' p : Nat.Primes,
    (1 : ℝ) / (((p : ℝ) - 1) ^ 2)), Real.exp_pos _, ?_⟩
  intro K N
  exact le_trans
    (phiOmegaSqTailSum_le_phiOmegaSqSum K N)
    (phiOmegaSqSum_le_exp_two_primePredSqTsum N)

/-- The admissible local-density coefficient sum is bounded by the pure
one-dimensional square tail times the ambient density `φ(s)/s`. -/
theorem phiProgressionOmegaLargeAdmissibleTotientCoeffSum_le_phiOmegaSqTailSum_mul_totientRatio
    (d s K N : ℕ) (hs : 0 < s) :
    phiProgressionOmegaLargeAdmissibleTotientCoeffSum d s K N ≤
      phiOmegaSqTailSum K N * ((Nat.totient s : ℝ) / (s : ℝ)) := by
  classical
  let T := (Finset.Icc (1 : ℕ) N).filter (fun k => ¬ k ≤ K)
  let coeff : ℕ → ℝ :=
    fun k => ((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)
  let ratioS : ℝ := (Nat.totient s : ℝ) / (s : ℝ)
  have hratioS_nonneg : 0 ≤ ratioS := by
    have hsR_nonneg : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs.le
    exact div_nonneg
      (by exact_mod_cast Nat.zero_le (Nat.totient s)) hsR_nonneg
  calc
    phiProgressionOmegaLargeAdmissibleTotientCoeffSum d s K N
        = ∑ k ∈ T,
            if Nat.Coprime k d ∧ Nat.Coprime k s then
              coeff k * ((Nat.totient (s * k) : ℝ) / (s * k : ℝ))
            else 0 := by
          rfl
    _ ≤ ∑ k ∈ T, coeff k * ratioS := by
          apply Finset.sum_le_sum
          intro k hk
          have hkIcc : k ∈ Finset.Icc (1 : ℕ) N :=
            (Finset.mem_filter.mp hk).1
          have hk_pos : 0 < k :=
            lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hkIcc).1
          have hcoef_nonneg : 0 ≤ coeff k :=
            div_nonneg
              (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Inputs.omega k))
              (sq_nonneg (k : ℝ))
          by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
          · rw [if_pos hadm]
            exact mul_le_mul_of_nonneg_left
              (totient_mul_ratio_le_left_of_coprime
                (s := s) (k := k) hs hk_pos hadm.2.symm)
              hcoef_nonneg
          · rw [if_neg hadm]
            exact mul_nonneg hcoef_nonneg hratioS_nonneg
    _ = phiOmegaSqTailSum K N * ((Nat.totient s : ℝ) / (s : ℝ)) := by
          unfold phiOmegaSqTailSum
          rw [Finset.sum_mul]
          simp [T, coeff, ratioS, phiOmegaSqCoeff]

/-- A uniform one-dimensional `2^ω(k)/k²` tail bound supplies the
local-density coefficient target used in the paper-facing large-tail bridge. -/
theorem PhiProgressionOmegaLargeTotientCoeffBoundCore_of_phiOmegaSqTailBound
    {P : Params} (homega : PhiOmegaSqTailBound) :
    PhiProgressionOmegaLargeTotientCoeffBoundCore P := by
  rcases homega with ⟨Comega, hComega, htail⟩
  refine ⟨fun _ _ _ => 0, Comega, 0, hComega, ?_⟩
  intro X _hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hratioS_nonneg :
      0 ≤ (Nat.totient s : ℝ) / (s : ℝ) := by
    have hsR_nonneg : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_pos.le
    exact div_nonneg
      (by exact_mod_cast Nat.zero_le (Nat.totient s)) hsR_nonneg
  exact le_trans
    (phiProgressionOmegaLargeAdmissibleTotientCoeffSum_le_phiOmegaSqTailSum_mul_totientRatio
      d s 0 ⌊phiProgressionU1 P s X⌋₊ hs_pos)
    (mul_le_mul_of_nonneg_right
      (htail 0 ⌊phiProgressionU1 P s X⌋₊) hratioS_nonneg)

/-- Concrete local-density coefficient target for the large squarefree tail.
The one-dimensional `2^ω(k)/k²` tail has already been discharged by the finite
Euler product, so this version leaves no analytic tail hypothesis. -/
theorem PhiProgressionOmegaLargeTotientCoeffBoundCore_concrete
    (P : Params) :
    PhiProgressionOmegaLargeTotientCoeffBoundCore P :=
  PhiProgressionOmegaLargeTotientCoeffBoundCore_of_phiOmegaSqTailBound
    (P := P) PhiOmegaSqTailBound_concrete

/-- The pointwise fixed-`k` ordinary-density estimate and the one-dimensional
large-tail local-density coefficient bound imply the model-side large-tail
upper core. -/
theorem PhiProgressionOmegaLargeSqfRecipAdmissibleInverseModelUpperCore_of_fixedKPointwise_and_totientCoeffBound
    {P : Params}
    (hfixed : PhiProgressionFixedKOrdinaryDensityUpper P)
    (hcoeff : PhiProgressionOmegaLargeTotientCoeffBoundCore P) :
    PhiProgressionOmegaLargeSqfRecipAdmissibleInverseModelUpperCore P := by
  rcases hfixed with ⟨Csqf, Xfixed, hCsqf, hfixed_bound⟩
  rcases hcoeff with ⟨K, Comega, Xcoeff, hComega, hcoeff_bound⟩
  refine ⟨K, Csqf * Comega, max (max Xfixed Xcoeff) (Real.exp 1),
    mul_pos hCsqf hComega, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  have hXfixed : Xfixed ≤ X :=
    le_trans (le_trans (le_max_left Xfixed Xcoeff)
      (le_max_left (max Xfixed Xcoeff) (Real.exp 1))) hX
  have hXcoeff : Xcoeff ≤ X :=
    le_trans (le_trans (le_max_right Xfixed Xcoeff)
      (le_max_left (max Xfixed Xcoeff) (Real.exp 1))) hX
  have hXe : Real.exp 1 ≤ X :=
    le_trans (le_max_right (max Xfixed Xcoeff) (Real.exp 1)) hX
  have hExpOne : (1 : ℝ) < Real.exp 1 := by
    calc
      (1 : ℝ) = Real.exp 0 := by simp
      _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
  have hXone : (1 : ℝ) < X := lt_of_lt_of_le hExpOne hXe
  have hXpos : 0 < X := lt_trans zero_lt_one hXone
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hU0 : 0 < phiProgressionU0 P s X :=
    phiProgressionU0_pos P hXpos hs_pos
  have hU01 : phiProgressionU0 P s X ≤ phiProgressionU1 P s X :=
    (phiProgressionU0_lt_U1_of_s_le_SScale P hXone hs_one hsS).le
  have hlog_nonneg :
      0 ≤ Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) :=
    log_phiProgressionU1_div_U0_nonneg P X s hU0 hU01
  have hscalar_nonneg :
      0 ≤ Csqf * ((1 / (d : ℝ)) *
        Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)) := by
    have hdR_nonneg : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_pos.le
    exact mul_nonneg hCsqf.le
      (mul_nonneg (div_nonneg zero_le_one hdR_nonneg) hlog_nonneg)
  have hcoeff_tail :
      phiProgressionOmegaLargeAdmissibleTotientCoeffSum d s
          (K X d s) ⌊phiProgressionU1 P s X⌋₊ ≤
        Comega * ((Nat.totient s : ℝ) / (s : ℝ)) :=
    hcoeff_bound X hXcoeff d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS
  unfold phiProgressionOmegaLargeSqfRecipAdmissibleInverseModelSum
  calc
    (∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
        (fun k => ¬ k ≤ K X d s),
      if Nat.Coprime k d ∧ Nat.Coprime k s then
        (((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)) *
          Inputs.sqfRecip X (s * k) d (a * modInverseChoice d k)
            (phiProgressionU0 P s X / (k : ℝ))
            (phiProgressionU1 P s X / (k : ℝ))
      else 0)
      ≤
    (∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
        (fun k => ¬ k ≤ K X d s),
      if Nat.Coprime k d ∧ Nat.Coprime k s then
        (((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)) *
          (Csqf * (((1 : ℝ) / (d : ℝ)) *
            ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) *
              Real.log (phiProgressionU1 P s X /
                phiProgressionU0 P s X)))
      else 0) := by
        apply Finset.sum_le_sum
        intro k hk
        by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
        · have hkIcc :
              k ∈ Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊ :=
            (Finset.mem_filter.mp hk).1
          have hk_one : 1 ≤ k := (Finset.mem_Icc.mp hkIcc).1
          have hcoef_nonneg :
              0 ≤ ((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2) :=
            div_nonneg
              (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Inputs.omega k))
              (sq_nonneg (k : ℝ))
          have hsqf_le :
              Inputs.sqfRecip X (s * k) d (a * modInverseChoice d k)
                (phiProgressionU0 P s X / (k : ℝ))
                (phiProgressionU1 P s X / (k : ℝ)) ≤
                Csqf * (((1 : ℝ) / (d : ℝ)) *
                  ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) *
                    Real.log (phiProgressionU1 P s X /
                      phiProgressionU0 P s X)) :=
            hfixed_bound X hXfixed d a s hd_pos hd_sqf hd_odd hdU
              ha_coprime hs_one hs_sqf hs_coprime hsS k hk_one hadm
          rw [if_pos hadm, if_pos hadm]
          exact mul_le_mul_of_nonneg_left hsqf_le hcoef_nonneg
        · simp [hadm]
    _ =
      phiProgressionOmegaLargeAdmissibleTotientCoeffSum d s
          (K X d s) ⌊phiProgressionU1 P s X⌋₊ *
        (Csqf * ((1 / (d : ℝ)) *
          Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X))) := by
        unfold phiProgressionOmegaLargeAdmissibleTotientCoeffSum
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
        · rw [if_pos hadm, if_pos hadm]
          ring
        · simp [hadm]
    _ ≤ (Comega * ((Nat.totient s : ℝ) / (s : ℝ))) *
        (Csqf * ((1 / (d : ℝ)) *
          Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X))) :=
        mul_le_mul_of_nonneg_right hcoeff_tail hscalar_nonneg
    _ = (Csqf * Comega) * phiProgressionAverageShape P X d s := by
        unfold phiProgressionAverageShape
        rw [log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos]
        ring

/-- Fixed-`k` ordinary density plus the pure one-dimensional square-tail bound
imply the model-side large-tail upper core. -/
theorem PhiProgressionOmegaLargeSqfRecipAdmissibleInverseModelUpperCore_of_fixedKPointwise_and_phiOmegaSqTailBound
    {P : Params}
    (hfixed : PhiProgressionFixedKOrdinaryDensityUpper P)
    (homega : PhiOmegaSqTailBound) :
    PhiProgressionOmegaLargeSqfRecipAdmissibleInverseModelUpperCore P :=
  PhiProgressionOmegaLargeSqfRecipAdmissibleInverseModelUpperCore_of_fixedKPointwise_and_totientCoeffBound
    hfixed
    (PhiProgressionOmegaLargeTotientCoeffBoundCore_of_phiOmegaSqTailBound
      (P := P) homega)

/-- Model-side large-tail upper core with the square-coefficient tail fully
discharged.  The only remaining hypothesis is the pointwise fixed-`k`
ordinary-density squarefree progression estimate. -/
theorem
    PhiProgressionOmegaLargeSqfRecipAdmissibleInverseModelUpperCore_of_fixedKPointwise_concreteTail
    {P : Params}
    (hfixed : PhiProgressionFixedKOrdinaryDensityUpper P) :
    PhiProgressionOmegaLargeSqfRecipAdmissibleInverseModelUpperCore P :=
  PhiProgressionOmegaLargeSqfRecipAdmissibleInverseModelUpperCore_of_fixedKPointwise_and_phiOmegaSqTailBound
    hfixed PhiOmegaSqTailBound_concrete

/-- Bounding the admissible squarefree-reciprocal large-tail model is enough
for the original raw large-tail majorant. -/
theorem PhiProgressionGammaLargeTailMajorantUpperCore_of_omegaLargeSqfRecipAdmissibleInverseModelUpperCore
    {P : Params}
    (h : PhiProgressionOmegaLargeSqfRecipAdmissibleInverseModelUpperCore P) :
    PhiProgressionGammaLargeTailMajorantUpperCore P := by
  rcases h with ⟨K, Ctail, X₀, hCtail, hmodel⟩
  refine ⟨K, Ctail, X₀, hCtail, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  exact le_trans
    (phiProgressionGammaLargeTailMajorant_le_omegaLargeSqfRecipAdmissibleInverseModelSum
      P X d a s (K X d s) hd_pos ha_coprime)
    (hmodel X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS)

/-- Raw large-tail majorant from the pointwise fixed-`k` ordinary-density
estimate and the now-concrete square-coefficient Euler-product tail. -/
theorem
    PhiProgressionGammaLargeTailMajorantUpperCore_of_fixedKPointwise_concreteOmegaTail
    {P : Params}
    (hfixed : PhiProgressionFixedKOrdinaryDensityUpper P) :
    PhiProgressionGammaLargeTailMajorantUpperCore P :=
  PhiProgressionGammaLargeTailMajorantUpperCore_of_omegaLargeSqfRecipAdmissibleInverseModelUpperCore
    (PhiProgressionOmegaLargeSqfRecipAdmissibleInverseModelUpperCore_of_fixedKPointwise_concreteTail
      hfixed)

/-- Manuscript-aligned large-tail target with the same power cutoff
`K=⌊X^κ⌋₊` as the small-divisor side. -/
def PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff
    (P : Params) (κ : ℝ) : Prop :=
  0 < κ ∧ P.η + κ < P.lam ∧
    ∃ Ctail X₀ : ℝ, 0 < Ctail ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          phiProgressionGammaLargeTailMajorant P X d a s
              (phiProgressionPowerCutoff κ X d s) ≤
            Ctail * phiProgressionAverageShape P X d s

/-- Same large-tail target on the tensor modulus range `d≤YU`. -/
def PhiProgressionGammaLargeTailMajorantUpperForPowerCutoffYU
    (P : Params) (κ : ℝ) : Prop :=
  0 < κ ∧ P.η + κ < P.lam ∧
    ∃ Ctail X₀ : ℝ, 0 < Ctail ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d →
        (d : ℝ) ≤ YScale P X * UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          phiProgressionGammaLargeTailMajorant P X d a s
              (phiProgressionPowerCutoff κ X d s) ≤
            Ctail * phiProgressionAverageShape P X d s

/-- Crude large-`k` quotient-fiber bound for the manuscript tail route.

This is the formal interface for the elementary step where the congruence and
coprimality restrictions in the quotient variable are dropped and the remaining
harmonic interval is bounded by the common logarithmic length. -/
def PhiProgressionQuotientFiberCrudeLogUpperForPowerCutoff
    (P : Params) (κ : ℝ) : Prop :=
  0 < κ ∧ P.η + κ < P.lam ∧
    ∃ Cfib X₀ : ℝ, 0 < Cfib ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          ∀ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
              (fun k => ¬ k ≤ phiProgressionPowerCutoff κ X d s),
            phiProgressionFixedKQuotientRecipFiber P X d a s k ≤
              Cfib *
                Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)

/-- Correct elementary large-`k` quotient-fiber bound, retaining the endpoint
term from the bare reciprocal progression estimate.

The endpoint term is essential: dropping conditions gives
`∑ 1/t ≪ 1/(U₀/k)+log(U₁/U₀)`, not a pure logarithmic bound. -/
def PhiProgressionQuotientFiberElementaryUpperForPowerCutoff
    (P : Params) (κ : ℝ) : Prop :=
  0 < κ ∧ P.η + κ < P.lam ∧
    ∃ Cfib X₀ : ℝ, 0 < Cfib ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          ∀ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
              (fun k => ¬ k ≤ phiProgressionPowerCutoff κ X d s),
            phiProgressionFixedKQuotientRecipFiber P X d a s k ≤
              Cfib * (((k : ℝ) * (1 / phiProgressionU0 P s X)) +
                Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X))

/-- Modulus-preserving elementary quotient-fiber bound on the tensor range.
The logarithmic term retains the reciprocal progression modulus. -/
def PhiProgressionQuotientFiberElementaryUpperForPowerCutoffYU
    (P : Params) (κ : ℝ) : Prop :=
  0 < κ ∧ P.η + κ < P.lam ∧
    ∃ Cfib X₀ : ℝ, 0 < Cfib ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d →
        (d : ℝ) ≤ YScale P X * UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          ∀ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
              (fun k => ¬ k ≤ phiProgressionPowerCutoff κ X d s),
            phiProgressionFixedKQuotientRecipFiber P X d a s k ≤
              Cfib * (((k : ℝ) * (1 / phiProgressionU0 P s X)) +
                (1 / (d : ℝ)) *
                  Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X))

/-- The elementary quotient-fiber bound is fully checked from the finite
carrier containment into the unrestricted reciprocal progression and the
project's elementary reciprocal-progression estimate. -/
theorem PhiProgressionQuotientFiberElementaryUpperForPowerCutoff_concrete
    {P : Params} {κ : ℝ}
    (hκ_pos : 0 < κ) (hκ_range : P.η + κ < P.lam) :
    PhiProgressionQuotientFiberElementaryUpperForPowerCutoff P κ := by
  refine ⟨hκ_pos, hκ_range, 1, Real.exp 1, by norm_num, ?_⟩
  intro X hX d a s _hd_pos _hd_sqf _hd_odd _hdU _ha_coprime
    hs_one _hs_sqf _hs_coprime hsS k hk
  have hExpOne : (1 : ℝ) < Real.exp 1 := by
    calc
      (1 : ℝ) = Real.exp 0 := by simp
      _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
  have hXone : (1 : ℝ) < X := lt_of_lt_of_le hExpOne hX
  have hXpos : 0 < X := lt_trans zero_lt_one hXone
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hU0_pos : 0 < phiProgressionU0 P s X :=
    phiProgressionU0_pos P hXpos hs_pos
  have hU01 : phiProgressionU0 P s X < phiProgressionU1 P s X :=
    phiProgressionU0_lt_U1_of_s_le_SScale P hXone hs_one hsS
  have hkIcc :
      k ∈ Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊ :=
    (Finset.mem_filter.mp hk).1
  have hk_pos_nat : 0 < k :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hkIcc).1
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos_nat
  have hdrop :=
    phiProgressionFixedKQuotientRecipFiber_le_unrestrictedProgressionRecip
      P X d a s k hk_pos_nat
  have hrec :=
    Inputs.progressionRecip_le_log_plus_inv 1 0 (by norm_num)
      (div_pos hU0_pos hk_pos)
      (div_lt_div_of_pos_right hU01 hk_pos)
  calc
    phiProgressionFixedKQuotientRecipFiber P X d a s k
        ≤ Inputs.progressionRecip 1 0
            (phiProgressionU0 P s X / (k : ℝ))
            (phiProgressionU1 P s X / (k : ℝ)) := hdrop
    _ ≤ 1 / (phiProgressionU0 P s X / (k : ℝ)) +
          (1 / (1 : ℝ)) *
            Real.log
              ((phiProgressionU1 P s X / (k : ℝ)) /
                (phiProgressionU0 P s X / (k : ℝ))) := by
          simpa using hrec
    _ = 1 * (((k : ℝ) * (1 / phiProgressionU0 P s X)) +
          Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)) := by
          rw [one_div_phiProgressionU0_div_nat P (ne_of_gt hU0_pos) hk_pos_nat,
            log_phiProgression_scaled_quotient_eq P (ne_of_gt hU0_pos) hk_pos_nat]
          ring

/-- The modulus-preserving tensor-range fiber bound follows from the exact
residue-class containment and the elementary reciprocal-progression estimate. -/
theorem PhiProgressionQuotientFiberElementaryUpperForPowerCutoffYU_concrete
    {P : Params} {κ : ℝ}
    (hκ_pos : 0 < κ) (hκ_range : P.η + κ < P.lam) :
    PhiProgressionQuotientFiberElementaryUpperForPowerCutoffYU P κ := by
  refine ⟨hκ_pos, hκ_range, 1, Real.exp 1, by norm_num, ?_⟩
  intro X hX d a s hd_pos _hd_sqf _hd_odd _hdYU ha_coprime
    hs_one _hs_sqf _hs_coprime hsS k hk
  have hExpOne : (1 : ℝ) < Real.exp 1 := by
    calc
      (1 : ℝ) = Real.exp 0 := by simp
      _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
  have hXone : (1 : ℝ) < X := lt_of_lt_of_le hExpOne hX
  have hXpos : 0 < X := lt_trans zero_lt_one hXone
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hU0_pos : 0 < phiProgressionU0 P s X :=
    phiProgressionU0_pos P hXpos hs_pos
  have hU01 : phiProgressionU0 P s X < phiProgressionU1 P s X :=
    phiProgressionU0_lt_U1_of_s_le_SScale P hXone hs_one hsS
  have hkIcc := (Finset.mem_filter.mp hk).1
  have hk_pos_nat : 0 < k :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hkIcc).1
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos_nat
  by_cases hkd : Nat.Coprime k d
  · have hdrop :=
      phiProgressionFixedKQuotientRecipFiber_le_progressionRecip_of_coprime
        P X d a s k hd_pos hk_pos_nat hkd
    have hrec :=
      Inputs.progressionRecip_le_log_plus_inv d
        (a * modInverseChoice d k) hd_pos
        (div_pos hU0_pos hk_pos)
        (div_lt_div_of_pos_right hU01 hk_pos)
    calc
      phiProgressionFixedKQuotientRecipFiber P X d a s k
          ≤ Inputs.progressionRecip d (a * modInverseChoice d k)
              (phiProgressionU0 P s X / (k : ℝ))
              (phiProgressionU1 P s X / (k : ℝ)) := hdrop
      _ ≤ 1 / (phiProgressionU0 P s X / (k : ℝ)) +
            (1 / (d : ℝ)) *
              Real.log
                ((phiProgressionU1 P s X / (k : ℝ)) /
                  (phiProgressionU0 P s X / (k : ℝ))) := hrec
      _ = 1 * (((k : ℝ) * (1 / phiProgressionU0 P s X)) +
            (1 / (d : ℝ)) *
              Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)) := by
            rw [one_div_phiProgressionU0_div_nat P (ne_of_gt hU0_pos) hk_pos_nat,
              log_phiProgression_scaled_quotient_eq P (ne_of_gt hU0_pos) hk_pos_nat]
            ring
  · rw [phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_coprime_d
      P X d a s k ha_coprime hkd]
    have hlog_nonneg :
        0 ≤ Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) :=
      log_phiProgressionU1_div_U0_nonneg P X s hU0_pos hU01.le
    positivity

/-- Endpoint-plus-log coefficient carrier left after the checked elementary
quotient-fiber bound is applied to the large-`k` quotient tail. -/
noncomputable def phiOmegaSqEndpointLogTailSum
    (P : Params) (X : ℝ) (s K N : ℕ) : ℝ := by
  classical
  exact
    ∑ k ∈ (Finset.Icc (1 : ℕ) N).filter (fun k => ¬ k ≤ K),
      phiOmegaSqCoeff k *
        (((k : ℝ) * (1 / phiProgressionU0 P s X)) +
          Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X))

/-- Exact separation of the elementary large-tail carrier into its endpoint
and logarithmic pieces. -/
theorem phiOmegaSqEndpointLogTailSum_eq_endpoint_add_log
    (P : Params) (X : ℝ) (s K N : ℕ)
    (hU0 : 0 < phiProgressionU0 P s X) :
    phiOmegaSqEndpointLogTailSum P X s K N =
      (1 / phiProgressionU0 P s X) * phiOmegaDivTailSum K N +
        Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) *
          phiOmegaSqTailSum K N := by
  classical
  let T := (Finset.Icc (1 : ℕ) N).filter (fun k => ¬ k ≤ K)
  let U0 := phiProgressionU0 P s X
  let L := Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)
  unfold phiOmegaSqEndpointLogTailSum phiOmegaDivTailSum phiOmegaSqTailSum
  change (∑ k ∈ T, phiOmegaSqCoeff k * ((k : ℝ) * (1 / U0) + L)) =
    (1 / U0) * (∑ k ∈ T, (2 : ℝ) ^ Inputs.omega k / (k : ℝ)) +
      L * (∑ k ∈ T, phiOmegaSqCoeff k)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hkone : 1 ≤ k :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hkone))
  unfold phiOmegaSqCoeff
  field_simp [hk0, ne_of_gt hU0]
  ring

/-- Finite reduction of the endpoint-plus-log tail: the endpoint contribution
is controlled by a harmonic square, while the logarithmic contribution is the
pure square-coefficient tail. -/
theorem phiOmegaSqEndpointLogTailSum_le_harmonic_endpoint_add_log
    (P : Params) (X : ℝ) (s K N : ℕ)
    (hU0 : 0 < phiProgressionU0 P s X) :
    phiOmegaSqEndpointLogTailSum P X s K N ≤
      (1 / phiProgressionU0 P s X) * ((harmonic N : ℚ) : ℝ) ^ 2 +
        Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) *
          phiOmegaSqTailSum K N := by
  rw [phiOmegaSqEndpointLogTailSum_eq_endpoint_add_log P X s K N hU0]
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left (phiOmegaDivTailSum_le_harmonic_sq K N)
      (div_nonneg zero_le_one hU0.le)) _

/-- Endpoint-plus-log carrier for the modulus-preserving tensor-range bound. -/
noncomputable def phiOmegaSqEndpointLogTailSumYU
    (P : Params) (X : ℝ) (d s K N : ℕ) : ℝ := by
  classical
  exact
    ∑ k ∈ (Finset.Icc (1 : ℕ) N).filter (fun k => ¬ k ≤ K),
      phiOmegaSqCoeff k *
        (((k : ℝ) * (1 / phiProgressionU0 P s X)) +
          (1 / (d : ℝ)) *
            Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X))

/-- Finite reduction of the modulus-preserving endpoint/log carrier. -/
theorem phiOmegaSqEndpointLogTailSumYU_le_harmonic_endpoint_add_log
    (P : Params) (X : ℝ) (d s K N : ℕ)
    (hU0 : 0 < phiProgressionU0 P s X) :
    phiOmegaSqEndpointLogTailSumYU P X d s K N ≤
      (1 / phiProgressionU0 P s X) * ((harmonic N : ℚ) : ℝ) ^ 2 +
        ((1 / (d : ℝ)) *
          Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)) *
            phiOmegaSqTailSum K N := by
  classical
  let T := (Finset.Icc (1 : ℕ) N).filter (fun k => ¬ k ≤ K)
  let U0 := phiProgressionU0 P s X
  let L := (1 / (d : ℝ)) *
    Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)
  unfold phiOmegaSqEndpointLogTailSumYU phiOmegaSqTailSum
  change (∑ k ∈ T, phiOmegaSqCoeff k * ((k : ℝ) * (1 / U0) + L)) ≤
    (1 / U0) * ((harmonic N : ℚ) : ℝ) ^ 2 +
      L * (∑ k ∈ T, phiOmegaSqCoeff k)
  have heq :
      (∑ k ∈ T, phiOmegaSqCoeff k * ((k : ℝ) * (1 / U0) + L)) =
        (1 / U0) * (∑ k ∈ T, (2 : ℝ) ^ Inputs.omega k / (k : ℝ)) +
          L * (∑ k ∈ T, phiOmegaSqCoeff k) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hkone : 1 ≤ k :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
    have hk0 : (k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hkone))
    unfold phiOmegaSqCoeff
    field_simp [hk0, ne_of_gt hU0]
    ring
  rw [heq]
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left (phiOmegaDivTailSum_le_harmonic_sq K N)
      (div_nonneg zero_le_one hU0.le)) _

/-- Tail absorption target for the manuscript's large-`k` argument.

After the quotient fiber is bounded by the common logarithmic length, the
remaining comparison is the one-dimensional
`∑_{k>K} 2^ω(k)/k²` tail together with the paper's polylogarithmic conductor
losses. -/
def PhiOmegaSqTailLogAbsorptionForPowerCutoff
    (P : Params) (κ : ℝ) : Prop :=
  0 < κ ∧ P.η + κ < P.lam ∧
    ∃ Comega X₀ : ℝ, 0 < Comega ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          phiOmegaSqTailSum (phiProgressionPowerCutoff κ X d s)
              ⌊phiProgressionU1 P s X⌋₊ *
              Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) ≤
            Comega * phiProgressionAverageShape P X d s

/-- Packaged form of the checked explicit-parameter logarithmic absorption. -/
theorem explicit_phiOmegaSqTailLogAbsorption :
    PhiOmegaSqTailLogAbsorptionForPowerCutoff
      Params.explicit (Params.explicit.σ / 2) :=
  explicit_phiOmegaSqTailLogAbsorption_components

/-- Corrected endpoint-plus-log absorption target for the elementary
large-`k` route.  This is the remaining one-dimensional analytic comparison
after the quotient carrier itself has been fully checked. -/
def PhiOmegaSqEndpointLogTailAbsorptionForPowerCutoff
    (P : Params) (κ : ℝ) : Prop :=
  0 < κ ∧ P.η + κ < P.lam ∧
    ∃ Comega X₀ : ℝ, 0 < Comega ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          phiOmegaSqEndpointLogTailSum P X s
              (phiProgressionPowerCutoff κ X d s)
              ⌊phiProgressionU1 P s X⌋₊ ≤
            Comega * phiProgressionAverageShape P X d s

/-- The corrected endpoint-plus-log absorption is unconditional for the
manuscript's explicit parameter choice. -/
theorem explicit_phiOmegaSqEndpointLogTailAbsorption :
    PhiOmegaSqEndpointLogTailAbsorptionForPowerCutoff
      Params.explicit (Params.explicit.σ / 2) := by
  rcases explicit_harmonic_endpoint_mul_modulus_conductor_quarter_bounded with
    ⟨Ce, Xe, hCe, hendScalar⟩
  rcases explicit_phiOmegaSqTailLogAbsorption with
    ⟨hκ, hκrange, Cl, Xl, hCl, hlog⟩
  rcases slantLogLength_ge_one_eventually Params.explicit with ⟨Xs, hslant⟩
  let Ctau := Inputs.tauSquareQuarterConstant
  refine ⟨hκ, hκrange, Ce * Ctau + Cl,
    max (max (max Xe Xl) Xs) (Real.exp 1),
    add_pos (mul_pos hCe ?_) hCl, ?_⟩
  · dsimp [Ctau, Inputs.tauSquareQuarterConstant]
    positivity
  intro X hX d a s hd hd_sqf hd_odd hdU ha hs hs_sqf hsd hsS
  have hXe : Xe ≤ X :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_max_left _ _)) hX
  have hXl : Xl ≤ X :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_left _ _)) hX
  have hXs : Xs ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X := le_trans (by norm_num) hXexp
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hsposN : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hsRpos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hsposN
  have hdRpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  let K := phiProgressionPowerCutoff (Params.explicit.σ / 2) X d s
  let N := ⌊phiProgressionU1 Params.explicit s X⌋₊
  let L := Real.log (phiProgressionU1 Params.explicit s X /
    phiProgressionU0 Params.explicit s X)
  let E := (1 / phiProgressionU0 Params.explicit s X) *
    ((harmonic N : ℚ) : ℝ) ^ 2
  have hsc := hendScalar X hXe d s (by omega) hdU hs hsS
  have hsqpos : 0 < (s : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_pos_of_pos hsRpos _
  have hEdiv : E ≤ Ce / ((d : ℝ) * (s : ℝ) ^ ((1 : ℝ) / 4)) := by
    apply (le_div_iff₀ (mul_pos hdRpos hsqpos)).2
    simpa [E, N, mul_assoc] using hsc
  have hEle :
      E ≤ Ce * ((1 : ℝ) / (d : ℝ)) *
        (s : ℝ) ^ (-((1 : ℝ) / 4)) := by
    calc
      E ≤ Ce / ((d : ℝ) * (s : ℝ) ^ ((1 : ℝ) / 4)) := hEdiv
      _ = Ce * ((1 : ℝ) / (d : ℝ)) *
          (s : ℝ) ^ (-((1 : ℝ) / 4)) := by
        rw [Real.rpow_neg hsRpos.le]
        field_simp [ne_of_gt hdRpos, ne_of_gt hsqpos]
  have hLone0 := hslant X hXs s hs hsS
  have hLone : 1 ≤ L := by
    simpa [L, log_phiProgressionU1_div_U0_eq_slantLogLength
      Params.explicit hXpos hsposN] using hLone0
  have hshape0 := phiProgressionAverageShape_lower_subpower
    Params.explicit hd hs (le_trans zero_le_one hLone0)
  have hshape :
      ((1 : ℝ) / (d : ℝ)) *
          ((1 / Ctau) * (s : ℝ) ^ (-((1 : ℝ) / 4))) * L ≤
        phiProgressionAverageShape Params.explicit X d s := by
    simpa [Ctau, L, log_phiProgressionU1_div_U0_eq_slantLogLength
      Params.explicit hXpos hsposN] using hshape0
  have hbase_nonneg :
      0 ≤ ((1 : ℝ) / (d : ℝ)) *
        (s : ℝ) ^ (-((1 : ℝ) / 4)) := by positivity
  have hbaseL :
      ((1 : ℝ) / (d : ℝ)) * (s : ℝ) ^ (-((1 : ℝ) / 4)) ≤
        ((1 : ℝ) / (d : ℝ)) *
          (s : ℝ) ^ (-((1 : ℝ) / 4)) * L := by
    nlinarith
  have hEshape :
      E ≤ (Ce * Ctau) * phiProgressionAverageShape Params.explicit X d s := by
    calc
      E ≤ Ce * ((1 : ℝ) / (d : ℝ)) *
          (s : ℝ) ^ (-((1 : ℝ) / 4)) := hEle
      _ ≤ Ce * (((1 : ℝ) / (d : ℝ)) *
          (s : ℝ) ^ (-((1 : ℝ) / 4)) * L) := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hbaseL hCe.le
      _ = (Ce * Ctau) * (((1 : ℝ) / (d : ℝ)) *
          ((1 / Ctau) * (s : ℝ) ^ (-((1 : ℝ) / 4))) * L) := by
        dsimp [Ctau, Inputs.tauSquareQuarterConstant]
        field_simp
        ring
      _ ≤ (Ce * Ctau) * phiProgressionAverageShape Params.explicit X d s :=
        mul_le_mul_of_nonneg_left hshape
          (mul_nonneg hCe.le (by
            dsimp [Ctau, Inputs.tauSquareQuarterConstant]
            positivity))
  have hlogtail :=
    hlog X hXl d a s hd hd_sqf hd_odd hdU ha hs hs_sqf hsd hsS
  have hU0pos := phiProgressionU0_pos Params.explicit hXpos hsposN
  have hdecomp :=
    phiOmegaSqEndpointLogTailSum_le_harmonic_endpoint_add_log
      Params.explicit X s K N hU0pos
  calc
    phiOmegaSqEndpointLogTailSum Params.explicit X s K N
      ≤ E + L * phiOmegaSqTailSum K N := by
        simpa [E, L] using hdecomp
    _ ≤ (Ce * Ctau) * phiProgressionAverageShape Params.explicit X d s +
        Cl * phiProgressionAverageShape Params.explicit X d s := by
      apply add_le_add hEshape
      simpa [K, N, L, mul_comm] using hlogtail
    _ = (Ce * Ctau + Cl) *
        phiProgressionAverageShape Params.explicit X d s := by ring

/-- Modulus-preserving endpoint/log absorption on the full tensor range. -/
def PhiOmegaSqEndpointLogTailAbsorptionForPowerCutoffYU
    (P : Params) (κ : ℝ) : Prop :=
  0 < κ ∧ P.η + κ < P.lam ∧
    ∃ Comega X₀ : ℝ, 0 < Comega ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d →
        (d : ℝ) ≤ YScale P X * UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          phiOmegaSqEndpointLogTailSumYU P X d s
              (phiProgressionPowerCutoff κ X d s)
              ⌊phiProgressionU1 P s X⌋₊ ≤
            Comega * phiProgressionAverageShape P X d s

/-- The full tensor-range endpoint/log absorption is unconditional for the
explicit manuscript parameters. -/
theorem explicit_phiOmegaSqEndpointLogTailAbsorptionYU :
    PhiOmegaSqEndpointLogTailAbsorptionForPowerCutoffYU
      Params.explicit (Params.explicit.σ / 2) := by
  rcases explicit_harmonic_endpoint_mul_wideModulus_conductor_quarter_bounded with
    ⟨Ce, Xe, hCe, hendScalar⟩
  rcases explicit_phiOmegaSqTail_mul_modulus_conductor_quarter_bounded with
    ⟨Ct, Xt, hCt, htailScalar⟩
  rcases slantLogLength_ge_one_eventually Params.explicit with ⟨Xs, hslant⟩
  let Ctau := Inputs.tauSquareQuarterConstant
  refine ⟨(by norm_num [Params.explicit]), (by norm_num [Params.explicit]),
    (Ce + Ct) * Ctau, max (max (max Xe Xt) Xs) (Real.exp 1),
    mul_pos (add_pos hCe hCt) ?_, ?_⟩
  · dsimp [Ctau, Inputs.tauSquareQuarterConstant]
    positivity
  intro X hX d a s hd _hd_sqf _hd_odd hdYU _ha hs _hs_sqf _hsd hsS
  have hXe : Xe ≤ X :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_max_left _ _)) hX
  have hXt : Xt ≤ X :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_left _ _)) hX
  have hXs : Xs ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X := le_trans (by norm_num) hXexp
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hlogone : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hXexp
  have hUone : (1 : ℝ) ≤ UScale X := by
    unfold UScale
    exact one_le_pow₀ hlogone
  have hsposN : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hsRpos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hsposN
  have hdRpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  let K := phiProgressionPowerCutoff (Params.explicit.σ / 2) X d s
  let N := ⌊phiProgressionU1 Params.explicit s X⌋₊
  let L := Real.log (phiProgressionU1 Params.explicit s X /
    phiProgressionU0 Params.explicit s X)
  let E := (1 / phiProgressionU0 Params.explicit s X) *
    ((harmonic N : ℚ) : ℝ) ^ 2
  let T := phiOmegaSqTailSum K N
  have hsc := hendScalar X hXe d s (by omega) hdYU hs hsS
  have hsqpos : 0 < (s : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_pos_of_pos hsRpos _
  have hEdiv : E ≤ Ce / ((d : ℝ) * (s : ℝ) ^ ((1 : ℝ) / 4)) := by
    apply (le_div_iff₀ (mul_pos hdRpos hsqpos)).2
    simpa [E, N, mul_assoc] using hsc
  have hEle :
      E ≤ Ce * ((1 : ℝ) / (d : ℝ)) *
        (s : ℝ) ^ (-((1 : ℝ) / 4)) := by
    calc
      E ≤ Ce / ((d : ℝ) * (s : ℝ) ^ ((1 : ℝ) / 4)) := hEdiv
      _ = Ce * ((1 : ℝ) / (d : ℝ)) *
          (s : ℝ) ^ (-((1 : ℝ) / 4)) := by
        rw [Real.rpow_neg hsRpos.le]
        field_simp [ne_of_gt hdRpos, ne_of_gt hsqpos]
  have htc0 := htailScalar X hXt 1 s N (by omega) (by simpa using hUone) hs hsS
  have htc : T * (s : ℝ) ^ ((1 : ℝ) / 4) ≤ Ct := by
    simpa [T, K, phiProgressionPowerCutoff] using htc0
  have hTle : T ≤ Ct * (s : ℝ) ^ (-((1 : ℝ) / 4)) := by
    rw [Real.rpow_neg hsRpos.le]
    apply (le_div_iff₀ hsqpos).2
    simpa [mul_comm] using htc
  have hLone0 := hslant X hXs s hs hsS
  have hLone : 1 ≤ L := by
    simpa [L, log_phiProgressionU1_div_U0_eq_slantLogLength
      Params.explicit hXpos hsposN] using hLone0
  have hshape0 := phiProgressionAverageShape_lower_subpower
    Params.explicit hd hs (le_trans zero_le_one hLone0)
  have hshape :
      ((1 : ℝ) / (d : ℝ)) *
          ((1 / Ctau) * (s : ℝ) ^ (-((1 : ℝ) / 4))) * L ≤
        phiProgressionAverageShape Params.explicit X d s := by
    simpa [Ctau, L, log_phiProgressionU1_div_U0_eq_slantLogLength
      Params.explicit hXpos hsposN] using hshape0
  have hbase_nonneg :
      0 ≤ ((1 : ℝ) / (d : ℝ)) *
        (s : ℝ) ^ (-((1 : ℝ) / 4)) := by positivity
  have hbaseL :
      ((1 : ℝ) / (d : ℝ)) * (s : ℝ) ^ (-((1 : ℝ) / 4)) ≤
        ((1 : ℝ) / (d : ℝ)) *
          (s : ℝ) ^ (-((1 : ℝ) / 4)) * L := by
    nlinarith
  have hEshape :
      E ≤ (Ce * Ctau) * phiProgressionAverageShape Params.explicit X d s := by
    calc
      E ≤ Ce * ((1 : ℝ) / (d : ℝ)) *
          (s : ℝ) ^ (-((1 : ℝ) / 4)) := hEle
      _ ≤ Ce * (((1 : ℝ) / (d : ℝ)) *
          (s : ℝ) ^ (-((1 : ℝ) / 4)) * L) := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hbaseL hCe.le
      _ = (Ce * Ctau) * (((1 : ℝ) / (d : ℝ)) *
          ((1 / Ctau) * (s : ℝ) ^ (-((1 : ℝ) / 4))) * L) := by
        dsimp [Ctau, Inputs.tauSquareQuarterConstant]
        field_simp
        ring
      _ ≤ (Ce * Ctau) * phiProgressionAverageShape Params.explicit X d s :=
        mul_le_mul_of_nonneg_left hshape
          (mul_nonneg hCe.le (by
            dsimp [Ctau, Inputs.tauSquareQuarterConstant]
            positivity))
  have hlogshape :
      ((1 / (d : ℝ)) * L) * T ≤
        (Ct * Ctau) * phiProgressionAverageShape Params.explicit X d s := by
    calc
      ((1 / (d : ℝ)) * L) * T
          ≤ ((1 / (d : ℝ)) * L) *
              (Ct * (s : ℝ) ^ (-((1 : ℝ) / 4))) :=
        mul_le_mul_of_nonneg_left hTle (by positivity)
      _ = (Ct * Ctau) * (((1 : ℝ) / (d : ℝ)) *
          ((1 / Ctau) * (s : ℝ) ^ (-((1 : ℝ) / 4))) * L) := by
        dsimp [Ctau, Inputs.tauSquareQuarterConstant]
        field_simp
        ring
      _ ≤ (Ct * Ctau) * phiProgressionAverageShape Params.explicit X d s :=
        mul_le_mul_of_nonneg_left hshape
          (mul_nonneg hCt.le (by
            dsimp [Ctau, Inputs.tauSquareQuarterConstant]
            positivity))
  have hU0pos := phiProgressionU0_pos Params.explicit hXpos hsposN
  have hdecomp :=
    phiOmegaSqEndpointLogTailSumYU_le_harmonic_endpoint_add_log
      Params.explicit X d s K N hU0pos
  calc
    phiOmegaSqEndpointLogTailSumYU Params.explicit X d s K N
      ≤ E + ((1 / (d : ℝ)) * L) * T := by
        simpa [E, T, L] using hdecomp
    _ ≤ (Ce * Ctau) * phiProgressionAverageShape Params.explicit X d s +
        (Ct * Ctau) * phiProgressionAverageShape Params.explicit X d s :=
      add_le_add hEshape hlogshape
    _ = ((Ce + Ct) * Ctau) *
        phiProgressionAverageShape Params.explicit X d s := by ring

/-- The manuscript's large-tail route implies the paper-facing power-cutoff
tail target: exact quotient-fiber identity, crude harmonic fiber bound, then
the one-dimensional square-coefficient tail absorption. -/
theorem PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff_of_crudeLogFiber_and_tailLogAbsorption
    {P : Params} {κ : ℝ}
    (hfiber : PhiProgressionQuotientFiberCrudeLogUpperForPowerCutoff P κ)
    (htail : PhiOmegaSqTailLogAbsorptionForPowerCutoff P κ) :
    PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff P κ := by
  rcases hfiber with ⟨hκ_pos, hκ_range, Cfib, Xfib, hCfib, hfiber_bound⟩
  rcases htail with ⟨_hκ_pos', _hκ_range', Comega, Xomega, hComega,
    htail_bound⟩
  refine ⟨hκ_pos, hκ_range, Cfib * Comega, max Xfib Xomega,
    mul_pos hCfib hComega, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  let K := phiProgressionPowerCutoff κ X d s
  let N := ⌊phiProgressionU1 P s X⌋₊
  let T := (Finset.Icc (1 : ℕ) N).filter (fun k => ¬ k ≤ K)
  let L := Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)
  have hXfib : Xfib ≤ X := le_trans (le_max_left _ _) hX
  have hXomega : Xomega ≤ X := le_trans (le_max_right _ _) hX
  have hweighted :
      phiProgressionOmegaLargeWeightedRecipFiberSum P X d a s K ≤
        phiOmegaSqTailSum K N * (Cfib * L) := by
    unfold phiProgressionOmegaLargeWeightedRecipFiberSum
      phiOmegaSqTailSum phiOmegaSqCoeff
    dsimp [K, N, T, L]
    calc
      (∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
          (fun k => ¬ k ≤ phiProgressionPowerCutoff κ X d s),
        (((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)) *
          phiProgressionFixedKQuotientRecipFiber P X d a s k)
          ≤
        ∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
          (fun k => ¬ k ≤ phiProgressionPowerCutoff κ X d s),
        (((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)) * (Cfib * L) := by
          apply Finset.sum_le_sum
          intro k hk
          have hcoeff_nonneg :
              0 ≤ ((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2) :=
            div_nonneg
              (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Inputs.omega k))
              (sq_nonneg (k : ℝ))
          exact mul_le_mul_of_nonneg_left
            (hfiber_bound X hXfib d a s hd_pos hd_sqf hd_odd hdU
              ha_coprime hs_one hs_sqf hs_coprime hsS k hk)
            hcoeff_nonneg
      _ =
        (∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
          (fun k => ¬ k ≤ phiProgressionPowerCutoff κ X d s),
          ((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)) * (Cfib * L) := by
          rw [Finset.sum_mul]
  calc
    phiProgressionGammaLargeTailMajorant P X d a s K
        = phiProgressionOmegaLargeWeightedRecipFiberSum P X d a s K :=
          phiProgressionGammaLargeTailMajorant_eq_omegaWeightedRecipFiberSum
            P X d a s K
    _ ≤ phiOmegaSqTailSum K N * (Cfib * L) := hweighted
    _ = Cfib * (phiOmegaSqTailSum K N * L) := by ring
    _ ≤ Cfib * (Comega * phiProgressionAverageShape P X d s) := by
          exact mul_le_mul_of_nonneg_left
            (htail_bound X hXomega d a s hd_pos hd_sqf hd_odd hdU
              ha_coprime hs_one hs_sqf hs_coprime hsS)
            hCfib.le
    _ = (Cfib * Comega) * phiProgressionAverageShape P X d s := by ring

/-- Corrected elementary large-tail bridge: the quotient-fiber carrier is
fully bounded by the endpoint-plus-log elementary expression, and the remaining
one-dimensional endpoint/log absorption supplies the paper-facing tail target. -/
theorem PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff_of_elementaryFiber_and_endpointLogAbsorption
    {P : Params} {κ : ℝ}
    (hfiber : PhiProgressionQuotientFiberElementaryUpperForPowerCutoff P κ)
    (htail : PhiOmegaSqEndpointLogTailAbsorptionForPowerCutoff P κ) :
    PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff P κ := by
  rcases hfiber with ⟨hκ_pos, hκ_range, Cfib, Xfib, hCfib, hfiber_bound⟩
  rcases htail with ⟨_hκ_pos', _hκ_range', Comega, Xomega, hComega,
    htail_bound⟩
  refine ⟨hκ_pos, hκ_range, Cfib * Comega, max Xfib Xomega,
    mul_pos hCfib hComega, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  let K := phiProgressionPowerCutoff κ X d s
  let N := ⌊phiProgressionU1 P s X⌋₊
  let E : ℕ → ℝ := fun k =>
    ((k : ℝ) * (1 / phiProgressionU0 P s X)) +
      Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)
  have hXfib : Xfib ≤ X := le_trans (le_max_left _ _) hX
  have hXomega : Xomega ≤ X := le_trans (le_max_right _ _) hX
  have hweighted :
      phiProgressionOmegaLargeWeightedRecipFiberSum P X d a s K ≤
        Cfib * phiOmegaSqEndpointLogTailSum P X s K N := by
    unfold phiProgressionOmegaLargeWeightedRecipFiberSum
      phiOmegaSqEndpointLogTailSum phiOmegaSqCoeff
    dsimp [K, N, E]
    calc
      (∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
          (fun k => ¬ k ≤ phiProgressionPowerCutoff κ X d s),
        (((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)) *
          phiProgressionFixedKQuotientRecipFiber P X d a s k)
          ≤
        ∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
          (fun k => ¬ k ≤ phiProgressionPowerCutoff κ X d s),
        (((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)) *
          (Cfib * (((k : ℝ) * (1 / phiProgressionU0 P s X)) +
            Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X))) := by
          apply Finset.sum_le_sum
          intro k hk
          have hcoeff_nonneg :
              0 ≤ ((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2) :=
            div_nonneg
              (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Inputs.omega k))
              (sq_nonneg (k : ℝ))
          exact mul_le_mul_of_nonneg_left
            (hfiber_bound X hXfib d a s hd_pos hd_sqf hd_odd hdU
              ha_coprime hs_one hs_sqf hs_coprime hsS k hk)
            hcoeff_nonneg
      _ =
        Cfib *
          (∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
            (fun k => ¬ k ≤ phiProgressionPowerCutoff κ X d s),
          ((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2) *
            (((k : ℝ) * (1 / phiProgressionU0 P s X)) +
              Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
  calc
    phiProgressionGammaLargeTailMajorant P X d a s K
        = phiProgressionOmegaLargeWeightedRecipFiberSum P X d a s K :=
          phiProgressionGammaLargeTailMajorant_eq_omegaWeightedRecipFiberSum
            P X d a s K
    _ ≤ Cfib * phiOmegaSqEndpointLogTailSum P X s K N := hweighted
    _ ≤ Cfib * (Comega * phiProgressionAverageShape P X d s) := by
          exact mul_le_mul_of_nonneg_left
            (htail_bound X hXomega d a s hd_pos hd_sqf hd_odd hdU
              ha_coprime hs_one hs_sqf hs_coprime hsS)
            hCfib.le
    _ = (Cfib * Comega) * phiProgressionAverageShape P X d s := by ring

/-- The corrected large-tail bridge with the elementary quotient-fiber side
already discharged.  The only remaining input is the endpoint-plus-log
one-dimensional tail absorption. -/
theorem PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff_of_endpointLogAbsorption
    {P : Params} {κ : ℝ}
    (hκ_pos : 0 < κ) (hκ_range : P.η + κ < P.lam)
    (htail : PhiOmegaSqEndpointLogTailAbsorptionForPowerCutoff P κ) :
    PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff P κ :=
  PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff_of_elementaryFiber_and_endpointLogAbsorption
    (PhiProgressionQuotientFiberElementaryUpperForPowerCutoff_concrete
      hκ_pos hκ_range)
    htail

/-- Fully checked large-quotient tail for the manuscript's explicit cutoff. -/
theorem explicit_phiProgressionGammaLargeTailMajorantUpper :
    PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff
      Params.explicit (Params.explicit.σ / 2) :=
  PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff_of_endpointLogAbsorption
    (by norm_num [Params.explicit])
    (by norm_num [Params.explicit])
    explicit_phiOmegaSqEndpointLogTailAbsorption

/-- Modulus-preserving large-tail bridge on the full tensor range. -/
theorem PhiProgressionGammaLargeTailMajorantUpperForPowerCutoffYU_of_elementaryFiber_and_endpointLogAbsorption
    {P : Params} {κ : ℝ}
    (hfiber : PhiProgressionQuotientFiberElementaryUpperForPowerCutoffYU P κ)
    (htail : PhiOmegaSqEndpointLogTailAbsorptionForPowerCutoffYU P κ) :
    PhiProgressionGammaLargeTailMajorantUpperForPowerCutoffYU P κ := by
  rcases hfiber with ⟨hκ_pos, hκ_range, Cfib, Xfib, hCfib, hfiber_bound⟩
  rcases htail with ⟨_hκ_pos', _hκ_range', Comega, Xomega, hComega,
    htail_bound⟩
  refine ⟨hκ_pos, hκ_range, Cfib * Comega, max Xfib Xomega,
    mul_pos hCfib hComega, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdYU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  let K := phiProgressionPowerCutoff κ X d s
  let N := ⌊phiProgressionU1 P s X⌋₊
  have hXfib : Xfib ≤ X := le_trans (le_max_left _ _) hX
  have hXomega : Xomega ≤ X := le_trans (le_max_right _ _) hX
  have hweighted :
      phiProgressionOmegaLargeWeightedRecipFiberSum P X d a s K ≤
        Cfib * phiOmegaSqEndpointLogTailSumYU P X d s K N := by
    unfold phiProgressionOmegaLargeWeightedRecipFiberSum
      phiOmegaSqEndpointLogTailSumYU phiOmegaSqCoeff
    dsimp [K, N]
    calc
      (∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
          (fun k => ¬ k ≤ phiProgressionPowerCutoff κ X d s),
        (((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)) *
          phiProgressionFixedKQuotientRecipFiber P X d a s k)
          ≤
        ∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
          (fun k => ¬ k ≤ phiProgressionPowerCutoff κ X d s),
        (((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)) *
          (Cfib * (((k : ℝ) * (1 / phiProgressionU0 P s X)) +
            (1 / (d : ℝ)) *
              Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X))) := by
          apply Finset.sum_le_sum
          intro k hk
          have hcoeff_nonneg :
              0 ≤ ((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2) :=
            div_nonneg
              (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Inputs.omega k))
              (sq_nonneg (k : ℝ))
          exact mul_le_mul_of_nonneg_left
            (hfiber_bound X hXfib d a s hd_pos hd_sqf hd_odd hdYU
              ha_coprime hs_one hs_sqf hs_coprime hsS k hk)
            hcoeff_nonneg
      _ = Cfib *
          (∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
            (fun k => ¬ k ≤ phiProgressionPowerCutoff κ X d s),
          ((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2) *
            (((k : ℝ) * (1 / phiProgressionU0 P s X)) +
              (1 / (d : ℝ)) *
                Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
  calc
    phiProgressionGammaLargeTailMajorant P X d a s K
        = phiProgressionOmegaLargeWeightedRecipFiberSum P X d a s K :=
          phiProgressionGammaLargeTailMajorant_eq_omegaWeightedRecipFiberSum
            P X d a s K
    _ ≤ Cfib * phiOmegaSqEndpointLogTailSumYU P X d s K N := hweighted
    _ ≤ Cfib * (Comega * phiProgressionAverageShape P X d s) := by
          exact mul_le_mul_of_nonneg_left
            (htail_bound X hXomega d a s hd_pos hd_sqf hd_odd hdYU
              ha_coprime hs_one hs_sqf hs_coprime hsS)
            hCfib.le
    _ = (Cfib * Comega) * phiProgressionAverageShape P X d s := by ring

/-- Fully checked large-quotient tail on the manuscript's full tensor modulus
range. -/
theorem explicit_phiProgressionGammaLargeTailMajorantUpperYU :
    PhiProgressionGammaLargeTailMajorantUpperForPowerCutoffYU
      Params.explicit (Params.explicit.σ / 2) :=
  PhiProgressionGammaLargeTailMajorantUpperForPowerCutoffYU_of_elementaryFiber_and_endpointLogAbsorption
    (PhiProgressionQuotientFiberElementaryUpperForPowerCutoffYU_concrete
      (by norm_num [Params.explicit]) (by norm_num [Params.explicit]))
    explicit_phiOmegaSqEndpointLogTailAbsorptionYU

/-- Power-cutoff version of the large-tail squarefree-reciprocal model target.
This is the model-side analogue of
`PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff`. -/
def PhiProgressionOmegaLargeSqfRecipAdmissibleInverseModelUpperForPowerCutoff
    (P : Params) (κ : ℝ) : Prop :=
  0 < κ ∧ P.η + κ < P.lam ∧
    ∃ Ctail X₀ : ℝ, 0 < Ctail ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          phiProgressionOmegaLargeSqfRecipAdmissibleInverseModelSum P X d a s
              (phiProgressionPowerCutoff κ X d s) ≤
            Ctail * phiProgressionAverageShape P X d s

/-- The power-cutoff model-side large-tail estimate supplies the original
power-cutoff raw-tail estimate. -/
theorem PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff_of_omegaLargeSqfRecipAdmissibleInverseModelUpperForPowerCutoff
    {P : Params} {κ : ℝ}
    (h : PhiProgressionOmegaLargeSqfRecipAdmissibleInverseModelUpperForPowerCutoff
      P κ) :
    PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff P κ := by
  rcases h with ⟨hκ_pos, hκ_range, Ctail, X₀, hCtail, hmodel⟩
  refine ⟨hκ_pos, hκ_range, Ctail, X₀, hCtail, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  exact le_trans
    (phiProgressionGammaLargeTailMajorant_le_omegaLargeSqfRecipAdmissibleInverseModelSum
      P X d a s (phiProgressionPowerCutoff κ X d s) hd_pos ha_coprime)
    (hmodel X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS)

/-- Power-cutoff model-side large-tail bound from the pointwise fixed-`k`
ordinary-density estimate and the one-dimensional `2^ω(k)/k²` tail bound.

Unlike the existential core version, this keeps the manuscript's common cutoff
`K=⌊X^κ⌋₊` fixed all the way through the proof. -/
theorem
    PhiProgressionOmegaLargeSqfRecipAdmissibleInverseModelUpperForPowerCutoff_of_fixedKPointwise_and_phiOmegaSqTailBound
    {P : Params} {κ : ℝ}
    (hκ_pos : 0 < κ) (hκ_range : P.η + κ < P.lam)
    (hfixed : PhiProgressionFixedKOrdinaryDensityUpper P)
    (homega : PhiOmegaSqTailBound) :
    PhiProgressionOmegaLargeSqfRecipAdmissibleInverseModelUpperForPowerCutoff P κ := by
  rcases hfixed with ⟨Csqf, Xfixed, hCsqf, hfixed_bound⟩
  rcases homega with ⟨Comega, hComega, htail⟩
  refine ⟨hκ_pos, hκ_range, Csqf * Comega, max Xfixed (Real.exp 1),
    mul_pos hCsqf hComega, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  have hXfixed : Xfixed ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hExpOne : (1 : ℝ) < Real.exp 1 := by
    calc
      (1 : ℝ) = Real.exp 0 := by simp
      _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
  have hXone : (1 : ℝ) < X := lt_of_lt_of_le hExpOne hXe
  have hXpos : 0 < X := lt_trans zero_lt_one hXone
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hU0 : 0 < phiProgressionU0 P s X :=
    phiProgressionU0_pos P hXpos hs_pos
  have hU01 : phiProgressionU0 P s X ≤ phiProgressionU1 P s X :=
    (phiProgressionU0_lt_U1_of_s_le_SScale P hXone hs_one hsS).le
  have hlog_nonneg :
      0 ≤ Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) :=
    log_phiProgressionU1_div_U0_nonneg P X s hU0 hU01
  have hscalar_nonneg :
      0 ≤ Csqf * ((1 / (d : ℝ)) *
        Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)) := by
    have hdR_nonneg : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_pos.le
    exact mul_nonneg hCsqf.le
      (mul_nonneg (div_nonneg zero_le_one hdR_nonneg) hlog_nonneg)
  have hratioS_nonneg :
      0 ≤ (Nat.totient s : ℝ) / (s : ℝ) := by
    have hsR_nonneg : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_pos.le
    exact div_nonneg
      (by exact_mod_cast Nat.zero_le (Nat.totient s)) hsR_nonneg
  have hcoeff_tail :
      phiProgressionOmegaLargeAdmissibleTotientCoeffSum d s
          (phiProgressionPowerCutoff κ X d s)
          ⌊phiProgressionU1 P s X⌋₊ ≤
        Comega * ((Nat.totient s : ℝ) / (s : ℝ)) :=
    le_trans
      (phiProgressionOmegaLargeAdmissibleTotientCoeffSum_le_phiOmegaSqTailSum_mul_totientRatio
        d s (phiProgressionPowerCutoff κ X d s)
        ⌊phiProgressionU1 P s X⌋₊ hs_pos)
      (mul_le_mul_of_nonneg_right
        (htail (phiProgressionPowerCutoff κ X d s)
          ⌊phiProgressionU1 P s X⌋₊)
        hratioS_nonneg)
  unfold phiProgressionOmegaLargeSqfRecipAdmissibleInverseModelSum
  calc
    (∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
        (fun k => ¬ k ≤ phiProgressionPowerCutoff κ X d s),
      if Nat.Coprime k d ∧ Nat.Coprime k s then
        (((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)) *
          Inputs.sqfRecip X (s * k) d (a * modInverseChoice d k)
            (phiProgressionU0 P s X / (k : ℝ))
            (phiProgressionU1 P s X / (k : ℝ))
      else 0)
      ≤
    (∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
        (fun k => ¬ k ≤ phiProgressionPowerCutoff κ X d s),
      if Nat.Coprime k d ∧ Nat.Coprime k s then
        (((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)) *
          (Csqf * (((1 : ℝ) / (d : ℝ)) *
            ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) *
              Real.log (phiProgressionU1 P s X /
                phiProgressionU0 P s X)))
      else 0) := by
        apply Finset.sum_le_sum
        intro k hk
        by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
        · have hkIcc :
              k ∈ Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊ :=
            (Finset.mem_filter.mp hk).1
          have hk_one : 1 ≤ k := (Finset.mem_Icc.mp hkIcc).1
          have hcoef_nonneg :
              0 ≤ ((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2) :=
            div_nonneg
              (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Inputs.omega k))
              (sq_nonneg (k : ℝ))
          have hsqf_le :
              Inputs.sqfRecip X (s * k) d (a * modInverseChoice d k)
                (phiProgressionU0 P s X / (k : ℝ))
                (phiProgressionU1 P s X / (k : ℝ)) ≤
                Csqf * (((1 : ℝ) / (d : ℝ)) *
                  ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) *
                    Real.log (phiProgressionU1 P s X /
                      phiProgressionU0 P s X)) :=
            hfixed_bound X hXfixed d a s hd_pos hd_sqf hd_odd hdU
              ha_coprime hs_one hs_sqf hs_coprime hsS k hk_one hadm
          rw [if_pos hadm, if_pos hadm]
          exact mul_le_mul_of_nonneg_left hsqf_le hcoef_nonneg
        · simp [hadm]
    _ =
      phiProgressionOmegaLargeAdmissibleTotientCoeffSum d s
          (phiProgressionPowerCutoff κ X d s)
          ⌊phiProgressionU1 P s X⌋₊ *
        (Csqf * ((1 / (d : ℝ)) *
          Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X))) := by
        unfold phiProgressionOmegaLargeAdmissibleTotientCoeffSum
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
        · rw [if_pos hadm, if_pos hadm]
          ring
        · simp [hadm]
    _ ≤ (Comega * ((Nat.totient s : ℝ) / (s : ℝ))) *
        (Csqf * ((1 / (d : ℝ)) *
          Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X))) :=
        mul_le_mul_of_nonneg_right hcoeff_tail hscalar_nonneg
    _ = (Csqf * Comega) * phiProgressionAverageShape P X d s := by
        unfold phiProgressionAverageShape
        rw [log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos]
        ring

/-- Power-cutoff model-side large-tail bound with the one-dimensional omega-square
tail fully discharged. -/
theorem
    PhiProgressionOmegaLargeSqfRecipAdmissibleInverseModelUpperForPowerCutoff_of_fixedKPointwise_concreteTail
    {P : Params} {κ : ℝ}
    (hκ_pos : 0 < κ) (hκ_range : P.η + κ < P.lam)
    (hfixed : PhiProgressionFixedKOrdinaryDensityUpper P) :
    PhiProgressionOmegaLargeSqfRecipAdmissibleInverseModelUpperForPowerCutoff P κ :=
  PhiProgressionOmegaLargeSqfRecipAdmissibleInverseModelUpperForPowerCutoff_of_fixedKPointwise_and_phiOmegaSqTailBound
    hκ_pos hκ_range hfixed PhiOmegaSqTailBound_concrete

/-- The pointwise fixed-`k` ordinary-density estimate supplies the manuscript's
matching power-cutoff large-tail target; the square-coefficient tail is already
closed by the Euler-product proof. -/
theorem PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff_of_fixedKPointwise_concreteOmegaTail
    {P : Params} {κ : ℝ}
    (hκ_pos : 0 < κ) (hκ_range : P.η + κ < P.lam)
    (hfixed : PhiProgressionFixedKOrdinaryDensityUpper P) :
    PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff P κ :=
  PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff_of_omegaLargeSqfRecipAdmissibleInverseModelUpperForPowerCutoff
    (PhiProgressionOmegaLargeSqfRecipAdmissibleInverseModelUpperForPowerCutoff_of_fixedKPointwise_concreteTail
      hκ_pos hκ_range hfixed)

/-- Large-tail bound from the generic ordinary squarefree progression upper
estimate on the actual large-tail range `k≤U₁`.

This avoids the overstrong pointwise all-`k` fixed-density hypothesis: the
ordinary estimate is used only for squarefree exposed divisors occurring in
the finite large-tail carrier; nonsquarefree and nonadmissible fibers are
already empty, and the remaining coefficient sum is the concrete
`2^ω(k)/k²` Euler-product tail. -/
theorem
    PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff_of_ordinaryUpper_wide_concreteOmegaTail
    {P : Params} {κ : ℝ}
    (hκ_pos : 0 < κ) (hκ_range : P.η + κ < P.lam)
    (hordinary :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff P κ := by
  rcases hordinary with ⟨Csqf, Xbase, hCsqf, hbound⟩
  rcases PhiOmegaSqTailBound_concrete with ⟨Comega, hComega, homega⟩
  refine ⟨hκ_pos, hκ_range, Csqf * Comega, max Xbase (Real.exp 1),
    mul_pos hCsqf hComega, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  let K := phiProgressionPowerCutoff κ X d s
  let N := ⌊phiProgressionU1 P s X⌋₊
  have hXbase : Xbase ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXexp
  have hXgtone : (1 : ℝ) < X :=
    lt_of_lt_of_le (by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)) hXexp
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hU0 : 0 < phiProgressionU0 P s X :=
    phiProgressionU0_pos P hXpos hs_pos
  have hU01_lt : phiProgressionU0 P s X < phiProgressionU1 P s X :=
    phiProgressionU0_lt_U1_of_s_le_SScale P hXgtone hs_one hsS
  have hlog_nonneg :
      0 ≤ Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) :=
    log_phiProgressionU1_div_U0_nonneg P X s hU0 hU01_lt.le
  have hslant_nonneg : 0 ≤ slantLogLength P s X := by
    rw [← log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos]
    exact hlog_nonneg
  have hshape_nonneg : 0 ≤ phiProgressionAverageShape P X d s := by
    have hdR_nonneg : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_pos.le
    have hsR_nonneg : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_pos.le
    unfold phiProgressionAverageShape
    exact mul_nonneg
      (mul_nonneg (div_nonneg zero_le_one hdR_nonneg)
        (div_nonneg (by exact_mod_cast Nat.zero_le (Nat.totient s)) hsR_nonneg))
      hslant_nonneg
  have hscalar_nonneg : 0 ≤ Csqf * phiProgressionAverageShape P X d s :=
    mul_nonneg hCsqf.le hshape_nonneg
  have hweighted :
      phiProgressionOmegaLargeWeightedRecipFiberSum P X d a s K ≤
        phiOmegaSqTailSum K N * (Csqf * phiProgressionAverageShape P X d s) := by
    unfold phiProgressionOmegaLargeWeightedRecipFiberSum
      phiOmegaSqTailSum phiOmegaSqCoeff
    dsimp [K, N]
    calc
      (∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
          (fun k => ¬ k ≤ phiProgressionPowerCutoff κ X d s),
        (((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)) *
          phiProgressionFixedKQuotientRecipFiber P X d a s k)
          ≤
        ∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
          (fun k => ¬ k ≤ phiProgressionPowerCutoff κ X d s),
        (((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)) *
          (Csqf * phiProgressionAverageShape P X d s) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkIcc :
              k ∈ Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊ :=
            (Finset.mem_filter.mp hk).1
          have hk_one : 1 ≤ k := (Finset.mem_Icc.mp hkIcc).1
          have hk_floor : k ≤ ⌊phiProgressionU1 P s X⌋₊ :=
            (Finset.mem_Icc.mp hkIcc).2
          have hk_pos_nat : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk_one
          have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos_nat
          have hcoef_nonneg :
              0 ≤ ((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2) :=
            div_nonneg
              (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Inputs.omega k))
              (sq_nonneg (k : ℝ))
          by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
          · by_cases hk_sqf : Squarefree k
            · have hM_sqf : Squarefree (s * k) :=
                (Nat.squarefree_mul hadm.2.symm).mpr ⟨hs_sqf, hk_sqf⟩
              have hM_coprime_d : Nat.Coprime (s * k) d :=
                hs_coprime.mul hadm.1
              have hb_coprime_d : Nat.Coprime (a * modInverseChoice d k) d :=
                ha_coprime.mul (modInverseChoice_value_coprime hd_pos hadm.1)
              have hM_scale :
                  ((s * k : ℕ) : ℝ) ≤ X ^ P.θ :=
                phiProgression_sk_le_rpow_theta_of_le_floor_U1
                  P hXpos hs_one hk_floor
              have hU0_scale :
                  X ^ (P.lam - P.θ) ≤
                    phiProgressionU0 P s X / (k : ℝ) :=
                phiProgressionU0_div_nat_ge_rpow_lam_sub_theta_of_le_floor_U1
                  P hXone hs_one hk_one hk_floor
              have hU1_scale :
                  phiProgressionU1 P s X / (k : ℝ) ≤ X ^ P.θ :=
                phiProgressionU1_div_nat_le_rpow_theta P hXpos hs_one hk_one
              have hU01 :
                  phiProgressionU0 P s X / (k : ℝ) <
                    phiProgressionU1 P s X / (k : ℝ) :=
                div_lt_div_of_pos_right hU01_lt hk_pos
              have hlog_arg :
                  (phiProgressionU1 P s X / (k : ℝ)) /
                      (phiProgressionU0 P s X / (k : ℝ)) =
                    phiProgressionU1 P s X / phiProgressionU0 P s X := by
                field_simp [ne_of_gt hk_pos, ne_of_gt hU0]
              have hfiber_le_sqf :
                  phiProgressionFixedKQuotientRecipFiber P X d a s k ≤
                    Inputs.sqfRecip X (s * k) d
                      (a * modInverseChoice d k)
                      (phiProgressionU0 P s X / (k : ℝ))
                      (phiProgressionU1 P s X / (k : ℝ)) :=
                phiProgressionFixedKQuotientRecipFiber_le_sqfRecip_of_inverse
                  P X d a s k (modInverseChoice d k) hk_pos_nat
                  (modInverseChoice_coprime hd_pos hadm.1)
              have hsqf_le :
                  Inputs.sqfRecip X (s * k) d
                      (a * modInverseChoice d k)
                      (phiProgressionU0 P s X / (k : ℝ))
                      (phiProgressionU1 P s X / (k : ℝ)) ≤
                    Csqf * (((1 : ℝ) / (d : ℝ)) *
                      ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) *
                      Real.log (phiProgressionU1 P s X /
                        phiProgressionU0 P s X)) := by
                have hraw :=
                  hbound X hXbase (s * k) d
                    (a * modInverseChoice d k)
                    hd_pos hM_sqf hd_sqf hM_coprime_d hb_coprime_d
                    hM_scale hdU
                    (phiProgressionU0 P s X / (k : ℝ))
                    (phiProgressionU1 P s X / (k : ℝ))
                    hU0_scale hU01 hU1_scale
                simpa [Nat.cast_mul, hlog_arg] using hraw
              have hlocal_le_shape :
                  ((1 : ℝ) / (d : ℝ)) *
                      ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) *
                      Real.log (phiProgressionU1 P s X /
                        phiProgressionU0 P s X) ≤
                    phiProgressionAverageShape P X d s := by
                simpa [phiProgressionAverageShape,
                  log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos]
                  using
                    (one_div_modulus_mul_totient_mul_ratio_log_le_left_of_coprime
                      (d := d) (s := s) (k := k)
                      (L := Real.log (phiProgressionU1 P s X /
                        phiProgressionU0 P s X))
                      hd_pos hs_pos hk_pos_nat hadm.2.symm hlog_nonneg)
              have hfiber_le_shape :
                  phiProgressionFixedKQuotientRecipFiber P X d a s k ≤
                    Csqf * phiProgressionAverageShape P X d s :=
                le_trans hfiber_le_sqf
                  (le_trans hsqf_le
                    (mul_le_mul_of_nonneg_left hlocal_le_shape hCsqf.le))
              exact mul_le_mul_of_nonneg_left hfiber_le_shape hcoef_nonneg
            · rw [phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_squarefree
                P X d a s k hk_sqf, mul_zero]
              exact mul_nonneg hcoef_nonneg hscalar_nonneg
          · by_cases hkd : Nat.Coprime k d
            · have hks : ¬ Nat.Coprime k s := by
                intro hks
                exact hadm ⟨hkd, hks⟩
              rw [phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_coprime_s
                P X d a s k hks, mul_zero]
              exact mul_nonneg hcoef_nonneg hscalar_nonneg
            · rw [phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_coprime_d
                P X d a s k ha_coprime hkd, mul_zero]
              exact mul_nonneg hcoef_nonneg hscalar_nonneg
      _ =
        (∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
          (fun k => ¬ k ≤ phiProgressionPowerCutoff κ X d s),
          ((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)) *
            (Csqf * phiProgressionAverageShape P X d s) := by
          rw [Finset.sum_mul]
  calc
    phiProgressionGammaLargeTailMajorant P X d a s K
        = phiProgressionOmegaLargeWeightedRecipFiberSum P X d a s K :=
          phiProgressionGammaLargeTailMajorant_eq_omegaWeightedRecipFiberSum
            P X d a s K
    _ ≤ phiOmegaSqTailSum K N *
          (Csqf * phiProgressionAverageShape P X d s) := hweighted
    _ ≤ Comega * (Csqf * phiProgressionAverageShape P X d s) :=
          mul_le_mul_of_nonneg_right (homega K N) hscalar_nonneg
    _ = (Csqf * Comega) * phiProgressionAverageShape P X d s := by ring

/-- Long-window version of the ordinary-density large-tail bridge.

The ordinary-squarefree upper input is consumed only on quotient intervals
arising from the phi-progressions.  On those intervals the long-window
hypothesis is not an extra assumption: after scaling by `k`, the quotient is
still `U₁/U₀`, and the checked phi-window estimate gives
`U₁/U₀ ≥ X^(θ-λ-η)`. -/
theorem
    PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff_of_ordinaryUpperLong_wide_concreteOmegaTail
    {P : Params} {κ : ℝ}
    (hκ_pos : 0 < κ) (hκ_range : P.η + κ < P.lam)
    (hordinary :
      OrdinarySquarefreeProgressionCoprimeDensityUpperLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ) :
    PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff P κ := by
  rcases hordinary with ⟨Csqf, Xbase, hCsqf, hbound⟩
  rcases PhiOmegaSqTailBound_concrete with ⟨Comega, hComega, homega⟩
  refine ⟨hκ_pos, hκ_range, Csqf * Comega, max Xbase (Real.exp 1),
    mul_pos hCsqf hComega, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  let K := phiProgressionPowerCutoff κ X d s
  let N := ⌊phiProgressionU1 P s X⌋₊
  have hXbase : Xbase ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXexp
  have hXgtone : (1 : ℝ) < X :=
    lt_of_lt_of_le (by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)) hXexp
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hU0 : 0 < phiProgressionU0 P s X :=
    phiProgressionU0_pos P hXpos hs_pos
  have hU01_lt : phiProgressionU0 P s X < phiProgressionU1 P s X :=
    phiProgressionU0_lt_U1_of_s_le_SScale P hXgtone hs_one hsS
  have hlog_nonneg :
      0 ≤ Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) :=
    log_phiProgressionU1_div_U0_nonneg P X s hU0 hU01_lt.le
  have hslant_nonneg : 0 ≤ slantLogLength P s X := by
    rw [← log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos]
    exact hlog_nonneg
  have hshape_nonneg : 0 ≤ phiProgressionAverageShape P X d s := by
    have hdR_nonneg : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_pos.le
    have hsR_nonneg : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_pos.le
    unfold phiProgressionAverageShape
    exact mul_nonneg
      (mul_nonneg (div_nonneg zero_le_one hdR_nonneg)
        (div_nonneg (by exact_mod_cast Nat.zero_le (Nat.totient s)) hsR_nonneg))
      hslant_nonneg
  have hscalar_nonneg : 0 ≤ Csqf * phiProgressionAverageShape P X d s :=
    mul_nonneg hCsqf.le hshape_nonneg
  have hweighted :
      phiProgressionOmegaLargeWeightedRecipFiberSum P X d a s K ≤
        phiOmegaSqTailSum K N * (Csqf * phiProgressionAverageShape P X d s) := by
    unfold phiProgressionOmegaLargeWeightedRecipFiberSum
      phiOmegaSqTailSum phiOmegaSqCoeff
    dsimp [K, N]
    calc
      (∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
          (fun k => ¬ k ≤ phiProgressionPowerCutoff κ X d s),
        (((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)) *
          phiProgressionFixedKQuotientRecipFiber P X d a s k)
          ≤
        ∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
          (fun k => ¬ k ≤ phiProgressionPowerCutoff κ X d s),
        (((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)) *
          (Csqf * phiProgressionAverageShape P X d s) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkIcc :
              k ∈ Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊ :=
            (Finset.mem_filter.mp hk).1
          have hk_one : 1 ≤ k := (Finset.mem_Icc.mp hkIcc).1
          have hk_floor : k ≤ ⌊phiProgressionU1 P s X⌋₊ :=
            (Finset.mem_Icc.mp hkIcc).2
          have hk_pos_nat : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk_one
          have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos_nat
          have hcoef_nonneg :
              0 ≤ ((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2) :=
            div_nonneg
              (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Inputs.omega k))
              (sq_nonneg (k : ℝ))
          by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
          · by_cases hk_sqf : Squarefree k
            · have hM_sqf : Squarefree (s * k) :=
                (Nat.squarefree_mul hadm.2.symm).mpr ⟨hs_sqf, hk_sqf⟩
              have hM_coprime_d : Nat.Coprime (s * k) d :=
                hs_coprime.mul hadm.1
              have hb_coprime_d : Nat.Coprime (a * modInverseChoice d k) d :=
                ha_coprime.mul (modInverseChoice_value_coprime hd_pos hadm.1)
              have hM_scale :
                  ((s * k : ℕ) : ℝ) ≤ X ^ P.θ :=
                phiProgression_sk_le_rpow_theta_of_le_floor_U1
                  P hXpos hs_one hk_floor
              have hU0_scale :
                  X ^ (P.lam - P.θ) ≤
                    phiProgressionU0 P s X / (k : ℝ) :=
                phiProgressionU0_div_nat_ge_rpow_lam_sub_theta_of_le_floor_U1
                  P hXone hs_one hk_one hk_floor
              have hU1_scale :
                  phiProgressionU1 P s X / (k : ℝ) ≤ X ^ P.θ :=
                phiProgressionU1_div_nat_le_rpow_theta P hXpos hs_one hk_one
              have hU01 :
                  phiProgressionU0 P s X / (k : ℝ) <
                    phiProgressionU1 P s X / (k : ℝ) :=
                div_lt_div_of_pos_right hU01_lt hk_pos
              have hU1_nonneg : 0 ≤ phiProgressionU1 P s X :=
                (hU0.trans hU01_lt).le
              have hk_real_le : (k : ℝ) ≤ phiProgressionU1 P s X :=
                (Nat.le_floor_iff hU1_nonneg).mp hk_floor
              have hU1_one :
                  (1 : ℝ) ≤ phiProgressionU1 P s X / (k : ℝ) := by
                calc
                  (1 : ℝ) = (k : ℝ) / (k : ℝ) := by
                    field_simp [ne_of_gt hk_pos]
                  _ ≤ phiProgressionU1 P s X / (k : ℝ) :=
                    div_le_div_of_nonneg_right hk_real_le hk_pos.le
              have hlog_arg :
                  (phiProgressionU1 P s X / (k : ℝ)) /
                      (phiProgressionU0 P s X / (k : ℝ)) =
                    phiProgressionU1 P s X / phiProgressionU0 P s X := by
                field_simp [ne_of_gt hk_pos, ne_of_gt hU0]
              have hratio_base :
                  X ^ (P.θ - P.lam - P.η) ≤
                    phiProgressionU1 P s X / phiProgressionU0 P s X :=
                phiProgression_ratio_ge_rpow_theta_sub_lam_sub_eta
                  P hXone hs_one hsS
              have hratio :
                  X ^ (P.θ - P.lam - P.η) ≤
                    (phiProgressionU1 P s X / (k : ℝ)) /
                      (phiProgressionU0 P s X / (k : ℝ)) := by
                rw [hlog_arg]
                exact hratio_base
              have hfiber_le_sqf :
                  phiProgressionFixedKQuotientRecipFiber P X d a s k ≤
                    Inputs.sqfRecip X (s * k) d
                      (a * modInverseChoice d k)
                      (phiProgressionU0 P s X / (k : ℝ))
                      (phiProgressionU1 P s X / (k : ℝ)) :=
                phiProgressionFixedKQuotientRecipFiber_le_sqfRecip_of_inverse
                  P X d a s k (modInverseChoice d k) hk_pos_nat
                  (modInverseChoice_coprime hd_pos hadm.1)
              have hsqf_le :
                  Inputs.sqfRecip X (s * k) d
                      (a * modInverseChoice d k)
                      (phiProgressionU0 P s X / (k : ℝ))
                      (phiProgressionU1 P s X / (k : ℝ)) ≤
                    Csqf * (((1 : ℝ) / (d : ℝ)) *
                      ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) *
                      Real.log (phiProgressionU1 P s X /
                        phiProgressionU0 P s X)) := by
                have hraw :=
                  hbound X hXbase (s * k) d
                    (a * modInverseChoice d k)
                    hd_pos hM_sqf hd_sqf hM_coprime_d hb_coprime_d
                    hM_scale hdU
                    (phiProgressionU0 P s X / (k : ℝ))
                    (phiProgressionU1 P s X / (k : ℝ))
                    hU0_scale hU01 hU1_one hU1_scale hratio
                simpa [Nat.cast_mul, hlog_arg] using hraw
              have hlocal_le_shape :
                  ((1 : ℝ) / (d : ℝ)) *
                      ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) *
                      Real.log (phiProgressionU1 P s X /
                        phiProgressionU0 P s X) ≤
                    phiProgressionAverageShape P X d s := by
                simpa [phiProgressionAverageShape,
                  log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos]
                  using
                    (one_div_modulus_mul_totient_mul_ratio_log_le_left_of_coprime
                      (d := d) (s := s) (k := k)
                      (L := Real.log (phiProgressionU1 P s X /
                        phiProgressionU0 P s X))
                      hd_pos hs_pos hk_pos_nat hadm.2.symm hlog_nonneg)
              have hfiber_le_shape :
                  phiProgressionFixedKQuotientRecipFiber P X d a s k ≤
                    Csqf * phiProgressionAverageShape P X d s :=
                le_trans hfiber_le_sqf
                  (le_trans hsqf_le
                    (mul_le_mul_of_nonneg_left hlocal_le_shape hCsqf.le))
              exact mul_le_mul_of_nonneg_left hfiber_le_shape hcoef_nonneg
            · rw [phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_squarefree
                P X d a s k hk_sqf, mul_zero]
              exact mul_nonneg hcoef_nonneg hscalar_nonneg
          · by_cases hkd : Nat.Coprime k d
            · have hks : ¬ Nat.Coprime k s := by
                intro hks
                exact hadm ⟨hkd, hks⟩
              rw [phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_coprime_s
                P X d a s k hks, mul_zero]
              exact mul_nonneg hcoef_nonneg hscalar_nonneg
            · rw [phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_coprime_d
                P X d a s k ha_coprime hkd, mul_zero]
              exact mul_nonneg hcoef_nonneg hscalar_nonneg
      _ =
        (∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
          (fun k => ¬ k ≤ phiProgressionPowerCutoff κ X d s),
          ((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)) *
            (Csqf * phiProgressionAverageShape P X d s) := by
          rw [Finset.sum_mul]
  calc
    phiProgressionGammaLargeTailMajorant P X d a s K
        = phiProgressionOmegaLargeWeightedRecipFiberSum P X d a s K :=
          phiProgressionGammaLargeTailMajorant_eq_omegaWeightedRecipFiberSum
            P X d a s K
    _ ≤ phiOmegaSqTailSum K N *
          (Csqf * phiProgressionAverageShape P X d s) := hweighted
    _ ≤ Comega * (Csqf * phiProgressionAverageShape P X d s) :=
          mul_le_mul_of_nonneg_right (homega K N) hscalar_nonneg
    _ = (Csqf * Comega) * phiProgressionAverageShape P X d s := by ring

/-- Wide-modulus version of the ordinary-density large-tail bridge.

This is the tensor-range analogue of
`PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff_of_ordinaryUpper_wide_concreteOmegaTail`:
the only external input is the cited ordinary squarefree progression upper
bound on `D≤YU`; the gamma coefficient tail itself is the concrete
Euler-product bound. -/
theorem
    PhiProgressionGammaLargeTailMajorantUpperForPowerCutoffYU_of_ordinaryUpper_wide_concreteOmegaTail
    {P : Params} {κ : ℝ}
    (hκ_pos : 0 < κ) (hκ_range : P.η + κ < P.lam)
    (hordinary :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ) :
    PhiProgressionGammaLargeTailMajorantUpperForPowerCutoffYU P κ := by
  rcases hordinary with ⟨Csqf, Xbase, hCsqf, hbound⟩
  rcases PhiOmegaSqTailBound_concrete with ⟨Comega, hComega, homega⟩
  refine ⟨hκ_pos, hκ_range, Csqf * Comega, max Xbase (Real.exp 1),
    mul_pos hCsqf hComega, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdYU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  let K := phiProgressionPowerCutoff κ X d s
  let N := ⌊phiProgressionU1 P s X⌋₊
  have hXbase : Xbase ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXexp
  have hXgtone : (1 : ℝ) < X :=
    lt_of_lt_of_le (by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)) hXexp
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hU0 : 0 < phiProgressionU0 P s X :=
    phiProgressionU0_pos P hXpos hs_pos
  have hU01_lt : phiProgressionU0 P s X < phiProgressionU1 P s X :=
    phiProgressionU0_lt_U1_of_s_le_SScale P hXgtone hs_one hsS
  have hlog_nonneg :
      0 ≤ Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) :=
    log_phiProgressionU1_div_U0_nonneg P X s hU0 hU01_lt.le
  have hslant_nonneg : 0 ≤ slantLogLength P s X := by
    rw [← log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos]
    exact hlog_nonneg
  have hshape_nonneg : 0 ≤ phiProgressionAverageShape P X d s := by
    have hdR_nonneg : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_pos.le
    have hsR_nonneg : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_pos.le
    unfold phiProgressionAverageShape
    exact mul_nonneg
      (mul_nonneg (div_nonneg zero_le_one hdR_nonneg)
        (div_nonneg (by exact_mod_cast Nat.zero_le (Nat.totient s)) hsR_nonneg))
      hslant_nonneg
  have hscalar_nonneg : 0 ≤ Csqf * phiProgressionAverageShape P X d s :=
    mul_nonneg hCsqf.le hshape_nonneg
  have hweighted :
      phiProgressionOmegaLargeWeightedRecipFiberSum P X d a s K ≤
        phiOmegaSqTailSum K N * (Csqf * phiProgressionAverageShape P X d s) := by
    unfold phiProgressionOmegaLargeWeightedRecipFiberSum
      phiOmegaSqTailSum phiOmegaSqCoeff
    dsimp [K, N]
    calc
      (∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
          (fun k => ¬ k ≤ phiProgressionPowerCutoff κ X d s),
        (((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)) *
          phiProgressionFixedKQuotientRecipFiber P X d a s k)
          ≤
        ∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
          (fun k => ¬ k ≤ phiProgressionPowerCutoff κ X d s),
        (((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)) *
          (Csqf * phiProgressionAverageShape P X d s) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkIcc :
              k ∈ Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊ :=
            (Finset.mem_filter.mp hk).1
          have hk_one : 1 ≤ k := (Finset.mem_Icc.mp hkIcc).1
          have hk_floor : k ≤ ⌊phiProgressionU1 P s X⌋₊ :=
            (Finset.mem_Icc.mp hkIcc).2
          have hk_pos_nat : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk_one
          have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos_nat
          have hcoef_nonneg :
              0 ≤ ((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2) :=
            div_nonneg
              (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Inputs.omega k))
              (sq_nonneg (k : ℝ))
          by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
          · by_cases hk_sqf : Squarefree k
            · have hM_sqf : Squarefree (s * k) :=
                (Nat.squarefree_mul hadm.2.symm).mpr ⟨hs_sqf, hk_sqf⟩
              have hM_coprime_d : Nat.Coprime (s * k) d :=
                hs_coprime.mul hadm.1
              have hb_coprime_d : Nat.Coprime (a * modInverseChoice d k) d :=
                ha_coprime.mul (modInverseChoice_value_coprime hd_pos hadm.1)
              have hM_scale :
                  ((s * k : ℕ) : ℝ) ≤ X ^ P.θ :=
                phiProgression_sk_le_rpow_theta_of_le_floor_U1
                  P hXpos hs_one hk_floor
              have hU0_scale :
                  X ^ (P.lam - P.θ) ≤
                    phiProgressionU0 P s X / (k : ℝ) :=
                phiProgressionU0_div_nat_ge_rpow_lam_sub_theta_of_le_floor_U1
                  P hXone hs_one hk_one hk_floor
              have hU1_scale :
                  phiProgressionU1 P s X / (k : ℝ) ≤ X ^ P.θ :=
                phiProgressionU1_div_nat_le_rpow_theta P hXpos hs_one hk_one
              have hU01 :
                  phiProgressionU0 P s X / (k : ℝ) <
                    phiProgressionU1 P s X / (k : ℝ) :=
                div_lt_div_of_pos_right hU01_lt hk_pos
              have hU1_nonneg : 0 ≤ phiProgressionU1 P s X :=
                (hU0.trans hU01_lt).le
              have hk_real_le : (k : ℝ) ≤ phiProgressionU1 P s X :=
                (Nat.le_floor_iff hU1_nonneg).mp hk_floor
              have hU1_one :
                  (1 : ℝ) ≤ phiProgressionU1 P s X / (k : ℝ) := by
                calc
                  (1 : ℝ) = (k : ℝ) / (k : ℝ) := by
                    field_simp [ne_of_gt hk_pos]
                  _ ≤ phiProgressionU1 P s X / (k : ℝ) :=
                    div_le_div_of_nonneg_right hk_real_le hk_pos.le
              have hlog_arg :
                  (phiProgressionU1 P s X / (k : ℝ)) /
                      (phiProgressionU0 P s X / (k : ℝ)) =
                    phiProgressionU1 P s X / phiProgressionU0 P s X := by
                field_simp [ne_of_gt hk_pos, ne_of_gt hU0]
              have hratio_base :
                  X ^ (P.θ - P.lam - P.η) ≤
                    phiProgressionU1 P s X / phiProgressionU0 P s X :=
                phiProgression_ratio_ge_rpow_theta_sub_lam_sub_eta
                  P hXone hs_one hsS
              have hratio :
                  X ^ (P.θ - P.lam - P.η) ≤
                    (phiProgressionU1 P s X / (k : ℝ)) /
                      (phiProgressionU0 P s X / (k : ℝ)) := by
                rw [hlog_arg]
                exact hratio_base
              have hfiber_le_sqf :
                  phiProgressionFixedKQuotientRecipFiber P X d a s k ≤
                    Inputs.sqfRecip X (s * k) d
                      (a * modInverseChoice d k)
                      (phiProgressionU0 P s X / (k : ℝ))
                      (phiProgressionU1 P s X / (k : ℝ)) :=
                phiProgressionFixedKQuotientRecipFiber_le_sqfRecip_of_inverse
                  P X d a s k (modInverseChoice d k) hk_pos_nat
                  (modInverseChoice_coprime hd_pos hadm.1)
              have hsqf_le :
                  Inputs.sqfRecip X (s * k) d
                      (a * modInverseChoice d k)
                      (phiProgressionU0 P s X / (k : ℝ))
                      (phiProgressionU1 P s X / (k : ℝ)) ≤
                    Csqf * (((1 : ℝ) / (d : ℝ)) *
                      ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) *
                      Real.log (phiProgressionU1 P s X /
                        phiProgressionU0 P s X)) := by
                have hraw :=
                  hbound X hXbase (s * k) d
                    (a * modInverseChoice d k)
                    hd_pos hM_sqf hd_sqf hM_coprime_d hb_coprime_d
                    hM_scale hdYU
                    (phiProgressionU0 P s X / (k : ℝ))
                    (phiProgressionU1 P s X / (k : ℝ))
                    hU0_scale hU01 hU1_one hU1_scale hratio
                simpa [Nat.cast_mul, hlog_arg] using hraw
              have hlocal_le_shape :
                  ((1 : ℝ) / (d : ℝ)) *
                      ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) *
                      Real.log (phiProgressionU1 P s X /
                        phiProgressionU0 P s X) ≤
                    phiProgressionAverageShape P X d s := by
                simpa [phiProgressionAverageShape,
                  log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos]
                  using
                    (one_div_modulus_mul_totient_mul_ratio_log_le_left_of_coprime
                      (d := d) (s := s) (k := k)
                      (L := Real.log (phiProgressionU1 P s X /
                        phiProgressionU0 P s X))
                      hd_pos hs_pos hk_pos_nat hadm.2.symm hlog_nonneg)
              have hfiber_le_shape :
                  phiProgressionFixedKQuotientRecipFiber P X d a s k ≤
                    Csqf * phiProgressionAverageShape P X d s :=
                le_trans hfiber_le_sqf
                  (le_trans hsqf_le
                    (mul_le_mul_of_nonneg_left hlocal_le_shape hCsqf.le))
              exact mul_le_mul_of_nonneg_left hfiber_le_shape hcoef_nonneg
            · rw [phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_squarefree
                P X d a s k hk_sqf, mul_zero]
              exact mul_nonneg hcoef_nonneg hscalar_nonneg
          · by_cases hkd : Nat.Coprime k d
            · have hks : ¬ Nat.Coprime k s := by
                intro hks
                exact hadm ⟨hkd, hks⟩
              rw [phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_coprime_s
                P X d a s k hks, mul_zero]
              exact mul_nonneg hcoef_nonneg hscalar_nonneg
            · rw [phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_coprime_d
                P X d a s k ha_coprime hkd, mul_zero]
              exact mul_nonneg hcoef_nonneg hscalar_nonneg
      _ =
        (∑ k ∈ (Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊).filter
          (fun k => ¬ k ≤ phiProgressionPowerCutoff κ X d s),
          ((2 : ℝ) ^ Inputs.omega k) / ((k : ℝ) ^ 2)) *
            (Csqf * phiProgressionAverageShape P X d s) := by
          rw [Finset.sum_mul]
  calc
    phiProgressionGammaLargeTailMajorant P X d a s K
        = phiProgressionOmegaLargeWeightedRecipFiberSum P X d a s K :=
          phiProgressionGammaLargeTailMajorant_eq_omegaWeightedRecipFiberSum
            P X d a s K
    _ ≤ phiOmegaSqTailSum K N *
          (Csqf * phiProgressionAverageShape P X d s) := hweighted
    _ ≤ Comega * (Csqf * phiProgressionAverageShape P X d s) :=
          mul_le_mul_of_nonneg_right (homega K N) hscalar_nonneg
    _ = (Csqf * Comega) * phiProgressionAverageShape P X d s := by ring

/-- The power-cutoff model-side large-tail estimate supplies the generic
model-side large-tail core at the concrete cutoff `⌊X^κ⌋₊`. -/
theorem PhiProgressionOmegaLargeSqfRecipAdmissibleInverseModelUpperCore_of_powerCutoff
    {P : Params} {κ : ℝ}
    (h : PhiProgressionOmegaLargeSqfRecipAdmissibleInverseModelUpperForPowerCutoff
      P κ) :
    PhiProgressionOmegaLargeSqfRecipAdmissibleInverseModelUpperCore P := by
  rcases h with ⟨_hκ_pos, _hκ_range, Ctail, X₀, hCtail, htail⟩
  exact ⟨phiProgressionPowerCutoff κ, Ctail, X₀, hCtail, htail⟩

/-- The paper's power-cutoff tail target supplies the generic large-tail core
at the concrete cutoff `⌊X^κ⌋₊`. -/
theorem PhiProgressionGammaLargeTailMajorantUpperCore_of_powerCutoff
    {P : Params} {κ : ℝ}
    (h : PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff P κ) :
    PhiProgressionGammaLargeTailMajorantUpperCore P := by
  rcases h with ⟨_hκ_pos, _hκ_range, Ctail, X₀, hCtail, htail⟩
  exact ⟨phiProgressionPowerCutoff κ, Ctail, X₀, hCtail, htail⟩

/-- If the gamma split cutoff is at the upper endpoint of the finite
progression interval, the large-divisor tail is empty: every exposed divisor
`k` satisfies `k ≤ r ≤ ⌊U₁⌋₊`. -/
theorem phiProgressionGammaLargeTailMajorant_eq_zero_of_floor_U1
    (P : Params) (X : ℝ) (d a s : ℕ) :
    phiProgressionGammaLargeTailMajorant P X d a s
        ⌊phiProgressionU1 P s X⌋₊ = 0 := by
  classical
  unfold phiProgressionGammaLargeTailMajorant
  apply Finset.sum_eq_zero
  intro x hx
  rcases Finset.mem_filter.mp hx with ⟨hxbase, hxlarge⟩
  have hx_outer :
      x.1 ∈ phiProgressionSupport P X d a s :=
    phiProgressionDivisorSigmaSupport_outer_mem_support
      (P := P) (X := X) (d := d) (a := a) (s := s) hxbase
  have hx_window :
      x.1 ∈ Inputs.natWindow (phiProgressionU0 P s X)
        (phiProgressionU1 P s X) := by
    unfold phiProgressionSupport at hx_outer
    exact (Finset.mem_filter.mp hx_outer).1
  have hx_icc :
      x.1 ∈ Finset.Icc (1 : ℕ) ⌊phiProgressionU1 P s X⌋₊ := by
    unfold Inputs.natWindow at hx_window
    exact (Finset.mem_filter.mp hx_window).1
  have hx1_pos : 0 < x.1 :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hx_icc).1
  have hx1_le_floor : x.1 ≤ ⌊phiProgressionU1 P s X⌋₊ :=
    (Finset.mem_Icc.mp hx_icc).2
  have hx2_le_x1 : x.2 ≤ x.1 :=
    Nat.le_of_dvd hx1_pos
      (phiProgressionDivisorSigmaSupport_divisor_dvd hxbase)
  exact False.elim (hxlarge (le_trans hx2_le_x1 hx1_le_floor))

/-- Concrete large-tail majorant bound: choose the split cutoff at the finite
interval's upper endpoint.  Then the large tail is identically zero, so no
analytic input is needed for this part of the gamma split. -/
theorem PhiProgressionGammaLargeTailMajorantUpperCore_concrete
    (P : Params) :
    PhiProgressionGammaLargeTailMajorantUpperCore P := by
  refine ⟨fun X _d s => ⌊phiProgressionU1 P s X⌋₊, 1, Real.exp 1,
    by norm_num, ?_⟩
  intro X hX d a s hd_pos _hd_sqf _hd_odd _hdU _ha_coprime
    hs_one _hs_sqf _hs_coprime hsS
  have hExpOne : (1 : ℝ) < Real.exp 1 := by
    calc
      (1 : ℝ) = Real.exp 0 := by simp
      _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
  have hXone : (1 : ℝ) < X := lt_of_lt_of_le hExpOne hX
  have hXpos : 0 < X := lt_trans zero_lt_one hXone
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hU0 : 0 < phiProgressionU0 P s X :=
    phiProgressionU0_pos P hXpos hs_pos
  have hU01 : phiProgressionU0 P s X ≤ phiProgressionU1 P s X :=
    (phiProgressionU0_lt_U1_of_s_le_SScale P hXone hs_one hsS).le
  have hlog_nonneg :
      0 ≤ Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) :=
    log_phiProgressionU1_div_U0_nonneg P X s hU0 hU01
  have hslant_nonneg : 0 ≤ slantLogLength P s X := by
    rw [← log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos]
    exact hlog_nonneg
  have hshape_nonneg : 0 ≤ phiProgressionAverageShape P X d s := by
    have hdR_nonneg : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_pos.le
    have hsR_nonneg : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_pos.le
    unfold phiProgressionAverageShape
    exact mul_nonneg
      (mul_nonneg (div_nonneg zero_le_one hdR_nonneg)
        (div_nonneg (by exact_mod_cast Nat.zero_le (Nat.totient s)) hsR_nonneg))
      hslant_nonneg
  rw [phiProgressionGammaLargeTailMajorant_eq_zero_of_floor_U1]
  simpa using hshape_nonneg

/-- Coefficient and large-tail part of the gamma split, with the cutoff chosen
by the analytic input. -/
def PhiProgressionGammaCoefficientTailMajorantUpperCore
    (P : Params) : Prop :=
  ∃ K : ℝ → ℕ → ℕ → ℕ, ∃ Cgamma Ctail X₀ : ℝ,
    0 < Cgamma ∧ 0 < Ctail ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          phiProgressionGammaSmallAdmissibleGammaDivSum d s (K X d s) ≤
            Cgamma ∧
          phiProgressionGammaLargeTailMajorant P X d a s (K X d s) ≤
            Ctail * phiProgressionAverageShape P X d s

/-- Recombines the fixed-cutoff gamma coefficient bound with the large-tail
estimate into the coefficient/tail package. -/
theorem PhiProgressionGammaCoefficientTailMajorantUpperCore_of_coefficientBound_and_largeTail
    {P : Params}
    (htail : PhiProgressionGammaLargeTailMajorantUpperCore P)
    (hcoeff : ∀ K : ℝ → ℕ → ℕ → ℕ,
      PhiProgressionGammaCoefficientBoundForCutoff P K) :
    PhiProgressionGammaCoefficientTailMajorantUpperCore P := by
  rcases htail with ⟨K, Ctail, Xtail, hCtail, htail_split⟩
  rcases hcoeff K with ⟨Cgamma, Xcoeff, hCgamma, hcoeff_split⟩
  refine ⟨K, Cgamma, Ctail, max Xcoeff Xtail, hCgamma, hCtail, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  have hXcoeff : Xcoeff ≤ X := le_trans (le_max_left _ _) hX
  have hXtail : Xtail ≤ X := le_trans (le_max_right _ _) hX
  exact ⟨
    hcoeff_split X hXcoeff d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS,
    htail_split X hXtail d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS
  ⟩

/-- Version of the coefficient/tail package whose coefficient input is the
one-dimensional full `γ(k)/k` summability bound. -/
theorem PhiProgressionGammaCoefficientTailMajorantUpperCore_of_phiGammaDivSummableBound_and_largeTail
    {P : Params}
    (htail : PhiProgressionGammaLargeTailMajorantUpperCore P)
    (hcoeff : PhiGammaDivSummableBound) :
    PhiProgressionGammaCoefficientTailMajorantUpperCore P :=
  PhiProgressionGammaCoefficientTailMajorantUpperCore_of_coefficientBound_and_largeTail
    htail
    (fun K => PhiProgressionGammaCoefficientBoundForCutoff_of_phiGammaDivSummableBound
      (P := P) (K := K) hcoeff)

def PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore
    (P : Params) : Prop :=
  ∃ K : ℝ → ℕ → ℕ → ℕ, ∃ Csqf Cgamma Ctail X₀ : ℝ,
    0 < Csqf ∧ 0 < Cgamma ∧ 0 < Ctail ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          (∀ k ∈ Finset.Icc (1 : ℕ) (K X d s),
              Nat.Coprime k d ∧ Nat.Coprime k s →
                Inputs.sqfRecip X (s * k) d (a * modInverseChoice d k)
                  (phiProgressionU0 P s X / (k : ℝ))
                  (phiProgressionU1 P s X / (k : ℝ)) ≤
                  Csqf * (((1 : ℝ) / (d : ℝ)) *
                    ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) *
                    Real.log (phiProgressionU1 P s X /
                      phiProgressionU0 P s X))) ∧
            phiProgressionGammaSmallAdmissibleGammaDivSum d s (K X d s) ≤
              Cgamma ∧
            phiProgressionGammaLargeTailMajorant P X d a s (K X d s) ≤
              Ctail * phiProgressionAverageShape P X d s

/-- Recombines the fixed-`k` ordinary-density estimate with the gamma
coefficient/tail package into the manuscript-shaped ordinary-density core. -/
theorem PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore_of_fixedK_and_gammaCoefficientTail
    {P : Params}
    (hgamma : PhiProgressionGammaCoefficientTailMajorantUpperCore P)
    (hfixed : ∀ K : ℝ → ℕ → ℕ → ℕ,
      PhiProgressionFixedKOrdinaryDensityUpperForCutoff P K) :
    PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore P := by
  rcases hgamma with ⟨K, Cgamma, Ctail, Xgamma,
    hCgamma, hCtail, hgamma_split⟩
  rcases hfixed K with ⟨Csqf, Xfixed, hCsqf, hfixed_split⟩
  refine ⟨K, Csqf, Cgamma, Ctail, max Xfixed Xgamma,
    hCsqf, hCgamma, hCtail, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  have hXfixed : Xfixed ≤ X := le_trans (le_max_left _ _) hX
  have hXgamma : Xgamma ≤ X := le_trans (le_max_right _ _) hX
  have hfixed_bound :
      ∀ k ∈ Finset.Icc (1 : ℕ) (K X d s),
        Nat.Coprime k d ∧ Nat.Coprime k s →
          Inputs.sqfRecip X (s * k) d (a * modInverseChoice d k)
            (phiProgressionU0 P s X / (k : ℝ))
            (phiProgressionU1 P s X / (k : ℝ)) ≤
            Csqf * (((1 : ℝ) / (d : ℝ)) *
              ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) *
              Real.log (phiProgressionU1 P s X /
                phiProgressionU0 P s X)) :=
    hfixed_split X hXfixed d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS
  rcases hgamma_split X hXgamma d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS with ⟨hgamma_sum, htail⟩
  exact ⟨hfixed_bound, hgamma_sum, htail⟩

/-- Manuscript power-cutoff recombination for the ordinary-density gamma core.
The small-`k` ordinary squarefree estimate, the checked full coefficient
summability, and the large-tail estimate are all tied to the same cutoff
`K=⌊X^κ⌋₊`. -/
theorem PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore_of_powerCutoff
    {P : Params} {κ : ℝ}
    (hfixed : PhiProgressionFixedKOrdinaryDensityUpperForPowerCutoff P κ)
    (htail : PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff P κ) :
    PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore P := by
  rcases hfixed with
    ⟨_hκ_pos_fixed, _hκ_range_fixed, Csqf, Xfixed, hCsqf, hfixed_split⟩
  rcases htail with
    ⟨_hκ_pos_tail, _hκ_range_tail, Ctail, Xtail, hCtail, htail_split⟩
  rcases
      (PhiProgressionGammaCoefficientBoundForCutoff_of_phiGammaDivSummableBound
        (P := P) (K := phiProgressionPowerCutoff κ)
        PhiGammaDivSummableBound_concrete) with
    ⟨Cgamma, Xcoeff, hCgamma, hcoeff_split⟩
  refine ⟨phiProgressionPowerCutoff κ, Csqf, Cgamma, Ctail,
    max Xfixed (max Xcoeff Xtail), hCsqf, hCgamma, hCtail, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  have hXfixed : Xfixed ≤ X :=
    le_trans (le_max_left Xfixed (max Xcoeff Xtail)) hX
  have hXcoeff : Xcoeff ≤ X :=
    le_trans (le_trans (le_max_left Xcoeff Xtail)
      (le_max_right Xfixed (max Xcoeff Xtail))) hX
  have hXtail : Xtail ≤ X :=
    le_trans (le_trans (le_max_right Xcoeff Xtail)
      (le_max_right Xfixed (max Xcoeff Xtail))) hX
  exact
    ⟨hfixed_split X hXfixed d a s hd_pos hd_sqf hd_odd hdU ha_coprime
        hs_one hs_sqf hs_coprime hsS,
      hcoeff_split X hXcoeff d a s hd_pos hd_sqf hd_odd hdU ha_coprime
        hs_one hs_sqf hs_coprime hsS,
      htail_split X hXtail d a s hd_pos hd_sqf hd_odd hdU ha_coprime
        hs_one hs_sqf hs_coprime hsS⟩

/-- Ordinary-density core after reducing the coefficient side to the
one-dimensional full `γ(k)/k` summability bound. -/
theorem PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore_of_fixedK_and_phiGammaDivSummableBound_and_largeTail
    {P : Params}
    (htail : PhiProgressionGammaLargeTailMajorantUpperCore P)
    (hcoeff : PhiGammaDivSummableBound)
    (hfixed : ∀ K : ℝ → ℕ → ℕ → ℕ,
      PhiProgressionFixedKOrdinaryDensityUpperForCutoff P K) :
    PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore P :=
  PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore_of_fixedK_and_gammaCoefficientTail
    (PhiProgressionGammaCoefficientTailMajorantUpperCore_of_phiGammaDivSummableBound_and_largeTail
      htail hcoeff)
    hfixed

/-- Ordinary-density core with the gamma coefficient side discharged
concretely.  After the finite Euler-product proof of
`PhiGammaDivSummableBound_concrete`, the remaining analytic obligations are
only the fixed-`k` ordinary squarefree reciprocal estimate and the large-gamma
tail majorant. -/
theorem PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore_of_fixedK_and_largeTail
    {P : Params}
    (htail : PhiProgressionGammaLargeTailMajorantUpperCore P)
    (hfixed : ∀ K : ℝ → ℕ → ℕ → ℕ,
      PhiProgressionFixedKOrdinaryDensityUpperForCutoff P K) :
    PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore P :=
  PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore_of_fixedK_and_phiGammaDivSummableBound_and_largeTail
    htail PhiGammaDivSummableBound_concrete hfixed

/-- Ordinary-density core with both the gamma coefficient series and the
large-divisor tail discharged concretely.  The sole remaining upper-half input
is the manuscript's fixed-`k` ordinary squarefree progression estimate. -/
theorem PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore_of_fixedK
    {P : Params}
    (hfixed : ∀ K : ℝ → ℕ → ℕ → ℕ,
      PhiProgressionFixedKOrdinaryDensityUpperForCutoff P K) :
    PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore P :=
  PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore_of_fixedK_and_largeTail
    (PhiProgressionGammaLargeTailMajorantUpperCore_concrete P) hfixed

/-- Ordinary-density core along the manuscript's local-density large-tail route:
the gamma coefficient series and the square-coefficient large tail are both
proved by Euler-product arguments, leaving only the pointwise fixed-`k`
ordinary squarefree progression estimate. -/
theorem
    PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore_of_fixedKPointwise_concreteOmegaTail
    {P : Params}
    (hfixed : PhiProgressionFixedKOrdinaryDensityUpper P) :
    PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore P :=
  PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore_of_fixedK_and_largeTail
    (PhiProgressionGammaLargeTailMajorantUpperCore_of_fixedKPointwise_concreteOmegaTail
      hfixed)
    (PhiProgressionFixedKOrdinaryDensityUpperForCutoff_of_pointwise hfixed)

/-- The manuscript-shaped ordinary-density small-`k` estimate implies the
admissible squarefree-model gamma split.  The proof uses the checked
comparison `φ(sk)/(sk) ≤ φ(s)/s` for `(s,k)=1` and the finite gamma coefficient
bound. -/
theorem
    PhiProgressionGammaSqfRecipAdmissibleInverseTailMajorantUpper_of_ordinaryDensityTailMajorantUpperCore
    {P : Params}
    (h : PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore P) :
    PhiProgressionGammaSqfRecipAdmissibleInverseTailMajorantUpper P := by
  rcases h with ⟨K, Csqf, Cgamma, Ctail, X₀,
    hCsqf, hCgamma, hCtail, hsplit⟩
  refine ⟨K, Csqf * Cgamma, Ctail, max X₀ (Real.exp 1),
    mul_pos hCsqf hCgamma, hCtail, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  have hX₀ : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hExpOne : (1 : ℝ) < Real.exp 1 := by
    calc
      (1 : ℝ) = Real.exp 0 := by simp
      _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
  have hXone : (1 : ℝ) < X := lt_of_lt_of_le hExpOne hXe
  have hXpos : 0 < X := lt_trans zero_lt_one hXone
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hU0 : 0 < phiProgressionU0 P s X :=
    phiProgressionU0_pos P hXpos hs_pos
  have hU01_lt : phiProgressionU0 P s X < phiProgressionU1 P s X :=
    phiProgressionU0_lt_U1_of_s_le_SScale P hXone hs_one hsS
  have hlog_nonneg :
      0 ≤ Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) :=
    log_phiProgressionU1_div_U0_nonneg P X s hU0 hU01_lt.le
  have hslant_nonneg : 0 ≤ slantLogLength P s X := by
    rw [← log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos]
    exact hlog_nonneg
  have hshape_nonneg : 0 ≤ phiProgressionAverageShape P X d s := by
    have hdR_nonneg : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_pos.le
    have hsR_nonneg : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_pos.le
    unfold phiProgressionAverageShape
    exact mul_nonneg
      (mul_nonneg (div_nonneg zero_le_one hdR_nonneg)
        (div_nonneg (by exact_mod_cast Nat.zero_le (Nat.totient s)) hsR_nonneg))
      hslant_nonneg
  rcases hsplit X hX₀ d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS with
    ⟨hfixed, hgamma, htail⟩
  constructor
  · unfold phiProgressionGammaSmallSqfRecipAdmissibleInverseModelSum
    calc
      (∑ k ∈ Finset.Icc (1 : ℕ) (K X d s),
          if Nat.Coprime k d ∧ Nat.Coprime k s then
            (phiGamma k / (k : ℝ)) *
              Inputs.sqfRecip X (s * k) d (a * modInverseChoice d k)
                (phiProgressionU0 P s X / (k : ℝ))
                (phiProgressionU1 P s X / (k : ℝ))
          else (0 : ℝ))
          ≤
        (∑ k ∈ Finset.Icc (1 : ℕ) (K X d s),
          if Nat.Coprime k d ∧ Nat.Coprime k s then
            (phiGamma k / (k : ℝ)) *
              (Csqf * phiProgressionAverageShape P X d s)
          else (0 : ℝ)) := by
            apply Finset.sum_le_sum
            intro k hk
            by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
            · have hk_pos : 0 < k := (Finset.mem_Icc.mp hk).1
              have hcoef_nonneg : 0 ≤ phiGamma k / (k : ℝ) :=
                div_nonneg (phiGamma_nonneg k) (by exact_mod_cast hk_pos.le)
              have hlocal_le_shape :
                  ((1 : ℝ) / (d : ℝ)) *
                      ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) *
                      Real.log (phiProgressionU1 P s X /
                        phiProgressionU0 P s X) ≤
                    phiProgressionAverageShape P X d s := by
                simpa [phiProgressionAverageShape,
                  log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos]
                  using
                    (one_div_modulus_mul_totient_mul_ratio_log_le_left_of_coprime
                      (d := d) (s := s) (k := k)
                      (L := Real.log (phiProgressionU1 P s X /
                        phiProgressionU0 P s X))
                      hd_pos hs_pos hk_pos hadm.2.symm hlog_nonneg)
              have hsqf_le :
                  Inputs.sqfRecip X (s * k) d (a * modInverseChoice d k)
                    (phiProgressionU0 P s X / (k : ℝ))
                    (phiProgressionU1 P s X / (k : ℝ)) ≤
                    Csqf * phiProgressionAverageShape P X d s :=
                le_trans (hfixed k hk hadm)
                  (mul_le_mul_of_nonneg_left hlocal_le_shape hCsqf.le)
              rw [if_pos hadm, if_pos hadm]
              exact mul_le_mul_of_nonneg_left hsqf_le hcoef_nonneg
            · simp [hadm]
      _ =
        phiProgressionGammaSmallAdmissibleGammaDivSum d s (K X d s) *
          (Csqf * phiProgressionAverageShape P X d s) := by
            unfold phiProgressionGammaSmallAdmissibleGammaDivSum
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k hk
            by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
            · simp [hadm]
            · simp [hadm]
      _ ≤ Cgamma * (Csqf * phiProgressionAverageShape P X d s) :=
          mul_le_mul_of_nonneg_right hgamma
            (mul_nonneg hCsqf.le hshape_nonneg)
      _ = (Csqf * Cgamma) * phiProgressionAverageShape P X d s := by
          ring
  · exact htail

/-- Elementary-envelope version of the admissible gamma split.  The
squarefree reciprocal carriers have been bounded termwise by the unconditional
endpoint/log progression envelope.  The remaining analytic work is therefore
to recover the sharper local-density saving for this envelope and control the
large-gamma tail. -/
def PhiProgressionGammaElementaryEnvelopeTailMajorantUpper
    (P : Params) : Prop :=
  ∃ K : ℝ → ℕ → ℕ → ℕ, ∃ Csmall Ctail X₀ : ℝ,
    0 < Csmall ∧ 0 < Ctail ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          0 < phiProgressionU0 P s X ∧
            phiProgressionU0 P s X < phiProgressionU1 P s X ∧
            phiProgressionGammaSmallAdmissibleElementaryEnvelopeSum
                P X d s (K X d s) ≤
                Csmall * phiProgressionAverageShape P X d s ∧
              phiProgressionGammaLargeTailMajorant P X d a s (K X d s) ≤
                Ctail * phiProgressionAverageShape P X d s

/-- Analytic core of the elementary-envelope gamma split.  Compared with
`PhiProgressionGammaElementaryEnvelopeTailMajorantUpper`, this target no longer
asks the analytic estimate to return the elementary endpoint facts
`0<U₀<U₁`; those follow deterministically from `s≤X^η` and `λ+η<θ`. -/
def PhiProgressionGammaElementaryEnvelopeTailMajorantUpperCore
    (P : Params) : Prop :=
  ∃ K : ℝ → ℕ → ℕ → ℕ, ∃ Csmall Ctail X₀ : ℝ,
    0 < Csmall ∧ 0 < Ctail ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          phiProgressionGammaSmallAdmissibleElementaryEnvelopeSum
              P X d s (K X d s) ≤
              Csmall * phiProgressionAverageShape P X d s ∧
            phiProgressionGammaLargeTailMajorant P X d a s (K X d s) ≤
              Ctail * phiProgressionAverageShape P X d s

/-- Coefficient form of the elementary-envelope gamma core.  The small side is
split into its endpoint coefficient and logarithmic coefficient.  This is the
formal target left after normalizing the fixed-`k` elementary progression
envelope. -/
def PhiProgressionGammaCoefficientEnvelopeTailMajorantUpperCore
    (P : Params) : Prop :=
  ∃ K : ℝ → ℕ → ℕ → ℕ, ∃ Cend Clog Ctail X₀ : ℝ,
    0 < Cend ∧ 0 < Clog ∧ 0 < Ctail ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          phiProgressionGammaSmallAdmissibleGammaSum d s (K X d s) *
              (1 / phiProgressionU0 P s X) ≤
              Cend * phiProgressionAverageShape P X d s ∧
            phiProgressionGammaSmallAdmissibleGammaDivSum d s (K X d s) *
              ((1 / (d : ℝ)) *
                Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)) ≤
              Clog * phiProgressionAverageShape P X d s ∧
            phiProgressionGammaLargeTailMajorant P X d a s (K X d s) ≤
              Ctail * phiProgressionAverageShape P X d s

/-- The coefficient endpoint/log target implies the elementary-envelope core,
using only the checked normalization of the fixed-`k` envelope. -/
theorem
    PhiProgressionGammaElementaryEnvelopeTailMajorantUpperCore_of_coefficientEnvelopeTailMajorantUpperCore
    {P : Params}
    (h : PhiProgressionGammaCoefficientEnvelopeTailMajorantUpperCore P) :
    PhiProgressionGammaElementaryEnvelopeTailMajorantUpperCore P := by
  rcases h with ⟨K, Cend, Clog, Ctail, X₀, hCend, hClog, hCtail, hsplit⟩
  refine ⟨K, Cend + Clog, Ctail, max X₀ (Real.exp 1),
    add_pos hCend hClog, hCtail, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  have hX₀ : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hExpOne : (1 : ℝ) < Real.exp 1 := by
    calc
      (1 : ℝ) = Real.exp 0 := by simp
      _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
  have hXone : (1 : ℝ) < X := lt_of_lt_of_le hExpOne hXe
  have hXpos : 0 < X := lt_trans zero_lt_one hXone
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hU0 : 0 < phiProgressionU0 P s X :=
    phiProgressionU0_pos P hXpos hs_pos
  rcases hsplit X hX₀ d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS with
    ⟨hend, hlog, htail⟩
  constructor
  · calc
      phiProgressionGammaSmallAdmissibleElementaryEnvelopeSum
          P X d s (K X d s)
          =
          phiProgressionGammaSmallAdmissibleGammaSum d s (K X d s) *
              (1 / phiProgressionU0 P s X) +
            phiProgressionGammaSmallAdmissibleGammaDivSum d s (K X d s) *
              ((1 / (d : ℝ)) *
                Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X)) := by
            rw [phiProgressionGammaSmallAdmissibleElementaryEnvelopeSum_eq_gammaSums
              P X d s (K X d s) (ne_of_gt hU0)]
      _ ≤ Cend * phiProgressionAverageShape P X d s +
            Clog * phiProgressionAverageShape P X d s :=
          add_le_add hend hlog
      _ = (Cend + Clog) * phiProgressionAverageShape P X d s := by
          ring
  · exact htail

/-- The analytic core of the elementary-envelope gamma split implies the older
form with endpoint side conditions: for large `X`, `U₀>0` and `U₀<U₁` are
deterministic consequences of the paper's scale inequalities. -/
theorem PhiProgressionGammaElementaryEnvelopeTailMajorantUpper_of_core
    {P : Params}
    (h : PhiProgressionGammaElementaryEnvelopeTailMajorantUpperCore P) :
    PhiProgressionGammaElementaryEnvelopeTailMajorantUpper P := by
  rcases h with ⟨K, Csmall, Ctail, X₀, hCsmall, hCtail, hsplit⟩
  refine ⟨K, Csmall, Ctail, max X₀ (Real.exp 1), hCsmall, hCtail, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  have hX₀ : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hExpOne : (1 : ℝ) < Real.exp 1 := by
    calc
      (1 : ℝ) = Real.exp 0 := by simp
      _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
  have hXone : (1 : ℝ) < X := lt_of_lt_of_le hExpOne hXe
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  rcases hsplit X hX₀ d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS with
    ⟨hsmall, htail⟩
  exact
    ⟨phiProgressionU0_pos P (lt_trans zero_lt_one hXone) hs_pos,
      phiProgressionU0_lt_U1_of_s_le_SScale P hXone hs_one hsS,
      hsmall, htail⟩

/-- Bounding the elementary endpoint/log envelope implies the weighted
reciprocal-fiber target, since the admissible `sqfRecip` model is termwise
bounded by that envelope. -/
theorem PhiProgressionGammaWeightedRecipTailMajorantUpper_of_elementaryEnvelopeTailMajorantUpper
    {P : Params}
    (h : PhiProgressionGammaElementaryEnvelopeTailMajorantUpper P) :
    PhiProgressionGammaWeightedRecipTailMajorantUpper P := by
  rcases h with ⟨K, Csmall, Ctail, X₀, hCsmall, hCtail, hsplit⟩
  refine ⟨K, Csmall, Ctail, X₀, hCsmall, hCtail, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  rcases hsplit X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS with
    ⟨hU0, hU01, hsmallEnvelope, htail⟩
  have hmodel :
      phiProgressionGammaSmallSqfRecipAdmissibleInverseModelSum
          P X d a s (K X d s) ≤
        phiProgressionGammaSmallAdmissibleElementaryEnvelopeSum
          P X d s (K X d s) :=
    phiProgressionGammaSmallSqfRecipAdmissibleInverseModelSum_le_elementaryEnvelope
      P X d a s (K X d s) hd_pos hU0 hU01
  exact
    ⟨le_trans
      (phiProgressionGammaSmallWeightedRecipFiberSum_le_admissibleInverseSqfRecipModelSum
        P X d a s (K X d s) hd_pos ha_coprime)
      (le_trans hmodel hsmallEnvelope),
      htail⟩

/-- Core elementary-envelope estimates are enough for the weighted
reciprocal-fiber target. -/
theorem PhiProgressionGammaWeightedRecipTailMajorantUpper_of_elementaryEnvelopeTailMajorantUpperCore
    {P : Params}
    (h : PhiProgressionGammaElementaryEnvelopeTailMajorantUpperCore P) :
    PhiProgressionGammaWeightedRecipTailMajorantUpper P :=
  PhiProgressionGammaWeightedRecipTailMajorantUpper_of_elementaryEnvelopeTailMajorantUpper
    (PhiProgressionGammaElementaryEnvelopeTailMajorantUpper_of_core h)

/-- Manuscript-aligned small-`k` recombination: it is enough to prove the ordinary
squarefree progression estimate for squarefree exposed divisors `k`.  The
actual fixed-divisor fibers with nonsquarefree `k` are empty, so this avoids
the older overstrong all-`k` local-density target while preserving the
manuscript's common cutoff `K=⌊X^κ⌋₊`. -/
theorem
    PhiProgressionGammaWeightedRecipTailMajorantUpper_of_squarefreeFixedK_and_powerCutoff
    {P : Params} {κ : ℝ}
    (hfixed :
      PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff P κ)
    (htail : PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff P κ) :
    PhiProgressionGammaWeightedRecipTailMajorantUpper P := by
  rcases hfixed with
    ⟨_hκ_pos_fixed, _hκ_range_fixed, Csqf, Xfixed, hCsqf, hfixed_split⟩
  rcases htail with
    ⟨_hκ_pos_tail, _hκ_range_tail, Ctail, Xtail, hCtail, htail_split⟩
  rcases
      (PhiProgressionGammaCoefficientBoundForCutoff_of_phiGammaDivSummableBound
        (P := P) (K := phiProgressionPowerCutoff κ)
        PhiGammaDivSummableBound_concrete) with
    ⟨Cgamma, Xcoeff, hCgamma, hcoeff_split⟩
  refine ⟨phiProgressionPowerCutoff κ, Csqf * Cgamma, Ctail,
    max (max Xfixed (max Xcoeff Xtail)) (Real.exp 1),
    mul_pos hCsqf hCgamma, hCtail, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  have hXfixed : Xfixed ≤ X :=
    le_trans (le_trans (le_max_left Xfixed (max Xcoeff Xtail))
      (le_max_left (max Xfixed (max Xcoeff Xtail)) (Real.exp 1))) hX
  have hXcoeff : Xcoeff ≤ X :=
    le_trans (le_trans (le_max_left Xcoeff Xtail)
      (le_max_right Xfixed (max Xcoeff Xtail)))
      (le_trans (le_max_left (max Xfixed (max Xcoeff Xtail)) (Real.exp 1)) hX)
  have hXtail : Xtail ≤ X :=
    le_trans (le_trans (le_max_right Xcoeff Xtail)
      (le_max_right Xfixed (max Xcoeff Xtail)))
      (le_trans (le_max_left (max Xfixed (max Xcoeff Xtail)) (Real.exp 1)) hX)
  have hXexp : Real.exp 1 ≤ X :=
    le_trans (le_max_right (max Xfixed (max Xcoeff Xtail)) (Real.exp 1)) hX
  have hXone : (1 : ℝ) ≤ X := by
    exact le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXexp
  have hXgtone : (1 : ℝ) < X :=
    lt_of_lt_of_le (by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)) hXexp
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hU0 : 0 < phiProgressionU0 P s X :=
    phiProgressionU0_pos P hXpos hs_pos
  have hU01 : phiProgressionU0 P s X ≤ phiProgressionU1 P s X :=
    (phiProgressionU0_lt_U1_of_s_le_SScale P
      hXgtone hs_one hsS).le
  have hlog_nonneg :
      0 ≤ Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) :=
    log_phiProgressionU1_div_U0_nonneg P X s hU0 hU01
  have hslant_nonneg : 0 ≤ slantLogLength P s X := by
    rw [← log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos]
    exact hlog_nonneg
  have hshape_nonneg : 0 ≤ phiProgressionAverageShape P X d s := by
    have hdR_nonneg : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_pos.le
    have hsR_nonneg : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_pos.le
    unfold phiProgressionAverageShape
    exact mul_nonneg
      (mul_nonneg (div_nonneg zero_le_one hdR_nonneg)
        (div_nonneg (by exact_mod_cast Nat.zero_le (Nat.totient s)) hsR_nonneg))
      hslant_nonneg
  have hfixed_bound :
      ∀ k ∈ Finset.Icc (1 : ℕ) (phiProgressionPowerCutoff κ X d s),
        Squarefree k → Nat.Coprime k d ∧ Nat.Coprime k s →
          Inputs.sqfRecip X (s * k) d (a * modInverseChoice d k)
            (phiProgressionU0 P s X / (k : ℝ))
            (phiProgressionU1 P s X / (k : ℝ)) ≤
            Csqf * (((1 : ℝ) / (d : ℝ)) *
              ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) *
              Real.log (phiProgressionU1 P s X /
                phiProgressionU0 P s X)) :=
    hfixed_split X hXfixed d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS
  have hgamma :
      phiProgressionGammaSmallAdmissibleGammaDivSum d s
          (phiProgressionPowerCutoff κ X d s) ≤ Cgamma :=
    hcoeff_split X hXcoeff d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS
  have htail :
      phiProgressionGammaLargeTailMajorant P X d a s
          (phiProgressionPowerCutoff κ X d s) ≤
        Ctail * phiProgressionAverageShape P X d s :=
    htail_split X hXtail d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS
  constructor
  · unfold phiProgressionGammaSmallWeightedRecipFiberSum
    calc
      (∑ k ∈ Finset.Icc (1 : ℕ) (phiProgressionPowerCutoff κ X d s),
          (phiGamma k / (k : ℝ)) *
            phiProgressionFixedKQuotientRecipFiber P X d a s k)
          ≤
        (∑ k ∈ Finset.Icc (1 : ℕ) (phiProgressionPowerCutoff κ X d s),
          if Nat.Coprime k d ∧ Nat.Coprime k s then
            (phiGamma k / (k : ℝ)) *
              (Csqf * phiProgressionAverageShape P X d s)
          else (0 : ℝ)) := by
            apply Finset.sum_le_sum
            intro k hk
            have hk_pos : 0 < k := (Finset.mem_Icc.mp hk).1
            have hcoef_nonneg : 0 ≤ phiGamma k / (k : ℝ) :=
              div_nonneg (phiGamma_nonneg k) (by exact_mod_cast hk_pos.le)
            by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
            · by_cases hk_sqf : Squarefree k
              · rw [if_pos hadm]
                have hfiber_le_sqf :
                    phiProgressionFixedKQuotientRecipFiber P X d a s k ≤
                      Inputs.sqfRecip X (s * k) d
                        (a * modInverseChoice d k)
                        (phiProgressionU0 P s X / (k : ℝ))
                        (phiProgressionU1 P s X / (k : ℝ)) :=
                  phiProgressionFixedKQuotientRecipFiber_le_sqfRecip_of_inverse
                    P X d a s k (modInverseChoice d k) hk_pos
                    (modInverseChoice_coprime hd_pos hadm.1)
                have hlocal_le_shape :
                    ((1 : ℝ) / (d : ℝ)) *
                        ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) *
                        Real.log (phiProgressionU1 P s X /
                          phiProgressionU0 P s X) ≤
                      phiProgressionAverageShape P X d s := by
                  simpa [phiProgressionAverageShape,
                    log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos]
                    using
                      (one_div_modulus_mul_totient_mul_ratio_log_le_left_of_coprime
                        (d := d) (s := s) (k := k)
                        (L := Real.log (phiProgressionU1 P s X /
                          phiProgressionU0 P s X))
                        hd_pos hs_pos hk_pos hadm.2.symm hlog_nonneg)
                have hsqf_le_shape :
                    Inputs.sqfRecip X (s * k) d
                        (a * modInverseChoice d k)
                        (phiProgressionU0 P s X / (k : ℝ))
                        (phiProgressionU1 P s X / (k : ℝ)) ≤
                      Csqf * phiProgressionAverageShape P X d s :=
                  le_trans (hfixed_bound k hk hk_sqf hadm)
                    (mul_le_mul_of_nonneg_left hlocal_le_shape hCsqf.le)
                exact mul_le_mul_of_nonneg_left
                  (le_trans hfiber_le_sqf hsqf_le_shape) hcoef_nonneg
              · rw [if_pos hadm,
                  phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_squarefree
                    P X d a s k hk_sqf,
                  mul_zero]
                exact mul_nonneg hcoef_nonneg
                  (mul_nonneg hCsqf.le hshape_nonneg)
            · rw [if_neg hadm]
              by_cases hkd : Nat.Coprime k d
              · have hks : ¬ Nat.Coprime k s := by
                  intro hks
                  exact hadm ⟨hkd, hks⟩
                rw [phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_coprime_s
                  P X d a s k hks, mul_zero]
              · rw [phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_coprime_d
                  P X d a s k ha_coprime hkd, mul_zero]
      _ =
        phiProgressionGammaSmallAdmissibleGammaDivSum d s
            (phiProgressionPowerCutoff κ X d s) *
          (Csqf * phiProgressionAverageShape P X d s) := by
            unfold phiProgressionGammaSmallAdmissibleGammaDivSum
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k hk
            by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
            · simp [hadm]
            · simp [hadm]
      _ ≤ Cgamma * (Csqf * phiProgressionAverageShape P X d s) :=
          mul_le_mul_of_nonneg_right hgamma
            (mul_nonneg hCsqf.le hshape_nonneg)
      _ = (Csqf * Cgamma) * phiProgressionAverageShape P X d s := by
          ring
  · exact htail

/-- Bounding the admissible canonical-inverse `sqfRecip` model small side
implies the weighted reciprocal-fiber target. -/
theorem PhiProgressionGammaWeightedRecipTailMajorantUpper_of_admissibleInverseSqfRecipModelTailMajorantUpper
    {P : Params}
    (h : PhiProgressionGammaSqfRecipAdmissibleInverseTailMajorantUpper P) :
    PhiProgressionGammaWeightedRecipTailMajorantUpper P := by
  rcases h with ⟨K, Csmall, Ctail, X₀, hCsmall, hCtail, hsplit⟩
  refine ⟨K, Csmall, Ctail, X₀, hCsmall, hCtail, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  rcases hsplit X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS with
    ⟨hsmallModel, htail⟩
  exact
    ⟨le_trans
      (phiProgressionGammaSmallWeightedRecipFiberSum_le_admissibleInverseSqfRecipModelSum
        P X d a s (K X d s) hd_pos ha_coprime)
      hsmallModel,
      htail⟩

/-- Bounding the canonical coprime-inverse `sqfRecip` model small side implies
the weighted reciprocal-fiber target. -/
theorem PhiProgressionGammaWeightedRecipTailMajorantUpper_of_coprimeInverseSqfRecipModelTailMajorantUpper
    {P : Params}
    (h : PhiProgressionGammaSqfRecipCoprimeInverseTailMajorantUpper P) :
    PhiProgressionGammaWeightedRecipTailMajorantUpper P := by
  rcases h with ⟨K, Csmall, Ctail, X₀, hCsmall, hCtail, hsplit⟩
  refine ⟨K, Csmall, Ctail, X₀, hCsmall, hCtail, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  rcases hsplit X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS with
    ⟨hsmallModel, htail⟩
  exact
    ⟨le_trans
      (phiProgressionGammaSmallWeightedRecipFiberSum_le_coprimeInverseSqfRecipModelSum
        P X d a s (K X d s) hd_pos ha_coprime)
      hsmallModel,
      htail⟩

/-- Bounding the `sqfRecip` model small side implies the weighted
reciprocal-fiber target. -/
theorem PhiProgressionGammaWeightedRecipTailMajorantUpper_of_sqfRecipModelTailMajorantUpper
    {P : Params} (h : PhiProgressionGammaSqfRecipModelTailMajorantUpper P) :
    PhiProgressionGammaWeightedRecipTailMajorantUpper P := by
  rcases h with ⟨K, B, Csmall, Ctail, X₀, hCsmall, hCtail, hsplit⟩
  refine ⟨K, Csmall, Ctail, X₀, hCsmall, hCtail, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  rcases hsplit X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS with
    ⟨hB, hsmallModel, htail⟩
  exact
    ⟨le_trans
      (phiProgressionGammaSmallWeightedRecipFiberSum_le_sqfRecipModelSum
        P X d a s (K X d s) (B X d a s) hB)
      hsmallModel,
      htail⟩

/-- The weighted reciprocal-fiber formulation implies the fixed-divisor
fiber-tail formulation. -/
theorem PhiProgressionGammaFiberTailMajorantUpper_of_weightedRecipTailMajorantUpper
    {P : Params} (h : PhiProgressionGammaWeightedRecipTailMajorantUpper P) :
    PhiProgressionGammaFiberTailMajorantUpper P := by
  rcases h with ⟨K, Csmall, Ctail, X₀, hCsmall, hCtail, hsplit⟩
  refine ⟨K, Csmall, Ctail, X₀, hCsmall, hCtail, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  rcases hsplit X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS with
    ⟨hsmall, htail⟩
  exact
    ⟨by
      simpa [phiProgressionGammaSmallFiberSum_eq_weightedRecipFiberSum]
        using hsmall,
      htail⟩

/-- The fixed-divisor fiber formulation implies the small/large
tail-majorant split. -/
theorem PhiProgressionGammaSplitTailMajorantUpper_of_fiberTailMajorantUpper
    {P : Params} (h : PhiProgressionGammaFiberTailMajorantUpper P) :
    PhiProgressionGammaSplitTailMajorantUpper P := by
  rcases h with ⟨K, Csmall, Ctail, X₀, hCsmall, hCtail, hsplit⟩
  refine ⟨K, Csmall, Ctail, X₀, hCsmall, hCtail, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  rcases hsplit X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS with
    ⟨hsmall, htail⟩
  exact
    ⟨by
      simpa [phiProgressionGammaSmallFiberSum_eq_smallQuotientAverage]
        using hsmall,
      htail⟩

/-- The tail-majorant split implies the exact small/large gamma split. -/
theorem PhiProgressionGammaSplitUpper_of_tailMajorantUpper
    {P : Params} (h : PhiProgressionGammaSplitTailMajorantUpper P) :
    PhiProgressionGammaSplitUpper P := by
  rcases h with ⟨K, Csmall, Ctail, X₀, hCsmall, hCtail, hsplit⟩
  refine ⟨K, Csmall, Ctail, X₀, hCsmall, hCtail, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  rcases hsplit X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS with
    ⟨hsmall, htail⟩
  exact ⟨hsmall,
    le_trans
      (phiProgressionGammaLargeQuotientAverage_le_tailMajorant
        P X d a s (K X d s))
      htail⟩

/-- The manuscript's small/large gamma split is enough to prove the unsplit
gamma-quotient upper estimate. -/
theorem PhiProgressionGammaQuotientUpper_of_splitUpper
    {P : Params} (h : PhiProgressionGammaSplitUpper P) :
    PhiProgressionGammaQuotientUpper P := by
  rcases h with ⟨K, Csmall, Clarge, X₀, hCsmall, hClarge, hsplit⟩
  refine ⟨Csmall + Clarge, X₀, add_pos hCsmall hClarge, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  rcases hsplit X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS with
    ⟨hsmall, hlarge⟩
  calc
    phiProgressionGammaQuotientAverage P X d a s
        = phiProgressionGammaSmallQuotientAverage P X d a s (K X d s) +
            phiProgressionGammaLargeQuotientAverage P X d a s (K X d s) := by
              exact phiProgressionGammaQuotientAverage_eq_small_add_large
                P X d a s (K X d s)
    _ ≤ Csmall * phiProgressionAverageShape P X d s +
          Clarge * phiProgressionAverageShape P X d s :=
            add_le_add hsmall hlarge
    _ = (Csmall + Clarge) * phiProgressionAverageShape P X d s := by
          ring

/-- The paper-shaped ordinary-density small-`k` estimate and gamma-tail
majorant imply the unsplit gamma-quotient upper half of
`lem:phi-progression-average`. -/
theorem PhiProgressionGammaQuotientUpper_of_ordinaryDensityTailMajorantUpperCore
    {P : Params}
    (h : PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore P) :
    PhiProgressionGammaQuotientUpper P :=
  PhiProgressionGammaQuotientUpper_of_splitUpper
    (PhiProgressionGammaSplitUpper_of_tailMajorantUpper
      (PhiProgressionGammaSplitTailMajorantUpper_of_fiberTailMajorantUpper
        (PhiProgressionGammaFiberTailMajorantUpper_of_weightedRecipTailMajorantUpper
          (PhiProgressionGammaWeightedRecipTailMajorantUpper_of_admissibleInverseSqfRecipModelTailMajorantUpper
            (PhiProgressionGammaSqfRecipAdmissibleInverseTailMajorantUpper_of_ordinaryDensityTailMajorantUpperCore
              h)))))

/-- Gamma-quotient upper half with the coefficient series already discharged.
This is the manuscript split after the checked Euler-product coefficient bound:
small `k` is supplied by the fixed-`k` ordinary-density estimate, and large `k`
by the gamma-tail majorant. -/
theorem PhiProgressionGammaQuotientUpper_of_fixedK_and_largeTail
    {P : Params}
    (htail : PhiProgressionGammaLargeTailMajorantUpperCore P)
    (hfixed : ∀ K : ℝ → ℕ → ℕ → ℕ,
      PhiProgressionFixedKOrdinaryDensityUpperForCutoff P K) :
    PhiProgressionGammaQuotientUpper P :=
  PhiProgressionGammaQuotientUpper_of_ordinaryDensityTailMajorantUpperCore
    (PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore_of_fixedK_and_largeTail
      htail hfixed)

/-- Gamma-quotient upper half from the paper's common power cutoff
`K=⌊X^κ⌋₊`: bounded small `k`, concrete coefficient summability, and matching
large-tail control. -/
theorem PhiProgressionGammaQuotientUpper_of_powerCutoff
    {P : Params} {κ : ℝ}
    (hfixed : PhiProgressionFixedKOrdinaryDensityUpperForPowerCutoff P κ)
    (htail : PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff P κ) :
    PhiProgressionGammaQuotientUpper P :=
  PhiProgressionGammaQuotientUpper_of_ordinaryDensityTailMajorantUpperCore
    (PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore_of_powerCutoff
      hfixed htail)

/-- Gamma-quotient upper half from the manuscript-aligned squarefree fixed-`k`
ordinary-density target and the common power cutoff.  This is the version that
does not require an artificial all-`k` fixed-divisor estimate. -/
theorem PhiProgressionGammaQuotientUpper_of_squarefreeFixedK_and_powerCutoff
    {P : Params} {κ : ℝ}
    (hfixed :
      PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff P κ)
    (htail : PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff P κ) :
    PhiProgressionGammaQuotientUpper P :=
  PhiProgressionGammaQuotientUpper_of_splitUpper
    (PhiProgressionGammaSplitUpper_of_tailMajorantUpper
      (PhiProgressionGammaSplitTailMajorantUpper_of_fiberTailMajorantUpper
        (PhiProgressionGammaFiberTailMajorantUpper_of_weightedRecipTailMajorantUpper
          (PhiProgressionGammaWeightedRecipTailMajorantUpper_of_squarefreeFixedK_and_powerCutoff
            hfixed htail))))

/-- Wide-modulus weighted reciprocal-fiber gamma split from the squarefree
fixed-`k` ordinary-density estimate and the matching large-tail estimate. -/
theorem
    PhiProgressionGammaWeightedRecipTailMajorantUpperYU_of_squarefreeFixedK_and_powerCutoff
    {P : Params} {κ : ℝ}
    (hfixed :
      PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoffYU P κ)
    (htail : PhiProgressionGammaLargeTailMajorantUpperForPowerCutoffYU P κ) :
    PhiProgressionGammaWeightedRecipTailMajorantUpperYU P := by
  rcases hfixed with
    ⟨_hκ_pos_fixed, _hκ_range_fixed, Csqf, Xfixed, hCsqf, hfixed_split⟩
  rcases htail with
    ⟨_hκ_pos_tail, _hκ_range_tail, Ctail, Xtail, hCtail, htail_split⟩
  rcases PhiGammaDivSummableBound_concrete with
    ⟨Cgamma, hCgamma, hgamma_all⟩
  refine ⟨phiProgressionPowerCutoff κ, Csqf * Cgamma, Ctail,
    max (max Xfixed Xtail) (Real.exp 1),
    mul_pos hCsqf hCgamma, hCtail, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdYU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  have hXfixed : Xfixed ≤ X :=
    le_trans (le_trans (le_max_left Xfixed Xtail)
      (le_max_left (max Xfixed Xtail) (Real.exp 1))) hX
  have hXtail : Xtail ≤ X :=
    le_trans (le_trans (le_max_right Xfixed Xtail)
      (le_max_left (max Xfixed Xtail) (Real.exp 1))) hX
  have hXexp : Real.exp 1 ≤ X :=
    le_trans (le_max_right (max Xfixed Xtail) (Real.exp 1)) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXexp
  have hXgtone : (1 : ℝ) < X :=
    lt_of_lt_of_le (by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)) hXexp
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hU0 : 0 < phiProgressionU0 P s X :=
    phiProgressionU0_pos P hXpos hs_pos
  have hU01 : phiProgressionU0 P s X ≤ phiProgressionU1 P s X :=
    (phiProgressionU0_lt_U1_of_s_le_SScale P
      hXgtone hs_one hsS).le
  have hlog_nonneg :
      0 ≤ Real.log (phiProgressionU1 P s X / phiProgressionU0 P s X) :=
    log_phiProgressionU1_div_U0_nonneg P X s hU0 hU01
  have hslant_nonneg : 0 ≤ slantLogLength P s X := by
    rw [← log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos]
    exact hlog_nonneg
  have hshape_nonneg : 0 ≤ phiProgressionAverageShape P X d s := by
    have hdR_nonneg : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_pos.le
    have hsR_nonneg : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_pos.le
    unfold phiProgressionAverageShape
    exact mul_nonneg
      (mul_nonneg (div_nonneg zero_le_one hdR_nonneg)
        (div_nonneg (by exact_mod_cast Nat.zero_le (Nat.totient s)) hsR_nonneg))
      hslant_nonneg
  have hfixed_bound :
      ∀ k ∈ Finset.Icc (1 : ℕ) (phiProgressionPowerCutoff κ X d s),
        Squarefree k → Nat.Coprime k d ∧ Nat.Coprime k s →
          Inputs.sqfRecip X (s * k) d (a * modInverseChoice d k)
            (phiProgressionU0 P s X / (k : ℝ))
            (phiProgressionU1 P s X / (k : ℝ)) ≤
            Csqf * (((1 : ℝ) / (d : ℝ)) *
              ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) *
              Real.log (phiProgressionU1 P s X /
                phiProgressionU0 P s X)) :=
    hfixed_split X hXfixed d a s hd_pos hd_sqf hd_odd hdYU ha_coprime
      hs_one hs_sqf hs_coprime hsS
  have hgamma :
      phiProgressionGammaSmallAdmissibleGammaDivSum d s
          (phiProgressionPowerCutoff κ X d s) ≤ Cgamma :=
    le_trans
      (phiProgressionGammaSmallAdmissibleGammaDivSum_le_phiGammaDivSum d s
        (phiProgressionPowerCutoff κ X d s))
      (hgamma_all (phiProgressionPowerCutoff κ X d s))
  have htail :
      phiProgressionGammaLargeTailMajorant P X d a s
          (phiProgressionPowerCutoff κ X d s) ≤
        Ctail * phiProgressionAverageShape P X d s :=
    htail_split X hXtail d a s hd_pos hd_sqf hd_odd hdYU ha_coprime
      hs_one hs_sqf hs_coprime hsS
  constructor
  · unfold phiProgressionGammaSmallWeightedRecipFiberSum
    calc
      (∑ k ∈ Finset.Icc (1 : ℕ) (phiProgressionPowerCutoff κ X d s),
          (phiGamma k / (k : ℝ)) *
            phiProgressionFixedKQuotientRecipFiber P X d a s k)
          ≤
        (∑ k ∈ Finset.Icc (1 : ℕ) (phiProgressionPowerCutoff κ X d s),
          if Nat.Coprime k d ∧ Nat.Coprime k s then
            (phiGamma k / (k : ℝ)) *
              (Csqf * phiProgressionAverageShape P X d s)
          else (0 : ℝ)) := by
            apply Finset.sum_le_sum
            intro k hk
            have hk_pos : 0 < k := (Finset.mem_Icc.mp hk).1
            have hcoef_nonneg : 0 ≤ phiGamma k / (k : ℝ) :=
              div_nonneg (phiGamma_nonneg k) (by exact_mod_cast hk_pos.le)
            by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
            · by_cases hk_sqf : Squarefree k
              · have hlocal_le_shape :
                    ((1 : ℝ) / (d : ℝ)) *
                        ((Nat.totient (s * k) : ℝ) / (s * k : ℝ)) *
                        Real.log (phiProgressionU1 P s X /
                          phiProgressionU0 P s X) ≤
                      phiProgressionAverageShape P X d s := by
                  simpa [phiProgressionAverageShape,
                    log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos]
                    using
                      (one_div_modulus_mul_totient_mul_ratio_log_le_left_of_coprime
                        (d := d) (s := s) (k := k)
                        (L := Real.log (phiProgressionU1 P s X /
                          phiProgressionU0 P s X))
                        hd_pos hs_pos hk_pos hadm.2.symm hlog_nonneg)
                have hsqf_le :
                    Inputs.sqfRecip X (s * k) d (a * modInverseChoice d k)
                      (phiProgressionU0 P s X / (k : ℝ))
                      (phiProgressionU1 P s X / (k : ℝ)) ≤
                      Csqf * phiProgressionAverageShape P X d s :=
                  le_trans (hfixed_bound k hk hk_sqf hadm)
                    (mul_le_mul_of_nonneg_left hlocal_le_shape hCsqf.le)
                have hfiber_le_sqf :
                    phiProgressionFixedKQuotientRecipFiber P X d a s k ≤
                      Inputs.sqfRecip X (s * k) d
                        (a * modInverseChoice d k)
                        (phiProgressionU0 P s X / (k : ℝ))
                        (phiProgressionU1 P s X / (k : ℝ)) :=
                  phiProgressionFixedKQuotientRecipFiber_le_sqfRecip_of_inverse
                    P X d a s k (modInverseChoice d k) hk_pos
                    (modInverseChoice_coprime hd_pos hadm.1)
                have hfiber_le_shape :
                    phiProgressionFixedKQuotientRecipFiber P X d a s k ≤
                      Csqf * phiProgressionAverageShape P X d s :=
                  le_trans hfiber_le_sqf hsqf_le
                rw [if_pos hadm]
                exact mul_le_mul_of_nonneg_left hfiber_le_shape hcoef_nonneg
              · rw [if_pos hadm,
                  phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_squarefree
                    P X d a s k hk_sqf, mul_zero]
                exact mul_nonneg hcoef_nonneg (mul_nonneg hCsqf.le hshape_nonneg)
            · rw [if_neg hadm]
              by_cases hkd : Nat.Coprime k d
              · have hks : ¬ Nat.Coprime k s := by
                  intro hks
                  exact hadm ⟨hkd, hks⟩
                rw [phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_coprime_s
                  P X d a s k hks, mul_zero]
              · rw [phiProgressionFixedKQuotientRecipFiber_eq_zero_of_not_coprime_d
                  P X d a s k ha_coprime hkd, mul_zero]
      _ =
        phiProgressionGammaSmallAdmissibleGammaDivSum d s
            (phiProgressionPowerCutoff κ X d s) *
          (Csqf * phiProgressionAverageShape P X d s) := by
            unfold phiProgressionGammaSmallAdmissibleGammaDivSum
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k hk
            by_cases hadm : Nat.Coprime k d ∧ Nat.Coprime k s
            · simp [hadm]
            · simp [hadm]
      _ ≤ Cgamma * (Csqf * phiProgressionAverageShape P X d s) :=
          mul_le_mul_of_nonneg_right hgamma
            (mul_nonneg hCsqf.le hshape_nonneg)
      _ = (Csqf * Cgamma) * phiProgressionAverageShape P X d s := by
          ring
  · exact htail

/-- The wide weighted reciprocal-fiber split implies the wide gamma-quotient
upper estimate. -/
theorem PhiProgressionGammaQuotientUpperYU_of_weightedRecipTailMajorantUpperYU
    {P : Params}
    (h : PhiProgressionGammaWeightedRecipTailMajorantUpperYU P) :
    PhiProgressionGammaQuotientUpperYU P := by
  rcases h with ⟨K, Csmall, Ctail, X₀, hCsmall, hCtail, hsplit⟩
  refine ⟨Csmall + Ctail, X₀, add_pos hCsmall hCtail, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdYU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  rcases hsplit X hX d a s hd_pos hd_sqf hd_odd hdYU ha_coprime
      hs_one hs_sqf hs_coprime hsS with
    ⟨hsmall, htail⟩
  have hsmall_fiber :
      phiProgressionGammaSmallFiberSum P X d a s (K X d s) ≤
        Csmall * phiProgressionAverageShape P X d s := by
    simpa [phiProgressionGammaSmallFiberSum_eq_weightedRecipFiberSum] using hsmall
  have hsmall_quot :
      phiProgressionGammaSmallQuotientAverage P X d a s (K X d s) ≤
        Csmall * phiProgressionAverageShape P X d s := by
    simpa [phiProgressionGammaSmallFiberSum_eq_smallQuotientAverage] using
      hsmall_fiber
  have hlarge_quot :
      phiProgressionGammaLargeQuotientAverage P X d a s (K X d s) ≤
        Ctail * phiProgressionAverageShape P X d s :=
    le_trans
      (phiProgressionGammaLargeQuotientAverage_le_tailMajorant
        P X d a s (K X d s))
      htail
  calc
    phiProgressionGammaQuotientAverage P X d a s
        = phiProgressionGammaSmallQuotientAverage P X d a s (K X d s) +
            phiProgressionGammaLargeQuotientAverage P X d a s (K X d s) := by
              exact phiProgressionGammaQuotientAverage_eq_small_add_large
                P X d a s (K X d s)
    _ ≤ Csmall * phiProgressionAverageShape P X d s +
          Ctail * phiProgressionAverageShape P X d s :=
            add_le_add hsmall_quot hlarge_quot
    _ = (Csmall + Ctail) * phiProgressionAverageShape P X d s := by
          ring

/-- Wide gamma-quotient upper half from the manuscript-aligned squarefree fixed-`k`
ordinary-density target and the matching wide large-tail estimate. -/
theorem PhiProgressionGammaQuotientUpperYU_of_squarefreeFixedK_and_powerCutoff
    {P : Params} {κ : ℝ}
    (hfixed :
      PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoffYU P κ)
    (htail : PhiProgressionGammaLargeTailMajorantUpperForPowerCutoffYU P κ) :
    PhiProgressionGammaQuotientUpperYU P :=
  PhiProgressionGammaQuotientUpperYU_of_weightedRecipTailMajorantUpperYU
    (PhiProgressionGammaWeightedRecipTailMajorantUpperYU_of_squarefreeFixedK_and_powerCutoff
      hfixed htail)

/-- Wide gamma-quotient upper half from the single cited ordinary squarefree
progression upper estimate on the tensor modulus range.

The small side is obtained by exponent monotonicity from the same wide
ordinary input; the large side is the concrete omega-square tail bridge. -/
theorem PhiProgressionGammaQuotientUpperYU_of_ordinaryUpper_wide_concreteOmegaTail
    {P : Params} {κ : ℝ}
    (hκ_pos : 0 < κ) (hκ_range : P.η + κ < P.lam)
    (hordinary :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ) :
    PhiProgressionGammaQuotientUpperYU P :=
  PhiProgressionGammaQuotientUpperYU_of_squarefreeFixedK_and_powerCutoff
    (PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoffYU_of_ordinaryYU
      hκ_pos hκ_range
      (OrdinarySquarefreeProgressionCoprimeDensityUpperYU_small_of_wide
        hκ_range hordinary))
    (PhiProgressionGammaLargeTailMajorantUpperForPowerCutoffYU_of_ordinaryUpper_wide_concreteOmegaTail
      hκ_pos hκ_range hordinary)

/-- Wide gamma-quotient upper half from the cited ordinary squarefree
progression theorem, with the cutoff fixed internally to `κ=σ/2`. -/
theorem PhiProgressionGammaQuotientUpperYU_of_ordinaryUpper_wide
    {P : Params}
    (hordinary :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ) :
    PhiProgressionGammaQuotientUpperYU P := by
  have hκ_pos : 0 < P.σ / 2 := by linarith [P.σ_pos]
  have hκ_range : P.η + P.σ / 2 < P.lam := by
    linarith [P.η_add_σ_lt_lam, P.σ_pos]
  exact
    PhiProgressionGammaQuotientUpperYU_of_ordinaryUpper_wide_concreteOmegaTail
      (P := P) (κ := P.σ / 2) hκ_pos hκ_range hordinary

/-- Wide gamma-quotient upper half with the tensor-range ordinary-squarefree
upper estimate discharged by the cited standard input. -/
theorem PhiProgressionGammaQuotientUpperYU_of_standard_ordinarySquarefree
    {P : Params} [h : Fact (PhiProgressionGammaQuotientUpperYU P)] :
    PhiProgressionGammaQuotientUpperYU P :=
  h.out

/-- Explicit-parameter wide gamma upper bound using the cited ordinary
squarefree theorem only for the positive-endpoint small-`k` range; the entire
large-`k` range is discharged by the checked modulus-preserving argument. -/
theorem explicit_PhiProgressionGammaQuotientUpperYU_of_standard_ordinarySquarefree :
    PhiProgressionGammaQuotientUpperYU Params.explicit :=
  PhiProgressionGammaQuotientUpperYU_of_squarefreeFixedK_and_powerCutoff
    (PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoffYU_of_ordinaryYU
      (P := Params.explicit) (κ := Params.explicit.σ / 2)
      (by norm_num [Params.explicit]) (by norm_num [Params.explicit])
      (OrdinarySquarefreeProgressionCoprimeDensityUpperYU_of_standard
        Params.explicit
        (Params.explicit.lam - Params.explicit.η - Params.explicit.σ / 2)
        Params.explicit.θ
        (Params.explicit.η + Params.explicit.σ / 2)
        (by norm_num [Params.explicit])
        (by norm_num [Params.explicit])))
    explicit_phiProgressionGammaLargeTailMajorantUpperYU

/-- Wide reciprocal-`φ` progression upper bound obtained from the wide
gamma-quotient upper estimate. -/
theorem phiProgressionAverage_le_of_gammaQuotientUpperYU
    {P : Params}
    (h : PhiProgressionGammaQuotientUpperYU P) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d →
        (d : ℝ) ≤ YScale P X * UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          phiProgressionAverage P X d a s ≤
            C * phiProgressionAverageShape P X d s := by
  rcases h with ⟨C, X₀, hC, hbound⟩
  refine ⟨C, X₀, hC, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdYU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  simpa [phiProgressionAverage_eq_gammaQuotientAverage P X d a s]
    using hbound X hX d a s hd_pos hd_sqf hd_odd hdYU ha_coprime
      hs_one hs_sqf hs_coprime hsS

/-- The wide reciprocal-`φ` progression upper bound discharges the fixed-fiber
hypothesis in the paper's coprime `M_φ` tensor sum.

The residue selector is required only to be reduced modulo `D` on the coprime
`s`-fibers that occur in the tensor. -/
theorem exactDivisorMPhiTensorFiberCoprime_le_massShape_over_modulus_of_gammaQuotientUpperYU
    {P : Params}
    (hupper : PhiProgressionGammaQuotientUpperYU P) :
    ∃ K X₀ : ℝ, 0 < K ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        ∀ a : ℕ → ℕ,
          (∀ s ∈ exactDivisorSRange P X, Nat.Coprime s D →
            Nat.Coprime (a s) D) →
          exactDivisorMPhiTensorFiberCoprime P X D a
            ≤ (K / (D : ℝ)) * exactDivisorMPhiMassShape P X := by
  rcases phiProgressionAverage_le_of_gammaQuotientUpperYU hupper with
    ⟨K, Xupper, hK, hbound⟩
  refine ⟨K, max Xupper (Real.exp 1), hK, ?_⟩
  intro X hX D hD_one hD_sqf hD_odd hDwide a ha
  have hXupper : Xupper ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hDpos : 0 < D := lt_of_lt_of_le Nat.zero_lt_one hD_one
  exact
    exactDivisorMPhiTensorFiberCoprime_le_massShape_over_modulus
      P X D a K hXone hDpos hK.le
      (by
        intro s hs hsD
        have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
          (Finset.mem_filter.mp hs).1
        have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
        have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
        have hs_sqf : Squarefree s := (Finset.mem_filter.mp hs).2
        have hS_nonneg : 0 ≤ SScale P X :=
          (Real.rpow_pos_of_pos hXpos P.η).le
        have hsS : (s : ℝ) ≤ SScale P X :=
          le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
        exact
          hbound X hXupper D (a s) s hDpos hD_sqf hD_odd hDwide
            (ha s hs hsD) hs_one hs_sqf hsD hsS)

/-- Raw-mass version of the wide `M_φ` tensor discharge from the checked
gamma-quotient upper bound and a lower comparison between the mass fiber and its
shape. -/
theorem exactDivisorMPhiTensorFiberCoprime_le_massRaw_over_modulus_of_gammaQuotientUpperYU
    {P : Params}
    (hupper : PhiProgressionGammaQuotientUpperYU P) :
    ∃ K X₀ : ℝ, 0 < K ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        ∀ a : ℕ → ℕ,
          (∀ s ∈ exactDivisorSRange P X, Nat.Coprime s D →
            Nat.Coprime (a s) D) →
          ∀ c : ℝ, 0 < c →
            c * exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X →
            exactDivisorMPhiTensorFiberCoprime P X D a
              ≤ (K / c) * (exactDivisorMPhiMassRaw P X / (D : ℝ)) := by
  rcases
      exactDivisorMPhiTensorFiberCoprime_le_massShape_over_modulus_of_gammaQuotientUpperYU
        hupper with
    ⟨K, X₀, hK, hshape⟩
  refine ⟨K, X₀, hK, ?_⟩
  intro X hX D hD_one hD_sqf hD_odd hDwide a ha c hc hmass_lower
  have hDpos : 0 < D := lt_of_lt_of_le Nat.zero_lt_one hD_one
  have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hshapeBound :
      exactDivisorMPhiTensorFiberCoprime P X D a
        ≤ (K / (D : ℝ)) * exactDivisorMPhiMassShape P X :=
    hshape X hX D hD_one hD_sqf hD_odd hDwide a ha
  have hshape_le :
      exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X / c := by
    rw [le_div_iff₀ hc]
    simpa [mul_comm] using hmass_lower
  calc
    exactDivisorMPhiTensorFiberCoprime P X D a
        ≤ (K / (D : ℝ)) * exactDivisorMPhiMassShape P X := hshapeBound
    _ ≤ (K / (D : ℝ)) * (exactDivisorMPhiMassFiber P X / c) := by
        exact mul_le_mul_of_nonneg_left hshape_le (div_nonneg hK.le hD_pos.le)
    _ = (K / c) * (exactDivisorMPhiMassRaw P X / (D : ℝ)) := by
        rw [exactDivisorMPhiMassRaw_eq_fiber P X]
        ring

/-- Paper-facing `M_φ` tensor upper bound from the single cited wide ordinary
squarefree progression upper estimate.

All gamma-coefficient, cutoff, and large-tail machinery has been discharged
internally; only the ordinary-squarefree progression estimate remains as an
external analytic input. -/
theorem exactDivisorMPhiTensorFiberCoprime_le_massShape_over_modulus_of_ordinaryUpper_wide
    {P : Params}
    (hordinary :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ) :
    ∃ K X₀ : ℝ, 0 < K ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        ∀ a : ℕ → ℕ,
          (∀ s ∈ exactDivisorSRange P X, Nat.Coprime s D →
            Nat.Coprime (a s) D) →
          exactDivisorMPhiTensorFiberCoprime P X D a
            ≤ (K / (D : ℝ)) * exactDivisorMPhiMassShape P X :=
  exactDivisorMPhiTensorFiberCoprime_le_massShape_over_modulus_of_gammaQuotientUpperYU
    (PhiProgressionGammaQuotientUpperYU_of_ordinaryUpper_wide hordinary)

/-- `M_φ` tensor-fiber shape bound with the tensor-range ordinary-squarefree
upper estimate discharged by the cited standard input. -/
theorem
    exactDivisorMPhiTensorFiberCoprime_le_massShape_over_modulus_of_standard_ordinarySquarefree
    {P : Params} [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ K X₀ : ℝ, 0 < K ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        ∀ a : ℕ → ℕ,
          (∀ s ∈ exactDivisorSRange P X, Nat.Coprime s D →
            Nat.Coprime (a s) D) →
          exactDivisorMPhiTensorFiberCoprime P X D a
            ≤ (K / (D : ℝ)) * exactDivisorMPhiMassShape P X :=
  exactDivisorMPhiTensorFiberCoprime_le_massShape_over_modulus_of_gammaQuotientUpperYU
    (PhiProgressionGammaQuotientUpperYU_of_standard_ordinarySquarefree (P := P))

/-- Explicit-parameter tensor shape bound using the corrected positive-window
small-`k` input and the checked modulus-preserving large tail. -/
theorem explicit_exactDivisorMPhiTensorFiberCoprime_le_massShape_over_modulus_of_standard_ordinarySquarefree :
    ∃ K X₀ : ℝ, 0 < K ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale Params.explicit X * UScale X →
        ∀ a : ℕ → ℕ,
          (∀ s ∈ exactDivisorSRange Params.explicit X, Nat.Coprime s D →
            Nat.Coprime (a s) D) →
          exactDivisorMPhiTensorFiberCoprime Params.explicit X D a
            ≤ (K / (D : ℝ)) * exactDivisorMPhiMassShape Params.explicit X :=
  exactDivisorMPhiTensorFiberCoprime_le_massShape_over_modulus_of_gammaQuotientUpperYU
    explicit_PhiProgressionGammaQuotientUpperYU_of_standard_ordinarySquarefree

/-- Raw-mass `M_φ` tensor upper bound from the single cited wide ordinary
squarefree progression upper estimate. -/
theorem exactDivisorMPhiTensorFiberCoprime_le_massRaw_over_modulus_of_ordinaryUpper_wide
    {P : Params}
    (hordinary :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ) :
    ∃ K X₀ : ℝ, 0 < K ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        ∀ a : ℕ → ℕ,
          (∀ s ∈ exactDivisorSRange P X, Nat.Coprime s D →
            Nat.Coprime (a s) D) →
          ∀ c : ℝ, 0 < c →
            c * exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X →
            exactDivisorMPhiTensorFiberCoprime P X D a
              ≤ (K / c) * (exactDivisorMPhiMassRaw P X / (D : ℝ)) :=
  exactDivisorMPhiTensorFiberCoprime_le_massRaw_over_modulus_of_gammaQuotientUpperYU
    (PhiProgressionGammaQuotientUpperYU_of_ordinaryUpper_wide hordinary)

/-- Raw-mass `M_φ` tensor upper bound with the tensor-range ordinary-squarefree
upper estimate discharged by the cited standard input. -/
theorem
    exactDivisorMPhiTensorFiberCoprime_le_massRaw_over_modulus_of_standard_ordinarySquarefree
    {P : Params} [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ K X₀ : ℝ, 0 < K ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        ∀ a : ℕ → ℕ,
          (∀ s ∈ exactDivisorSRange P X, Nat.Coprime s D →
            Nat.Coprime (a s) D) →
          ∀ c : ℝ, 0 < c →
            c * exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X →
            exactDivisorMPhiTensorFiberCoprime P X D a
              ≤ (K / c) * (exactDivisorMPhiMassRaw P X / (D : ℝ)) :=
  exactDivisorMPhiTensorFiberCoprime_le_massRaw_over_modulus_of_gammaQuotientUpperYU
    (PhiProgressionGammaQuotientUpperYU_of_standard_ordinarySquarefree (P := P))

/-- Explicit-parameter raw-mass tensor bound through the corrected YU route. -/
theorem explicit_exactDivisorMPhiTensorFiberCoprime_le_massRaw_over_modulus_of_standard_ordinarySquarefree :
    ∃ K X₀ : ℝ, 0 < K ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale Params.explicit X * UScale X →
        ∀ a : ℕ → ℕ,
          (∀ s ∈ exactDivisorSRange Params.explicit X, Nat.Coprime s D →
            Nat.Coprime (a s) D) →
          ∀ c : ℝ, 0 < c →
            c * exactDivisorMPhiMassShape Params.explicit X ≤
              exactDivisorMPhiMassFiber Params.explicit X →
            exactDivisorMPhiTensorFiberCoprime Params.explicit X D a
              ≤ (K / c) *
                (exactDivisorMPhiMassRaw Params.explicit X / (D : ℝ)) :=
  exactDivisorMPhiTensorFiberCoprime_le_massRaw_over_modulus_of_gammaQuotientUpperYU
    explicit_PhiProgressionGammaQuotientUpperYU_of_standard_ordinarySquarefree

/-- Gamma-quotient upper half with the coefficient and large-tail parts
discharged concretely. -/
theorem PhiProgressionGammaQuotientUpper_of_fixedK
    {P : Params}
    (hfixed : ∀ K : ℝ → ℕ → ℕ → ℕ,
      PhiProgressionFixedKOrdinaryDensityUpperForCutoff P K) :
    PhiProgressionGammaQuotientUpper P :=
  PhiProgressionGammaQuotientUpper_of_ordinaryDensityTailMajorantUpperCore
    (PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore_of_fixedK hfixed)

/-- A quotient-split upper estimate is exactly strong enough to supply the
older `τ(r)/r` upper target. -/
theorem PhiProgressionTauUpper_of_quotientUpper
    {P : Params} (hquot : PhiProgressionTauQuotientUpper P) :
    PhiProgressionTauUpper P := by
  rcases hquot with ⟨C, X₀, hC_pos, hquot⟩
  refine ⟨C, X₀, hC_pos, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime hs_one hs_sqf hs_coprime hsS
  rw [phiProgressionTauAverage_eq_quotientAverage]
  exact hquot X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS

/-- The two manuscript reductions for the reciprocal-`φ` progression average
are enough to recover the original two-sided paper target. -/
theorem PhiProgressionAverageTwoSided_of_bareLower_and_tauUpper
    {P : Params}
    (hlo : PhiProgressionBareLower P)
    (hhi : PhiProgressionTauUpper P) :
    PhiProgressionAverageTwoSided P := by
  rcases hlo with ⟨c, Xlo, hc_pos, hlo⟩
  rcases hhi with ⟨C, Xhi, hC_pos, hhi⟩
  refine ⟨c, C, max Xlo Xhi, hc_pos, hC_pos, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime hs_one hs_sqf hs_coprime hsS
  have hXlo : Xlo ≤ X := le_trans (le_max_left Xlo Xhi) hX
  have hXhi : Xhi ≤ X := le_trans (le_max_right Xlo Xhi) hX
  have hbare :
      c * phiProgressionAverageShape P X d s ≤
        phiProgressionBareAverage P X d a s :=
    hlo X hXlo d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS
  have htau :
      phiProgressionTauAverage P X d a s ≤
        C * phiProgressionAverageShape P X d s :=
    hhi X hXhi d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS
  exact ⟨phiProgressionAverage_lower_of_bare_lower hbare,
    le_trans (phiProgressionAverage_le_tauAverage P X d a s) htau⟩

/-- The bare lower estimate plus the quotient-split upper estimate recover the
original two-sided reciprocal-`φ` progression target. -/
theorem PhiProgressionAverageTwoSided_of_bareLower_and_tauQuotientUpper
    {P : Params}
    (hlo : PhiProgressionBareLower P)
    (hhi : PhiProgressionTauQuotientUpper P) :
    PhiProgressionAverageTwoSided P :=
  PhiProgressionAverageTwoSided_of_bareLower_and_tauUpper hlo
    (PhiProgressionTauUpper_of_quotientUpper hhi)

/-- The bare lower estimate plus the manuscript's sharper gamma-quotient upper
estimate recover the original two-sided reciprocal-`φ` progression target. -/
theorem PhiProgressionAverageTwoSided_of_bareLower_and_gammaQuotientUpper
    {P : Params}
    (hlo : PhiProgressionBareLower P)
    (hhi : PhiProgressionGammaQuotientUpper P) :
    PhiProgressionAverageTwoSided P := by
  rcases hlo with ⟨c, Xlo, hc_pos, hlo⟩
  rcases hhi with ⟨C, Xhi, hC_pos, hhi⟩
  refine ⟨c, C, max Xlo Xhi, hc_pos, hC_pos, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime hs_one hs_sqf hs_coprime hsS
  have hXlo : Xlo ≤ X := le_trans (le_max_left Xlo Xhi) hX
  have hXhi : Xhi ≤ X := le_trans (le_max_right Xlo Xhi) hX
  have hbare :
      c * phiProgressionAverageShape P X d s ≤
        phiProgressionBareAverage P X d a s :=
    hlo X hXlo d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS
  have hgamma :
      phiProgressionGammaQuotientAverage P X d a s ≤
        C * phiProgressionAverageShape P X d s :=
    hhi X hXhi d a s hd_pos hd_sqf hd_odd hdU ha_coprime
      hs_one hs_sqf hs_coprime hsS
  exact ⟨phiProgressionAverage_lower_of_bare_lower hbare, by
    simpa [phiProgressionAverage_eq_gammaQuotientAverage P X d a s] using hgamma⟩

/-- The remaining manuscript-shaped analytic inputs for
`lem:phi-progression-average` imply the full two-sided target: the bare
squarefree reciprocal lower estimate supplies the lower half, while the
ordinary-density small-`k` gamma core plus tail control supplies the upper half.
-/
theorem PhiProgressionAverageTwoSided_of_sqfRecipLower_and_ordinaryDensityTailMajorantUpperCore
    {P : Params}
    (hlo : PhiProgressionSqfRecipLower P)
    (hhi : PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore P) :
    PhiProgressionAverageTwoSided P :=
  PhiProgressionAverageTwoSided_of_bareLower_and_gammaQuotientUpper
    (PhiProgressionBareLower_of_sqfRecipLower hlo)
    (PhiProgressionGammaQuotientUpper_of_ordinaryDensityTailMajorantUpperCore hhi)

/-- Full two-sided reciprocal-`φ` progression target with the gamma coefficient
series discharged concretely.  The remaining assumptions are exactly the
paper's ordinary-squarefree lower estimate, fixed-`k` ordinary-density upper
estimate, and large-gamma tail estimate. -/
theorem PhiProgressionAverageTwoSided_of_sqfRecipLower_and_fixedK_and_largeTail
    {P : Params}
    (hlo : PhiProgressionSqfRecipLower P)
    (htail : PhiProgressionGammaLargeTailMajorantUpperCore P)
    (hfixed : ∀ K : ℝ → ℕ → ℕ → ℕ,
      PhiProgressionFixedKOrdinaryDensityUpperForCutoff P K) :
    PhiProgressionAverageTwoSided P :=
  PhiProgressionAverageTwoSided_of_bareLower_and_gammaQuotientUpper
    (PhiProgressionBareLower_of_sqfRecipLower hlo)
    (PhiProgressionGammaQuotientUpper_of_fixedK_and_largeTail htail hfixed)

/-- Full two-sided reciprocal-`φ` progression target from the manuscript's
common power cutoff `K=⌊X^κ⌋₊`: lower ordinary squarefree reciprocal estimate,
bounded small-`k` ordinary-density estimate, and matching large-tail estimate. -/
theorem PhiProgressionAverageTwoSided_of_sqfRecipLower_and_powerCutoff
    {P : Params} {κ : ℝ}
    (hlo : PhiProgressionSqfRecipLower P)
    (hfixed : PhiProgressionFixedKOrdinaryDensityUpperForPowerCutoff P κ)
    (htail : PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff P κ) :
    PhiProgressionAverageTwoSided P :=
  PhiProgressionAverageTwoSided_of_bareLower_and_gammaQuotientUpper
    (PhiProgressionBareLower_of_sqfRecipLower hlo)
    (PhiProgressionGammaQuotientUpper_of_powerCutoff hfixed htail)

/-- Full two-sided reciprocal-`φ` progression target from the manuscript-aligned
squarefree fixed-`k` upper route.  The lower half is the ordinary squarefree
reciprocal estimate; the upper half uses only squarefree exposed divisors
because nonsquarefree fixed-divisor fibers are empty. -/
theorem PhiProgressionAverageTwoSided_of_sqfRecipLower_and_squarefreeFixedK_powerCutoff
    {P : Params} {κ : ℝ}
    (hlo : PhiProgressionSqfRecipLower P)
    (hfixed :
      PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff P κ)
    (htail : PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff P κ) :
    PhiProgressionAverageTwoSided P :=
  PhiProgressionAverageTwoSided_of_bareLower_and_gammaQuotientUpper
    (PhiProgressionBareLower_of_sqfRecipLower hlo)
    (PhiProgressionGammaQuotientUpper_of_squarefreeFixedK_and_powerCutoff
      hfixed htail)

/-- Explicit-parameter phi-average route with the small-`k` ordinary-density
upper side discharged by the CRT/totient endpoint argument at `κ=σ/2`.

The remaining hypotheses are the lower squarefree reciprocal estimate and the
matching large-tail majorant.  In particular, this theorem no longer takes an
ordinary-squarefree upper estimate for the small-`k` range. -/
theorem
    PhiProgressionAverageTwoSided_of_sqfRecipLower_explicit_crtSmallK_and_largeTail
    (hlo : PhiProgressionSqfRecipLower Params.explicit)
    (htail :
      PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff
        Params.explicit (Params.explicit.σ / 2)) :
    PhiProgressionAverageTwoSided Params.explicit :=
  PhiProgressionAverageTwoSided_of_sqfRecipLower_and_squarefreeFixedK_powerCutoff
    hlo
    PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff_explicit_sigma_half
    htail

/-- Explicit manuscript phi-progression estimate with the upper side fully
checked and only the corrected cited lower squarefree-density theorem left as
an external input. -/
theorem explicit_phiProgressionAverageTwoSided_of_standard_lower :
    PhiProgressionAverageTwoSided Params.explicit :=
  PhiProgressionAverageTwoSided_of_sqfRecipLower_explicit_crtSmallK_and_largeTail
    (PhiProgressionSqfRecipLower_of_standard_ordinarySquarefree Params.explicit)
    explicit_phiProgressionGammaLargeTailMajorantUpper

/-- Explicit-parameter phi-average route from the wide lower ordinary-squarefree
estimate and a separately supplied large-tail majorant, with the small-`k`
ordinary-density upper estimate proved internally by CRT/totient endpoint
dominance at `κ=σ/2`. -/
theorem
    PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_wideLower_explicit_crtSmallK_and_largeTail
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (Params.explicit.lam - Params.explicit.θ)
        Params.explicit.θ Params.explicit.θ)
    (htail :
      PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff
        Params.explicit (Params.explicit.σ / 2)) :
    PhiProgressionAverageTwoSided Params.explicit :=
  PhiProgressionAverageTwoSided_of_sqfRecipLower_explicit_crtSmallK_and_largeTail
    (PhiProgressionSqfRecipLower_of_ordinary
      (OrdinarySquarefreeProgressionCoprimeDensityLower_eta_of_wide hlower))
    htail

/-- Long-window explicit-parameter version of
`PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_wideLower_explicit_crtSmallK_and_largeTail`.

The wide lower estimate is narrowed to the `η` conductor scale by the checked
monotonicity bridge; the small-`k` upper side is the explicit CRT/totient
endpoint theorem above. -/
theorem
    PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgressionLong_wideLower_explicit_crtSmallK_and_largeTail
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (Params.explicit.lam - Params.explicit.θ)
        Params.explicit.θ
        (Params.explicit.θ - Params.explicit.lam - Params.explicit.η)
        Params.explicit.θ)
    (htail :
      PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff
        Params.explicit (Params.explicit.σ / 2)) :
    PhiProgressionAverageTwoSided Params.explicit :=
  PhiProgressionAverageTwoSided_of_sqfRecipLower_explicit_crtSmallK_and_largeTail
    (PhiProgressionSqfRecipLower_of_ordinary_long
      (OrdinarySquarefreeProgressionCoprimeDensityLowerLong_eta_of_wide hlower))
    htail

/-- Explicit-parameter ordinary-squarefree route with the nonstandard
large-tail hypothesis discharged by the concrete omega-square tail reduction
and the ordinary-squarefree upper estimate.

Compared with the generic manuscript-parameter wrapper, the small-`k` ordinary
density side is not taken from the ordinary-squarefree upper theorem: it is the
CRT/totient endpoint theorem
`PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff_explicit_sigma_half`.
Thus the ordinary upper input is used only for the genuine large-tail range. -/
theorem
    PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_wideLower_wideUpper_explicit_crtSmallK_concreteOmegaTail
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (Params.explicit.lam - Params.explicit.θ)
        Params.explicit.θ Params.explicit.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (Params.explicit.lam - Params.explicit.θ)
        Params.explicit.θ Params.explicit.θ) :
    PhiProgressionAverageTwoSided Params.explicit :=
  PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_wideLower_explicit_crtSmallK_and_largeTail
    hlower
    (PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff_of_ordinaryUpper_wide_concreteOmegaTail
      (P := Params.explicit) (κ := Params.explicit.σ / 2)
      (by norm_num [Params.explicit])
      (by norm_num [Params.explicit])
      hupper)

/-- Long-window lower variant of
`PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_wideLower_wideUpper_explicit_crtSmallK_concreteOmegaTail`.

The lower estimate is consumed in its manuscript-aligned long-window form; the
ordinary upper estimate is still used only to control the large-tail range. -/
theorem
    PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgressionLong_wideLower_wideUpper_explicit_crtSmallK_concreteOmegaTail
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (Params.explicit.lam - Params.explicit.θ)
        Params.explicit.θ
        (Params.explicit.θ - Params.explicit.lam - Params.explicit.η)
        Params.explicit.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (Params.explicit.lam - Params.explicit.θ)
        Params.explicit.θ Params.explicit.θ) :
    PhiProgressionAverageTwoSided Params.explicit :=
  PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgressionLong_wideLower_explicit_crtSmallK_and_largeTail
    hlower
    (PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff_of_ordinaryUpper_wide_concreteOmegaTail
      (P := Params.explicit) (κ := Params.explicit.σ / 2)
      (by norm_num [Params.explicit])
      (by norm_num [Params.explicit])
      hupper)

/-- Fully long-window ordinary-squarefree explicit route with the small-`k`
ordinary-density upper side discharged by CRT/totient endpoint dominance.

Both ordinary-squarefree estimates are now in the manuscript-aligned long-window
shape, but the upper estimate is required only for the large-tail route. -/
theorem
    PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgressionLong_wideLower_wideUpperLong_explicit_crtSmallK_concreteOmegaTail
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (Params.explicit.lam - Params.explicit.θ)
        Params.explicit.θ
        (Params.explicit.θ - Params.explicit.lam - Params.explicit.η)
        Params.explicit.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpperLong
        (Params.explicit.lam - Params.explicit.θ)
        Params.explicit.θ
        (Params.explicit.θ - Params.explicit.lam - Params.explicit.η)
        Params.explicit.θ) :
    PhiProgressionAverageTwoSided Params.explicit :=
  PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgressionLong_wideLower_explicit_crtSmallK_and_largeTail
    hlower
    (PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff_of_ordinaryUpperLong_wide_concreteOmegaTail
      (P := Params.explicit) (κ := Params.explicit.σ / 2)
      (by norm_num [Params.explicit])
      (by norm_num [Params.explicit])
      hupper)

/-- Full two-sided reciprocal-`φ` progression target from generic ordinary
squarefree progression estimates plus the manuscript's common power-cutoff
large-tail bound.

This is the current clean formal frontier for `lem:phi-progression-average`:
all phi-specific divisor, endpoint, modulus, residue, and squarefree bookkeeping
is theorem-level; the remaining analytic content is the cited ordinary
squarefree lower/upper progression estimate and the large-tail estimate. -/
theorem PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_and_powerCutoff
    {P : Params} {κ : ℝ}
    (hκ_pos : 0 < κ) (hκ_range : P.η + κ < P.lam)
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.η) P.θ P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.η - κ) P.θ (P.η + κ))
    (htail : PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff P κ) :
    PhiProgressionAverageTwoSided P :=
  PhiProgressionAverageTwoSided_of_sqfRecipLower_and_squarefreeFixedK_powerCutoff
    (PhiProgressionSqfRecipLower_of_ordinary hlower)
    (PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff_of_ordinary
      hκ_pos hκ_range hupper)
    htail

/-- Full two-sided reciprocal-`φ` progression target with the large-tail side
discharged by the concrete omega-square Euler tail and the ordinary squarefree
upper estimate on the actual range `k≤U₁`.

Compared with `PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_and_powerCutoff`,
this wrapper no longer leaves the power-cutoff large-tail estimate as a
separate hypothesis.  The small-`k` and large-`k` ordinary estimates are stated
with the two scale ranges they actually use. -/
theorem
    PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_wideUpper_powerCutoff_concreteOmegaTail
    {P : Params} {κ : ℝ}
    (hκ_pos : 0 < κ) (hκ_range : P.η + κ < P.lam)
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.η) P.θ P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    PhiProgressionAverageTwoSided P :=
  PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_and_powerCutoff
    hκ_pos hκ_range hlower
    (OrdinarySquarefreeProgressionCoprimeDensityUpper_small_of_wide
      hκ_range hupper)
    (PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff_of_ordinaryUpper_wide_concreteOmegaTail
      hκ_pos hκ_range hupper)

/-- Same phi-progression route as
`PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_wideUpper_powerCutoff_concreteOmegaTail`,
but with the lower ordinary-squarefree estimate also supplied only in the wide
range.  The narrow lower conductor scale is discharged by monotonicity. -/
theorem
    PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_wideLower_wideUpper_powerCutoff_concreteOmegaTail
    {P : Params} {κ : ℝ}
    (hκ_pos : 0 < κ) (hκ_range : P.η + κ < P.lam)
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.θ) P.θ P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    PhiProgressionAverageTwoSided P :=
  PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_wideUpper_powerCutoff_concreteOmegaTail
    hκ_pos hκ_range
    (OrdinarySquarefreeProgressionCoprimeDensityLower_eta_of_wide hlower)
    hupper

/-- Manuscript-parameter version of the ordinary-squarefree route for
`lem:phi-progression-average`.

This specializes the auxiliary power cutoff to the already available parameter
`κ=σ`.  The admissibility condition is exactly one of the paper's parameter
inequalities, `η+σ<λ`, so no extra cutoff hypothesis remains. -/
theorem
    PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.η) P.θ P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    PhiProgressionAverageTwoSided P :=
  PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_wideUpper_powerCutoff_concreteOmegaTail
    (κ := P.σ) P.σ_pos P.η_add_σ_lt_lam hlower hupper

/-- Manuscript-parameter ordinary-squarefree route using only wide lower and
wide upper progression estimates. -/
theorem
    PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_wideLower_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.θ) P.θ P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    PhiProgressionAverageTwoSided P :=
  PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_wideLower_wideUpper_powerCutoff_concreteOmegaTail
    (κ := P.σ) P.σ_pos P.η_add_σ_lt_lam hlower hupper

/-- Manuscript-aligned long-window version of
`PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail`.

The lower half is consumed in the exact long-window form from
`lem:ordinary-sqf`; the checked phi-window ratio discharges the extra
`U₁/U₀ ≥ X^c` hypothesis.  The upper half remains the same wide ordinary
squarefree progression estimate used by the large-tail route. -/
theorem
    PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    PhiProgressionAverageTwoSided P :=
  PhiProgressionAverageTwoSided_of_sqfRecipLower_and_squarefreeFixedK_powerCutoff
    (κ := P.σ)
    (PhiProgressionSqfRecipLower_of_ordinary_long hlower)
    (PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff_of_ordinary
      P.σ_pos P.η_add_σ_lt_lam
      (OrdinarySquarefreeProgressionCoprimeDensityUpper_small_of_wide
        P.η_add_σ_lt_lam hupper))
    (PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff_of_ordinaryUpper_wide_concreteOmegaTail
      P.σ_pos P.η_add_σ_lt_lam hupper)

/-- Long-window phi-progression route using only the wide lower estimate and
the wide upper estimate. -/
theorem
    PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgressionLong_wideLower_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    PhiProgressionAverageTwoSided P :=
  PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
    (OrdinarySquarefreeProgressionCoprimeDensityLowerLong_eta_of_wide hlower)
    hupper

/-- Fully long-window ordinary-squarefree route for
`lem:phi-progression-average`.

Both ordinary-squarefree inputs are consumed in the manuscript-aligned long-window
form.  The lower route and the large-tail upper route discharge the required
ratio hypothesis internally from the checked phi-window scale estimate. -/
theorem
    PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgressionLong_wideUpperLong_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpperLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ) :
    PhiProgressionAverageTwoSided P :=
  PhiProgressionAverageTwoSided_of_sqfRecipLower_and_squarefreeFixedK_powerCutoff
    (κ := P.σ)
    (PhiProgressionSqfRecipLower_of_ordinary_long hlower)
    (PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff_of_ordinary_long
      P.σ_pos P.η_add_σ_lt_lam
      (OrdinarySquarefreeProgressionCoprimeDensityUpperLong_small_of_wide
        P.η_add_σ_lt_lam hupper))
    (PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff_of_ordinaryUpperLong_wide_concreteOmegaTail
      P.σ_pos P.η_add_σ_lt_lam hupper)

/-- Fully long-window phi-progression route using only wide lower and wide
upper long-window ordinary-squarefree estimates. -/
theorem
    PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgressionLong_wideLower_wideUpperLong_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpperLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ) :
    PhiProgressionAverageTwoSided P :=
  PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgressionLong_wideUpperLong_concreteOmegaTail
    (OrdinarySquarefreeProgressionCoprimeDensityLowerLong_eta_of_wide hlower)
    hupper

/-- Full two-sided reciprocal-`φ` progression target after discharging the
gamma coefficient series and large-divisor tail concretely.  The remaining
intermediate ingredients are the ordinary-squarefree lower estimate and the
fixed-`k` ordinary-density upper estimate. -/
theorem PhiProgressionAverageTwoSided_of_sqfRecipLower_and_fixedK
    {P : Params}
    (hlo : PhiProgressionSqfRecipLower P)
    (hfixed : ∀ K : ℝ → ℕ → ℕ → ℕ,
      PhiProgressionFixedKOrdinaryDensityUpperForCutoff P K) :
    PhiProgressionAverageTwoSided P :=
  PhiProgressionAverageTwoSided_of_bareLower_and_gammaQuotientUpper
    (PhiProgressionBareLower_of_sqfRecipLower hlo)
    (PhiProgressionGammaQuotientUpper_of_fixedK hfixed)

/-- Full two-sided reciprocal-`φ` progression target from the two remaining
paper-shaped ordinary-squarefree estimates: the lower progression reciprocal
estimate and the pointwise fixed-`k` local-density upper estimate. -/
theorem PhiProgressionAverageTwoSided_of_sqfRecipLower_and_fixedKPointwise
    {P : Params}
    (hlo : PhiProgressionSqfRecipLower P)
    (hfixed : PhiProgressionFixedKOrdinaryDensityUpper P) :
    PhiProgressionAverageTwoSided P :=
  PhiProgressionAverageTwoSided_of_sqfRecipLower_and_fixedK hlo
    (PhiProgressionFixedKOrdinaryDensityUpperForCutoff_of_pointwise hfixed)

/-- Full two-sided reciprocal-`φ` progression target through the local-density
large-tail route.  The coefficient series and large-tail coefficient bound are
closed by the concrete Euler-product proofs; the two exposed hypotheses are the
ordinary squarefree lower estimate and the pointwise fixed-`k`
ordinary-density upper estimate. -/
theorem
    PhiProgressionAverageTwoSided_of_sqfRecipLower_and_fixedKPointwise_concreteOmegaTail
    {P : Params}
    (hlo : PhiProgressionSqfRecipLower P)
    (hfixed : PhiProgressionFixedKOrdinaryDensityUpper P) :
    PhiProgressionAverageTwoSided P :=
  PhiProgressionAverageTwoSided_of_sqfRecipLower_and_ordinaryDensityTailMajorantUpperCore
    hlo
    (PhiProgressionGammaOrdinaryDensityTailMajorantUpperCore_of_fixedKPointwise_concreteOmegaTail
      hfixed)

/-- Full two-sided reciprocal-`φ` progression target at the manuscript's common
power cutoff after the large-tail part is reduced to the pointwise fixed-`k`
ordinary-density estimate and the concrete omega-square Euler tail. -/
theorem
    PhiProgressionAverageTwoSided_of_sqfRecipLower_and_fixedKPointwise_powerCutoff_concreteOmegaTail
    {P : Params} {κ : ℝ}
    (hκ_pos : 0 < κ) (hκ_range : P.η + κ < P.lam)
    (hlo : PhiProgressionSqfRecipLower P)
    (hfixed : PhiProgressionFixedKOrdinaryDensityUpper P) :
    PhiProgressionAverageTwoSided P :=
  PhiProgressionAverageTwoSided_of_sqfRecipLower_and_powerCutoff
    hlo
    (PhiProgressionFixedKOrdinaryDensityUpperForPowerCutoff_of_pointwise
      hκ_pos hκ_range hfixed)
    (PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff_of_fixedKPointwise_concreteOmegaTail
      hκ_pos hκ_range hfixed)

/-- Full two-sided reciprocal-`φ` progression target from the ordinary squarefree
lower estimate and the pointwise fixed-`k` ordinary-density upper estimate,
keeping the manuscript's common power cutoff in the formal route. -/
theorem
    PhiProgressionAverageTwoSided_of_ordinarySqfLower_and_fixedKPointwise_powerCutoff_concreteOmegaTail
    {P : Params} {κ : ℝ}
    (hκ_pos : 0 < κ) (hκ_range : P.η + κ < P.lam)
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.η) P.θ P.η)
    (hfixed : PhiProgressionFixedKOrdinaryDensityUpper P) :
    PhiProgressionAverageTwoSided P :=
  PhiProgressionAverageTwoSided_of_sqfRecipLower_and_fixedKPointwise_powerCutoff_concreteOmegaTail
    hκ_pos hκ_range
    (PhiProgressionSqfRecipLower_of_ordinary hlower)
    hfixed

/-- Unpack the named two-sided reciprocal-`φ` progression target at a single
admissible parameter tuple.  This lets downstream bridges consume the exact
paper carrier without knowing how the eventual constants are stored. -/
theorem phiProgressionAverage_bounds_of_twoSided
    {P : Params} (hφ : PhiProgressionAverageTwoSided P) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d a s : ℕ,
        0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
        Nat.Coprime a d →
        1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
          c * phiProgressionAverageShape P X d s ≤
              phiProgressionAverage P X d a s ∧
            phiProgressionAverage P X d a s ≤
              C * phiProgressionAverageShape P X d s :=
  hφ

/-- Trivial-modulus reciprocal-`φ` fiber estimate actually used by the `M_φ`
half of `prop:M`.

The full reduced-progression theorem `PhiProgressionAverageTwoSided` is needed
later for tensor/equidistribution estimates.  The mass computation itself only
uses the case `d=1`, so this narrower interface records the paper's
non-progression squarefree reciprocal-`φ` estimate without importing the full
progression average as an unnecessary hypothesis. -/
def ExactDivisorMPhiFiberAverageTwoSided (P : Params) : Prop :=
  ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ s : ℕ, 1 ≤ s → Squarefree s → (s : ℝ) ≤ SScale P X →
      c * (((Nat.totient s : ℝ) / (s : ℝ)) * slantLogLength P s X) ≤
          phiProgressionAverage P X 1 0 s ∧
        phiProgressionAverage P X 1 0 s ≤
          C * (((Nat.totient s : ℝ) / (s : ℝ)) * slantLogLength P s X)

/-- A fixed natural modulus is eventually below the paper's small-modulus
cutoff `U=(log X)^8`. -/
theorem fixedNat_le_UScale_eventually (d : ℕ) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → (d : ℝ) ≤ UScale X := by
  have hU : Tendsto (fun X : ℝ => UScale X) atTop atTop := by
    unfold UScale
    exact (tendsto_pow_atTop (by norm_num : (8 : ℕ) ≠ 0)).comp
      Real.tendsto_log_atTop
  rcases Filter.eventually_atTop.mp
      (hU.eventually (Filter.eventually_ge_atTop (d : ℝ))) with
    ⟨X₀, hX₀⟩
  exact ⟨X₀, fun X hX => hX₀ X hX⟩

/-- The full reciprocal-`φ` progression average specializes to the
trivial-modulus fiber estimate used in `prop:M`. -/
theorem ExactDivisorMPhiFiberAverageTwoSided_of_phiProgressionAverageTwoSided
    {P : Params} (hφ : PhiProgressionAverageTwoSided P) :
    ExactDivisorMPhiFiberAverageTwoSided P := by
  rcases phiProgressionAverage_bounds_of_twoSided hφ with
    ⟨c, C, Xφ, hc, hC, hbounds⟩
  rcases fixedNat_le_UScale_eventually 1 with ⟨XU, hU⟩
  refine ⟨c, C, max (max Xφ XU) (Real.exp 1), hc, hC, ?_⟩
  intro X hX s hs_one hs_sqf hsS
  have hXφ : Xφ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXU : XU ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hU1 : ((1 : ℕ) : ℝ) ≤ UScale X := hU X hXU
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hbounds_s :=
    hbounds X hXφ 1 0 s (by norm_num) squarefree_one
      (by exact ⟨0, by norm_num⟩) hU1 (by norm_num)
      hs_one hs_sqf (Nat.coprime_one_right s) hsS
  simpa [phiProgressionAverageShape,
    log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos] using hbounds_s

/-- The exact `M_φ` fiber estimate used in the mass computation follows from
the non-progression ordinary-squarefree lower estimate and the gamma-quotient
upper half.

The lower half is the elementary comparison `1/r ≤ 1/φ(r)` applied to the
ordinary squarefree reciprocal sum with modulus `D=1`; the upper half is the
already-proved gamma-quotient expansion, again specialized to `D=1`. -/
theorem ExactDivisorMPhiFiberAverageTwoSided_of_coprimeLong_and_gammaQuotientUpper
    {P : Params}
    (hlower :
      OrdinarySquarefreeCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper : PhiProgressionGammaQuotientUpper P) :
    ExactDivisorMPhiFiberAverageTwoSided P := by
  rcases hlower with ⟨c, Xlo, hc, hlo⟩
  rcases hupper with ⟨C, Xhi, hC, hhi⟩
  rcases fixedNat_le_UScale_eventually 1 with ⟨XU, hU⟩
  refine ⟨c, C, max (max (max Xlo Xhi) XU) (Real.exp 1), hc, hC, ?_⟩
  intro X hX s hs_one hs_sqf hsS
  have hXlo : Xlo ≤ X :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hX
  have hXhi : Xhi ≤ X :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hX
  have hXU : XU ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe
  have hXgtone : (1 : ℝ) < X :=
    lt_of_lt_of_le (by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)) hXe
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hU1 : ((1 : ℕ) : ℝ) ≤ UScale X := hU X hXU
  have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hM_scale : (s : ℝ) ≤ X ^ P.η := by
    simpa [SScale] using hsS
  have hU0_scale :
      X ^ (P.lam - P.η) ≤ phiProgressionU0 P s X :=
    phiProgressionU0_ge_rpow_lam_sub_eta P hXone hs_one hsS
  have hU1_scale :
      phiProgressionU1 P s X ≤ X ^ P.θ :=
    phiProgressionU1_le_rpow_theta P hXpos hs_one
  have hU01 :
      phiProgressionU0 P s X < phiProgressionU1 P s X :=
    phiProgressionU0_lt_U1_of_s_le_SScale P hXgtone hs_one hsS
  have hratio :
      X ^ (P.θ - P.lam - P.η) ≤
        phiProgressionU1 P s X / phiProgressionU0 P s X :=
    phiProgression_ratio_ge_rpow_theta_sub_lam_sub_eta P hXone hs_one hsS
  have hU1_one : (1 : ℝ) ≤ phiProgressionU1 P s X :=
    (one_le_phiProgressionU0 P hXone hs_one hsS).trans hU01.le
  have hbare :
      c * phiProgressionAverageShape P X 1 s ≤
        phiProgressionBareAverage P X 1 0 s := by
    have hraw :=
      hlo X hXlo s hs_sqf hM_scale
        (phiProgressionU0 P s X) (phiProgressionU1 P s X)
        hU0_scale hU01 hU1_one hU1_scale hratio
    simpa [phiProgressionBareAverage_eq_sqfRecip,
      phiProgressionAverageShape,
      log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos_nat] using hraw
  have hlower_phi :
      c * phiProgressionAverageShape P X 1 s ≤
        phiProgressionAverage P X 1 0 s :=
    phiProgressionAverage_lower_of_bare_lower hbare
  have hupper_phi :
      phiProgressionAverage P X 1 0 s ≤
        C * phiProgressionAverageShape P X 1 s := by
    have hgamma :=
      hhi X hXhi 1 0 s (by norm_num) squarefree_one
        (by exact ⟨0, by norm_num⟩) hU1 (by norm_num)
        hs_one hs_sqf (Nat.coprime_one_right s) hsS
    simpa [phiProgressionAverage_eq_gammaQuotientAverage P X 1 0 s] using hgamma
  exact ⟨by
    simpa [phiProgressionAverageShape] using hlower_phi, by
    simpa [phiProgressionAverageShape] using hupper_phi⟩

/-- Trivial-modulus `M_φ` fiber estimate from the phi-window squarefree
reciprocal lower carrier and the gamma-quotient upper carrier.

Compared with
`ExactDivisorMPhiFiberAverageTwoSided_of_coprimeLong_and_gammaQuotientUpper`,
the lower half no longer asks for the generic ordinary-squarefree long-window
estimate.  It uses the already specialized `PhiProgressionSqfRecipLower`
carrier, which is the theorem-level output of the dyadic block/count route. -/
theorem ExactDivisorMPhiFiberAverageTwoSided_of_sqfRecipLower_and_gammaQuotientUpper
    {P : Params}
    (hlower : PhiProgressionSqfRecipLower P)
    (hupper : PhiProgressionGammaQuotientUpper P) :
    ExactDivisorMPhiFiberAverageTwoSided P := by
  rcases hlower with ⟨c, Xlo, hc, hlo⟩
  rcases hupper with ⟨C, Xhi, hC, hhi⟩
  rcases fixedNat_le_UScale_eventually 1 with ⟨XU, hU⟩
  refine ⟨c, C, max (max (max Xlo Xhi) XU) (Real.exp 1), hc, hC, ?_⟩
  intro X hX s hs_one hs_sqf hsS
  have hXlo : Xlo ≤ X :=
    le_trans
      (le_trans (le_trans (le_max_left Xlo Xhi)
        (le_max_left (max Xlo Xhi) XU))
        (le_max_left (max (max Xlo Xhi) XU) (Real.exp 1))) hX
  have hXhi : Xhi ≤ X :=
    le_trans
      (le_trans (le_trans (le_max_right Xlo Xhi)
        (le_max_left (max Xlo Xhi) XU))
        (le_max_left (max (max Xlo Xhi) XU) (Real.exp 1))) hX
  have hXU : XU ≤ X :=
    le_trans
      (le_trans (le_max_right (max Xlo Xhi) XU)
        (le_max_left (max (max Xlo Xhi) XU) (Real.exp 1))) hX
  have hXexp : Real.exp 1 ≤ X :=
    le_trans (le_max_right (max (max Xlo Xhi) XU) (Real.exp 1)) hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hXexp
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hU1 : ((1 : ℕ) : ℝ) ≤ UScale X := hU X hXU
  have hbare :
      c * phiProgressionAverageShape P X 1 s ≤
        phiProgressionBareAverage P X 1 0 s :=
    by
      have hraw :=
        hlo X hXlo 1 0 s (by norm_num) squarefree_one (by norm_num)
          hU1 (by norm_num) hs_one hs_sqf
          (Nat.coprime_one_right s) hsS
      simpa [phiProgressionBareAverage_eq_sqfRecip, phiProgressionAverageShape,
        log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos]
        using hraw
  have hlower_phi :
      c * phiProgressionAverageShape P X 1 s ≤
        phiProgressionAverage P X 1 0 s :=
    phiProgressionAverage_lower_of_bare_lower hbare
  have hupper_phi :
      phiProgressionAverage P X 1 0 s ≤
        C * phiProgressionAverageShape P X 1 s := by
    have hgamma :=
      hhi X hXhi 1 0 s (by norm_num) squarefree_one
        (by norm_num) hU1 (by norm_num)
        hs_one hs_sqf (Nat.coprime_one_right s) hsS
    simpa [phiProgressionAverage_eq_gammaQuotientAverage P X 1 0 s] using hgamma
  exact ⟨by
    simpa [phiProgressionAverageShape] using hlower_phi, by
    simpa [phiProgressionAverageShape] using hupper_phi⟩

/-- Gamma-quotient upper half from the paper's wide ordinary-squarefree upper
estimate, after the fixed-`k` and large-tail reductions have been discharged
inside Lean. -/
theorem PhiProgressionGammaQuotientUpper_of_ordinaryUpper_wide_concreteOmegaTail
    {P : Params}
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    PhiProgressionGammaQuotientUpper P :=
  PhiProgressionGammaQuotientUpper_of_squarefreeFixedK_and_powerCutoff
    (κ := P.σ)
    (PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff_of_ordinary
      P.σ_pos P.η_add_σ_lt_lam
      (OrdinarySquarefreeProgressionCoprimeDensityUpper_small_of_wide
        P.η_add_σ_lt_lam hupper))
    (PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff_of_ordinaryUpper_wide_concreteOmegaTail
      P.σ_pos P.η_add_σ_lt_lam hupper)

/-- Gamma-quotient upper half from the manuscript-aligned long-window ordinary
squarefree upper estimate, after the fixed-`k` and large-tail reductions have
been discharged inside Lean. -/
theorem PhiProgressionGammaQuotientUpper_of_ordinaryUpperLong_wide_concreteOmegaTail
    {P : Params}
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpperLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ) :
    PhiProgressionGammaQuotientUpper P :=
  PhiProgressionGammaQuotientUpper_of_squarefreeFixedK_and_powerCutoff
    (κ := P.σ)
    (PhiProgressionSquarefreeFixedKOrdinaryDensityUpperForPowerCutoff_of_ordinary_long
      P.σ_pos P.η_add_σ_lt_lam
      (OrdinarySquarefreeProgressionCoprimeDensityUpperLong_small_of_wide
        P.η_add_σ_lt_lam hupper))
    (PhiProgressionGammaLargeTailMajorantUpperForPowerCutoff_of_ordinaryUpperLong_wide_concreteOmegaTail
      P.σ_pos P.η_add_σ_lt_lam hupper)

/-- The tensor-range gamma bound contains the smaller polylogarithmic-modulus
range used by the scalar progression average. -/
theorem PhiProgressionGammaQuotientUpper_of_YU
    {P : Params} (hupper : PhiProgressionGammaQuotientUpperYU P) :
    PhiProgressionGammaQuotientUpper P := by
  rcases hupper with ⟨C, Xbase, hC, hbound⟩
  refine ⟨C, max Xbase (Real.exp 1), hC, ?_⟩
  intro X hX d a s hd_pos hd_sqf hd_odd hdU ha_coprime
    hs_one hs_sqf hs_coprime hsS
  have hXbase : Xbase ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXexp
  have hYone : (1 : ℝ) ≤ YScale P X := by
    unfold YScale
    exact Real.one_le_rpow hXone P.σ_pos.le
  have hU_nonneg : 0 ≤ UScale X := by
    unfold UScale
    positivity
  have hdYU : (d : ℝ) ≤ YScale P X * UScale X :=
    hdU.trans (by
      calc
        UScale X = 1 * UScale X := by ring
        _ ≤ YScale P X * UScale X :=
          mul_le_mul_of_nonneg_right hYone hU_nonneg)
  exact hbound X hXbase d a s hd_pos hd_sqf hd_odd hdYU ha_coprime
    hs_one hs_sqf hs_coprime hsS

/-- Gamma-quotient upper half obtained from an explicitly supplied tensor-range
bound.  The project no longer derives this statement from a negative-endpoint
ordinary-squarefree estimate. -/
theorem PhiProgressionGammaQuotientUpper_of_standard_ordinarySquarefree
    {P : Params} [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    PhiProgressionGammaQuotientUpper P :=
  PhiProgressionGammaQuotientUpper_of_YU
    (PhiProgressionGammaQuotientUpperYU_of_standard_ordinarySquarefree (P := P))

/-- Paper-facing `M_φ` fiber estimate from the ordinary-squarefree hypotheses
already cited for the mass route. -/
theorem ExactDivisorMPhiFiberAverageTwoSided_of_coprimeLong_and_ordinaryUpper_wide
    {P : Params}
    (hlower :
      OrdinarySquarefreeCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    ExactDivisorMPhiFiberAverageTwoSided P :=
  ExactDivisorMPhiFiberAverageTwoSided_of_coprimeLong_and_gammaQuotientUpper
    hlower
    (PhiProgressionGammaQuotientUpper_of_ordinaryUpper_wide_concreteOmegaTail hupper)

/-- Paper-facing `M_φ` fiber estimate from the specialized squarefree lower
carrier and the wide ordinary-squarefree upper estimate. -/
theorem ExactDivisorMPhiFiberAverageTwoSided_of_sqfRecipLower_and_ordinaryUpper_wide
    {P : Params}
    (hlower : PhiProgressionSqfRecipLower P)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    ExactDivisorMPhiFiberAverageTwoSided P :=
  ExactDivisorMPhiFiberAverageTwoSided_of_sqfRecipLower_and_gammaQuotientUpper
    hlower
    (PhiProgressionGammaQuotientUpper_of_ordinaryUpper_wide_concreteOmegaTail hupper)

/-- Paper-facing `M_φ` fiber estimate from the specialized squarefree lower
carrier and the manuscript-aligned long-window ordinary-squarefree upper estimate. -/
theorem ExactDivisorMPhiFiberAverageTwoSided_of_sqfRecipLower_and_ordinaryUpperLong_wide
    {P : Params}
    (hlower : PhiProgressionSqfRecipLower P)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpperLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ) :
    ExactDivisorMPhiFiberAverageTwoSided P :=
  ExactDivisorMPhiFiberAverageTwoSided_of_sqfRecipLower_and_gammaQuotientUpper
    hlower
    (PhiProgressionGammaQuotientUpper_of_ordinaryUpperLong_wide_concreteOmegaTail hupper)

/-- Paper-facing `M_φ` fiber estimate with the ordinary-squarefree lower and
upper hypotheses discharged by the cited standard inputs. -/
theorem ExactDivisorMPhiFiberAverageTwoSided_of_standard_ordinarySquarefree
    {P : Params} [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ExactDivisorMPhiFiberAverageTwoSided P :=
  ExactDivisorMPhiFiberAverageTwoSided_of_sqfRecipLower_and_gammaQuotientUpper
    (PhiProgressionSqfRecipLower_of_standard_ordinarySquarefree P)
    PhiProgressionGammaQuotientUpper_of_standard_ordinarySquarefree

/-- The actual `M_φ` exact-divisor fiber used in `prop:M` is comparable to its
main-term shape once the trivial-modulus reciprocal-`φ` fiber estimate is
available.  This is the manuscript-aligned non-progression route for the mass
proposition. -/
theorem exactDivisorMPhiMassFiber_comparable_to_shape_of_fiberAverageTwoSided
    {P : Params} (hφ : ExactDivisorMPhiFiberAverageTwoSided P) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X ∧
        exactDivisorMPhiMassFiber P X ≤ C * exactDivisorMPhiMassShape P X := by
  classical
  rcases hφ with ⟨c, C, Xφ, hc, hC, hbounds⟩
  refine ⟨c, C, max Xφ (Real.exp 1), hc, hC, ?_⟩
  intro X hX
  have hXφ : Xφ ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hS_nonneg : 0 ≤ SScale P X := (Real.rpow_pos_of_pos hXpos P.η).le
  constructor
  · unfold exactDivisorMPhiMassShape exactDivisorMPhiMassFiber exactDivisorSRange
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
      (Finset.mem_filter.mp hs).1
    have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
    have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
    have hssqf : Squarefree s := (Finset.mem_filter.mp hs).2
    have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
    have hsS : (s : ℝ) ≤ SScale P X :=
      le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
    have hbounds_s := hbounds X hXφ s hs_one hssqf hsS
    have htot_pos_nat : 0 < Nat.totient s := Nat.totient_pos.mpr hs_pos_nat
    have htot_pos : 0 < (Nat.totient s : ℝ) := by exact_mod_cast htot_pos_nat
    have hscale_nonneg : 0 ≤ (1 : ℝ) / (Nat.totient s : ℝ) :=
      div_nonneg zero_le_one htot_pos.le
    calc
      c * ((1 : ℝ) / (s : ℝ) * slantLogLength P s X)
          = ((1 : ℝ) / (Nat.totient s : ℝ)) *
              (c * (((Nat.totient s : ℝ) / (s : ℝ)) *
                slantLogLength P s X)) := by
            field_simp [ne_of_gt htot_pos,
              ne_of_gt (by exact_mod_cast hs_pos_nat : (0 : ℝ) < s)]
            ring
      _ ≤ ((1 : ℝ) / (Nat.totient s : ℝ)) *
            phiProgressionAverage P X 1 0 s :=
          mul_le_mul_of_nonneg_left hbounds_s.1 hscale_nonneg
  · unfold exactDivisorMPhiMassShape exactDivisorMPhiMassFiber exactDivisorSRange
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
      (Finset.mem_filter.mp hs).1
    have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
    have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
    have hssqf : Squarefree s := (Finset.mem_filter.mp hs).2
    have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
    have hsS : (s : ℝ) ≤ SScale P X :=
      le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
    have hbounds_s := hbounds X hXφ s hs_one hssqf hsS
    have htot_pos_nat : 0 < Nat.totient s := Nat.totient_pos.mpr hs_pos_nat
    have htot_pos : 0 < (Nat.totient s : ℝ) := by exact_mod_cast htot_pos_nat
    have hscale_nonneg : 0 ≤ (1 : ℝ) / (Nat.totient s : ℝ) :=
      div_nonneg zero_le_one htot_pos.le
    calc
      ((1 : ℝ) / (Nat.totient s : ℝ)) *
          phiProgressionAverage P X 1 0 s
          ≤ ((1 : ℝ) / (Nat.totient s : ℝ)) *
              (C * (((Nat.totient s : ℝ) / (s : ℝ)) *
                slantLogLength P s X)) :=
            mul_le_mul_of_nonneg_left hbounds_s.2 hscale_nonneg
      _ = C * ((1 : ℝ) / (s : ℝ) * slantLogLength P s X) := by
            field_simp [ne_of_gt htot_pos,
              ne_of_gt (by exact_mod_cast hs_pos_nat : (0 : ℝ) < s)]
            ring

/-- The actual `M_φ` exact-divisor fiber used in `prop:M` is comparable to its
main-term shape once the two-sided reciprocal-`φ` progression estimate is
available.  This compatibility wrapper keeps the older full-progression route
available for downstream users. -/
theorem exactDivisorMPhiMassFiber_comparable_to_shape_of_phiProgressionAverageTwoSided
    {P : Params} (hφ : PhiProgressionAverageTwoSided P) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X ∧
        exactDivisorMPhiMassFiber P X ≤ C * exactDivisorMPhiMassShape P X :=
  exactDivisorMPhiMassFiber_comparable_to_shape_of_fiberAverageTwoSided
    (ExactDivisorMPhiFiberAverageTwoSided_of_phiProgressionAverageTwoSided hφ)

/-- The `M_φ` exact-divisor mass comparison from the narrower
trivial-modulus fiber route.

This avoids invoking the full reciprocal-`φ` progression theorem when the mass
argument only needs the `D=1` fiber estimate. -/
theorem exactDivisorMPhiMassFiber_comparable_to_shape_of_coprimeLong_ordinaryUpper_wide
    {P : Params}
    (hlower :
      OrdinarySquarefreeCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X ∧
        exactDivisorMPhiMassFiber P X ≤ C * exactDivisorMPhiMassShape P X :=
  exactDivisorMPhiMassFiber_comparable_to_shape_of_fiberAverageTwoSided
    (ExactDivisorMPhiFiberAverageTwoSided_of_coprimeLong_and_ordinaryUpper_wide
      hlower hupper)

/-- The `M_φ` exact-divisor mass comparison from the specialized phi-window
squarefree lower carrier and the wide upper estimate. -/
theorem exactDivisorMPhiMassFiber_comparable_to_shape_of_sqfRecipLower_ordinaryUpper_wide
    {P : Params}
    (hlower : PhiProgressionSqfRecipLower P)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X ∧
        exactDivisorMPhiMassFiber P X ≤ C * exactDivisorMPhiMassShape P X :=
  exactDivisorMPhiMassFiber_comparable_to_shape_of_fiberAverageTwoSided
    (ExactDivisorMPhiFiberAverageTwoSided_of_sqfRecipLower_and_ordinaryUpper_wide
      hlower hupper)

/-- The actual `M₁` exact-divisor fiber used in `prop:M` is comparable to its
main-term shape from the ordinary squarefree progression lower and upper
estimates.  This is the bare-reciprocal analogue of the `M_φ` bridge above. -/
theorem exactDivisorM1MassFiber_comparable_to_shape_of_ordinarySquarefreeProgression
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.η) P.θ P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.η) P.θ P.η) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * exactDivisorM1MassShape P X ≤ exactDivisorM1MassFiber P X ∧
        exactDivisorM1MassFiber P X ≤ C * exactDivisorM1MassShape P X := by
  classical
  rcases hlower with ⟨c, Xlo, hc, hlo⟩
  rcases hupper with ⟨C, Xhi, hC, hhi⟩
  rcases fixedNat_le_UScale_eventually 1 with ⟨XU, hU⟩
  refine ⟨c, C, max (max (max Xlo Xhi) XU) (Real.exp 1), hc, hC, ?_⟩
  intro X hX
  have hXlo : Xlo ≤ X :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hX
  have hXhi : Xhi ≤ X :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hX
  have hXU : XU ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe
  have hXgtone : (1 : ℝ) < X :=
    lt_of_lt_of_le (by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)) hXe
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hS_nonneg : 0 ≤ SScale P X := (Real.rpow_pos_of_pos hXpos P.η).le
  have hU1 : ((1 : ℕ) : ℝ) ≤ UScale X := hU X hXU
  constructor
  · unfold exactDivisorM1MassShape exactDivisorM1MassFiber exactDivisorSRange
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
      (Finset.mem_filter.mp hs).1
    have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
    have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
    have hssqf : Squarefree s := (Finset.mem_filter.mp hs).2
    have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
    have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos_nat
    have hsS : (s : ℝ) ≤ SScale P X :=
      le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
    have hM_scale : (s : ℝ) ≤ X ^ P.η := by
      simpa [SScale] using hsS
    have hU0_scale :
        X ^ (P.lam - P.η) ≤ phiProgressionU0 P s X :=
      phiProgressionU0_ge_rpow_lam_sub_eta P hXone hs_one hsS
    have hU1_scale :
        phiProgressionU1 P s X ≤ X ^ P.θ :=
      phiProgressionU1_le_rpow_theta P hXpos hs_one
    have hU01 :
        phiProgressionU0 P s X < phiProgressionU1 P s X :=
      phiProgressionU0_lt_U1_of_s_le_SScale P hXgtone hs_one hsS
    have hbare :
        c * phiProgressionAverageShape P X 1 s ≤
          phiProgressionBareAverage P X 1 0 s := by
      have hraw :=
        hlo X hXlo s 1 0 (by norm_num) hssqf squarefree_one
          (Nat.coprime_one_right s) (by norm_num) hM_scale hU1
          (phiProgressionU0 P s X) (phiProgressionU1 P s X)
          hU0_scale hU01 hU1_scale
      simpa [phiProgressionBareAverage_eq_sqfRecip,
        phiProgressionAverageShape,
        log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos_nat] using hraw
    have hscale_nonneg : 0 ≤ (1 : ℝ) / (s : ℝ) :=
      div_nonneg zero_le_one hs_pos.le
    calc
      c * (((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) * slantLogLength P s X)
          = ((1 : ℝ) / (s : ℝ)) * (c * phiProgressionAverageShape P X 1 s) := by
            unfold phiProgressionAverageShape
            ring_nf
      _ ≤ ((1 : ℝ) / (s : ℝ)) * phiProgressionBareAverage P X 1 0 s :=
          mul_le_mul_of_nonneg_left hbare hscale_nonneg
  · unfold exactDivisorM1MassShape exactDivisorM1MassFiber exactDivisorSRange
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
      (Finset.mem_filter.mp hs).1
    have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
    have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
    have hssqf : Squarefree s := (Finset.mem_filter.mp hs).2
    have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
    have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos_nat
    have hsS : (s : ℝ) ≤ SScale P X :=
      le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
    have hM_scale : (s : ℝ) ≤ X ^ P.η := by
      simpa [SScale] using hsS
    have hU0_scale :
        X ^ (P.lam - P.η) ≤ phiProgressionU0 P s X :=
      phiProgressionU0_ge_rpow_lam_sub_eta P hXone hs_one hsS
    have hU1_scale :
        phiProgressionU1 P s X ≤ X ^ P.θ :=
      phiProgressionU1_le_rpow_theta P hXpos hs_one
    have hU01 :
        phiProgressionU0 P s X < phiProgressionU1 P s X :=
      phiProgressionU0_lt_U1_of_s_le_SScale P hXgtone hs_one hsS
    have hbare :
        phiProgressionBareAverage P X 1 0 s ≤
          C * phiProgressionAverageShape P X 1 s := by
      have hraw :=
        hhi X hXhi s 1 0 (by norm_num) hssqf squarefree_one
          (Nat.coprime_one_right s) (by norm_num) hM_scale hU1
          (phiProgressionU0 P s X) (phiProgressionU1 P s X)
          hU0_scale hU01 hU1_scale
      simpa [phiProgressionBareAverage_eq_sqfRecip,
        phiProgressionAverageShape,
        log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos_nat] using hraw
    have hscale_nonneg : 0 ≤ (1 : ℝ) / (s : ℝ) :=
      div_nonneg zero_le_one hs_pos.le
    calc
      ((1 : ℝ) / (s : ℝ)) * phiProgressionBareAverage P X 1 0 s
          ≤ ((1 : ℝ) / (s : ℝ)) * (C * phiProgressionAverageShape P X 1 s) :=
          mul_le_mul_of_nonneg_left hbare hscale_nonneg
      _ = C * (((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) *
            slantLogLength P s X) := by
            unfold phiProgressionAverageShape
            ring_nf

/-- Paper-facing `M₁` fiber-to-shape bridge using the same wide ordinary
squarefree upper estimate that feeds the reciprocal-`φ` progression route. -/
theorem
    exactDivisorM1MassFiber_comparable_to_shape_of_ordinarySquarefreeProgression_wideUpper
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.η) P.θ P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * exactDivisorM1MassShape P X ≤ exactDivisorM1MassFiber P X ∧
        exactDivisorM1MassFiber P X ≤ C * exactDivisorM1MassShape P X :=
  exactDivisorM1MassFiber_comparable_to_shape_of_ordinarySquarefreeProgression
    hlower
    (OrdinarySquarefreeProgressionCoprimeDensityUpper_eta_of_wide hupper)

/-- `M₁` fiber-to-shape bridge from the specialized phi-window squarefree lower
carrier and the wide ordinary-squarefree upper estimate.

This removes the generic ordinary-squarefree lower hypothesis from the `M₁`
mass half: the lower bound is exactly the `D=1` instance of
`PhiProgressionSqfRecipLower`. -/
theorem
    exactDivisorM1MassFiber_comparable_to_shape_of_sqfRecipLower_ordinaryUpper_wide
    {P : Params}
    (hlower : PhiProgressionSqfRecipLower P)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * exactDivisorM1MassShape P X ≤ exactDivisorM1MassFiber P X ∧
        exactDivisorM1MassFiber P X ≤ C * exactDivisorM1MassShape P X := by
  classical
  rcases hlower with ⟨c, Xlo, hc, hlo⟩
  rcases OrdinarySquarefreeProgressionCoprimeDensityUpper_eta_of_wide hupper with
    ⟨C, Xhi, hC, hhi⟩
  rcases fixedNat_le_UScale_eventually 1 with ⟨XU, hU⟩
  refine ⟨c, C, max (max (max Xlo Xhi) XU) (Real.exp 1), hc, hC, ?_⟩
  intro X hX
  have hXlo : Xlo ≤ X :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hX
  have hXhi : Xhi ≤ X :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hX
  have hXU : XU ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe
  have hXgtone : (1 : ℝ) < X :=
    lt_of_lt_of_le (by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)) hXe
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hS_nonneg : 0 ≤ SScale P X := (Real.rpow_pos_of_pos hXpos P.η).le
  have hU1 : ((1 : ℕ) : ℝ) ≤ UScale X := hU X hXU
  constructor
  · unfold exactDivisorM1MassShape exactDivisorM1MassFiber exactDivisorSRange
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
      (Finset.mem_filter.mp hs).1
    have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
    have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
    have hssqf : Squarefree s := (Finset.mem_filter.mp hs).2
    have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
    have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos_nat
    have hsS : (s : ℝ) ≤ SScale P X :=
      le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
    have hbare :
        c * phiProgressionAverageShape P X 1 s ≤
          phiProgressionBareAverage P X 1 0 s := by
      have hraw :=
        hlo X hXlo 1 0 s (by norm_num) squarefree_one (by norm_num)
          hU1 (by norm_num) hs_one hssqf
          (Nat.coprime_one_right s) hsS
      simpa [phiProgressionBareAverage_eq_sqfRecip,
        phiProgressionAverageShape,
        log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos_nat] using hraw
    have hscale_nonneg : 0 ≤ (1 : ℝ) / (s : ℝ) :=
      div_nonneg zero_le_one hs_pos.le
    calc
      c * (((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) * slantLogLength P s X)
          = ((1 : ℝ) / (s : ℝ)) * (c * phiProgressionAverageShape P X 1 s) := by
            unfold phiProgressionAverageShape
            ring_nf
      _ ≤ ((1 : ℝ) / (s : ℝ)) * phiProgressionBareAverage P X 1 0 s :=
          mul_le_mul_of_nonneg_left hbare hscale_nonneg
  · unfold exactDivisorM1MassShape exactDivisorM1MassFiber exactDivisorSRange
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
      (Finset.mem_filter.mp hs).1
    have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
    have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
    have hssqf : Squarefree s := (Finset.mem_filter.mp hs).2
    have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
    have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos_nat
    have hsS : (s : ℝ) ≤ SScale P X :=
      le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
    have hM_scale : (s : ℝ) ≤ X ^ P.η := by
      simpa [SScale] using hsS
    have hU0_scale :
        X ^ (P.lam - P.η) ≤ phiProgressionU0 P s X :=
      phiProgressionU0_ge_rpow_lam_sub_eta P hXone hs_one hsS
    have hU1_scale :
        phiProgressionU1 P s X ≤ X ^ P.θ :=
      phiProgressionU1_le_rpow_theta P hXpos hs_one
    have hU01 :
        phiProgressionU0 P s X < phiProgressionU1 P s X :=
      phiProgressionU0_lt_U1_of_s_le_SScale P hXgtone hs_one hsS
    have hbare :
        phiProgressionBareAverage P X 1 0 s ≤
          C * phiProgressionAverageShape P X 1 s := by
      have hraw :=
        hhi X hXhi s 1 0 (by norm_num) hssqf squarefree_one
          (Nat.coprime_one_right s) (by norm_num) hM_scale hU1
          (phiProgressionU0 P s X) (phiProgressionU1 P s X)
          hU0_scale hU01 hU1_scale
      simpa [phiProgressionBareAverage_eq_sqfRecip,
        phiProgressionAverageShape,
        log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos_nat] using hraw
    have hscale_nonneg : 0 ≤ (1 : ℝ) / (s : ℝ) :=
      div_nonneg zero_le_one hs_pos.le
    calc
      ((1 : ℝ) / (s : ℝ)) * phiProgressionBareAverage P X 1 0 s
          ≤ ((1 : ℝ) / (s : ℝ)) * (C * phiProgressionAverageShape P X 1 s) :=
          mul_le_mul_of_nonneg_left hbare hscale_nonneg
      _ = C * (((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) *
            slantLogLength P s X) := by
            unfold phiProgressionAverageShape
            ring_nf

/-- Long-window version of
`exactDivisorM1MassFiber_comparable_to_shape_of_sqfRecipLower_ordinaryUpper_wide`.

The `M₁` upper half uses the same ordinary-squarefree upper estimate as the
reciprocal-`φ` route, but now in the manuscript-aligned long-window form.  The
required ratio hypothesis is discharged by the checked phi-window scale
inequality. -/
theorem
    exactDivisorM1MassFiber_comparable_to_shape_of_sqfRecipLower_ordinaryUpperLong_wide
    {P : Params}
    (hlower : PhiProgressionSqfRecipLower P)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpperLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * exactDivisorM1MassShape P X ≤ exactDivisorM1MassFiber P X ∧
        exactDivisorM1MassFiber P X ≤ C * exactDivisorM1MassShape P X := by
  classical
  rcases hlower with ⟨c, Xlo, hc, hlo⟩
  rcases OrdinarySquarefreeProgressionCoprimeDensityUpperLong_eta_of_wide hupper with
    ⟨C, Xhi, hC, hhi⟩
  rcases fixedNat_le_UScale_eventually 1 with ⟨XU, hU⟩
  refine ⟨c, C, max (max (max Xlo Xhi) XU) (Real.exp 1), hc, hC, ?_⟩
  intro X hX
  have hXlo : Xlo ≤ X :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hX
  have hXhi : Xhi ≤ X :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hX
  have hXU : XU ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe
  have hXgtone : (1 : ℝ) < X :=
    lt_of_lt_of_le (by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)) hXe
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hS_nonneg : 0 ≤ SScale P X := (Real.rpow_pos_of_pos hXpos P.η).le
  have hU1 : ((1 : ℕ) : ℝ) ≤ UScale X := hU X hXU
  constructor
  · unfold exactDivisorM1MassShape exactDivisorM1MassFiber exactDivisorSRange
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
      (Finset.mem_filter.mp hs).1
    have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
    have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
    have hssqf : Squarefree s := (Finset.mem_filter.mp hs).2
    have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
    have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos_nat
    have hsS : (s : ℝ) ≤ SScale P X :=
      le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
    have hbare :
        c * phiProgressionAverageShape P X 1 s ≤
          phiProgressionBareAverage P X 1 0 s := by
      have hraw :=
        hlo X hXlo 1 0 s (by norm_num) squarefree_one (by norm_num)
          hU1 (by norm_num) hs_one hssqf
          (Nat.coprime_one_right s) hsS
      simpa [phiProgressionBareAverage_eq_sqfRecip,
        phiProgressionAverageShape,
        log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos_nat] using hraw
    have hscale_nonneg : 0 ≤ (1 : ℝ) / (s : ℝ) :=
      div_nonneg zero_le_one hs_pos.le
    calc
      c * (((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) * slantLogLength P s X)
          = ((1 : ℝ) / (s : ℝ)) * (c * phiProgressionAverageShape P X 1 s) := by
            unfold phiProgressionAverageShape
            ring_nf
      _ ≤ ((1 : ℝ) / (s : ℝ)) * phiProgressionBareAverage P X 1 0 s :=
          mul_le_mul_of_nonneg_left hbare hscale_nonneg
  · unfold exactDivisorM1MassShape exactDivisorM1MassFiber exactDivisorSRange
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
      (Finset.mem_filter.mp hs).1
    have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
    have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
    have hssqf : Squarefree s := (Finset.mem_filter.mp hs).2
    have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
    have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos_nat
    have hsS : (s : ℝ) ≤ SScale P X :=
      le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
    have hM_scale : (s : ℝ) ≤ X ^ P.η := by
      simpa [SScale] using hsS
    have hU0_scale :
        X ^ (P.lam - P.η) ≤ phiProgressionU0 P s X :=
      phiProgressionU0_ge_rpow_lam_sub_eta P hXone hs_one hsS
    have hU1_scale :
        phiProgressionU1 P s X ≤ X ^ P.θ :=
      phiProgressionU1_le_rpow_theta P hXpos hs_one
    have hU01 :
        phiProgressionU0 P s X < phiProgressionU1 P s X :=
      phiProgressionU0_lt_U1_of_s_le_SScale P hXgtone hs_one hsS
    have hratio :
        X ^ (P.θ - P.lam - P.η) ≤
          phiProgressionU1 P s X / phiProgressionU0 P s X :=
      phiProgression_ratio_ge_rpow_theta_sub_lam_sub_eta P hXone hs_one hsS
    have hU1_one : (1 : ℝ) ≤ phiProgressionU1 P s X :=
      (one_le_phiProgressionU0 P hXone hs_one hsS).trans hU01.le
    have hbare :
        phiProgressionBareAverage P X 1 0 s ≤
          C * phiProgressionAverageShape P X 1 s := by
      have hraw :=
        hhi X hXhi s 1 0 (by norm_num) hssqf squarefree_one
          (Nat.coprime_one_right s) (by norm_num) hM_scale hU1
          (phiProgressionU0 P s X) (phiProgressionU1 P s X)
          hU0_scale hU01 hU1_one hU1_scale hratio
      simpa [phiProgressionBareAverage_eq_sqfRecip,
        phiProgressionAverageShape,
        log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos_nat] using hraw
    have hscale_nonneg : 0 ≤ (1 : ℝ) / (s : ℝ) :=
      div_nonneg zero_le_one hs_pos.le
    calc
      ((1 : ℝ) / (s : ℝ)) * phiProgressionBareAverage P X 1 0 s
          ≤ ((1 : ℝ) / (s : ℝ)) * (C * phiProgressionAverageShape P X 1 s) :=
          mul_le_mul_of_nonneg_left hbare hscale_nonneg
      _ = C * (((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) *
            slantLogLength P s X) := by
            unfold phiProgressionAverageShape
            ring_nf

/-- Manuscript-aligned `M₁` fiber-to-shape bridge using only the non-progression
lower half of `lem:ordinary-sqf`.

The `M₁` mass computation specializes the fixed modulus to `D=1`, so its lower
bound needs only the coprime squarefree reciprocal estimate displayed in
`eq:ordinary-sqf-coprime`.  The progression lower estimate remains a separate
input for the reciprocal-`φ` progression-average route. -/
theorem
    exactDivisorM1MassFiber_comparable_to_shape_of_ordinarySquarefreeCoprimeLong_and_upper
    {P : Params}
    (hlower :
      OrdinarySquarefreeCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.η) P.θ P.η) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * exactDivisorM1MassShape P X ≤ exactDivisorM1MassFiber P X ∧
        exactDivisorM1MassFiber P X ≤ C * exactDivisorM1MassShape P X := by
  classical
  rcases hlower with ⟨c, Xlo, hc, hlo⟩
  rcases hupper with ⟨C, Xhi, hC, hhi⟩
  rcases fixedNat_le_UScale_eventually 1 with ⟨XU, hU⟩
  refine ⟨c, C, max (max (max Xlo Xhi) XU) (Real.exp 1), hc, hC, ?_⟩
  intro X hX
  have hXlo : Xlo ≤ X :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hX
  have hXhi : Xhi ≤ X :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hX
  have hXU : XU ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe
  have hXgtone : (1 : ℝ) < X :=
    lt_of_lt_of_le (by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)) hXe
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hS_nonneg : 0 ≤ SScale P X := (Real.rpow_pos_of_pos hXpos P.η).le
  have hU1 : ((1 : ℕ) : ℝ) ≤ UScale X := hU X hXU
  constructor
  · unfold exactDivisorM1MassShape exactDivisorM1MassFiber exactDivisorSRange
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
      (Finset.mem_filter.mp hs).1
    have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
    have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
    have hssqf : Squarefree s := (Finset.mem_filter.mp hs).2
    have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
    have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos_nat
    have hsS : (s : ℝ) ≤ SScale P X :=
      le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
    have hM_scale : (s : ℝ) ≤ X ^ P.η := by
      simpa [SScale] using hsS
    have hU0_scale :
        X ^ (P.lam - P.η) ≤ phiProgressionU0 P s X :=
      phiProgressionU0_ge_rpow_lam_sub_eta P hXone hs_one hsS
    have hU1_scale :
        phiProgressionU1 P s X ≤ X ^ P.θ :=
      phiProgressionU1_le_rpow_theta P hXpos hs_one
    have hU01 :
        phiProgressionU0 P s X < phiProgressionU1 P s X :=
      phiProgressionU0_lt_U1_of_s_le_SScale P hXgtone hs_one hsS
    have hratio :
        X ^ (P.θ - P.lam - P.η) ≤
          phiProgressionU1 P s X / phiProgressionU0 P s X :=
      phiProgression_ratio_ge_rpow_theta_sub_lam_sub_eta P hXone hs_one hsS
    have hU1_one : (1 : ℝ) ≤ phiProgressionU1 P s X :=
      (one_le_phiProgressionU0 P hXone hs_one hsS).trans hU01.le
    have hbare :
        c * phiProgressionAverageShape P X 1 s ≤
          phiProgressionBareAverage P X 1 0 s := by
      have hraw :=
        hlo X hXlo s hssqf hM_scale
          (phiProgressionU0 P s X) (phiProgressionU1 P s X)
          hU0_scale hU01 hU1_one hU1_scale hratio
      simpa [phiProgressionBareAverage_eq_sqfRecip,
        phiProgressionAverageShape,
        log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos_nat] using hraw
    have hscale_nonneg : 0 ≤ (1 : ℝ) / (s : ℝ) :=
      div_nonneg zero_le_one hs_pos.le
    calc
      c * (((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) * slantLogLength P s X)
          = ((1 : ℝ) / (s : ℝ)) * (c * phiProgressionAverageShape P X 1 s) := by
            unfold phiProgressionAverageShape
            ring_nf
      _ ≤ ((1 : ℝ) / (s : ℝ)) * phiProgressionBareAverage P X 1 0 s :=
          mul_le_mul_of_nonneg_left hbare hscale_nonneg
  · unfold exactDivisorM1MassShape exactDivisorM1MassFiber exactDivisorSRange
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
      (Finset.mem_filter.mp hs).1
    have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
    have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
    have hssqf : Squarefree s := (Finset.mem_filter.mp hs).2
    have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
    have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos_nat
    have hsS : (s : ℝ) ≤ SScale P X :=
      le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
    have hM_scale : (s : ℝ) ≤ X ^ P.η := by
      simpa [SScale] using hsS
    have hU0_scale :
        X ^ (P.lam - P.η) ≤ phiProgressionU0 P s X :=
      phiProgressionU0_ge_rpow_lam_sub_eta P hXone hs_one hsS
    have hU1_scale :
        phiProgressionU1 P s X ≤ X ^ P.θ :=
      phiProgressionU1_le_rpow_theta P hXpos hs_one
    have hU01 :
        phiProgressionU0 P s X < phiProgressionU1 P s X :=
      phiProgressionU0_lt_U1_of_s_le_SScale P hXgtone hs_one hsS
    have hbare :
        phiProgressionBareAverage P X 1 0 s ≤
          C * phiProgressionAverageShape P X 1 s := by
      have hraw :=
        hhi X hXhi s 1 0 (by norm_num) hssqf squarefree_one
          (Nat.coprime_one_right s) (by norm_num) hM_scale hU1
          (phiProgressionU0 P s X) (phiProgressionU1 P s X)
          hU0_scale hU01 hU1_scale
      simpa [phiProgressionBareAverage_eq_sqfRecip,
        phiProgressionAverageShape,
        log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos_nat] using hraw
    have hscale_nonneg : 0 ≤ (1 : ℝ) / (s : ℝ) :=
      div_nonneg zero_le_one hs_pos.le
    calc
      ((1 : ℝ) / (s : ℝ)) * phiProgressionBareAverage P X 1 0 s
          ≤ ((1 : ℝ) / (s : ℝ)) * (C * phiProgressionAverageShape P X 1 s) :=
          mul_le_mul_of_nonneg_left hbare hscale_nonneg
      _ = C * (((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) *
            slantLogLength P s X) := by
            unfold phiProgressionAverageShape
            ring_nf

/-- Wide-upper version of the manuscript-aligned `M₁` bridge. -/
theorem
    exactDivisorM1MassFiber_comparable_to_shape_of_ordinarySquarefreeCoprimeLong_wideUpper
    {P : Params}
    (hlower :
      OrdinarySquarefreeCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * exactDivisorM1MassShape P X ≤ exactDivisorM1MassFiber P X ∧
        exactDivisorM1MassFiber P X ≤ C * exactDivisorM1MassShape P X :=
  exactDivisorM1MassFiber_comparable_to_shape_of_ordinarySquarefreeCoprimeLong_and_upper
    hlower
    (OrdinarySquarefreeProgressionCoprimeDensityUpper_eta_of_wide hupper)

/-- The deterministic scale part of `lem:phi-progression-average`: uniformly for
`1 ≤ s ≤ S = X^η`, the logarithmic interval length `log(H/(Y₀s))` is comparable
to `log X`.  The lower constant is `θ - λ - η > 0`, exactly the conductor
separation inequality `λ + η < θ`; the upper constant is `θ - λ`.

This does not prove the arithmetic progression average itself.  It formalizes
the scale comparison used after that average is invoked in the proof of
`lem:small-saturation-average`. -/
theorem slantLogLength_uniform_bounds (P : Params) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → ∀ s : ℕ,
      1 ≤ s → (s : ℝ) ≤ SScale P X →
        c * logX X ≤ slantLogLength P s X ∧ slantLogLength P s X ≤ C * logX X := by
  refine ⟨P.θ - P.lam - P.η, P.θ - P.lam, Real.exp 1, ?_, ?_, ?_⟩
  · linarith [P.lam_add_η_lt_θ]
  · linarith [P.lam_add_η_lt_θ, P.η_pos]
  intro X hX s hs hsS
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hlogX_nonneg : 0 ≤ Real.log X := by
    have hXge1 : (1 : ℝ) ≤ X := by
      exact le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hX
    exact Real.log_nonneg hXge1
  have hspos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hspos_nat
  have hs_ge_one_real : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hlog_s_nonneg : 0 ≤ Real.log (s : ℝ) := Real.log_nonneg hs_ge_one_real
  have hSpos : 0 < SScale P X := Real.rpow_pos_of_pos hXpos P.η
  have hlog_s_le_logS : Real.log (s : ℝ) ≤ Real.log (SScale P X) :=
    Real.log_le_log hspos hsS
  have hlog_s_le_eta : Real.log (s : ℝ) ≤ P.η * Real.log X := by
    simpa [log_SScale P hXpos] using hlog_s_le_logS
  have hY0pos : 0 < Y0Scale P X := Real.rpow_pos_of_pos hXpos P.lam
  have hHpos : 0 < HScale P X := Real.rpow_pos_of_pos hXpos P.θ
  have hdenpos : 0 < Y0Scale P X * (s : ℝ) := mul_pos hY0pos hspos
  have hlen_eq :
      slantLogLength P s X = (P.θ - P.lam) * Real.log X - Real.log (s : ℝ) := by
    unfold slantLogLength
    rw [Real.log_div (ne_of_gt hHpos) (ne_of_gt hdenpos)]
    rw [Real.log_mul (ne_of_gt hY0pos) (ne_of_gt hspos)]
    rw [log_HScale P hXpos, log_Y0Scale P hXpos]
    ring
  unfold logX
  rw [hlen_eq]
  constructor
  · nlinarith [hlog_s_le_eta]
  · nlinarith [hlog_s_nonneg]

/-- Fixed-`s` explicit version of `slantLogLength_uniform_bounds`.

For each fixed `s ≥ 1`, the threshold
`max e (s^(1/η))` is enough to ensure `s ≤ SScale P X`, so the uniform
slanted-length calculation becomes a reusable large-`X` bound for the single
function `X ↦ log(H/(Y₀s))`. -/
theorem slantLogLength_fixed_bounds (P : Params) (s : ℕ) (hs : 1 ≤ s) :
    ∀ X : ℝ, max (Real.exp 1) (((s : ℝ) ^ (1 / P.η))) ≤ X →
      (P.θ - P.lam - P.η) * logX X ≤ slantLogLength P s X
        ∧ slantLogLength P s X ≤ (P.θ - P.lam) * logX X := by
  intro X hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_left _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hlogX_nonneg : 0 ≤ Real.log X := by
    exact Real.log_nonneg (le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe)
  have hspos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hspos_nat
  have hs_nonneg : (0 : ℝ) ≤ (s : ℝ) := hspos.le
  have hs_ge_one_real : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hlog_s_nonneg : 0 ≤ Real.log (s : ℝ) := Real.log_nonneg hs_ge_one_real
  have hbase_nonneg : 0 ≤ ((s : ℝ) ^ (1 / P.η)) :=
    Real.rpow_nonneg hs_nonneg _
  have hbase_le_X : ((s : ℝ) ^ (1 / P.η)) ≤ X :=
    le_trans (le_max_right _ _) hX
  have hs_le_S : (s : ℝ) ≤ SScale P X := by
    unfold SScale
    have hpow :
        ((s : ℝ) ^ (1 / P.η)) ^ P.η ≤ X ^ P.η :=
      Real.rpow_le_rpow hbase_nonneg hbase_le_X P.η_pos.le
    have hleft : ((s : ℝ) ^ (1 / P.η)) ^ P.η = (s : ℝ) := by
      rw [← Real.rpow_mul hs_nonneg]
      have heta_ne : P.η ≠ 0 := ne_of_gt P.η_pos
      have hmul : 1 / P.η * P.η = 1 := by
        field_simp [heta_ne]
      rw [hmul, Real.rpow_one]
    have hleft' : ((s : ℝ) ^ P.η⁻¹) ^ P.η = (s : ℝ) := by
      simpa [one_div] using hleft
    simpa [hleft'] using hpow
  have hSpos : 0 < SScale P X := Real.rpow_pos_of_pos hXpos P.η
  have hlog_s_le_logS : Real.log (s : ℝ) ≤ Real.log (SScale P X) :=
    Real.log_le_log hspos hs_le_S
  have hlog_s_le_eta : Real.log (s : ℝ) ≤ P.η * Real.log X := by
    simpa [log_SScale P hXpos] using hlog_s_le_logS
  have hY0pos : 0 < Y0Scale P X := Real.rpow_pos_of_pos hXpos P.lam
  have hHpos : 0 < HScale P X := Real.rpow_pos_of_pos hXpos P.θ
  have hdenpos : 0 < Y0Scale P X * (s : ℝ) := mul_pos hY0pos hspos
  have hlen_eq :
      slantLogLength P s X = (P.θ - P.lam) * Real.log X - Real.log (s : ℝ) := by
    unfold slantLogLength
    rw [Real.log_div (ne_of_gt hHpos) (ne_of_gt hdenpos)]
    rw [Real.log_mul (ne_of_gt hY0pos) (ne_of_gt hspos)]
    rw [log_HScale P hXpos, log_Y0Scale P hXpos]
    ring
  unfold logX
  rw [hlen_eq]
  constructor
  · nlinarith [hlog_s_le_eta]
  · nlinarith [hlog_s_nonneg]

/-- Fixed-`s` factor-asymptotic form of `slantLogLength_fixed_bounds`.

For each fixed `s ≥ 1`, the deterministic interval length
`log(H/(Y₀s))` is `≍ log X` for large `X`.  This packages the scale calculation
as reusable `FactorAsymp` data.  It does not prove the arithmetic progression
average in `lem:phi-progression-average`; that averaging step remains a
separate intermediate input. -/
noncomputable def slantLogLength_factor_asymp (P : Params) (s : ℕ) (hs : 1 ≤ s) :
    FactorAsymp (fun X => slantLogLength P s X) logX where
  c := P.θ - P.lam - P.η
  C := P.θ - P.lam
  X₀ := max (Real.exp 1) (((s : ℝ) ^ (1 / P.η)))
  c_pos := by linarith [P.lam_add_η_lt_θ]
  C_pos := by linarith [P.lam_add_η_lt_θ, P.η_pos]
  f_nonneg := fun X hX => by
    have hsand := slantLogLength_fixed_bounds P s hs X hX
    have hXe : Real.exp 1 ≤ X := le_trans (le_max_left _ _) hX
    have hlog_nonneg : 0 ≤ logX X := by
      unfold logX
      exact Real.log_nonneg (le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe)
    have hc : 0 ≤ P.θ - P.lam - P.η := by
      linarith [P.lam_add_η_lt_θ]
    exact le_trans (mul_nonneg hc hlog_nonneg) hsand.1
  sandwich := fun X hX => by
    exact slantLogLength_fixed_bounds P s hs X hX

/-- Fixed-parameter `FactorAsymp` consequence of the exact
`lem:phi-progression-average` target.

This theorem does not prove the reciprocal-`φ` progression average itself.  It
checks the remaining interface work: once the exact two-sided paper statement is
available, the finite carrier
`X ↦ phiProgressionAverage P X d a s` supplies the `≍ log X` datum used by the
small-mass assembly. -/
noncomputable def phiProgressionAverage_factor_asymp_of_twoSided
    {P : Params} (hφ : PhiProgressionAverageTwoSided P)
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    FactorAsymp (fun X => phiProgressionAverage P X d a s) logX := by
  let cφ : ℝ := Classical.choose hφ
  have hφ_c :
      ∃ C X₀ : ℝ, 0 < cφ ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        ∀ d a s : ℕ,
          0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
          Nat.Coprime a d →
          1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
            cφ * phiProgressionAverageShape P X d s ≤
                phiProgressionAverage P X d a s ∧
              phiProgressionAverage P X d a s ≤
                C * phiProgressionAverageShape P X d s :=
    Classical.choose_spec hφ
  let Cφ : ℝ := Classical.choose hφ_c
  have hφ_C :
      ∃ X₀ : ℝ, 0 < cφ ∧ 0 < Cφ ∧ ∀ X : ℝ, X₀ ≤ X →
        ∀ d a s : ℕ,
          0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
          Nat.Coprime a d →
          1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
            cφ * phiProgressionAverageShape P X d s ≤
                phiProgressionAverage P X d a s ∧
              phiProgressionAverage P X d a s ≤
                Cφ * phiProgressionAverageShape P X d s :=
    Classical.choose_spec hφ_c
  let Xφ : ℝ := Classical.choose hφ_C
  have hφ_spec :
      0 < cφ ∧ 0 < Cφ ∧ ∀ X : ℝ, Xφ ≤ X →
        ∀ d a s : ℕ,
          0 < d → Squarefree d → Odd d → (d : ℝ) ≤ UScale X →
          Nat.Coprime a d →
          1 ≤ s → Squarefree s → Nat.Coprime s d → (s : ℝ) ≤ SScale P X →
            cφ * phiProgressionAverageShape P X d s ≤
                phiProgressionAverage P X d a s ∧
              phiProgressionAverage P X d a s ≤
                Cφ * phiProgressionAverageShape P X d s :=
    Classical.choose_spec hφ_C
  have hcφ : 0 < cφ := hφ_spec.1
  have hCφ : 0 < Cφ := hφ_spec.2.1
  have hbound := hφ_spec.2.2
  let XU : ℝ := Classical.choose (fixedNat_le_UScale_eventually d)
  have hU : ∀ X : ℝ, XU ≤ X → (d : ℝ) ≤ UScale X :=
    Classical.choose_spec (fixedNat_le_UScale_eventually d)
  let hslant := slantLogLength_factor_asymp P s hs
  let k : ℝ := ((1 : ℝ) / (d : ℝ)) * ((Nat.totient s : ℝ) / (s : ℝ))
  have hspos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hsposR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hspos_nat
  have htot_pos : 0 < Nat.totient s := Nat.totient_pos.mpr hspos_nat
  have hk_pos : 0 < k := by
    dsimp [k]
    have hdposR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
    have htot_posR : (0 : ℝ) < (Nat.totient s : ℝ) := by exact_mod_cast htot_pos
    positivity
  refine
    { c := cφ * k * hslant.c
      C := Cφ * k * hslant.C
      X₀ := max (max Xφ XU) hslant.X₀
      c_pos := mul_pos (mul_pos hcφ hk_pos) hslant.c_pos
      C_pos := mul_pos (mul_pos hCφ hk_pos) hslant.C_pos
      f_nonneg := ?_
      sandwich := ?_ }
  · intro X _hX
    exact phiProgressionAverage_nonneg P X d a s
  · intro X hX
    have hXφ : Xφ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
    have hXU : XU ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
    have hXs : hslant.X₀ ≤ X := le_trans (le_max_right _ _) hX
    have hUle : (d : ℝ) ≤ UScale X := hU X hXU
    have hsS : (s : ℝ) ≤ SScale P X := by
      -- Reuse the explicit threshold chosen by `slantLogLength_factor_asymp`.
      have hbase_le : ((s : ℝ) ^ (1 / P.η)) ≤ X := by
        exact le_trans (le_max_right _ _) hXs
      have hbase_nonneg : 0 ≤ ((s : ℝ) ^ (1 / P.η)) :=
        Real.rpow_nonneg hsposR.le _
      unfold SScale
      have hpow :
          ((s : ℝ) ^ (1 / P.η)) ^ P.η ≤ X ^ P.η :=
        Real.rpow_le_rpow hbase_nonneg hbase_le P.η_pos.le
      have hleft : ((s : ℝ) ^ (1 / P.η)) ^ P.η = (s : ℝ) := by
        rw [← Real.rpow_mul hsposR.le]
        have heta_ne : P.η ≠ 0 := ne_of_gt P.η_pos
        have hmul : 1 / P.η * P.η = 1 := by field_simp [heta_ne]
        rw [hmul, Real.rpow_one]
      have hleft' : ((s : ℝ) ^ P.η⁻¹) ^ P.η = (s : ℝ) := by
        simpa [one_div] using hleft
      simpa [hleft'] using hpow
    have hφX :=
      hbound X hXφ d a s hdpos hdsqf hdodd hUle had hs hssqf hsd hsS
    have hshape_eq :
        phiProgressionAverageShape P X d s =
          k * slantLogLength P s X := by
      unfold phiProgressionAverageShape
      dsimp [k]
    have hslant_bounds := hslant.sandwich X hXs
    have hshape_lower :
        k * (hslant.c * logX X) ≤ phiProgressionAverageShape P X d s := by
      rw [hshape_eq]
      exact mul_le_mul_of_nonneg_left hslant_bounds.1 hk_pos.le
    have hshape_upper :
        phiProgressionAverageShape P X d s ≤ k * (hslant.C * logX X) := by
      rw [hshape_eq]
      exact mul_le_mul_of_nonneg_left hslant_bounds.2 hk_pos.le
    constructor
    · calc
        (cφ * k * hslant.c) * logX X
            = cφ * (k * (hslant.c * logX X)) := by ring
        _ ≤ cφ * phiProgressionAverageShape P X d s :=
          mul_le_mul_of_nonneg_left hshape_lower hcφ.le
        _ ≤ phiProgressionAverage P X d a s := hφX.1
    · calc
        phiProgressionAverage P X d a s
            ≤ Cφ * phiProgressionAverageShape P X d s := hφX.2
        _ ≤ Cφ * (k * (hslant.C * logX X)) :=
          mul_le_mul_of_nonneg_left hshape_upper hCφ.le
        _ = (Cφ * k * hslant.C) * logX X := by ring

/-- Fixed-parameter `FactorAsymp` consequence of the manuscript-parameter
ordinary-squarefree route for `lem:phi-progression-average`.

Compared with `phiProgressionAverage_factor_asymp_of_twoSided`, this wrapper
threads the paper's ordinary lower estimate and the single wide ordinary upper
estimate directly through the checked phi-progression bridge. -/
noncomputable def
    phiProgressionAverage_factor_asymp_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.η) P.θ P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    FactorAsymp (fun X => phiProgressionAverage P X d a s) logX :=
  phiProgressionAverage_factor_asymp_of_twoSided
    (PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
      hlower hupper)
    hdpos hdsqf hdodd had hs hssqf hsd

/-- Fixed-parameter `FactorAsymp` consequence of the wide-lower/wide-upper
ordinary-squarefree route. -/
noncomputable def
    phiProgressionAverage_factor_asymp_of_ordinarySquarefreeProgression_wideLower_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.θ) P.θ P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    FactorAsymp (fun X => phiProgressionAverage P X d a s) logX :=
  phiProgressionAverage_factor_asymp_of_twoSided
    (PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_wideLower_wideUpper_concreteOmegaTail
      hlower hupper)
    hdpos hdsqf hdodd had hs hssqf hsd

/-- Fixed-parameter `FactorAsymp` consequence of the manuscript-aligned
long-window ordinary-squarefree route for `lem:phi-progression-average`. -/
noncomputable def
    phiProgressionAverage_factor_asymp_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    FactorAsymp (fun X => phiProgressionAverage P X d a s) logX :=
  phiProgressionAverage_factor_asymp_of_twoSided
    (PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
      hlower hupper)
    hdpos hdsqf hdodd had hs hssqf hsd

/-- Fixed-parameter `FactorAsymp` consequence of the wide-lower long-window
ordinary-squarefree route. -/
noncomputable def
    phiProgressionAverage_factor_asymp_of_ordinarySquarefreeProgressionLong_wideLower_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    FactorAsymp (fun X => phiProgressionAverage P X d a s) logX :=
  phiProgressionAverage_factor_asymp_of_twoSided
    (PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgressionLong_wideLower_wideUpper_concreteOmegaTail
      hlower hupper)
    hdpos hdsqf hdodd had hs hssqf hsd

/-- Combined paper-facing output of `lem:phi-progression-average`.

The same ordinary-squarefree lower estimate and wide ordinary-squarefree upper
estimate yield both the uniform two-sided reciprocal-`φ` progression average
and the fixed-parameter `FactorAsymp` datum consumed by the mass assembly. -/
noncomputable def PhiProgressionAverage_outputs_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.η) P.θ P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    (Σ' _h : PhiProgressionAverageTwoSided P,
      FactorAsymp (fun X => phiProgressionAverage P X d a s) logX) :=
  ⟨PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
      hlower hupper,
    phiProgressionAverage_factor_asymp_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
      hlower hupper hdpos hdsqf hdodd had hs hssqf hsd⟩

/-- Combined output of the wide-lower/wide-upper route for the
phi-progression average. -/
noncomputable def
    PhiProgressionAverage_outputs_of_ordinarySquarefreeProgression_wideLower_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.θ) P.θ P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    (Σ' _h : PhiProgressionAverageTwoSided P,
      FactorAsymp (fun X => phiProgressionAverage P X d a s) logX) :=
  ⟨PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_wideLower_wideUpper_concreteOmegaTail
      hlower hupper,
    phiProgressionAverage_factor_asymp_of_ordinarySquarefreeProgression_wideLower_wideUpper_concreteOmegaTail
      hlower hupper hdpos hdsqf hdodd had hs hssqf hsd⟩

/-- Reciprocal-`φ` progression average with the ordinary-squarefree progression
hypotheses discharged by the cited standard input. -/
theorem PhiProgressionAverageTwoSided_of_standard_ordinarySquarefree
    {P : Params} [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    PhiProgressionAverageTwoSided P :=
  PhiProgressionAverageTwoSided_of_bareLower_and_gammaQuotientUpper
    (PhiProgressionBareLower_of_sqfRecipLower
      (PhiProgressionSqfRecipLower_of_standard_ordinarySquarefree P))
    PhiProgressionGammaQuotientUpper_of_standard_ordinarySquarefree

/-- Fixed-parameter `FactorAsymp` consequence of the cited standard
ordinary-squarefree progression input. -/
noncomputable def phiProgressionAverage_factor_asymp_of_standard_ordinarySquarefree
    {P : Params} [Fact (PhiProgressionGammaQuotientUpperYU P)]
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    FactorAsymp (fun X => phiProgressionAverage P X d a s) logX :=
  phiProgressionAverage_factor_asymp_of_twoSided
    (PhiProgressionAverageTwoSided_of_standard_ordinarySquarefree (P := P))
    hdpos hdsqf hdodd had hs hssqf hsd

/-- Combined phi-progression output with the ordinary-squarefree hypotheses
reduced to the cited standard input. -/
noncomputable def PhiProgressionAverage_outputs_of_standard_ordinarySquarefree
    {P : Params} [Fact (PhiProgressionGammaQuotientUpperYU P)]
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    (Σ' _h : PhiProgressionAverageTwoSided P,
      FactorAsymp (fun X => phiProgressionAverage P X d a s) logX) :=
  ⟨PhiProgressionAverageTwoSided_of_standard_ordinarySquarefree (P := P),
    phiProgressionAverage_factor_asymp_of_standard_ordinarySquarefree
      hdpos hdsqf hdodd had hs hssqf hsd⟩

/-- Combined manuscript-aligned long-window output of
`lem:phi-progression-average`. -/
noncomputable def
    PhiProgressionAverage_outputs_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    (Σ' _h : PhiProgressionAverageTwoSided P,
      FactorAsymp (fun X => phiProgressionAverage P X d a s) logX) :=
  ⟨PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
      hlower hupper,
    phiProgressionAverage_factor_asymp_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
      hlower hupper hdpos hdsqf hdodd had hs hssqf hsd⟩

/-- Combined output of the wide-lower long-window route for the
phi-progression average. -/
noncomputable def
    PhiProgressionAverage_outputs_of_ordinarySquarefreeProgressionLong_wideLower_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    (Σ' _h : PhiProgressionAverageTwoSided P,
      FactorAsymp (fun X => phiProgressionAverage P X d a s) logX) :=
  ⟨PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgressionLong_wideLower_wideUpper_concreteOmegaTail
      hlower hupper,
    phiProgressionAverage_factor_asymp_of_ordinarySquarefreeProgressionLong_wideLower_wideUpper_concreteOmegaTail
      hlower hupper hdpos hdsqf hdodd had hs hssqf hsd⟩

/-- **Squarefree-conductor average as a `FactorAsymp` to `log X`** (cited:
`Inputs.s_average_recip` = `lem:s-average`, tex 936–953).

`sAvgRecip P X = ∑_{s ≤ X^η, μ²(s)} 1/s ≍ log S = η log X ≍ log X`.  The `η` is
absorbed into the two constants.  This discharges the manuscript's `log S` factor
(the `∑_s μ²(s)/s` part of `lem:small-divisor-average`, tex 1509–1512) to a cited
input.

The nonnegativity of the finite reciprocal sum is proved in `Inputs`; the
threshold is taken above `e` so `log X > 0`. -/
noncomputable def sAvgRecip_asymp (P : Params) :
    FactorAsymp (fun X => Inputs.sAvgRecip P X) logX where
  c := P.η * (Inputs.s_average_recip P).choose
  C := P.η * (Inputs.s_average_recip P).choose_spec.choose
  X₀ := max (Inputs.s_average_recip P).choose_spec.choose_spec.choose (Real.exp 1)
  c_pos := mul_pos P.η_pos (Inputs.s_average_recip P).choose_spec.choose_spec.choose_spec.1
  C_pos := mul_pos P.η_pos (Inputs.s_average_recip P).choose_spec.choose_spec.choose_spec.2.1
  f_nonneg := fun X _ => Inputs.sAvgRecip_nonneg P X
  sandwich := fun X hX => by
    have hX0' : (Inputs.s_average_recip P).choose_spec.choose_spec.choose ≤ X :=
      le_trans (le_max_left _ _) hX
    have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
    have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
    have hsand :=
      (Inputs.s_average_recip P).choose_spec.choose_spec.choose_spec.2.2 X hX0'
    -- rewrite `log (SScale P X) = η · log X`
    rw [log_SScale P hXpos] at hsand
    obtain ⟨hlo, hhi⟩ := hsand
    refine ⟨?_, ?_⟩
    · -- (η·c)·(log X) = c·(η·log X) ≤ sAvgRecip
      have : (Inputs.s_average_recip P).choose * (P.η * Real.log X)
              ≤ Inputs.sAvgRecip P X := hlo
      unfold logX
      linarith [this]
    · have : Inputs.sAvgRecip P X
              ≤ (Inputs.s_average_recip P).choose_spec.choose * (P.η * Real.log X) := hhi
      unfold logX
      linarith [this]

noncomputable def sAvgPhi_asymp (P : Params) :
    FactorAsymp (fun X => Inputs.sAvgPhi P X) logX where
  c := P.η * (Inputs.s_average_phi_unconditional P).choose
  C := P.η * (Inputs.s_average_phi_unconditional P).choose_spec.choose
  X₀ := max (Inputs.s_average_phi_unconditional P).choose_spec.choose_spec.choose (Real.exp 1)
  c_pos := mul_pos P.η_pos
    (Inputs.s_average_phi_unconditional P).choose_spec.choose_spec.choose_spec.1
  C_pos := mul_pos P.η_pos
    (Inputs.s_average_phi_unconditional P).choose_spec.choose_spec.choose_spec.2.1
  f_nonneg := fun X _ => Inputs.sAvgPhi_nonneg P X
  sandwich := fun X hX => by
    have hX0' : (Inputs.s_average_phi_unconditional P).choose_spec.choose_spec.choose ≤ X :=
      le_trans (le_max_left _ _) hX
    have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
    have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
    have hsand :=
      (Inputs.s_average_phi_unconditional P).choose_spec.choose_spec.choose_spec.2.2 X hX0'
    rw [log_SScale P hXpos] at hsand
    obtain ⟨hlo, hhi⟩ := hsand
    refine ⟨?_, ?_⟩
    · have : (Inputs.s_average_phi_unconditional P).choose * (P.η * Real.log X)
              ≤ Inputs.sAvgPhi P X := hlo
      unfold logX
      linarith [this]
    · have : Inputs.sAvgPhi P X
              ≤ (Inputs.s_average_phi_unconditional P).choose_spec.choose *
                (P.η * Real.log X) := hhi
      unfold logX
      linarith [this]

noncomputable def exactDivisorMPhiMassShape_factor_asymp
    (P : Params) :
    FactorAsymp (fun X => exactDivisorMPhiMassShape P X) logSq where
  c := (P.θ - P.lam - P.η) * (sAvgRecip_asymp P).c
  C := (P.θ - P.lam) * (sAvgRecip_asymp P).C
  X₀ := max (sAvgRecip_asymp P).X₀ (Real.exp 1)
  c_pos := by
    have hcoef : 0 < P.θ - P.lam - P.η := by
      linarith [P.lam_add_η_lt_θ]
    exact mul_pos hcoef (sAvgRecip_asymp P).c_pos
  C_pos := by
    have hcoef : 0 < P.θ - P.lam := by
      linarith [P.lam_add_η_lt_θ, P.η_pos]
    exact mul_pos hcoef (sAvgRecip_asymp P).C_pos
  f_nonneg := by
    intro X hX
    have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
    exact exactDivisorMPhiMassShape_nonneg P hXe
  sandwich := by
    intro X hX
    have hXs : (sAvgRecip_asymp P).X₀ ≤ X := le_trans (le_max_left _ _) hX
    have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
    have hlog_nonneg : 0 ≤ logX X := by
      unfold logX
      exact Real.log_nonneg
        (le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe)
    have hsavg_lower := (sAvgRecip_asymp P).lower hXs
    have hsavg_upper := (sAvgRecip_asymp P).upper hXs
    have hshape_lower :=
      exactDivisorMPhiMassShape_lower_logX_sAvgRecip P hXe
    have hshape_upper :=
      exactDivisorMPhiMassShape_upper_logX_sAvgRecip P hXe
    have hcoef_lower : 0 ≤ P.θ - P.lam - P.η := by
      have : 0 < P.θ - P.lam - P.η := by
        linarith [P.lam_add_η_lt_θ]
      exact this.le
    have hcoef_upper : 0 ≤ P.θ - P.lam := by
      have : 0 < P.θ - P.lam := by
        linarith [P.lam_add_η_lt_θ, P.η_pos]
      exact this.le
    constructor
    · calc
        ((P.θ - P.lam - P.η) * (sAvgRecip_asymp P).c) * logSq X
            = (P.θ - P.lam - P.η) * ((sAvgRecip_asymp P).c * logX X) * logX X := by
              unfold logSq logX
              ring
        _ ≤ (P.θ - P.lam - P.η) * Inputs.sAvgRecip P X * logX X := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hsavg_lower hcoef_lower) hlog_nonneg
        _ = (P.θ - P.lam - P.η) * logX X * Inputs.sAvgRecip P X := by ring
        _ ≤ exactDivisorMPhiMassShape P X := hshape_lower
    · calc
        exactDivisorMPhiMassShape P X
            ≤ (P.θ - P.lam) * logX X * Inputs.sAvgRecip P X := hshape_upper
        _ ≤ (P.θ - P.lam) * logX X * ((sAvgRecip_asymp P).C * logX X) := by
              exact mul_le_mul_of_nonneg_left hsavg_upper
                (mul_nonneg hcoef_upper hlog_nonneg)
        _ = ((P.θ - P.lam) * (sAvgRecip_asymp P).C) * logSq X := by
              unfold logSq logX
              ring

theorem exactDivisorMPhiMassShape_logSq
    (P : Params) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassShape P X ∧
        exactDivisorMPhiMassShape P X ≤ C * logSq X := by
  let h := exactDivisorMPhiMassShape_factor_asymp P
  exact ⟨h.c, h.C, h.X₀, h.c_pos, h.C_pos, fun X hX => h.sandwich X hX⟩

noncomputable def exactDivisorM1MassShape_factor_asymp
    (P : Params) :
    FactorAsymp (fun X => exactDivisorM1MassShape P X) logSq where
  c := (P.θ - P.lam - P.η) * (sAvgPhi_asymp P).c
  C := (P.θ - P.lam) * (sAvgPhi_asymp P).C
  X₀ := max (sAvgPhi_asymp P).X₀ (Real.exp 1)
  c_pos := by
    have hcoef : 0 < P.θ - P.lam - P.η := by
      linarith [P.lam_add_η_lt_θ]
    exact mul_pos hcoef (sAvgPhi_asymp P).c_pos
  C_pos := by
    have hcoef : 0 < P.θ - P.lam := by
      linarith [P.lam_add_η_lt_θ, P.η_pos]
    exact mul_pos hcoef (sAvgPhi_asymp P).C_pos
  f_nonneg := by
    intro X hX
    have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
    exact exactDivisorM1MassShape_nonneg P hXe
  sandwich := by
    intro X hX
    have hXs : (sAvgPhi_asymp P).X₀ ≤ X := le_trans (le_max_left _ _) hX
    have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
    have hlog_nonneg : 0 ≤ logX X := by
      unfold logX
      exact Real.log_nonneg
        (le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe)
    have hsavg_lower := (sAvgPhi_asymp P).lower hXs
    have hsavg_upper := (sAvgPhi_asymp P).upper hXs
    have hshape_lower :=
      exactDivisorM1MassShape_lower_logX_sAvgPhi P hXe
    have hshape_upper :=
      exactDivisorM1MassShape_upper_logX_sAvgPhi P hXe
    have hcoef_lower : 0 ≤ P.θ - P.lam - P.η := by
      have : 0 < P.θ - P.lam - P.η := by
        linarith [P.lam_add_η_lt_θ]
      exact this.le
    have hcoef_upper : 0 ≤ P.θ - P.lam := by
      have : 0 < P.θ - P.lam := by
        linarith [P.lam_add_η_lt_θ, P.η_pos]
      exact this.le
    constructor
    · calc
        ((P.θ - P.lam - P.η) * (sAvgPhi_asymp P).c) * logSq X
            = (P.θ - P.lam - P.η) * ((sAvgPhi_asymp P).c * logX X) * logX X := by
              unfold logSq logX
              ring
        _ ≤ (P.θ - P.lam - P.η) * Inputs.sAvgPhi P X * logX X := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hsavg_lower hcoef_lower) hlog_nonneg
        _ = (P.θ - P.lam - P.η) * logX X * Inputs.sAvgPhi P X := by ring
        _ ≤ exactDivisorM1MassShape P X := hshape_lower
    · calc
        exactDivisorM1MassShape P X
            ≤ (P.θ - P.lam) * logX X * Inputs.sAvgPhi P X := hshape_upper
        _ ≤ (P.θ - P.lam) * logX X * ((sAvgPhi_asymp P).C * logX X) := by
              exact mul_le_mul_of_nonneg_left hsavg_upper
                (mul_nonneg hcoef_upper hlog_nonneg)
        _ = ((P.θ - P.lam) * (sAvgPhi_asymp P).C) * logSq X := by
              unfold logSq logX
              ring

theorem exactDivisorM1MassShape_logSq
    (P : Params) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorM1MassShape P X ∧
        exactDivisorM1MassShape P X ≤ C * logSq X := by
  let h := exactDivisorM1MassShape_factor_asymp P
  exact ⟨h.c, h.C, h.X₀, h.c_pos, h.C_pos, fun X hX => h.sandwich X hX⟩

/-! ### Paper-facing exact-divisor mass output for `prop:M`. -/

/-- The raw `M₁` exact-divisor mass is quadratic in `log X` along the paper's
ordinary-squarefree progression route.

This composes the checked raw-to-fiber identity, the fiber-to-shape comparison,
and the shape-level `≍ (log X)^2` theorem. -/
theorem exactDivisorM1MassRaw_logSq_of_ordinarySquarefreeProgression_wideUpper
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.η) P.θ P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorM1MassRaw P X ∧
        exactDivisorM1MassRaw P X ≤ C * logSq X := by
  rcases
      exactDivisorM1MassFiber_comparable_to_shape_of_ordinarySquarefreeProgression_wideUpper
        hlower hupper with
    ⟨a, A, Xcmp, ha, hA, hcmp⟩
  rcases exactDivisorM1MassShape_logSq P with
    ⟨c, C, Xshape, hc, hC, hshape⟩
  refine ⟨a * c, A * C, max Xcmp Xshape, mul_pos ha hc, mul_pos hA hC, ?_⟩
  intro X hX
  have hXcmp : Xcmp ≤ X := le_trans (le_max_left _ _) hX
  have hXshape : Xshape ≤ X := le_trans (le_max_right _ _) hX
  have hcmpX := hcmp X hXcmp
  have hshapeX := hshape X hXshape
  constructor
  · calc
      (a * c) * logSq X = a * (c * logSq X) := by ring
      _ ≤ a * exactDivisorM1MassShape P X :=
          mul_le_mul_of_nonneg_left hshapeX.1 ha.le
      _ ≤ exactDivisorM1MassFiber P X := hcmpX.1
      _ = exactDivisorM1MassRaw P X := by
          rw [← exactDivisorM1MassRaw_eq_fiber P X]
  · calc
      exactDivisorM1MassRaw P X = exactDivisorM1MassFiber P X := by
          rw [exactDivisorM1MassRaw_eq_fiber P X]
      _ ≤ A * exactDivisorM1MassShape P X := hcmpX.2
      _ ≤ A * (C * logSq X) := mul_le_mul_of_nonneg_left hshapeX.2 hA.le
      _ = (A * C) * logSq X := by ring

/-- The raw `M₁` exact-divisor mass is quadratic in `log X` using the
manuscript-aligned non-progression lower half of `lem:ordinary-sqf`.

Only the upper bound still uses the progression form, because the fixed
trivial-modulus lower bound is all that `prop:M` needs. -/
theorem exactDivisorM1MassRaw_logSq_of_ordinarySquarefreeCoprimeLong_wideUpper
    {P : Params}
    (hlower :
      OrdinarySquarefreeCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorM1MassRaw P X ∧
        exactDivisorM1MassRaw P X ≤ C * logSq X := by
  rcases
      exactDivisorM1MassFiber_comparable_to_shape_of_ordinarySquarefreeCoprimeLong_wideUpper
        hlower hupper with
    ⟨a, A, Xcmp, ha, hA, hcmp⟩
  rcases exactDivisorM1MassShape_logSq P with
    ⟨c, C, Xshape, hc, hC, hshape⟩
  refine ⟨a * c, A * C, max Xcmp Xshape, mul_pos ha hc, mul_pos hA hC, ?_⟩
  intro X hX
  have hXcmp : Xcmp ≤ X := le_trans (le_max_left _ _) hX
  have hXshape : Xshape ≤ X := le_trans (le_max_right _ _) hX
  have hcmpX := hcmp X hXcmp
  have hshapeX := hshape X hXshape
  constructor
  · calc
      (a * c) * logSq X = a * (c * logSq X) := by ring
      _ ≤ a * exactDivisorM1MassShape P X :=
          mul_le_mul_of_nonneg_left hshapeX.1 ha.le
      _ ≤ exactDivisorM1MassFiber P X := hcmpX.1
      _ = exactDivisorM1MassRaw P X := by
          rw [← exactDivisorM1MassRaw_eq_fiber P X]
  · calc
      exactDivisorM1MassRaw P X = exactDivisorM1MassFiber P X := by
          rw [exactDivisorM1MassRaw_eq_fiber P X]
      _ ≤ A * exactDivisorM1MassShape P X := hcmpX.2
      _ ≤ A * (C * logSq X) := mul_le_mul_of_nonneg_left hshapeX.2 hA.le
      _ = (A * C) * logSq X := by ring

/-- The raw `M₁` exact-divisor mass is quadratic in `log X` from the
specialized phi-window squarefree lower carrier and the wide upper estimate. -/
theorem exactDivisorM1MassRaw_logSq_of_sqfRecipLower_ordinaryUpper_wide
    {P : Params}
    (hlower : PhiProgressionSqfRecipLower P)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorM1MassRaw P X ∧
        exactDivisorM1MassRaw P X ≤ C * logSq X := by
  rcases
      exactDivisorM1MassFiber_comparable_to_shape_of_sqfRecipLower_ordinaryUpper_wide
        hlower hupper with
    ⟨a, A, Xcmp, ha, hA, hcmp⟩
  rcases exactDivisorM1MassShape_logSq P with
    ⟨c, C, Xshape, hc, hC, hshape⟩
  refine ⟨a * c, A * C, max Xcmp Xshape, mul_pos ha hc, mul_pos hA hC, ?_⟩
  intro X hX
  have hXcmp : Xcmp ≤ X := le_trans (le_max_left _ _) hX
  have hXshape : Xshape ≤ X := le_trans (le_max_right _ _) hX
  have hcmpX := hcmp X hXcmp
  have hshapeX := hshape X hXshape
  constructor
  · calc
      (a * c) * logSq X = a * (c * logSq X) := by ring
      _ ≤ a * exactDivisorM1MassShape P X :=
          mul_le_mul_of_nonneg_left hshapeX.1 ha.le
      _ ≤ exactDivisorM1MassFiber P X := hcmpX.1
      _ = exactDivisorM1MassRaw P X := by
          rw [← exactDivisorM1MassRaw_eq_fiber P X]
  · calc
      exactDivisorM1MassRaw P X = exactDivisorM1MassFiber P X := by
          rw [exactDivisorM1MassRaw_eq_fiber P X]
      _ ≤ A * exactDivisorM1MassShape P X := hcmpX.2
      _ ≤ A * (C * logSq X) := mul_le_mul_of_nonneg_left hshapeX.2 hA.le
      _ = (A * C) * logSq X := by ring

/-- Long-window version of
`exactDivisorM1MassRaw_logSq_of_sqfRecipLower_ordinaryUpper_wide`. -/
theorem exactDivisorM1MassRaw_logSq_of_sqfRecipLower_ordinaryUpperLong_wide
    {P : Params}
    (hlower : PhiProgressionSqfRecipLower P)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpperLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorM1MassRaw P X ∧
        exactDivisorM1MassRaw P X ≤ C * logSq X := by
  rcases
      exactDivisorM1MassFiber_comparable_to_shape_of_sqfRecipLower_ordinaryUpperLong_wide
        hlower hupper with
    ⟨a, A, Xcmp, ha, hA, hcmp⟩
  rcases exactDivisorM1MassShape_logSq P with
    ⟨c, C, Xshape, hc, hC, hshape⟩
  refine ⟨a * c, A * C, max Xcmp Xshape, mul_pos ha hc, mul_pos hA hC, ?_⟩
  intro X hX
  have hXcmp : Xcmp ≤ X := le_trans (le_max_left _ _) hX
  have hXshape : Xshape ≤ X := le_trans (le_max_right _ _) hX
  have hcmpX := hcmp X hXcmp
  have hshapeX := hshape X hXshape
  constructor
  · calc
      (a * c) * logSq X = a * (c * logSq X) := by ring
      _ ≤ a * exactDivisorM1MassShape P X :=
          mul_le_mul_of_nonneg_left hshapeX.1 ha.le
      _ ≤ exactDivisorM1MassFiber P X := hcmpX.1
      _ = exactDivisorM1MassRaw P X := by
          rw [← exactDivisorM1MassRaw_eq_fiber P X]
  · calc
      exactDivisorM1MassRaw P X = exactDivisorM1MassFiber P X := by
          rw [exactDivisorM1MassRaw_eq_fiber P X]
      _ ≤ A * exactDivisorM1MassShape P X := hcmpX.2
      _ ≤ A * (C * logSq X) := mul_le_mul_of_nonneg_left hshapeX.2 hA.le
      _ = (A * C) * logSq X := by ring

/-- The raw `M_φ` exact-divisor mass is quadratic in `log X` from the
trivial-modulus reciprocal-`φ` fiber estimate used directly in `prop:M`. -/
theorem exactDivisorMPhiMassRaw_logSq_of_fiberAverageTwoSided
    {P : Params}
    (hφ : ExactDivisorMPhiFiberAverageTwoSided P) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
        exactDivisorMPhiMassRaw P X ≤ C * logSq X := by
  rcases exactDivisorMPhiMassFiber_comparable_to_shape_of_fiberAverageTwoSided hφ with
    ⟨a, A, Xcmp, ha, hA, hcmp⟩
  rcases exactDivisorMPhiMassShape_logSq P with
    ⟨c, C, Xshape, hc, hC, hshape⟩
  refine ⟨a * c, A * C, max Xcmp Xshape, mul_pos ha hc, mul_pos hA hC, ?_⟩
  intro X hX
  have hXcmp : Xcmp ≤ X := le_trans (le_max_left _ _) hX
  have hXshape : Xshape ≤ X := le_trans (le_max_right _ _) hX
  have hcmpX := hcmp X hXcmp
  have hshapeX := hshape X hXshape
  constructor
  · calc
      (a * c) * logSq X = a * (c * logSq X) := by ring
      _ ≤ a * exactDivisorMPhiMassShape P X :=
          mul_le_mul_of_nonneg_left hshapeX.1 ha.le
      _ ≤ exactDivisorMPhiMassFiber P X := hcmpX.1
      _ = exactDivisorMPhiMassRaw P X := by
          rw [← exactDivisorMPhiMassRaw_eq_fiber P X]
  · calc
      exactDivisorMPhiMassRaw P X = exactDivisorMPhiMassFiber P X := by
          rw [exactDivisorMPhiMassRaw_eq_fiber P X]
      _ ≤ A * exactDivisorMPhiMassShape P X := hcmpX.2
      _ ≤ A * (C * logSq X) := mul_le_mul_of_nonneg_left hshapeX.2 hA.le
      _ = (A * C) * logSq X := by ring

/-- The raw `M_φ` exact-divisor mass is quadratic in `log X` along the same
ordinary-squarefree progression route as `lem:phi-progression-average`.

The reciprocal-`φ` progression theorem supplies the fiber-to-shape comparison;
the finite raw/fiber identity and the shape-level log-square law then give the
raw mass statement. -/
theorem
    exactDivisorMPhiMassRaw_logSq_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.η) P.θ P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
        exactDivisorMPhiMassRaw P X ≤ C * logSq X := by
  let hφ :=
    PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
      hlower hupper
  exact exactDivisorMPhiMassRaw_logSq_of_fiberAverageTwoSided
    (ExactDivisorMPhiFiberAverageTwoSided_of_phiProgressionAverageTwoSided hφ)

/-- Raw `M_φ` exact-divisor mass route using only wide lower and wide upper
ordinary-squarefree estimates. -/
theorem
    exactDivisorMPhiMassRaw_logSq_of_ordinarySquarefreeProgression_wideLower_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.θ) P.θ P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
        exactDivisorMPhiMassRaw P X ≤ C * logSq X := by
  exact
    exactDivisorMPhiMassRaw_logSq_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
      (OrdinarySquarefreeProgressionCoprimeDensityLower_eta_of_wide hlower)
      hupper

/-- Long-window version of the raw `M_φ` exact-divisor mass route. -/
theorem
    exactDivisorMPhiMassRaw_logSq_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
        exactDivisorMPhiMassRaw P X ≤ C * logSq X := by
  exact exactDivisorMPhiMassRaw_logSq_of_fiberAverageTwoSided
    (ExactDivisorMPhiFiberAverageTwoSided_of_coprimeLong_and_ordinaryUpper_wide
      (OrdinarySquarefreeCoprimeDensityLowerLong_of_progression_long hlower)
      hupper)

/-- Long-window raw `M_φ` mass route using only wide lower and wide upper
ordinary-squarefree estimates. -/
theorem
    exactDivisorMPhiMassRaw_logSq_of_ordinarySquarefreeProgressionLong_wideLower_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
        exactDivisorMPhiMassRaw P X ≤ C * logSq X := by
  exact
    exactDivisorMPhiMassRaw_logSq_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
      (OrdinarySquarefreeProgressionCoprimeDensityLowerLong_eta_of_wide hlower)
      hupper

/-- Raw `M_φ` exact-divisor mass from the specialized phi-window squarefree
lower carrier and the wide ordinary-squarefree upper estimate. -/
theorem
    exactDivisorMPhiMassRaw_logSq_of_sqfRecipLower_ordinaryUpper_wide
    {P : Params}
    (hlower : PhiProgressionSqfRecipLower P)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
        exactDivisorMPhiMassRaw P X ≤ C * logSq X :=
    exactDivisorMPhiMassRaw_logSq_of_fiberAverageTwoSided
      (ExactDivisorMPhiFiberAverageTwoSided_of_sqfRecipLower_and_ordinaryUpper_wide
        hlower hupper)

/-- Long-window raw `M_φ` exact-divisor mass route from the specialized
phi-window squarefree lower carrier. -/
theorem
    exactDivisorMPhiMassRaw_logSq_of_sqfRecipLower_ordinaryUpperLong_wide
    {P : Params}
    (hlower : PhiProgressionSqfRecipLower P)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpperLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
        exactDivisorMPhiMassRaw P X ≤ C * logSq X :=
  exactDivisorMPhiMassRaw_logSq_of_fiberAverageTwoSided
    (ExactDivisorMPhiFiberAverageTwoSided_of_sqfRecipLower_and_ordinaryUpperLong_wide
      hlower hupper)

/-- Unpacked raw exact-divisor mass bounds from the specialized phi-window
squarefree reciprocal lower carrier and the wide ordinary-squarefree upper
estimate.

This is the tight `prop:M` bridge used to remove the generic lower-density
hypothesis from both exact-divisor mass halves. -/
theorem exactDivisorMassRaw_quadratic_of_sqfRecipLower_wideUpper
    {P : Params}
    (hlower : PhiProgressionSqfRecipLower P)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorM1MassRaw P X ∧
        exactDivisorM1MassRaw P X ≤ C * logSq X)
    ∧
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
        exactDivisorMPhiMassRaw P X ≤ C * logSq X) := by
  constructor
  · exact exactDivisorM1MassRaw_logSq_of_sqfRecipLower_ordinaryUpper_wide
      hlower hupper
  · exact exactDivisorMPhiMassRaw_logSq_of_sqfRecipLower_ordinaryUpper_wide
      hlower hupper

/-- Long-window version of
`exactDivisorMassRaw_quadratic_of_sqfRecipLower_wideUpper`. -/
theorem exactDivisorMassRaw_quadratic_of_sqfRecipLower_wideUpperLong
    {P : Params}
    (hlower : PhiProgressionSqfRecipLower P)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpperLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ) :
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorM1MassRaw P X ∧
        exactDivisorM1MassRaw P X ≤ C * logSq X)
    ∧
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
        exactDivisorMPhiMassRaw P X ≤ C * logSq X) := by
  constructor
  · exact exactDivisorM1MassRaw_logSq_of_sqfRecipLower_ordinaryUpperLong_wide
      hlower hupper
  · exact exactDivisorMPhiMassRaw_logSq_of_sqfRecipLower_ordinaryUpperLong_wide
      hlower hupper

/-- The specialized squarefree reciprocal lower bound gives the lower half of
the raw `M1` mass comparison without any progression upper estimate. -/
theorem exactDivisorM1MassFiber_lower_of_sqfRecipLower
    {P : Params} (hlower : PhiProgressionSqfRecipLower P) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      c * exactDivisorM1MassShape P X ≤ exactDivisorM1MassFiber P X := by
  classical
  rcases hlower with ⟨c, Xlo, hc, hlo⟩
  rcases fixedNat_le_UScale_eventually 1 with ⟨XU, hU⟩
  refine ⟨c, max (max Xlo XU) (Real.exp 1), hc, ?_⟩
  intro X hX
  have hXlo : Xlo ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXU : XU ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXe
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hS_nonneg : 0 ≤ SScale P X :=
    (Real.rpow_pos_of_pos hXpos P.η).le
  have hU1 : ((1 : ℕ) : ℝ) ≤ UScale X := hU X hXU
  unfold exactDivisorM1MassShape exactDivisorM1MassFiber exactDivisorSRange
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊SScale P X⌋₊ :=
    (Finset.mem_filter.mp hs).1
  have hs_one : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
  have hs_floor : s ≤ ⌊SScale P X⌋₊ := (Finset.mem_Icc.mp hsIcc).2
  have hs_sqf : Squarefree s := (Finset.mem_filter.mp hs).2
  have hs_pos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos_nat
  have hsS : (s : ℝ) ≤ SScale P X :=
    le_trans (by exact_mod_cast hs_floor) (Nat.floor_le hS_nonneg)
  have hbare :
      c * phiProgressionAverageShape P X 1 s ≤
        phiProgressionBareAverage P X 1 0 s := by
    have hraw := hlo X hXlo 1 0 s (by norm_num) squarefree_one
      (by norm_num) hU1 (by norm_num) hs_one hs_sqf
      (Nat.coprime_one_right s) hsS
    simpa [phiProgressionBareAverage_eq_sqfRecip,
      phiProgressionAverageShape,
      log_phiProgressionU1_div_U0_eq_slantLogLength P hXpos hs_pos_nat]
      using hraw
  have hscale_nonneg : 0 ≤ (1 : ℝ) / (s : ℝ) := by positivity
  calc
    c * (((Nat.totient s : ℝ) / (s : ℝ) ^ (2 : ℕ)) *
          slantLogLength P s X) =
        ((1 : ℝ) / (s : ℝ)) *
          (c * phiProgressionAverageShape P X 1 s) := by
            unfold phiProgressionAverageShape
            ring_nf
    _ ≤ ((1 : ℝ) / (s : ℝ)) *
          phiProgressionBareAverage P X 1 0 s :=
      mul_le_mul_of_nonneg_left hbare hscale_nonneg

/-- Pointwise `1/n <= 1/phi(n)` makes the raw `M1` mass no larger than the
raw reciprocal-totient mass on the same finite support. -/
theorem exactDivisorM1MassRaw_le_MPhiMassRaw (P : Params) (X : ℝ) :
    exactDivisorM1MassRaw P X ≤ exactDivisorMPhiMassRaw P X := by
  rw [exactDivisorM1MassRaw_eq_fiber, exactDivisorMPhiMassRaw_eq_fiber]
  unfold exactDivisorM1MassFiber exactDivisorMPhiMassFiber
  apply Finset.sum_le_sum
  intro s hs
  have hs_one : 1 ≤ s :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
  have hs_pos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs_one
  have hcoeff : (1 : ℝ) / (s : ℝ) ≤
      (1 : ℝ) / (Nat.totient s : ℝ) :=
    one_div_nat_le_one_div_totient hs_pos
  have hfiber := phiProgressionBareAverage_le_phiProgressionAverage P X 1 0 s
  exact mul_le_mul hcoeff hfiber
    (phiProgressionBareAverage_nonneg P X 1 0 s) (by positivity)

/-- Two-sided raw `M1` mass bound from the specialized lower estimate and the
already bounded reciprocal-totient mass. -/
theorem exactDivisorM1MassRaw_logSq_of_standard_lower_and_gammaYU
    {P : Params} [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorM1MassRaw P X ∧
        exactDivisorM1MassRaw P X ≤ C * logSq X := by
  rcases exactDivisorM1MassFiber_lower_of_sqfRecipLower
      (PhiProgressionSqfRecipLower_of_standard_ordinarySquarefree P) with
    ⟨a, Xlower, ha, hlower⟩
  rcases exactDivisorM1MassShape_logSq P with
    ⟨c, _Cshape, Xshape, hc, _hCshape, hshape⟩
  rcases exactDivisorMPhiMassRaw_logSq_of_fiberAverageTwoSided
      (ExactDivisorMPhiFiberAverageTwoSided_of_standard_ordinarySquarefree
        (P := P)) with
    ⟨_cm, Cm, Xm, _hcm, hCm, hmphi⟩
  refine ⟨a * c, Cm, max (max Xlower Xshape) Xm,
    mul_pos ha hc, hCm, ?_⟩
  intro X hX
  have hXlower : Xlower ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXshape : Xshape ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXm : Xm ≤ X := le_trans (le_max_right _ _) hX
  constructor
  · calc
      (a * c) * logSq X = a * (c * logSq X) := by ring
      _ ≤ a * exactDivisorM1MassShape P X :=
        mul_le_mul_of_nonneg_left (hshape X hXshape).1 ha.le
      _ ≤ exactDivisorM1MassFiber P X := hlower X hXlower
      _ = exactDivisorM1MassRaw P X := by
        rw [← exactDivisorM1MassRaw_eq_fiber]
  · exact (exactDivisorM1MassRaw_le_MPhiMassRaw P X).trans
      (hmphi X hXm).2

/-- Unpacked raw exact-divisor mass bounds for `prop:M`.  The lower density is
the cited ordinary-squarefree input; the upper route is the explicit
tensor-range gamma bound rather than the invalid negative-endpoint shortcut. -/
theorem exactDivisorMassRaw_quadratic_of_standard_ordinarySquarefree
    {P : Params} [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorM1MassRaw P X ∧
        exactDivisorM1MassRaw P X ≤ C * logSq X)
    ∧
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
          exactDivisorMPhiMassRaw P X ≤ C * logSq X) :=
  ⟨exactDivisorM1MassRaw_logSq_of_standard_lower_and_gammaYU,
    exactDivisorMPhiMassRaw_logSq_of_fiberAverageTwoSided
      (ExactDivisorMPhiFiberAverageTwoSided_of_standard_ordinarySquarefree
        (P := P))⟩

/-- Unpacked two-sided raw exact-divisor mass bounds for `prop:M`.

Both manuscript masses, `M₁` and `M_φ`, are represented by their raw finite
carriers and are shown to be `≍ (log X)^2` from the ordinary-squarefree lower
estimate and the wide ordinary-squarefree upper estimate. -/
theorem
    exactDivisorMassRaw_quadratic_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.η) P.θ P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorM1MassRaw P X ∧
        exactDivisorM1MassRaw P X ≤ C * logSq X)
    ∧
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
        exactDivisorMPhiMassRaw P X ≤ C * logSq X) := by
  constructor
  · exact
      exactDivisorM1MassRaw_logSq_of_ordinarySquarefreeProgression_wideUpper
        hlower hupper
  · exact
      exactDivisorMPhiMassRaw_logSq_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
        hlower hupper

/-- Unpacked raw exact-divisor mass bounds using only wide lower and wide upper
ordinary-squarefree estimates. -/
theorem
    exactDivisorMassRaw_quadratic_of_ordinarySquarefreeProgression_wideLower_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.θ) P.θ P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorM1MassRaw P X ∧
        exactDivisorM1MassRaw P X ≤ C * logSq X)
    ∧
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
        exactDivisorMPhiMassRaw P X ≤ C * logSq X) := by
  exact
    exactDivisorMassRaw_quadratic_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
      (OrdinarySquarefreeProgressionCoprimeDensityLower_eta_of_wide hlower)
      hupper

/-- Long-window version of the unpacked two-sided raw exact-divisor mass bounds
for `prop:M`.

The single progression long-window lower estimate supplies both the D=1 `M₁`
lower carrier and the reciprocal-`φ` progression lower carrier. -/
theorem
    exactDivisorMassRaw_quadratic_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorM1MassRaw P X ∧
        exactDivisorM1MassRaw P X ≤ C * logSq X)
    ∧
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
        exactDivisorMPhiMassRaw P X ≤ C * logSq X) := by
  constructor
  · exact
      exactDivisorM1MassRaw_logSq_of_ordinarySquarefreeCoprimeLong_wideUpper
        (OrdinarySquarefreeCoprimeDensityLowerLong_of_progression_long hlower)
        hupper
  · exact
      exactDivisorMPhiMassRaw_logSq_of_fiberAverageTwoSided
        (ExactDivisorMPhiFiberAverageTwoSided_of_coprimeLong_and_ordinaryUpper_wide
          (OrdinarySquarefreeCoprimeDensityLowerLong_of_progression_long hlower)
          hupper)

/-- Long-window raw exact-divisor mass bounds using only wide lower and wide
upper ordinary-squarefree estimates. -/
theorem
    exactDivisorMassRaw_quadratic_of_ordinarySquarefreeProgressionLong_wideLower_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorM1MassRaw P X ∧
        exactDivisorM1MassRaw P X ≤ C * logSq X)
    ∧
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
        exactDivisorMPhiMassRaw P X ≤ C * logSq X) := by
  exact
    exactDivisorMassRaw_quadratic_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
      (OrdinarySquarefreeProgressionCoprimeDensityLowerLong_eta_of_wide hlower)
      hupper

/-- Unpacked two-sided raw exact-divisor mass bounds for `prop:M` using only
the non-progression mass estimates needed by that proposition.

This is narrower than the full `lem:phi-progression-average` route: `M₁` uses
the `D=1` ordinary squarefree lower estimate, and `M_φ` uses the `D=1`
reciprocal-`φ` fiber estimate. -/
theorem
    exactDivisorMassRaw_quadratic_of_coprimeLong_mphiFiber_wideUpper
    {P : Params}
    (hM1lower :
      OrdinarySquarefreeCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hM1upper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (hMφ : ExactDivisorMPhiFiberAverageTwoSided P) :
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorM1MassRaw P X ∧
        exactDivisorM1MassRaw P X ≤ C * logSq X)
    ∧
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
        exactDivisorMPhiMassRaw P X ≤ C * logSq X) := by
  exact
    ⟨exactDivisorM1MassRaw_logSq_of_ordinarySquarefreeCoprimeLong_wideUpper
        hM1lower hM1upper,
      exactDivisorMPhiMassRaw_logSq_of_fiberAverageTwoSided hMφ⟩

/-- Unpacked two-sided raw exact-divisor mass bounds for `prop:M` with the
formerly separate `M_φ` fiber hypothesis discharged.

Both mass halves now consume the same paper-facing ordinary-squarefree inputs:
the non-progression long lower estimate for the fixed `D=1` fiber and the wide
progression upper estimate for the reciprocal-`φ` gamma upper route. -/
theorem
    exactDivisorMassRaw_quadratic_of_coprimeLong_wideUpper
    {P : Params}
    (hM1lower :
      OrdinarySquarefreeCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hM1upper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorM1MassRaw P X ∧
        exactDivisorM1MassRaw P X ≤ C * logSq X)
    ∧
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
        exactDivisorMPhiMassRaw P X ≤ C * logSq X) :=
  exactDivisorMassRaw_quadratic_of_coprimeLong_mphiFiber_wideUpper
    hM1lower hM1upper
    (ExactDivisorMPhiFiberAverageTwoSided_of_coprimeLong_and_ordinaryUpper_wide
      hM1lower hM1upper)

/-- Unpacked raw exact-divisor mass bounds with the `M_φ` lower half supplied
by the specialized phi-window squarefree lower carrier.

This separates the two lower requirements: the `M₁` half still uses the
trivial-modulus ordinary squarefree lower estimate, while the `M_φ` half can be
fed by the dyadic count-to-reciprocal lower route. -/
theorem
    exactDivisorMassRaw_quadratic_of_coprimeLong_sqfRecipLower_wideUpper
    {P : Params}
    (hM1lower :
      OrdinarySquarefreeCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hMφlower : PhiProgressionSqfRecipLower P)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorM1MassRaw P X ∧
        exactDivisorM1MassRaw P X ≤ C * logSq X)
    ∧
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
        exactDivisorMPhiMassRaw P X ≤ C * logSq X) :=
  ⟨exactDivisorM1MassRaw_logSq_of_ordinarySquarefreeCoprimeLong_wideUpper
      hM1lower hupper,
    exactDivisorMPhiMassRaw_logSq_of_sqfRecipLower_ordinaryUpper_wide
      hMφlower hupper⟩

/-- Combined paper-facing output for `prop:M`.

The package keeps the same ordinary-squarefree hypotheses exposed, returns the
two-sided reciprocal-`φ` progression target used by the `M_φ` fiber, and proves
the two raw exact-divisor mass asymptotics. -/
theorem
    ExactDivisorMass_outputs_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.η) P.θ P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    PhiProgressionAverageTwoSided P ∧
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorM1MassRaw P X ∧
        exactDivisorM1MassRaw P X ≤ C * logSq X)
    ∧
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
        exactDivisorMPhiMassRaw P X ≤ C * logSq X) :=
  ⟨PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
      hlower hupper,
    exactDivisorMassRaw_quadratic_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
      hlower hupper⟩

/-- Combined exact-divisor output using only wide lower and wide upper
ordinary-squarefree estimates. -/
theorem
    ExactDivisorMass_outputs_of_ordinarySquarefreeProgression_wideLower_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.θ) P.θ P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    PhiProgressionAverageTwoSided P ∧
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorM1MassRaw P X ∧
        exactDivisorM1MassRaw P X ≤ C * logSq X)
    ∧
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
        exactDivisorMPhiMassRaw P X ≤ C * logSq X) :=
  ⟨PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_wideLower_wideUpper_concreteOmegaTail
      hlower hupper,
    exactDivisorMassRaw_quadratic_of_ordinarySquarefreeProgression_wideLower_wideUpper_concreteOmegaTail
      hlower hupper⟩

/-- Combined exact-divisor output with the ordinary-squarefree hypotheses
discharged by the cited standard input. -/
theorem ExactDivisorMass_outputs_of_standard_ordinarySquarefree
    {P : Params} [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    PhiProgressionAverageTwoSided P ∧
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorM1MassRaw P X ∧
        exactDivisorM1MassRaw P X ≤ C * logSq X)
    ∧
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
        exactDivisorMPhiMassRaw P X ≤ C * logSq X) :=
  ⟨PhiProgressionAverageTwoSided_of_standard_ordinarySquarefree (P := P),
    exactDivisorMassRaw_quadratic_of_standard_ordinarySquarefree⟩

/-- Combined `prop:M`/`thm:tensor-e` output with the ordinary-squarefree
hypotheses discharged by the cited standard input.

This is the paper-facing endpoint for the exact-divisor mass and `M_φ` tensor
route: the exact mass lower/upper outputs, the trivial-modulus `M_φ` fiber, and
both tensor-fiber bounds are all obtained without caller-supplied
ordinary-squarefree hypotheses. -/
theorem ExactDivisorMassAndTensor_outputs_of_standard_ordinarySquarefree
    {P : Params} [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    (PhiProgressionAverageTwoSided P ∧
      (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        c * logSq X ≤ exactDivisorM1MassRaw P X ∧
          exactDivisorM1MassRaw P X ≤ C * logSq X)
      ∧
      (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
          exactDivisorMPhiMassRaw P X ≤ C * logSq X))
    ∧ ExactDivisorMPhiFiberAverageTwoSided P
    ∧ (∃ K X₀ : ℝ, 0 < K ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        ∀ a : ℕ → ℕ,
          (∀ s ∈ exactDivisorSRange P X, Nat.Coprime s D →
            Nat.Coprime (a s) D) →
          exactDivisorMPhiTensorFiberCoprime P X D a
            ≤ (K / (D : ℝ)) * exactDivisorMPhiMassShape P X)
    ∧ (∃ K X₀ : ℝ, 0 < K ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        ∀ a : ℕ → ℕ,
          (∀ s ∈ exactDivisorSRange P X, Nat.Coprime s D →
            Nat.Coprime (a s) D) →
          ∀ c : ℝ, 0 < c →
            c * exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X →
            exactDivisorMPhiTensorFiberCoprime P X D a
              ≤ (K / c) * (exactDivisorMPhiMassRaw P X / (D : ℝ))) :=
  ⟨ExactDivisorMass_outputs_of_standard_ordinarySquarefree,
    ExactDivisorMPhiFiberAverageTwoSided_of_standard_ordinarySquarefree,
    exactDivisorMPhiTensorFiberCoprime_le_massShape_over_modulus_of_standard_ordinarySquarefree,
    exactDivisorMPhiTensorFiberCoprime_le_massRaw_over_modulus_of_standard_ordinarySquarefree⟩

/-- Paired tensor output with the two pointwise lower-mass comparisons
discharged from the cited ordinary-squarefree inputs.

The local fixed-`s` fiber upper bounds remain as the finite tensor hypotheses.
The constants `c₁` and `cφ` used to convert `massShape` to raw mass are chosen
internally from the already checked `M₁` and `M_φ` mass-comparison theorems. -/
theorem exactDivisorTensorPaperOutputs_of_standard_ordinarySquarefree_auto_mass_lower
    {P : Params} [Fact (PhiProgressionGammaQuotientUpperYU P)] :
    ∃ c₁ cφ X₀ : ℝ, 0 < c₁ ∧ 0 < cφ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, ∀ a : ℕ → ℕ, ∀ K₁ Kφ : ℝ,
        0 < D → 0 ≤ K₁ → 0 ≤ Kφ →
        (∀ s ∈ exactDivisorSRange P X,
          phiProgressionBareAverage P X D (a s) s
            ≤ K₁ * phiProgressionAverageShape P X D s) →
        (∀ s ∈ exactDivisorSRange P X,
          phiProgressionAverage P X D (a s) s
            ≤ Kφ * phiProgressionAverageShape P X D s) →
        exactDivisorM1MassRaw P X = exactDivisorM1MassFiber P X
          ∧ exactDivisorMPhiMassRaw P X = exactDivisorMPhiMassFiber P X
          ∧ exactDivisorM1TensorFiber P X D a
              ≤ (K₁ / c₁) * (exactDivisorM1MassRaw P X / (D : ℝ))
          ∧ exactDivisorMPhiTensorFiber P X D a
              ≤ (Kφ / cφ) * (exactDivisorMPhiMassRaw P X / (D : ℝ)) := by
  classical
  let hSqfLower : PhiProgressionSqfRecipLower P :=
    PhiProgressionSqfRecipLower_of_standard_ordinarySquarefree P
  rcases
      exactDivisorM1MassFiber_lower_of_sqfRecipLower hSqfLower with
    ⟨c₁, X₁, hc₁, hM₁⟩
  rcases
      exactDivisorMPhiMassFiber_comparable_to_shape_of_fiberAverageTwoSided
        (ExactDivisorMPhiFiberAverageTwoSided_of_standard_ordinarySquarefree
          (P := P)) with
    ⟨cφ, Cφ, Xφ, hcφ, _hCφ, hMφ⟩
  refine ⟨c₁, cφ, max X₁ Xφ, hc₁, hcφ, ?_⟩
  intro X hX D a K₁ Kφ hD hK₁ hKφ hfiber₁ hfiberφ
  have hX₁ : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hXφ : Xφ ≤ X := le_trans (le_max_right _ _) hX
  exact
    exactDivisorTensorPaperOutputs P X D a K₁ c₁ Kφ cφ
      hD hK₁ hc₁ hKφ hcφ hfiber₁ hfiberφ
      (hM₁ X hX₁) (hMφ X hXφ).1

/-- Manuscript-aligned paired coprime tensor output with the local fiber and mass
lower hypotheses discharged.

The `M₁` tensor fiber is bounded by the elementary wide-modulus CRT endpoint
calculation.  The `M_φ` tensor fiber is bounded by the cited ordinary-squarefree
upper input.  The two mass-shape lower comparisons are chosen internally from
the cited ordinary-squarefree lower/upper inputs. -/
theorem exactDivisorTensorCoprimePaperOutputs_of_standard_ordinarySquarefree_auto
    {P : Params} [Fact (PhiProgressionGammaQuotientUpperYU P)]
    (hmargin : 2 * P.η + P.σ < P.lam) :
    ∃ c₁ cφ Kφ X₀ : ℝ, 0 < c₁ ∧ 0 < cφ ∧ 0 < Kφ ∧
      ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        ∀ a : ℕ → ℕ,
          (∀ s ∈ exactDivisorSRange P X, Nat.Coprime s D →
            Nat.Coprime (a s) D) →
          exactDivisorM1MassRaw P X = exactDivisorM1MassFiber P X
            ∧ exactDivisorMPhiMassRaw P X = exactDivisorMPhiMassFiber P X
            ∧ exactDivisorM1TensorFiberCoprime P X D a
                ≤ (2 / c₁) * (exactDivisorM1MassRaw P X / (D : ℝ))
            ∧ exactDivisorMPhiTensorFiberCoprime P X D a
                ≤ (Kφ / cφ) * (exactDivisorMPhiMassRaw P X / (D : ℝ)) := by
  classical
  let hSqfLower : PhiProgressionSqfRecipLower P :=
    PhiProgressionSqfRecipLower_of_standard_ordinarySquarefree P
  rcases
      exactDivisorM1MassFiber_lower_of_sqfRecipLower hSqfLower with
    ⟨c₁, Xmass₁, hc₁, hM₁⟩
  rcases
      exactDivisorMPhiMassFiber_comparable_to_shape_of_fiberAverageTwoSided
        (ExactDivisorMPhiFiberAverageTwoSided_of_standard_ordinarySquarefree
          (P := P)) with
    ⟨cφ, Cφ, Xmassφ, hcφ, _hCφ, hMφ⟩
  rcases exactDivisorM1TensorFiberCoprime_le_massShape_over_modulus_of_wideModulus
      P hmargin with
    ⟨XM₁tensor, hM₁tensor⟩
  rcases exactDivisorMPhiTensorFiberCoprime_le_massShape_over_modulus_of_standard_ordinarySquarefree
      (P := P) with
    ⟨Kφ, XMφtensor, hKφ, hMφtensor⟩
  refine
    ⟨c₁, cφ, Kφ, max (max Xmass₁ Xmassφ) (max XM₁tensor XMφtensor),
      hc₁, hcφ, hKφ, ?_⟩
  intro X hX D hD_one hD_sqf hD_odd hDwide a ha
  have hXmass₁ : Xmass₁ ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXmassφ : Xmassφ ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXM₁tensor : XM₁tensor ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXMφtensor : XMφtensor ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hDpos : 0 < D := lt_of_lt_of_le Nat.zero_lt_one hD_one
  have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hM₁shape :
      exactDivisorM1TensorFiberCoprime P X D a
        ≤ (2 / (D : ℝ)) * exactDivisorM1MassShape P X :=
    hM₁tensor X hXM₁tensor D hD_one hD_sqf hDwide a
  have hMφshape :
      exactDivisorMPhiTensorFiberCoprime P X D a
        ≤ (Kφ / (D : ℝ)) * exactDivisorMPhiMassShape P X :=
    hMφtensor X hXMφtensor D hD_one hD_sqf hD_odd hDwide a ha
  have hM₁_shape_le :
      exactDivisorM1MassShape P X ≤ exactDivisorM1MassFiber P X / c₁ := by
    rw [le_div_iff₀ hc₁]
    simpa [mul_comm] using hM₁ X hXmass₁
  have hMφ_shape_le :
      exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X / cφ := by
    rw [le_div_iff₀ hcφ]
    simpa [mul_comm] using (hMφ X hXmassφ).1
  have hM₁raw :
      exactDivisorM1TensorFiberCoprime P X D a
        ≤ (2 / c₁) * (exactDivisorM1MassRaw P X / (D : ℝ)) := by
    calc
      exactDivisorM1TensorFiberCoprime P X D a
          ≤ (2 / (D : ℝ)) * exactDivisorM1MassShape P X := hM₁shape
      _ ≤ (2 / (D : ℝ)) * (exactDivisorM1MassFiber P X / c₁) := by
          exact mul_le_mul_of_nonneg_left hM₁_shape_le
            (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hD_pos.le)
      _ = (2 / c₁) * (exactDivisorM1MassRaw P X / (D : ℝ)) := by
          rw [exactDivisorM1MassRaw_eq_fiber P X]
          ring
  have hMφraw :
      exactDivisorMPhiTensorFiberCoprime P X D a
        ≤ (Kφ / cφ) * (exactDivisorMPhiMassRaw P X / (D : ℝ)) := by
    calc
      exactDivisorMPhiTensorFiberCoprime P X D a
          ≤ (Kφ / (D : ℝ)) * exactDivisorMPhiMassShape P X := hMφshape
      _ ≤ (Kφ / (D : ℝ)) * (exactDivisorMPhiMassFiber P X / cφ) := by
          exact mul_le_mul_of_nonneg_left hMφ_shape_le
            (div_nonneg hKφ.le hD_pos.le)
      _ = (Kφ / cφ) * (exactDivisorMPhiMassRaw P X / (D : ℝ)) := by
          rw [exactDivisorMPhiMassRaw_eq_fiber P X]
          ring
  exact
    ⟨exactDivisorM1MassRaw_eq_fiber P X,
      exactDivisorMPhiMassRaw_eq_fiber P X,
      hM₁raw,
      hMφraw⟩

/-- Explicit-parameter paired coprime tensor output with no exposed endpoint
margin hypothesis.

For the manuscript parameters the inequality `2η+σ<λ` is a checked numerical
fact, so the paper-facing exact-divisor tensor statement depends only on the
cited ordinary-squarefree progression inputs and on the displayed reduced-class
conditions on `D` and `a`. -/
theorem exactDivisorTensorCoprimePaperOutputs_explicit_of_standard_ordinarySquarefree_auto :
    ∃ c₁ cφ Kφ X₀ : ℝ, 0 < c₁ ∧ 0 < cφ ∧ 0 < Kφ ∧
      ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale Params.explicit X * UScale X →
        ∀ a : ℕ → ℕ,
          (∀ s ∈ exactDivisorSRange Params.explicit X, Nat.Coprime s D →
            Nat.Coprime (a s) D) →
          exactDivisorM1MassRaw Params.explicit X =
              exactDivisorM1MassFiber Params.explicit X
            ∧ exactDivisorMPhiMassRaw Params.explicit X =
              exactDivisorMPhiMassFiber Params.explicit X
            ∧ exactDivisorM1TensorFiberCoprime Params.explicit X D a
                ≤ (2 / c₁) *
                  (exactDivisorM1MassRaw Params.explicit X / (D : ℝ))
            ∧ exactDivisorMPhiTensorFiberCoprime Params.explicit X D a
                ≤ (Kφ / cφ) *
                  (exactDivisorMPhiMassRaw Params.explicit X / (D : ℝ)) := by
  letI : Fact (PhiProgressionGammaQuotientUpperYU Params.explicit) :=
    ⟨explicit_PhiProgressionGammaQuotientUpperYU_of_standard_ordinarySquarefree⟩
  exact exactDivisorTensorCoprimePaperOutputs_of_standard_ordinarySquarefree_auto
    (P := Params.explicit) explicit_two_eta_add_sigma_lt_lam

/-- Combined paper-facing long-window output for `prop:M`. -/
theorem
    ExactDivisorMass_outputs_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    PhiProgressionAverageTwoSided P ∧
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorM1MassRaw P X ∧
        exactDivisorM1MassRaw P X ≤ C * logSq X)
    ∧
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
        exactDivisorMPhiMassRaw P X ≤ C * logSq X) :=
  ⟨PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
      hlower hupper,
    exactDivisorMassRaw_quadratic_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
      hlower hupper⟩

/-- Combined long-window exact-divisor output using only wide lower and wide
upper ordinary-squarefree estimates. -/
theorem
    ExactDivisorMass_outputs_of_ordinarySquarefreeProgressionLong_wideLower_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ) :
    PhiProgressionAverageTwoSided P ∧
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorM1MassRaw P X ∧
        exactDivisorM1MassRaw P X ≤ C * logSq X)
    ∧
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
        exactDivisorMPhiMassRaw P X ≤ C * logSq X) :=
  ⟨PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgressionLong_wideLower_wideUpper_concreteOmegaTail
      hlower hupper,
    exactDivisorMassRaw_quadratic_of_ordinarySquarefreeProgressionLong_wideLower_wideUpper_concreteOmegaTail
      hlower hupper⟩

/-- Paired paper-facing output for `prop:M` and `thm:tensor-e`.

This combines the ordinary-squarefree exact-divisor mass package with the
endpoint-safe tensor package.  The progression-average hypotheses and lower
mass-comparison constants for the tensor summation remain explicit; the
raw-mass asymptotics, raw/fiber identities, and paired `1/D` tensor bounds are
all theorem-level consequences. -/
theorem
    ExactDivisorMassTensor_outputs_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.η) P.θ P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (X : ℝ) (D : ℕ) (a : ℕ → ℕ)
    (K₁ c₁ Kφ cφ : ℝ)
    (hD : 0 < D) (hK₁ : 0 ≤ K₁) (hc₁ : 0 < c₁)
    (hKφ : 0 ≤ Kφ) (hcφ : 0 < cφ)
    (hfiber₁ : ∀ s ∈ exactDivisorSRange P X,
      phiProgressionBareAverage P X D (a s) s
        ≤ K₁ * phiProgressionAverageShape P X D s)
    (hfiberφ : ∀ s ∈ exactDivisorSRange P X,
      phiProgressionAverage P X D (a s) s
        ≤ Kφ * phiProgressionAverageShape P X D s)
    (hmass₁_lower :
      c₁ * exactDivisorM1MassShape P X ≤ exactDivisorM1MassFiber P X)
    (hmassφ_lower :
      cφ * exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X) :
    (PhiProgressionAverageTwoSided P ∧
      (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        c * logSq X ≤ exactDivisorM1MassRaw P X ∧
          exactDivisorM1MassRaw P X ≤ C * logSq X)
      ∧
      (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
          exactDivisorMPhiMassRaw P X ≤ C * logSq X))
    ∧
    (exactDivisorM1MassRaw P X = exactDivisorM1MassFiber P X
      ∧ exactDivisorMPhiMassRaw P X = exactDivisorMPhiMassFiber P X
      ∧ exactDivisorM1TensorFiber P X D a
          ≤ (K₁ / c₁) * (exactDivisorM1MassRaw P X / (D : ℝ))
      ∧ exactDivisorMPhiTensorFiber P X D a
          ≤ (Kφ / cφ) * (exactDivisorMPhiMassRaw P X / (D : ℝ))) := by
  exact
    ⟨ExactDivisorMass_outputs_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
        hlower hupper,
      exactDivisorTensorPaperOutputs P X D a K₁ c₁ Kφ cφ hD hK₁ hc₁ hKφ hcφ
        hfiber₁ hfiberφ hmass₁_lower hmassφ_lower⟩

/-- Paired `prop:M`/`thm:tensor-e` output using only wide lower and wide upper
ordinary-squarefree estimates on the mass side. -/
theorem
    ExactDivisorMassTensor_outputs_of_ordinarySquarefreeProgression_wideLower_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.θ) P.θ P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (X : ℝ) (D : ℕ) (a : ℕ → ℕ)
    (K₁ c₁ Kφ cφ : ℝ)
    (hD : 0 < D) (hK₁ : 0 ≤ K₁) (hc₁ : 0 < c₁)
    (hKφ : 0 ≤ Kφ) (hcφ : 0 < cφ)
    (hfiber₁ : ∀ s ∈ exactDivisorSRange P X,
      phiProgressionBareAverage P X D (a s) s
        ≤ K₁ * phiProgressionAverageShape P X D s)
    (hfiberφ : ∀ s ∈ exactDivisorSRange P X,
      phiProgressionAverage P X D (a s) s
        ≤ Kφ * phiProgressionAverageShape P X D s)
    (hmass₁_lower :
      c₁ * exactDivisorM1MassShape P X ≤ exactDivisorM1MassFiber P X)
    (hmassφ_lower :
      cφ * exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X) :
    (PhiProgressionAverageTwoSided P ∧
      (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        c * logSq X ≤ exactDivisorM1MassRaw P X ∧
          exactDivisorM1MassRaw P X ≤ C * logSq X)
      ∧
      (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
          exactDivisorMPhiMassRaw P X ≤ C * logSq X))
    ∧
    (exactDivisorM1MassRaw P X = exactDivisorM1MassFiber P X
      ∧ exactDivisorMPhiMassRaw P X = exactDivisorMPhiMassFiber P X
      ∧ exactDivisorM1TensorFiber P X D a
          ≤ (K₁ / c₁) * (exactDivisorM1MassRaw P X / (D : ℝ))
      ∧ exactDivisorMPhiTensorFiber P X D a
          ≤ (Kφ / cφ) * (exactDivisorMPhiMassRaw P X / (D : ℝ))) := by
  exact
    ⟨ExactDivisorMass_outputs_of_ordinarySquarefreeProgression_wideLower_wideUpper_concreteOmegaTail
        hlower hupper,
      exactDivisorTensorPaperOutputs P X D a K₁ c₁ Kφ cφ hD hK₁ hc₁ hKφ hcφ
        hfiber₁ hfiberφ hmass₁_lower hmassφ_lower⟩

/-- Long-window paired paper-facing output for `prop:M` and `thm:tensor-e`. -/
theorem
    ExactDivisorMassTensor_outputs_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (X : ℝ) (D : ℕ) (a : ℕ → ℕ)
    (K₁ c₁ Kφ cφ : ℝ)
    (hD : 0 < D) (hK₁ : 0 ≤ K₁) (hc₁ : 0 < c₁)
    (hKφ : 0 ≤ Kφ) (hcφ : 0 < cφ)
    (hfiber₁ : ∀ s ∈ exactDivisorSRange P X,
      phiProgressionBareAverage P X D (a s) s
        ≤ K₁ * phiProgressionAverageShape P X D s)
    (hfiberφ : ∀ s ∈ exactDivisorSRange P X,
      phiProgressionAverage P X D (a s) s
        ≤ Kφ * phiProgressionAverageShape P X D s)
    (hmass₁_lower :
      c₁ * exactDivisorM1MassShape P X ≤ exactDivisorM1MassFiber P X)
    (hmassφ_lower :
      cφ * exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X) :
    (PhiProgressionAverageTwoSided P ∧
      (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        c * logSq X ≤ exactDivisorM1MassRaw P X ∧
          exactDivisorM1MassRaw P X ≤ C * logSq X)
      ∧
      (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
          exactDivisorMPhiMassRaw P X ≤ C * logSq X))
    ∧
    (exactDivisorM1MassRaw P X = exactDivisorM1MassFiber P X
      ∧ exactDivisorMPhiMassRaw P X = exactDivisorMPhiMassFiber P X
      ∧ exactDivisorM1TensorFiber P X D a
          ≤ (K₁ / c₁) * (exactDivisorM1MassRaw P X / (D : ℝ))
      ∧ exactDivisorMPhiTensorFiber P X D a
          ≤ (Kφ / cφ) * (exactDivisorMPhiMassRaw P X / (D : ℝ))) := by
  exact
    ⟨ExactDivisorMass_outputs_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
        hlower hupper,
      exactDivisorTensorPaperOutputs P X D a K₁ c₁ Kφ cφ hD hK₁ hc₁ hKφ hcφ
        hfiber₁ hfiberφ hmass₁_lower hmassφ_lower⟩

/-- Long-window paired `prop:M`/`thm:tensor-e` output using only wide lower and
wide upper ordinary-squarefree estimates on the mass side. -/
theorem
    ExactDivisorMassTensor_outputs_of_ordinarySquarefreeProgressionLong_wideLower_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (X : ℝ) (D : ℕ) (a : ℕ → ℕ)
    (K₁ c₁ Kφ cφ : ℝ)
    (hD : 0 < D) (hK₁ : 0 ≤ K₁) (hc₁ : 0 < c₁)
    (hKφ : 0 ≤ Kφ) (hcφ : 0 < cφ)
    (hfiber₁ : ∀ s ∈ exactDivisorSRange P X,
      phiProgressionBareAverage P X D (a s) s
        ≤ K₁ * phiProgressionAverageShape P X D s)
    (hfiberφ : ∀ s ∈ exactDivisorSRange P X,
      phiProgressionAverage P X D (a s) s
        ≤ Kφ * phiProgressionAverageShape P X D s)
    (hmass₁_lower :
      c₁ * exactDivisorM1MassShape P X ≤ exactDivisorM1MassFiber P X)
    (hmassφ_lower :
      cφ * exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X) :
    (PhiProgressionAverageTwoSided P ∧
      (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        c * logSq X ≤ exactDivisorM1MassRaw P X ∧
          exactDivisorM1MassRaw P X ≤ C * logSq X)
      ∧
      (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        c * logSq X ≤ exactDivisorMPhiMassRaw P X ∧
          exactDivisorMPhiMassRaw P X ≤ C * logSq X))
    ∧
    (exactDivisorM1MassRaw P X = exactDivisorM1MassFiber P X
      ∧ exactDivisorMPhiMassRaw P X = exactDivisorMPhiMassFiber P X
      ∧ exactDivisorM1TensorFiber P X D a
          ≤ (K₁ / c₁) * (exactDivisorM1MassRaw P X / (D : ℝ))
      ∧ exactDivisorMPhiTensorFiber P X D a
          ≤ (Kφ / cφ) * (exactDivisorMPhiMassRaw P X / (D : ℝ))) := by
  exact
    ⟨ExactDivisorMass_outputs_of_ordinarySquarefreeProgressionLong_wideLower_wideUpper_concreteOmegaTail
        hlower hupper,
      exactDivisorTensorPaperOutputs P X D a K₁ c₁ Kφ cφ hD hK₁ hc₁ hKφ hcφ
        hfiber₁ hfiberφ hmass₁_lower hmassφ_lower⟩

/-! ## A concrete quadratic mass factor for `prop:M`.

The raw exact-divisor masses above are the paper-facing `prop:M` carriers.  The
older helper below is retained as a reusable product lemma for local quadratic
factors: a squarefree conductor average times a supplied slanted-length or
progression-average carrier. -/

/-- Concrete quadratic mass carrier: squarefree conductor mass times the
slanted-length factor.  This is the checked `log X · log X` part of `prop:M`. -/
noncomputable def quadraticMassConcrete (avg slant : ℝ → ℝ) (X : ℝ) : ℝ :=
  avg X * slant X

/-- Shape identity for the quadratic mass carrier. -/
theorem logX_mul_logX_eq_logSq (X : ℝ) :
    logX X * logX X = logSq X := by
  unfold logX logSq
  ring

/-- Concrete quadratic-mass factor asymptotic from the checked squarefree
conductor average and any supplied slanted-length factor. -/
noncomputable def quadraticMass_factor_asymp
    (P : Params) (slant : ℝ → ℝ) (hslant : FactorAsymp slant logX) :
    FactorAsymp (quadraticMassConcrete (fun X => Inputs.sAvgRecip P X) slant) logSq := by
  have hprod :
      FactorAsymp
        (fun X => Inputs.sAvgRecip P X * slant X)
        (fun X => logX X * logX X) :=
    FactorAsymp.mul (sAvgRecip_asymp P) hslant
      (fun X hX => by
        have hX1 : (sAvgRecip_asymp P).X₀ ≤ X := le_trans (le_max_left _ _) hX
        unfold logX
        have hfn := (sAvgRecip_asymp P).f_nonneg X hX1
        have hhi := ((sAvgRecip_asymp P).sandwich X hX1).2
        unfold logX at hhi
        have : 0 ≤ (sAvgRecip_asymp P).C * Real.log X := le_trans hfn hhi
        have hCpos := (sAvgRecip_asymp P).C_pos
        nlinarith [this, hCpos])
      (fun X hX => by
        have hX2 : hslant.X₀ ≤ X := le_trans (le_max_right _ _) hX
        unfold logX
        have hfn := hslant.f_nonneg X hX2
        have hhi := (hslant.sandwich X hX2).2
        have : 0 ≤ hslant.C * Real.log X := le_trans hfn hhi
        have hCpos := hslant.C_pos
        nlinarith [this, hCpos])
  have hshape : (fun X => logX X * logX X) = logSq := by
    funext X
    exact logX_mul_logX_eq_logSq X
  have hfun :
      (fun X => Inputs.sAvgRecip P X * slant X)
        = quadraticMassConcrete (fun X => Inputs.sAvgRecip P X) slant := by
    funext X
    rfl
  rw [hshape, hfun] at hprod
  exact hprod

/-- Concrete quadratic-mass factor using the checked `lem:phi-progression-average`
carrier, after routing that carrier through the paper's ordinary squarefree
lower estimate and wide ordinary squarefree upper estimate.

This is the `log X · log X` mass component with the actual progression-average
factor, rather than the deterministic slanted-length surrogate. -/
noncomputable def
    quadraticMass_factor_asymp_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.η) P.θ P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    FactorAsymp
      (quadraticMassConcrete (fun X => Inputs.sAvgRecip P X)
        (fun X => phiProgressionAverage P X d a s))
      logSq :=
  quadraticMass_factor_asymp P
    (fun X => phiProgressionAverage P X d a s)
    (phiProgressionAverage_factor_asymp_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
      hlower hupper hdpos hdsqf hdodd had hs hssqf hsd)

/-- Concrete quadratic-mass factor through the wide-lower/wide-upper
ordinary-squarefree route. -/
noncomputable def
    quadraticMass_factor_asymp_of_ordinarySquarefreeProgression_wideLower_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.θ) P.θ P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    FactorAsymp
      (quadraticMassConcrete (fun X => Inputs.sAvgRecip P X)
        (fun X => phiProgressionAverage P X d a s))
      logSq :=
  quadraticMass_factor_asymp P
    (fun X => phiProgressionAverage P X d a s)
    (phiProgressionAverage_factor_asymp_of_ordinarySquarefreeProgression_wideLower_wideUpper_concreteOmegaTail
      hlower hupper hdpos hdsqf hdodd had hs hssqf hsd)

/-- Concrete quadratic-mass factor through the manuscript-aligned long-window
ordinary-squarefree route. -/
noncomputable def
    quadraticMass_factor_asymp_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    FactorAsymp
      (quadraticMassConcrete (fun X => Inputs.sAvgRecip P X)
        (fun X => phiProgressionAverage P X d a s))
      logSq :=
  quadraticMass_factor_asymp P
    (fun X => phiProgressionAverage P X d a s)
    (phiProgressionAverage_factor_asymp_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
      hlower hupper hdpos hdsqf hdodd had hs hssqf hsd)

/-- Concrete quadratic-mass factor through the wide-lower long-window
ordinary-squarefree route. -/
noncomputable def
    quadraticMass_factor_asymp_of_ordinarySquarefreeProgressionLong_wideLower_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    FactorAsymp
      (quadraticMassConcrete (fun X => Inputs.sAvgRecip P X)
        (fun X => phiProgressionAverage P X d a s))
      logSq :=
  quadraticMass_factor_asymp P
    (fun X => phiProgressionAverage P X d a s)
    (phiProgressionAverage_factor_asymp_of_ordinarySquarefreeProgressionLong_wideLower_wideUpper_concreteOmegaTail
      hlower hupper hdpos hdsqf hdodd had hs hssqf hsd)

/-- Unpacked two-sided concrete quadratic-mass theorem for the paper-route
progression-average carrier. -/
theorem quadratic_mass_from_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.η) P.θ P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X
        ≤ quadraticMassConcrete (fun X => Inputs.sAvgRecip P X)
            (fun X => phiProgressionAverage P X d a s) X
      ∧ quadraticMassConcrete (fun X => Inputs.sAvgRecip P X)
            (fun X => phiProgressionAverage P X d a s) X
        ≤ C * logSq X := by
  let hq :=
    quadraticMass_factor_asymp_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
      hlower hupper hdpos hdsqf hdodd had hs hssqf hsd
  exact ⟨hq.c, hq.C, hq.X₀, hq.c_pos, hq.C_pos, fun X hX => hq.sandwich X hX⟩

/-- Unpacked concrete quadratic-mass theorem through the wide-lower/wide-upper
ordinary-squarefree route. -/
theorem quadratic_mass_from_ordinarySquarefreeProgression_wideLower_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.θ) P.θ P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X
        ≤ quadraticMassConcrete (fun X => Inputs.sAvgRecip P X)
            (fun X => phiProgressionAverage P X d a s) X
      ∧ quadraticMassConcrete (fun X => Inputs.sAvgRecip P X)
            (fun X => phiProgressionAverage P X d a s) X
        ≤ C * logSq X := by
  let hq :=
    quadraticMass_factor_asymp_of_ordinarySquarefreeProgression_wideLower_wideUpper_concreteOmegaTail
      hlower hupper hdpos hdsqf hdodd had hs hssqf hsd
  exact ⟨hq.c, hq.C, hq.X₀, hq.c_pos, hq.C_pos, fun X hX => hq.sandwich X hX⟩

/-- Unpacked two-sided concrete quadratic-mass theorem through the
manuscript-aligned long-window route. -/
theorem quadratic_mass_from_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X
        ≤ quadraticMassConcrete (fun X => Inputs.sAvgRecip P X)
            (fun X => phiProgressionAverage P X d a s) X
      ∧ quadraticMassConcrete (fun X => Inputs.sAvgRecip P X)
            (fun X => phiProgressionAverage P X d a s) X
        ≤ C * logSq X := by
  let hq :=
    quadraticMass_factor_asymp_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
      hlower hupper hdpos hdsqf hdodd had hs hssqf hsd
  exact ⟨hq.c, hq.C, hq.X₀, hq.c_pos, hq.C_pos, fun X hX => hq.sandwich X hX⟩

/-- Unpacked concrete quadratic-mass theorem through the wide-lower
long-window ordinary-squarefree route. -/
theorem quadratic_mass_from_ordinarySquarefreeProgressionLong_wideLower_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X
        ≤ quadraticMassConcrete (fun X => Inputs.sAvgRecip P X)
            (fun X => phiProgressionAverage P X d a s) X
      ∧ quadraticMassConcrete (fun X => Inputs.sAvgRecip P X)
            (fun X => phiProgressionAverage P X d a s) X
        ≤ C * logSq X := by
  let hq :=
    quadraticMass_factor_asymp_of_ordinarySquarefreeProgressionLong_wideLower_wideUpper_concreteOmegaTail
      hlower hupper hdpos hdsqf hdodd had hs hssqf hsd
  exact ⟨hq.c, hq.C, hq.X₀, hq.c_pos, hq.C_pos, fun X hX => hq.sandwich X hX⟩

/-- Combined paper-facing output for the `prop:M` quadratic-mass route.

The same ordinary-squarefree lower estimate and wide ordinary-squarefree upper
estimate that prove `lem:phi-progression-average` also supply the quadratic
`log X · log X` mass factor used in `prop:M`, with the actual
`phiProgressionAverage` carrier rather than the deterministic slant surrogate.

This is not the full exact-divisor identity for `M₁` or `M_φ`; it is the checked
progression-average-to-quadratic-mass bridge that the full identity must feed. -/
noncomputable def
    QuadraticMass_outputs_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.η) P.θ P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    (Σ' _h : PhiProgressionAverageTwoSided P,
      FactorAsymp
        (quadraticMassConcrete (fun X => Inputs.sAvgRecip P X)
          (fun X => phiProgressionAverage P X d a s))
        logSq) :=
  ⟨PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
      hlower hupper,
    quadraticMass_factor_asymp_of_ordinarySquarefreeProgression_wideUpper_concreteOmegaTail
      hlower hupper hdpos hdsqf hdodd had hs hssqf hsd⟩

/-- Combined quadratic-mass output through the wide-lower/wide-upper route. -/
noncomputable def
    QuadraticMass_outputs_of_ordinarySquarefreeProgression_wideLower_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLower
        (P.lam - P.θ) P.θ P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    (Σ' _h : PhiProgressionAverageTwoSided P,
      FactorAsymp
        (quadraticMassConcrete (fun X => Inputs.sAvgRecip P X)
          (fun X => phiProgressionAverage P X d a s))
        logSq) :=
  ⟨PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgression_wideLower_wideUpper_concreteOmegaTail
      hlower hupper,
    quadraticMass_factor_asymp_of_ordinarySquarefreeProgression_wideLower_wideUpper_concreteOmegaTail
      hlower hupper hdpos hdsqf hdodd had hs hssqf hsd⟩

/-- Fixed-parameter quadratic-mass `FactorAsymp` with the ordinary-squarefree
hypotheses discharged by the cited standard input. -/
noncomputable def quadraticMass_factor_asymp_of_standard_ordinarySquarefree
    {P : Params} [Fact (PhiProgressionGammaQuotientUpperYU P)]
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    FactorAsymp
      (quadraticMassConcrete (fun X => Inputs.sAvgRecip P X)
        (fun X => phiProgressionAverage P X d a s))
      logSq :=
  quadraticMass_factor_asymp P
    (fun X => phiProgressionAverage P X d a s)
    (phiProgressionAverage_factor_asymp_of_standard_ordinarySquarefree
      hdpos hdsqf hdodd had hs hssqf hsd)

/-- Combined quadratic-mass output with the ordinary-squarefree hypotheses
reduced to the cited standard input. -/
noncomputable def QuadraticMass_outputs_of_standard_ordinarySquarefree
    {P : Params} [Fact (PhiProgressionGammaQuotientUpperYU P)]
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    (Σ' _h : PhiProgressionAverageTwoSided P,
      FactorAsymp
        (quadraticMassConcrete (fun X => Inputs.sAvgRecip P X)
          (fun X => phiProgressionAverage P X d a s))
        logSq) :=
  ⟨PhiProgressionAverageTwoSided_of_standard_ordinarySquarefree (P := P),
    quadraticMass_factor_asymp_of_standard_ordinarySquarefree
      hdpos hdsqf hdodd had hs hssqf hsd⟩

/-- Combined paper-facing long-window output for the `prop:M` quadratic-mass
route. -/
noncomputable def
    QuadraticMass_outputs_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    (Σ' _h : PhiProgressionAverageTwoSided P,
      FactorAsymp
        (quadraticMassConcrete (fun X => Inputs.sAvgRecip P X)
          (fun X => phiProgressionAverage P X d a s))
        logSq) :=
  ⟨PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
      hlower hupper,
    quadraticMass_factor_asymp_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
      hlower hupper hdpos hdsqf hdodd had hs hssqf hsd⟩

/-- Combined quadratic-mass output through the wide-lower long-window route. -/
noncomputable def
    QuadraticMass_outputs_of_ordinarySquarefreeProgressionLong_wideLower_wideUpper_concreteOmegaTail
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    {d a s : ℕ} (hdpos : 0 < d) (hdsqf : Squarefree d) (hdodd : Odd d)
    (had : Nat.Coprime a d) (hs : 1 ≤ s) (hssqf : Squarefree s)
    (hsd : Nat.Coprime s d) :
    (Σ' _h : PhiProgressionAverageTwoSided P,
      FactorAsymp
        (quadraticMassConcrete (fun X => Inputs.sAvgRecip P X)
          (fun X => phiProgressionAverage P X d a s))
        logSq) :=
  ⟨PhiProgressionAverageTwoSided_of_ordinarySquarefreeProgressionLong_wideLower_wideUpper_concreteOmegaTail
      hlower hupper,
    quadraticMass_factor_asymp_of_ordinarySquarefreeProgressionLong_wideLower_wideUpper_concreteOmegaTail
      hlower hupper hdpos hdsqf hdodd had hs hssqf hsd⟩

/-- Concrete `prop:M`-shaped quadratic mass theorem with a fixed checked slant.

This closes the `log X · log X` part of the quadratic mass from actual carriers:
`Inputs.sAvgRecip P` and `slantLogLength P s`.  It still does not prove the full
exact-divisor `M₁/M_φ` identities or tensorisation. -/
theorem quadratic_mass_from_inputs_fixed_slant
    (P : Params) (s : ℕ) (hs : 1 ≤ s) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X
        ≤ quadraticMassConcrete (fun X => Inputs.sAvgRecip P X)
            (fun X => slantLogLength P s X) X
      ∧ quadraticMassConcrete (fun X => Inputs.sAvgRecip P X)
            (fun X => slantLogLength P s X) X
        ≤ C * logSq X := by
  let hq :=
    quadraticMass_factor_asymp P (fun X => slantLogLength P s X)
      (slantLogLength_factor_asymp P s hs)
  exact ⟨hq.c, hq.C, hq.X₀, hq.c_pos, hq.C_pos, fun X hX => hq.sandwich X hX⟩

/-- The small-divisor Euler carrier as a `FactorAsymp` to `log z`, once its
standard Mertens/Euler-product lower bound is supplied.

The upper half is now proved in `Inputs.smallDivisorEulerSum_upper_unconditional`
from the harmonic envelope.  Thus the remaining hypothesis is only the arithmetic
lower growth of the explicit finite carrier, not an arbitrary `divLogZ`
asymptotic datum. -/
noncomputable def smallDivisorEulerSum_factor_asymp
    (cE XE : ℝ) (hcE : 0 < cE)
    (hE : ∀ X : ℝ, XE ≤ X →
      cE * logZ X ≤ Inputs.smallDivisorEulerSum X) :
    FactorAsymp (fun X => Inputs.smallDivisorEulerSum X) logZ where
  c := cE
  C := (Inputs.smallDivisorEulerSum_upper_unconditional).choose
  X₀ := max XE (Inputs.smallDivisorEulerSum_upper_unconditional).choose_spec.choose
  c_pos := hcE
  C_pos := (Inputs.smallDivisorEulerSum_upper_unconditional).choose_spec.choose_spec.1
  f_nonneg := fun X _ => Inputs.smallDivisorEulerSum_nonneg X
  sandwich := fun X hX => by
    have hXE : XE ≤ X := le_trans (le_max_left _ _) hX
    have hXU :
        (Inputs.smallDivisorEulerSum_upper_unconditional).choose_spec.choose ≤ X :=
      le_trans (le_max_right _ _) hX
    exact ⟨hE X hXE,
      (Inputs.smallDivisorEulerSum_upper_unconditional).choose_spec.choose_spec.2 X hXU⟩

/-- The already-interchanged finite small-divisor average carrier satisfies
`smallDivisorAverage P X ≍ log X · log z` from any supplied lower bound of the
natural shape `log S · log z` and the unconditional upper bound in `Inputs`.

This is stated existentially because its constants come from existential
analytic bounds; downstream Prop-valued theorems can unpack it and reuse the
resulting `FactorAsymp` datum. -/
theorem smallDivisorAverage_factor_asymp_of_lower_bound
    (P : Params)
    (hlower :
      ∃ cA Xlo : ℝ, 0 < cA ∧ ∀ X : ℝ, Xlo ≤ X →
        cA * Real.log (SScale P X) * Real.log (zScale X) ≤
          Inputs.smallDivisorAverage P X) :
    ∃ _h : FactorAsymp
        (fun X => Inputs.smallDivisorAverage P X)
        (fun X => logX X * logZ X), True := by
  rcases hlower with ⟨cA, Xlo, hcA, hlo⟩
  rcases Inputs.smallDivisorAverage_upper_unconditional P with
    ⟨CA, Xhi, hCA, hhi⟩
  refine ⟨?_, trivial⟩
  exact
    { c := cA * P.η
      C := CA * P.η
      X₀ := max (max Xlo Xhi) 1
      c_pos := mul_pos hcA P.η_pos
      C_pos := mul_pos hCA P.η_pos
      f_nonneg := fun X _ => Inputs.smallDivisorAverage_nonneg P X
      sandwich := fun X hX => by
        have hXlo : Xlo ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
        have hXhi : Xhi ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
        have hXone : (1 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
        have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
        have hlogS : Real.log (SScale P X) = P.η * Real.log X := log_SScale P hXpos
        refine ⟨?_, ?_⟩
        · calc
            (cA * P.η) * (logX X * logZ X)
                = cA * Real.log (SScale P X) * Real.log (zScale X) := by
                  unfold logX logZ
                  rw [hlogS]
                  ring
            _ ≤ Inputs.smallDivisorAverage P X := hlo X hXlo
        · calc
            Inputs.smallDivisorAverage P X
                ≤ CA * Real.log (SScale P X) * Real.log (zScale X) := hhi X hXhi
            _ = (CA * P.η) * (logX X * logZ X) := by
                  unfold logX logZ
                  rw [hlogS]
                  ring }

/-- The standard-input specialization of
`smallDivisorAverage_factor_asymp_of_lower_bound`. -/
theorem smallDivisorAverage_factor_asymp_standard (P : Params) :
    ∃ _h : FactorAsymp
        (fun X => Inputs.smallDivisorAverage P X)
        (fun X => logX X * logZ X), True :=
  smallDivisorAverage_factor_asymp_of_lower_bound P
    (Inputs.smallDivisorAverage_lower_from_standard_inputs P)

/-- Conditional exact-density specialization of the finite small-divisor average
asymptotic.

The explicit density hypothesis replaces the named finite-witness Euler input;
the upper bound and the conversion from `log S` to `log X` remain checked here. -/
theorem smallDivisorAverage_factor_asymp_of_oddSquarefreeTotientNat_recip_density
    (P : Params)
    (hdensity : ∃ δ > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      δ * Inputs.oddSquarefreeRecipNat (2 ^ k)
        ≤ Inputs.oddSquarefreeTotientNat (2 ^ k)) :
    ∃ _h : FactorAsymp
        (fun X => Inputs.smallDivisorAverage P X)
        (fun X => logX X * logZ X), True :=
  smallDivisorAverage_factor_asymp_of_lower_bound P
    (Inputs.smallDivisorAverage_lower_from_oddSquarefreeTotientNat_recip_density
      P hdensity)

/-- Finite small-divisor average factor from the defect-gap form of the
small-side replacement. -/
theorem smallDivisorAverage_factor_asymp_of_defectGap
    (P : Params) (h : Inputs.OddSquarefreeTotientDefectGapBound) :
    ∃ _h : FactorAsymp
        (fun X => Inputs.smallDivisorAverage P X)
        (fun X => logX X * logZ X), True :=
  smallDivisorAverage_factor_asymp_of_oddSquarefreeTotientNat_recip_density P
    (Inputs.OddSquarefreeTotientDensityBound_of_defectGap h)

/-- Finite small-divisor average factor from the product-lower form of the
small-side replacement. -/
theorem smallDivisorAverage_factor_asymp_of_productLowerBound
    (P : Params) (h : Inputs.OddSquarefreeTotientProductDyadicLowerBound) :
    ∃ _h : FactorAsymp
        (fun X => Inputs.smallDivisorAverage P X)
        (fun X => logX X * logZ X), True :=
  smallDivisorAverage_factor_asymp_of_oddSquarefreeTotientNat_recip_density P
    (Inputs.OddSquarefreeTotientDensityBound_of_productLowerBound h)

/-- Finite small-divisor average factor from the product-defect-gap form of the
small-side replacement. -/
theorem smallDivisorAverage_factor_asymp_of_defectProductGap
    (P : Params) (h : Inputs.OddSquarefreeTotientDefectProductGapBound) :
    ∃ _h : FactorAsymp
        (fun X => Inputs.smallDivisorAverage P X)
        (fun X => logX X * logZ X), True :=
  smallDivisorAverage_factor_asymp_of_oddSquarefreeTotientNat_recip_density P
    (Inputs.OddSquarefreeTotientDensityBound_of_defectProductGap h)

/-! ## Shape algebra: `logX · logX · logZ = sigmaShape`.

`sigmaShape X = (log X)² · log z`, and our concrete `Σ_b` is built as the product
of the three constituent factors with shapes `logX`, `logX`, `logZ`.  We check the
shape identity so the assembled `FactorAsymp` lands on `sigmaShape` exactly. -/

/-- `(logX X) * (logX X * logZ X) = sigmaShape X`.  (Associated so it matches the
product `sAvg · (slant · divLogZ)` built below.) -/
theorem logX_mul_logX_mul_logZ (X : ℝ) :
    logX X * (logX X * logZ X) = sigmaShape X := by
  unfold logX logZ sigmaShape
  ring

/-! ## The concrete small-prime saturation average `Σ_b`.

We encode `Σ_b` as the product of its three constituent factor-functions, in the
manuscript's grouping `Σ_b ≍ (log S) · ((inner r-length) · (A_s-divisor)) ≍
log X · (log X · log z)` (tex 1559–1578):

* `sAvg`     — the cited squarefree-conductor average `≍ log X`
              (`Inputs.sAvgRecip P`, discharged by `sAvgRecip_asymp`);
* `slant`    — the inner reduced `r`-progression length `≍ log X`
              (`lem:phi-progression-average`, intermediate hypothesis);
* `divLogZ`  — the odd-divisor `A_s`-average `≍ log z`
              (`lem:small-divisor-average`, intermediate hypothesis).

`sigmaSmallConcrete = sAvg · (slant · divLogZ)`. -/

/-- The concrete small-prime saturation average `Σ_b`, as the product of its three
constituent factor-functions (`lem:small-saturation-average`, tex 1542–1578,
factored per the proof at 1559–1578). -/
noncomputable def sigmaSmallConcrete (sAvg slant divLogZ : ℝ → ℝ) (X : ℝ) : ℝ :=
  sAvg X * (slant X * divLogZ X)

/-- Alternative concrete small-prime saturation average using the already
interchanged finite carrier `Inputs.smallDivisorAverage P` for
`∑_{s≤S,sqf} A_s/s`, instead of keeping its `sAvg · divLogZ` proof factors
separate. -/
noncomputable def sigmaSmallAverageConcrete (slant avg : ℝ → ℝ) (X : ℝ) : ℝ :=
  slant X * avg X

/-- The actual finite small-divisor average carrier, multiplied by the checked
fixed slanted length, has the `Σ_b` shape `(log X)^2 log z`.

This names the algebra used by both the mass-law and event-tensor wrappers for
the carrier `slantLogLength P s · Inputs.smallDivisorAverage P`, so the finite
small-divisor average no longer has to be rebuilt locally in each endpoint. -/
noncomputable def sigmaSmallAverage_factor_asymp_standard
    (P : Params) (s : ℕ) (hs : 1 ≤ s) :
    FactorAsymp
      (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
        (fun X => Inputs.smallDivisorAverage P X))
      sigmaShape := by
  let hAvg := Classical.choose (smallDivisorAverage_factor_asymp_standard P)
  have hslant : FactorAsymp (fun X => slantLogLength P s X) logX :=
    slantLogLength_factor_asymp P s hs
  have hprod :
      FactorAsymp
        (fun X => slantLogLength P s X * Inputs.smallDivisorAverage P X)
        (fun X => logX X * (logX X * logZ X)) :=
    FactorAsymp.mul hslant hAvg
      (fun X hX => by
        have hX1 : hslant.X₀ ≤ X := le_trans (le_max_left _ _) hX
        unfold logX
        have hfn := hslant.f_nonneg X hX1
        have hhi' := (hslant.sandwich X hX1).2
        have : 0 ≤ hslant.C * Real.log X := le_trans hfn hhi'
        nlinarith [this, hslant.C_pos])
      (fun X hX => by
        have hX2 : hAvg.X₀ ≤ X := le_trans (le_max_right _ _) hX
        have hfn := hAvg.f_nonneg X hX2
        have hhi' := (hAvg.sandwich X hX2).2
        have : 0 ≤ hAvg.C * (logX X * logZ X) := le_trans hfn hhi'
        have hAvgShape : 0 ≤ logX X * logZ X :=
          (mul_nonneg_iff_of_pos_left hAvg.C_pos).mp this
        simpa using hAvgShape)
  have hshape : (fun X => logX X * (logX X * logZ X)) = sigmaShape := by
    funext X
    exact logX_mul_logX_mul_logZ X
  have hfun :
      (fun X => slantLogLength P s X * Inputs.smallDivisorAverage P X)
        =
      sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
        (fun X => Inputs.smallDivisorAverage P X) := by
    funext X
    rfl
  rw [hshape, hfun] at hprod
  exact hprod

/-- Unpacked paper-facing form of `lem:small-saturation-average` for the
already-interchanged finite small-divisor average carrier.

The `FactorAsymp` data in `sigmaSmallAverage_factor_asymp_standard` is converted
to the explicit two-sided constants used in the manuscript statement
`Σ_b ≍ (log X)^2 log z`. -/
theorem sigmaSmallAverage_from_inputs_fixed_slant_smallDivisorAverage_standard
    (P : Params) (s : ℕ) (hs : 1 ≤ s) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * sigmaShape X
        ≤ sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
            (fun X => Inputs.smallDivisorAverage P X) X
      ∧ sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
            (fun X => Inputs.smallDivisorAverage P X) X
        ≤ C * sigmaShape X := by
  let hSigma := sigmaSmallAverage_factor_asymp_standard P s hs
  exact ⟨hSigma.c, hSigma.C, hSigma.X₀, hSigma.c_pos, hSigma.C_pos,
    fun X hX => hSigma.sandwich X hX⟩

/-- Conditional exact-density version of
`sigmaSmallAverage_factor_asymp_standard`.

This keeps the small-divisor density input explicit while preserving the same
finite carrier `slantLogLength P s · smallDivisorAverage P`. -/
noncomputable def sigmaSmallAverage_factor_asymp_of_oddSquarefreeTotientNat_recip_density
    (P : Params) (s : ℕ) (hs : 1 ≤ s)
    (hdensity : ∃ δ > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      δ * Inputs.oddSquarefreeRecipNat (2 ^ k)
        ≤ Inputs.oddSquarefreeTotientNat (2 ^ k)) :
    FactorAsymp
      (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
        (fun X => Inputs.smallDivisorAverage P X))
      sigmaShape := by
  let hAvg :=
    Classical.choose
      (smallDivisorAverage_factor_asymp_of_oddSquarefreeTotientNat_recip_density
        P hdensity)
  have hslant : FactorAsymp (fun X => slantLogLength P s X) logX :=
    slantLogLength_factor_asymp P s hs
  have hprod :
      FactorAsymp
        (fun X => slantLogLength P s X * Inputs.smallDivisorAverage P X)
        (fun X => logX X * (logX X * logZ X)) :=
    FactorAsymp.mul hslant hAvg
      (fun X hX => by
        have hX1 : hslant.X₀ ≤ X := le_trans (le_max_left _ _) hX
        unfold logX
        have hfn := hslant.f_nonneg X hX1
        have hhi' := (hslant.sandwich X hX1).2
        have : 0 ≤ hslant.C * Real.log X := le_trans hfn hhi'
        nlinarith [this, hslant.C_pos])
      (fun X hX => by
        have hX2 : hAvg.X₀ ≤ X := le_trans (le_max_right _ _) hX
        have hfn := hAvg.f_nonneg X hX2
        have hhi' := (hAvg.sandwich X hX2).2
        have : 0 ≤ hAvg.C * (logX X * logZ X) := le_trans hfn hhi'
        have hAvgShape : 0 ≤ logX X * logZ X :=
          (mul_nonneg_iff_of_pos_left hAvg.C_pos).mp this
        simpa using hAvgShape)
  have hshape : (fun X => logX X * (logX X * logZ X)) = sigmaShape := by
    funext X
    exact logX_mul_logX_mul_logZ X
  have hfun :
      (fun X => slantLogLength P s X * Inputs.smallDivisorAverage P X)
        =
      sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
        (fun X => Inputs.smallDivisorAverage P X) := by
    funext X
    rfl
  rw [hshape, hfun] at hprod
  exact hprod

/-- Sigma-side factor from the defect-gap form of the small-side replacement. -/
noncomputable def sigmaSmallAverage_factor_asymp_of_defectGap
    (P : Params) (s : ℕ) (hs : 1 ≤ s)
    (h : Inputs.OddSquarefreeTotientDefectGapBound) :
    FactorAsymp
      (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
        (fun X => Inputs.smallDivisorAverage P X))
      sigmaShape :=
  sigmaSmallAverage_factor_asymp_of_oddSquarefreeTotientNat_recip_density
    P s hs (Inputs.OddSquarefreeTotientDensityBound_of_defectGap h)

/-- Sigma-side factor from the product-lower form of the small-side
replacement. -/
noncomputable def sigmaSmallAverage_factor_asymp_of_productLowerBound
    (P : Params) (s : ℕ) (hs : 1 ≤ s)
    (h : Inputs.OddSquarefreeTotientProductDyadicLowerBound) :
    FactorAsymp
      (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
        (fun X => Inputs.smallDivisorAverage P X))
      sigmaShape :=
  sigmaSmallAverage_factor_asymp_of_oddSquarefreeTotientNat_recip_density
    P s hs (Inputs.OddSquarefreeTotientDensityBound_of_productLowerBound h)

/-- Sigma-side factor from the product-defect-gap form of the small-side
replacement. -/
noncomputable def sigmaSmallAverage_factor_asymp_of_defectProductGap
    (P : Params) (s : ℕ) (hs : 1 ≤ s)
    (h : Inputs.OddSquarefreeTotientDefectProductGapBound) :
    FactorAsymp
      (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
        (fun X => Inputs.smallDivisorAverage P X))
      sigmaShape :=
  sigmaSmallAverage_factor_asymp_of_oddSquarefreeTotientNat_recip_density
    P s hs (Inputs.OddSquarefreeTotientDensityBound_of_defectProductGap h)

/-- Mertens-free fallback for the actual finite small-divisor average contribution
to `Σ_b`.

The `d = 1` slice in `Inputs.smallDivisorAverage_mertensFree_with_carrier_bounds`
gives only the lower shape `(log X)^2` after multiplication by the checked
slanted length. The harmonic upper bound still gives the full `sigmaShape`
upper. Thus this theorem isolates exactly the missing arithmetic content in the
standard `Σ_b` factor: the extra lower `log z` gain. -/
theorem sigmaSmallAverage_mertensFree_with_carrier_bounds
    (P : Params) (s : ℕ) (hs : 1 ≤ s) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      0 ≤ logX X ∧
        0 ≤ logZ X ∧
        0 ≤ sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X) X ∧
        c * logSq X ≤
          sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
            (fun X => Inputs.smallDivisorAverage P X) X ∧
        sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
            (fun X => Inputs.smallDivisorAverage P X) X
          ≤ C * sigmaShape X ∧
        |sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
            (fun X => Inputs.smallDivisorAverage P X) X|
          ≤ C * sigmaShape X := by
  let hslant := slantLogLength_factor_asymp P s hs
  rcases Inputs.smallDivisorAverage_mertensFree_with_carrier_bounds P with
    ⟨cA, CA, XA, hcA, hCA, hAvg⟩
  refine ⟨hslant.c * cA * P.η, hslant.C * CA * P.η,
    max (max hslant.X₀ XA) (Real.exp (Real.exp 1)),
    mul_pos (mul_pos hslant.c_pos hcA) P.η_pos,
    mul_pos (mul_pos hslant.C_pos hCA) P.η_pos, ?_⟩
  intro X hX
  have hXslant : hslant.X₀ ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXA : XA ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXexp2 : Real.exp (Real.exp 1) ≤ X :=
    le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hXexp2
  have hXone : (1 : ℝ) ≤ X :=
    le_trans (by
      calc
        (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
        _ ≤ Real.exp (Real.exp 1) := Real.exp_le_exp.mpr (Real.exp_pos 1).le) hXexp2
  have hlogX_nonneg : 0 ≤ logX X := by
    unfold logX
    exact Real.log_nonneg hXone
  have hlogS_eq : Real.log (SScale P X) = P.η * logX X := by
    simpa [logX] using log_SScale P hXpos
  obtain ⟨_hlogS_nonneg, hlogZ_nonneg, hAvg_nonneg,
    hAvg_lower, hAvg_upper, _hAvg_abs⟩ := hAvg X hXA
  have hslant_nonneg : 0 ≤ slantLogLength P s X :=
    hslant.f_nonneg X hXslant
  obtain ⟨hslant_lower, hslant_upper⟩ := hslant.sandwich X hXslant
  have hAvg_lower_logX :
      cA * P.η * logX X ≤ Inputs.smallDivisorAverage P X := by
    calc
      cA * P.η * logX X = cA * Real.log (SScale P X) := by
        rw [hlogS_eq]
        ring
      _ ≤ Inputs.smallDivisorAverage P X := hAvg_lower
  have hAvg_upper_logX :
      Inputs.smallDivisorAverage P X ≤ CA * P.η * logX X * logZ X := by
    calc
      Inputs.smallDivisorAverage P X
          ≤ CA * Real.log (SScale P X) * Real.log (zScale X) := hAvg_upper
      _ = CA * P.η * logX X * logZ X := by
            rw [hlogS_eq]
            unfold logZ
            ring
  have hupper_shape_nonneg : 0 ≤ hslant.C * logX X :=
    mul_nonneg hslant.C_pos.le hlogX_nonneg
  have hSig_nonneg :
      0 ≤ sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
        (fun X => Inputs.smallDivisorAverage P X) X := by
    unfold sigmaSmallAverageConcrete
    exact mul_nonneg hslant_nonneg hAvg_nonneg
  have hSig_lower :
      (hslant.c * cA * P.η) * logSq X ≤
        sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X) X := by
    unfold sigmaSmallAverageConcrete
    calc
      (hslant.c * cA * P.η) * logSq X
          = (hslant.c * logX X) * (cA * P.η * logX X) := by
              unfold logSq logX
              ring
      _ ≤ slantLogLength P s X * Inputs.smallDivisorAverage P X :=
          mul_le_mul hslant_lower hAvg_lower_logX
            (mul_nonneg (mul_nonneg hcA.le P.η_pos.le) hlogX_nonneg)
            hslant_nonneg
  have hSig_upper :
      sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X) X
        ≤ (hslant.C * CA * P.η) * sigmaShape X := by
    unfold sigmaSmallAverageConcrete
    calc
      slantLogLength P s X * Inputs.smallDivisorAverage P X
          ≤ (hslant.C * logX X) * (CA * P.η * logX X * logZ X) :=
          mul_le_mul hslant_upper hAvg_upper_logX hAvg_nonneg hupper_shape_nonneg
      _ = (hslant.C * CA * P.η) * sigmaShape X := by
            unfold sigmaShape logX logZ
            ring
  exact ⟨hlogX_nonneg, hlogZ_nonneg, hSig_nonneg, hSig_lower, hSig_upper, by
    rw [abs_of_nonneg hSig_nonneg]
    exact hSig_upper⟩

/-- Bare lower/upper bounds for the Mertens-free `Σ_b` fallback give the
carrier-bundled package after adding the checked log and absolute-value side
conditions. -/
theorem sigmaSmallAverage_mertensFree_with_carrier_bounds_of_bounds
    (P : Params) (s : ℕ) (hs : 1 ≤ s)
    (h :
      ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        c * logSq X ≤
          sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
            (fun X => Inputs.smallDivisorAverage P X) X ∧
        sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
            (fun X => Inputs.smallDivisorAverage P X) X
          ≤ C * sigmaShape X) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      0 ≤ logX X ∧
        0 ≤ logZ X ∧
        0 ≤ sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X) X ∧
        c * logSq X ≤
          sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
            (fun X => Inputs.smallDivisorAverage P X) X ∧
        sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
            (fun X => Inputs.smallDivisorAverage P X) X
          ≤ C * sigmaShape X ∧
        |sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
            (fun X => Inputs.smallDivisorAverage P X) X|
          ≤ C * sigmaShape X := by
  rcases h with ⟨c, C, Xbase, hc, hC, hbounds⟩
  let hslant := slantLogLength_factor_asymp P s hs
  refine ⟨c, C, max (max Xbase hslant.X₀) (Real.exp 2), hc, hC, ?_⟩
  intro X hX
  have hXbase : Xbase ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXslant : hslant.X₀ ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXexp2 : Real.exp 2 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : (1 : ℝ) ≤ X := by
    have hExpOne : (1 : ℝ) ≤ Real.exp 2 := by
      calc
        (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
        _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 2)
    exact le_trans hExpOne hXexp2
  have hlogX_nonneg : 0 ≤ logX X := by
    unfold logX
    exact Real.log_nonneg hXone
  have hlogZ_nonneg : 0 ≤ logZ X := by
    unfold logZ
    exact (Inputs.log_zScale_pos_of_exp_two_le hXexp2).le
  have hSig_nonneg :
      0 ≤ sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
        (fun X => Inputs.smallDivisorAverage P X) X := by
    unfold sigmaSmallAverageConcrete
    exact mul_nonneg (hslant.f_nonneg X hXslant)
      (Inputs.smallDivisorAverage_nonneg P X)
  rcases hbounds X hXbase with ⟨hlower, hupper⟩
  exact ⟨hlogX_nonneg, hlogZ_nonneg, hSig_nonneg, hlower, hupper, by
    rw [abs_of_nonneg hSig_nonneg]
    exact hupper⟩

/-- Forget the checked side conditions from the bundled Mertens-free `Σ_b`
fallback. -/
theorem sigmaSmallAverage_mertensFree_bounds_of_carrier_bounds
    (P : Params) (s : ℕ) (_hs : 1 ≤ s)
    (h :
      ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        0 ≤ logX X ∧
          0 ≤ logZ X ∧
          0 ≤ sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
            (fun X => Inputs.smallDivisorAverage P X) X ∧
          c * logSq X ≤
            sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
              (fun X => Inputs.smallDivisorAverage P X) X ∧
          sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
              (fun X => Inputs.smallDivisorAverage P X) X
            ≤ C * sigmaShape X ∧
          |sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
              (fun X => Inputs.smallDivisorAverage P X) X|
            ≤ C * sigmaShape X) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤
        sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X) X ∧
      sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X) X
        ≤ C * sigmaShape X := by
  rcases h with ⟨c, C, X₀, hc, hC, hcarrier⟩
  refine ⟨c, C, X₀, hc, hC, ?_⟩
  intro X hX
  have hcarr := hcarrier X hX
  exact ⟨hcarr.2.2.2.1, hcarr.2.2.2.2.1⟩

/-- Bare lower/upper bounds and the carrier-bundled Mertens-free `Σ_b` fallback
have the same analytic content. -/
theorem sigmaSmallAverage_mertensFree_bounds_iff_carrier_bounds
    (P : Params) (s : ℕ) (hs : 1 ≤ s) :
    (∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * logSq X ≤
        sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X) X ∧
      sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X) X
        ≤ C * sigmaShape X) ↔
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      0 ≤ logX X ∧
        0 ≤ logZ X ∧
        0 ≤ sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X) X ∧
        c * logSq X ≤
          sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
            (fun X => Inputs.smallDivisorAverage P X) X ∧
        sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
            (fun X => Inputs.smallDivisorAverage P X) X
          ≤ C * sigmaShape X ∧
        |sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
            (fun X => Inputs.smallDivisorAverage P X) X|
          ≤ C * sigmaShape X := by
  constructor
  · exact sigmaSmallAverage_mertensFree_with_carrier_bounds_of_bounds P s hs
  · exact sigmaSmallAverage_mertensFree_bounds_of_carrier_bounds P s hs

/-- **The small-prime saturation average as a `FactorAsymp` to `sigmaShape`**
(`lem:small-saturation-average`, tex 1542–1578), analogous to
`MassTensor.roughFactor_asymp`.

The cited `log S ≍ log X` factor (`sAvg = Inputs.sAvgRecip P`) is discharged to
`Inputs.s_average_recip` via `sAvgRecip_asymp`; the inner `r`-progression length
`slant ≍ log X` (`lem:phi-progression-average`) and the odd-divisor `A_s`-average
`divLogZ ≍ log z` (`lem:small-divisor-average`) are threaded as the explicit
intermediate hypotheses `hslant`, `hdiv`.

The output shape is exactly `sigmaShape = (log X)² · log z`, by the shape
identity `logX · (logX · logZ) = sigmaShape`, so this datum feeds directly into
`MassTensor.mass_law`'s `hSig` slot.

The sign facts `0 ≤ log X`, `0 ≤ log z` needed by the product combinator are
derived *internally* from the threaded factor-asymptotics themselves (a nonneg
sum bounded above by `C · shape` forces `0 ≤ shape`), so no extra sign hypothesis
is required. -/
noncomputable def sigmaFactor_asymp (P : Params)
    (slant divLogZ : ℝ → ℝ)
    (hslant : FactorAsymp slant logX)
    (hdiv : FactorAsymp divLogZ logZ) :
    FactorAsymp (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ) sigmaShape := by
  -- Build the inner product `FactorAsymp (slant · divLogZ) (logX · logZ)`.
  have hinner :
      FactorAsymp (fun X => slant X * divLogZ X) (fun X => logX X * logZ X) :=
    FactorAsymp.mul hslant hdiv
      (fun X hX => by
        -- need 0 ≤ logX X for X ≥ max hslant.X₀ hdiv.X₀
        -- derive from `slant ≍ logX`: slant ≥ 0 and slant ≤ C·logX ⟹ 0 ≤ logX.
        have hX1 : hslant.X₀ ≤ X := le_trans (le_max_left _ _) hX
        unfold logX
        have hfn := hslant.f_nonneg X hX1
        have hhi := (hslant.sandwich X hX1).2
        have : 0 ≤ hslant.C * Real.log X := le_trans hfn hhi
        have hCpos := hslant.C_pos
        nlinarith [this, hCpos])
      (fun X hX => by
        have hX2 : hdiv.X₀ ≤ X := le_trans (le_max_right _ _) hX
        unfold logZ
        have hfn := hdiv.f_nonneg X hX2
        have hhi := (hdiv.sandwich X hX2).2
        have : 0 ≤ hdiv.C * Real.log (zScale X) := le_trans hfn hhi
        have hCpos := hdiv.C_pos
        nlinarith [this, hCpos])
  -- now multiply the cited sAvg factor with the inner product
  have hprod :
      FactorAsymp
        (fun X => Inputs.sAvgRecip P X * (slant X * divLogZ X))
        (fun X => logX X * (logX X * logZ X)) :=
    FactorAsymp.mul (sAvgRecip_asymp P) hinner
      (fun X hX => by
        have hX1 : (sAvgRecip_asymp P).X₀ ≤ X := le_trans (le_max_left _ _) hX
        unfold logX
        have hfn := (sAvgRecip_asymp P).f_nonneg X hX1
        have hhi := ((sAvgRecip_asymp P).sandwich X hX1).2
        unfold logX at hhi
        have : 0 ≤ (sAvgRecip_asymp P).C * Real.log X := le_trans hfn hhi
        have hCpos := (sAvgRecip_asymp P).C_pos
        nlinarith [this, hCpos])
      (fun X hX => by
        -- 0 ≤ logX X * logZ X on the product threshold
        have hX2 : hinner.X₀ ≤ X := le_trans (le_max_right _ _) hX
        have hfn := hinner.f_nonneg X hX2
        have hhi := (hinner.sandwich X hX2).2
        have : 0 ≤ hinner.C * (logX X * logZ X) := le_trans hfn hhi
        have hCpos := hinner.C_pos
        nlinarith [this, hCpos])
  -- rewrite the shape `logX · (logX · logZ)` to `sigmaShape`, and the function to
  -- `sigmaSmallConcrete`.
  have hshape : (fun X => logX X * (logX X * logZ X)) = sigmaShape := by
    funext X; exact logX_mul_logX_mul_logZ X
  have hfun :
      (fun X => Inputs.sAvgRecip P X * (slant X * divLogZ X))
        = sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ := by
    funext X; rfl
  rw [hshape, hfun] at hprod
  exact hprod

/-! ## `mass_law_from_inputs` — the saturated mass law with both factors from Inputs.

We now feed `sigmaFactor_asymp` (from `Inputs.s_average_recip` + intermediate
`Σ_b` constituents) and `MassTensor.roughFactor_asymp` (from
`Inputs.rough_sqf_recip`) into `MassTensor.mass_law`, eliminating *both*
`FactorAsymp` hypotheses.

The residual non-`Inputs` content is exactly the two documented intermediate
factor-asymptotics for `Σ_b` (the inner `r`-progression length `≍ log X` and the
odd-divisor `A_s`-average `≍ log z`); these are the manuscript's
`lem:phi-progression-average` and `lem:small-divisor-average`, which the cited
`Inputs` interface does not isolate as single sums. -/

/-- **Saturated cubic event mass, reduced to cited Inputs** (`prop:mu`,
tex 1580–1629).

Both constituent factor-asymptotics of `μ_b = Σ_b · roughFactor` are produced
internally:

* the rough `d₊`-factor `roughFactor ≍ (log X)/(log z)` from the cited
  `Inputs.rough_sqf_recip` (via `MassTensor.roughFactor_asymp`);
* the small-prime saturation average `Σ_b ≍ (log X)² · log z` from the cited
  `Inputs.s_average_recip` (the `log S ≍ log X` factor) via `sigmaFactor_asymp`,
  together with the two threaded intermediate `Σ_b`-constituent asymptotics
  `hslant`/`hdiv`.

The conclusion is the manuscript's `μ_b ≍ (log X)³`: explicit positive constants
`c₁, c₂` and a threshold `X₀` with `c₁ (log X)³ ≤ μ_b ≤ c₂ (log X)³`.

This needs **no `FactorAsymp` hypothesis** on `μ_b`'s factors — both are
discharged.  The nonnegativity of the finite reciprocal carriers is proved in
`Inputs`; the hypotheses that remain are the rough window data the manuscript
fixes (tex 1618–1620), plus the two intermediate `Σ_b`-constituent
asymptotics. -/
theorem mass_law_from_inputs
    (P : Params) (b : ℕ)
    -- intermediate `Σ_b` constituents (`lem:phi-progression-average`,
    -- `lem:small-divisor-average`):
    (slant divLogZ : ℝ → ℝ)
    (hslant : FactorAsymp slant logX)
    (hdiv : FactorAsymp divLogZ logZ)
    -- cited-input nonnegativity (reciprocal sums):
    -- rough `d₊`-window data (tex 1618–1620) for `rough_sqf_recip`:
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      c₁ * logCube X
          ≤ muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
              (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X := by
  -- the cited rough factor (already in MassTensor)
  have hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape :=
    roughFactor_asymp P a₀ b₀ c₁w C₀ ha₀ hab hc₁w Mr aw bw
      haw hawltbw hbw hgapw hMr
  -- the (partly cited) sigma factor
  have hSig :
      FactorAsymp (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ) sigmaShape :=
    sigmaFactor_asymp P slant divLogZ hslant hdiv
  -- feed both into MassTensor.mass_law
  exact mass_law P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
    (fun X => Inputs.roughRecip X Mr aw bw) hSig hR

/-- Generic mass-law bridge from the intermediate small-side factors and the
clean bounded-defect/normalized rough-count targets. -/
theorem mass_law_from_inputs_of_defectIsBigOOne_and_normalized
    (P : Params) (b : ℕ)
    (slant divLogZ : ℝ → ℝ)
    (hslant : FactorAsymp slant logX)
    (hdiv : FactorAsymp divLogZ logZ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hmertens : Inputs.PrimeRecipSharpMertensNatDefectIsBigOOne)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      c₁ * logCube X
          ≤ muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
              (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X := by
  have hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape :=
    roughFactor_asymp_of_defectIsBigOOne_and_normalized P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hmertens hdisc
  have hSig :
      FactorAsymp (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ) sigmaShape :=
    sigmaFactor_asymp P slant divLogZ hslant hdiv
  exact mass_law P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
    (fun X => Inputs.roughRecip X Mr aw bw) hSig hR

/-- Generic mass-law bridge from eventual absolute Mertens control and normalized
rough-count discrepancy. -/
theorem mass_law_from_inputs_of_eventuallyAbsBound_and_normalized
    (P : Params) (b : ℕ)
    (slant divLogZ : ℝ → ℝ)
    (hslant : FactorAsymp slant logX)
    (hdiv : FactorAsymp divLogZ logZ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hmertens : Inputs.PrimeRecipSharpMertensNatDefectEventuallyAbsBound)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      c₁ * logCube X
          ≤ muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
              (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X :=
  mass_law_from_inputs_of_defectIsBigOOne_and_normalized P b slant divLogZ hslant hdiv
    a₀ b₀ c₁w C₀ ha₀ hab hc₁w
    (Inputs.PrimeRecipSharpMertensNatDefectIsBigOOne_of_eventuallyAbsBound hmertens)
    hdisc Mr aw bw haw hawltbw hbw hgapw hMr

/-- Generic mass-law bridge from two-sided Mertens control and normalized
rough-count discrepancy. -/
theorem mass_law_from_inputs_of_twoSided_and_normalized
    (P : Params) (b : ℕ)
    (slant divLogZ : ℝ → ℝ)
    (hslant : FactorAsymp slant logX)
    (hdiv : FactorAsymp divLogZ logZ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hmertens : Inputs.PrimeRecipSharpMertensNatDefectEventuallyTwoSidedBound)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      c₁ * logCube X
          ≤ muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
              (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X :=
  mass_law_from_inputs_of_defectIsBigOOne_and_normalized P b slant divLogZ hslant hdiv
    a₀ b₀ c₁w C₀ ha₀ hab hc₁w
    (Inputs.PrimeRecipSharpMertensNatDefectIsBigOOne_of_twoSided hmertens)
    hdisc Mr aw bw haw hawltbw hbw hgapw hMr

/-- Fixed-slant specialization of `mass_law_from_inputs`.

This removes the generic `FactorAsymp slant logX` hypothesis by taking the
slanted-length constituent to be the checked deterministic scale
`slantLogLength P s`.  The remaining `divLogZ` factor is still the arithmetic
small-divisor/Euler-product component of `lem:small-divisor-average`. -/
theorem mass_law_from_inputs_fixed_slant
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    -- intermediate divisor/Euler-product constituent:
    (divLogZ : ℝ → ℝ)
    (hdiv : FactorAsymp divLogZ logZ)
    -- rough `d₊`-window data (tex 1618–1620) for `rough_sqf_recip`:
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      c₁ * logCube X
          ≤ muB P b
              (sigmaSmallConcrete (Inputs.sAvgRecip P) (fun X => slantLogLength P s X)
                divLogZ)
              (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallConcrete (Inputs.sAvgRecip P) (fun X => slantLogLength P s X)
                divLogZ)
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X :=
  mass_law_from_inputs P b (fun X => slantLogLength P s X) divLogZ
    (slantLogLength_factor_asymp P s hs) hdiv
    a₀ b₀ c₁w C₀ ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr

/-- Fixed-slant specialization with the divisor/Euler-product constituent fixed
to the concrete carrier `Inputs.smallDivisorEulerSum`.

Compared with `mass_law_from_inputs_fixed_slant`, this removes the arbitrary
`FactorAsymp divLogZ logZ` hypothesis.  The caller supplies the lower bound
`smallDivisorEulerSum X ≳ log z`; the matching upper bound is proved in
`Inputs`. -/
theorem mass_law_from_inputs_fixed_slant_euler
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    -- standard Mertens/Euler-product lower bound for the explicit carrier:
    (cE XE : ℝ) (hcE : 0 < cE)
    (hE : ∀ X : ℝ, XE ≤ X →
      cE * logZ X ≤ Inputs.smallDivisorEulerSum X)
    -- rough `d₊`-window data (tex 1618–1620) for `rough_sqf_recip`:
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      c₁ * logCube X
          ≤ muB P b
              (sigmaSmallConcrete (Inputs.sAvgRecip P) (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorEulerSum X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallConcrete (Inputs.sAvgRecip P) (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorEulerSum X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X :=
  mass_law_from_inputs_fixed_slant P b s hs
    (fun X => Inputs.smallDivisorEulerSum X)
    (smallDivisorEulerSum_factor_asymp cE XE hcE hE)
    a₀ b₀ c₁w C₀ ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr

/-- Fixed-slant specialization with the concrete small-divisor Euler carrier.

This is the same mass-law endpoint as `mass_law_from_inputs_fixed_slant_euler`,
but the lower-bound argument for `Inputs.smallDivisorEulerSum` is discharged
internally by `Inputs.smallDivisorEulerSum_lower_from_standard_input`, which is
now theorem-level in the package frontier. -/
theorem mass_law_from_inputs_fixed_slant_euler_prime_recip
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    -- rough `d₊`-window data (tex 1618–1620) for `rough_sqf_recip`:
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      c₁ * logCube X
          ≤ muB P b
              (sigmaSmallConcrete (Inputs.sAvgRecip P) (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorEulerSum X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallConcrete (Inputs.sAvgRecip P) (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorEulerSum X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X :=
by
  rcases Inputs.smallDivisorEulerSum_lower_from_standard_input with ⟨cE, XE, hcE, hE⟩
  exact mass_law_from_inputs_fixed_slant P b s hs
    (fun X => Inputs.smallDivisorEulerSum X)
    (smallDivisorEulerSum_factor_asymp cE XE hcE (by simpa [logZ] using hE))
    a₀ b₀ c₁w C₀ ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr

/-- Fixed-slant mass law using the actual finite small-divisor average carrier
`Inputs.smallDivisorAverage P`, rather than the factored surrogate
`Inputs.sAvgRecip P * Inputs.smallDivisorEulerSum`.

The asymptotic `smallDivisorAverage P X ≍ log X · log z` is supplied by
`Inputs.smallDivisorAverage_lower_from_standard_inputs` and
`Inputs.smallDivisorAverage_upper_unconditional`; the conversion
`log(SScale P X) = η log X` and the final log-shape multiplication are checked
here.  Thus the sigma-side carrier is now
`slantLogLength P s · smallDivisorAverage P`. -/
theorem mass_law_from_inputs_fixed_slant_smallDivisorAverage_standard
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    -- rough `d₊`-window data (tex 1618–1620) for `rough_sqf_recip`:
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X := by
  have hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape :=
    sigmaSmallAverage_factor_asymp_standard P s hs
  have hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape :=
    roughFactor_asymp P a₀ b₀ c₁w C₀ ha₀ hab hc₁w Mr aw bw
      haw hawltbw hbw hgapw hMr
  exact mass_law P b
    (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
      (fun X => Inputs.smallDivisorAverage P X))
    (fun X => Inputs.roughRecip X Mr aw bw) hSig hR

/-- Eventual-modulus version of
`mass_law_from_inputs_fixed_slant_smallDivisorAverage_standard`.

The auxiliary modulus only needs to be bounded by `X^C₀` eventually, matching
the asymptotic use of the cited rough reciprocal estimate. -/
theorem mass_law_from_inputs_fixed_slant_smallDivisorAverage_standard_eventual_modulus
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (XMr : ℝ) (hMr : ∀ X : ℝ, XMr ≤ X → (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X := by
  have hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape :=
    sigmaSmallAverage_factor_asymp_standard P s hs
  have hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape :=
    roughFactor_asymp_eventual_modulus P a₀ b₀ c₁w C₀ ha₀ hab hc₁w Mr aw bw
      haw hawltbw hbw hgapw XMr hMr
  exact mass_law P b
    (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
      (fun X => Inputs.smallDivisorAverage P X))
    (fun X => Inputs.roughRecip X Mr aw bw) hSig hR

/-- Positive-exponent version of
`mass_law_from_inputs_fixed_slant_smallDivisorAverage_standard`.

The fixed auxiliary modulus condition is discharged internally: for `0 < C₀`,
any fixed `Mr` is eventually at most `X^C₀`. -/
theorem mass_law_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X := by
  rcases fixedNat_le_rpow_eventually_threshold Mr hC₀ with ⟨XMr, hMr⟩
  exact mass_law_from_inputs_fixed_slant_smallDivisorAverage_standard_eventual_modulus
    P b s hs a₀ b₀ c₁w C₀ ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw XMr hMr

/-- Fixed-carrier mass law from any packaged small-side factor and any packaged
rough-side factor.

This is a reusable concrete bridge: the carrier is the manuscript-shaped
`slantLogLength P s · smallDivisorAverage P` on the small side and
`roughRecip` on the rough side, while the two asymptotic inputs are supplied as
already proved `FactorAsymp` data. -/
theorem mass_law_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ) (Mr : ℕ) (aw bw : ℝ)
    (hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape)
    (hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X :=
  mass_law P b
    (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
      (fun X => Inputs.smallDivisorAverage P X))
    (fun X => Inputs.roughRecip X Mr aw bw) hSig hR

/-- Fixed-slant mass law from the standard small-side factor, bounded Mertens
defect, and normalized rough-count discrepancy. -/
theorem mass_law_from_inputs_fixed_slant_smallDivisorAverage_standard_of_defectIsBigOOne_and_normalized
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hmertens : Inputs.PrimeRecipSharpMertensNatDefectIsBigOOne)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X :=
  mass_law_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw
    (sigmaSmallAverage_factor_asymp_standard P s hs)
    (roughFactor_asymp_of_defectIsBigOOne_and_normalized P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hmertens hdisc)

/-- Fixed-slant mass law from the standard small-side factor, the one-sided
Mertens upper bound actually needed by the rough Euler-product lower half, and
normalized rough-count discrepancy. -/
theorem mass_law_from_inputs_fixed_slant_smallDivisorAverage_standard_of_defectEventuallyUpperBound_and_normalized
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hmertens : Inputs.PrimeRecipSharpMertensNatDefectEventuallyUpperBound)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X :=
  mass_law_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw
    (sigmaSmallAverage_factor_asymp_standard P s hs)
    (roughFactor_asymp_of_defectEventuallyUpperBound_and_normalized P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hmertens hdisc)

/-- Fixed-slant mass law from the standard small-side factor, the coefficient-one
dyadic prime-reciprocal block formulation of Mertens, and normalized rough-count
discrepancy. -/
theorem mass_law_from_inputs_fixed_slant_smallDivisorAverage_standard_of_dyadicBlocksSharpUpperBound_and_normalized
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hmertens : Inputs.PrimeRecipDyadicBlocksSharpUpperBound)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X :=
  mass_law_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw
    (sigmaSmallAverage_factor_asymp_standard P s hs)
    (roughFactor_asymp_of_dyadicBlocksSharpUpperBound_and_normalized P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hmertens hdisc)

/-- Fixed-slant mass law from standard small side, eventual absolute Mertens
control, and normalized rough-count discrepancy. -/
theorem mass_law_from_inputs_fixed_slant_smallDivisorAverage_standard_of_eventuallyAbsBound_and_normalized
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hmertens : Inputs.PrimeRecipSharpMertensNatDefectEventuallyAbsBound)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X :=
  mass_law_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw
    (sigmaSmallAverage_factor_asymp_standard P s hs)
    (roughFactor_asymp_of_eventuallyAbsBound_and_normalized P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hmertens hdisc)

/-- Fixed-slant mass law from standard small side, two-sided Mertens control,
and normalized rough-count discrepancy. -/
theorem mass_law_from_inputs_fixed_slant_smallDivisorAverage_standard_of_twoSided_and_normalized
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hmertens : Inputs.PrimeRecipSharpMertensNatDefectEventuallyTwoSidedBound)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X :=
  mass_law_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw
    (sigmaSmallAverage_factor_asymp_standard P s hs)
    (roughFactor_asymp_of_twoSided_and_normalized P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hmertens hdisc)

/-- Fixed-slant mass law from any packaged small-side factor and finite
bad-prime main-term dominance on the rough side. -/
theorem mass_law_from_small_factor_and_badPrimeProductMainTermDominatesError_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ)
    (hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hrough : Inputs.roughDyadicBadPrimeProductMainTermDominatesErrorBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X :=
  mass_law_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw hSig
    (roughFactor_asymp_of_badPrimeProductMainTermDominatesError P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hrough)

/-- Fixed-slant mass law from any packaged small-side factor and finite
Euler-product/error control on the rough side. -/
theorem mass_law_from_small_factor_and_badPrimeEulerProductError_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ)
    (hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hrough : Inputs.roughDyadicBadPrimeEulerProductErrorBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X :=
  mass_law_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw hSig
    (roughFactor_asymp_of_badPrimeEulerProductError P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hrough)

/-- Fixed-slant mass law from any packaged small-side factor and split finite
Euler-product/error control on the rough side. -/
theorem mass_law_from_small_factor_and_splitEulerProductError_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ)
    (hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hrough : Inputs.roughDyadicBadPrimeSplitEulerProductErrorBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X :=
  mass_law_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw hSig
    (roughFactor_asymp_of_splitEulerProductError P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hrough)

/-- Fixed-slant mass law from any packaged small-side factor and separated
finite Euler-product/error control on the rough side. -/
theorem mass_law_from_small_factor_and_separatedEulerProductError_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ)
    (hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hrough : Inputs.roughDyadicBadPrimeSeparatedEulerProductErrorBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X :=
  mass_law_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw hSig
    (roughFactor_asymp_of_separatedEulerProductError P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hrough)

/-- Diagnostic fixed-slant mass law from any packaged small-side factor, lower finite
Euler-product/error control, and the overstrong quotient-envelope upper premise
on the rough side. -/
theorem mass_law_from_small_factor_and_lowerEulerProductError_and_envelope_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ)
    (hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hLower : Inputs.roughDyadicBadPrimeLowerEulerProductErrorBound a₀ b₀ C₀)
    (hEnv : Inputs.roughDyadicBadPrimeProductEnvelopeUpperBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X :=
  mass_law_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw hSig
    (roughFactor_asymp_of_lowerEulerProductError_and_envelope P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hLower hEnv)

/-- Diagnostic fixed-slant mass law from any packaged small-side factor, split finite
Euler-product/error control, and the overstrong quotient-envelope upper premise
on the rough side. -/
theorem mass_law_from_small_factor_and_splitLowerEulerProductError_and_envelope_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ)
    (hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hSplit : Inputs.roughDyadicBadPrimeSplitEulerProductErrorBound a₀ b₀ C₀)
    (hEnv : Inputs.roughDyadicBadPrimeProductEnvelopeUpperBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X :=
  mass_law_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw hSig
    (roughFactor_asymp_of_splitLowerEulerProductError_and_envelope P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hSplit hEnv)

/-- Fixed-slant mass law from explicit density replacements for the two
remaining analytic inputs.

The small side is supplied by the exact odd-squarefree totient-density
hypothesis, and the rough side by a normalized dyadic-density estimate. All
transport to the concrete carriers used by `mass_law` is proved in Lean here and
in `Inputs`. -/
theorem mass_law_from_density_inputs_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hsmall : ∃ δ > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      δ * Inputs.oddSquarefreeRecipNat (2 ^ k)
        ≤ Inputs.oddSquarefreeTotientNat (2 ^ k))
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hrough :
      ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        ∀ (M : ℕ), (M : ℝ) ≤ X ^ C₀ →
        ∀ t : ℝ, X ^ a₀ ≤ t → t ≤ 2 * X ^ b₀ → 0 < t →
          0 < Real.log (zScale X) ∧
            c / Real.log (zScale X) ≤ Inputs.roughDyadicDensity X M t ∧
            Inputs.roughDyadicDensity X M t ≤ C / Real.log (zScale X))
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X := by
  have hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape :=
    sigmaSmallAverage_factor_asymp_of_oddSquarefreeTotientNat_recip_density
      P s hs hsmall
  have hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape :=
    roughFactor_asymp_of_roughDyadicDensity_bound P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hrough
  exact mass_law P b
    (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
      (fun X => Inputs.smallDivisorAverage P X))
    (fun X => Inputs.roughRecip X Mr aw bw) hSig hR

/-- Fixed-slant mass law from the small-side density replacement and finite
bad-prime main-term dominance on the rough side. -/
theorem mass_law_from_small_density_and_badPrimeProductMainTermDominatesError_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hsmall : ∃ δ > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      δ * Inputs.oddSquarefreeRecipNat (2 ^ k)
        ≤ Inputs.oddSquarefreeTotientNat (2 ^ k))
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hrough : Inputs.roughDyadicBadPrimeProductMainTermDominatesErrorBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X := by
  have hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape :=
    sigmaSmallAverage_factor_asymp_of_oddSquarefreeTotientNat_recip_density
      P s hs hsmall
  have hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape :=
    roughFactor_asymp_of_badPrimeProductMainTermDominatesError P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hrough
  exact mass_law P b
    (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
      (fun X => Inputs.smallDivisorAverage P X))
    (fun X => Inputs.roughRecip X Mr aw bw) hSig hR

/-- Fixed-slant mass law from the small-side density replacement and finite
Euler-product/error control on the rough side. -/
theorem mass_law_from_small_density_and_badPrimeEulerProductError_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hsmall : ∃ δ > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      δ * Inputs.oddSquarefreeRecipNat (2 ^ k)
        ≤ Inputs.oddSquarefreeTotientNat (2 ^ k))
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hrough : Inputs.roughDyadicBadPrimeEulerProductErrorBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X := by
  have hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape :=
    sigmaSmallAverage_factor_asymp_of_oddSquarefreeTotientNat_recip_density
      P s hs hsmall
  have hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape :=
    roughFactor_asymp_of_badPrimeEulerProductError P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hrough
  exact mass_law P b
    (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
      (fun X => Inputs.smallDivisorAverage P X))
    (fun X => Inputs.roughRecip X Mr aw bw) hSig hR

/-- Fixed-slant mass law from the small-side density replacement and split
finite Euler-product/error control on the rough side. -/
theorem mass_law_from_small_density_and_splitEulerProductError_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hsmall : ∃ δ > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      δ * Inputs.oddSquarefreeRecipNat (2 ^ k)
        ≤ Inputs.oddSquarefreeTotientNat (2 ^ k))
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hrough : Inputs.roughDyadicBadPrimeSplitEulerProductErrorBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X := by
  have hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape :=
    sigmaSmallAverage_factor_asymp_of_oddSquarefreeTotientNat_recip_density
      P s hs hsmall
  have hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape :=
    roughFactor_asymp_of_splitEulerProductError P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hrough
  exact mass_law P b
    (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
      (fun X => Inputs.smallDivisorAverage P X))
    (fun X => Inputs.roughRecip X Mr aw bw) hSig hR

/-- Fixed-slant mass law from the small-side density replacement and separated
finite Euler-product/error control on the rough side. -/
theorem mass_law_from_small_density_and_separatedEulerProductError_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hsmall : ∃ δ > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      δ * Inputs.oddSquarefreeRecipNat (2 ^ k)
        ≤ Inputs.oddSquarefreeTotientNat (2 ^ k))
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hrough : Inputs.roughDyadicBadPrimeSeparatedEulerProductErrorBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X := by
  have hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape :=
    sigmaSmallAverage_factor_asymp_of_oddSquarefreeTotientNat_recip_density
      P s hs hsmall
  have hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape :=
    roughFactor_asymp_of_separatedEulerProductError P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hrough
  exact mass_law P b
    (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
      (fun X => Inputs.smallDivisorAverage P X))
    (fun X => Inputs.roughRecip X Mr aw bw) hSig hR

/-- Diagnostic fixed-slant mass law from the small-side density replacement, lower finite
Euler-product/error control, and the overstrong quotient-envelope upper premise
on the rough side. -/
theorem mass_law_from_small_density_and_lowerEulerProductError_and_envelope_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hsmall : ∃ δ > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      δ * Inputs.oddSquarefreeRecipNat (2 ^ k)
        ≤ Inputs.oddSquarefreeTotientNat (2 ^ k))
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hLower : Inputs.roughDyadicBadPrimeLowerEulerProductErrorBound a₀ b₀ C₀)
    (hEnv : Inputs.roughDyadicBadPrimeProductEnvelopeUpperBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X :=
  mass_law_from_small_factor_and_lowerEulerProductError_and_envelope_fixed_slant_smallDivisorAverage
    P b s
    (sigmaSmallAverage_factor_asymp_of_oddSquarefreeTotientNat_recip_density
      P s hs hsmall)
    a₀ b₀ c₁w C₀ ha₀ hab hc₁w hLower hEnv
    Mr aw bw haw hawltbw hbw hgapw hMr

/-- Diagnostic fixed-slant mass law from the small-side density replacement, split finite
Euler-product/error control, and the overstrong quotient-envelope upper premise
on the rough side. The rough product upper estimate in the split input is not
used; the upper half is supplied by `hEnv`. -/
theorem mass_law_from_small_density_and_splitLowerEulerProductError_and_envelope_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hsmall : ∃ δ > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      δ * Inputs.oddSquarefreeRecipNat (2 ^ k)
        ≤ Inputs.oddSquarefreeTotientNat (2 ^ k))
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hSplit : Inputs.roughDyadicBadPrimeSplitEulerProductErrorBound a₀ b₀ C₀)
    (hEnv : Inputs.roughDyadicBadPrimeProductEnvelopeUpperBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X :=
  mass_law_from_small_factor_and_splitLowerEulerProductError_and_envelope_fixed_slant_smallDivisorAverage
    P b s
    (sigmaSmallAverage_factor_asymp_of_oddSquarefreeTotientNat_recip_density
      P s hs hsmall)
    a₀ b₀ c₁w C₀ ha₀ hab hc₁w hSplit hEnv
    Mr aw bw haw hawltbw hbw hgapw hMr

/-- Fixed-slant mass law from the defect-gap small-side replacement and any
already packaged rough-factor asymptotic. -/
theorem mass_law_from_defectGap_and_rough_factor_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hsmall : Inputs.OddSquarefreeTotientDefectGapBound)
    (Mr : ℕ) (aw bw : ℝ)
    (hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X :=
  mass_law_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw
    (sigmaSmallAverage_factor_asymp_of_defectGap P s hs hsmall) hR

/-- Fixed-slant mass law from the product-lower small-side replacement and any
already packaged rough-factor asymptotic. -/
theorem mass_law_from_productLowerBound_and_rough_factor_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hsmall : Inputs.OddSquarefreeTotientProductDyadicLowerBound)
    (Mr : ℕ) (aw bw : ℝ)
    (hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X :=
  mass_law_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw
    (sigmaSmallAverage_factor_asymp_of_productLowerBound P s hs hsmall) hR

/-- Fixed-slant mass law from the product-defect-gap small-side replacement and
any already packaged rough-factor asymptotic. -/
theorem mass_law_from_defectProductGap_and_rough_factor_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hsmall : Inputs.OddSquarefreeTotientDefectProductGapBound)
    (Mr : ℕ) (aw bw : ℝ)
    (hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
        ∧ muB P b
              (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                (fun X => Inputs.smallDivisorAverage P X))
              (fun X => Inputs.roughRecip X Mr aw bw) X
            ≤ c₂ * logCube X :=
  mass_law_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw
    (sigmaSmallAverage_factor_asymp_of_defectProductGap P s hs hsmall) hR

/-! ## Bundled headline: mass law (from Inputs) + event-tensor bounds.

The same packaging as `MassTensor.mass_law_and_event_tensor`, but with the sigma
factor discharged from `Inputs.s_average_recip` instead of threaded.  This is the
form downstream files would consume once the two intermediate `Σ_b`
constituents are supplied. -/

/-- The Inputs-reduced mass law bundled with the event-tensor bounds
(`prop:mu` + `prop:event-tensor`), with both `μ_b`-factors discharged from cited
inputs (`s_average_recip`, `rough_sqf_recip`) plus the two intermediate `Σ_b`
constituent asymptotics. -/
theorem mass_law_and_event_tensor_from_inputs
    (P : Params) (b : ℕ)
    (slant divLogZ : ℝ → ℝ)
    (hslant : FactorAsymp slant logX)
    (hdiv : FactorAsymp divLogZ logZ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
      ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) := by
  -- the cited rough factor and the (partly cited) sigma factor
  have hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape :=
    roughFactor_asymp P a₀ b₀ c₁w C₀ ha₀ hab hc₁w Mr aw bw
      haw hawltbw hbw hgapw hMr
  have hSig :
      FactorAsymp (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ) sigmaShape :=
    sigmaFactor_asymp P slant divLogZ hslant hdiv
  exact mass_law_and_event_tensor P b
    (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
    (fun X => Inputs.roughRecip X Mr aw bw) hSig hR
    B Bsingle Kassemb XB hKassemb hassemb

/-- Generic mass/event bridge from bounded Mertens defect and normalized
rough-count discrepancy. -/
theorem mass_law_and_event_tensor_from_inputs_of_defectIsBigOOne_and_normalized
    (P : Params) (b : ℕ)
    (slant divLogZ : ℝ → ℝ)
    (hslant : FactorAsymp slant logX)
    (hdiv : FactorAsymp divLogZ logZ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hmertens : Inputs.PrimeRecipSharpMertensNatDefectIsBigOOne)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
      ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) := by
  have hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape :=
    roughFactor_asymp_of_defectIsBigOOne_and_normalized P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hmertens hdisc
  have hSig :
      FactorAsymp (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ) sigmaShape :=
    sigmaFactor_asymp P slant divLogZ hslant hdiv
  exact mass_law_and_event_tensor P b
    (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
    (fun X => Inputs.roughRecip X Mr aw bw) hSig hR
    B Bsingle Kassemb XB hKassemb hassemb

/-- Generic mass/event bridge from eventual absolute Mertens control and
normalized rough-count discrepancy. -/
theorem mass_law_and_event_tensor_from_inputs_of_eventuallyAbsBound_and_normalized
    (P : Params) (b : ℕ)
    (slant divLogZ : ℝ → ℝ)
    (hslant : FactorAsymp slant logX)
    (hdiv : FactorAsymp divLogZ logZ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hmertens : Inputs.PrimeRecipSharpMertensNatDefectEventuallyAbsBound)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
      ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_inputs_of_defectIsBigOOne_and_normalized
    P b slant divLogZ hslant hdiv a₀ b₀ c₁w C₀ ha₀ hab hc₁w
    (Inputs.PrimeRecipSharpMertensNatDefectIsBigOOne_of_eventuallyAbsBound hmertens)
    hdisc Mr aw bw haw hawltbw hbw hgapw hMr
    B Bsingle Kassemb XB hKassemb hassemb

/-- Generic mass/event bridge from two-sided Mertens control and normalized
rough-count discrepancy. -/
theorem mass_law_and_event_tensor_from_inputs_of_twoSided_and_normalized
    (P : Params) (b : ℕ)
    (slant divLogZ : ℝ → ℝ)
    (hslant : FactorAsymp slant logX)
    (hdiv : FactorAsymp divLogZ logZ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hmertens : Inputs.PrimeRecipSharpMertensNatDefectEventuallyTwoSidedBound)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
      ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b (sigmaSmallConcrete (Inputs.sAvgRecip P) slant divLogZ)
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_inputs_of_defectIsBigOOne_and_normalized
    P b slant divLogZ hslant hdiv a₀ b₀ c₁w C₀ ha₀ hab hc₁w
    (Inputs.PrimeRecipSharpMertensNatDefectIsBigOOne_of_twoSided hmertens)
    hdisc Mr aw bw haw hawltbw hbw hgapw hMr
    B Bsingle Kassemb XB hKassemb hassemb

/-- Fixed-slant specialization of `mass_law_and_event_tensor_from_inputs`.

This carries the checked deterministic slanted-length scale through the bundled
mass-law/event-tensor route, leaving only the divisor/Euler-product constituent
`divLogZ` as the small-saturation arithmetic input. -/
theorem mass_law_and_event_tensor_from_inputs_fixed_slant
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (divLogZ : ℝ → ℝ)
    (hdiv : FactorAsymp divLogZ logZ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallConcrete (Inputs.sAvgRecip P) (fun X => slantLogLength P s X)
                  divLogZ)
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallConcrete (Inputs.sAvgRecip P) (fun X => slantLogLength P s X)
                  divLogZ)
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
      ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallConcrete (Inputs.sAvgRecip P) (fun X => slantLogLength P s X)
                  divLogZ)
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallConcrete (Inputs.sAvgRecip P) (fun X => slantLogLength P s X)
                  divLogZ)
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_inputs P b
    (fun X => slantLogLength P s X) divLogZ
    (slantLogLength_factor_asymp P s hs) hdiv
    a₀ b₀ c₁w C₀ ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr
    B Bsingle Kassemb XB hKassemb hassemb

/-- Event-tensor bundle with fixed slant and the concrete small-divisor Euler
carrier.  This is the most concrete current mass-law route: `sAvgRecip`,
`slantLogLength`, `smallDivisorEulerSum`, and `roughRecip` are all fixed carriers;
only the standard Euler lower bound and the rough-window/certificate-tensor
inputs remain. -/
theorem mass_law_and_event_tensor_from_inputs_fixed_slant_euler
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (cE XE : ℝ) (hcE : 0 < cE)
    (hE : ∀ X : ℝ, XE ≤ X →
      cE * logZ X ≤ Inputs.smallDivisorEulerSum X)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallConcrete (Inputs.sAvgRecip P) (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorEulerSum X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallConcrete (Inputs.sAvgRecip P) (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorEulerSum X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
      ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallConcrete (Inputs.sAvgRecip P) (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorEulerSum X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallConcrete (Inputs.sAvgRecip P) (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorEulerSum X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_inputs_fixed_slant P b s hs
    (fun X => Inputs.smallDivisorEulerSum X)
    (smallDivisorEulerSum_factor_asymp cE XE hcE hE)
    a₀ b₀ c₁w C₀ ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr
    B Bsingle Kassemb XB hKassemb hassemb

/-- Event-tensor bundle with fixed slant and the concrete small-divisor Euler
carrier, with that carrier's lower growth discharged from the standard
truncated Euler-sum/Mertens input.

This is the event-tensor companion to
`mass_law_from_inputs_fixed_slant_euler_prime_recip`: the explicit
`smallDivisorEulerSum X ≳ log z` hypothesis is no longer threaded through the
API. -/
theorem mass_law_and_event_tensor_from_inputs_fixed_slant_euler_prime_recip
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallConcrete (Inputs.sAvgRecip P) (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorEulerSum X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallConcrete (Inputs.sAvgRecip P) (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorEulerSum X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
      ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallConcrete (Inputs.sAvgRecip P) (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorEulerSum X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallConcrete (Inputs.sAvgRecip P) (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorEulerSum X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) := by
  rcases Inputs.smallDivisorEulerSum_lower_from_standard_input with ⟨cE, XE, hcE, hE⟩
  exact mass_law_and_event_tensor_from_inputs_fixed_slant_euler P b s hs
    cE XE hcE (by simpa [logZ] using hE)
    a₀ b₀ c₁w C₀ ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr
    B Bsingle Kassemb XB hKassemb hassemb

/-- Event-tensor bundle with fixed slant and the actual finite small-divisor
average carrier `Inputs.smallDivisorAverage P`.

Compared with the concrete-Euler route above, this packages the already
interchanged `∑_{s≤S,sqf} A_s/s` carrier directly.  Its two-sided asymptotic is
supplied by `smallDivisorAverage_factor_asymp_standard`, whose only external
content is the two named Mertens-type Inputs; the shape multiplication and final
event-tensor comparison are checked here. -/
theorem mass_law_and_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) := by
  have hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape :=
    sigmaSmallAverage_factor_asymp_standard P s hs
  have hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape :=
    roughFactor_asymp P a₀ b₀ c₁w C₀ ha₀ hab hc₁w Mr aw bw
      haw hawltbw hbw hgapw hMr
  exact mass_law_and_event_tensor P b
    (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
      (fun X => Inputs.smallDivisorAverage P X))
    (fun X => Inputs.roughRecip X Mr aw bw) hSig hR
    B Bsingle Kassemb XB hKassemb hassemb

/-- Eventual-modulus version of
`mass_law_and_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard`.

This keeps the cited Mertens/rough-window inputs unchanged while replacing the
artificial global auxiliary-modulus bound by the eventual bound actually used
by the asymptotic argument. -/
theorem mass_law_and_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_eventual_modulus
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (XMr : ℝ) (hMr : ∀ X : ℝ, XMr ≤ X → (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) := by
  have hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape :=
    sigmaSmallAverage_factor_asymp_standard P s hs
  have hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape :=
    roughFactor_asymp_eventual_modulus P a₀ b₀ c₁w C₀ ha₀ hab hc₁w Mr aw bw
      haw hawltbw hbw hgapw XMr hMr
  exact mass_law_and_event_tensor P b
    (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
      (fun X => Inputs.smallDivisorAverage P X))
    (fun X => Inputs.roughRecip X Mr aw bw) hSig hR
    B Bsingle Kassemb XB hKassemb hassemb

/-- Positive-exponent version of
`mass_law_and_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard`.

For fixed `Mr`, the auxiliary rough-modulus bound `Mr ≤ X^C₀` is automatic
eventually as soon as `0 < C₀`; this theorem folds that threshold into the final
mass/event-tensor threshold. -/
theorem mass_law_and_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) := by
  rcases fixedNat_le_rpow_eventually_threshold Mr hC₀ with ⟨XMr, hMr⟩
  exact mass_law_and_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_eventual_modulus
    P b s hs a₀ b₀ c₁w C₀ ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw
    XMr hMr B Bsingle Kassemb XB hKassemb hassemb

/-- Standard fixed-slant event-tensor route with both auxiliary event constants
discharged internally.

Compared with
`mass_law_and_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus`,
this version also removes the separate sign hypothesis on the assembled
event-estimate constant.  The proof replaces that constant by `max Kassemb 0`
on the eventual range, where the log-cube divisor shapes are nonnegative. -/
theorem mass_law_and_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_event_constant
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) := by
  rcases fixedNat_le_rpow_eventually_threshold Mr hC₀ with ⟨XMr, hMr⟩
  have hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape :=
    sigmaSmallAverage_factor_asymp_standard P s hs
  have hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape :=
    roughFactor_asymp_eventual_modulus P a₀ b₀ c₁w C₀ ha₀ hab hc₁w Mr aw bw
      haw hawltbw hbw hgapw XMr hMr
  exact mass_law_and_event_tensor_of_arbitrary_event_constant P b
    (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
      (fun X => Inputs.smallDivisorAverage P X))
    (fun X => Inputs.roughRecip X Mr aw bw) hSig hR
    B Bsingle Kassemb XB hassemb

/-- Standard fixed-slant route with the event carriers specialized to the
concrete exact-divisor tensor carriers.

This discharges the formerly exposed `prop:event-tensor` hypothesis for the
actual carrier family used downstream: the required `logCube/D²` and
`logCube/D` bounds are produced by the prime-window estimate, the
exact-divisor tensor estimate, and the reciprocal-`φ` mass upper bound. -/
theorem mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (a : ℝ → ℕ → ℕ → ℕ)
    (Cprime Ktensor cmass Cmass Xprime Xtensor Xmass : ℝ)
    (hCprime : 0 ≤ Cprime) (hKtensor : 0 ≤ Ktensor) (hcmass : 0 < cmass)
    (hprime : ∀ X : ℝ, Xprime ≤ X →
      Inputs.primeRecipWindow P X ≤ Cprime * Real.log X)
    (htensor : ∀ X : ℝ, Xtensor ≤ X → ∀ D : ℕ, 1 ≤ D →
      exactDivisorMPhiTensorFiberCoprime P X D (a X D) ≤
        (Ktensor / cmass) * (exactDivisorMPhiMassRaw P X / (D : ℝ)))
    (hmass : ∀ X : ℝ, Xmass ≤ X →
      exactDivisorMPhiMassRaw P X ≤ Cmass * logSq X) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        exactDivisorEventDoubleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) := by
  exact
    mass_law_and_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_event_constant
      P b s hs a₀ b₀ c₁w C₀ ha₀ hab hc₁w hC₀ Mr aw bw
      haw hawltbw hbw hgapw
      (exactDivisorEventDoubleCarrier P a)
      (exactDivisorEventSingleCarrier P a)
      (Cprime * (Ktensor / cmass) * Cmass)
      (max (max Xprime Xtensor) (max Xmass (Real.exp 1)))
      (exactDivisorEventCarriers_logCube_bound
        P a Cprime Ktensor cmass Cmass Xprime Xtensor Xmass
        hCprime hKtensor hcmass hprime htensor hmass)

/-- Standard fixed-slant exact-divisor event route with the elementary
prime-window bound also discharged internally.

After this bridge, the only event-carrier estimates still supplied by the
caller are the exact-divisor tensor bound and the reciprocal-`φ` mass upper
bound; the unrestricted reciprocal prime-window estimate is obtained from the
checked unconditional harmonic-sum argument in `Inputs`. -/
theorem mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (a : ℝ → ℕ → ℕ → ℕ)
    (Ktensor cmass Cmass Xtensor Xmass : ℝ)
    (hKtensor : 0 ≤ Ktensor) (hcmass : 0 < cmass)
    (htensor : ∀ X : ℝ, Xtensor ≤ X → ∀ D : ℕ, 1 ≤ D →
      exactDivisorMPhiTensorFiberCoprime P X D (a X D) ≤
        (Ktensor / cmass) * (exactDivisorMPhiMassRaw P X / (D : ℝ)))
    (hmass : ∀ X : ℝ, Xmass ≤ X →
      exactDivisorMPhiMassRaw P X ≤ Cmass * logSq X) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        exactDivisorEventDoubleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) := by
  rcases Inputs.primeRecipWindow_upper_unconditional P with
    ⟨Cprime, Xprime, hCprime_pos, hprime⟩
  exact
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus
      P b s hs a₀ b₀ c₁w C₀ ha₀ hab hc₁w hC₀ Mr aw bw
      haw hawltbw hbw hgapw a Cprime Ktensor cmass Cmass Xprime Xtensor Xmass
      hCprime_pos.le hKtensor hcmass hprime htensor hmass

/-- Standard fixed-slant exact-divisor event route with both the prime-window
bound and the reciprocal-`φ` quadratic mass upper bound discharged internally
from the paper's long ordinary-squarefree progression package.

The remaining analytic event input is the tensor estimate itself.  All algebra
from that tensor estimate to the final `μ/D²` and `μ/D` event bounds is checked
in this file. -/
theorem mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (a : ℝ → ℕ → ℕ → ℕ)
    (Ktensor cmass Xtensor : ℝ)
    (hKtensor : 0 ≤ Ktensor) (hcmass : 0 < cmass)
    (htensor : ∀ X : ℝ, Xtensor ≤ X → ∀ D : ℕ, 1 ≤ D →
      exactDivisorMPhiTensorFiberCoprime P X D (a X D) ≤
        (Ktensor / cmass) * (exactDivisorMPhiMassRaw P X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        exactDivisorEventDoubleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) := by
  rcases
      exactDivisorMPhiMassRaw_logSq_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
        (P := P) hlower hupper with
    ⟨_cmass_lower, Cmass, Xmass, _hcmass_lower, _hCmass, hmass_two_sided⟩
  exact
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime
      P b s hs a₀ b₀ c₁w C₀ ha₀ hab hc₁w hC₀ Mr aw bw
      haw hawltbw hbw hgapw a Ktensor cmass Cmass Xtensor Xmass
      hKtensor hcmass htensor
      (fun X hX => (hmass_two_sided X hX).2)

/-- Standard fixed-slant exact-divisor event route with the compressed tensor
estimate expanded into the checked finite-sum tensor ingredients.

This is the paper-facing decomposition of the remaining event-tensor input:
instead of assuming the final `M_φ/D` tensor estimate directly, the caller
supplies the fixed-`s` reciprocal-`φ` progression upper bound and the lower
comparison between the reciprocal-`φ` mass and its main-term shape. -/
theorem mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long_of_tensor_fiber_lower
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (a : ℝ → ℕ → ℕ → ℕ)
    (Kφ cφ Xfiber XmassLower : ℝ)
    (hKφ : 0 ≤ Kφ) (hcφ : 0 < cφ)
    (hfiberφ : ∀ X : ℝ, Xfiber ≤ X → ∀ D : ℕ, 1 ≤ D →
      ∀ t ∈ exactDivisorSRange P X,
        Nat.Coprime t D →
        phiProgressionAverage P X D (a X D t) t
          ≤ Kφ * phiProgressionAverageShape P X D t)
    (hmassφ_lower : ∀ X : ℝ, XmassLower ≤ X →
      cφ * exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        exactDivisorEventDoubleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) := by
  exact
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long
      P b s hs hlower hupper a₀ b₀ c₁w C₀ ha₀ hab hc₁w hC₀ Mr aw bw
      haw hawltbw hbw hgapw a Kφ cφ
      (max (max Xfiber XmassLower) (Real.exp 1)) hKφ hcφ
      (by
        intro X hX D hD
        have hXfiber : Xfiber ≤ X :=
          le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
        have hXmass : XmassLower ≤ X :=
          le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
        have hXone : (1 : ℝ) ≤ X :=
          le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1)
            (le_trans (le_max_right _ _) hX)
        have hDpos : 0 < D := lt_of_lt_of_le Nat.zero_lt_one hD
        exact
          exactDivisorMPhiTensorFiberCoprime_le_massRaw_over_modulus
            P X D (a X D) Kφ cφ hXone hDpos hKφ hcφ
            (hfiberφ X hXfiber D hD)
            (hmassφ_lower X hXmass))

/-- Standard fixed-slant exact-divisor event route with the mass lower
comparison also discharged from the paper's long ordinary-squarefree
progression package.

The only event-tensor hypothesis left here is the fixed-`s` reciprocal-`φ`
progression upper bound used inside the tensor fiber sum. -/
theorem mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long_of_tensor_fiber_upper
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (a : ℝ → ℕ → ℕ → ℕ)
    (Kφ Xfiber : ℝ)
    (hKφ : 0 ≤ Kφ)
    (hfiberφ : ∀ X : ℝ, Xfiber ≤ X → ∀ D : ℕ, 1 ≤ D →
      ∀ t ∈ exactDivisorSRange P X,
        Nat.Coprime t D →
        phiProgressionAverage P X D (a X D t) t
          ≤ Kφ * phiProgressionAverageShape P X D t) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        exactDivisorEventDoubleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) := by
  rcases
      exactDivisorMPhiMassFiber_comparable_to_shape_of_coprimeLong_ordinaryUpper_wide
        (OrdinarySquarefreeCoprimeDensityLowerLong_of_progression_long hlower)
        hupper with
    ⟨cφ, _Cφ, XmassLower, hcφ, _hCφ, hmassφ⟩
  exact
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long_of_tensor_fiber_lower
      P b s hs hlower hupper a₀ b₀ c₁w C₀ ha₀ hab hc₁w hC₀ Mr aw bw
      haw hawltbw hbw hgapw a Kφ cφ Xfiber XmassLower hKφ hcφ
      hfiberφ
      (fun X hX => (hmassφ X hX).1)

/-- Wide-lower version of
`mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long`. -/
theorem
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long_wideLower
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (a : ℝ → ℕ → ℕ → ℕ)
    (Ktensor cmass Xtensor : ℝ)
    (hKtensor : 0 ≤ Ktensor) (hcmass : 0 < cmass)
    (htensor : ∀ X : ℝ, Xtensor ≤ X → ∀ D : ℕ, 1 ≤ D →
      exactDivisorMPhiTensorFiberCoprime P X D (a X D) ≤
        (Ktensor / cmass) * (exactDivisorMPhiMassRaw P X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        exactDivisorEventDoubleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long
    P b s hs (OrdinarySquarefreeProgressionCoprimeDensityLowerLong_eta_of_wide hlower)
    hupper a₀ b₀ c₁w C₀ ha₀ hab hc₁w hC₀ Mr aw bw
    haw hawltbw hbw hgapw a Ktensor cmass Xtensor hKtensor hcmass htensor

/-- Wide-lower version of the expanded tensor-fiber/lower-mass event route. -/
theorem
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long_of_tensor_fiber_lower_wideLower
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (a : ℝ → ℕ → ℕ → ℕ)
    (Kφ cφ Xfiber XmassLower : ℝ)
    (hKφ : 0 ≤ Kφ) (hcφ : 0 < cφ)
    (hfiberφ : ∀ X : ℝ, Xfiber ≤ X → ∀ D : ℕ, 1 ≤ D →
      ∀ t ∈ exactDivisorSRange P X,
        Nat.Coprime t D →
        phiProgressionAverage P X D (a X D t) t
          ≤ Kφ * phiProgressionAverageShape P X D t)
    (hmassφ_lower : ∀ X : ℝ, XmassLower ≤ X →
      cφ * exactDivisorMPhiMassShape P X ≤ exactDivisorMPhiMassFiber P X) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        exactDivisorEventDoubleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long_of_tensor_fiber_lower
    P b s hs (OrdinarySquarefreeProgressionCoprimeDensityLowerLong_eta_of_wide hlower)
    hupper a₀ b₀ c₁w C₀ ha₀ hab hc₁w hC₀ Mr aw bw
    haw hawltbw hbw hgapw a Kφ cφ Xfiber XmassLower hKφ hcφ
    hfiberφ hmassφ_lower

/-- Wide-lower version of the expanded tensor-fiber event route. -/
theorem
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long_of_tensor_fiber_upper_wideLower
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (a : ℝ → ℕ → ℕ → ℕ)
    (Kφ Xfiber : ℝ)
    (hKφ : 0 ≤ Kφ)
    (hfiberφ : ∀ X : ℝ, Xfiber ≤ X → ∀ D : ℕ, 1 ≤ D →
      ∀ t ∈ exactDivisorSRange P X,
        Nat.Coprime t D →
        phiProgressionAverage P X D (a X D t) t
          ≤ Kφ * phiProgressionAverageShape P X D t) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        exactDivisorEventDoubleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long_of_tensor_fiber_upper
    P b s hs (OrdinarySquarefreeProgressionCoprimeDensityLowerLong_eta_of_wide hlower)
    hupper a₀ b₀ c₁w C₀ ha₀ hab hc₁w hC₀ Mr aw bw
    haw hawltbw hbw hgapw a Kφ Xfiber hKφ hfiberφ

/-- Paper-range exact-divisor event carrier bound with the `M_φ` tensor input
discharged from the cited wide ordinary-squarefree progression upper estimate.

The conclusion keeps the manuscript modulus hypotheses:
`D` is squarefree, odd, and `D≤YU`.  The remaining non-analytic hypothesis is
the finite residue-map fact that the selected residue is reduced modulo `D`
on the coprime `s`-fibers. -/
theorem exactDivisorEventCarriers_logCube_bound_on_YU_of_ordinaryUpper_wide
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (hordinaryYU :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ)
    (a : ℝ → ℕ → ℕ → ℕ)
    (hresidue : ∀ X : ℝ, ∀ D s : ℕ,
      s ∈ exactDivisorSRange P X → Nat.Coprime s D →
        Nat.Coprime (a X D s) D) :
    ∃ Kev X₀ : ℝ, 0 ≤ Kev ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P a X D
            ≤ Kev * (logCube X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P a X D
            ≤ Kev * (logCube X / (D : ℝ)) := by
  rcases Inputs.primeRecipWindow_upper_unconditional P with
    ⟨Cprime, Xprime, hCprime_pos, hprime⟩
  rcases
      exactDivisorMPhiMassRaw_logSq_of_ordinarySquarefreeProgressionLong_wideUpper_concreteOmegaTail
        (P := P) hlower hupper with
    ⟨_cmass_raw, Cmass, XmassUpper, _hcmass_raw, hCmass, hmass_upper⟩
  rcases
      exactDivisorMPhiMassFiber_comparable_to_shape_of_coprimeLong_ordinaryUpper_wide
        (OrdinarySquarefreeCoprimeDensityLowerLong_of_progression_long hlower)
        hupper with
    ⟨cφ, _Cφ, XmassLower, hcφ, _hCφ, hmassφ⟩
  rcases exactDivisorMPhiTensorFiberCoprime_le_massRaw_over_modulus_of_ordinaryUpper_wide
      hordinaryYU with
    ⟨Ktensor, Xtensor, hKtensor, htensor_raw⟩
  refine ⟨Cprime * (Ktensor / cφ) * Cmass,
    max (max Xprime (max Xtensor XmassLower)) (max XmassUpper (Real.exp 1)),
    ?_, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hCprime_pos.le (div_nonneg hKtensor.le hcφ.le))
      hCmass.le
  · intro X hX D hD hD_sqf hD_odd hDwide
    exact
      exactDivisorEventCarriers_logCube_bound_on_YU
        P a Cprime Ktensor cφ Cmass Xprime (max Xtensor XmassLower)
        XmassUpper hCprime_pos.le hKtensor.le hcφ hprime
        (by
          intro X hX D hD hD_sqf hD_odd hDwide
          have hXtensor : Xtensor ≤ X :=
            le_trans (le_max_left _ _) hX
          have hXmassLower : XmassLower ≤ X :=
            le_trans (le_max_right _ _) hX
          exact
            htensor_raw X hXtensor D hD hD_sqf hD_odd hDwide
              (a X D)
              (fun s hs hsD => hresidue X D s hs hsD)
              cφ hcφ ((hmassφ X hXmassLower).1))
        (fun X hX => (hmass_upper X hX).2)
        X hX D hD hD_sqf hD_odd hDwide

/-- Paper-range event-carrier bound using the specialized phi-window squarefree
lower carrier for the `M_φ` mass lower comparison.

Compared with `exactDivisorEventCarriers_logCube_bound_on_YU_of_ordinaryUpper_wide`,
this avoids asking the event layer for the stronger long ordinary-squarefree
lower estimate.  The remaining analytic inputs are the phi-window squarefree
reciprocal lower carrier, the ordinary-squarefree upper estimate, and the
wide-`YU` upper estimate used in the tensor fiber. -/
theorem exactDivisorEventCarriers_logCube_bound_on_YU_of_sqfRecipLower_ordinaryUpper_wide
    {P : Params}
    (hlower : PhiProgressionSqfRecipLower P)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (hordinaryYU :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ)
    (a : ℝ → ℕ → ℕ → ℕ)
    (hresidue : ∀ X : ℝ, ∀ D s : ℕ,
      s ∈ exactDivisorSRange P X → Nat.Coprime s D →
        Nat.Coprime (a X D s) D) :
    ∃ Kev X₀ : ℝ, 0 ≤ Kev ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P a X D
            ≤ Kev * (logCube X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P a X D
            ≤ Kev * (logCube X / (D : ℝ)) := by
  rcases Inputs.primeRecipWindow_upper_unconditional P with
    ⟨Cprime, Xprime, hCprime_pos, hprime⟩
  rcases exactDivisorMPhiMassRaw_logSq_of_sqfRecipLower_ordinaryUpper_wide
      (P := P) hlower hupper with
    ⟨_cmass_raw, Cmass, XmassUpper, _hcmass_raw, hCmass, hmass_upper⟩
  rcases exactDivisorMPhiMassFiber_comparable_to_shape_of_sqfRecipLower_ordinaryUpper_wide
      hlower hupper with
    ⟨cφ, _Cφ, XmassLower, hcφ, _hCφ, hmassφ⟩
  rcases exactDivisorMPhiTensorFiberCoprime_le_massRaw_over_modulus_of_ordinaryUpper_wide
      hordinaryYU with
    ⟨Ktensor, Xtensor, hKtensor, htensor_raw⟩
  refine ⟨Cprime * (Ktensor / cφ) * Cmass,
    max (max Xprime (max Xtensor XmassLower)) (max XmassUpper (Real.exp 1)),
    ?_, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hCprime_pos.le (div_nonneg hKtensor.le hcφ.le))
      hCmass.le
  · intro X hX D hD hD_sqf hD_odd hDwide
    exact
      exactDivisorEventCarriers_logCube_bound_on_YU
        P a Cprime Ktensor cφ Cmass Xprime (max Xtensor XmassLower)
        XmassUpper hCprime_pos.le hKtensor.le hcφ hprime
        (by
          intro X hX D hD hD_sqf hD_odd hDwide
          have hXtensor : Xtensor ≤ X :=
            le_trans (le_max_left _ _) hX
          have hXmassLower : XmassLower ≤ X :=
            le_trans (le_max_right _ _) hX
          exact
            htensor_raw X hXtensor D hD hD_sqf hD_odd hDwide
              (a X D)
              (fun s hs hsD => hresidue X D s hs hsD)
              cφ hcφ ((hmassφ X hXmassLower).1))
        (fun X hX => (hmass_upper X hX).2)
        X hX D hD hD_sqf hD_odd hDwide

/-- Long-window replacement for the legacy unrestricted ordinary-upper event
bridge.  Every squarefree estimate used here is applied only to the actual
phi-progression windows. -/
theorem exactDivisorEventCarriers_logCube_bound_on_YU_of_sqfRecipLower_ordinaryUpperLong_wide
    {P : Params}
    (hlower : PhiProgressionSqfRecipLower P)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpperLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ)
    (hordinaryYU :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ)
    (a : ℝ → ℕ → ℕ → ℕ)
    (hresidue : ∀ X : ℝ, ∀ D s : ℕ,
      s ∈ exactDivisorSRange P X → Nat.Coprime s D →
        Nat.Coprime (a X D s) D) :
    ∃ Kev X₀ : ℝ, 0 ≤ Kev ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P a X D
            ≤ Kev * (logCube X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P a X D
            ≤ Kev * (logCube X / (D : ℝ)) := by
  rcases Inputs.primeRecipWindow_upper_unconditional P with
    ⟨Cprime, Xprime, hCprime_pos, hprime⟩
  rcases exactDivisorMPhiMassRaw_logSq_of_sqfRecipLower_ordinaryUpperLong_wide
      (P := P) hlower hupper with
    ⟨_cmass_raw, Cmass, XmassUpper, _hcmass_raw, hCmass, hmass_upper⟩
  rcases exactDivisorMPhiMassFiber_comparable_to_shape_of_fiberAverageTwoSided
      (ExactDivisorMPhiFiberAverageTwoSided_of_sqfRecipLower_and_ordinaryUpperLong_wide
        hlower hupper) with
    ⟨cφ, _Cφ, XmassLower, hcφ, _hCφ, hmassφ⟩
  rcases exactDivisorMPhiTensorFiberCoprime_le_massRaw_over_modulus_of_ordinaryUpper_wide
      hordinaryYU with
    ⟨Ktensor, Xtensor, hKtensor, htensor_raw⟩
  refine ⟨Cprime * (Ktensor / cφ) * Cmass,
    max (max Xprime (max Xtensor XmassLower)) (max XmassUpper (Real.exp 1)),
    ?_, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hCprime_pos.le (div_nonneg hKtensor.le hcφ.le))
      hCmass.le
  · intro X hX D hD hD_sqf hD_odd hDwide
    exact
      exactDivisorEventCarriers_logCube_bound_on_YU
        P a Cprime Ktensor cφ Cmass Xprime (max Xtensor XmassLower)
        XmassUpper hCprime_pos.le hKtensor.le hcφ hprime
        (by
          intro X hX D hD hD_sqf hD_odd hDwide
          have hXtensor : Xtensor ≤ X := le_trans (le_max_left _ _) hX
          have hXmassLower : XmassLower ≤ X := le_trans (le_max_right _ _) hX
          exact
            htensor_raw X hXtensor D hD hD_sqf hD_odd hDwide
              (a X D) (fun s hs hsD => hresidue X D s hs hsD)
              cφ hcφ ((hmassφ X hXmassLower).1))
        (fun X hX => (hmass_upper X hX).2)
        X hX D hD hD_sqf hD_odd hDwide

/-- Canonical inverse-square residue-selector version of
`exactDivisorEventCarriers_logCube_bound_on_YU_of_sqfRecipLower_ordinaryUpper_wide`. -/
theorem exactDivisorEventCarriers_logCube_bound_on_YU_inverseSquare_of_sqfRecipLower_ordinaryUpper_wide
    {P : Params}
    (hlower : PhiProgressionSqfRecipLower P)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (hordinaryYU :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ) :
    ∃ Kev X₀ : ℝ, 0 ≤ Kev ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P exactDivisorInverseSquareResidueSelector X D
            ≤ Kev * (logCube X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P exactDivisorInverseSquareResidueSelector X D
            ≤ Kev * (logCube X / (D : ℝ)) :=
  exactDivisorEventCarriers_logCube_bound_on_YU_of_sqfRecipLower_ordinaryUpper_wide
    hlower hupper hordinaryYU exactDivisorInverseSquareResidueSelector
    (fun X D s _hs hsD =>
      exactDivisorInverseSquareResidueSelector_coprime X D s hsD)

/-- Twisted inverse-square residue-selector version of
`exactDivisorEventCarriers_logCube_bound_on_YU_of_sqfRecipLower_ordinaryUpper_wide`. -/
theorem exactDivisorEventCarriers_logCube_bound_on_YU_twistedInverseSquare_of_sqfRecipLower_ordinaryUpper_wide
    {P : Params} (c : ℝ → ℕ → ℕ)
    (hc : ∀ X D, 0 < D → Nat.Coprime (c X D) D)
    (hlower : PhiProgressionSqfRecipLower P)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (hordinaryYU :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ) :
    ∃ Kev X₀ : ℝ, 0 ≤ Kev ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P
            (exactDivisorTwistedInverseSquareResidueSelector c) X D
            ≤ Kev * (logCube X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P
            (exactDivisorTwistedInverseSquareResidueSelector c) X D
            ≤ Kev * (logCube X / (D : ℝ)) :=
  exactDivisorEventCarriers_logCube_bound_on_YU_of_sqfRecipLower_ordinaryUpper_wide
    hlower hupper hordinaryYU
    (exactDivisorTwistedInverseSquareResidueSelector c)
    (fun X D s _hs hsD =>
      exactDivisorTwistedInverseSquareResidueSelector_coprime c hc X D s hsD)

/-- Paper-range exact-divisor event carrier bound for the canonical
inverse-square residue selector.

This discharges the finite residue-map side condition in
`exactDivisorEventCarriers_logCube_bound_on_YU_of_ordinaryUpper_wide`: the
selected inverse-square residue is reduced modulo `D` on every coprime
`s`-fiber by `exactDivisorInverseSquareResidueSelector_coprime`. -/
theorem exactDivisorEventCarriers_logCube_bound_on_YU_inverseSquare_of_ordinaryUpper_wide
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (hordinaryYU :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ) :
    ∃ Kev X₀ : ℝ, 0 ≤ Kev ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P exactDivisorInverseSquareResidueSelector X D
            ≤ Kev * (logCube X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P exactDivisorInverseSquareResidueSelector X D
            ≤ Kev * (logCube X / (D : ℝ)) :=
  exactDivisorEventCarriers_logCube_bound_on_YU_of_ordinaryUpper_wide
    hlower hupper hordinaryYU exactDivisorInverseSquareResidueSelector
    (fun X D s _hs hsD =>
      exactDivisorInverseSquareResidueSelector_coprime X D s hsD)

/-- Paper-range exact-divisor event carrier bound for a fixed reduced
twist of the inverse-square residue selector.

This is the twisted analogue of
`exactDivisorEventCarriers_logCube_bound_on_YU_inverseSquare_of_ordinaryUpper_wide`:
the only extra local side condition is that the twist `c X D` is reduced
modulo each positive `D`. -/
theorem exactDivisorEventCarriers_logCube_bound_on_YU_twistedInverseSquare_of_ordinaryUpper_wide
    {P : Params} (c : ℝ → ℕ → ℕ)
    (hc : ∀ X D, 0 < D → Nat.Coprime (c X D) D)
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (hordinaryYU :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ) :
    ∃ Kev X₀ : ℝ, 0 ≤ Kev ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P
            (exactDivisorTwistedInverseSquareResidueSelector c) X D
            ≤ Kev * (logCube X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P
            (exactDivisorTwistedInverseSquareResidueSelector c) X D
            ≤ Kev * (logCube X / (D : ℝ)) :=
  exactDivisorEventCarriers_logCube_bound_on_YU_of_ordinaryUpper_wide
    hlower hupper hordinaryYU
    (exactDivisorTwistedInverseSquareResidueSelector c)
    (fun X D s _hs hsD =>
      exactDivisorTwistedInverseSquareResidueSelector_coprime c hc X D s hsD)

/-- Wide-lower version of
`exactDivisorEventCarriers_logCube_bound_on_YU_of_ordinaryUpper_wide`. -/
theorem exactDivisorEventCarriers_logCube_bound_on_YU_of_ordinaryUpper_wideLower_wide
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (hordinaryYU :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ)
    (a : ℝ → ℕ → ℕ → ℕ)
    (hresidue : ∀ X : ℝ, ∀ D s : ℕ,
      s ∈ exactDivisorSRange P X → Nat.Coprime s D →
        Nat.Coprime (a X D s) D) :
    ∃ Kev X₀ : ℝ, 0 ≤ Kev ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P a X D
            ≤ Kev * (logCube X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P a X D
            ≤ Kev * (logCube X / (D : ℝ)) :=
  exactDivisorEventCarriers_logCube_bound_on_YU_of_ordinaryUpper_wide
    (OrdinarySquarefreeProgressionCoprimeDensityLowerLong_eta_of_wide hlower)
    hupper hordinaryYU a hresidue

/-- Wide-lower paper-range exact-divisor event carrier bound for the canonical
inverse-square residue selector. -/
theorem exactDivisorEventCarriers_logCube_bound_on_YU_inverseSquare_of_ordinaryUpper_wideLower_wide
    {P : Params}
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (hordinaryYU :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ) :
    ∃ Kev X₀ : ℝ, 0 ≤ Kev ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P exactDivisorInverseSquareResidueSelector X D
            ≤ Kev * (logCube X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P exactDivisorInverseSquareResidueSelector X D
            ≤ Kev * (logCube X / (D : ℝ)) :=
  exactDivisorEventCarriers_logCube_bound_on_YU_inverseSquare_of_ordinaryUpper_wide
    (OrdinarySquarefreeProgressionCoprimeDensityLowerLong_eta_of_wide hlower)
    hupper hordinaryYU

/-- Wide-lower paper-range exact-divisor event carrier bound for a fixed
reduced twist of the inverse-square residue selector. -/
theorem exactDivisorEventCarriers_logCube_bound_on_YU_twistedInverseSquare_of_ordinaryUpper_wideLower_wide
    {P : Params} (c : ℝ → ℕ → ℕ)
    (hc : ∀ X D, 0 < D → Nat.Coprime (c X D) D)
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (hordinaryYU :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ) :
    ∃ Kev X₀ : ℝ, 0 ≤ Kev ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P
            (exactDivisorTwistedInverseSquareResidueSelector c) X D
            ≤ Kev * (logCube X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P
            (exactDivisorTwistedInverseSquareResidueSelector c) X D
            ≤ Kev * (logCube X / (D : ℝ)) :=
  exactDivisorEventCarriers_logCube_bound_on_YU_twistedInverseSquare_of_ordinaryUpper_wide
    c hc
    (OrdinarySquarefreeProgressionCoprimeDensityLowerLong_eta_of_wide hlower)
    hupper hordinaryYU

/-- Paper-range exact-divisor event tensor with the local carrier hypotheses
discharged from the ordinary-squarefree progression package.

Unlike the unrestricted event wrapper above, this theorem states the event
conclusion only on the manuscript range `D` squarefree, odd, and `D≤YU`; on
that range the `M_φ` tensor estimate is supplied by the wide
ordinary-squarefree progression upper estimate. -/
theorem
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long_paper_range_of_ordinaryUpper_wide
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (hordinaryYU :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (a : ℝ → ℕ → ℕ → ℕ)
    (hresidue : ∀ X : ℝ, ∀ D s : ℕ,
      s ∈ exactDivisorSRange P X → Nat.Coprime s D →
        Nat.Coprime (a X D s) D) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) := by
  rcases fixedNat_le_rpow_eventually_threshold Mr hC₀ with ⟨XMr, hMr⟩
  have hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape :=
    sigmaSmallAverage_factor_asymp_standard P s hs
  have hrough : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape :=
    roughFactor_asymp_eventual_modulus P a₀ b₀ c₁w C₀ ha₀ hab hc₁w Mr aw bw
      haw hawltbw hbw hgapw XMr hMr
  rcases exactDivisorEventCarriers_logCube_bound_on_YU_of_ordinaryUpper_wide
      hlower hupper hordinaryYU a hresidue with
    ⟨Kassemb, XB, hKassemb, hassemb⟩
  rcases
      mass_law_and_event_tensor_on_range P b
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        (fun X => Inputs.roughRecip X Mr aw bw)
        hSig hrough
        (exactDivisorEventDoubleCarrier P a)
        (exactDivisorEventSingleCarrier P a)
        (fun X D => Squarefree D ∧ Odd D ∧ (D : ℝ) ≤ YScale P X * UScale X)
        Kassemb XB hKassemb
        (by
          intro X hX D hD hR
          rcases hR with ⟨hD_sqf, hD_odd, hDwide⟩
          exact hassemb X hX D hD hD_sqf hD_odd hDwide) with
    ⟨c₁, hc₁, c₂, hc₂, Kev, hKev, X₀, hmass, hevent⟩
  refine ⟨c₁, hc₁, c₂, hc₂, Kev, hKev, X₀, hmass, ?_⟩
  intro X hX D hD hD_sqf hD_odd hDwide
  exact hevent X hX D hD ⟨hD_sqf, hD_odd, hDwide⟩

/-- Paper-range exact-divisor event tensor with the `M_φ` mass lower comparison
discharged from the specialized phi-window squarefree lower carrier.

This is the narrower companion to
`mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long_paper_range_of_ordinaryUpper_wide`:
the event layer no longer asks for the stronger long ordinary-squarefree lower
estimate when the already specialized reciprocal lower target is enough. -/
theorem
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_sqfRecipLower_paper_range_of_ordinaryUpper_wide
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hlower : PhiProgressionSqfRecipLower P)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (hordinaryYU :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (a : ℝ → ℕ → ℕ → ℕ)
    (hresidue : ∀ X : ℝ, ∀ D s : ℕ,
      s ∈ exactDivisorSRange P X → Nat.Coprime s D →
        Nat.Coprime (a X D s) D) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) := by
  rcases fixedNat_le_rpow_eventually_threshold Mr hC₀ with ⟨XMr, hMr⟩
  have hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape :=
    sigmaSmallAverage_factor_asymp_standard P s hs
  have hrough : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape :=
    roughFactor_asymp_eventual_modulus P a₀ b₀ c₁w C₀ ha₀ hab hc₁w Mr aw bw
      haw hawltbw hbw hgapw XMr hMr
  rcases exactDivisorEventCarriers_logCube_bound_on_YU_of_sqfRecipLower_ordinaryUpper_wide
      hlower hupper hordinaryYU a hresidue with
    ⟨Kassemb, XB, hKassemb, hassemb⟩
  rcases
      mass_law_and_event_tensor_on_range P b
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        (fun X => Inputs.roughRecip X Mr aw bw)
        hSig hrough
        (exactDivisorEventDoubleCarrier P a)
        (exactDivisorEventSingleCarrier P a)
        (fun X D => Squarefree D ∧ Odd D ∧ (D : ℝ) ≤ YScale P X * UScale X)
        Kassemb XB hKassemb
        (by
          intro X hX D hD hR
          rcases hR with ⟨hD_sqf, hD_odd, hDwide⟩
          exact hassemb X hX D hD hD_sqf hD_odd hDwide) with
    ⟨c₁, hc₁, c₂, hc₂, Kev, hKev, X₀, hmass, hevent⟩
  refine ⟨c₁, hc₁, c₂, hc₂, Kev, hKev, X₀, hmass, ?_⟩
  intro X hX D hD hD_sqf hD_odd hDwide
  exact hevent X hX D hD ⟨hD_sqf, hD_odd, hDwide⟩

/-- Long-window version of the specialized squarefree-lower paper-range event
assembly.  This is the route used by the no-hypothesis standard wrapper. -/
theorem
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_sqfRecipLower_paper_range_of_ordinaryUpperLong_wide
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hlower : PhiProgressionSqfRecipLower P)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpperLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ)
    (hordinaryYU :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (a : ℝ → ℕ → ℕ → ℕ)
    (hresidue : ∀ X : ℝ, ∀ D s : ℕ,
      s ∈ exactDivisorSRange P X → Nat.Coprime s D →
        Nat.Coprime (a X D s) D) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) := by
  rcases fixedNat_le_rpow_eventually_threshold Mr hC₀ with ⟨XMr, hMr⟩
  have hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X)) sigmaShape :=
    sigmaSmallAverage_factor_asymp_standard P s hs
  have hrough : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape :=
    roughFactor_asymp_eventual_modulus P a₀ b₀ c₁w C₀ ha₀ hab hc₁w Mr aw bw
      haw hawltbw hbw hgapw XMr hMr
  rcases
      exactDivisorEventCarriers_logCube_bound_on_YU_of_sqfRecipLower_ordinaryUpperLong_wide
        hlower hupper hordinaryYU a hresidue with
    ⟨Kassemb, XB, hKassemb, hassemb⟩
  rcases
      mass_law_and_event_tensor_on_range P b
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        (fun X => Inputs.roughRecip X Mr aw bw)
        hSig hrough
        (exactDivisorEventDoubleCarrier P a)
        (exactDivisorEventSingleCarrier P a)
        (fun X D => Squarefree D ∧ Odd D ∧ (D : ℝ) ≤ YScale P X * UScale X)
        Kassemb XB hKassemb
        (by
          intro X hX D hD hR
          rcases hR with ⟨hD_sqf, hD_odd, hDwide⟩
          exact hassemb X hX D hD hD_sqf hD_odd hDwide) with
    ⟨c₁, hc₁, c₂, hc₂, Kev, hKev, X₀, hmass, hevent⟩
  refine ⟨c₁, hc₁, c₂, hc₂, Kev, hKev, X₀, hmass, ?_⟩
  intro X hX D hD hD_sqf hD_odd hDwide
  exact hevent X hX D hD ⟨hD_sqf, hD_odd, hDwide⟩

/-- Paper-range exact-divisor event tensor with the ordinary-squarefree
progression inputs discharged by their cited standard theorem.

The remaining hypotheses are the paper's fixed rough-window parameters, the
tensor-range squarefree upper estimate, and the finite reduced-residue selector
condition. The long-window upper estimate is obtained by restricting the
tensor-range estimate. -/
theorem
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_sqfRecipLower_paper_range_standard_ordinarySquarefree
    (P : Params)
    [hYU : Fact (OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
      (P.lam - P.θ) P.θ P.θ)]
    (b s : ℕ) (hs : 1 ≤ s)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (a : ℝ → ℕ → ℕ → ℕ)
    (hresidue : ∀ X : ℝ, ∀ D s : ℕ,
      s ∈ exactDivisorSRange P X → Nat.Coprime s D →
        Nat.Coprime (a X D s) D) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_sqfRecipLower_paper_range_of_ordinaryUpperLong_wide
    P b s hs
    (PhiProgressionSqfRecipLower_of_standard_ordinarySquarefree P)
    (OrdinarySquarefreeProgressionCoprimeDensityUpperLong_of_YU hYU.out)
    hYU.out
    a₀ b₀ c₁w C₀ ha₀ hab hc₁w hC₀ Mr aw bw haw hawltbw hbw hgapw
    a hresidue

/-- Canonical inverse-square paper-range event tensor through the specialized
phi-window squarefree lower route. -/
theorem
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_sqfRecipLower_paper_range_inverseSquare_of_ordinaryUpper_wide
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hlower : PhiProgressionSqfRecipLower P)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (hordinaryYU :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P exactDivisorInverseSquareResidueSelector X D
            ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P exactDivisorInverseSquareResidueSelector X D
            ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) := by
  exact
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_sqfRecipLower_paper_range_of_ordinaryUpper_wide
      P b s hs hlower hupper hordinaryYU a₀ b₀ c₁w C₀ ha₀ hab hc₁w hC₀ Mr aw bw
      haw hawltbw hbw hgapw exactDivisorInverseSquareResidueSelector
      (fun X D s hs hsD =>
        exactDivisorInverseSquareResidueSelector_coprime X D s hsD)

/-- Canonical inverse-square paper-range event tensor with the
ordinary-squarefree hypotheses discharged by the cited standard theorem. -/
theorem
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_sqfRecipLower_paper_range_inverseSquare_standard_ordinarySquarefree
    (P : Params)
    [Fact (OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
      (P.lam - P.θ) P.θ P.θ)]
    (b s : ℕ) (hs : 1 ≤ s)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P exactDivisorInverseSquareResidueSelector X D
            ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P exactDivisorInverseSquareResidueSelector X D
            ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_sqfRecipLower_paper_range_standard_ordinarySquarefree
    P b s hs a₀ b₀ c₁w C₀ ha₀ hab hc₁w hC₀ Mr aw bw
    haw hawltbw hbw hgapw exactDivisorInverseSquareResidueSelector
    (fun X D s _hs hsD =>
      exactDivisorInverseSquareResidueSelector_coprime X D s hsD)

/-- Twisted inverse-square paper-range event tensor through the specialized
phi-window squarefree lower route. -/
theorem
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_sqfRecipLower_paper_range_twistedInverseSquare_of_ordinaryUpper_wide
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hlower : PhiProgressionSqfRecipLower P)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (hordinaryYU :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (c : ℝ → ℕ → ℕ)
    (hc : ∀ X D, 0 < D → Nat.Coprime (c X D) D) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P (exactDivisorTwistedInverseSquareResidueSelector c) X D
            ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P (exactDivisorTwistedInverseSquareResidueSelector c) X D
            ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) := by
  exact
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_sqfRecipLower_paper_range_of_ordinaryUpper_wide
      P b s hs hlower hupper hordinaryYU a₀ b₀ c₁w C₀ ha₀ hab hc₁w hC₀ Mr aw bw
      haw hawltbw hbw hgapw (exactDivisorTwistedInverseSquareResidueSelector c)
      (fun X D s hs hsD =>
        exactDivisorTwistedInverseSquareResidueSelector_coprime c hc X D s hsD)

/-- Twisted inverse-square paper-range event tensor with the ordinary-squarefree
hypotheses discharged by the cited standard theorem. -/
theorem
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_sqfRecipLower_paper_range_twistedInverseSquare_standard_ordinarySquarefree
    (P : Params)
    [Fact (OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
      (P.lam - P.θ) P.θ P.θ)]
    (b s : ℕ) (hs : 1 ≤ s)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (c : ℝ → ℕ → ℕ)
    (hc : ∀ X D, 0 < D → Nat.Coprime (c X D) D) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P (exactDivisorTwistedInverseSquareResidueSelector c) X D
            ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P (exactDivisorTwistedInverseSquareResidueSelector c) X D
            ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_sqfRecipLower_paper_range_standard_ordinarySquarefree
    P b s hs a₀ b₀ c₁w C₀ ha₀ hab hc₁w hC₀ Mr aw bw
    haw hawltbw hbw hgapw (exactDivisorTwistedInverseSquareResidueSelector c)
    (fun X D s _hs hsD =>
      exactDivisorTwistedInverseSquareResidueSelector_coprime c hc X D s hsD)

/-- Paper-range exact-divisor event tensor for the canonical inverse-square
residue selector.

This removes the finite residue-map side condition from
`..._paper_range_of_ordinaryUpper_wide` for the canonical reduced residue model:
the selector is proved reduced modulo `D` internally. -/
theorem
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long_paper_range_inverseSquare_of_ordinaryUpper_wide
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (hordinaryYU :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P exactDivisorInverseSquareResidueSelector X D
            ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P exactDivisorInverseSquareResidueSelector X D
            ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) := by
  exact
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long_paper_range_of_ordinaryUpper_wide
      P b s hs hlower hupper hordinaryYU a₀ b₀ c₁w C₀ ha₀ hab hc₁w hC₀ Mr aw bw
      haw hawltbw hbw hgapw exactDivisorInverseSquareResidueSelector
      (fun X D s hs hsD =>
        exactDivisorInverseSquareResidueSelector_coprime X D s hsD)

/-- Paper-range exact-divisor event tensor for the manuscript-shaped reduced
residue `c·s⁻²`.

This is the same bridge as the canonical inverse-square route, but with the
fixed reduced multiplier that appears in the exact-divisor residue model.  The
only extra local hypothesis is the natural one: the multiplier itself is
reduced modulo each positive `D`. -/
theorem
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long_paper_range_twistedInverseSquare_of_ordinaryUpper_wide
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.η) P.θ (P.θ - P.lam - P.η) P.η)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (hordinaryYU :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (c : ℝ → ℕ → ℕ)
    (hc : ∀ X D, 0 < D → Nat.Coprime (c X D) D) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P (exactDivisorTwistedInverseSquareResidueSelector c) X D
            ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P (exactDivisorTwistedInverseSquareResidueSelector c) X D
            ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) := by
  exact
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long_paper_range_of_ordinaryUpper_wide
      P b s hs hlower hupper hordinaryYU a₀ b₀ c₁w C₀ ha₀ hab hc₁w hC₀ Mr aw bw
      haw hawltbw hbw hgapw (exactDivisorTwistedInverseSquareResidueSelector c)
      (fun X D s hs hsD =>
        exactDivisorTwistedInverseSquareResidueSelector_coprime c hc X D s hsD)

/-- Wide-lower version of the paper-range exact-divisor event tensor route. -/
theorem
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long_paper_range_of_ordinaryUpper_wideLower_wide
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (hordinaryYU :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (a : ℝ → ℕ → ℕ → ℕ)
    (hresidue : ∀ X : ℝ, ∀ D s : ℕ,
      s ∈ exactDivisorSRange P X → Nat.Coprime s D →
        Nat.Coprime (a X D s) D) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P a X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long_paper_range_of_ordinaryUpper_wide
    P b s hs
    (OrdinarySquarefreeProgressionCoprimeDensityLowerLong_eta_of_wide hlower)
    hupper hordinaryYU a₀ b₀ c₁w C₀ ha₀ hab hc₁w hC₀ Mr aw bw
    haw hawltbw hbw hgapw a hresidue

/-- Wide-lower paper-range event tensor for the canonical inverse-square
residue selector. -/
theorem
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long_paper_range_inverseSquare_of_ordinaryUpper_wideLower_wide
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (hordinaryYU :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P exactDivisorInverseSquareResidueSelector X D
            ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P exactDivisorInverseSquareResidueSelector X D
            ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long_paper_range_inverseSquare_of_ordinaryUpper_wide
    P b s hs
    (OrdinarySquarefreeProgressionCoprimeDensityLowerLong_eta_of_wide hlower)
    hupper hordinaryYU a₀ b₀ c₁w C₀ ha₀ hab hc₁w hC₀ Mr aw bw
    haw hawltbw hbw hgapw

/-- Wide-lower paper-range event tensor for a fixed reduced twist of the
inverse-square residue selector. -/
theorem
    mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long_paper_range_twistedInverseSquare_of_ordinaryUpper_wideLower_wide
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hlower :
      OrdinarySquarefreeProgressionCoprimeDensityLowerLong
        (P.lam - P.θ) P.θ (P.θ - P.lam - P.η) P.θ)
    (hupper :
      OrdinarySquarefreeProgressionCoprimeDensityUpper
        (P.lam - P.θ) P.θ P.θ)
    (hordinaryYU :
      OrdinarySquarefreeProgressionCoprimeDensityUpperYU P
        (P.lam - P.θ) P.θ P.θ)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hC₀ : 0 < C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (c : ℝ → ℕ → ℕ)
    (hc : ∀ X D, 0 < D → Nat.Coprime (c X D) D) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D → Squarefree D → Odd D →
        (D : ℝ) ≤ YScale P X * UScale X →
        exactDivisorEventDoubleCarrier P (exactDivisorTwistedInverseSquareResidueSelector c) X D
            ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ exactDivisorEventSingleCarrier P (exactDivisorTwistedInverseSquareResidueSelector c) X D
            ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_concrete_exactDivisor_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_auto_modulus_auto_prime_auto_mphiMass_long_paper_range_twistedInverseSquare_of_ordinaryUpper_wide
    P b s hs
    (OrdinarySquarefreeProgressionCoprimeDensityLowerLong_eta_of_wide hlower)
    hupper hordinaryYU a₀ b₀ c₁w C₀ ha₀ hab hc₁w hC₀ Mr aw bw
    haw hawltbw hbw hgapw c hc

/-- Event-tensor bundle from explicit density replacements for the two remaining
analytic inputs.

This is the event-level companion to
`mass_law_from_density_inputs_fixed_slant_smallDivisorAverage`: the same
concrete `smallDivisorAverage` and `roughRecip` carriers are used, and both
factor asymptotics are discharged from explicit density hypotheses rather than
the named standard inputs. -/
theorem mass_law_and_event_tensor_from_density_inputs_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hsmall : ∃ δ > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      δ * Inputs.oddSquarefreeRecipNat (2 ^ k)
        ≤ Inputs.oddSquarefreeTotientNat (2 ^ k))
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hrough :
      ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        ∀ (M : ℕ), (M : ℝ) ≤ X ^ C₀ →
        ∀ t : ℝ, X ^ a₀ ≤ t → t ≤ 2 * X ^ b₀ → 0 < t →
          0 < Real.log (zScale X) ∧
            c / Real.log (zScale X) ≤ Inputs.roughDyadicDensity X M t ∧
            Inputs.roughDyadicDensity X M t ≤ C / Real.log (zScale X))
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) := by
  have hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape :=
    sigmaSmallAverage_factor_asymp_of_oddSquarefreeTotientNat_recip_density
      P s hs hsmall
  have hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape :=
    roughFactor_asymp_of_roughDyadicDensity_bound P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hrough
  exact mass_law_and_event_tensor P b
    (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
      (fun X => Inputs.smallDivisorAverage P X))
    (fun X => Inputs.roughRecip X Mr aw bw) hSig hR
    B Bsingle Kassemb XB hKassemb hassemb

/-- Event-tensor bridge from any packaged small-side factor and any packaged
rough-side factor for the concrete fixed-slant carriers. -/
theorem mass_law_and_event_tensor_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ) (Mr : ℕ) (aw bw : ℝ)
    (hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape)
    (hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor P b
    (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
      (fun X => Inputs.smallDivisorAverage P X))
    (fun X => Inputs.roughRecip X Mr aw bw) hSig hR
    B Bsingle Kassemb XB hKassemb hassemb

/-- Event-tensor bundle from standard small side, bounded Mertens defect, and
normalized rough-count discrepancy. -/
theorem mass_law_and_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_of_defectIsBigOOne_and_normalized
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hmertens : Inputs.PrimeRecipSharpMertensNatDefectIsBigOOne)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw
    (sigmaSmallAverage_factor_asymp_standard P s hs)
    (roughFactor_asymp_of_defectIsBigOOne_and_normalized P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hmertens hdisc)
    B Bsingle Kassemb XB hKassemb hassemb

/-- Event-tensor bundle from standard small side, the one-sided Mertens upper
bound actually needed by the rough Euler-product lower half, and normalized
rough-count discrepancy. -/
theorem mass_law_and_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_of_defectEventuallyUpperBound_and_normalized
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hmertens : Inputs.PrimeRecipSharpMertensNatDefectEventuallyUpperBound)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw
    (sigmaSmallAverage_factor_asymp_standard P s hs)
    (roughFactor_asymp_of_defectEventuallyUpperBound_and_normalized P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hmertens hdisc)
    B Bsingle Kassemb XB hKassemb hassemb

/-- Event-tensor bundle from standard small side, the coefficient-one dyadic
prime-reciprocal block formulation of Mertens, and normalized rough-count
discrepancy. -/
theorem mass_law_and_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_of_dyadicBlocksSharpUpperBound_and_normalized
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hmertens : Inputs.PrimeRecipDyadicBlocksSharpUpperBound)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw
    (sigmaSmallAverage_factor_asymp_standard P s hs)
    (roughFactor_asymp_of_dyadicBlocksSharpUpperBound_and_normalized P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hmertens hdisc)
    B Bsingle Kassemb XB hKassemb hassemb

/-- Event-tensor bundle from standard small side, eventual absolute Mertens
control, and normalized rough-count discrepancy. -/
theorem mass_law_and_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_of_eventuallyAbsBound_and_normalized
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hmertens : Inputs.PrimeRecipSharpMertensNatDefectEventuallyAbsBound)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw
    (sigmaSmallAverage_factor_asymp_standard P s hs)
    (roughFactor_asymp_of_eventuallyAbsBound_and_normalized P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hmertens hdisc)
    B Bsingle Kassemb XB hKassemb hassemb

/-- Event-tensor bundle from standard small side, two-sided Mertens control, and
normalized rough-count discrepancy. -/
theorem mass_law_and_event_tensor_from_inputs_fixed_slant_smallDivisorAverage_standard_of_twoSided_and_normalized
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hmertens : Inputs.PrimeRecipSharpMertensNatDefectEventuallyTwoSidedBound)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw
    (sigmaSmallAverage_factor_asymp_standard P s hs)
    (roughFactor_asymp_of_twoSided_and_normalized P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hmertens hdisc)
    B Bsingle Kassemb XB hKassemb hassemb

/-- Event-tensor bridge from any packaged small-side factor and finite
bad-prime main-term dominance on the rough side. -/
theorem mass_law_and_event_tensor_from_small_factor_and_badPrimeProductMainTermDominatesError_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ)
    (hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hrough : Inputs.roughDyadicBadPrimeProductMainTermDominatesErrorBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw hSig
    (roughFactor_asymp_of_badPrimeProductMainTermDominatesError P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hrough)
    B Bsingle Kassemb XB hKassemb hassemb

/-- Event-tensor bridge from any packaged small-side factor and finite
Euler-product/error control on the rough side. -/
theorem mass_law_and_event_tensor_from_small_factor_and_badPrimeEulerProductError_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ)
    (hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hrough : Inputs.roughDyadicBadPrimeEulerProductErrorBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw hSig
    (roughFactor_asymp_of_badPrimeEulerProductError P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hrough)
    B Bsingle Kassemb XB hKassemb hassemb

/-- Event-tensor bridge from any packaged small-side factor and split finite
Euler-product/error control on the rough side. -/
theorem mass_law_and_event_tensor_from_small_factor_and_splitEulerProductError_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ)
    (hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hrough : Inputs.roughDyadicBadPrimeSplitEulerProductErrorBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw hSig
    (roughFactor_asymp_of_splitEulerProductError P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hrough)
    B Bsingle Kassemb XB hKassemb hassemb

/-- Event-tensor bridge from any packaged small-side factor and separated
finite Euler-product/error control on the rough side. -/
theorem mass_law_and_event_tensor_from_small_factor_and_separatedEulerProductError_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ)
    (hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hrough : Inputs.roughDyadicBadPrimeSeparatedEulerProductErrorBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw hSig
    (roughFactor_asymp_of_separatedEulerProductError P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hrough)
    B Bsingle Kassemb XB hKassemb hassemb

/-- Diagnostic event-tensor bridge from any packaged small-side factor, lower finite
Euler-product/error control, and the overstrong quotient-envelope upper premise
on the rough side. -/
theorem mass_law_and_event_tensor_from_small_factor_and_lowerEulerProductError_and_envelope_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ)
    (hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hLower : Inputs.roughDyadicBadPrimeLowerEulerProductErrorBound a₀ b₀ C₀)
    (hEnv : Inputs.roughDyadicBadPrimeProductEnvelopeUpperBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw hSig
    (roughFactor_asymp_of_lowerEulerProductError_and_envelope P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hLower hEnv)
    B Bsingle Kassemb XB hKassemb hassemb

/-- Diagnostic event-tensor bridge from any packaged small-side factor, split finite
Euler-product/error control, and the overstrong quotient-envelope upper premise
on the rough side. -/
theorem mass_law_and_event_tensor_from_small_factor_and_splitLowerEulerProductError_and_envelope_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ)
    (hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape)
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hSplit : Inputs.roughDyadicBadPrimeSplitEulerProductErrorBound a₀ b₀ C₀)
    (hEnv : Inputs.roughDyadicBadPrimeProductEnvelopeUpperBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw hSig
    (roughFactor_asymp_of_splitLowerEulerProductError_and_envelope P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hSplit hEnv)
    B Bsingle Kassemb XB hKassemb hassemb

/-- Event-tensor bridge from the small-side density replacement and any
already packaged rough-factor asymptotic.

The four concrete wrappers below instantiate `hR` from finite bad-prime
main-term/error hypotheses, avoiding the primitive-backed standard rough route. -/
theorem mass_law_and_event_tensor_from_small_density_and_rough_factor_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hsmall : ∃ δ > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      δ * Inputs.oddSquarefreeRecipNat (2 ^ k)
        ≤ Inputs.oddSquarefreeTotientNat (2 ^ k))
    (Mr : ℕ) (aw bw : ℝ)
    (hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) := by
  have hSig :
      FactorAsymp
        (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
          (fun X => Inputs.smallDivisorAverage P X))
        sigmaShape :=
    sigmaSmallAverage_factor_asymp_of_oddSquarefreeTotientNat_recip_density
      P s hs hsmall
  exact mass_law_and_event_tensor P b
    (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
      (fun X => Inputs.smallDivisorAverage P X))
    (fun X => Inputs.roughRecip X Mr aw bw) hSig hR
    B Bsingle Kassemb XB hKassemb hassemb

/-- Event-tensor bridge from the defect-gap small-side replacement and any
already packaged rough-factor asymptotic. -/
theorem mass_law_and_event_tensor_from_defectGap_and_rough_factor_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hsmall : Inputs.OddSquarefreeTotientDefectGapBound)
    (Mr : ℕ) (aw bw : ℝ)
    (hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw
    (sigmaSmallAverage_factor_asymp_of_defectGap P s hs hsmall) hR
    B Bsingle Kassemb XB hKassemb hassemb

/-- Event-tensor bridge from the product-lower small-side replacement and any
already packaged rough-factor asymptotic. -/
theorem mass_law_and_event_tensor_from_productLowerBound_and_rough_factor_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hsmall : Inputs.OddSquarefreeTotientProductDyadicLowerBound)
    (Mr : ℕ) (aw bw : ℝ)
    (hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw
    (sigmaSmallAverage_factor_asymp_of_productLowerBound P s hs hsmall) hR
    B Bsingle Kassemb XB hKassemb hassemb

/-- Event-tensor bridge from the product-defect-gap small-side replacement and
any already packaged rough-factor asymptotic. -/
theorem mass_law_and_event_tensor_from_defectProductGap_and_rough_factor_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hsmall : Inputs.OddSquarefreeTotientDefectProductGapBound)
    (Mr : ℕ) (aw bw : ℝ)
    (hR : FactorAsymp (fun X => Inputs.roughRecip X Mr aw bw) roughShape)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_small_factor_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s Mr aw bw
    (sigmaSmallAverage_factor_asymp_of_defectProductGap P s hs hsmall) hR
    B Bsingle Kassemb XB hKassemb hassemb

/-- Event-tensor bundle from small-side density and finite bad-prime main-term
dominance on the rough side. -/
theorem mass_law_and_event_tensor_from_small_density_and_badPrimeProductMainTermDominatesError_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hsmall : ∃ δ > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      δ * Inputs.oddSquarefreeRecipNat (2 ^ k)
        ≤ Inputs.oddSquarefreeTotientNat (2 ^ k))
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hrough : Inputs.roughDyadicBadPrimeProductMainTermDominatesErrorBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_small_density_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s hs hsmall Mr aw bw
    (roughFactor_asymp_of_badPrimeProductMainTermDominatesError P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hrough)
    B Bsingle Kassemb XB hKassemb hassemb

/-- Event-tensor bundle from small-side density and finite Euler-product/error
control on the rough side. -/
theorem mass_law_and_event_tensor_from_small_density_and_badPrimeEulerProductError_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hsmall : ∃ δ > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      δ * Inputs.oddSquarefreeRecipNat (2 ^ k)
        ≤ Inputs.oddSquarefreeTotientNat (2 ^ k))
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hrough : Inputs.roughDyadicBadPrimeEulerProductErrorBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_small_density_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s hs hsmall Mr aw bw
    (roughFactor_asymp_of_badPrimeEulerProductError P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hrough)
    B Bsingle Kassemb XB hKassemb hassemb

/-- Event-tensor bundle from small-side density and split finite
Euler-product/error control on the rough side. -/
theorem mass_law_and_event_tensor_from_small_density_and_splitEulerProductError_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hsmall : ∃ δ > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      δ * Inputs.oddSquarefreeRecipNat (2 ^ k)
        ≤ Inputs.oddSquarefreeTotientNat (2 ^ k))
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hrough : Inputs.roughDyadicBadPrimeSplitEulerProductErrorBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_small_density_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s hs hsmall Mr aw bw
    (roughFactor_asymp_of_splitEulerProductError P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hrough)
    B Bsingle Kassemb XB hKassemb hassemb

/-- Event-tensor bundle from small-side density and separated finite
Euler-product/error control on the rough side. -/
theorem mass_law_and_event_tensor_from_small_density_and_separatedEulerProductError_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hsmall : ∃ δ > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      δ * Inputs.oddSquarefreeRecipNat (2 ^ k)
        ≤ Inputs.oddSquarefreeTotientNat (2 ^ k))
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hrough : Inputs.roughDyadicBadPrimeSeparatedEulerProductErrorBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_small_density_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s hs hsmall Mr aw bw
    (roughFactor_asymp_of_separatedEulerProductError P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hrough)
    B Bsingle Kassemb XB hKassemb hassemb

/-- Diagnostic event-tensor bundle from small-side density, lower finite
Euler-product/error control, and the overstrong quotient-envelope upper premise
on the rough side. -/
theorem mass_law_and_event_tensor_from_small_density_and_lowerEulerProductError_and_envelope_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hsmall : ∃ δ > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      δ * Inputs.oddSquarefreeRecipNat (2 ^ k)
        ≤ Inputs.oddSquarefreeTotientNat (2 ^ k))
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hLower : Inputs.roughDyadicBadPrimeLowerEulerProductErrorBound a₀ b₀ C₀)
    (hEnv : Inputs.roughDyadicBadPrimeProductEnvelopeUpperBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_small_density_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s hs hsmall Mr aw bw
    (roughFactor_asymp_of_lowerEulerProductError_and_envelope P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hLower hEnv)
    B Bsingle Kassemb XB hKassemb hassemb

/-- Diagnostic event-tensor bundle from small-side density, split finite
Euler-product/error control, and the overstrong quotient-envelope upper premise
on the rough side. -/
theorem mass_law_and_event_tensor_from_small_density_and_splitLowerEulerProductError_and_envelope_fixed_slant_smallDivisorAverage
    (P : Params) (b s : ℕ) (hs : 1 ≤ s)
    (hsmall : ∃ δ > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      δ * Inputs.oddSquarefreeRecipNat (2 ^ k)
        ≤ Inputs.oddSquarefreeTotientNat (2 ^ k))
    (a₀ b₀ c₁w C₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁w : 0 < c₁w)
    (hSplit : Inputs.roughDyadicBadPrimeSplitEulerProductErrorBound a₀ b₀ C₀)
    (hEnv : Inputs.roughDyadicBadPrimeProductEnvelopeUpperBound a₀ b₀ C₀)
    (Mr : ℕ) (aw bw : ℝ)
    (haw : a₀ ≤ aw) (hawltbw : aw < bw) (hbw : bw ≤ b₀) (hgapw : c₁w ≤ bw - aw)
    (hMr : ∀ X : ℝ, (Mr : ℝ) ≤ X ^ C₀)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X
            ≤ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
          ∧ muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X
              ≤ c₂ * logCube X)
        ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b
                (sigmaSmallAverageConcrete (fun X => slantLogLength P s X)
                  (fun X => Inputs.smallDivisorAverage P X))
                (fun X => Inputs.roughRecip X Mr aw bw) X / (D : ℝ))) :=
  mass_law_and_event_tensor_from_small_density_and_rough_factor_fixed_slant_smallDivisorAverage
    P b s hs hsmall Mr aw bw
    (roughFactor_asymp_of_splitLowerEulerProductError_and_envelope P a₀ b₀ c₁w C₀
      ha₀ hab hc₁w Mr aw bw haw hawltbw hbw hgapw hMr hSplit hEnv)
    B Bsingle Kassemb XB hKassemb hassemb

end EscAnalytic
