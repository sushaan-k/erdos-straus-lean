import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Tactic
import EscLeanChecks
import EscAnalytic.Core
import EscAnalytic.Inputs
import EscAnalytic.Counting

/-!
# Brun bounds and modular no-hit estimates

This file formalizes, at the **abstract real-variable level**, the four results of
the manuscript §"Brun coefficient bound" / §"base-conditioned CRT no-hit"
in `esc.tex`:

* `thm:Brun` (tex 1776–1830) — the Brun *envelope* consequence
  `∑_{r≤2R} X^r F_r ≤ X^{2R} exp((1+o_K(1)) μ)` of the finite factorial recurrence
  `F_r ≤ μ^r/r!` proved combinatorially in `EscLeanChecks`;
* `prop:mass-dependency-scale` (tex 1831–1869) — the two `o(1)` scale identities
  `μ_b (log Y)/(z log z) = o(1)` and `μ_b ∑_{D} 1/D² = o(1)`, plus the consequence
  `μ_b² ∑_D 1/D² = o(μ_b)`;
* `lem:delta-Delta` (tex 1870–1921) — `δ_b = o(1)` and `Δ_b = o(μ_b)` from the
  event-tensor bounds and the mass law;
* `thm:CRT-nohit` (tex 1922–1948) — the `(1-o(1))` no-hit envelope
  `P(W_b = 0) ≤ exp(-(1-o(1)) μ_b)` at the abstract carrier level, derived from
  the packaged `EscAnalytic.Inputs.suenProb_bound_with_carrier_bounds` envelope
  together with `lem:delta-Delta`.

## Interface conventions

* The Suen-style carrier bound is consumed through
  `EscAnalytic.Inputs.suenProb_bound_with_carrier_bounds`; it is **not**
  re-axiomatized here.  The active Lean interface is an abstract envelope, not a
  formal probability-space model of the CRT events.
* The *paper's own* upstream results that other files establish — the mass law
  `μ_b ≍ (log X)³` (`prop:mu`), the event-tensor bounds (`prop:event-tensor`), the
  appendage bound `ε_X(K) = o_K(1)` (`lem:appendage`), and the raw rough residual
  squarefree tail — appear as explicit hypotheses of the theorems, never as
  axioms. Each theorem below records the resulting conditional deduction.
* Asymptotics are rendered via `Filter.atTop` on `ℝ` (the manuscript variable `X`).
  `f = o(g)` for `g` positive and bounded away from `0` is encoded as
  `Tendsto (fun X => f X / g X) atTop (𝓝 0)`; `f = o(1)` as
  `Tendsto f atTop (𝓝 0)`; `f ≍ g` as a two-sided constant sandwich.
* No new `axiom`s are introduced in this file.
-/

namespace EscAnalytic

open Filter Topology
open scoped BigOperators

/-! ## Part 0. Real-analysis helpers (the genuine inequality content). -/

/-- `(1 + ε)^r ≤ exp (r · ε)` for `ε ≥ 0` (and any `r`): the elementary step that
turns the manuscript's `(1+ε_X(K))^r` factor into `exp{r ε_X(K)}`
(tex 1810–1812). -/
theorem one_add_pow_le_exp_nat_mul {ε : ℝ} (hε : 0 ≤ ε) (r : ℕ) :
    (1 + ε) ^ r ≤ Real.exp ((r : ℝ) * ε) := by
  calc
    (1 + ε) ^ r ≤ (Real.exp ε) ^ r := by
      have h1 : 1 + ε ≤ Real.exp ε := by
        have := Real.add_one_le_exp ε; linarith
      exact pow_le_pow_left₀ (by linarith) h1 r
    _ = Real.exp ((r : ℝ) * ε) := by
      rw [← Real.exp_nat_mul]

/-- Partial exponential series bound `∑_{r∈range n} t^r/r! ≤ exp t` for `t ≥ 0`
(Mathlib `Real.sum_le_exp_of_nonneg`), restated for the envelope step. -/
theorem sum_factorial_le_exp {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ∑ r ∈ Finset.range n, t ^ r / (Nat.factorial r : ℝ) ≤ Real.exp t :=
  Real.sum_le_exp_of_nonneg ht n

/-- Finite Brun envelope from a factorial coefficient bound available only up
to the truncation rank. -/
theorem brun_envelope_of_factorial_bound_up_to
    (F : ℕ → ℝ) (M X : ℝ) (n : ℕ)
    (hM : 0 ≤ M) (hX : 1 ≤ X)
    (hF : ∀ r : ℕ, r ≤ n →
      F r ≤ M ^ r / (Nat.factorial r : ℝ)) :
    (∑ r ∈ Finset.range (n + 1), X ^ r * F r) ≤
      X ^ n * Real.exp M := by
  have hXnonneg : 0 ≤ X := le_trans zero_le_one hX
  calc
    (∑ r ∈ Finset.range (n + 1), X ^ r * F r) ≤
        ∑ r ∈ Finset.range (n + 1),
          X ^ r * (M ^ r / (Nat.factorial r : ℝ)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left
        (hF r (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)))
        (pow_nonneg hXnonneg r)
    _ ≤ X ^ n * ∑ r ∈ Finset.range (n + 1),
        M ^ r / (Nat.factorial r : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hX
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)))
      exact div_nonneg (pow_nonneg hM r) (by positivity)
    _ ≤ X ^ n * Real.exp M :=
      mul_le_mul_of_nonneg_left
        (sum_factorial_le_exp hM (n + 1)) (pow_nonneg hXnonneg n)

/-! ## Part 1. `thm:Brun` — the Brun envelope. -/

/-- **Appendage error from a vanishing Euler-product exponent** (`lem:appendage`,
asymptotic conversion).

The manuscript bounds the one-step increment error by an Euler-product factor
`exp(tail X)-1`, where the exponent is the prime-by-prime appendage tail.  This
lemma isolates the real-analysis part: once that exponent tends to zero, the
appendage error tends to zero.  The arithmetic estimate for the exponent is
kept as an explicit hypothesis. -/
theorem appendage_error_tendsto_zero_of_exp_tail
    (ε tail : ℝ → ℝ)
    (hε_nonneg : ∀ᶠ X in atTop, 0 ≤ ε X)
    (hε_le : ∀ᶠ X in atTop, ε X ≤ Real.exp (tail X) - 1)
    (htail0 : Tendsto tail atTop (𝓝 0)) :
    Tendsto ε atTop (𝓝 0) := by
  have hupper : Tendsto (fun X => Real.exp (tail X) - 1) atTop (𝓝 0) := by
    have hexp : Tendsto (fun X => Real.exp (tail X)) atTop (𝓝 (Real.exp 0)) := by
      exact (Real.continuous_exp.tendsto 0).comp htail0
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
      tendsto_const_nhds
    simpa [Real.exp_zero] using hexp.sub hone
  exact squeeze_zero' hε_nonneg hε_le hupper

/-- **Appendage error from the mass/medium-prime scale** (`lem:appendage`,
paper-scale form).

After the combinatorial appendage count gives an eventual bound of the shape
`ε_X(K) ≤ C_K · μ_b(X) · medScale(X)`, the scale estimate
`μ_b medScale → 0` proves `ε_X(K)=o_K(1)`. -/
theorem appendage_error_tendsto_zero_of_mass_medScale
    (ε μ medScale : ℝ → ℝ) (C : ℝ)
    (hε_nonneg : ∀ᶠ X in atTop, 0 ≤ ε X)
    (hε_le : ∀ᶠ X in atTop, ε X ≤ C * (μ X * medScale X))
    (hmed0 : Tendsto (fun X => μ X * medScale X) atTop (𝓝 0)) :
    Tendsto ε atTop (𝓝 0) := by
  have hupper : Tendsto (fun X => C * (μ X * medScale X)) atTop (𝓝 0) := by
    simpa using hmed0.const_mul C
  exact squeeze_zero' hε_nonneg hε_le hupper

/-- **Brun envelope, abstract factorial form** (`thm:Brun`, tex 1776–1816).

Working over `ℝ`, take the Brun coefficients `F : ℕ → ℝ` satisfying the finite
multiplicative recurrence `r · F_r ≤ μ(1+ε) · F_{r-1}` (the manuscript's
`r F_r ≤ μ(1+ε_X(K)) F_{r-1}`, tex 1800–1806, with `ε = ε_X(K)`), with
`F_0 ≤ 1` and `μ, ε ≥ 0`.  Then for every `X ≥ 1`,
`∑_{r ≤ 2R} X^r F_r ≤ X^{2R} · exp(μ·(1+ε))`.

This is the *real* envelope consequence of the factorial recurrence
`F_r ≤ (μ(1+ε))^r / r!`: bound `∑ X^r F_r ≤ ∑ (Xμ(1+ε))^r/r! ≤ X^{2R}∑ (μ(1+ε))^r/r!`
(the `X ≥ 1` top-power split) and `∑ (μ(1+ε))^r/r! ≤ exp(μ(1+ε))`.  The same
factorial recurrence is proved combinatorially in
`EscLeanChecks.brun_recurrence_iterated_bound_from_mul`; here we reproduce the
real-variable bound directly so the envelope is self-contained over `ℝ`. -/
theorem brun_envelope_factorial
    (F : ℕ → ℝ) (μ ε X : ℝ) (R : ℕ)
    (hμ : 0 ≤ μ) (hε : 0 ≤ ε) (hX : 1 ≤ X)
    (hF0 : F 0 ≤ 1) (_hFnonneg : ∀ r, 0 ≤ F r)
    (hrec : ∀ r : ℕ, 1 ≤ r → (r : ℝ) * F r ≤ (μ * (1 + ε)) * F (r - 1)) :
    (∑ r ∈ Finset.range (2 * R + 1), X ^ r * F r)
      ≤ X ^ (2 * R) * Real.exp (μ * (1 + ε)) := by
  set M : ℝ := μ * (1 + ε) with hM_def
  have hM : 0 ≤ M := by
    have : 0 ≤ 1 + ε := by linarith
    exact mul_nonneg hμ this
  clear_value M
  -- factorial recurrence over ℝ: F_r ≤ M^r / r!
  have hfact : ∀ r : ℕ, F r ≤ M ^ r / (Nat.factorial r : ℝ) := by
    intro r
    induction r with
    | zero => simpa using hF0
    | succ k ih =>
        have hstep := hrec (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
        have hkfac : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by push_cast; ring
        have hpos : (0 : ℝ) < (k + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k
        have hcoef : 0 ≤ M / ((k + 1 : ℕ) : ℝ) := div_nonneg hM (le_of_lt hpos)
        have hmul : (M / ((k + 1 : ℕ) : ℝ)) * F k
            ≤ (M / ((k + 1 : ℕ) : ℝ)) * (M ^ k / (Nat.factorial k : ℝ)) :=
          mul_le_mul_of_nonneg_left ih hcoef
        have hdiv : F (k + 1) ≤ (M / ((k + 1 : ℕ) : ℝ)) * F k := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
          have : F (k + 1) * ((k + 1 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) * F (k + 1) := by
            ring
          rw [this]
          simpa using hstep
        calc
          F (k + 1) ≤ (M / ((k + 1 : ℕ) : ℝ)) * F k := hdiv
          _ ≤ (M / ((k + 1 : ℕ) : ℝ)) * (M ^ k / (Nat.factorial k : ℝ)) := hmul
          _ = M ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) := by
              have hfne : (Nat.factorial k : ℝ) ≠ 0 := by
                exact_mod_cast (Nat.factorial_pos k).ne'
              have hkne : ((k + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hpos
              rw [Nat.factorial_succ]
              push_cast
              field_simp
              ring
  -- weighted sum ≤ factorial series in (X M)
  have hXnonneg : 0 ≤ X := le_trans zero_le_one hX
  have hweighted : (∑ r ∈ Finset.range (2 * R + 1), X ^ r * F r)
      ≤ ∑ r ∈ Finset.range (2 * R + 1), (X * M) ^ r / (Nat.factorial r : ℝ) := by
    apply Finset.sum_le_sum
    intro r _hr
    have hxpow : 0 ≤ X ^ r := pow_nonneg hXnonneg r
    calc
      X ^ r * F r ≤ X ^ r * (M ^ r / (Nat.factorial r : ℝ)) :=
        mul_le_mul_of_nonneg_left (hfact r) hxpow
      _ = (X * M) ^ r / (Nat.factorial r : ℝ) := by
        rw [mul_pow]; rw [mul_div_assoc]
  -- top-power split: (X M)^r / r! ≤ X^{2R} · M^r / r! for r ≤ 2R, since X ≥ 1
  have htop : (∑ r ∈ Finset.range (2 * R + 1), (X * M) ^ r / (Nat.factorial r : ℝ))
      ≤ X ^ (2 * R) * ∑ r ∈ Finset.range (2 * R + 1), M ^ r / (Nat.factorial r : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    have hrle : r ≤ 2 * R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have hxr_le : X ^ r ≤ X ^ (2 * R) := pow_le_pow_right₀ hX hrle
    have hfne : (0 : ℝ) < (Nat.factorial r : ℝ) := by exact_mod_cast Nat.factorial_pos r
    have hMr : 0 ≤ M ^ r := pow_nonneg hM r
    have heq : (X * M) ^ r / (Nat.factorial r : ℝ)
        = X ^ r * (M ^ r / (Nat.factorial r : ℝ)) := by
      rw [mul_pow, mul_div_assoc]
    rw [heq]
    apply mul_le_mul_of_nonneg_right hxr_le
    exact div_nonneg hMr (le_of_lt hfne)
  -- factorial series ≤ exp M
  have hexp : (∑ r ∈ Finset.range (2 * R + 1), M ^ r / (Nat.factorial r : ℝ))
      ≤ Real.exp M := sum_factorial_le_exp hM (2 * R + 1)
  have hXpow_nonneg : 0 ≤ X ^ (2 * R) := pow_nonneg hXnonneg (2 * R)
  calc
    (∑ r ∈ Finset.range (2 * R + 1), X ^ r * F r)
        ≤ ∑ r ∈ Finset.range (2 * R + 1), (X * M) ^ r / (Nat.factorial r : ℝ) := hweighted
    _ ≤ X ^ (2 * R) * ∑ r ∈ Finset.range (2 * R + 1), M ^ r / (Nat.factorial r : ℝ) := htop
    _ ≤ X ^ (2 * R) * Real.exp M := mul_le_mul_of_nonneg_left hexp hXpow_nonneg

/-- **Brun envelope, `(1+o_K(1))` form** (`thm:Brun`, tex 1810–1815).

The exponent `μ(1+ε)` of `brun_envelope_factorial` is exactly the manuscript's
`exp{(1+o_K(1))μ}` once `ε = ε_X(K) = o_K(1)`.  Here we record the clean
restatement: for `ε ≥ 0` the envelope is
`∑_{r ≤ 2R} X^r F_r ≤ X^{2R} exp((1 + ε) μ)`, and as `ε → 0` (the appendage
bound `lem:appendage`) the factor is `exp{(1+o(1))μ}`. -/
theorem brun_envelope_one_plus_eps
    (F : ℕ → ℝ) (μ ε X : ℝ) (R : ℕ)
    (hμ : 0 ≤ μ) (hε : 0 ≤ ε) (hX : 1 ≤ X)
    (hF0 : F 0 ≤ 1) (hFnonneg : ∀ r, 0 ≤ F r)
    (hrec : ∀ r : ℕ, 1 ≤ r → (r : ℝ) * F r ≤ (μ * (1 + ε)) * F (r - 1)) :
    (∑ r ∈ Finset.range (2 * R + 1), X ^ r * F r)
      ≤ X ^ (2 * R) * Real.exp ((1 + ε) * μ) := by
  have h := brun_envelope_factorial F μ ε X R hμ hε hX hF0 hFnonneg hrec
  rwa [mul_comm μ (1 + ε)] at h

/-- **Brun envelope for finite elementary-symmetric coefficients.**

This composes the finite Brun recurrence already checked in `EscLeanChecks` for
the elementary-symmetric coefficient carrier with the real envelope
`brun_envelope_factorial`.  Thus the paper-facing Brun route can consume the
actual finite coefficient model rather than a free recurrence hypothesis:
nonnegative rational weights with total mass at most `M` satisfy
`∑_{r≤2R} X^r e_r ≤ X^{2R} exp(M)`.
-/
theorem brun_envelope_elemSymm_rational_weights
    (weights : List ℚ) (M X : ℚ) (R : ℕ)
    (hnn : ∀ w ∈ weights, 0 ≤ w)
    (hmass : weights.sum ≤ M)
    (hX : 1 ≤ X) :
    (∑ r ∈ Finset.range (2 * R + 1),
        (X : ℝ) ^ r * (EscLeanChecks.elemSymmList weights r : ℝ))
      ≤ (X : ℝ) ^ (2 * R) * Real.exp (M : ℝ) := by
  have hM_nonneg_Q : 0 ≤ M :=
    le_trans (List.sum_nonneg hnn) hmass
  have hM : 0 ≤ (M : ℝ) := by exact_mod_cast hM_nonneg_Q
  have hX_real : 1 ≤ (X : ℝ) := by exact_mod_cast hX
  have hF0 : ((EscLeanChecks.elemSymmList weights 0 : ℚ) : ℝ) ≤ 1 := by
    norm_num
  have hFnonneg :
      ∀ r : ℕ, 0 ≤ ((EscLeanChecks.elemSymmList weights r : ℚ) : ℝ) := by
    intro r
    exact_mod_cast EscLeanChecks.elemSymmList_nonneg weights r hnn
  have hrec :
      ∀ r : ℕ, 1 ≤ r →
        (r : ℝ) * (EscLeanChecks.elemSymmList weights r : ℝ)
          ≤ ((M : ℝ) * (1 + 0)) *
              (EscLeanChecks.elemSymmList weights (r - 1) : ℝ) := by
    intro r hr
    have hbase :
        (r : ℚ) * EscLeanChecks.elemSymmList weights r
          ≤ weights.sum * EscLeanChecks.elemSymmList weights (r - 1) :=
      EscLeanChecks.elemSymmList_brun_recurrence weights hnn r hr
    have hprev_nonneg :
        0 ≤ EscLeanChecks.elemSymmList weights (r - 1) :=
      EscLeanChecks.elemSymmList_nonneg weights (r - 1) hnn
    have hmass_step :
        weights.sum * EscLeanChecks.elemSymmList weights (r - 1)
          ≤ M * EscLeanChecks.elemSymmList weights (r - 1) :=
      mul_le_mul_of_nonneg_right hmass hprev_nonneg
    have hrat :
        (r : ℚ) * EscLeanChecks.elemSymmList weights r
          ≤ M * EscLeanChecks.elemSymmList weights (r - 1) :=
      le_trans hbase hmass_step
    have hreal :
        (r : ℝ) * (EscLeanChecks.elemSymmList weights r : ℝ)
          ≤ (M : ℝ) * (EscLeanChecks.elemSymmList weights (r - 1) : ℝ) := by
      exact_mod_cast hrat
    simpa using hreal
  have h :=
    brun_envelope_factorial
      (fun r : ℕ => (EscLeanChecks.elemSymmList weights r : ℝ))
      (M : ℝ) 0 (X : ℝ) R hM (by norm_num) hX_real hF0 hFnonneg hrec
  simpa using h

/-- **Brun envelope for finite elementary-symmetric coefficients, real scale.**

This is the same finite coefficient envelope as
`brun_envelope_elemSymm_rational_weights`, but the Brun scale `X` is real.  The
weights and their mass cap remain rational, matching the certificate carrier,
while the paper-facing exponential cutoff can now be used directly. -/
theorem brun_envelope_elemSymm_rational_weights_real_X
    (weights : List ℚ) (M : ℚ) (X : ℝ) (R : ℕ)
    (hnn : ∀ w ∈ weights, 0 ≤ w)
    (hmass : weights.sum ≤ M)
    (hX : 1 ≤ X) :
    (∑ r ∈ Finset.range (2 * R + 1),
        X ^ r * (EscLeanChecks.elemSymmList weights r : ℝ))
      ≤ X ^ (2 * R) * Real.exp (M : ℝ) := by
  have hM_nonneg_Q : 0 ≤ M :=
    le_trans (List.sum_nonneg hnn) hmass
  have hM : 0 ≤ (M : ℝ) := by exact_mod_cast hM_nonneg_Q
  have hF0 : ((EscLeanChecks.elemSymmList weights 0 : ℚ) : ℝ) ≤ 1 := by
    norm_num
  have hFnonneg :
      ∀ r : ℕ, 0 ≤ ((EscLeanChecks.elemSymmList weights r : ℚ) : ℝ) := by
    intro r
    exact_mod_cast EscLeanChecks.elemSymmList_nonneg weights r hnn
  have hrec :
      ∀ r : ℕ, 1 ≤ r →
        (r : ℝ) * (EscLeanChecks.elemSymmList weights r : ℝ)
          ≤ ((M : ℝ) * (1 + 0)) *
              (EscLeanChecks.elemSymmList weights (r - 1) : ℝ) := by
    intro r hr
    have hbase :
        (r : ℚ) * EscLeanChecks.elemSymmList weights r
          ≤ weights.sum * EscLeanChecks.elemSymmList weights (r - 1) :=
      EscLeanChecks.elemSymmList_brun_recurrence weights hnn r hr
    have hprev_nonneg :
        0 ≤ EscLeanChecks.elemSymmList weights (r - 1) :=
      EscLeanChecks.elemSymmList_nonneg weights (r - 1) hnn
    have hmass_step :
        weights.sum * EscLeanChecks.elemSymmList weights (r - 1)
          ≤ M * EscLeanChecks.elemSymmList weights (r - 1) :=
      mul_le_mul_of_nonneg_right hmass hprev_nonneg
    have hrat :
        (r : ℚ) * EscLeanChecks.elemSymmList weights r
          ≤ M * EscLeanChecks.elemSymmList weights (r - 1) :=
      le_trans hbase hmass_step
    have hreal :
        (r : ℝ) * (EscLeanChecks.elemSymmList weights r : ℝ)
          ≤ (M : ℝ) * (EscLeanChecks.elemSymmList weights (r - 1) : ℝ) := by
      exact_mod_cast hrat
    simpa using hreal
  have h :=
    brun_envelope_factorial
      (fun r : ℕ => (EscLeanChecks.elemSymmList weights r : ℝ))
      (M : ℝ) 0 X R hM (by norm_num) hX hF0 hFnonneg hrec
  simpa using h

/-- **Top Brun coefficient from the finite elementary-symmetric model.**

The finite-transfer proof needs the manuscript tail bound
`F_{2R} ≤ exp(-3μ)`.  This lemma ties that tail to the actual finite coefficient
carrier: once the explicit factorial/Stirling inequality
`M^{2R}/(2R)! ≤ exp(-3μ)` is available, the elementary-symmetric coefficient
`e_{2R}` has the required bound. -/
theorem elemSymm_top_coefficient_tail_rational_weights
    (weights : List ℚ) (M : ℚ) (R : ℕ) (μ : ℝ)
    (hnn : ∀ w ∈ weights, 0 ≤ w)
    (hmass : weights.sum ≤ M)
    (htail : ((M : ℝ) ^ (2 * R)) / (Nat.factorial (2 * R) : ℝ)
      ≤ Real.exp (-3 * μ)) :
    (EscLeanChecks.elemSymmList weights (2 * R) : ℝ) ≤ Real.exp (-3 * μ) := by
  have hcoefQ :
      EscLeanChecks.elemSymmList weights (2 * R)
        ≤ M ^ (2 * R) / (Nat.factorial (2 * R) : ℚ) :=
    EscLeanChecks.elemSymmList_le_mass_pow_div_factorial weights M (2 * R) hnn hmass
  have hcoefR :
      (EscLeanChecks.elemSymmList weights (2 * R) : ℝ)
        ≤ ((M : ℝ) ^ (2 * R)) / (Nat.factorial (2 * R) : ℝ) := by
    exact_mod_cast hcoefQ
  exact le_trans hcoefR htail

/-- Self-mass factorial tail from the scalar `2μ` tail.

When the actual coefficient mass is bounded by `2μ`, the factorial top-tail
condition can be checked at the scalar budget `2μ` instead of at the exact
finite weight sum. -/
theorem rational_weight_self_tail_of_two_mu_tail
    (weights : List ℚ) (R : ℕ) (μ : ℝ)
    (hnn : ∀ w ∈ weights, 0 ≤ w)
    (hmass_two_mu : ((weights.sum : ℚ) : ℝ) ≤ 2 * μ)
    (htail_two_mu : (2 * μ) ^ (2 * R) /
        (Nat.factorial (2 * R) : ℝ) ≤ Real.exp (-3 * μ)) :
    (((weights.sum : ℚ) : ℝ) ^ (2 * R)) /
        (Nat.factorial (2 * R) : ℝ) ≤ Real.exp (-3 * μ) := by
  have hsum_nonneg_Q : 0 ≤ weights.sum := List.sum_nonneg hnn
  have hsum_nonneg : 0 ≤ ((weights.sum : ℚ) : ℝ) := by
    exact_mod_cast hsum_nonneg_Q
  have hpow :
      (((weights.sum : ℚ) : ℝ) ^ (2 * R)) ≤ (2 * μ) ^ (2 * R) :=
    pow_le_pow_left₀ hsum_nonneg hmass_two_mu (2 * R)
  have hfact_nonneg : 0 ≤ (Nat.factorial (2 * R) : ℝ) := by
    exact_mod_cast (Nat.zero_le (Nat.factorial (2 * R)))
  exact le_trans (div_le_div_of_nonneg_right hpow hfact_nonneg) htail_two_mu

/-- Elementary exponential-series factorial lower bound in the form used for
the top Brun tail: `n^n/n! ≤ exp n`. -/
theorem pow_self_div_factorial_le_exp_self (n : ℕ) :
    ((n : ℝ) ^ n) / (Nat.factorial n : ℝ) ≤ Real.exp (n : ℝ) := by
  have hnonneg : ∀ r ∈ Finset.range (n + 1),
      0 ≤ (n : ℝ) ^ r / (Nat.factorial r : ℝ) := by
    intro r _hr
    positivity
  have hmem : n ∈ Finset.range (n + 1) := by
    rw [Finset.mem_range]
    omega
  exact le_trans (Finset.single_le_sum hnonneg hmem)
    (sum_factorial_le_exp (by positivity : 0 ≤ (n : ℝ)) (n + 1))

/-- Consequence of the exponential-series bound:
`(n/e)^n ≤ n!`. This is the only factorial growth input needed for the scalar
Brun top-tail cutoff below. -/
theorem factorial_lower_exp_self (n : ℕ) :
    ((n : ℝ) / Real.exp 1) ^ n ≤ (Nat.factorial n : ℝ) := by
  have hterm := pow_self_div_factorial_le_exp_self n
  have hfact_pos : 0 < (Nat.factorial n : ℝ) := by positivity
  have hmul : (n : ℝ) ^ n ≤ Real.exp (n : ℝ) * (Nat.factorial n : ℝ) := by
    exact (div_le_iff₀ hfact_pos).mp hterm
  calc
    ((n : ℝ) / Real.exp 1) ^ n = (n : ℝ) ^ n / (Real.exp 1) ^ n := by
      rw [div_pow]
    _ = (n : ℝ) ^ n / Real.exp (n : ℝ) := by
      rw [Real.exp_one_pow]
    _ ≤ (Nat.factorial n : ℝ) := by
      rw [div_le_iff₀ (Real.exp_pos (n : ℝ))]
      linarith

/-- Scalar top-tail discharge for the Brun coefficient route.

If the truncation rank is chosen so that `2R ≥ 24 μ`, then the explicit
factorial tail at mass `2μ` is already at most `exp(-3μ)`. This removes the
previous bare scalar-tail hypothesis from the paper-facing route; only the
rank-size choice remains to be supplied by the construction of `R`. -/
theorem scalar_two_mu_factorial_tail_of_rank_ge
    {μ : ℝ} {R : ℕ} (hμ_nonneg : 0 ≤ μ)
    (hrank : 24 * μ ≤ (2 * R : ℝ)) :
    (2 * μ) ^ (2 * R) / (Nat.factorial (2 * R) : ℝ)
      ≤ Real.exp (-3 * μ) := by
  set n : ℕ := 2 * R
  by_cases hn0 : n = 0
  · have hR0 : R = 0 := by
      have : 2 * R = 0 := by simpa [n] using hn0
      omega
    have hμ0 : μ = 0 := by
      have hle0 : 24 * μ ≤ 0 := by simpa [hR0] using hrank
      nlinarith
    subst μ
    simp [hR0, n]
  · have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn0
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
    have hbase_nonneg : 0 ≤ 2 * μ := by nlinarith
    have hfac_lower := factorial_lower_exp_self n
    have hlower_pos : 0 < ((n : ℝ) / Real.exp 1) ^ n := by
      positivity
    have hdiv1 :
        (2 * μ) ^ n / (Nat.factorial n : ℝ)
          ≤ (2 * μ) ^ n / (((n : ℝ) / Real.exp 1) ^ n) := by
      exact div_le_div_of_nonneg_left (pow_nonneg hbase_nonneg n)
        hlower_pos hfac_lower
    have he_le_three : Real.exp 1 ≤ (3 : ℝ) := by
      exact le_of_lt (Real.exp_one_lt_d9.trans (by norm_num))
    have hnum_le : 2 * μ * Real.exp 1 ≤ (n : ℝ) / 4 := by
      have h24 : 24 * μ ≤ (n : ℝ) := by simpa [n] using hrank
      have h6 : 6 * μ ≤ (n : ℝ) / 4 := by nlinarith
      have h2e : 2 * μ * Real.exp 1 ≤ 2 * μ * 3 := by
        exact mul_le_mul_of_nonneg_left he_le_three (by nlinarith)
      nlinarith
    have hbase_ratio_nonneg : 0 ≤ (2 * μ * Real.exp 1) / (n : ℝ) := by
      positivity
    have hbase_le_quarter :
        (2 * μ * Real.exp 1) / (n : ℝ) ≤ (1 : ℝ) / 4 := by
      rw [div_le_iff₀ hnpos]
      nlinarith
    have hratio_eq :
        (2 * μ) ^ n / (((n : ℝ) / Real.exp 1) ^ n)
          = ((2 * μ * Real.exp 1) / (n : ℝ)) ^ n := by
      rw [div_pow, Real.exp_one_pow]
      field_simp [hnpos.ne', Real.exp_ne_zero]
      rw [← Real.exp_one_pow]
      ring
    have hpow_quarter :
        ((2 * μ * Real.exp 1) / (n : ℝ)) ^ n ≤ ((1 : ℝ) / 4) ^ n :=
      pow_le_pow_left₀ hbase_ratio_nonneg hbase_le_quarter n
    have hquarter_exp : ((1 : ℝ) / 4) ≤ Real.exp (-1) := by
      have he4 : Real.exp 1 ≤ (4 : ℝ) := by
        exact le_of_lt (Real.exp_one_lt_d9.trans (by norm_num))
      rw [Real.exp_neg]
      simpa [one_div] using one_div_le_one_div_of_le (Real.exp_pos 1) he4
    have hpow_exp : ((1 : ℝ) / 4) ^ n ≤ (Real.exp (-1)) ^ n :=
      pow_le_pow_left₀ (by norm_num) hquarter_exp n
    have hexp_pow : (Real.exp (-1)) ^ n = Real.exp (-(n : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hn_ge_three_mu : 3 * μ ≤ (n : ℝ) := by
      have h24 : 24 * μ ≤ (n : ℝ) := by simpa [n] using hrank
      nlinarith
    have hexp_le : Real.exp (-(n : ℝ)) ≤ Real.exp (-3 * μ) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc
      (2 * μ) ^ (2 * R) / (Nat.factorial (2 * R) : ℝ)
          = (2 * μ) ^ n / (Nat.factorial n : ℝ) := by rfl
      _ ≤ (2 * μ) ^ n / (((n : ℝ) / Real.exp 1) ^ n) := hdiv1
      _ = ((2 * μ * Real.exp 1) / (n : ℝ)) ^ n := hratio_eq
      _ ≤ ((1 : ℝ) / 4) ^ n := hpow_quarter
      _ ≤ (Real.exp (-1)) ^ n := hpow_exp
      _ = Real.exp (-(n : ℝ)) := hexp_pow
      _ ≤ Real.exp (-3 * μ) := hexp_le

/-! ## Part 2. `prop:mass-dependency-scale` — the two `o(1)` scale identities. -/

/-- **Mass–dependency compatibility scale** (`prop:mass-dependency-scale`,
tex 1831–1868).

We take the manuscript's two *upstream* ingredients as hypotheses (they are
proved in other files):

* `hmass`  : the mass law `μ_b ≍ (log X)³`, here in the only form used —
  `μ_b X ≤ Cμ · (log X)³` for `X` large (the `≪` half; `prop:mu`);
* `hscale1`: `(log Y)/(z log z) = o(1/(log X)³)`, equivalently
  `(log X)³ · (log Y)/(z log z) = o(1)` — the medium-prime reciprocal scale
  (tex 1851–1855 with `Y = X^σ`, `z = (log X)⁴`);
* `htail`  : the rough residual squarefree tail `T(X) := ∑_{D>1 sqf, (D,P(z))=1} 1/D²`
  obeys `(log X)³ · T = o(1)` (tex 1856–1867: `T ≪ 1/(z log z)`, so
  `(log X)³ T ≪ 1/((log X) log log X) = o(1)`).

The conclusion is the manuscript's pair of `o(1)` facts together with the
consequence `μ_b² T = o(μ_b)`.  All three follow by *real algebra* from the
hypotheses; this is a proof. -/
theorem mass_dependency_scale
    (μ depTail medScale : ℝ → ℝ)
    (Cμ : ℝ)
    (hμnonneg : ∀ X, 0 ≤ μ X)
    (hmass : ∀ᶠ X in atTop, μ X ≤ Cμ * (Real.log X) ^ 3)
    (hscale1 : Tendsto (fun X => (Real.log X) ^ 3 * medScale X) atTop (𝓝 0))
    (htail : Tendsto (fun X => (Real.log X) ^ 3 * depTail X) atTop (𝓝 0))
    (hmedNonneg : ∀ᶠ X in atTop, 0 ≤ medScale X)
    (htailNonneg : ∀ᶠ X in atTop, 0 ≤ depTail X)
    (_hCμ : 0 ≤ Cμ) :
    -- first o(1): μ_b · (log Y)/(z log z) → 0
    Tendsto (fun X => μ X * medScale X) atTop (𝓝 0)
    ∧ -- second o(1): μ_b · T → 0
    Tendsto (fun X => μ X * depTail X) atTop (𝓝 0)
    ∧ -- consequence: μ_b² · T = o(μ_b).  The Landau relation `f = o(μ_b)` unfolds
      -- to `f / μ_b → 0`; with `f = μ_b² T` this is `(μ_b² T)/μ_b = μ_b T → 0`
      -- (equal to the previous statement on the positivity set where division is
      -- meaningful), so the direct formulation is `μ_b · T → 0` again.
    Tendsto (fun X => (μ X) ^ 2 * depTail X / μ X) atTop (𝓝 0) := by
  -- `μ_b · medScale ≤ Cμ · ((log X)³ · medScale)` eventually, squeezed to 0.
  have key₁ : Tendsto (fun X => μ X * medScale X) atTop (𝓝 0) := by
    have hCμscale : Tendsto (fun X => Cμ * ((Real.log X) ^ 3 * medScale X)) atTop (𝓝 0) := by
      simpa using hscale1.const_mul Cμ
    refine squeeze_zero' ?_ ?_ hCμscale
    · filter_upwards [hmedNonneg] with X hX
      exact mul_nonneg (hμnonneg X) hX
    · filter_upwards [hmass, hmedNonneg] with X hmX hmedX
      have : μ X * medScale X ≤ (Cμ * (Real.log X) ^ 3) * medScale X :=
        mul_le_mul_of_nonneg_right hmX hmedX
      calc μ X * medScale X ≤ (Cμ * (Real.log X) ^ 3) * medScale X := this
        _ = Cμ * ((Real.log X) ^ 3 * medScale X) := by ring
  -- `μ_b · depTail ≤ Cμ · ((log X)³ · depTail) → 0`
  have key₂ : Tendsto (fun X => μ X * depTail X) atTop (𝓝 0) := by
    have hCμtail : Tendsto (fun X => Cμ * ((Real.log X) ^ 3 * depTail X)) atTop (𝓝 0) := by
      simpa using htail.const_mul Cμ
    refine squeeze_zero' ?_ ?_ hCμtail
    · filter_upwards [htailNonneg] with X hX
      exact mul_nonneg (hμnonneg X) hX
    · filter_upwards [hmass, htailNonneg] with X hmX htailX
      have : μ X * depTail X ≤ (Cμ * (Real.log X) ^ 3) * depTail X :=
        mul_le_mul_of_nonneg_right hmX htailX
      calc μ X * depTail X ≤ (Cμ * (Real.log X) ^ 3) * depTail X := this
        _ = Cμ * ((Real.log X) ^ 3 * depTail X) := by ring
  -- consequence: μ_b · (μ_b · depTail) ≤ (Cμ (log X)³) · (μ_b depTail) → 0
  have key₃ : Tendsto (fun X => (μ X) ^ 2 * depTail X / μ X) atTop (𝓝 0) := by
    -- `μ_b² T / μ_b = μ_b T` pointwise (Lean's `0/0 = 0` makes the `μ_b = 0`
    -- case agree), so the `o(μ_b)` consequence is exactly `key₂`.
    have hpt : (fun X => (μ X) ^ 2 * depTail X / μ X)
        = (fun X => μ X * depTail X) := by
      funext X
      rcases eq_or_ne (μ X) 0 with h0 | h0
      · simp [h0]
      · field_simp
        ring
    rw [hpt]; exact key₂
  exact ⟨key₁, key₂, key₃⟩

/-- Eventual-nonnegativity version of `mass_dependency_scale`.

All squeezes in `prop:mass-dependency-scale` occur on a sufficiently large
tail, so the mass carrier only needs to be nonnegative eventually. -/
theorem mass_dependency_scale_eventually_nonneg
    (μ depTail medScale : ℝ → ℝ)
    (Cμ : ℝ)
    (hμnonneg : ∀ᶠ X in atTop, 0 ≤ μ X)
    (hmass : ∀ᶠ X in atTop, μ X ≤ Cμ * (Real.log X) ^ 3)
    (hscale1 : Tendsto (fun X => (Real.log X) ^ 3 * medScale X) atTop (𝓝 0))
    (htail : Tendsto (fun X => (Real.log X) ^ 3 * depTail X) atTop (𝓝 0))
    (hmedNonneg : ∀ᶠ X in atTop, 0 ≤ medScale X)
    (htailNonneg : ∀ᶠ X in atTop, 0 ≤ depTail X)
    (_hCμ : 0 ≤ Cμ) :
    Tendsto (fun X => μ X * medScale X) atTop (𝓝 0)
    ∧ Tendsto (fun X => μ X * depTail X) atTop (𝓝 0)
    ∧ Tendsto (fun X => (μ X) ^ 2 * depTail X / μ X) atTop (𝓝 0) := by
  have key₁ : Tendsto (fun X => μ X * medScale X) atTop (𝓝 0) := by
    have hCμscale : Tendsto (fun X => Cμ * ((Real.log X) ^ 3 * medScale X)) atTop (𝓝 0) := by
      simpa using hscale1.const_mul Cμ
    refine squeeze_zero' ?_ ?_ hCμscale
    · filter_upwards [hμnonneg, hmedNonneg] with X hμX hmedX
      exact mul_nonneg hμX hmedX
    · filter_upwards [hmass, hmedNonneg] with X hmX hmedX
      have : μ X * medScale X ≤ (Cμ * (Real.log X) ^ 3) * medScale X :=
        mul_le_mul_of_nonneg_right hmX hmedX
      calc μ X * medScale X ≤ (Cμ * (Real.log X) ^ 3) * medScale X := this
        _ = Cμ * ((Real.log X) ^ 3 * medScale X) := by ring
  have key₂ : Tendsto (fun X => μ X * depTail X) atTop (𝓝 0) := by
    have hCμtail : Tendsto (fun X => Cμ * ((Real.log X) ^ 3 * depTail X)) atTop (𝓝 0) := by
      simpa using htail.const_mul Cμ
    refine squeeze_zero' ?_ ?_ hCμtail
    · filter_upwards [hμnonneg, htailNonneg] with X hμX htailX
      exact mul_nonneg hμX htailX
    · filter_upwards [hmass, htailNonneg] with X hmX htailX
      have : μ X * depTail X ≤ (Cμ * (Real.log X) ^ 3) * depTail X :=
        mul_le_mul_of_nonneg_right hmX htailX
      calc μ X * depTail X ≤ (Cμ * (Real.log X) ^ 3) * depTail X := this
        _ = Cμ * ((Real.log X) ^ 3 * depTail X) := by ring
  have key₃ : Tendsto (fun X => (μ X) ^ 2 * depTail X / μ X) atTop (𝓝 0) := by
    have hpt : (fun X => (μ X) ^ 2 * depTail X / μ X)
        = (fun X => μ X * depTail X) := by
      funext X
      rcases eq_or_ne (μ X) 0 with h0 | h0
      · simp [h0]
      · field_simp
        ring
    rw [hpt]; exact key₂
  exact ⟨key₁, key₂, key₃⟩

/-! ## Part 3. Large-prime neighbours and `lem:delta-Delta`. -/

/-- A fixed negative power tends to zero at infinity.

This is the real-variable endpoint used after the manuscript's
large-prime-neighbour estimate has produced a genuine power saving. -/
theorem negative_rpow_tendsto_zero (C η : ℝ) (hη : 0 < η) :
    Tendsto (fun X : ℝ => C * X ^ (-η)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun X : ℝ => X ^ η) atTop atTop := tendsto_rpow_atTop hη
  have hinv : Tendsto (fun X : ℝ => ((X ^ η) : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hpow
  have heq :
      (fun X : ℝ => ((X ^ η) : ℝ)⁻¹) =ᶠ[atTop] (fun X : ℝ => X ^ (-η)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with X hX
    rw [Real.rpow_neg hX.le η]
  have hneg : Tendsto (fun X : ℝ => X ^ (-η)) atTop (𝓝 0) :=
    Filter.Tendsto.congr' heq hinv
  simpa using hneg.const_mul C

/-- A fixed negative power of `log X` tends to zero.

This is the elementary analytic conversion behind the paper's repeated
`z=(log X)^4` power savings. -/
theorem log_negative_rpow_tendsto_zero (C η : ℝ) (hη : 0 < η) :
    Tendsto (fun X : ℝ => C * (Real.log X) ^ (-η)) atTop (𝓝 0) :=
  (negative_rpow_tendsto_zero C η hη).comp Real.tendsto_log_atTop

/-- The manuscript's medium-prime dependency scale
`log Y /(z log z)` with `Y=X^σ` and `z=(log X)^4`. -/
noncomputable def paperMediumScale (P : Params) (X : ℝ) : ℝ :=
  Real.log (YScale P X) / (zScale X * Real.log (zScale X))

/-- The paper's medium-prime dependency scale is eventually nonnegative. -/
theorem paperMediumScale_eventually_nonneg (P : Params) :
    ∀ᶠ X in atTop, 0 ≤ paperMediumScale P X := by
  filter_upwards [eventually_ge_atTop (Real.exp 2)] with X hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 2) hX
  have hlogX_ge_two : (2 : ℝ) ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hX
  have hlogX_nonneg : 0 ≤ Real.log X := le_trans (by norm_num) hlogX_ge_two
  have hlogY_nonneg : 0 ≤ Real.log (YScale P X) := by
    unfold YScale
    rw [Real.log_rpow hXpos]
    exact mul_nonneg P.σ_pos.le hlogX_nonneg
  have hz_pos : 0 < zScale X := by
    unfold zScale
    exact pow_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hlogX_ge_two) 4
  have hlogz_pos : 0 < Real.log (zScale X) :=
    Inputs.log_zScale_pos_of_exp_two_le hX
  unfold paperMediumScale
  exact div_nonneg hlogY_nonneg (mul_nonneg hz_pos.le hlogz_pos.le)

/-- The medium-prime dependency scale needed in `prop:mass-dependency-scale`
is genuinely small for the paper's cutoff `z=(log X)^4`.

After multiplying by `(log X)^3`, the scale is eventually exactly
`σ / log z(X)`, hence tends to zero because `log z(X) → ∞`.  This is the
correct elementary replacement for any stronger negative-log-power envelope. -/
theorem paperMediumScale_logCube_tendsto_zero (P : Params) :
    Tendsto (fun X : ℝ => (Real.log X) ^ 3 * paperMediumScale P X)
      atTop (𝓝 0) := by
  have hden :
      Tendsto (fun X : ℝ => (Real.log (zScale X))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Inputs.tendsto_log_zScale_atTop
  have htarget :
      Tendsto (fun X : ℝ => P.σ * (Real.log (zScale X))⁻¹) atTop (𝓝 0) := by
    simpa using hden.const_mul P.σ
  refine htarget.congr' ?_
  filter_upwards [eventually_ge_atTop (Real.exp 2)] with X hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 2) hX
  have hlogX_ge_two : (2 : ℝ) ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hX
  have hlogX_pos : 0 < Real.log X :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hlogX_ge_two
  have hlogX_ne : Real.log X ≠ 0 := ne_of_gt hlogX_pos
  have hlogz_pos : 0 < Real.log (zScale X) :=
    Inputs.log_zScale_pos_of_exp_two_le hX
  have hlogz_ne : Real.log (zScale X) ≠ 0 := ne_of_gt hlogz_pos
  have hloglog_pos : 0 < Real.log (Real.log X) :=
    Real.log_pos (lt_of_lt_of_le one_lt_two hlogX_ge_two)
  have hloglog_ne : Real.log (Real.log X) ≠ 0 := ne_of_gt hloglog_pos
  unfold paperMediumScale YScale zScale
  rw [Real.log_rpow hXpos]
  field_simp [hlogX_ne, hloglog_ne]
  ring

/-- If `(log X)^3 f(X)` is eventually bounded by a negative log-power, then it
tends to zero.

The nonnegativity hypothesis is large-range only, matching the way the
dependency tails enter the manuscript. -/
theorem log_cube_mul_tendsto_zero_of_log_power_upper
    (f : ℝ → ℝ) (C η : ℝ) (hη : 0 < η)
    (hf_nonneg : ∀ᶠ X in atTop, 0 ≤ f X)
    (hupper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * f X ≤ C * (Real.log X) ^ (-η)) :
    Tendsto (fun X => (Real.log X) ^ 3 * f X) atTop (𝓝 0) := by
  have hlog_nonneg : ∀ᶠ X in atTop, 0 ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0 : ℝ))
  refine squeeze_zero' ?_ hupper (log_negative_rpow_tendsto_zero C η hη)
  filter_upwards [hlog_nonneg, hf_nonneg] with X hlogX hfX
  exact mul_nonneg (pow_nonneg hlogX 3) hfX

/-- **Mass–dependency compatibility from explicit logarithmic power envelopes.**

This is a more paper-facing form of `mass_dependency_scale`: instead of taking
the two scale limits as hypotheses, it derives them from eventual bounds by
negative powers of `log X`.  The upstream arithmetic work is now isolated in the
two displayed envelope hypotheses. -/
theorem mass_dependency_scale_from_log_power_bounds
    (μ depTail medScale : ℝ → ℝ)
    (Cμ Cmed Ctail ηmed ηtail : ℝ)
    (hηmed : 0 < ηmed) (hηtail : 0 < ηtail)
    (hμnonneg : ∀ X, 0 ≤ μ X)
    (hmass : ∀ᶠ X in atTop, μ X ≤ Cμ * (Real.log X) ^ 3)
    (hmedNonneg : ∀ᶠ X in atTop, 0 ≤ medScale X)
    (htailNonneg : ∀ᶠ X in atTop, 0 ≤ depTail X)
    (hmedUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * medScale X ≤ Cmed * (Real.log X) ^ (-ηmed))
    (htailUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * depTail X ≤ Ctail * (Real.log X) ^ (-ηtail))
    (hCμ : 0 ≤ Cμ) :
    Tendsto (fun X => μ X * medScale X) atTop (𝓝 0)
    ∧ Tendsto (fun X => μ X * depTail X) atTop (𝓝 0)
    ∧ Tendsto (fun X => (μ X) ^ 2 * depTail X / μ X) atTop (𝓝 0) := by
  have hscale1 : Tendsto (fun X => (Real.log X) ^ 3 * medScale X) atTop (𝓝 0) :=
    log_cube_mul_tendsto_zero_of_log_power_upper
      medScale Cmed ηmed hηmed hmedNonneg hmedUpper
  have htail : Tendsto (fun X => (Real.log X) ^ 3 * depTail X) atTop (𝓝 0) :=
    log_cube_mul_tendsto_zero_of_log_power_upper
      depTail Ctail ηtail hηtail htailNonneg htailUpper
  exact mass_dependency_scale μ depTail medScale Cμ hμnonneg hmass hscale1 htail
    hmedNonneg htailNonneg hCμ

/-- Eventual-nonnegativity version of
`mass_dependency_scale_from_log_power_bounds`. -/
theorem mass_dependency_scale_from_log_power_bounds_eventually_nonneg
    (μ depTail medScale : ℝ → ℝ)
    (Cμ Cmed Ctail ηmed ηtail : ℝ)
    (hηmed : 0 < ηmed) (hηtail : 0 < ηtail)
    (hμnonneg : ∀ᶠ X in atTop, 0 ≤ μ X)
    (hmass : ∀ᶠ X in atTop, μ X ≤ Cμ * (Real.log X) ^ 3)
    (hmedNonneg : ∀ᶠ X in atTop, 0 ≤ medScale X)
    (htailNonneg : ∀ᶠ X in atTop, 0 ≤ depTail X)
    (hmedUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * medScale X ≤ Cmed * (Real.log X) ^ (-ηmed))
    (htailUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * depTail X ≤ Ctail * (Real.log X) ^ (-ηtail))
    (hCμ : 0 ≤ Cμ) :
    Tendsto (fun X => μ X * medScale X) atTop (𝓝 0)
    ∧ Tendsto (fun X => μ X * depTail X) atTop (𝓝 0)
    ∧ Tendsto (fun X => (μ X) ^ 2 * depTail X / μ X) atTop (𝓝 0) := by
  have hscale1 : Tendsto (fun X => (Real.log X) ^ 3 * medScale X) atTop (𝓝 0) :=
    log_cube_mul_tendsto_zero_of_log_power_upper
      medScale Cmed ηmed hηmed hmedNonneg hmedUpper
  have htail : Tendsto (fun X => (Real.log X) ^ 3 * depTail X) atTop (𝓝 0) :=
    log_cube_mul_tendsto_zero_of_log_power_upper
      depTail Ctail ηtail hηtail htailNonneg htailUpper
  exact mass_dependency_scale_eventually_nonneg μ depTail medScale Cμ hμnonneg
    hmass hscale1 htail hmedNonneg htailNonneg hCμ

/-- `prop:mass-dependency-scale` with the paper's concrete medium-prime scale
`log Y/(z log z)` discharged internally.

The residual squarefree tail is still supplied as the displayed log-power
envelope; the medium scale no longer appears as a free hypothesis. -/
theorem mass_dependency_scale_from_paper_medium_and_log_power_tail_eventually_nonneg
    (P : Params) (μ depTail : ℝ → ℝ)
    (Cμ Ctail ηtail : ℝ) (hηtail : 0 < ηtail)
    (hμnonneg : ∀ᶠ X in atTop, 0 ≤ μ X)
    (hmass : ∀ᶠ X in atTop, μ X ≤ Cμ * (Real.log X) ^ 3)
    (htailNonneg : ∀ᶠ X in atTop, 0 ≤ depTail X)
    (htailUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * depTail X ≤ Ctail * (Real.log X) ^ (-ηtail))
    (hCμ : 0 ≤ Cμ) :
    Tendsto (fun X => μ X * paperMediumScale P X) atTop (𝓝 0)
    ∧ Tendsto (fun X => μ X * depTail X) atTop (𝓝 0)
    ∧ Tendsto (fun X => (μ X) ^ 2 * depTail X / μ X) atTop (𝓝 0) := by
  have htail : Tendsto (fun X => (Real.log X) ^ 3 * depTail X) atTop (𝓝 0) :=
    log_cube_mul_tendsto_zero_of_log_power_upper
      depTail Ctail ηtail hηtail htailNonneg htailUpper
  exact mass_dependency_scale_eventually_nonneg
    μ depTail (paperMediumScale P) Cμ hμnonneg hmass
    (paperMediumScale_logCube_tendsto_zero P) htail
    (paperMediumScale_eventually_nonneg P) htailNonneg hCμ

/-- **Large-prime-neighbour decay bridge** (`lem:large-prime-neighbour`, final
`= o(1)` step).

After the manuscript's divisor-counting argument bounds the large-prime
neighbour contribution by a fixed power saving `C X^{-η}`, the contribution tends
to zero.  This isolates the exact real-analysis step used by `lem:delta-Delta`;
the upstream arithmetic estimate is supplied as the explicit eventual bound. -/
theorem large_prime_neighbour_power_saving_tendsto_zero
    (largePrime : ℝ → ℝ) (C η : ℝ) (hη : 0 < η)
    (hlarge_nonneg : ∀ X, 0 ≤ largePrime X)
    (hlarge_le : ∀ᶠ X in atTop, largePrime X ≤ C * X ^ (-η)) :
    Tendsto largePrime atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall hlarge_nonneg) hlarge_le ?_
  exact negative_rpow_tendsto_zero C η hη

/-- Eventual-nonnegativity variant of
`large_prime_neighbour_power_saving_tendsto_zero`.

The large-prime-neighbour term is only consumed at large cutoffs, so eventual
nonnegativity is enough for the squeeze-to-zero step. -/
theorem large_prime_neighbour_power_saving_tendsto_zero_eventually_nonneg
    (largePrime : ℝ → ℝ) (C η : ℝ) (hη : 0 < η)
    (hlarge_nonneg : ∀ᶠ X in atTop, 0 ≤ largePrime X)
    (hlarge_le : ∀ᶠ X in atTop, largePrime X ≤ C * X ^ (-η)) :
    Tendsto largePrime atTop (𝓝 0) := by
  refine squeeze_zero' hlarge_nonneg hlarge_le ?_
  exact negative_rpow_tendsto_zero C η hη

/-! ## Part 3b. `lem:delta-Delta` — the dependency bounds `δ_b = o(1)`, `Δ_b = o(μ_b)`. -/

/-- **Dependency bounds** (`lem:delta-Delta`, tex 1870–1920).

The manuscript bounds the dependency parameters by the scale quantities of
`prop:mass-dependency-scale`:

* medium- and large-prime neighbours give
  `δ_b ≤ C₁ · (μ_b · medScale) + largePrime_b` (tex 1875–1898), where
  `largePrime_b → 0` is the large-prime-neighbour contribution
  (`≪ X^ε p^{-1}(log X)^{O(1)}`, tex 1896–1898);
* the correlation sum is dominated by the residual squarefree tail,
  `Δ_b ≤ C₂ · μ_b² · T` (tex 1903–1918).

Taking those two pointwise bounds and the scale facts (`mass_dependency_scale`'s
`key₁` and the `o(μ_b)` form) as hypotheses, the conclusions `δ_b = o(1)` and
`Δ_b = o(μ_b)` follow by real squeeze arguments.  Proof. -/
theorem delta_Delta_bounds
    (μ δb Δb medScale depTail largePrime : ℝ → ℝ)
    (C₁ C₂ : ℝ) (_hC₁ : 0 ≤ C₁) (_hC₂ : 0 ≤ C₂)
    (hδ_nonneg : ∀ X, 0 ≤ δb X)
    (hΔ_nonneg : ∀ X, 0 ≤ Δb X)
    (hμ_nonneg : ∀ X, 0 ≤ μ X)
    -- pointwise structural bounds (proved upstream from `prop:event-tensor`)
    (hδ_le : ∀ᶠ X in atTop, δb X ≤ C₁ * (μ X * medScale X) + largePrime X)
    (hΔ_le : ∀ᶠ X in atTop, Δb X ≤ C₂ * ((μ X) ^ 2 * depTail X))
    -- scale facts from `mass_dependency_scale`
    (hmed0 : Tendsto (fun X => μ X * medScale X) atTop (𝓝 0))
    (hlarge0 : Tendsto largePrime atTop (𝓝 0))
    (htail_o_μ : Tendsto (fun X => (μ X) ^ 2 * depTail X / μ X) atTop (𝓝 0)) :
    -- δ_b = o(1)
    Tendsto δb atTop (𝓝 0)
    ∧ -- Δ_b = o(μ_b), i.e. Δ_b / μ_b → 0
    Tendsto (fun X => Δb X / μ X) atTop (𝓝 0) := by
  refine ⟨?_, ?_⟩
  · -- δ_b ≤ C₁(μ medScale) + largePrime → C₁·0 + 0 = 0, and δ_b ≥ 0
    have hub : Tendsto (fun X => C₁ * (μ X * medScale X) + largePrime X) atTop (𝓝 0) := by
      have h1 : Tendsto (fun X => C₁ * (μ X * medScale X)) atTop (𝓝 0) := by
        simpa using hmed0.const_mul C₁
      simpa using h1.add hlarge0
    refine squeeze_zero' (Eventually.of_forall hδ_nonneg) ?_ hub
    filter_upwards [hδ_le] with X hX using hX
  · -- Δ_b / μ_b ≤ C₂ · ((μ²T)/μ) → 0, and Δ_b/μ_b ≥ 0 eventually (μ_b ≥ 0)
    have hub : Tendsto (fun X => C₂ * ((μ X) ^ 2 * depTail X / μ X)) atTop (𝓝 0) := by
      simpa using htail_o_μ.const_mul C₂
    refine squeeze_zero' ?_ ?_ hub
    · -- 0 ≤ Δ_b / μ_b needs μ_b ≥ 0; division by nonneg of nonneg is nonneg
      filter_upwards with X
      exact div_nonneg (hΔ_nonneg X) (hμ_nonneg X)
    · -- Δ_b/μ_b ≤ C₂((μ²T)/μ): from Δ_b ≤ C₂ μ² T, divide by μ ≥ 0
      filter_upwards [hΔ_le] with X hX
      rcases eq_or_ne (μ X) 0 with h0 | h0
      · -- μ_b = 0 ⇒ both sides 0 (Lean `_/0 = 0`)
        simp [h0]
      · have hμpos : 0 < μ X := lt_of_le_of_ne (hμ_nonneg X) (Ne.symm h0)
        rw [div_le_iff₀ hμpos]
        have hrw : C₂ * ((μ X) ^ 2 * depTail X / μ X) * μ X
            = C₂ * ((μ X) ^ 2 * depTail X) := by
          field_simp
        rw [hrw]
        exact hX

/-- `lem:delta-Delta` with the large-prime-neighbour input supplied in the
power-saving form proved above.  This is the form closest to the paper's
`X^ε p^{-1}(\log X)^{O(1)} = o(1)` line after the fixed positive power saving has
been extracted. -/
theorem delta_Delta_bounds_from_large_prime_power_saving
    (μ δb Δb medScale depTail largePrime : ℝ → ℝ)
    (C₁ C₂ Clarge η : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hη : 0 < η)
    (hδ_nonneg : ∀ X, 0 ≤ δb X)
    (hΔ_nonneg : ∀ X, 0 ≤ Δb X)
    (hμ_nonneg : ∀ X, 0 ≤ μ X)
    (hlarge_nonneg : ∀ X, 0 ≤ largePrime X)
    (hδ_le : ∀ᶠ X in atTop, δb X ≤ C₁ * (μ X * medScale X) + largePrime X)
    (hΔ_le : ∀ᶠ X in atTop, Δb X ≤ C₂ * ((μ X) ^ 2 * depTail X))
    (hlarge_le : ∀ᶠ X in atTop, largePrime X ≤ Clarge * X ^ (-η))
    (hmed0 : Tendsto (fun X => μ X * medScale X) atTop (𝓝 0))
    (htail_o_μ : Tendsto (fun X => (μ X) ^ 2 * depTail X / μ X) atTop (𝓝 0)) :
    Tendsto δb atTop (𝓝 0)
    ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0) := by
  have hlarge0 : Tendsto largePrime atTop (𝓝 0) :=
    large_prime_neighbour_power_saving_tendsto_zero largePrime Clarge η hη
      hlarge_nonneg hlarge_le
  exact delta_Delta_bounds μ δb Δb medScale depTail largePrime C₁ C₂
    hC₁ hC₂ hδ_nonneg hΔ_nonneg hμ_nonneg hδ_le hΔ_le hmed0 hlarge0 htail_o_μ

/-- Eventual-nonnegativity version of `delta_Delta_bounds`.

All inequalities in the dependency squeeze are large-range inequalities, so the
nonnegativity hypotheses for `δ_b`, `Δ_b`, and `μ_b` may also be large-range
hypotheses. -/
theorem delta_Delta_bounds_eventually_nonneg
    (μ δb Δb medScale depTail largePrime : ℝ → ℝ)
    (C₁ C₂ : ℝ) (_hC₁ : 0 ≤ C₁) (_hC₂ : 0 ≤ C₂)
    (hδ_nonneg : ∀ᶠ X in atTop, 0 ≤ δb X)
    (hΔ_nonneg : ∀ᶠ X in atTop, 0 ≤ Δb X)
    (hμ_nonneg : ∀ᶠ X in atTop, 0 ≤ μ X)
    (hδ_le : ∀ᶠ X in atTop, δb X ≤ C₁ * (μ X * medScale X) + largePrime X)
    (hΔ_le : ∀ᶠ X in atTop, Δb X ≤ C₂ * ((μ X) ^ 2 * depTail X))
    (hmed0 : Tendsto (fun X => μ X * medScale X) atTop (𝓝 0))
    (hlarge0 : Tendsto largePrime atTop (𝓝 0))
    (htail_o_μ : Tendsto (fun X => (μ X) ^ 2 * depTail X / μ X) atTop (𝓝 0)) :
    Tendsto δb atTop (𝓝 0)
    ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0) := by
  refine ⟨?_, ?_⟩
  · have hub : Tendsto (fun X => C₁ * (μ X * medScale X) + largePrime X) atTop (𝓝 0) := by
      have h1 : Tendsto (fun X => C₁ * (μ X * medScale X)) atTop (𝓝 0) := by
        simpa using hmed0.const_mul C₁
      simpa using h1.add hlarge0
    refine squeeze_zero' hδ_nonneg ?_ hub
    filter_upwards [hδ_le] with X hX using hX
  · have hub : Tendsto (fun X => C₂ * ((μ X) ^ 2 * depTail X / μ X)) atTop (𝓝 0) := by
      simpa using htail_o_μ.const_mul C₂
    refine squeeze_zero' ?_ ?_ hub
    · filter_upwards [hΔ_nonneg, hμ_nonneg] with X hΔX hμX
      exact div_nonneg hΔX hμX
    · filter_upwards [hΔ_le, hμ_nonneg] with X hX hμX
      rcases eq_or_ne (μ X) 0 with h0 | h0
      · simp [h0]
      · have hμpos : 0 < μ X := lt_of_le_of_ne hμX (Ne.symm h0)
        rw [div_le_iff₀ hμpos]
        have hrw : C₂ * ((μ X) ^ 2 * depTail X / μ X) * μ X
            = C₂ * ((μ X) ^ 2 * depTail X) := by
          field_simp
        rw [hrw]
        exact hX

/-- Eventual-nonnegativity variant of
`delta_Delta_bounds_from_large_prime_power_saving`. -/
theorem delta_Delta_bounds_from_large_prime_power_saving_eventually_nonneg
    (μ δb Δb medScale depTail largePrime : ℝ → ℝ)
    (C₁ C₂ Clarge η : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hη : 0 < η)
    (hδ_nonneg : ∀ᶠ X in atTop, 0 ≤ δb X)
    (hΔ_nonneg : ∀ᶠ X in atTop, 0 ≤ Δb X)
    (hμ_nonneg : ∀ᶠ X in atTop, 0 ≤ μ X)
    (hlarge_nonneg : ∀ᶠ X in atTop, 0 ≤ largePrime X)
    (hδ_le : ∀ᶠ X in atTop, δb X ≤ C₁ * (μ X * medScale X) + largePrime X)
    (hΔ_le : ∀ᶠ X in atTop, Δb X ≤ C₂ * ((μ X) ^ 2 * depTail X))
    (hlarge_le : ∀ᶠ X in atTop, largePrime X ≤ Clarge * X ^ (-η))
    (hmed0 : Tendsto (fun X => μ X * medScale X) atTop (𝓝 0))
    (htail_o_μ : Tendsto (fun X => (μ X) ^ 2 * depTail X / μ X) atTop (𝓝 0)) :
    Tendsto δb atTop (𝓝 0)
    ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0) := by
  have hlarge0 : Tendsto largePrime atTop (𝓝 0) :=
    large_prime_neighbour_power_saving_tendsto_zero_eventually_nonneg
      largePrime Clarge η hη hlarge_nonneg hlarge_le
  exact delta_Delta_bounds_eventually_nonneg μ δb Δb medScale depTail largePrime C₁ C₂
    hC₁ hC₂ hδ_nonneg hΔ_nonneg hμ_nonneg hδ_le hΔ_le hmed0 hlarge0 htail_o_μ

/-- `lem:delta-Delta` from concrete logarithmic scale envelopes and a large-prime
power saving.

This composes `mass_dependency_scale_from_log_power_bounds` with the
eventual-nonnegativity dependency squeeze.  It keeps the arithmetic estimates as
explicit large-range envelopes, but removes the need to supply the intermediate
`Tendsto` scale facts by hand. -/
theorem delta_Delta_bounds_from_log_power_bounds_and_large_prime_power_saving
    (μ δb Δb medScale depTail largePrime : ℝ → ℝ)
    (Cμ Cmed Ctail C₁ C₂ Clarge ηmed ηtail ηlarge : ℝ)
    (hηmed : 0 < ηmed) (hηtail : 0 < ηtail) (hηlarge : 0 < ηlarge)
    (hCμ : 0 ≤ Cμ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hμ_nonneg_all : ∀ X, 0 ≤ μ X)
    (hδ_nonneg : ∀ᶠ X in atTop, 0 ≤ δb X)
    (hΔ_nonneg : ∀ᶠ X in atTop, 0 ≤ Δb X)
    (hmedNonneg : ∀ᶠ X in atTop, 0 ≤ medScale X)
    (htailNonneg : ∀ᶠ X in atTop, 0 ≤ depTail X)
    (hlarge_nonneg : ∀ᶠ X in atTop, 0 ≤ largePrime X)
    (hmass : ∀ᶠ X in atTop, μ X ≤ Cμ * (Real.log X) ^ 3)
    (hmedUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * medScale X ≤ Cmed * (Real.log X) ^ (-ηmed))
    (htailUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * depTail X ≤ Ctail * (Real.log X) ^ (-ηtail))
    (hδ_le : ∀ᶠ X in atTop, δb X ≤ C₁ * (μ X * medScale X) + largePrime X)
    (hΔ_le : ∀ᶠ X in atTop, Δb X ≤ C₂ * ((μ X) ^ 2 * depTail X))
    (hlarge_le : ∀ᶠ X in atTop, largePrime X ≤ Clarge * X ^ (-ηlarge)) :
    Tendsto δb atTop (𝓝 0)
    ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0) := by
  have hscale := mass_dependency_scale_from_log_power_bounds
    μ depTail medScale Cμ Cmed Ctail ηmed ηtail hηmed hηtail
    hμ_nonneg_all hmass hmedNonneg htailNonneg hmedUpper htailUpper hCμ
  exact delta_Delta_bounds_from_large_prime_power_saving_eventually_nonneg
    μ δb Δb medScale depTail largePrime C₁ C₂ Clarge ηlarge
    hC₁ hC₂ hηlarge hδ_nonneg hΔ_nonneg (Eventually.of_forall hμ_nonneg_all)
    hlarge_nonneg hδ_le hΔ_le hlarge_le hscale.1 hscale.2.2

/-- Eventual-nonnegativity version of
`delta_Delta_bounds_from_log_power_bounds_and_large_prime_power_saving`. -/
theorem delta_Delta_bounds_from_log_power_bounds_and_large_prime_power_saving_eventually_nonneg
    (μ δb Δb medScale depTail largePrime : ℝ → ℝ)
    (Cμ Cmed Ctail C₁ C₂ Clarge ηmed ηtail ηlarge : ℝ)
    (hηmed : 0 < ηmed) (hηtail : 0 < ηtail) (hηlarge : 0 < ηlarge)
    (hCμ : 0 ≤ Cμ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hμ_nonneg : ∀ᶠ X in atTop, 0 ≤ μ X)
    (hδ_nonneg : ∀ᶠ X in atTop, 0 ≤ δb X)
    (hΔ_nonneg : ∀ᶠ X in atTop, 0 ≤ Δb X)
    (hmedNonneg : ∀ᶠ X in atTop, 0 ≤ medScale X)
    (htailNonneg : ∀ᶠ X in atTop, 0 ≤ depTail X)
    (hlarge_nonneg : ∀ᶠ X in atTop, 0 ≤ largePrime X)
    (hmass : ∀ᶠ X in atTop, μ X ≤ Cμ * (Real.log X) ^ 3)
    (hmedUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * medScale X ≤ Cmed * (Real.log X) ^ (-ηmed))
    (htailUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * depTail X ≤ Ctail * (Real.log X) ^ (-ηtail))
    (hδ_le : ∀ᶠ X in atTop, δb X ≤ C₁ * (μ X * medScale X) + largePrime X)
    (hΔ_le : ∀ᶠ X in atTop, Δb X ≤ C₂ * ((μ X) ^ 2 * depTail X))
    (hlarge_le : ∀ᶠ X in atTop, largePrime X ≤ Clarge * X ^ (-ηlarge)) :
    Tendsto δb atTop (𝓝 0)
    ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0) := by
  have hscale := mass_dependency_scale_from_log_power_bounds_eventually_nonneg
    μ depTail medScale Cμ Cmed Ctail ηmed ηtail hηmed hηtail
    hμ_nonneg hmass hmedNonneg htailNonneg hmedUpper htailUpper hCμ
  exact delta_Delta_bounds_from_large_prime_power_saving_eventually_nonneg
    μ δb Δb medScale depTail largePrime C₁ C₂ Clarge ηlarge
    hC₁ hC₂ hηlarge hδ_nonneg hΔ_nonneg hμ_nonneg
    hlarge_nonneg hδ_le hΔ_le hlarge_le hscale.1 hscale.2.2

/-! ## Part 4. `thm:CRT-nohit` — the `(1-o(1))` no-hit estimate. -/

/-- Suen-style envelope bound, ℝ-form (`thm:CRT-nohit`, tex 1930–1934).

We expose the exact inequality `prob ≤ exp(-μ + K·Δ·exp(2δ))` consumed by the
no-hit derivation.  It is projected from the packaged envelope theorem, so
downstream uses inherit the same carrier-range boundary; no new axiom is
created here. -/
theorem suen_real_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ μ δ Δ : ℝ, 0 ≤ μ → 0 ≤ δ → 0 ≤ Δ →
      Inputs.suenProb μ δ Δ ≤ Real.exp (-μ + K * Δ * Real.exp (2 * δ)) := by
  rcases Inputs.suenProb_bound_with_carrier_bounds with ⟨K, hK, hbound⟩
  exact ⟨K, hK, fun μ δ Δ hμ hδ hΔ => (hbound μ δ Δ hμ hδ hΔ).2.2.2.2.2⟩

/-- **Pointwise `(1-ε)` rewriting of the Suen exponent.**

For `μ > 0`, with `ε := K·Δ·exp(2δ)/μ`, the Suen exponent equals `-(1-ε)·μ`:
`-μ + K·Δ·exp(2δ) = -(1-ε)·μ`.  This is the algebraic heart of the
`exp{-(1-o(1))μ}` conclusion (tex 1925, 1933). -/
theorem suen_exponent_eq
    (μ δ Δ K : ℝ) (hμ : μ ≠ 0) :
    -μ + (K * Δ) * Real.exp (2 * δ)
      = -(1 - (K * Δ) * Real.exp (2 * δ) / μ) * μ := by
  field_simp
  ring

/-- **Base-conditioned CRT no-hit estimate, abstract real form**
(`thm:CRT-nohit`, tex 1922–1938).

Indexing by the manuscript variable `X → ∞`, take:

* the Suen-style envelope bound, pointwise:
  `prob X ≤ exp(-μ_b X + K·Δ_b X·exp(2 δ_b X))` (from `suen_real_bound`);
* `δ_b → 0` and `Δ_b = o(μ_b)` (the conclusions of `lem:delta-Delta`);
* `μ_b → ∞` (consequence of the mass law `μ_b ≍ (log X)³`), giving
  eventual positivity of `μ_b`.

Define the explicit `o(1)` defect `ε_b X := K·Δ_b X·exp(2 δ_b X)/μ_b X`.  Then
`ε_b → 0` and, eventually, `prob X ≤ exp(-(1-ε_b X)·μ_b X)` — i.e. the manuscript's
`P(W_b = 0) ≤ exp{-(1-o(1)) μ_b}`.  Real-analysis derivation. -/
theorem crt_nohit
    (μ δb Δb prob : ℝ → ℝ) (K : ℝ) (_hK : 0 ≤ K)
    (_hμ_nonneg : ∀ X, 0 ≤ μ X)
    (hsuen : ∀ᶠ X in atTop,
      prob X ≤ Real.exp (-μ X + (K * Δb X) * Real.exp (2 * δb X)))
    (hδ0 : Tendsto δb atTop (𝓝 0))
    (hΔ_o_μ : Tendsto (fun X => Δb X / μ X) atTop (𝓝 0))
    (hμ_top : Tendsto μ atTop atTop) :
    ∃ εb : ℝ → ℝ, Tendsto εb atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop, prob X ≤ Real.exp (-(1 - εb X) * μ X)) := by
  -- the explicit o(1) defect
  refine ⟨fun X => (K * Δb X) * Real.exp (2 * δb X) / μ X, ?_, ?_⟩
  · -- εb = K · (Δb/μ) · exp(2δb) → K · 0 · exp 0 = 0
    have hexp : Tendsto (fun X => Real.exp (2 * δb X)) atTop (𝓝 1) := by
      have h2δ : Tendsto (fun X => 2 * δb X) atTop (𝓝 0) := by
        simpa using hδ0.const_mul (2 : ℝ)
      have := (Real.continuous_exp.tendsto (0 : ℝ)).comp h2δ
      simpa using this
    have hratio : Tendsto (fun X => K * (Δb X / μ X)) atTop (𝓝 0) := by
      simpa using hΔ_o_μ.const_mul K
    have hprod : Tendsto
        (fun X => (K * (Δb X / μ X)) * Real.exp (2 * δb X)) atTop (𝓝 (0 * 1)) :=
      hratio.mul hexp
    have hpt : (fun X => (K * Δb X) * Real.exp (2 * δb X) / μ X)
        = (fun X => (K * (Δb X / μ X)) * Real.exp (2 * δb X)) := by
      funext X
      rcases eq_or_ne (μ X) 0 with h0 | h0
      · simp [h0]
      · field_simp
    rw [hpt]; simpa using hprod
  · -- prob X ≤ exp(-μ + K Δ exp(2δ)) = exp(-(1-εb) μ), once μ X ≠ 0
    have hμpos : ∀ᶠ X in atTop, 0 < μ X :=
      hμ_top.eventually (eventually_gt_atTop 0)
    filter_upwards [hsuen, hμpos] with X hX hμX
    have hμne : μ X ≠ 0 := ne_of_gt hμX
    have hrw := suen_exponent_eq (μ X) (δb X) (Δb X) K hμne
    rwa [hrw] at hX

/-- CRT no-hit estimate with the explicit defect's eventual nonnegativity.

This is the same real-variable derivation as `crt_nohit`, but it exposes one
more piece of data used by the finite-transfer layer: for the Suen defect
`ε_b X = K Δ_b(X) exp(2δ_b(X))/μ_b(X)`, the assumptions `K ≥ 0`, `Δ_b ≥ 0`,
and eventual positivity of `μ_b` imply `ε_b ≥ 0` eventually. -/
theorem crt_nohit_with_nonneg_defect
    (μ δb Δb prob : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (_hμ_nonneg : ∀ X, 0 ≤ μ X)
    (hΔ_nonneg : ∀ X, 0 ≤ Δb X)
    (hsuen : ∀ᶠ X in atTop,
      prob X ≤ Real.exp (-μ X + (K * Δb X) * Real.exp (2 * δb X)))
    (hδ0 : Tendsto δb atTop (𝓝 0))
    (hΔ_o_μ : Tendsto (fun X => Δb X / μ X) atTop (𝓝 0))
    (hμ_top : Tendsto μ atTop atTop) :
    ∃ εb : ℝ → ℝ, Tendsto εb atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop, 0 ≤ εb X)
      ∧ (∀ᶠ X in atTop, prob X ≤ Real.exp (-(1 - εb X) * μ X)) := by
  refine ⟨fun X => (K * Δb X) * Real.exp (2 * δb X) / μ X, ?_, ?_, ?_⟩
  · have hexp : Tendsto (fun X => Real.exp (2 * δb X)) atTop (𝓝 1) := by
      have h2δ : Tendsto (fun X => 2 * δb X) atTop (𝓝 0) := by
        simpa using hδ0.const_mul (2 : ℝ)
      have := (Real.continuous_exp.tendsto (0 : ℝ)).comp h2δ
      simpa using this
    have hratio : Tendsto (fun X => K * (Δb X / μ X)) atTop (𝓝 0) := by
      simpa using hΔ_o_μ.const_mul K
    have hprod : Tendsto
        (fun X => (K * (Δb X / μ X)) * Real.exp (2 * δb X)) atTop (𝓝 (0 * 1)) :=
      hratio.mul hexp
    have hpt : (fun X => (K * Δb X) * Real.exp (2 * δb X) / μ X)
        = (fun X => (K * (Δb X / μ X)) * Real.exp (2 * δb X)) := by
      funext X
      rcases eq_or_ne (μ X) 0 with h0 | h0
      · simp [h0]
      · field_simp
    rw [hpt]; simpa using hprod
  · have hμpos : ∀ᶠ X in atTop, 0 < μ X :=
      hμ_top.eventually (eventually_gt_atTop 0)
    filter_upwards [hμpos] with X hμX
    exact div_nonneg
      (mul_nonneg (mul_nonneg hK (hΔ_nonneg X)) (le_of_lt (Real.exp_pos _)))
      (le_of_lt hμX)
  · have hμpos : ∀ᶠ X in atTop, 0 < μ X :=
      hμ_top.eventually (eventually_gt_atTop 0)
    filter_upwards [hsuen, hμpos] with X hX hμX
    have hμne : μ X ≠ 0 := ne_of_gt hμX
    have hrw := suen_exponent_eq (μ X) (δb X) (Δb X) K hμne
    rwa [hrw] at hX

/-- **CRT no-hit envelope estimate** (`thm:CRT-nohit`).

This applies `crt_nohit` to the formal no-hit envelope
`fun X => Inputs.suenProb (μ X) (δb X) (Δb X)`, with the per-`X` Suen bound
discharged from the packaged carrier-bound theorem (not from a free hypothesis).
Thus the `exp{-(1-o(1))μ_b}` envelope conclusion follows from the checked range
facts, the carrier tail bound, and the dependency bounds `δ_b → 0`,
`Δ_b = o(μ_b)`, and `μ_b → ∞`. -/
theorem crt_nohit_of_suen
    (μ δb Δb : ℝ → ℝ)
    (hμ_nonneg : ∀ X, 0 ≤ μ X) (hδ_nonneg : ∀ X, 0 ≤ δb X) (hΔ_nonneg : ∀ X, 0 ≤ Δb X)
    (hδ0 : Tendsto δb atTop (𝓝 0))
    (hΔ_o_μ : Tendsto (fun X => Δb X / μ X) atTop (𝓝 0))
    (hμ_top : Tendsto μ atTop atTop) :
    ∃ εb : ℝ → ℝ, Tendsto εb atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop,
          Inputs.suenProb (μ X) (δb X) (Δb X) ≤ Real.exp (-(1 - εb X) * μ X)) := by
  obtain ⟨K, hKpos, hbound⟩ := Inputs.suenProb_bound_with_carrier_bounds
  refine crt_nohit μ δb Δb (fun X => Inputs.suenProb (μ X) (δb X) (Δb X)) K hKpos.le
    hμ_nonneg ?_ hδ0 hΔ_o_μ hμ_top
  filter_upwards with X
  rcases hbound (μ X) (δb X) (Δb X) (hμ_nonneg X) (hδ_nonneg X) (hΔ_nonneg X) with
    ⟨_htail_pos, _hrange, _hprob_nonneg, _hprob_le_one, _habsolute, htail⟩
  simpa [mul_assoc] using htail

/-- CRT no-hit estimate with the checked probability range carried alongside
the final exponential bound.

The Suen carrier is clipped in `Inputs`, so the no-hit layer can expose the
unit-interval probability fact without taking it as a separate hypothesis. -/
theorem crt_nohit_of_suen_with_range
    (μ δb Δb : ℝ → ℝ)
    (hμ_nonneg : ∀ X, 0 ≤ μ X) (hδ_nonneg : ∀ X, 0 ≤ δb X) (hΔ_nonneg : ∀ X, 0 ≤ Δb X)
    (hδ0 : Tendsto δb atTop (𝓝 0))
    (hΔ_o_μ : Tendsto (fun X => Δb X / μ X) atTop (𝓝 0))
    (hμ_top : Tendsto μ atTop atTop) :
    ∃ εb : ℝ → ℝ, Tendsto εb atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop,
          Inputs.suenProb (μ X) (δb X) (Δb X) ∈ Set.Icc 0 1 ∧
          Inputs.suenProb (μ X) (δb X) (Δb X) ≤ Real.exp (-(1 - εb X) * μ X)) := by
  rcases crt_nohit_of_suen μ δb Δb hμ_nonneg hδ_nonneg hΔ_nonneg
      hδ0 hΔ_o_μ hμ_top with ⟨εb, hεb, hbound⟩
  obtain ⟨_K, _hKpos, hsuenRange⟩ := Inputs.suenProb_bound_with_carrier_bounds
  refine ⟨εb, hεb, ?_⟩
  filter_upwards [hbound] with X hX
  rcases hsuenRange (μ X) (δb X) (Δb X) (hμ_nonneg X) (hδ_nonneg X) (hΔ_nonneg X) with
    ⟨_htail_pos, hrange, _hprob_nonneg, _hprob_le_one, _habsolute, _htail⟩
  exact ⟨hrange, hX⟩

/-- CRT no-hit estimate with both downstream-facing facts exposed:
eventual nonnegativity of the explicit `o(1)` defect and the checked
unit-interval range for the Suen carrier probability. -/
theorem crt_nohit_of_suen_with_range_and_nonneg_defect
    (μ δb Δb : ℝ → ℝ)
    (hμ_nonneg : ∀ X, 0 ≤ μ X) (hδ_nonneg : ∀ X, 0 ≤ δb X) (hΔ_nonneg : ∀ X, 0 ≤ Δb X)
    (hδ0 : Tendsto δb atTop (𝓝 0))
    (hΔ_o_μ : Tendsto (fun X => Δb X / μ X) atTop (𝓝 0))
    (hμ_top : Tendsto μ atTop atTop) :
    ∃ εb : ℝ → ℝ, Tendsto εb atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop, 0 ≤ εb X)
      ∧ (∀ᶠ X in atTop,
          Inputs.suenProb (μ X) (δb X) (Δb X) ∈ Set.Icc 0 1 ∧
          Inputs.suenProb (μ X) (δb X) (Δb X) ≤ Real.exp (-(1 - εb X) * μ X)) := by
  obtain ⟨K, hKpos, hbound⟩ := Inputs.suenProb_bound_with_carrier_bounds
  have hsuen : ∀ᶠ X in atTop,
      Inputs.suenProb (μ X) (δb X) (Δb X)
        ≤ Real.exp (-μ X + (K * Δb X) * Real.exp (2 * δb X)) := by
    filter_upwards with X
    rcases hbound (μ X) (δb X) (Δb X) (hμ_nonneg X) (hδ_nonneg X) (hΔ_nonneg X) with
      ⟨_htail_pos, _hrange, _hprob_nonneg, _hprob_le_one, _habsolute, htail⟩
    simpa [mul_assoc] using htail
  rcases crt_nohit_with_nonneg_defect μ δb Δb
      (fun X => Inputs.suenProb (μ X) (δb X) (Δb X)) K hKpos.le
      hμ_nonneg hΔ_nonneg hsuen hδ0 hΔ_o_μ hμ_top with
    ⟨εb, hεb, hεb_nonneg, hnohit⟩
  refine ⟨εb, hεb, hεb_nonneg, ?_⟩
  filter_upwards [hnohit] with X hX
  rcases hbound (μ X) (δb X) (Δb X) (hμ_nonneg X) (hδ_nonneg X) (hΔ_nonneg X) with
    ⟨_htail_pos, hrange, _hprob_nonneg, _hprob_le_one, _habsolute, _htail⟩
  exact ⟨hrange, hX⟩

/-- Eventual-nonnegativity version of
`crt_nohit_of_suen_with_range_and_nonneg_defect`.

The Suen carrier bound is only used eventually in the no-hit transfer.  This
variant therefore accepts eventual nonnegativity of `μ`, `δ_b`, and `Δ_b`, and
derives the same downstream range/no-hit facts on a large range. -/
theorem crt_nohit_of_suen_with_range_and_nonneg_defect_eventually_nonneg
    (μ δb Δb : ℝ → ℝ)
    (hμ_nonneg : ∀ᶠ X in atTop, 0 ≤ μ X)
    (hδ_nonneg : ∀ᶠ X in atTop, 0 ≤ δb X)
    (hΔ_nonneg : ∀ᶠ X in atTop, 0 ≤ Δb X)
    (hδ0 : Tendsto δb atTop (𝓝 0))
    (hΔ_o_μ : Tendsto (fun X => Δb X / μ X) atTop (𝓝 0))
    (hμ_top : Tendsto μ atTop atTop) :
    ∃ εb : ℝ → ℝ, Tendsto εb atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop, 0 ≤ εb X)
      ∧ (∀ᶠ X in atTop,
          Inputs.suenProb (μ X) (δb X) (Δb X) ∈ Set.Icc 0 1 ∧
          Inputs.suenProb (μ X) (δb X) (Δb X) ≤ Real.exp (-(1 - εb X) * μ X)) := by
  obtain ⟨K, hKpos, hbound⟩ := Inputs.suenProb_bound_with_carrier_bounds
  let εb : ℝ → ℝ := fun X => (K * Δb X) * Real.exp (2 * δb X) / μ X
  have hεb0 : Tendsto εb atTop (𝓝 0) := by
    have hexp : Tendsto (fun X => Real.exp (2 * δb X)) atTop (𝓝 1) := by
      have h2δ : Tendsto (fun X => 2 * δb X) atTop (𝓝 0) := by
        simpa using hδ0.const_mul (2 : ℝ)
      have := (Real.continuous_exp.tendsto (0 : ℝ)).comp h2δ
      simpa using this
    have hratio : Tendsto (fun X => K * (Δb X / μ X)) atTop (𝓝 0) := by
      simpa using hΔ_o_μ.const_mul K
    have hprod : Tendsto
        (fun X => (K * (Δb X / μ X)) * Real.exp (2 * δb X)) atTop (𝓝 (0 * 1)) :=
      hratio.mul hexp
    have hpt : (fun X => (K * Δb X) * Real.exp (2 * δb X) / μ X)
        = (fun X => (K * (Δb X / μ X)) * Real.exp (2 * δb X)) := by
      funext X
      rcases eq_or_ne (μ X) 0 with h0 | h0
      · simp [h0]
      · field_simp
    rw [show εb = fun X => (K * Δb X) * Real.exp (2 * δb X) / μ X by rfl]
    rw [hpt]
    simpa using hprod
  have hεb_nonneg : ∀ᶠ X in atTop, 0 ≤ εb X := by
    have hμpos : ∀ᶠ X in atTop, 0 < μ X :=
      hμ_top.eventually (eventually_gt_atTop 0)
    filter_upwards [hΔ_nonneg, hμpos] with X hΔX hμX
    exact div_nonneg
      (mul_nonneg (mul_nonneg hKpos.le hΔX) (le_of_lt (Real.exp_pos _)))
      (le_of_lt hμX)
  have hsuen : ∀ᶠ X in atTop,
      Inputs.suenProb (μ X) (δb X) (Δb X)
        ≤ Real.exp (-μ X + (K * Δb X) * Real.exp (2 * δb X)) := by
    filter_upwards [hμ_nonneg, hδ_nonneg, hΔ_nonneg] with X hμX hδX hΔX
    rcases hbound (μ X) (δb X) (Δb X) hμX hδX hΔX with
      ⟨_htail_pos, _hrange, _hprob_nonneg, _hprob_le_one, _habsolute, htail⟩
    simpa [mul_assoc] using htail
  have hnohit : ∀ᶠ X in atTop,
      Inputs.suenProb (μ X) (δb X) (Δb X)
        ≤ Real.exp (-(1 - εb X) * μ X) := by
    have hμpos : ∀ᶠ X in atTop, 0 < μ X :=
      hμ_top.eventually (eventually_gt_atTop 0)
    filter_upwards [hsuen, hμpos] with X hX hμX
    have hμne : μ X ≠ 0 := ne_of_gt hμX
    have hrw := suen_exponent_eq (μ X) (δb X) (Δb X) K hμne
    have hexp_eq :
        Real.exp (-μ X + K * Δb X * Real.exp (2 * δb X))
          = Real.exp (-(1 - εb X) * μ X) := by
      rw [show εb X = (K * Δb X) * Real.exp (2 * δb X) / μ X by rfl]
      rw [hrw]
    rwa [hexp_eq] at hX
  refine ⟨εb, hεb0, hεb_nonneg, ?_⟩
  filter_upwards [hnohit, hμ_nonneg, hδ_nonneg, hΔ_nonneg] with X hX hμX hδX hΔX
  rcases hbound (μ X) (δb X) (Δb X) hμX hδX hΔX with
    ⟨_htail_pos, hrange, _hprob_nonneg, _hprob_le_one, _habsolute, _htail⟩
  exact ⟨hrange, hX⟩

/-! ## Part 4b. Paper-facing Brun/Suen package. -/

/-- Combined real-variable package for the Brun/Suen part of the manuscript.

This theorem checks the paper's composition step from the appendage bound,
mass/dependency logarithmic scale envelopes, dependency inequalities, a
large-prime-neighbour power saving, and the cited Suen carrier theorem to the
downstream no-hit envelope.  The only standard input used by this package is the
Suen carrier through `crt_nohit_of_suen_with_range_and_nonneg_defect_eventually_nonneg`;
all scale and squeeze arguments are theorem-level consequences of the displayed
hypotheses. -/
theorem brun_suen_real_variable_package_from_log_power_bounds
    (ε μ δb Δb medScale depTail largePrime : ℝ → ℝ)
    (Cε Cμ Cmed Ctail C₁ C₂ Clarge ηmed ηtail ηlarge : ℝ)
    (hηmed : 0 < ηmed) (hηtail : 0 < ηtail) (hηlarge : 0 < ηlarge)
    (hCμ : 0 ≤ Cμ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hμ_nonneg_all : ∀ X, 0 ≤ μ X)
    (hε_nonneg : ∀ᶠ X in atTop, 0 ≤ ε X)
    (hδ_nonneg : ∀ᶠ X in atTop, 0 ≤ δb X)
    (hΔ_nonneg : ∀ᶠ X in atTop, 0 ≤ Δb X)
    (hmedNonneg : ∀ᶠ X in atTop, 0 ≤ medScale X)
    (htailNonneg : ∀ᶠ X in atTop, 0 ≤ depTail X)
    (hlarge_nonneg : ∀ᶠ X in atTop, 0 ≤ largePrime X)
    (happendage_le : ∀ᶠ X in atTop, ε X ≤ Cε * (μ X * medScale X))
    (hmass : ∀ᶠ X in atTop, μ X ≤ Cμ * (Real.log X) ^ 3)
    (hmedUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * medScale X ≤ Cmed * (Real.log X) ^ (-ηmed))
    (htailUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * depTail X ≤ Ctail * (Real.log X) ^ (-ηtail))
    (hδ_le : ∀ᶠ X in atTop, δb X ≤ C₁ * (μ X * medScale X) + largePrime X)
    (hΔ_le : ∀ᶠ X in atTop, Δb X ≤ C₂ * ((μ X) ^ 2 * depTail X))
    (hlarge_le : ∀ᶠ X in atTop, largePrime X ≤ Clarge * X ^ (-ηlarge))
    (hμ_top : Tendsto μ atTop atTop) :
    Tendsto ε atTop (𝓝 0)
    ∧ Tendsto (fun X => μ X * medScale X) atTop (𝓝 0)
    ∧ Tendsto (fun X => μ X * depTail X) atTop (𝓝 0)
    ∧ Tendsto (fun X => (μ X) ^ 2 * depTail X / μ X) atTop (𝓝 0)
    ∧ Tendsto δb atTop (𝓝 0)
    ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0)
    ∧ ∃ εb : ℝ → ℝ, Tendsto εb atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop, 0 ≤ εb X)
      ∧ (∀ᶠ X in atTop,
          Inputs.suenProb (μ X) (δb X) (Δb X) ∈ Set.Icc 0 1 ∧
          Inputs.suenProb (μ X) (δb X) (Δb X) ≤ Real.exp (-(1 - εb X) * μ X)) := by
  have hscale := mass_dependency_scale_from_log_power_bounds
    μ depTail medScale Cμ Cmed Ctail ηmed ηtail hηmed hηtail
    hμ_nonneg_all hmass hmedNonneg htailNonneg hmedUpper htailUpper hCμ
  have happendage : Tendsto ε atTop (𝓝 0) :=
    appendage_error_tendsto_zero_of_mass_medScale
      ε μ medScale Cε hε_nonneg happendage_le hscale.1
  have hdeps :
      Tendsto δb atTop (𝓝 0)
        ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0) :=
    delta_Delta_bounds_from_log_power_bounds_and_large_prime_power_saving
      μ δb Δb medScale depTail largePrime
      Cμ Cmed Ctail C₁ C₂ Clarge ηmed ηtail ηlarge
      hηmed hηtail hηlarge hCμ hC₁ hC₂ hμ_nonneg_all
      hδ_nonneg hΔ_nonneg hmedNonneg htailNonneg hlarge_nonneg hmass
      hmedUpper htailUpper hδ_le hΔ_le hlarge_le
  have hnohit :
      ∃ εb : ℝ → ℝ, Tendsto εb atTop (𝓝 0)
        ∧ (∀ᶠ X in atTop, 0 ≤ εb X)
        ∧ (∀ᶠ X in atTop,
            Inputs.suenProb (μ X) (δb X) (Δb X) ∈ Set.Icc 0 1 ∧
            Inputs.suenProb (μ X) (δb X) (Δb X) ≤ Real.exp (-(1 - εb X) * μ X)) :=
    crt_nohit_of_suen_with_range_and_nonneg_defect_eventually_nonneg
      μ δb Δb (Eventually.of_forall hμ_nonneg_all) hδ_nonneg hΔ_nonneg
      hdeps.1 hdeps.2 hμ_top
  exact ⟨happendage, hscale.1, hscale.2.1, hscale.2.2, hdeps.1, hdeps.2, hnohit⟩

/-- Eventual-nonnegativity version of
`brun_suen_real_variable_package_from_log_power_bounds`.

The paper only consumes this package on a sufficiently large tail.  This variant
therefore removes the artificial global mass-nonnegativity hypothesis and keeps
only the large-`X` statement actually used by the squeeze and Suen steps. -/
theorem brun_suen_real_variable_package_from_log_power_bounds_eventually_nonneg
    (ε μ δb Δb medScale depTail largePrime : ℝ → ℝ)
    (Cε Cμ Cmed Ctail C₁ C₂ Clarge ηmed ηtail ηlarge : ℝ)
    (hηmed : 0 < ηmed) (hηtail : 0 < ηtail) (hηlarge : 0 < ηlarge)
    (hCμ : 0 ≤ Cμ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hμ_nonneg : ∀ᶠ X in atTop, 0 ≤ μ X)
    (hε_nonneg : ∀ᶠ X in atTop, 0 ≤ ε X)
    (hδ_nonneg : ∀ᶠ X in atTop, 0 ≤ δb X)
    (hΔ_nonneg : ∀ᶠ X in atTop, 0 ≤ Δb X)
    (hmedNonneg : ∀ᶠ X in atTop, 0 ≤ medScale X)
    (htailNonneg : ∀ᶠ X in atTop, 0 ≤ depTail X)
    (hlarge_nonneg : ∀ᶠ X in atTop, 0 ≤ largePrime X)
    (happendage_le : ∀ᶠ X in atTop, ε X ≤ Cε * (μ X * medScale X))
    (hmass : ∀ᶠ X in atTop, μ X ≤ Cμ * (Real.log X) ^ 3)
    (hmedUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * medScale X ≤ Cmed * (Real.log X) ^ (-ηmed))
    (htailUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * depTail X ≤ Ctail * (Real.log X) ^ (-ηtail))
    (hδ_le : ∀ᶠ X in atTop, δb X ≤ C₁ * (μ X * medScale X) + largePrime X)
    (hΔ_le : ∀ᶠ X in atTop, Δb X ≤ C₂ * ((μ X) ^ 2 * depTail X))
    (hlarge_le : ∀ᶠ X in atTop, largePrime X ≤ Clarge * X ^ (-ηlarge))
    (hμ_top : Tendsto μ atTop atTop) :
    Tendsto ε atTop (𝓝 0)
    ∧ Tendsto (fun X => μ X * medScale X) atTop (𝓝 0)
    ∧ Tendsto (fun X => μ X * depTail X) atTop (𝓝 0)
    ∧ Tendsto (fun X => (μ X) ^ 2 * depTail X / μ X) atTop (𝓝 0)
    ∧ Tendsto δb atTop (𝓝 0)
    ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0)
    ∧ ∃ εb : ℝ → ℝ, Tendsto εb atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop, 0 ≤ εb X)
      ∧ (∀ᶠ X in atTop,
          Inputs.suenProb (μ X) (δb X) (Δb X) ∈ Set.Icc 0 1 ∧
          Inputs.suenProb (μ X) (δb X) (Δb X) ≤ Real.exp (-(1 - εb X) * μ X)) := by
  have hscale := mass_dependency_scale_from_log_power_bounds_eventually_nonneg
    μ depTail medScale Cμ Cmed Ctail ηmed ηtail hηmed hηtail
    hμ_nonneg hmass hmedNonneg htailNonneg hmedUpper htailUpper hCμ
  have happendage : Tendsto ε atTop (𝓝 0) :=
    appendage_error_tendsto_zero_of_mass_medScale
      ε μ medScale Cε hε_nonneg happendage_le hscale.1
  have hdeps :
      Tendsto δb atTop (𝓝 0)
        ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0) :=
    delta_Delta_bounds_from_log_power_bounds_and_large_prime_power_saving_eventually_nonneg
      μ δb Δb medScale depTail largePrime
      Cμ Cmed Ctail C₁ C₂ Clarge ηmed ηtail ηlarge
      hηmed hηtail hηlarge hCμ hC₁ hC₂ hμ_nonneg
      hδ_nonneg hΔ_nonneg hmedNonneg htailNonneg hlarge_nonneg hmass
      hmedUpper htailUpper hδ_le hΔ_le hlarge_le
  have hnohit :
      ∃ εb : ℝ → ℝ, Tendsto εb atTop (𝓝 0)
        ∧ (∀ᶠ X in atTop, 0 ≤ εb X)
        ∧ (∀ᶠ X in atTop,
            Inputs.suenProb (μ X) (δb X) (Δb X) ∈ Set.Icc 0 1 ∧
            Inputs.suenProb (μ X) (δb X) (Δb X) ≤ Real.exp (-(1 - εb X) * μ X)) :=
    crt_nohit_of_suen_with_range_and_nonneg_defect_eventually_nonneg
      μ δb Δb hμ_nonneg hδ_nonneg hΔ_nonneg hdeps.1 hdeps.2 hμ_top
  exact ⟨happendage, hscale.1, hscale.2.1, hscale.2.2, hdeps.1, hdeps.2, hnohit⟩

/-- Paper-local Brun/Suen output bundle.

This packages the finite elementary-symmetric Brun envelope together with the
real-variable appendage, large-prime-neighbour, mass/dependency, dependency
parameter, and Suen no-hit outputs.  It is a theorem-level composition of the
local ingredients used in the manuscript around `lem:appendage`, `thm:Brun`,
`prop:mass-dependency-scale`, `lem:large-prime-neighbour`, `lem:delta-Delta`,
and `thm:CRT-nohit`; the only cited analytic input in the dependency closure is
the standard Suen carrier theorem. -/
theorem brun_suen_paper_local_outputs_from_log_power_bounds
    (weights : List ℚ) (M Xq : ℚ) (R : ℕ)
    (ε μ δb Δb medScale depTail largePrime : ℝ → ℝ)
    (Cε Cμ Cmed Ctail C₁ C₂ Clarge ηmed ηtail ηlarge : ℝ)
    (hnn : ∀ w ∈ weights, 0 ≤ w)
    (hmassQ : weights.sum ≤ M)
    (hXq : 1 ≤ Xq)
    (hηmed : 0 < ηmed) (hηtail : 0 < ηtail) (hηlarge : 0 < ηlarge)
    (hCμ : 0 ≤ Cμ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hμ_nonneg_all : ∀ X, 0 ≤ μ X)
    (hε_nonneg : ∀ᶠ X in atTop, 0 ≤ ε X)
    (hδ_nonneg : ∀ᶠ X in atTop, 0 ≤ δb X)
    (hΔ_nonneg : ∀ᶠ X in atTop, 0 ≤ Δb X)
    (hmedNonneg : ∀ᶠ X in atTop, 0 ≤ medScale X)
    (htailNonneg : ∀ᶠ X in atTop, 0 ≤ depTail X)
    (hlarge_nonneg : ∀ᶠ X in atTop, 0 ≤ largePrime X)
    (happendage_le : ∀ᶠ X in atTop, ε X ≤ Cε * (μ X * medScale X))
    (hmass : ∀ᶠ X in atTop, μ X ≤ Cμ * (Real.log X) ^ 3)
    (hmedUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * medScale X ≤ Cmed * (Real.log X) ^ (-ηmed))
    (htailUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * depTail X ≤ Ctail * (Real.log X) ^ (-ηtail))
    (hδ_le : ∀ᶠ X in atTop, δb X ≤ C₁ * (μ X * medScale X) + largePrime X)
    (hΔ_le : ∀ᶠ X in atTop, Δb X ≤ C₂ * ((μ X) ^ 2 * depTail X))
    (hlarge_le : ∀ᶠ X in atTop, largePrime X ≤ Clarge * X ^ (-ηlarge))
    (hμ_top : Tendsto μ atTop atTop) :
    (∑ r ∈ Finset.range (2 * R + 1),
        (Xq : ℝ) ^ r * (EscLeanChecks.elemSymmList weights r : ℝ))
      ≤ (Xq : ℝ) ^ (2 * R) * Real.exp (M : ℝ)
    ∧ Tendsto ε atTop (𝓝 0)
    ∧ Tendsto largePrime atTop (𝓝 0)
    ∧ Tendsto (fun X => μ X * medScale X) atTop (𝓝 0)
    ∧ Tendsto (fun X => μ X * depTail X) atTop (𝓝 0)
    ∧ Tendsto (fun X => (μ X) ^ 2 * depTail X / μ X) atTop (𝓝 0)
    ∧ Tendsto δb atTop (𝓝 0)
    ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0)
    ∧ ∃ εb : ℝ → ℝ, Tendsto εb atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop, 0 ≤ εb X)
      ∧ (∀ᶠ X in atTop,
          Inputs.suenProb (μ X) (δb X) (Δb X) ∈ Set.Icc 0 1 ∧
          Inputs.suenProb (μ X) (δb X) (Δb X) ≤ Real.exp (-(1 - εb X) * μ X)) := by
  have hbrun :=
    brun_envelope_elemSymm_rational_weights weights M Xq R hnn hmassQ hXq
  have hlarge0 :
      Tendsto largePrime atTop (𝓝 0) :=
    large_prime_neighbour_power_saving_tendsto_zero_eventually_nonneg
      largePrime Clarge ηlarge hηlarge hlarge_nonneg hlarge_le
  have hpkg :=
    brun_suen_real_variable_package_from_log_power_bounds
      ε μ δb Δb medScale depTail largePrime
      Cε Cμ Cmed Ctail C₁ C₂ Clarge ηmed ηtail ηlarge
      hηmed hηtail hηlarge hCμ hC₁ hC₂ hμ_nonneg_all
      hε_nonneg hδ_nonneg hΔ_nonneg hmedNonneg htailNonneg hlarge_nonneg
      happendage_le hmass hmedUpper htailUpper hδ_le hΔ_le hlarge_le hμ_top
  exact
    ⟨hbrun, hpkg.1, hlarge0, hpkg.2.1, hpkg.2.2.1, hpkg.2.2.2.1,
      hpkg.2.2.2.2.1, hpkg.2.2.2.2.2.1, hpkg.2.2.2.2.2.2⟩

/-- Eventual-nonnegativity version of
`brun_suen_paper_local_outputs_from_log_power_bounds`.

This is the paper-facing bundle with the finite-initial-range mass sign
condition removed.  The remaining hypotheses are the displayed log-power,
large-prime, appendage, and Suen-carrier inputs. -/
theorem brun_suen_paper_local_outputs_from_log_power_bounds_eventually_nonneg
    (weights : List ℚ) (M Xq : ℚ) (R : ℕ)
    (ε μ δb Δb medScale depTail largePrime : ℝ → ℝ)
    (Cε Cμ Cmed Ctail C₁ C₂ Clarge ηmed ηtail ηlarge : ℝ)
    (hnn : ∀ w ∈ weights, 0 ≤ w)
    (hmassQ : weights.sum ≤ M)
    (hXq : 1 ≤ Xq)
    (hηmed : 0 < ηmed) (hηtail : 0 < ηtail) (hηlarge : 0 < ηlarge)
    (hCμ : 0 ≤ Cμ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hμ_nonneg : ∀ᶠ X in atTop, 0 ≤ μ X)
    (hε_nonneg : ∀ᶠ X in atTop, 0 ≤ ε X)
    (hδ_nonneg : ∀ᶠ X in atTop, 0 ≤ δb X)
    (hΔ_nonneg : ∀ᶠ X in atTop, 0 ≤ Δb X)
    (hmedNonneg : ∀ᶠ X in atTop, 0 ≤ medScale X)
    (htailNonneg : ∀ᶠ X in atTop, 0 ≤ depTail X)
    (hlarge_nonneg : ∀ᶠ X in atTop, 0 ≤ largePrime X)
    (happendage_le : ∀ᶠ X in atTop, ε X ≤ Cε * (μ X * medScale X))
    (hmass : ∀ᶠ X in atTop, μ X ≤ Cμ * (Real.log X) ^ 3)
    (hmedUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * medScale X ≤ Cmed * (Real.log X) ^ (-ηmed))
    (htailUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * depTail X ≤ Ctail * (Real.log X) ^ (-ηtail))
    (hδ_le : ∀ᶠ X in atTop, δb X ≤ C₁ * (μ X * medScale X) + largePrime X)
    (hΔ_le : ∀ᶠ X in atTop, Δb X ≤ C₂ * ((μ X) ^ 2 * depTail X))
    (hlarge_le : ∀ᶠ X in atTop, largePrime X ≤ Clarge * X ^ (-ηlarge))
    (hμ_top : Tendsto μ atTop atTop) :
    (∑ r ∈ Finset.range (2 * R + 1),
        (Xq : ℝ) ^ r * (EscLeanChecks.elemSymmList weights r : ℝ))
      ≤ (Xq : ℝ) ^ (2 * R) * Real.exp (M : ℝ)
    ∧ Tendsto ε atTop (𝓝 0)
    ∧ Tendsto largePrime atTop (𝓝 0)
    ∧ Tendsto (fun X => μ X * medScale X) atTop (𝓝 0)
    ∧ Tendsto (fun X => μ X * depTail X) atTop (𝓝 0)
    ∧ Tendsto (fun X => (μ X) ^ 2 * depTail X / μ X) atTop (𝓝 0)
    ∧ Tendsto δb atTop (𝓝 0)
    ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0)
    ∧ ∃ εb : ℝ → ℝ, Tendsto εb atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop, 0 ≤ εb X)
      ∧ (∀ᶠ X in atTop,
          Inputs.suenProb (μ X) (δb X) (Δb X) ∈ Set.Icc 0 1 ∧
          Inputs.suenProb (μ X) (δb X) (Δb X) ≤ Real.exp (-(1 - εb X) * μ X)) := by
  have hbrun :=
    brun_envelope_elemSymm_rational_weights weights M Xq R hnn hmassQ hXq
  have hlarge0 :
      Tendsto largePrime atTop (𝓝 0) :=
    large_prime_neighbour_power_saving_tendsto_zero_eventually_nonneg
      largePrime Clarge ηlarge hηlarge hlarge_nonneg hlarge_le
  have hpkg :=
    brun_suen_real_variable_package_from_log_power_bounds_eventually_nonneg
      ε μ δb Δb medScale depTail largePrime
      Cε Cμ Cmed Ctail C₁ C₂ Clarge ηmed ηtail ηlarge
      hηmed hηtail hηlarge hCμ hC₁ hC₂ hμ_nonneg
      hε_nonneg hδ_nonneg hΔ_nonneg hmedNonneg htailNonneg hlarge_nonneg
      happendage_le hmass hmedUpper htailUpper hδ_le hΔ_le hlarge_le hμ_top
  exact
    ⟨hbrun, hpkg.1, hlarge0, hpkg.2.1, hpkg.2.2.1, hpkg.2.2.2.1,
      hpkg.2.2.2.2.1, hpkg.2.2.2.2.2.1, hpkg.2.2.2.2.2.2⟩

/-- Paper-local projection of the Brun elementary-symmetric envelope
(`thm:Brun`) from the checked finite coefficient carrier. -/
theorem brun_suen_paper_local_brun_envelope_from_log_power_bounds
    (weights : List ℚ) (M Xq : ℚ) (R : ℕ)
    (hnn : ∀ w ∈ weights, 0 ≤ w)
    (hmassQ : weights.sum ≤ M)
    (hXq : 1 ≤ Xq) :
    (∑ r ∈ Finset.range (2 * R + 1),
        (Xq : ℝ) ^ r * (EscLeanChecks.elemSymmList weights r : ℝ))
      ≤ (Xq : ℝ) ^ (2 * R) * Real.exp (M : ℝ) := by
  exact brun_envelope_elemSymm_rational_weights weights M Xq R hnn hmassQ hXq

/-- Paper-local projection of the appendage, large-prime-neighbour,
mass/dependency-scale, and dependency-parameter asymptotics.

This is the Suen-free part of the local Brun/Suen package: the no-hit estimate
is separated into `brun_suen_paper_local_nohit_output_from_log_power_bounds`,
while the real-variable asymptotic bookkeeping here is proved directly from the
displayed log-power and large-prime hypotheses. -/
theorem brun_suen_paper_local_asymptotic_outputs_from_log_power_bounds
    (ε μ δb Δb medScale depTail largePrime : ℝ → ℝ)
    (Cε Cμ Cmed Ctail C₁ C₂ Clarge ηmed ηtail ηlarge : ℝ)
    (hηmed : 0 < ηmed) (hηtail : 0 < ηtail) (hηlarge : 0 < ηlarge)
    (hCμ : 0 ≤ Cμ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hμ_nonneg_all : ∀ X, 0 ≤ μ X)
    (hε_nonneg : ∀ᶠ X in atTop, 0 ≤ ε X)
    (hδ_nonneg : ∀ᶠ X in atTop, 0 ≤ δb X)
    (hΔ_nonneg : ∀ᶠ X in atTop, 0 ≤ Δb X)
    (hmedNonneg : ∀ᶠ X in atTop, 0 ≤ medScale X)
    (htailNonneg : ∀ᶠ X in atTop, 0 ≤ depTail X)
    (hlarge_nonneg : ∀ᶠ X in atTop, 0 ≤ largePrime X)
    (happendage_le : ∀ᶠ X in atTop, ε X ≤ Cε * (μ X * medScale X))
    (hmass : ∀ᶠ X in atTop, μ X ≤ Cμ * (Real.log X) ^ 3)
    (hmedUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * medScale X ≤ Cmed * (Real.log X) ^ (-ηmed))
    (htailUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * depTail X ≤ Ctail * (Real.log X) ^ (-ηtail))
    (hδ_le : ∀ᶠ X in atTop, δb X ≤ C₁ * (μ X * medScale X) + largePrime X)
    (hΔ_le : ∀ᶠ X in atTop, Δb X ≤ C₂ * ((μ X) ^ 2 * depTail X))
    (hlarge_le : ∀ᶠ X in atTop, largePrime X ≤ Clarge * X ^ (-ηlarge)) :
    Tendsto ε atTop (𝓝 0)
    ∧ Tendsto largePrime atTop (𝓝 0)
    ∧ Tendsto (fun X => μ X * medScale X) atTop (𝓝 0)
    ∧ Tendsto (fun X => μ X * depTail X) atTop (𝓝 0)
    ∧ Tendsto (fun X => (μ X) ^ 2 * depTail X / μ X) atTop (𝓝 0)
    ∧ Tendsto δb atTop (𝓝 0)
    ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0) := by
  have hscale := mass_dependency_scale_from_log_power_bounds
    μ depTail medScale Cμ Cmed Ctail ηmed ηtail hηmed hηtail
    hμ_nonneg_all hmass hmedNonneg htailNonneg hmedUpper htailUpper hCμ
  have happendage : Tendsto ε atTop (𝓝 0) :=
    appendage_error_tendsto_zero_of_mass_medScale
      ε μ medScale Cε hε_nonneg happendage_le hscale.1
  have hlarge0 :
      Tendsto largePrime atTop (𝓝 0) :=
    large_prime_neighbour_power_saving_tendsto_zero_eventually_nonneg
      largePrime Clarge ηlarge hηlarge hlarge_nonneg hlarge_le
  have hdeps :
      Tendsto δb atTop (𝓝 0)
        ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0) :=
    delta_Delta_bounds_from_log_power_bounds_and_large_prime_power_saving
      μ δb Δb medScale depTail largePrime
      Cμ Cmed Ctail C₁ C₂ Clarge ηmed ηtail ηlarge
      hηmed hηtail hηlarge hCμ hC₁ hC₂ hμ_nonneg_all
      hδ_nonneg hΔ_nonneg hmedNonneg htailNonneg hlarge_nonneg hmass
      hmedUpper htailUpper hδ_le hΔ_le hlarge_le
  exact
    ⟨happendage, hlarge0, hscale.1, hscale.2.1, hscale.2.2, hdeps.1,
      hdeps.2⟩

/-- Eventual-nonnegativity version of
`brun_suen_paper_local_asymptotic_outputs_from_log_power_bounds`. -/
theorem brun_suen_paper_local_asymptotic_outputs_from_log_power_bounds_eventually_nonneg
    (ε μ δb Δb medScale depTail largePrime : ℝ → ℝ)
    (Cε Cμ Cmed Ctail C₁ C₂ Clarge ηmed ηtail ηlarge : ℝ)
    (hηmed : 0 < ηmed) (hηtail : 0 < ηtail) (hηlarge : 0 < ηlarge)
    (hCμ : 0 ≤ Cμ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hμ_nonneg : ∀ᶠ X in atTop, 0 ≤ μ X)
    (hε_nonneg : ∀ᶠ X in atTop, 0 ≤ ε X)
    (hδ_nonneg : ∀ᶠ X in atTop, 0 ≤ δb X)
    (hΔ_nonneg : ∀ᶠ X in atTop, 0 ≤ Δb X)
    (hmedNonneg : ∀ᶠ X in atTop, 0 ≤ medScale X)
    (htailNonneg : ∀ᶠ X in atTop, 0 ≤ depTail X)
    (hlarge_nonneg : ∀ᶠ X in atTop, 0 ≤ largePrime X)
    (happendage_le : ∀ᶠ X in atTop, ε X ≤ Cε * (μ X * medScale X))
    (hmass : ∀ᶠ X in atTop, μ X ≤ Cμ * (Real.log X) ^ 3)
    (hmedUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * medScale X ≤ Cmed * (Real.log X) ^ (-ηmed))
    (htailUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * depTail X ≤ Ctail * (Real.log X) ^ (-ηtail))
    (hδ_le : ∀ᶠ X in atTop, δb X ≤ C₁ * (μ X * medScale X) + largePrime X)
    (hΔ_le : ∀ᶠ X in atTop, Δb X ≤ C₂ * ((μ X) ^ 2 * depTail X))
    (hlarge_le : ∀ᶠ X in atTop, largePrime X ≤ Clarge * X ^ (-ηlarge)) :
    Tendsto ε atTop (𝓝 0)
    ∧ Tendsto largePrime atTop (𝓝 0)
    ∧ Tendsto (fun X => μ X * medScale X) atTop (𝓝 0)
    ∧ Tendsto (fun X => μ X * depTail X) atTop (𝓝 0)
    ∧ Tendsto (fun X => (μ X) ^ 2 * depTail X / μ X) atTop (𝓝 0)
    ∧ Tendsto δb atTop (𝓝 0)
    ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0) := by
  have hscale := mass_dependency_scale_from_log_power_bounds_eventually_nonneg
    μ depTail medScale Cμ Cmed Ctail ηmed ηtail hηmed hηtail
    hμ_nonneg hmass hmedNonneg htailNonneg hmedUpper htailUpper hCμ
  have happendage : Tendsto ε atTop (𝓝 0) :=
    appendage_error_tendsto_zero_of_mass_medScale
      ε μ medScale Cε hε_nonneg happendage_le hscale.1
  have hlarge0 :
      Tendsto largePrime atTop (𝓝 0) :=
    large_prime_neighbour_power_saving_tendsto_zero_eventually_nonneg
      largePrime Clarge ηlarge hηlarge hlarge_nonneg hlarge_le
  have hdeps :
      Tendsto δb atTop (𝓝 0)
        ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0) :=
    delta_Delta_bounds_from_log_power_bounds_and_large_prime_power_saving_eventually_nonneg
      μ δb Δb medScale depTail largePrime
      Cμ Cmed Ctail C₁ C₂ Clarge ηmed ηtail ηlarge
      hηmed hηtail hηlarge hCμ hC₁ hC₂ hμ_nonneg
      hδ_nonneg hΔ_nonneg hmedNonneg htailNonneg hlarge_nonneg hmass
      hmedUpper htailUpper hδ_le hΔ_le hlarge_le
  exact
    ⟨happendage, hlarge0, hscale.1, hscale.2.1, hscale.2.2, hdeps.1,
      hdeps.2⟩

/-- Paper-local asymptotic outputs with the medium-prime scale fixed to the
manuscript's concrete `log Y/(z log z)` expression.

Compared with
`brun_suen_paper_local_asymptotic_outputs_from_log_power_bounds_eventually_nonneg`,
this theorem no longer assumes nonnegativity or a log-power upper envelope for a
free `medScale`.  The required medium-scale limit is proved by
`paperMediumScale_logCube_tendsto_zero`; the residual squarefree tail and the
large-prime neighbour remain as the displayed analytic envelopes. -/
theorem
    brun_suen_paper_local_asymptotic_outputs_from_paper_medium_and_tail_log_power_eventually_nonneg
    (P : Params) (ε μ δb Δb depTail largePrime : ℝ → ℝ)
    (Cε Cμ Ctail C₁ C₂ Clarge ηtail ηlarge : ℝ)
    (hηtail : 0 < ηtail) (hηlarge : 0 < ηlarge)
    (hCμ : 0 ≤ Cμ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hμ_nonneg : ∀ᶠ X in atTop, 0 ≤ μ X)
    (hε_nonneg : ∀ᶠ X in atTop, 0 ≤ ε X)
    (hδ_nonneg : ∀ᶠ X in atTop, 0 ≤ δb X)
    (hΔ_nonneg : ∀ᶠ X in atTop, 0 ≤ Δb X)
    (htailNonneg : ∀ᶠ X in atTop, 0 ≤ depTail X)
    (hlarge_nonneg : ∀ᶠ X in atTop, 0 ≤ largePrime X)
    (happendage_le : ∀ᶠ X in atTop, ε X ≤ Cε * (μ X * paperMediumScale P X))
    (hmass : ∀ᶠ X in atTop, μ X ≤ Cμ * (Real.log X) ^ 3)
    (htailUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * depTail X ≤ Ctail * (Real.log X) ^ (-ηtail))
    (hδ_le : ∀ᶠ X in atTop,
      δb X ≤ C₁ * (μ X * paperMediumScale P X) + largePrime X)
    (hΔ_le : ∀ᶠ X in atTop, Δb X ≤ C₂ * ((μ X) ^ 2 * depTail X))
    (hlarge_le : ∀ᶠ X in atTop, largePrime X ≤ Clarge * X ^ (-ηlarge)) :
    Tendsto ε atTop (𝓝 0)
    ∧ Tendsto largePrime atTop (𝓝 0)
    ∧ Tendsto (fun X => μ X * paperMediumScale P X) atTop (𝓝 0)
    ∧ Tendsto (fun X => μ X * depTail X) atTop (𝓝 0)
    ∧ Tendsto (fun X => (μ X) ^ 2 * depTail X / μ X) atTop (𝓝 0)
    ∧ Tendsto δb atTop (𝓝 0)
    ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0) := by
  have hscale :=
    mass_dependency_scale_from_paper_medium_and_log_power_tail_eventually_nonneg
      P μ depTail Cμ Ctail ηtail hηtail hμ_nonneg hmass htailNonneg
      htailUpper hCμ
  have happendage : Tendsto ε atTop (𝓝 0) :=
    appendage_error_tendsto_zero_of_mass_medScale
      ε μ (paperMediumScale P) Cε hε_nonneg happendage_le hscale.1
  have hlarge0 : Tendsto largePrime atTop (𝓝 0) :=
    large_prime_neighbour_power_saving_tendsto_zero_eventually_nonneg
      largePrime Clarge ηlarge hηlarge hlarge_nonneg hlarge_le
  have hdeps :
      Tendsto δb atTop (𝓝 0)
        ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0) :=
    delta_Delta_bounds_from_large_prime_power_saving_eventually_nonneg
      μ δb Δb (paperMediumScale P) depTail largePrime C₁ C₂ Clarge ηlarge
      hC₁ hC₂ hηlarge hδ_nonneg hΔ_nonneg hμ_nonneg
      hlarge_nonneg hδ_le hΔ_le hlarge_le hscale.1 hscale.2.2
  exact
    ⟨happendage, hlarge0, hscale.1, hscale.2.1, hscale.2.2, hdeps.1,
      hdeps.2⟩

/-- Paper-local projection of the Suen no-hit estimate (`thm:CRT-nohit`).

This is the Suen-bearing part of the local Brun/Suen package.  It derives the
dependency parameter limits from the displayed log-power hypotheses, then calls
the cited Suen carrier.  In particular, it does not require the finite Brun
coefficient carrier or the appendage estimate. -/
theorem brun_suen_paper_local_nohit_output_from_log_power_bounds
    (μ δb Δb medScale depTail largePrime : ℝ → ℝ)
    (Cμ Cmed Ctail C₁ C₂ Clarge ηmed ηtail ηlarge : ℝ)
    (hηmed : 0 < ηmed) (hηtail : 0 < ηtail) (hηlarge : 0 < ηlarge)
    (hCμ : 0 ≤ Cμ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hμ_nonneg_all : ∀ X, 0 ≤ μ X)
    (hδ_nonneg : ∀ᶠ X in atTop, 0 ≤ δb X)
    (hΔ_nonneg : ∀ᶠ X in atTop, 0 ≤ Δb X)
    (hmedNonneg : ∀ᶠ X in atTop, 0 ≤ medScale X)
    (htailNonneg : ∀ᶠ X in atTop, 0 ≤ depTail X)
    (hlarge_nonneg : ∀ᶠ X in atTop, 0 ≤ largePrime X)
    (hmass : ∀ᶠ X in atTop, μ X ≤ Cμ * (Real.log X) ^ 3)
    (hmedUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * medScale X ≤ Cmed * (Real.log X) ^ (-ηmed))
    (htailUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * depTail X ≤ Ctail * (Real.log X) ^ (-ηtail))
    (hδ_le : ∀ᶠ X in atTop, δb X ≤ C₁ * (μ X * medScale X) + largePrime X)
    (hΔ_le : ∀ᶠ X in atTop, Δb X ≤ C₂ * ((μ X) ^ 2 * depTail X))
    (hlarge_le : ∀ᶠ X in atTop, largePrime X ≤ Clarge * X ^ (-ηlarge))
    (hμ_top : Tendsto μ atTop atTop) :
    ∃ εb : ℝ → ℝ, Tendsto εb atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop, 0 ≤ εb X)
      ∧ (∀ᶠ X in atTop,
          Inputs.suenProb (μ X) (δb X) (Δb X) ∈ Set.Icc 0 1 ∧
          Inputs.suenProb (μ X) (δb X) (Δb X) ≤ Real.exp (-(1 - εb X) * μ X)) := by
  have hdeps :
      Tendsto δb atTop (𝓝 0)
        ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0) :=
    delta_Delta_bounds_from_log_power_bounds_and_large_prime_power_saving
      μ δb Δb medScale depTail largePrime
      Cμ Cmed Ctail C₁ C₂ Clarge ηmed ηtail ηlarge
      hηmed hηtail hηlarge hCμ hC₁ hC₂ hμ_nonneg_all
      hδ_nonneg hΔ_nonneg hmedNonneg htailNonneg hlarge_nonneg hmass
      hmedUpper htailUpper hδ_le hΔ_le hlarge_le
  exact
    crt_nohit_of_suen_with_range_and_nonneg_defect_eventually_nonneg
      μ δb Δb (Eventually.of_forall hμ_nonneg_all) hδ_nonneg hΔ_nonneg
      hdeps.1 hdeps.2 hμ_top

/-- Eventual-nonnegativity version of
`brun_suen_paper_local_nohit_output_from_log_power_bounds`. -/
theorem brun_suen_paper_local_nohit_output_from_log_power_bounds_eventually_nonneg
    (μ δb Δb medScale depTail largePrime : ℝ → ℝ)
    (Cμ Cmed Ctail C₁ C₂ Clarge ηmed ηtail ηlarge : ℝ)
    (hηmed : 0 < ηmed) (hηtail : 0 < ηtail) (hηlarge : 0 < ηlarge)
    (hCμ : 0 ≤ Cμ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hμ_nonneg : ∀ᶠ X in atTop, 0 ≤ μ X)
    (hδ_nonneg : ∀ᶠ X in atTop, 0 ≤ δb X)
    (hΔ_nonneg : ∀ᶠ X in atTop, 0 ≤ Δb X)
    (hmedNonneg : ∀ᶠ X in atTop, 0 ≤ medScale X)
    (htailNonneg : ∀ᶠ X in atTop, 0 ≤ depTail X)
    (hlarge_nonneg : ∀ᶠ X in atTop, 0 ≤ largePrime X)
    (hmass : ∀ᶠ X in atTop, μ X ≤ Cμ * (Real.log X) ^ 3)
    (hmedUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * medScale X ≤ Cmed * (Real.log X) ^ (-ηmed))
    (htailUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * depTail X ≤ Ctail * (Real.log X) ^ (-ηtail))
    (hδ_le : ∀ᶠ X in atTop, δb X ≤ C₁ * (μ X * medScale X) + largePrime X)
    (hΔ_le : ∀ᶠ X in atTop, Δb X ≤ C₂ * ((μ X) ^ 2 * depTail X))
    (hlarge_le : ∀ᶠ X in atTop, largePrime X ≤ Clarge * X ^ (-ηlarge))
    (hμ_top : Tendsto μ atTop atTop) :
    ∃ εb : ℝ → ℝ, Tendsto εb atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop, 0 ≤ εb X)
      ∧ (∀ᶠ X in atTop,
          Inputs.suenProb (μ X) (δb X) (Δb X) ∈ Set.Icc 0 1 ∧
          Inputs.suenProb (μ X) (δb X) (Δb X) ≤ Real.exp (-(1 - εb X) * μ X)) := by
  have hdeps :
      Tendsto δb atTop (𝓝 0)
        ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0) :=
    delta_Delta_bounds_from_log_power_bounds_and_large_prime_power_saving_eventually_nonneg
      μ δb Δb medScale depTail largePrime
      Cμ Cmed Ctail C₁ C₂ Clarge ηmed ηtail ηlarge
      hηmed hηtail hηlarge hCμ hC₁ hC₂ hμ_nonneg
      hδ_nonneg hΔ_nonneg hmedNonneg htailNonneg hlarge_nonneg hmass
      hmedUpper htailUpper hδ_le hΔ_le hlarge_le
  exact
    crt_nohit_of_suen_with_range_and_nonneg_defect_eventually_nonneg
      μ δb Δb hμ_nonneg hδ_nonneg hΔ_nonneg hdeps.1 hdeps.2 hμ_top

/-- Paper-local Suen no-hit output with the medium-prime scale fixed to the
manuscript's concrete `log Y/(z log z)` expression.

This is the no-hit analogue of
`brun_suen_paper_local_asymptotic_outputs_from_paper_medium_and_tail_log_power_eventually_nonneg`:
the caller no longer supplies a free `medScale`, its nonnegativity, or a
log-power upper envelope for it.  The only remaining analytic envelopes are the
residual squarefree dependency tail and the large-prime-neighbour saving,
together with the cited Suen/Janson carrier. -/
theorem brun_suen_paper_local_nohit_output_from_paper_medium_and_tail_log_power_eventually_nonneg
    (P : Params) (μ δb Δb depTail largePrime : ℝ → ℝ)
    (Cμ Ctail C₁ C₂ Clarge ηtail ηlarge : ℝ)
    (hηtail : 0 < ηtail) (hηlarge : 0 < ηlarge)
    (hCμ : 0 ≤ Cμ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hμ_nonneg : ∀ᶠ X in atTop, 0 ≤ μ X)
    (hδ_nonneg : ∀ᶠ X in atTop, 0 ≤ δb X)
    (hΔ_nonneg : ∀ᶠ X in atTop, 0 ≤ Δb X)
    (htailNonneg : ∀ᶠ X in atTop, 0 ≤ depTail X)
    (hlarge_nonneg : ∀ᶠ X in atTop, 0 ≤ largePrime X)
    (hmass : ∀ᶠ X in atTop, μ X ≤ Cμ * (Real.log X) ^ 3)
    (htailUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * depTail X ≤ Ctail * (Real.log X) ^ (-ηtail))
    (hδ_le : ∀ᶠ X in atTop,
      δb X ≤ C₁ * (μ X * paperMediumScale P X) + largePrime X)
    (hΔ_le : ∀ᶠ X in atTop, Δb X ≤ C₂ * ((μ X) ^ 2 * depTail X))
    (hlarge_le : ∀ᶠ X in atTop, largePrime X ≤ Clarge * X ^ (-ηlarge))
    (hμ_top : Tendsto μ atTop atTop) :
    ∃ εb : ℝ → ℝ, Tendsto εb atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop, 0 ≤ εb X)
      ∧ (∀ᶠ X in atTop,
          Inputs.suenProb (μ X) (δb X) (Δb X) ∈ Set.Icc 0 1 ∧
          Inputs.suenProb (μ X) (δb X) (Δb X) ≤ Real.exp (-(1 - εb X) * μ X)) := by
  have hscale :=
    mass_dependency_scale_from_paper_medium_and_log_power_tail_eventually_nonneg
      P μ depTail Cμ Ctail ηtail hηtail hμ_nonneg hmass htailNonneg
      htailUpper hCμ
  have hdeps :
      Tendsto δb atTop (𝓝 0)
        ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0) :=
    delta_Delta_bounds_from_large_prime_power_saving_eventually_nonneg
      μ δb Δb (paperMediumScale P) depTail largePrime C₁ C₂ Clarge ηlarge
      hC₁ hC₂ hηlarge hδ_nonneg hΔ_nonneg hμ_nonneg
      hlarge_nonneg hδ_le hΔ_le hlarge_le hscale.1 hscale.2.2
  exact
    crt_nohit_of_suen_with_range_and_nonneg_defect_eventually_nonneg
      μ δb Δb hμ_nonneg hδ_nonneg hΔ_nonneg hdeps.1 hdeps.2 hμ_top

/-- Paper-local Brun/Suen output bundle with the manuscript's concrete
medium-prime scale `log Y/(z log z)`.

Compared with
`brun_suen_paper_local_outputs_from_log_power_bounds_eventually_nonneg`, this
version has no free `medScale`, no medium-scale nonnegativity hypothesis, and no
medium-scale log-power envelope hypothesis.  Those are discharged by
`paperMediumScale_eventually_nonneg` and
`paperMediumScale_logCube_tendsto_zero`; the residual squarefree dependency
tail, large-prime-neighbour saving, and cited Suen/Janson input remain exactly
visible. -/
theorem brun_suen_paper_local_outputs_from_paper_medium_and_tail_log_power_eventually_nonneg
    (P : Params) (weights : List ℚ) (M Xq : ℚ) (R : ℕ)
    (ε μ δb Δb depTail largePrime : ℝ → ℝ)
    (Cε Cμ Ctail C₁ C₂ Clarge ηtail ηlarge : ℝ)
    (hnn : ∀ w ∈ weights, 0 ≤ w)
    (hmassQ : weights.sum ≤ M)
    (hXq : 1 ≤ Xq)
    (hηtail : 0 < ηtail) (hηlarge : 0 < ηlarge)
    (hCμ : 0 ≤ Cμ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hμ_nonneg : ∀ᶠ X in atTop, 0 ≤ μ X)
    (hε_nonneg : ∀ᶠ X in atTop, 0 ≤ ε X)
    (hδ_nonneg : ∀ᶠ X in atTop, 0 ≤ δb X)
    (hΔ_nonneg : ∀ᶠ X in atTop, 0 ≤ Δb X)
    (htailNonneg : ∀ᶠ X in atTop, 0 ≤ depTail X)
    (hlarge_nonneg : ∀ᶠ X in atTop, 0 ≤ largePrime X)
    (happendage_le : ∀ᶠ X in atTop, ε X ≤ Cε * (μ X * paperMediumScale P X))
    (hmass : ∀ᶠ X in atTop, μ X ≤ Cμ * (Real.log X) ^ 3)
    (htailUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * depTail X ≤ Ctail * (Real.log X) ^ (-ηtail))
    (hδ_le : ∀ᶠ X in atTop,
      δb X ≤ C₁ * (μ X * paperMediumScale P X) + largePrime X)
    (hΔ_le : ∀ᶠ X in atTop, Δb X ≤ C₂ * ((μ X) ^ 2 * depTail X))
    (hlarge_le : ∀ᶠ X in atTop, largePrime X ≤ Clarge * X ^ (-ηlarge))
    (hμ_top : Tendsto μ atTop atTop) :
    (∑ r ∈ Finset.range (2 * R + 1),
        (Xq : ℝ) ^ r * (EscLeanChecks.elemSymmList weights r : ℝ))
      ≤ (Xq : ℝ) ^ (2 * R) * Real.exp (M : ℝ)
    ∧ Tendsto ε atTop (𝓝 0)
    ∧ Tendsto largePrime atTop (𝓝 0)
    ∧ Tendsto (fun X => μ X * paperMediumScale P X) atTop (𝓝 0)
    ∧ Tendsto (fun X => μ X * depTail X) atTop (𝓝 0)
    ∧ Tendsto (fun X => (μ X) ^ 2 * depTail X / μ X) atTop (𝓝 0)
    ∧ Tendsto δb atTop (𝓝 0)
    ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0)
    ∧ ∃ εb : ℝ → ℝ, Tendsto εb atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop, 0 ≤ εb X)
      ∧ (∀ᶠ X in atTop,
          Inputs.suenProb (μ X) (δb X) (Δb X) ∈ Set.Icc 0 1 ∧
          Inputs.suenProb (μ X) (δb X) (Δb X) ≤ Real.exp (-(1 - εb X) * μ X)) := by
  have hbrun :=
    brun_envelope_elemSymm_rational_weights weights M Xq R hnn hmassQ hXq
  have hasymp :=
    brun_suen_paper_local_asymptotic_outputs_from_paper_medium_and_tail_log_power_eventually_nonneg
      P ε μ δb Δb depTail largePrime Cε Cμ Ctail C₁ C₂ Clarge ηtail
      ηlarge hηtail hηlarge hCμ hC₁ hC₂ hμ_nonneg hε_nonneg
      hδ_nonneg hΔ_nonneg htailNonneg hlarge_nonneg happendage_le hmass
      htailUpper hδ_le hΔ_le hlarge_le
  have hnohit :=
    brun_suen_paper_local_nohit_output_from_paper_medium_and_tail_log_power_eventually_nonneg
      P μ δb Δb depTail largePrime Cμ Ctail C₁ C₂ Clarge ηtail ηlarge
      hηtail hηlarge hCμ hC₁ hC₂ hμ_nonneg hδ_nonneg hΔ_nonneg
      htailNonneg hlarge_nonneg hmass htailUpper hδ_le hΔ_le hlarge_le
      hμ_top
  exact
    ⟨hbrun, hasymp.1, hasymp.2.1, hasymp.2.2.1, hasymp.2.2.2.1,
      hasymp.2.2.2.2.1, hasymp.2.2.2.2.2.1, hasymp.2.2.2.2.2.2,
      hnohit⟩

/-! ## Part 5. Fixed-`m` dependency/no-hit bridge. -/

/-- Fixed-`m` dependency/no-hit bridge for `prop:fixed-m-transfer`.

Once the fixed-numerator transfer has supplied the same structural dependency
bounds as `lem:delta-Delta`, together with the fixed-power large-prime saving
and the mass-scale limits, the checked Suen carrier immediately gives the
downstream no-hit envelope with probability range and nonnegative `o(1)` defect.

This theorem is deliberately only a composition of `delta_Delta_bounds_from_large_prime_power_saving`
and `crt_nohit_of_suen_with_range_and_nonneg_defect`; it adds no new analytic
input and keeps the Suen step on the cited-theorem frontier. -/
theorem fixed_m_dependency_nohit_of_transported_bounds
    (μ δb Δb medScale depTail largePrime : ℝ → ℝ)
    (C₁ C₂ Clarge η : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hη : 0 < η)
    (hδ_nonneg : ∀ X, 0 ≤ δb X)
    (hΔ_nonneg : ∀ X, 0 ≤ Δb X)
    (hμ_nonneg : ∀ X, 0 ≤ μ X)
    (hlarge_nonneg : ∀ X, 0 ≤ largePrime X)
    (hδ_le : ∀ᶠ X in atTop, δb X ≤ C₁ * (μ X * medScale X) + largePrime X)
    (hΔ_le : ∀ᶠ X in atTop, Δb X ≤ C₂ * ((μ X) ^ 2 * depTail X))
    (hlarge_le : ∀ᶠ X in atTop, largePrime X ≤ Clarge * X ^ (-η))
    (hmed0 : Tendsto (fun X => μ X * medScale X) atTop (𝓝 0))
    (htail_o_μ : Tendsto (fun X => (μ X) ^ 2 * depTail X / μ X) atTop (𝓝 0))
    (hμ_top : Tendsto μ atTop atTop) :
    ∃ εb : ℝ → ℝ, Tendsto εb atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop, 0 ≤ εb X)
      ∧ (∀ᶠ X in atTop,
          Inputs.suenProb (μ X) (δb X) (Δb X) ∈ Set.Icc 0 1 ∧
          Inputs.suenProb (μ X) (δb X) (Δb X) ≤ Real.exp (-(1 - εb X) * μ X)) := by
  have hdeps :
      Tendsto δb atTop (𝓝 0)
        ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0) :=
    delta_Delta_bounds_from_large_prime_power_saving
      μ δb Δb medScale depTail largePrime C₁ C₂ Clarge η
      hC₁ hC₂ hη hδ_nonneg hΔ_nonneg hμ_nonneg hlarge_nonneg
      hδ_le hΔ_le hlarge_le hmed0 htail_o_μ
  exact crt_nohit_of_suen_with_range_and_nonneg_defect
    μ δb Δb hμ_nonneg hδ_nonneg hΔ_nonneg hdeps.1 hdeps.2 hμ_top

/-- Eventual-nonnegativity version of
`fixed_m_dependency_nohit_of_transported_bounds`.

The fixed-`m` transported dependency/no-hit route is a large-range route, so
nonnegativity of the dependency parameters and large-prime contribution only
needs to hold eventually.  No new analytic input is introduced; the cited Suen
carrier is used on that same eventual range. -/
theorem fixed_m_dependency_nohit_of_transported_bounds_eventually_nonneg
    (μ δb Δb medScale depTail largePrime : ℝ → ℝ)
    (C₁ C₂ Clarge η : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hη : 0 < η)
    (hδ_nonneg : ∀ᶠ X in atTop, 0 ≤ δb X)
    (hΔ_nonneg : ∀ᶠ X in atTop, 0 ≤ Δb X)
    (hμ_nonneg : ∀ᶠ X in atTop, 0 ≤ μ X)
    (hlarge_nonneg : ∀ᶠ X in atTop, 0 ≤ largePrime X)
    (hδ_le : ∀ᶠ X in atTop, δb X ≤ C₁ * (μ X * medScale X) + largePrime X)
    (hΔ_le : ∀ᶠ X in atTop, Δb X ≤ C₂ * ((μ X) ^ 2 * depTail X))
    (hlarge_le : ∀ᶠ X in atTop, largePrime X ≤ Clarge * X ^ (-η))
    (hmed0 : Tendsto (fun X => μ X * medScale X) atTop (𝓝 0))
    (htail_o_μ : Tendsto (fun X => (μ X) ^ 2 * depTail X / μ X) atTop (𝓝 0))
    (hμ_top : Tendsto μ atTop atTop) :
    ∃ εb : ℝ → ℝ, Tendsto εb atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop, 0 ≤ εb X)
      ∧ (∀ᶠ X in atTop,
          Inputs.suenProb (μ X) (δb X) (Δb X) ∈ Set.Icc 0 1 ∧
          Inputs.suenProb (μ X) (δb X) (Δb X) ≤ Real.exp (-(1 - εb X) * μ X)) := by
  have hdeps :
      Tendsto δb atTop (𝓝 0)
        ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0) :=
    delta_Delta_bounds_from_large_prime_power_saving_eventually_nonneg
      μ δb Δb medScale depTail largePrime C₁ C₂ Clarge η
      hC₁ hC₂ hη hδ_nonneg hΔ_nonneg hμ_nonneg hlarge_nonneg
      hδ_le hΔ_le hlarge_le hmed0 htail_o_μ
  exact crt_nohit_of_suen_with_range_and_nonneg_defect_eventually_nonneg
    μ δb Δb hμ_nonneg hδ_nonneg hΔ_nonneg hdeps.1 hdeps.2 hμ_top

end EscAnalytic
