import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Tactic
import EscAnalytic.Core
import EscAnalytic.Inputs
import EscAnalytic.Counting
import EscAnalytic.BrunSuen
import EscAnalytic.Optimization

/-!
# Transfer to finite intervals

This file formalizes `thm:finite-transfer`.  For a fixed truncation constant
`K` and `R_b = floor(K mu_b)`, the finite-level condition controls the error in
replacing finite interval counts by their CRT densities.  The conclusion is the
uniform estimate

`M_b(N) <= (N/P(z)) exp(-(1-o(1)) mu_b)`.

## Ingredients

The proof combines the following finite and analytic estimates:

* **Even Bonferroni, pointwise + companion** (`EscLeanChecks`):
  `even_bonferroni_nohit_le_prefix`, `even_bonferroni_arithmetic_bound`, i.e.
  `1_{W=0} ≤ ∑_{r≤2R}(-1)^r C(W,r) ≤ 1_{W=0} + C(W,2R)`.
* **Finite double-count over `r`-subsets**:
  `hitEventSubsets_alternating_double_count`,
  `hitEventSubsets_bonferroni_lower/upper_double_count` — swaps the sum over
  points with the sum over `r`-subsets of events, turning the pointwise
  Bonferroni inequalities into `M_b(N) ≤ ∑_{r≤2R_b}(-1)^r C_r^{(b)}(N)`.
* **Finite interval approximation** (`residueClassCountUpTo_le_div_add_one`,
  `satEventCommonHitCountUpTo_le_div_add_one_of_common_hit`, …): each
  `C_r^{(b)}(N) = (N/P(z))·F_r + O(X^r F_r)`.
* **Brun envelope** (`EscAnalytic.BrunSuen.brun_envelope_factorial`):
  `∑_{r≤2R} X^r F_r ≤ X^{2R}·exp{(1+o(1))μ}`.
* **CRT no-hit** (`EscAnalytic.BrunSuen.crt_nohit`): `P(W_b=0) ≤ exp{-(1-o(1))μ_b}`.

The assembly proceeds in four steps:

1. main term `≤ (N/P(z))·(nohit + 𝔼[C(W_b,2R_b)])` and the expectation of the
   `2R`-fold term is `≤ (N/P(z))·F_{2R_b}`;
2. error `≤ X^{2R_b}·exp{2μ_b} ≤ N·exp{-4μ_b} ≤ (N/P(z))·exp{-4μ_b}` via the
   Brun envelope, the bound `(1+o(1))μ ≤ 2μ`, and the **level condition**;
3. `F_{2R_b} ≤ exp{-3μ_b}` via `thm:Brun` with constant `2K` and Stirling
   (`R_b = ⌊Kμ_b⌋`, `K` large);
4. summing the three `exp` pieces:
   `nohit + exp{-3μ_b} + exp{-4μ_b} ≤ exp{-(1-o(1))μ_b}`.

## Interface boundary

The mass law and finite-level condition enter through explicit hypotheses.  The
finite double-count and interval approximation are proved in `EscLeanChecks`;
`finite_transfer` receives their combined per-class inequality as `hdecomp`.
This module declares no axioms.
-/

namespace EscAnalytic

open Filter Topology
open scoped BigOperators

/-! ## Part 0. Real-analysis assembly lemmas -/

/-- **Exponential dominance step** (tex 2008–2013).

If `0 < μ`, `0 ≤ ε`, and three nonnegative no-hit/error pieces are controlled by
`exp(-(1-ε)μ)`, `exp(-3μ)`, `exp(-4μ)`, then their sum is bounded by
`exp(-(1-ε')μ)` with the *single* relaxed defect
`ε' = ε + (log 3)/μ`, which is still `o(1)` when `ε = o(1)` and `μ → ∞`.

This is the elementary `exp{-3μ}, exp{-4μ} ≤ exp{-(1-o(1))μ}` absorption that
turns the three saving terms of the manuscript into one. -/
theorem three_exp_absorb
    {μ ε p₁ p₂ p₃ : ℝ} (hμ : 0 < μ) (hε : 0 ≤ ε)
    (hp₁ : p₁ ≤ Real.exp (-(1 - ε) * μ))
    (hp₂ : p₂ ≤ Real.exp (-3 * μ))
    (hp₃ : p₃ ≤ Real.exp (-4 * μ)) :
    p₁ + p₂ + p₃ ≤ Real.exp (-(1 - (ε + Real.log 3 / μ)) * μ) := by
  -- The common envelope is `exp(-(1-ε)μ)`, which dominates `exp(-3μ)` and
  -- `exp(-4μ)` once `μ` is moderately large; here we only need the algebraic
  -- factor-3 absorption: each of the three terms is `≤ exp(-(1-ε)μ)` and
  -- `3·exp(-(1-ε)μ) = exp(log 3)·exp(-(1-ε)μ) = exp(-(1-(ε+log3/μ))μ)`.
  have hμne : μ ≠ 0 := ne_of_gt hμ
  -- bound p₂, p₃ by the p₁-envelope.  Since `ε ≥ 0`, `-(1-ε)μ ≥ -μ ≥ -3μ ≥ -4μ`.
  have henv₂ : Real.exp (-3 * μ) ≤ Real.exp (-(1 - ε) * μ) := by
    apply Real.exp_le_exp.mpr
    have : (-3 : ℝ) * μ ≤ -(1 - ε) * μ := by nlinarith [hμ.le, hε]
    exact this
  have henv₃ : Real.exp (-4 * μ) ≤ Real.exp (-(1 - ε) * μ) := by
    apply Real.exp_le_exp.mpr
    have : (-4 : ℝ) * μ ≤ -(1 - ε) * μ := by nlinarith [hμ.le, hε]
    exact this
  -- so the sum is ≤ 3 · exp(-(1-ε)μ)
  have hsum : p₁ + p₂ + p₃ ≤ 3 * Real.exp (-(1 - ε) * μ) := by
    have h2 : p₂ ≤ Real.exp (-(1 - ε) * μ) := le_trans hp₂ henv₂
    have h3 : p₃ ≤ Real.exp (-(1 - ε) * μ) := le_trans hp₃ henv₃
    linarith
  -- repackage `3 · exp(-(1-ε)μ) = exp(-(1-(ε+log3/μ))μ)`
  have hexp3 : (3 : ℝ) = Real.exp (Real.log 3) := by
    rw [Real.exp_log (by norm_num)]
  have hpack : 3 * Real.exp (-(1 - ε) * μ)
      = Real.exp (-(1 - (ε + Real.log 3 / μ)) * μ) := by
    rw [hexp3, ← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [hpack] at hsum
  exact hsum

/-- **Combination of the relaxed defect with `o(1)` data** (tex 2009).

If `ε_b → 0` (the CRT no-hit defect) and `μ_b → ∞` (mass law), then the relaxed
defect `ε_b + (log 3)/μ_b` of `three_exp_absorb` is again `o(1)`.  This is the
asymptotic justification that the headline `exp{-(1-o(1))μ_b}` survives the
factor-3 absorption. -/
theorem relaxed_defect_tendsto_zero
    {εb μ : ℝ → ℝ}
    (hε : Tendsto εb atTop (𝓝 0))
    (hμ : Tendsto μ atTop atTop) :
    Tendsto (fun X => εb X + Real.log 3 / μ X) atTop (𝓝 0) := by
  have hlog : Tendsto (fun X => Real.log 3 / μ X) atTop (𝓝 0) := by
    have : Tendsto (fun X => (Real.log 3) * (μ X)⁻¹) atTop (𝓝 (Real.log 3 * 0)) :=
      (hμ.inv_tendsto_atTop).const_mul (Real.log 3)
    simpa [div_eq_mul_inv, mul_zero] using this
  simpa using hε.add hlog

/-- **Error-side level-condition step** (tex 1995–2002).

The Brun envelope error `∑_{r≤2R} X^r F_r ≤ X^{2R}·exp{(1+ε_K)μ}` is bounded by
`X^{2R}·exp{2μ}` once `(1+ε_K)μ ≤ 2μ` (i.e. `ε_K ≤ 1`, the increment bound for
`K` large, tex 1810–1815), and then — *dividing the level condition*
`P(z)·X^{2R}·exp{2μ} ≤ N·exp{-4μ}` by `P(z) > 0` — by `(N/P(z))·exp{-4μ}`.  This
is precisely the manuscript's "at most `(N/P(z))e^{-4μ}` by the hypothesis."
We package the chain
`errTerm ≤ X^{2R}·exp{(1+ε)μ} ≤ X^{2R}·exp{2μ} ≤ (N/P(z))·exp{-4μ}`. -/
theorem error_le_level
    {errTerm Xpow μ Pz N ε : ℝ}
    (hXpow : 0 ≤ Xpow) (hμ : 0 ≤ μ) (hPz : 1 ≤ Pz)
    (herr : errTerm ≤ Xpow * Real.exp ((1 + ε) * μ))
    (hεle : ε ≤ 1)
    (hlevel : Pz * Xpow * Real.exp (2 * μ) ≤ N * Real.exp (-4 * μ)) :
    errTerm ≤ (N / Pz) * Real.exp (-4 * μ) := by
  have hPz_pos : 0 < Pz := lt_of_lt_of_le zero_lt_one hPz
  -- step 1: (1+ε)μ ≤ 2μ, so exp((1+ε)μ) ≤ exp(2μ)
  have hstep1 : Xpow * Real.exp ((1 + ε) * μ) ≤ Xpow * Real.exp (2 * μ) := by
    apply mul_le_mul_of_nonneg_left _ hXpow
    apply Real.exp_le_exp.mpr
    nlinarith [hμ, hεle]
  -- step 2: divide the level condition by Pz > 0:
  --   Xpow·exp(2μ) = (Pz·Xpow·exp(2μ))/Pz ≤ (N·exp(-4μ))/Pz = (N/Pz)·exp(-4μ)
  have hstep2 : Xpow * Real.exp (2 * μ) ≤ (N / Pz) * Real.exp (-4 * μ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hPz_pos]
    calc Xpow * Real.exp (2 * μ) * Pz
          = Pz * Xpow * Real.exp (2 * μ) := by ring
      _ ≤ N * Real.exp (-4 * μ) := hlevel
  calc errTerm ≤ Xpow * Real.exp ((1 + ε) * μ) := herr
    _ ≤ Xpow * Real.exp (2 * μ) := hstep1
    _ ≤ (N / Pz) * Real.exp (-4 * μ) := hstep2

/-! ## Part 1.  `thm:finite-transfer` — the assembled per-base-class bound. -/

/-- **Certificate finite-interval transfer** (`thm:finite-transfer`, tex 1963–2013).

We index by the manuscript variable `X` (the missed count, scales, and mass are
all functions of `X`).  Fix a base class `b`; abbreviate

* `Mb X`     := the per-base missed count
  `#{n ≤ N : n ≡ b (mod P(z)), n ∉ A_i^{(b)} ∀ i}`  (LHS, tex 1969–1972);
* `N X`, `Pz X`  := `N` and `P(z)`;
* `μ X`      := the certificate mass `μ_b`;
* `Xpow X`   := `X^{2R_b}` (the top power of the Brun envelope);
* `nohit X`  := the CRT no-hit probability `P(W_b = 0)` (tex 1922–1925).

**Hypotheses.**

* `hmass` : the mass law half `μ_b → ∞` (consequence of `μ_b ≍ (log X)³`,
  `prop:mu`, tex 2014);
* `hlevel`: the **finite-level condition** `eq:finite-level-condition`
  (tex 1966–1968), supplied by `Optimization.finite_level_condition_of_optimization`;
* `hPz`, `hXpow`, `hNpos` : positivity `P(z) ≥ 1`, `0 ≤ X^{2R_b}`, `0 ≤ N`;
* `hdecomp` : the **double-count + `lem:finite-approx` decomposition** of `M_b(N)`
  into a main term and an `O(∑ X^r F_r)` error (proved in `EscLeanChecks`):
  `M_b(N) ≤ (N/P(z))·(nohit + F_{2R}) + errTerm`, with `errTerm`,`F_{2R}` the
  Brun-coefficient data;
* `herr`  : the **Brun envelope** bound `errTerm ≤ X^{2R}·exp{(1+ε_K)μ}`
  (`thm:Brun`, tex 1776–1816 via `brun_envelope_factorial`);
* `hεle`  : the increment bound `ε_K ≤ 1` (`lem:increment`, `K` large, tex 1810);
* `hF2R`  : **`thm:Brun` + Stirling** `F_{2R_b} ≤ exp{-3μ_b}` (tex 2006–2007);
* `hnohit`: the **CRT no-hit** bound `nohit ≤ exp{-(1-ε_b)μ_b}`
  (`thm:CRT-nohit` via `crt_nohit`, tex 1922–1925).

**Conclusion.**  With the single relaxed defect `ε'_b := ε_b + (log 3)/μ_b`
(still `o(1)`, `relaxed_defect_tendsto_zero`),
`M_b(N) ≤ (N/P(z))·exp{-(1-ε'_b)μ_b}`, i.e. the manuscript's
`(N/P(z))·exp{-(1-o(1))μ_b}`. -/
theorem finite_transfer
    {Mb N Pz μ Xpow nohit errTerm F2R εb εK : ℝ}
    (hμ : 0 < μ) (hPz : 1 ≤ Pz) (hXpow : 0 ≤ Xpow) (hNpos : 0 ≤ N)
    (hεb : 0 ≤ εb)
    -- Combinatorial decomposition: finite double-count plus lem:finite-approx.
    (hdecomp : Mb ≤ (N / Pz) * (nohit + F2R) + errTerm)
    -- Brun envelope for the error
    (herr : errTerm ≤ Xpow * Real.exp ((1 + εK) * μ))
    (hεle : εK ≤ 1)
    -- level condition (eq:finite-level-condition)
    (hlevel : Pz * Xpow * Real.exp (2 * μ) ≤ N * Real.exp (-4 * μ))
    -- thm:Brun + Stirling on the top coefficient
    (hF2R : F2R ≤ Real.exp (-3 * μ))
    -- CRT no-hit
    (hnohit : nohit ≤ Real.exp (-(1 - εb) * μ)) :
    Mb ≤ (N / Pz) * Real.exp (-(1 - (εb + Real.log 3 / μ)) * μ) := by
  -- 0 ≤ N/Pz
  have hPz_pos : 0 < Pz := lt_of_lt_of_le one_pos hPz
  have hNPz_nonneg : 0 ≤ N / Pz := div_nonneg hNpos hPz_pos.le
  -- the error, via the level condition, is ≤ (N/Pz)·exp(-4μ)
  have herrLevel : errTerm ≤ (N / Pz) * Real.exp (-4 * μ) :=
    error_le_level hXpow hμ.le hPz herr hεle hlevel
  -- assemble the three exponential pieces inside the (N/Pz) bracket
  have hbracket :
      nohit + F2R + Real.exp (-4 * μ)
        ≤ Real.exp (-(1 - (εb + Real.log 3 / μ)) * μ) :=
    three_exp_absorb hμ hεb hnohit hF2R (le_refl _)
  -- Mb ≤ (N/Pz)·(nohit + F2R) + errTerm
  --    ≤ (N/Pz)·(nohit + F2R) + (N/Pz)·exp(-4μ)
  --    = (N/Pz)·(nohit + F2R + exp(-4μ))
  --    ≤ (N/Pz)·exp(-(1-ε')μ).
  calc Mb ≤ (N / Pz) * (nohit + F2R) + errTerm := hdecomp
    _ ≤ (N / Pz) * (nohit + F2R) + (N / Pz) * Real.exp (-4 * μ) := by
        linarith [herrLevel]
    _ = (N / Pz) * (nohit + F2R + Real.exp (-4 * μ)) := by ring
    _ ≤ (N / Pz) * Real.exp (-(1 - (εb + Real.log 3 / μ)) * μ) :=
        mul_le_mul_of_nonneg_left hbracket hNPz_nonneg

/-- Finite transfer with the Brun-error envelope discharged from the checked
finite elementary-symmetric coefficient model.

This replaces the abstract hypothesis
`errTerm ≤ Xpow * exp((1+εK)μ)` in `finite_transfer` by the concrete
paper-facing data

* `errTerm` is bounded by the finite Brun coefficient sum
  `∑_{r≤2R} X^r e_r(weights)`;
* the nonnegative rational weights have total mass at most `M`;
* the rational mass parameter satisfies `M ≤ (1+εK)μ`.

The checked theorem `brun_envelope_elemSymm_rational_weights` supplies the
finite Brun envelope; only the level condition, top coefficient tail, and
CRT no-hit estimate remain as the same explicit hypotheses as in
`finite_transfer`. -/
theorem finite_transfer_of_elemSymm_brun_error
    {Mb N Pz μ nohit errTerm F2R εb εK : ℝ}
    (weights : List ℚ) (M X : ℚ) (R : ℕ)
    (hweights_nonneg : ∀ w ∈ weights, 0 ≤ w)
    (hmass : weights.sum ≤ M)
    (hMle : (M : ℝ) ≤ (1 + εK) * μ)
    (hX : 1 ≤ X)
    (hμ : 0 < μ) (hPz : 1 ≤ Pz) (hNpos : 0 ≤ N)
    (hεb : 0 ≤ εb)
    (hdecomp : Mb ≤ (N / Pz) * (nohit + F2R) + errTerm)
    (herr_raw : errTerm ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        (X : ℝ) ^ r * (EscLeanChecks.elemSymmList weights r : ℝ))
    (hεle : εK ≤ 1)
    (hlevel : Pz * ((X : ℝ) ^ (2 * R)) * Real.exp (2 * μ)
      ≤ N * Real.exp (-4 * μ))
    (hF2R : F2R ≤ Real.exp (-3 * μ))
    (hnohit : nohit ≤ Real.exp (-(1 - εb) * μ)) :
    Mb ≤ (N / Pz) * Real.exp (-(1 - (εb + Real.log 3 / μ)) * μ) := by
  have hXpow_nonneg : 0 ≤ (X : ℝ) ^ (2 * R) := by
    have hX_nonneg : 0 ≤ (X : ℝ) := by exact_mod_cast (le_trans (by norm_num : (0 : ℚ) ≤ 1) hX)
    exact pow_nonneg hX_nonneg _
  have hbrun :=
    brun_envelope_elemSymm_rational_weights weights M X R hweights_nonneg hmass hX
  have hexp_mono :
      Real.exp (M : ℝ) ≤ Real.exp ((1 + εK) * μ) :=
    Real.exp_le_exp.mpr hMle
  have herr :
      errTerm ≤ ((X : ℝ) ^ (2 * R)) * Real.exp ((1 + εK) * μ) := by
    calc
      errTerm
          ≤ ∑ r ∈ Finset.range (2 * R + 1),
              (X : ℝ) ^ r * (EscLeanChecks.elemSymmList weights r : ℝ) := herr_raw
      _ ≤ (X : ℝ) ^ (2 * R) * Real.exp (M : ℝ) := hbrun
      _ ≤ (X : ℝ) ^ (2 * R) * Real.exp ((1 + εK) * μ) :=
          mul_le_mul_of_nonneg_left hexp_mono hXpow_nonneg
  exact finite_transfer hμ hPz hXpow_nonneg hNpos hεb hdecomp herr hεle
    hlevel hF2R hnohit

/-- Finite transfer with both Brun-side coefficient hypotheses tied to the
checked finite elementary-symmetric model.

Compared with `finite_transfer_of_elemSymm_brun_error`, this also replaces the
raw top-coefficient hypothesis `F2R ≤ exp(-3μ)` by:

* `F2R` is bounded by the concrete coefficient `e_{2R}(weights)`;
* the explicit factorial/Stirling tail inequality
  `M^{2R}/(2R)! ≤ exp(-3μ)`.

Thus the remaining hypotheses are the decomposition, increment/level
inequalities, and the cited-Suen no-hit envelope, not a free Brun coefficient
tail. -/
theorem finite_transfer_of_elemSymm_brun_error_and_top
    {Mb N Pz μ nohit errTerm F2R εb εK : ℝ}
    (weights : List ℚ) (M X : ℚ) (R : ℕ)
    (hweights_nonneg : ∀ w ∈ weights, 0 ≤ w)
    (hmass : weights.sum ≤ M)
    (hMle : (M : ℝ) ≤ (1 + εK) * μ)
    (hX : 1 ≤ X)
    (hμ : 0 < μ) (hPz : 1 ≤ Pz) (hNpos : 0 ≤ N)
    (hεb : 0 ≤ εb)
    (hdecomp : Mb ≤ (N / Pz) * (nohit + F2R) + errTerm)
    (herr_raw : errTerm ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        (X : ℝ) ^ r * (EscLeanChecks.elemSymmList weights r : ℝ))
    (hεle : εK ≤ 1)
    (hlevel : Pz * ((X : ℝ) ^ (2 * R)) * Real.exp (2 * μ)
      ≤ N * Real.exp (-4 * μ))
    (hF2R_raw : F2R ≤ (EscLeanChecks.elemSymmList weights (2 * R) : ℝ))
    (hF2R_tail : ((M : ℝ) ^ (2 * R)) / (Nat.factorial (2 * R) : ℝ)
      ≤ Real.exp (-3 * μ))
    (hnohit : nohit ≤ Real.exp (-(1 - εb) * μ)) :
    Mb ≤ (N / Pz) * Real.exp (-(1 - (εb + Real.log 3 / μ)) * μ) := by
  have hF2R_elem :
      (EscLeanChecks.elemSymmList weights (2 * R) : ℝ) ≤ Real.exp (-3 * μ) :=
    elemSymm_top_coefficient_tail_rational_weights
      weights M R μ hweights_nonneg hmass hF2R_tail
  have hF2R : F2R ≤ Real.exp (-3 * μ) :=
    le_trans hF2R_raw hF2R_elem
  exact finite_transfer_of_elemSymm_brun_error
    weights M X R hweights_nonneg hmass hMle hX hμ hPz hNpos hεb
    hdecomp herr_raw hεle hlevel hF2R hnohit

/-! ## Part 2.  The `o(1)` defect: the `exp{-(1-o(1))μ_b}` shape is uniform. -/

/-- **Uniform `(1-o(1))` shape of the transfer bound** (tex 2008–2013).

Indexing by `X → ∞`, if the per-`X` finite-transfer bound holds with CRT defect
`εb X → 0` and the mass `μ X → ∞`, then there is a *single* `o(1)` defect
`εb' X := εb X + (log 3)/μ X → 0` realizing the headline
`M_b(N) ≤ (N/P(z))·exp{-(1-o(1))μ_b}` — i.e. the relaxed defect from the
factor-3 absorption is still `o(1)`.  This is the asymptotic packaging used to
feed `MainInputs.Ered_bound`. -/
theorem finite_transfer_defect_o1
    {εb μ : ℝ → ℝ}
    (hε : Tendsto εb atTop (𝓝 0))
    (hμ : Tendsto μ atTop atTop) :
    ∃ εb' : ℝ → ℝ, Tendsto εb' atTop (𝓝 0)
      ∧ εb' = fun X => εb X + Real.log 3 / μ X :=
  ⟨fun X => εb X + Real.log 3 / μ X,
    relaxed_defect_tendsto_zero hε hμ, rfl⟩

/-- **Finite transfer, asymptotic `o(1)` form** (`thm:finite-transfer`, tex 2013).

Bundles `finite_transfer` (per-`X`) with `finite_transfer_defect_o1`: under the
mass law `μ_b → ∞` and the CRT defect `εb → 0`, *eventually in `X`* there is an
`o(1)` defect `εb'` with `M_b(N) ≤ (N/P(z))·exp{-(1-εb' X)μ_b}`.  This is the
form `MainInputs.Ered_bound` consumes after summing over reduced `b`. -/
theorem finite_transfer_asymp
    {Mb N Pz μ Xpow nohit errTerm F2R εb : ℝ → ℝ} {εK : ℝ}
    (hμpos : ∀ X, 0 < μ X) (hPz : ∀ X, 1 ≤ Pz X)
    (hXpow : ∀ X, 0 ≤ Xpow X) (hNpos : ∀ X, 0 ≤ N X)
    (hεb_nonneg : ∀ X, 0 ≤ εb X)
    (hdecomp : ∀ X, Mb X ≤ (N X / Pz X) * (nohit X + F2R X) + errTerm X)
    (herr : ∀ X, errTerm X ≤ Xpow X * Real.exp ((1 + εK) * μ X))
    (hεle : εK ≤ 1)
    (hlevel : ∀ X, Pz X * Xpow X * Real.exp (2 * μ X)
      ≤ N X * Real.exp (-4 * μ X))
    (hF2R : ∀ X, F2R X ≤ Real.exp (-3 * μ X))
    (hnohit : ∀ X, nohit X ≤ Real.exp (-(1 - εb X) * μ X))
    (hε0 : Tendsto εb atTop (𝓝 0))
    (hμtop : Tendsto μ atTop atTop) :
    ∃ εb' : ℝ → ℝ, Tendsto εb' atTop (𝓝 0)
      ∧ ∀ X, Mb X ≤ (N X / Pz X) * Real.exp (-(1 - εb' X) * μ X) := by
  refine ⟨fun X => εb X + Real.log 3 / μ X,
    relaxed_defect_tendsto_zero hε0 hμtop, fun X => ?_⟩
  exact finite_transfer (hμpos X) (hPz X) (hXpow X) (hNpos X) (hεb_nonneg X)
    (hdecomp X) (herr X) hεle (hlevel X) (hF2R X) (hnohit X)

/-- Asymptotic finite transfer with both Brun-side coefficient hypotheses
discharged from the indexed finite elementary-symmetric model.

This is the function-level counterpart of
`finite_transfer_of_elemSymm_brun_error_and_top`: for every cutoff parameter
`t`, the error term is bounded by the finite coefficient sum, the top
coefficient is bounded by `e_{2R(t)}`, and the explicit factorial tail
`M(t)^{2R(t)}/(2R(t))! ≤ exp(-3 μ(t))` supplies the top-coefficient estimate.
The resulting defect is the same relaxed `ε_b(t) + log 3 / μ(t)` and is `o(1)`
whenever `ε_b → 0` and `μ → ∞`. -/
theorem finite_transfer_asymp_of_elemSymm_brun_error_and_top
    {Mb N Pz μ nohit errTerm F2R εb : ℝ → ℝ} {εK : ℝ}
    (weights : ℝ → List ℚ) (M Xq : ℝ → ℚ) (R : ℝ → ℕ)
    (hweights_nonneg : ∀ t w, w ∈ weights t → 0 ≤ w)
    (hmass : ∀ t, (weights t).sum ≤ M t)
    (hMle : ∀ t, (M t : ℝ) ≤ (1 + εK) * μ t)
    (hXq : ∀ t, 1 ≤ Xq t)
    (hμpos : ∀ t, 0 < μ t) (hPz : ∀ t, 1 ≤ Pz t)
    (hNpos : ∀ t, 0 ≤ N t)
    (hεb_nonneg : ∀ t, 0 ≤ εb t)
    (hdecomp : ∀ t, Mb t ≤ (N t / Pz t) * (nohit t + F2R t) + errTerm t)
    (herr_raw : ∀ t, errTerm t ≤
      ∑ r ∈ Finset.range (2 * R t + 1),
        (Xq t : ℝ) ^ r * (EscLeanChecks.elemSymmList (weights t) r : ℝ))
    (hεle : εK ≤ 1)
    (hlevel : ∀ t,
      Pz t * ((Xq t : ℝ) ^ (2 * R t)) * Real.exp (2 * μ t)
        ≤ N t * Real.exp (-4 * μ t))
    (hF2R_raw : ∀ t, F2R t ≤
      (EscLeanChecks.elemSymmList (weights t) (2 * R t) : ℝ))
    (hF2R_tail : ∀ t,
      ((M t : ℝ) ^ (2 * R t)) / (Nat.factorial (2 * R t) : ℝ)
        ≤ Real.exp (-3 * μ t))
    (hnohit : ∀ t, nohit t ≤ Real.exp (-(1 - εb t) * μ t))
    (hε0 : Tendsto εb atTop (𝓝 0))
    (hμtop : Tendsto μ atTop atTop) :
    ∃ εb' : ℝ → ℝ, Tendsto εb' atTop (𝓝 0)
      ∧ ∀ t, Mb t ≤ (N t / Pz t) * Real.exp (-(1 - εb' t) * μ t) := by
  refine ⟨fun t => εb t + Real.log 3 / μ t,
    relaxed_defect_tendsto_zero hε0 hμtop, fun t => ?_⟩
  exact finite_transfer_of_elemSymm_brun_error_and_top
    (weights t) (M t) (Xq t) (R t)
    (fun w hw => hweights_nonneg t w hw) (hmass t) (hMle t) (hXq t)
    (hμpos t) (hPz t) (hNpos t) (hεb_nonneg t) (hdecomp t)
    (herr_raw t) hεle (hlevel t) (hF2R_raw t) (hF2R_tail t) (hnohit t)

/-- Eventual version of `finite_transfer_asymp`.

This is the manuscript's natural asymptotic shape: all finite-transfer
ingredients only need to hold for sufficiently large `X`, and the conclusion is
the corresponding eventual per-base transfer estimate with an `o(1)` defect. -/
theorem finite_transfer_asymp_eventually
    {Mb N Pz μ Xpow nohit errTerm F2R εb : ℝ → ℝ} {εK : ℝ}
    (hμpos : ∀ᶠ X in atTop, 0 < μ X)
    (hPz : ∀ᶠ X in atTop, 1 ≤ Pz X)
    (hXpow : ∀ᶠ X in atTop, 0 ≤ Xpow X)
    (hNpos : ∀ᶠ X in atTop, 0 ≤ N X)
    (hεb_nonneg : ∀ᶠ X in atTop, 0 ≤ εb X)
    (hdecomp : ∀ᶠ X in atTop,
      Mb X ≤ (N X / Pz X) * (nohit X + F2R X) + errTerm X)
    (herr : ∀ᶠ X in atTop,
      errTerm X ≤ Xpow X * Real.exp ((1 + εK) * μ X))
    (hεle : εK ≤ 1)
    (hlevel : ∀ᶠ X in atTop,
      Pz X * Xpow X * Real.exp (2 * μ X) ≤ N X * Real.exp (-4 * μ X))
    (hF2R : ∀ᶠ X in atTop, F2R X ≤ Real.exp (-3 * μ X))
    (hnohit : ∀ᶠ X in atTop, nohit X ≤ Real.exp (-(1 - εb X) * μ X))
    (hε0 : Tendsto εb atTop (𝓝 0))
    (hμtop : Tendsto μ atTop atTop) :
    ∃ εb' : ℝ → ℝ, Tendsto εb' atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop,
          Mb X ≤ (N X / Pz X) * Real.exp (-(1 - εb' X) * μ X)) := by
  refine ⟨fun X => εb X + Real.log 3 / μ X,
    relaxed_defect_tendsto_zero hε0 hμtop, ?_⟩
  filter_upwards [hμpos, hPz, hXpow, hNpos, hεb_nonneg, hdecomp, herr, hlevel,
      hF2R, hnohit] with X hμX hPzX hXpowX hNposX hεbX hdecompX herrX hlevelX
      hF2RX hnohitX
  exact finite_transfer hμX hPzX hXpowX hNposX hεbX hdecompX herrX hεle
    hlevelX hF2RX hnohitX

/-- Eventual asymptotic finite transfer with both Brun-side coefficient
hypotheses discharged from the indexed finite elementary-symmetric model.

This is the eventual counterpart of
`finite_transfer_asymp_of_elemSymm_brun_error_and_top`: the finite Brun
coefficient error bound, the rational mass bound, the explicit level condition,
and the factorial/Stirling top-coefficient tail only need to hold for
sufficiently large parameters.  The conclusion is the same eventual
`exp(-(1-o(1)) μ)` transfer estimate. -/
theorem finite_transfer_asymp_eventually_of_elemSymm_brun_error_and_top
    {Mb N Pz μ nohit errTerm F2R εb : ℝ → ℝ} {εK : ℝ}
    (weights : ℝ → List ℚ) (M Xq : ℝ → ℚ) (R : ℝ → ℕ)
    (hweights_nonneg : ∀ᶠ t in atTop, ∀ w, w ∈ weights t → 0 ≤ w)
    (hmass : ∀ᶠ t in atTop, (weights t).sum ≤ M t)
    (hMle : ∀ᶠ t in atTop, (M t : ℝ) ≤ (1 + εK) * μ t)
    (hXq : ∀ᶠ t in atTop, 1 ≤ Xq t)
    (hμpos : ∀ᶠ t in atTop, 0 < μ t)
    (hPz : ∀ᶠ t in atTop, 1 ≤ Pz t)
    (hNpos : ∀ᶠ t in atTop, 0 ≤ N t)
    (hεb_nonneg : ∀ᶠ t in atTop, 0 ≤ εb t)
    (hdecomp : ∀ᶠ t in atTop,
      Mb t ≤ (N t / Pz t) * (nohit t + F2R t) + errTerm t)
    (herr_raw : ∀ᶠ t in atTop, errTerm t ≤
      ∑ r ∈ Finset.range (2 * R t + 1),
        (Xq t : ℝ) ^ r * (EscLeanChecks.elemSymmList (weights t) r : ℝ))
    (hεle : εK ≤ 1)
    (hlevel : ∀ᶠ t in atTop,
      Pz t * ((Xq t : ℝ) ^ (2 * R t)) * Real.exp (2 * μ t)
        ≤ N t * Real.exp (-4 * μ t))
    (hF2R_raw : ∀ᶠ t in atTop, F2R t ≤
      (EscLeanChecks.elemSymmList (weights t) (2 * R t) : ℝ))
    (hF2R_tail : ∀ᶠ t in atTop,
      ((M t : ℝ) ^ (2 * R t)) / (Nat.factorial (2 * R t) : ℝ)
        ≤ Real.exp (-3 * μ t))
    (hnohit : ∀ᶠ t in atTop, nohit t ≤ Real.exp (-(1 - εb t) * μ t))
    (hε0 : Tendsto εb atTop (𝓝 0))
    (hμtop : Tendsto μ atTop atTop) :
    ∃ εb' : ℝ → ℝ, Tendsto εb' atTop (𝓝 0)
      ∧ (∀ᶠ t in atTop,
          Mb t ≤ (N t / Pz t) * Real.exp (-(1 - εb' t) * μ t)) := by
  refine ⟨fun t => εb t + Real.log 3 / μ t,
    relaxed_defect_tendsto_zero hε0 hμtop, ?_⟩
  filter_upwards [hweights_nonneg, hmass, hMle, hXq, hμpos, hPz, hNpos,
      hεb_nonneg, hdecomp, herr_raw, hlevel, hF2R_raw, hF2R_tail, hnohit]
    with t hweights_nonneg_t hmass_t hMle_t hXq_t hμpos_t hPz_t hNpos_t
      hεb_nonneg_t hdecomp_t herr_raw_t hlevel_t hF2R_raw_t hF2R_tail_t hnohit_t
  exact finite_transfer_of_elemSymm_brun_error_and_top
    (weights t) (M t) (Xq t) (R t)
    (fun w hw => hweights_nonneg_t w hw) hmass_t hMle_t hXq_t
    hμpos_t hPz_t hNpos_t hεb_nonneg_t hdecomp_t herr_raw_t hεle
    hlevel_t hF2R_raw_t hF2R_tail_t hnohit_t

/-- Finite transfer with the CRT no-hit hypothesis discharged by the cited Suen
carrier theorem.

The only deep input used for the no-hit term is
the theorem-level legacy Suen envelope, through
`crt_nohit_of_suen_with_range_and_nonneg_defect`; the remaining hypotheses are
the paper's finite-transfer ingredients (Bonferroni/decomposition, Brun envelope,
level condition, and the top-coefficient tail) in eventual real-variable form. -/
theorem finite_transfer_asymp_eventually_of_suen
    {Mb N Pz μ δb Δb Xpow errTerm F2R : ℝ → ℝ} {εK : ℝ}
    (hμ_nonneg : ∀ X, 0 ≤ μ X) (hδ_nonneg : ∀ X, 0 ≤ δb X)
    (hΔ_nonneg : ∀ X, 0 ≤ Δb X)
    (hδ0 : Tendsto δb atTop (𝓝 0))
    (hΔ_o_μ : Tendsto (fun X => Δb X / μ X) atTop (𝓝 0))
    (hμtop : Tendsto μ atTop atTop)
    (hPz : ∀ᶠ X in atTop, 1 ≤ Pz X)
    (hXpow : ∀ᶠ X in atTop, 0 ≤ Xpow X)
    (hNpos : ∀ᶠ X in atTop, 0 ≤ N X)
    (hdecomp : ∀ᶠ X in atTop,
      Mb X ≤ (N X / Pz X) * (Inputs.suenProb (μ X) (δb X) (Δb X) + F2R X)
        + errTerm X)
    (herr : ∀ᶠ X in atTop,
      errTerm X ≤ Xpow X * Real.exp ((1 + εK) * μ X))
    (hεle : εK ≤ 1)
    (hlevel : ∀ᶠ X in atTop,
      Pz X * Xpow X * Real.exp (2 * μ X) ≤ N X * Real.exp (-4 * μ X))
    (hF2R : ∀ᶠ X in atTop, F2R X ≤ Real.exp (-3 * μ X)) :
    ∃ εb' : ℝ → ℝ, Tendsto εb' atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop,
          Mb X ≤ (N X / Pz X) * Real.exp (-(1 - εb' X) * μ X)) := by
  rcases crt_nohit_of_suen_with_range_and_nonneg_defect μ δb Δb
      hμ_nonneg hδ_nonneg hΔ_nonneg hδ0 hΔ_o_μ hμtop with
    ⟨εb, hεb0, hεb_nonneg, hrange_nohit⟩
  have hμpos : ∀ᶠ X in atTop, 0 < μ X :=
    hμtop.eventually (eventually_gt_atTop 0)
  have hnohit : ∀ᶠ X in atTop,
      Inputs.suenProb (μ X) (δb X) (Δb X) ≤ Real.exp (-(1 - εb X) * μ X) := by
    filter_upwards [hrange_nohit] with X hX
    exact hX.2
  exact finite_transfer_asymp_eventually
    (Mb := Mb) (N := N) (Pz := Pz) (μ := μ) (Xpow := Xpow)
    (nohit := fun X => Inputs.suenProb (μ X) (δb X) (Δb X))
    (errTerm := errTerm) (F2R := F2R) (εb := εb) (εK := εK)
    hμpos hPz hXpow hNpos hεb_nonneg hdecomp herr hεle hlevel hF2R
    hnohit hεb0 hμtop

/-- Finite transfer with the CRT no-hit hypothesis discharged by Suen, requiring
only eventual sign hypotheses on `μ`, `δ_b`, and `Δ_b`. -/
theorem finite_transfer_asymp_eventually_of_suen_eventually_nonneg
    {Mb N Pz μ δb Δb Xpow errTerm F2R : ℝ → ℝ} {εK : ℝ}
    (hμ_nonneg : ∀ᶠ X in atTop, 0 ≤ μ X)
    (hδ_nonneg : ∀ᶠ X in atTop, 0 ≤ δb X)
    (hΔ_nonneg : ∀ᶠ X in atTop, 0 ≤ Δb X)
    (hδ0 : Tendsto δb atTop (𝓝 0))
    (hΔ_o_μ : Tendsto (fun X => Δb X / μ X) atTop (𝓝 0))
    (hμtop : Tendsto μ atTop atTop)
    (hPz : ∀ᶠ X in atTop, 1 ≤ Pz X)
    (hXpow : ∀ᶠ X in atTop, 0 ≤ Xpow X)
    (hNpos : ∀ᶠ X in atTop, 0 ≤ N X)
    (hdecomp : ∀ᶠ X in atTop,
      Mb X ≤ (N X / Pz X) * (Inputs.suenProb (μ X) (δb X) (Δb X) + F2R X)
        + errTerm X)
    (herr : ∀ᶠ X in atTop,
      errTerm X ≤ Xpow X * Real.exp ((1 + εK) * μ X))
    (hεle : εK ≤ 1)
    (hlevel : ∀ᶠ X in atTop,
      Pz X * Xpow X * Real.exp (2 * μ X) ≤ N X * Real.exp (-4 * μ X))
    (hF2R : ∀ᶠ X in atTop, F2R X ≤ Real.exp (-3 * μ X)) :
    ∃ εb' : ℝ → ℝ, Tendsto εb' atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop,
          Mb X ≤ (N X / Pz X) * Real.exp (-(1 - εb' X) * μ X)) := by
  rcases crt_nohit_of_suen_with_range_and_nonneg_defect_eventually_nonneg
      μ δb Δb hμ_nonneg hδ_nonneg hΔ_nonneg hδ0 hΔ_o_μ hμtop with
    ⟨εb, hεb0, hεb_nonneg, hrange_nohit⟩
  have hμpos : ∀ᶠ X in atTop, 0 < μ X :=
    hμtop.eventually (eventually_gt_atTop 0)
  have hnohit : ∀ᶠ X in atTop,
      Inputs.suenProb (μ X) (δb X) (Δb X) ≤ Real.exp (-(1 - εb X) * μ X) := by
    filter_upwards [hrange_nohit] with X hX
    exact hX.2
  exact finite_transfer_asymp_eventually
    (Mb := Mb) (N := N) (Pz := Pz) (μ := μ) (Xpow := Xpow)
    (nohit := fun X => Inputs.suenProb (μ X) (δb X) (Δb X))
    (errTerm := errTerm) (F2R := F2R) (εb := εb) (εK := εK)
    hμpos hPz hXpow hNpos hεb_nonneg hdecomp herr hεle hlevel hF2R
    hnohit hεb0 hμtop

/-- Eventual finite transfer with Suen discharging the CRT no-hit term and the
finite elementary-symmetric model discharging both Brun-side coefficient
hypotheses.

Compared with `finite_transfer_asymp_eventually_of_suen`, this removes the
abstract `Xpow`, raw Brun-error envelope, and raw `F2R ≤ exp(-3μ)` assumptions.
The transfer error is bounded by the checked finite coefficient sum, and the
top coefficient is bounded through the explicit factorial/Stirling tail.  The
only deep no-hit input is still the cited Suen/Janson carrier theorem. -/
theorem finite_transfer_asymp_eventually_of_suen_and_elemSymm_brun_top
    {Mb N Pz μ δb Δb errTerm F2R : ℝ → ℝ} {εK : ℝ}
    (weights : ℝ → List ℚ) (M Xq : ℝ → ℚ) (R : ℝ → ℕ)
    (hμ_nonneg : ∀ X, 0 ≤ μ X) (hδ_nonneg : ∀ X, 0 ≤ δb X)
    (hΔ_nonneg : ∀ X, 0 ≤ Δb X)
    (hδ0 : Tendsto δb atTop (𝓝 0))
    (hΔ_o_μ : Tendsto (fun X => Δb X / μ X) atTop (𝓝 0))
    (hμtop : Tendsto μ atTop atTop)
    (hweights_nonneg : ∀ᶠ X in atTop, ∀ w, w ∈ weights X → 0 ≤ w)
    (hmass : ∀ᶠ X in atTop, (weights X).sum ≤ M X)
    (hMle : ∀ᶠ X in atTop, (M X : ℝ) ≤ (1 + εK) * μ X)
    (hXq : ∀ᶠ X in atTop, 1 ≤ Xq X)
    (hPz : ∀ᶠ X in atTop, 1 ≤ Pz X)
    (hNpos : ∀ᶠ X in atTop, 0 ≤ N X)
    (hdecomp : ∀ᶠ X in atTop,
      Mb X ≤ (N X / Pz X) * (Inputs.suenProb (μ X) (δb X) (Δb X) + F2R X)
        + errTerm X)
    (herr_raw : ∀ᶠ X in atTop, errTerm X ≤
      ∑ r ∈ Finset.range (2 * R X + 1),
        (Xq X : ℝ) ^ r * (EscLeanChecks.elemSymmList (weights X) r : ℝ))
    (hεle : εK ≤ 1)
    (hlevel : ∀ᶠ X in atTop,
      Pz X * ((Xq X : ℝ) ^ (2 * R X)) * Real.exp (2 * μ X)
        ≤ N X * Real.exp (-4 * μ X))
    (hF2R_raw : ∀ᶠ X in atTop, F2R X ≤
      (EscLeanChecks.elemSymmList (weights X) (2 * R X) : ℝ))
    (hF2R_tail : ∀ᶠ X in atTop,
      ((M X : ℝ) ^ (2 * R X)) / (Nat.factorial (2 * R X) : ℝ)
        ≤ Real.exp (-3 * μ X)) :
    ∃ εb' : ℝ → ℝ, Tendsto εb' atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop,
          Mb X ≤ (N X / Pz X) * Real.exp (-(1 - εb' X) * μ X)) := by
  rcases crt_nohit_of_suen_with_range_and_nonneg_defect μ δb Δb
      hμ_nonneg hδ_nonneg hΔ_nonneg hδ0 hΔ_o_μ hμtop with
    ⟨εb, hεb0, hεb_nonneg, hrange_nohit⟩
  have hμpos : ∀ᶠ X in atTop, 0 < μ X :=
    hμtop.eventually (eventually_gt_atTop 0)
  have hnohit : ∀ᶠ X in atTop,
      Inputs.suenProb (μ X) (δb X) (Δb X) ≤ Real.exp (-(1 - εb X) * μ X) := by
    filter_upwards [hrange_nohit] with X hX
    exact hX.2
  exact finite_transfer_asymp_eventually_of_elemSymm_brun_error_and_top
    (Mb := Mb) (N := N) (Pz := Pz) (μ := μ)
    (nohit := fun X => Inputs.suenProb (μ X) (δb X) (Δb X))
    (errTerm := errTerm) (F2R := F2R) (εb := εb) (εK := εK)
    weights M Xq R hweights_nonneg hmass hMle hXq hμpos hPz hNpos
    hεb_nonneg hdecomp herr_raw hεle hlevel hF2R_raw hF2R_tail hnohit
    hεb0 hμtop

/-- Elementary-symmetric finite transfer with Suen, requiring only eventual sign
hypotheses on `μ`, `δ_b`, and `Δ_b`. -/
theorem finite_transfer_asymp_eventually_of_suen_and_elemSymm_brun_top_eventually_nonneg
    {Mb N Pz μ δb Δb errTerm F2R : ℝ → ℝ} {εK : ℝ}
    (weights : ℝ → List ℚ) (M Xq : ℝ → ℚ) (R : ℝ → ℕ)
    (hμ_nonneg : ∀ᶠ X in atTop, 0 ≤ μ X)
    (hδ_nonneg : ∀ᶠ X in atTop, 0 ≤ δb X)
    (hΔ_nonneg : ∀ᶠ X in atTop, 0 ≤ Δb X)
    (hδ0 : Tendsto δb atTop (𝓝 0))
    (hΔ_o_μ : Tendsto (fun X => Δb X / μ X) atTop (𝓝 0))
    (hμtop : Tendsto μ atTop atTop)
    (hweights_nonneg : ∀ᶠ X in atTop, ∀ w, w ∈ weights X → 0 ≤ w)
    (hmass : ∀ᶠ X in atTop, (weights X).sum ≤ M X)
    (hMle : ∀ᶠ X in atTop, (M X : ℝ) ≤ (1 + εK) * μ X)
    (hXq : ∀ᶠ X in atTop, 1 ≤ Xq X)
    (hPz : ∀ᶠ X in atTop, 1 ≤ Pz X)
    (hNpos : ∀ᶠ X in atTop, 0 ≤ N X)
    (hdecomp : ∀ᶠ X in atTop,
      Mb X ≤ (N X / Pz X) * (Inputs.suenProb (μ X) (δb X) (Δb X) + F2R X)
        + errTerm X)
    (herr_raw : ∀ᶠ X in atTop, errTerm X ≤
      ∑ r ∈ Finset.range (2 * R X + 1),
        (Xq X : ℝ) ^ r * (EscLeanChecks.elemSymmList (weights X) r : ℝ))
    (hεle : εK ≤ 1)
    (hlevel : ∀ᶠ X in atTop,
      Pz X * ((Xq X : ℝ) ^ (2 * R X)) * Real.exp (2 * μ X)
        ≤ N X * Real.exp (-4 * μ X))
    (hF2R_raw : ∀ᶠ X in atTop, F2R X ≤
      (EscLeanChecks.elemSymmList (weights X) (2 * R X) : ℝ))
    (hF2R_tail : ∀ᶠ X in atTop,
      ((M X : ℝ) ^ (2 * R X)) / (Nat.factorial (2 * R X) : ℝ)
        ≤ Real.exp (-3 * μ X)) :
    ∃ εb' : ℝ → ℝ, Tendsto εb' atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop,
          Mb X ≤ (N X / Pz X) * Real.exp (-(1 - εb' X) * μ X)) := by
  rcases crt_nohit_of_suen_with_range_and_nonneg_defect_eventually_nonneg
      μ δb Δb hμ_nonneg hδ_nonneg hΔ_nonneg hδ0 hΔ_o_μ hμtop with
    ⟨εb, hεb0, hεb_nonneg, hrange_nohit⟩
  have hμpos : ∀ᶠ X in atTop, 0 < μ X :=
    hμtop.eventually (eventually_gt_atTop 0)
  have hnohit : ∀ᶠ X in atTop,
      Inputs.suenProb (μ X) (δb X) (Δb X) ≤ Real.exp (-(1 - εb X) * μ X) := by
    filter_upwards [hrange_nohit] with X hX
    exact hX.2
  exact finite_transfer_asymp_eventually_of_elemSymm_brun_error_and_top
    (Mb := Mb) (N := N) (Pz := Pz) (μ := μ)
    (nohit := fun X => Inputs.suenProb (μ X) (δb X) (Δb X))
    (errTerm := errTerm) (F2R := F2R) (εb := εb) (εK := εK)
    weights M Xq R hweights_nonneg hmass hMle hXq hμpos hPz hNpos
    hεb_nonneg hdecomp herr_raw hεle hlevel hF2R_raw hF2R_tail hnohit
    hεb0 hμtop

/-- Elementary-symmetric finite transfer with Suen, where the dependency limits
`δ_b → 0` and `Δ_b = o(μ_b)` are discharged from the paper's logarithmic
dependency envelopes.

This is a theorem-level bridge from `lem:delta-Delta` into `thm:finite-transfer`:
the caller no longer supplies the two asymptotic dependency conclusions
directly.  They are proved from the displayed mass, medium-prime, dependency-tail,
and large-prime-neighbour bounds. -/
theorem finite_transfer_asymp_eventually_of_log_power_suen_and_elemSymm_brun_top
    {Mb N Pz μ δb Δb errTerm F2R : ℝ → ℝ} {εK : ℝ}
    (weights : ℝ → List ℚ) (M Xq : ℝ → ℚ) (R : ℝ → ℕ)
    (medScale depTail largePrime : ℝ → ℝ)
    (Cμ Cmed Ctail C₁ C₂ Clarge ηmed ηtail ηlarge : ℝ)
    (hηmed : 0 < ηmed) (hηtail : 0 < ηtail) (hηlarge : 0 < ηlarge)
    (hCμ : 0 ≤ Cμ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hμ_nonneg : ∀ᶠ X in atTop, 0 ≤ μ X)
    (hδ_nonneg : ∀ᶠ X in atTop, 0 ≤ δb X)
    (hΔ_nonneg : ∀ᶠ X in atTop, 0 ≤ Δb X)
    (hmedNonneg : ∀ᶠ X in atTop, 0 ≤ medScale X)
    (htailNonneg : ∀ᶠ X in atTop, 0 ≤ depTail X)
    (hlarge_nonneg : ∀ᶠ X in atTop, 0 ≤ largePrime X)
    (hmassLog : ∀ᶠ X in atTop, μ X ≤ Cμ * (Real.log X) ^ 3)
    (hmedUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * medScale X ≤ Cmed * (Real.log X) ^ (-ηmed))
    (htailUpper : ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * depTail X ≤ Ctail * (Real.log X) ^ (-ηtail))
    (hδ_le : ∀ᶠ X in atTop, δb X ≤ C₁ * (μ X * medScale X) + largePrime X)
    (hΔ_le : ∀ᶠ X in atTop, Δb X ≤ C₂ * ((μ X) ^ 2 * depTail X))
    (hlarge_le : ∀ᶠ X in atTop, largePrime X ≤ Clarge * X ^ (-ηlarge))
    (hμtop : Tendsto μ atTop atTop)
    (hweights_nonneg : ∀ᶠ X in atTop, ∀ w, w ∈ weights X → 0 ≤ w)
    (hmass : ∀ᶠ X in atTop, (weights X).sum ≤ M X)
    (hMle : ∀ᶠ X in atTop, (M X : ℝ) ≤ (1 + εK) * μ X)
    (hXq : ∀ᶠ X in atTop, 1 ≤ Xq X)
    (hPz : ∀ᶠ X in atTop, 1 ≤ Pz X)
    (hNpos : ∀ᶠ X in atTop, 0 ≤ N X)
    (hdecomp : ∀ᶠ X in atTop,
      Mb X ≤ (N X / Pz X) * (Inputs.suenProb (μ X) (δb X) (Δb X) + F2R X)
        + errTerm X)
    (herr_raw : ∀ᶠ X in atTop, errTerm X ≤
      ∑ r ∈ Finset.range (2 * R X + 1),
        (Xq X : ℝ) ^ r * (EscLeanChecks.elemSymmList (weights X) r : ℝ))
    (hεle : εK ≤ 1)
    (hlevel : ∀ᶠ X in atTop,
      Pz X * ((Xq X : ℝ) ^ (2 * R X)) * Real.exp (2 * μ X)
        ≤ N X * Real.exp (-4 * μ X))
    (hF2R_raw : ∀ᶠ X in atTop, F2R X ≤
      (EscLeanChecks.elemSymmList (weights X) (2 * R X) : ℝ))
    (hF2R_tail : ∀ᶠ X in atTop,
      ((M X : ℝ) ^ (2 * R X)) / (Nat.factorial (2 * R X) : ℝ)
        ≤ Real.exp (-3 * μ X)) :
    ∃ εb' : ℝ → ℝ, Tendsto εb' atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop,
          Mb X ≤ (N X / Pz X) * Real.exp (-(1 - εb' X) * μ X)) := by
  have hdeps :
      Tendsto δb atTop (𝓝 0)
        ∧ Tendsto (fun X => Δb X / μ X) atTop (𝓝 0) :=
    delta_Delta_bounds_from_log_power_bounds_and_large_prime_power_saving_eventually_nonneg
      μ δb Δb medScale depTail largePrime
      Cμ Cmed Ctail C₁ C₂ Clarge ηmed ηtail ηlarge
      hηmed hηtail hηlarge hCμ hC₁ hC₂ hμ_nonneg
      hδ_nonneg hΔ_nonneg hmedNonneg htailNonneg hlarge_nonneg
      hmassLog hmedUpper htailUpper hδ_le hΔ_le hlarge_le
  exact
    finite_transfer_asymp_eventually_of_suen_and_elemSymm_brun_top_eventually_nonneg
      (Mb := Mb) (N := N) (Pz := Pz) (μ := μ) (δb := δb) (Δb := Δb)
      (errTerm := errTerm) (F2R := F2R) (εK := εK)
      weights M Xq R hμ_nonneg hδ_nonneg hΔ_nonneg hdeps.1 hdeps.2
      hμtop hweights_nonneg hmass hMle hXq hPz hNpos hdecomp herr_raw
      hεle hlevel hF2R_raw hF2R_tail

/-- Fixed-`m` finite-transfer bridge with transported dependency bounds.

This is the fixed-numerator version of `finite_transfer_asymp_eventually_of_suen`
after the `δ_b = o(1)` and `Δ_b = o(μ_b)` hypotheses have been discharged from
the transported structural bounds of `prop:fixed-m-transfer`.  The only
paper-facing standard input used by this bridge is the cited Suen correlation
inequality; the finite-transfer decomposition, Brun error envelope, level
condition, and top-coefficient tail remain explicit eventual hypotheses. -/
theorem fixed_m_finite_transfer_asymp_eventually_of_transported_bounds
    {Mb N Pz μ δb Δb medScale depTail largePrime Xpow errTerm F2R : ℝ → ℝ}
    {εK : ℝ}
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
    (hμtop : Tendsto μ atTop atTop)
    (hPz : ∀ᶠ X in atTop, 1 ≤ Pz X)
    (hXpow : ∀ᶠ X in atTop, 0 ≤ Xpow X)
    (hNpos : ∀ᶠ X in atTop, 0 ≤ N X)
    (hdecomp : ∀ᶠ X in atTop,
      Mb X ≤ (N X / Pz X) * (Inputs.suenProb (μ X) (δb X) (Δb X) + F2R X)
        + errTerm X)
    (herr : ∀ᶠ X in atTop,
      errTerm X ≤ Xpow X * Real.exp ((1 + εK) * μ X))
    (hεle : εK ≤ 1)
    (hlevel : ∀ᶠ X in atTop,
      Pz X * Xpow X * Real.exp (2 * μ X) ≤ N X * Real.exp (-4 * μ X))
    (hF2R : ∀ᶠ X in atTop, F2R X ≤ Real.exp (-3 * μ X)) :
    ∃ εb' : ℝ → ℝ, Tendsto εb' atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop,
          Mb X ≤ (N X / Pz X) * Real.exp (-(1 - εb' X) * μ X)) := by
  rcases fixed_m_dependency_nohit_of_transported_bounds
      μ δb Δb medScale depTail largePrime C₁ C₂ Clarge η
      hC₁ hC₂ hη hδ_nonneg hΔ_nonneg hμ_nonneg hlarge_nonneg
      hδ_le hΔ_le hlarge_le hmed0 htail_o_μ hμtop with
    ⟨εb, hεb0, hεb_nonneg, hrange_nohit⟩
  have hμpos : ∀ᶠ X in atTop, 0 < μ X :=
    hμtop.eventually (eventually_gt_atTop 0)
  have hnohit : ∀ᶠ X in atTop,
      Inputs.suenProb (μ X) (δb X) (Δb X) ≤ Real.exp (-(1 - εb X) * μ X) := by
    filter_upwards [hrange_nohit] with X hX
    exact hX.2
  exact finite_transfer_asymp_eventually
    (Mb := Mb) (N := N) (Pz := Pz) (μ := μ) (Xpow := Xpow)
    (nohit := fun X => Inputs.suenProb (μ X) (δb X) (Δb X))
    (errTerm := errTerm) (F2R := F2R) (εb := εb) (εK := εK)
    hμpos hPz hXpow hNpos hεb_nonneg hdecomp herr hεle hlevel hF2R
    hnohit hεb0 hμtop

/-- Fixed-`m` finite-transfer bridge with transported dependency bounds and
eventual nonnegativity.

This is the large-range variant of
`fixed_m_finite_transfer_asymp_eventually_of_transported_bounds`: the sign
hypotheses on `δ_b`, `Δ_b`, `μ_b`, and the large-prime contribution only need to
hold eventually, matching the way the paper uses the transported estimates. -/
theorem fixed_m_finite_transfer_asymp_eventually_of_transported_bounds_eventually_nonneg
    {Mb N Pz μ δb Δb medScale depTail largePrime Xpow errTerm F2R : ℝ → ℝ}
    {εK : ℝ}
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
    (hμtop : Tendsto μ atTop atTop)
    (hPz : ∀ᶠ X in atTop, 1 ≤ Pz X)
    (hXpow : ∀ᶠ X in atTop, 0 ≤ Xpow X)
    (hNpos : ∀ᶠ X in atTop, 0 ≤ N X)
    (hdecomp : ∀ᶠ X in atTop,
      Mb X ≤ (N X / Pz X) * (Inputs.suenProb (μ X) (δb X) (Δb X) + F2R X)
        + errTerm X)
    (herr : ∀ᶠ X in atTop,
      errTerm X ≤ Xpow X * Real.exp ((1 + εK) * μ X))
    (hεle : εK ≤ 1)
    (hlevel : ∀ᶠ X in atTop,
      Pz X * Xpow X * Real.exp (2 * μ X) ≤ N X * Real.exp (-4 * μ X))
    (hF2R : ∀ᶠ X in atTop, F2R X ≤ Real.exp (-3 * μ X)) :
    ∃ εb' : ℝ → ℝ, Tendsto εb' atTop (𝓝 0)
      ∧ (∀ᶠ X in atTop,
          Mb X ≤ (N X / Pz X) * Real.exp (-(1 - εb' X) * μ X)) := by
  rcases fixed_m_dependency_nohit_of_transported_bounds_eventually_nonneg
      μ δb Δb medScale depTail largePrime C₁ C₂ Clarge η
      hC₁ hC₂ hη hδ_nonneg hΔ_nonneg hμ_nonneg hlarge_nonneg
      hδ_le hΔ_le hlarge_le hmed0 htail_o_μ hμtop with
    ⟨εb, hεb0, hεb_nonneg, hrange_nohit⟩
  have hμpos : ∀ᶠ X in atTop, 0 < μ X :=
    hμtop.eventually (eventually_gt_atTop 0)
  have hnohit : ∀ᶠ X in atTop,
      Inputs.suenProb (μ X) (δb X) (Δb X) ≤ Real.exp (-(1 - εb X) * μ X) := by
    filter_upwards [hrange_nohit] with X hX
    exact hX.2
  exact finite_transfer_asymp_eventually
    (Mb := Mb) (N := N) (Pz := Pz) (μ := μ) (Xpow := Xpow)
    (nohit := fun X => Inputs.suenProb (μ X) (δb X) (Δb X))
    (errTerm := errTerm) (F2R := F2R) (εb := εb) (εK := εK)
    hμpos hPz hXpow hNpos hεb_nonneg hdecomp herr hεle hlevel hF2R
    hnohit hεb0 hμtop

/-- Extract a natural-number large-range threshold from an eventual real-cutoff
statement.  This is a pure filter bridge: if a property holds for all
sufficiently large real `X`, then it holds on all sufficiently large natural
cutoffs after coercion. -/
theorem real_eventually_atTop_to_nat_cast_large_range
    {p : ℝ → Prop}
    (h : ∀ᶠ X in atTop, p X) :
    ∃ T0 : ℕ, ∀ N : ℕ, T0 ≤ N → p (N : ℝ) := by
  have hnat : ∀ᶠ N : ℕ in atTop, p (N : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h
  exact Filter.eventually_atTop.mp hnat

/-- Natural-cutoff large-range form of the eventual finite-transfer estimate. -/
theorem finite_transfer_asymp_nat_large_range
    {Mb N Pz μ εb : ℝ → ℝ}
    (htransfer : ∀ᶠ X in atTop,
      Mb X ≤ (N X / Pz X) * Real.exp (-(1 - εb X) * μ X)) :
    ∃ T0 : ℕ, ∀ n : ℕ, T0 ≤ n →
      Mb (n : ℝ)
        ≤ (N (n : ℝ) / Pz (n : ℝ))
          * Real.exp (-(1 - εb (n : ℝ)) * μ (n : ℝ)) := by
  exact real_eventually_atTop_to_nat_cast_large_range htransfer

/-- Finite-uniform version of
`real_eventually_atTop_to_nat_cast_large_range`: a finite family of eventual
real-cutoff statements admits one natural-number threshold valid for every
index in the finite set. -/
theorem real_eventually_atTop_to_nat_cast_large_range_finset
    {ι : Type*} (S : Finset ι) {p : ι → ℝ → Prop}
    (h : ∀ b ∈ S, ∀ᶠ X in atTop, p b X) :
    ∃ T0 : ℕ, ∀ N : ℕ, T0 ≤ N → ∀ b ∈ S, p b (N : ℝ) := by
  classical
  have hAll : ∀ᶠ X in atTop, ∀ b ∈ S, p b X := by
    revert h
    refine Finset.induction_on S ?empty ?insert
    · intro _h
      simp
    · intro a S ha hS h
      have ha_ev : ∀ᶠ X in atTop, p a X := h a (by simp [ha])
      have hS_ev : ∀ᶠ X in atTop, ∀ b ∈ S, p b X := by
        exact hS (by
          intro b hb
          exact h b (by simp [hb]))
      filter_upwards [ha_ev, hS_ev] with X haX hSX b hb
      rcases Finset.mem_insert.mp hb with rfl | hbS
      · exact haX
      · exact hSX b hbS
  rcases real_eventually_atTop_to_nat_cast_large_range hAll with ⟨T0, hT0⟩
  exact ⟨T0, fun N hN b hb => hT0 N hN b hb⟩

/-- Finite-uniform natural-cutoff large-range form of eventual finite-transfer
estimates. -/
theorem finite_transfer_asymp_nat_large_range_finset
    {ι : Type*} (S : Finset ι)
    {Mb : ι → ℝ → ℝ} {N Pz : ℝ → ℝ} {μ εb : ι → ℝ → ℝ}
    (htransfer : ∀ b ∈ S, ∀ᶠ X in atTop,
      Mb b X ≤ (N X / Pz X) * Real.exp (-(1 - εb b X) * μ b X)) :
    ∃ T0 : ℕ, ∀ n : ℕ, T0 ≤ n → ∀ b ∈ S,
      Mb b (n : ℝ)
        ≤ (N (n : ℝ) / Pz (n : ℝ))
          * Real.exp (-(1 - εb b (n : ℝ)) * μ b (n : ℝ)) := by
  exact real_eventually_atTop_to_nat_cast_large_range_finset S htransfer

/-- Coarsen a finite family of per-class transfer defects to a supplied common
defect.  The caller supplies the eventual domination `ε_b ≤ ε` and the
nonnegativity needed to preserve the exponential order. -/
theorem finite_transfer_nat_large_range_finset_mono_defect
    {ι : Type*} (S : Finset ι)
    {Mb : ι → ℝ → ℝ} {N Pz : ℝ → ℝ} {μ εb : ι → ℝ → ℝ} {ε : ℝ → ℝ}
    (hNPz_nonneg : ∀ᶠ X in atTop, 0 ≤ N X / Pz X)
    (hμ_nonneg : ∀ b ∈ S, ∀ᶠ X in atTop, 0 ≤ μ b X)
    (hε_le : ∀ᶠ X in atTop, ∀ b ∈ S, εb b X ≤ ε X)
    (htransfer : ∃ T0 : ℕ, ∀ n : ℕ, T0 ≤ n → ∀ b ∈ S,
      Mb b (n : ℝ)
        ≤ (N (n : ℝ) / Pz (n : ℝ))
          * Real.exp (-(1 - εb b (n : ℝ)) * μ b (n : ℝ))) :
    ∃ T0 : ℕ, ∀ n : ℕ, T0 ≤ n → ∀ b ∈ S,
      Mb b (n : ℝ)
        ≤ (N (n : ℝ) / Pz (n : ℝ))
          * Real.exp (-(1 - ε (n : ℝ)) * μ b (n : ℝ)) := by
  rcases htransfer with ⟨Ttr, hTtr⟩
  rcases real_eventually_atTop_to_nat_cast_large_range hNPz_nonneg with
    ⟨Tnpz, hTnpz⟩
  rcases real_eventually_atTop_to_nat_cast_large_range_finset S hμ_nonneg with
    ⟨Tμ, hTμ⟩
  rcases real_eventually_atTop_to_nat_cast_large_range hε_le with ⟨Tε, hTε⟩
  refine ⟨max Ttr (max Tnpz (max Tμ Tε)), ?_⟩
  intro n hn b hb
  have htr_le : Ttr ≤ n := le_trans (le_max_left _ _) hn
  have hnpz_le : Tnpz ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hμ_le : Tμ ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hn
  have hε_le_n : Tε ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hn
  have hbase := hTtr n htr_le b hb
  have hnpz := hTnpz n hnpz_le
  have hμn := hTμ n hμ_le b hb
  have hεn := hTε n hε_le_n b hb
  have hexp :
      Real.exp (-(1 - εb b (n : ℝ)) * μ b (n : ℝ))
        ≤ Real.exp (-(1 - ε (n : ℝ)) * μ b (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact le_trans hbase (mul_le_mul_of_nonneg_left hexp hnpz)

/-- Coarsen a finite family of per-class transfer exponents to a supplied common
exponent.  This is the package-facing monotonicity step: if
`(1 - ε) μ` is eventually no larger than every per-class
`(1 - ε_b) μ_b`, then the sharper per-class finite-transfer estimates imply
the common-exponent transfer estimate used after summing classes. -/
theorem finite_transfer_nat_large_range_finset_mono_common_exponent
    {ι : Type*} (S : Finset ι)
    {Mb : ι → ℝ → ℝ} {N Pz : ℝ → ℝ} {μb εb : ι → ℝ → ℝ} {μ ε : ℝ → ℝ}
    (hNPz_nonneg : ∀ᶠ X in atTop, 0 ≤ N X / Pz X)
    (hexponent : ∀ᶠ X in atTop, ∀ b ∈ S,
      (1 - ε X) * μ X ≤ (1 - εb b X) * μb b X)
    (htransfer : ∃ T0 : ℕ, ∀ n : ℕ, T0 ≤ n → ∀ b ∈ S,
      Mb b (n : ℝ)
        ≤ (N (n : ℝ) / Pz (n : ℝ))
          * Real.exp (-(1 - εb b (n : ℝ)) * μb b (n : ℝ))) :
    ∃ T0 : ℕ, ∀ n : ℕ, T0 ≤ n → ∀ b ∈ S,
      Mb b (n : ℝ)
        ≤ (N (n : ℝ) / Pz (n : ℝ))
          * Real.exp (-(1 - ε (n : ℝ)) * μ (n : ℝ)) := by
  rcases htransfer with ⟨Ttr, hTtr⟩
  rcases real_eventually_atTop_to_nat_cast_large_range hNPz_nonneg with
    ⟨Tnpz, hTnpz⟩
  rcases real_eventually_atTop_to_nat_cast_large_range hexponent with
    ⟨Texp, hTexponent⟩
  refine ⟨max Ttr (max Tnpz Texp), ?_⟩
  intro n hn b hb
  have htr_le : Ttr ≤ n := le_trans (le_max_left _ _) hn
  have hnpz_le : Tnpz ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hexp_le : Texp ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hbase := hTtr n htr_le b hb
  have hnpz := hTnpz n hnpz_le
  have hexponent_n := hTexponent n hexp_le b hb
  have hexp :
      Real.exp (-(1 - εb b (n : ℝ)) * μb b (n : ℝ))
        ≤ Real.exp (-(1 - ε (n : ℝ)) * μ (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith
  exact le_trans hbase (mul_le_mul_of_nonneg_left hexp hnpz)

/-- Fixed-`m` transported finite-transfer bridge in natural-cutoff large-range
form.

This composes the transported dependency/no-hit estimates, the eventual
finite-transfer assembly, and the real-to-natural threshold extraction.  It
still treats the Bonferroni/decomposition, Brun error envelope, level condition,
and top-coefficient tail as explicit eventual hypotheses. -/
theorem fixed_m_finite_transfer_nat_large_range_of_transported_bounds
    {Mb N Pz μ δb Δb medScale depTail largePrime Xpow errTerm F2R : ℝ → ℝ}
    {εK : ℝ}
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
    (hμtop : Tendsto μ atTop atTop)
    (hPz : ∀ᶠ X in atTop, 1 ≤ Pz X)
    (hXpow : ∀ᶠ X in atTop, 0 ≤ Xpow X)
    (hNpos : ∀ᶠ X in atTop, 0 ≤ N X)
    (hdecomp : ∀ᶠ X in atTop,
      Mb X ≤ (N X / Pz X) * (Inputs.suenProb (μ X) (δb X) (Δb X) + F2R X)
        + errTerm X)
    (herr : ∀ᶠ X in atTop,
      errTerm X ≤ Xpow X * Real.exp ((1 + εK) * μ X))
    (hεle : εK ≤ 1)
    (hlevel : ∀ᶠ X in atTop,
      Pz X * Xpow X * Real.exp (2 * μ X) ≤ N X * Real.exp (-4 * μ X))
    (hF2R : ∀ᶠ X in atTop, F2R X ≤ Real.exp (-3 * μ X)) :
    ∃ εb' : ℝ → ℝ, Tendsto εb' atTop (𝓝 0) ∧
      ∃ T0 : ℕ, ∀ n : ℕ, T0 ≤ n →
        Mb (n : ℝ)
          ≤ (N (n : ℝ) / Pz (n : ℝ))
            * Real.exp (-(1 - εb' (n : ℝ)) * μ (n : ℝ)) := by
  rcases fixed_m_finite_transfer_asymp_eventually_of_transported_bounds
      C₁ C₂ Clarge η hC₁ hC₂ hη hδ_nonneg hΔ_nonneg hμ_nonneg
      hlarge_nonneg hδ_le hΔ_le hlarge_le hmed0 htail_o_μ hμtop hPz hXpow
      hNpos hdecomp herr hεle hlevel hF2R with
    ⟨εb', hεb'0, htransfer⟩
  rcases finite_transfer_asymp_nat_large_range htransfer with ⟨T0, hT0⟩
  exact ⟨εb', hεb'0, T0, hT0⟩

/-- Natural-cutoff large-range form of the transported fixed-`m` bridge with
eventual nonnegativity hypotheses. -/
theorem fixed_m_finite_transfer_nat_large_range_of_transported_bounds_eventually_nonneg
    {Mb N Pz μ δb Δb medScale depTail largePrime Xpow errTerm F2R : ℝ → ℝ}
    {εK : ℝ}
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
    (hμtop : Tendsto μ atTop atTop)
    (hPz : ∀ᶠ X in atTop, 1 ≤ Pz X)
    (hXpow : ∀ᶠ X in atTop, 0 ≤ Xpow X)
    (hNpos : ∀ᶠ X in atTop, 0 ≤ N X)
    (hdecomp : ∀ᶠ X in atTop,
      Mb X ≤ (N X / Pz X) * (Inputs.suenProb (μ X) (δb X) (Δb X) + F2R X)
        + errTerm X)
    (herr : ∀ᶠ X in atTop,
      errTerm X ≤ Xpow X * Real.exp ((1 + εK) * μ X))
    (hεle : εK ≤ 1)
    (hlevel : ∀ᶠ X in atTop,
      Pz X * Xpow X * Real.exp (2 * μ X) ≤ N X * Real.exp (-4 * μ X))
    (hF2R : ∀ᶠ X in atTop, F2R X ≤ Real.exp (-3 * μ X)) :
    ∃ εb' : ℝ → ℝ, Tendsto εb' atTop (𝓝 0) ∧
      ∃ T0 : ℕ, ∀ n : ℕ, T0 ≤ n →
        Mb (n : ℝ)
          ≤ (N (n : ℝ) / Pz (n : ℝ))
            * Real.exp (-(1 - εb' (n : ℝ)) * μ (n : ℝ)) := by
  rcases fixed_m_finite_transfer_asymp_eventually_of_transported_bounds_eventually_nonneg
      C₁ C₂ Clarge η hC₁ hC₂ hη hδ_nonneg hΔ_nonneg hμ_nonneg
      hlarge_nonneg hδ_le hΔ_le hlarge_le hmed0 htail_o_μ hμtop hPz hXpow
      hNpos hdecomp herr hεle hlevel hF2R with
    ⟨εb', hεb'0, htransfer⟩
  rcases finite_transfer_asymp_nat_large_range htransfer with ⟨T0, hT0⟩
  exact ⟨εb', hεb'0, T0, hT0⟩

/-- Finite-family fixed-`m` transported finite-transfer bridge.

For a fixed finite class set, the transported dependency/no-hit hypotheses and
finite-transfer ingredients may be checked class-by-class, while this theorem
produces one natural cutoff valid for all classes in the set. -/
theorem fixed_m_finite_transfer_nat_large_range_finset_of_transported_bounds
    {ι : Type*} (S : Finset ι)
    {Mb : ι → ℝ → ℝ} {N Pz : ℝ → ℝ}
    {μ δb Δb medScale depTail largePrime Xpow errTerm F2R : ι → ℝ → ℝ}
    {εK : ℝ}
    (C₁ C₂ Clarge η : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hη : 0 < η)
    (hδ_nonneg : ∀ b ∈ S, ∀ X, 0 ≤ δb b X)
    (hΔ_nonneg : ∀ b ∈ S, ∀ X, 0 ≤ Δb b X)
    (hμ_nonneg : ∀ b ∈ S, ∀ X, 0 ≤ μ b X)
    (hlarge_nonneg : ∀ b ∈ S, ∀ X, 0 ≤ largePrime b X)
    (hδ_le : ∀ b ∈ S, ∀ᶠ X in atTop,
      δb b X ≤ C₁ * (μ b X * medScale b X) + largePrime b X)
    (hΔ_le : ∀ b ∈ S, ∀ᶠ X in atTop,
      Δb b X ≤ C₂ * ((μ b X) ^ 2 * depTail b X))
    (hlarge_le : ∀ b ∈ S, ∀ᶠ X in atTop,
      largePrime b X ≤ Clarge * X ^ (-η))
    (hmed0 : ∀ b ∈ S, Tendsto (fun X => μ b X * medScale b X) atTop (𝓝 0))
    (htail_o_μ : ∀ b ∈ S,
      Tendsto (fun X => (μ b X) ^ 2 * depTail b X / μ b X) atTop (𝓝 0))
    (hμtop : ∀ b ∈ S, Tendsto (μ b) atTop atTop)
    (hPz : ∀ᶠ X in atTop, 1 ≤ Pz X)
    (hNpos : ∀ᶠ X in atTop, 0 ≤ N X)
    (hXpow : ∀ b ∈ S, ∀ᶠ X in atTop, 0 ≤ Xpow b X)
    (hdecomp : ∀ b ∈ S, ∀ᶠ X in atTop,
      Mb b X ≤ (N X / Pz X) *
        (Inputs.suenProb (μ b X) (δb b X) (Δb b X) + F2R b X) + errTerm b X)
    (herr : ∀ b ∈ S, ∀ᶠ X in atTop,
      errTerm b X ≤ Xpow b X * Real.exp ((1 + εK) * μ b X))
    (hεle : εK ≤ 1)
    (hlevel : ∀ b ∈ S, ∀ᶠ X in atTop,
      Pz X * Xpow b X * Real.exp (2 * μ b X)
        ≤ N X * Real.exp (-4 * μ b X))
    (hF2R : ∀ b ∈ S, ∀ᶠ X in atTop,
      F2R b X ≤ Real.exp (-3 * μ b X)) :
    ∃ εb' : ι → ℝ → ℝ, (∀ b ∈ S, Tendsto (εb' b) atTop (𝓝 0)) ∧
      ∃ T0 : ℕ, ∀ n : ℕ, T0 ≤ n → ∀ b ∈ S,
        Mb b (n : ℝ)
          ≤ (N (n : ℝ) / Pz (n : ℝ))
            * Real.exp (-(1 - εb' b (n : ℝ)) * μ b (n : ℝ)) := by
  classical
  have hsingle : ∀ b ∈ S,
      ∃ εb' : ℝ → ℝ, Tendsto εb' atTop (𝓝 0) ∧
        ∀ᶠ X in atTop,
          Mb b X ≤ (N X / Pz X) * Real.exp (-(1 - εb' X) * μ b X) := by
    intro b hb
    exact fixed_m_finite_transfer_asymp_eventually_of_transported_bounds
      (Mb := Mb b) (N := N) (Pz := Pz) (μ := μ b)
      (δb := δb b) (Δb := Δb b) (medScale := medScale b)
      (depTail := depTail b) (largePrime := largePrime b) (Xpow := Xpow b)
      (errTerm := errTerm b) (F2R := F2R b) (εK := εK)
      C₁ C₂ Clarge η hC₁ hC₂ hη
      (hδ_nonneg b hb) (hΔ_nonneg b hb) (hμ_nonneg b hb)
      (hlarge_nonneg b hb) (hδ_le b hb) (hΔ_le b hb) (hlarge_le b hb)
      (hmed0 b hb) (htail_o_μ b hb) (hμtop b hb) hPz (hXpow b hb)
      hNpos (hdecomp b hb) (herr b hb) hεle (hlevel b hb) (hF2R b hb)
  let εb' : ι → ℝ → ℝ := fun b =>
    if hb : b ∈ S then Classical.choose (hsingle b hb) else fun _ => 0
  have hεb'_tendsto : ∀ b ∈ S, Tendsto (εb' b) atTop (𝓝 0) := by
    intro b hb
    have hspec := Classical.choose_spec (hsingle b hb)
    have hε_eq : εb' b = Classical.choose (hsingle b hb) := by
      dsimp [εb']
      rw [dif_pos hb]
    rw [hε_eq]
    exact hspec.1
  have htransfer : ∀ b ∈ S, ∀ᶠ X in atTop,
      Mb b X ≤ (N X / Pz X) * Real.exp (-(1 - εb' b X) * μ b X) := by
    intro b hb
    have hspec := Classical.choose_spec (hsingle b hb)
    have hε_eq : εb' b = Classical.choose (hsingle b hb) := by
      dsimp [εb']
      rw [dif_pos hb]
    rw [hε_eq]
    exact hspec.2
  rcases finite_transfer_asymp_nat_large_range_finset S htransfer with ⟨T0, hT0⟩
  exact ⟨εb', hεb'_tendsto, T0, hT0⟩

/-- Finite-family fixed-`m` transported finite-transfer bridge with eventual
nonnegativity hypotheses. -/
theorem fixed_m_finite_transfer_nat_large_range_finset_of_transported_bounds_eventually_nonneg
    {ι : Type*} (S : Finset ι)
    {Mb : ι → ℝ → ℝ} {N Pz : ℝ → ℝ}
    {μ δb Δb medScale depTail largePrime Xpow errTerm F2R : ι → ℝ → ℝ}
    {εK : ℝ}
    (C₁ C₂ Clarge η : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hη : 0 < η)
    (hδ_nonneg : ∀ b ∈ S, ∀ᶠ X in atTop, 0 ≤ δb b X)
    (hΔ_nonneg : ∀ b ∈ S, ∀ᶠ X in atTop, 0 ≤ Δb b X)
    (hμ_nonneg : ∀ b ∈ S, ∀ᶠ X in atTop, 0 ≤ μ b X)
    (hlarge_nonneg : ∀ b ∈ S, ∀ᶠ X in atTop, 0 ≤ largePrime b X)
    (hδ_le : ∀ b ∈ S, ∀ᶠ X in atTop,
      δb b X ≤ C₁ * (μ b X * medScale b X) + largePrime b X)
    (hΔ_le : ∀ b ∈ S, ∀ᶠ X in atTop,
      Δb b X ≤ C₂ * ((μ b X) ^ 2 * depTail b X))
    (hlarge_le : ∀ b ∈ S, ∀ᶠ X in atTop,
      largePrime b X ≤ Clarge * X ^ (-η))
    (hmed0 : ∀ b ∈ S, Tendsto (fun X => μ b X * medScale b X) atTop (𝓝 0))
    (htail_o_μ : ∀ b ∈ S,
      Tendsto (fun X => (μ b X) ^ 2 * depTail b X / μ b X) atTop (𝓝 0))
    (hμtop : ∀ b ∈ S, Tendsto (μ b) atTop atTop)
    (hPz : ∀ᶠ X in atTop, 1 ≤ Pz X)
    (hNpos : ∀ᶠ X in atTop, 0 ≤ N X)
    (hXpow : ∀ b ∈ S, ∀ᶠ X in atTop, 0 ≤ Xpow b X)
    (hdecomp : ∀ b ∈ S, ∀ᶠ X in atTop,
      Mb b X ≤ (N X / Pz X) *
        (Inputs.suenProb (μ b X) (δb b X) (Δb b X) + F2R b X) + errTerm b X)
    (herr : ∀ b ∈ S, ∀ᶠ X in atTop,
      errTerm b X ≤ Xpow b X * Real.exp ((1 + εK) * μ b X))
    (hεle : εK ≤ 1)
    (hlevel : ∀ b ∈ S, ∀ᶠ X in atTop,
      Pz X * Xpow b X * Real.exp (2 * μ b X)
        ≤ N X * Real.exp (-4 * μ b X))
    (hF2R : ∀ b ∈ S, ∀ᶠ X in atTop,
      F2R b X ≤ Real.exp (-3 * μ b X)) :
    ∃ εb' : ι → ℝ → ℝ, (∀ b ∈ S, Tendsto (εb' b) atTop (𝓝 0)) ∧
      ∃ T0 : ℕ, ∀ n : ℕ, T0 ≤ n → ∀ b ∈ S,
        Mb b (n : ℝ)
          ≤ (N (n : ℝ) / Pz (n : ℝ))
            * Real.exp (-(1 - εb' b (n : ℝ)) * μ b (n : ℝ)) := by
  classical
  have hsingle : ∀ b ∈ S,
      ∃ εb' : ℝ → ℝ, Tendsto εb' atTop (𝓝 0) ∧
        ∀ᶠ X in atTop,
          Mb b X ≤ (N X / Pz X) * Real.exp (-(1 - εb' X) * μ b X) := by
    intro b hb
    exact fixed_m_finite_transfer_asymp_eventually_of_transported_bounds_eventually_nonneg
      (Mb := Mb b) (N := N) (Pz := Pz) (μ := μ b)
      (δb := δb b) (Δb := Δb b) (medScale := medScale b)
      (depTail := depTail b) (largePrime := largePrime b) (Xpow := Xpow b)
      (errTerm := errTerm b) (F2R := F2R b) (εK := εK)
      C₁ C₂ Clarge η hC₁ hC₂ hη
      (hδ_nonneg b hb) (hΔ_nonneg b hb) (hμ_nonneg b hb)
      (hlarge_nonneg b hb) (hδ_le b hb) (hΔ_le b hb) (hlarge_le b hb)
      (hmed0 b hb) (htail_o_μ b hb) (hμtop b hb) hPz (hXpow b hb)
      hNpos (hdecomp b hb) (herr b hb) hεle (hlevel b hb) (hF2R b hb)
  let εb' : ι → ℝ → ℝ := fun b =>
    if hb : b ∈ S then Classical.choose (hsingle b hb) else fun _ => 0
  have hεb'_tendsto : ∀ b ∈ S, Tendsto (εb' b) atTop (𝓝 0) := by
    intro b hb
    have hspec := Classical.choose_spec (hsingle b hb)
    have hε_eq : εb' b = Classical.choose (hsingle b hb) := by
      dsimp [εb']
      rw [dif_pos hb]
    rw [hε_eq]
    exact hspec.1
  have htransfer : ∀ b ∈ S, ∀ᶠ X in atTop,
      Mb b X ≤ (N X / Pz X) * Real.exp (-(1 - εb' b X) * μ b X) := by
    intro b hb
    have hspec := Classical.choose_spec (hsingle b hb)
    have hε_eq : εb' b = Classical.choose (hsingle b hb) := by
      dsimp [εb']
      rw [dif_pos hb]
    rw [hε_eq]
    exact hspec.2
  rcases finite_transfer_asymp_nat_large_range_finset S htransfer with ⟨T0, hT0⟩
  exact ⟨εb', hεb'_tendsto, T0, hT0⟩

/-- Finite-family fixed-`m` transported finite-transfer bridge in the common
exponent shape used by the reduced-class summation.

The transported fixed-`m` estimates naturally produce a finite family of
per-class defects and scales.  If the caller supplies the final common exponent
domination needed for the paper's uniform-in-class transfer statement, this
bridge converts those transported estimates into the exact common finite-range
bound consumed by the fixed-numerator package constructors. -/
theorem fixed_m_finite_transfer_nat_large_range_finset_common_exponent_of_transported_bounds
    {ι : Type*} (S : Finset ι)
    {Mb : ι → ℝ → ℝ} {N Pz : ℝ → ℝ}
    {μb δb Δb medScale depTail largePrime Xpow errTerm F2R : ι → ℝ → ℝ}
    {μ ε : ℝ → ℝ} {εK : ℝ}
    (C₁ C₂ Clarge η : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hη : 0 < η)
    (hδ_nonneg : ∀ b ∈ S, ∀ X, 0 ≤ δb b X)
    (hΔ_nonneg : ∀ b ∈ S, ∀ X, 0 ≤ Δb b X)
    (hμ_nonneg : ∀ b ∈ S, ∀ X, 0 ≤ μb b X)
    (hlarge_nonneg : ∀ b ∈ S, ∀ X, 0 ≤ largePrime b X)
    (hδ_le : ∀ b ∈ S, ∀ᶠ X in atTop,
      δb b X ≤ C₁ * (μb b X * medScale b X) + largePrime b X)
    (hΔ_le : ∀ b ∈ S, ∀ᶠ X in atTop,
      Δb b X ≤ C₂ * ((μb b X) ^ 2 * depTail b X))
    (hlarge_le : ∀ b ∈ S, ∀ᶠ X in atTop,
      largePrime b X ≤ Clarge * X ^ (-η))
    (hmed0 : ∀ b ∈ S, Tendsto (fun X => μb b X * medScale b X) atTop (𝓝 0))
    (htail_o_μ : ∀ b ∈ S,
      Tendsto (fun X => (μb b X) ^ 2 * depTail b X / μb b X) atTop (𝓝 0))
    (hμtop : ∀ b ∈ S, Tendsto (μb b) atTop atTop)
    (hPz : ∀ᶠ X in atTop, 1 ≤ Pz X)
    (hNpos : ∀ᶠ X in atTop, 0 ≤ N X)
    (hXpow : ∀ b ∈ S, ∀ᶠ X in atTop, 0 ≤ Xpow b X)
    (hdecomp : ∀ b ∈ S, ∀ᶠ X in atTop,
      Mb b X ≤ (N X / Pz X) *
        (Inputs.suenProb (μb b X) (δb b X) (Δb b X) + F2R b X) + errTerm b X)
    (herr : ∀ b ∈ S, ∀ᶠ X in atTop,
      errTerm b X ≤ Xpow b X * Real.exp ((1 + εK) * μb b X))
    (hεle : εK ≤ 1)
    (hlevel : ∀ b ∈ S, ∀ᶠ X in atTop,
      Pz X * Xpow b X * Real.exp (2 * μb b X)
        ≤ N X * Real.exp (-4 * μb b X))
    (hF2R : ∀ b ∈ S, ∀ᶠ X in atTop,
      F2R b X ≤ Real.exp (-3 * μb b X))
    (hcommon : ∀ εb' : ι → ℝ → ℝ,
      (∀ b ∈ S, Tendsto (εb' b) atTop (𝓝 0)) →
        ∀ᶠ X in atTop, ∀ b ∈ S,
          (1 - ε X) * μ X ≤ (1 - εb' b X) * μb b X) :
    ∃ T0 : ℕ, ∀ n : ℕ, T0 ≤ n → ∀ b ∈ S,
      Mb b (n : ℝ)
        ≤ (N (n : ℝ) / Pz (n : ℝ))
          * Real.exp (-(1 - ε (n : ℝ)) * μ (n : ℝ)) := by
  rcases fixed_m_finite_transfer_nat_large_range_finset_of_transported_bounds
      (S := S) (Mb := Mb) (N := N) (Pz := Pz) (μ := μb)
      (δb := δb) (Δb := Δb) (medScale := medScale)
      (depTail := depTail) (largePrime := largePrime) (Xpow := Xpow)
      (errTerm := errTerm) (F2R := F2R) (εK := εK)
      C₁ C₂ Clarge η hC₁ hC₂ hη hδ_nonneg hΔ_nonneg hμ_nonneg
      hlarge_nonneg hδ_le hΔ_le hlarge_le hmed0 htail_o_μ hμtop hPz
      hNpos hXpow hdecomp herr hεle hlevel hF2R with
    ⟨εb', hεb'_tendsto, htransfer⟩
  have hNPz_nonneg : ∀ᶠ X in atTop, 0 ≤ N X / Pz X := by
    filter_upwards [hNpos, hPz] with X hNX hPzX
    exact div_nonneg hNX (le_trans zero_le_one hPzX)
  exact finite_transfer_nat_large_range_finset_mono_common_exponent
    (S := S) (Mb := Mb) (N := N) (Pz := Pz) (μb := μb) (εb := εb')
    (μ := μ) (ε := ε) hNPz_nonneg (hcommon εb' hεb'_tendsto) htransfer

/-- Common-scale finite-family fixed-`m` transported finite-transfer bridge.

When all reduced classes share the same mass scale `μ`, the finite collection of
per-class `o(1)` transfer defects produced by the transported fixed-`m` bridge
can be replaced by one explicit common `o(1)` defect, namely the finite sum of
their absolute values.  This discharges the finite-class uniformity step without
introducing a new analytic input. -/
theorem fixed_m_finite_transfer_nat_large_range_finset_common_defect_of_transported_bounds
    {ι : Type*} (S : Finset ι)
    {Mb : ι → ℝ → ℝ} {N Pz μ : ℝ → ℝ}
    {δb Δb medScale depTail largePrime Xpow errTerm F2R : ι → ℝ → ℝ}
    {εK : ℝ}
    (C₁ C₂ Clarge η : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hη : 0 < η)
    (hδ_nonneg : ∀ b ∈ S, ∀ X, 0 ≤ δb b X)
    (hΔ_nonneg : ∀ b ∈ S, ∀ X, 0 ≤ Δb b X)
    (hμ_nonneg : ∀ X, 0 ≤ μ X)
    (hlarge_nonneg : ∀ b ∈ S, ∀ X, 0 ≤ largePrime b X)
    (hδ_le : ∀ b ∈ S, ∀ᶠ X in atTop,
      δb b X ≤ C₁ * (μ X * medScale b X) + largePrime b X)
    (hΔ_le : ∀ b ∈ S, ∀ᶠ X in atTop,
      Δb b X ≤ C₂ * ((μ X) ^ 2 * depTail b X))
    (hlarge_le : ∀ b ∈ S, ∀ᶠ X in atTop,
      largePrime b X ≤ Clarge * X ^ (-η))
    (hmed0 : ∀ b ∈ S, Tendsto (fun X => μ X * medScale b X) atTop (𝓝 0))
    (htail_o_μ : ∀ b ∈ S,
      Tendsto (fun X => (μ X) ^ 2 * depTail b X / μ X) atTop (𝓝 0))
    (hμtop : Tendsto μ atTop atTop)
    (hPz : ∀ᶠ X in atTop, 1 ≤ Pz X)
    (hNpos : ∀ᶠ X in atTop, 0 ≤ N X)
    (hXpow : ∀ b ∈ S, ∀ᶠ X in atTop, 0 ≤ Xpow b X)
    (hdecomp : ∀ b ∈ S, ∀ᶠ X in atTop,
      Mb b X ≤ (N X / Pz X) *
        (Inputs.suenProb (μ X) (δb b X) (Δb b X) + F2R b X) + errTerm b X)
    (herr : ∀ b ∈ S, ∀ᶠ X in atTop,
      errTerm b X ≤ Xpow b X * Real.exp ((1 + εK) * μ X))
    (hεle : εK ≤ 1)
    (hlevel : ∀ b ∈ S, ∀ᶠ X in atTop,
      Pz X * Xpow b X * Real.exp (2 * μ X)
        ≤ N X * Real.exp (-4 * μ X))
    (hF2R : ∀ b ∈ S, ∀ᶠ X in atTop,
      F2R b X ≤ Real.exp (-3 * μ X)) :
    ∃ ε : ℝ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∃ T0 : ℕ, ∀ n : ℕ, T0 ≤ n → ∀ b ∈ S,
        Mb b (n : ℝ)
          ≤ (N (n : ℝ) / Pz (n : ℝ))
            * Real.exp (-(1 - ε (n : ℝ)) * μ (n : ℝ)) := by
  classical
  rcases fixed_m_finite_transfer_nat_large_range_finset_of_transported_bounds
      (S := S) (Mb := Mb) (N := N) (Pz := Pz) (μ := fun _ => μ)
      (δb := δb) (Δb := Δb) (medScale := medScale)
      (depTail := depTail) (largePrime := largePrime) (Xpow := Xpow)
      (errTerm := errTerm) (F2R := F2R) (εK := εK)
      C₁ C₂ Clarge η hC₁ hC₂ hη hδ_nonneg hΔ_nonneg
      (fun _ _ => hμ_nonneg) hlarge_nonneg hδ_le hΔ_le hlarge_le hmed0
      htail_o_μ (fun _ _ => hμtop) hPz hNpos hXpow hdecomp herr hεle
      hlevel hF2R with
    ⟨εb', hεb'_tendsto, htransfer⟩
  let ε : ℝ → ℝ := fun X => ∑ b ∈ S, |εb' b X|
  have hε_tendsto : Tendsto ε atTop (𝓝 0) := by
    have hsum : Tendsto (fun X => ∑ b ∈ S, |εb' b X|) atTop
        (𝓝 (∑ b ∈ S, (0 : ℝ))) := by
      apply tendsto_finset_sum
      intro b hb
      simpa using (hεb'_tendsto b hb).abs
    simpa [ε] using hsum
  have hNPz_nonneg : ∀ᶠ X in atTop, 0 ≤ N X / Pz X := by
    filter_upwards [hNpos, hPz] with X hNX hPzX
    exact div_nonneg hNX (le_trans zero_le_one hPzX)
  have hμ_nonneg_eventually : ∀ b ∈ S, ∀ᶠ X in atTop, 0 ≤ μ X := by
    intro _ _
    exact Eventually.of_forall hμ_nonneg
  have hε_le : ∀ᶠ X in atTop, ∀ b ∈ S, εb' b X ≤ ε X := by
    exact Eventually.of_forall (fun X b hb =>
      le_trans (le_abs_self (εb' b X))
        (Finset.single_le_sum
          (s := S) (a := b) (f := fun b => |εb' b X|)
          (fun y _ => abs_nonneg (εb' y X)) hb))
  refine ⟨ε, hε_tendsto, ?_⟩
  exact finite_transfer_nat_large_range_finset_mono_defect
    (S := S) (Mb := Mb) (N := N) (Pz := Pz) (μ := fun _ => μ)
    (εb := εb') (ε := ε) hNPz_nonneg hμ_nonneg_eventually hε_le htransfer

/-- Common-scale finite-family fixed-`m` transported finite-transfer bridge
with eventual nonnegativity hypotheses. -/
theorem fixed_m_finite_transfer_nat_large_range_finset_common_defect_of_transported_bounds_eventually_nonneg
    {ι : Type*} (S : Finset ι)
    {Mb : ι → ℝ → ℝ} {N Pz μ : ℝ → ℝ}
    {δb Δb medScale depTail largePrime Xpow errTerm F2R : ι → ℝ → ℝ}
    {εK : ℝ}
    (C₁ C₂ Clarge η : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hη : 0 < η)
    (hδ_nonneg : ∀ b ∈ S, ∀ᶠ X in atTop, 0 ≤ δb b X)
    (hΔ_nonneg : ∀ b ∈ S, ∀ᶠ X in atTop, 0 ≤ Δb b X)
    (hμ_nonneg : ∀ᶠ X in atTop, 0 ≤ μ X)
    (hlarge_nonneg : ∀ b ∈ S, ∀ᶠ X in atTop, 0 ≤ largePrime b X)
    (hδ_le : ∀ b ∈ S, ∀ᶠ X in atTop,
      δb b X ≤ C₁ * (μ X * medScale b X) + largePrime b X)
    (hΔ_le : ∀ b ∈ S, ∀ᶠ X in atTop,
      Δb b X ≤ C₂ * ((μ X) ^ 2 * depTail b X))
    (hlarge_le : ∀ b ∈ S, ∀ᶠ X in atTop,
      largePrime b X ≤ Clarge * X ^ (-η))
    (hmed0 : ∀ b ∈ S, Tendsto (fun X => μ X * medScale b X) atTop (𝓝 0))
    (htail_o_μ : ∀ b ∈ S,
      Tendsto (fun X => (μ X) ^ 2 * depTail b X / μ X) atTop (𝓝 0))
    (hμtop : Tendsto μ atTop atTop)
    (hPz : ∀ᶠ X in atTop, 1 ≤ Pz X)
    (hNpos : ∀ᶠ X in atTop, 0 ≤ N X)
    (hXpow : ∀ b ∈ S, ∀ᶠ X in atTop, 0 ≤ Xpow b X)
    (hdecomp : ∀ b ∈ S, ∀ᶠ X in atTop,
      Mb b X ≤ (N X / Pz X) *
        (Inputs.suenProb (μ X) (δb b X) (Δb b X) + F2R b X) + errTerm b X)
    (herr : ∀ b ∈ S, ∀ᶠ X in atTop,
      errTerm b X ≤ Xpow b X * Real.exp ((1 + εK) * μ X))
    (hεle : εK ≤ 1)
    (hlevel : ∀ b ∈ S, ∀ᶠ X in atTop,
      Pz X * Xpow b X * Real.exp (2 * μ X)
        ≤ N X * Real.exp (-4 * μ X))
    (hF2R : ∀ b ∈ S, ∀ᶠ X in atTop,
      F2R b X ≤ Real.exp (-3 * μ X)) :
    ∃ ε : ℝ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∃ T0 : ℕ, ∀ n : ℕ, T0 ≤ n → ∀ b ∈ S,
        Mb b (n : ℝ)
          ≤ (N (n : ℝ) / Pz (n : ℝ))
            * Real.exp (-(1 - ε (n : ℝ)) * μ (n : ℝ)) := by
  classical
  rcases fixed_m_finite_transfer_nat_large_range_finset_of_transported_bounds_eventually_nonneg
      (S := S) (Mb := Mb) (N := N) (Pz := Pz) (μ := fun _ => μ)
      (δb := δb) (Δb := Δb) (medScale := medScale)
      (depTail := depTail) (largePrime := largePrime) (Xpow := Xpow)
      (errTerm := errTerm) (F2R := F2R) (εK := εK)
      C₁ C₂ Clarge η hC₁ hC₂ hη hδ_nonneg hΔ_nonneg
      (fun _ _ => hμ_nonneg) hlarge_nonneg hδ_le hΔ_le hlarge_le hmed0
      htail_o_μ (fun _ _ => hμtop) hPz hNpos hXpow hdecomp herr hεle
      hlevel hF2R with
    ⟨εb', hεb'_tendsto, htransfer⟩
  let ε : ℝ → ℝ := fun X => ∑ b ∈ S, |εb' b X|
  have hε_tendsto : Tendsto ε atTop (𝓝 0) := by
    have hsum : Tendsto (fun X => ∑ b ∈ S, |εb' b X|) atTop
        (𝓝 (∑ b ∈ S, (0 : ℝ))) := by
      apply tendsto_finset_sum
      intro b hb
      simpa using (hεb'_tendsto b hb).abs
    simpa [ε] using hsum
  have hNPz_nonneg : ∀ᶠ X in atTop, 0 ≤ N X / Pz X := by
    filter_upwards [hNpos, hPz] with X hNX hPzX
    exact div_nonneg hNX (le_trans zero_le_one hPzX)
  have hμ_nonneg_eventually : ∀ b ∈ S, ∀ᶠ X in atTop, 0 ≤ μ X := by
    intro _ _
    exact hμ_nonneg
  have hε_le : ∀ᶠ X in atTop, ∀ b ∈ S, εb' b X ≤ ε X := by
    exact Eventually.of_forall (fun X b hb =>
      le_trans (le_abs_self (εb' b X))
        (Finset.single_le_sum
          (s := S) (a := b) (f := fun b => |εb' b X|)
          (fun y _ => abs_nonneg (εb' y X)) hb))
  refine ⟨ε, hε_tendsto, ?_⟩
  exact finite_transfer_nat_large_range_finset_mono_defect
    (S := S) (Mb := Mb) (N := N) (Pz := Pz) (μ := fun _ => μ)
    (εb := εb') (ε := ε) hNPz_nonneg hμ_nonneg_eventually hε_le htransfer

/-- Common-scale finite-family fixed-`m` finite transfer with the local scale
limits discharged from the paper's logarithmic envelopes.

This strengthens
`fixed_m_finite_transfer_nat_large_range_finset_common_defect_of_transported_bounds_eventually_nonneg`:
the caller supplies the mass, medium-prime, and dependency-tail log-power
bounds, and the bridge derives the two scale limits internally before applying
the transported Suen finite-transfer theorem. -/
theorem fixed_m_finite_transfer_nat_large_range_finset_common_defect_of_log_power_bounds_eventually_nonneg
    {ι : Type*} (S : Finset ι)
    {Mb : ι → ℝ → ℝ} {N Pz μ : ℝ → ℝ}
    {δb Δb medScale depTail largePrime Xpow errTerm F2R : ι → ℝ → ℝ}
    {εK : ℝ}
    (Cμ Cmed Ctail C₁ C₂ Clarge ηmed ηtail ηlarge : ℝ)
    (hηmed : 0 < ηmed) (hηtail : 0 < ηtail) (hηlarge : 0 < ηlarge)
    (hCμ : 0 ≤ Cμ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hδ_nonneg : ∀ b ∈ S, ∀ᶠ X in atTop, 0 ≤ δb b X)
    (hΔ_nonneg : ∀ b ∈ S, ∀ᶠ X in atTop, 0 ≤ Δb b X)
    (hμ_nonneg : ∀ᶠ X in atTop, 0 ≤ μ X)
    (hmedNonneg : ∀ b ∈ S, ∀ᶠ X in atTop, 0 ≤ medScale b X)
    (htailNonneg : ∀ b ∈ S, ∀ᶠ X in atTop, 0 ≤ depTail b X)
    (hlarge_nonneg : ∀ b ∈ S, ∀ᶠ X in atTop, 0 ≤ largePrime b X)
    (hmassLog : ∀ᶠ X in atTop, μ X ≤ Cμ * (Real.log X) ^ 3)
    (hmedUpper : ∀ b ∈ S, ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * medScale b X ≤ Cmed * (Real.log X) ^ (-ηmed))
    (htailUpper : ∀ b ∈ S, ∀ᶠ X in atTop,
      (Real.log X) ^ 3 * depTail b X ≤ Ctail * (Real.log X) ^ (-ηtail))
    (hδ_le : ∀ b ∈ S, ∀ᶠ X in atTop,
      δb b X ≤ C₁ * (μ X * medScale b X) + largePrime b X)
    (hΔ_le : ∀ b ∈ S, ∀ᶠ X in atTop,
      Δb b X ≤ C₂ * ((μ X) ^ 2 * depTail b X))
    (hlarge_le : ∀ b ∈ S, ∀ᶠ X in atTop,
      largePrime b X ≤ Clarge * X ^ (-ηlarge))
    (hμtop : Tendsto μ atTop atTop)
    (hPz : ∀ᶠ X in atTop, 1 ≤ Pz X)
    (hNpos : ∀ᶠ X in atTop, 0 ≤ N X)
    (hXpow : ∀ b ∈ S, ∀ᶠ X in atTop, 0 ≤ Xpow b X)
    (hdecomp : ∀ b ∈ S, ∀ᶠ X in atTop,
      Mb b X ≤ (N X / Pz X) *
        (Inputs.suenProb (μ X) (δb b X) (Δb b X) + F2R b X) + errTerm b X)
    (herr : ∀ b ∈ S, ∀ᶠ X in atTop,
      errTerm b X ≤ Xpow b X * Real.exp ((1 + εK) * μ X))
    (hεle : εK ≤ 1)
    (hlevel : ∀ b ∈ S, ∀ᶠ X in atTop,
      Pz X * Xpow b X * Real.exp (2 * μ X)
        ≤ N X * Real.exp (-4 * μ X))
    (hF2R : ∀ b ∈ S, ∀ᶠ X in atTop,
      F2R b X ≤ Real.exp (-3 * μ X)) :
    ∃ ε : ℝ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∃ T0 : ℕ, ∀ n : ℕ, T0 ≤ n → ∀ b ∈ S,
        Mb b (n : ℝ)
          ≤ (N (n : ℝ) / Pz (n : ℝ))
            * Real.exp (-(1 - ε (n : ℝ)) * μ (n : ℝ)) := by
  have hscale : ∀ b ∈ S,
      Tendsto (fun X => μ X * medScale b X) atTop (𝓝 0)
        ∧ Tendsto (fun X => μ X * depTail b X) atTop (𝓝 0)
        ∧ Tendsto (fun X => (μ X) ^ 2 * depTail b X / μ X) atTop (𝓝 0) := by
    intro b hb
    exact mass_dependency_scale_from_log_power_bounds_eventually_nonneg
      μ (depTail b) (medScale b) Cμ Cmed Ctail ηmed ηtail hηmed hηtail
      hμ_nonneg hmassLog (hmedNonneg b hb) (htailNonneg b hb)
      (hmedUpper b hb) (htailUpper b hb) hCμ
  exact fixed_m_finite_transfer_nat_large_range_finset_common_defect_of_transported_bounds_eventually_nonneg
    (S := S) (Mb := Mb) (N := N) (Pz := Pz) (μ := μ)
    (δb := δb) (Δb := Δb) (medScale := medScale) (depTail := depTail)
    (largePrime := largePrime) (Xpow := Xpow) (errTerm := errTerm)
    (F2R := F2R) (εK := εK)
    C₁ C₂ Clarge ηlarge hC₁ hC₂ hηlarge hδ_nonneg hΔ_nonneg hμ_nonneg
    hlarge_nonneg hδ_le hΔ_le hlarge_le
    (fun b hb => (hscale b hb).1) (fun b hb => (hscale b hb).2.2)
    hμtop hPz hNpos hXpow hdecomp herr hεle hlevel hF2R

/-! ## Part 3.  Summing over reduced base classes → `E_red(N;z)` (tex 2035–2043). -/

/-- **Reduced missed count from the per-base transfer** (`eq:reduced-missed`,
tex 2035–2043).

Summing `thm:finite-transfer` over the `W = φ(P(z))` reduced classes `b` gives
`E_red(N;z) = ∑_b M_b(N) ≤ W·(N/P(z))·exp{-(1-ε)μ} ≤ N·exp{-(1-ε)μ}`, using the
*uniform-in-`b`* per-base bound and `W ≤ P(z)` (there are at most `P(z)` reduced
classes), so `W/P(z) ≤ 1`.  We state it abstractly: `Ered` is bounded by the sum
over a finite index set `cls` of reduced classes, each obeying the per-base
transfer with a *common* defect `ε` (uniformity in `b`, tex 2013), and
`(cls.card : ℝ) ≤ P(z)`. -/
theorem reduced_missed_of_finite_transfer
    {ι : Type*} (cls : Finset ι)
    {Mb : ι → ℝ} {N Pz μ ε : ℝ}
    (hPz : 1 ≤ Pz) (hNpos : 0 ≤ N)
    (hcard : (cls.card : ℝ) ≤ Pz)
    (htransfer : ∀ b ∈ cls,
      Mb b ≤ (N / Pz) * Real.exp (-(1 - ε) * μ)) :
    (∑ b ∈ cls, Mb b) ≤ N * Real.exp (-(1 - ε) * μ) := by
  have hPz_pos : 0 < Pz := lt_of_lt_of_le zero_lt_one hPz
  -- ∑_b M_b ≤ ∑_b (N/Pz)·e = card·(N/Pz)·e ≤ Pz·(N/Pz)·e = N·e
  have hNPz_nonneg : 0 ≤ N / Pz := div_nonneg hNpos hPz_pos.le
  have he_nonneg : 0 ≤ Real.exp (-(1 - ε) * μ) := (Real.exp_pos _).le
  calc (∑ b ∈ cls, Mb b)
        ≤ ∑ _b ∈ cls, (N / Pz) * Real.exp (-(1 - ε) * μ) :=
          Finset.sum_le_sum htransfer
    _ = (cls.card : ℝ) * ((N / Pz) * Real.exp (-(1 - ε) * μ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Pz * ((N / Pz) * Real.exp (-(1 - ε) * μ)) := by
          apply mul_le_mul_of_nonneg_right hcard
          exact mul_nonneg hNPz_nonneg he_nonneg
    _ = N * Real.exp (-(1 - ε) * μ) := by
          field_simp

/-- Variant of `reduced_missed_of_finite_transfer` with the natural
paper-facing modulus lower bound `1 ≤ Pz`.

The strict positivity needed for division is elementary and is discharged here,
so downstream transfer routes do not have to carry a separate `0 < Pz`
hypothesis. -/
theorem reduced_missed_of_finite_transfer_of_one_le
    {ι : Type*} (cls : Finset ι)
    {Mb : ι → ℝ} {N Pz μ ε : ℝ}
    (hPz : 1 ≤ Pz) (hNpos : 0 ≤ N)
    (hcard : (cls.card : ℝ) ≤ Pz)
    (htransfer : ∀ b ∈ cls,
      Mb b ≤ (N / Pz) * Real.exp (-(1 - ε) * μ)) :
    (∑ b ∈ cls, Mb b) ≤ N * Real.exp (-(1 - ε) * μ) :=
  reduced_missed_of_finite_transfer cls hPz hNpos hcard htransfer

/-- **Saving-shape comparison** (`eq:mu-asymp-N`, tex 2024).

Under `μ_b ≍_α (log N)^{3/4}`, the per-class exponent satisfies, for a fixed
`c₁ > 0` with `c₁·(log N)^{3/4} ≤ (1-ε)·μ_b`, the inequality
`exp{-(1-ε)μ_b} ≤ exp{-c₁(log N)^{3/4}} = saving c₁ N`.  This converts the
transfer's `exp{-(1-o(1))μ_b}` into the manuscript's `saving` shape used by
`MainInputs.Ered_bound`. -/
theorem exp_neg_mu_le_saving
    {μ ε c₁ : ℝ} {N : ℕ}
    (hbound : c₁ * (Real.log N) ^ ((3 : ℝ) / 4) ≤ (1 - ε) * μ) :
    Real.exp (-(1 - ε) * μ) ≤ saving c₁ N := by
  unfold saving
  apply Real.exp_le_exp.mpr
  -- -(1-ε)μ ≤ -c₁(log N)^{3/4}  ⟺  c₁(log N)^{3/4} ≤ (1-ε)μ
  nlinarith [hbound]

/-- **`E_red`-shaped bound from the finite transfer** (assembles `eq:reduced-missed`
into the `MainInputs.Ered_bound` shape, tex 2042–2043).

Combining `reduced_missed_of_finite_transfer` (summation over reduced `b`) with
`exp_neg_mu_le_saving` (the `μ_b ≍ (log N)^{3/4}` conversion), the reduced missed
count `E_red := ∑_b M_b(N)` obeys `E_red ≤ N·saving c₁ N`, i.e. *exactly* the
`MainInputs.Ered_bound` inequality with implied constant `1`.  This is the
deliverable consumed by `AbstractMain.MainInputs.Ered_bound`. -/
theorem Ered_bound_of_finite_transfer
    {ι : Type*} (cls : Finset ι)
    {Mb : ι → ℝ} {N Pz μ ε c₁ : ℝ} {Nnat : ℕ}
    (hPz : 1 ≤ Pz) (hNpos : 0 ≤ N)
    (hcard : (cls.card : ℝ) ≤ Pz)
    (htransfer : ∀ b ∈ cls,
      Mb b ≤ (N / Pz) * Real.exp (-(1 - ε) * μ))
    (hsaving : c₁ * (Real.log Nnat) ^ ((3 : ℝ) / 4) ≤ (1 - ε) * μ) :
    (∑ b ∈ cls, Mb b) ≤ N * saving c₁ Nnat := by
  have h1 : (∑ b ∈ cls, Mb b) ≤ N * Real.exp (-(1 - ε) * μ) :=
    reduced_missed_of_finite_transfer cls hPz hNpos hcard htransfer
  have h2 : Real.exp (-(1 - ε) * μ) ≤ saving c₁ Nnat :=
    exp_neg_mu_le_saving hsaving
  calc (∑ b ∈ cls, Mb b) ≤ N * Real.exp (-(1 - ε) * μ) := h1
    _ ≤ N * saving c₁ Nnat := mul_le_mul_of_nonneg_left h2 hNpos

/-- `Ered_bound_of_finite_transfer` with `1 ≤ Pz` instead of a separate
strict-positivity side condition. -/
theorem Ered_bound_of_finite_transfer_of_one_le
    {ι : Type*} (cls : Finset ι)
    {Mb : ι → ℝ} {N Pz μ ε c₁ : ℝ} {Nnat : ℕ}
    (hPz : 1 ≤ Pz) (hNpos : 0 ≤ N)
    (hcard : (cls.card : ℝ) ≤ Pz)
    (htransfer : ∀ b ∈ cls,
      Mb b ≤ (N / Pz) * Real.exp (-(1 - ε) * μ))
    (hsaving : c₁ * (Real.log Nnat) ^ ((3 : ℝ) / 4) ≤ (1 - ε) * μ) :
    (∑ b ∈ cls, Mb b) ≤ N * saving c₁ Nnat :=
  Ered_bound_of_finite_transfer cls
    hPz hNpos hcard htransfer hsaving

/-- Any fixed finite initial range can be absorbed into the same saving shape by
enlarging the implied constant.

This is the formal version of the manuscript's repeated "enlarge the constant
to absorb the remaining finite range" step.  It is purely finite bookkeeping:
for a fixed threshold `T`, the ratios
`Ered N / (N * saving c N)` over `3 <= N < T` have a finite sum, and a constant
larger than that sum dominates every term in the range. -/
theorem finite_initial_saving_bound
    (Ered : ℕ → ℕ) {c : ℝ} (_hc : 0 < c) (T : ℕ) :
    ∃ Cinit : ℝ, 0 < Cinit ∧
      ∀ N : ℕ, 3 ≤ N → N < T →
        (Ered N : ℝ) ≤ Cinit * ((N : ℝ) * saving c N) := by
  classical
  let scale : ℕ → ℝ := fun n => (n : ℝ) * saving c n
  let term : ℕ → ℝ := fun n => (Ered n : ℝ) / scale n
  let Cinit : ℝ := 1 + ∑ n in Finset.range T, term n
  have hterm_nonneg : ∀ n ∈ Finset.range T, 0 ≤ term n := by
    intro n _hn
    have hscale_nonneg : 0 ≤ scale n := by
      dsimp [scale, saving]
      positivity
    dsimp [term]
    exact div_nonneg (by positivity) hscale_nonneg
  have hsum_nonneg : 0 ≤ ∑ n in Finset.range T, term n :=
    Finset.sum_nonneg hterm_nonneg
  refine ⟨Cinit, ?_, ?_⟩
  · dsimp [Cinit]
    linarith
  · intro N hN hNT
    have hmem : N ∈ Finset.range T := Finset.mem_range.mpr hNT
    have hterm_le_sum : term N ≤ ∑ n in Finset.range T, term n :=
      Finset.single_le_sum hterm_nonneg hmem
    have hterm_le_C : term N ≤ Cinit := by
      dsimp [Cinit]
      linarith
    have hNpos : 0 < (N : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 3) hN)
    have hscale_pos : 0 < scale N := by
      dsimp [scale, saving]
      positivity
    have hmul := mul_le_mul_of_nonneg_right hterm_le_C hscale_pos.le
    have hterm_scale : term N * scale N = (Ered N : ℝ) := by
      dsimp [term]
      field_simp [hscale_pos.ne']
    calc
      (Ered N : ℝ) = term N * scale N := hterm_scale.symm
      _ ≤ Cinit * scale N := hmul
      _ = Cinit * ((N : ℝ) * saving c N) := by rfl

/-- Global reduced-count bound from a large-`N` estimate plus an explicit
finite-initial certificate.

This is the constant-enlargement bookkeeping behind the manuscript's passage
from asymptotic estimates to the `∀ N ≥ 3` `MainInputs.Ered_bound` shape.  The
large range may come from the analytic proof; the small range must be supplied
as a finite certificate bound.  No analytic input is used here. -/
theorem Ered_bound_global_of_large_and_initial
    (Ered : ℕ → ℕ) (c Cevent Cinit : ℝ) (T : ℕ)
    (_hc : 0 < c) (hCevent : 0 < Cevent) (hCinit : 0 < Cinit)
    (hlarge : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      (Ered N : ℝ) ≤ Cevent * ((N : ℝ) * saving c N))
    (hinitial : ∀ N : ℕ, 3 ≤ N → N < T →
      (Ered N : ℝ) ≤ Cinit * ((N : ℝ) * saving c N)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      (Ered N : ℝ) ≤ C * ((N : ℝ) * saving c N) := by
  refine ⟨max Cevent Cinit, ?_, ?_⟩
  · have _hlargeC : 0 < max Cevent Cinit :=
      lt_of_lt_of_le hCevent (le_max_left _ _)
    exact lt_of_lt_of_le hCinit (le_max_right _ _)
  intro N hN
  have hscale_nonneg : 0 ≤ (N : ℝ) * saving c N := by
    unfold saving
    positivity
  by_cases hTN : T ≤ N
  · exact le_trans (hlarge N hN hTN)
      (mul_le_mul_of_nonneg_right (le_max_left Cevent Cinit) hscale_nonneg)
  · have hNT : N < T := Nat.lt_of_not_ge hTN
    exact le_trans (hinitial N hN hNT)
      (mul_le_mul_of_nonneg_right (le_max_right Cevent Cinit) hscale_nonneg)

/-- Global reduced-count bound from finite transfer on the large range and an
explicit finite-initial certificate.

This packages `Ered_bound_of_finite_transfer` into the all-`N` shape required by
`MainInputs.Ered_bound`: the analytic finite-transfer hypotheses are needed only
for `N ≥ T`; the remaining `3 ≤ N < T` range is represented by a separate
finite certificate/bound. -/
theorem Ered_bound_global_of_large_finite_transfer_and_initial
    {ι : Type*}
    (cls : ℕ → Finset ι)
    (Mb : ℕ → ι → ℝ)
    (Ered : ℕ → ℕ)
    (Pz μ ε : ℕ → ℝ)
    (c Cinit : ℝ) (T : ℕ)
    (hc : 0 < c) (hCinit : 0 < Cinit)
    (hEred_sum : ∀ N : ℕ, 3 ≤ N →
      (Ered N : ℝ) ≤ ∑ b ∈ cls N, Mb N b)
    (hPz : ∀ N : ℕ, 3 ≤ N → T ≤ N → 1 ≤ Pz N)
    (hcard : ∀ N : ℕ, 3 ≤ N → T ≤ N → ((cls N).card : ℝ) ≤ Pz N)
    (htransfer : ∀ N : ℕ, 3 ≤ N → T ≤ N → ∀ b ∈ cls N,
      Mb N b ≤ ((N : ℝ) / Pz N) * Real.exp (-(1 - ε N) * μ N))
    (hsaving : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      c * (Real.log N) ^ ((3 : ℝ) / 4) ≤ (1 - ε N) * μ N)
    (hinitial : ∀ N : ℕ, 3 ≤ N → N < T →
      (Ered N : ℝ) ≤ Cinit * ((N : ℝ) * saving c N)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      (Ered N : ℝ) ≤ C * ((N : ℝ) * saving c N) := by
  refine Ered_bound_global_of_large_and_initial Ered c 1 Cinit T hc
    zero_lt_one hCinit ?_ hinitial
  intro N hN hTN
  have hsum :
      (∑ b ∈ cls N, Mb N b) ≤ (N : ℝ) * saving c N :=
    Ered_bound_of_finite_transfer_of_one_le (cls N)
      (hPz N hN hTN) (by positivity) (hcard N hN hTN)
      (htransfer N hN hTN) (hsaving N hN hTN)
  calc (Ered N : ℝ)
      ≤ ∑ b ∈ cls N, Mb N b := hEred_sum N hN
    _ ≤ (N : ℝ) * saving c N := hsum
    _ = 1 * ((N : ℝ) * saving c N) := by ring

/-- `Ered_bound_global_of_large_finite_transfer_and_initial` with the modulus
lower bound in the stronger, paper-facing form `1 ≤ Pz N`.

This removes the otherwise redundant strict-positivity hypothesis from the
large-range reduced-count bridge. -/
theorem Ered_bound_global_of_large_finite_transfer_and_initial_of_one_le
    {ι : Type*}
    (cls : ℕ → Finset ι)
    (Mb : ℕ → ι → ℝ)
    (Ered : ℕ → ℕ)
    (Pz μ ε : ℕ → ℝ)
    (c Cinit : ℝ) (T : ℕ)
    (hc : 0 < c) (hCinit : 0 < Cinit)
    (hEred_sum : ∀ N : ℕ, 3 ≤ N →
      (Ered N : ℝ) ≤ ∑ b ∈ cls N, Mb N b)
    (hPz : ∀ N : ℕ, 3 ≤ N → T ≤ N → 1 ≤ Pz N)
    (hcard : ∀ N : ℕ, 3 ≤ N → T ≤ N → ((cls N).card : ℝ) ≤ Pz N)
    (htransfer : ∀ N : ℕ, 3 ≤ N → T ≤ N → ∀ b ∈ cls N,
      Mb N b ≤ ((N : ℝ) / Pz N) * Real.exp (-(1 - ε N) * μ N))
    (hsaving : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      c * (Real.log N) ^ ((3 : ℝ) / 4) ≤ (1 - ε N) * μ N)
    (hinitial : ∀ N : ℕ, 3 ≤ N → N < T →
      (Ered N : ℝ) ≤ Cinit * ((N : ℝ) * saving c N)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      (Ered N : ℝ) ≤ C * ((N : ℝ) * saving c N) :=
  Ered_bound_global_of_large_finite_transfer_and_initial cls Mb Ered Pz μ ε
    c Cinit T hc hCinit hEred_sum hPz hcard htransfer hsaving hinitial

/-! ## Part 4.  Rational certificate output → real analytic input.

The certificate layer (`EscLeanChecks`) naturally proves many finite-transfer
and reduced-exceptional bounds in `ℚ`, because alternating Bonferroni sums are
signed.  The analytic layer consumes real-valued estimates.  The following
lemmas isolate the cast bridge so those rational certificate outputs can feed
`Ered_bound` without being restated as opaque real hypotheses. -/

/-- A rational reduced-count certificate, together with real per-class transfer
bounds for the rational per-class budgets, implies the same real reduced-missed
bound as `reduced_missed_of_finite_transfer`.

This is the bridge for certificate-side statements of the form
`(E_red : ℚ) ≤ ∑_b M_b^cert`: after casting the finite sum to `ℝ`, the usual
uniform transfer summation applies. -/
theorem reduced_missed_of_finite_transfer_rat
    {ι : Type*} (cls : Finset ι)
    {Ered : ℕ} {MbQ : ι → ℚ} {N Pz μ ε : ℝ}
    (hEred : (Ered : ℚ) ≤ ∑ b ∈ cls, MbQ b)
    (hPz : 1 ≤ Pz) (hNpos : 0 ≤ N)
    (hcard : (cls.card : ℝ) ≤ Pz)
    (htransfer : ∀ b ∈ cls,
      (MbQ b : ℝ) ≤ (N / Pz) * Real.exp (-(1 - ε) * μ)) :
    (Ered : ℝ) ≤ N * Real.exp (-(1 - ε) * μ) := by
  have hEredReal :
      (Ered : ℝ) ≤ ∑ b ∈ cls, (MbQ b : ℝ) := by
    exact_mod_cast hEred
  exact le_trans hEredReal
    (reduced_missed_of_finite_transfer cls hPz hNpos hcard htransfer)

/-- Rational-certificate reduced-count bridge with `1 ≤ Pz` in place of a
separate strict-positivity side condition. -/
theorem reduced_missed_of_finite_transfer_rat_of_one_le
    {ι : Type*} (cls : Finset ι)
    {Ered : ℕ} {MbQ : ι → ℚ} {N Pz μ ε : ℝ}
    (hEred : (Ered : ℚ) ≤ ∑ b ∈ cls, MbQ b)
    (hPz : 1 ≤ Pz) (hNpos : 0 ≤ N)
    (hcard : (cls.card : ℝ) ≤ Pz)
    (htransfer : ∀ b ∈ cls,
      (MbQ b : ℝ) ≤ (N / Pz) * Real.exp (-(1 - ε) * μ)) :
    (Ered : ℝ) ≤ N * Real.exp (-(1 - ε) * μ) :=
  reduced_missed_of_finite_transfer_rat cls hEred
    hPz hNpos hcard htransfer

/-- Rational-certificate version of `Ered_bound_of_finite_transfer`.

The hypotheses mirror the strongest current capstone path except that the
finite/certificate side may supply rational budgets `MbQ`.  The conclusion is
the real `Ered ≤ N·saving` shape consumed by `MainInputs.Ered_bound`. -/
theorem Ered_bound_of_finite_transfer_rat
    {ι : Type*} (cls : Finset ι)
    {Ered : ℕ} {MbQ : ι → ℚ} {N Pz μ ε c₁ : ℝ} {Nnat : ℕ}
    (hEred : (Ered : ℚ) ≤ ∑ b ∈ cls, MbQ b)
    (hPz : 1 ≤ Pz) (hNpos : 0 ≤ N)
    (hcard : (cls.card : ℝ) ≤ Pz)
    (htransfer : ∀ b ∈ cls,
      (MbQ b : ℝ) ≤ (N / Pz) * Real.exp (-(1 - ε) * μ))
    (hsaving : c₁ * (Real.log Nnat) ^ ((3 : ℝ) / 4) ≤ (1 - ε) * μ) :
    (Ered : ℝ) ≤ N * saving c₁ Nnat := by
  have h1 : (Ered : ℝ) ≤ N * Real.exp (-(1 - ε) * μ) :=
    reduced_missed_of_finite_transfer_rat cls hEred hPz hNpos hcard htransfer
  have h2 : Real.exp (-(1 - ε) * μ) ≤ saving c₁ Nnat :=
    exp_neg_mu_le_saving hsaving
  exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hNpos)

/-- Rational-certificate `Ered` bridge with the natural lower bound
`1 ≤ Pz`. -/
theorem Ered_bound_of_finite_transfer_rat_of_one_le
    {ι : Type*} (cls : Finset ι)
    {Ered : ℕ} {MbQ : ι → ℚ} {N Pz μ ε c₁ : ℝ} {Nnat : ℕ}
    (hEred : (Ered : ℚ) ≤ ∑ b ∈ cls, MbQ b)
    (hPz : 1 ≤ Pz) (hNpos : 0 ≤ N)
    (hcard : (cls.card : ℝ) ≤ Pz)
    (htransfer : ∀ b ∈ cls,
      (MbQ b : ℝ) ≤ (N / Pz) * Real.exp (-(1 - ε) * μ))
    (hsaving : c₁ * (Real.log Nnat) ^ ((3 : ℝ) / 4) ≤ (1 - ε) * μ) :
    (Ered : ℝ) ≤ N * saving c₁ Nnat :=
  Ered_bound_of_finite_transfer_rat cls hEred
    hPz hNpos hcard htransfer hsaving

/-- Global reduced-count bound from rational finite-transfer data on the large
range and an explicit finite-initial certificate.

This is the rational-budget analogue of
`Ered_bound_global_of_large_finite_transfer_and_initial`: on `N ≥ T`, a
certificate-side rational bound `(Ered N : ℚ) ≤ ∑_b MbQ N b` and the real
finite-transfer estimates for `(MbQ N b : ℝ)` imply the reduced saving bound;
on `3 ≤ N < T`, the caller supplies a finite certificate/bound. -/
theorem Ered_bound_global_of_large_finite_transfer_rat_and_initial
    {ι : Type*}
    (cls : ℕ → Finset ι)
    (MbQ : ℕ → ι → ℚ)
    (Ered : ℕ → ℕ)
    (Pz μ ε : ℕ → ℝ)
    (c Cinit : ℝ) (T : ℕ)
    (hc : 0 < c) (hCinit : 0 < Cinit)
    (hEred_rat : ∀ N : ℕ, 3 ≤ N →
      (Ered N : ℚ) ≤ ∑ b ∈ cls N, MbQ N b)
    (hPz : ∀ N : ℕ, 3 ≤ N → T ≤ N → 1 ≤ Pz N)
    (hcard : ∀ N : ℕ, 3 ≤ N → T ≤ N → ((cls N).card : ℝ) ≤ Pz N)
    (htransfer : ∀ N : ℕ, 3 ≤ N → T ≤ N → ∀ b ∈ cls N,
      (MbQ N b : ℝ) ≤ ((N : ℝ) / Pz N) * Real.exp (-(1 - ε N) * μ N))
    (hsaving : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      c * (Real.log N) ^ ((3 : ℝ) / 4) ≤ (1 - ε N) * μ N)
    (hinitial : ∀ N : ℕ, 3 ≤ N → N < T →
      (Ered N : ℝ) ≤ Cinit * ((N : ℝ) * saving c N)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      (Ered N : ℝ) ≤ C * ((N : ℝ) * saving c N) := by
  refine Ered_bound_global_of_large_and_initial Ered c 1 Cinit T hc
    zero_lt_one hCinit ?_ hinitial
  intro N hN hTN
  have hbound :
      (Ered N : ℝ) ≤ (N : ℝ) * saving c N :=
    Ered_bound_of_finite_transfer_rat_of_one_le (cls N)
      (hEred_rat N hN) (hPz N hN hTN) (by positivity) (hcard N hN hTN)
      (htransfer N hN hTN) (hsaving N hN hTN)
  calc (Ered N : ℝ)
      ≤ (N : ℝ) * saving c N := hbound
    _ = 1 * ((N : ℝ) * saving c N) := by ring

/-- Rational-budget global reduced-count bridge with `1 ≤ Pz N` instead of a
separate strict-positivity hypothesis. -/
theorem Ered_bound_global_of_large_finite_transfer_rat_and_initial_of_one_le
    {ι : Type*}
    (cls : ℕ → Finset ι)
    (MbQ : ℕ → ι → ℚ)
    (Ered : ℕ → ℕ)
    (Pz μ ε : ℕ → ℝ)
    (c Cinit : ℝ) (T : ℕ)
    (hc : 0 < c) (hCinit : 0 < Cinit)
    (hEred_rat : ∀ N : ℕ, 3 ≤ N →
      (Ered N : ℚ) ≤ ∑ b ∈ cls N, MbQ N b)
    (hPz : ∀ N : ℕ, 3 ≤ N → T ≤ N → 1 ≤ Pz N)
    (hcard : ∀ N : ℕ, 3 ≤ N → T ≤ N → ((cls N).card : ℝ) ≤ Pz N)
    (htransfer : ∀ N : ℕ, 3 ≤ N → T ≤ N → ∀ b ∈ cls N,
      (MbQ N b : ℝ) ≤ ((N : ℝ) / Pz N) * Real.exp (-(1 - ε N) * μ N))
    (hsaving : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      c * (Real.log N) ^ ((3 : ℝ) / 4) ≤ (1 - ε N) * μ N)
    (hinitial : ∀ N : ℕ, 3 ≤ N → N < T →
      (Ered N : ℝ) ≤ Cinit * ((N : ℝ) * saving c N)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      (Ered N : ℝ) ≤ C * ((N : ℝ) * saving c N) :=
  Ered_bound_global_of_large_finite_transfer_rat_and_initial cls MbQ Ered
    Pz μ ε c Cinit T hc hCinit hEred_rat hPz hcard htransfer hsaving hinitial

/-- Global reduced-count bound from rational finite-transfer data available only
on the large range, plus an explicit finite-initial certificate.

This is the same rational-certificate bridge as
`Ered_bound_global_of_large_finite_transfer_rat_and_initial`, but it does not
ask the caller to provide the rational reduced-count certificate below the
threshold `T`, where the finite-initial bound is used instead. -/
theorem Ered_bound_global_of_large_finite_transfer_rat_on_range_and_initial
    {ι : Type*}
    (cls : ℕ → Finset ι)
    (MbQ : ℕ → ι → ℚ)
    (Ered : ℕ → ℕ)
    (Pz μ ε : ℕ → ℝ)
    (c Cinit : ℝ) (T : ℕ)
    (hc : 0 < c) (hCinit : 0 < Cinit)
    (hEred_rat : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      (Ered N : ℚ) ≤ ∑ b ∈ cls N, MbQ N b)
    (hPz : ∀ N : ℕ, 3 ≤ N → T ≤ N → 1 ≤ Pz N)
    (hcard : ∀ N : ℕ, 3 ≤ N → T ≤ N → ((cls N).card : ℝ) ≤ Pz N)
    (htransfer : ∀ N : ℕ, 3 ≤ N → T ≤ N → ∀ b ∈ cls N,
      (MbQ N b : ℝ) ≤ ((N : ℝ) / Pz N) * Real.exp (-(1 - ε N) * μ N))
    (hsaving : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      c * (Real.log N) ^ ((3 : ℝ) / 4) ≤ (1 - ε N) * μ N)
    (hinitial : ∀ N : ℕ, 3 ≤ N → N < T →
      (Ered N : ℝ) ≤ Cinit * ((N : ℝ) * saving c N)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      (Ered N : ℝ) ≤ C * ((N : ℝ) * saving c N) := by
  refine Ered_bound_global_of_large_and_initial Ered c 1 Cinit T hc
    zero_lt_one hCinit ?_ hinitial
  intro N hN hTN
  have hbound :
      (Ered N : ℝ) ≤ (N : ℝ) * saving c N :=
    Ered_bound_of_finite_transfer_rat_of_one_le (cls N)
      (hEred_rat N hN hTN) (hPz N hN hTN) (by positivity) (hcard N hN hTN)
      (htransfer N hN hTN) (hsaving N hN hTN)
  calc (Ered N : ℝ)
      ≤ (N : ℝ) * saving c N := hbound
    _ = 1 * ((N : ℝ) * saving c N) := by ring

/-- On-range rational-budget global reduced-count bridge with `1 ≤ Pz N`
instead of a separate strict-positivity hypothesis. -/
theorem Ered_bound_global_of_large_finite_transfer_rat_on_range_and_initial_of_one_le
    {ι : Type*}
    (cls : ℕ → Finset ι)
    (MbQ : ℕ → ι → ℚ)
    (Ered : ℕ → ℕ)
    (Pz μ ε : ℕ → ℝ)
    (c Cinit : ℝ) (T : ℕ)
    (hc : 0 < c) (hCinit : 0 < Cinit)
    (hEred_rat : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      (Ered N : ℚ) ≤ ∑ b ∈ cls N, MbQ N b)
    (hPz : ∀ N : ℕ, 3 ≤ N → T ≤ N → 1 ≤ Pz N)
    (hcard : ∀ N : ℕ, 3 ≤ N → T ≤ N → ((cls N).card : ℝ) ≤ Pz N)
    (htransfer : ∀ N : ℕ, 3 ≤ N → T ≤ N → ∀ b ∈ cls N,
      (MbQ N b : ℝ) ≤ ((N : ℝ) / Pz N) * Real.exp (-(1 - ε N) * μ N))
    (hsaving : ∀ N : ℕ, 3 ≤ N → T ≤ N →
      c * (Real.log N) ^ ((3 : ℝ) / 4) ≤ (1 - ε N) * μ N)
    (hinitial : ∀ N : ℕ, 3 ≤ N → N < T →
      (Ered N : ℝ) ≤ Cinit * ((N : ℝ) * saving c N)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      (Ered N : ℝ) ≤ C * ((N : ℝ) * saving c N) :=
  Ered_bound_global_of_large_finite_transfer_rat_on_range_and_initial cls MbQ
    Ered Pz μ ε c Cinit T hc hCinit hEred_rat hPz hcard htransfer hsaving
    hinitial

end EscAnalytic
