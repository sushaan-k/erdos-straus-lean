import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import EscAnalytic.Core

/-!
# Parameter optimization

This module proves the parameter optimization used in the final transfer.  The
manuscript chooses `X` by
`log X = α (log N)^{1/4}`, with `α > 0` fixed and small.  The cubic mass law then
gives
```
  μ_b ≍_α (log N)^{3/4}.
```
It then verifies the finite-level condition
```
  P(z) X^{2R_b} exp{2 μ_b} ≤ N exp{-4 μ_b}
```
for `α` sufficiently small, using:

* the prime-product estimate `log P(z) ≤ 2z`, exposed as the hypothesis
  `mertens : Real.log Pz ≤ 2 * z`; and
* the level-budget algebra `2 R_b log X + 6 μ_b ≤ C_K μ_b log X ≤ C'_K α^4 log N`
  for the chosen scale.

## Main deductions

1. `logX_cube_eq` / `mu_asymp_N`: the **power algebra** `(log X)^3 = α^3 (log N)^{3/4}`
   and the resulting two-sided `μ ≍ (log N)^{3/4}` with explicit constants
   `α^3 c₁, α^3 c₂` (Goal 1). Pure `Real.rpow` / `Real.log` algebra.
2. `finite_level_condition_of_*`: the **level-condition algebra** (Goal 2). The
   condition `P(z) X^{2R} e^{2μ} ≤ N e^{-4μ}` is equivalent, after taking
   logarithms, to `log P(z) + 2R log X + 6μ ≤ log N`; we prove this from the
   Mertens bound and the level-budget bound, and combine the two into the
   exponential-form condition, using concrete inequalities over `ℝ`.

The prime-product estimate, cubic mass law, and level budget enter through
explicit hypotheses; the deductions from them are proved in this module.
-/

namespace EscAnalytic

open scoped BigOperators

/-! ## Goal 1 — the mass-law transfer `μ ≍ (log X)^3 ⟹ μ ≍ (log N)^{3/4}`.

The scale choice is `log X = α (log N)^{1/4}` (`eq:X-choice`).  We work with the
two logarithms `LX = log X` and `LN = log N` as nonnegative reals (the regime is
`N, X → ∞`), and `α > 0` fixed. -/

/-- **Power algebra of the scale choice** (tex 2018–2024).

If `LX = α · LN^{1/4}` (with `LN ≥ 0`), then `LX^3 = α^3 · LN^{3/4}`.

This is the algebraic heart of `eq:mu-asymp-N`: cubing the scale choice turns
`(log X)^3` into `α^3 (log N)^{3/4}`. -/
theorem logX_cube_eq {α LX LN : ℝ} (hLN : 0 ≤ LN)
    (hscale : LX = α * LN ^ ((1 : ℝ) / 4)) :
    LX ^ 3 = α ^ 3 * LN ^ ((3 : ℝ) / 4) := by
  subst hscale
  rw [mul_pow]
  congr 1
  -- `(LN^{1/4})^3 = LN^{(1/4)·3} = LN^{3/4}`
  rw [← Real.rpow_natCast (LN ^ ((1 : ℝ) / 4)) 3, ← Real.rpow_mul hLN]
  norm_num

/-- **Mass-law transfer, lower half** (`eq:mu-asymp-N`, tex 2022–2024).

Given the scale choice `LX = α LN^{1/4}` and the saturated mass law's lower bound
`c₁ · LX^3 ≤ μ` (`μ_b ≍ (log X)^3`, tex 2016), we get
`(α^3 c₁) · LN^{3/4} ≤ μ`. -/
theorem mu_lower_N {α LX LN μ c₁ : ℝ} (hLN : 0 ≤ LN)
    (hscale : LX = α * LN ^ ((1 : ℝ) / 4))
    (hμ : c₁ * LX ^ 3 ≤ μ) :
    (α ^ 3 * c₁) * LN ^ ((3 : ℝ) / 4) ≤ μ := by
  have h := logX_cube_eq hLN hscale
  calc (α ^ 3 * c₁) * LN ^ ((3 : ℝ) / 4)
      = c₁ * (α ^ 3 * LN ^ ((3 : ℝ) / 4)) := by ring
    _ = c₁ * LX ^ 3 := by rw [h]
    _ ≤ μ := hμ

/-- **Mass-law transfer, upper half** (`eq:mu-asymp-N`, tex 2022–2024).

Given the scale choice and the upper bound `μ ≤ c₂ · LX^3`, we get
`μ ≤ (α^3 c₂) · LN^{3/4}`. -/
theorem mu_upper_N {α LX LN μ c₂ : ℝ} (hLN : 0 ≤ LN)
    (hscale : LX = α * LN ^ ((1 : ℝ) / 4))
    (hμ : μ ≤ c₂ * LX ^ 3) :
    μ ≤ (α ^ 3 * c₂) * LN ^ ((3 : ℝ) / 4) := by
  have h := logX_cube_eq hLN hscale
  calc μ ≤ c₂ * LX ^ 3 := hμ
    _ = c₂ * (α ^ 3 * LN ^ ((3 : ℝ) / 4)) := by rw [h]
    _ = (α ^ 3 * c₂) * LN ^ ((3 : ℝ) / 4) := by ring

/-- **Mass-law transfer** (`eq:mu-asymp-N`, tex 2022–2024), two-sided form.

From the scale choice `log X = α (log N)^{1/4}` and the saturated mass law
`c₁ (log X)^3 ≤ μ ≤ c₂ (log X)^3`, conclude `μ ≍ (log N)^{3/4}` with the explicit
constants `α^3 c₁` and `α^3 c₂`:
```
  (α^3 c₁) (log N)^{3/4} ≤ μ ≤ (α^3 c₂) (log N)^{3/4}.
```
This is `eq:mu-asymp-N`. -/
theorem mu_asymp_N {α LX LN μ c₁ c₂ : ℝ} (hLN : 0 ≤ LN)
    (hscale : LX = α * LN ^ ((1 : ℝ) / 4))
    (hlo : c₁ * LX ^ 3 ≤ μ) (hhi : μ ≤ c₂ * LX ^ 3) :
    (α ^ 3 * c₁) * LN ^ ((3 : ℝ) / 4) ≤ μ ∧
      μ ≤ (α ^ 3 * c₂) * LN ^ ((3 : ℝ) / 4) :=
  ⟨mu_lower_N hLN hscale hlo, mu_upper_N hLN hscale hhi⟩

/-- Positivity of the transferred lower constant `α^3 c₁` when `α, c₁ > 0`
(needed to keep `≍` two-sided with strictly positive constants). -/
theorem transfer_const_pos {α c : ℝ} (hα : 0 < α) (hc : 0 < c) :
    0 < α ^ 3 * c :=
  mul_pos (pow_pos hα 3) hc

/-! ## Goal 2 — the finite-level condition algebra (tex 2026–2034).

`eq:finite-level-condition` (tex 1966–1968) reads
```
  P(z) · X^{2R} · exp{2 μ} ≤ N · exp{-4 μ}.
```
We work with the logarithms `LX = log X`, `LN = log N`, the sieve threshold
`z = (log X)^4 = LX^4`, and `Pz = P(z)` (so `log P(z) = log Pz`).

Taking logarithms (everything positive) turns `eq:finite-level-condition` into
the **additive level inequality**
```
  log P(z) + 2R · log X + 6 μ ≤ log N,        (★)
```
since `log(P(z) X^{2R} e^{2μ}) = log P(z) + 2R log X + 2μ` and
`log(N e^{-4μ}) = log N - 4μ`.

The manuscript supplies two cited/derived bounds (tex 2026–2032):
* Mertens: `log P(z) ≤ 2 z = 2 LX^4` and `LX^4 = α^4 LN` (since `LX = α LN^{1/4}`),
  hence `log P(z) ≤ 2 α^4 LN`;
* level budget: `2 R log X + 6 μ ≤ C'_K · α^4 · LN`.

Adding gives `log P(z) + 2R log X + 6μ ≤ (2 + C'_K) α^4 LN ≤ LN` whenever
`α` is small enough that `(2 + C'_K) α^4 ≤ 1`.  This is exactly "choosing `α`
sufficiently small makes `eq:finite-level-condition` valid". -/

/-- `z = (log X)^4 = α^4 log N` under the scale choice `log X = α (log N)^{1/4}`
(tex 2026: "`z = (log X)^4`").  Here `z` is the sieve threshold `zScale X`. -/
theorem z_eq_alpha4_LN {α LN : ℝ} (hLN : 0 ≤ LN)
    {X : ℝ} (hscale : Real.log X = α * LN ^ ((1 : ℝ) / 4)) :
    zScale X = α ^ 4 * LN := by
  unfold zScale
  rw [hscale, mul_pow]
  congr 1
  rw [← Real.rpow_natCast (LN ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul hLN]
  norm_num

/-- **Mertens bound transferred to `α^4 log N`** (tex 2026–2028).

Given the cited Mertens bound `log P(z) ≤ 2 z` (with `z = zScale X`) and the
scale choice `log X = α (log N)^{1/4}`, we get `log P(z) ≤ 2 α^4 log N`. -/
theorem logPz_le_alpha4_LN {α LN Pz : ℝ} (hLN : 0 ≤ LN)
    {X : ℝ} (hscale : Real.log X = α * LN ^ ((1 : ℝ) / 4))
    (mertens : Real.log Pz ≤ 2 * zScale X) :
    Real.log Pz ≤ 2 * (α ^ 4 * LN) := by
  rw [z_eq_alpha4_LN hLN hscale] at mertens
  exact mertens

/-- **Additive level inequality (★)** (the log of `eq:finite-level-condition`).

If `log P(z) ≤ 2 α^4 LN` (Mertens) and `2R log X + 6μ ≤ C' α^4 LN` (level budget),
and `α` is small enough that `(2 + C') α^4 ≤ 1`, then
```
  log P(z) + (2 R log X + 6 μ) ≤ log N = LN.
```
The hypothesis `LN ≥ 0` (i.e. `N ≥ 1`) is what makes the final step `≤ LN` go
through: all the slack is collected into the single factor `(2 + C') α^4 ≤ 1`. -/
theorem additive_level_le {α LN logPz levelBudget Cp : ℝ} (hLN : 0 ≤ LN)
    (hmert : logPz ≤ 2 * (α ^ 4 * LN))
    (hbudget : levelBudget ≤ Cp * (α ^ 4 * LN))
    (hα_small : (2 + Cp) * α ^ 4 ≤ 1) :
    logPz + levelBudget ≤ LN := by
  calc logPz + levelBudget
      ≤ 2 * (α ^ 4 * LN) + Cp * (α ^ 4 * LN) := by
        exact add_le_add hmert hbudget
    _ = ((2 + Cp) * α ^ 4) * LN := by ring
    _ ≤ 1 * LN := by
        exact mul_le_mul_of_nonneg_right hα_small hLN
    _ = LN := one_mul LN

/-- **Logarithmic form of the finite-level condition** (tex 1966–1968, 2026–2034).

`eq:finite-level-condition` `P(z) X^{2R} e^{2μ} ≤ N e^{-4μ}` is *equivalent* to its
logarithm. Here we state and prove the convenient one-directional packaging used in
the manuscript: if
```
  log P(z) + 2 R log X + 6 μ ≤ log N
```
then the finite-level condition holds, provided `P(z), X^{2R}, N > 0`.

We pass through `log P(z) = log Pz`, `log(X^{2R}) = 2R · log X`, and the
`exp`/`log` adjoint. -/
theorem finite_level_condition_of_log
    {Pz N μ R LX : ℝ} {Xpow : ℝ}
    (hPz : 0 < Pz) (hXpow : 0 < Xpow) (hN : 0 < N)
    (hXpow_log : Real.log Xpow = 2 * R * LX)
    (hlog : Real.log Pz + (2 * R * LX + 6 * μ) ≤ Real.log N) :
    Pz * Xpow * Real.exp (2 * μ) ≤ N * Real.exp (-4 * μ) := by
  -- Take logarithms of both sides; both are positive so `Real.log` is monotone
  -- and an inequality of logs upgrades to an inequality of the values.
  have hLHS : (0 : ℝ) < Pz * Xpow * Real.exp (2 * μ) :=
    mul_pos (mul_pos hPz hXpow) (Real.exp_pos _)
  have hRHS : (0 : ℝ) < N * Real.exp (-4 * μ) :=
    mul_pos hN (Real.exp_pos _)
  rw [← Real.log_le_log_iff hLHS hRHS]
  -- Expand both logs.
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
      Real.log_mul (ne_of_gt hPz) (ne_of_gt hXpow),
      Real.log_mul (ne_of_gt hN) (Real.exp_ne_zero _),
      Real.log_exp, Real.log_exp, hXpow_log]
  -- Goal: log Pz + 2R LX + 2μ ≤ log N + (-4 μ).  Equivalent to (★).
  linarith [hlog]

/-- **Finite-level condition, fully assembled** (tex 1966–1968, 2026–2034).

This is the main payload of Goal 2: under the scale choice
`log X = α (log N)^{1/4}`, with
* Mertens `log P(z) ≤ 2 z`  (cited input),
* `log(X^{2R}) = 2R log X` (the defining identity of the power `X^{2R}`),
* the level budget `2R log X + 6μ ≤ C' α^4 log N` (tex 2030–2032), and
* `α` small enough that `(2 + C') α^4 ≤ 1`,

the finite-level condition
```
  P(z) · X^{2R} · exp{2μ} ≤ N · exp{-4μ}
```
holds (positivity of `P(z), X^{2R}, N` assumed).  Concretely `LN = log N`. -/
theorem finite_level_condition_of_optimization
    {α R μ Pz N LN : ℝ} {X Xpow : ℝ}
    (hLN : 0 ≤ LN) (hLNeq : LN = Real.log N)
    (hPz : 0 < Pz) (hXpow : 0 < Xpow) (hN : 0 < N)
    (hscale : Real.log X = α * LN ^ ((1 : ℝ) / 4))
    (hXpow_log : Real.log Xpow = 2 * R * Real.log X)
    (mertens : Real.log Pz ≤ 2 * zScale X)
    (hbudget : 2 * R * Real.log X + 6 * μ ≤ Cp * (α ^ 4 * LN))
    (hα_small : (2 + Cp) * α ^ 4 ≤ 1) :
    Pz * Xpow * Real.exp (2 * μ) ≤ N * Real.exp (-4 * μ) := by
  -- Step 1: Mertens transferred.
  have hmert : Real.log Pz ≤ 2 * (α ^ 4 * LN) :=
    logPz_le_alpha4_LN hLN hscale mertens
  -- Step 2: additive level inequality (★).
  have hadd : Real.log Pz + (2 * R * Real.log X + 6 * μ) ≤ LN :=
    additive_level_le hLN hmert hbudget hα_small
  -- Step 3: upgrade to the exponential form.
  rw [hLNeq] at hadd
  exact finite_level_condition_of_log hPz hXpow hN hXpow_log hadd

/-- Version of `finite_level_condition_of_optimization` with the natural
paper-facing lower bound `1 ≤ Pz`; strict positivity for the logarithm is
derived internally. -/
theorem finite_level_condition_of_optimization_of_one_le
    {α R μ Pz N LN : ℝ} {X Xpow : ℝ}
    (hLN : 0 ≤ LN) (hLNeq : LN = Real.log N)
    (hPz : 1 ≤ Pz) (hXpow : 0 < Xpow) (hN : 0 < N)
    (hscale : Real.log X = α * LN ^ ((1 : ℝ) / 4))
    (hXpow_log : Real.log Xpow = 2 * R * Real.log X)
    (mertens : Real.log Pz ≤ 2 * zScale X)
    (hbudget : 2 * R * Real.log X + 6 * μ ≤ Cp * (α ^ 4 * LN))
    (hα_small : (2 + Cp) * α ^ 4 ≤ 1) :
    Pz * Xpow * Real.exp (2 * μ) ≤ N * Real.exp (-4 * μ) :=
  finite_level_condition_of_optimization
    (hLN := hLN) (hLNeq := hLNeq)
    (hPz := lt_of_lt_of_le zero_lt_one hPz) (hXpow := hXpow) (hN := hN)
    (hscale := hscale) (hXpow_log := hXpow_log) (mertens := mertens)
    (hbudget := hbudget) (hα_small := hα_small)

/-- Concrete-power version of `finite_level_condition_of_optimization`.

This is the same finite-level condition with the auxiliary variable `LN` fixed to
`log N` and the auxiliary power `Xpow` fixed to the actual real power
`X ^ (2R)`.  Thus callers only supply the manuscript-scale assumptions
`1 ≤ N`, `0 < X`, the scale choice, Mertens, the level budget, and the smallness
condition on `α`. -/
theorem finite_level_condition_of_optimization_rpow
    {α R μ Pz N : ℝ} {X : ℝ}
    (hNge : 1 ≤ N) (hPz : 0 < Pz) (hX : 0 < X)
    (hscale : Real.log X = α * (Real.log N) ^ ((1 : ℝ) / 4))
    (mertens : Real.log Pz ≤ 2 * zScale X)
    (hbudget :
      2 * R * Real.log X + 6 * μ ≤ Cp * (α ^ 4 * Real.log N))
    (hα_small : (2 + Cp) * α ^ 4 ≤ 1) :
    Pz * (X ^ (2 * R)) * Real.exp (2 * μ)
        ≤ N * Real.exp (-4 * μ) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hNge
  have hLN : 0 ≤ Real.log N := Real.log_nonneg hNge
  have hXpow : 0 < X ^ (2 * R) := Real.rpow_pos_of_pos hX _
  have hXpow_log : Real.log (X ^ (2 * R)) = 2 * R * Real.log X := by
    rw [Real.log_rpow hX]
  exact finite_level_condition_of_optimization
    (hLN := hLN) (hLNeq := rfl) (hPz := hPz) (hXpow := hXpow)
    (hN := hNpos) (hscale := hscale) (hXpow_log := hXpow_log)
    (mertens := mertens) (hbudget := hbudget) (hα_small := hα_small)

/-- Concrete-power version with the paper-facing lower bound `1 ≤ Pz`.

The strict positivity needed by the logarithmic exponential comparison is
derived internally from the natural sieve-size lower bound. -/
theorem finite_level_condition_of_optimization_rpow_of_one_le
    {α R μ Pz N : ℝ} {X : ℝ}
    (hNge : 1 ≤ N) (hPz : 1 ≤ Pz) (hX : 0 < X)
    (hscale : Real.log X = α * (Real.log N) ^ ((1 : ℝ) / 4))
    (mertens : Real.log Pz ≤ 2 * zScale X)
    (hbudget :
      2 * R * Real.log X + 6 * μ ≤ Cp * (α ^ 4 * Real.log N))
    (hα_small : (2 + Cp) * α ^ 4 ≤ 1) :
    Pz * (X ^ (2 * R)) * Real.exp (2 * μ)
        ≤ N * Real.exp (-4 * μ) :=
  finite_level_condition_of_optimization_rpow
    (hNge := hNge) (hPz := lt_of_lt_of_le zero_lt_one hPz) (hX := hX)
    (hscale := hscale) (mertens := mertens)
    (hbudget := hbudget) (hα_small := hα_small)

/-- Natural-parameter version of `finite_level_condition_of_optimization_rpow`.

This is the form closest to the later assembly layer, where the level parameter
is a natural number with `3 ≤ N`.  The real positivity/log-nonnegativity
obligations are derived from that single natural lower bound. -/
theorem finite_level_condition_of_optimization_nat
    {α R μ Pz : ℝ} {X : ℝ} {N : ℕ}
    (hN : 3 ≤ N) (hPz : 0 < Pz) (hX : 0 < X)
    (hscale : Real.log X = α * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))
    (mertens : Real.log Pz ≤ 2 * zScale X)
    (hbudget :
      2 * R * Real.log X + 6 * μ ≤ Cp * (α ^ 4 * Real.log (N : ℝ)))
    (hα_small : (2 + Cp) * α ^ 4 ≤ 1) :
    Pz * (X ^ (2 * R)) * Real.exp (2 * μ)
        ≤ (N : ℝ) * Real.exp (-4 * μ) := by
  have hNge_real : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ N)
  exact finite_level_condition_of_optimization_rpow
    (hNge := hNge_real) (hPz := hPz) (hX := hX)
    (hscale := hscale) (mertens := mertens)
    (hbudget := hbudget) (hα_small := hα_small)

/-- Natural-parameter version with the paper-facing lower bound `1 ≤ Pz`.

This is the public optimization bridge used by the assembly layer: the natural
lower bound on `N` and the sieve-size lower bound on `Pz` discharge the
positivity/log side conditions of the lower-level optimization lemma. -/
theorem finite_level_condition_of_optimization_nat_of_one_le
    {α R μ Pz : ℝ} {X : ℝ} {N : ℕ}
    (hN : 3 ≤ N) (hPz : 1 ≤ Pz) (hX : 0 < X)
    (hscale : Real.log X = α * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))
    (mertens : Real.log Pz ≤ 2 * zScale X)
    (hbudget :
      2 * R * Real.log X + 6 * μ ≤ Cp * (α ^ 4 * Real.log (N : ℝ)))
    (hα_small : (2 + Cp) * α ^ 4 ≤ 1) :
    Pz * (X ^ (2 * R)) * Real.exp (2 * μ)
        ≤ (N : ℝ) * Real.exp (-4 * μ) := by
  have hNge_real : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ N)
  exact finite_level_condition_of_optimization_rpow_of_one_le
    (hNge := hNge_real) (hPz := hPz) (hX := hX)
    (hscale := hscale) (mertens := mertens)
    (hbudget := hbudget) (hα_small := hα_small)

end EscAnalytic
