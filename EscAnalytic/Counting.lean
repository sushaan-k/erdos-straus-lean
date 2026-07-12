import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Tactic
import EscLeanChecks

/-!
# ESC analytic layer — counting functions and the main-bound predicate

Shared vocabulary for the exceptional-set counting function `E(N)` (manuscript
tex line 128) and the exponential saving `exp(-c (log N)^{3/4})`, so that
`thm:main` and its applications are stated against one definition.
-/

namespace EscAnalytic

open scoped BigOperators
open Classical

/-- `E(N)` = number of exceptional `n` with `2 ≤ n ≤ N`, i.e. those `n` for which
`4/n` has no representation as a sum of three unit fractions
(`EscLeanChecks.esExceptional`). Manuscript tex 128. -/
noncomputable def exceptionalCount (N : ℕ) : ℕ :=
  ((Finset.Icc 2 N).filter (fun n => EscLeanChecks.esExceptional n)).card

/-- Trivial finite carrier bound for the exceptional count. -/
theorem exceptionalCount_le_self (N : ℕ) : exceptionalCount N ≤ N := by
  classical
  unfold exceptionalCount
  calc
    ((Finset.Icc (2 : ℕ) N).filter (fun n => EscLeanChecks.esExceptional n)).card
        ≤ (Finset.Icc (2 : ℕ) N).card :=
          Finset.card_filter_le _ _
    _ ≤ N := by
      rw [Nat.card_Icc]
      omega

/-- The exceptional set restricted to primes (`𝒫_exc(N)`, tex 2094-2096). -/
noncomputable def primeExceptionalCount (N : ℕ) : ℕ :=
  ((Finset.Icc 2 N).filter (fun n => n.Prime ∧ EscLeanChecks.esExceptional n)).card

/-- The exponential saving `exp(-c · (log N)^{3/4})` of the main theorem. -/
noncomputable def saving (c : ℝ) (N : ℕ) : ℝ :=
  Real.exp (-c * (Real.log N) ^ ((3 : ℝ) / 4))

/-! ## Shared real-analysis helpers for saving absorption -/

/-- A crude but uniform quadratic lower bound on `exp`: `t² ≤ 4 · exp t` for all
`t ≥ 0`. -/
theorem sq_le_four_mul_exp {t : ℝ} (ht : 0 ≤ t) : t ^ 2 ≤ 4 * Real.exp t := by
  have h1 : t / 2 ≤ Real.exp (t / 2) := by
    have := Real.add_one_le_exp (t / 2)
    linarith
  have hpos : (0 : ℝ) ≤ t / 2 := by linarith
  have hexp : (t / 2) ^ 2 ≤ (Real.exp (t / 2)) ^ 2 := by
    apply pow_le_pow_left₀ hpos h1
  have hsplit : Real.exp t = (Real.exp (t / 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    ring_nf
  rw [hsplit]
  nlinarith [hexp]

/-- `t^{4/3} ≤ 1 + t²` for all `t ≥ 0`. -/
theorem rpow_four_thirds_le {t : ℝ} (ht : 0 ≤ t) :
    t ^ ((4 : ℝ) / 3) ≤ 1 + t ^ 2 := by
  rcases le_or_lt t 1 with h | h
  · calc t ^ ((4 : ℝ) / 3) ≤ 1 ^ ((4 : ℝ) / 3) :=
            Real.rpow_le_rpow ht h (by norm_num)
      _ = 1 := by simp
      _ ≤ 1 + t ^ 2 := by nlinarith
  · have h1 : t ^ ((4 : ℝ) / 3) ≤ t ^ ((2 : ℝ)) :=
      (Real.rpow_le_rpow_left_iff h).mpr (by norm_num)
    calc t ^ ((4 : ℝ) / 3) ≤ t ^ ((2 : ℝ)) := h1
      _ = t ^ 2 := Real.rpow_two t
      _ ≤ 1 + t ^ 2 := by nlinarith

/-- `(L^{3/4})^{4/3} = L` for `L ≥ 0`. -/
theorem rpow_three_quarters_four_thirds {L : ℝ} (hL : 0 ≤ L) :
    (L ^ ((3 : ℝ) / 4)) ^ ((4 : ℝ) / 3) = L := by
  rw [← Real.rpow_mul hL]
  norm_num

/-- `log N ≥ 2/3` for `N ≥ 3`. -/
theorem log_ge_of_three_le {N : ℕ} (hN : 3 ≤ N) : (2 : ℝ) / 3 ≤ Real.log N := by
  have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hmono : Real.log 3 ≤ Real.log N := Real.log_le_log (by norm_num) h3
  have h3' : (2 : ℝ) / 3 ≤ Real.log 3 := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 by norm_num)
    norm_num at this ⊢
    linarith
  linarith

/-- `log N > 0` for `N ≥ 3`. -/
theorem log_pos_of_three_le {N : ℕ} (hN : 3 ≤ N) : 0 < Real.log N := by
  have := log_ge_of_three_le hN
  linarith

/-- Lean form of `f(N) ≪ N · exp(-c(log N)^{3/4})`: there are absolute
constants `c, C > 0` with `f N ≤ C · N · saving c N` for all `N ≥ 3`. -/
def IsMainBound (f : ℕ → ℕ) : Prop :=
  ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N : ℕ, 3 ≤ N → (f N : ℝ) ≤ C * N * saving c N

/-- The exponential saving in the main theorem tends to zero. -/
theorem saving_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun N : ℕ => saving c N) Filter.atTop (nhds 0) := by
  change
    Filter.Tendsto
      (fun N : ℕ => Real.exp (-c * (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4)))
      Filter.atTop (nhds 0)
  have hlog :
      Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp :
      Filter.Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4))
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (3 : ℝ) / 4)).comp hlog
  have hmul :
      Filter.Tendsto (fun N : ℕ => c * (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4))
        Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hc hp
  have hneg :
      Filter.Tendsto (fun N : ℕ => -(c * (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4)))
        Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atTop_atBot.comp hmul
  convert Real.tendsto_exp_atBot.comp hneg using 1
  ext N
  simp [Function.comp, neg_mul]

/-- Any main-bound estimate implies density zero for the counted set. -/
theorem IsMainBound.density_tendsto_zero {f : ℕ → ℕ} (h : IsMainBound f) :
    Filter.Tendsto (fun N : ℕ => (f N : ℝ) / (N : ℝ)) Filter.atTop (nhds 0) := by
  obtain ⟨c, hc, C, _hC, hmain⟩ := h
  refine squeeze_zero_norm' (a := fun N : ℕ => C * saving c N) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 3] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hdiv :
        (f N : ℝ) / (N : ℝ) ≤ C * saving c N := by
      have hmainN := hmain N hN
      rw [div_le_iff₀ hNpos]
      calc (f N : ℝ)
          ≤ C * N * saving c N := hmainN
        _ = (C * saving c N) * (N : ℝ) := by ring
    rw [Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) hNpos.le)]
    exact hdiv
  · simpa using (saving_tendsto_zero hc).const_mul C

/-- Monotone comparison: if `f ≤ g` pointwise and `g` satisfies the main bound,
so does `f`. (Used to pass from all denominators to prime denominators.) -/
theorem IsMainBound.of_le {f g : ℕ → ℕ} (hfg : ∀ N, f N ≤ g N)
    (hg : IsMainBound g) : IsMainBound f := by
  obtain ⟨c, hc, C, hC, h⟩ := hg
  refine ⟨c, hc, C, hC, fun N hN => ?_⟩
  exact le_trans (by exact_mod_cast hfg N) (h N hN)

/-- `primeExceptionalCount ≤ exceptionalCount` pointwise (primes are a subset). -/
theorem primeExceptionalCount_le (N : ℕ) :
    primeExceptionalCount N ≤ exceptionalCount N := by
  classical
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.2⟩

end EscAnalytic
