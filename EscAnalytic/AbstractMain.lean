import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Unbundled
import Mathlib.Tactic
import EscAnalytic.Core
import EscAnalytic.Counting

/-!
# Abstract main-theorem assembly

This module isolates the last deduction in `thm:main`.  In the notation of
`EscAnalytic.Counting`, the target is `IsMainBound exceptionalCount`.

## Assembly boundary

The argument uses two intermediate estimates.  First, summing the finite
transfer over reduced classes gives
`E_red(N;z) ≪ N exp(-c₁ (log N)^{3/4})`.  Second, the decomposition `n = s*m`
with `s` smooth and `m` coprime to the small-prime product separates a smooth
range from a rough range.  The smooth range has polynomial size, while the
rough range is controlled by the reduced estimate and an Euler-product factor.

These estimates are bundled in `MainInputs`.  The remaining work in this file
is elementary: combine the two ranges and absorb both the polynomial term and
the logarithmic Euler-product factor into the exponential saving.

Thus `main (H : MainInputs)` proves `IsMainBound exceptionalCount` from the
bundled intermediate results.  `EscAnalytic.Paper` exposes the separate closed
instantiation used by the current development.
-/

namespace EscAnalytic

open scoped BigOperators
open Real

/-! ## Smooth-number counting carrier. -/

/-- `Ψ(x,y)`, the count of `y`-smooth positive integers `≤ x`.
The summed smooth-range estimate used by the canonical assembly wrappers is
isolated in `Assembly.rankin_smoothRange_zNatScale_bound`. -/
noncomputable def smoothPsi (x y : ℝ) : ℝ := by
  classical
  exact
    (((Finset.Icc (1 : ℕ) ⌊x⌋₊).filter
      (fun n : ℕ => ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) ≤ y)).card : ℝ)

/-- The smooth-number counting carrier is nonnegative. -/
theorem smoothPsi_nonneg (x y : ℝ) : 0 ≤ smoothPsi x y := by
  classical
  unfold smoothPsi
  exact Nat.cast_nonneg _

/-- The smooth-number carrier is bounded by the full interval cardinality. -/
theorem smoothPsi_le_floor (x y : ℝ) : smoothPsi x y ≤ (⌊x⌋₊ : ℝ) := by
  classical
  unfold smoothPsi
  have hfilter :
      (((Finset.Icc (1 : ℕ) ⌊x⌋₊).filter
        (fun n : ℕ => ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) ≤ y)).card : ℝ)
        ≤ ((Finset.Icc (1 : ℕ) ⌊x⌋₊).card : ℝ) := by
    exact_mod_cast
      Finset.card_filter_le (Finset.Icc (1 : ℕ) ⌊x⌋₊)
        (fun n : ℕ => ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) ≤ y)
  have hcard : (Finset.Icc (1 : ℕ) ⌊x⌋₊).card = ⌊x⌋₊ := by
    rw [Nat.card_Icc]
    omega
  simpa [hcard] using hfilter

/-- For nonnegative `x`, `Ψ(x,y) ≤ x`. -/
theorem smoothPsi_le_self_of_nonneg {x y : ℝ} (hx : 0 ≤ x) : smoothPsi x y ≤ x := by
  exact (smoothPsi_le_floor x y).trans (Nat.floor_le hx)

/-- The real smooth-number carrier is bounded by the integer endpoint on natural
arguments. -/
theorem smoothPsi_nat_le (B z : ℕ) : smoothPsi (B : ℝ) (z : ℝ) ≤ (B : ℝ) := by
  simpa using smoothPsi_le_floor (B : ℝ) (z : ℝ)

/-- `Ψ(x,y)` is monotone in the range endpoint. -/
theorem smoothPsi_mono_left {x x' y : ℝ} (hxx' : x ≤ x') :
    smoothPsi x y ≤ smoothPsi x' y := by
  classical
  unfold smoothPsi
  have hfloor : ⌊x⌋₊ ≤ ⌊x'⌋₊ := Nat.floor_mono hxx'
  have hsub :
      (Finset.Icc (1 : ℕ) ⌊x⌋₊).filter
          (fun n : ℕ => ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) ≤ y)
        ⊆
      (Finset.Icc (1 : ℕ) ⌊x'⌋₊).filter
          (fun n : ℕ => ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) ≤ y) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn.1).1,
      le_trans (Finset.mem_Icc.mp hn.1).2 hfloor⟩, hn.2⟩
  exact_mod_cast Finset.card_le_card hsub

/-- `Ψ(x,y)` is monotone in the smoothness cutoff. -/
theorem smoothPsi_mono_right {x y y' : ℝ} (hyy' : y ≤ y') :
    smoothPsi x y ≤ smoothPsi x y' := by
  classical
  unfold smoothPsi
  have hsub :
      (Finset.Icc (1 : ℕ) ⌊x⌋₊).filter
          (fun n : ℕ => ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) ≤ y)
        ⊆
      (Finset.Icc (1 : ℕ) ⌊x⌋₊).filter
          (fun n : ℕ => ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) ≤ y') := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, fun p hp hpd => le_trans (hn.2 p hp hpd) hyy'⟩
  exact_mod_cast Finset.card_le_card hsub

/-! ## Concrete Euler product carrier for the lifting range. -/

/-- The finite Euler product `∏_{p≤z} (1-1/p)^{-1}` appearing in the lifting
argument. -/
noncomputable def eulerProductFactor (z : ℝ) : ℝ := by
  classical
  exact
    ∏ p in (Finset.Icc (2 : ℕ) ⌊z⌋₊).filter Nat.Prime,
      ((1 : ℝ) - (1 : ℝ) / (p : ℝ))⁻¹

/-- The concrete finite Euler product is nonnegative. -/
theorem eulerProductFactor_nonneg (z : ℝ) : 0 ≤ eulerProductFactor z := by
  classical
  unfold eulerProductFactor
  apply Finset.prod_nonneg
  intro p hp
  have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have hp_gt_one_nat : 1 < p := hpPrime.one_lt
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hp_gt_one_nat)
  have hp_gt_one : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp_gt_one_nat
  have hinv_lt_one : (1 : ℝ) / (p : ℝ) < 1 := by
    rw [div_lt_iff₀ hp_pos]
    linarith
  exact inv_nonneg.mpr (sub_pos.mpr hinv_lt_one).le

/-- Each integer factor in the full telescoping product
`∏_{2≤m≤n}(1-1/m)⁻¹` is at least one. -/
theorem eulerIntegerTerm_one_le (m : ℕ) (hm : 2 ≤ m) :
    (1 : ℝ) ≤ (((1 : ℝ) - (1 : ℝ) / (m : ℝ))⁻¹) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
  have hmgt1 : (1 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hm)
  have hinv_lt_one : (1 : ℝ) / (m : ℝ) < 1 := by
    rw [div_lt_iff₀ hmpos]
    simpa using hmgt1
  have hbase_pos : 0 < (1 : ℝ) - 1 / (m : ℝ) := sub_pos.mpr hinv_lt_one
  exact (one_le_inv₀ hbase_pos).2 (by nlinarith [div_pos zero_lt_one hmpos])

/-- The concrete finite Euler product is at least one. -/
theorem eulerProductFactor_one_le (z : ℝ) : 1 ≤ eulerProductFactor z := by
  classical
  unfold eulerProductFactor
  simpa using
    (Finset.prod_le_prod
      (s := (Finset.Icc (2 : ℕ) ⌊z⌋₊).filter Nat.Prime)
      (f := fun _p : ℕ => (1 : ℝ))
      (g := fun p : ℕ => (((1 : ℝ) - (1 : ℝ) / (p : ℝ))⁻¹))
      (fun _p _hp => zero_le_one)
      (fun p hp =>
        eulerIntegerTerm_one_le p (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1))

/-- Telescoping identity for the full integer product. -/
theorem eulerIntegerProduct_telescopes_succ (n : ℕ) :
    (∏ m in Finset.Icc (2 : ℕ) (n + 1),
        (((1 : ℝ) - (1 : ℝ) / (m : ℝ))⁻¹)) = (n + 1 : ℝ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hle : 2 ≤ n.succ + 1 := by omega
      rw [Finset.prod_Icc_succ_top hle, ih]
      have hpos : ((n : ℝ) + 2) ≠ 0 := by positivity
      field_simp [hpos]

/-- Telescoping identity for `∏_{2≤m≤n}(1-1/m)⁻¹ = n`. -/
theorem eulerIntegerProduct_telescopes (n : ℕ) (hn : 1 ≤ n) :
    (∏ m in Finset.Icc (2 : ℕ) n,
        (((1 : ℝ) - (1 : ℝ) / (m : ℝ))⁻¹)) = (n : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    eulerIntegerProduct_telescopes_succ k

/-- The prime Euler product is bounded by the corresponding full integer
telescoping product.  This is only a coarse elementary fallback, not Mertens. -/
theorem eulerProductFactor_le_integerProduct (z : ℝ) :
    eulerProductFactor z ≤
      ∏ m in Finset.Icc (2 : ℕ) ⌊z⌋₊,
        (((1 : ℝ) - (1 : ℝ) / (m : ℝ))⁻¹) := by
  classical
  unfold eulerProductFactor
  rw [Finset.prod_filter]
  apply Finset.prod_le_prod
  · intro m hm
    by_cases hp : Nat.Prime m
    · simp only [hp, ↓reduceIte]
      exact le_trans zero_le_one (eulerIntegerTerm_one_le m (Finset.mem_Icc.mp hm).1)
    · simp [hp]
  · intro m hm
    by_cases hp : Nat.Prime m
    · simp [hp]
    · simp only [hp, ↓reduceIte]
      exact eulerIntegerTerm_one_le m (Finset.mem_Icc.mp hm).1

/-- Elementary unconditional fallback for the concrete Euler product:
`∏_{p≤z}(1-1/p)⁻¹ ≤ z` for `z ≥ 1`. -/
theorem eulerProductFactor_le_self_of_one_le (z : ℝ) (hz : 1 ≤ z) :
    eulerProductFactor z ≤ z := by
  have hfloor : 1 ≤ ⌊z⌋₊ := by
    rw [Nat.one_le_floor_iff]
    exact hz
  calc
    eulerProductFactor z
        ≤ ∏ m in Finset.Icc (2 : ℕ) ⌊z⌋₊,
            (((1 : ℝ) - (1 : ℝ) / (m : ℝ))⁻¹) :=
          eulerProductFactor_le_integerProduct z
    _ = (⌊z⌋₊ : ℝ) := eulerIntegerProduct_telescopes ⌊z⌋₊ hfloor
    _ ≤ z := Nat.floor_le (le_trans zero_le_one hz)

/-- At the manuscript cutoff `z(X)=(log X)^4`, the elementary fallback gives
`O((log X)^4)`. -/
theorem eulerProductFactor_zScale_eventual_log_fourth_bound :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      eulerProductFactor (zScale X) ≤ C * (Real.log X) ^ (4 : ℕ) := by
  refine ⟨1, Real.exp 1, by norm_num, ?_⟩
  intro X hX
  have hlog_ge_one : 1 ≤ Real.log X := by
    have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hX
    rw [Real.le_log_iff_exp_le hXpos]
    exact hX
  have hz_ge_one : 1 ≤ zScale X := by
    unfold zScale
    simpa using pow_le_pow_left₀ zero_le_one hlog_ge_one 4
  calc
    eulerProductFactor (zScale X)
        ≤ zScale X := eulerProductFactor_le_self_of_one_le (zScale X) hz_ge_one
    _ = 1 * (Real.log X) ^ (4 : ℕ) := by
          unfold zScale
          ring

/-- Concrete Euler factor at denominator cutoff `N`. -/
noncomputable def eulerProductFactorAtNat (N : ℕ) : ℝ :=
  eulerProductFactor (zScale (N : ℝ))

/-- The concrete `N`-indexed Euler factor is nonnegative. -/
theorem eulerProductFactorAtNat_nonneg (N : ℕ) :
    0 ≤ eulerProductFactorAtNat N := by
  unfold eulerProductFactorAtNat
  exact eulerProductFactor_nonneg (zScale (N : ℝ))

/-- The concrete `N`-indexed Euler factor is at least one. -/
theorem eulerProductFactorAtNat_one_le (N : ℕ) :
    1 ≤ eulerProductFactorAtNat N := by
  unfold eulerProductFactorAtNat
  exact eulerProductFactor_one_le (zScale (N : ℝ))

/-- Mertens-free bound for the concrete Euler factor.

The telescoping integer-product fallback gives
`∏_{p≤z_N}(1-1/p)^{-1} ≤ z_N = (log N)^4`; this uses no analytic input. -/
theorem eulerProductFactorAtNat_log_fourth_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      eulerProductFactorAtNat N ≤ C * (Real.log N) ^ (4 : ℕ) := by
  refine ⟨1, by norm_num, ?_⟩
  intro N hN
  have hN_ge_exp : Real.exp 1 ≤ (N : ℝ) := by
    have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hexp3 : Real.exp 1 ≤ (3 : ℝ) := by
      exact le_of_lt (Real.exp_one_lt_d9.trans (by norm_num))
    exact le_trans hexp3 hN3
  have hNpos : (0 : ℝ) < (N : ℝ) :=
    lt_of_lt_of_le (Real.exp_pos 1) hN_ge_exp
  have hlog_ge_one : (1 : ℝ) ≤ Real.log (N : ℝ) := by
    rw [Real.le_log_iff_exp_le hNpos]
    exact hN_ge_exp
  have hz_ge_one : (1 : ℝ) ≤ zScale (N : ℝ) := by
    unfold zScale
    calc
      (1 : ℝ) = (1 : ℝ) ^ (4 : ℕ) := by norm_num
      _ ≤ (Real.log (N : ℝ)) ^ (4 : ℕ) :=
        pow_le_pow_left₀ zero_le_one hlog_ge_one 4
  calc
    eulerProductFactorAtNat N
        = eulerProductFactor (zScale (N : ℝ)) := rfl
    _ ≤ zScale (N : ℝ) :=
        eulerProductFactor_le_self_of_one_le (zScale (N : ℝ)) hz_ge_one
    _ = 1 * (Real.log N) ^ (4 : ℕ) := by
        unfold zScale
        ring

/-- For `N ≥ 3`, one logarithm is bounded by four logarithms.  This keeps older
sharp-log Euler interfaces compatible with the weaker `MainInputs` fourth-log
field. -/
theorem log_le_log_pow_four_of_three_le {N : ℕ} (hN : 3 ≤ N) :
    Real.log N ≤ (Real.log N) ^ (4 : ℕ) := by
  have hN_ge_exp : Real.exp 1 ≤ (N : ℝ) := by
    have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hexp3 : Real.exp 1 ≤ (3 : ℝ) := by
      exact le_of_lt (Real.exp_one_lt_d9.trans (by norm_num))
    exact le_trans hexp3 hN3
  have hNpos : (0 : ℝ) < (N : ℝ) :=
    lt_of_lt_of_le (Real.exp_pos 1) hN_ge_exp
  have hlog_ge_one : (1 : ℝ) ≤ Real.log (N : ℝ) := by
    rw [Real.le_log_iff_exp_le hNpos]
    exact hN_ge_exp
  have hlog_nonneg : (0 : ℝ) ≤ Real.log (N : ℝ) := le_trans zero_le_one hlog_ge_one
  have hpow : (1 : ℝ) ≤ (Real.log (N : ℝ)) ^ (3 : ℕ) :=
    one_le_pow₀ hlog_ge_one (n := 3)
  calc
    Real.log N = Real.log (N : ℝ) * 1 := by ring
    _ ≤ Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ (3 : ℕ) :=
        mul_le_mul_of_nonneg_left hpow hlog_nonneg
    _ = (Real.log N) ^ (4 : ℕ) := by ring

/-! ## Real analytic helper lemmas for the two absorptions. -/

/-- The basic rewrite `N · saving c N = exp(log N + (-c)(log N)^{3/4})` for
`N > 0`, used to merge the `N`-factor into the exponent. -/
theorem mul_saving_eq_exp (c : ℝ) {N : ℕ} (hN : 0 < N) :
    (N : ℝ) * saving c N
      = Real.exp (Real.log N + (-c) * (Real.log N) ^ ((3 : ℝ) / 4)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  unfold saving
  rw [← Real.exp_log hNpos, ← Real.exp_add, Real.log_exp]

/-- **Absorption of a polynomial range into the exponential saving.**
If `0 < θ < 1` then for every `Cs > 0` there exist `c > 0`, `C > 0` such that
`Cs · N^θ ≤ C · N · saving c N` for all `N ≥ 3`.  This directly formalizes
of `N^{3/4+o(1)} ≪ N · exp(-c (log N)^{3/4})` (tex 2057–2063, 2077): a fixed power
`θ < 1` of `N` is dominated by `N` times the slowly-decaying saving.

Proof: with `c := (1-θ)/2` and `C := max Cs 1`, after merging the `N`-factor into
the exponent it suffices that `(1-θ)·log N ≥ c·(log N)^{3/4}`, equivalently
`(1-θ)·(log N)^{1/4} ≥ (1-θ)/2`, i.e. `(log N)^{1/4} ≥ 1/2`, which holds since
`log N ≥ log 3 > 1/16`. -/
theorem poly_absorb {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {Cs : ℝ} (hCs : 0 < Cs) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ N : ℕ, 3 ≤ N → Cs * (N : ℝ) ^ θ ≤ C * ((N : ℝ) * saving c N) := by
  refine ⟨(1 - θ) / 2, by linarith, max Cs 1, lt_of_lt_of_le hCs (le_max_left _ _), ?_⟩
  intro N hN
  set c : ℝ := (1 - θ) / 2 with hc
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set L : ℝ := Real.log N with hLdef
  have hL0 : 0 < L := log_pos_of_three_le hN
  -- `N^θ = exp (θ · L)`
  have hNrpow : (N : ℝ) ^ θ = Real.exp (θ * L) := by
    rw [Real.rpow_def_of_pos hNpos]; ring_nf
  -- `N · saving c N = exp (L + (-c) L^{3/4})`
  have hsave : (N : ℝ) * saving c N = Real.exp (L + (-c) * L ^ ((3 : ℝ) / 4)) := by
    have := mul_saving_eq_exp c (by omega : 0 < N); rw [← hLdef] at this; exact this
  rw [hNrpow, hsave]
  -- Step 1: the exponential inequality `θ L ≤ L + (-c) L^{3/4}`.
  have hkey : θ * L ≤ L + (-c) * L ^ ((3 : ℝ) / 4) := by
    -- equivalently `c · L^{3/4} ≤ (1-θ) L`.
    have hL34pos : 0 < L ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL0 _
    -- `L^{1/4} ≥ 1/2` since `L ≥ 2/3 > 1/16`.
    have hLlower : (1 : ℝ) / 16 < L := by
      have := log_ge_of_three_le hN; rw [← hLdef] at this; linarith
    have hquart : (1 : ℝ) / 2 ≤ L ^ ((1 : ℝ) / 4) := by
      have h16 : ((1 : ℝ) / 16) ^ ((1 : ℝ) / 4) ≤ L ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (by norm_num) hLlower.le (by norm_num)
      have : ((1 : ℝ) / 16) ^ ((1 : ℝ) / 4) = (1 : ℝ) / 2 := by
        rw [show (1 : ℝ) / 16 = (1 / 2) ^ (4 : ℕ) by norm_num,
          ← Real.rpow_natCast (1 / 2 : ℝ) 4, ← Real.rpow_mul (by norm_num)]
        norm_num
      linarith [this ▸ h16]
    -- `L = L^{3/4} · L^{1/4}` so `(1-θ) L = (1-θ) L^{1/4} · L^{3/4} ≥ c · L^{3/4}`.
    have hLsplit : L = L ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_add hL0]; norm_num
    have hcle : c ≤ (1 - θ) * L ^ ((1 : ℝ) / 4) := by
      have : c = (1 - θ) * (1 / 2) := by rw [hc]; ring
      rw [this]
      apply mul_le_mul_of_nonneg_left hquart (by linarith)
    have : c * L ^ ((3 : ℝ) / 4) ≤ (1 - θ) * L := by
      calc c * L ^ ((3 : ℝ) / 4)
          ≤ ((1 - θ) * L ^ ((1 : ℝ) / 4)) * L ^ ((3 : ℝ) / 4) :=
            mul_le_mul_of_nonneg_right hcle hL34pos.le
        _ = (1 - θ) * (L ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4)) := by ring
        _ = (1 - θ) * L := by rw [← hLsplit]
    linarith
  -- Step 2: monotonicity of `exp` and of multiplication by the positive constant.
  have hexpmono : Real.exp (θ * L) ≤ Real.exp (L + (-c) * L ^ ((3 : ℝ) / 4)) :=
    Real.exp_le_exp.mpr hkey
  have hCsle : Cs ≤ max Cs 1 := le_max_left _ _
  calc Cs * Real.exp (θ * L)
      ≤ Cs * Real.exp (L + (-c) * L ^ ((3 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left hexpmono hCs.le
    _ ≤ max Cs 1 * Real.exp (L + (-c) * L ^ ((3 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_right hCsle (Real.exp_pos _).le

/-- **Absorption of a `log`-sized factor into the exponential saving.**
For any `c₁ > 0` and `Ce, C₁ > 0` there exist `c > 0`, `C > 0` such that
`Ce · log N · (C₁ · N · saving c₁ N) ≤ C · N · saving c N` for all `N ≥ 3`.

This formalizes the manuscript's final Euler-factor absorption:
the Euler product `∏_{p≤z_N}(1-1/p)^{-1} ≪ log z_N ≪ log N` is "absorbed into the
exponential saving" by enlarging the constant and slightly shrinking `c`.

Proof: with `c := c₁/2` it suffices that `Ce·C₁·log N ≤ C·exp((c₁/2)(log N)^{3/4})`.
Writing `L := log N`, `t := L^{3/4}`, we have `L = t^{4/3} ≤ 1 + t²`, and the
quadratic `t²` is dominated by `(8/c₁²)·exp((c₁/2)t)` via `sq_le_four_mul_exp`,
while `1 ≤ exp((c₁/2)t)`; the constant `C` collects these. -/
theorem log_absorb {c₁ : ℝ} (hc₁ : 0 < c₁) {Ce C₁ : ℝ} (hCe : 0 < Ce) (hC₁ : 0 < C₁) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ N : ℕ, 3 ≤ N →
        Ce * Real.log N * (C₁ * ((N : ℝ) * saving c₁ N)) ≤ C * ((N : ℝ) * saving c N) := by
  -- new saving constant
  set c : ℝ := c₁ / 2 with hc
  -- absorbing constant: `C := Ce·C₁·(1 + 16/c₁²)`.
  refine ⟨c, by positivity, Ce * C₁ * (1 + 16 / c₁ ^ 2), by positivity, ?_⟩
  intro N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set L : ℝ := Real.log N with hLdef
  have hL0 : 0 < L := log_pos_of_three_le hN
  set t : ℝ := L ^ ((3 : ℝ) / 4) with htdef
  have ht0 : 0 < t := Real.rpow_pos_of_pos hL0 _
  -- `N · saving c₁ N = N · exp(-c₁ t)`, `N · saving c N = N · exp(-c t)`.
  have hsave₁ : (N : ℝ) * saving c₁ N = (N : ℝ) * Real.exp (-c₁ * t) := by
    unfold saving; rw [← hLdef, ← htdef]
  have hsaveC : (N : ℝ) * saving c N = (N : ℝ) * Real.exp (-c * t) := by
    unfold saving; rw [← hLdef, ← htdef]
  rw [hsave₁, hsaveC]
  -- Reduce to `Ce·C₁·L·exp(-c₁ t) ≤ C·exp(-c t)` after cancelling the positive `N`.
  -- It suffices to show `Ce·C₁·L ≤ C·exp((c₁ - c) t) = C·exp(c t)`.
  have hLbound : L ≤ 1 + t ^ 2 := by
    have : t ^ ((4 : ℝ) / 3) = L := by
      rw [htdef]; exact rpow_three_quarters_four_thirds hL0.le
    calc L = t ^ ((4 : ℝ) / 3) := this.symm
      _ ≤ 1 + t ^ 2 := rpow_four_thirds_le ht0.le
  -- quadratic domination: `t² ≤ (16/c₁²)·exp(c·t)` since `c = c₁/2`.
  have hquad : t ^ 2 ≤ (16 / c₁ ^ 2) * Real.exp (c * t) := by
    have hct : 0 ≤ c * t := by positivity
    have h := sq_le_four_mul_exp hct          -- `(c·t)² ≤ 4·exp(c·t)`
    have hcsq : (c * t) ^ 2 = c ^ 2 * t ^ 2 := by ring
    have hcpos : 0 < c ^ 2 := by positivity
    -- from `c²·t² ≤ 4·exp(c t)` divide by `c²`.
    have hdiv : t ^ 2 ≤ (4 / c ^ 2) * Real.exp (c * t) := by
      rw [hcsq] at h
      rw [div_mul_eq_mul_div, le_div_iff₀ hcpos]
      nlinarith [h]
    -- `4/c² = 4/(c₁/2)² = 16/c₁²`.
    have hcc : c ^ 2 = c₁ ^ 2 / 4 := by rw [hc]; ring
    have e : (4 : ℝ) / c ^ 2 = 16 / c₁ ^ 2 := by
      rw [hcc]; field_simp; ring
    rw [e] at hdiv; exact hdiv
  -- one more: `1 ≤ exp(c t)`.
  have hone : (1 : ℝ) ≤ Real.exp (c * t) := by
    have : (0 : ℝ) ≤ c * t := by positivity
    simpa using Real.one_le_exp this
  -- combine: `L ≤ 1 + t² ≤ (1 + 16/c₁²)·exp(c t)`.
  have hLexp : L ≤ (1 + 16 / c₁ ^ 2) * Real.exp (c * t) := by
    have : (1 : ℝ) + t ^ 2 ≤ (1 + 16 / c₁ ^ 2) * Real.exp (c * t) := by
      have h16 : (0 : ℝ) ≤ 16 / c₁ ^ 2 := by positivity
      nlinarith [hone, hquad, Real.exp_pos (c * t)]
    linarith
  -- Now assemble the multiplicative chain (cancel the positive `N`, then `exp`).
  -- LHS = Ce·L·(C₁·N·exp(-c₁ t)); RHS = (Ce·C₁·(1+8/c₁²))·N·exp(-c t).
  have hexp_id : Real.exp (-c₁ * t) * Real.exp (c * t) = Real.exp (-c * t) := by
    rw [← Real.exp_add]; congr 1; rw [hc]; ring
  have hExpPos : 0 < Real.exp (-c₁ * t) := Real.exp_pos _
  -- bound L by its exponential domination, keeping everything nonneg.
  have key : Ce * L * (C₁ * ((N : ℝ) * Real.exp (-c₁ * t)))
      ≤ Ce * C₁ * (1 + 16 / c₁ ^ 2) * ((N : ℝ) * Real.exp (-c * t)) := by
    have hmul : Ce * L * (C₁ * ((N : ℝ) * Real.exp (-c₁ * t)))
        ≤ Ce * ((1 + 16 / c₁ ^ 2) * Real.exp (c * t))
            * (C₁ * ((N : ℝ) * Real.exp (-c₁ * t))) := by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left hLexp hCe.le
      · positivity
    refine hmul.trans ?_
    have : Ce * ((1 + 16 / c₁ ^ 2) * Real.exp (c * t))
            * (C₁ * ((N : ℝ) * Real.exp (-c₁ * t)))
      = Ce * C₁ * (1 + 16 / c₁ ^ 2)
            * ((N : ℝ) * (Real.exp (-c₁ * t) * Real.exp (c * t))) := by ring
    rw [this, hexp_id]
  exact key

/-- Four logarithmic factors can also be absorbed into the exponential saving.

This is the Mertens-free replacement needed when the concrete Euler product is
bounded only by the elementary fallback `O((log N)^4)`.  The proof simply
iterates `log_absorb` four times. -/
theorem log_pow_four_absorb {c₁ : ℝ} (hc₁ : 0 < c₁)
    {Ce C₁ : ℝ} (hCe : 0 < Ce) (hC₁ : 0 < C₁) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ N : ℕ, 3 ≤ N →
        Ce * (Real.log N) ^ (4 : ℕ) * (C₁ * ((N : ℝ) * saving c₁ N))
          ≤ C * ((N : ℝ) * saving c N) := by
  obtain ⟨c₂, hc₂, C₂, hC₂, h₂⟩ :=
    log_absorb hc₁ (by norm_num : (0 : ℝ) < 1) hC₁
  obtain ⟨c₃, hc₃, C₃, hC₃, h₃⟩ :=
    log_absorb hc₂ (by norm_num : (0 : ℝ) < 1) hC₂
  obtain ⟨c₄, hc₄, C₄, hC₄, h₄⟩ :=
    log_absorb hc₃ (by norm_num : (0 : ℝ) < 1) hC₃
  obtain ⟨c₅, hc₅, C₅, hC₅, h₅⟩ :=
    log_absorb hc₄ hCe hC₄
  refine ⟨c₅, hc₅, C₅, hC₅, ?_⟩
  intro N hN
  set L : ℝ := Real.log N with hLdef
  have hL_nonneg : 0 ≤ L := (log_pos_of_three_le hN).le
  have h₂N :
      L * (C₁ * ((N : ℝ) * saving c₁ N))
        ≤ C₂ * ((N : ℝ) * saving c₂ N) := by
    have := h₂ N hN
    rw [← hLdef] at this
    simpa [one_mul] using this
  have h₃N :
      L * (C₂ * ((N : ℝ) * saving c₂ N))
        ≤ C₃ * ((N : ℝ) * saving c₃ N) := by
    have := h₃ N hN
    rw [← hLdef] at this
    simpa [one_mul] using this
  have h₄N :
      L * (C₃ * ((N : ℝ) * saving c₃ N))
        ≤ C₄ * ((N : ℝ) * saving c₄ N) := by
    have := h₄ N hN
    rw [← hLdef] at this
    simpa [one_mul] using this
  have h₅N :
      Ce * L * (C₄ * ((N : ℝ) * saving c₄ N))
        ≤ C₅ * ((N : ℝ) * saving c₅ N) := by
    have := h₅ N hN
    rw [← hLdef] at this
    simpa using this
  calc
    Ce * (Real.log N) ^ (4 : ℕ) * (C₁ * ((N : ℝ) * saving c₁ N))
        = Ce * L ^ (4 : ℕ) * (C₁ * ((N : ℝ) * saving c₁ N)) := by rw [hLdef]
    _ = Ce * L ^ (3 : ℕ) * (L * (C₁ * ((N : ℝ) * saving c₁ N))) := by ring
    _ ≤ Ce * L ^ (3 : ℕ) * (C₂ * ((N : ℝ) * saving c₂ N)) := by
        exact mul_le_mul_of_nonneg_left h₂N
          (mul_nonneg hCe.le (pow_nonneg hL_nonneg 3))
    _ = Ce * L ^ (2 : ℕ) * (L * (C₂ * ((N : ℝ) * saving c₂ N))) := by ring
    _ ≤ Ce * L ^ (2 : ℕ) * (C₃ * ((N : ℝ) * saving c₃ N)) := by
        exact mul_le_mul_of_nonneg_left h₃N
          (mul_nonneg hCe.le (pow_nonneg hL_nonneg 2))
    _ = Ce * L * (L * (C₃ * ((N : ℝ) * saving c₃ N))) := by ring
    _ ≤ Ce * L * (C₄ * ((N : ℝ) * saving c₄ N)) := by
        exact mul_le_mul_of_nonneg_left h₄N (mul_nonneg hCe.le hL_nonneg)
    _ ≤ C₅ * ((N : ℝ) * saving c₅ N) := h₅N

/-! ## The hypothesis bundle for the abstract theorem -/

/-- The intermediate results consumed by the final deduction of `thm:main`.
Each field is supplied by another module; bundling them here keeps the
conditional interface explicit.

Fields:
* `Ered` — the reduced-class missed count `E_red(N;z)` (tex 2036–2043).
* `Ered_c₁`, `Ered_C₁`, `Ered_pos₁`, `Ered_posC₁`, `Ered_bound` — the bound (a):
  `E_red(N;z) ≪ N · exp(-c₁ (log N)^{3/4})` obtained by summing
  `thm:finite-transfer` over reduced `b` (tex 2035–2043, `eq:reduced-missed`).
* `smooth` — the contribution of the smooth range `m ≤ N^{1/2}` of the lifting
  (tex 2057–2063); `smoothExp`, `smoothExp_pos`, `smoothExp_lt_one`, `smoothC`,
  `smoothC_pos`, `smooth_bound` encode `≪ N^{3/4+o(1)} ≪ N^θ` for a fixed
  `θ ∈ (0,1)` (`N^{3/4+o(1)}`, tex 2063, 2077, via a cited smooth-number input).
* `euler` — the Euler-product factor `∏_{p≤z_N}(1-1/p)^{-1}` of the `m > N^{1/2}`
  range; `eulerC`, `eulerC_pos`, `euler_bound` encode the Mertens-free
  fallback `≪ (log N)^4`, which is still absorbed by the exponential saving.
* `lift` — the **master lifting inequality** (tex 2057–2078): writing `n = s·m`
  and splitting into the two `m`-ranges, the full exceptional count is at most the
  smooth-range contribution plus the Euler-product factor times the reduced bound. -/
structure MainInputs where
  /-- reduced-class missed count `E_red(N;z)` (tex 2036). -/
  Ered : ℕ → ℕ
  /-- saving constant of the reduced bound. -/
  Ered_c₁ : ℝ
  /-- implied constant of the reduced bound. -/
  Ered_C₁ : ℝ
  Ered_pos₁ : 0 < Ered_c₁
  Ered_posC₁ : 0 < Ered_C₁
  /-- (a) `E_red(N;z) ≪ N exp(-c₁ (log N)^{3/4})` (tex 2042–2043, `eq:reduced-missed`). -/
  Ered_bound : ∀ N : ℕ, 3 ≤ N →
    (Ered N : ℝ) ≤ Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N)
  /-- contribution of the smooth range `m ≤ N^{1/2}` (tex 2057). -/
  smooth : ℕ → ℝ
  /-- the `o(1)`-stable exponent `3/4 + o(1)` of the smooth range, a fixed `< 1`. -/
  smoothExp : ℝ
  smoothExp_pos : 0 < smoothExp
  smoothExp_lt_one : smoothExp < 1
  smoothC : ℝ
  smoothC_pos : 0 < smoothC
  /-- (b₁) smooth range bound `≪ N^{3/4+o(1)} ≪ N^θ` (tex 2057–2063, via a
  cited smooth-number input). -/
  smooth_bound : ∀ N : ℕ, 3 ≤ N → smooth N ≤ smoothC * (N : ℝ) ^ smoothExp
  smooth_nonneg : ∀ N : ℕ, 0 ≤ smooth N
  /-- Euler-product factor `∏_{p≤z_N}(1-1/p)^{-1}` of the `m > N^{1/2}` range. -/
  euler : ℕ → ℝ
  eulerC : ℝ
  eulerC_pos : 0 < eulerC
  euler_nonneg : ∀ N : ℕ, 0 ≤ euler N
  /-- (b₂) Euler product fallback `≪ (log N)^4`; the fourth logarithmic power is
  absorbed into the final exponential saving. -/
  euler_bound : ∀ N : ℕ, 3 ≤ N → euler N ≤ eulerC * (Real.log N) ^ (4 : ℕ)
  /-- (b) master lifting inequality (tex 2057–2078): the exceptional count is
  bounded by the smooth range plus the Euler-product factor times `E_red`. -/
  lift : ∀ N : ℕ, 3 ≤ N →
    (exceptionalCount N : ℝ) ≤ smooth N + euler N * (Ered N : ℝ)

/-! ## Assembly of `thm:main`. -/

/-- **Main theorem of the manuscript (`thm:main`), conditional on
`H : MainInputs`.**

`E(N) = exceptionalCount N ≪ N · exp(-c (log N)^{3/4})`, i.e.
`IsMainBound exceptionalCount`.

The proof is the bookkeeping of tex 2057–2078:

1.  Bound the smooth range `smooth N ≤ smoothC · N^θ` (`θ < 1`) and absorb the
    polynomial into the saving via `poly_absorb` (`N^{3/4+o(1)} ≪ N·saving`).
2.  Bound the `m > N^{1/2}` range
    `euler N · E_red N ≤ eulerC·(log N)^4·(C₁·N·saving c₁ N)`
    and absorb the fourth-log Euler-product factor via `log_pow_four_absorb`.
3.  Add the two `N·saving`-shaped bounds, using the *smaller* of the two saving
    constants for a common saving (since `saving` is decreasing in `c`). -/
theorem main (H : MainInputs) : IsMainBound exceptionalCount := by
  classical
  -- Step 1: polynomial absorption of the smooth range.
  obtain ⟨cs, hcs, Cs, hCs, hpoly⟩ :=
    poly_absorb H.smoothExp_pos H.smoothExp_lt_one H.smoothC_pos
  -- Step 2: fourth-log absorption of the Euler-product × reduced bound.
  obtain ⟨ce, hce, Ce, hCe, hlog⟩ :=
    log_pow_four_absorb H.Ered_pos₁ H.eulerC_pos H.Ered_posC₁
  -- Common saving constant: the smaller of `cs, ce`.
  set c : ℝ := min cs ce with hcdef
  have hc : 0 < c := lt_min hcs hce
  -- Both saving-shaped bounds re-expressed with the common `c`:
  -- `saving c' N ≤ saving c N` whenever `c ≤ c'` (saving decreasing in c), for log N ≥ 0.
  have sav_mono : ∀ (c' : ℝ), c ≤ c' → ∀ N : ℕ, 3 ≤ N →
      (N : ℝ) * saving c' N ≤ (N : ℝ) * saving c N := by
    intro c' hcc' N hN
    have hLpos : 0 < Real.log N := log_pos_of_three_le hN
    have hL34 : 0 ≤ (Real.log N) ^ ((3 : ℝ) / 4) := (Real.rpow_pos_of_pos hLpos _).le
    have hNpos : (0 : ℝ) ≤ N := by positivity
    apply mul_le_mul_of_nonneg_left _ hNpos
    unfold saving
    apply Real.exp_le_exp.mpr
    have : -c' * (Real.log N) ^ ((3 : ℝ) / 4) ≤ -c * (Real.log N) ^ ((3 : ℝ) / 4) := by
      apply mul_le_mul_of_nonneg_right _ hL34; linarith
    exact this
  -- Final constant.
  refine ⟨c, hc, Cs + Ce, by positivity, ?_⟩
  intro N hN
  -- master lifting inequality
  have hlift := H.lift N hN
  -- bound smooth term
  have hsmooth_le : H.smooth N ≤ Cs * ((N : ℝ) * saving c N) := by
    have h1 : H.smooth N ≤ H.smoothC * (N : ℝ) ^ H.smoothExp := H.smooth_bound N hN
    have h2 : H.smoothC * (N : ℝ) ^ H.smoothExp ≤ Cs * ((N : ℝ) * saving cs N) :=
      hpoly N hN
    have h3 : (N : ℝ) * saving cs N ≤ (N : ℝ) * saving c N :=
      sav_mono cs (min_le_left _ _) N hN
    calc H.smooth N ≤ Cs * ((N : ℝ) * saving cs N) := h1.trans h2
      _ ≤ Cs * ((N : ℝ) * saving c N) := mul_le_mul_of_nonneg_left h3 hCs.le
  -- bound Euler × reduced term
  have hreduced_le : H.euler N * (H.Ered N : ℝ) ≤ Ce * ((N : ℝ) * saving c N) := by
    -- first replace `euler N` by `eulerC·(log N)^4` and `Ered N` by its bound
    have heu : H.euler N ≤ H.eulerC * (Real.log N) ^ (4 : ℕ) := H.euler_bound N hN
    have hEr : (H.Ered N : ℝ) ≤ H.Ered_C₁ * ((N : ℝ) * saving H.Ered_c₁ N) :=
      H.Ered_bound N hN
    have hEr0 : (0 : ℝ) ≤ (H.Ered N : ℝ) := by positivity
    have hlogpos : 0 ≤ Real.log N := (log_pos_of_three_le hN).le
    -- `euler N · Ered N ≤ (eulerC·(log N)^4)·(C₁·N·saving c₁ N)`
    have step1 : H.euler N * (H.Ered N : ℝ)
        ≤ (H.eulerC * (Real.log N) ^ (4 : ℕ)) *
            (H.Ered_C₁ * ((N : ℝ) * saving H.Ered_c₁ N)) := by
      apply mul_le_mul heu hEr hEr0
      exact mul_nonneg H.eulerC_pos.le (pow_nonneg hlogpos 4)
    -- apply `log_pow_four_absorb` (states the bound with `ce`/`Ce`), then `sav_mono` to `c`.
    have step2 : (H.eulerC * (Real.log N) ^ (4 : ℕ)) *
          (H.Ered_C₁ * ((N : ℝ) * saving H.Ered_c₁ N))
        ≤ Ce * ((N : ℝ) * saving ce N) := by
      have := hlog N hN
      simpa [mul_assoc] using this
    have step3 : (N : ℝ) * saving ce N ≤ (N : ℝ) * saving c N :=
      sav_mono ce (min_le_right _ _) N hN
    calc H.euler N * (H.Ered N : ℝ)
        ≤ (H.eulerC * (Real.log N) ^ (4 : ℕ)) *
            (H.Ered_C₁ * ((N : ℝ) * saving H.Ered_c₁ N)) := step1
      _ ≤ Ce * ((N : ℝ) * saving ce N) := step2
      _ ≤ Ce * ((N : ℝ) * saving c N) := mul_le_mul_of_nonneg_left step3 hCe.le
  -- combine
  calc (exceptionalCount N : ℝ)
      ≤ H.smooth N + H.euler N * (H.Ered N : ℝ) := hlift
    _ ≤ Cs * ((N : ℝ) * saving c N) + Ce * ((N : ℝ) * saving c N) :=
        add_le_add hsmooth_le hreduced_le
    _ = (Cs + Ce) * ((N : ℝ) * saving c N) := by ring
    _ = (Cs + Ce) * (N : ℝ) * saving c N := by ring

/-- Main-bound assembly with a Mertens-free fourth-log Euler estimate.

This has the same bookkeeping content as `main`, but the Euler hypothesis is
weaker: `euler N ≤ C(log N)^4`.  The extra logarithms are absorbed by
`log_pow_four_absorb`, so the final main-bound shape is unchanged. -/
theorem main_of_euler_log_four
    (Ered : ℕ → ℕ) (Ered_c₁ Ered_C₁ : ℝ)
    (Ered_pos₁ : 0 < Ered_c₁) (Ered_posC₁ : 0 < Ered_C₁)
    (Ered_bound : ∀ N : ℕ, 3 ≤ N →
      (Ered N : ℝ) ≤ Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N))
    (smooth : ℕ → ℝ) (smoothExp smoothC : ℝ)
    (smoothExp_pos : 0 < smoothExp) (smoothExp_lt_one : smoothExp < 1)
    (smoothC_pos : 0 < smoothC)
    (smooth_bound : ∀ N : ℕ, 3 ≤ N → smooth N ≤ smoothC * (N : ℝ) ^ smoothExp)
    (euler : ℕ → ℝ) (eulerC : ℝ) (eulerC_pos : 0 < eulerC)
    (euler_bound_four : ∀ N : ℕ, 3 ≤ N → euler N ≤ eulerC * (Real.log N) ^ (4 : ℕ))
    (lift : ∀ N : ℕ, 3 ≤ N →
      (exceptionalCount N : ℝ) ≤ smooth N + euler N * (Ered N : ℝ)) :
    IsMainBound exceptionalCount := by
  classical
  obtain ⟨cs, hcs, Cs, hCs, hpoly⟩ :=
    poly_absorb smoothExp_pos smoothExp_lt_one smoothC_pos
  obtain ⟨ce, hce, Ce, hCe, hlog⟩ :=
    log_pow_four_absorb Ered_pos₁ eulerC_pos Ered_posC₁
  set c : ℝ := min cs ce with hcdef
  have hc : 0 < c := lt_min hcs hce
  have sav_mono : ∀ (c' : ℝ), c ≤ c' → ∀ N : ℕ, 3 ≤ N →
      (N : ℝ) * saving c' N ≤ (N : ℝ) * saving c N := by
    intro c' hcc' N hN
    have hLpos : 0 < Real.log N := log_pos_of_three_le hN
    have hL34 : 0 ≤ (Real.log N) ^ ((3 : ℝ) / 4) := (Real.rpow_pos_of_pos hLpos _).le
    have hNpos : (0 : ℝ) ≤ N := by positivity
    apply mul_le_mul_of_nonneg_left _ hNpos
    unfold saving
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by linarith : -c' ≤ -c) hL34
  refine ⟨c, hc, Cs + Ce, by positivity, ?_⟩
  intro N hN
  have hlift := lift N hN
  have hsmooth_le : smooth N ≤ Cs * ((N : ℝ) * saving c N) := by
    have h1 : smooth N ≤ smoothC * (N : ℝ) ^ smoothExp := smooth_bound N hN
    have h2 : smoothC * (N : ℝ) ^ smoothExp ≤ Cs * ((N : ℝ) * saving cs N) :=
      hpoly N hN
    have h3 : (N : ℝ) * saving cs N ≤ (N : ℝ) * saving c N :=
      sav_mono cs (min_le_left _ _) N hN
    calc smooth N ≤ Cs * ((N : ℝ) * saving cs N) := h1.trans h2
      _ ≤ Cs * ((N : ℝ) * saving c N) := mul_le_mul_of_nonneg_left h3 hCs.le
  have hreduced_le : euler N * (Ered N : ℝ) ≤ Ce * ((N : ℝ) * saving c N) := by
    have heu : euler N ≤ eulerC * (Real.log N) ^ (4 : ℕ) := euler_bound_four N hN
    have hEr : (Ered N : ℝ) ≤ Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N) :=
      Ered_bound N hN
    have hEr0 : (0 : ℝ) ≤ (Ered N : ℝ) := by positivity
    have hlog_nonneg : 0 ≤ Real.log N := (log_pos_of_three_le hN).le
    have step1 : euler N * (Ered N : ℝ)
        ≤ (eulerC * (Real.log N) ^ (4 : ℕ)) *
            (Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N)) := by
      apply mul_le_mul heu hEr hEr0
      exact mul_nonneg eulerC_pos.le (pow_nonneg hlog_nonneg 4)
    have step2 :
        (eulerC * (Real.log N) ^ (4 : ℕ)) *
            (Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N))
          ≤ Ce * ((N : ℝ) * saving ce N) := by
      simpa [mul_assoc] using hlog N hN
    have step3 : (N : ℝ) * saving ce N ≤ (N : ℝ) * saving c N :=
      sav_mono ce (min_le_right _ _) N hN
    calc euler N * (Ered N : ℝ)
        ≤ (eulerC * (Real.log N) ^ (4 : ℕ)) *
            (Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N)) := step1
      _ ≤ Ce * ((N : ℝ) * saving ce N) := step2
      _ ≤ Ce * ((N : ℝ) * saving c N) := mul_le_mul_of_nonneg_left step3 hCe.le
  calc (exceptionalCount N : ℝ)
      ≤ smooth N + euler N * (Ered N : ℝ) := hlift
    _ ≤ Cs * ((N : ℝ) * saving c N) + Ce * ((N : ℝ) * saving c N) :=
        add_le_add hsmooth_le hreduced_le
    _ = (Cs + Ce) * ((N : ℝ) * saving c N) := by ring
    _ = (Cs + Ce) * (N : ℝ) * saving c N := by ring

/-- Generic version of `main_of_euler_log_four` for an arbitrary exceptional-count
carrier.  This is used by the fixed-numerator application, where the analytic
inputs have the same final shape but the counted set is `E_m(N)` rather than the
ordinary Erdős-Straus exceptional set. -/
theorem main_bound_of_euler_log_four_for
    (target : ℕ → ℕ)
    (Ered : ℕ → ℕ) (Ered_c₁ Ered_C₁ : ℝ)
    (Ered_pos₁ : 0 < Ered_c₁) (Ered_posC₁ : 0 < Ered_C₁)
    (Ered_bound : ∀ N : ℕ, 3 ≤ N →
      (Ered N : ℝ) ≤ Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N))
    (smooth : ℕ → ℝ) (smoothExp smoothC : ℝ)
    (smoothExp_pos : 0 < smoothExp) (smoothExp_lt_one : smoothExp < 1)
    (smoothC_pos : 0 < smoothC)
    (smooth_bound : ∀ N : ℕ, 3 ≤ N → smooth N ≤ smoothC * (N : ℝ) ^ smoothExp)
    (euler : ℕ → ℝ) (eulerC : ℝ) (eulerC_pos : 0 < eulerC)
    (euler_bound_four : ∀ N : ℕ, 3 ≤ N → euler N ≤ eulerC * (Real.log N) ^ (4 : ℕ))
    (lift : ∀ N : ℕ, 3 ≤ N →
      (target N : ℝ) ≤ smooth N + euler N * (Ered N : ℝ)) :
    IsMainBound target := by
  classical
  obtain ⟨cs, hcs, Cs, hCs, hpoly⟩ :=
    poly_absorb smoothExp_pos smoothExp_lt_one smoothC_pos
  obtain ⟨ce, hce, Ce, hCe, hlog⟩ :=
    log_pow_four_absorb Ered_pos₁ eulerC_pos Ered_posC₁
  set c : ℝ := min cs ce with hcdef
  have hc : 0 < c := lt_min hcs hce
  have sav_mono : ∀ (c' : ℝ), c ≤ c' → ∀ N : ℕ, 3 ≤ N →
      (N : ℝ) * saving c' N ≤ (N : ℝ) * saving c N := by
    intro c' hcc' N hN
    have hLpos : 0 < Real.log N := log_pos_of_three_le hN
    have hL34 : 0 ≤ (Real.log N) ^ ((3 : ℝ) / 4) := (Real.rpow_pos_of_pos hLpos _).le
    have hNpos : (0 : ℝ) ≤ N := by positivity
    apply mul_le_mul_of_nonneg_left _ hNpos
    unfold saving
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by linarith : -c' ≤ -c) hL34
  refine ⟨c, hc, Cs + Ce, by positivity, ?_⟩
  intro N hN
  have hlift := lift N hN
  have hsmooth_le : smooth N ≤ Cs * ((N : ℝ) * saving c N) := by
    have h1 : smooth N ≤ smoothC * (N : ℝ) ^ smoothExp := smooth_bound N hN
    have h2 : smoothC * (N : ℝ) ^ smoothExp ≤ Cs * ((N : ℝ) * saving cs N) :=
      hpoly N hN
    have h3 : (N : ℝ) * saving cs N ≤ (N : ℝ) * saving c N :=
      sav_mono cs (min_le_left _ _) N hN
    calc smooth N ≤ Cs * ((N : ℝ) * saving cs N) := h1.trans h2
      _ ≤ Cs * ((N : ℝ) * saving c N) := mul_le_mul_of_nonneg_left h3 hCs.le
  have hreduced_le : euler N * (Ered N : ℝ) ≤ Ce * ((N : ℝ) * saving c N) := by
    have heu : euler N ≤ eulerC * (Real.log N) ^ (4 : ℕ) := euler_bound_four N hN
    have hEr : (Ered N : ℝ) ≤ Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N) :=
      Ered_bound N hN
    have hEr0 : (0 : ℝ) ≤ (Ered N : ℝ) := by positivity
    have hlog_nonneg : 0 ≤ Real.log N := (log_pos_of_three_le hN).le
    have step1 : euler N * (Ered N : ℝ)
        ≤ (eulerC * (Real.log N) ^ (4 : ℕ)) *
            (Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N)) := by
      apply mul_le_mul heu hEr hEr0
      exact mul_nonneg eulerC_pos.le (pow_nonneg hlog_nonneg 4)
    have step2 :
        (eulerC * (Real.log N) ^ (4 : ℕ)) *
            (Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N))
          ≤ Ce * ((N : ℝ) * saving ce N) := by
      simpa [mul_assoc] using hlog N hN
    have step3 : (N : ℝ) * saving ce N ≤ (N : ℝ) * saving c N :=
      sav_mono ce (min_le_right _ _) N hN
    calc euler N * (Ered N : ℝ)
        ≤ (eulerC * (Real.log N) ^ (4 : ℕ)) *
            (Ered_C₁ * ((N : ℝ) * saving Ered_c₁ N)) := step1
      _ ≤ Ce * ((N : ℝ) * saving ce N) := step2
      _ ≤ Ce * ((N : ℝ) * saving c N) := mul_le_mul_of_nonneg_left step3 hCe.le
  calc (target N : ℝ)
      ≤ smooth N + euler N * (Ered N : ℝ) := hlift
    _ ≤ Cs * ((N : ℝ) * saving c N) + Ce * ((N : ℝ) * saving c N) :=
        add_le_add hsmooth_le hreduced_le
    _ = (Cs + Ce) * ((N : ℝ) * saving c N) := by ring
    _ = (Cs + Ce) * (N : ℝ) * saving c N := by ring

/-- **The Erdős–Straus main bound (`thm:main`).** Abbreviation exposing `main`
under the manuscript's name: conditional on `MainInputs`, the exceptional set
satisfies `E(N) ≪ N exp(-c (log N)^{3/4})`. -/
theorem erdos_straus_main (H : MainInputs) : IsMainBound exceptionalCount := main H

end EscAnalytic
