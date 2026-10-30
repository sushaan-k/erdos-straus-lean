import ErdosStraus.Family.Scales
import ErdosStraus.Estimates.Mertens
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic
import ErdosStraus.Estimates.BrunHooley
import ErdosStraus.Basic
import ErdosStraus.Estimates.PartialSummation

/-!
# Lemmas 3.5 and 3.6: primes in arithmetic progressions

For `(a, q) = 1` and `y ≥ 2^16 q`, `π(y; q, a) ≪ y / (φ(q) log(y/q))` (Lemma 3.5). The proof
is the block form of Hooley's almost pure sieve: the primes `p < w = (y/q)^{1/16}` with
`p ∤ q` are split into blocks `w^{2^{-j-1}} ≤ p < w^{2^{-j}}`, each with `∑ 1/p` bounded, and
the main term is controlled by Mertens' product `∏_{p ≤ w} (1 - 1/p) ≪ 1/log w`. Partial
summation over the window `X^β < p ≤ X^{1-σ}` then gives `∑ 1/p ≪ 1/φ(q)` over the primes
`p ≡ a (mod q)`, uniformly for `q ≤ X^ν` with `ν < β` (Lemma 3.6).
-/

/-! ## Mertens' product -/

namespace ErdosStraus.PrimeEstimates

open Filter Finset
open scoped BigOperators Topology

/-- The primes `p ≤ x`. -/
noncomputable def primes (x : ℝ) : Finset ℕ :=
  (Icc 2 ⌊x⌋₊).filter Nat.Prime

/-- Mertens' product `∏_{p ≤ x} (1 - 1/p)`. -/
noncomputable def primeProduct (x : ℝ) : ℝ :=
  ∏ p ∈ primes x, (1 - (p : ℝ)⁻¹)

theorem mem_primes {x : ℝ} {p : ℕ} (hx : 0 ≤ x) :
    p ∈ primes x ↔ p.Prime ∧ (p : ℝ) ≤ x := by
  simp only [primes, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨_, hp⟩, hprime⟩
    exact ⟨hprime, (Nat.le_floor_iff hx).mp hp⟩
  · rintro ⟨hprime, hp⟩
    exact ⟨⟨hprime.two_le, (Nat.le_floor_iff hx).mpr hp⟩, hprime⟩

theorem primeProduct_pos (x : ℝ) : 0 < primeProduct x := by
  apply Finset.prod_pos
  intro p hp
  have hprime := (Finset.mem_filter.mp hp).2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
  exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)

theorem primeProduct_le_one (x : ℝ) : primeProduct x ≤ 1 := by
  apply Finset.prod_le_one
  · intro p hp
    have hprime := (Finset.mem_filter.mp hp).2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
    exact (sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)).le
  · intro p hp
    exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg p))

theorem primeProduct_antitone : Antitone primeProduct := by
  intro x y hxy
  unfold primeProduct
  have hs : primes x ⊆ primes y := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpi, hprime⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hpi).1,
        (Finset.mem_Icc.mp hpi).2.trans (Nat.floor_mono hxy)⟩, hprime⟩
  have he : (∏ p ∈ primes y \ primes x, (1 - (p : ℝ)⁻¹)) ≤ 1 := by
    apply Finset.prod_le_one
    · intro p hp
      have hprime := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
      exact (sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)).le
    · intro p hp
      exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg p))
  calc
    (∏ p ∈ primes y, (1 - (p : ℝ)⁻¹)) =
        (∏ p ∈ primes y \ primes x, (1 - (p : ℝ)⁻¹)) *
          ∏ p ∈ primes x, (1 - (p : ℝ)⁻¹) := (Finset.prod_sdiff hs).symm
    _ ≤ 1 * ∏ p ∈ primes x, (1 - (p : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right he (primeProduct_pos x).le
    _ = _ := one_mul _

theorem primeProduct_zScale (X : ℝ) :
    primeProduct (zScale X) = Estimates.roughDyadicBadPrimeMainEulerProduct X := by
  simp [primeProduct, primes, Estimates.roughDyadicBadPrimeMainEulerProduct,
    Estimates.roughModulus, Estimates.primeProductBelow_primeFactors_eq]

private theorem zScale_exp_root {w : ℝ} (hw : 0 ≤ w) :
    zScale (Real.exp (w ^ (1 / 4 : ℝ))) = w := by
  rw [zScale, Real.log_exp, ← Real.rpow_natCast,
    ← Real.rpow_mul hw]
  norm_num

private theorem root_exp_tendsto :
    Tendsto (fun w : ℝ => Real.exp (w ^ (1 / 4 : ℝ))) atTop atTop :=
  Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop (by norm_num))

/-- `∏_{p ≤ w} (1 - 1/p) ≪ 1/log w` for large `w`: apply the bound at `z = (log X)^4` with
`X = exp(w^{1/4})`. -/
theorem primeProduct_eventual_upper :
    ∃ C > 0, ∀ᶠ w : ℝ in atTop, primeProduct w ≤ C / Real.log w := by
  obtain ⟨C, X₀, hC, hbound⟩ :=
    Estimates.roughEulerProduct_upper
  refine ⟨C, hC, ?_⟩
  filter_upwards [root_exp_tendsto.eventually (eventually_ge_atTop X₀),
    eventually_ge_atTop (0 : ℝ)] with w hw hw0
  have hz := zScale_exp_root hw0
  have h := hbound (Real.exp (w ^ (1 / 4 : ℝ))) hw
  rwa [← primeProduct_zScale, hz] at h

/-- `∏_{p ≤ w} (1 - 1/p) ≫ 1/log w` for large `w`. -/
theorem primeProduct_eventual_lower :
    ∃ c > 0, ∀ᶠ w : ℝ in atTop, c / Real.log w ≤ primeProduct w := by
  obtain ⟨c, X₀, hc, hbound⟩ :=
    Estimates.roughEulerProduct_lower_of_mertensDefect
      Mertens.sharp_upper
  refine ⟨c, hc, ?_⟩
  filter_upwards [root_exp_tendsto.eventually (eventually_ge_atTop X₀),
    eventually_ge_atTop (0 : ℝ)] with w hw hw0
  have hz := zScale_exp_root hw0
  have h := hbound (Real.exp (w ^ (1 / 4 : ℝ))) hw
  rwa [← primeProduct_zScale, hz] at h

theorem primeProduct_upper :
    ∃ C > 0, ∀ w : ℝ, 2 ≤ w → primeProduct w ≤ C / Real.log w := by
  obtain ⟨C, hC, hbound⟩ := primeProduct_eventual_upper
  obtain ⟨W, hW⟩ := eventually_atTop.1 hbound
  let T := max 2 W
  refine ⟨max C (Real.log T), lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
  intro w hw
  have hw1 : 1 < w := lt_of_lt_of_le (by norm_num) hw
  have hlog := Real.log_pos hw1
  by_cases ht : T ≤ w
  · exact (hW w ((le_max_right _ _).trans ht)).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) hlog.le)
  · have hwt : w ≤ T := le_of_not_ge ht
    have hlogle : Real.log w ≤ max C (Real.log T) :=
      (Real.log_le_log (by positivity) hwt).trans (le_max_right _ _)
    exact (primeProduct_le_one w).trans ((le_div_iff₀ hlog).mpr (by
      simpa only [one_mul] using hlogle))

theorem primeProduct_inv_upper :
    ∃ C > 0, ∀ w : ℝ, 2 ≤ w → (primeProduct w)⁻¹ ≤ C * Real.log (2 * w) := by
  obtain ⟨c, hc, hbound⟩ := primeProduct_eventual_lower
  obtain ⟨W, hW⟩ := eventually_atTop.1 hbound
  let T := max 2 W
  let C := max c⁻¹ ((primeProduct T)⁻¹ / Real.log 4)
  refine ⟨C, lt_of_lt_of_le (inv_pos.mpr hc) (le_max_left _ _), ?_⟩
  intro w hw
  have hwp := primeProduct_pos w
  have hlog := Real.log_pos (lt_of_lt_of_le (by norm_num) hw)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog2w : 0 < Real.log (2 * w) := Real.log_pos (by linarith)
  by_cases ht : T ≤ w
  · have hlow := hW w ((le_max_right _ _).trans ht)
    have hinv := inv_anti₀ (div_pos hc hlog) hlow
    have hlogle : Real.log w ≤ Real.log (2 * w) :=
      Real.log_le_log (by positivity) (by linarith)
    calc
      (primeProduct w)⁻¹ ≤ (c / Real.log w)⁻¹ := hinv
      _ = c⁻¹ * Real.log w := by field_simp
      _ ≤ c⁻¹ * Real.log (2 * w) := mul_le_mul_of_nonneg_left hlogle (by positivity)
      _ ≤ C * Real.log (2 * w) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hlog2w.le
  · have hwt : w ≤ T := le_of_not_ge ht
    have hinv := inv_anti₀ (primeProduct_pos T) (primeProduct_antitone hwt)
    have hlogle : Real.log 4 ≤ Real.log (2 * w) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hC : (primeProduct T)⁻¹ / Real.log 4 ≤ C := le_max_right _ _
    calc
      (primeProduct w)⁻¹ ≤ (primeProduct T)⁻¹ := hinv
      _ = ((primeProduct T)⁻¹ / Real.log 4) * Real.log 4 := by
        rw [div_mul_cancel₀ _ hlog4.ne']
      _ ≤ C * Real.log 4 := mul_le_mul_of_nonneg_right hC hlog4.le
      _ ≤ C * Real.log (2 * w) :=
        mul_le_mul_of_nonneg_left hlogle
          (le_trans (inv_nonneg.mpr hc.le) (le_max_left _ _))

private theorem product_le_subset {s t : Finset ℕ} (hst : s ⊆ t)
    (ht : ∀ p ∈ t, p.Prime) :
    (∏ p ∈ t, (1 - (p : ℝ)⁻¹)) ≤ ∏ p ∈ s, (1 - (p : ℝ)⁻¹) := by
  have hp : ∀ p ∈ t, 0 < 1 - (p : ℝ)⁻¹ := by
    intro p hp
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ (by exact_mod_cast (ht p hp).one_lt))
  rw [← Finset.prod_sdiff hst]
  have hleft : (∏ p ∈ t \ s, (1 - (p : ℝ)⁻¹)) ≤ 1 := by
    apply Finset.prod_le_one
    · intro p hpm
      exact (hp p (Finset.mem_sdiff.mp hpm).1).le
    · intro p hpm
      exact sub_le_self _ (by positivity)
  have hright : 0 ≤ ∏ p ∈ s, (1 - (p : ℝ)⁻¹) :=
    Finset.prod_nonneg (fun p hpm => (hp p (hst hpm)).le)
  exact (mul_le_mul_of_nonneg_right hleft hright).trans_eq (one_mul _)

/-- There is an absolute `B` with `∑_{p ∈ S} 1/p ≤ B` for every set `S` of primes in
`[v, v²)`, `v ≥ 2`. For `v ≥ 4`, `∏_{p ∈ S} (1 - 1/p)⁻¹` is at most
`∏_{p ≤ v/2} (1 - 1/p) / ∏_{p ≤ v²} (1 - 1/p) ≪ 1`. -/
theorem block_harmonic_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (v : ℝ) (S : Finset ℕ), 2 ≤ v →
      (∀ p ∈ S, p.Prime ∧ v ≤ (p : ℝ) ∧ (p : ℝ) < v ^ 2) →
      (∑ p ∈ S, (p : ℝ)⁻¹) ≤ B := by
  classical
  obtain ⟨C, hC, hupper⟩ := primeProduct_upper
  obtain ⟨D, hD, hinverse⟩ := primeProduct_inv_upper
  refine ⟨max 16 (Real.log (6 * C * D)), le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro v S hv hS
  by_cases hv4 : 4 ≤ v
  · let A := primes (v / 2)
    let T := primes (v ^ 2)
    let V : ℝ := ∏ p ∈ S, (1 - (p : ℝ)⁻¹)
    have hvpos : 0 < v := by linarith
    have hVp : 0 < V := Finset.prod_pos (fun p hp =>
      sub_pos.mpr (inv_lt_one_of_one_lt₀ (by exact_mod_cast (hS p hp).1.one_lt)))
    have hdis : Disjoint A S := by
      apply Finset.disjoint_left.mpr
      intro p hp hps
      have hpa := (mem_primes (by positivity)).mp hp
      have hpb := (hS p hps).2.1
      linarith
    have hsub : A ∪ S ⊆ T := by
      intro p hp
      apply (mem_primes (sq_nonneg v)).mpr
      rcases Finset.mem_union.mp hp with hp | hp
      · have hpa := (mem_primes (by positivity)).mp hp
        exact ⟨hpa.1, hpa.2.trans (by nlinarith)⟩
      · exact ⟨(hS p hp).1, (hS p hp).2.2.le⟩
    have hprod : primeProduct (v ^ 2) ≤ primeProduct (v / 2) * V := by
      have h := product_le_subset hsub (fun p hp => (mem_primes (sq_nonneg v)).mp hp |>.1)
      simpa only [Finset.prod_union hdis, A, V, T, primeProduct] using h
    have hratio : V⁻¹ ≤ primeProduct (v / 2) * (primeProduct (v ^ 2))⁻¹ := by
      rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ hVp (primeProduct_pos _)]
      simpa only [one_mul] using hprod
    have hlogv : 0 < Real.log v := Real.log_pos (by linarith)
    have hloghalf : 0 < Real.log (v / 2) := Real.log_pos (by linarith)
    have hloglower : Real.log v / 2 ≤ Real.log (v / 2) := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hv4
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h
      rw [Real.log_div hvpos.ne' (by norm_num)]
      norm_num only [Nat.cast_ofNat] at h
      linarith
    have hlogupper : Real.log (2 * v ^ 2) ≤ 3 * Real.log v := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hv
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith
    have hscalar : primeProduct (v / 2) * (primeProduct (v ^ 2))⁻¹ ≤ 6 * C * D := by
      have hu := hupper (v / 2) (by linarith)
      have hi := hinverse (v ^ 2) (by nlinarith)
      calc
        primeProduct (v / 2) * (primeProduct (v ^ 2))⁻¹ ≤
            (C / Real.log (v / 2)) * (D * Real.log (2 * v ^ 2)) :=
          mul_le_mul hu hi (inv_nonneg.mpr (primeProduct_pos _).le) (by positivity)
        _ ≤ (C / (Real.log v / 2)) * (D * (3 * Real.log v)) := by
          apply mul_le_mul
          · exact div_le_div_of_nonneg_left hC.le (by positivity) hloglower
          · exact mul_le_mul_of_nonneg_left hlogupper hD.le
          · exact mul_nonneg hD.le (Real.log_nonneg (by nlinarith))
          · positivity
        _ = 6 * C * D := by field_simp; ring
    have hlog : (∑ p ∈ S, (p : ℝ)⁻¹) ≤ Real.log V⁻¹ := by
      rw [show V⁻¹ = ∏ p ∈ S, (1 - (p : ℝ)⁻¹)⁻¹ by
        simp only [V, Finset.prod_inv_distrib], Real.log_prod]
      · apply Finset.sum_le_sum
        intro p hp
        have hpp : 0 < 1 - (p : ℝ)⁻¹ :=
          sub_pos.mpr (inv_lt_one_of_one_lt₀ (by exact_mod_cast (hS p hp).1.one_lt))
        have h := Real.one_sub_inv_le_log_of_pos (inv_pos.mpr hpp)
        simpa only [inv_inv, sub_sub_cancel] using h
      · intro p hp
        have hpp : 0 < 1 - (p : ℝ)⁻¹ :=
          sub_pos.mpr (inv_lt_one_of_one_lt₀ (by exact_mod_cast (hS p hp).1.one_lt))
        exact (inv_pos.mpr hpp).ne'
    exact hlog.trans ((Real.log_le_log (inv_pos.mpr hVp)
      (hratio.trans hscalar)).trans (le_max_right _ _))
  · have hs : S ⊆ Finset.range 16 := by
      intro p hp
      have hpv := (hS p hp).2.2
      apply Finset.mem_range.mpr
      have h : (p : ℝ) < 16 := by nlinarith [le_of_not_ge hv4]
      exact_mod_cast h
    have hsum : (∑ p ∈ S, (p : ℝ)⁻¹) ≤ ∑ p ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact inv_le_one_of_one_le₀ (by exact_mod_cast (hS p hp).1.one_le)
    have hc : (S.card : ℝ) ≤ 16 := by
      have h := Finset.card_le_card hs
      simpa only [Finset.card_range, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr h
    exact hsum.trans ((by simpa using hc) : (∑ p ∈ S, (1 : ℝ)) ≤ 16) |>.trans (le_max_left _ _)

end ErdosStraus.PrimeEstimates

namespace ErdosStraus.BrunHooley

/-! ## Blocks of small primes -/

section

open Classical Filter
open scoped BigOperators Topology

/-- The block scales `w_j = w^{2^{-j}}`. -/
noncomputable def blockScale (w : ℝ) (j : ℕ) : ℝ :=
  w ^ ((2 : ℝ) ^ j)⁻¹

@[simp] theorem blockScale_zero (w : ℝ) : blockScale w 0 = w := by
  simp [blockScale]

theorem blockScale_antitone (w : ℝ) (hw : 1 ≤ w) : Antitone (blockScale w) := by
  intro i j hij
  apply Real.rpow_le_rpow_of_exponent_le hw
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hij)

theorem blockScale_square (w : ℝ) (hw : 0 ≤ w) (j : ℕ) :
    blockScale w (j + 1) ^ 2 = blockScale w j := by
  rw [blockScale, ← Real.rpow_natCast, ← Real.rpow_mul hw]
  congr 1
  rw [pow_succ]
  field_simp
  ring

theorem exists_blockScale_le_two (w : ℝ) (hw : 0 < w) :
    ∃ j, blockScale w j ≤ 2 := by
  have hp : Tendsto (fun j : ℕ => ((2 : ℝ) ^ j)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1))
  have ht : Tendsto (blockScale w) atTop (𝓝 1) := by
    unfold blockScale
    simpa [Function.comp_def] using (Real.continuousAt_const_rpow hw.ne').tendsto.comp hp
  have he := ht.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))
  obtain ⟨j, hj⟩ := he.exists
  exact ⟨j, hj.le⟩

/-- The first `J` with `w_J ≤ 2`. -/
noncomputable def blockStop (w : ℝ) (hw : 0 < w) : ℕ :=
  Nat.find (exists_blockScale_le_two w hw)

theorem blockStop_terminal (w : ℝ) (hw : 0 < w) :
    blockScale w (blockStop w hw) ≤ 2 :=
  Nat.find_spec (exists_blockScale_le_two w hw)

/-- The primes `p < w` with `p ∤ q`. -/
noncomputable def primeSupport (w : ℝ) (q : ℕ) : Finset ℕ :=
  (Finset.range (⌊w⌋₊ + 1)).filter
    (fun p => Nat.Prime p ∧ (p : ℝ) < w ∧ ¬p ∣ q)

@[simp] theorem mem_primeSupport {w : ℝ} {q p : ℕ} :
    p ∈ primeSupport w q ↔ Nat.Prime p ∧ (p : ℝ) < w ∧ ¬p ∣ q := by
  simp only [primeSupport, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact And.right
  · intro h
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor h.2.1.le), h⟩

/-- The block of primes `p < w` with `p ∤ q` and `max(2, w_{j+1}) ≤ p < w_j`, for `j < J`. -/
noncomputable def primeBlocks (w : ℝ) (q J : ℕ) (j : Fin J) : Finset ℕ :=
  (primeSupport w q).filter (fun p =>
    max 2 (blockScale w ((j : ℕ) + 1)) ≤ (p : ℝ) ∧ (p : ℝ) < blockScale w j)

@[simp] theorem mem_primeBlocks {w : ℝ} {q J p : ℕ} {j : Fin J} :
    p ∈ primeBlocks w q J j ↔
      Nat.Prime p ∧ (p : ℝ) < w ∧ ¬p ∣ q ∧
        max 2 (blockScale w ((j : ℕ) + 1)) ≤ (p : ℝ) ∧
          (p : ℝ) < blockScale w j := by
  simp only [primeBlocks, Finset.mem_filter, mem_primeSupport]
  tauto

theorem primeBlocks_disjoint (w : ℝ) (hw : 1 ≤ w) (q J : ℕ) :
    Pairwise (fun j k => Disjoint (primeBlocks w q J j) (primeBlocks w q J k)) := by
  intro j k hjk
  apply Finset.disjoint_left.mpr
  intro p hpj hpk
  have hj := (mem_primeBlocks.mp hpj).2.2.2
  have hk := (mem_primeBlocks.mp hpk).2.2.2
  have hne : (j : ℕ) ≠ k := fun h => hjk (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hscale := blockScale_antitone w hw (Nat.succ_le_iff.mpr hlt)
    have hlower := (le_max_right 2 (blockScale w ((j : ℕ) + 1))).trans hj.1
    linarith [hk.2]
  · have hscale := blockScale_antitone w hw (Nat.succ_le_iff.mpr hgt)
    have hlower := (le_max_right 2 (blockScale w ((k : ℕ) + 1))).trans hk.1
    linarith [hj.2]

theorem primeBlocks_cover (w : ℝ) (q J : ℕ) (hstop : blockScale w J ≤ 2) :
    (Finset.univ.biUnion (primeBlocks w q J)) = primeSupport w q := by
  ext p
  constructor
  · intro hp
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp hj).1
  · intro hp
    have hp' := mem_primeSupport.mp hp
    have htwo : (2 : ℝ) ≤ p := by exact_mod_cast hp'.1.two_le
    have hex : ∃ k, blockScale w k ≤ (p : ℝ) := ⟨J, hstop.trans htwo⟩
    let k := Nat.find hex
    have hk : blockScale w k ≤ (p : ℝ) := Nat.find_spec hex
    have hkpos : 0 < k := by
      by_contra h
      have he : k = 0 := by omega
      simpa [he] using hk.trans_lt hp'.2.1
    have hkJ : k ≤ J := Nat.find_min' hex (hstop.trans htwo)
    have hprev : (p : ℝ) < blockScale w (k - 1) :=
      lt_of_not_ge (Nat.find_min hex (by omega : k - 1 < k))
    refine Finset.mem_biUnion.mpr ⟨⟨k - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨hp, ?_, hprev⟩
    rw [show k - 1 + 1 = k by omega]
    exact max_le htwo hk

theorem primeBlocks_primes (w : ℝ) (q J : ℕ) :
    ∀ j p, p ∈ primeBlocks w q J j → Nat.Prime p :=
  fun _ _ hp => (mem_primeBlocks.mp hp).1

theorem primeBlocks_coprime (w : ℝ) (q J : ℕ) :
    ∀ j p, p ∈ primeBlocks w q J j → Nat.Coprime q p := by
  intro j p hp
  have h := mem_primeBlocks.mp hp
  exact h.1.coprime_iff_not_dvd.mpr h.2.2.1 |>.symm

theorem primeBlocks_bound (w : ℝ) (q J : ℕ) :
    ∀ j p, p ∈ primeBlocks w q J j →
      (p : ℝ) ≤ w ^ ((2 : ℝ) ^ (j : ℕ))⁻¹ :=
  fun _ _ hp => (mem_primeBlocks.mp hp).2.2.2.2.le

end

/-! ## The block sieve bound -/

section

open Classical
open scoped BigOperators

/-- The primes `p ≤ y` with `p ≡ a (mod q)`; their number is `π(y; q, a)`. -/
noncomputable def primePrefix (y : ℝ) (q a : ℕ) : Finset ℕ :=
  (Finset.range (⌊y⌋₊ + 1)).filter (fun p => Nat.Prime p ∧ p ≡ a [MOD q])

@[simp] theorem mem_primePrefix {y : ℝ} {q a p : ℕ} :
    p ∈ primePrefix y q a ↔ p ≤ ⌊y⌋₊ ∧ Nat.Prime p ∧ p ≡ a [MOD q] := by
  simp only [primePrefix, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

/-- A prime `p ≥ w` has no prime factor in the blocks, and at most `⌊w⌋ + 1` primes are
smaller than `w`. -/
theorem primePrefix_card_le_sift_add (y w : ℝ) (q a J : ℕ) :
    (primePrefix y q a).card ≤
      (((Finset.Ico 0 (⌊y⌋₊ + 1)).filter (fun n => n ≡ a [MOD q])).filter
        (fun n => ∀ j p, p ∈ primeBlocks w q J j → ¬p ∣ n)).card + (⌊w⌋₊ + 1) := by
  let A := ((Finset.Ico 0 (⌊y⌋₊ + 1)).filter (fun n => n ≡ a [MOD q])).filter
    (fun n => ∀ j p, p ∈ primeBlocks w q J j → ¬p ∣ n)
  have hsub : primePrefix y q a ⊆ A ∪ Finset.range (⌊w⌋₊ + 1) := by
    intro p hp
    have hp' := mem_primePrefix.mp hp
    by_cases hpw : (p : ℝ) < w
    · exact Finset.mem_union_right _ (Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Nat.le_floor hpw.le)))
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨Nat.zero_le _,
        Nat.lt_succ_of_le hp'.1⟩, hp'.2.2⟩, ?_⟩
      intro j r hr hdiv
      have hr' := mem_primeBlocks.mp hr
      have he : r = p := (Nat.prime_dvd_prime_iff_eq hr'.1 hp'.2.1).mp hdiv
      exact hpw (he ▸ hr'.2.1)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans_eq (by simp [A]))

theorem block_euler_eq_support (w : ℝ) (hw : 1 ≤ w) (q J : ℕ)
    (hstop : blockScale w J ≤ 2) :
    (∏ j : Fin J, ∏ p ∈ primeBlocks w q J j, (1 - (p : ℝ)⁻¹)) =
      ∏ p ∈ primeSupport w q, (1 - (p : ℝ)⁻¹) := by
  rw [← primeBlocks_cover w q J hstop]
  symm
  exact Finset.prod_biUnion (fun j _ k _ hjk => primeBlocks_disjoint w hw q J hjk)

/-- If every block has `∑ 1/p ≤ H`, then `π(y; q, a)` is at most
`((⌊y⌋ + 1)/q) ∏_{p < w, p ∤ q} (1 - 1/p) · exp(e^H / e^{-2H}) + 2⌊w⁸⌋ + ⌊w⌋ + 1`. -/
theorem primePrefix_block_upper (y w : ℝ) (q a J : ℕ) (hw : 1 ≤ w)
    (hq : 0 < q) (hstop : blockScale w J ≤ 2)
    (H : ℝ) (hH : 0 ≤ H)
    (hSum : ∀ j, (∑ p ∈ primeBlocks w q J j, (p : ℝ)⁻¹) ≤ H) :
    ((primePrefix y q a).card : ℝ) ≤
      (((⌊y⌋₊ : ℝ) + 1) / q) *
        (∏ p ∈ primeSupport w q, (1 - (p : ℝ)⁻¹)) *
          Real.exp (Real.exp H / Real.exp (-2 * H)) +
        2 * (⌊w ^ 8⌋₊ : ℝ) + ((⌊w⌋₊ : ℝ) + 1) := by
  have hc : ((primePrefix y q a).card : ℝ) ≤
      (((((Finset.Ico 0 (⌊y⌋₊ + 1)).filter (fun n => n ≡ a [MOD q])).filter
        (fun n => ∀ j p, p ∈ primeBlocks w q J j → ¬p ∣ n)).card : ℝ)) +
          ((⌊w⌋₊ : ℝ) + 1) := by
    exact_mod_cast primePrefix_card_le_sift_add y w q a J
  have hs := geometric_progression_euler_upper J (primeBlocks w q J)
    (primeBlocks_primes w q J) (primeBlocks_disjoint w hw q J)
    w hw (primeBlocks_bound w q J) H hH hSum 0 (⌊y⌋₊ + 1) q a
    (Nat.zero_le _) hq (primeBlocks_coprime w q J)
  rw [block_euler_eq_support w hw q J hstop] at hs
  exact hc.trans (by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero] using
      add_le_add_left hs ((⌊w⌋₊ : ℝ) + 1))

/-- Dropping the condition `p ∤ q` costs at most the factor `q/φ(q)`. -/
theorem support_euler_le_totient_mul (w : ℝ) (q : ℕ) (hq : 0 < q) :
    (∏ p ∈ primeSupport w q, (1 - (p : ℝ)⁻¹)) ≤
      ((q : ℝ) / Nat.totient q) *
        (∏ p ∈ primeSupport w 1, (1 - (p : ℝ)⁻¹)) := by
  let f : ℕ → ℝ := fun p => 1 - (p : ℝ)⁻¹
  have hf (p : ℕ) (hp : Nat.Prime p) : 0 < f p ∧ f p ≤ 1 := by
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact ⟨sub_pos.mpr (inv_lt_one_of_one_lt₀ hpR),
      sub_le_self _ (by positivity)⟩
  have hone (p : ℕ) (hp : Nat.Prime p) : ¬p ∣ 1 := hp.not_dvd_one
  have hgood : (primeSupport w 1).filter (fun p => ¬p ∣ q) = primeSupport w q := by
    ext p
    simp only [Finset.mem_filter, mem_primeSupport]
    constructor
    · tauto
    · intro h
      exact ⟨⟨h.1, h.2.1, hone p h.1⟩, h.2.2⟩
  have hbad : (primeSupport w 1).filter (fun p => p ∣ q) =
      q.primeFactors.filter (fun p : ℕ => (p : ℝ) < w) := by
    ext p
    simp only [Finset.mem_filter, mem_primeSupport, Nat.mem_primeFactors_of_ne_zero hq.ne']
    constructor
    · tauto
    · intro h
      exact ⟨⟨h.1.1, h.2, hone p h.1.1⟩, h.1.2⟩
  have hprod : (∏ p ∈ primeSupport w 1, f p) =
      (∏ p ∈ primeSupport w q, f p) *
        (∏ p ∈ q.primeFactors.filter (fun p : ℕ => (p : ℝ) < w), f p) := by
    rw [← hgood, ← hbad]
    simpa only [not_not] using
      (Finset.prod_filter_mul_prod_filter_not (primeSupport w 1) (fun p => ¬p ∣ q) f).symm
  have hφ : (Nat.totient q : ℝ) = (q : ℝ) * ∏ p ∈ q.primeFactors, f p := by
    have h := congrArg (fun r : ℚ => (r : ℝ)) (Nat.totient_eq_mul_prod_factors q)
    simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub,
      Rat.cast_one, Rat.cast_inv] using h
  have hsub : (∏ p ∈ q.primeFactors, f p) ≤
      ∏ p ∈ q.primeFactors.filter (fun p : ℕ => (p : ℝ) < w), f p := by
    rw [Finset.prod_filter]
    apply Finset.prod_le_prod
    · intro p hp
      exact (hf p (Nat.prime_of_mem_primeFactors hp)).1.le
    · intro p hp
      split_ifs
      · exact le_rfl
      · exact (hf p (Nat.prime_of_mem_primeFactors hp)).2
  have hnonneg : 0 ≤ ∏ p ∈ primeSupport w q, f p :=
    Finset.prod_nonneg (fun p hp => (hf p (mem_primeSupport.mp hp).1).1.le)
  have hmul := mul_le_mul_of_nonneg_left hsub hnonneg
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hφR : (0 : ℝ) < Nat.totient q := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  change (∏ p ∈ primeSupport w q, f p) ≤
    (q : ℝ) / Nat.totient q * (∏ p ∈ primeSupport w 1, f p)
  rw [hprod, div_mul_eq_mul_div, le_div_iff₀ hφR, hφ]
  nlinarith

end

/-! ## From prime counts to reciprocal sums -/

section

open Estimates
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Partial summation: if `π(y; q, a) ≤ K y/(φ(q) log(y/q))` whenever `y/q ≥ 2^16`, then the
primes `p ≡ a (mod q)` with `T < p ≤ V` satisfy
`∑ 1/p ≤ (K/(φ(q) log(T/q))) (2 + log((V + 1)/T))`. -/
theorem prime_window_reciprocal_of_prefix (K : ℝ) (hK : 0 ≤ K)
    (hprefix : ∀ (y : ℝ) (q a : ℕ), 0 < q → (2 : ℝ) ^ 16 ≤ y / q →
      ((primePrefix y q a).card : ℝ) ≤
        K * y / ((Nat.totient q : ℝ) * Real.log (y / q)))
    (q a : ℕ) (hq : 0 < q) (T V : ℝ) (hT : 0 < T) (hTV : T ≤ V)
    (hTq : (2 : ℝ) ^ 16 ≤ T / q) :
    (∑ p ∈ (natWindow T V).filter (fun p => Nat.Prime p ∧ p ≡ a [MOD q]),
      (1 : ℝ) / p) ≤
      (K / ((Nat.totient q : ℝ) * Real.log (T / q))) *
        (2 + Real.log ((V + 1) / T)) := by
  classical
  let L := ⌊T⌋₊ + 1
  let U := ⌊V⌋₊ + 1
  let α := K / ((Nat.totient q : ℝ) * Real.log (T / q))
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hφ : (0 : ℝ) < Nat.totient q := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hlog : 0 < Real.log (T / q) := Real.log_pos (lt_of_lt_of_le (by norm_num) hTq)
  have hα : 0 ≤ α := div_nonneg hK (mul_pos hφ hlog).le
  have hL : 0 < L := by dsimp [L]; omega
  have hLU : L ≤ U := Nat.add_le_add_right (Nat.floor_le_floor hTV) 1
  have hTL : T ≤ (L : ℝ) := by
    simpa only [L, Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one T).le
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hUU : (U : ℝ) ≤ V + 1 := by
    dsimp [U]
    push_cast
    exact add_le_add_left (Nat.floor_le (hT.le.trans hTV)) 1
  have hcount : ∀ W, L ≤ W → W ≤ U →
      (((Finset.Ico L W).filter (fun p => Nat.Prime p ∧ p ≡ a [MOD q])).card : ℝ) ≤
        ((W : ℝ) - L) * α + α * L := by
    intro W hLW hWU
    have hTW : T ≤ (W : ℝ) := hTL.trans (Nat.cast_le.mpr hLW)
    have hqW : T / (q : ℝ) ≤ (W : ℝ) / q := div_le_div_of_nonneg_right hTW hqR.le
    have hlogW : Real.log (T / q) ≤ Real.log ((W : ℝ) / q) :=
      Real.log_le_log (div_pos hT hqR) hqW
    have hsub : (Finset.Ico L W).filter (fun p => Nat.Prime p ∧ p ≡ a [MOD q]) ⊆
        primePrefix (W : ℝ) q a := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      apply mem_primePrefix.mpr
      refine ⟨?_, hp'.2⟩
      simpa only [Nat.floor_natCast] using (Finset.mem_Ico.mp hp'.1).2.le
    have hcard : (((Finset.Ico L W).filter
        (fun p => Nat.Prime p ∧ p ≡ a [MOD q])).card : ℝ) ≤
          ((primePrefix (W : ℝ) q a).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    calc
      _ ≤ K * (W : ℝ) / ((Nat.totient q : ℝ) * Real.log ((W : ℝ) / q)) :=
        hcard.trans (hprefix W q a hq (hTq.trans hqW))
      _ ≤ K * (W : ℝ) / ((Nat.totient q : ℝ) * Real.log (T / q)) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hφ hlog)
          (mul_le_mul_of_nonneg_left hlogW hφ.le)
      _ = _ := by dsimp [α]; ring
  have hs := SieveEstimates.reciprocal_Ico_le_of_count_le
    (fun p => Nat.Prime p ∧ p ≡ a [MOD q]) L U hL hLU α (α * L)
    (mul_nonneg hα (Nat.cast_nonneg _)) hcount
  have hsum := SieveEstimates.sum_Ico_reciprocal_le_log L U hL hLU
  have hlogU : Real.log ((U : ℝ) / L) ≤ Real.log ((V + 1) / T) := by
    apply Real.log_le_log (div_pos (by exact_mod_cast (hL.trans_le hLU))
      (by exact_mod_cast hL))
    exact div_le_div₀ (by linarith) hUU hT hTL
  have hinvL : (1 : ℝ) / L ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hL1
  rw [SieveEstimates.natWindow_eq_Ico hT.le]
  change (∑ p ∈ (Finset.Ico L U).filter
    (fun p => Nat.Prime p ∧ p ≡ a [MOD q]), (1 : ℝ) / p) ≤ _
  apply hs.trans
  have hsum' : (∑ p ∈ Finset.Ico L U, (1 : ℝ) / p) ≤
      1 + Real.log ((V + 1) / T) := hsum.trans (add_le_add hinvL hlogU)
  have he : α * (L : ℝ) / L = α := by
    exact mul_div_cancel_right₀ α (Nat.cast_ne_zero.mpr hL.ne')
  rw [he]
  calc
    _ ≤ α * (1 + Real.log ((V + 1) / T)) + α :=
      add_le_add_left (mul_le_mul_of_nonneg_left hsum' hα) _
    _ = _ := by dsimp [α]; ring

/-- On the window `X^β < p ≤ X^{1-σ}` the same hypothesis gives `∑ 1/p ≪ 1/φ(q)` for
`q ≤ X^ν`, `ν < β`. -/
theorem prime_power_window_reciprocal_of_prefix (K : ℝ) (hK : 0 < K)
    (hprefix : ∀ (y : ℝ) (q a : ℕ), 0 < q → (2 : ℝ) ^ 16 ≤ y / q →
      ((primePrefix y q a).card : ℝ) ≤
        K * y / ((Nat.totient q : ℝ) * Real.log (y / q))) :
    ∀ P : Params, ∀ ν : ℝ, 0 < ν → ν < P.β →
      ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        ∀ q a : ℕ, 1 ≤ q → (q : ℝ) ≤ X ^ ν → Nat.Coprime a q →
          (∑ p ∈ (natWindow (X ^ P.β) (X ^ (1 - P.σ))).filter
            (fun p => Nat.Prime p ∧ congMod p a q), (1 : ℝ) / p) ≤
              C / (Nat.totient q : ℝ) := by
  intro P ν _hν hνβ
  let δ := P.β - ν
  have hδ : 0 < δ := sub_pos.mpr hνβ
  refine ⟨4 * K / δ, max (Real.exp 1) (Real.exp (16 / δ)), by positivity, ?_⟩
  intro X hX q a hq hqX _ha
  have hX1exp : Real.exp 1 ≤ X := (le_max_left _ _).trans hX
  have hXδexp : Real.exp (16 / δ) ≤ X := (le_max_right _ _).trans hX
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX1exp
  have hlogX : 1 ≤ Real.log X := (Real.le_log_iff_exp_le hX0).mpr hX1exp
  have hlogXδ : 16 / δ ≤ Real.log X := (Real.le_log_iff_exp_le hX0).mpr hXδexp
  have hX1 : 1 ≤ X := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hq0 : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq0
  have hφ : (0 : ℝ) < Nat.totient q := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq0)
  have hT : 0 < X ^ P.β := Real.rpow_pos_of_pos hX0 _
  have hTV : X ^ P.β ≤ X ^ (1 - P.σ) :=
    Real.rpow_le_rpow_of_exponent_le hX1 P.β_lt_one_sub_σ.le
  have hlogq : Real.log q ≤ ν * Real.log X := by
    have h := Real.log_le_log hqR hqX
    rwa [Real.log_rpow hX0] at h
  have hloglower : δ * Real.log X ≤ Real.log (X ^ P.β / q) := by
    rw [Real.log_div hT.ne' hqR.ne', Real.log_rpow hX0]
    dsimp [δ]
    linarith
  have hδlog : 16 ≤ δ * Real.log X := by
    have h := (div_le_iff₀ hδ).mp hlogXδ
    nlinarith
  have hTq : (2 : ℝ) ^ 16 ≤ X ^ P.β / q := by
    apply (Real.log_le_log_iff (by positivity) (div_pos hT hqR)).mp
    rw [Real.log_pow]
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hlog2 ⊢
    have hh : 16 * Real.log 2 ≤ (16 : ℝ) := by
      simpa using (mul_le_mul_of_nonneg_left hlog2 (by norm_num : (0 : ℝ) ≤ 16))
    exact hh.trans (hδlog.trans hloglower)
  have hlogTq : 0 < Real.log (X ^ P.β / q) := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 16) (hδlog.trans hloglower)
  have hupper : X ^ (1 - P.σ) ≤ X := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX1
      (show 1 - P.σ ≤ 1 by linarith [P.σ_pos])
  have hTone : 1 ≤ X ^ P.β := Real.one_le_rpow hX1 P.β_pos.le
  have harg : (X ^ (1 - P.σ) + 1) / X ^ P.β ≤ 2 * X := by
    apply (div_le_iff₀ hT).mpr
    have h := mul_le_mul_of_nonneg_left hTone (by positivity : 0 ≤ 2 * X)
    nlinarith
  have hbracket : 2 + Real.log ((X ^ (1 - P.σ) + 1) / X ^ P.β) ≤
      4 * Real.log X := by
    have h := Real.log_le_log (div_pos (by positivity) hT) harg
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hX0.ne'] at h
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hlog2
    linarith
  have hfinite := prime_window_reciprocal_of_prefix K hK.le hprefix q a hq0
    (X ^ P.β) (X ^ (1 - P.σ)) hT hTV hTq
  have hcong : (natWindow (X ^ P.β) (X ^ (1 - P.σ))).filter
      (fun p => Nat.Prime p ∧ congMod p a q) =
        (natWindow (X ^ P.β) (X ^ (1 - P.σ))).filter
          (fun p => Nat.Prime p ∧ p ≡ a [MOD q]) := by
    ext p
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [congMod, Nat.ModEq]
  rw [hcong]
  apply hfinite.trans
  calc
    _ ≤ (K / ((Nat.totient q : ℝ) * Real.log (X ^ P.β / q))) *
        (4 * Real.log X) :=
      mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ ≤ (K / ((Nat.totient q : ℝ) * (δ * Real.log X))) *
        (4 * Real.log X) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact div_le_div_of_nonneg_left hK.le (by positivity)
        (mul_le_mul_of_nonneg_left hloglower hφ.le)
    _ = _ := by field_simp

end

/-! ## The sieve level `w = (y/q)^{1/16}` -/

section

open scoped BigOperators

theorem sixteenth_root_pow (t : ℝ) (ht : 0 ≤ t) :
    (t ^ (1 / 16 : ℝ)) ^ 16 = t := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
  norm_num

theorem sixteenth_root_ge_two (t : ℝ) (ht : (2 : ℝ) ^ 16 ≤ t) :
    2 ≤ t ^ (1 / 16 : ℝ) := by
  have ht0 : 0 ≤ t := (by positivity : (0 : ℝ) ≤ 2 ^ 16).trans ht
  apply le_of_pow_le_pow_left₀ (by norm_num : (16 : ℕ) ≠ 0)
    (Real.rpow_nonneg ht0 _)
  rwa [sixteenth_root_pow t ht0]

theorem sieve_rounding_error (w : ℝ) (hw : 2 ≤ w) :
    2 * (⌊w ^ 8⌋₊ : ℝ) + ((⌊w⌋₊ : ℝ) + 1) ≤
      64 * w ^ 16 / Real.log (w ^ 16) := by
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have hw1 : 1 ≤ w := (by norm_num : (1 : ℝ) ≤ 2).trans hw
  have hpow1 : (1 : ℝ) ≤ w ^ 8 := one_le_pow₀ hw1
  have hpoww : w ≤ w ^ 8 := by
    simpa using pow_le_pow_right₀ hw1 (by norm_num : (1 : ℕ) ≤ 8)
  have hfloor : 2 * (⌊w ^ 8⌋₊ : ℝ) + ((⌊w⌋₊ : ℝ) + 1) ≤ 4 * w ^ 8 := by
    nlinarith [Nat.floor_le (by positivity : 0 ≤ w ^ 8), Nat.floor_le hw0.le]
  have hlogpos : 0 < Real.log (w ^ 16) := by
    apply Real.log_pos
    exact one_lt_pow₀ (by linarith : (1 : ℝ) < w) (by norm_num)
  have hlog : Real.log (w ^ 16) ≤ 16 * w := by
    rw [Real.log_pow]
    exact mul_le_mul_of_nonneg_left (Real.log_le_self hw0.le) (by norm_num)
  have h916 : w ^ 9 ≤ w ^ 16 := pow_le_pow_right₀ hw1 (by norm_num)
  apply hfloor.trans
  rw [le_div_iff₀ hlogpos]
  have hm := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 4 * w ^ 8)
  have he : 4 * w ^ 8 * (16 * w) = 64 * w ^ 9 := by ring
  rw [he] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left h916 (by norm_num))

/-- The sieve bound with `w = (y/q)^{1/16}`, given `∑ 1/p ≤ B` on every block and Mertens'
bound `∏_{p < w} (1 - 1/p) ≤ C/log w`. -/
theorem primePrefix_upper_of_block_estimates (y : ℝ) (q a : ℕ) (hq : 0 < q)
    (hy : (2 : ℝ) ^ 16 ≤ y / q) (B C : ℝ) (hB : 0 ≤ B)
    (hBlocks : ∀ (w : ℝ) (J : ℕ) (j : Fin J), 2 ≤ w →
      (∑ p ∈ primeBlocks w q J j, (p : ℝ)⁻¹) ≤ B)
    (hEuler : ∀ w : ℝ, 2 ≤ w →
      (∏ p ∈ primeSupport w 1, (1 - (p : ℝ)⁻¹)) ≤ C / Real.log w) :
    ((primePrefix y q a).card : ℝ) ≤
      (32 * C * Real.exp (Real.exp B / Real.exp (-2 * B)) + 64) *
        y / ((Nat.totient q : ℝ) * Real.log (y / q)) := by
  let t := y / (q : ℝ)
  let w := t ^ (1 / 16 : ℝ)
  let E := Real.exp (Real.exp B / Real.exp (-2 * B))
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hφR : (0 : ℝ) < Nat.totient q := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have ht : (2 : ℝ) ^ 16 ≤ t := hy
  have ht1 : 1 < t := lt_of_lt_of_le (by norm_num) ht
  have hw : 2 ≤ w := sixteenth_root_ge_two t ht
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have hw1 : 1 ≤ w := (by norm_num : (1 : ℝ) ≤ 2).trans hw
  have hw16 : w ^ 16 = t := sixteenth_root_pow t (by linarith)
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogt : 0 < Real.log t := Real.log_pos ht1
  have hlog : Real.log t = 16 * Real.log w := by rw [← hw16, Real.log_pow]; norm_num
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hy1 : 1 ≤ y := by
    have he : y = t * q := (div_mul_cancel₀ y hqR.ne').symm
    rw [he]
    nlinarith
  have hfloor : (⌊y⌋₊ : ℝ) + 1 ≤ 2 * y := by
    nlinarith [Nat.floor_le (by linarith : 0 ≤ y)]
  let J := blockStop w hw0
  have hs := primePrefix_block_upper y w q a J hw1 hq
    (blockStop_terminal w hw0) B hB (fun j => hBlocks w J j hw)
  have heuler : (∏ p ∈ primeSupport w q, (1 - (p : ℝ)⁻¹)) ≤
      ((q : ℝ) / Nat.totient q) * (C / Real.log w) :=
    (support_euler_le_totient_mul w q hq).trans
      (mul_le_mul_of_nonneg_left (hEuler w hw) (div_nonneg hqR.le hφR.le))
  have hnonneg : 0 ≤ ∏ p ∈ primeSupport w q, (1 - (p : ℝ)⁻¹) := by
    apply Finset.prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primeSupport.mp hp).1.two_le
    have hi := inv_anti₀ (by norm_num : (0 : ℝ) < 2) hp2
    norm_num at hi
    linarith
  have hmain : (((⌊y⌋₊ : ℝ) + 1) / q) *
      (∏ p ∈ primeSupport w q, (1 - (p : ℝ)⁻¹)) * E ≤
        (32 * C * E) * (y / ((Nat.totient q : ℝ) * Real.log t)) := by
    calc
      _ ≤ (2 * y / q) * (∏ p ∈ primeSupport w q, (1 - (p : ℝ)⁻¹)) * E := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hfloor hqR.le) hnonneg
      _ ≤ (2 * y / q) * (((q : ℝ) / Nat.totient q) * (C / Real.log w)) * E := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left heuler (by positivity)
      _ = _ := by rw [hlog]; field_simp; ring
  have herr : 2 * (⌊w ^ 8⌋₊ : ℝ) + ((⌊w⌋₊ : ℝ) + 1) ≤
      64 * (y / ((Nat.totient q : ℝ) * Real.log t)) := by
    apply (sieve_rounding_error w hw).trans
    rw [hw16]
    have hφq : (Nat.totient q : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
    calc
      64 * t / Real.log t = 64 * (y / ((q : ℝ) * Real.log t)) := by
        dsimp [t]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (by linarith) (mul_pos hφR hlogt)
          (mul_le_mul_of_nonneg_right hφq hlogt.le)) (by norm_num)
  change ((primePrefix y q a).card : ℝ) ≤
    (32 * C * E + 64) * y / ((Nat.totient q : ℝ) * Real.log t)
  have htotal := add_le_add hmain herr
  apply hs.trans
  convert htotal using 1 <;> ring

end

/-! ## Proofs of Lemmas 3.5 and 3.6 -/

section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem primeBlocks_in_square (w : ℝ) (hw : 0 ≤ w) (q J : ℕ) (j : Fin J) :
    ∀ p ∈ primeBlocks w q J j,
      Nat.Prime p ∧ max 2 (blockScale w ((j : ℕ) + 1)) ≤ (p : ℝ) ∧
        (p : ℝ) < (max 2 (blockScale w ((j : ℕ) + 1))) ^ 2 := by
  intro p hp
  have hp' := mem_primeBlocks.mp hp
  refine ⟨hp'.1, hp'.2.2.2.1, hp'.2.2.2.2.trans_le ?_⟩
  rw [← blockScale_square w hw j]
  apply pow_le_pow_left₀
  · exact Real.rpow_nonneg hw _
  · exact le_max_right _ _

theorem primeSupport_product_le_one (w : ℝ) (q : ℕ) :
    (∏ p ∈ primeSupport w q, (1 - (p : ℝ)⁻¹)) ≤ 1 := by
  apply Finset.prod_le_one
  · intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (mem_primeSupport.mp hp).1.one_lt
    exact (sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)).le
  · intro p hp
    exact sub_le_self _ (by positivity)

theorem primeSupport_product_le_half (w : ℝ) (hw : 0 < w) :
    (∏ p ∈ primeSupport w 1, (1 - (p : ℝ)⁻¹)) ≤
      PrimeEstimates.primeProduct (w / 2) := by
  classical
  have hs : PrimeEstimates.primes (w / 2) ⊆ primeSupport w 1 := by
    intro p hp
    have hp' := (PrimeEstimates.mem_primes (by positivity)).mp hp
    exact mem_primeSupport.mpr ⟨hp'.1, lt_of_le_of_lt hp'.2 (by linarith), hp'.1.not_dvd_one⟩
  have he : (∏ p ∈ primeSupport w 1 \ PrimeEstimates.primes (w / 2),
      (1 - (p : ℝ)⁻¹)) ≤ 1 := by
    apply Finset.prod_le_one
    · intro p hp
      have hp1 : (1 : ℝ) < p := by
        exact_mod_cast (mem_primeSupport.mp (Finset.mem_sdiff.mp hp).1).1.one_lt
      exact (sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)).le
    · intro p hp
      exact sub_le_self _ (by positivity)
  calc
    _ = (∏ p ∈ primeSupport w 1 \ PrimeEstimates.primes (w / 2),
        (1 - (p : ℝ)⁻¹)) * PrimeEstimates.primeProduct (w / 2) :=
      (Finset.prod_sdiff hs).symm
    _ ≤ 1 * PrimeEstimates.primeProduct (w / 2) :=
      mul_le_mul_of_nonneg_right he (PrimeEstimates.primeProduct_pos _).le
    _ = _ := one_mul _

theorem strict_euler_upper : ∃ C > 0, ∀ w : ℝ, 2 ≤ w →
    (∏ p ∈ primeSupport w 1, (1 - (p : ℝ)⁻¹)) ≤ C / Real.log w := by
  obtain ⟨C, hC, hbound⟩ := PrimeEstimates.primeProduct_upper
  refine ⟨max (2 * C) (Real.log 4), lt_of_lt_of_le (by positivity) (le_max_left _ _), ?_⟩
  intro w hw
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have hlog : 0 < Real.log w := Real.log_pos (by linarith)
  by_cases hw4 : 4 ≤ w
  · have hhalf : 2 ≤ w / 2 := by linarith
    have hloghalf : 0 < Real.log (w / 2) := Real.log_pos (by linarith)
    have hlog2 : Real.log 2 ≤ Real.log (w / 2) :=
      Real.log_le_log (by norm_num) hhalf
    have hlogeq : Real.log w = Real.log (w / 2) + Real.log 2 := by
      rw [← Real.log_mul (by positivity : w / 2 ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      ring
    calc
      _ ≤ PrimeEstimates.primeProduct (w / 2) := primeSupport_product_le_half w hw0
      _ ≤ C / Real.log (w / 2) := hbound _ hhalf
      _ ≤ (2 * C) / Real.log w := by
        rw [div_le_div_iff₀ hloghalf hlog]
        rw [hlogeq]
        nlinarith
      _ ≤ _ := div_le_div_of_nonneg_right (le_max_left _ _) hlog.le
  · have hlogle : Real.log w ≤ max (2 * C) (Real.log 4) :=
      (Real.log_le_log hw0 (le_of_not_ge hw4)).trans (le_max_right _ _)
    exact (primeSupport_product_le_one w 1).trans
      ((le_div_iff₀ hlog).mpr (by simpa using hlogle))

theorem primePrefix_uniform_upper : ∃ K > 0,
    ∀ (y : ℝ) (q a : ℕ), 0 < q → (2 : ℝ) ^ 16 ≤ y / q →
      ((primePrefix y q a).card : ℝ) ≤
        K * y / ((Nat.totient q : ℝ) * Real.log (y / q)) := by
  obtain ⟨B, hB, hblock⟩ := PrimeEstimates.block_harmonic_bound
  obtain ⟨C, hC, heuler⟩ := strict_euler_upper
  refine ⟨32 * C * Real.exp (Real.exp B / Real.exp (-2 * B)) + 64, by positivity, ?_⟩
  intro y q a hq hy
  apply primePrefix_upper_of_block_estimates y q a hq hy B C hB _ heuler
  intro w J j hw
  exact hblock (max 2 (blockScale w ((j : ℕ) + 1))) (primeBlocks w q J j)
    (le_max_left _ _) (primeBlocks_in_square w (by linarith) q J j)

/-- Lemma 3.5: `π(y; q, a) ≪ y / (φ(q) log(y/q))` uniformly for `(a, q) = 1` and
`y ≥ 2^16 q`. -/
theorem prime_progression_count_upper : ∃ K > 0,
    ∀ (y : ℝ) (q a : ℕ), 0 < q → (2 : ℝ) ^ 16 * q ≤ y → Nat.Coprime a q →
      ((primePrefix y q a).card : ℝ) ≤
        K * y / ((Nat.totient q : ℝ) * Real.log (y / q)) := by
  obtain ⟨K, hK, hbound⟩ := primePrefix_uniform_upper
  refine ⟨K, hK, ?_⟩
  intro y q a hq hy _ha
  exact hbound y q a hq ((le_div_iff₀ (Nat.cast_pos.mpr hq)).mpr hy)

/-- Lemma 3.6: for `ν < β`, `∑_{X^β < p ≤ X^{1-σ}, p ≡ a (mod q)} 1/p ≪ 1/φ(q)` uniformly for
`q ≤ X^ν` and `(a, q) = 1`. -/
theorem prime_reciprocal_power_window_bound :
    ∀ P : Params, ∀ ν : ℝ, 0 < ν → ν < P.β →
      ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        ∀ q a : ℕ, 1 ≤ q → (q : ℝ) ≤ X ^ ν → Nat.Coprime a q →
          (∑ p ∈ (Estimates.natWindow (X ^ P.β) (X ^ (1 - P.σ))).filter
            (fun p => Nat.Prime p ∧ Estimates.congMod p a q), (1 : ℝ) / p) ≤
              C / (Nat.totient q : ℝ) := by
  obtain ⟨K, hK, hbound⟩ := primePrefix_uniform_upper
  exact prime_power_window_reciprocal_of_prefix K hK hbound

end

end ErdosStraus.BrunHooley
