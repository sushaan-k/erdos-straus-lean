import ErdosStraus.BombieriVinogradov.DirichletL.ConditionalSeries

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

/-!
# Bounds for Dirichlet `L`-functions near `re s = 1`

For the principal character `χ₀` mod `q`, `|L(s, χ₀)| ≤ (1 + log q) |ζ(s)|` when
`re s ≥ 1` and `s ≠ 1`, and `|ζ(1 + x + iu)| ≪ 1 + log (|u| + 2) + 1/|u|` for `0 < x ≤ 1`.
For nonprincipal `χ` mod `q` and `M = q (⌊|t|⌋ + 1)`, `|L(σ + it, χ)| ≤ 32 (1 + log M)` and
`|L'(σ + it, χ)| ≤ 64 (1 + log M)²` when `1/2 ≤ σ ≤ 2` and `σ ≥ 1 - 1/log M`.
For `σ > 1`, `|L(σ + it, χ)| ≤ 1 + 1/(σ - 1)` and `-L'(s, χ)/L(s, χ) = ∑ χ(n) Λ(n) n^{-s}`.
-/

section

/-! ## The principal character -/

open Complex Finset

namespace DirichletCharacter

private lemma primeSubsetProduct_injective (q : ℕ) :
    Set.InjOn (fun t : Finset ℕ => ∏ p ∈ t, p) q.primeFactors.powerset := by
  have subset_of_prod_eq : ∀ t ∈ q.primeFactors.powerset,
      ∀ u ∈ q.primeFactors.powerset, (∏ p ∈ t, p) = (∏ p ∈ u, p) → t ⊆ u := by
    intro t ht u hu htu p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht hp)
    have hpd : p ∣ ∏ a ∈ u, a := htu ▸ Finset.dvd_prod_of_mem id hp
    obtain ⟨a, ha, hpa⟩ := (Prime.dvd_finsetProd_iff hpp.prime id).mp hpd
    have hap : a.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hu ha)
    have : p = a := (Nat.dvd_prime hap).mp hpa |>.resolve_left hpp.ne_one
    simpa [this] using ha
  intro t ht u hu htu
  exact Finset.Subset.antisymm (subset_of_prod_eq t ht u hu htu)
    (subset_of_prod_eq u hu t ht htu.symm)

/-- Expanding the product gives `∑ 1/d` over squarefree `d ∣ q`, which is at most the
harmonic number `H_q ≤ 1 + log q`. -/
lemma prod_one_add_inv_primeFactors_le_one_add_log (q : ℕ) (hq : 1 ≤ q) :
    (∏ p ∈ q.primeFactors, (1 + ((p : ℝ)⁻¹))) ≤ 1 + Real.log q := by
  let d : Finset ℕ → ℕ := fun t => ∏ p ∈ t, p
  have himage : Finset.image d q.primeFactors.powerset ⊆ Finset.Icc 1 q := by
    intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    have ht' : t ⊆ q.primeFactors := Finset.mem_powerset.mp ht
    rw [Finset.mem_Icc]
    constructor
    · exact Finset.prod_pos fun p hp =>
        (Nat.prime_of_mem_primeFactors (ht' hp)).pos
    · exact Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hq)
        ((Finset.prod_dvd_prod_of_subset t q.primeFactors id ht').trans
          (Nat.prod_primeFactors_dvd q))
  have hsumImage :
      (∑ n ∈ Finset.image d q.primeFactors.powerset, ((n : ℝ)⁻¹)) =
        ∑ t ∈ q.primeFactors.powerset, ∏ p ∈ t, ((p : ℝ)⁻¹) := by
    rw [Finset.sum_image (primeSubsetProduct_injective q)]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Nat.cast_prod, Finset.prod_inv_distrib]
  calc
    (∏ p ∈ q.primeFactors, (1 + ((p : ℝ)⁻¹))) =
        ∑ t ∈ q.primeFactors.powerset, ∏ p ∈ t, ((p : ℝ)⁻¹) := by
      simp_rw [add_comm (1 : ℝ), Finset.prod_add]
      simp
    _ = ∑ n ∈ Finset.image d q.primeFactors.powerset, ((n : ℝ)⁻¹) :=
      hsumImage.symm
    _ ≤ ∑ n ∈ Finset.Icc 1 q, ((n : ℝ)⁻¹) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg himage (by
        intro i hi hni
        positivity)
    _ = (harmonic q : ℝ) := by
      simpa only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
        congrArg (fun x : ℚ => (x : ℝ)) (harmonic_eq_sum_Icc (n := q)).symm
    _ ≤ 1 + Real.log q := by exact_mod_cast harmonic_le_one_add_log q

lemma principalEulerFactorNorm_le_one_add_inv
    {s : ℂ} (hs : 1 ≤ s.re) {p : ℕ} (hp : p.Prime) :
    ‖1 - (p : ℂ) ^ (-s)‖ ≤ 1 + (p : ℝ)⁻¹ := by
  have hpow : ‖(p : ℂ) ^ (-s)‖ ≤ (p : ℝ)⁻¹ := by
    calc
      ‖(p : ℂ) ^ (-s)‖ ≤ ‖(p : ℂ) ^ (-(1 : ℂ))‖ := by
        apply Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos hp.pos
        simp only [neg_re, one_re]
        linarith
      _ = (p : ℝ)⁻¹ := by
        rw [show -(1 : ℂ) = (-1 : ℤ) by norm_num, cpow_intCast]
        simp
  calc
    ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ 1 + (p : ℝ)⁻¹ := by simpa using add_le_add_left hpow 1

/-- The Euler factors `1 - p^{-s}`, `p ∣ q`, relating `L(s, χ₀)` to `ζ(s)` have product
of norm at most `1 + log q` when `re s ≥ 1`. -/
lemma principalEulerCorrectionNorm_le_one_add_log
    (q : ℕ) (hq : 1 ≤ q) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ 1 + Real.log q := by
  calc
    ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))‖ =
        ∏ p ∈ q.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖ := by simp
    _ ≤ ∏ p ∈ q.primeFactors, (1 + (p : ℝ)⁻¹) := by
      gcongr with p hp
      exact principalEulerFactorNorm_le_one_add_inv hs
        (Nat.prime_of_mem_primeFactors hp)
    _ ≤ 1 + Real.log q := prod_one_add_inv_primeFactors_le_one_add_log q hq

/-- `|L(s, χ₀)| ≤ (1 + log q) |ζ(s)|` for the principal character `χ₀` mod `q`,
when `re s ≥ 1` and `s ≠ 1`. -/
theorem norm_LFunctionTrivChar_le_one_add_log_mul_riemannZeta
    (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 ≤ s.re) (hsne : s ≠ 1) :
    ‖LFunctionTrivChar q s‖ ≤ (1 + Real.log q) * ‖riemannZeta s‖ := by
  rw [LFunctionTrivChar_eq_mul_riemannZeta hsne, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (principalEulerCorrectionNorm_le_one_add_log q
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) hs) (norm_nonneg _)

/-- If `χ² = 1`, then `|L(s, χ²)| ≤ (1 + log q) |ζ(s)|` when `re s ≥ 1` and `s ≠ 1`. -/
theorem norm_LFunction_sq_le_one_add_log_mul_riemannZeta
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1)
    {s : ℂ} (hs : 1 ≤ s.re) (hsne : s ≠ 1) :
    ‖(χ ^ 2).LFunction s‖ ≤ (1 + Real.log q) * ‖riemannZeta s‖ := by
  rw [hquad, ← LFunctionTrivChar]
  exact norm_LFunctionTrivChar_le_one_add_log_mul_riemannZeta q hs hsne

end DirichletCharacter

end

section

/-! ## The Riemann zeta function to the right of `s = 1` -/
/-!
## Nonprincipal characters

For `re s > 0` the series `∑ χ(n) n^{-s}` converges to `L(s, χ)`. Split it at
`M = q (⌊|t|⌋ + 1)`. The initial segment is at most a constant times the harmonic sum
`H_M`, and partial summation bounds the tail by `q M^{-σ} (1 + |s|/σ)`, which is
bounded because `|t| < M/q`.
-/

open Complex Topology Filter Set
/-- `|ζ(1 + x + iu)| ≤ Z/|u|` for `0 < x ≤ 1` and `0 < |u| ≤ 3`. Near `s = 1` this
follows from `(s - 1) ζ(s) → 1`, and on the rest of the rectangle from compactness. -/
theorem zeta_pole_bound_small_height :
    ∃ Z : ℝ, 0 < Z ∧ ∀ (x u : ℝ), 0 < x → x ≤ 1 → u ≠ 0 → |u| ≤ 3 →
      ‖riemannZeta (1 + x + I * u)‖ ≤ Z / |u| := by
  have hnear : ∀ᶠ s : ℂ in 𝓝[≠] 1, ‖(s - 1) * riemannZeta s‖ < 2 := by
    have hball : Metric.ball (1 : ℂ) 1 ∈ 𝓝 (1 : ℂ) :=
      Metric.ball_mem_nhds _ (by norm_num)
    filter_upwards [riemannZeta_residue_one.eventually hball] with s hs
    rw [dist_eq_norm] at hs
    calc
      ‖(s - 1) * riemannZeta s‖
          ≤ ‖(s - 1) * riemannZeta s - 1‖ + ‖(1 : ℂ)‖ := by
              simpa using norm_add_le ((s - 1) * riemannZeta s - 1) 1
      _ < 2 := by simp only [norm_one]; linarith
  have hnear' : ∀ᶠ s : ℂ in 𝓝 1,
      s ≠ 1 → ‖(s - 1) * riemannZeta s‖ < 2 :=
    (eventually_nhdsWithin_iff).1 hnear
  rcases (eventually_nhds_iff.1 hnear') with ⟨U, hUsub, hUopen, h1U⟩
  rcases Metric.isOpen_iff.mp hUopen 1 h1U with ⟨ε, hεpos, hεU⟩
  let R : Set ℂ := {s | s.re ∈ Icc 1 2 ∧ s.im ∈ Icc (-3) 3}
  have hRcompact : IsCompact R := by
    change IsCompact (Complex.reProdIm (Icc (1 : ℝ) 2) (Icc (-3 : ℝ) 3))
    exact isCompact_Icc.reProdIm isCompact_Icc
  let K : Set ℂ := R ∩ {s | ε ≤ dist s 1}
  have hKclosed : IsClosed K := by
    exact hRcompact.isClosed.inter <|
      isClosed_Ici.preimage (by fun_prop : Continuous fun s : ℂ => dist s 1)
  have hKcompact : IsCompact K := by
    apply hRcompact.of_isClosed_subset hKclosed
    intro s hs
    exact hs.1
  have hKne : ∀ s ∈ K, s ≠ 1 := by
    intro s hs hseq
    have hbad : ε ≤ 0 := by simpa [hseq] using hs.2
    linarith
  have hcont : ContinuousOn riemannZeta K := by
    intro s hs
    exact (differentiableAt_riemannZeta (hKne s hs)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn hKcompact hcont
  let C' : ℝ := max C 1
  have hC'pos : 0 < C' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨max 2 (3 * C'), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro x u hx hx1 hu hule
  have huabspos : 0 < |u| := abs_pos.mpr hu
  let s : ℂ := 1 + x + I * u
  have hsne : s ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp [s] at this
    exact hu this
  have hsR : s ∈ R := by
    simp only [R, mem_ofPred_eq, mem_Icc]
    constructor
    · constructor
      · simp [s, hx.le]
      · simp [s]
        linarith
    · simpa [s, abs_le] using hule
  by_cases hsball : dist s 1 < ε
  · have hprod : ‖(s - 1) * riemannZeta s‖ < 2 :=
      hUsub s (hεU hsball) hsne
    have hu_le : |u| ≤ ‖s - 1‖ := by
      have him : (s - 1).im = u := by simp [s]
      rw [← him]
      exact abs_im_le_norm (s - 1)
    apply (le_div_iff₀ huabspos).2
    calc
      ‖riemannZeta s‖ * |u| = |u| * ‖riemannZeta s‖ := mul_comm _ _
      _ ≤ ‖s - 1‖ * ‖riemannZeta s‖ :=
        mul_le_mul_of_nonneg_right hu_le (norm_nonneg _)
      _ = ‖(s - 1) * riemannZeta s‖ := (norm_mul _ _).symm
      _ ≤ 2 := hprod.le
      _ ≤ max 2 (3 * C') := le_max_left _ _
  · have hsK : s ∈ K := ⟨hsR, le_of_not_gt hsball⟩
    have hzC : ‖riemannZeta s‖ ≤ C' :=
      (hC s hsK).trans (le_max_left _ _)
    apply hzC.trans
    apply (le_div_iff₀ huabspos).2
    calc
      C' * |u| ≤ C' * 3 := mul_le_mul_of_nonneg_left hule hC'pos.le
      _ = 3 * C' := mul_comm _ _
      _ ≤ max 2 (3 * C') := le_max_right _ _
/-- `|ζ(1 + x + iu)| ≤ Z (1 + log (|u| + 2) + 1/|u|)` uniformly for `0 < x ≤ 1` and
`u ≠ 0`. For `|u| > 3` this uses `ZetaUpperBnd`. -/
theorem zeta_pole_plus_log_bound :
    ∃ Z : ℝ, 0 < Z ∧ ∀ (x u : ℝ), 0 < x → x ≤ 1 → u ≠ 0 →
      ‖riemannZeta (1 + x + I * u)‖ ≤
        Z * (1 + Real.log (|u| + 2) + 1 / |u|) := by
  obtain ⟨z, hz, hsmall⟩ := zeta_pole_bound_small_height
  obtain ⟨A, hA, C, hC, hlarge⟩ := ZetaUpperBnd
  let Z : ℝ := max z C
  have hZpos : 0 < Z := hz.trans_le (le_max_left _ _)
  refine ⟨Z, hZpos, ?_⟩
  intro x u hx hx1 hu
  have huabspos : 0 < |u| := abs_pos.mpr hu
  have hlognonneg : 0 ≤ Real.log (|u| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg u])
  by_cases hsmallHeight : |u| ≤ 3
  · calc
      ‖riemannZeta (1 + x + I * u)‖ ≤ z / |u| :=
        hsmall x u hx hx1 hu hsmallHeight
      _ ≤ Z / |u| := div_le_div_of_nonneg_right (le_max_left _ _) huabspos.le
      _ ≤ Z * (1 + Real.log (|u| + 2) + 1 / |u|) := by
        rw [div_eq_mul_inv, one_div]
        exact mul_le_mul_of_nonneg_left (by linarith) hZpos.le
  · have hu3 : 3 < |u| := lt_of_not_ge hsmallHeight
    have hlogpos : 0 < Real.log |u| := Real.log_pos (by linarith)
    have hlower : 1 - A / Real.log |u| ≤ 1 + x := by
      have : 0 < A / Real.log |u| := div_pos hA.1 hlogpos
      linarith
    have hupper : 1 + x ≤ 2 := by linarith
    have hb := hlarge (1 + x) u hu3 ⟨hlower, hupper⟩
    have hb' : ‖riemannZeta (1 + x + I * u)‖ ≤ C * Real.log |u| := by
      simpa [ofReal_add, mul_comm, add_comm] using hb
    have hlogmono : Real.log |u| ≤ Real.log (|u| + 2) := by
      apply Real.strictMonoOn_log.monotoneOn huabspos
      · show 0 < |u| + 2
        linarith
      · linarith
    calc
      ‖riemannZeta (1 + x + I * u)‖ ≤ C * Real.log |u| := hb'
      _ ≤ Z * Real.log |u| :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hlogpos.le
      _ ≤ Z * Real.log (|u| + 2) :=
        mul_le_mul_of_nonneg_left hlogmono hZpos.le
      _ ≤ Z * (1 + Real.log (|u| + 2) + 1 / |u|) := by
        apply mul_le_mul_of_nonneg_left _ hZpos.le
        have hinv : 0 < 1 / |u| := one_div_pos.mpr huabspos
        linarith
end
section
open Complex Finset

namespace BombieriVinogradov.LValueBound

open BombieriVinogradov.AbelWeight
open BombieriVinogradov.LValueSeries
variable {q : ℕ} [NeZero q]

/-- `⌊|t|⌋ + 1`, the least natural number greater than `|t|`. -/
noncomputable def dirichletLHeightBlock (t : ℝ) : ℕ := ⌊|t|⌋₊ + 1

/-- The cutoff `M = q (⌊|t|⌋ + 1)` at which the series for `L(σ + it, χ)` is split. -/
noncomputable def dirichletLConductorHeightCutoff (q : ℕ) (t : ℝ) : ℕ :=
  q * dirichletLHeightBlock t

private lemma character_nat_zero_of_ne_one
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : χ (0 : ℕ) = 0 := by
  exact BombieriVinogradov.LValueSeries.character_nat_zero_of_ne_one χ hχ

lemma two_le_modulus_of_ne_one
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : 2 ≤ q := by
  have hq1 : q ≠ 1 := by
    intro h
    subst q
    exact hχ (Subsingleton.elim _ _)
  exact (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨NeZero.ne q, hq1⟩)

lemma abs_lt_heightBlock (t : ℝ) : |t| < dirichletLHeightBlock t := by
  simpa [dirichletLHeightBlock, Nat.cast_add, Nat.cast_one] using
    (Nat.lt_floor_add_one |t|)

lemma one_le_heightBlock (t : ℝ) : 1 ≤ dirichletLHeightBlock t := by
  simp [dirichletLHeightBlock]

lemma two_le_conductorHeightCutoff
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    2 ≤ dirichletLConductorHeightCutoff q t := by
  unfold dirichletLConductorHeightCutoff
  calc
    2 ≤ q := two_le_modulus_of_ne_one χ hχ
    _ = q * 1 := by simp
    _ ≤ q * dirichletLHeightBlock t := Nat.mul_le_mul_left q (one_le_heightBlock t)

lemma log_conductorHeightCutoff_pos
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    0 < Real.log (dirichletLConductorHeightCutoff q t) := by
  apply Real.log_pos
  exact_mod_cast (two_le_conductorHeightCutoff χ hχ t)

lemma rpow_one_sub_le_exp_one
    {m k : ℕ} {σ : ℝ} (hm : 2 ≤ m) (hk1 : 1 ≤ k) (hkm : k ≤ m)
    (hnear : 1 - 1 / Real.log m ≤ σ) :
    (k : ℝ) ^ (1 - σ) ≤ Real.exp 1 := by
  have hlogm : 0 < Real.log (m : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hm
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)
  rw [Real.rpow_def_of_pos hkpos]
  apply Real.exp_le_exp.mpr
  have hlogk0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk1)
  have hlogle : Real.log (k : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log hkpos (by exact_mod_cast hkm)
  have hene : 1 - σ ≤ 1 / Real.log (m : ℝ) := by linarith
  calc
    Real.log (k : ℝ) * (1 - σ)
        ≤ Real.log (k : ℝ) * (1 / Real.log (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hene hlogk0
    _ ≤ Real.log (m : ℝ) * (1 / Real.log (m : ℝ)) :=
      mul_le_mul_of_nonneg_right hlogle (by positivity)
    _ = 1 := mul_one_div_cancel hlogm.ne'

private lemma norm_prefix_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ t : ℝ} {m : ℕ}
    (hm : 2 ≤ m) (hnear : 1 - 1 / Real.log m ≤ σ) :
    ‖∑ k ∈ range m, cpowWeight (σ + I * t) k * χ k‖ ≤
      2 * Real.exp 1 * (1 + Real.log m) := by
  calc
    _ ≤ ∑ k ∈ range m, ‖cpowWeight (σ + I * t) k * χ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range m, 2 * Real.exp 1 * ((k + 1 : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hk0 : k = 0
      · subst k
        rw [character_nat_zero_of_ne_one χ hχ]
        simp
        exact Real.exp_pos 1 |>.le
      · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        have hkm : k < m := Finset.mem_range.mp hk
        have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_ne_zero hk0)
        have hpow := rpow_one_sub_le_exp_one hm hk1 hkm.le hnear
        have hinv : (k : ℝ)⁻¹ ≤ 2 * ((k + 1 : ℕ) : ℝ)⁻¹ := by
          rw [inv_eq_one_div, show 2 * ((k + 1 : ℕ) : ℝ)⁻¹ =
            2 / ((k + 1 : ℕ) : ℝ) by rw [div_eq_mul_inv]]
          rw [div_le_div_iff₀ hkpos (by positivity)]
          push_cast
          have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
          nlinarith
        calc
          ‖cpowWeight (σ + I * t) k * χ k‖
              = ‖cpowWeight (σ + I * t) k‖ * ‖χ k‖ := norm_mul _ _
          _ ≤ ‖cpowWeight (σ + I * t) k‖ := by
            exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one k)
          _ = (k : ℝ) ^ (-σ) := by
            rw [cpowWeight, Complex.norm_cpow_eq_rpow_re_of_pos hkpos]
            simp
          _ = (k : ℝ) ^ (1 - σ) * (k : ℝ)⁻¹ := by
            rw [← Real.rpow_neg_one, ← Real.rpow_add hkpos]
            congr 1
            ring
          _ ≤ Real.exp 1 * (k : ℝ)⁻¹ := by gcongr
          _ ≤ Real.exp 1 * (2 * ((k + 1 : ℕ) : ℝ)⁻¹) := by gcongr
          _ = 2 * Real.exp 1 * ((k + 1 : ℕ) : ℝ)⁻¹ := by ring
    _ = 2 * Real.exp 1 * (harmonic m : ℝ) := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      rw [Finset.mul_sum]
    _ ≤ 2 * Real.exp 1 * (1 + Real.log m) := by
      gcongr
      exact_mod_cast harmonic_le_one_add_log m

private lemma norm_tail_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ t : ℝ}
    (hσlower : 1 / 2 ≤ σ) (_hσupper : σ ≤ 2)
    (hnear : 1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ σ) :
    ‖orderedValueSeries χ hχ (σ + I * t)
        (by have hσpos : 0 < σ := lt_of_lt_of_le (by norm_num) hσlower
            simpa using hσpos) -
        ∑ k ∈ range (dirichletLConductorHeightCutoff q t),
          cpowWeight (σ + I * t) k * χ k‖ ≤ 7 * Real.exp 1 := by
  let H := dirichletLHeightBlock t
  let m := dirichletLConductorHeightCutoff q t
  have hm : 2 ≤ m := two_le_conductorHeightCutoff χ hχ t
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast one_le_heightBlock t
  have hHpos : (0 : ℝ) < H := lt_of_lt_of_le zero_lt_one hH1
  have htH : |t| < (H : ℝ) := by simpa [H] using abs_lt_heightBlock t
  have hσpos : 0 < σ := lt_of_lt_of_le (by norm_num) hσlower
  have hsre : (σ + I * t : ℂ).re = σ := by simp
  have hnorm : ‖(σ + I * t : ℂ)‖ ≤ σ + |t| := by
    calc
      _ ≤ ‖(σ : ℂ)‖ + ‖I * (t : ℂ)‖ := norm_add_le _ _
      _ = |σ| + |t| := by simp
      _ = σ + |t| := by rw [abs_of_pos hσpos]
  have hratio : ‖(σ + I * t : ℂ)‖ / σ ≤ 4 + 2 * |t| := by
    rw [div_le_iff₀ hσpos]
    nlinarith [abs_nonneg t]
  have hheightpay : (1 + ‖(σ + I * t : ℂ)‖ / σ) / (H : ℝ) ≤ 7 := by
    rw [div_le_iff₀ hHpos]
    nlinarith
  have hpow : (m : ℝ) ^ (1 - σ) ≤ Real.exp 1 :=
    rpow_one_sub_le_exp_one hm (by omega) (le_refl m) (by simpa [m] using hnear)
  have htail := norm_orderedValueSeries_sub_sum_range_le
    χ hχ (σ + I * t) (by simpa using hσpos) (m := m) (by omega)
  have hfactor : (q : ℝ) * (m : ℝ) ^ (-σ) = (m : ℝ) ^ (1 - σ) / H := by
    have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    have hmcast : (m : ℝ) = (q : ℝ) * (H : ℝ) := by
      simp [m, H, dirichletLConductorHeightCutoff]
    rw [show -σ = (1 - σ) + (-1) by ring, Real.rpow_add (by positivity),
      Real.rpow_neg_one, hmcast, div_eq_mul_inv]
    field_simp
  calc
    _ ≤ (q : ℝ) * ((m : ℝ) ^ (-σ) +
        (‖(σ + I * t : ℂ)‖ / σ) * (m : ℝ) ^ (-σ)) := by
          simpa [m, hsre] using htail
    _ = ((m : ℝ) ^ (1 - σ) / H) *
        (1 + ‖(σ + I * t : ℂ)‖ / σ) := by rw [← hfactor]; ring
    _ = (m : ℝ) ^ (1 - σ) *
        ((1 + ‖(σ + I * t : ℂ)‖ / σ) / H) := by ring
    _ ≤ Real.exp 1 * 7 := by gcongr
    _ = 7 * Real.exp 1 := by ring

/-- For nonprincipal `χ` mod `q` and `M = q (⌊|t|⌋ + 1)`,
`|L(σ + it, χ)| ≤ 32 (1 + log M)` when `1/2 ≤ σ ≤ 2` and `σ ≥ 1 - 1/log M`. -/
theorem norm_LFunction_le_one_add_log
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ t : ℝ}
    (hσlower : 1 / 2 ≤ σ) (hσupper : σ ≤ 2)
    (hnear : 1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ σ) :
    ‖χ.LFunction (σ + I * t)‖ ≤
      32 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) := by
  let m := dirichletLConductorHeightCutoff q t
  have hm : 2 ≤ m := two_le_conductorHeightCutoff χ hχ t
  have hlog0 : 0 ≤ Real.log (m : ℝ) :=
    (log_conductorHeightCutoff_pos χ hχ t).le
  have hσpos : 0 < σ := lt_of_lt_of_le (by norm_num) hσlower
  have hseries := orderedValueSeries_eq_LFunction_of_re_pos
    χ hχ (σ + I * t) (by simpa using hσpos)
  have hprefix := norm_prefix_le χ hχ (σ := σ) (t := t) (m := m)
    hm (by simpa [m] using hnear)
  have htail := norm_tail_le χ hχ hσlower hσupper hnear
  change ‖χ.LFunction (σ + I * t)‖ ≤ 32 * (1 + Real.log (m : ℝ))
  rw [← hseries]
  calc
    _ ≤ ‖orderedValueSeries χ hχ (σ + I * t) (by simpa using hσpos) -
          ∑ k ∈ range m, cpowWeight (σ + I * t) k * χ k‖ +
        ‖∑ k ∈ range m, cpowWeight (σ + I * t) k * χ k‖ :=
          norm_le_norm_sub_add _ _
    _ ≤ 7 * Real.exp 1 + 2 * Real.exp 1 * (1 + Real.log m) := by
      gcongr
    _ ≤ 32 * (1 + Real.log m) := by
      have he : Real.exp 1 < 3 := Real.exp_one_lt_three
      nlinarith

end BombieriVinogradov.LValueBound

end

section

/-!
## The derivative for nonprincipal characters

The same splitting at `M = q (⌊|t|⌋ + 1)`, applied to `L'(s, χ) = -∑ χ(n) (log n) n^{-s}`,
gives a bound of order `(1 + log M)²`.
-/

open Complex Finset

namespace BombieriVinogradov.LDerivBound

open BombieriVinogradov.AbelWeight
open BombieriVinogradov.LDerivSeries
open BombieriVinogradov.LDerivContinuation
open BombieriVinogradov.LValueBound
variable {q : ℕ} [NeZero q]

private lemma character_nat_zero_of_ne_one
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : χ (0 : ℕ) = 0 := by
  exact BombieriVinogradov.LValueSeries.character_nat_zero_of_ne_one χ hχ

private lemma rpow_one_sub_le_exp_one
    {m k : ℕ} {σ : ℝ} (hm : 2 ≤ m) (hk1 : 1 ≤ k) (hkm : k ≤ m)
    (hnear : 1 - 1 / Real.log m ≤ σ) :
    (k : ℝ) ^ (1 - σ) ≤ Real.exp 1 := by
  exact BombieriVinogradov.LValueBound.rpow_one_sub_le_exp_one hm hk1 hkm hnear

private lemma norm_derivative_prefix_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ t : ℝ} {m : ℕ}
    (hm : 2 ≤ m) (hnear : 1 - 1 / Real.log m ≤ σ) :
    ‖∑ k ∈ range m, logCpowWeight (σ + I * t) k * χ k‖ ≤
      2 * Real.exp 1 * Real.log m * (1 + Real.log m) := by
  have hlogm0 : 0 ≤ Real.log (m : ℝ) := (Real.log_pos (by exact_mod_cast hm)).le
  calc
    _ ≤ ∑ k ∈ range m, ‖logCpowWeight (σ + I * t) k * χ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range m,
        2 * Real.exp 1 * Real.log m * ((k + 1 : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hk0 : k = 0
      · subst k
        rw [character_nat_zero_of_ne_one χ hχ]
        simp
        positivity
      · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        have hkm : k < m := Finset.mem_range.mp hk
        have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_ne_zero hk0)
        have hpow := rpow_one_sub_le_exp_one hm hk1 hkm.le hnear
        have hlogk0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk1)
        have hlogkm : Real.log (k : ℝ) ≤ Real.log (m : ℝ) :=
          Real.strictMonoOn_log.monotoneOn hkpos
            (show (0 : ℝ) < (m : ℝ) by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hm))
            (by exact_mod_cast hkm.le)
        have hinv : (k : ℝ)⁻¹ ≤ 2 * ((k + 1 : ℕ) : ℝ)⁻¹ := by
          rw [inv_eq_one_div, show 2 * ((k + 1 : ℕ) : ℝ)⁻¹ =
            2 / ((k + 1 : ℕ) : ℝ) by rw [div_eq_mul_inv]]
          rw [div_le_div_iff₀ hkpos (by positivity)]
          push_cast
          have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
          nlinarith
        calc
          ‖logCpowWeight (σ + I * t) k * χ k‖
              ≤ ‖logCpowWeight (σ + I * t) k‖ := by
                rw [norm_mul]
                exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one k)
          _ = Real.log (k : ℝ) * (k : ℝ) ^ (-σ) := by
                rw [logCpowWeight, norm_mul, norm_neg, norm_real, Real.norm_eq_abs,
                  abs_of_nonneg hlogk0, cpowWeight,
                  Complex.norm_cpow_eq_rpow_re_of_pos hkpos]
                simp
          _ = Real.log (k : ℝ) * ((k : ℝ) ^ (1 - σ) * (k : ℝ)⁻¹) := by
                rw [← Real.rpow_neg_one, ← Real.rpow_add hkpos]
                congr 2
                ring
          _ ≤ Real.log m * (Real.exp 1 * (k : ℝ)⁻¹) := by
                exact mul_le_mul hlogkm
                  (mul_le_mul_of_nonneg_right hpow (by positivity))
                  (by positivity) hlogm0
          _ ≤ Real.log m * (Real.exp 1 *
                (2 * ((k + 1 : ℕ) : ℝ)⁻¹)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hinv (Real.exp_pos 1).le) hlogm0
          _ = 2 * Real.exp 1 * Real.log m * ((k + 1 : ℕ) : ℝ)⁻¹ := by ring
    _ = 2 * Real.exp 1 * Real.log m * (harmonic m : ℝ) := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      rw [Finset.mul_sum]
    _ ≤ 2 * Real.exp 1 * Real.log m * (1 + Real.log m) := by
      exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast harmonic_le_one_add_log m)
        (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 1).le) hlogm0)

private lemma norm_derivative_tail_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ t : ℝ}
    (hσlower : 1 / 2 ≤ σ) (hσupper : σ ≤ 2)
    (hnear : 1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ σ) :
    ‖orderedLogDerivativeSeries χ hχ (σ + I * t)
        (by have hσpos : 0 < σ := lt_of_lt_of_le (by norm_num) hσlower
            simpa using hσpos) -
        ∑ k ∈ range (dirichletLConductorHeightCutoff q t),
          logCpowWeight (σ + I * t) k * χ k‖ ≤
      3 * (14 + 7 * Real.log (dirichletLConductorHeightCutoff q t)) := by
  let H := dirichletLHeightBlock t
  let m := dirichletLConductorHeightCutoff q t
  let s : ℂ := σ + I * t
  let L : ℝ := Real.log m
  let P : ℝ := (m : ℝ) ^ (1 - σ)
  have hm : 2 ≤ m := two_le_conductorHeightCutoff χ hχ t
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast one_le_heightBlock t
  have hHpos : (0 : ℝ) < H := lt_of_lt_of_le zero_lt_one hH1
  have htH : |t| < (H : ℝ) := by simpa [H] using abs_lt_heightBlock t
  have hσpos : 0 < σ := lt_of_lt_of_le (by norm_num) hσlower
  have hL0 : 0 ≤ L := (log_conductorHeightCutoff_pos χ hχ t).le
  have hP0 : 0 ≤ P := by positivity
  have hP : P ≤ Real.exp 1 :=
    rpow_one_sub_le_exp_one hm (by omega) (le_refl m) (by simpa [m] using hnear)
  have he : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hnorm : ‖s‖ ≤ σ + |t| := by
    dsimp [s]
    calc
      _ ≤ ‖(σ : ℂ)‖ + ‖I * (t : ℂ)‖ := norm_add_le _ _
      _ = |σ| + |t| := by simp
      _ = σ + |t| := by rw [abs_of_pos hσpos]
  have hnormH : ‖s‖ / (H : ℝ) ≤ 3 := by
    rw [div_le_iff₀ hHpos]
    nlinarith
  have hinv : 1 / σ ≤ 2 := by
    rw [div_le_iff₀ hσpos]
    nlinarith
  have hinv2 : 1 / σ ^ 2 ≤ 4 := by
    rw [div_le_iff₀ (sq_pos_of_pos hσpos)]
    nlinarith
  have hsre : s.re = σ := by simp [s]
  have hfactor : (q : ℝ) * (m : ℝ) ^ (-σ) = P / H := by
    dsimp [P]
    have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    have hmcast : (m : ℝ) = (q : ℝ) * (H : ℝ) := by
      simp [m, H, dirichletLConductorHeightCutoff]
    rw [show -σ = (1 - σ) + (-1) by ring, Real.rpow_add (by positivity),
      Real.rpow_neg_one, hmcast, div_eq_mul_inv]
    field_simp [ne_of_gt hqpos]
  have hweight : (q : ℝ) * ‖logCpowWeight s m‖ ≤ P * L := by
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hm)
    have hw : ‖logCpowWeight s m‖ = L * (m : ℝ) ^ (-σ) := by
      rw [logCpowWeight, norm_mul, norm_neg, norm_real, Real.norm_eq_abs,
        abs_of_nonneg hL0, cpowWeight, Complex.norm_cpow_eq_rpow_re_of_pos hmpos]
      simp only [neg_re, hsre]
    calc
      (q : ℝ) * ‖logCpowWeight s m‖ = L * ((q : ℝ) * (m : ℝ) ^ (-σ)) := by
        rw [hw]
        ring
      _ = L * (P / H) := by rw [hfactor]
      _ ≤ L * P := mul_le_mul_of_nonneg_left (div_le_self hP0 hH1) hL0
      _ = P * L := by ring
  have hbudget : (q : ℝ) * logVariationBudget s m ≤ P * (14 + 6 * L) := by
    rw [logVariationBudget, hsre]
    have hinv0 : 0 ≤ 1 / σ := by positivity
    have hinner :
        (1 / σ) / (H : ℝ) + (‖s‖ / (H : ℝ)) * (L / σ + 1 / σ ^ 2) ≤
          14 + 6 * L := by
      have hfirst : (1 / σ) / (H : ℝ) ≤ 2 :=
        (div_le_self hinv0 hH1).trans hinv
      have hinv' : σ⁻¹ ≤ 2 := by simpa only [one_div] using hinv
      have hlog : L / σ ≤ 2 * L := by
        rw [div_eq_mul_inv]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hinv' hL0
      have hparen : L / σ + 1 / σ ^ 2 ≤ 2 * L + 4 := add_le_add hlog hinv2
      have hsecond : (‖s‖ / (H : ℝ)) * (L / σ + 1 / σ ^ 2) ≤
          3 * (2 * L + 4) := by
        exact mul_le_mul hnormH hparen (by positivity) (by norm_num)
      nlinarith
    calc
      (q : ℝ) * ((m : ℝ) ^ (-σ) *
          (1 / σ + ‖s‖ * (L / σ + 1 / σ ^ 2))) =
          P * ((1 / σ) / (H : ℝ) +
            (‖s‖ / (H : ℝ)) * (L / σ + 1 / σ ^ 2)) := by
              rw [← mul_assoc, hfactor]
              ring
      _ ≤ P * (14 + 6 * L) := mul_le_mul_of_nonneg_left hinner hP0
  have htail := norm_orderedLogDerivativeSeries_sub_sum_range_le
    χ hχ s (by simpa [hsre] using hσpos) (m := m) (by omega)
  calc
    _ ≤ (q : ℝ) * (‖logCpowWeight s m‖ + logVariationBudget s m) := by
      simpa [m, s] using htail
    _ = (q : ℝ) * ‖logCpowWeight s m‖ +
        (q : ℝ) * logVariationBudget s m := by ring
    _ ≤ P * L + P * (14 + 6 * L) := add_le_add hweight hbudget
    _ = P * (14 + 7 * L) := by ring
    _ ≤ 3 * (14 + 7 * L) :=
      mul_le_mul (hP.trans he.le) le_rfl (by positivity) (by norm_num)

/-- For nonprincipal `χ` mod `q` and `M = q (⌊|t|⌋ + 1)`,
`|L'(σ + it, χ)| ≤ 64 (1 + log M)²` when `1/2 ≤ σ ≤ 2` and `σ ≥ 1 - 1/log M`. -/
theorem norm_deriv_LFunction_le_one_add_log_sq
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ t : ℝ}
    (hσlower : 1 / 2 ≤ σ) (hσupper : σ ≤ 2)
    (hnear : 1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ σ) :
    ‖deriv χ.LFunction (σ + I * t)‖ ≤
      64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 := by
  let m := dirichletLConductorHeightCutoff q t
  let L : ℝ := Real.log m
  have hm : 2 ≤ m := two_le_conductorHeightCutoff χ hχ t
  have hL0 : 0 ≤ L := (log_conductorHeightCutoff_pos χ hχ t).le
  have hσpos : 0 < σ := lt_of_lt_of_le (by norm_num) hσlower
  have hseries := orderedLogDerivativeSeries_eq_deriv_LFunction_of_re_pos
    χ hχ (σ + I * t) (by simpa using hσpos)
  have hprefix := norm_derivative_prefix_le χ hχ (σ := σ) (t := t) (m := m)
    hm (by simpa [m] using hnear)
  have htail := norm_derivative_tail_le χ hχ hσlower hσupper hnear
  change ‖deriv χ.LFunction (σ + I * t)‖ ≤ 64 * (1 + L) ^ 2
  rw [← hseries]
  calc
    _ ≤ ‖orderedLogDerivativeSeries χ hχ (σ + I * t) (by simpa using hσpos) -
          ∑ k ∈ range m, logCpowWeight (σ + I * t) k * χ k‖ +
        ‖∑ k ∈ range m, logCpowWeight (σ + I * t) k * χ k‖ :=
          norm_le_norm_sub_add _ _
    _ ≤ 3 * (14 + 7 * L) + 2 * Real.exp 1 * L * (1 + L) := by
      simpa [m, L] using add_le_add htail hprefix
    _ ≤ 3 * (14 + 7 * L) + 6 * L * (1 + L) := by
      have hcoef : 2 * Real.exp 1 ≤ 6 := by
        linarith only [Real.exp_one_lt_three]
      gcongr
    _ ≤ 64 * (1 + L) ^ 2 := by
      nlinarith

end BombieriVinogradov.LDerivBound

end

section

/-! ## The half-plane `re s > 1` -/

open Complex MeasureTheory Set

namespace BombieriVinogradov

/-- `∑_{n ≥ 1} n^{-σ} ≤ 1 + 1/(σ - 1)` for `σ > 1`, by comparison with
`∫_1^∞ x^{-σ} dx`. -/
theorem tsum_nat_add_one_rpow_neg_le (σ : ℝ) (hσ : 1 < σ) :
    (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith : -σ < -1)
  have hsumm : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-σ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-σ)) 1).mpr hbase)
  rw [hsumm.tsum_eq_zero_add]
  simp only [zero_add, Nat.cast_one, Real.one_rpow]
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Ici (1 : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : -σ ≤ 0)).mono
      (Ici_subset_Ioi.2 zero_lt_one)
  have hanti' : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Ici ((1 : ℕ) : ℝ)) := by
    norm_num
    exact hanti
  have hone : (0 : ℝ) < ((1 : ℕ) : ℝ) := by norm_num
  have htail := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x ^ (-σ))
    (1 : ℕ) hanti'
    (integrableOn_Ioi_rpow_of_lt (by linarith : -σ < -1) hone)
    (fun t ht => Real.rpow_nonneg (by
      have ht' := mem_Ioi.mp ht
      norm_num at ht' ⊢
      linarith) _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -σ < -1) hone] at htail
  norm_num at htail
  have hid : -1 / (-σ + 1) = 1 / (σ - 1) := by
    rw [show -σ + 1 = -(σ - 1) by ring, div_neg]
    ring
  rw [hid] at htail
  simpa only [Nat.cast_add, Nat.cast_one, add_comm] using add_le_add_left htail 1

theorem tsum_nat_rpow_neg_le (σ : ℝ) (hσ : 1 < σ) :
    (∑' n : ℕ, (n : ℝ) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith : -σ < -1)
  rw [hbase.tsum_eq_zero_add]
  norm_num [Real.zero_rpow (by linarith : -σ ≠ 0)]
  simpa only [Nat.cast_add, Nat.cast_one, one_div] using
    tsum_nat_add_one_rpow_neg_le σ hσ

/-- `|∑ χ(n) n^{-σ-it}| ≤ 1 + 1/(σ - 1)` for `σ > 1`, uniformly in `q`, `χ` and `t`. -/
theorem norm_dirichletLSeries_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) (hσ : 1 < σ) :
    ‖LSeries (fun n : ℕ => χ n) (σ + Complex.I * t)‖ ≤ 1 + 1 / (σ - 1) := by
  have hs : 1 < (σ + Complex.I * t : ℂ).re := by simpa using hσ
  have hsum : Summable (LSeries.term (fun n : ℕ => χ n) (σ + Complex.I * t)) :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hre : (σ + Complex.I * t : ℂ).re = σ := by simp
  have hterm (n : ℕ) :
      ‖LSeries.term (fun n : ℕ => χ n) (σ + Complex.I * t) n‖ ≤ (n : ℝ) ^ (-σ) := by
    by_cases hn : n = 0
    · simp [LSeries.term, hn, Real.zero_rpow (by linarith : -σ ≠ 0)]
    · rw [LSeries.term, if_neg hn, norm_div,
        norm_natCast_cpow_of_re_ne_zero n (by rw [hre]; linarith), hre,
        Real.rpow_neg (Nat.cast_nonneg n)]
      simpa only [one_div] using
        div_le_div_of_nonneg_right (χ.norm_le_one n)
          (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
  calc
    ‖LSeries (fun n : ℕ => χ n) (σ + Complex.I * t)‖
        ≤ ∑' n, ‖LSeries.term (fun n : ℕ => χ n) (σ + Complex.I * t) n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-σ) :=
      hsum.norm.tsum_le_tsum hterm
        (Real.summable_nat_rpow.mpr (by linarith : -σ < -1))
    _ ≤ 1 + 1 / (σ - 1) := tsum_nat_rpow_neg_le σ hσ

/-- `|L(σ + it, χ)| ≤ 1 + 1/(σ - 1)` for `σ > 1`. -/
theorem norm_dirichletLFunction_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ t : ℝ) (hσ : 1 < σ) :
    ‖χ.LFunction (σ + Complex.I * t)‖ ≤ 1 + 1 / (σ - 1) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ (by simpa using hσ)]
  exact norm_dirichletLSeries_le χ σ t hσ

end BombieriVinogradov

end

section

open Complex
open ArithmeticFunction hiding log
open scoped LSeries.notation

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

/-- `-L'(s, χ)/L(s, χ) = ∑ χ(n) Λ(n) n^{-s}` for `re s > 1`. -/
lemma LSeries_twist_vonMangoldt_eq_neg_logDeriv_LFunction
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    L (↗χ * ↗vonMangoldt) s = -deriv (LFunction χ) s / LFunction χ s := by
  rw [deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs]
  exact LSeries_twist_vonMangoldt_eq χ hs

end DirichletCharacter

end
