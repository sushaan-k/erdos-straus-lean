import Mathlib.NumberTheory.SmoothNumbers
import ErdosStraus.Estimates.Chebyshev
import ErdosStraus.Counting.Transfer
import ErdosStraus.Counting.Lifting
import ErdosStraus.Basic
import ErdosStraus.Family.Overlaps
import ErdosStraus.Family.Definition

/-!
# Theorem 2: the exceptional set for a fixed numerator

The completion of the proof in Section 6.1. Theorem 5.4 with `K = 13`, applied to the family
of Section 6 at the scale `log X = α (log N)^{1/4}` of (23) and summed over the reduced classes
modulo `P(z)`, bounds the exceptions coprime to `P(z)`. Since a representation of `m/d` for a
divisor `d ∣ n` scales to one of `m/n`, Lemma 5.5 then gives
`E_m(N) ≤ C N exp(-c (log N)^{3/4})`, and Theorem 1 is the case `m = 4`.
-/

/-! ## Representations along divisors -/

namespace ErdosStraus

open Nat Finset
open Classical

/-- If `m / p` is a sum of three positive unit fractions and `p ∣ n`, then so is
`m / n`: multiply all three denominators by `n / p`. -/
theorem fixedNumeratorRepresentable_scale_of_dvd
    (m n p : ℕ)
    (hn : 0 < n) (hp : 0 < p)
    (hdiv : p ∣ n)
    (hrep : fixedNumeratorRepresentable m p) :
    fixedNumeratorRepresentable m n := by
  rcases hrep with ⟨x, y, z, hx, hy, hz, hident⟩
  rcases hdiv with ⟨k, hk⟩
  have hkpos : 0 < k := by
    by_contra hknot
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hknot
    rw [hk, hk0, mul_zero] at hn
    exact (Nat.lt_irrefl 0 hn)
  refine ⟨k * x, k * y, k * z,
    Nat.mul_pos hkpos hx, Nat.mul_pos hkpos hy, Nat.mul_pos hkpos hz, ?_⟩
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hkpos)
  have hxQ : (x : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hx)
  have hyQ : (y : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hy)
  have hzQ : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz)
  rw [hk]
  field_simp [hpQ, hkQ, hxQ, hyQ, hzQ] at hident ⊢
  have hmul := congrArg (fun t : ℚ => (k : ℚ) ^ 3 * t) hident
  push_cast
  ring_nf at hmul ⊢
  nlinarith [hmul]

end ErdosStraus

/-! ## Completion of the proof -/

namespace ErdosStraus.FixedNumeratorMain

open Classical Filter Family ModularFamily

/-- The events of `I_b` at the scale `X`, with `b` a class modulo `P(z)`. -/
noncomputable def events (m : ℕ) (P : Params) (X : ℝ) (b : ℕ) : Finset Event :=
  FixedNumeratorFamily.modularEvents m
    (FixedNumeratorFamily.indexFinset m P X (Estimates.roughModulus X) b)

/-- The total weight `μ_b` of (17). -/
noncomputable def mass (m : ℕ) (P : Params) (X : ℝ) (b : ℕ) : ℝ :=
  Estimates.modularMass (events m P X b)

theorem mass_nonneg (m : ℕ) (P : Params) (X : ℝ) (b : ℕ) : 0 ≤ mass m P X b :=
  Finset.sum_nonneg (fun j _ => Estimates.modularEventMass_nonneg j)

theorem mass_eq_index_sum (m : ℕ) (P : Params) (X : ℝ) (b : ℕ) :
    mass m P X b = ∑ i ∈ FixedNumeratorFamily.indexFinset m P X
      (Estimates.roughModulus X) b, (1 : ℝ) / i.q := by
  exact FixedNumeratorFamily.modularMass_eq_indexMass _ _

/-- Proposition 6.6: `μ_b ≍ (log X)^3`, uniformly in the reduced classes `b`. -/
theorem mass_two_sided (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ b : ℕ, Nat.Coprime b (Estimates.roughModulus X) →
        c * (Real.log X) ^ 3 ≤ mass m P X b ∧
          mass m P X b ≤ C * (Real.log X) ^ 3 := by
  obtain ⟨c, Xc, hc, hlower⟩ := FixedNumeratorFamily.indexMass_lower m hm P
  obtain ⟨C, XC, hC, hupper⟩ := FixedNumeratorFamily.indexFinset_mass_upper_log_cube m hm P
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (max Xc XC), eventually_gt_atTop 1]
    with X hX hX1
  intro b hb
  rw [mass_eq_index_sum]
  exact ⟨hlower X ((le_max_left _ _).trans hX) hX1 b hb,
    hupper X ((le_max_right _ _).trans hX) hX1 b⟩

/-- Lemma 6.9: for every `ε > 0` and large `X`, `δ_b ≤ ε` and `Δ_b ≤ ε μ_b`, uniformly in
the reduced classes `b`. -/
theorem dependencies_eventually_small (m : ℕ) (hm : 0 < m) (P : Params)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ b : ℕ, Nat.Coprime b (Estimates.roughModulus X) →
      Estimates.modularDelta (events m P X b) ≤ ε ∧
      Estimates.modularDependencyMass (events m P X b) ≤ ε * mass m P X b := by
  filter_upwards [FixedNumeratorFamily.modularDelta_eventually_small m hm P ε hε,
    FixedNumeratorFamily.modularDependencyMass_eventually_small m hm P ε hε]
    with X hδ hΔ
  intro b hb
  refine ⟨hδ b, ?_⟩
  simpa only [mass, events, FixedNumeratorFamily.modularMass_eq_indexMass] using hΔ b hb

theorem eventual_event_data (P : Params) :
    ∀ᶠ X : ℝ in atTop, 1 < X ∧ ∀ m b : ℕ, ∀ j ∈ events m P X b,
      0 < j.modulus ∧ (j.modulus : ℝ) ≤ X ∧
        Nat.Coprime (Estimates.roughModulus X) j.modulus := by
  filter_upwards [FixedNumeratorLifting.eventual_index_data P] with X hX
  refine ⟨hX.1, ?_⟩
  intro m b j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  exact hX.2 m b i hi

theorem reduced_count_le_noHitSum (P : Params) :
    ∀ᶠ X : ℝ in atTop, ∀ m N : ℕ, 2 ≤ m →
      FixedNumeratorFamily.reducedExceptionalCount m N (Estimates.roughModulus X) ≤
        ∑ b ∈ ErdosStraus.Arithmetic.reducedResiduesMod (Estimates.roughModulus X),
          positiveNoHitCount N (Estimates.roughModulus X) b (events m P X b) := by
  obtain ⟨X₀, hsep⟩ := FixedNumeratorFamily.scale_separation P
  filter_upwards [eventually_ge_atTop X₀] with X hX
  intro m N hm
  obtain ⟨hX1, hU, _⟩ := hsep X hX
  apply (FixedNumeratorFamily.reducedExceptionalCount_le_noHitSum m hm P X
    (zero_lt_one.trans hX1) N _ (Estimates.roughModulus_pos X) hU).trans
  apply Finset.sum_le_sum
  intro b _
  unfold FixedNumeratorFamily.rowNoHitCount positiveNoHitCount
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hnrange, hnb, hno⟩ := Finset.mem_filter.mp hn
  have hbase : n ≡ b [MOD Estimates.roughModulus X] := by
    change n % _ = b % _
    rw [← hnb, Nat.mod_mod]
  refine Finset.mem_filter.mpr ⟨hnrange, hbase, ?_⟩
  intro j hj hhit
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  have hstatic := (FixedNumeratorFamily.mem_indexFinset_iff m P X _ b i
    (zero_lt_one.trans hX1)).mp hi
  exact hno i hi ((FixedNumeratorFamily.hit_iff_row
    (Nat.mul_pos hstatic.dplus_pos hstatic.p_prime.pos)).mpr hhit)

/-- The level condition in the proof of Theorem 2, with `R = ⌊13 μ⌋`: for `X ≥ e` and
`0 ≤ μ ≤ C (log X)^3`, `log P(z) + 2 R log X + 6 μ ≤ (2 + 32 C) (log X)^4`. -/
theorem level_budget {C μ : ℝ} (hC : 0 < C) (X : ℝ) (hX : Real.exp 1 ≤ X)
    (hμ : 0 ≤ μ) (hupp : μ ≤ C * (Real.log X) ^ 3) :
    Real.log (Estimates.roughModulus X : ℝ) +
      (2 * (⌊13 * μ⌋₊ : ℝ) * Real.log X + 6 * μ) ≤
        (2 + 32 * C) * (Real.log X) ^ 4 := by
  have hlog1 : 1 ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hP := log_roughModulus_le_two_zScale X (by unfold zScale; positivity)
  have hR : (⌊13 * μ⌋₊ : ℝ) ≤ 13 * μ := Nat.floor_le (by positivity)
  have h3 : (Real.log X) ^ 3 ≤ (Real.log X) ^ 4 := by
    nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ Real.log X) 3]
  have hR' : 2 * (⌊13 * μ⌋₊ : ℝ) * Real.log X ≤ 26 * C * (Real.log X) ^ 4 := by
    have := mul_le_mul_of_nonneg_right hR (by linarith : (0 : ℝ) ≤ Real.log X)
    have h4 : C * (Real.log X) ^ 3 * Real.log X = C * (Real.log X) ^ 4 := by ring
    nlinarith
  unfold zScale at hP
  nlinarith

/-- For `⌊√N⌋ ≤ M` and `N ≥ 16`, `log M ≥ (log N)/4`. -/
theorem quarter_log_le_of_sqrt_le {N M : ℕ} (hN : 16 ≤ N) (hM : Nat.sqrt N ≤ M) :
    Real.log (N : ℝ) / 4 ≤ Real.log (M : ℝ) := by
  have hs : 4 ≤ Nat.sqrt N := Nat.le_sqrt.mpr (by omega)
  have hlt : N < 4 * (M * M) := by
    have h1 := Nat.lt_succ_sqrt N
    nlinarith
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hlog : Real.log (N : ℝ) ≤ Real.log 4 + 2 * Real.log (M : ℝ) := by
    calc Real.log (N : ℝ) ≤ Real.log (4 * ((M : ℝ) * M)) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) (by exact_mod_cast hlt.le)
      _ = Real.log 4 + 2 * Real.log (M : ℝ) := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul hMpos.ne' hMpos.ne']
          ring
  have h16 : 2 * Real.log 4 ≤ Real.log (N : ℝ) := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by positivity) (by norm_num; exact_mod_cast hN)
  linarith

/-- The pairs `(N, M)` with `N → ∞` and `⌊√N⌋ ≤ M ≤ N`, along which Theorem 5.4 is applied
uniformly on the range of Lemma 5.5. -/
def scalePairs : Filter (ℕ × ℕ) :=
  Filter.comap Prod.fst atTop ⊓ Filter.principal {x | Nat.sqrt x.1 ≤ x.2 ∧ x.2 ≤ x.1}

/-- Theorem 5.4 with `K = 13`, summed over the reduced classes modulo `P(z)`, at the scale
`log X = α (log N)^{1/4}`: uniformly for `⌊√N⌋ ≤ M ≤ N`, the number of `n ≤ M` coprime to
`P(z)` with no representation is at most `M exp(-c (log X)^3 / 2)`. -/
theorem reduced_saving (m : ℕ) (hm : 2 ≤ m) (P : Params) :
    ∃ α c : ℝ, 0 < α ∧ 0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, Nat.sqrt N ≤ M → M ≤ N →
      (FixedNumeratorFamily.reducedExceptionalCount m M
        (Estimates.roughModulus (optimizationScale α N)) : ℝ) ≤
          M * Real.exp (-(c * Real.log (optimizationScale α N) ^ 3) / 2) := by
  obtain ⟨c, C, hc, hC, hmass⟩ := mass_two_sided m (by omega) P
  let D : ℝ := max 1 (2 + 32 * C)
  have hD : 1 ≤ D := le_max_left _ _
  let α : ℝ := (2 * D)⁻¹
  have hα : 0 < α := by positivity
  have hαD : (2 + 32 * C) * α ^ 4 ≤ 1 / 4 := by
    have h1 : (2 + 32 * C) ≤ D := le_max_right _ _
    have h2 : D * α ^ 4 = (16 * D ^ 3)⁻¹ := by
      simp only [α]; field_simp; ring
    have h3 : (16 * D ^ 3)⁻¹ ≤ 1 / 16 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      nlinarith [one_le_pow₀ hD (n := 3)]
    nlinarith [pow_pos hα 4]
  refine ⟨α, c, hα, hc, ?_⟩
  let Xs : ℕ → ℝ := optimizationScale α
  have hX : Tendsto (fun x : ℕ × ℕ => Xs x.1) scalePairs atTop :=
    (optimizationScale_tendsto_atTop hα).comp (tendsto_comap.mono_left inf_le_left)
  have hfst : Tendsto (fun x : ℕ × ℕ => x.1) scalePairs atTop :=
    tendsto_comap.mono_left inf_le_left
  have hpair : ∀ᶠ x in scalePairs, Nat.sqrt x.1 ≤ x.2 ∧ x.2 ≤ x.1 :=
    eventually_inf_principal.mpr (Eventually.of_forall fun _ hx => hx)
  have hcube : Tendsto (fun X : ℝ => c * (Real.log X) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop
      |>.const_mul_atTop hc
  have htransfer := positive_finite_transfer_uniform_near_leading scalePairs
    (fun x b => events m P (Xs x.1) b)
    (fun x b => Nat.Coprime b (Estimates.roughModulus (Xs x.1)))
    (fun x => x.2) (fun x => Estimates.roughModulus (Xs x.1)) (fun x => Xs x.1)
    (fun _ b => b) 13 le_rfl
    (by
      filter_upwards [hX.eventually (eventual_event_data P)] with x hx
      exact ⟨Estimates.roughModulus_pos _, hx.1.le, fun b _ i hi => hx.2 m b i hi⟩)
    (by
      intro A
      filter_upwards [hX.eventually hmass, hX.eventually (hcube.eventually_ge_atTop A)]
        with x hx hA b hb
      exact hA.trans (hx b hb).1)
    (by
      filter_upwards [hX.eventually
        (FixedNumeratorFamily.increment_eventually_le_two_mass m (by omega) P)]
        with x hx b hb S hS hC' hcard
      exact hx b hb S hS hC' (by simpa [events, show (2 : ℝ) * 13 = 26 by norm_num] using hcard))
    (by
      filter_upwards [hX.eventually (dependencies_eventually_small m (by omega) P (1 / 4)
        (by norm_num))] with x hx b hb
      exact (hx b hb).1)
    (fun η hη => by
      filter_upwards [hX.eventually (dependencies_eventually_small m (by omega) P η hη)]
        with x hx b hb
      exact (hx b hb).2)
    (by
      filter_upwards [hX.eventually hmass, hX.eventually (eventually_ge_atTop (Real.exp 1)),
        hfst.eventually (eventually_ge_atTop 16), hfst.eventually (eventually_ge_atTop 1),
        hpair] with x hmassx hXe hN16 hN1 hxpair b hb
      let μ := Estimates.modularMass (events m P (Xs x.1) b)
      have hμ0 : 0 ≤ μ := mass_nonneg m P (Xs x.1) b
      have hbudget := level_budget hC (Xs x.1) hXe hμ0 (hmassx b hb).2
      have hfour : Real.log (Xs x.1) ^ 4 = α ^ 4 * Real.log (x.1 : ℝ) :=
        CommonScale.log_scale_fourth α hN1
      have hMlog := quarter_log_le_of_sqrt_le hN16 hxpair.1
      have hlogN : 0 ≤ Real.log (x.1 : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
      have hMpos : (0 : ℝ) < x.2 := by
        have : 4 ≤ Nat.sqrt x.1 := Nat.le_sqrt.mpr (by omega)
        exact_mod_cast (by omega : 0 < x.2)
      apply finite_level_condition_of_log (R := (⌊13 * μ⌋₊ : ℝ)) (LX := Real.log (Xs x.1))
        (by exact_mod_cast Estimates.roughModulus_pos _) (by
          have : 0 < Xs x.1 := (Real.exp_pos 1).trans_le hXe
          positivity) hMpos
      · rw [Real.log_pow]; push_cast; ring
      · refine hbudget.trans (le_trans ?_ hMlog)
        rw [hfour]
        nlinarith)
  have hhalf := htransfer (1 / 2) (by norm_num)
  have hall : ∀ᶠ x in scalePairs,
      (FixedNumeratorFamily.reducedExceptionalCount m x.2
        (Estimates.roughModulus (Xs x.1)) : ℝ) ≤
          x.2 * Real.exp (-(c * Real.log (Xs x.1) ^ 3) / 2) := by
    filter_upwards [hhalf, hX.eventually (reduced_count_le_noHitSum P),
      hX.eventually hmass] with x hx hred hmassx
    let Pz := Estimates.roughModulus (Xs x.1)
    have hPz : (0 : ℝ) < Pz := by exact_mod_cast Estimates.roughModulus_pos _
    have hrow : ∀ b ∈ ErdosStraus.Arithmetic.reducedResiduesMod Pz,
        (positiveNoHitCount x.2 Pz b (events m P (Xs x.1) b) : ℝ) ≤
          (x.2 : ℝ) / Pz * Real.exp (-(c * Real.log (Xs x.1) ^ 3) / 2) := by
      intro b hb
      have hcop := ((ErdosStraus.Arithmetic.mem_reducedResiduesMod_iff _ _).mp hb).2
      apply (hx b hcop).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have := (hmassx b hcop).1
      dsimp only [mass] at this
      linarith
    have hcard : (ErdosStraus.Arithmetic.reducedResiduesMod Pz).card ≤ Pz := by
      unfold ErdosStraus.Arithmetic.reducedResiduesMod
      exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
    calc (FixedNumeratorFamily.reducedExceptionalCount m x.2 Pz : ℝ)
        ≤ ∑ b ∈ ErdosStraus.Arithmetic.reducedResiduesMod Pz,
            (positiveNoHitCount x.2 Pz b (events m P (Xs x.1) b) : ℝ) := by
          exact_mod_cast hred m x.2 hm
      _ ≤ ∑ b ∈ ErdosStraus.Arithmetic.reducedResiduesMod Pz,
            (x.2 : ℝ) / Pz * Real.exp (-(c * Real.log (Xs x.1) ^ 3) / 2) :=
          Finset.sum_le_sum hrow
      _ = (ErdosStraus.Arithmetic.reducedResiduesMod Pz).card *
            ((x.2 : ℝ) / Pz * Real.exp (-(c * Real.log (Xs x.1) ^ 3) / 2)) := by simp
      _ ≤ (Pz : ℝ) * ((x.2 : ℝ) / Pz * Real.exp (-(c * Real.log (Xs x.1) ^ 3) / 2)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = x.2 * Real.exp (-(c * Real.log (Xs x.1) ^ 3) / 2) := by field_simp
  have hN := Filter.eventually_comap.mp (eventually_inf_principal.mp hall)
  filter_upwards [hN] with N hN M hM1 hM2
  exact hN (N, M) rfl ⟨hM1, hM2⟩

theorem primorial_floor_eq_roughModulus (X : ℝ) :
    Counting.primorial ⌊zScale X⌋₊ = Estimates.roughModulus X := by
  unfold Counting.primorial Estimates.roughModulus Estimates.primeProductBelow
  congr 1
  ext p
  simp only [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hp, hprime⟩; exact ⟨⟨hprime.two_le, by omega⟩, hprime⟩
  · rintro ⟨⟨_, hp⟩, hprime⟩; exact ⟨by omega, hprime⟩

/-- Theorem 2: `E_m(N) ≤ C N exp(-c (log N)^{3/4})` for `N ≥ 3`. The exceptions coprime to
`P(z)` are bounded by `reduced_saving`, and Lemma 5.5 at the cutoff `z = α^4 log N` removes
the coprimality condition. -/
theorem exceptional_set_bound (m : ℕ) (hm : 2 ≤ m) (P : Params) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      (fixedNumeratorExceptionalCount m N : ℝ) ≤ C * (N : ℝ) * saving c N := by
  obtain ⟨α, c₀, hα, hc₀, hred⟩ := reduced_saving m hm P
  obtain ⟨cl, hcl, hlift⟩ := Counting.lifting
  let E : Set ℕ := {n | ¬fixedNumeratorRepresentable m n}
  have hE : Counting.DivisorClosed E := by
    intro n d hn hnpos hd hrep
    exact hn (fixedNumeratorRepresentable_scale_of_dvd m n d hnpos
      (Nat.pos_of_dvd_of_pos hd hnpos) hd hrep)
  let c₁ : ℝ := c₀ * α ^ 3 / 2
  have hc₁ : 0 < c₁ := by positivity
  have hloglog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop, (fixedNumeratorExceptionalCount m N : ℝ) ≤
      cl * 1 * N * Real.log (2 * (α ^ 4 * Real.log (N : ℝ))) * saving c₁ N +
        (N : ℝ) ^ (3 / 4 + 1 / 8 : ℝ) := by
    filter_upwards [hred, hlift (α ^ 4) (by positivity) (1 / 8) (by norm_num),
      hloglog.eventually (eventually_ge_atTop (2 / α ^ 4)), eventually_ge_atTop 1]
      with N hredN hliftN hlogN hN1
    have hz : zScale (optimizationScale α N) = α ^ 4 * Real.log (N : ℝ) :=
      CommonScale.log_scale_fourth α hN1
    have hcube : Real.log (optimizationScale α N) ^ 3 =
        α ^ 3 * Real.log (N : ℝ) ^ ((3 : ℝ) / 4) := CommonScale.log_scale_cube α hN1
    have hcount : (fixedNumeratorExceptionalCount m N : ℝ) = (Counting.count E N : ℝ) := by
      unfold fixedNumeratorExceptionalCount Counting.count
      congr
    rw [hcount]
    have hy2 : 2 ≤ α ^ 4 * Real.log (N : ℝ) := by
      have := (div_le_iff₀' (by positivity : (0 : ℝ) < α ^ 4)).mp hlogN
      linarith
    have hsav : Real.exp (-(c₀ * Real.log (optimizationScale α N) ^ 3) / 2) =
        saving c₁ N := by
      unfold saving; rw [hcube]; congr 1; simp only [c₁]; ring
    have hF : 0 ≤ c₀ * Real.log (optimizationScale α N) ^ 3 / 2 := by
      rw [hcube]; positivity
    have hexpF : Real.exp (-(c₀ * Real.log (optimizationScale α N) ^ 3) / 2) =
        Real.exp (-(c₀ * Real.log (optimizationScale α N) ^ 3 / 2)) := by
      congr 1; ring
    rw [← hsav, hexpF]
    refine hliftN (α ^ 4 * Real.log (N : ℝ)) hy2 le_rfl E hE 1 _ one_pos hF ?_
    · intro M hMlo hMhi
      have hM' : Nat.sqrt N ≤ ⌊M⌋₊ := by
        rw [← Real.nat_floor_real_sqrt_eq_nat_sqrt]; exact Nat.floor_mono hMlo
      have hMN : ⌊M⌋₊ ≤ N := Nat.floor_le_of_le hMhi
      have hM0 : 0 ≤ M := (Real.sqrt_nonneg _).trans hMlo
      calc _ = ((FixedNumeratorFamily.reducedExceptionalCount m ⌊M⌋₊
            (Estimates.roughModulus (optimizationScale α N)) : ℕ) : ℝ) := by
            congr 1
            unfold FixedNumeratorFamily.reducedExceptionalCount
            rw [← hz, primorial_floor_eq_roughModulus]
            congr 1
            ext n
            have hmod : Nat.Coprime (n % Estimates.roughModulus (optimizationScale α N))
                (Estimates.roughModulus (optimizationScale α N)) ↔
                Nat.Coprime n (Estimates.roughModulus (optimizationScale α N)) := by
              unfold Nat.Coprime; rw [← Nat.gcd_rec, Nat.gcd_comm]
            simp only [Finset.mem_filter, E, Set.mem_ofPred_eq, hmod]
            tauto
        _ ≤ ⌊M⌋₊ * Real.exp (-(c₀ * Real.log (optimizationScale α N) ^ 3) / 2) :=
            hredN _ hM' hMN
        _ ≤ 1 * M * Real.exp (-(c₀ * Real.log (optimizationScale α N) ^ 3 / 2)) := by
            rw [one_mul, ← hexpF]
            exact mul_le_mul_of_nonneg_right (Nat.floor_le hM0) (Real.exp_pos _).le
  obtain ⟨ca, hca, Ca, hCa, habsorb⟩ :=
    log_absorb hc₁ (Ce := cl) (C₁ := 1) hcl (by norm_num)
  obtain ⟨cp, hcp, Cp, hCp, hpoly⟩ :=
    poly_absorb (θ := 3 / 4 + 1 / 8) (by norm_num) (by norm_num) (Cs := 1) (by norm_num)
  let c := min ca cp
  have hc : 0 < c := lt_min hca hcp
  have hbound : ∀ᶠ N : ℕ in atTop, (fixedNumeratorExceptionalCount m N : ℝ) ≤
      (Ca + Cp) * ((N : ℝ) * saving c N) := by
    filter_upwards [hlarge, eventually_ge_atTop 3, eventually_ge_atTop ⌈16 * α ^ 8⌉₊]
      with N hN hN3 hNα
    have hN1 : (1 : ℕ) ≤ N := by omega
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hy : Real.log (2 * (α ^ 4 * Real.log (N : ℝ))) ≤ Real.log (N : ℝ) := by
      apply Real.log_le_log (by positivity)
      have hlog := Real.log_le_rpow_div (x := (N : ℝ)) hNpos.le (by norm_num : (0 : ℝ) < 1 / 2)
      rw [← Real.sqrt_eq_rpow] at hlog
      have hN16 : 16 * α ^ 8 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNα)
      have hroot : 4 * α ^ 4 ≤ Real.sqrt N := by
        rw [show 4 * α ^ 4 = Real.sqrt (16 * α ^ 8) by
          rw [show (16 : ℝ) * α ^ 8 = (4 * α ^ 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]]
        exact Real.sqrt_le_sqrt hN16
      have hsq := Real.mul_self_sqrt hNpos.le
      have hs0 := Real.sqrt_nonneg (N : ℝ)
      nlinarith [pow_pos hα 4]
    have hsavpos : 0 ≤ (N : ℝ) * saving c₁ N := by unfold saving; positivity
    have h1 : cl * 1 * N * Real.log (2 * (α ^ 4 * Real.log (N : ℝ))) * saving c₁ N ≤
        Ca * ((N : ℝ) * saving c N) := by
      calc cl * 1 * N * Real.log (2 * (α ^ 4 * Real.log (N : ℝ))) * saving c₁ N
          ≤ cl * Real.log N * (1 * ((N : ℝ) * saving c₁ N)) := by
            have := mul_le_mul_of_nonneg_left hy (mul_nonneg hcl.le hsavpos)
            nlinarith
        _ ≤ Ca * ((N : ℝ) * saving ca N) := habsorb N hN3
        _ ≤ Ca * ((N : ℝ) * saving c N) := by
            apply mul_le_mul_of_nonneg_left _ hCa.le
            exact mul_le_mul_of_nonneg_left
              (saving_le_saving_of_le (min_le_left _ _) hN1) hNpos.le
    have h2 : (N : ℝ) ^ (3 / 4 + 1 / 8 : ℝ) ≤ Cp * ((N : ℝ) * saving c N) := by
      calc (N : ℝ) ^ (3 / 4 + 1 / 8 : ℝ) = 1 * (N : ℝ) ^ (3 / 4 + 1 / 8 : ℝ) := by ring
        _ ≤ Cp * ((N : ℝ) * saving cp N) := hpoly N hN3
        _ ≤ Cp * ((N : ℝ) * saving c N) := by
            apply mul_le_mul_of_nonneg_left _ hCp.le
            exact mul_le_mul_of_nonneg_left
              (saving_le_saving_of_le (min_le_right _ _) hN1) hNpos.le
    linarith
  obtain ⟨T, hT⟩ := eventually_atTop.mp hbound
  obtain ⟨Cinit, hCinit, hinit⟩ :=
    finite_initial_saving_bound (fixedNumeratorExceptionalCount m) hc T
  refine ⟨c, max (Ca + Cp) Cinit, hc, (add_pos hCa hCp).trans_le (le_max_left _ _), ?_⟩
  intro N hN
  have hscale : 0 ≤ (N : ℝ) * saving c N := by unfold saving; positivity
  by_cases hTN : T ≤ N
  · apply (hT N hTN).trans
    convert mul_le_mul_of_nonneg_right (le_max_left (Ca + Cp) Cinit) hscale using 1
    ring
  · apply (hinit N hN (lt_of_not_ge hTN)).trans
    convert mul_le_mul_of_nonneg_right (le_max_right (Ca + Cp) Cinit) hscale using 1
    ring

theorem main_bound (m : ℕ) (hm : 2 ≤ m) (P : Params) :
    IsMainBound (fixedNumeratorExceptionalCount m) := by
  obtain ⟨c, C, hc, hC, hbound⟩ := exceptional_set_bound m hm P
  exact ⟨c, hc, C, hC, hbound⟩

/-- `E(N) ≤ E_4(N)`. -/
theorem exceptionalCount_le_fixedNumerator_four (N : ℕ) :
    exceptionalCount N ≤ fixedNumeratorExceptionalCount 4 N := by
  unfold exceptionalCount fixedNumeratorExceptionalCount
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hrange, hex⟩ := Finset.mem_filter.mp hn
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨by have := (Finset.mem_Icc.mp hrange).1; omega,
      (Finset.mem_Icc.mp hrange).2⟩, ?_⟩
  exact hex

/-- Theorem 1: the case `m = 4` of Theorem 2. -/
theorem ordinary_main_bound (P : Params) : IsMainBound exceptionalCount := by
  obtain ⟨c, hc, C, hC, hbound⟩ := main_bound 4 (by norm_num) P
  refine ⟨c, hc, C, hC, ?_⟩
  intro N hN
  exact (Nat.cast_le.mpr (exceptionalCount_le_fixedNumerator_four N)).trans (hbound N hN)

end ErdosStraus.FixedNumeratorMain
