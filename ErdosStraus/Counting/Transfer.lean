import Batteries.Tactic.Lemma
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AlmostPrime
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import ErdosStraus.Basic
import ErdosStraus.Family.Scales
import ErdosStraus.Counting.NoHit

/-!
# Theorem 5.4: the finite counting estimate

Lemma 5.1, Theorem 5.2 and the level condition (11) combine into Theorem 5.4: uniformly in
`b`, the number of `n ≤ N` with `n ≡ b (mod P(z))` lying in no event is at most
`(N/P(z)) exp(-(1-o(1))μ_b)`. The file also proves Lemma 5.3 for `1 ≤ n ≤ N`, and shows
that a bounded range of `N` is absorbed into the constant of a bound
`≪ N exp(-c (log N)^{3/4})`.
-/

namespace ErdosStraus

/-! ## Scalar lemmas -/

/-- Condition (11) bounds the error term in the proof of Theorem 5.4: if
`err ≤ X^{2R} e^{(1+ε)μ}` with `ε ≤ 1` and `P(z) X^{2R} e^{2μ} ≤ N e^{-4μ}`, then
`err ≤ (N/P(z)) e^{-4μ}`. Here `Xpow` stands for `X^{2R}`. -/
theorem error_le_level
    {errTerm Xpow μ Pz N ε : ℝ}
    (hXpow : 0 ≤ Xpow) (hμ : 0 ≤ μ) (hPz : 1 ≤ Pz)
    (herr : errTerm ≤ Xpow * Real.exp ((1 + ε) * μ))
    (hεle : ε ≤ 1)
    (hlevel : Pz * Xpow * Real.exp (2 * μ) ≤ N * Real.exp (-4 * μ)) :
    errTerm ≤ (N / Pz) * Real.exp (-4 * μ) := by
  have hPz_pos : 0 < Pz := lt_of_lt_of_le zero_lt_one hPz
  have hstep1 : Xpow * Real.exp ((1 + ε) * μ) ≤ Xpow * Real.exp (2 * μ) := by
    apply mul_le_mul_of_nonneg_left _ hXpow
    apply Real.exp_le_exp.mpr
    nlinarith [hμ, hεle]
  have hstep2 : Xpow * Real.exp (2 * μ) ≤ (N / Pz) * Real.exp (-4 * μ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hPz_pos]
    calc Xpow * Real.exp (2 * μ) * Pz
          = Pz * Xpow * Real.exp (2 * μ) := by ring
      _ ≤ N * Real.exp (-4 * μ) := hlevel
  calc errTerm ≤ Xpow * Real.exp ((1 + ε) * μ) := herr
    _ ≤ Xpow * Real.exp (2 * μ) := hstep1
    _ ≤ (N / Pz) * Real.exp (-4 * μ) := hstep2

/-- A bounded range `3 ≤ N < T` satisfies `Ered N ≤ C · N · saving c N` with
`C = 1 + ∑_{n < T} Ered n / (n · saving c n)`. -/
theorem finite_initial_saving_bound
    (Ered : ℕ → ℕ) {c : ℝ} (_hc : 0 < c) (T : ℕ) :
    ∃ Cinit : ℝ, 0 < Cinit ∧
      ∀ N : ℕ, 3 ≤ N → N < T →
        (Ered N : ℝ) ≤ Cinit * ((N : ℝ) * saving c N) := by
  classical
  let scale : ℕ → ℝ := fun n => (n : ℝ) * saving c n
  let term : ℕ → ℝ := fun n => (Ered n : ℝ) / scale n
  let Cinit : ℝ := 1 + ∑ n ∈ Finset.range T, term n
  have hterm_nonneg : ∀ n ∈ Finset.range T, 0 ≤ term n := by
    intro n _hn
    have hscale_nonneg : 0 ≤ scale n := by
      dsimp [scale, saving]
      positivity
    dsimp [term]
    exact div_nonneg (by positivity) hscale_nonneg
  have hsum_nonneg : 0 ≤ ∑ n ∈ Finset.range T, term n :=
    Finset.sum_nonneg hterm_nonneg
  refine ⟨Cinit, ?_, ?_⟩
  · dsimp [Cinit]
    linarith
  · intro N hN hNT
    have hmem : N ∈ Finset.range T := Finset.mem_range.mpr hNT
    have hterm_le_sum : term N ≤ ∑ n ∈ Finset.range T, term n :=
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

theorem canonicalBrunRank_le_floor_mass_mul {μ K : ℝ} (hμ : 1 ≤ μ) (hK : 13 ≤ K) :
    canonicalBrunRank μ ≤ ⌊K * μ⌋₊ := by
  apply Nat.le_floor
  have hμ0 : 0 ≤ μ := zero_le_one.trans hμ
  calc
    (canonicalBrunRank μ : ℝ) = (⌊12 * μ⌋₊ : ℝ) + 1 := by
      simp only [canonicalBrunRank, Nat.cast_add, Nat.cast_one]
    _ ≤ 12 * μ + 1 := add_le_add_left (Nat.floor_le (by positivity)) 1
    _ ≤ 13 * μ := by linarith
    _ ≤ K * μ := mul_le_mul_of_nonneg_right hK hμ0

end ErdosStraus

namespace ErdosStraus.ModularFamily

open Filter

/-! ## Theorem 5.4 -/

/-- The tail bound in the proof of Theorem 5.4, from `r! ≥ (r/e)^r`. -/
theorem two_mu_factorial_tail_four {μ : ℝ} {R : ℕ} (hμ : 0 ≤ μ)
    (hrank : 24 * μ ≤ (2 * R : ℝ)) :
    (2 * μ) ^ (2 * R) / ((2 * R).factorial : ℝ) ≤ Real.exp (-4 * μ) := by
  let n := 2 * R
  by_cases hn : n = 0
  · have hR : R = 0 := by dsimp [n] at hn; omega
    have hμ0 : μ = 0 := by rw [hR] at hrank; norm_num at hrank; linarith
    simp [hR, hμ0]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnμ : 24 * μ ≤ (n : ℝ) := by simpa [n, Nat.cast_mul] using hrank
  have he : Real.exp 1 ≤ (3 : ℝ) := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hquarter : 2 * μ * Real.exp 1 / (n : ℝ) ≤ 1 / 4 := by
    rw [div_le_iff₀ hnpos]
    have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * μ by positivity)
    nlinarith
  have hquarterexp : (1 / 4 : ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos 1)
      (he.trans (by norm_num : (3 : ℝ) ≤ 4))
  calc
    (2 * μ) ^ (2 * R) / ((2 * R).factorial : ℝ) ≤
        (2 * μ) ^ n / (((n : ℝ) / Real.exp 1) ^ n) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (factorial_lower_exp_self n)
    _ = (2 * μ * Real.exp 1 / (n : ℝ)) ^ n := by
      rw [← div_pow]
      congr 1
      field_simp
    _ ≤ (1 / 4 : ℝ) ^ n := pow_le_pow_left₀ (by positivity) hquarter _
    _ ≤ (Real.exp (-1)) ^ n := pow_le_pow_left₀ (by norm_num) hquarterexp _
    _ = Real.exp (-(n : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp (-4 * μ) := Real.exp_le_exp.mpr (by nlinarith)

/-- Theorem 5.4 for one family, with explicit error terms. Suppose `μ ≥ 1`,
`A(S) ≤ 2μ` for compatible `S` with `|S| ≤ 2Kμ`, `P(W = 0) ≤ e^{-(1-ε)μ}`, and the level
condition (11) with `X = B` and `R = ⌊Kμ⌋`. Then the number of `n ≤ N` with
`n ≡ b (mod P)` lying in no event is at most `(N/P)(e^{-(1-ε)μ} + 2e^{-4μ})`. -/
theorem fixed_rank_exponentials
    (E : Finset Event) (N P b B : ℕ) (K ε : ℝ)
    (hP : 0 < P) (hB : 1 ≤ B) (hK : 13 ≤ K)
    (hpos : ∀ i ∈ E, 0 < i.modulus) (hcop : ∀ i ∈ E, Nat.Coprime P i.modulus)
    (hmod : ∀ i ∈ E, i.modulus ≤ B)
    (hμ : 1 ≤ Estimates.modularMass E)
    (hext : ∀ S ∈ E.powerset, Compatible S →
      (S.card : ℝ) ≤ 2 * K * Estimates.modularMass E →
      (increment E S : ℝ) ≤ 2 * Estimates.modularMass E)
    (hprob : Estimates.modularNoHitProbability (period E) E ≤
      Real.exp (-(1 - ε) * Estimates.modularMass E))
    (hlevel : (P : ℝ) * (B : ℝ) ^ (2 * ⌊K * Estimates.modularMass E⌋₊) *
      Real.exp (2 * Estimates.modularMass E) ≤
      (N : ℝ) * Real.exp (-4 * Estimates.modularMass E)) :
    (baseNoHitCount N P b E : ℝ) ≤ (N : ℝ) / P *
      (Real.exp (-(1 - ε) * Estimates.modularMass E) +
        Real.exp (-4 * Estimates.modularMass E) + Real.exp (-4 * Estimates.modularMass E)) := by
  let μ := Estimates.modularMass E
  let R := ⌊K * μ⌋₊
  have hμ0 : 0 ≤ μ := zero_le_one.trans hμ
  have hK0 : 0 ≤ K := by linarith
  have hRupper : ((2 * R : ℕ) : ℝ) ≤ 2 * K * μ := by
    have hf := Nat.floor_le (mul_nonneg hK0 hμ0)
    dsimp [R]
    push_cast
    nlinarith
  have hcoef := coefficient_factorial_bound E hpos (2 * μ) (by positivity) (2 * R)
    (by
      intro S hS hC hcard
      apply hext S hS hC
      have hc : (S.card : ℝ) ≤ (2 * R : ℕ) := by exact_mod_cast hcard.le
      exact hc.trans hRupper)
  have hcanonical := canonicalBrunRank_le_floor_mass_mul hμ hK
  have hrank : 24 * μ ≤ (2 * R : ℝ) :=
    (twentyFour_mul_le_two_canonicalBrunRank hμ0).trans (by
      dsimp [R]
      exact_mod_cast Nat.mul_le_mul_left 2 hcanonical)
  have htail : (coefficient E (2 * R) : ℝ) ≤ Real.exp (-4 * μ) :=
    (hcoef _ le_rfl).trans (two_mu_factorial_tail_four hμ0 hrank)
  have herror := brun_envelope_of_factorial_bound_up_to
    (fun r => (coefficient E r : ℝ)) (2 * μ) (B : ℝ) (2 * R)
    (by positivity) (by exact_mod_cast hB) hcoef
  have herror' : (∑ r ∈ Finset.range (2 * R + 1),
      (B : ℝ) ^ r * (coefficient E r : ℝ)) ≤
      ((N : ℝ) / P) * Real.exp (-4 * μ) := by
    apply error_le_level (Xpow := (B : ℝ) ^ (2 * R)) (ε := 1)
      (by positivity) hμ0 (by exact_mod_cast hP) ?_ le_rfl hlevel
    convert herror using 1
    norm_num
  have hd := finite_transfer_decomposition N P b B R E hP hpos hcop hmod
  calc
    _ ≤ ((N : ℝ) / P) * (Real.exp (-(1 - ε) * μ) + Real.exp (-4 * μ)) +
        ((N : ℝ) / P) * Real.exp (-4 * μ) :=
      hd.trans (add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add hprob htail) (by positivity)) herror')
    _ = _ := by ring

/-- Theorem 5.2 over any common period `L`: if `δ ≤ 1/4`, then
`P(W = 0) ≤ exp(-μ + 2Δ)`. -/
theorem noHit_sharp_correction (L : ℕ) (E : Finset Event)
    (hL : 0 < L) (hperiod : ∀ i ∈ E, 0 < i.modulus ∧ i.modulus ∣ L)
    (hδ : Estimates.modularDelta E ≤ 1 / 4) :
    Estimates.modularNoHitProbability L E ≤
      Real.exp (-Estimates.modularMass E + Estimates.modularDependencyMass E) :=
  Conditioning.noHit_le_exp_dependency L E (Estimates.modularDelta E) hL hperiod
    (fun _ hi => Estimates.modularNeighbourMass_le_delta E hi) hδ

/-- Theorem 5.2 uniformly in `b`: if eventually `δ_b ≤ 1/4`, and `2Δ_b ≤ η μ_b` eventually
for every `η > 0`, then for every `ε > 0` eventually `P(W_b = 0) ≤ exp(-(1-ε)μ_b)`. -/
theorem noHit_uniform_near_leading
    {α β : Type*} (l : Filter α) (E : α → β → Finset Event) (Good : α → β → Prop)
    (hpos : ∀ᶠ x in l, ∀ b, Good x b → ∀ i ∈ E x b, 0 < i.modulus)
    (hδ : ∀ᶠ x in l, ∀ b, Good x b → Estimates.modularDelta (E x b) ≤ 1 / 4)
    (hdep : ∀ η : ℝ, 0 < η → ∀ᶠ x in l, ∀ b, Good x b →
      Estimates.modularDependencyMass (E x b) ≤ η * Estimates.modularMass (E x b)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, ∀ b, Good x b →
      Estimates.modularNoHitProbability (period (E x b)) (E x b) ≤
        Real.exp (-(1 - ε) * Estimates.modularMass (E x b)) := by
  intro ε hε
  filter_upwards [hpos, hδ, hdep ε hε] with x hx hδx hdepx b hb
  have hp := noHit_sharp_correction (period (E x b)) (E x b)
    (period_pos _ (hx b hb)) (fun i hi => ⟨hx b hb i hi, modulus_dvd_period hi⟩) (hδx b hb)
  exact hp.trans (Real.exp_le_exp.mpr (by linarith [hdepx b hb]))

/-- Theorem 5.4 uniformly in `b`, for moduli at most an integer `B`: under the
hypotheses of Section 5 and the level condition (11), for every `η > 0` the number of
`n ≤ N` with `n ≡ b (mod P)` lying in no event is eventually at most
`(N/P) exp(-(1-η)μ_b)`. -/
theorem finite_transfer_uniform_near_leading
    {α β : Type*} (l : Filter α) (E : α → β → Finset Event) (Good : α → β → Prop)
    (N P B : α → ℕ) (residue : α → β → ℕ) (K : ℝ) (hK : 13 ≤ K)
    (hdata : ∀ᶠ x in l, 0 < P x ∧ 1 ≤ B x ∧ ∀ b, Good x b →
      ∀ i ∈ E x b, 0 < i.modulus ∧ i.modulus ≤ B x ∧ Nat.Coprime (P x) i.modulus)
    (hmass : ∀ A : ℝ, ∀ᶠ x in l, ∀ b, Good x b → A ≤ Estimates.modularMass (E x b))
    (hext : ∀ᶠ x in l, ∀ b, Good x b → ∀ S ∈ (E x b).powerset, Compatible S →
      (S.card : ℝ) ≤ 2 * K * Estimates.modularMass (E x b) →
      (increment (E x b) S : ℝ) ≤ 2 * Estimates.modularMass (E x b))
    (hδ : ∀ᶠ x in l, ∀ b, Good x b → Estimates.modularDelta (E x b) ≤ 1 / 4)
    (hdep : ∀ η : ℝ, 0 < η → ∀ᶠ x in l, ∀ b, Good x b →
      Estimates.modularDependencyMass (E x b) ≤ η * Estimates.modularMass (E x b))
    (hlevel : ∀ᶠ x in l, ∀ b, Good x b →
      (P x : ℝ) * (B x : ℝ) ^ (2 * ⌊K * Estimates.modularMass (E x b)⌋₊) *
        Real.exp (2 * Estimates.modularMass (E x b)) ≤
          (N x : ℝ) * Real.exp (-4 * Estimates.modularMass (E x b))) :
    ∀ η : ℝ, 0 < η → ∀ᶠ x in l, ∀ b, Good x b →
      (baseNoHitCount (N x) (P x) (residue x b) (E x b) : ℝ) ≤
        (N x : ℝ) / P x * Real.exp (-(1 - η) * Estimates.modularMass (E x b)) := by
  have hpos : ∀ᶠ x in l, ∀ b, Good x b → ∀ i ∈ E x b, 0 < i.modulus := by
    filter_upwards [hdata] with x hx b hb i hi
    exact (hx.2.2 b hb i hi).1
  intro η hη
  have hprob := noHit_uniform_near_leading l E Good hpos hδ hdep (η / 2) (by positivity)
  filter_upwards [hdata, hmass 1, hmass (2 * Real.log 3 / η), hext, hprob, hlevel]
    with x hx hm hlog he hp hl b hb
  let μ := Estimates.modularMass (E x b)
  have hμ : 0 ≤ μ := zero_le_one.trans (hm b hb)
  have hF := fixed_rank_exponentials (E x b) (N x) (P x) (residue x b) (B x) K
    (η / 2) hx.1 hx.2.1 hK
    (fun i hi => (hx.2.2 b hb i hi).1)
    (fun i hi => (hx.2.2 b hb i hi).2.2)
    (fun i hi => (hx.2.2 b hb i hi).2.1) (hm b hb) (he b hb) (hp b hb) (hl b hb)
  have hlog' : 2 * Real.log 3 ≤ μ * η :=
    (div_le_iff₀ hη).mp (hlog b hb)
  have h4 : Real.exp (-4 * μ) ≤ Real.exp (-(1 - η / 2) * μ) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have habsorb : Real.exp (-(1 - η / 2) * μ) + Real.exp (-4 * μ) +
      Real.exp (-4 * μ) ≤ Real.exp (-(1 - η) * μ) := by
    calc
      _ ≤ 3 * Real.exp (-(1 - η / 2) * μ) := by linarith
      _ = Real.exp (Real.log 3 + (-(1 - η / 2) * μ)) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  exact hF.trans (mul_le_mul_of_nonneg_left habsorb (by positivity))

/-- Theorem 5.4 with a real bound `X ≥ 1` on the moduli. -/
theorem finite_transfer_real_uniform_near_leading
    {α β : Type*} (l : Filter α) (E : α → β → Finset Event) (Good : α → β → Prop)
    (N P : α → ℕ) (X : α → ℝ) (residue : α → β → ℕ) (K : ℝ) (hK : 13 ≤ K)
    (hdata : ∀ᶠ x in l, 0 < P x ∧ 1 ≤ X x ∧ ∀ b, Good x b →
      ∀ i ∈ E x b, 0 < i.modulus ∧ (i.modulus : ℝ) ≤ X x ∧
        Nat.Coprime (P x) i.modulus)
    (hmass : ∀ A : ℝ, ∀ᶠ x in l, ∀ b, Good x b → A ≤ Estimates.modularMass (E x b))
    (hext : ∀ᶠ x in l, ∀ b, Good x b → ∀ S ∈ (E x b).powerset, Compatible S →
      (S.card : ℝ) ≤ 2 * K * Estimates.modularMass (E x b) →
      (increment (E x b) S : ℝ) ≤ 2 * Estimates.modularMass (E x b))
    (hδ : ∀ᶠ x in l, ∀ b, Good x b → Estimates.modularDelta (E x b) ≤ 1 / 4)
    (hdep : ∀ η : ℝ, 0 < η → ∀ᶠ x in l, ∀ b, Good x b →
      Estimates.modularDependencyMass (E x b) ≤ η * Estimates.modularMass (E x b))
    (hlevel : ∀ᶠ x in l, ∀ b, Good x b →
      (P x : ℝ) * X x ^ (2 * ⌊K * Estimates.modularMass (E x b)⌋₊) *
        Real.exp (2 * Estimates.modularMass (E x b)) ≤
          (N x : ℝ) * Real.exp (-4 * Estimates.modularMass (E x b))) :
    ∀ η : ℝ, 0 < η → ∀ᶠ x in l, ∀ b, Good x b →
      (baseNoHitCount (N x) (P x) (residue x b) (E x b) : ℝ) ≤
        (N x : ℝ) / P x * Real.exp (-(1 - η) * Estimates.modularMass (E x b)) := by
  apply finite_transfer_uniform_near_leading l E Good N P (fun x => ⌊X x⌋₊) residue K hK
  · filter_upwards [hdata] with x hx
    refine ⟨hx.1, Nat.le_floor (by simpa using hx.2.1), ?_⟩
    intro b hb i hi
    have hd := hx.2.2 b hb i hi
    exact ⟨hd.1, Nat.le_floor hd.2.1, hd.2.2⟩
  · exact hmass
  · exact hext
  · exact hδ
  · exact hdep
  · filter_upwards [hdata, hlevel] with x hx hl b hb
    apply le_trans _ (hl b hb)
    gcongr
    exact Nat.floor_le (zero_le_one.trans hx.2.1)

end ErdosStraus.ModularFamily

/-! ## Lemma 5.3 and Theorem 5.4 for `1 ≤ n ≤ N` -/

namespace ErdosStraus.ModularFamily

open Classical ErdosStraus.Arithmetic Filter

/-- The number of `1 ≤ n ≤ N` with `n ≡ b (mod P)` lying in every event of `S`. -/
noncomputable def positiveCommonCount (N P b : ℕ) (S : Finset Event) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n => n ≡ b [MOD P] ∧ ∀ i ∈ S, i.Hits n)).card

/-- `C_r(N)` for `1 ≤ n ≤ N`: the sum of `positiveCommonCount N P b S` over `|S| = r`. -/
noncomputable def positiveRankCount (N P b : ℕ) (E : Finset Event) (r : ℕ) : ℕ :=
  ∑ S ∈ E.powersetCard r, positiveCommonCount N P b S

/-- The number of `1 ≤ n ≤ N` with `n ≡ b (mod P)` lying in no event of `E`. -/
noncomputable def positiveNoHitCount (N P b : ℕ) (E : Finset Event) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n => n ≡ b [MOD P] ∧ ∀ i ∈ E, ¬ i.Hits n)).card

theorem positiveNoHitCount_le (N P b : ℕ) (E : Finset Event) :
    positiveNoHitCount N P b E ≤ baseNoHitCount N P b E := by
  unfold positiveNoHitCount baseNoHitCount
  rw [Finset.filter_filter]
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hnrange, hn⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
    (by have := (Finset.mem_Icc.mp hnrange).2; omega), hn⟩

theorem positive_residue_lower (N q a : ℕ) (hq : 0 < q) :
    N / q ≤ ((Finset.Icc 1 N).filter (fun n => n ≡ a [MOD q])).card := by
  let r := if a % q = 0 then q else a % q
  have hrpos : 0 < r := by
    dsimp [r]
    split_ifs with h
    · exact hq
    · omega
  have hrle : r ≤ q := by
    dsimp [r]
    split_ifs
    · exact le_rfl
    · exact (Nat.mod_lt a hq).le
  have hrmod : r ≡ a [MOD q] := by
    dsimp [r]
    split_ifs with h
    · change q % q = a % q
      simp [h]
    · exact Nat.mod_modEq _ _
  have hcard := Finset.card_le_card_of_injOn (s := Finset.range (N / q))
    (t := (Finset.Icc 1 N).filter (fun n => n ≡ a [MOD q]))
    (fun k => r + k * q) (by
      intro k hk
      have hklt := Finset.mem_range.mp hk
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨by nlinarith, ?_⟩, ?_⟩
      · calc
          r + k * q ≤ (k + 1) * q := by nlinarith
          _ ≤ (N / q) * q := Nat.mul_le_mul_right q (by omega)
          _ ≤ N := Nat.div_mul_le_self _ _
      · exact (show r + k * q ≡ r [MOD q] by
          simp [Nat.ModEq, Nat.add_mod]).trans hrmod)
    (by intro x hx y hy hxy; exact Nat.eq_of_mul_eq_mul_right hq (Nat.add_left_cancel hxy))
  simpa using hcard

theorem positiveCommonCount_bounds (N P b : ℕ) (S : Finset Event) (hP : 0 < P)
    (hpos : ∀ i ∈ S, 0 < i.modulus) (hcop : ∀ i ∈ S, Nat.Coprime P i.modulus)
    (hcompat : Compatible S) :
    (N : ℚ) / P * weight S - 1 ≤ (positiveCommonCount N P b S : ℚ) ∧
      (positiveCommonCount N P b S : ℚ) ≤ (N : ℚ) / P * weight S + 1 := by
  obtain ⟨a, habase, ha⟩ := exists_base_solution S hP hpos hcop hcompat
  have heq : positiveCommonCount N P b S =
      ((Finset.Icc 1 N).filter (fun n => n ≡ a [MOD P * period S])).card := by
    unfold positiveCommonCount
    congr 1
    apply Finset.filter_congr
    intro n hn
    exact (and_congr_right (fun _ => (rows_satisfied_iff S n).symm)).trans
      (baseResidualRows_solution_iff_modEq_product P b (rows S) a n
        (base_coprime_period S hP hpos hcop) habase ((rows_satisfied_iff S a).mpr ha))
  have hq := Nat.mul_pos hP (period_pos S hpos)
  have hlow : N / (P * period S) ≤ positiveCommonCount N P b S := by
    rw [heq]
    exact positive_residue_lower N _ a hq
  have hupper : positiveCommonCount N P b S ≤ residueClassCountUpTo N (P * period S) a := by
    rw [heq]
    apply Finset.card_le_card
    intro n hn
    obtain ⟨hnrange, hnmod⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (by have := (Finset.mem_Icc.mp hnrange).2; omega), hnmod⟩
  have hfloor : (N : ℚ) / (P * period S : ℕ) - 1 ≤ (N / (P * period S) : ℕ) := by
    have hrem : ((N % (P * period S) : ℕ) : ℚ) ≤ (P * period S : ℕ) := by
      exact_mod_cast (Nat.mod_lt N hq).le
    have hdecomp : (N : ℚ) = (N % (P * period S) : ℕ) +
        (P * period S : ℕ) * (N / (P * period S) : ℕ) := by
      exact_mod_cast (Nat.mod_add_div N (P * period S)).symm
    rw [sub_le_iff_le_add, div_le_iff₀ (by exact_mod_cast hq)]
    nlinarith
  have hid : (N : ℚ) / (P * period S : ℕ) = (N : ℚ) / P * weight S := by
    simp only [Nat.cast_mul, weight]
    ring
  rw [hid] at hfloor
  refine ⟨hfloor.trans (by exact_mod_cast hlow), ?_⟩
  have hu := residueClassCountUpTo_cast_le_div_add_one N (P * period S) a hq
  have hdiv : ((N / (P * period S) : ℕ) : ℚ) ≤ (N : ℚ) / (P * period S : ℕ) := Nat.cast_div_le
  rw [hid] at hdiv
  exact (show (positiveCommonCount N P b S : ℚ) ≤ residueClassCountUpTo N (P * period S) a by
    exact_mod_cast hupper).trans (hu.trans (add_le_add hdiv le_rfl))

/-- Lemma 5.3: `|C_r(N) - (N/P) F_r| ≤ X^r F_r` when the moduli are at most `X` and
coprime to `P`. -/
theorem positiveRankCount_abs_sub_main (N P b r : ℕ) (X : ℝ) (E : Finset Event)
    (hP : 0 < P) (hX : 0 ≤ X)
    (hpos : ∀ i ∈ E, 0 < i.modulus) (hcop : ∀ i ∈ E, Nat.Coprime P i.modulus)
    (hmod : ∀ i ∈ E, (i.modulus : ℝ) ≤ X) :
    |(positiveRankCount N P b E r : ℝ) - (N : ℝ) / P * (coefficient E r : ℝ)| ≤
      X ^ r * (coefficient E r : ℝ) := by
  have hzero : ∀ S, ¬ Compatible S → positiveCommonCount N P b S = 0 := by
    intro S hS
    unfold positiveCommonCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro n hn hhit
    exact hS (compatible_of_common_hit hhit.2)
  have hrank : positiveRankCount N P b E r =
      ∑ S ∈ subsets E r, positiveCommonCount N P b S := by
    unfold positiveRankCount subsets
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun S _ => by by_cases h : Compatible S <;> simp [h, hzero])
  have hrat : |(positiveRankCount N P b E r : ℚ) - (N : ℚ) / P * coefficient E r| ≤
      (⌊X⌋₊ : ℚ) ^ r * coefficient E r := by
    rw [hrank, Nat.cast_sum, coefficient, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro S hS
    obtain ⟨hpow, hcompat⟩ := Finset.mem_filter.mp hS
    obtain ⟨hSE, hcard⟩ := Finset.mem_powersetCard.mp hpow
    obtain ⟨hlo, hup⟩ := positiveCommonCount_bounds N P b S hP
      (fun i hi => hpos i (hSE hi)) (fun i hi => hcop i (hSE hi)) hcompat
    have hone : (1 : ℚ) ≤ (⌊X⌋₊ : ℚ) ^ r * weight S := by
      simpa [hcard] using one_le_pow_weight S ⌊X⌋₊
        (fun i hi => hpos i (hSE hi)) (fun i hi => Nat.le_floor (hmod i (hSE hi)))
    exact (abs_le.mpr ⟨by linarith, by linarith⟩).trans hone
  have hc := (Rat.cast_le (K := ℝ)).mpr hrat
  push_cast at hc
  exact hc.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hX) r)
    (by exact_mod_cast coefficient_nonneg E r))

/-- Theorem 5.4 for `1 ≤ n ≤ N`. -/
theorem positive_finite_transfer_uniform_near_leading
    {α β : Type*} (l : Filter α) (E : α → β → Finset Event) (Good : α → β → Prop)
    (N P : α → ℕ) (X : α → ℝ) (residue : α → β → ℕ) (K : ℝ) (hK : 13 ≤ K)
    (hdata : ∀ᶠ x in l, 0 < P x ∧ 1 ≤ X x ∧ ∀ b, Good x b →
      ∀ i ∈ E x b, 0 < i.modulus ∧ (i.modulus : ℝ) ≤ X x ∧
        Nat.Coprime (P x) i.modulus)
    (hmass : ∀ A : ℝ, ∀ᶠ x in l, ∀ b, Good x b → A ≤ Estimates.modularMass (E x b))
    (hext : ∀ᶠ x in l, ∀ b, Good x b → ∀ S ∈ (E x b).powerset, Compatible S →
      (S.card : ℝ) ≤ 2 * K * Estimates.modularMass (E x b) →
      (increment (E x b) S : ℝ) ≤ 2 * Estimates.modularMass (E x b))
    (hδ : ∀ᶠ x in l, ∀ b, Good x b → Estimates.modularDelta (E x b) ≤ 1 / 4)
    (hdep : ∀ η : ℝ, 0 < η → ∀ᶠ x in l, ∀ b, Good x b →
      Estimates.modularDependencyMass (E x b) ≤ η * Estimates.modularMass (E x b))
    (hlevel : ∀ᶠ x in l, ∀ b, Good x b →
      (P x : ℝ) * X x ^ (2 * ⌊K * Estimates.modularMass (E x b)⌋₊) *
        Real.exp (2 * Estimates.modularMass (E x b)) ≤
          (N x : ℝ) * Real.exp (-4 * Estimates.modularMass (E x b))) :
    ∀ η : ℝ, 0 < η → ∀ᶠ x in l, ∀ b, Good x b →
      (positiveNoHitCount (N x) (P x) (residue x b) (E x b) : ℝ) ≤
        (N x : ℝ) / P x * Real.exp (-(1 - η) * Estimates.modularMass (E x b)) := by
  intro η hη
  filter_upwards [finite_transfer_real_uniform_near_leading l E Good N P X residue K hK
    hdata hmass hext hδ hdep hlevel η hη] with x hx b hb
  exact (show (positiveNoHitCount (N x) (P x) (residue x b) (E x b) : ℝ) ≤
    baseNoHitCount (N x) (P x) (residue x b) (E x b) by
      exact_mod_cast positiveNoHitCount_le (N x) (P x) (residue x b) (E x b)).trans (hx b hb)

end ErdosStraus.ModularFamily
