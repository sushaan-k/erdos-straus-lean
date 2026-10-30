import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic
import ErdosStraus.Congruences.Certificates
import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.Harmonic.Bounds
import Batteries.Tactic.Lemma
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AlmostPrime
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Analysis.PSeries

/-!
# Parameters, scales and exceptional sets

The parameters `η, σ, λ, θ, β` of (4) with the inequalities used in the proof, the
scales `z = (log X)^4`, `U = (log X)^8`, `S₀ = X^η`, `Y₀ = X^λ`, `Y = X^σ` and
`H = X^θ`, and the divisors `e = rs²` with `rad(e) = rs` of Section 6. The file
also defines the counting function `E(N)` of Theorem 1 with the bound
`E(N) ≪ N exp(-c (log N)^{3/4})`, the prime product `P(z)`, and two-sided
asymptotics `f ≍ g`.
-/

namespace ErdosStraus

open scoped BigOperators
open Filter

/-! ## Parameters -/

/-- Real parameters `η, σ, λ, θ, β > 0` with `β < 1`, `3η < λ`, `η + σ < λ`,
`λ + η < θ` and `2θ < β < 1 - σ`, as in (4). -/
structure Params where
  η : ℝ
  σ : ℝ
  lam : ℝ
  θ : ℝ
  β : ℝ
  η_pos : 0 < η
  σ_pos : 0 < σ
  lam_pos : 0 < lam
  θ_pos : 0 < θ
  β_pos : 0 < β
  β_lt_one : β < 1
  three_η_lt_lam : 3 * η < lam
  η_add_σ_lt_lam : η + σ < lam
  lam_add_η_lt_θ : lam + η < θ
  two_θ_lt_β : 2 * θ < β
  β_lt_one_sub_σ : β < 1 - σ

namespace Params

/-- The values fixed in (4): `η = 1/100`, `σ = 1/20`, `λ = 1/10`, `θ = 3/10`,
`β = 2/3`. -/
noncomputable def explicit : Params where
  η := 1 / 100
  σ := 1 / 20
  lam := 1 / 10
  θ := 3 / 10
  β := 2 / 3
  η_pos := by norm_num
  σ_pos := by norm_num
  lam_pos := by norm_num
  θ_pos := by norm_num
  β_pos := by norm_num
  β_lt_one := by norm_num
  three_η_lt_lam := by norm_num
  η_add_σ_lt_lam := by norm_num
  lam_add_η_lt_θ := by norm_num
  two_θ_lt_β := by norm_num
  β_lt_one_sub_σ := by norm_num

variable (P : Params)

/-- `σ < λ`, so that `Y₀ = X^λ > X^σ = Y`, as in (13). -/
theorem σ_lt_lam : P.σ < P.lam :=
  lt_of_le_of_lt (le_add_of_nonneg_left P.η_pos.le) P.η_add_σ_lt_lam

theorem σ_lt_θ : P.σ < P.θ := by
  have h1 : P.σ < P.lam := P.σ_lt_lam
  have h2 : P.lam < P.θ := lt_of_le_of_lt (le_add_of_nonneg_right P.η_pos.le) P.lam_add_η_lt_θ
  exact h1.trans h2

end Params

/-! ## Scales -/

/-- Sieve threshold `z = (log X)^4`. -/
noncomputable def zScale (X : ℝ) : ℝ := (Real.log X) ^ 4
/-- `U = (log X)^8`, the cap on the small divisor `d₋`. -/
noncomputable def UScale (X : ℝ) : ℝ := (Real.log X) ^ 8
/-- `S₀ = X^η`, the cap on `s`. -/
noncomputable def SScale (P : Params) (X : ℝ) : ℝ := X ^ P.η
/-- `Y₀ = X^λ`, the lower bound for `rs`. -/
noncomputable def Y0Scale (P : Params) (X : ℝ) : ℝ := X ^ P.lam
/-- `Y = X^σ`, the cap on `d₋d₊`. -/
noncomputable def YScale (P : Params) (X : ℝ) : ℝ := X ^ P.σ
/-- `H = X^θ`, the cap on `e`. -/
noncomputable def HScale (P : Params) (X : ℝ) : ℝ := X ^ P.θ

/-- `Y < Y₀` for `X > 1`. -/
theorem YScale_lt_Y0Scale (P : Params) {X : ℝ} (hX : 1 < X) :
    YScale P X < Y0Scale P X := by
  unfold YScale Y0Scale
  exact Real.rpow_lt_rpow_left_iff hX |>.mpr P.σ_lt_lam

/-! ## The divisors `e = rs²` -/

/-- Coprime squarefree numbers `r, s`, representing `e = rs²` as in the definition
of the set `𝓕` in Section 6. The ranges (12) are imposed separately. -/
structure ExactDivisor where
  r : ℕ
  s : ℕ
  r_squarefree : Squarefree r
  s_squarefree : Squarefree s
  coprime_rs : Nat.Coprime r s

namespace ExactDivisor

/-- `e = rs²`. -/
def e (E : ExactDivisor) : ℕ := E.r * E.s ^ 2
/-- `rad(e) = rs`. -/
def rho (E : ExactDivisor) : ℕ := E.r * E.s

theorem rho_squarefree (E : ExactDivisor) : Squarefree E.rho := by
  unfold rho
  exact (Nat.squarefree_mul E.coprime_rs).mpr ⟨E.r_squarefree, E.s_squarefree⟩

theorem prime_dvd_rho_iff_dvd_e (E : ExactDivisor) (p : ℕ) (hp : p.Prime) :
    p ∣ E.rho ↔ p ∣ E.e := by
  unfold rho e
  constructor
  · intro h
    rcases hp.dvd_mul.mp h with hr | hs
    · exact dvd_mul_of_dvd_left hr (E.s ^ 2)
    · have hsSq : E.s ∣ E.s ^ 2 := dvd_pow_self E.s (by norm_num)
      exact dvd_mul_of_dvd_right (hs.trans hsSq) E.r
  · intro h
    rcases hp.dvd_mul.mp h with hr | hsSq
    · exact dvd_mul_of_dvd_left hr E.s
    · exact dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow hsSq) E.r

/-- `rad(e)` is determined by `e`. -/
theorem rho_eq_of_e_eq (E F : ExactDivisor) (h : E.e = F.e) :
    E.rho = F.rho := by
  apply (Nat.Squarefree.ext_iff (rho_squarefree E) (rho_squarefree F)).2
  intro p hp
  rw [prime_dvd_rho_iff_dvd_e E p hp,
    prime_dvd_rho_iff_dvd_e F p hp, h]

/-- If `rs > 0`, the coordinates `r, s` are determined by `e = rs²`. -/
theorem eq_of_e_eq_of_rho_pos (E F : ExactDivisor) (he : E.e = F.e)
    (hrho : 0 < E.rho) : E = F := by
  have hrhoEq : E.rho = F.rho := rho_eq_of_e_eq E F he
  have hEfactor : E.e = E.rho * E.s := by
    unfold e rho
    ring
  have hFfactor : F.e = F.rho * F.s := by
    unfold e rho
    ring
  have hsMul : E.rho * E.s = E.rho * F.s := by
    calc
      E.rho * E.s = E.e := hEfactor.symm
      _ = F.e := he
      _ = F.rho * F.s := hFfactor
      _ = E.rho * F.s := by rw [hrhoEq]
  have hs : E.s = F.s := Nat.eq_of_mul_eq_mul_left hrho hsMul
  have hsPos : 0 < E.s := Nat.pos_of_mul_pos_left hrho
  have hrMul : E.r * E.s = F.r * E.s := by
    calc
      E.r * E.s = E.rho := rfl
      _ = F.rho := hrhoEq
      _ = F.r * F.s := rfl
      _ = F.r * E.s := by rw [hs]
  have hr : E.r = F.r := Nat.eq_of_mul_eq_mul_right hsPos hrMul
  cases E
  cases F
  simp_all

theorem e_dvd_sq_of_rho_dvd (E : ExactDivisor) {a : ℕ} (h : E.rho ∣ a) : E.e ∣ a ^ 2 := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨E.r * k ^ 2, ?_⟩
  unfold e rho
  ring

/-- `1/rad(e) = (1/r)(1/s)`, used for the sum `M₁` of Proposition 6.2. -/
theorem one_div_rho_cast_eq (E : ExactDivisor) (hr : 0 < E.r) (hs : 0 < E.s) :
    (1 : ℝ) / (E.rho : ℝ) = ((1 : ℝ) / (E.r : ℝ)) * ((1 : ℝ) / (E.s : ℝ)) := by
  have hrR : (E.r : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  have hsR : (E.s : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  unfold rho
  rw [Nat.cast_mul]
  field_simp [hrR, hsR]

/-- `1/φ(rad(e)) = (1/φ(r))(1/φ(s))`, used for the sum `M_φ` of
Proposition 6.2. -/
theorem one_div_totient_rho_cast_eq
    (E : ExactDivisor) (hr : 0 < E.r) (hs : 0 < E.s) :
    (1 : ℝ) / (Nat.totient E.rho : ℝ) =
      ((1 : ℝ) / (Nat.totient E.r : ℝ)) *
        ((1 : ℝ) / (Nat.totient E.s : ℝ)) := by
  have htot_r : (Nat.totient E.r : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Nat.totient_pos.mpr hr)
  have htot_s : (Nat.totient E.s : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Nat.totient_pos.mpr hs)
  unfold rho
  rw [Nat.totient_mul E.coprime_rs, Nat.cast_mul]
  field_simp [htot_r, htot_s]

end ExactDivisor

end ErdosStraus

/-! ## Exceptional sets -/

namespace ErdosStraus

open scoped BigOperators
open Classical

/-- `E(N)`, the number of `2 ≤ n ≤ N` for which `4/n` is not a sum of three unit
fractions. -/
noncomputable def exceptionalCount (N : ℕ) : ℕ :=
  ((Finset.Icc 2 N).filter (fun n => ErdosStraus.Arithmetic.esExceptional n)).card

/-- The number of primes `p ≤ N` for which `4/p` is not a sum of three unit
fractions. -/
noncomputable def primeExceptionalCount (N : ℕ) : ℕ :=
  ((Finset.Icc 2 N).filter (fun n => n.Prime ∧ ErdosStraus.Arithmetic.esExceptional n)).card

/-- The saving `exp(-c (log N)^{3/4})` of Theorem 1. -/
noncomputable def saving (c : ℝ) (N : ℕ) : ℝ :=
  Real.exp (-c * (Real.log N) ^ ((3 : ℝ) / 4))

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

theorem rpow_four_thirds_le {t : ℝ} (ht : 0 ≤ t) :
    t ^ ((4 : ℝ) / 3) ≤ 1 + t ^ 2 := by
  rcases le_or_gt t 1 with h | h
  · calc t ^ ((4 : ℝ) / 3) ≤ 1 ^ ((4 : ℝ) / 3) :=
            Real.rpow_le_rpow ht h (by norm_num)
      _ = 1 := by simp
      _ ≤ 1 + t ^ 2 := by nlinarith
  · have h1 : t ^ ((4 : ℝ) / 3) ≤ t ^ ((2 : ℝ)) :=
      (Real.rpow_le_rpow_left_iff h).mpr (by norm_num)
    calc t ^ ((4 : ℝ) / 3) ≤ t ^ ((2 : ℝ)) := h1
      _ = t ^ 2 := Real.rpow_two t
      _ ≤ 1 + t ^ 2 := by nlinarith

theorem rpow_three_quarters_four_thirds {L : ℝ} (hL : 0 ≤ L) :
    (L ^ ((3 : ℝ) / 4)) ^ ((4 : ℝ) / 3) = L := by
  rw [← Real.rpow_mul hL]
  norm_num

theorem log_ge_of_three_le {N : ℕ} (hN : 3 ≤ N) : (2 : ℝ) / 3 ≤ Real.log N := by
  have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hmono : Real.log 3 ≤ Real.log N := Real.log_le_log (by norm_num) h3
  have h3' : (2 : ℝ) / 3 ≤ Real.log 3 := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 by norm_num)
    norm_num at this ⊢
    linarith
  linarith

theorem log_pos_of_three_le {N : ℕ} (hN : 3 ≤ N) : 0 < Real.log N := by
  have := log_ge_of_three_le hN
  linarith

/-- `f(N) ≪ N exp(-c (log N)^{3/4})`: there are constants `c, C > 0` with
`f(N) ≤ C N exp(-c (log N)^{3/4})` for all `N ≥ 3`. -/
def IsMainBound (f : ℕ → ℕ) : Prop :=
  ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N : ℕ, 3 ≤ N → (f N : ℝ) ≤ C * N * saving c N

theorem IsMainBound.of_le {f g : ℕ → ℕ} (hfg : ∀ N, f N ≤ g N)
    (hg : IsMainBound g) : IsMainBound f := by
  obtain ⟨c, hc, C, hC, h⟩ := hg
  refine ⟨c, hc, C, hC, fun N hN => ?_⟩
  exact le_trans (by exact_mod_cast hfg N) (h N hN)

theorem primeExceptionalCount_le (N : ℕ) :
    primeExceptionalCount N ≤ exceptionalCount N := by
  classical
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.2⟩

end ErdosStraus

namespace ErdosStraus

/-- The saving `exp(-c (log N)^{3/4})` decreases in `c`. -/
theorem saving_le_saving_of_le
    {c d : ℝ} (hdc : d ≤ c) {N : ℕ} (hN : 1 ≤ N) :
    saving c N ≤ saving d N := by
  unfold saving
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hpow : 0 ≤ (Real.log (N : ℝ)) ^ ((3 : ℝ) / 4) :=
    Real.rpow_nonneg hlog _
  nlinarith

end ErdosStraus

/-! ## Prime products and summation windows -/

namespace ErdosStraus.Estimates

open scoped BigOperators Pointwise

/-- The positive integers `n` with `U₀ < n ≤ U₁`. -/
noncomputable def natWindow (U₀ U₁ : ℝ) : Finset ℕ :=
  (Finset.Icc (1 : ℕ) ⌊U₁⌋₊).filter (fun n => U₀ < (n : ℝ))

/-- `P(z)`, the product of the primes `ℓ ≤ z`. -/
noncomputable def primeProductBelow (z : ℝ) : ℕ :=
  ∏ ℓ ∈ (Finset.Icc (2 : ℕ) ⌊z⌋₊).filter (fun ℓ => Nat.Prime ℓ), ℓ

theorem finite_prime_product_squarefree (s : Finset ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p) :
    Squarefree (∏ p ∈ s, p) := by
  classical
  revert hs
  refine Finset.induction_on s ?empty ?insert
  · intro _hs
    simp
  · intro p s hps ih hs
    rw [Finset.prod_insert hps]
    have hp : Nat.Prime p := hs p (Finset.mem_insert_self p s)
    have hs_primes : ∀ q ∈ s, Nat.Prime q := by
      intro q hq
      exact hs q (Finset.mem_insert_of_mem hq)
    have hs_sqf : Squarefree (∏ q ∈ s, q) := ih hs_primes
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      rw [hp.coprime_iff_not_dvd]
      intro hdiv
      have hnz : ∏ q ∈ s, q ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun q hq => (hs_primes q hq).ne_zero)
      have hpf : p ∈ Nat.primeFactors (∏ q ∈ s, q) :=
        (Nat.mem_primeFactors).mpr ⟨hp, hdiv, hnz⟩
      rw [Nat.primeFactors_prod hs_primes] at hpf
      exact hps hpf
    exact (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, hs_sqf⟩

theorem primeProductBelow_squarefree (z : ℝ) : Squarefree (primeProductBelow z) := by
  classical
  unfold primeProductBelow
  apply finite_prime_product_squarefree
  intro ℓ hℓ
  exact (Finset.mem_filter.mp hℓ).2

theorem primeProductBelow_pos (z : ℝ) : 0 < primeProductBelow z :=
  Nat.pos_of_ne_zero (primeProductBelow_squarefree z).ne_zero

theorem primeProductBelow_primeFactors_eq (z : ℝ) :
    (primeProductBelow z).primeFactors =
      (Finset.Icc (2 : ℕ) ⌊z⌋₊).filter (fun p => Nat.Prime p) := by
  classical
  unfold primeProductBelow
  apply Nat.primeFactors_prod
  intro p hp
  exact (Finset.mem_filter.mp hp).2

theorem prime_dvd_primeProductBelow_of_le_floor (z : ℝ) (p : ℕ)
    (hp : Nat.Prime p) (hp_le : p ≤ ⌊z⌋₊) :
    p ∣ primeProductBelow z := by
  classical
  unfold primeProductBelow
  apply Finset.dvd_prod_of_mem
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hp.two_le, hp_le⟩, hp⟩

/-- A squarefree `d ≤ z` divides `P(z)`, since every prime factor of `d` is at
most `d`. -/
theorem squarefree_dvd_primeProductBelow_of_le_floor
    (z : ℝ) {d : ℕ} (hd : Squarefree d) (hd_le : d ≤ ⌊z⌋₊) :
    d ∣ primeProductBelow z := by
  classical
  let s := (Finset.Icc (2 : ℕ) ⌊z⌋₊).filter (fun q => Nat.Prime q)
  have hsubset : d.primeFactors ⊆ s := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
    have hple_d : p ≤ d :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hd.ne_zero) hpdvd
    exact ⟨⟨hprime.two_le, le_trans hple_d hd_le⟩, hprime⟩
  have hprod_sdiff := Finset.prod_sdiff hsubset (f := fun p : ℕ => p)
  have hprod_dvd : (∏ p ∈ d.primeFactors, p) ∣ (∏ p ∈ s, p) := by
    rw [← hprod_sdiff]
    exact dvd_mul_left _ _
  rw [← Nat.prod_primeFactors_of_squarefree hd]
  simpa [primeProductBelow, s] using hprod_dvd

/-- `P(z)` with `z = (log X)^4`. -/
noncomputable def roughModulus (X : ℝ) : ℕ :=
  primeProductBelow (ErdosStraus.zScale X)

theorem roughModulus_squarefree (X : ℝ) : Squarefree (roughModulus X) := by
  unfold roughModulus
  exact primeProductBelow_squarefree (ErdosStraus.zScale X)

theorem roughModulus_pos (X : ℝ) : 0 < roughModulus X :=
  Nat.pos_of_ne_zero (roughModulus_squarefree X).ne_zero

theorem prime_dvd_roughModulus_le_floor_zScale
    (X : ℝ) {p : ℕ} (hp : Nat.Prime p) (hdiv : p ∣ roughModulus X) :
    p ≤ ⌊ErdosStraus.zScale X⌋₊ := by
  have hmem : p ∈ (roughModulus X).primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨hp, hdiv, Nat.ne_of_gt (roughModulus_pos X)⟩
  rw [roughModulus, primeProductBelow_primeFactors_eq] at hmem
  exact (Finset.mem_Icc.mp (Finset.mem_of_mem_filter p hmem)).2

/-- Congruence `n ≡ b (mod D)`, defined by `n % D = b % D`; for `D = 0` it is
equality. -/
def congMod (n b D : ℕ) : Prop :=
  n % D = b % D

end ErdosStraus.Estimates

namespace ErdosStraus.SieveEstimates

open scoped BigOperators
open ErdosStraus.Estimates

/-- For `U₀ ≥ 0`, the integers in `(U₀, U₁]` form `[⌊U₀⌋ + 1, ⌊U₁⌋ + 1)`. -/
theorem natWindow_eq_Ico {U₀ U₁ : ℝ} (hU₀ : 0 ≤ U₀) :
    natWindow U₀ U₁ = Finset.Ico (⌊U₀⌋₊ + 1) (⌊U₁⌋₊ + 1) := by
  classical
  ext n
  simp only [natWindow, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨hn1, hnU⟩, hnlo⟩
    exact ⟨by have := (Nat.floor_lt hU₀).mpr hnlo; omega, by omega⟩
  · rintro ⟨hnL, hnU⟩
    exact ⟨⟨by omega, by omega⟩, (Nat.floor_lt hU₀).mp (by omega)⟩

end ErdosStraus.SieveEstimates

/-! ## Two-sided asymptotics -/

namespace ErdosStraus

open Filter
open scoped BigOperators

/-- `f ≍ g` for `X ≥ X₀`: constants `c, C > 0` with `c g(X) ≤ f(X) ≤ C g(X)` and
`f(X) ≥ 0` for `X ≥ X₀`. The constants and the threshold are part of the data. -/
structure FactorAsymp (f g : ℝ → ℝ) where
  /-- lower constant -/
  c : ℝ
  /-- upper constant -/
  C : ℝ
  /-- threshold beyond which the bounds hold -/
  X₀ : ℝ
  c_pos : 0 < c
  C_pos : 0 < C
  /-- `f` is nonnegative for `X ≥ X₀`. -/
  f_nonneg : ∀ X : ℝ, X₀ ≤ X → 0 ≤ f X
  /-- `c g(X) ≤ f(X) ≤ C g(X)` for `X ≥ X₀`. -/
  sandwich : ∀ X : ℝ, X₀ ≤ X → c * g X ≤ f X ∧ f X ≤ C * g X

namespace FactorAsymp

theorem lower {f g : ℝ → ℝ} (h : FactorAsymp f g) {X : ℝ} (hX : h.X₀ ≤ X) :
    h.c * g X ≤ f X := (h.sandwich X hX).1

theorem upper {f g : ℝ → ℝ} (h : FactorAsymp f g) {X : ℝ} (hX : h.X₀ ≤ X) :
    f X ≤ h.C * g X := (h.sandwich X hX).2

end FactorAsymp

/-- `(log X)²`. -/
noncomputable def logSq (X : ℝ) : ℝ := (Real.log X) ^ 2

theorem fixedNat_le_rpow_eventually_threshold
    (M : ℕ) {C : ℝ} (hC : 0 < C) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → (M : ℝ) ≤ X ^ C := by
  exact Filter.eventually_atTop.mp
    ((_root_.tendsto_rpow_atTop hC).eventually
      (Filter.eventually_ge_atTop (M : ℝ)))

end ErdosStraus
