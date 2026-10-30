import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic
import ErdosStraus.Estimates.WeightedSums

/-!
# Euler products over the primes below `z`

For squarefree `d`, `∑_{g ∣ d} 1/g = ∏_{p ∣ d} (1 + 1/p)`. Applied to `d = P(z)` this gives
`∏_{p ≤ z} (1 - 1/p) ≍ 1/log z`. The upper bound combines `(φ(P)/P) ∑_{d ∣ P} 1/d ≤ 1` with
`∑ φ(d)/d² ≫ log z` over the small odd divisors `d` of `P = P(z)`; the lower bound uses
`∏_{p ≤ z} (1 - p⁻²) ≥ 1/4` and Mertens' estimate `∑_{p ≤ z} 1/p ≤ log log z + O(1)`
(Lemma 3.1). The file also bounds the number of prime factors larger than `z` of an
auxiliary modulus `M`, and defines the sum of Lemma 3.4.
-/

namespace ErdosStraus.Estimates

/-! ## Reciprocal divisor sums -/

section

open scoped BigOperators

/-- The arithmetic function `n ↦ 1/n`, with value `0` at `0`. -/
noncomputable def recipArithmeticFunction : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (n : ℝ)⁻¹, by simp⟩

@[simp]
theorem recipArithmeticFunction_apply_pos {n : ℕ} (hn : 0 < n) :
    recipArithmeticFunction n = (n : ℝ)⁻¹ := by
  simp [recipArithmeticFunction, Nat.ne_of_gt hn]

theorem recipArithmeticFunction_isMultiplicative :
    ArithmeticFunction.IsMultiplicative recipArithmeticFunction := by
  constructor
  · simp [recipArithmeticFunction]
  · intro m n _hcop
    by_cases hm : m = 0
    · simp [recipArithmeticFunction, hm]
    by_cases hn : n = 0
    · simp [recipArithmeticFunction, hn]
    have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simp [recipArithmeticFunction, hm, hn, hmn, Nat.cast_mul]
    field_simp [hmR, hnR]

theorem divisor_recip_sum_eq_primeFactorProduct_one_add_inv
    {d : ℕ} (hsqf : Squarefree d) :
    (∑ g ∈ d.divisors, (1 : ℝ) / (g : ℝ)) =
      ∏ p ∈ d.primeFactors, (1 + (p : ℝ)⁻¹) := by
  classical
  have h :=
    ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_add_of_squarefree
      (f := recipArithmeticFunction)
      recipArithmeticFunction_isMultiplicative hsqf
  calc
    (∑ g ∈ d.divisors, (1 : ℝ) / (g : ℝ))
        = ∑ g ∈ d.divisors, recipArithmeticFunction g := by
            apply Finset.sum_congr rfl
            intro g hg
            rw [recipArithmeticFunction_apply_pos (Nat.pos_of_mem_divisors hg)]
            simp [one_div]
    _ = ∏ p ∈ d.primeFactors, (1 + recipArithmeticFunction p) := h.symm
    _ = ∏ p ∈ d.primeFactors, (1 + (p : ℝ)⁻¹) := by
          apply Finset.prod_congr rfl
          intro p hp
          rw [recipArithmeticFunction_apply_pos
            (Nat.prime_of_mem_primeFactors hp).pos]

theorem prod_one_sub_inv_mul_divisorRecip_eq
    {d : ℕ} (hsqf : Squarefree d) :
    (∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)) *
        (∑ g ∈ d.divisors, (1 : ℝ) / (g : ℝ)) =
      ∏ p ∈ d.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹) := by
  classical
  rw [divisor_recip_sum_eq_primeFactorProduct_one_add_inv hsqf,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hpR_ne : (p : ℝ) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
  field_simp [hpR_ne]
  ring

end

section

open Filter Asymptotics
open scoped BigOperators Pointwise

/-! ## The auxiliary modulus -/

/-- The auxiliary modulus `max 1 M` of Lemma 3.4. Replacing `0` by `1` makes `M = 0` impose
no condition, whereas `Nat.Coprime n 0` holds only for `n = 1`. -/
def auxiliaryModulus (M : ℕ) : ℕ := max 1 M

theorem auxiliaryModulus_pos (M : ℕ) : 0 < auxiliaryModulus M := by
  simp [auxiliaryModulus]

theorem auxiliaryModulus_eq_self_of_pos {M : ℕ} (hM : 0 < M) :
    auxiliaryModulus M = M := by
  simp [auxiliaryModulus, Nat.succ_le_iff.mpr hM]

/-- If every prime factor of `m ≠ 0` divides `P`, then `(n, P) = 1` implies
`(n, m) = 1`. -/
theorem coprime_of_primeFactors_subset_right
    {n m P : ℕ} (hm : m ≠ 0) (hsub : m.primeFactors ⊆ P.primeFactors)
    (hcop : Nat.Coprime n P) :
    Nat.Coprime n m := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hg
  rcases Nat.exists_prime_and_dvd hg with ⟨p, hp, hpg⟩
  have hpn : p ∣ n := Nat.dvd_trans hpg (Nat.gcd_dvd_left n m)
  have hpm : p ∣ m := Nat.dvd_trans hpg (Nat.gcd_dvd_right n m)
  have hpmem : p ∈ m.primeFactors := (Nat.mem_primeFactors).mpr ⟨hp, hpm, hm⟩
  have hpP : p ∣ P := Nat.dvd_of_mem_primeFactors (hsub hpmem)
  have hp_gcd : p ∣ Nat.gcd n P := Nat.dvd_gcd hpn hpP
  rw [hcop.gcd_eq_one] at hp_gcd
  exact hp.not_dvd_one hp_gcd

/-- The product of the primes that divide `max 1 M` but not `P(z)`. For `n` coprime to
`P(z)`, coprimality to `max 1 M` is coprimality to this squarefree number. -/
noncomputable def auxiliaryTailModulus (X : ℝ) (M : ℕ) : ℕ :=
  ∏ p ∈ (auxiliaryModulus M).primeFactors.filter
    (fun p => p ∉ (roughModulus X).primeFactors), p

theorem auxiliaryTailModulus_pos (X : ℝ) (M : ℕ) :
    0 < auxiliaryTailModulus X M := by
  classical
  unfold auxiliaryTailModulus
  exact Finset.prod_pos (fun p hp => by
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos)

theorem auxiliaryTailModulus_primeFactors
    (X : ℝ) (M : ℕ) :
    (auxiliaryTailModulus X M).primeFactors =
      (auxiliaryModulus M).primeFactors.filter
        (fun p => p ∉ (roughModulus X).primeFactors) := by
  classical
  unfold auxiliaryTailModulus
  rw [Nat.primeFactors_prod]
  intro p hp
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

theorem auxiliaryTailModulus_primeFactors_subset_auxiliary
    (X : ℝ) (M : ℕ) :
    (auxiliaryTailModulus X M).primeFactors ⊆
      (auxiliaryModulus M).primeFactors := by
  classical
  rw [auxiliaryTailModulus_primeFactors]
  exact Finset.filter_subset _ _

theorem auxiliaryTailModulus_dvd_auxiliaryModulus
    (X : ℝ) (M : ℕ) :
    auxiliaryTailModulus X M ∣ auxiliaryModulus M := by
  classical
  unfold auxiliaryTailModulus
  exact dvd_trans
    (Finset.prod_dvd_prod_of_subset
      ((auxiliaryModulus M).primeFactors.filter
        (fun p => p ∉ (roughModulus X).primeFactors))
      (auxiliaryModulus M).primeFactors (fun p : ℕ => p)
      (Finset.filter_subset _ _))
    (Nat.prod_primeFactors_dvd (auxiliaryModulus M))

theorem auxiliaryModulus_cast_le_natCast_add_one (M : ℕ) :
    ((auxiliaryModulus M : ℕ) : ℝ) ≤ (M : ℝ) + 1 := by
  have hnat : auxiliaryModulus M ≤ M + 1 := by
    unfold auxiliaryModulus
    exact max_le (Nat.succ_le_succ (Nat.zero_le M)) (Nat.le_succ M)
  exact_mod_cast hnat

theorem auxiliaryTailModulus_prime_gt_floor_zScale
    {X : ℝ} {M p : ℕ}
    (hp : p ∈ (auxiliaryTailModulus X M).primeFactors) :
    ⌊ErdosStraus.zScale X⌋₊ < p := by
  classical
  rw [auxiliaryTailModulus_primeFactors] at hp
  have hp_aux : p ∈ (auxiliaryModulus M).primeFactors :=
    (Finset.mem_filter.mp hp).1
  have hp_not_rough : p ∉ (roughModulus X).primeFactors :=
    (Finset.mem_filter.mp hp).2
  have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_aux
  by_contra hnot
  have hp_le : p ≤ ⌊ErdosStraus.zScale X⌋₊ := Nat.le_of_not_gt hnot
  have hp_dvd_rough : p ∣ roughModulus X := by
    unfold roughModulus
    exact prime_dvd_primeProductBelow_of_le_floor
      (ErdosStraus.zScale X) p hpPrime hp_le
  have hp_rough : p ∈ (roughModulus X).primeFactors :=
    (Nat.mem_primeFactors).mpr
      ⟨hpPrime, hp_dvd_rough, Nat.ne_of_gt (roughModulus_pos X)⟩
  exact hp_not_rough hp_rough

theorem auxiliaryTailModulus_succ_floor_zScale_le_prime
    {X : ℝ} {M p : ℕ}
    (hp : p ∈ (auxiliaryTailModulus X M).primeFactors) :
    ⌊ErdosStraus.zScale X⌋₊ + 1 ≤ p :=
  Nat.succ_le_of_lt (auxiliaryTailModulus_prime_gt_floor_zScale hp)

theorem pow_card_le_auxiliaryTailModulus
    (X : ℝ) (M : ℕ) :
    (⌊ErdosStraus.zScale X⌋₊ + 1) ^
        (auxiliaryTailModulus X M).primeFactors.card
      ≤ auxiliaryTailModulus X M := by
  classical
  let q : ℕ := ⌊ErdosStraus.zScale X⌋₊ + 1
  let s : Finset ℕ :=
    (auxiliaryModulus M).primeFactors.filter
      (fun p => p ∉ (roughModulus X).primeFactors)
  have hterm : ∀ p ∈ s, q ≤ p := by
    intro p hp
    have hp_tail : p ∈ (auxiliaryTailModulus X M).primeFactors := by
      simpa [auxiliaryTailModulus_primeFactors, s] using hp
    simpa [q] using auxiliaryTailModulus_succ_floor_zScale_le_prime hp_tail
  have hprod : ∏ p ∈ s, q ≤ ∏ p ∈ s, p :=
    Finset.prod_le_prod (fun p _hp => Nat.zero_le q) hterm
  have hpf : (auxiliaryTailModulus X M).primeFactors = s := by
    simpa [s] using auxiliaryTailModulus_primeFactors X M
  calc
    (⌊ErdosStraus.zScale X⌋₊ + 1) ^
        (auxiliaryTailModulus X M).primeFactors.card
        = q ^ s.card := by simp [q, hpf]
    _ = ∏ _p ∈ s, q := by simp [Finset.prod_const]
    _ ≤ ∏ p ∈ s, p := hprod
    _ = auxiliaryTailModulus X M := by simp [auxiliaryTailModulus, s]

theorem auxiliaryTailModulus_card_mul_log_le
    (X : ℝ) (M : ℕ) :
    (((auxiliaryTailModulus X M).primeFactors.card : ℕ) : ℝ) *
        Real.log (((⌊ErdosStraus.zScale X⌋₊ + 1 : ℕ) : ℝ))
      ≤ Real.log ((M : ℝ) + 1) := by
  let q : ℕ := ⌊ErdosStraus.zScale X⌋₊ + 1
  let T : ℕ := auxiliaryTailModulus X M
  have hpow_nat : q ^ T.primeFactors.card ≤ T := by
    simpa [q, T] using
      pow_card_le_auxiliaryTailModulus X M
  have hqpos_nat : 0 < q := by simp [q]
  have hpow_pos : 0 < ((q ^ T.primeFactors.card : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_pos (n := T.primeFactors.card) hqpos_nat
  have hlog_pow_le_log_T :
      Real.log (((q ^ T.primeFactors.card : ℕ) : ℝ)) ≤
        Real.log (T : ℝ) := by
    exact Real.log_le_log hpow_pos (by exact_mod_cast hpow_nat)
  have hT_le_aux : T ≤ auxiliaryModulus M := by
    exact Nat.le_of_dvd (auxiliaryModulus_pos M)
      (by simpa [T] using auxiliaryTailModulus_dvd_auxiliaryModulus X M)
  have hT_le_M : (T : ℝ) ≤ (M : ℝ) + 1 := by
    exact le_trans (by exact_mod_cast hT_le_aux)
      (auxiliaryModulus_cast_le_natCast_add_one M)
  have hTpos : 0 < (T : ℝ) := by
    exact_mod_cast (by simpa [T] using auxiliaryTailModulus_pos X M)
  have hlog_T_le_log_M :
      Real.log (T : ℝ) ≤ Real.log ((M : ℝ) + 1) :=
    Real.log_le_log hTpos hT_le_M
  have hlog_pow_eq :
      Real.log (((q ^ T.primeFactors.card : ℕ) : ℝ)) =
        (T.primeFactors.card : ℝ) * Real.log (q : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  calc
    (((auxiliaryTailModulus X M).primeFactors.card : ℕ) : ℝ) *
        Real.log (((⌊ErdosStraus.zScale X⌋₊ + 1 : ℕ) : ℝ))
        = (T.primeFactors.card : ℝ) * Real.log (q : ℝ) := by
          simp [q, T]
    _ = Real.log (((q ^ T.primeFactors.card : ℕ) : ℝ)) := hlog_pow_eq.symm
    _ ≤ Real.log (T : ℝ) := hlog_pow_le_log_T
    _ ≤ Real.log ((M : ℝ) + 1) := hlog_T_le_log_M

/-- Each prime factor of the tail exceeds `⌊z⌋`, so for `X ≥ e` there are at most
`log(M + 1)/log(⌊z⌋ + 1)` of them. -/
theorem auxiliaryTailModulus_card_le_log_div_log
    (X : ℝ) (M : ℕ) (hX : Real.exp 1 ≤ X) :
    (((auxiliaryTailModulus X M).primeFactors.card : ℕ) : ℝ)
      ≤ Real.log ((M : ℝ) + 1) /
          Real.log (((⌊ErdosStraus.zScale X⌋₊ + 1 : ℕ) : ℝ)) := by
  have hz_ge_one : 1 ≤ ErdosStraus.zScale X := zScale_ge_one_of_exp_one_le hX
  have hfloor_one : 1 ≤ ⌊ErdosStraus.zScale X⌋₊ :=
    Nat.le_floor (by simpa using hz_ge_one)
  have hq_ge_two : 2 ≤ ⌊ErdosStraus.zScale X⌋₊ + 1 := by omega
  have hlog_pos :
      0 < Real.log (((⌊ErdosStraus.zScale X⌋₊ + 1 : ℕ) : ℝ)) :=
    Real.log_pos (by exact_mod_cast hq_ge_two)
  have hmul :=
    auxiliaryTailModulus_card_mul_log_le
      X M
  exact (le_div_iff₀ hlog_pos).mpr hmul

theorem log_natCast_add_one_le_add_one_mul_log_of_natCast_le_rpow
    {X C : ℝ} (M : ℕ)
    (hX : Real.exp 2 ≤ X) (hC : 0 ≤ C) (hM : (M : ℝ) ≤ X ^ C) :
    Real.log ((M : ℝ) + 1) ≤ (C + 1) * Real.log X := by
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 2) hX
  have hlogX_ge_two : (2 : ℝ) ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hX
  have hlogX_nonneg : 0 ≤ Real.log X := le_trans (by norm_num) hlogX_ge_two
  have hXone : 1 ≤ X := le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 2) hX
  have hXpow_one : 1 ≤ X ^ C := by
    simpa using Real.one_le_rpow hXone hC
  have hXpow_pos : 0 < X ^ C := Real.rpow_pos_of_pos hXpos C
  have hM_add : (M : ℝ) + 1 ≤ 2 * X ^ C := by
    nlinarith
  have hM_add_pos : 0 < (M : ℝ) + 1 := by positivity
  have hlog_mono :
      Real.log ((M : ℝ) + 1) ≤ Real.log (2 * X ^ C) :=
    Real.log_le_log hM_add_pos hM_add
  have hlog_prod :
      Real.log (2 * X ^ C) = Real.log 2 + C * Real.log X := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hXpow_pos),
      Real.log_rpow hXpos]
  have hlog_two_le_logX : Real.log 2 ≤ Real.log X := by
    have hlog_two_le_one :
        Real.log 2 ≤ (1 : ℝ) := by
      calc
        Real.log 2 ≤ (2 : ℝ) - 1 :=
          Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        _ = 1 := by norm_num
    exact hlog_two_le_one.trans (by linarith)
  calc
    Real.log ((M : ℝ) + 1)
        ≤ Real.log (2 * X ^ C) := hlog_mono
    _ = Real.log 2 + C * Real.log X := hlog_prod
    _ ≤ Real.log X + C * Real.log X :=
          add_le_add_left hlog_two_le_logX _
    _ = (C + 1) * Real.log X := by ring

theorem two_mul_C_add_one_mul_log_div_zScale_le_eps
    {X C eps : ℝ}
    (hX : Real.exp (max 2 (2 * (C + 1) / eps)) ≤ X)
    (hC : 0 ≤ C) (heps : 0 < eps) :
    (2 * (C + 1) * Real.log X) / ErdosStraus.zScale X ≤ eps := by
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hlog_ge :
      max 2 (2 * (C + 1) / eps) ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hX
  have hlog_ge_two : (2 : ℝ) ≤ Real.log X :=
    le_trans (le_max_left _ _) hlog_ge
  have hlog_pos : 0 < Real.log X :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hlog_ge_two
  have hlog_ge_one : (1 : ℝ) ≤ Real.log X :=
    le_trans (by norm_num : (1 : ℝ) ≤ 2) hlog_ge_two
  have hC1_nonneg : 0 ≤ C + 1 := by linarith
  have hA_nonneg : 0 ≤ 2 * (C + 1) := by nlinarith
  have hlog_ge_A :
      2 * (C + 1) / eps ≤ Real.log X :=
    le_trans (le_max_right _ _) hlog_ge
  have hA_le_log_mul_eps :
      2 * (C + 1) ≤ Real.log X * eps :=
    (div_le_iff₀ heps).mp hlog_ge_A
  have hA_le_eps_log : 2 * (C + 1) ≤ eps * Real.log X := by
    nlinarith
  have hlog_le_log_cube :
      Real.log X ≤ (Real.log X) ^ (3 : ℕ) := by
    have hsq : (1 : ℝ) ≤ (Real.log X) ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (Real.log X - 1)]
    calc
      Real.log X = Real.log X * 1 := by ring
      _ ≤ Real.log X * (Real.log X) ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_left hsq hlog_pos.le
      _ = (Real.log X) ^ (3 : ℕ) := by ring
  have hA_le_eps_log_cube :
      2 * (C + 1) ≤ eps * (Real.log X) ^ (3 : ℕ) :=
    hA_le_eps_log.trans
      (mul_le_mul_of_nonneg_left hlog_le_log_cube heps.le)
  have hlog_cube_pos : 0 < (Real.log X) ^ (3 : ℕ) :=
    pow_pos hlog_pos 3
  calc
    (2 * (C + 1) * Real.log X) / ErdosStraus.zScale X
        = (2 * (C + 1)) / (Real.log X) ^ (3 : ℕ) := by
          unfold ErdosStraus.zScale
          field_simp [ne_of_gt hlog_pos]
    _ ≤ eps := by
          rw [div_le_iff₀ hlog_cube_pos]
          exact hA_le_eps_log_cube

theorem coprime_auxiliaryModulus_iff_coprime_tail_of_coprime_rough
    {X : ℝ} {M n : ℕ} (hrough : Nat.Coprime n (roughModulus X)) :
    Nat.Coprime n (auxiliaryModulus M) ↔
      Nat.Coprime n (auxiliaryTailModulus X M) := by
  constructor
  · intro haux
    exact coprime_of_primeFactors_subset_right
      (Nat.ne_of_gt (auxiliaryTailModulus_pos X M))
      (auxiliaryTailModulus_primeFactors_subset_auxiliary X M) haux
  · intro htail
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hg
    rcases Nat.exists_prime_and_dvd hg with ⟨p, hp, hpg⟩
    have hpn : p ∣ n := Nat.dvd_trans hpg (Nat.gcd_dvd_left n (auxiliaryModulus M))
    have hpaux : p ∣ auxiliaryModulus M :=
      Nat.dvd_trans hpg (Nat.gcd_dvd_right n (auxiliaryModulus M))
    have hpaux_mem : p ∈ (auxiliaryModulus M).primeFactors :=
      (Nat.mem_primeFactors).mpr
        ⟨hp, hpaux, Nat.ne_of_gt (auxiliaryModulus_pos M)⟩
    by_cases hp_rough : p ∈ (roughModulus X).primeFactors
    · have hp_dvd_rough : p ∣ roughModulus X :=
        Nat.dvd_of_mem_primeFactors hp_rough
      have hp_gcd : p ∣ Nat.gcd n (roughModulus X) :=
        Nat.dvd_gcd hpn hp_dvd_rough
      rw [hrough.gcd_eq_one] at hp_gcd
      exact hp.not_dvd_one hp_gcd
    · have hp_tail_mem : p ∈ (auxiliaryTailModulus X M).primeFactors := by
        rw [auxiliaryTailModulus_primeFactors]
        exact Finset.mem_filter.mpr ⟨hpaux_mem, hp_rough⟩
      have hp_dvd_tail : p ∣ auxiliaryTailModulus X M :=
        Nat.dvd_of_mem_primeFactors hp_tail_mem
      have hp_gcd_tail : p ∣ Nat.gcd n (auxiliaryTailModulus X M) :=
        Nat.dvd_gcd hpn hp_dvd_tail
      rw [htail.gcd_eq_one] at hp_gcd_tail
      exact hp.not_dvd_one hp_gcd_tail

/-! ## Mertens bounds for `∏_{p ≤ z} (1 - 1/p)` -/

/-- The Euler product `∏_{p ∣ P(z)} (1 - 1/p) = ∏_{p ≤ z} (1 - 1/p)`. -/
noncomputable def roughDyadicBadPrimeMainEulerProduct (X : ℝ) : ℝ :=
  ∏ p ∈ (roughModulus X).primeFactors, (1 - (p : ℝ)⁻¹)

theorem roughDyadicBadPrimeMainEulerProduct_nonneg (X : ℝ) :
    0 ≤ roughDyadicBadPrimeMainEulerProduct X := by
  classical
  unfold roughDyadicBadPrimeMainEulerProduct
  apply Finset.prod_nonneg
  intro p hp
  have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hpOne : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpPrime.one_lt.le
  exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hpOne)

theorem tendsto_log_zScale_atTop :
    Filter.Tendsto (fun X : ℝ => Real.log (ErdosStraus.zScale X))
      Filter.atTop Filter.atTop := by
  have hloglog :
      Filter.Tendsto (fun X : ℝ => Real.log (Real.log X))
        Filter.atTop Filter.atTop := by
    exact Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hmul :
      Filter.Tendsto (fun X : ℝ => (4 : ℝ) * Real.log (Real.log X))
        Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 4) hloglog
  refine hmul.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with X _hX
  unfold ErdosStraus.zScale
  rw [Real.log_pow]
  ring

/-- The lower bound `∏_{p ≤ z} (1 - 1/p) ≫ 1/log z` for large `X`. -/
def roughDyadicBadPrimeMainEulerProductLowerBound : Prop :=
  ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
    c / Real.log (ErdosStraus.zScale X) ≤
      roughDyadicBadPrimeMainEulerProduct X

/-- The upper bound `∏_{p ≤ z} (1 - 1/p) ≪ 1/log z` for large `X`. -/
def roughDyadicBadPrimeMainEulerProductUpperBound : Prop :=
  ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
    roughDyadicBadPrimeMainEulerProduct X ≤
      C / Real.log (ErdosStraus.zScale X)

/-- `∏_{p ≤ z} (1 - 1/p) · ∑ φ(d)/d² ≤ 1` for large `X`, the sum over the odd divisors
`d ≤ U` of `P(z)`. Together with `∑ φ(d)/d² ≫ log z` it gives the upper bound. -/
def roughDyadicBadPrimeMainEulerProductSmallDivisorDualBound : Prop :=
  ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    roughDyadicBadPrimeMainEulerProduct X * smallDivisorEulerSum X ≤ 1

/-- `∑ φ(d)/d² ≤ ∑_{d ∣ P(z)} 1/d`, since `φ(d)/d² ≤ 1/d`. -/
theorem smallDivisorEulerSum_le_roughModulus_divisor_recip_sum (X : ℝ) :
    smallDivisorEulerSum X ≤
      ∑ d ∈ (roughModulus X).divisors, (1 : ℝ) / (d : ℝ) := by
  classical
  unfold smallDivisorEulerSum
  let support : Finset ℕ :=
    (Finset.Icc (1 : ℕ) ⌊ErdosStraus.UScale X⌋₊).filter
      (fun d => d ∣ roughModulus X ∧ Odd d)
  have hterm :
      (∑ d ∈ support, (Nat.totient d : ℝ) / (d : ℝ) ^ 2) ≤
        ∑ d ∈ support, (1 : ℝ) / (d : ℝ) := by
    apply Finset.sum_le_sum
    intro d hd
    dsimp [support] at hd
    rw [Finset.mem_filter] at hd
    have hdIcc : d ∈ Finset.Icc (1 : ℕ) ⌊ErdosStraus.UScale X⌋₊ := hd.1
    have hdpos_nat : 0 < d :=
      lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdIcc).1
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hdpos_nat
    have htot_le_nat : (Nat.totient d : ℝ) ≤ (d : ℝ) := by
      exact_mod_cast Nat.totient_le d
    calc
      (Nat.totient d : ℝ) / (d : ℝ) ^ 2
          ≤ (d : ℝ) / (d : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right htot_le_nat (sq_nonneg _)
      _ = (1 : ℝ) / (d : ℝ) := by
            field_simp [ne_of_gt hdpos]
  have hsubset : support ⊆ (roughModulus X).divisors := by
    intro d hd
    dsimp [support] at hd
    rw [Finset.mem_filter] at hd
    exact Nat.mem_divisors.mpr
      ⟨hd.2.1, Nat.ne_of_gt (roughModulus_pos X)⟩
  have hsubsum :
      (∑ d ∈ support, (1 : ℝ) / (d : ℝ)) ≤
        ∑ d ∈ (roughModulus X).divisors, (1 : ℝ) / (d : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro d _hdDiv _hdSmall
      exact div_nonneg zero_le_one (Nat.cast_nonneg d))
  exact hterm.trans hsubsum

/-- `(φ(P)/P) ∑_{d ∣ P} 1/d ≤ 1` for `P = P(z)`. -/
theorem roughEulerProduct_mul_divisorRecip_le_one
    (X : ℝ) :
    roughDyadicBadPrimeMainEulerProduct X *
        (∑ d ∈ (roughModulus X).divisors, (1 : ℝ) / (d : ℝ)) ≤ 1 := by
  have hPpos_nat : 0 < roughModulus X := roughModulus_pos X
  have hPpos : (0 : ℝ) < (roughModulus X : ℝ) := by exact_mod_cast hPpos_nat
  have hdiv :=
    divisor_recip_sum_mul_totient_le_self hPpos_nat (roughModulus_squarefree X)
  change totientPrimeFactorProduct (roughModulus X) *
      (∑ d ∈ (roughModulus X).divisors, (1 : ℝ) / (d : ℝ)) ≤ 1
  rw [← totient_div_eq_totientPrimeFactorProduct hPpos_nat]
  calc
    ((Nat.totient (roughModulus X) : ℝ) / (roughModulus X : ℝ)) *
        (∑ d ∈ (roughModulus X).divisors, (1 : ℝ) / (d : ℝ))
        = ((∑ d ∈ (roughModulus X).divisors, (1 : ℝ) / (d : ℝ)) *
            (Nat.totient (roughModulus X) : ℝ)) / (roughModulus X : ℝ) := by
              field_simp [ne_of_gt hPpos]
    _ ≤ (roughModulus X : ℝ) / (roughModulus X : ℝ) :=
          div_le_div_of_nonneg_right hdiv hPpos.le
    _ = 1 := by field_simp [ne_of_gt hPpos]

theorem roughEulerProduct_mul_divisorRecip_eq
    (X : ℝ) :
    roughDyadicBadPrimeMainEulerProduct X *
        (∑ d ∈ (roughModulus X).divisors, (1 : ℝ) / (d : ℝ)) =
      ∏ p ∈ (roughModulus X).primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹) := by
  unfold roughDyadicBadPrimeMainEulerProduct
  exact prod_one_sub_inv_mul_divisorRecip_eq
    (roughModulus_squarefree X)

/-- The bound `∑_{d ∣ P(z)} 1/d ≪ log z` for large `X`. -/
def roughModulusDivisorRecipUpperBound : Prop :=
  ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
    (∑ d ∈ (roughModulus X).divisors, (1 : ℝ) / (d : ℝ)) ≤
      C * Real.log (ErdosStraus.zScale X)

/-- `∑_{m ∣ d} 1/m ≤ exp(∑_{p ∣ d} 1/p)` for squarefree `d`, since `1 + t ≤ eᵗ`. -/
theorem divisor_recip_sum_le_exp_primeFactor_recip_sum_of_squarefree
    {d : ℕ} (hsqf : Squarefree d) :
    (∑ m ∈ d.divisors, (1 : ℝ) / (m : ℝ)) ≤
      Real.exp (∑ p ∈ d.primeFactors, (p : ℝ)⁻¹) := by
  classical
  have hprod_le :
      ∏ p ∈ d.primeFactors, (1 + (p : ℝ)⁻¹)
        ≤ ∏ p ∈ d.primeFactors, Real.exp ((p : ℝ)⁻¹) := by
    refine Finset.prod_le_prod ?h_nonneg ?h_point
    · intro p _hp
      exact add_nonneg zero_le_one (inv_nonneg.mpr (Nat.cast_nonneg p))
    · intro p _hp
      have h := Real.add_one_le_exp ((p : ℝ)⁻¹)
      nlinarith
  calc
    (∑ m ∈ d.divisors, (1 : ℝ) / (m : ℝ))
        = ∏ p ∈ d.primeFactors, (1 + (p : ℝ)⁻¹) := by
          rw [divisor_recip_sum_eq_primeFactorProduct_one_add_inv hsqf]
    _ ≤ ∏ p ∈ d.primeFactors, Real.exp ((p : ℝ)⁻¹) := hprod_le
    _ = Real.exp (∑ p ∈ d.primeFactors, (p : ℝ)⁻¹) := by
          rw [Real.exp_sum]

/-- Mertens' bound `∑_{p ∣ P(z)} 1/p ≤ log log z + O(1)` for large `X`. The coefficient `1`
of `log log z` is what the bound `∑_{d ∣ P(z)} 1/d ≪ log z` needs. -/
def roughModulusPrimeRecipSharpMertensUpperBound : Prop :=
  ∃ K X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    (∑ p ∈ (roughModulus X).primeFactors, (p : ℝ)⁻¹) ≤
      Real.log (Real.log (ErdosStraus.zScale X)) + K

/-- Mertens' bound `∑_{p ≤ z} 1/p ≤ log log z + O(1)` for large real `z` (Lemma 3.1). -/
def PrimeRecipSharpMertensUpperBound : Prop :=
  ∃ K Z₀ : ℝ, ∀ z : ℝ, Z₀ ≤ z →
    (∑ p ∈ (Finset.Icc (2 : ℕ) ⌊z⌋₊).filter (fun p => Nat.Prime p),
        (p : ℝ)⁻¹) ≤
      Real.log (Real.log z) + K

/-- Mertens' bound `∑_{p ≤ N} 1/p ≤ log log N + K` for large integers `N`, with `K ∈ ℕ`. -/
def PrimeRecipSharpMertensNatUpperBound : Prop :=
  ∃ K N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    (∑ p ∈ (Finset.Icc (2 : ℕ) N).filter (fun p => Nat.Prime p),
        (p : ℝ)⁻¹) ≤
      Real.log (Real.log (N : ℝ)) + K

/-- Mertens' bound `∑_{p ≤ N} 1/p ≤ log log N + K` for large integers `N`, with `K ∈ ℝ`. -/
def PrimeRecipSharpMertensNatRealConstantUpperBound : Prop :=
  ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    (∑ p ∈ (Finset.Icc (2 : ℕ) N).filter (fun p => Nat.Prime p),
        (p : ℝ)⁻¹) ≤
      Real.log (Real.log (N : ℝ)) + K

/-- The defect `∑_{p ≤ N} 1/p - log log N`. -/
noncomputable def primeRecipSharpMertensNatDefect (N : ℕ) : ℝ :=
  (∑ p ∈ (Finset.Icc (2 : ℕ) N).filter (fun p => Nat.Prime p),
      (p : ℝ)⁻¹) - Real.log (Real.log (N : ℝ))

/-- The defect `∑_{p ≤ N} 1/p - log log N` is bounded above for large `N`. -/
def PrimeRecipSharpMertensNatDefectEventuallyUpperBound : Prop :=
  ∃ K : ℝ, ∀ᶠ N : ℕ in Filter.atTop,
    primeRecipSharpMertensNatDefect N ≤ K

theorem natRealMertens_of_mertensDefect
    (h : PrimeRecipSharpMertensNatDefectEventuallyUpperBound) :
    PrimeRecipSharpMertensNatRealConstantUpperBound := by
  rcases h with ⟨K, hK⟩
  rw [Filter.eventually_atTop] at hK
  rcases hK with ⟨N₀, hN₀⟩
  refine ⟨K, N₀, ?_⟩
  intro N hN
  have hdef := hN₀ N hN
  dsimp [primeRecipSharpMertensNatDefect] at hdef
  linarith

theorem PrimeRecipSharpMertensNatUpperBound_of_natRealConstant
    (h : PrimeRecipSharpMertensNatRealConstantUpperBound) :
    PrimeRecipSharpMertensNatUpperBound := by
  rcases h with ⟨K, N₀, hN⟩
  let KNat : ℕ := ⌊max K 0⌋₊ + 1
  refine ⟨KNat, N₀, ?_⟩
  intro N hN₀
  have hK_le : K ≤ (KNat : ℝ) := by
    have hK_nonneg_le : K ≤ max K 0 := le_max_left _ _
    have hfloor_lt :
        max K 0 < ((⌊max K 0⌋₊ : ℕ) : ℝ) + 1 := by
      exact Nat.lt_floor_add_one (max K 0)
    have hfloor_lt' : max K 0 < (KNat : ℝ) := by
      dsimp [KNat]
      simpa [Nat.cast_add, Nat.cast_one] using hfloor_lt
    exact le_trans hK_nonneg_le (le_of_lt hfloor_lt')
  exact (hN N hN₀).trans (add_le_add_right hK_le _)

theorem PrimeRecipSharpMertensUpperBound_of_nat
    (h : PrimeRecipSharpMertensNatUpperBound) :
    PrimeRecipSharpMertensUpperBound := by
  rcases h with ⟨K, N₀, hN⟩
  refine ⟨K, max (3 : ℝ) ((N₀ : ℝ) + 1), ?_⟩
  intro z hz
  have hz_three : (3 : ℝ) ≤ z := le_trans (le_max_left _ _) hz
  have hz_N₀ : (N₀ : ℝ) + 1 ≤ z := le_trans (le_max_right _ _) hz
  have hz_pos : 0 < z := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) hz_three
  have hN₀_le_floor : N₀ ≤ ⌊z⌋₊ := by
    exact Nat.le_floor (show (N₀ : ℝ) ≤ z by nlinarith)
  have hfloor_ge_three : (3 : ℕ) ≤ ⌊z⌋₊ := by
    exact Nat.le_floor hz_three
  have hfloor_pos : 0 < ((⌊z⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 3) hfloor_ge_three)
  have hfloor_gt_one : (1 : ℝ) < ((⌊z⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 3) hfloor_ge_three)
  have hlog_floor_pos : 0 < Real.log ((⌊z⌋₊ : ℕ) : ℝ) :=
    Real.log_pos hfloor_gt_one
  have hfloor_le_z : ((⌊z⌋₊ : ℕ) : ℝ) ≤ z :=
    Nat.floor_le hz_pos.le
  have hlog_floor_le_log_z :
      Real.log ((⌊z⌋₊ : ℕ) : ℝ) ≤ Real.log z :=
    Real.log_le_log hfloor_pos hfloor_le_z
  have hloglog_floor_le_loglog_z :
      Real.log (Real.log ((⌊z⌋₊ : ℕ) : ℝ)) ≤
        Real.log (Real.log z) :=
    Real.log_le_log hlog_floor_pos hlog_floor_le_log_z
  exact (hN ⌊z⌋₊ hN₀_le_floor).trans
    (add_le_add_left hloglog_floor_le_loglog_z K)

theorem roughMertens_of_realMertens
    (h : PrimeRecipSharpMertensUpperBound) :
    roughModulusPrimeRecipSharpMertensUpperBound := by
  rcases h with ⟨K, Z₀, hprime⟩
  refine ⟨K, max (Real.exp 1) (Real.exp (max 1 Z₀)), ?_⟩
  intro X hX
  have hXexp1 : Real.exp 1 ≤ X := le_trans (le_max_left _ _) hX
  have hXexpZ : Real.exp (max 1 Z₀) ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hXexp1
  have hlog_ge_max : max 1 Z₀ ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hXexpZ
  have hlog_ge_one : 1 ≤ Real.log X := le_trans (le_max_left _ _) hlog_ge_max
  have hlog_ge_Z₀ : Z₀ ≤ Real.log X := le_trans (le_max_right _ _) hlog_ge_max
  have hlog_nonneg : 0 ≤ Real.log X := le_trans zero_le_one hlog_ge_one
  have hlog_le_z : Real.log X ≤ ErdosStraus.zScale X := by
    unfold ErdosStraus.zScale
    have hle_sq : Real.log X ≤ Real.log X * Real.log X := by nlinarith
    have hsq_ge_one : 1 ≤ Real.log X * Real.log X := by nlinarith
    have hsq_nonneg : 0 ≤ Real.log X * Real.log X := by nlinarith
    have hsq_le_four :
        Real.log X * Real.log X ≤
          (Real.log X * Real.log X) * (Real.log X * Real.log X) := by
      have hmul := mul_le_mul_of_nonneg_left hsq_ge_one hsq_nonneg
      simpa [one_mul] using hmul
    calc
      Real.log X ≤ Real.log X * Real.log X := hle_sq
      _ ≤ (Real.log X * Real.log X) * (Real.log X * Real.log X) := hsq_le_four
      _ = (Real.log X) ^ (4 : ℕ) := by ring
  have hz_ge_Z₀ : Z₀ ≤ ErdosStraus.zScale X := hlog_ge_Z₀.trans hlog_le_z
  simpa [roughModulus, primeProductBelow_primeFactors_eq]
    using hprime (ErdosStraus.zScale X) hz_ge_Z₀

theorem roughMertens_of_natMertens
    (h : PrimeRecipSharpMertensNatUpperBound) :
    roughModulusPrimeRecipSharpMertensUpperBound :=
  roughMertens_of_realMertens
    (PrimeRecipSharpMertensUpperBound_of_nat h)

/-- If `∑_{p ∣ P(z)} 1/p ≤ log log z + K`, then `∑_{d ∣ P(z)} 1/d ≤ e^K log z`. -/
theorem roughModulus_divisor_recip_upper_of_primeRecipSharpMertens
    {K Xprime : ℝ}
    (hprime : ∀ X : ℝ, Xprime ≤ X →
      (∑ p ∈ (roughModulus X).primeFactors, (p : ℝ)⁻¹) ≤
        Real.log (Real.log (ErdosStraus.zScale X)) + K) :
    ∀ X : ℝ, max Xprime (Real.exp 2) ≤ X →
      (∑ d ∈ (roughModulus X).divisors, (1 : ℝ) / (d : ℝ)) ≤
        Real.exp K * Real.log (ErdosStraus.zScale X) := by
  intro X hX
  have hXprime : Xprime ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 2 ≤ X := le_trans (le_max_right _ _) hX
  have hlogZ_pos : 0 < Real.log (ErdosStraus.zScale X) :=
    log_zScale_pos_of_exp_two_le hXexp
  have hdiv_exp :=
    divisor_recip_sum_le_exp_primeFactor_recip_sum_of_squarefree
      (d := roughModulus X) (roughModulus_squarefree X)
  have hprime_sum := hprime X hXprime
  have hexp_le :
      Real.exp (∑ p ∈ (roughModulus X).primeFactors, (p : ℝ)⁻¹)
        ≤ Real.exp (Real.log (Real.log (ErdosStraus.zScale X)) + K) :=
    Real.exp_le_exp.mpr hprime_sum
  calc
    (∑ d ∈ (roughModulus X).divisors, (1 : ℝ) / (d : ℝ))
        ≤ Real.exp (∑ p ∈ (roughModulus X).primeFactors, (p : ℝ)⁻¹) :=
          hdiv_exp
    _ ≤ Real.exp (Real.log (Real.log (ErdosStraus.zScale X)) + K) :=
          hexp_le
    _ = Real.exp K * Real.log (ErdosStraus.zScale X) := by
          rw [Real.exp_add, Real.exp_log hlogZ_pos]
          ring

theorem roughModulusDivisorRecipUpperBound_of_primeRecipSharpMertens
    (hprime : roughModulusPrimeRecipSharpMertensUpperBound) :
    roughModulusDivisorRecipUpperBound := by
  rcases hprime with ⟨K, Xprime, hprime⟩
  refine ⟨Real.exp K, max Xprime (Real.exp 2), Real.exp_pos K, ?_⟩
  exact roughModulus_divisor_recip_upper_of_primeRecipSharpMertens hprime

/-- If `∑_{d ∣ P(z)} 1/d ≤ C log z`, then `∏_{p ≤ z} (1 - 1/p) ≥ (4C)⁻¹/log z`: the product
times the divisor sum is `∏_{p ≤ z} (1 - p⁻²) ≥ 1/4`. -/
theorem roughEulerProduct_lower_explicit
    {C Xdiv : ℝ} (hC : 0 < C)
    (hdiv : ∀ X : ℝ, Xdiv ≤ X →
      (∑ d ∈ (roughModulus X).divisors, (1 : ℝ) / (d : ℝ)) ≤
        C * Real.log (ErdosStraus.zScale X)) :
    ∀ X : ℝ, max Xdiv (Real.exp 2) ≤ X →
      (4 * C)⁻¹ / Real.log (ErdosStraus.zScale X) ≤
        roughDyadicBadPrimeMainEulerProduct X := by
  intro X hX
  have hXdiv : Xdiv ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 2 ≤ X := le_trans (le_max_right _ _) hX
  have hlog_pos : 0 < Real.log (ErdosStraus.zScale X) :=
    log_zScale_pos_of_exp_two_le hXexp
  have hprod_nonneg : 0 ≤ roughDyadicBadPrimeMainEulerProduct X :=
    roughDyadicBadPrimeMainEulerProduct_nonneg X
  have hsum_upper := hdiv X hXdiv
  have hsquare := roughModulus_square_euler_product_ge_quarter X
  have hidentity :=
    roughEulerProduct_mul_divisorRecip_eq X
  have hquarter_le :
      (1 / 4 : ℝ) ≤
        roughDyadicBadPrimeMainEulerProduct X *
          (∑ d ∈ (roughModulus X).divisors, (1 : ℝ) / (d : ℝ)) := by
    rw [hidentity]
    exact hsquare
  have hquarter_le_scaled :
      (1 / 4 : ℝ) ≤
        roughDyadicBadPrimeMainEulerProduct X *
          (C * Real.log (ErdosStraus.zScale X)) :=
    hquarter_le.trans
      (mul_le_mul_of_nonneg_left hsum_upper hprod_nonneg)
  rw [div_le_iff₀ hlog_pos]
  rw [inv_le_iff_one_le_mul₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hC)]
  nlinarith

theorem roughEulerProduct_lower_of_divisorRecip
    (hdiv : roughModulusDivisorRecipUpperBound) :
    roughDyadicBadPrimeMainEulerProductLowerBound := by
  rcases hdiv with ⟨C, Xdiv, hC, hdiv⟩
  refine ⟨(4 * C)⁻¹, max Xdiv (Real.exp 2),
    inv_pos.mpr (mul_pos (by norm_num) hC), ?_⟩
  exact roughEulerProduct_lower_explicit hC hdiv

theorem roughEulerProduct_lower_of_roughMertens
    (hprime : roughModulusPrimeRecipSharpMertensUpperBound) :
    roughDyadicBadPrimeMainEulerProductLowerBound :=
  roughEulerProduct_lower_of_divisorRecip
    (roughModulusDivisorRecipUpperBound_of_primeRecipSharpMertens hprime)

theorem roughEulerProduct_lower_of_natMertens
    (hprime : PrimeRecipSharpMertensNatUpperBound) :
    roughDyadicBadPrimeMainEulerProductLowerBound :=
  roughEulerProduct_lower_of_roughMertens
    (roughMertens_of_natMertens
      hprime)

/-- The lower bound `∏_{p ≤ z} (1 - 1/p) ≫ 1/log z`, assuming that
`∑_{p ≤ N} 1/p - log log N` is bounded above for large `N`. -/
theorem roughEulerProduct_lower_of_mertensDefect
    (hprime : PrimeRecipSharpMertensNatDefectEventuallyUpperBound) :
    roughDyadicBadPrimeMainEulerProductLowerBound :=
  roughEulerProduct_lower_of_natMertens
    (PrimeRecipSharpMertensNatUpperBound_of_natRealConstant
      (natRealMertens_of_mertensDefect
        hprime))

theorem roughEulerProduct_mul_eulerSum_le_one :
    roughDyadicBadPrimeMainEulerProductSmallDivisorDualBound := by
  refine ⟨0, ?_⟩
  intro X _hX
  have hprod_nonneg := roughDyadicBadPrimeMainEulerProduct_nonneg X
  calc
    roughDyadicBadPrimeMainEulerProduct X * smallDivisorEulerSum X
        ≤ roughDyadicBadPrimeMainEulerProduct X *
            (∑ d ∈ (roughModulus X).divisors, (1 : ℝ) / (d : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (smallDivisorEulerSum_le_roughModulus_divisor_recip_sum X)
            hprod_nonneg
    _ ≤ 1 := roughEulerProduct_mul_divisorRecip_le_one X

/-- Combined with `∑ φ(d)/d² ≫ log z`, the inequality
`∏_{p ≤ z} (1 - 1/p) · ∑ φ(d)/d² ≤ 1` gives the upper bound. -/
theorem roughEulerProduct_upper_of_dual
    (hdual : roughDyadicBadPrimeMainEulerProductSmallDivisorDualBound) :
    roughDyadicBadPrimeMainEulerProductUpperBound := by
  rcases hdual with ⟨Xdual, hdual⟩
  rcases smallDivisorEulerSum_lower_bound with ⟨c, Xlow, hc, hlow⟩
  refine ⟨c⁻¹, max (max Xdual Xlow) (Real.exp 2), inv_pos.mpr hc, ?_⟩
  intro X hX
  have hXdual : Xdual ≤ X := le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) hX)
  have hXlow : Xlow ≤ X := le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) hX)
  have hXexp : Real.exp 2 ≤ X := le_trans (le_max_right _ _) hX
  have hlog_pos : 0 < Real.log (ErdosStraus.zScale X) :=
    log_zScale_pos_of_exp_two_le hXexp
  have hprod_nonneg : 0 ≤ roughDyadicBadPrimeMainEulerProduct X :=
    roughDyadicBadPrimeMainEulerProduct_nonneg X
  have hsmall_lower :
      c * Real.log (ErdosStraus.zScale X) ≤ smallDivisorEulerSum X :=
    hlow X hXlow
  have hmul_lower :
      roughDyadicBadPrimeMainEulerProduct X *
          (c * Real.log (ErdosStraus.zScale X)) ≤
        roughDyadicBadPrimeMainEulerProduct X * smallDivisorEulerSum X :=
    mul_le_mul_of_nonneg_left hsmall_lower hprod_nonneg
  have hmul_one :
      roughDyadicBadPrimeMainEulerProduct X *
          (c * Real.log (ErdosStraus.zScale X)) ≤ 1 :=
    hmul_lower.trans (hdual X hXdual)
  have hden_pos : 0 < c * Real.log (ErdosStraus.zScale X) :=
    mul_pos hc hlog_pos
  calc
    roughDyadicBadPrimeMainEulerProduct X
        = (roughDyadicBadPrimeMainEulerProduct X *
            (c * Real.log (ErdosStraus.zScale X))) /
            (c * Real.log (ErdosStraus.zScale X)) := by
              field_simp [ne_of_gt hden_pos]
    _ ≤ 1 / (c * Real.log (ErdosStraus.zScale X)) :=
          div_le_div_of_nonneg_right hmul_one hden_pos.le
    _ = c⁻¹ / Real.log (ErdosStraus.zScale X) := by
          field_simp [ne_of_gt hc, ne_of_gt hlog_pos]

/-- `∏_{p ≤ z} (1 - 1/p) ≪ 1/log z`. -/
theorem roughEulerProduct_upper :
    roughDyadicBadPrimeMainEulerProductUpperBound :=
  roughEulerProduct_upper_of_dual
    roughEulerProduct_mul_eulerSum_le_one

/-! ## The sum of Lemma 3.4 -/

/-- The sum `∑ 1/n` of Lemma 3.4 over squarefree `n ≤ X^{σ₀}` with `(n, P(z)) = 1` and
`(n, M) = 1`; here `M = 0` imposes no condition. -/
noncomputable def roughInitial (X : ℝ) (M : ℕ) (σ₀ : ℝ) : ℝ := by
  classical
  exact
    ∑ n ∈ (Finset.Icc (1 : ℕ) ⌊X ^ σ₀⌋₊).filter
        (fun n =>
          Squarefree n ∧ Nat.Coprime n (roughModulus X) ∧
            Nat.Coprime n (auxiliaryModulus M)),
      (1 : ℝ) / (n : ℝ)

theorem roughInitial_nonneg (X : ℝ) (M : ℕ) (σ₀ : ℝ) :
    0 ≤ roughInitial X M σ₀ := by
  classical
  unfold roughInitial
  apply Finset.sum_nonneg
  intro n _hn
  exact div_nonneg zero_le_one (Nat.cast_nonneg n)

end

end ErdosStraus.Estimates
