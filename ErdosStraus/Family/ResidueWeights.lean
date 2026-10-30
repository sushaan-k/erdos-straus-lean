import ErdosStraus.Family.Definition
import ErdosStraus.Family.Scales
import ErdosStraus.Estimates.ReciprocalPrimes
import ErdosStraus.Basic
import ErdosStraus.Estimates.PrimeCounts
import ErdosStraus.Family.DivisorSums
import ErdosStraus.Estimates.RoughSums
import ErdosStraus.Family.TotalWeight
import ErdosStraus.Family.Events

/-!
# Proposition 6.7: event weights in residue classes

For `D ≤ Y` coprime to `P(z)`, the members of `I_b` with `D ∣ d₊` and `e ≡ c (mod D)`
have total weight `B_{D,c} ≪ (log X)³/D²`, and those with `D ∣ d₊` have total weight
`≪ (log X)³/D`, uniformly in `b`, `D` and `c`. For fixed `(e, d₋, d₊)` the large primes
lie in one reduced class modulo `m rad(e)`, so Lemma 3.6 bounds their reciprocal sum;
the sums over `d₊`, `e` and `d₋` are bounded by Lemma 3.4, Theorem 6.3 and
`∑_{d₋ ≤ U} 1/d₋ ≪ log z`. With Proposition 6.6 this gives `B_{D,c} ≤ K μ_b/D²` and
`∑_{D ∣ d₊} w_i ≤ K μ_b/D`.
-/

namespace ErdosStraus.FixedNumeratorFamily

open Classical Family
open scoped BigOperators

/-! ## Summing over the rough cofactor `d₊` -/

/-- For fixed `(e, d₋)`, the weight of the members with `D ∣ d₊` is
`∑_{D ∣ d₊} (1/d₊) ∑_p 1/p`. -/
theorem fixedDivisorMass_eq_prime_fibers (indices : Finset FamilyIndex)
    (E : ExactDivisor) (dminus D : ℕ) :
    familyFixedEDminusDivisorMass indices E dminus D =
      ∑ dplus ∈ (familyDplusValues indices E dminus).filter (fun dplus => D ∣ dplus),
        ((1 : ℝ) / dplus) *
          ∑ p ∈ familyPrimeValues indices E dminus dplus, (1 : ℝ) / p := by
  classical
  let s := indices.filter (fun i => i.E = E ∧ i.dminus = dminus ∧ D ∣ i.dplus)
  let t := (familyDplusValues indices E dminus).filter (fun dplus => D ∣ dplus)
  have hmaps : ∀ i ∈ s, i.dplus ∈ t := by
    intro i hi
    obtain ⟨hiI, hiE, himinus, hiD⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
      ⟨i, Finset.mem_filter.mpr ⟨hiI, hiE, himinus⟩, rfl⟩, hiD⟩
  have hpartition := Finset.sum_fiberwise_of_maps_to hmaps
    (fun i : FamilyIndex => (1 : ℝ) / ((i.dplus * i.p : ℕ) : ℝ))
  unfold familyFixedEDminusDivisorMass
  change (∑ i ∈ s, (1 : ℝ) / ((i.dplus * i.p : ℕ) : ℝ)) = _
  rw [← hpartition]
  apply Finset.sum_congr rfl
  intro dplus hdplus
  let fiber := indices.filter (fun i => i.E = E ∧ i.dminus = dminus ∧ i.dplus = dplus)
  have hfilter : s.filter (fun i => i.dplus = dplus) = fiber := by
    ext i
    simp only [s, fiber, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hi, hiE, himinus, _hiD⟩, hiplus⟩
      exact ⟨hi, hiE, himinus, hiplus⟩
    · rintro ⟨hi, hiE, himinus, hiplus⟩
      exact ⟨⟨hi, hiE, himinus, hiplus ▸ (Finset.mem_filter.mp hdplus).2⟩, hiplus⟩
  rw [hfilter]
  have hinj : Set.InjOn (fun i : FamilyIndex => i.p) (fiber : Set _) := by
    intro i hi j hj hp
    have hiData := Finset.mem_filter.mp hi
    have hjData := Finset.mem_filter.mp hj
    cases i
    cases j
    simp_all
  have hprime : (∑ p ∈ familyPrimeValues indices E dminus dplus, (1 : ℝ) / p) =
      ∑ i ∈ fiber, (1 : ℝ) / i.p := Finset.sum_image hinj
  rw [hprime, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2.2.2]
  simp only [Nat.cast_mul, one_div, mul_inv_rev]
  ring

theorem dplus_multiples_recip_le_roughInitial
    (m : ℕ) (P : Params) (X : ℝ) (b : ℕ) (indices : Finset FamilyIndex)
    (E : ExactDivisor) (dminus D : ℕ)
    (hmem : ∀ i ∈ indices, StaticMem m P X (Estimates.roughModulus X) b i)
    (hD : 0 < D) :
    (∑ dplus ∈ (familyDplusValues indices E dminus).filter (fun dplus => D ∣ dplus),
      (1 : ℝ) / dplus) ≤ (1 / (D : ℝ)) * Estimates.roughInitial X 1 P.σ := by
  classical
  let U := familyDplusValues indices E dminus
  have hUpos : ∀ dplus ∈ U, 0 < dplus := by
    intro dplus hdplus
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hdplus
    exact (hmem i (Finset.mem_filter.mp hi).1).dplus_pos
  rw [ErdosStraus.Arithmetic.reciprocal_sum_multiples_eq_divisor_inv_mul_quotient_image U D hD hUpos]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold Estimates.roughInitial
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    obtain ⟨dplus, hdplus, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hdplusU, hDplus⟩ := Finset.mem_filter.mp hdplus
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hdplusU
    have h := hmem i (Finset.mem_filter.mp hi).1
    have htDvd := Nat.div_dvd_of_dvd hDplus
    have htpos := Nat.div_pos (Nat.le_of_dvd h.dplus_pos hDplus) hD
    have hplusY : (i.dplus : ℝ) ≤ YScale P X := by
      exact (show (i.dplus : ℝ) ≤ (i.dminus : ℝ) * i.dplus by
        exact_mod_cast Nat.le_mul_of_pos_left i.dplus h.dminus_pos).trans h.dd_le_Y
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨htpos, (Nat.div_le_self _ _).trans (Nat.le_floor hplusY)⟩,
      h.dplus_squarefree.squarefree_of_dvd htDvd,
      h.dplus_coprime_Pz.coprime_dvd_left htDvd, by simp [Estimates.auxiliaryModulus]⟩
  · intro t _ht _hnot
    positivity

theorem fixedDivisorMass_le_prime_bound
    (m : ℕ) (P : Params) (X : ℝ) (b : ℕ) (indices : Finset FamilyIndex)
    (E : ExactDivisor) (dminus D : ℕ) (C : ℝ)
    (hmem : ∀ i ∈ indices, StaticMem m P X (Estimates.roughModulus X) b i)
    (hD : 0 < D) (hC : 0 ≤ C)
    (hprime : ∀ dplus : ℕ,
      (∑ p ∈ familyPrimeValues indices E dminus dplus, (1 : ℝ) / p) ≤
        C / (Nat.totient (m * E.rho) : ℝ)) :
    familyFixedEDminusDivisorMass indices E dminus D ≤
      (C / (Nat.totient (m * E.rho) : ℝ)) *
        (1 / (D : ℝ)) * Estimates.roughInitial X 1 P.σ := by
  rw [fixedDivisorMass_eq_prime_fibers]
  calc
    _ ≤ ∑ dplus ∈ (familyDplusValues indices E dminus).filter (fun dplus => D ∣ dplus),
        ((1 : ℝ) / dplus) * (C / (Nat.totient (m * E.rho) : ℝ)) := by
      exact Finset.sum_le_sum (fun dplus _ =>
        mul_le_mul_of_nonneg_left (hprime dplus) (by positivity))
    _ = (C / (Nat.totient (m * E.rho) : ℝ)) *
        ∑ dplus ∈ (familyDplusValues indices E dminus).filter (fun dplus => D ∣ dplus),
          (1 : ℝ) / dplus := by rw [Finset.mul_sum]; congr 1; ext dplus; ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left
        (dplus_multiples_recip_le_roughInitial m P X b indices E dminus D hmem hD)
        (show 0 ≤ C / (Nat.totient (m * E.rho) : ℝ) by positivity)
      simpa only [mul_assoc] using hh

/-! ## The large primes of a fibre -/

theorem StaticMem.rho_le_HScale
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ} {i : FamilyIndex}
    (h : StaticMem m P X Pz b i) : (i.rho : ℝ) ≤ HScale P X := by
  have hs : (1 : ℝ) ≤ i.E.s := by exact_mod_cast h.s_pos
  have hsp : (0 : ℝ) < i.E.s := zero_lt_one.trans_le hs
  have hprod := (le_div_iff₀ (sq_pos_of_pos hsp)).mp h.r_le
  have hsq : (i.E.s : ℝ) ≤ (i.E.s : ℝ) ^ 2 := by nlinarith
  have hh := (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg i.E.r)).trans hprod
  simpa only [FamilyIndex.rho, ExactDivisor.rho, Nat.cast_mul] using hh

/-- The large primes of members with given `(e, d₋, d₊)` all satisfy
`d₋ d₊ p ≡ -1 (mod m rad(e))`, hence lie in one reduced class modulo
`m rad(e)`; their reciprocal sum is at most the prime-window sum in that
class. -/
theorem primeValues_recip_le_btRecip
    (m : ℕ) (P : Params) (X : ℝ) (Pz b : ℕ)
    (indices : Finset FamilyIndex) (E : ExactDivisor) (dminus dplus : ℕ)
    (hmem : ∀ i ∈ indices, StaticMem m P X Pz b i) :
    ∃ a : ℕ, Nat.Coprime a (m * E.rho) ∧
      (∑ p ∈ familyPrimeValues indices E dminus dplus, (1 : ℝ) / p) ≤
        Estimates.btRecip P X (m * E.rho) a := by
  classical
  by_cases hne : (familyPrimeValues indices E dminus dplus).Nonempty
  · obtain ⟨p₀, hp₀⟩ := hne
    obtain ⟨i₀, hi₀, hip₀⟩ := Finset.mem_image.mp hp₀
    obtain ⟨hi₀I, hi₀E, hi₀minus, hi₀plus⟩ := Finset.mem_filter.mp hi₀
    have h₀ := hmem i₀ hi₀I
    have hcop : Nat.Coprime (dminus * dplus) (m * E.rho) := by
      simpa only [FamilyIndex.rho, hi₀E, hi₀minus, hi₀plus] using h₀.dd_coprime_mrho
    have hsat₀ : (dminus * dplus) * p₀ + 1 ≡ 0 [MOD m * E.rho] := by
      apply Nat.modEq_zero_iff_dvd.mpr
      simpa only [FamilyIndex.Q, FamilyIndex.rho, hi₀E, hi₀minus, hi₀plus,
        hip₀, Nat.mul_assoc] using h₀.sat_cong
    have hp₀cop : Nat.Coprime p₀ (m * E.rho) := by
      simpa only [FamilyIndex.rho, hi₀E, hip₀] using h₀.prime_coprime_mrho
    refine ⟨p₀, hp₀cop, ?_⟩
    unfold Estimates.btRecip
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨i, hi, hip⟩ := Finset.mem_image.mp hp
      obtain ⟨hiI, hiE, himinus, hiplus⟩ := Finset.mem_filter.mp hi
      have h := hmem i hiI
      have hpprime : Nat.Prime p := hip ▸ h.p_prime
      have hpwindow : p ∈ Estimates.natWindow (X ^ P.β) (X ^ (1 - P.σ)) := by
        unfold Estimates.natWindow
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
          ⟨hpprime.one_le, Nat.le_floor (hip ▸ h.p_le)⟩, hip ▸ h.p_gt⟩
      have hsat : (dminus * dplus) * p + 1 ≡ 0 [MOD m * E.rho] := by
        apply Nat.modEq_zero_iff_dvd.mpr
        simpa only [FamilyIndex.Q, FamilyIndex.rho, hiE, himinus, hiplus,
          hip, Nat.mul_assoc] using h.sat_cong
      have hmul := Nat.ModEq.add_right_cancel' 1 (hsat.trans hsat₀.symm)
      have hpcong : p ≡ p₀ [MOD m * E.rho] :=
        Nat.ModEq.cancel_left_of_coprime hcop.symm.gcd_eq_one hmul
      exact Finset.mem_filter.mpr
        ⟨hpwindow, hpprime, by simpa only [Estimates.congMod, Nat.ModEq] using hpcong⟩
    · intro p _hp _hnot
      positivity
  · refine ⟨1, Nat.coprime_one_left _, ?_⟩
    rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simpa using Estimates.btRecip_nonneg P X (m * E.rho) 1

/-- The reciprocal sum of the large primes with given `(e, d₋, d₊)` is
`O(1/φ(m rad(e)))`, uniformly in `Pz`, `b` and the finite subfamily (Lemma 3.6).
Since `θ < ν`, the modulus satisfies `m rad(e) ≤ X^ν` for large `X`. -/
theorem primeValues_recip_upper (m : ℕ) (hm : 0 < m) (P : Params)
    (ν : ℝ) (hν : 0 < ν) (hθν : P.θ < ν) (hνβ : ν < P.β) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X →
      ∀ Pz b : ℕ, ∀ indices : Finset FamilyIndex,
        (∀ i ∈ indices, StaticMem m P X Pz b i) →
        ∀ E : ExactDivisor, ∀ dminus dplus : ℕ,
          (∑ p ∈ familyPrimeValues indices E dminus dplus, (1 : ℝ) / p) ≤
            C / (Nat.totient (m * E.rho) : ℝ) := by
  obtain ⟨C, Xbt, hC, hbt⟩ := BrunHooley.prime_reciprocal_power_window_bound P ν hν hνβ
  obtain ⟨Xm, hXm⟩ := fixedNat_le_rpow_eventually_threshold m (sub_pos.mpr hθν)
  refine ⟨C, max Xbt Xm, hC, ?_⟩
  intro X hX hX1 Pz b indices hmem E dminus dplus
  by_cases hne : (familyPrimeValues indices E dminus dplus).Nonempty
  · obtain ⟨p, hp⟩ := hne
    obtain ⟨i, hi, _hip⟩ := Finset.mem_image.mp hp
    obtain ⟨hiI, hiE, _himinus, _hiplus⟩ := Finset.mem_filter.mp hi
    have h := hmem i hiI
    have hρ : 0 < E.rho := by
      have hh : 0 < i.rho := (Nat.zero_le _).trans_lt (h.medium_lt_rho hX1)
      simpa only [FamilyIndex.rho, hiE] using hh
    have hρH : (E.rho : ℝ) ≤ X ^ P.θ := by
      simpa only [hiE, HScale, FamilyIndex.rho] using h.rho_le_HScale
    have hmod : ((m * E.rho : ℕ) : ℝ) ≤ X ^ ν := by
      push_cast
      calc
        (m : ℝ) * (E.rho : ℝ) ≤ X ^ (ν - P.θ) * X ^ P.θ :=
          mul_le_mul (hXm X ((le_max_right _ _).trans hX)) hρH
            (Nat.cast_nonneg _) (Real.rpow_nonneg (zero_le_one.trans hX1.le) _)
        _ = X ^ ν := by
          rw [← Real.rpow_add (zero_lt_one.trans hX1)]
          congr 1
          ring
    obtain ⟨a, ha, hfiber⟩ := primeValues_recip_le_btRecip m P X Pz b indices E
      dminus dplus hmem
    exact hfiber.trans (hbt X ((le_max_left _ _).trans hX) (m * E.rho) a
      (Nat.mul_pos hm hρ) hmod ha)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.sum_empty]
    positivity

/-! ## Weights in residue classes -/

theorem one_div_totient_numerator_mul_le (m n : ℕ) (hm : 0 < m) :
    (1 : ℝ) / Nat.totient (m * n) ≤ 1 / (Nat.totient n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hφ : 0 < Nat.totient (m * n) := Nat.totient_pos.mpr (Nat.mul_pos hm hnpos)
  have hle : Nat.totient n ≤ Nat.totient (m * n) :=
    Nat.le_of_dvd hφ (Nat.totient_dvd_of_dvd (dvd_mul_left n m))
  apply one_div_le_one_div_of_le
    (show (0 : ℝ) < Nat.totient n by exact_mod_cast Nat.totient_pos.mpr hnpos)
  exact_mod_cast hle

theorem fixedDminus_residueMass_upper (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X →
      ∀ b : ℕ, ∀ indices : Finset FamilyIndex,
        (∀ i ∈ indices, StaticMem m P X (Estimates.roughModulus X) b i) →
        ∀ D c dminus : ℕ, 0 < D → Nat.Coprime D (Estimates.roughModulus X) →
          0 < dminus → (D : ℝ) ≤ YScale P X → (dminus : ℝ) ≤ UScale X →
          (∑ E ∈ familyExactValuesAtDminus indices D c dminus,
            familyFixedEDminusDivisorMass (indices.filter (fun i => i.e % D = c)) E dminus D) ≤
              C * (Real.log X / Real.log (zScale X)) *
                (exactDivisorMPhiMassRaw P X / ((D : ℝ) ^ 2 * dminus)) := by
  let ν := (P.θ + P.β) / 2
  have hθβ : P.θ < P.β := by linarith [P.two_θ_lt_β, P.θ_pos]
  obtain ⟨Cp, Xp, hCp, hp⟩ := primeValues_recip_upper m hm P ν
    (by dsimp [ν]; linarith [P.θ_pos])
    (by dsimp [ν]; linarith) (by dsimp [ν]; linarith)
  obtain ⟨_cr, Cr, Xr, _hcr, hCr, hr⟩ :=
    RoughReciprocal.roughInitial_two_sided P.σ 0 P.σ_pos
  obtain ⟨K, Xt, hK, ht⟩ := exactValues_recipTotient_upper m P
  refine ⟨Cp * Cr * K, max (max Xp Xr) (max Xt (Real.exp 2)), by positivity, ?_⟩
  intro X hX hX1 b indices hmem D c dminus hD hDcop hminus hDY hminusU
  have hXp : Xp ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hXr : Xr ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  have hXt : Xt ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hX)
  have hXe : Real.exp 2 ≤ X := (le_max_right _ _).trans ((le_max_right _ _).trans hX)
  have hratio : 0 ≤ Real.log X / Real.log (zScale X) :=
    div_nonneg (Real.log_pos hX1).le (Estimates.log_zScale_pos_of_exp_two_le hXe).le
  let I := indices.filter (fun i => i.e % D = c)
  have hmemI : ∀ i ∈ I, StaticMem m P X (Estimates.roughModulus X) b i :=
    fun i hi => hmem i (Finset.mem_filter.mp hi).1
  have hrough : Estimates.roughInitial X 1 P.σ ≤ Cr * (Real.log X / Real.log (zScale X)) :=
    (hr X hXr 1 (by simp)).2.2.2.2.2.1
  have hmass := ht X hXt hX1 (Estimates.roughModulus X) b indices hmem
    D c dminus hD hDcop hminus hDY hminusU
  have hpoint : ∀ E ∈ familyExactValuesAtDminus indices D c dminus,
      familyFixedEDminusDivisorMass I E dminus D ≤
        (Cp * Cr * (Real.log X / Real.log (zScale X)) / (D : ℝ)) *
          ((1 : ℝ) / Nat.totient E.rho) := by
    intro E _hE
    have hfiber := fixedDivisorMass_le_prime_bound m P X b I E dminus D Cp hmemI hD hCp.le
      (hp X hXp hX1 _ b I hmemI E dminus)
    have hcoeff : Cp / (Nat.totient (m * E.rho) : ℝ) ≤ Cp / (Nat.totient E.rho : ℝ) := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
        (one_div_totient_numerator_mul_le m E.rho hm) hCp.le
    calc
      _ ≤ (Cp / (Nat.totient (m * E.rho) : ℝ)) *
          (1 / (D : ℝ)) * Estimates.roughInitial X 1 P.σ := hfiber
      _ ≤ (Cp / (Nat.totient E.rho : ℝ)) *
          (1 / (D : ℝ)) * Estimates.roughInitial X 1 P.σ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff (by positivity))
          (Estimates.roughInitial_nonneg _ _ _)
      _ ≤ (Cp / (Nat.totient E.rho : ℝ)) *
          (1 / (D : ℝ)) * (Cr * (Real.log X / Real.log (zScale X))) :=
        mul_le_mul_of_nonneg_left hrough (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ E ∈ familyExactValuesAtDminus indices D c dminus,
        (Cp * Cr * (Real.log X / Real.log (zScale X)) / (D : ℝ)) *
          ((1 : ℝ) / Nat.totient E.rho) := Finset.sum_le_sum hpoint
    _ = (Cp * Cr * (Real.log X / Real.log (zScale X)) / (D : ℝ)) *
        ∑ E ∈ familyExactValuesAtDminus indices D c dminus,
          ((1 : ℝ) / Nat.totient E.rho) := by rw [Finset.mul_sum]
    _ ≤ (Cp * Cr * (Real.log X / Real.log (zScale X)) / (D : ℝ)) *
        ((K / ((D : ℝ) * dminus)) * exactDivisorMPhiMassRaw P X) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

theorem residue_sum_eq_dminus_exact_partition (indices : Finset FamilyIndex) (D c : ℕ) :
    (∑ i ∈ indices.filter (fun i => D ∣ i.dplus ∧ i.e % D = c),
      (1 : ℝ) / ((i.dplus * i.p : ℕ) : ℝ)) =
      ∑ dminus ∈ indices.image (fun i => i.dminus),
        ∑ E ∈ familyExactValuesAtDminus indices D c dminus,
          familyFixedEDminusDivisorMass (indices.filter (fun i => i.e % D = c)) E dminus D := by
  classical
  let S := indices.filter (fun i => D ∣ i.dplus ∧ i.e % D = c)
  have hmaps : ∀ i ∈ S, i.dminus ∈ indices.image (fun i => i.dminus) := by
    intro i hi
    exact Finset.mem_image.mpr ⟨i, (Finset.mem_filter.mp hi).1, rfl⟩
  have hp := Finset.sum_fiberwise_of_maps_to hmaps
    (fun i : FamilyIndex => (1 : ℝ) / ((i.dplus * i.p : ℕ) : ℝ))
  change (∑ i ∈ S, (1 : ℝ) / ((i.dplus * i.p : ℕ) : ℝ)) = _
  rw [← hp]
  apply Finset.sum_congr rfl
  intro dminus _hdminus
  let T := S.filter (fun i => i.dminus = dminus)
  have hEMaps : ∀ i ∈ T, i.E ∈ familyExactValuesAtDminus indices D c dminus := by
    intro i hi
    obtain ⟨hiS, himinus⟩ := Finset.mem_filter.mp hi
    obtain ⟨hiI, hiD, hic⟩ := Finset.mem_filter.mp hiS
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiI, himinus, hiD, hic⟩, rfl⟩
  have hEp := Finset.sum_fiberwise_of_maps_to hEMaps
    (fun i : FamilyIndex => (1 : ℝ) / ((i.dplus * i.p : ℕ) : ℝ))
  change (∑ i ∈ T, (1 : ℝ) / ((i.dplus * i.p : ℕ) : ℝ)) = _
  rw [← hEp]
  apply Finset.sum_congr rfl
  intro E _hE
  unfold familyFixedEDminusDivisorMass
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp only [T, S, Finset.mem_filter]
  tauto

theorem dminus_recip_sum_le_smallDivisorWeight
    (m : ℕ) (P : Params) (X : ℝ) (b : ℕ) (indices : Finset FamilyIndex)
    (hmem : ∀ i ∈ indices, StaticMem m P X (Estimates.roughModulus X) b i) :
    (∑ d ∈ indices.image (fun i => i.dminus), (1 : ℝ) / d) ≤
      Estimates.smallDivisorWeight X 1 := by
  classical
  unfold Estimates.smallDivisorWeight
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
    have h := hmem i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨h.dminus_pos, Nat.le_floor h.dminus_le_U⟩, h.dminus_dvd_Pz, h.dminus_odd, by simp⟩
  · intro d _hd _hnot
    positivity

/-- For `D ≤ Y` coprime to `P(z)`, the event mass of the indices with
`D ∣ d₊` and `e ≡ c (mod D)` is `≪ log X · M_φ / D²`, uniformly over finite
subfamilies of the family. -/
theorem residue_event_upper (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X →
      ∀ b : ℕ, ∀ indices : Finset FamilyIndex,
        (∀ i ∈ indices, StaticMem m P X (Estimates.roughModulus X) b i) →
        ∀ D c : ℕ, 0 < D → Nat.Coprime D (Estimates.roughModulus X) →
          (D : ℝ) ≤ YScale P X →
          (∑ i ∈ indices.filter (fun i => D ∣ i.dplus ∧ i.e % D = c),
            (1 : ℝ) / ((i.dplus * i.p : ℕ) : ℝ)) ≤
              C * Real.log X * (exactDivisorMPhiMassRaw P X / (D : ℝ) ^ 2) := by
  obtain ⟨Cf, Xf, hCf, hf⟩ := fixedDminus_residueMass_upper m hm P
  obtain ⟨Cs, Xs, hCs, hs⟩ := Estimates.smallDivisorWeight_upper_logZ
  refine ⟨Cf * Cs, max (max Xf Xs) (Real.exp 2), by positivity, ?_⟩
  intro X hX hX1 b indices hmem D c hD hDcop hDY
  have hXf : Xf ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hXs : Xs ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  have hXe : Real.exp 2 ≤ X := (le_max_right _ _).trans hX
  have hlogz : 0 < Real.log (zScale X) := Estimates.log_zScale_pos_of_exp_two_le hXe
  have hratio : 0 ≤ Real.log X / Real.log (zScale X) :=
    div_nonneg (Real.log_pos hX1).le hlogz.le
  have hM : 0 ≤ exactDivisorMPhiMassRaw P X := by
    unfold exactDivisorMPhiMassRaw
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  let F := Cf * (Real.log X / Real.log (zScale X)) *
    (exactDivisorMPhiMassRaw P X / (D : ℝ) ^ 2)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  rw [residue_sum_eq_dminus_exact_partition]
  calc
    _ ≤ ∑ dminus ∈ indices.image (fun i => i.dminus), F * ((1 : ℝ) / dminus) := by
      apply Finset.sum_le_sum
      intro dminus hdminus
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hdminus
      have h := hmem i hi
      have hbound := hf X hXf hX1 b indices hmem D c i.dminus hD hDcop
        h.dminus_pos hDY h.dminus_le_U
      exact hbound.trans_eq (by dsimp [F]; ring)
    _ = F * ∑ dminus ∈ indices.image (fun i => i.dminus), (1 : ℝ) / dminus := by
      rw [Finset.mul_sum]
    _ ≤ F * (Cs * Real.log (zScale X)) := by
      apply mul_le_mul_of_nonneg_left _ hF
      exact (dminus_recip_sum_le_smallDivisorWeight m P X b indices hmem).trans
        (hs X hXs 1)
    _ = _ := by
      dsimp [F]
      field_simp

theorem divisor_event_upper (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X →
      ∀ b : ℕ, ∀ indices : Finset FamilyIndex,
        (∀ i ∈ indices, StaticMem m P X (Estimates.roughModulus X) b i) →
        ∀ D : ℕ, 0 < D → Nat.Coprime D (Estimates.roughModulus X) →
          (D : ℝ) ≤ YScale P X →
          (∑ i ∈ indices.filter (fun i => D ∣ i.dplus),
            (1 : ℝ) / ((i.dplus * i.p : ℕ) : ℝ)) ≤
              C * Real.log X * (exactDivisorMPhiMassRaw P X / (D : ℝ)) := by
  obtain ⟨C, X₀, hC, hres⟩ := residue_event_upper m hm P
  refine ⟨C, X₀, hC, ?_⟩
  intro X hX hX1 b indices hmem D hD hDcop hDY
  let S := indices.filter (fun i => D ∣ i.dplus)
  have hmaps : ∀ i ∈ S, i.e % D ∈ Finset.range D := by
    intro i _hi
    exact Finset.mem_range.mpr (Nat.mod_lt _ hD)
  have hp := Finset.sum_fiberwise_of_maps_to hmaps
    (fun i : FamilyIndex => (1 : ℝ) / ((i.dplus * i.p : ℕ) : ℝ))
  change (∑ i ∈ S, (1 : ℝ) / ((i.dplus * i.p : ℕ) : ℝ)) ≤ _
  rw [← hp]
  calc
    _ ≤ ∑ _c ∈ Finset.range D,
        C * Real.log X * (exactDivisorMPhiMassRaw P X / (D : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro c _hc
      have hh := hres X hX hX1 b indices hmem D c hD hDcop hDY
      simpa only [S, Finset.filter_filter] using hh
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

/-- The residue-class and divisor event masses are `≪ (log X)³/D²` and
`≪ (log X)³/D` respectively. -/
theorem event_upper_log_cube (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X →
      ∀ b : ℕ, ∀ indices : Finset FamilyIndex,
        (∀ i ∈ indices, StaticMem m P X (Estimates.roughModulus X) b i) →
        ∀ D : ℕ, 0 < D → Nat.Coprime D (Estimates.roughModulus X) →
          (D : ℝ) ≤ YScale P X →
          (∀ c : ℕ, (∑ i ∈ indices.filter (fun i => D ∣ i.dplus ∧ i.e % D = c),
            (1 : ℝ) / ((i.dplus * i.p : ℕ) : ℝ)) ≤ C * (Real.log X) ^ 3 / (D : ℝ) ^ 2) ∧
          (∑ i ∈ indices.filter (fun i => D ∣ i.dplus),
            (1 : ℝ) / ((i.dplus * i.p : ℕ) : ℝ)) ≤ C * (Real.log X) ^ 3 / (D : ℝ) := by
  obtain ⟨Cr, Xr, hCr, hr⟩ := residue_event_upper m hm P
  obtain ⟨Cd, Xd, hCd, hd⟩ := divisor_event_upper m hm P
  obtain ⟨_cl, Cm, Xm, _hcl, hCm, hmass⟩ := ProgressionEstimates.quadratic_masses P
  let C := max Cr Cd * Cm
  have hC : 0 < C := mul_pos (hCr.trans_le (le_max_left _ _)) hCm
  refine ⟨C, max Xm (max Xr Xd), hC, ?_⟩
  intro X hX hX1 b indices hmem D hD hDcop hDY
  have hXm : Xm ≤ X := (le_max_left _ _).trans hX
  have hXr : Xr ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hX)
  have hXd : Xd ≤ X := (le_max_right _ _).trans ((le_max_right _ _).trans hX)
  have hM := (hmass X hXm).2.2
  have hlog : 0 ≤ Real.log X := (Real.log_pos hX1).le
  have hDreal : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  constructor
  · intro c
    apply (hr X hXr hX1 b indices hmem D c hD hDcop hDY).trans
    calc
      Cr * Real.log X * (exactDivisorMPhiMassRaw P X / (D : ℝ) ^ 2) ≤
          Cr * Real.log X * ((Cm * (Real.log X) ^ 2) / (D : ℝ) ^ 2) := by gcongr
      _ = (Cr * Cm) * (Real.log X) ^ 3 / (D : ℝ) ^ 2 := by ring
      _ ≤ C * (Real.log X) ^ 3 / (D : ℝ) ^ 2 := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left Cr Cd) hCm.le)
          (pow_nonneg hlog 3)) (sq_nonneg (D : ℝ))
  · apply (hd X hXd hX1 b indices hmem D hD hDcop hDY).trans
    calc
      Cd * Real.log X * (exactDivisorMPhiMassRaw P X / (D : ℝ)) ≤
          Cd * Real.log X * ((Cm * (Real.log X) ^ 2) / (D : ℝ)) := by gcongr
      _ = (Cd * Cm) * (Real.log X) ^ 3 / (D : ℝ) := by ring
      _ ≤ C * (Real.log X) ^ 3 / (D : ℝ) := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right Cr Cd) hCm.le)
          (pow_nonneg hlog 3)) hDreal.le

theorem indexFinset_event_upper_log_cube (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X →
      ∀ b D : ℕ, 0 < D → Nat.Coprime D (Estimates.roughModulus X) →
        (D : ℝ) ≤ YScale P X →
        let I := indexFinset m P X (Estimates.roughModulus X) b
        (∀ c : ℕ, (∑ i ∈ I.filter (fun i => D ∣ i.dplus ∧ i.e % D = c),
          (1 : ℝ) / ((i.dplus * i.p : ℕ) : ℝ)) ≤ C * (Real.log X) ^ 3 / (D : ℝ) ^ 2) ∧
        (∑ i ∈ I.filter (fun i => D ∣ i.dplus),
          (1 : ℝ) / ((i.dplus * i.p : ℕ) : ℝ)) ≤ C * (Real.log X) ^ 3 / (D : ℝ) := by
  obtain ⟨C, X₀, hC, hu⟩ := event_upper_log_cube m hm P
  refine ⟨C, X₀, hC, ?_⟩
  intro X hX hX1 b D hD hDcop hDY
  apply hu X hX hX1 b _ _ D hD hDcop hDY
  intro i hi
  exact (mem_indexFinset_iff m P X _ b i (zero_lt_one.trans hX1)).mp hi

theorem indexFinset_mass_upper_log_cube (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X → ∀ b : ℕ,
      (∑ i ∈ indexFinset m P X (Estimates.roughModulus X) b,
        (1 : ℝ) / ((i.dplus * i.p : ℕ) : ℝ)) ≤ C * (Real.log X) ^ 3 := by
  obtain ⟨C, X₀, hC, hu⟩ := indexFinset_event_upper_log_cube m hm P
  refine ⟨C, X₀, hC, ?_⟩
  intro X hX hX1 b
  have hY : (1 : ℝ) ≤ YScale P X := Real.one_le_rpow hX1.le P.σ_pos.le
  simpa only [one_dvd, Finset.filter_true, Nat.cast_one, div_one] using
    (hu X hX hX1 b 1 (by norm_num) (by simp) (by simpa only [Nat.cast_one] using hY)).2

end ErdosStraus.FixedNumeratorFamily

/-! ## Weights relative to `μ_b` -/

namespace ErdosStraus.FixedNumeratorFamily

open Classical Filter Family
open scoped BigOperators

/-- Propositions 6.6 and 6.7, uniformly in reduced `b (mod P(z))`: `μ_b ≍ (log X)³`,
and for every `D > 0` coprime to `P(z)` and every residue `a`,
`B_{D,a} ≤ K μ_b / D²` and `∑_{D ∣ d₊} w_i ≤ K μ_b / D`.
For `D > Y` both sums are empty, since `d₊ ≤ Y`. -/
theorem mass_and_distribution (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c C K : ℝ, 0 < c ∧ 0 < C ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ b : ℕ, Nat.Coprime b (Estimates.roughModulus X) →
        let I := indexFinset m P X (Estimates.roughModulus X) b
        c * (Real.log X) ^ 3 ≤ indexMass I ∧
        indexMass I ≤ C * (Real.log X) ^ 3 ∧
        ∀ D : ℕ, 0 < D → Nat.Coprime D (Estimates.roughModulus X) →
          (∀ a : ℕ, (∑ i ∈ I.filter (fun i => D ∣ i.dplus ∧ i.e % D = a),
            (1 : ℝ) / i.q) ≤ K * indexMass I / (D : ℝ) ^ 2) ∧
          (∑ i ∈ I.filter (fun i => D ∣ i.dplus), (1 : ℝ) / i.q) ≤
            K * indexMass I / (D : ℝ) := by
  obtain ⟨c, Xc, hc, hlower⟩ := indexMass_lower m hm P
  obtain ⟨C, XC, hC, hupper⟩ := indexFinset_mass_upper_log_cube m hm P
  obtain ⟨A, XA, hA, hdist⟩ := indexFinset_event_upper_log_cube m hm P
  let K := A / c
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨c, C, K, hc, hC, hK, ?_⟩
  filter_upwards [eventually_ge_atTop Xc, eventually_ge_atTop XC,
    eventually_ge_atTop XA, eventually_gt_atTop 1] with X hXc hXC hXA hX1
  intro b hb
  let I := indexFinset m P X (Estimates.roughModulus X) b
  have hl : c * (Real.log X) ^ 3 ≤ indexMass I := hlower X hXc hX1 b hb
  have hu : indexMass I ≤ C * (Real.log X) ^ 3 := hupper X hXC hX1 b
  refine ⟨hl, hu, ?_⟩
  intro D hD hcop
  have hscaled : A * (Real.log X) ^ 3 ≤ K * indexMass I := by
    calc
      A * (Real.log X) ^ 3 = K * (c * (Real.log X) ^ 3) := by
        dsimp [K]
        field_simp
      _ ≤ K * indexMass I := mul_le_mul_of_nonneg_left hl hK.le
  by_cases hDY : (D : ℝ) ≤ YScale P X
  · obtain ⟨hr, hd⟩ := hdist X hXA hX1 b D hD hcop hDY
    refine ⟨?_, ?_⟩
    · intro a
      exact (hr a).trans (div_le_div_of_nonneg_right hscaled (sq_nonneg (D : ℝ)))
    · exact hd.trans (div_le_div_of_nonneg_right hscaled (Nat.cast_nonneg D))
  · have hnot : ∀ i ∈ I, ¬ D ∣ i.dplus := by
      intro i hi hdiv
      have hmem := (mem_indexFinset_iff m P X _ b i (zero_lt_one.trans hX1)).mp hi
      have hle : (D : ℝ) ≤ i.dplus := by
        exact_mod_cast Nat.le_of_dvd hmem.dplus_pos hdiv
      exact hDY (hle.trans hmem.dplus_le_YScale)
    have hz : I.filter (fun i => D ∣ i.dplus) = ∅ :=
      Finset.filter_eq_empty_iff.mpr hnot
    have hzr (a : ℕ) : I.filter (fun i => D ∣ i.dplus ∧ i.e % D = a) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun i hi h => hnot i hi h.1)
    have hμ := indexMass_nonneg I
    constructor
    · intro a
      rw [hzr a, Finset.sum_empty]
      positivity
    · rw [hz, Finset.sum_empty]
      positivity

end ErdosStraus.FixedNumeratorFamily
