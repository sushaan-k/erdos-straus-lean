import ErdosStraus.CubicSums.Titchmarsh
import ErdosStraus.CubicSums.FanMass

/-!
# The divisor sets `Λ_int(a)` and `Λ_<(a)`

For `a ≥ 1` put `Λ_int(a) = {h ∣ a² : h ∉ {1, a, a²}}` and `Λ_<(a) = {h ∣ a² : 1 < h < a}`.
We prove Proposition 4.5: a subfamily of `a ≤ L` with pairwise coprime moduli `4a - 1` carries
mass `∑ |Λ_int(a)|/(4a-1) ≪ (log L)²`. We also show `|Λ_int(a)| = 2 |Λ_<(a)| = τ(a²) - 3` for
`a ≥ 2`, restate Propositions 4.2 and 4.5 for these sets, derive the consequences of
Proposition 4.3 at odd prime powers and at the prime `2`, and check the prime-power case of the
identity in Lemma 4.1.
-/

namespace ErdosStraus.Estimates

/-! ## Proposition 4.5: subfamilies with pairwise coprime moduli -/

/-- Lemma 4.4 for `titchSum`: `|titchSum L| ≤ C (log L)²` for large `L`. -/
theorem titchSum_le_log_square :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L : ℝ, L₀ ≤ L →
      |titchSum L| ≤ C * (Real.log L) ^ (2 : ℝ) :=
  by simpa only [titchSum, tau] using DivisorEstimates.weighted_titchmarsh_divisor_bound

/-- The prime moduli of any subfamily carry mass `O((log L)²)`. -/
theorem pairwisePrimeSubfanMass_le_log_square :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L : ℝ, L₀ ≤ L → ∀ B : Finset ℕ,
      pairwisePrimeSubfanMass L B ≤ C * (Real.log L) ^ (2 : ℝ) := by
  rcases titchSum_le_log_square with
    ⟨C, L₀, hC, hbound⟩
  refine ⟨C, L₀, hC, ?_⟩
  intro L hL B
  have hprime := pairwisePrimeSubfanMass_le_titchSum L B
  have htitch_nonneg : 0 ≤ titchSum L := titchSum_nonneg L
  have htitch_abs := hbound L hL
  rw [abs_of_nonneg htitch_nonneg] at htitch_abs
  exact le_trans hprime htitch_abs

/-- Proposition 4.5 from a pointwise bound on the composite moduli in terms of their least
prime factor `r`: `|Λ_int(a)|/(4a-1) ≤ K r^{-2+2η}` with `η < 1/2`. The least prime factors
are distinct, so the composite moduli contribute at most `K ∑_r r^{-2+2η}`. -/
theorem pairwiseSubfanMass_le_log_square_of_minFac
    {K η : ℝ} (hK : 0 ≤ K) (hη : η < 1 / 2)
    (hpoint : ∀ L : ℝ, ∀ B : Finset ℕ, pairwiseFanModuliCoprime B →
      ∀ a : ℕ,
        a ∈ (B.filter (fun a => 1 ≤ a ∧ a ≤ ⌊L⌋₊)).filter
          (fun a => ¬ Nat.Prime (4 * a - 1)) →
        interiorFanWeight a ≤
          K * ((Nat.minFac (4 * a - 1) : ℝ) ^ (-2 + 2 * η))) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L : ℝ, L₀ ≤ L → ∀ B : Finset ℕ,
      pairwiseFanModuliCoprime B →
      pairwiseSubfanMass L B ≤ C * (Real.log L) ^ (2 : ℝ) := by
  rcases pairwisePrimeSubfanMass_le_log_square with
    ⟨Cprime, Lprime, hCprime, hprime⟩
  let T : ℝ := ∑' r : ℕ, ((r : ℝ) ^ (-2 + 2 * η))
  refine ⟨Cprime + K * T, max Lprime (Real.exp 1), ?_, ?_⟩
  · have hT_nonneg : 0 ≤ T := by
      dsimp [T]
      exact tsum_nonneg
        (fun r : ℕ => Real.rpow_nonneg (Nat.cast_nonneg r) _)
    exact add_pos_of_pos_of_nonneg hCprime (mul_nonneg hK hT_nonneg)
  intro L hL B hcop
  have hLprime : Lprime ≤ L := le_trans (le_max_left _ _) hL
  have hLexp : Real.exp 1 ≤ L := le_trans (le_max_right _ _) hL
  have hlog_ge_one : (1 : ℝ) ≤ Real.log L := by
    have hlog := Real.log_le_log (Real.exp_pos 1) hLexp
    simpa using hlog
  have hlogpow_ge_one : (1 : ℝ) ≤ (Real.log L) ^ (2 : ℝ) :=
    Real.one_le_rpow hlog_ge_one (by norm_num)
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    exact tsum_nonneg
      (fun r : ℕ => Real.rpow_nonneg (Nat.cast_nonneg r) _)
  have hKT_nonneg : 0 ≤ K * T := mul_nonneg hK hT_nonneg
  have hcomp :
      pairwiseCompositeSubfanMass L B ≤ K * T := by
    exact pairwiseCompositeSubfanMass_upper_of_pointwise_minFac L hcop hK hη
      (hpoint L B hcop)
  have hprimeL :
      pairwisePrimeSubfanMass L B ≤ Cprime * (Real.log L) ^ (2 : ℝ) :=
    hprime L hLprime B
  have hcomp_log :
      K * T ≤ (K * T) * (Real.log L) ^ (2 : ℝ) := by
    calc
      K * T = (K * T) * 1 := by ring
      _ ≤ (K * T) * (Real.log L) ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_left hlogpow_ge_one hKT_nonneg
  rw [pairwiseSubfanMass_eq_prime_add_composite]
  calc
    pairwisePrimeSubfanMass L B + pairwiseCompositeSubfanMass L B
        ≤ Cprime * (Real.log L) ^ (2 : ℝ) + K * T :=
          add_le_add hprimeL hcomp
    _ ≤ Cprime * (Real.log L) ^ (2 : ℝ) +
        (K * T) * (Real.log L) ^ (2 : ℝ) :=
          add_le_add_right hcomp_log _
    _ = (Cprime + K * T) * (Real.log L) ^ (2 : ℝ) := by
          ring

/-- Proposition 4.5 from a divisor bound `τ(a²) ≤ K a^η` with `0 ≤ η < 1/2`. -/
theorem pairwiseSubfanMass_le_log_square_of_tau_power
    {K η : ℝ} (hK : 0 ≤ K) (hη_nonneg : 0 ≤ η) (hη : η < 1 / 2)
    (htau : ∀ a : ℕ, 1 ≤ a →
      ((tau (a ^ 2) : ℕ) : ℝ) ≤ K * (a : ℝ) ^ η) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L : ℝ, L₀ ≤ L → ∀ B : Finset ℕ,
      pairwiseFanModuliCoprime B →
      pairwiseSubfanMass L B ≤ C * (Real.log L) ^ (2 : ℝ) := by
  have hη_one : η < 1 := by linarith
  exact
    pairwiseSubfanMass_le_log_square_of_minFac
      hK hη
      (fun _L _B _hcop a ha =>
        interiorFanWeight_le_minFac_rpow_of_tau_square_subpower
          hK hη_nonneg hη_one htau
          (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2.1
          (Finset.mem_filter.mp ha).2)

/-- Proposition 4.5: if the moduli `4a - 1`, `a ∈ B`, are pairwise coprime, then
`∑_{a ∈ B, a ≤ L} |Λ_int(a)|/(4a-1) ≪ (log L)²`. -/
theorem pairwiseSubfanMass_le_log_square :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L : ℝ, L₀ ≤ L → ∀ B : Finset ℕ,
      pairwiseFanModuliCoprime B →
      pairwiseSubfanMass L B ≤ C * (Real.log L) ^ (2 : ℝ) := by
  exact
    pairwiseSubfanMass_le_log_square_of_tau_power
      (K := tauSquareQuarterConstant) (η := (1 : ℝ) / 4)
      (by dsimp [tauSquareQuarterConstant]; positivity)
      (by norm_num) (by norm_num)
      (fun a ha => tau_square_le_const_rpow_quarter ha)

end ErdosStraus.Estimates

namespace ErdosStraus.DivisorEstimates

open Filter
open scoped BigOperators

/-! ## The divisor sets `Λ_int(a)` and `Λ_<(a)` -/

/-- `Λ_int(a) = {h ∣ a² : h ∉ {1, a, a²}}`. -/
def interiorDivisors (a : ℕ) : Finset ℕ :=
  (a ^ 2).divisors.filter (fun h => h ≠ 1 ∧ h ≠ a ∧ h ≠ a ^ 2)

/-- `Λ_<(a) = {h ∣ a² : 1 < h < a}`. -/
def lowerDivisors (a : ℕ) : Finset ℕ :=
  (a ^ 2).divisors.filter (fun h => 1 < h ∧ h < a)

/-- The divisors of `a²` strictly between `a` and `a²`. -/
def upperDivisors (a : ℕ) : Finset ℕ :=
  (a ^ 2).divisors.filter (fun h => a < h ∧ h < a ^ 2)

theorem interiorDivisors_eq_sdiff (a : ℕ) :
    interiorDivisors a = (a ^ 2).divisors \ {1, a, a ^ 2} := by
  ext h
  simp only [interiorDivisors, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert,
    Finset.mem_singleton, not_or]

theorem boundaryDivisors_subset {a : ℕ} (ha : 1 ≤ a) :
    ({1, a, a ^ 2} : Finset ℕ) ⊆ (a ^ 2).divisors := by
  intro h hh
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 (by omega)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with rfl | rfl | rfl
  · exact Nat.mem_divisors.mpr ⟨one_dvd _, ha2⟩
  · exact Nat.mem_divisors.mpr ⟨Dvd.intro_left _ (sq h).symm, ha2⟩
  · exact Nat.mem_divisors.mpr ⟨dvd_refl _, ha2⟩

theorem card_boundaryDivisors {a : ℕ} (ha : 2 ≤ a) :
    ({1, a, a ^ 2} : Finset ℕ).card = 3 := by
  have h1 : 1 ≠ a := by omega
  have h2 : a < a ^ 2 := by nlinarith
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp only [Finset.mem_singleton]
    omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor <;> omega

theorem three_le_tau_sq {a : ℕ} (ha : 2 ≤ a) : 3 ≤ Estimates.tau (a ^ 2) := by
  have h := Finset.card_le_card (boundaryDivisors_subset (a := a) (by omega))
  rw [card_boundaryDivisors ha] at h
  exact h

/-- `|Λ_int(a)| = τ(a²) - 3` for `a ≥ 2`. -/
theorem card_interiorDivisors {a : ℕ} (ha : 2 ≤ a) :
    (interiorDivisors a).card = Estimates.tau (a ^ 2) - 3 := by
  rw [interiorDivisors_eq_sdiff, Finset.card_sdiff_of_subset (boundaryDivisors_subset (by omega)),
    card_boundaryDivisors ha]
  rfl

theorem interiorDivisors_one : interiorDivisors 1 = ∅ := by
  decide

/-- `|Λ_int(a)|` in the form used by `Estimates.divisorFanInteriorMass`. -/
theorem cast_card_interiorDivisors {a : ℕ} (ha : 1 ≤ a) :
    ((interiorDivisors a).card : ℝ) =
      if a = 1 then 0 else ((Estimates.tau (a ^ 2) : ℕ) : ℝ) - 3 := by
  split_ifs with h1
  · subst h1
    simp [interiorDivisors_one]
  · have ha2 : 2 ≤ a := by omega
    rw [card_interiorDivisors ha2, Nat.cast_sub (three_le_tau_sq ha2)]
    norm_num

theorem interiorDivisors_eq_union {a : ℕ} (ha : 1 ≤ a) :
    interiorDivisors a = lowerDivisors a ∪ upperDivisors a := by
  ext h
  simp only [interiorDivisors, lowerDivisors, upperDivisors, Finset.mem_union,
    Finset.mem_filter]
  constructor
  · rintro ⟨hd, h1, h2, h3⟩
    have hpos : 0 < h := Nat.pos_of_mem_divisors hd
    have hle : h ≤ a ^ 2 := Nat.divisor_le hd
    rcases lt_trichotomy h a with hlt | heq | hgt
    · exact Or.inl ⟨hd, by omega, hlt⟩
    · exact absurd heq h2
    · exact Or.inr ⟨hd, hgt, lt_of_le_of_ne hle h3⟩
  · rintro (⟨hd, h1, h2⟩ | ⟨hd, h1, h2⟩)
    · have : h ≠ a ^ 2 := by
        have : a ≤ a ^ 2 := by nlinarith
        omega
      exact ⟨hd, by omega, by omega, this⟩
    · exact ⟨hd, by omega, by omega, by omega⟩

theorem disjoint_lowerDivisors_upperDivisors (a : ℕ) :
    Disjoint (lowerDivisors a) (upperDivisors a) := by
  rw [Finset.disjoint_left]
  intro h hl hu
  simp only [lowerDivisors, upperDivisors, Finset.mem_filter] at hl hu
  omega

/-- The involution `h ↦ a²/h` maps the divisors below `a` onto those above `a`. -/
theorem card_upperDivisors_eq (a : ℕ) :
    (upperDivisors a).card = (lowerDivisors a).card := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [upperDivisors, lowerDivisors]
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha.ne'
  have hsq : a ^ 2 = a * a := sq a
  have hmul : ∀ {h : ℕ}, h ∣ a ^ 2 → h * (a ^ 2 / h) = a ^ 2 :=
    fun hd => Nat.mul_div_cancel' hd
  refine Finset.card_nbij' (fun h => a ^ 2 / h) (fun h => a ^ 2 / h) ?_ ?_ ?_ ?_
  · intro h hh
    simp only [upperDivisors, lowerDivisors, Finset.mem_coe, Finset.mem_filter,
      Nat.mem_divisors] at hh ⊢
    obtain ⟨⟨hd, -⟩, h1, h2⟩ := hh
    have hk := hmul hd
    refine ⟨⟨Nat.div_dvd_of_dvd hd, ha2⟩, ?_, ?_⟩
    · by_contra hc
      push Not at hc
      have : h * (a ^ 2 / h) ≤ h * 1 := Nat.mul_le_mul_left h hc
      omega
    · by_contra hc
      push Not at hc
      have : h * a ≤ h * (a ^ 2 / h) := Nat.mul_le_mul_left h hc
      nlinarith
  · intro h hh
    simp only [upperDivisors, lowerDivisors, Finset.mem_coe, Finset.mem_filter,
      Nat.mem_divisors] at hh ⊢
    obtain ⟨⟨hd, -⟩, h1, h2⟩ := hh
    have hk := hmul hd
    refine ⟨⟨Nat.div_dvd_of_dvd hd, ha2⟩, ?_, ?_⟩
    · by_contra hc
      push Not at hc
      have : h * (a ^ 2 / h) ≤ h * a := Nat.mul_le_mul_left h hc
      nlinarith
    · by_contra hc
      push Not at hc
      have : h * a ^ 2 ≤ h * (a ^ 2 / h) := Nat.mul_le_mul_left h hc
      nlinarith
  · intro h hh
    simp only [upperDivisors, Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hh
    exact Nat.div_div_self hh.1.1 ha2
  · intro h hh
    simp only [lowerDivisors, Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hh
    exact Nat.div_div_self hh.1.1 ha2

/-- `|Λ_int(a)| = 2 |Λ_<(a)|` for `a ≥ 1`. -/
theorem card_interiorDivisors_eq_two_mul {a : ℕ} (ha : 1 ≤ a) :
    (interiorDivisors a).card = 2 * (lowerDivisors a).card := by
  rw [interiorDivisors_eq_union ha,
    Finset.card_union_of_disjoint (disjoint_lowerDivisors_upperDivisors a),
    card_upperDivisors_eq]
  ring

/-- `|Λ_<(a)|` in the form used by `Estimates.divisorFanLowerMass`. -/
theorem cast_card_lowerDivisors {a : ℕ} (ha : 1 ≤ a) :
    ((lowerDivisors a).card : ℝ) =
      if a = 1 then 0 else (((Estimates.tau (a ^ 2) : ℕ) : ℝ) - 3) / 2 := by
  have h := cast_card_interiorDivisors ha
  rw [card_interiorDivisors_eq_two_mul ha] at h
  push_cast at h
  split_ifs at h ⊢ <;> linarith

/-! ## The cubic sums of Proposition 4.2 -/

/-- The interior sum `∑_{a ≤ L} |Λ_int(a)|/(4a-1)` equals
`Estimates.divisorFanInteriorMass L`. -/
theorem interiorDivisors_sum_eq (L : ℝ) :
    ∑ a ∈ Finset.Icc 1 ⌊L⌋₊, ((interiorDivisors a).card : ℝ) / (4 * (a : ℝ) - 1) =
      Estimates.divisorFanInteriorMass L := by
  unfold Estimates.divisorFanInteriorMass
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [cast_card_interiorDivisors (Finset.mem_Icc.mp ha).1]

/-- The lower sum `∑_{a ≤ L} |Λ_<(a)|/(4a-1)` equals
`Estimates.divisorFanLowerMass L`. -/
theorem lowerDivisors_sum_eq (L : ℝ) :
    ∑ a ∈ Finset.Icc 1 ⌊L⌋₊, ((lowerDivisors a).card : ℝ) / (4 * (a : ℝ) - 1) =
      Estimates.divisorFanLowerMass L := by
  unfold Estimates.divisorFanLowerMass
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [cast_card_lowerDivisors (Finset.mem_Icc.mp ha).1]

/-- Proposition 4.2, first part:
`∑_{a ≤ L} |Λ_int(a)|/(4a-1) ∼ (log L)³/(24 ζ(2))`. -/
theorem interiorDivisors_sum_asymptotic :
    Tendsto
      (fun L : ℝ =>
        (∑ a ∈ Finset.Icc 1 ⌊L⌋₊, ((interiorDivisors a).card : ℝ) / (4 * (a : ℝ) - 1)) /
          (Real.log L) ^ (3 : ℝ))
      atTop (nhds (1 / (24 * Estimates.zeta2))) := by
  simp_rw [interiorDivisors_sum_eq]
  exact Estimates.divisorFanInteriorMass_asymptotic_from_cubic_estimate

/-- Proposition 4.2, second part:
`∑_{a ≤ L} |Λ_<(a)|/(4a-1) ∼ (log L)³/(48 ζ(2))`. -/
theorem lowerDivisors_sum_asymptotic :
    Tendsto
      (fun L : ℝ =>
        (∑ a ∈ Finset.Icc 1 ⌊L⌋₊, ((lowerDivisors a).card : ℝ) / (4 * (a : ℝ) - 1)) /
          (Real.log L) ^ (3 : ℝ))
      atTop (nhds (1 / (48 * Estimates.zeta2))) := by
  simp_rw [lowerDivisors_sum_eq]
  exact Estimates.divisorFanLowerMass_asymptotic_from_cubic_estimate

/-! ## Local restrictions in Proposition 4.3 -/

/-- The prime `2` in Proposition 4.3: since `4a-1` is odd, an odd class `n ≡ c (mod 2^k)`
and any class `n ≡ r (mod 4a-1)` hold simultaneously for some natural `n`. -/
theorem exists_two_adic_class {a : ℕ} (ha : 1 ≤ a) (k : ℕ) {c : ℤ} (hc : Odd c) (r : ℤ) :
    ∃ n : ℕ, (n : ℤ) ≡ c [ZMOD 2 ^ k] ∧ (n : ℤ) ≡ r [ZMOD 4 * a - 1] ∧
      (0 < k → Odd (n : ℤ)) := by
  set q : ℤ := 4 * (a : ℤ) - 1
  have h₂q : IsCoprime (2 : ℤ) q := ⟨2 * a, -1, by ring⟩
  have hcop : IsCoprime ((2 : ℤ) ^ k) q := h₂q.pow_left
  obtain ⟨s, t, hst⟩ := hcop
  set N : ℤ := c * t * q + r * s * 2 ^ k
  have hN₁ : N ≡ c [ZMOD 2 ^ k] := by
    rw [Int.modEq_iff_dvd]
    exact ⟨c * s - r * s, by linear_combination (-c) * hst⟩
  have hN₂ : N ≡ r [ZMOD q] := by
    rw [Int.modEq_iff_dvd]
    exact ⟨r * t - c * t, by linear_combination (-r) * hst⟩
  have hqpos : 0 < q := by
    have : (1 : ℤ) ≤ a := by exact_mod_cast ha
    omega
  have hMne : (2 : ℤ) ^ k * q ≠ 0 := mul_ne_zero (pow_ne_zero k two_ne_zero) hqpos.ne'
  have hnn : 0 ≤ N % (2 ^ k * q) := Int.emod_nonneg N hMne
  refine ⟨(N % (2 ^ k * q)).toNat, ?_, ?_, ?_⟩
  · rw [Int.toNat_of_nonneg hnn]
    exact (Int.emod_emod_of_dvd N (dvd_mul_right _ _)).trans hN₁
  · rw [Int.toNat_of_nonneg hnn]
    exact (Int.emod_emod_of_dvd N (dvd_mul_left _ _)).trans hN₂
  · intro hk
    rw [Int.toNat_of_nonneg hnn]
    have h₂ : N % (2 ^ k * q) ≡ c [ZMOD 2] :=
      Int.ModEq.of_dvd (dvd_pow_self 2 hk.ne')
        ((Int.emod_emod_of_dvd N (dvd_mul_right _ _)).trans hN₁)
    rw [Int.odd_iff] at hc ⊢
    rw [Int.ModEq] at h₂
    omega

/-- For a fixed odd modulus `M`, the interior local mass has positive cubic
order, with constants uniform over reduced residues `a_M` and `u`. -/
theorem localObstrInteriorMass_cubic_order (M : ℕ) (hM : Odd M) :
    ∃ c C L₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < L₀ ∧
      ∀ aM u : ℕ, Nat.Coprime aM M → Nat.Coprime u M → ∀ L : ℝ, L₀ ≤ L →
        c * (Real.log L) ^ 3 ≤ Estimates.localObstrInteriorMass L M aM u ∧
          Estimates.localObstrInteriorMass L M aM u ≤ C * (Real.log L) ^ 3 := by
  obtain ⟨C₀, hC₀, hrem⟩ := Estimates.localObstrInteriorMass_cubic_remainder M hM
  have hMpos : 0 < M := hM.pos
  set A : ℝ := Estimates.singularSeries M / (24 * (Nat.totient M : ℝ) ^ 2)
  have hApos : 0 < A := by
    have := Estimates.singularSeries_pos M
    have ht : (0 : ℝ) < Nat.totient M := by exact_mod_cast Nat.totient_pos.mpr hMpos
    positivity
  refine ⟨A / 2, A + C₀, Real.exp (max 1 (2 * C₀ / A)), by positivity, by positivity,
    Real.exp_pos _, ?_⟩
  intro aM u haM hu L hL
  have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hlog : max 1 (2 * C₀ / A) ≤ Real.log L := (Real.le_log_iff_exp_le hLpos).mpr hL
  have hlog₁ : 1 ≤ Real.log L := le_trans (le_max_left _ _) hlog
  have hlog₂ : 2 * C₀ / A ≤ Real.log L := le_trans (le_max_right _ _) hlog
  have hL₁ : Real.exp 1 ≤ L := le_trans (Real.exp_le_exp.mpr (le_max_left _ _)) hL
  have hb := hrem aM u haM hu L hL₁
  rw [abs_le] at hb
  have hAℓ : 2 * C₀ ≤ A * Real.log L := by
    rw [div_le_iff₀ hApos] at hlog₂
    linarith
  have hsq : 0 ≤ Real.log L ^ 2 := sq_nonneg _
  have h₁ := mul_le_mul_of_nonneg_left hAℓ hsq
  have h₂ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog₁ hsq) hC₀.le
  constructor
  · nlinarith
  · nlinarith

/-- Proposition 4.3 at a fixed odd modulus `M`: for every reduced class
`c (mod M)`, the mass `𝔐_{M,c}(L)` built from `a_M ≡ 4⁻¹` and
`u_c ≡ -c·4⁻¹ (mod M)` has positive cubic order, uniformly in `c`. -/
theorem localObstr_class_mass_cubic_order (M : ℕ) (hM : Odd M) :
    ∃ c₀ C L₀ : ℝ, 0 < c₀ ∧ 0 < C ∧ 0 < L₀ ∧
      ∀ c : ℤ, IsCoprime c (M : ℤ) → ∀ aM u : ℕ,
        4 * (aM : ℤ) ≡ 1 [ZMOD M] → 4 * (u : ℤ) ≡ -c [ZMOD M] → ∀ L : ℝ, L₀ ≤ L →
          c₀ * (Real.log L) ^ 3 ≤ Estimates.localObstrInteriorMass L M aM u ∧
            Estimates.localObstrInteriorMass L M aM u ≤ C * (Real.log L) ^ 3 := by
  obtain ⟨c₀, C, L₀, hc₀, hC, hL₀, h⟩ := localObstrInteriorMass_cubic_order M hM
  refine ⟨c₀, C, L₀, hc₀, hC, hL₀, fun c hc aM u haM hu => h aM u ?_ ?_⟩
  · rw [← Nat.isCoprime_iff_coprime]
    obtain ⟨t, ht⟩ := haM.symm.dvd
    exact ⟨4, -t, by linarith⟩
  · rw [← Nat.isCoprime_iff_coprime]
    obtain ⟨x, y, hxy⟩ := hc
    obtain ⟨t, ht⟩ := hu.symm.dvd
    exact ⟨-4 * x, x * t + y, by linear_combination hxy - x * ht⟩

/-- Proposition 4.3 at an odd prime power `ℓ^k`: the interior local
mass has positive cubic order, uniformly over reduced residues. -/
theorem localObstrInteriorMass_prime_pow_cubic_order {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ₂ : ℓ ≠ 2)
    (k : ℕ) :
    ∃ c C L₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < L₀ ∧
      ∀ aM u : ℕ, Nat.Coprime aM (ℓ ^ k) → Nat.Coprime u (ℓ ^ k) → ∀ L : ℝ, L₀ ≤ L →
        c * (Real.log L) ^ 3 ≤ Estimates.localObstrInteriorMass L (ℓ ^ k) aM u ∧
          Estimates.localObstrInteriorMass L (ℓ ^ k) aM u ≤ C * (Real.log L) ^ 3 :=
  localObstrInteriorMass_cubic_order (ℓ ^ k) (hℓ.odd_of_ne_two hℓ₂).pow

/-! ## Proposition 4.5 in terms of `Λ_int(a)` -/

/-- For `B ⊆ [1, L]`, the sum `∑_{a ∈ B} |Λ_int(a)|/(4a-1)` equals
`Estimates.pairwiseSubfanMass L B`. -/
theorem interiorDivisors_subfan_sum_eq {L : ℝ} {B : Finset ℕ}
    (hB : B ⊆ Finset.Icc 1 ⌊L⌋₊) :
    ∑ a ∈ B, ((interiorDivisors a).card : ℝ) / (4 * (a : ℝ) - 1) =
      Estimates.pairwiseSubfanMass L B := by
  unfold Estimates.pairwiseSubfanMass
  rw [Finset.filter_true_of_mem (fun a ha => Finset.mem_Icc.mp (hB ha))]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [cast_card_interiorDivisors (Finset.mem_Icc.mp (hB ha)).1]
  rfl

/-- No pairwise-coprime subfamily carries a positive proportion of the
interior mass: for every `ε > 0` and large `L`, every such subfamily has
mass at most `ε` times the full interior mass. -/
theorem pairwiseSubfanMass_le_mul_interior :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ B : Finset ℕ,
      Estimates.pairwiseFanModuliCoprime B →
        Estimates.pairwiseSubfanMass L B ≤ ε * Estimates.divisorFanInteriorMass L := by
  intro ε hε
  obtain ⟨C, L₁, hC, hbar⟩ :=
    Estimates.pairwiseSubfanMass_le_log_square
  have hκ : 0 < 1 / (24 * Estimates.zeta2) := by
    have := Estimates.zeta2_pos
    positivity
  have hev₁ : ∀ᶠ L in atTop, (1 / (24 * Estimates.zeta2)) / 2 ≤
      Estimates.divisorFanInteriorMass L / (Real.log L) ^ (3 : ℝ) :=
    Estimates.divisorFanInteriorMass_asymptotic_from_cubic_estimate.eventually_const_le
      (by linarith)
  have hev₂ : ∀ᶠ L in atTop, max 1 (2 * C / (ε * (1 / (24 * Estimates.zeta2)))) ≤
      Real.log L :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (hev₁.and (hev₂.and (eventually_ge_atTop L₁)))
  refine ⟨L₀, fun L hL B hB => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := hL₀ L hL
  set κ : ℝ := 1 / (24 * Estimates.zeta2)
  have hℓ₁ : 1 ≤ Real.log L := le_trans (le_max_left _ _) h₂
  have hℓ₂ : 2 * C / (ε * κ) ≤ Real.log L := le_trans (le_max_right _ _) h₂
  have h3r : Real.log L ^ (3 : ℝ) = Real.log L ^ 3 := by
    exact_mod_cast Real.rpow_natCast (Real.log L) 3
  have h2r : Real.log L ^ (2 : ℝ) = Real.log L ^ 2 := by
    exact_mod_cast Real.rpow_natCast (Real.log L) 2
  have hpos : 0 < Real.log L ^ 3 := by positivity
  rw [h3r, le_div_iff₀ hpos] at h₁
  have hb := hbar L h₃ B hB
  rw [h2r] at hb
  have hεκ : 0 < ε * κ := mul_pos hε hκ
  have hCℓ : 2 * C ≤ ε * κ * Real.log L := by
    rw [div_le_iff₀ hεκ] at hℓ₂
    linarith
  have hsq : 0 ≤ Real.log L ^ 2 := sq_nonneg _
  have k₁ := mul_le_mul_of_nonneg_left hCℓ hsq
  have k₂ := mul_le_mul_of_nonneg_left h₁ hε.le
  nlinarith

/-- The last sentence of Proposition 4.5: a subfamily with pairwise coprime moduli
carries at most an `ε`-proportion of the cubic mass of Proposition 4.2, for every `ε > 0`
and all large `L`. -/
theorem coprime_barrier_relative :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ B : Finset ℕ,
      B ⊆ Finset.Icc 1 ⌊L⌋₊ →
      (∀ a ∈ B, ∀ b ∈ B, a ≠ b → Nat.Coprime (4 * a - 1) (4 * b - 1)) →
        ∑ a ∈ B, ((interiorDivisors a).card : ℝ) / (4 * (a : ℝ) - 1) ≤
          ε * ∑ a ∈ Finset.Icc 1 ⌊L⌋₊, ((interiorDivisors a).card : ℝ) / (4 * (a : ℝ) - 1) := by
  intro ε hε
  obtain ⟨L₀, h⟩ := pairwiseSubfanMass_le_mul_interior ε hε
  refine ⟨L₀, fun L hL B hBL hB => ?_⟩
  rw [interiorDivisors_subfan_sum_eq hBL, interiorDivisors_sum_eq]
  exact h L hL B hB

/-! ## Prime powers in Lemma 4.1 -/

theorem card_divisors_sq_prime_pow {p : ℕ} (hp : p.Prime) (j : ℕ) :
    ((p ^ j) ^ 2).divisors.card = 2 * j + 1 := by
  rw [← pow_mul, ← ArithmeticFunction.sigma_zero_apply,
    ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  ring

theorem choose_add_two_two (j : ℕ) :
    Nat.choose (j + 2) 2 = 2 * j + 1 + Nat.choose j 2 := by
  have h₁ : Nat.choose (j + 2) 2 = Nat.choose (j + 1) 1 + Nat.choose (j + 1) 2 :=
    Nat.choose_succ_succ (j + 1) 1
  have h₂ : Nat.choose (j + 1) 2 = Nat.choose j 1 + Nat.choose j 2 :=
    Nat.choose_succ_succ j 1
  rw [h₁, h₂, Nat.choose_one_right, Nat.choose_one_right]
  ring

/-- `τ₃(p^j) = binom(j+2, 2)`. -/
theorem tripleDivisorAF_prime_pow_eq_choose {p : ℕ} (hp : p.Prime) (j : ℕ) :
    tripleDivisorAF (p ^ j) = Nat.choose (j + 2) 2 := by
  rw [tripleDivisorAF_prime_pow p j hp]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ (j + 2), Nat.choose_one_right]
    ring

/-- The prime-power case of the identity in Lemma 4.1:
`τ((p^j)²) = binom(j+2, 2) - binom(j, 2) = 2j+1`. -/
theorem tau_sq_prime_pow_eq_choose_sub {p : ℕ} (hp : p.Prime) (j : ℕ) :
    ((p ^ j) ^ 2).divisors.card = Nat.choose (j + 2) 2 - Nat.choose j 2 ∧
      Nat.choose (j + 2) 2 - Nat.choose j 2 = 2 * j + 1 := by
  have h := choose_add_two_two j
  refine ⟨?_, by omega⟩
  rw [card_divisors_sq_prime_pow hp]
  omega

end ErdosStraus.DivisorEstimates
