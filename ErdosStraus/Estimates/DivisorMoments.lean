import ErdosStraus.Estimates.Squarefree
import ErdosStraus.Estimates.Mertens

/-! # Divisor moments

Bounds for the moments `∑_{m ≤ Y} τ(m)^K / φ(m)`. From `m/φ(m) ≤ τ(m)` and
`∑_{m ≤ Y} τ(m)^{r+1}/m ≤ (∑_{m ≤ Y} τ(m)^r/m)^2` the moment is at most `H_Y^{2^{K+1}}`, with
`H_Y` the harmonic number, so it is `≪ (log X)^{2^{K+1}}` for `Y = X^ν`. For `K = 2`, expanding
the Euler product of `τ²/φ` and Mertens' product theorem give the sharper bound
`∑_{q ≤ Q} τ(q)²/φ(q) ≪ (log 2Q)^4` used in the proof of Lemma 3.8.
-/

namespace ErdosStraus.Estimates
open Filter Asymptotics
open scoped BigOperators Pointwise

/-! ## Moments of `τ^K/φ` -/

/-- The divisor moment `∑_{1 ≤ m ≤ X^ν} τ(m)^K / φ(m)`; the range is empty when `X^ν < 1`. -/
noncomputable def divisorPhiMoment (X : ℝ) (K : ℕ) (ν : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc (1 : ℕ) ⌊X ^ ν⌋₊,
    ((tau m ^ K : ℕ) : ℝ) / (Nat.totient m : ℝ)

theorem divisorPhiMoment_nonneg (X : ℝ) (K : ℕ) (ν : ℝ) :
    0 ≤ divisorPhiMoment X K ν := by
  classical
  unfold divisorPhiMoment
  apply Finset.sum_nonneg
  intro m _hm
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem tau_mul_le_mul_tau (m n : ℕ) : tau (m * n) ≤ tau m * tau n := by
  unfold tau
  rw [Nat.divisors_mul]
  exact Finset.card_mul_le

theorem tau_pow_div_self_le_divisor_split
    (r m d : ℕ) (hd : d ∈ m.divisors) :
    ((tau m ^ r : ℕ) : ℝ) / (m : ℝ)
      ≤ (((tau d ^ r : ℕ) : ℝ) / (d : ℝ)) *
        (((tau (m / d) ^ r : ℕ) : ℝ) / ((m / d : ℕ) : ℝ)) := by
  let q := m / d
  have hdvd : d ∣ m := Nat.dvd_of_mem_divisors hd
  have hdpos_nat : 0 < d := Nat.pos_of_mem_divisors hd
  have hmpos_nat : 0 < m := lt_of_lt_of_le hdpos_nat (Nat.divisor_le hd)
  have hqpos_nat : 0 < q := by
    unfold q
    exact Nat.div_pos (Nat.divisor_le hd) hdpos_nat
  have hmul_nat : d * q = m := by
    unfold q
    exact Nat.mul_div_cancel' hdvd
  have htau : tau m ≤ tau d * tau q := by
    rw [← hmul_nat]
    exact tau_mul_le_mul_tau d q
  have hpow_nat : tau m ^ r ≤ (tau d * tau q) ^ r :=
    Nat.pow_le_pow_left htau r
  have hpow_real :
      ((tau m ^ r : ℕ) : ℝ) ≤ (((tau d * tau q) ^ r : ℕ) : ℝ) := by
    exact_mod_cast hpow_nat
  have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hd_ne : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hdpos_nat)
  have hq_ne : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos_nat)
  have hmul_real : (m : ℝ) = (d : ℝ) * (q : ℝ) := by
    exact_mod_cast hmul_nat.symm
  have hnum_mul :
      (((tau d * tau q) ^ r : ℕ) : ℝ)
        = ((tau d ^ r : ℕ) : ℝ) * ((tau q ^ r : ℕ) : ℝ) := by
    rw [Nat.mul_pow, Nat.cast_mul]
  calc
    ((tau m ^ r : ℕ) : ℝ) / (m : ℝ)
        ≤ (((tau d * tau q) ^ r : ℕ) : ℝ) / (m : ℝ) :=
          by exact div_le_div_of_nonneg_right hpow_real hm_nonneg
    _ = (((tau d ^ r : ℕ) : ℝ) / (d : ℝ)) *
        (((tau q ^ r : ℕ) : ℝ) / (q : ℝ)) := by
          rw [hnum_mul, hmul_real]
          field_simp [hd_ne, hq_ne]
    _ = (((tau d ^ r : ℕ) : ℝ) / (d : ℝ)) *
        (((tau (m / d) ^ r : ℕ) : ℝ) / ((m / d : ℕ) : ℝ)) := by
          dsimp [q]

/-- `m/φ(m) ≤ τ(m)`, from `m = ∑_{d ∣ m} φ(d)` and `φ(d) ≤ φ(m)`. -/
theorem self_le_totient_mul_tau (m : ℕ) (hm : 0 < m) :
    m ≤ Nat.totient m * tau m := by
  unfold tau
  have hphi_pos : 0 < Nat.totient m := Nat.totient_pos.mpr hm
  calc
    m = ∑ d ∈ m.divisors, Nat.totient d := (Nat.sum_totient m).symm
    _ ≤ ∑ _d ∈ m.divisors, Nat.totient m := by
          apply Finset.sum_le_sum
          intro d hd
          have hdm : d ∣ m := Nat.dvd_of_mem_divisors hd
          exact Nat.le_of_dvd hphi_pos (Nat.totient_dvd_of_dvd hdm)
    _ = Nat.totient m * m.divisors.card := by
          simp [Finset.sum_const, mul_comm]

theorem div_totient_le_tau (m : ℕ) (hm : 0 < m) :
    (m : ℝ) / (Nat.totient m : ℝ) ≤ (tau m : ℝ) := by
  have hphi_pos_nat : 0 < Nat.totient m := Nat.totient_pos.mpr hm
  have hphi_pos : (0 : ℝ) < (Nat.totient m : ℝ) := by exact_mod_cast hphi_pos_nat
  have hmain : (m : ℝ) ≤ (Nat.totient m : ℝ) * (tau m : ℝ) := by
    exact_mod_cast self_le_totient_mul_tau m hm
  exact (div_le_iff₀ hphi_pos).mpr (by simpa [mul_comm] using hmain)

theorem divisorPhiMoment_summand_le_tau_succ_div
    (K m : ℕ) (hm : 1 ≤ m) :
    ((tau m ^ K : ℕ) : ℝ) / (Nat.totient m : ℝ)
      ≤ ((tau m ^ (K + 1) : ℕ) : ℝ) / (m : ℝ) := by
  have hmpos_nat : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos_nat
  have hphi_pos_nat : 0 < Nat.totient m := Nat.totient_pos.mpr hmpos_nat
  have hphi_pos : (0 : ℝ) < (Nat.totient m : ℝ) := by exact_mod_cast hphi_pos_nat
  have htau_nonneg : 0 ≤ ((tau m ^ K : ℕ) : ℝ) := Nat.cast_nonneg _
  have hratio : (m : ℝ) / (Nat.totient m : ℝ) ≤ (tau m : ℝ) :=
    div_totient_le_tau m hmpos_nat
  have hmul :
      ((tau m ^ K : ℕ) : ℝ) * ((m : ℝ) / (Nat.totient m : ℝ))
        ≤ ((tau m ^ K : ℕ) : ℝ) * (tau m : ℝ) :=
    mul_le_mul_of_nonneg_left hratio htau_nonneg
  have hrew :
      ((tau m ^ K : ℕ) : ℝ) * ((m : ℝ) / (Nat.totient m : ℝ))
        = (((tau m ^ K : ℕ) : ℝ) / (Nat.totient m : ℝ)) * (m : ℝ) := by
    ring
  have hpow :
      ((tau m ^ K : ℕ) : ℝ) * (tau m : ℝ)
        = ((tau m ^ (K + 1) : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_pow]
    rw [pow_succ']
    ring
  rw [hrew, hpow] at hmul
  exact (le_div_iff₀ hmpos).mpr hmul

/-- The moment `∑_{1 ≤ m ≤ X^ν} τ(m)^{K+1}/m`. -/
noncomputable def divisorTauSuccOverN (X : ℝ) (K : ℕ) (ν : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc (1 : ℕ) ⌊X ^ ν⌋₊,
    ((tau m ^ (K + 1) : ℕ) : ℝ) / (m : ℝ)

/-- The moment `∑_{1 ≤ m ≤ Y} τ(m)^r/m`. -/
noncomputable def tauPowOverN (Y r : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc (1 : ℕ) Y, ((tau m ^ r : ℕ) : ℝ) / (m : ℝ)

theorem divisorTauSuccOverN_eq_tauPowOverN (X : ℝ) (K : ℕ) (ν : ℝ) :
    divisorTauSuccOverN X K ν = tauPowOverN ⌊X ^ ν⌋₊ (K + 1) := by
  rfl

theorem divisorPhiMoment_le_tauSuccOverN (X : ℝ) (K : ℕ) (ν : ℝ) :
    divisorPhiMoment X K ν ≤ divisorTauSuccOverN X K ν := by
  classical
  unfold divisorPhiMoment divisorTauSuccOverN
  apply Finset.sum_le_sum
  intro m hm
  exact divisorPhiMoment_summand_le_tau_succ_div K m (Finset.mem_Icc.mp hm).1

theorem abs_divisorPhiMoment_le_tauSuccOverN (X : ℝ) (K : ℕ) (ν : ℝ) :
    |divisorPhiMoment X K ν| ≤ divisorTauSuccOverN X K ν := by
  rw [abs_of_nonneg (divisorPhiMoment_nonneg X K ν)]
  exact divisorPhiMoment_le_tauSuccOverN X K ν

theorem tauPowOverN_nonneg (Y r : ℕ) :
    0 ≤ tauPowOverN Y r := by
  classical
  unfold tauPowOverN
  apply Finset.sum_nonneg
  intro m _hm
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg m)

theorem harmonic_nonneg_real (Y : ℕ) :
    0 ≤ ((harmonic Y : ℚ) : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_nonneg
  intro n _hn
  exact inv_nonneg.mpr (Nat.cast_nonneg n)

/-- `∑_{m ≤ Y} τ(m)^{r+1}/m ≤ (∑_{m ≤ Y} τ(m)^r/m)^2`: write `τ(m)^{r+1}/m` as
`∑_{d ∣ m} τ(m)^r/m` and use `τ(m)^r/m ≤ (τ(d)^r/d)(τ(m/d)^r/(m/d))`. -/
theorem tauPowOverN_succ_le_square (Y r : ℕ) :
    tauPowOverN Y (r + 1) ≤ (tauPowOverN Y r) ^ 2 := by
  classical
  let I : Finset ℕ := Finset.Icc (1 : ℕ) Y
  let s : Finset ((m : ℕ) × ℕ) := I.sigma (fun m => m.divisors)
  let F : ((m : ℕ) × ℕ) → ℕ × ℕ := fun x => (x.2, x.1 / x.2)
  let a : ℕ → ℝ := fun n => ((tau n ^ r : ℕ) : ℝ) / (n : ℝ)
  have hleft_inner :
      tauPowOverN Y (r + 1)
        = ∑ m ∈ I, ∑ _d ∈ m.divisors, a m := by
    unfold tauPowOverN I a
    apply Finset.sum_congr rfl
    intro m hm
    have hmpos_nat : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1
    have hmpos : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hmpos_nat)
    unfold tau
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [Nat.cast_pow, Nat.cast_pow, pow_succ']
    field_simp [hmpos]
  have hinner_sigma :
      (∑ m ∈ I, ∑ _d ∈ m.divisors, a m)
        = ∑ x ∈ s, a x.1 := by
    unfold s
    exact Finset.sum_sigma' I (fun m => m.divisors) (fun m _d => a m)
  have hleft_eq_sigma :
      tauPowOverN Y (r + 1) = ∑ x ∈ s, a x.1 := by
    rw [hleft_inner, hinner_sigma]
  let split : ℕ × ℕ → ℝ := fun p => a p.1 * a p.2
  have hsplit_bound :
      (∑ x ∈ s, a x.1) ≤ ∑ x ∈ s, split (F x) := by
    apply Finset.sum_le_sum
    intro x hx
    rcases x with ⟨m, d⟩
    have hx' := hx
    rw [Finset.mem_sigma] at hx'
    rcases hx' with ⟨_hm, hd⟩
    exact tau_pow_div_self_le_divisor_split r m d hd
  have hF_mem : ∀ x ∈ s, F x ∈ I.product I := by
    intro x hx
    rcases x with ⟨m, d⟩
    have hx' := hx
    rw [Finset.mem_sigma] at hx'
    rcases hx' with ⟨hm, hd⟩
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdle : d ≤ Y := le_trans (Nat.divisor_le hd) (Finset.mem_Icc.mp hm).2
    have hquot_pos : 0 < m / d := Nat.div_pos (Nat.divisor_le hd) hdpos
    have hquot_le_m : m / d ≤ m := Nat.div_le_self m d
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hdpos, hdle⟩,
        Finset.mem_Icc.mpr ⟨hquot_pos, le_trans hquot_le_m (Finset.mem_Icc.mp hm).2⟩⟩
  have hF_inj : ∀ x ∈ s, ∀ y ∈ s, F x = F y → x = y := by
    intro x hx y hy hxy
    rcases x with ⟨m, d⟩
    rcases y with ⟨n, e⟩
    have hx' := hx
    have hy' := hy
    rw [Finset.mem_sigma] at hx'
    rw [Finset.mem_sigma] at hy'
    rcases hx' with ⟨_hm, hd⟩
    rcases hy' with ⟨_hn, he⟩
    have hdvd : d ∣ m := Nat.dvd_of_mem_divisors hd
    have hevd : e ∣ n := Nat.dvd_of_mem_divisors he
    have hde : d = e := congrArg Prod.fst hxy
    have hquot : m / d = n / e := congrArg Prod.snd hxy
    have hm_eq : m = d * (m / d) := (Nat.mul_div_cancel' hdvd).symm
    have hn_eq : n = e * (n / e) := (Nat.mul_div_cancel' hevd).symm
    subst e
    have hmn : m = n := by
      rw [hm_eq, hn_eq, hquot]
    subst n
    rfl
  have hsum_image :
      (∑ x ∈ s, split (F x)) = ∑ p ∈ s.image F, split p := by
    rw [Finset.sum_image]
    intro x hx y hy hxy
    exact hF_inj x hx y hy hxy
  have himage_subset : s.image F ⊆ I.product I := by
    intro p hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨x, hx, rfl⟩
    exact hF_mem x hx
  have hnonneg_extra : ∀ p ∈ I.product I, p ∉ s.image F → 0 ≤ split p := by
    intro p _hp _
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have himage_le_product :
      (∑ p ∈ s.image F, split p) ≤ ∑ p ∈ I.product I, split p :=
    Finset.sum_le_sum_of_subset_of_nonneg himage_subset hnonneg_extra
  have hproduct_eq :
      (∑ p ∈ I.product I, split p) = (tauPowOverN Y r) ^ 2 := by
    unfold split tauPowOverN I a
    change
      (∑ p ∈ (Finset.Icc (1 : ℕ) Y) ×ˢ (Finset.Icc (1 : ℕ) Y),
        (((tau p.1 ^ r : ℕ) : ℝ) / (p.1 : ℝ)) *
          (((tau p.2 ^ r : ℕ) : ℝ) / (p.2 : ℝ))) =
        (∑ m ∈ Finset.Icc (1 : ℕ) Y, ((tau m ^ r : ℕ) : ℝ) / (m : ℝ)) ^ 2
    rw [Finset.sum_product]
    rw [sq]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
  rw [hleft_eq_sigma]
  exact le_trans hsplit_bound
    (le_trans (by rw [hsum_image]; exact himage_le_product) hproduct_eq.le)

/-- `∑_{m ≤ Y} τ(m)/m ≤ H_Y²`, by writing each `m` as `d · (m/d)` with `d, m/d ≤ Y`. -/
theorem tau_div_self_sum_le_harmonic_sq (Y : ℕ) :
    (∑ m ∈ Finset.Icc (1 : ℕ) Y, ((tau m : ℕ) : ℝ) / (m : ℝ))
      ≤ ((harmonic Y : ℚ) : ℝ) ^ 2 := by
  classical
  let s : Finset ((m : ℕ) × ℕ) := (Finset.Icc (1 : ℕ) Y).sigma (fun m => m.divisors)
  let F : ((m : ℕ) × ℕ) → ℕ × ℕ := fun x => (x.2, x.1 / x.2)
  have hleft_inner :
      (∑ m ∈ Finset.Icc (1 : ℕ) Y, ((tau m : ℕ) : ℝ) / (m : ℝ))
        = ∑ m ∈ Finset.Icc (1 : ℕ) Y, ∑ _d ∈ m.divisors, (1 : ℝ) / (m : ℝ) := by
    apply Finset.sum_congr rfl
    intro m hm
    have hmpos_nat : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos_nat
    unfold tau
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp [ne_of_gt hmpos]
  have hinner_sigma :
      (∑ m ∈ Finset.Icc (1 : ℕ) Y, ∑ _d ∈ m.divisors, (1 : ℝ) / (m : ℝ))
        = ∑ x ∈ s, (1 : ℝ) / (x.1 : ℝ) := by
    unfold s
    exact Finset.sum_sigma' (Finset.Icc (1 : ℕ) Y) (fun m => m.divisors)
      (fun m _d => (1 : ℝ) / (m : ℝ))
  have hleft_eq_sigma :
      (∑ m ∈ Finset.Icc (1 : ℕ) Y, ((tau m : ℕ) : ℝ) / (m : ℝ))
        = ∑ x ∈ s, (1 : ℝ) / (x.1 : ℝ) := by
    rw [hleft_inner, hinner_sigma]
  have hF_mem : ∀ x ∈ s, F x ∈ (Finset.Icc (1 : ℕ) Y).product (Finset.Icc (1 : ℕ) Y) := by
    intro x hx
    rcases x with ⟨m, d⟩
    have hx' := hx
    rw [Finset.mem_sigma] at hx'
    rcases hx' with ⟨hm, hd⟩
    change (d, m / d) ∈ (Finset.Icc (1 : ℕ) Y) ×ˢ (Finset.Icc (1 : ℕ) Y)
    rw [Finset.mem_product]
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdle : d ≤ Y := le_trans (Nat.divisor_le hd) (Finset.mem_Icc.mp hm).2
    have hquot_pos : 0 < m / d := Nat.div_pos (Nat.divisor_le hd) hdpos
    have hquot_le_m : m / d ≤ m := Nat.div_le_self m d
    exact ⟨Finset.mem_Icc.mpr ⟨hdpos, hdle⟩,
      Finset.mem_Icc.mpr ⟨hquot_pos, le_trans hquot_le_m (Finset.mem_Icc.mp hm).2⟩⟩
  have hF_inj : ∀ x ∈ s, ∀ y ∈ s, F x = F y → x = y := by
    intro x hx y hy hxy
    rcases x with ⟨m, d⟩
    rcases y with ⟨n, e⟩
    have hx' := hx
    have hy' := hy
    rw [Finset.mem_sigma] at hx'
    rw [Finset.mem_sigma] at hy'
    rcases hx' with ⟨_hm, hd⟩
    rcases hy' with ⟨_hn, he⟩
    have hdvd : d ∣ m := Nat.dvd_of_mem_divisors hd
    have hevd : e ∣ n := Nat.dvd_of_mem_divisors he
    have hde : d = e := congrArg Prod.fst hxy
    have hquot : m / d = n / e := congrArg Prod.snd hxy
    have hm_eq : m = d * (m / d) := (Nat.mul_div_cancel' hdvd).symm
    have hn_eq : n = e * (n / e) := (Nat.mul_div_cancel' hevd).symm
    subst e
    have hmn : m = n := by
      rw [hm_eq, hn_eq, hquot]
    subst n
    rfl
  have hsum_image :
      (∑ x ∈ s, (1 : ℝ) / (x.1 : ℝ))
        = ∑ p ∈ s.image F, (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro x hx
      rcases x with ⟨m, d⟩
      have hx' := hx
      rw [Finset.mem_sigma] at hx'
      rcases hx' with ⟨_hm, hd⟩
      have hdvd : d ∣ m := Nat.dvd_of_mem_divisors hd
      have hmul : d * (m / d) = m := Nat.mul_div_cancel' hdvd
      simp only [F]
      rw [hmul]
    · intro x hx y hy hxy
      exact hF_inj x hx y hy hxy
  have himage_subset : s.image F ⊆ (Finset.Icc (1 : ℕ) Y).product (Finset.Icc (1 : ℕ) Y) := by
    intro p hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨x, hx, rfl⟩
    exact hF_mem x hx
  have hnonneg_extra : ∀ p ∈ (Finset.Icc (1 : ℕ) Y).product (Finset.Icc (1 : ℕ) Y),
      p ∉ s.image F → 0 ≤ (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) := by
    intro p _hp _
    exact div_nonneg zero_le_one (Nat.cast_nonneg _)
  have himage_le_product :
      (∑ p ∈ s.image F, (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ))
        ≤ ∑ p ∈ (Finset.Icc (1 : ℕ) Y).product (Finset.Icc (1 : ℕ) Y),
            (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg himage_subset hnonneg_extra
  have hprod_eq :
      (∑ p ∈ (Finset.Icc (1 : ℕ) Y).product (Finset.Icc (1 : ℕ) Y),
            (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ))
        = ((harmonic Y : ℚ) : ℝ) ^ 2 := by
    change (∑ p ∈ (Finset.Icc (1 : ℕ) Y) ×ˢ (Finset.Icc (1 : ℕ) Y),
            (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ))
        = ((harmonic Y : ℚ) : ℝ) ^ 2
    rw [Finset.sum_product]
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    simp_rw [one_div]
    rw [sq]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hdpos_nat : 0 < d := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hd).1
    have hrpos_nat : 0 < r := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hr).1
    have hdpos : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hdpos_nat)
    have hrpos : (r : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hrpos_nat)
    norm_num [Nat.cast_mul]
    field_simp [hdpos, hrpos]
  rw [hleft_eq_sigma, hsum_image]
  exact le_trans himage_le_product hprod_eq.le

/-- `∑_{m ≤ Y} τ(m)^{K+1}/m ≤ H_Y^{2^{K+1}}`, by induction on `K`. -/
theorem tauPowOverN_succ_le_harmonic_two_pow (Y K : ℕ) :
    tauPowOverN Y (K + 1)
      ≤ ((harmonic Y : ℚ) : ℝ) ^ (2 ^ (K + 1)) := by
  induction K with
  | zero =>
      simpa [tauPowOverN] using tau_div_self_sum_le_harmonic_sq Y
  | succ K ih =>
      have hrec :
          tauPowOverN Y (Nat.succ K + 1) ≤ (tauPowOverN Y (K + 1)) ^ 2 := by
        simpa [Nat.succ_eq_add_one, add_assoc] using
          tauPowOverN_succ_le_square Y (K + 1)
      have hsq :
          (tauPowOverN Y (K + 1)) ^ 2
            ≤ (((harmonic Y : ℚ) : ℝ) ^ (2 ^ (K + 1))) ^ 2 :=
        pow_le_pow_left₀ (tauPowOverN_nonneg Y (K + 1)) ih 2
      have hexp :
          2 ^ (Nat.succ K + 1) = 2 ^ (K + 1) * 2 := by
        rw [Nat.succ_eq_add_one]
        have hsucc : K + 1 + 1 = Nat.succ (K + 1) := by omega
        rw [hsucc, pow_succ]
      calc
        tauPowOverN Y (Nat.succ K + 1)
            ≤ (tauPowOverN Y (K + 1)) ^ 2 := hrec
        _ ≤ (((harmonic Y : ℚ) : ℝ) ^ (2 ^ (K + 1))) ^ 2 := hsq
        _ = ((harmonic Y : ℚ) : ℝ) ^ (2 ^ (Nat.succ K + 1)) := by
              rw [← pow_mul, hexp]

/-- `∑_{m ≤ X^ν} τ(m)^K/φ(m) ≤ H_Y^{2^{K+1}}` with `Y = ⌊X^ν⌋`. -/
theorem abs_divisorPhiMoment_le_harmonic_two_pow (X : ℝ) (K : ℕ) (ν : ℝ) :
    |divisorPhiMoment X K ν|
      ≤ ((harmonic ⌊X ^ ν⌋₊ : ℚ) : ℝ) ^ (2 ^ (K + 1)) := by
  calc
    |divisorPhiMoment X K ν|
        ≤ divisorTauSuccOverN X K ν := abs_divisorPhiMoment_le_tauSuccOverN X K ν
    _ = tauPowOverN ⌊X ^ ν⌋₊ (K + 1) := divisorTauSuccOverN_eq_tauPowOverN X K ν
    _ ≤ ((harmonic ⌊X ^ ν⌋₊ : ℚ) : ℝ) ^ (2 ^ (K + 1)) :=
          tauPowOverN_succ_le_harmonic_two_pow ⌊X ^ ν⌋₊ K

theorem divisorTauSuccOverN_zero_le_harmonic_sq (X ν : ℝ) :
    divisorTauSuccOverN X 0 ν ≤ ((harmonic ⌊X ^ ν⌋₊ : ℚ) : ℝ) ^ 2 := by
  simpa [divisorTauSuccOverN] using tau_div_self_sum_le_harmonic_sq ⌊X ^ ν⌋₊

theorem abs_divisorPhiMoment_zero_le_harmonic_sq (X ν : ℝ) :
    |divisorPhiMoment X 0 ν| ≤ ((harmonic ⌊X ^ ν⌋₊ : ℚ) : ℝ) ^ 2 :=
  le_trans (abs_divisorPhiMoment_le_tauSuccOverN X 0 ν)
    (divisorTauSuccOverN_zero_le_harmonic_sq X ν)

/-- `∑_{m ≤ X^ν} τ(m)^K/φ(m) ≪ (log X)^{O_K(1)}`; the proof gives the exponent `2^{K+1}`. -/
theorem divisor_phi_moment_general (K : ℕ) (ν : ℝ) (hν : 0 < ν) :
    ∃ C E X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      |divisorPhiMoment X K ν| ≤ C * (Real.log X) ^ E := by
  let N : ℕ := 2 ^ (K + 1)
  refine ⟨(ν + 1) ^ N, (N : ℝ), Real.exp 1, ?_, ?_⟩
  · have hν1 : 0 < ν + 1 := by linarith
    exact pow_pos hν1 N
  intro X hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hlogX_ge_one : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hX
  have hlogX_nonneg : 0 ≤ Real.log X := le_trans zero_le_one hlogX_ge_one
  have hcut_pos : 0 < X ^ ν := Real.rpow_pos_of_pos hXpos ν
  have hlog_cut_eq : Real.log (X ^ ν) = ν * Real.log X := by
    rw [Real.log_rpow hXpos]
  have hcut_ge_one : 1 ≤ X ^ ν := by
    apply (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 1) hcut_pos).mp
    rw [hlog_cut_eq]
    simpa using mul_nonneg hν.le hlogX_nonneg
  have hharm : ((harmonic ⌊X ^ ν⌋₊ : ℚ) : ℝ) ≤ 1 + Real.log (X ^ ν) :=
    harmonic_floor_le_one_add_log (X ^ ν) hcut_ge_one
  have hlinear : 1 + Real.log (X ^ ν) ≤ (ν + 1) * Real.log X := by
    rw [hlog_cut_eq]
    nlinarith [hlogX_ge_one, hν.le]
  have hharm_target : ((harmonic ⌊X ^ ν⌋₊ : ℚ) : ℝ) ≤ (ν + 1) * Real.log X :=
    le_trans hharm hlinear
  have hharm_nonneg : 0 ≤ ((harmonic ⌊X ^ ν⌋₊ : ℚ) : ℝ) :=
    harmonic_nonneg_real ⌊X ^ ν⌋₊
  calc
    |divisorPhiMoment X K ν|
        ≤ ((harmonic ⌊X ^ ν⌋₊ : ℚ) : ℝ) ^ N := by
          simpa [N] using abs_divisorPhiMoment_le_harmonic_two_pow X K ν
    _ ≤ ((ν + 1) * Real.log X) ^ N :=
          pow_le_pow_left₀ hharm_nonneg hharm_target N
    _ = (ν + 1) ^ N * (Real.log X) ^ N := by
          rw [mul_pow]
    _ = (ν + 1) ^ N * (Real.log X) ^ (N : ℝ) := by
          rw [Real.rpow_natCast]

end ErdosStraus.Estimates

/-! ## The Euler product for `τ(q)²/φ(q)`

For a prime `p` and `x = 1/p`,
`1 + ∑_{j ≥ 1} (j+1)²/φ(p^j) = (1 + 3x² - 3x³ + x⁴)/(1 - x)⁴`.
Expanding the product of these local factors over the primes `p ≤ Q` dominates
`∑_{q ≤ Q} τ(q)²/φ(q)`. The product of the numerators is at most `e^8`, and Mertens' product
theorem `∏_{p ≤ N} (1 - 1/p)^{-1} ≪ log N` (Lemma 3.1) bounds the denominators.
-/

namespace ErdosStraus.DivisorEstimates

open scoped BigOperators
open ErdosStraus.PrimeEstimates.Mertens

/-- `∑_{m ≥ 0} (m+1)^2 x^m = (1+x)/(1-x)^3` for `|x| < 1`. -/
theorem hasSum_succ_sq_mul_geometric {x : ℝ} (hx : |x| < 1) :
    HasSum (fun m : ℕ => ((m : ℝ) + 1) ^ 2 * x ^ m) ((1 + x) / (1 - x) ^ 3) := by
  have hn : ‖x‖ < 1 := by rwa [Real.norm_eq_abs]
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one 2 hn
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one 1 hn
  have hx1 : 1 - x ≠ 0 := by linarith [(abs_lt.mp hx).2]
  convert! (h2.mul_left 2).sub h1 using 1
  · funext m
    rw [Nat.cast_choose_two, Nat.choose_one_right]
    push_cast
    ring
  · field_simp
    ring

/-- The local series of `τ^2/φ` at a prime, written in `x = 1/p`:
`∑_{j ≥ 0} (j+2)^2 x^{j+1}/(1-x) = (1 + 3x^2 - 3x^3 + x^4)/(1-x)^4 - 1`. -/
theorem hasSum_square_divisor_local_series {x : ℝ} (hx : |x| < 1) :
    HasSum (fun j : ℕ => ((j : ℝ) + 2) ^ 2 * x ^ (j + 1) / (1 - x))
      ((1 + 3 * x ^ 2 - 3 * x ^ 3 + x ^ 4) / (1 - x) ^ 4 - 1) := by
  have hx1 : 1 - x ≠ 0 := by linarith [(abs_lt.mp hx).2]
  have hshift := (hasSum_nat_add_iff' 1).mpr (hasSum_succ_sq_mul_geometric hx)
  convert! hshift.div_const (1 - x) using 1
  · funext j
    push_cast
    ring
  · simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, one_pow, pow_zero, mul_one]
    field_simp
    ring

/-- The number of divisors of a prime power: `τ(p^k) = k + 1`. -/
theorem divisor_card_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (p ^ k).divisors.card = k + 1 := by
  rw [← ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply_prime_pow hp]

/-- The prime-power terms of `τ^2/φ`:
`τ(p^{j+1})^2/φ(p^{j+1}) = (j+2)^2 x^{j+1}/(1-x)` with `x = 1/p`. -/
theorem square_divisor_card_div_totient_prime_pow {p : ℕ} (hp : p.Prime) (j : ℕ) :
    ((p ^ (j + 1)).divisors.card : ℝ) ^ 2 / Nat.totient (p ^ (j + 1)) =
      ((j : ℝ) + 2) ^ 2 * (p : ℝ)⁻¹ ^ (j + 1) / (1 - (p : ℝ)⁻¹) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hpm : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [divisor_card_prime_pow hp, Nat.totient_prime_pow_succ hp,
    Nat.cast_mul, Nat.cast_sub hp.one_le]
  push_cast
  rw [inv_pow]
  field_simp
  ring

/-- The local Euler factor of `τ^2/φ` at a prime `p`:
`∑_{j ≥ 1} (j+1)^2/φ(p^j) = (1 + 3p^{-2} - 3p^{-3} + p^{-4})/(1 - p^{-1})^4 - 1`. -/
theorem hasSum_succ_sq_div_totient_prime_pow {p : ℕ} (hp : p.Prime) :
    HasSum (fun j : ℕ => ((j : ℝ) + 2) ^ 2 / Nat.totient (p ^ (j + 1)))
      ((1 + 3 * (p : ℝ)⁻¹ ^ 2 - 3 * (p : ℝ)⁻¹ ^ 3 + (p : ℝ)⁻¹ ^ 4) /
        (1 - (p : ℝ)⁻¹) ^ 4 - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hx : |(p : ℝ)⁻¹| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ hp1
  convert hasSum_square_divisor_local_series hx using 1
  funext j
  rw [← square_divisor_card_div_totient_prime_pow hp j, divisor_card_prime_pow hp]
  push_cast
  ring

/-- The local Euler factor of `τ^2/φ`, in terms of the divisor function. -/
theorem hasSum_square_divisor_card_div_totient_prime_pow {p : ℕ} (hp : p.Prime) :
    HasSum (fun j : ℕ => ((p ^ (j + 1)).divisors.card : ℝ) ^ 2 / Nat.totient (p ^ (j + 1)))
      ((1 + 3 * (p : ℝ)⁻¹ ^ 2 - 3 * (p : ℝ)⁻¹ ^ 3 + (p : ℝ)⁻¹ ^ 4) /
        (1 - (p : ℝ)⁻¹) ^ 4 - 1) := by
  convert hasSum_succ_sq_div_totient_prime_pow hp using 1
  funext j
  rw [divisor_card_prime_pow hp]
  push_cast
  ring

/-- The full local factor: `1 + ∑_{j ≥ 1} τ(p^j)^2/φ(p^j) =
(1 + 3p^{-2} - 3p^{-3} + p^{-4})/(1 - p^{-1})^4`. -/
theorem one_add_tsum_square_divisor_card_div_totient_prime_pow {p : ℕ} (hp : p.Prime) :
    1 + ∑' j : ℕ, ((p ^ (j + 1)).divisors.card : ℝ) ^ 2 / Nat.totient (p ^ (j + 1)) =
      (1 + 3 * (p : ℝ)⁻¹ ^ 2 - 3 * (p : ℝ)⁻¹ ^ 3 + (p : ℝ)⁻¹ ^ 4) /
        (1 - (p : ℝ)⁻¹) ^ 4 := by
  rw [(hasSum_square_divisor_card_div_totient_prime_pow hp).tsum_eq]
  ring

/-- Expansion of a finite Euler product: for a nonnegative multiplicative
`f`, `∑_{q ≤ Q} f(q) ≤ ∏_{p ≤ Q} ∑_{0 ≤ j ≤ Q} f(p^j)`.  Each `q ≤ Q` is
recorded by its exponent vector over the primes `p ≤ Q`. -/
theorem sum_Icc_le_prod_primesUpTo_sum_range_prime_pow {f : ℕ → ℝ} (hf1 : f 1 = 1)
    (hmul : ∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) (hnonneg : ∀ n, 0 ≤ f n)
    (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, f q) ≤
      ∏ p ∈ primesUpTo Q, ∑ j ∈ Finset.range (Q + 1), f (p ^ j) := by
  classical
  rw [Finset.prod_sum]
  set P := primesUpTo Q with hP
  let vec : ℕ → ∀ p ∈ P, ℕ := fun q p _ => q.factorization p
  let W : (∀ p ∈ P, ℕ) → ℝ := fun v => ∏ x ∈ P.attach, f (x.1 ^ v x.1 x.2)
  have hsupp : ∀ q ∈ Finset.Icc 1 Q, q.factorization.support ⊆ P := by
    intro q hq p hp
    rw [Nat.support_factorization] at hp
    have hq' := Finset.mem_Icc.mp hq
    exact mem_primesUpTo.mpr ⟨Nat.prime_of_mem_primeFactors hp,
      (Nat.le_of_dvd hq'.1 (Nat.dvd_of_mem_primeFactors hp)).trans hq'.2⟩
  have hW : ∀ q ∈ Finset.Icc 1 Q, f q = W (vec q) := by
    intro q hq
    have hq0 : q ≠ 0 := by have := (Finset.mem_Icc.mp hq).1; omega
    rw [Nat.multiplicative_factorization f hmul hf1 hq0,
      Finsupp.prod_of_support_subset _ (hsupp q hq) _ (fun p _ => by rw [pow_zero, hf1])]
    exact (Finset.prod_attach P (fun p => f (p ^ q.factorization p))).symm
  have hinj : ∀ a ∈ Finset.Icc 1 Q, ∀ b ∈ Finset.Icc 1 Q, vec a = vec b → a = b := by
    intro a ha b hb hab
    have ha' := Finset.mem_Icc.mp ha
    have hb' := Finset.mem_Icc.mp hb
    refine Nat.eq_of_factorization_eq (by omega) (by omega) ?_
    intro p
    by_cases hpP : p ∈ P
    · exact congrFun (congrFun hab p) hpP
    · by_cases hp : p.Prime
      · have hpQ : Q < p := by
          by_contra h
          exact hpP (mem_primesUpTo.mpr ⟨hp, by omega⟩)
        have hna : ¬ p ∣ a := fun h => by have := Nat.le_of_dvd ha'.1 h; omega
        have hnb : ¬ p ∣ b := fun h => by have := Nat.le_of_dvd hb'.1 h; omega
        rw [Nat.factorization_eq_zero_of_not_dvd hna, Nat.factorization_eq_zero_of_not_dvd hnb]
      · rw [Nat.factorization_eq_zero_of_not_prime a hp,
          Nat.factorization_eq_zero_of_not_prime b hp]
  have hmem : ∀ q ∈ Finset.Icc 1 Q, vec q ∈ P.pi fun _ => Finset.range (Q + 1) := by
    intro q hq
    have hq' := Finset.mem_Icc.mp hq
    rw [Finset.mem_pi]
    intro p hp
    rw [Finset.mem_range]
    have hpp := (mem_primesUpTo.mp hp).1
    have hlt := Nat.lt_pow_self (n := q.factorization p) hpp.one_lt
    have hle := Nat.le_of_dvd hq'.1 (Nat.ordProj_dvd q p)
    show q.factorization p < Q + 1
    omega
  calc
    (∑ q ∈ Finset.Icc 1 Q, f q) = ∑ q ∈ Finset.Icc 1 Q, W (vec q) :=
      Finset.sum_congr rfl hW
    _ = ∑ v ∈ (Finset.Icc 1 Q).image vec, W v := (Finset.sum_image hinj).symm
    _ ≤ ∑ v ∈ P.pi fun _ => Finset.range (Q + 1), W v := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro v hv
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
        exact hmem q hq
      · intro v _ _
        exact Finset.prod_nonneg fun x _ => hnonneg _

/-- `τ^2/φ` is multiplicative. -/
theorem square_divisor_card_div_totient_mul {m n : ℕ} (hmn : m.Coprime n) :
    ((m * n).divisors.card : ℝ) ^ 2 / Nat.totient (m * n) =
      ((m.divisors.card : ℝ) ^ 2 / Nat.totient m) *
        ((n.divisors.card : ℝ) ^ 2 / Nat.totient n) := by
  rw [Nat.Coprime.card_divisors_mul hmn, Nat.totient_mul hmn]
  push_cast
  rw [mul_pow, div_mul_div_comm]

/-- Expansion of the Euler product of the local series of `τ^2/φ`:
`∑_{q ≤ Q} τ(q)^2/φ(q) ≤ ∏_{p ≤ Q} (1 + ∑_{j ≥ 1} τ(p^j)^2/φ(p^j))`. -/
theorem square_divisor_card_totient_sum_le_prod_local_series (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (q.divisors.card : ℝ) ^ 2 / Nat.totient q) ≤
      ∏ p ∈ primesUpTo Q,
        (1 + ∑' j : ℕ, ((p ^ (j + 1)).divisors.card : ℝ) ^ 2 / Nat.totient (p ^ (j + 1))) := by
  refine (sum_Icc_le_prod_primesUpTo_sum_range_prime_pow
    (f := fun n => (n.divisors.card : ℝ) ^ 2 / Nat.totient n) (by simp)
    (fun m n hmn => square_divisor_card_div_totient_mul hmn)
    (fun n => by positivity) Q).trans ?_
  apply Finset.prod_le_prod
  · intro p _
    exact Finset.sum_nonneg fun j _ => by positivity
  · intro p hp
    have hpp := (mem_primesUpTo.mp hp).1
    rw [Finset.sum_range_succ']
    simp only [pow_zero, Nat.divisors_one, Finset.card_singleton, Nat.cast_one, one_pow,
      Nat.totient_one, div_one]
    rw [add_comm]
    exact add_le_add_right (sum_le_hasSum _ (fun j _ => by positivity)
      (hasSum_square_divisor_card_div_totient_prime_pow hpp).summable.hasSum) 1

/-- The Euler-product inequality for `τ^2/φ`, with the local factors in closed form:
`∑_{q ≤ Q} τ(q)^2/φ(q) ≤ ∏_{p ≤ Q} (1 + 3p^{-2} - 3p^{-3} + p^{-4})/(1 - p^{-1})^4`. -/
theorem square_divisor_card_totient_sum_le_euler_product (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (q.divisors.card : ℝ) ^ 2 / Nat.totient q) ≤
      ∏ p ∈ primesUpTo Q,
        (1 + 3 * (p : ℝ)⁻¹ ^ 2 - 3 * (p : ℝ)⁻¹ ^ 3 + (p : ℝ)⁻¹ ^ 4) /
          (1 - (p : ℝ)⁻¹) ^ 4 := by
  refine (square_divisor_card_totient_sum_le_prod_local_series Q).trans (le_of_eq ?_)
  apply Finset.prod_congr rfl
  intro p hp
  exact one_add_tsum_square_divisor_card_div_totient_prime_pow (mem_primesUpTo.mp hp).1

/-- The numerator of the local factor lies in `[0, exp(4/p^2)]`. -/
theorem square_divisor_euler_numerator_bounds {p : ℕ} (hp : p.Prime) :
    0 ≤ 1 + 3 * (p : ℝ)⁻¹ ^ 2 - 3 * (p : ℝ)⁻¹ ^ 3 + (p : ℝ)⁻¹ ^ 4 ∧
      1 + 3 * (p : ℝ)⁻¹ ^ 2 - 3 * (p : ℝ)⁻¹ ^ 3 + (p : ℝ)⁻¹ ^ 4 ≤
        Real.exp (4 * (1 / (p : ℝ) ^ 2)) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hx0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hx1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1
  have hsq : 1 / (p : ℝ) ^ 2 = (p : ℝ)⁻¹ ^ 2 := by rw [inv_pow, one_div]
  rw [hsq]
  have h42 : (p : ℝ)⁻¹ ^ 4 ≤ (p : ℝ)⁻¹ ^ 2 := pow_le_pow_of_le_one hx0 hx1 (by norm_num)
  have h3 : 0 ≤ (p : ℝ)⁻¹ ^ 3 := by positivity
  have h23 : (p : ℝ)⁻¹ ^ 3 ≤ (p : ℝ)⁻¹ ^ 2 := pow_le_pow_of_le_one hx0 hx1 (by norm_num)
  have hexp := Real.add_one_le_exp (4 * (p : ℝ)⁻¹ ^ 2)
  constructor
  · nlinarith [pow_nonneg hx0 4]
  · nlinarith

/-- The squares of the prime reciprocals: `∑_{p ≤ N} 1/p^2 ≤ 2`. -/
theorem prime_reciprocal_square_sum_le_two (N : ℕ) :
    (∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 2 := by
  refine le_trans ?_ (ErdosStraus.PrimeEstimates.sum_reciprocal_sq_le_two N)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp', hpN⟩ := mem_primesUpTo.mp hp
    exact Finset.mem_Icc.mpr ⟨hp'.pos, hpN⟩
  · intro p _ _
    positivity

/-- `∏_{p ≤ Q} (1 + 3p^{-2} - 3p^{-3} + p^{-4}) ≤ e^8`. -/
theorem prod_square_divisor_euler_numerator_le_exp (Q : ℕ) :
    (∏ p ∈ primesUpTo Q, (1 + 3 * (p : ℝ)⁻¹ ^ 2 - 3 * (p : ℝ)⁻¹ ^ 3 + (p : ℝ)⁻¹ ^ 4)) ≤
      Real.exp 8 := by
  calc
    _ ≤ ∏ p ∈ primesUpTo Q, Real.exp (4 * (1 / (p : ℝ) ^ 2)) :=
      Finset.prod_le_prod
        (fun p hp => (square_divisor_euler_numerator_bounds (mem_primesUpTo.mp hp).1).1)
        (fun p hp => (square_divisor_euler_numerator_bounds (mem_primesUpTo.mp hp).1).2)
    _ = Real.exp (4 * ∑ p ∈ primesUpTo Q, 1 / (p : ℝ) ^ 2) := by
      rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ Real.exp 8 :=
      Real.exp_le_exp.mpr (by linarith [prime_reciprocal_square_sum_le_two Q])

/-- The closed-form Euler product splits as the numerator product over the fourth
power of the Mertens product `∏_{p ≤ Q} (1 - 1/p)`. -/
theorem square_divisor_euler_product_eq_div_pow (Q : ℕ) :
    (∏ p ∈ primesUpTo Q,
        (1 + 3 * (p : ℝ)⁻¹ ^ 2 - 3 * (p : ℝ)⁻¹ ^ 3 + (p : ℝ)⁻¹ ^ 4) /
          (1 - (p : ℝ)⁻¹) ^ 4) =
      (∏ p ∈ primesUpTo Q, (1 + 3 * (p : ℝ)⁻¹ ^ 2 - 3 * (p : ℝ)⁻¹ ^ 3 + (p : ℝ)⁻¹ ^ 4)) /
        primeProduct Q ^ 4 := by
  rw [Finset.prod_div_distrib, Finset.prod_pow, primeProduct]
  simp only [one_div]

/-- `∑_{q ≤ Q} τ(q)^2/φ(q) ≪ (log 2Q)^4` for real `Q ≥ 2` (proof of Lemma 3.8). -/
theorem exists_square_divisor_card_totient_moment_le_log_fourth :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 2 ≤ Q →
      (∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (q.divisors.card : ℝ) ^ 2 / Nat.totient q) ≤
        C * Real.log (2 * Q) ^ 4 := by
  obtain ⟨_c, C, -, hC, hprod⟩ := PrimeEstimates.Mertens.inverse_product_bounds
  refine ⟨Real.exp 8 * C ^ 4, by positivity, fun Q hQ => ?_⟩
  have hfloor : 2 ≤ ⌊Q⌋₊ := Nat.le_floor (by exact_mod_cast hQ)
  have hfloorR : (2 : ℝ) ≤ ⌊Q⌋₊ := by exact_mod_cast hfloor
  have hle : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le (by linarith)
  have hlog0 : 0 ≤ Real.log (⌊Q⌋₊ : ℝ) := Real.log_nonneg (by linarith)
  have hlog : Real.log (⌊Q⌋₊ : ℝ) ≤ Real.log (2 * Q) :=
    Real.log_le_log (by linarith) (by linarith)
  have hinv := (hprod (⌊Q⌋₊ : ℝ) hfloorR).2
  rw [Nat.floor_natCast] at hinv
  have hpos := primeProduct_pos ⌊Q⌋₊
  calc
    _ ≤ _ := square_divisor_card_totient_sum_le_euler_product ⌊Q⌋₊
    _ = _ := square_divisor_euler_product_eq_div_pow ⌊Q⌋₊
    _ ≤ Real.exp 8 * ((primeProduct ⌊Q⌋₊)⁻¹) ^ 4 := by
      rw [div_eq_mul_inv, ← inv_pow]
      exact mul_le_mul_of_nonneg_right (prod_square_divisor_euler_numerator_le_exp _)
        (by positivity)
    _ ≤ Real.exp 8 * (C * Real.log (⌊Q⌋₊ : ℝ)) ^ 4 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv 4) (by positivity)
    _ ≤ Real.exp 8 * (C * Real.log (2 * Q)) ^ 4 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left hlog hC.le) 4) (by positivity)
    _ = _ := by ring

end ErdosStraus.DivisorEstimates
