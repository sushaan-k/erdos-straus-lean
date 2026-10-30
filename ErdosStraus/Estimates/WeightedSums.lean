import ErdosStraus.Estimates.Squarefree
import Batteries.Tactic.Lemma
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AlmostPrime
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter

/-! # Lemmas 3.3 and 6.4: squarefree weighted sums

For `S = X^η`, `z = (log X)^4` and `U = (log X)^8` this file proves
`∑_{s ≤ S, s squarefree} φ(s)/s² ≍ log S` and `∑_{s ≤ S, s squarefree} 1/s ≍ log S`
(Lemma 3.3), the second of these with the extra condition `(s, m) = 1`, and
`∑_{s ≤ S, s squarefree} A_s/s ≍ log S · log z` for
`A_s = ∑_{d ≤ U, d ∣ P(z), d odd, (d, s) = 1} 1/d` (Lemma 6.4 with `m = 1`).
The lower bounds rest on `∑_{d ≤ Y, d odd squarefree} φ(d)/d² ≫ log Y`, which follows from
`∑_{d ≤ Y, d odd squarefree} (d - φ(d))/d² ≤ (1/2) ∑_{d ≤ Y, d odd squarefree} 1/d`.
-/

namespace ErdosStraus.Estimates
open Filter Asymptotics
open scoped BigOperators Pointwise

/-! ## From dyadic to real cutoffs -/

theorem oddSquarefreeEulerWitness_eq_nat (X : ℝ) :
    oddSquarefreeEulerWitness X =
      oddSquarefreeEulerWitnessNat ⌊ErdosStraus.zScale X⌋₊ := by
  rfl

/-- A bound `∑_{d ≤ 2^k, d odd squarefree} φ(d)/d² ≥ c log 2^k` for `k ≥ 2` gives the same
bound, with `c/2`, at `z = (log X)^4`. Take `B = 2^⌊log₂ ⌊z⌋⌋`, so that `B ≤ ⌊z⌋ < 2B`; for
`X ≥ e²` this gives `z ≤ 4B` and `log z ≤ 2 log B`. -/
theorem oddSqfTotient_lower_of_dyadic
    (hdy :
      ∃ c > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
        c * Real.log ((2 ^ k : ℕ) : ℝ)
          ≤ ∑ d ∈ oddSquarefreeEulerWitnessNat (2 ^ k),
              (Nat.totient d : ℝ) / (d : ℝ) ^ 2) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      c * Real.log (ErdosStraus.zScale X)
        ≤ ∑ d ∈ oddSquarefreeEulerWitness X,
            (Nat.totient d : ℝ) / (d : ℝ) ^ 2 := by
  rcases hdy with ⟨c, hc, hdy⟩
  refine ⟨c / 2, Real.exp 2, half_pos hc, ?_⟩
  intro X hX
  let Z : ℕ := ⌊ErdosStraus.zScale X⌋₊
  let k : ℕ := Nat.log 2 Z
  let B : ℕ := 2 ^ k
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 2) hX
  have hlogX_ge_two : (2 : ℝ) ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hX
  have hz_ge_sixteen : (16 : ℝ) ≤ ErdosStraus.zScale X := by
    unfold ErdosStraus.zScale
    nlinarith [sq_nonneg (Real.log X - 2),
      mul_self_nonneg ((Real.log X) ^ 2 - 4)]
  have hz_pos : 0 < ErdosStraus.zScale X := lt_of_lt_of_le (by norm_num) hz_ge_sixteen
  have hz_nonneg : 0 ≤ ErdosStraus.zScale X := hz_pos.le
  have hZ_ge_four : 4 ≤ Z := by
    exact Nat.le_floor (by linarith : (4 : ℝ) ≤ ErdosStraus.zScale X)
  have hZ_ne_zero : Z ≠ 0 := by omega
  have hB_le_Z : B ≤ Z := by
    exact Nat.pow_log_le_self 2 hZ_ne_zero
  have hk_ge_two : 2 ≤ k := by
    exact Nat.le_log_of_pow_le (by norm_num : 1 < 2)
      (by simpa [k] using hZ_ge_four)
  have hB_ge_four : 4 ≤ B := by
    exact le_trans (by simp : 4 ≤ 2 ^ (2 : ℕ))
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) hk_ge_two)
  have hB_pos_nat : 0 < B := by omega
  have hB_pos : 0 < (B : ℝ) := by exact_mod_cast hB_pos_nat
  have hB_ge_one_real : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast (by omega : 1 ≤ B)
  have hZ_lt_pow_succ : Z < 2 ^ (k + 1) := by
    exact Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) Z
  have hZ_le_twoB : Z ≤ 2 * B := by
    have hpow_eq : 2 ^ (k + 1) = 2 * B := by
      simp [B, pow_succ, mul_comm]
    exact Nat.le_of_lt (by simpa [hpow_eq] using hZ_lt_pow_succ)
  have hz_le_Z_add_one :
      ErdosStraus.zScale X ≤ (Z : ℝ) + 1 := by
    exact (Nat.lt_floor_add_one (ErdosStraus.zScale X)).le
  have hZ_add_one_le_fourB : (Z : ℝ) + 1 ≤ 4 * (B : ℝ) := by
    have hZ_le_twoB_real : (Z : ℝ) ≤ 2 * (B : ℝ) := by
      exact_mod_cast hZ_le_twoB
    have hone_le_twoB : (1 : ℝ) ≤ 2 * (B : ℝ) := by nlinarith [hB_ge_one_real]
    nlinarith
  have hz_le_fourB : ErdosStraus.zScale X ≤ 4 * (B : ℝ) :=
    le_trans hz_le_Z_add_one hZ_add_one_le_fourB
  have hfourB_pos : 0 < 4 * (B : ℝ) := by positivity
  have hlog_z_le_log_fourB :
      Real.log (ErdosStraus.zScale X) ≤ Real.log (4 * (B : ℝ)) :=
    Real.log_le_log hz_pos hz_le_fourB
  have hlog_fourB_eq :
      Real.log (4 * (B : ℝ)) = Real.log 4 + Real.log (B : ℝ) := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hB_pos)]
  have hlog_four_le_logB : Real.log 4 ≤ Real.log (B : ℝ) := by
    exact Real.log_le_log (by norm_num : (0 : ℝ) < 4)
      (by exact_mod_cast hB_ge_four)
  have hlog_z_le_two_logB :
      Real.log (ErdosStraus.zScale X) ≤ 2 * Real.log (B : ℝ) := by
    calc
      Real.log (ErdosStraus.zScale X)
          ≤ Real.log (4 * (B : ℝ)) := hlog_z_le_log_fourB
      _ = Real.log 4 + Real.log (B : ℝ) := hlog_fourB_eq
      _ ≤ 2 * Real.log (B : ℝ) := by linarith
  have hscaled :
      (c / 2) * Real.log (ErdosStraus.zScale X)
        ≤ c * Real.log (B : ℝ) := by
    nlinarith [hc, hlog_z_le_two_logB]
  have hdy_B :
      c * Real.log (B : ℝ)
        ≤ ∑ d ∈ oddSquarefreeEulerWitnessNat B,
            (Nat.totient d : ℝ) / (d : ℝ) ^ 2 := by
    simpa [B] using hdy k hk_ge_two
  have hmono :
      (∑ d ∈ oddSquarefreeEulerWitnessNat B,
          (Nat.totient d : ℝ) / (d : ℝ) ^ 2)
        ≤ ∑ d ∈ oddSquarefreeEulerWitnessNat Z,
            (Nat.totient d : ℝ) / (d : ℝ) ^ 2 :=
    oddSquarefreeEulerWitnessNat_sum_mono hB_le_Z
  calc
    (c / 2) * Real.log (ErdosStraus.zScale X)
        ≤ c * Real.log (B : ℝ) := hscaled
    _ ≤ ∑ d ∈ oddSquarefreeEulerWitnessNat B,
          (Nat.totient d : ℝ) / (d : ℝ) ^ 2 := hdy_B
    _ ≤ ∑ d ∈ oddSquarefreeEulerWitnessNat Z,
          (Nat.totient d : ℝ) / (d : ℝ) ^ 2 := hmono
    _ = ∑ d ∈ oddSquarefreeEulerWitness X,
          (Nat.totient d : ℝ) / (d : ℝ) ^ 2 := by
          simp [oddSquarefreeEulerWitness_eq_nat, Z]

/-! ## Adding a coprimality condition -/

theorem sAvgRecipCoprime_nonneg (P : ErdosStraus.Params) (X : ℝ) (d : ℕ) :
    0 ≤ sAvgRecipCoprime P X d := by
  classical
  unfold sAvgRecipCoprime
  apply Finset.sum_nonneg
  intro s _hs
  exact div_nonneg zero_le_one (Nat.cast_nonneg s)

/-- Adding the condition `(s, d) = 1` loses at most the factor `∑_{g ∣ d} 1/g`. Each
squarefree `s` factors as `s = (s, d) · s/(s, d)`, where `s/(s, d)` is squarefree and
coprime to `d`, and this factorization is injective. -/
theorem sAvgRecip_le_divisor_recip_mul_sAvgRecipCoprime
    (P : ErdosStraus.Params) (X : ℝ) {d : ℕ} (hd : 0 < d) :
    sAvgRecip P X ≤
      (∑ g ∈ d.divisors, (1 : ℝ) / (g : ℝ)) *
        sAvgRecipCoprime P X d := by
  classical
  let Sset : Finset ℕ :=
    (Finset.Icc (1 : ℕ) ⌊ErdosStraus.SScale P X⌋₊).filter (fun s => Squarefree s)
  let Cset : Finset ℕ :=
    (Finset.Icc (1 : ℕ) ⌊ErdosStraus.SScale P X⌋₊).filter
      (fun r => Squarefree r ∧ Nat.Coprime r d)
  let F : ℕ → ℕ × ℕ := fun s => (Nat.gcd s d, s / Nat.gcd s d)
  let G : ℕ × ℕ → ℝ := fun p => ((1 : ℝ) / (p.1 : ℝ)) * ((1 : ℝ) / (p.2 : ℝ))
  have hF_inj : ∀ a ∈ Sset, ∀ b ∈ Sset, F a = F b → a = b := by
    intro a ha b hb hab
    have hg : Nat.gcd a d = Nat.gcd b d := congrArg Prod.fst hab
    have hq : a / Nat.gcd a d = b / Nat.gcd b d := congrArg Prod.snd hab
    have haIcc : a ∈ Finset.Icc (1 : ℕ) ⌊ErdosStraus.SScale P X⌋₊ :=
      (Finset.mem_filter.mp ha).1
    have hbIcc : b ∈ Finset.Icc (1 : ℕ) ⌊ErdosStraus.SScale P X⌋₊ :=
      (Finset.mem_filter.mp hb).1
    have hapos : 0 < a := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp haIcc).1
    have hbpos : 0 < b := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hbIcc).1
    have hq' : a / Nat.gcd b d = b / Nat.gcd b d := by
      simpa [hg] using hq
    calc
      a = Nat.gcd a d * (a / Nat.gcd a d) := by
            rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left a d)]
      _ = Nat.gcd b d * (b / Nat.gcd b d) := by rw [hg, hq']
      _ = b := by
            rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left b d)]
  have hF_mem : ∀ s ∈ Sset, F s ∈ d.divisors.product Cset := by
    intro s hs
    have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊ErdosStraus.SScale P X⌋₊ :=
      (Finset.mem_filter.mp hs).1
    have hsqf : Squarefree s := (Finset.mem_filter.mp hs).2
    have hspos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hsIcc).1
    have hgpos : 0 < Nat.gcd s d := Nat.gcd_pos_of_pos_left d hspos
    have hquot_pos : 0 < s / Nat.gcd s d :=
      Nat.div_pos (Nat.gcd_le_left d hspos) hgpos
    have hquot_le_s : s / Nat.gcd s d ≤ s := Nat.div_le_self s (Nat.gcd s d)
    have hquot_Icc : s / Nat.gcd s d ∈
        Finset.Icc (1 : ℕ) ⌊ErdosStraus.SScale P X⌋₊ :=
      Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hquot_pos,
        le_trans hquot_le_s (Finset.mem_Icc.mp hsIcc).2⟩
    have hquot_sqf : Squarefree (s / Nat.gcd s d) :=
      hsqf.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left s d))
    have hquot_coprime : Nat.Coprime (s / Nat.gcd s d) d :=
      Nat.coprime_div_gcd_of_squarefree hsqf hd.ne'
    have hg_mem : Nat.gcd s d ∈ d.divisors :=
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right s d, hd.ne'⟩
    exact Finset.mem_product.mpr
      ⟨hg_mem, Finset.mem_filter.mpr ⟨hquot_Icc, hquot_sqf, hquot_coprime⟩⟩
  have hterm : ∀ s ∈ Sset, (1 : ℝ) / (s : ℝ) = G (F s) := by
    intro s hs
    have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊ErdosStraus.SScale P X⌋₊ :=
      (Finset.mem_filter.mp hs).1
    have hspos_nat : 0 < s :=
      lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hsIcc).1
    have hgpos_nat : 0 < Nat.gcd s d := Nat.gcd_pos_of_pos_left d hspos_nat
    have hqpos_nat : 0 < s / Nat.gcd s d :=
      Nat.div_pos (Nat.gcd_le_left d hspos_nat) hgpos_nat
    have hs_eq : s = Nat.gcd s d * (s / Nat.gcd s d) := by
      rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left s d)]
    have hgpos : (0 : ℝ) < (Nat.gcd s d : ℝ) := by exact_mod_cast hgpos_nat
    have hqpos : (0 : ℝ) < ((s / Nat.gcd s d : ℕ) : ℝ) := by exact_mod_cast hqpos_nat
    have hs_cast :
        (s : ℝ) = (Nat.gcd s d : ℝ) * ((s / Nat.gcd s d : ℕ) : ℝ) := by
      exact_mod_cast hs_eq
    unfold F G
    change (1 : ℝ) / (s : ℝ) =
      ((1 : ℝ) / (Nat.gcd s d : ℝ)) *
        ((1 : ℝ) / ((s / Nat.gcd s d : ℕ) : ℝ))
    rw [hs_cast]
    field_simp [ne_of_gt hgpos, ne_of_gt hqpos]
  have himage_eq :
      (∑ s ∈ Sset, (1 : ℝ) / (s : ℝ)) = ∑ p ∈ Sset.image F, G p := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro s hs
      exact hterm s hs
    · intro a ha b hb hab
      exact hF_inj a ha b hb hab
  have himage_subset : Sset.image F ⊆ d.divisors.product Cset := by
    intro p hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨s, hs, rfl⟩
    exact hF_mem s hs
  have hnonneg_extra :
      ∀ p ∈ d.divisors.product Cset, p ∉ Sset.image F → 0 ≤ G p := by
    intro p _hp _
    unfold G
    exact mul_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg _))
      (div_nonneg zero_le_one (Nat.cast_nonneg _))
  have himage_le_product :
      (∑ p ∈ Sset.image F, G p) ≤ ∑ p ∈ d.divisors.product Cset, G p :=
    Finset.sum_le_sum_of_subset_of_nonneg himage_subset hnonneg_extra
  have hproduct_eq :
      (∑ p ∈ d.divisors.product Cset, G p)
        = (∑ g ∈ d.divisors, (1 : ℝ) / (g : ℝ)) *
            (∑ r ∈ Cset, (1 : ℝ) / (r : ℝ)) := by
    change (∑ p ∈ d.divisors ×ˢ Cset, G p) = _
    rw [Finset.sum_product]
    unfold G
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro g _hg
    rw [Finset.mul_sum]
  have hS_eq : (∑ s ∈ Sset, (1 : ℝ) / (s : ℝ)) = sAvgRecip P X := by
    unfold Sset sAvgRecip
    rfl
  have hC_eq : (∑ r ∈ Cset, (1 : ℝ) / (r : ℝ)) = sAvgRecipCoprime P X d := by
    unfold Cset sAvgRecipCoprime
    rfl
  calc
    sAvgRecip P X = ∑ s ∈ Sset, (1 : ℝ) / (s : ℝ) := hS_eq.symm
    _ = ∑ p ∈ Sset.image F, G p := himage_eq
    _ ≤ ∑ p ∈ d.divisors.product Cset, G p := himage_le_product
    _ = (∑ g ∈ d.divisors, (1 : ℝ) / (g : ℝ)) *
          sAvgRecipCoprime P X d := by rw [hproduct_eq, hC_eq]

/-- For squarefree `d`, `(∑_{g ∣ d} 1/g) φ(d) ≤ d`, since `φ(d)/g ≤ φ(d/g)` and
`∑_{g ∣ d} φ(d/g) = d`. -/
theorem divisor_recip_sum_mul_totient_le_self
    {d : ℕ} (hd : 0 < d) (hsqf : Squarefree d) :
    (∑ g ∈ d.divisors, (1 : ℝ) / (g : ℝ)) *
        (Nat.totient d : ℝ) ≤ (d : ℝ) := by
  classical
  have hterm :
      ∀ g ∈ d.divisors,
        ((1 : ℝ) / (g : ℝ)) * (Nat.totient d : ℝ) ≤
          (Nat.totient (d / g) : ℝ) := by
    intro g hg
    have hgd : g ∣ d := Nat.dvd_of_mem_divisors hg
    have hgpos_nat : 0 < g := Nat.pos_of_mem_divisors hg
    have hgpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hgpos_nat
    have hqpos_nat : 0 < d / g := Nat.div_pos (Nat.le_of_dvd hd hgd) hgpos_nat
    have hq_nonneg : (0 : ℝ) ≤ (Nat.totient (d / g) : ℝ) := Nat.cast_nonneg _
    have hsqf_prod : Squarefree (g * (d / g)) := by
      have hprod_eq : g * (d / g) = d := by
        rw [Nat.mul_comm, Nat.div_mul_cancel hgd]
      simpa [hprod_eq] using hsqf
    have hcop : Nat.Coprime g (d / g) :=
      Nat.coprime_of_squarefree_mul hsqf_prod
    have htot_eq : Nat.totient d = Nat.totient g * Nat.totient (d / g) := by
      calc
        Nat.totient d = Nat.totient (g * (d / g)) := by
          rw [Nat.mul_comm, Nat.div_mul_cancel hgd]
        _ = Nat.totient g * Nat.totient (d / g) := Nat.totient_mul hcop
    have htot_g_le_nat : Nat.totient g ≤ g := Nat.totient_le g
    have htot_g_le : (Nat.totient g : ℝ) ≤ (g : ℝ) := by exact_mod_cast htot_g_le_nat
    calc
      ((1 : ℝ) / (g : ℝ)) * (Nat.totient d : ℝ)
          = ((Nat.totient g : ℝ) / (g : ℝ)) *
              (Nat.totient (d / g) : ℝ) := by
            rw [htot_eq, Nat.cast_mul]
            field_simp [ne_of_gt hgpos]
      _ ≤ 1 * (Nat.totient (d / g) : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hq_nonneg
            calc
              (Nat.totient g : ℝ) / (g : ℝ) ≤ (g : ℝ) / (g : ℝ) :=
                div_le_div_of_nonneg_right htot_g_le hgpos.le
              _ = 1 := by field_simp [ne_of_gt hgpos]
      _ = (Nat.totient (d / g) : ℝ) := by ring
  calc
    (∑ g ∈ d.divisors, (1 : ℝ) / (g : ℝ)) * (Nat.totient d : ℝ)
        = ∑ g ∈ d.divisors, ((1 : ℝ) / (g : ℝ)) * (Nat.totient d : ℝ) := by
          rw [Finset.sum_mul]
    _ ≤ ∑ g ∈ d.divisors, (Nat.totient (d / g) : ℝ) := by
          apply Finset.sum_le_sum
          intro g hg
          exact hterm g hg
    _ = ∑ g ∈ d.divisors, (Nat.totient g : ℝ) := by
          exact_mod_cast Nat.sum_div_divisors d Nat.totient
    _ = (d : ℝ) := by
          exact_mod_cast Nat.sum_totient d

theorem divisor_recip_sum_le_totient_ratio
    {d : ℕ} (hd : 0 < d) (hsqf : Squarefree d) :
    (∑ g ∈ d.divisors, (1 : ℝ) / (g : ℝ)) ≤
      (d : ℝ) / (Nat.totient d : ℝ) := by
  have hphi_pos_nat : 0 < Nat.totient d := Nat.totient_pos.mpr hd
  have hphi_pos : (0 : ℝ) < (Nat.totient d : ℝ) := by exact_mod_cast hphi_pos_nat
  rw [le_div_iff₀ hphi_pos]
  exact divisor_recip_sum_mul_totient_le_self hd hsqf

/-! ## The decomposition `n = b²a` -/

/-- The squarefree factor `a` in a decomposition `n = b²a` with `a` squarefree. -/
noncomputable def sfPartForCoprimeLower (n : ℕ) : ℕ :=
  Classical.choose (Nat.sq_mul_squarefree n)

/-- The factor `b` in the decomposition `n = b²a` that defines `sfPartForCoprimeLower`. -/
noncomputable def sqPartForCoprimeLower (n : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (Nat.sq_mul_squarefree n))

theorem sfPartForCoprimeLower_spec (n : ℕ) :
    sqPartForCoprimeLower n ^ 2 * sfPartForCoprimeLower n = n ∧
      Squarefree (sfPartForCoprimeLower n) := by
  unfold sfPartForCoprimeLower sqPartForCoprimeLower
  exact Classical.choose_spec (Classical.choose_spec (Nat.sq_mul_squarefree n))

theorem sfPartForCoprimeLower_pos {n : ℕ} (hn : 0 < n) :
    0 < sfPartForCoprimeLower n := by
  have hprod := (sfPartForCoprimeLower_spec n).1
  by_contra h
  have ha0 : sfPartForCoprimeLower n = 0 := Nat.eq_zero_of_not_pos h
  rw [ha0, Nat.mul_zero] at hprod
  omega

theorem sqPartForCoprimeLower_pos {n : ℕ} (hn : 0 < n) :
    0 < sqPartForCoprimeLower n := by
  have hprod := (sfPartForCoprimeLower_spec n).1
  by_contra h
  have hb0 : sqPartForCoprimeLower n = 0 := Nat.eq_zero_of_not_pos h
  rw [hb0] at hprod
  norm_num at hprod
  omega

theorem sfPartForCoprimeLower_le_self {n : ℕ} (hn : 0 < n) :
    sfPartForCoprimeLower n ≤ n := by
  have hprod := (sfPartForCoprimeLower_spec n).1
  have hbpos : 0 < sqPartForCoprimeLower n := sqPartForCoprimeLower_pos hn
  have hsqpos : 0 < sqPartForCoprimeLower n ^ 2 := pow_pos hbpos 2
  calc
    sfPartForCoprimeLower n
        ≤ sqPartForCoprimeLower n ^ 2 * sfPartForCoprimeLower n :=
          Nat.le_mul_of_pos_left (sfPartForCoprimeLower n) hsqpos
    _ = n := hprod

theorem sqPartForCoprimeLower_le_self {n : ℕ} (hn : 0 < n) :
    sqPartForCoprimeLower n ≤ n := by
  have hprod := (sfPartForCoprimeLower_spec n).1
  have hsfpos : 0 < sfPartForCoprimeLower n := sfPartForCoprimeLower_pos hn
  calc
    sqPartForCoprimeLower n
        ≤ sqPartForCoprimeLower n ^ 2 :=
          Nat.le_self_pow (by norm_num : 2 ≠ 0) (sqPartForCoprimeLower n)
    _ ≤ sqPartForCoprimeLower n ^ 2 * sfPartForCoprimeLower n :=
          Nat.le_mul_of_pos_right (sqPartForCoprimeLower n ^ 2) hsfpos
    _ = n := hprod

theorem square_recip_sum_le_two_for_coprime_lower (Y : ℕ) :
    (∑ b ∈ Finset.Icc (1 : ℕ) Y, ((b : ℝ) ^ 2)⁻¹) ≤ 2 := by
  by_cases hY : 1 ≤ Y
  · rw [Finset.Icc_eq_cons_Ioc hY, Finset.sum_cons]
    have htail : (∑ b ∈ Finset.Ioc (1 : ℕ) Y, ((b : ℝ) ^ 2)⁻¹) ≤ (1 : ℝ) := by
      have h := (sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 1) (n := Y) (by norm_num) hY)
      have h' :
          (∑ b ∈ Finset.Ioc (1 : ℕ) Y, ((b : ℝ) ^ 2)⁻¹)
            ≤ (1 : ℝ) - ((Y : ℝ))⁻¹ := by
        simpa using h
      have hnonneg : (0 : ℝ) ≤ ((Y : ℝ))⁻¹ :=
        inv_nonneg.mpr (Nat.cast_nonneg Y)
      linarith
    norm_num
    linarith
  · have hempty : Finset.Icc (1 : ℕ) Y = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro b hb
      exact hY (le_trans (Finset.mem_Icc.mp hb).1 (Finset.mem_Icc.mp hb).2)
    rw [hempty, Finset.sum_empty]
    norm_num

/-- `H_Y ≤ (∑_{a≤Y, a squarefree} 1/a)(∑_{b≤Y} 1/b²)`, by writing `n = b²a` with `a`
squarefree. -/
theorem harmonic_le_squarefree_mul_square_recip (Y : ℕ) :
    ((harmonic Y : ℚ) : ℝ)
      ≤ (∑ a ∈ (Finset.Icc (1 : ℕ) Y).filter (fun a => Squarefree a),
            (1 : ℝ) / (a : ℝ)) *
          (∑ b ∈ Finset.Icc (1 : ℕ) Y, ((b : ℝ) ^ 2)⁻¹) := by
  classical
  let base : Finset ℕ := Finset.Icc (1 : ℕ) Y
  let sfSet : Finset ℕ := base.filter (fun a => Squarefree a)
  let F : ℕ → ℕ × ℕ := fun n => (sfPartForCoprimeLower n, sqPartForCoprimeLower n)
  let G : ℕ × ℕ → ℝ := fun p => ((1 : ℝ) / (p.1 : ℝ)) * (((p.2 : ℝ) ^ 2)⁻¹)
  have hF_mem : ∀ n ∈ base, F n ∈ sfSet.product base := by
    intro n hn
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
    have hnle : n ≤ Y := (Finset.mem_Icc.mp hn).2
    change F n ∈ sfSet ×ˢ base
    rw [Finset.mem_product]
    constructor
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_Icc.mpr
          ⟨sfPartForCoprimeLower_pos hnpos,
            le_trans (sfPartForCoprimeLower_le_self hnpos) hnle⟩,
        (sfPartForCoprimeLower_spec n).2⟩
    · exact Finset.mem_Icc.mpr
        ⟨sqPartForCoprimeLower_pos hnpos,
          le_trans (sqPartForCoprimeLower_le_self hnpos) hnle⟩
  have hF_inj : ∀ n ∈ base, ∀ m ∈ base, F n = F m → n = m := by
    intro n _hn m _hm hnm
    have hnprod := (sfPartForCoprimeLower_spec n).1
    have hmprod := (sfPartForCoprimeLower_spec m).1
    have ha : sfPartForCoprimeLower n = sfPartForCoprimeLower m :=
      congrArg Prod.fst hnm
    have hb : sqPartForCoprimeLower n = sqPartForCoprimeLower m :=
      congrArg Prod.snd hnm
    rw [← hnprod, ← hmprod, ha, hb]
  have himage_eq :
      (∑ n ∈ base, (1 : ℝ) / (n : ℝ)) = ∑ p ∈ base.image F, G p := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro n hn
      have hnpos_nat : 0 < n :=
        lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
      have hapos_nat : 0 < sfPartForCoprimeLower n :=
        sfPartForCoprimeLower_pos hnpos_nat
      have hbpos_nat : 0 < sqPartForCoprimeLower n :=
        sqPartForCoprimeLower_pos hnpos_nat
      have hapos : (sfPartForCoprimeLower n : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hapos_nat)
      have hbpos : (sqPartForCoprimeLower n : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hbpos_nat)
      have hprod := (sfPartForCoprimeLower_spec n).1
      have hcast :
          ((sqPartForCoprimeLower n ^ 2 * sfPartForCoprimeLower n : ℕ) : ℝ)
            = (sqPartForCoprimeLower n : ℝ) ^ 2 *
                (sfPartForCoprimeLower n : ℝ) := by
        norm_num [Nat.cast_mul, Nat.cast_pow]
      calc
        (1 : ℝ) / (n : ℝ)
            = (1 : ℝ) /
                ((sqPartForCoprimeLower n ^ 2 * sfPartForCoprimeLower n : ℕ) : ℝ) := by
              rw [hprod]
        _ = (1 : ℝ) /
              ((sqPartForCoprimeLower n : ℝ) ^ 2 *
                (sfPartForCoprimeLower n : ℝ)) := by
              rw [hcast]
        _ = ((1 : ℝ) / (sfPartForCoprimeLower n : ℝ)) *
              (((sqPartForCoprimeLower n : ℝ) ^ 2)⁻¹) := by
              field_simp [hapos, hbpos]
        _ = G (F n) := by simp [G, F]
    · intro n hn m hm hnm
      exact hF_inj n hn m hm hnm
  have himage_subset : base.image F ⊆ sfSet.product base := by
    intro p hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨n, hn, rfl⟩
    exact hF_mem n hn
  have hnonneg_extra : ∀ p ∈ sfSet.product base, p ∉ base.image F → 0 ≤ G p := by
    intro p _hp _
    unfold G
    exact mul_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg _))
      (inv_nonneg.mpr (sq_nonneg _))
  have himage_le_product :
      (∑ p ∈ base.image F, G p) ≤ ∑ p ∈ sfSet.product base, G p :=
    Finset.sum_le_sum_of_subset_of_nonneg himage_subset hnonneg_extra
  have hproduct_eq :
      (∑ p ∈ sfSet.product base, G p)
        = (∑ a ∈ sfSet, (1 : ℝ) / (a : ℝ)) *
            (∑ b ∈ base, ((b : ℝ) ^ 2)⁻¹) := by
    change (∑ p ∈ sfSet ×ˢ base, G p) = _
    rw [Finset.sum_product]
    unfold G
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [Finset.mul_sum]
  have hharm_eq : ((harmonic Y : ℚ) : ℝ) = ∑ n ∈ base, (1 : ℝ) / (n : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    unfold base
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    simp_rw [one_div]
  calc
    ((harmonic Y : ℚ) : ℝ) = ∑ n ∈ base, (1 : ℝ) / (n : ℝ) := hharm_eq
    _ = ∑ p ∈ base.image F, G p := himage_eq
    _ ≤ ∑ p ∈ sfSet.product base, G p := himage_le_product
    _ = (∑ a ∈ sfSet, (1 : ℝ) / (a : ℝ)) *
            (∑ b ∈ base, ((b : ℝ) ^ 2)⁻¹) := hproduct_eq

/-! ## Odd squarefree sums on dyadic ranges -/

/-- `∑_{n ≤ Y, n odd} 1/n`. -/
noncomputable def oddRecipNat (Y : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc (1 : ℕ) Y).filter (fun n => Odd n),
    (1 : ℝ) / (n : ℝ)

/-- `∑_{a ≤ Y, a odd squarefree} 1/a`. -/
noncomputable def oddSquarefreeRecipNat (Y : ℕ) : ℝ :=
  ∑ a ∈ oddSquarefreeEulerWitnessNat Y, (1 : ℝ) / (a : ℝ)

/-- `∑_{a ≤ Y, a odd squarefree} φ(a)/a²`. -/
noncomputable def oddSquarefreeTotientNat (Y : ℕ) : ℝ :=
  ∑ a ∈ oddSquarefreeEulerWitnessNat Y, (Nat.totient a : ℝ) / (a : ℝ) ^ 2

/-- `∑_{a ≤ Y, a odd squarefree} (a - φ(a))/a²`, the difference of the two previous
sums. -/
noncomputable def oddSquarefreeTotientDefectNat (Y : ℕ) : ℝ :=
  ∑ a ∈ oddSquarefreeEulerWitnessNat Y,
    ((a - Nat.totient a : ℕ) : ℝ) / (a : ℝ) ^ 2

/-- `∏_{p ∣ n} (1 - 1/p)`, which equals `φ(n)/n` for `n > 0`. -/
noncomputable def totientPrimeFactorProduct (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹)

/-- `∑_{a ≤ Y, a odd squarefree} (1 - ∏_{p ∣ a} (1 - 1/p))/a`, which equals
`oddSquarefreeTotientDefectNat Y`. -/
noncomputable def oddSquarefreeTotientDefectProductNat (Y : ℕ) : ℝ :=
  ∑ a ∈ oddSquarefreeEulerWitnessNat Y,
    (1 - totientPrimeFactorProduct a) / (a : ℝ)

/-- For some `0 < ε < 1` and all `k ≥ 2`,
`oddSquarefreeTotientDefectProductNat 2^k ≤ (1 - ε) oddSquarefreeRecipNat 2^k`. -/
def OddSquarefreeTotientDefectProductGapBound : Prop :=
  ∃ ε > (0 : ℝ), ε < 1 ∧ ∀ k : ℕ, 2 ≤ k →
    oddSquarefreeTotientDefectProductNat (2 ^ k)
      ≤ (1 - ε) * oddSquarefreeRecipNat (2 ^ k)

theorem oddSquarefreeRecipNat_nonneg (Y : ℕ) :
    0 ≤ oddSquarefreeRecipNat Y := by
  unfold oddSquarefreeRecipNat
  exact Finset.sum_nonneg (by
    intro a _ha
    exact div_nonneg zero_le_one (Nat.cast_nonneg a))

theorem totient_div_eq_totientPrimeFactorProduct
    {n : ℕ} (hn : 0 < n) :
    (Nat.totient n : ℝ) / (n : ℝ) =
      totientPrimeFactorProduct n := by
  have hq := Nat.totient_eq_mul_prod_factors n
  have hr : (Nat.totient n : ℝ) =
      (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have hcast := congrArg (fun q : ℚ => (q : ℝ)) hq
    simpa [totientPrimeFactorProduct, Rat.cast_natCast, Rat.cast_mul,
      Rat.cast_prod, Rat.cast_sub, Rat.cast_one, Rat.cast_inv] using hcast
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  rw [totientPrimeFactorProduct, hr]
  field_simp [hnreal]

theorem oddSquarefreeTotientDefectProductNat_eq_defectNat (Y : ℕ) :
    oddSquarefreeTotientDefectProductNat Y =
      oddSquarefreeTotientDefectNat Y := by
  classical
  unfold oddSquarefreeTotientDefectProductNat oddSquarefreeTotientDefectNat
  apply Finset.sum_congr rfl
  intro d hd
  have hdIcc : d ∈ Finset.Icc (1 : ℕ) Y := (Finset.mem_filter.mp hd).1
  have hd_pos_nat : 0 < d :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdIcc).1
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos_nat
  have htot_le_nat : Nat.totient d ≤ d := Nat.totient_le d
  have hsub_cast :
      ((d - Nat.totient d : ℕ) : ℝ) =
        (d : ℝ) - (Nat.totient d : ℝ) := by
    exact Nat.cast_sub htot_le_nat
  have hratio := totient_div_eq_totientPrimeFactorProduct hd_pos_nat
  calc
    (1 - totientPrimeFactorProduct d) / (d : ℝ)
        = (1 - (Nat.totient d : ℝ) / (d : ℝ)) / (d : ℝ) := by rw [hratio]
    _ = ((d - Nat.totient d : ℕ) : ℝ) / (d : ℝ) ^ 2 := by
          rw [hsub_cast]
          rw [show (1 : ℝ) - (Nat.totient d : ℝ) / (d : ℝ) =
              ((d : ℝ) - (Nat.totient d : ℝ)) / (d : ℝ) by
            field_simp [hd_pos.ne']]
          rw [div_div, pow_two]

theorem oddSquarefreeTotientNat_add_defect_eq_recipNat (Y : ℕ) :
    oddSquarefreeTotientNat Y + oddSquarefreeTotientDefectNat Y =
      oddSquarefreeRecipNat Y := by
  classical
  unfold oddSquarefreeTotientNat oddSquarefreeTotientDefectNat
    oddSquarefreeRecipNat
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdIcc : d ∈ Finset.Icc (1 : ℕ) Y := (Finset.mem_filter.mp hd).1
  have hd_pos_nat : 0 < d := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdIcc).1
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos_nat
  have htot_le_nat : Nat.totient d ≤ d := Nat.totient_le d
  have hsub_cast :
      ((d - Nat.totient d : ℕ) : ℝ) =
        (d : ℝ) - (Nat.totient d : ℝ) := by
    exact Nat.cast_sub htot_le_nat
  calc
    (Nat.totient d : ℝ) / (d : ℝ) ^ 2 +
        ((d - Nat.totient d : ℕ) : ℝ) / (d : ℝ) ^ 2
        = (1 : ℝ) / (d : ℝ) := by
          rw [hsub_cast]
          field_simp [hd_pos.ne']
          ring

theorem odd_of_dvd_odd {a n : ℕ} (hn : Odd n) (ha : a ∣ n) : Odd a := by
  have hn_coprime : Nat.Coprime 2 n := by simpa using hn
  have ha_coprime : Nat.Coprime 2 a := hn_coprime.coprime_dvd_right ha
  simpa using ha_coprime

/-- Write an odd `n ≤ Y` as `n = b²a` with `a` odd and squarefree, and use
`∑_{b ≤ Y} 1/b² ≤ 2`. -/
theorem oddRecipNat_le_two_mul_oddSquarefreeRecipNat (Y : ℕ) :
    oddRecipNat Y ≤ 2 * oddSquarefreeRecipNat Y := by
  classical
  let base : Finset ℕ := (Finset.Icc (1 : ℕ) Y).filter (fun n => Odd n)
  let sfSet : Finset ℕ := oddSquarefreeEulerWitnessNat Y
  let sqSet : Finset ℕ := Finset.Icc (1 : ℕ) Y
  let F : ℕ → ℕ × ℕ := fun n => (sfPartForCoprimeLower n, sqPartForCoprimeLower n)
  let G : ℕ × ℕ → ℝ := fun p => ((1 : ℝ) / (p.1 : ℝ)) * (((p.2 : ℝ) ^ 2)⁻¹)
  have hF_mem : ∀ n ∈ base, F n ∈ sfSet.product sqSet := by
    intro n hn
    have hnIcc : n ∈ Finset.Icc (1 : ℕ) Y := (Finset.mem_filter.mp hn).1
    have hnodd : Odd n := (Finset.mem_filter.mp hn).2
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hnIcc).1
    have hnle : n ≤ Y := (Finset.mem_Icc.mp hnIcc).2
    have hprod := (sfPartForCoprimeLower_spec n).1
    have hsf_dvd : sfPartForCoprimeLower n ∣ n := by
      refine ⟨sqPartForCoprimeLower n ^ 2, ?_⟩
      calc
        n = sqPartForCoprimeLower n ^ 2 * sfPartForCoprimeLower n := hprod.symm
        _ = sfPartForCoprimeLower n * sqPartForCoprimeLower n ^ 2 := by
          rw [Nat.mul_comm]
    have hsf_odd : Odd (sfPartForCoprimeLower n) :=
      odd_of_dvd_odd hnodd hsf_dvd
    change F n ∈ sfSet ×ˢ sqSet
    rw [Finset.mem_product]
    constructor
    · unfold sfSet oddSquarefreeEulerWitnessNat
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_Icc.mpr
          ⟨sfPartForCoprimeLower_pos hnpos,
            le_trans (sfPartForCoprimeLower_le_self hnpos) hnle⟩,
        ⟨(sfPartForCoprimeLower_spec n).2, hsf_odd⟩⟩
    · exact Finset.mem_Icc.mpr
        ⟨sqPartForCoprimeLower_pos hnpos,
          le_trans (sqPartForCoprimeLower_le_self hnpos) hnle⟩
  have hF_inj : ∀ n ∈ base, ∀ m ∈ base, F n = F m → n = m := by
    intro n _hn m _hm hnm
    have hnprod := (sfPartForCoprimeLower_spec n).1
    have hmprod := (sfPartForCoprimeLower_spec m).1
    have ha : sfPartForCoprimeLower n = sfPartForCoprimeLower m :=
      congrArg Prod.fst hnm
    have hb : sqPartForCoprimeLower n = sqPartForCoprimeLower m :=
      congrArg Prod.snd hnm
    rw [← hnprod, ← hmprod, ha, hb]
  have himage_eq :
      (∑ n ∈ base, (1 : ℝ) / (n : ℝ)) = ∑ p ∈ base.image F, G p := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro n hn
      have hnIcc : n ∈ Finset.Icc (1 : ℕ) Y := (Finset.mem_filter.mp hn).1
      have hnpos_nat : 0 < n :=
        lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hnIcc).1
      have hapos_nat : 0 < sfPartForCoprimeLower n :=
        sfPartForCoprimeLower_pos hnpos_nat
      have hbpos_nat : 0 < sqPartForCoprimeLower n :=
        sqPartForCoprimeLower_pos hnpos_nat
      have hapos : (sfPartForCoprimeLower n : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hapos_nat)
      have hbpos : (sqPartForCoprimeLower n : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hbpos_nat)
      have hprod := (sfPartForCoprimeLower_spec n).1
      have hcast :
          ((sqPartForCoprimeLower n ^ 2 * sfPartForCoprimeLower n : ℕ) : ℝ)
            = (sqPartForCoprimeLower n : ℝ) ^ 2 *
                (sfPartForCoprimeLower n : ℝ) := by
        norm_num [Nat.cast_mul, Nat.cast_pow]
      calc
        (1 : ℝ) / (n : ℝ)
            = (1 : ℝ) /
                ((sqPartForCoprimeLower n ^ 2 * sfPartForCoprimeLower n : ℕ) : ℝ) := by
              rw [hprod]
        _ = (1 : ℝ) /
              ((sqPartForCoprimeLower n : ℝ) ^ 2 *
                (sfPartForCoprimeLower n : ℝ)) := by
              rw [hcast]
        _ = ((1 : ℝ) / (sfPartForCoprimeLower n : ℝ)) *
              (((sqPartForCoprimeLower n : ℝ) ^ 2)⁻¹) := by
              field_simp [hapos, hbpos]
        _ = G (F n) := by simp [G, F]
    · intro n hn m hm hnm
      exact hF_inj n hn m hm hnm
  have himage_subset : base.image F ⊆ sfSet.product sqSet := by
    intro p hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨n, hn, rfl⟩
    exact hF_mem n hn
  have hnonneg_extra : ∀ p ∈ sfSet.product sqSet, p ∉ base.image F → 0 ≤ G p := by
    intro p _hp _
    unfold G
    exact mul_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg _))
      (inv_nonneg.mpr (sq_nonneg _))
  have himage_le_product :
      (∑ p ∈ base.image F, G p) ≤ ∑ p ∈ sfSet.product sqSet, G p :=
    Finset.sum_le_sum_of_subset_of_nonneg himage_subset hnonneg_extra
  have hproduct_eq :
      (∑ p ∈ sfSet.product sqSet, G p)
        = (∑ a ∈ sfSet, (1 : ℝ) / (a : ℝ)) *
            (∑ b ∈ sqSet, ((b : ℝ) ^ 2)⁻¹) := by
    change (∑ p ∈ sfSet ×ˢ sqSet, G p) = _
    rw [Finset.sum_product]
    unfold G
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [Finset.mul_sum]
  have hodd_eq : oddRecipNat Y = ∑ n ∈ base, (1 : ℝ) / (n : ℝ) := by
    rfl
  have hsquares := square_recip_sum_le_two_for_coprime_lower Y
  have hodd_sf_nonneg : 0 ≤ oddSquarefreeRecipNat Y :=
    oddSquarefreeRecipNat_nonneg Y
  have hproduct_le :
      (∑ a ∈ sfSet, (1 : ℝ) / (a : ℝ)) *
          (∑ b ∈ sqSet, ((b : ℝ) ^ 2)⁻¹)
        ≤ oddSquarefreeRecipNat Y * 2 := by
    have hsf_eq : (∑ a ∈ sfSet, (1 : ℝ) / (a : ℝ)) = oddSquarefreeRecipNat Y := by
      rfl
    have hsq_eq :
        (∑ b ∈ sqSet, ((b : ℝ) ^ 2)⁻¹)
          = ∑ b ∈ Finset.Icc (1 : ℕ) Y, ((b : ℝ) ^ 2)⁻¹ := by
      rfl
    rw [hsf_eq, hsq_eq]
    exact mul_le_mul_of_nonneg_left hsquares hodd_sf_nonneg
  calc
    oddRecipNat Y = ∑ n ∈ base, (1 : ℝ) / (n : ℝ) := hodd_eq
    _ = ∑ p ∈ base.image F, G p := himage_eq
    _ ≤ ∑ p ∈ sfSet.product sqSet, G p := himage_le_product
    _ = (∑ a ∈ sfSet, (1 : ℝ) / (a : ℝ)) *
          (∑ b ∈ sqSet, ((b : ℝ) ^ 2)⁻¹) := hproduct_eq
    _ ≤ oddSquarefreeRecipNat Y * 2 := hproduct_le
    _ = 2 * oddSquarefreeRecipNat Y := by ring

theorem half_oddRecipNat_le_oddSquarefreeRecipNat (Y : ℕ) :
    (1 / 2 : ℝ) * oddRecipNat Y ≤ oddSquarefreeRecipNat Y := by
  have h := oddRecipNat_le_two_mul_oddSquarefreeRecipNat Y
  nlinarith

/-- `∑_{n ≤ 2^k, n odd} 1/n ≫ log 2^k`, using the odd numbers `2n - 1` with
`n ≤ 2^{k-1}`. -/
theorem oddRecipNat_dyadic_log_lower :
    ∃ c > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      c * Real.log ((2 ^ k : ℕ) : ℝ) ≤ oddRecipNat (2 ^ k) := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro k hk
  let H : ℕ := 2 ^ (k - 1)
  let T : Finset ℕ := (Finset.Icc (1 : ℕ) H).image (fun n => 2 * n - 1)
  have hk_eq : k = (k - 1) + 1 := by omega
  have htwoH : 2 * H = 2 ^ k := by
    calc
      2 * H = 2 * 2 ^ (k - 1) := by rfl
      _ = 2 ^ k := by
        rw [hk_eq]
        simp [pow_succ, Nat.mul_comm]
  have hT_subset :
      T ⊆ (Finset.Icc (1 : ℕ) (2 ^ k)).filter (fun n => Odd n) := by
    intro p hp
    dsimp [T] at hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨n, hn, rfl⟩
    have hnlo : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnhi : n ≤ H := (Finset.mem_Icc.mp hn).2
    have hle_twoH : 2 * n ≤ 2 * H := Nat.mul_le_mul_left 2 hnhi
    have hle_pow : 2 * n ≤ 2 ^ k := by simpa [htwoH] using hle_twoH
    have hodd : Odd (2 * n - 1) := by
      exact ⟨n - 1, by omega⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, hodd⟩
  have hT_sum_le :
      (∑ p ∈ T, (1 : ℝ) / (p : ℝ)) ≤ oddRecipNat (2 ^ k) := by
    unfold oddRecipNat
    exact Finset.sum_le_sum_of_subset_of_nonneg hT_subset (by
      intro p _hp_big _hp_small
      exact div_nonneg zero_le_one (Nat.cast_nonneg p))
  have hT_sum_eq :
      (∑ p ∈ T, (1 : ℝ) / (p : ℝ)) =
        ∑ n ∈ Finset.Icc (1 : ℕ) H, (1 : ℝ) / ((2 * n - 1 : ℕ) : ℝ) := by
    dsimp [T]
    rw [Finset.sum_image]
    intro a ha b hb hab
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    dsimp only at hab
    omega
  have hharm_eq :
      ((harmonic H : ℚ) : ℝ) = ∑ n ∈ Finset.Icc (1 : ℕ) H, (1 : ℝ) / (n : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    simp_rw [one_div]
  have hhalf_harm_le_T :
      (1 / 2 : ℝ) * ((harmonic H : ℚ) : ℝ)
        ≤ ∑ p ∈ T, (1 : ℝ) / (p : ℝ) := by
    rw [hharm_eq, Finset.mul_sum, hT_sum_eq]
    apply Finset.sum_le_sum
    intro n hn
    have hnlo : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnpos_nat : 0 < n := by omega
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos_nat
    have hden_pos_nat : 0 < 2 * n - 1 := by omega
    have hden_pos : (0 : ℝ) < ((2 * n - 1 : ℕ) : ℝ) := by
      exact_mod_cast hden_pos_nat
    have hden_le_nat : 2 * n - 1 ≤ 2 * n := by omega
    have hden_le : (((2 * n - 1 : ℕ) : ℝ)) ≤ (((2 * n : ℕ) : ℝ)) := by
      exact_mod_cast hden_le_nat
    calc
      (1 / 2 : ℝ) * ((1 : ℝ) / (n : ℝ))
          = (1 : ℝ) / (((2 * n : ℕ) : ℝ)) := by
            push_cast
            field_simp [hnpos.ne']
      _ ≤ (1 : ℝ) / (((2 * n - 1 : ℕ) : ℝ)) :=
            one_div_le_one_div_of_le hden_pos hden_le
  have hH_nonneg : 0 ≤ ((H : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlogH_le_harm :
      Real.log ((H : ℕ) : ℝ) ≤ ((harmonic H : ℚ) : ℝ) := by
    have h := log_le_harmonic_floor ((H : ℕ) : ℝ) hH_nonneg
    have hfloor : ⌊((H : ℕ) : ℝ)⌋₊ = H := Nat.floor_natCast H
    rw [hfloor] at h
    simpa using h
  have hlog2_nonneg : 0 ≤ Real.log (2 : ℝ) :=
    Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have hlogH :
      Real.log ((H : ℕ) : ℝ) = ((k - 1 : ℕ) : ℝ) * Real.log (2 : ℝ) := by
    dsimp [H]
    norm_num [Nat.cast_pow, Real.log_pow]
  have hlogK :
      Real.log ((2 ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log (2 : ℝ) := by
    norm_num [Nat.cast_pow, Real.log_pow]
  have hhalf_logK_le_logH :
      (1 / 2 : ℝ) * Real.log ((2 ^ k : ℕ) : ℝ)
        ≤ Real.log ((H : ℕ) : ℝ) := by
    have hcast_sub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      norm_num
    have hcoef : (1 / 2 : ℝ) * (k : ℝ) ≤ (k : ℝ) - 1 := by
      have hk_real : (2 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    rw [hlogH, hlogK, hcast_sub]
    nlinarith [hcoef, hlog2_nonneg]
  calc
    (1 / 4 : ℝ) * Real.log ((2 ^ k : ℕ) : ℝ)
        ≤ (1 / 2 : ℝ) * Real.log ((H : ℕ) : ℝ) := by nlinarith
    _ ≤ (1 / 2 : ℝ) * ((harmonic H : ℚ) : ℝ) := by nlinarith
    _ ≤ ∑ p ∈ T, (1 : ℝ) / (p : ℝ) := hhalf_harm_le_T
    _ ≤ oddRecipNat (2 ^ k) := hT_sum_le

theorem oddSquarefreeRecipNat_dyadic_log_lower :
    ∃ c > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      c * Real.log ((2 ^ k : ℕ) : ℝ) ≤ oddSquarefreeRecipNat (2 ^ k) := by
  rcases oddRecipNat_dyadic_log_lower with ⟨c, hc, hodd⟩
  refine ⟨c / 2, half_pos hc, ?_⟩
  intro k hk
  have hodd_lower := hodd k hk
  have hhalf := half_oddRecipNat_le_oddSquarefreeRecipNat (2 ^ k)
  calc
    (c / 2) * Real.log ((2 ^ k : ℕ) : ℝ)
        ≤ (1 / 2 : ℝ) * oddRecipNat (2 ^ k) := by nlinarith
    _ ≤ oddSquarefreeRecipNat (2 ^ k) := hhalf

theorem oddSquarefreeRecipNat_le_harmonic (Y : ℕ) :
    oddSquarefreeRecipNat Y ≤ ((harmonic Y : ℚ) : ℝ) := by
  classical
  unfold oddSquarefreeRecipNat oddSquarefreeEulerWitnessNat
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  simp_rw [one_div]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset _ _
  · intro n _hn_big _hn_small
    exact inv_nonneg.mpr (Nat.cast_nonneg n)

theorem oddSquarefreeRecipNat_dyadic_log_upper :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      oddSquarefreeRecipNat (2 ^ k) ≤ C * Real.log ((2 ^ k : ℕ) : ℝ) := by
  refine ⟨1 + (Real.log 4)⁻¹, ?_, ?_⟩
  · exact add_pos zero_lt_one (inv_pos.mpr (Real.log_pos (by norm_num : (1 : ℝ) < 4)))
  intro k hk
  have hN_ge_one : (1 : ℝ) ≤ (((2 ^ k : ℕ) : ℝ)) := by
    exact_mod_cast (by
      have hpos : 0 < 2 ^ k := pow_pos (by norm_num : (0 : ℕ) < 2) k
      omega)
  have hharm_upper :
      ((harmonic (2 ^ k) : ℚ) : ℝ) ≤
        1 + Real.log (((2 ^ k : ℕ) : ℝ)) := by
    have h := harmonic_floor_le_one_add_log (((2 ^ k : ℕ) : ℝ)) hN_ge_one
    have hfloor : ⌊(((2 ^ k : ℕ) : ℝ))⌋₊ = 2 ^ k :=
      Nat.floor_natCast (2 ^ k)
    rw [hfloor] at h
    simpa using h
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have hfour_le_nat : 4 ≤ 2 ^ k := by
    simpa using Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2) hk
  have hfour_le : (4 : ℝ) ≤ (((2 ^ k : ℕ) : ℝ)) := by
    exact_mod_cast hfour_le_nat
  have hlog4_le_logK :
      Real.log 4 ≤ Real.log (((2 ^ k : ℕ) : ℝ)) :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 4) hfour_le
  have hone_le_inv_log4_mul_logK :
      (1 : ℝ) ≤ (Real.log 4)⁻¹ * Real.log (((2 ^ k : ℕ) : ℝ)) := by
    calc
      (1 : ℝ) = (Real.log 4)⁻¹ * Real.log 4 := by
        field_simp [ne_of_gt hlog4_pos]
      _ ≤ (Real.log 4)⁻¹ * Real.log (((2 ^ k : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog4_le_logK (inv_nonneg.mpr hlog4_pos.le)
  calc
    oddSquarefreeRecipNat (2 ^ k)
        ≤ ((harmonic (2 ^ k) : ℚ) : ℝ) :=
          oddSquarefreeRecipNat_le_harmonic (2 ^ k)
    _ ≤ 1 + Real.log (((2 ^ k : ℕ) : ℝ)) := hharm_upper
    _ ≤ (1 + (Real.log 4)⁻¹) * Real.log (((2 ^ k : ℕ) : ℝ)) := by
          calc
            1 + Real.log (((2 ^ k : ℕ) : ℝ))
                ≤ (Real.log 4)⁻¹ * Real.log (((2 ^ k : ℕ) : ℝ)) +
                    Real.log (((2 ^ k : ℕ) : ℝ)) :=
                  add_le_add_left hone_le_inv_log4_mul_logK _
            _ = (1 + (Real.log 4)⁻¹) * Real.log (((2 ^ k : ℕ) : ℝ)) := by
                  ring

/-- If `∑ φ(d)/d² ≥ δ ∑ 1/d` over the odd squarefree `d ≤ 2^k`, then
`∑ φ(d)/d² ≫ log 2^k`. -/
theorem oddSqfTotient_dyadic_lower_of_recip
    (hcmp : ∃ δ > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      δ * oddSquarefreeRecipNat (2 ^ k)
        ≤ ∑ d ∈ oddSquarefreeEulerWitnessNat (2 ^ k),
            (Nat.totient d : ℝ) / (d : ℝ) ^ 2) :
    ∃ c > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      c * Real.log ((2 ^ k : ℕ) : ℝ)
        ≤ ∑ d ∈ oddSquarefreeEulerWitnessNat (2 ^ k),
            (Nat.totient d : ℝ) / (d : ℝ) ^ 2 := by
  rcases oddSquarefreeRecipNat_dyadic_log_lower with ⟨c, hc, hrecip⟩
  rcases hcmp with ⟨δ, hδ, hcmp⟩
  refine ⟨δ * c, mul_pos hδ hc, ?_⟩
  intro k hk
  have hrec := hrecip k hk
  have hweighted := hcmp k hk
  calc
    (δ * c) * Real.log ((2 ^ k : ℕ) : ℝ)
        ≤ δ * oddSquarefreeRecipNat (2 ^ k) := by nlinarith
    _ ≤ ∑ d ∈ oddSquarefreeEulerWitnessNat (2 ^ k),
            (Nat.totient d : ℝ) / (d : ℝ) ^ 2 := hweighted

/-- Over the odd squarefree `d ≤ 2^k`, `∑ φ(d)/d² ≫ log 2^k` holds if and only if
`∑ φ(d)/d² ≫ ∑ 1/d`, because `∑ 1/d ≍ log 2^k`. -/
theorem oddSqfTotient_dyadic_lower_iff_recip :
    (∃ c > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      c * Real.log ((2 ^ k : ℕ) : ℝ)
        ≤ ∑ d ∈ oddSquarefreeEulerWitnessNat (2 ^ k),
            (Nat.totient d : ℝ) / (d : ℝ) ^ 2) ↔
    (∃ δ > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      δ * oddSquarefreeRecipNat (2 ^ k)
        ≤ ∑ d ∈ oddSquarefreeEulerWitnessNat (2 ^ k),
            (Nat.totient d : ℝ) / (d : ℝ) ^ 2) := by
  constructor
  · intro hdy
    rcases hdy with ⟨c, hc, hdy⟩
    rcases oddSquarefreeRecipNat_dyadic_log_upper with ⟨C, hC, hupper⟩
    refine ⟨c / C, div_pos hc hC, ?_⟩
    intro k hk
    have hU := hupper k hk
    have hD := hdy k hk
    have hcoef_nonneg : 0 ≤ c / C := div_nonneg hc.le hC.le
    calc
      (c / C) * oddSquarefreeRecipNat (2 ^ k)
          ≤ (c / C) * (C * Real.log ((2 ^ k : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hU hcoef_nonneg
      _ = c * Real.log ((2 ^ k : ℕ) : ℝ) := by
            field_simp [ne_of_gt hC]
      _ ≤ ∑ d ∈ oddSquarefreeEulerWitnessNat (2 ^ k),
              (Nat.totient d : ℝ) / (d : ℝ) ^ 2 := hD
  · exact
      oddSqfTotient_dyadic_lower_of_recip

theorem oddSquarefreeTotientNat_recip_density_iff_defect_gap :
    (∃ δ > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      δ * oddSquarefreeRecipNat (2 ^ k)
        ≤ oddSquarefreeTotientNat (2 ^ k)) ↔
    (∃ ε > (0 : ℝ), ε < 1 ∧ ∀ k : ℕ, 2 ≤ k →
      oddSquarefreeTotientDefectNat (2 ^ k)
        ≤ (1 - ε) * oddSquarefreeRecipNat (2 ^ k)) := by
  constructor
  · rintro ⟨δ, hδ, hdensity⟩
    let ε : ℝ := δ / (δ + 1)
    have hden_pos : 0 < δ + 1 := by linarith
    have hεpos : 0 < ε := div_pos hδ hden_pos
    have hεlt : ε < 1 := by
      dsimp [ε]
      rw [div_lt_one hden_pos]
      linarith
    have hεleδ : ε ≤ δ := by
      dsimp [ε]
      rw [div_le_iff₀ hden_pos]
      nlinarith [sq_nonneg δ]
    refine ⟨ε, hεpos, hεlt, ?_⟩
    intro k hk
    have hrecip_nonneg : 0 ≤ oddSquarefreeRecipNat (2 ^ k) :=
      oddSquarefreeRecipNat_nonneg (2 ^ k)
    have htot_ε :
        ε * oddSquarefreeRecipNat (2 ^ k)
          ≤ oddSquarefreeTotientNat (2 ^ k) :=
      (mul_le_mul_of_nonneg_right hεleδ hrecip_nonneg).trans
        (hdensity k hk)
    have hdecomp :=
      oddSquarefreeTotientNat_add_defect_eq_recipNat (2 ^ k)
    nlinarith
  · rintro ⟨ε, hε, _hεlt, hdefect⟩
    refine ⟨ε, hε, ?_⟩
    intro k hk
    have hdecomp :=
      oddSquarefreeTotientNat_add_defect_eq_recipNat (2 ^ k)
    have hdef := hdefect k hk
    nlinarith

theorem oddSqfTotient_dyadic_lower_iff_defect :
    (∃ c > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      c * Real.log ((2 ^ k : ℕ) : ℝ)
        ≤ ∑ d ∈ oddSquarefreeEulerWitnessNat (2 ^ k),
            (Nat.totient d : ℝ) / (d : ℝ) ^ 2) ↔
    (∃ ε > (0 : ℝ), ε < 1 ∧ ∀ k : ℕ, 2 ≤ k →
      oddSquarefreeTotientDefectNat (2 ^ k)
        ≤ (1 - ε) * oddSquarefreeRecipNat (2 ^ k)) := by
  rw [
    oddSqfTotient_dyadic_lower_iff_recip]
  simpa [oddSquarefreeTotientNat] using
    oddSquarefreeTotientNat_recip_density_iff_defect_gap

theorem oddSqfTotient_dyadic_lower_iff_defectProd :
    (∃ c > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      c * Real.log ((2 ^ k : ℕ) : ℝ)
        ≤ ∑ d ∈ oddSquarefreeEulerWitnessNat (2 ^ k),
            (Nat.totient d : ℝ) / (d : ℝ) ^ 2) ↔
    (∃ ε > (0 : ℝ), ε < 1 ∧ ∀ k : ℕ, 2 ≤ k →
      oddSquarefreeTotientDefectProductNat (2 ^ k)
        ≤ (1 - ε) * oddSquarefreeRecipNat (2 ^ k)) := by
  simpa [oddSquarefreeTotientDefectProductNat_eq_defectNat] using
    oddSqfTotient_dyadic_lower_iff_defect

theorem one_sub_prod_le_sum_one_sub {α : Type} [DecidableEq α]
    (s : Finset α) (f : α → ℝ)
    (h0 : ∀ x ∈ s, 0 ≤ f x) (h1 : ∀ x ∈ s, f x ≤ 1) :
    1 - ∏ x ∈ s, f x ≤ ∑ x ∈ s, (1 - f x) := by
  classical
  revert h0 h1
  refine Finset.induction_on s ?empty ?insert
  · intro _h0 _h1
    simp
  · intro a s has ih h0 h1
    rw [Finset.prod_insert has, Finset.sum_insert has]
    have h0s : ∀ x ∈ s, 0 ≤ f x := by
      intro x hx
      exact h0 x (Finset.mem_insert_of_mem hx)
    have h1s : ∀ x ∈ s, f x ≤ 1 := by
      intro x hx
      exact h1 x (Finset.mem_insert_of_mem hx)
    have hprod_le_one : ∏ x ∈ s, f x ≤ 1 := by
      calc
        ∏ x ∈ s, f x ≤ ∏ _x ∈ s, (1 : ℝ) := by
          exact Finset.prod_le_prod h0s h1s
        _ = 1 := by simp
    have hfa_le_one : f a ≤ 1 := h1 a (Finset.mem_insert_self a s)
    have hsplit :
        1 - f a * (∏ x ∈ s, f x)
          ≤ (1 - f a) + (1 - ∏ x ∈ s, f x) := by
      nlinarith [sub_nonneg.mpr hfa_le_one, sub_nonneg.mpr hprod_le_one]
    calc
      1 - f a * (∏ x ∈ s, f x)
          ≤ (1 - f a) + (1 - ∏ x ∈ s, f x) := hsplit
      _ ≤ (1 - f a) + ∑ x ∈ s, (1 - f x) :=
          add_le_add_right (ih h0s h1s) _

theorem one_sub_totientPrimeFactorProduct_le_primeFactor_recip_sum (a : ℕ) :
    1 - totientPrimeFactorProduct a ≤ ∑ p ∈ a.primeFactors, (p : ℝ)⁻¹ := by
  classical
  unfold totientPrimeFactorProduct
  have h0 : ∀ p ∈ a.primeFactors, 0 ≤ (1 : ℝ) - (p : ℝ)⁻¹ := by
    intro p hp
    have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hpOne : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpPrime.one_lt.le
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hpOne)
  have h1 : ∀ p ∈ a.primeFactors, (1 : ℝ) - (p : ℝ)⁻¹ ≤ 1 := by
    intro p _hp
    have hinv_nonneg : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
    linarith
  simpa using
    one_sub_prod_le_sum_one_sub a.primeFactors
      (fun p : ℕ => (1 : ℝ) - (p : ℝ)⁻¹) h0 h1

/-- The terms with `p ∣ a` contribute at most `p⁻² ∑ 1/a`: the map `a ↦ a/p` is injective
and `1/(p a) = p⁻² · 1/(a/p)`. -/
theorem oddSquarefree_primeFactor_slice_sum_le (Y p : ℕ) :
    (∑ a ∈ (oddSquarefreeEulerWitnessNat Y).filter
        (fun a => p ∈ a.primeFactors),
        (1 : ℝ) / ((p : ℝ) * (a : ℝ)))
      ≤ ((p : ℝ) ^ 2)⁻¹ * oddSquarefreeRecipNat Y := by
  classical
  let slice :=
    (oddSquarefreeEulerWitnessNat Y).filter (fun a => p ∈ a.primeFactors)
  let F : ℕ → ℕ := fun a => a / p
  have hF_inj : ∀ a ∈ slice, ∀ b ∈ slice, F a = F b → a = b := by
    intro a ha b hb hF
    change a / p = b / p at hF
    have hpa : p ∈ a.primeFactors := (Finset.mem_filter.mp ha).2
    have hpb : p ∈ b.primeFactors := (Finset.mem_filter.mp hb).2
    have hpda : p ∣ a := Nat.dvd_of_mem_primeFactors hpa
    have hpdb : p ∣ b := Nat.dvd_of_mem_primeFactors hpb
    calc
      a = p * (a / p) := by rw [Nat.mul_div_cancel' hpda]
      _ = p * (b / p) := by rw [hF]
      _ = b := by rw [Nat.mul_div_cancel' hpdb]
  have hF_mem : ∀ a ∈ slice, F a ∈ oddSquarefreeEulerWitnessNat Y := by
    intro a ha
    have haS : a ∈ oddSquarefreeEulerWitnessNat Y := (Finset.mem_filter.mp ha).1
    have hpa : p ∈ a.primeFactors := (Finset.mem_filter.mp ha).2
    have hpda : p ∣ a := Nat.dvd_of_mem_primeFactors hpa
    have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hpa
    have haIcc : a ∈ Finset.Icc (1 : ℕ) Y := (Finset.mem_filter.mp haS).1
    have hasqf : Squarefree a := (Finset.mem_filter.mp haS).2.1
    have haodd : Odd a := (Finset.mem_filter.mp haS).2.2
    have hapos_nat : 0 < a :=
      lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp haIcc).1
    have hFpos : 0 < F a :=
      Nat.div_pos (Nat.le_of_dvd hapos_nat hpda) hpPrime.pos
    have hFle : F a ≤ Y := by
      calc
        F a ≤ a := Nat.div_le_self a p
        _ ≤ Y := (Finset.mem_Icc.mp haIcc).2
    have hFsqf : Squarefree (F a) :=
      hasqf.squarefree_of_dvd (Nat.div_dvd_of_dvd hpda)
    have hFodd : Odd (F a) :=
      odd_of_dvd_odd haodd (Nat.div_dvd_of_dvd hpda)
    rw [oddSquarefreeEulerWitnessNat, Finset.mem_filter]
    exact ⟨Finset.mem_Icc.mpr ⟨hFpos, hFle⟩, ⟨hFsqf, hFodd⟩⟩
  have himage_eq :
      (∑ a ∈ slice, (1 : ℝ) / ((p : ℝ) * (a : ℝ)))
        = ∑ m ∈ slice.image F, ((p : ℝ) ^ 2)⁻¹ * ((1 : ℝ) / (m : ℝ)) := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro a ha
      have hpa : p ∈ a.primeFactors := (Finset.mem_filter.mp ha).2
      have hpda : p ∣ a := Nat.dvd_of_mem_primeFactors hpa
      have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hpa
      have haS : a ∈ oddSquarefreeEulerWitnessNat Y := (Finset.mem_filter.mp ha).1
      have haIcc : a ∈ Finset.Icc (1 : ℕ) Y := (Finset.mem_filter.mp haS).1
      have hapos_nat : 0 < a :=
        lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp haIcc).1
      have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
      have hFpos_nat : 0 < F a :=
        Nat.div_pos (Nat.le_of_dvd hapos_nat hpda) hpPrime.pos
      have hF_pos : (0 : ℝ) < (F a : ℝ) := by exact_mod_cast hFpos_nat
      have ha_eq : (a : ℝ) = (p : ℝ) * (F a : ℝ) := by
        have hnat : a = p * (a / p) := by rw [Nat.mul_div_cancel' hpda]
        exact_mod_cast hnat
      rw [ha_eq]
      field_simp [ne_of_gt hp_pos, ne_of_gt hF_pos]
    · intro a ha b hb h
      exact hF_inj a ha b hb h
  have himage_subset : slice.image F ⊆ oddSquarefreeEulerWitnessNat Y := by
    intro m hm
    rw [Finset.mem_image] at hm
    rcases hm with ⟨a, ha, rfl⟩
    exact hF_mem a ha
  have hnonneg_extra :
      ∀ m ∈ oddSquarefreeEulerWitnessNat Y, m ∉ slice.image F →
        0 ≤ ((p : ℝ) ^ 2)⁻¹ * ((1 : ℝ) / (m : ℝ)) := by
    intro m _hm _hnot
    exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
      (div_nonneg zero_le_one (Nat.cast_nonneg m))
  have himage_le :
      (∑ m ∈ slice.image F, ((p : ℝ) ^ 2)⁻¹ * ((1 : ℝ) / (m : ℝ)))
        ≤ ∑ m ∈ oddSquarefreeEulerWitnessNat Y,
            ((p : ℝ) ^ 2)⁻¹ * ((1 : ℝ) / (m : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg himage_subset hnonneg_extra
  calc
    (∑ a ∈ (oddSquarefreeEulerWitnessNat Y).filter
        (fun a => p ∈ a.primeFactors),
        (1 : ℝ) / ((p : ℝ) * (a : ℝ)))
        = ∑ m ∈ slice.image F, ((p : ℝ) ^ 2)⁻¹ * ((1 : ℝ) / (m : ℝ)) := by
          simpa [slice] using himage_eq
    _ ≤ ∑ m ∈ oddSquarefreeEulerWitnessNat Y,
          ((p : ℝ) ^ 2)⁻¹ * ((1 : ℝ) / (m : ℝ)) := himage_le
    _ = ((p : ℝ) ^ 2)⁻¹ * oddSquarefreeRecipNat Y := by
          rw [← Finset.mul_sum]
          rfl

theorem square_tail_from_three_le_half (Y : ℕ) :
    (∑ p ∈ Finset.Ioc (2 : ℕ) Y, ((p : ℝ) ^ 2)⁻¹) ≤ (1 / 2 : ℝ) := by
  by_cases hY : 2 ≤ Y
  · have h :=
      (sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 2) (n := Y)
        (by norm_num) hY)
    have hnonneg : (0 : ℝ) ≤ (Y : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg Y)
    nlinarith
  · have hempty : Finset.Ioc (2 : ℕ) Y = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      exact hY (le_trans (Finset.mem_Ioc.mp hp).1.le (Finset.mem_Ioc.mp hp).2)
    rw [hempty, Finset.sum_empty]
    norm_num

/-- The prime `2` contributes at most `1/4`, and the other primes at most
`∑_{n ≥ 3} 1/n² ≤ 1/2`. -/
theorem prime_square_recip_sum_le_three_fourths (s : Finset ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p) :
    (∑ p ∈ s, ((p : ℝ) ^ 2)⁻¹) ≤ (3 / 4 : ℝ) := by
  classical
  let f : ℕ → ℝ := fun p => ((p : ℝ) ^ 2)⁻¹
  let tail : Finset ℕ := s.filter (fun p => p ≠ 2)
  have hsplit :
      (∑ p ∈ s, f p)
        = (∑ p ∈ s.filter (fun p => p = 2), f p) + ∑ p ∈ tail, f p := by
    simpa [tail, f] using
      (Finset.sum_filter_add_sum_filter_not (s := s)
        (p := fun p : ℕ => p = 2) (f := f)).symm
  have htwo : (∑ p ∈ s.filter (fun p => p = 2), f p) ≤ (1 / 4 : ℝ) := by
    calc
      (∑ p ∈ s.filter (fun p => p = 2), f p)
          ≤ ∑ p ∈ ({2} : Finset ℕ), f p := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?subset ?nonneg
            · intro p hp
              rw [Finset.mem_singleton]
              exact (Finset.mem_filter.mp hp).2
            · intro p _hp_big _hp_small
              exact inv_nonneg.mpr (sq_nonneg _)
      _ = (1 / 4 : ℝ) := by
            norm_num [f]
  have htail : (∑ p ∈ tail, f p) ≤ (1 / 2 : ℝ) := by
    by_cases hne : tail.Nonempty
    · let Y := tail.max' hne
      have hsubset : tail ⊆ Finset.Ioc (2 : ℕ) Y := by
        intro p hp
        have hp_s : p ∈ s := (Finset.mem_filter.mp hp).1
        have hp_ne : p ≠ 2 := (Finset.mem_filter.mp hp).2
        have hp_prime : Nat.Prime p := hs p hp_s
        have hp_two_le : 2 ≤ p := hp_prime.two_le
        have hp_gt_two : 2 < p := by omega
        have hp_le_Y : p ≤ Y := Finset.le_max' tail p hp
        exact Finset.mem_Ioc.mpr ⟨hp_gt_two, hp_le_Y⟩
      calc
        (∑ p ∈ tail, f p)
            ≤ ∑ p ∈ Finset.Ioc (2 : ℕ) Y, f p := by
              refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
              intro p _hp_big _hp_small
              exact inv_nonneg.mpr (sq_nonneg _)
        _ ≤ (1 / 2 : ℝ) := by
              simpa [f] using square_tail_from_three_le_half Y
    · have hempty : tail = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [hempty]
      norm_num
  rw [hsplit]
  nlinarith

theorem prime_square_euler_product_ge_quarter (s : Finset ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p) :
    (1 / 4 : ℝ) ≤ ∏ p ∈ s, (1 - ((p : ℝ) ^ 2)⁻¹) := by
  classical
  let f : ℕ → ℝ := fun p => (1 : ℝ) - ((p : ℝ) ^ 2)⁻¹
  have h0 : ∀ p ∈ s, 0 ≤ f p := by
    intro p hp
    have hp_prime : Nat.Prime p := hs p hp
    have hp_one : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.one_lt.le
    have hsq_one : (1 : ℝ) ≤ (p : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((p : ℝ) - 1)]
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hsq_one)
  have h1 : ∀ p ∈ s, f p ≤ 1 := by
    intro p _hp
    have hinv_nonneg : 0 ≤ ((p : ℝ) ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
    dsimp [f]
    linarith
  have hdefect :=
    one_sub_prod_le_sum_one_sub s f h0 h1
  have hsum :=
    prime_square_recip_sum_le_three_fourths s hs
  have hdefect' :
      1 - ∏ p ∈ s, (1 - ((p : ℝ) ^ 2)⁻¹)
        ≤ ∑ p ∈ s, ((p : ℝ) ^ 2)⁻¹ := by
    simpa [f] using hdefect
  nlinarith

theorem roughModulus_square_euler_product_ge_quarter (X : ℝ) :
    (1 / 4 : ℝ) ≤
      ∏ p ∈ (roughModulus X).primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹) := by
  exact prime_square_euler_product_ge_quarter (roughModulus X).primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp)

/-- `∑ (1 - φ(a)/a)/a ≤ (1/2) ∑ 1/a` over the odd squarefree `a ≤ Y`: bound
`1 - ∏_{p ∣ a} (1 - 1/p)` by `∑_{p ∣ a} 1/p`, interchange the sums, and use
`∑_{p ≥ 3} 1/p² ≤ 1/2`. -/
theorem oddSquarefreeTotientDefectProductNat_le_half_recip (Y : ℕ) :
    oddSquarefreeTotientDefectProductNat Y
      ≤ (1 / 2 : ℝ) * oddSquarefreeRecipNat Y := by
  classical
  let S := oddSquarefreeEulerWitnessNat Y
  have hpoint :
      ∀ a ∈ S, (1 - totientPrimeFactorProduct a) / (a : ℝ)
        ≤ ∑ p ∈ a.primeFactors, (1 : ℝ) / ((p : ℝ) * (a : ℝ)) := by
    intro a ha
    have haIcc : a ∈ Finset.Icc (1 : ℕ) Y := (Finset.mem_filter.mp ha).1
    have hapos_nat : 0 < a :=
      lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp haIcc).1
    have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hapos_nat
    have hprod := one_sub_totientPrimeFactorProduct_le_primeFactor_recip_sum a
    have hdiv := div_le_div_of_nonneg_right hprod hapos.le
    calc
      (1 - totientPrimeFactorProduct a) / (a : ℝ)
          ≤ (∑ p ∈ a.primeFactors, (p : ℝ)⁻¹) / (a : ℝ) := hdiv
      _ = ∑ p ∈ a.primeFactors, (1 : ℝ) / ((p : ℝ) * (a : ℝ)) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro p _hp
          field_simp [ne_of_gt hapos]
  have hsum_point :
      oddSquarefreeTotientDefectProductNat Y
        ≤ ∑ a ∈ S, ∑ p ∈ a.primeFactors,
            (1 : ℝ) / ((p : ℝ) * (a : ℝ)) := by
    unfold oddSquarefreeTotientDefectProductNat
    apply Finset.sum_le_sum
    intro a ha
    exact hpoint a ha
  have hsubset_pf : ∀ a ∈ S, a.primeFactors ⊆ Finset.Ioc (2 : ℕ) Y := by
    intro a ha p hp
    have haIcc : a ∈ Finset.Icc (1 : ℕ) Y := (Finset.mem_filter.mp ha).1
    have haodd : Odd a := (Finset.mem_filter.mp ha).2.2
    have hapos_nat : 0 < a :=
      lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp haIcc).1
    have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ a := Nat.dvd_of_mem_primeFactors hp
    have hp_ne_two : p ≠ 2 := by
      intro hp2
      subst p
      have htwo_odd : Odd (2 : ℕ) := odd_of_dvd_odd haodd hpdvd
      exact (by norm_num : ¬ Odd (2 : ℕ)) htwo_odd
    have hp_gt_two : 2 < p := by
      have hp2le : 2 ≤ p := hpPrime.two_le
      omega
    have hp_le_a : p ≤ a := Nat.le_of_dvd hapos_nat hpdvd
    exact Finset.mem_Ioc.mpr ⟨hp_gt_two, le_trans hp_le_a (Finset.mem_Icc.mp haIcc).2⟩
  have hto_tail :
      (∑ a ∈ S, ∑ p ∈ a.primeFactors, (1 : ℝ) / ((p : ℝ) * (a : ℝ)))
        ≤ ∑ p ∈ Finset.Ioc (2 : ℕ) Y,
            ∑ a ∈ S.filter (fun a => p ∈ a.primeFactors),
              (1 : ℝ) / ((p : ℝ) * (a : ℝ)) := by
    calc
      (∑ a ∈ S, ∑ p ∈ a.primeFactors, (1 : ℝ) / ((p : ℝ) * (a : ℝ)))
          ≤ ∑ a ∈ S, ∑ p ∈ Finset.Ioc (2 : ℕ) Y,
              if p ∈ a.primeFactors then (1 : ℝ) / ((p : ℝ) * (a : ℝ)) else 0 := by
            apply Finset.sum_le_sum
            intro a ha
            have hsum_if :
                (∑ p ∈ a.primeFactors, (1 : ℝ) / ((p : ℝ) * (a : ℝ))) =
                  ∑ p ∈ a.primeFactors,
                    if p ∈ a.primeFactors then (1 : ℝ) / ((p : ℝ) * (a : ℝ))
                    else 0 := by
              apply Finset.sum_congr rfl
              intro p hp
              rw [if_pos hp]
            rw [hsum_if]
            exact Finset.sum_le_sum_of_subset_of_nonneg (hsubset_pf a ha) (by
              intro p _hpBig hpSmall
              rw [if_neg hpSmall])
      _ = ∑ p ∈ Finset.Ioc (2 : ℕ) Y, ∑ a ∈ S,
              if p ∈ a.primeFactors then (1 : ℝ) / ((p : ℝ) * (a : ℝ)) else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ p ∈ Finset.Ioc (2 : ℕ) Y,
            ∑ a ∈ S.filter (fun a => p ∈ a.primeFactors),
              (1 : ℝ) / ((p : ℝ) * (a : ℝ)) := by
            apply Finset.sum_congr rfl
            intro p _hp
            rw [Finset.sum_filter]
  have hslice_sum :
      (∑ p ∈ Finset.Ioc (2 : ℕ) Y,
            ∑ a ∈ S.filter (fun a => p ∈ a.primeFactors),
              (1 : ℝ) / ((p : ℝ) * (a : ℝ)))
        ≤ ∑ p ∈ Finset.Ioc (2 : ℕ) Y,
            ((p : ℝ) ^ 2)⁻¹ * oddSquarefreeRecipNat Y := by
    apply Finset.sum_le_sum
    intro p _hp
    simpa [S] using oddSquarefree_primeFactor_slice_sum_le Y p
  have htail :
      (∑ p ∈ Finset.Ioc (2 : ℕ) Y,
            ((p : ℝ) ^ 2)⁻¹ * oddSquarefreeRecipNat Y)
        ≤ (1 / 2 : ℝ) * oddSquarefreeRecipNat Y := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (square_tail_from_three_le_half Y)
      (oddSquarefreeRecipNat_nonneg Y)
  exact hsum_point.trans (hto_tail.trans (hslice_sum.trans htail))

theorem oddSquarefreeTotientDefectProductGapBound :
    OddSquarefreeTotientDefectProductGapBound := by
  refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
  intro k _hk
  convert oddSquarefreeTotientDefectProductNat_le_half_recip (2 ^ k) using 1
  norm_num

/-- `∑_{d ≤ 2^k, d odd squarefree} φ(d)/d² ≫ log 2^k`. -/
theorem oddSqfTotient_dyadic_lower :
    ∃ c > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      c * Real.log ((2 ^ k : ℕ) : ℝ)
        ≤ ∑ d ∈ oddSquarefreeEulerWitnessNat (2 ^ k),
            (Nat.totient d : ℝ) / (d : ℝ) ^ 2 := by
  exact (oddSqfTotient_dyadic_lower_iff_defectProd).mpr
    oddSquarefreeTotientDefectProductGapBound

theorem oddSquarefreeTotientNat_dyadic_lower_bound :
    ∃ c > (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      c * Real.log ((2 ^ k : ℕ) : ℝ)
        ≤ oddSquarefreeTotientNat (2 ^ k) := by
  simpa [oddSquarefreeTotientNat] using
    oddSqfTotient_dyadic_lower

/-! ## Lower bounds in Lemmas 3.3 and 6.4 -/

theorem oddSquarefreeTotientNat_le_sAvgPhi_of_le_floor_SScale
    (P : ErdosStraus.Params) (X : ℝ) {Z : ℕ}
    (hZ : Z ≤ ⌊ErdosStraus.SScale P X⌋₊) :
    oddSquarefreeTotientNat Z ≤ sAvgPhi P X := by
  classical
  unfold oddSquarefreeTotientNat oddSquarefreeEulerWitnessNat sAvgPhi
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    have hdIcc : d ∈ Finset.Icc (1 : ℕ) Z :=
      (Finset.mem_filter.mp hd).1
    have hsqf : Squarefree d := (Finset.mem_filter.mp hd).2.1
    have hd_le_Z : d ≤ Z := (Finset.mem_Icc.mp hdIcc).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp hdIcc).1, le_trans hd_le_Z hZ⟩,
        hsqf⟩
  · intro d _hdBig _hdSmall
    exact div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

/-- The lower bound in the first sum of Lemma 3.3: with `B = 2^⌊log₂ ⌊S⌋⌋`, the odd
squarefree `s ≤ B` alone give `∑ φ(s)/s² ≫ log B ≫ log S`. -/
theorem sAvgPhi_lower_log (P : ErdosStraus.Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      c * Real.log (ErdosStraus.SScale P X) ≤ sAvgPhi P X := by
  rcases oddSquarefreeTotientNat_dyadic_lower_bound with ⟨c, hc, hdy⟩
  refine ⟨c / 2,
    max 1 (Real.exp (Real.log 16 / P.η)), half_pos hc, ?_⟩
  intro X hX
  let S : ℝ := ErdosStraus.SScale P X
  let Z : ℕ := ⌊S⌋₊
  let k : ℕ := Nat.log 2 Z
  let B : ℕ := 2 ^ k
  have hXone : (1 : ℝ) ≤ X := le_trans (le_max_left _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hXexp : Real.exp (Real.log 16 / P.η) ≤ X :=
    le_trans (le_max_right _ _) hX
  have hlog_threshold :
      Real.log 16 / P.η ≤ Real.log X := by
    exact (Real.le_log_iff_exp_le hXpos).mpr hXexp
  have heta_pos : 0 < P.η := P.η_pos
  have hlogS_eq : Real.log S = P.η * Real.log X := by
    unfold S ErdosStraus.SScale
    rw [Real.log_rpow hXpos]
  have hlog16_le_logS : Real.log 16 ≤ Real.log S := by
    rw [hlogS_eq]
    have hmul := mul_le_mul_of_nonneg_left hlog_threshold heta_pos.le
    have hη_ne : P.η ≠ 0 := ne_of_gt heta_pos
    refine Eq.trans_le ?_ hmul
    field_simp [hη_ne]
  have hS_pos : 0 < S := by
    unfold S ErdosStraus.SScale
    exact Real.rpow_pos_of_pos hXpos P.η
  have hS_ge_sixteen : (16 : ℝ) ≤ S := by
    exact (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 16) hS_pos).mp
      hlog16_le_logS
  have hS_nonneg : 0 ≤ S := hS_pos.le
  have hZ_ge_four : 4 ≤ Z := by
    exact Nat.le_floor (by linarith : (4 : ℝ) ≤ S)
  have hZ_ne_zero : Z ≠ 0 := by omega
  have hB_le_Z : B ≤ Z := by
    exact Nat.pow_log_le_self 2 hZ_ne_zero
  have hk_ge_two : 2 ≤ k := by
    exact Nat.le_log_of_pow_le (by norm_num : 1 < 2)
      (by simpa [k] using hZ_ge_four)
  have hB_ge_four : 4 ≤ B := by
    exact le_trans (by simp : 4 ≤ 2 ^ (2 : ℕ))
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) hk_ge_two)
  have hB_pos_nat : 0 < B := by omega
  have hB_pos : 0 < (B : ℝ) := by exact_mod_cast hB_pos_nat
  have hB_ge_one_real : (1 : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ B)
  have hZ_lt_pow_succ : Z < 2 ^ (k + 1) := by
    exact Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) Z
  have hZ_le_twoB : Z ≤ 2 * B := by
    have hpow_eq : 2 ^ (k + 1) = 2 * B := by
      simp [B, pow_succ, mul_comm]
    exact Nat.le_of_lt (by simpa [hpow_eq] using hZ_lt_pow_succ)
  have hS_le_Z_add_one : S ≤ (Z : ℝ) + 1 := by
    exact (Nat.lt_floor_add_one S).le
  have hZ_add_one_le_fourB : (Z : ℝ) + 1 ≤ 4 * (B : ℝ) := by
    have hZ_le_twoB_real : (Z : ℝ) ≤ 2 * (B : ℝ) := by
      exact_mod_cast hZ_le_twoB
    have hone_le_twoB : (1 : ℝ) ≤ 2 * (B : ℝ) := by
      nlinarith [hB_ge_one_real]
    nlinarith
  have hS_le_fourB : S ≤ 4 * (B : ℝ) :=
    le_trans hS_le_Z_add_one hZ_add_one_le_fourB
  have hlog_S_le_log_fourB :
      Real.log S ≤ Real.log (4 * (B : ℝ)) :=
    Real.log_le_log hS_pos hS_le_fourB
  have hlog_fourB_eq :
      Real.log (4 * (B : ℝ)) = Real.log 4 + Real.log (B : ℝ) := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hB_pos)]
  have hlog_four_le_logB : Real.log 4 ≤ Real.log (B : ℝ) := by
    exact Real.log_le_log (by norm_num : (0 : ℝ) < 4)
      (by exact_mod_cast hB_ge_four)
  have hlog_S_le_two_logB :
      Real.log S ≤ 2 * Real.log (B : ℝ) := by
    calc
      Real.log S ≤ Real.log (4 * (B : ℝ)) := hlog_S_le_log_fourB
      _ = Real.log 4 + Real.log (B : ℝ) := hlog_fourB_eq
      _ ≤ 2 * Real.log (B : ℝ) := by linarith
  have hscaled :
      (c / 2) * Real.log S ≤ c * Real.log (B : ℝ) := by
    nlinarith [hc, hlog_S_le_two_logB]
  have hdy_B : c * Real.log (B : ℝ) ≤ oddSquarefreeTotientNat B := by
    simpa [B] using hdy k hk_ge_two
  have hle_sAvgPhi :
      oddSquarefreeTotientNat B ≤ sAvgPhi P X :=
    oddSquarefreeTotientNat_le_sAvgPhi_of_le_floor_SScale P X hB_le_Z
  calc
    (c / 2) * Real.log (ErdosStraus.SScale P X)
        = (c / 2) * Real.log S := by rfl
    _ ≤ c * Real.log (B : ℝ) := hscaled
    _ ≤ oddSquarefreeTotientNat B := hdy_B
    _ ≤ sAvgPhi P X := hle_sAvgPhi

/-- Lemma 3.3, first sum, for `M = 1`: `∑_{s ≤ S, s squarefree} φ(s)/s² ≍ log S` for
`S = X^η`. -/
theorem s_average_phi (P : ErdosStraus.Params) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * Real.log (ErdosStraus.SScale P X) ≤ sAvgPhi P X ∧
        sAvgPhi P X ≤ C * Real.log (ErdosStraus.SScale P X) := by
  rcases sAvgPhi_lower_log P with ⟨c, Xlo, hc, hlo⟩
  rcases sAvgPhi_upper_log P with ⟨C, Xhi, hC, hhi⟩
  refine ⟨c, C, max Xlo Xhi, hc, hC, ?_⟩
  intro X hX
  have hXlo : Xlo ≤ X := le_trans (le_max_left _ _) hX
  have hXhi : Xhi ≤ X := le_trans (le_max_right _ _) hX
  exact ⟨hlo X hXlo, hhi X hXhi⟩

/-- `∑_{d ≤ z, d odd squarefree} φ(d)/d² ≫ log z` for `z = (log X)^4`. -/
theorem smallDivisorEulerSum_oddSquarefreeWitness_lower_bound :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      c * Real.log (ErdosStraus.zScale X)
        ≤ ∑ d ∈ oddSquarefreeEulerWitness X,
            (Nat.totient d : ℝ) / (d : ℝ) ^ 2 :=
  oddSqfTotient_lower_of_dyadic
    oddSqfTotient_dyadic_lower

theorem smallDivisorEulerSum_finite_witness_lower_bound :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      ∃ T : Finset ℕ,
        T ⊆ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.UScale X⌋₊).filter
          (fun d => d ∣ roughModulus X ∧ Odd d) ∧
        c * Real.log (ErdosStraus.zScale X)
          ≤ ∑ d ∈ T, (Nat.totient d : ℝ) / (d : ℝ) ^ 2 := by
  rcases smallDivisorEulerSum_oddSquarefreeWitness_lower_bound with
    ⟨c, X₀, hc, hW⟩
  refine ⟨c, max X₀ (Real.exp 1), hc, ?_⟩
  intro X hX
  have hXbase : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  refine ⟨oddSquarefreeEulerWitness X, ?_, hW X hXbase⟩
  exact oddSquarefreeEulerWitness_subset_smallDivisorSupport X
    (zScale_ge_one_of_exp_one_le hXexp)

theorem smallDivisorEulerSum_lower_bound :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      c * Real.log (ErdosStraus.zScale X) ≤ smallDivisorEulerSum X := by
  rcases smallDivisorEulerSum_finite_witness_lower_bound with ⟨c, X₀, hc, hwit⟩
  refine ⟨c, X₀, hc, ?_⟩
  intro X hX
  rcases hwit X hX with ⟨T, hT, hW⟩
  exact hW.trans (by
    classical
    unfold smallDivisorEulerSum
    apply Finset.sum_le_sum_of_subset_of_nonneg hT
    intro d _hdBig _hdSmall
    exact div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

/-- `sAvgRecip P X ≫ log S`, since `log S ≤ H_⌊S⌋ ≤ 2 sAvgRecip P X`. -/
theorem s_average_recip_lower_for_coprime (P : ErdosStraus.Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      c * Real.log (ErdosStraus.SScale P X) ≤ sAvgRecip P X := by
  refine ⟨1 / 2, 1, by norm_num, ?_⟩
  intro X hX
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hSpos : 0 < ErdosStraus.SScale P X :=
    Real.rpow_pos_of_pos hXpos P.η
  have hlog_le_harm :
      Real.log (ErdosStraus.SScale P X)
        ≤ ((harmonic ⌊ErdosStraus.SScale P X⌋₊ : ℚ) : ℝ) :=
    log_le_harmonic_floor (ErdosStraus.SScale P X) hSpos.le
  have hdecomp :=
    harmonic_le_squarefree_mul_square_recip
      ⌊ErdosStraus.SScale P X⌋₊
  have hsquares :=
    square_recip_sum_le_two_for_coprime_lower ⌊ErdosStraus.SScale P X⌋₊
  have hsAvg_nonneg : 0 ≤ sAvgRecip P X := sAvgRecip_nonneg P X
  have hproduct_le :
      ((∑ a ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.SScale P X⌋₊).filter
            (fun a => Squarefree a), (1 : ℝ) / (a : ℝ)) *
          (∑ b ∈ Finset.Icc (1 : ℕ) ⌊ErdosStraus.SScale P X⌋₊, ((b : ℝ) ^ 2)⁻¹))
        ≤ sAvgRecip P X * 2 := by
    have hsum_eq :
        (∑ a ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.SScale P X⌋₊).filter
            (fun a => Squarefree a), (1 : ℝ) / (a : ℝ)) = sAvgRecip P X := by
      unfold sAvgRecip
      rfl
    rw [hsum_eq]
    exact mul_le_mul_of_nonneg_left hsquares hsAvg_nonneg
  have hlog_le_twice : Real.log (ErdosStraus.SScale P X) ≤ sAvgRecip P X * 2 :=
    le_trans hlog_le_harm (le_trans hdecomp hproduct_le)
  nlinarith

theorem sAvgRecipCoprime_lower_from_sAvgRecip
    (P : ErdosStraus.Params) (X : ℝ) {d : ℕ}
    (hd : 0 < d) (hsqf : Squarefree d) :
    ((Nat.totient d : ℝ) / (d : ℝ)) * sAvgRecip P X ≤
      sAvgRecipCoprime P X d := by
  let A : ℝ := ∑ g ∈ d.divisors, (1 : ℝ) / (g : ℝ)
  let B : ℝ := sAvgRecipCoprime P X d
  have hfactor : sAvgRecip P X ≤ A * B := by
    simpa [A, B] using sAvgRecip_le_divisor_recip_mul_sAvgRecipCoprime P X hd
  have hcost : A ≤ (d : ℝ) / (Nat.totient d : ℝ) := by
    simpa [A] using divisor_recip_sum_le_totient_ratio hd hsqf
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hphi_pos_nat : 0 < Nat.totient d := Nat.totient_pos.mpr hd
  have hphi_pos : (0 : ℝ) < (Nat.totient d : ℝ) := by exact_mod_cast hphi_pos_nat
  have hdensity_nonneg : 0 ≤ (Nat.totient d : ℝ) / (d : ℝ) :=
    div_nonneg hphi_pos.le hdpos.le
  have hB_nonneg : 0 ≤ B := by
    simpa [B] using sAvgRecipCoprime_nonneg P X d
  have hcost_unit : A * ((Nat.totient d : ℝ) / (d : ℝ)) ≤ 1 := by
    calc
      A * ((Nat.totient d : ℝ) / (d : ℝ))
          ≤ ((d : ℝ) / (Nat.totient d : ℝ)) *
              ((Nat.totient d : ℝ) / (d : ℝ)) :=
            mul_le_mul_of_nonneg_right hcost hdensity_nonneg
      _ = 1 := by
            field_simp [ne_of_gt hdpos, ne_of_gt hphi_pos]
  calc
    ((Nat.totient d : ℝ) / (d : ℝ)) * sAvgRecip P X
        ≤ ((Nat.totient d : ℝ) / (d : ℝ)) * (A * B) :=
          mul_le_mul_of_nonneg_left hfactor hdensity_nonneg
    _ = (A * ((Nat.totient d : ℝ) / (d : ℝ))) * B := by ring
    _ ≤ 1 * B := mul_le_mul_of_nonneg_right hcost_unit hB_nonneg
    _ = B := by ring

/-- Uniformly for odd `d ∣ P(z)` with `d ≤ U`,
`∑_{s ≤ S, s squarefree, (s, d) = 1} 1/s ≫ (φ(d)/d) log S`. -/
theorem coprimeSquarefreeRecip_lower_bound (P : ErdosStraus.Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ d ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.UScale X⌋₊).filter
          (fun d => d ∣ roughModulus X ∧ Odd d),
        c * Real.log (ErdosStraus.SScale P X) *
            ((Nat.totient d : ℝ) / (d : ℝ)) ≤ sAvgRecipCoprime P X d := by
  rcases s_average_recip_lower_for_coprime P with ⟨c, X₀, hc, hlow⟩
  refine ⟨c, X₀, hc, ?_⟩
  intro X hX d hdmem
  have hdIcc : d ∈ Finset.Icc (1 : ℕ) ⌊ErdosStraus.UScale X⌋₊ :=
    (Finset.mem_filter.mp hdmem).1
  have hdpos_nat : 0 < d :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdIcc).1
  have hdvd : d ∣ roughModulus X := (Finset.mem_filter.mp hdmem).2.1
  have hsqf : Squarefree d := (roughModulus_squarefree X).squarefree_of_dvd hdvd
  have hdensity_nonneg :
      0 ≤ (Nat.totient d : ℝ) / (d : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg d)
  calc
    c * Real.log (ErdosStraus.SScale P X) *
        ((Nat.totient d : ℝ) / (d : ℝ))
        = ((Nat.totient d : ℝ) / (d : ℝ)) *
            (c * Real.log (ErdosStraus.SScale P X)) := by ring
    _ ≤ ((Nat.totient d : ℝ) / (d : ℝ)) * sAvgRecip P X :=
          mul_le_mul_of_nonneg_left (hlow X hX) hdensity_nonneg
    _ ≤ sAvgRecipCoprime P X d :=
          sAvgRecipCoprime_lower_from_sAvgRecip P X hdpos_nat hsqf

theorem sAvgRecipCoprime_le_sAvgRecip
    (P : ErdosStraus.Params) (X : ℝ) (d : ℕ) :
    sAvgRecipCoprime P X d ≤ sAvgRecip P X := by
  classical
  unfold sAvgRecipCoprime sAvgRecip
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    rw [Finset.mem_filter] at hs ⊢
    exact ⟨hs.1, hs.2.1⟩
  · intro s _hsBig _hsSmall
    exact div_nonneg zero_le_one (Nat.cast_nonneg s)

theorem sAvgRecipCoprime_upper_log (P : ErdosStraus.Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → ∀ d : ℕ,
      sAvgRecipCoprime P X d ≤ C * Real.log (ErdosStraus.SScale P X) := by
  rcases sAvgRecip_upper_log P with ⟨C, X₀, hC, hupper⟩
  refine ⟨C, X₀, hC, ?_⟩
  intro X hX d
  exact (sAvgRecipCoprime_le_sAvgRecip P X d).trans (hupper X hX)

/-- Adds the nonnegativity and absolute value bounds to a two-sided estimate for
`sAvgRecipCoprime`. -/
theorem sAvgRecipCoprime_bounds_of_two_sided
    (P : ErdosStraus.Params)
    (h :
      ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        ∀ d ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.UScale X⌋₊).filter
            (fun d => d ∣ roughModulus X ∧ Odd d),
          c * Real.log (ErdosStraus.SScale P X) *
              ((Nat.totient d : ℝ) / (d : ℝ)) ≤
            sAvgRecipCoprime P X d ∧
          sAvgRecipCoprime P X d ≤
            C * Real.log (ErdosStraus.SScale P X)) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      0 ≤ Real.log (ErdosStraus.SScale P X) ∧
        ∀ d ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.UScale X⌋₊).filter
            (fun d => d ∣ roughModulus X ∧ Odd d),
          0 ≤ (Nat.totient d : ℝ) / (d : ℝ) ∧
            0 ≤ sAvgRecipCoprime P X d ∧
            c * Real.log (ErdosStraus.SScale P X) *
                ((Nat.totient d : ℝ) / (d : ℝ)) ≤
              sAvgRecipCoprime P X d ∧
            sAvgRecipCoprime P X d ≤
              C * Real.log (ErdosStraus.SScale P X) ∧
            |sAvgRecipCoprime P X d| ≤
              C * Real.log (ErdosStraus.SScale P X) := by
  rcases h with ⟨c, C, Xbase, hc, hC, hbounds⟩
  refine ⟨c, C, max Xbase 1, hc, hC, ?_⟩
  intro X hX
  have hXbase : Xbase ≤ X := le_trans (le_max_left _ _) hX
  have hXone : (1 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hlogS_nonneg : 0 ≤ Real.log (ErdosStraus.SScale P X) := by
    unfold ErdosStraus.SScale
    rw [Real.log_rpow hXpos]
    exact mul_nonneg P.η_pos.le (Real.log_nonneg hXone)
  refine ⟨hlogS_nonneg, ?_⟩
  intro d hd
  have htot_nonneg : 0 ≤ (Nat.totient d : ℝ) / (d : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg d)
  have hrecip_nonneg : 0 ≤ sAvgRecipCoprime P X d :=
    sAvgRecipCoprime_nonneg P X d
  rcases hbounds X hXbase d hd with ⟨hlower, hupper⟩
  exact ⟨htot_nonneg, hrecip_nonneg, hlower, hupper, by
    rw [abs_of_nonneg hrecip_nonneg]
    exact hupper⟩

/-- `(φ(d)/d) log S ≪ sAvgRecipCoprime P X d ≪ log S` uniformly for odd `d ∣ P(z)` with
`d ≤ U`. -/
theorem sAvgRecipCoprime_bounds
    (P : ErdosStraus.Params) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      0 ≤ Real.log (ErdosStraus.SScale P X) ∧
        ∀ d ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.UScale X⌋₊).filter
            (fun d => d ∣ roughModulus X ∧ Odd d),
          0 ≤ (Nat.totient d : ℝ) / (d : ℝ) ∧
            0 ≤ sAvgRecipCoprime P X d ∧
            c * Real.log (ErdosStraus.SScale P X) *
                ((Nat.totient d : ℝ) / (d : ℝ)) ≤
              sAvgRecipCoprime P X d ∧
            sAvgRecipCoprime P X d ≤
              C * Real.log (ErdosStraus.SScale P X) ∧
            |sAvgRecipCoprime P X d| ≤
              C * Real.log (ErdosStraus.SScale P X) := by
  rcases coprimeSquarefreeRecip_lower_bound P with ⟨c, Xlower, hc, hlower⟩
  rcases sAvgRecipCoprime_upper_log P with ⟨C, Xupper, hC, hupper⟩
  apply sAvgRecipCoprime_bounds_of_two_sided P
  refine ⟨c, C, max Xlower Xupper, hc, hC, ?_⟩
  intro X hX
  have hXlower : Xlower ≤ X := le_trans (le_max_left _ _) hX
  have hXupper : Xupper ≤ X := le_trans (le_max_right _ _) hX
  intro d hd
  exact ⟨hlower X hXlower d hd, hupper X hXupper d⟩

theorem log_zScale_pos_of_exp_two_le {X : ℝ} (hX : Real.exp 2 ≤ X) :
    0 < Real.log (ErdosStraus.zScale X) := by
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 2) hX
  have hlogX_ge_two : (2 : ℝ) ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hX
  have hloglog_pos : 0 < Real.log (Real.log X) :=
    Real.log_pos (lt_of_lt_of_le one_lt_two hlogX_ge_two)
  have hlogZ_eq :
      Real.log (ErdosStraus.zScale X) = 4 * Real.log (Real.log X) := by
    unfold ErdosStraus.zScale
    rw [Real.log_pow]
    ring
  rw [hlogZ_eq]
  positivity

theorem eventually_UScale_le_rpow {δ : ℝ} (hδ : 0 < δ) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ErdosStraus.UScale X ≤ X ^ δ := by
  have hδ8 : 0 < δ / 8 := by positivity
  have hsmall_eventually :
      ∀ᶠ X : ℝ in Filter.atTop,
        ‖Real.log X‖ ≤ (1 : ℝ) * ‖X ^ (δ / 8)‖ :=
    (isLittleO_log_rpow_atTop hδ8).def (by norm_num : (0 : ℝ) < 1)
  rcases Filter.eventually_atTop.mp hsmall_eventually with ⟨Xsmall, hsmall⟩
  refine ⟨max Xsmall (Real.exp 1), ?_⟩
  intro X hX
  have hXsmall : Xsmall ≤ X := le_trans (le_max_left _ _) hX
  have hXexp1 : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hXexp1
  have hXnonneg : 0 ≤ X := hXpos.le
  have hlogX_nonneg : 0 ≤ Real.log X := by
    rw [Real.log_nonneg_iff hXpos]
    exact le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hXexp1
  have hpow_nonneg : 0 ≤ X ^ (δ / 8) :=
    (Real.rpow_pos_of_pos hXpos (δ / 8)).le
  have hlog_le :
      Real.log X ≤ X ^ (δ / 8) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hlogX_nonneg,
      abs_of_nonneg hpow_nonneg] using hsmall X hXsmall
  unfold ErdosStraus.UScale
  calc
    (Real.log X) ^ (8 : ℕ)
        ≤ (X ^ (δ / 8)) ^ (8 : ℕ) :=
          pow_le_pow_left₀ hlogX_nonneg hlog_le 8
    _ = X ^ δ := by
          rw [← Real.rpow_natCast (X ^ (δ / 8)) 8]
          rw [← Real.rpow_mul hXnonneg]
          congr 1
          ring

/-! ## Lemma 6.4 -/

theorem smallDivisorEulerSum_lower_log :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      c * Real.log (ErdosStraus.zScale X) ≤ smallDivisorEulerSum X :=
  smallDivisorEulerSum_lower_bound

/-- Interchanging the sums in Lemma 6.4:
`∑_{s≤S, s squarefree} A_s/s = ∑_{d≤U, d∣P(z), d odd} d⁻¹ ∑_{s≤S, s squarefree, (s,d)=1} s⁻¹`.
-/
theorem smallDivisorAverage_eq_sum_coprime (P : ErdosStraus.Params) (X : ℝ) :
    smallDivisorAverage P X =
      ∑ d ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.UScale X⌋₊).filter
          (fun d => d ∣ roughModulus X ∧ Odd d),
        (1 : ℝ) / (d : ℝ) * sAvgRecipCoprime P X d := by
  classical
  let Sset : Finset ℕ :=
    (Finset.Icc (1 : ℕ) ⌊ErdosStraus.SScale P X⌋₊).filter (fun s => Squarefree s)
  let Dset : Finset ℕ :=
    (Finset.Icc (1 : ℕ) ⌊ErdosStraus.UScale X⌋₊).filter
      (fun d => d ∣ roughModulus X ∧ Odd d)
  have hleft :
      smallDivisorAverage P X =
        ∑ s ∈ Sset, ∑ d ∈ Dset,
          if Nat.Coprime d s then ((1 : ℝ) / (d : ℝ)) * ((1 : ℝ) / (s : ℝ))
          else 0 := by
    unfold smallDivisorAverage smallDivisorWeight
    simp only [Sset, Dset]
    apply Finset.sum_congr rfl
    intro s hs
    calc
      (∑ d ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.UScale X⌋₊).filter
          (fun d => d ∣ roughModulus X ∧ Odd d ∧ Nat.Coprime d s),
          (1 : ℝ) / (d : ℝ)) / (s : ℝ)
          = (∑ d ∈ Dset, if Nat.Coprime d s then (1 : ℝ) / (d : ℝ) else 0) *
              ((1 : ℝ) / (s : ℝ)) := by
            have hsum :
                (∑ d ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.UScale X⌋₊).filter
                    (fun d => d ∣ roughModulus X ∧ Odd d ∧ Nat.Coprime d s),
                    (1 : ℝ) / (d : ℝ))
                  =
                ∑ d ∈ Dset, if Nat.Coprime d s then (1 : ℝ) / (d : ℝ) else 0 := by
              simp only [Dset]
              rw [Finset.sum_filter]
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro d hd
              by_cases hdiv : d ∣ roughModulus X
              · by_cases hodd : Odd d
                · by_cases hcop : Nat.Coprime d s
                  · simp [hdiv, hodd]
                  · simp [hdiv, hodd, hcop]
                · by_cases hcop : Nat.Coprime d s
                  · simp [hdiv, hodd]
                  · simp [hdiv, hodd, hcop]
              · by_cases hodd : Odd d
                · by_cases hcop : Nat.Coprime d s
                  · simp [hdiv, hodd]
                  · simp [hdiv, hodd, hcop]
                · by_cases hcop : Nat.Coprime d s
                  · simp [hdiv, hodd]
                  · simp [hdiv, hodd, hcop]
            rw [hsum]
            ring
      _ = ∑ d ∈ Dset,
          if Nat.Coprime d s then ((1 : ℝ) / (d : ℝ)) * ((1 : ℝ) / (s : ℝ))
          else 0 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hcop : Nat.Coprime d s
          · simp
          · simp [hcop]
  have hcomm :
      (∑ s ∈ Sset, ∑ d ∈ Dset,
          if Nat.Coprime d s then ((1 : ℝ) / (d : ℝ)) * ((1 : ℝ) / (s : ℝ))
          else 0)
        =
      ∑ d ∈ Dset, ∑ s ∈ Sset,
          if Nat.Coprime d s then ((1 : ℝ) / (d : ℝ)) * ((1 : ℝ) / (s : ℝ))
          else 0 := by
    rw [Finset.sum_comm]
  have hright :
      (∑ d ∈ Dset, ∑ s ∈ Sset,
          if Nat.Coprime d s then ((1 : ℝ) / (d : ℝ)) * ((1 : ℝ) / (s : ℝ))
          else 0)
        =
      ∑ d ∈ Dset, (1 : ℝ) / (d : ℝ) * sAvgRecipCoprime P X d := by
    apply Finset.sum_congr rfl
    intro d hd
    unfold sAvgRecipCoprime
    calc
        (∑ s ∈ Sset,
            if Nat.Coprime d s then ((1 : ℝ) / (d : ℝ)) * ((1 : ℝ) / (s : ℝ))
            else 0)
            = ∑ s ∈ Sset.filter (fun s => Nat.Coprime d s),
                ((1 : ℝ) / (d : ℝ)) * ((1 : ℝ) / (s : ℝ)) := by
            exact (Finset.sum_filter
              (s := Sset)
              (p := fun s => Nat.Coprime d s)
              (f := fun s => ((1 : ℝ) / (d : ℝ)) * ((1 : ℝ) / (s : ℝ)))).symm
      _ = (1 : ℝ) / (d : ℝ) *
            ∑ s ∈ Sset.filter (fun s => Nat.Coprime d s), (1 : ℝ) / (s : ℝ) := by
            rw [Finset.mul_sum]
      _ = (1 : ℝ) / (d : ℝ) *
            ∑ s ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.SScale P X⌋₊).filter
              (fun s => Squarefree s ∧ Nat.Coprime s d), (1 : ℝ) / (s : ℝ) := by
            congr 1
            apply Finset.sum_congr ?_ ?_
            · simp only [Sset]
              apply Finset.ext
              intro s
              simp only [Finset.mem_filter]
              constructor
              · intro hs
                exact ⟨hs.1.1, ⟨hs.1.2, hs.2.symm⟩⟩
              · intro hs
                exact ⟨⟨hs.1, hs.2.1⟩, hs.2.2.symm⟩
            · intro s hs
              rfl
  calc
    smallDivisorAverage P X
        = ∑ s ∈ Sset, ∑ d ∈ Dset,
          if Nat.Coprime d s then ((1 : ℝ) / (d : ℝ)) * ((1 : ℝ) / (s : ℝ))
          else 0 := hleft
    _ = ∑ d ∈ Dset, ∑ s ∈ Sset,
          if Nat.Coprime d s then ((1 : ℝ) / (d : ℝ)) * ((1 : ℝ) / (s : ℝ))
          else 0 := hcomm
    _ = ∑ d ∈ Dset, (1 : ℝ) / (d : ℝ) * sAvgRecipCoprime P X d := hright

/-- If each inner sum satisfies `sAvgRecipCoprime P X d ≥ c (φ(d)/d) log S`, then
`smallDivisorAverage P X ≥ c log S · smallDivisorEulerSum X`. -/
theorem smallDivisorAverage_lower_from_coprime_average
    (P : ErdosStraus.Params) (X c : ℝ)
    (hcop : ∀ d ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.UScale X⌋₊).filter
          (fun d => d ∣ roughModulus X ∧ Odd d),
        c * Real.log (ErdosStraus.SScale P X) *
            ((Nat.totient d : ℝ) / (d : ℝ)) ≤ sAvgRecipCoprime P X d) :
    c * Real.log (ErdosStraus.SScale P X) * smallDivisorEulerSum X
      ≤ smallDivisorAverage P X := by
  classical
  rw [smallDivisorAverage_eq_sum_coprime]
  unfold smallDivisorEulerSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hdIcc : d ∈ Finset.Icc (1 : ℕ) ⌊ErdosStraus.UScale X⌋₊ :=
    (Finset.mem_filter.mp hd).1
  have hdpos_nat : 0 < d :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdIcc).1
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos_nat
  have hinv_nonneg : 0 ≤ (1 : ℝ) / (d : ℝ) :=
    div_nonneg zero_le_one hdpos.le
  have hterm :=
    mul_le_mul_of_nonneg_left (hcop d hd) hinv_nonneg
  calc
    c * Real.log (ErdosStraus.SScale P X) *
        ((Nat.totient d : ℝ) / (d : ℝ) ^ 2)
        = (1 : ℝ) / (d : ℝ) *
            (c * Real.log (ErdosStraus.SScale P X) *
              ((Nat.totient d : ℝ) / (d : ℝ))) := by
          ring_nf
    _ ≤ (1 : ℝ) / (d : ℝ) * sAvgRecipCoprime P X d := hterm

theorem smallDivisorAverage_lower_from_coprime_and_euler
    (P : ErdosStraus.Params) (X cS cE : ℝ)
    (hcS_nonneg : 0 ≤ cS)
    (hlogS_nonneg : 0 ≤ Real.log (ErdosStraus.SScale P X))
    (hcop : ∀ d ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.UScale X⌋₊).filter
          (fun d => d ∣ roughModulus X ∧ Odd d),
        cS * Real.log (ErdosStraus.SScale P X) *
            ((Nat.totient d : ℝ) / (d : ℝ)) ≤ sAvgRecipCoprime P X d)
    (hE : cE * Real.log (ErdosStraus.zScale X) ≤ smallDivisorEulerSum X) :
    cS * cE * Real.log (ErdosStraus.SScale P X) *
        Real.log (ErdosStraus.zScale X)
      ≤ smallDivisorAverage P X := by
  have hmain := smallDivisorAverage_lower_from_coprime_average P X cS hcop
  have hscale_nonneg : 0 ≤ cS * Real.log (ErdosStraus.SScale P X) := by
    exact mul_nonneg hcS_nonneg hlogS_nonneg
  have hEuler_scaled :
      (cS * Real.log (ErdosStraus.SScale P X)) *
          (cE * Real.log (ErdosStraus.zScale X))
        ≤ (cS * Real.log (ErdosStraus.SScale P X)) *
          smallDivisorEulerSum X :=
    mul_le_mul_of_nonneg_left hE hscale_nonneg
  calc
    cS * cE * Real.log (ErdosStraus.SScale P X) *
        Real.log (ErdosStraus.zScale X)
        = (cS * Real.log (ErdosStraus.SScale P X)) *
            (cE * Real.log (ErdosStraus.zScale X)) := by ring
    _ ≤ (cS * Real.log (ErdosStraus.SScale P X)) *
          smallDivisorEulerSum X := hEuler_scaled
    _ ≤ smallDivisorAverage P X := hmain

theorem smallDivisorAverage_lower_from_coprime_and_euler_bound
    (P : ErdosStraus.Params) (cS XS : ℝ) (hcS : 0 < cS)
    (hcop : ∀ X : ℝ, XS ≤ X →
      ∀ d ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.UScale X⌋₊).filter
          (fun d => d ∣ roughModulus X ∧ Odd d),
        cS * Real.log (ErdosStraus.SScale P X) *
            ((Nat.totient d : ℝ) / (d : ℝ)) ≤ sAvgRecipCoprime P X d)
    (hEuler :
      ∃ cE XE : ℝ, 0 < cE ∧ ∀ X : ℝ, XE ≤ X →
        cE * Real.log (ErdosStraus.zScale X) ≤ smallDivisorEulerSum X) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      c * Real.log (ErdosStraus.SScale P X) * Real.log (ErdosStraus.zScale X)
        ≤ smallDivisorAverage P X := by
  rcases hEuler with ⟨cE, XE, hcE, hE⟩
  refine ⟨cS * cE, max XS (max XE 1), mul_pos hcS hcE, ?_⟩
  intro X hX
  have hXS : XS ≤ X := le_trans (le_max_left _ _) hX
  have htail : max XE (1 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hXE : XE ≤ X := le_trans (le_max_left _ _) htail
  have hXone : (1 : ℝ) ≤ X := le_trans (le_max_right _ _) htail
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hlogS_nonneg : 0 ≤ Real.log (ErdosStraus.SScale P X) := by
    unfold ErdosStraus.SScale
    rw [Real.log_rpow hXpos]
    exact mul_nonneg P.η_pos.le (Real.log_nonneg hXone)
  exact smallDivisorAverage_lower_from_coprime_and_euler P X cS cE hcS.le
    hlogS_nonneg (hcop X hXS) (hE X hXE)

theorem smallDivisorAverage_lower_from_coprime_and_euler_input
    (P : ErdosStraus.Params) (cS XS : ℝ) (hcS : 0 < cS)
    (hcop : ∀ X : ℝ, XS ≤ X →
      ∀ d ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.UScale X⌋₊).filter
          (fun d => d ∣ roughModulus X ∧ Odd d),
        cS * Real.log (ErdosStraus.SScale P X) *
            ((Nat.totient d : ℝ) / (d : ℝ)) ≤ sAvgRecipCoprime P X d) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      c * Real.log (ErdosStraus.SScale P X) * Real.log (ErdosStraus.zScale X)
        ≤ smallDivisorAverage P X :=
  smallDivisorAverage_lower_from_coprime_and_euler_bound P cS XS hcS hcop
    smallDivisorEulerSum_lower_log

/-- Lemma 6.4 with `m = 1`, lower bound: `∑_{s ≤ S, s squarefree} A_s/s ≫ log S · log z`. -/
theorem smallDivisorAverage_lower (P : ErdosStraus.Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      c * Real.log (ErdosStraus.SScale P X) * Real.log (ErdosStraus.zScale X)
        ≤ smallDivisorAverage P X := by
  rcases sAvgRecipCoprime_bounds P with
    ⟨cS, _CS, XS, hcS, _hCS, hcopPack⟩
  exact smallDivisorAverage_lower_from_coprime_and_euler_input P cS XS hcS
    (fun X hX d hd => ((hcopPack X hX).2 d hd).2.2.1)

theorem smallDivisorWeight_le_harmonic_floor (X : ℝ) (s : ℕ) :
    smallDivisorWeight X s ≤ (harmonic ⌊ErdosStraus.UScale X⌋₊ : ℝ) := by
  classical
  unfold smallDivisorWeight
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  simp_rw [one_div]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    exact (Finset.mem_filter.mp hd).1
  · intro d _hdBig _hdSmall
    exact inv_nonneg.mpr (Nat.cast_nonneg d)

theorem log_UScale_eq_two_log_zScale (X : ℝ) :
    Real.log (ErdosStraus.UScale X) = 2 * Real.log (ErdosStraus.zScale X) := by
  unfold ErdosStraus.UScale ErdosStraus.zScale
  rw [Real.log_pow, Real.log_pow]
  ring

/-- `A_s ≤ H_⌊U⌋ ≤ 1 + 2 log z ≪ log z`, since `U = z²`. -/
theorem smallDivisorWeight_upper_logZ :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ s : ℕ, smallDivisorWeight X s ≤ C * Real.log (ErdosStraus.zScale X) := by
  refine ⟨4, Real.exp (Real.exp 1), by norm_num, ?_⟩
  intro X hX s
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hlogX_ge_exp : Real.exp 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hX
  have hlogX_pos : 0 < Real.log X := lt_of_lt_of_le (Real.exp_pos 1) hlogX_ge_exp
  have hlogX_ge_one : (1 : ℝ) ≤ Real.log X :=
    le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hlogX_ge_exp
  have hU_ge_one : (1 : ℝ) ≤ ErdosStraus.UScale X := by
    unfold ErdosStraus.UScale
    calc
      (1 : ℝ) = (1 : ℝ) ^ (8 : ℕ) := by norm_num
      _ ≤ (Real.log X) ^ (8 : ℕ) :=
          pow_le_pow_left₀ zero_le_one hlogX_ge_one 8
  have hharm :
      (harmonic ⌊ErdosStraus.UScale X⌋₊ : ℝ) ≤
        1 + Real.log (ErdosStraus.UScale X) :=
    harmonic_floor_le_one_add_log (ErdosStraus.UScale X) hU_ge_one
  have hloglog_ge_one : (1 : ℝ) ≤ Real.log (Real.log X) := by
    rw [Real.le_log_iff_exp_le hlogX_pos]
    exact hlogX_ge_exp
  have hlogZ_eq :
      Real.log (ErdosStraus.zScale X) = 4 * Real.log (Real.log X) := by
    unfold ErdosStraus.zScale
    rw [Real.log_pow]
    ring
  have hlogZ_ge_one : (1 : ℝ) ≤ Real.log (ErdosStraus.zScale X) := by
    rw [hlogZ_eq]
    nlinarith
  have htail :
      1 + Real.log (ErdosStraus.UScale X) ≤
        4 * Real.log (ErdosStraus.zScale X) := by
    rw [log_UScale_eq_two_log_zScale X]
    nlinarith
  calc
    smallDivisorWeight X s
        ≤ (harmonic ⌊ErdosStraus.UScale X⌋₊ : ℝ) :=
          smallDivisorWeight_le_harmonic_floor X s
    _ ≤ 1 + Real.log (ErdosStraus.UScale X) := hharm
    _ ≤ 4 * Real.log (ErdosStraus.zScale X) := htail

theorem smallDivisorAverage_le_logZ_mul_sAvgRecip :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ P : ErdosStraus.Params,
        smallDivisorAverage P X
          ≤ C * Real.log (ErdosStraus.zScale X) * sAvgRecip P X := by
  rcases smallDivisorWeight_upper_logZ with ⟨C, X₀, hC, hweight⟩
  refine ⟨C, X₀, hC, ?_⟩
  intro X hX P
  classical
  unfold smallDivisorAverage sAvgRecip
  calc
    (∑ s ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.SScale P X⌋₊).filter
          (fun s => Squarefree s), smallDivisorWeight X s / (s : ℝ))
        ≤ ∑ s ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.SScale P X⌋₊).filter
          (fun s => Squarefree s),
            (C * Real.log (ErdosStraus.zScale X)) * ((1 : ℝ) / (s : ℝ)) := by
          apply Finset.sum_le_sum
          intro s hs
          have hsIcc : s ∈ Finset.Icc (1 : ℕ) ⌊ErdosStraus.SScale P X⌋₊ :=
            (Finset.mem_filter.mp hs).1
          have hspos_nat : 0 < s :=
            lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hsIcc).1
          have hs_nonneg : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
          calc
            smallDivisorWeight X s / (s : ℝ)
                ≤ (C * Real.log (ErdosStraus.zScale X)) / (s : ℝ) :=
                  div_le_div_of_nonneg_right (hweight X hX s) hs_nonneg
            _ = (C * Real.log (ErdosStraus.zScale X)) * ((1 : ℝ) / (s : ℝ)) := by
                  ring
    _ = (C * Real.log (ErdosStraus.zScale X)) *
          (∑ s ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.SScale P X⌋₊).filter
            (fun s => Squarefree s), (1 : ℝ) / (s : ℝ)) := by
          rw [Finset.mul_sum]
    _ = C * Real.log (ErdosStraus.zScale X) *
          (∑ s ∈ (Finset.Icc (1 : ℕ) ⌊ErdosStraus.SScale P X⌋₊).filter
            (fun s => Squarefree s), (1 : ℝ) / (s : ℝ)) := by
          ring

/-- Lemma 6.4 with `m = 1`, upper bound: `∑_{s ≤ S, s squarefree} A_s/s ≪ log S · log z`. -/
theorem smallDivisorAverage_upper (P : ErdosStraus.Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      smallDivisorAverage P X
        ≤ C * Real.log (ErdosStraus.SScale P X) * Real.log (ErdosStraus.zScale X) := by
  rcases smallDivisorAverage_le_logZ_mul_sAvgRecip with ⟨Cz, Xz, hCz, hz⟩
  rcases sAvgRecip_upper_log P with ⟨Cs, Xs, hCs, hs⟩
  refine ⟨Cz * Cs, max (max Xz Xs) (Real.exp (Real.exp 1)), mul_pos hCz hCs, ?_⟩
  intro X hX
  have hXz : Xz ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXs : Xs ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXexp : Real.exp (Real.exp 1) ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hXexp
  have hlogZ_nonneg : 0 ≤ Real.log (ErdosStraus.zScale X) := by
    have hlogX_ge_exp : Real.exp 1 ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le hXpos]
      exact hXexp
    have hlogX_ge_one : (1 : ℝ) ≤ Real.log X :=
      le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hlogX_ge_exp
    have hz_ge_one : (1 : ℝ) ≤ ErdosStraus.zScale X := by
      unfold ErdosStraus.zScale
      calc
        (1 : ℝ) = (1 : ℝ) ^ (4 : ℕ) := by norm_num
        _ ≤ (Real.log X) ^ (4 : ℕ) :=
            pow_le_pow_left₀ zero_le_one hlogX_ge_one 4
    exact Real.log_nonneg hz_ge_one
  have h1 := hz X hXz P
  have h2 := hs X hXs
  calc
    smallDivisorAverage P X
        ≤ Cz * Real.log (ErdosStraus.zScale X) * sAvgRecip P X := h1
    _ ≤ Cz * Real.log (ErdosStraus.zScale X) *
          (Cs * Real.log (ErdosStraus.SScale P X)) := by
          exact mul_le_mul_of_nonneg_left h2
            (mul_nonneg hCz.le hlogZ_nonneg)
    _ = (Cz * Cs) * Real.log (ErdosStraus.SScale P X) *
          Real.log (ErdosStraus.zScale X) := by ring

/-! ## Lemma 3.3: the second sum -/

theorem s_average_recip_lower (P : ErdosStraus.Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      c * Real.log (ErdosStraus.SScale P X) ≤ sAvgRecip P X :=
  s_average_recip_lower_for_coprime P

/-- Lemma 3.3, second sum, for `M = 1`: `∑_{s ≤ S, s squarefree} 1/s ≍ log S` for
`S = X^η`. The lower bound comes from writing `n = b²a` with `a` squarefree, the upper bound
from `H_⌊S⌋ ≤ 1 + log S`. -/
theorem s_average_recip (P : ErdosStraus.Params) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * Real.log (ErdosStraus.SScale P X) ≤ sAvgRecip P X
        ∧ sAvgRecip P X ≤ C * Real.log (ErdosStraus.SScale P X) := by
  obtain ⟨c, Xlo, hc, hlo⟩ := s_average_recip_lower P
  obtain ⟨C, Xhi, hC, hhi⟩ := sAvgRecip_upper_log P
  refine ⟨c, C, max Xlo Xhi, hc, hC, ?_⟩
  intro X hX
  have hXlo : Xlo ≤ X := le_trans (le_max_left _ _) hX
  have hXhi : Xhi ≤ X := le_trans (le_max_right _ _) hX
  exact ⟨hlo X hXlo, hhi X hXhi⟩

end ErdosStraus.Estimates

/-! ## Scale separation and the sum over `s` coprime to `m` -/

namespace ErdosStraus.FixedNumeratorFamily

open Classical

/-- For large `X`, `U < X^β` and `⌊z⌋ < X^β`. -/
theorem scale_separation (P : Params) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      1 < X ∧ UScale X < X ^ P.β ∧
        ((⌊zScale X⌋₊ : ℕ) : ℝ) < X ^ P.β := by
  obtain ⟨XU, hU⟩ := Estimates.eventually_UScale_le_rpow
    (δ := P.β / 2) (by linarith [P.β_pos])
  refine ⟨max XU (Real.exp 1), ?_⟩
  intro X hX
  have hXe : Real.exp 1 ≤ X := (le_max_right _ _).trans hX
  have hX1 : 1 < X :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hXe
  have hUβ : UScale X < X ^ P.β :=
    (hU X ((le_max_left _ _).trans hX)).trans_lt
      (Real.rpow_lt_rpow_of_exponent_lt hX1 (by linarith [P.β_pos]))
  have hlog : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le (zero_lt_one.trans hX1)).mpr hXe
  have hzU : zScale X ≤ UScale X :=
    pow_le_pow_right₀ hlog (by norm_num : 4 ≤ 8)
  have hfloor : ((⌊zScale X⌋₊ : ℕ) : ℝ) ≤ zScale X :=
    Nat.floor_le (by unfold zScale; positivity)
  exact ⟨hX1, hUβ, (hfloor.trans hzU).trans_lt hUβ⟩

/-- Lemma 3.3, second sum, at `T = S`: for every positive integer `m`,
`∑_{s ≤ S, s squarefree, (s, m) = 1} 1/s ≍_m log S`. -/
theorem coprime_conductor_mass (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      c * Real.log (SScale P X) ≤ Estimates.sAvgRecipCoprime P X m ∧
        Estimates.sAvgRecipCoprime P X m ≤ C * Real.log (SScale P X) := by
  obtain ⟨c₀, Xlow, hc₀, hlow⟩ := Estimates.s_average_recip_lower_for_coprime P
  obtain ⟨C, Xup, hC, hup⟩ := Estimates.sAvgRecipCoprime_upper_log P
  let A : ℝ := ∑ g ∈ m.divisors, (1 : ℝ) / (g : ℝ)
  have hA : 0 < A := by
    have h1 : (1 : ℝ) ≤ A := by
      have hm1 : 1 ∈ m.divisors := Nat.one_mem_divisors.mpr hm.ne'
      have h := Finset.single_le_sum
        (s := m.divisors) (f := fun g : ℕ => (1 : ℝ) / (g : ℝ))
        (fun g _hg => by positivity) hm1
      simpa [A] using h
    linarith
  refine ⟨c₀ / A, C, max Xlow Xup, div_pos hc₀ hA, hC, ?_⟩
  intro X hX
  refine ⟨?_, hup X ((le_max_right _ _).trans hX) m⟩
  have hfactor := Estimates.sAvgRecip_le_divisor_recip_mul_sAvgRecipCoprime P X hm
  have hl := hlow X ((le_max_left _ _).trans hX)
  have hprod : c₀ * Real.log (SScale P X) ≤ A * Estimates.sAvgRecipCoprime P X m :=
    hl.trans hfactor
  have hdiv := (div_le_iff₀ hA).mpr (by simpa [mul_comm] using hprod)
  simpa [div_mul_eq_mul_div] using hdiv

end ErdosStraus.FixedNumeratorFamily
