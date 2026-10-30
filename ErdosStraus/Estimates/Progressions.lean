import Mathlib.Data.Int.CardIntervalMod
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-!
# Counting integers in arithmetic progressions

Elementary counts behind Lemma 3.2. Each residue class modulo `q` meets an interval of
length `N` in `N/q + O(1)` integers. Möbius inversion over the divisors of a squarefree `M`
coprime to `D` shows that the integers of `[L, U)` in a class modulo `D` and coprime to `M`
number `((U - L)/D) φ(M)/M` up to an error of at most `2τ(M)`; removing the multiples of
`k²` for `2 ≤ k ≤ K` gives a lower bound for the squarefree ones. The file also proves
`τ(M) ≪_ε M^ε` for squarefree `M`.
-/

/-! ## The divisor function of squarefree integers -/

namespace ErdosStraus.ProgressionEstimates

open scoped BigOperators
open Filter

theorem squarefree_card_divisors {M : ℕ} (hM : Squarefree M) :
    M.divisors.card = 2 ^ M.primeFactors.card := by
  rw [Nat.card_divisors hM.ne_zero]
  calc
    _ = ∏ _p ∈ M.primeFactors, (2 : ℕ) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree hM
        (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
    _ = _ := by simp

/-- For every `ε > 0` there is `C_ε` with `τ(M) ≤ C_ε M^ε` for all squarefree
`M`. -/
theorem exists_squarefree_divisor_card_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, Squarefree M →
      (M.divisors.card : ℝ) ≤ C * (M : ℝ) ^ ε := by
  classical
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨K, hK⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2 : ℝ)))
  refine ⟨(2 : ℝ) ^ K, by positivity, ?_⟩
  intro M hM
  let S := M.primeFactors.filter (fun p => p < K)
  let T := M.primeFactors.filter (fun p => ¬ p < K)
  have hsplit (f : ℕ → ℝ) : (∏ p ∈ S, f p) * (∏ p ∈ T, f p) =
      ∏ p ∈ M.primeFactors, f p :=
    Finset.prod_filter_mul_prod_filter_not _ _ _
  have hScard : S.card ≤ K := by
    have hsub : S ⊆ Finset.range K := by
      intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    simpa using Finset.card_le_card hsub
  have hsmall : (∏ _p ∈ S, (2 : ℝ)) ≤
      (2 : ℝ) ^ K * (∏ p ∈ S, (p : ℝ) ^ ε) := by
    have hprod : 1 ≤ ∏ p ∈ S, (p : ℝ) ^ ε := by
      have hle : (∏ _p ∈ S, (1 : ℝ)) ≤ ∏ p ∈ S, (p : ℝ) ^ ε := by
        apply Finset.prod_le_prod
        · intro p hp
          norm_num
        · intro p hp
          have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
            exact_mod_cast (Nat.prime_of_mem_primeFactors
              (Finset.mem_filter.mp hp).1).one_le
          exact Real.one_le_rpow hp1 hε.le
      simpa using hle
    calc
      _ = (2 : ℝ) ^ S.card := by simp
      _ ≤ (2 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) hScard
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hprod
  have hlarge : (∏ _p ∈ T, (2 : ℝ)) ≤ ∏ p ∈ T, (p : ℝ) ^ ε := by
    apply Finset.prod_le_prod
    · intro p hp
      norm_num
    · intro p hp
      exact hK p (by simpa only [not_lt] using (Finset.mem_filter.mp hp).2)
  have hMprod : (∏ p ∈ M.primeFactors, (p : ℝ) ^ ε) = (M : ℝ) ^ ε := by
    rw [Real.finsetProd_rpow _ _ (fun p hp => Nat.cast_nonneg p),
      ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hM]
  calc
    (M.divisors.card : ℝ) = ∏ _p ∈ M.primeFactors, (2 : ℝ) := by
      rw [squarefree_card_divisors hM]
      simp
    _ = (∏ _p ∈ S, (2 : ℝ)) * (∏ _p ∈ T, (2 : ℝ)) := (hsplit _).symm
    _ ≤ ((2 : ℝ) ^ K * (∏ p ∈ S, (p : ℝ) ^ ε)) *
        (∏ p ∈ T, (p : ℝ) ^ ε) :=
      mul_le_mul hsmall hlarge (by positivity) (by positivity)
    _ = (2 : ℝ) ^ K * (M : ℝ) ^ ε := by
      rw [mul_assoc, hsplit, hMprod]

/-- `1 ≤ τ(M) φ(M)/M`, since `M = ∑_{d ∣ M} φ(d) ≤ τ(M) φ(M)`. -/
theorem one_le_divisor_card_mul_totient_density {M : ℕ} (hM : M ≠ 0) :
    (1 : ℝ) ≤ (M.divisors.card : ℝ) *
      ((Nat.totient M : ℝ) / (M : ℝ)) := by
  have hphi : M ≤ Nat.totient M * M.divisors.card := by
    calc
      M = ∑ d ∈ M.divisors, Nat.totient d := (Nat.sum_totient M).symm
      _ ≤ ∑ _d ∈ M.divisors, Nat.totient M := by
        apply Finset.sum_le_sum
        intro d hd
        exact Nat.le_of_dvd (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hM))
          (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
      _ = _ := by simp [mul_comm]
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM)
  have hphiR : (M : ℝ) ≤ (Nat.totient M : ℝ) * (M.divisors.card : ℝ) := by
    exact_mod_cast hphi
  rw [← mul_div_assoc, le_div_iff₀ hMR]
  nlinarith

end ErdosStraus.ProgressionEstimates

/-! ## Residue classes in an interval -/

namespace ErdosStraus.SieveEstimates

open scoped BigOperators

theorem abs_range_modEq_card_sub_div (N b : ℕ) {q : ℕ} (hq : 0 < q) :
    |(((Finset.range N).filter (fun n => n ≡ b [MOD q])).card : ℝ) -
      (N : ℝ) / (q : ℝ)| ≤ 1 := by
  classical
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hrem : 0 ≤ ((N % q : ℕ) : ℝ) / (q : ℝ) := by positivity
  have hrem1 : ((N % q : ℕ) : ℝ) / (q : ℝ) < 1 := by
    rw [div_lt_one hqR]
    exact_mod_cast Nat.mod_lt N hq
  have hdiv : (N : ℝ) / (q : ℝ) = ((N / q : ℕ) : ℝ) + ((N % q : ℕ) : ℝ) / (q : ℝ) := by
    apply (div_eq_iff (ne_of_gt hqR)).mpr
    have hcast : (N : ℝ) = ((N % q : ℕ) : ℝ) + (q : ℝ) * ((N / q : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mod_add_div N q).symm
    field_simp
    nlinarith only [hcast]
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card N hq b]
  rw [Nat.cast_add, hdiv]
  split_ifs <;> norm_num <;> rw [abs_le] <;> constructor <;> linarith

theorem card_filter_Ico_add_range (L U : ℕ) (hLU : L ≤ U) (p : ℕ → Prop)
    [DecidablePred p] :
    ((Finset.Ico L U).filter p).card + ((Finset.range L).filter p).card =
      ((Finset.range U).filter p).card := by
  classical
  have hset : Finset.Ico L U ∪ Finset.range L = Finset.range U := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_range]
    omega
  have hd : Disjoint ((Finset.Ico L U).filter p) ((Finset.range L).filter p) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    have h1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1).1
    have h2 := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
    omega
  rw [← Finset.card_union_of_disjoint hd, ← Finset.filter_union, hset]

theorem abs_Ico_modEq_card_sub_length (L U b : ℕ) (hLU : L ≤ U) {q : ℕ} (hq : 0 < q) :
    |(((Finset.Ico L U).filter (fun n => n ≡ b [MOD q])).card : ℝ) -
      ((U : ℝ) - (L : ℝ)) / (q : ℝ)| ≤ 2 := by
  classical
  have hcard := card_filter_Ico_add_range L U hLU (fun n => n ≡ b [MOD q])
  have hcardR : (((Finset.Ico L U).filter (fun n => n ≡ b [MOD q])).card : ℝ) +
      (((Finset.range L).filter (fun n => n ≡ b [MOD q])).card : ℝ) =
      (((Finset.range U).filter (fun n => n ≡ b [MOD q])).card : ℝ) := by
    exact_mod_cast hcard
  have hU := abs_range_modEq_card_sub_div U b hq
  have hL := abs_range_modEq_card_sub_div L b hq
  rw [abs_le] at hU hL ⊢
  rw [sub_div]
  constructor <;> linarith

/-- For coprime `D` and `q`, the multiples of `q` in the class `b` modulo `D` form a single
class modulo `Dq`. -/
theorem progression_multiples_eq_single_class (L U D b q : ℕ) (hcop : Nat.Coprime D q) :
    ((Finset.Ico L U).filter (fun n => n ≡ b [MOD D])).filter (fun n => q ∣ n) =
      (Finset.Ico L U).filter (fun n => n ≡ Nat.chineseRemainder hcop b 0 [MOD D * q]) := by
  classical
  ext n
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hn, hnD⟩, hnq⟩
    exact ⟨hn, Nat.chineseRemainder_modEq_unique hcop hnD (Nat.modEq_zero_iff_dvd.mpr hnq)⟩
  · rintro ⟨hn, hmod⟩
    have hm := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mpr hmod
    exact ⟨⟨hn, hm.1.trans (Nat.chineseRemainder hcop b 0).property.1⟩,
      Nat.modEq_zero_iff_dvd.mp (hm.2.trans (Nat.chineseRemainder hcop b 0).property.2)⟩

theorem abs_progression_multiples_card_sub_length (L U D b q : ℕ)
    (hLU : L ≤ U) (hD : 0 < D) (hq : 0 < q) (hcop : Nat.Coprime D q) :
    |((((Finset.Ico L U).filter (fun n => n ≡ b [MOD D])).filter
      (fun n => q ∣ n)).card : ℝ) - (((U : ℝ) - (L : ℝ)) / (D : ℝ)) / (q : ℝ)| ≤ 2 := by
  rw [progression_multiples_eq_single_class L U D b q hcop, div_div]
  simpa only [Nat.cast_mul] using abs_Ico_modEq_card_sub_length L U
    (Nat.chineseRemainder hcop b 0) hLU (Nat.mul_pos hD hq)

end ErdosStraus.SieveEstimates

/-! ## Coprime and squarefree integers in a progression -/

namespace ErdosStraus.ProgressionEstimates

open scoped BigOperators

theorem coprime_indicator_eq_moebius_sum (n : ℕ) {M : ℕ} (hM : M ≠ 0) :
    (if Nat.Coprime n M then (1 : ℝ) else 0) =
      ∑ d ∈ M.divisors, if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0 := by
  classical
  have hg : n.gcd M ≠ 0 := Nat.gcd_ne_zero_right hM
  have hfilter : M.divisors.filter (fun d => d ∣ n) = (n.gcd M).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdM, _⟩, hdn⟩
      exact ⟨Nat.dvd_gcd hdn hdM, hg⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨hd.trans (Nat.gcd_dvd_right n M), hM⟩,
        hd.trans (Nat.gcd_dvd_left n M)⟩
  rw [← Finset.sum_filter, hfilter]
  have hs := congrArg (fun f : ArithmeticFunction ℝ => f (n.gcd M))
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  rw [ArithmeticFunction.coe_mul_zeta_apply] at hs
  simp only [ArithmeticFunction.intCoe_apply] at hs
  rw [hs]
  simp [ArithmeticFunction.one_apply, Nat.coprime_iff_gcd_eq_one]

theorem coprime_progression_card_eq_moebius_sum
    (L U D b M : ℕ) (hM : M ≠ 0) :
    ((((Finset.Ico L U).filter (fun n => n ≡ b [MOD D])).filter
      (fun n => Nat.Coprime n M)).card : ℝ) =
      ∑ d ∈ M.divisors, (ArithmeticFunction.moebius d : ℝ) *
        ((((Finset.Ico L U).filter (fun n => n ≡ b [MOD D])).filter
          (fun n => d ∣ n)).card : ℝ) := by
  classical
  simp only [← Finset.sum_boole]
  simp_rw [coprime_indicator_eq_moebius_sum _ hM]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp

/-- The number of `n ∈ [L, U)` with `n ≡ b (mod D)` and `(n, M) = 1` differs from
`((U - L)/D) ∑_{d ∣ M} μ(d)/d` by at most `2τ(M)`. -/
theorem abs_coprime_progression_card_sub_moebius_density
    (L U D b M : ℕ) (hLU : L ≤ U) (hD : 0 < D) (hM : M ≠ 0)
    (hDM : Nat.Coprime D M) :
    |((((Finset.Ico L U).filter (fun n => n ≡ b [MOD D])).filter
      (fun n => Nat.Coprime n M)).card : ℝ) -
        (((U : ℝ) - (L : ℝ)) / (D : ℝ)) *
          (∑ d ∈ M.divisors, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ))| ≤
      2 * (M.divisors.card : ℝ) := by
  classical
  rw [coprime_progression_card_eq_moebius_sum L U D b M hM, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ M.divisors,
        |(ArithmeticFunction.moebius d : ℝ) *
          ((((Finset.Ico L U).filter (fun n => n ≡ b [MOD D])).filter
            (fun n => d ∣ n)).card : ℝ) -
          (((U : ℝ) - (L : ℝ)) / (D : ℝ)) *
            ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ M.divisors, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hcount := SieveEstimates.abs_progression_multiples_card_sub_length
        L U D b d hLU hD (Nat.pos_of_mem_divisors hd)
        (hDM.coprime_dvd_right (Nat.dvd_of_mem_divisors hd))
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      calc
        _ = |(ArithmeticFunction.moebius d : ℝ)| *
            |((((Finset.Ico L U).filter (fun n => n ≡ b [MOD D])).filter
              (fun n => d ∣ n)).card : ℝ) -
              (((U : ℝ) - (L : ℝ)) / (D : ℝ)) / (d : ℝ)| := by
          rw [← abs_mul]
          congr 1
          ring
        _ ≤ 1 * 2 := mul_le_mul hmu hcount (abs_nonneg _) zero_le_one
        _ = 2 := by norm_num
    _ = _ := by simp [mul_comm]

theorem moebius_divisor_density_eq_totient {M : ℕ} (hM : Squarefree M) :
    (∑ d ∈ M.divisors, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) =
      (Nat.totient M : ℝ) / (M : ℝ) := by
  classical
  let f : ArithmeticFunction ℝ :=
    ArithmeticFunction.pdiv (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
      (ArithmeticFunction.id : ArithmeticFunction ℝ)
  have hf : f.IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast.pdiv
      ArithmeticFunction.isMultiplicative_id.natCast
  have hp := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    f hf hM
  have heq : (∑ d ∈ M.divisors, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) =
      ∏ p ∈ M.primeFactors, (1 - (p : ℝ)⁻¹) := by
    calc
      _ = ∑ d ∈ M.divisors, (ArithmeticFunction.moebius d : ℝ) * f d := by
        apply Finset.sum_congr rfl
        intro d hd
        simp [f, ArithmeticFunction.pdiv_apply, ArithmeticFunction.zeta_apply_ne
          (Nat.pos_of_mem_divisors hd).ne', ArithmeticFunction.id_apply, div_eq_mul_inv]
      _ = ∏ p ∈ M.primeFactors, (1 - f p) := hp.symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro p hpM
        simp [f, ArithmeticFunction.pdiv_apply, ArithmeticFunction.zeta_apply_ne
          (Nat.prime_of_mem_primeFactors hpM).ne_zero, ArithmeticFunction.id_apply]
  rw [heq]
  have hphi := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors M)
  have hphiR : (Nat.totient M : ℝ) =
      (M : ℝ) * ∏ p ∈ M.primeFactors, (1 - (p : ℝ)⁻¹) := by
    simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub,
      Rat.cast_one, Rat.cast_inv] using hphi
  rw [hphiR]
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne_zero
  field_simp

/-- For squarefree `M` the main term is `((U - L)/D) φ(M)/M`. -/
theorem abs_coprime_progression_card_sub_totient_density
    (L U D b M : ℕ) (hLU : L ≤ U) (hD : 0 < D) (hM : Squarefree M)
    (hDM : Nat.Coprime D M) :
    |((((Finset.Ico L U).filter (fun n => n ≡ b [MOD D])).filter
      (fun n => Nat.Coprime n M)).card : ℝ) -
        (((U : ℝ) - (L : ℝ)) / (D : ℝ)) *
          ((Nat.totient M : ℝ) / (M : ℝ))| ≤
      2 * (M.divisors.card : ℝ) := by
  simpa only [moebius_divisor_density_eq_totient hM] using
    abs_coprime_progression_card_sub_moebius_density L U D b M hLU hD hM.ne_zero hDM

/-- The `n ∈ [L, U)` with `n ≡ b (mod D)`, `(n, M) = 1` and `k² ∣ n` number at most
`((U - L)/D) (φ(M)/M) / k² + 2τ(M)`. If there is such an `n`, then `k` is coprime to `DM`
and these `n` form a single class modulo `Dk²`. -/
theorem coprime_progression_square_multiples_card_le
    (L U D b M k : ℕ) (hLU : L ≤ U) (hD : 0 < D) (hM : Squarefree M)
    (hDM : Nat.Coprime D M) (hb : Nat.Coprime b D) (hk : 0 < k) :
    (((((Finset.Ico L U).filter (fun n => n ≡ b [MOD D])).filter
      (fun n => Nat.Coprime n M)).filter (fun n => k ^ 2 ∣ n)).card : ℝ) ≤
      (((U : ℝ) - (L : ℝ)) / (D : ℝ)) *
        ((Nat.totient M : ℝ) / (M : ℝ)) / ((k : ℝ) ^ 2) +
      2 * (M.divisors.card : ℝ) := by
  classical
  let S := (((Finset.Ico L U).filter (fun n => n ≡ b [MOD D])).filter
    (fun n => Nat.Coprime n M)).filter (fun n => k ^ 2 ∣ n)
  by_cases hS : S.Nonempty
  · obtain ⟨n, hn⟩ := hS
    obtain ⟨hn', hnK⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn'', hnM⟩ := Finset.mem_filter.mp hn'
    obtain ⟨hnI, hnD⟩ := Finset.mem_filter.mp hn''
    have hkn : k ∣ n := (dvd_pow_self k (by norm_num : 2 ≠ 0)).trans hnK
    have hkM : Nat.Coprime k M := hnM.coprime_dvd_left hkn
    have hnDcop : Nat.Coprime n D := by
      rw [Nat.coprime_iff_gcd_eq_one, hnD.gcd_eq]
      exact hb
    have hDk : Nat.Coprime D (k ^ 2) := (hnDcop.coprime_dvd_left hkn).symm.pow_right 2
    have hqM : Nat.Coprime (k ^ 2) M := hkM.pow_left 2
    have heq : S = ((Finset.Ico L U).filter
        (fun n => n ≡ Nat.chineseRemainder hDk b 0 [MOD D * k ^ 2])).filter
          (fun n => Nat.Coprime n M) := by
      rw [← SieveEstimates.progression_multiples_eq_single_class L U D b (k ^ 2) hDk]
      ext n
      simp only [S, Finset.mem_filter]
      tauto
    have hc := (abs_le.mp (abs_coprime_progression_card_sub_totient_density
      L U (D * k ^ 2) (Nat.chineseRemainder hDk b 0) M hLU
        (Nat.mul_pos hD (pow_pos hk 2)) hM ((hDM.symm.mul_right hqM.symm).symm))).2
    change (S.card : ℝ) ≤ _
    rw [heq]
    simp only [Nat.cast_mul, Nat.cast_pow] at hc
    have he : (((U : ℝ) - (L : ℝ)) / ((D : ℝ) * (k : ℝ) ^ 2)) *
        ((Nat.totient M : ℝ) / (M : ℝ)) =
        (((U : ℝ) - (L : ℝ)) / (D : ℝ)) *
          ((Nat.totient M : ℝ) / (M : ℝ)) / ((k : ℝ) ^ 2) := by ring
    rw [he] at hc
    linarith
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change (S.card : ℝ) ≤ _
    rw [he, Finset.card_empty, Nat.cast_zero]
    have hlen : (0 : ℝ) ≤ (U : ℝ) - (L : ℝ) :=
      sub_nonneg.mpr (Nat.cast_le.mpr hLU)
    positivity

/-- A non-squarefree `n` with `0 < n ≤ K²` is divisible by `k²` for some `2 ≤ k ≤ K`, so
the non-squarefree elements of `S` are counted by the sum over `k`. -/
theorem card_le_squarefree_card_add_square_multiples
    (S : Finset ℕ) (K : ℕ) (hS : ∀ n ∈ S, 0 < n ∧ n ≤ K ^ 2) :
    S.card ≤ (S.filter Squarefree).card +
      ∑ k ∈ Finset.Icc 2 K, (S.filter (fun n => k ^ 2 ∣ n)).card := by
  classical
  have hcover : S.filter (fun n => ¬ Squarefree n) ⊆
      (Finset.Icc 2 K).biUnion (fun k => S.filter (fun n => k ^ 2 ∣ n)) := by
    intro n hn
    obtain ⟨hnS, hnSq⟩ := Finset.mem_filter.mp hn
    rw [Nat.squarefree_iff_prime_squarefree] at hnSq
    push Not at hnSq
    obtain ⟨p, hp, hpn⟩ := hnSq
    have hp2 : p ^ 2 ∣ n := by simpa only [pow_two] using hpn
    have hple : p ^ 2 ≤ n := Nat.le_of_dvd (hS n hnS).1 hp2
    have hpK : p ≤ K := by nlinarith [(hS n hnS).2]
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_Icc.mpr ⟨hp.two_le, hpK⟩,
      Finset.mem_filter.mpr ⟨hnS, hp2⟩⟩
  have hbad := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hpart := Finset.card_filter_add_card_filter_not (s := S) Squarefree
  omega

theorem sum_reciprocal_squares_from_two_le (K : ℕ) :
    (∑ k ∈ Finset.Icc 2 K, (1 : ℝ) / ((k : ℝ) ^ 2)) ≤ 3 / 4 := by
  have haux : ∀ K : ℕ, 2 ≤ K →
      (∑ k ∈ Finset.Icc 2 K, (1 : ℝ) / ((k : ℝ) ^ 2)) ≤ 3 / 4 - 1 / (K : ℝ) := by
    intro K hK
    induction K, hK using Nat.le_induction with
    | base => norm_num
    | succ K hK ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hKR : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
      have hK1R : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
      have hterm : (1 : ℝ) / (((K + 1 : ℕ) : ℝ) ^ 2) ≤
          1 / (K : ℝ) - 1 / ((K + 1 : ℕ) : ℝ) := by
        have he : (1 : ℝ) / (K : ℝ) - 1 / ((K + 1 : ℕ) : ℝ) =
            1 / ((K : ℝ) * ((K + 1 : ℕ) : ℝ)) := by
          field_simp
          push_cast
          ring
        rw [he]
        apply one_div_le_one_div_of_le (mul_pos hKR hK1R)
        push_cast
        nlinarith
      linarith
  by_cases hK : 2 ≤ K
  · exact (haux K hK).trans (sub_le_self _ (by positivity))
  · have he : Finset.Icc 2 K = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    rw [he, Finset.sum_empty]
    norm_num

/-- If `U ≤ K² + 1` and `(b, D) = 1`, the squarefree `n ∈ [L, U)` with `n ≡ b (mod D)` and
`(n, M) = 1` number at least `(1/4) ((U - L)/D) φ(M)/M - 2τ(M)(K + 1)`. -/
theorem squarefree_coprime_progression_card_lower
    (L U D b M K : ℕ) (hL : 0 < L) (hLU : L ≤ U) (hUK : U ≤ K ^ 2 + 1)
    (hD : 0 < D) (hM : Squarefree M) (hDM : Nat.Coprime D M)
    (hb : Nat.Coprime b D) :
    (1 / 4 : ℝ) * (((U : ℝ) - (L : ℝ)) / (D : ℝ)) *
        ((Nat.totient M : ℝ) / (M : ℝ)) -
        2 * (M.divisors.card : ℝ) * ((K : ℝ) + 1) ≤
      ((((Finset.Ico L U).filter (fun n => n ≡ b [MOD D])).filter
        (fun n => Nat.Coprime n M)).filter Squarefree).card := by
  classical
  let S := ((Finset.Ico L U).filter (fun n => n ≡ b [MOD D])).filter
    (fun n => Nat.Coprime n M)
  let α : ℝ := (((U : ℝ) - (L : ℝ)) / (D : ℝ)) *
    ((Nat.totient M : ℝ) / (M : ℝ))
  let τ : ℝ := M.divisors.card
  have hα : 0 ≤ α := by
    have hlen : (0 : ℝ) ≤ (U : ℝ) - (L : ℝ) :=
      sub_nonneg.mpr (Nat.cast_le.mpr hLU)
    dsimp [α]
    positivity
  have hτ : 0 ≤ τ := Nat.cast_nonneg _
  have hbase : α - 2 * τ ≤ (S.card : ℝ) := by
    have h := (abs_le.mp (abs_coprime_progression_card_sub_totient_density
      L U D b M hLU hD hM hDM)).1
    change -(2 * τ) ≤ (S.card : ℝ) - α at h
    linarith
  have hremove := card_le_squarefree_card_add_square_multiples S K (by
    intro n hn
    have hnI := Finset.mem_Ico.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
    exact ⟨hL.trans_le hnI.1, by omega⟩)
  have hremoveR : (S.card : ℝ) ≤ ((S.filter Squarefree).card : ℝ) +
      ∑ k ∈ Finset.Icc 2 K, ((S.filter (fun n => k ^ 2 ∣ n)).card : ℝ) := by
    exact_mod_cast hremove
  have hsquares : (∑ k ∈ Finset.Icc 2 K,
      ((S.filter (fun n => k ^ 2 ∣ n)).card : ℝ)) ≤
      α * (3 / 4 : ℝ) + 2 * τ * (K : ℝ) := by
    calc
      _ ≤ ∑ k ∈ Finset.Icc 2 K, (α / ((k : ℝ) ^ 2) + 2 * τ) := by
        apply Finset.sum_le_sum
        intro k hk
        exact coprime_progression_square_multiples_card_le L U D b M k hLU hD hM
          hDM hb (by have := (Finset.mem_Icc.mp hk).1; omega)
      _ = α * (∑ k ∈ Finset.Icc 2 K, (1 : ℝ) / ((k : ℝ) ^ 2)) +
          2 * τ * ((Finset.Icc 2 K).card : ℝ) := by
        simp only [Finset.sum_add_distrib, div_eq_mul_inv, ← Finset.mul_sum,
          Finset.sum_const, nsmul_eq_mul, one_mul]
        ring
      _ ≤ α * (3 / 4 : ℝ) + 2 * τ * (K : ℝ) := by
        apply add_le_add (mul_le_mul_of_nonneg_left
          (sum_reciprocal_squares_from_two_le K) hα)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast (show (Finset.Icc 2 K).card ≤ K by
          rw [Nat.card_Icc]
          omega)
  have hfinal : α / 4 - 2 * τ * ((K : ℝ) + 1) ≤
      ((S.filter Squarefree).card : ℝ) := by linarith
  convert hfinal using 1
  dsimp [α, τ]
  ring

end ErdosStraus.ProgressionEstimates
