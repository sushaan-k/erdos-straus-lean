import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.Tactic
import Mathlib.Data.Int.CardIntervalMod
import ErdosStraus.CubicSums.HarmonicSums
import ErdosStraus.Estimates.SquarefreeCounts
import ErdosStraus.CubicSums.Reindexing
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.ZetaValues

/-!
# Lemma 4.1: a divisor identity for `τ(n²)`

We prove the identity `τ(n²) = ∑_{k² ∣ n} μ(k) τ₃(n/k²)` and the asymptotic
`∑_{n ≤ L} τ(n²)/n = (log L)³/(6ζ(2)) + O((log L)²)` with an explicit constant. For the latter
the sum is written as `∑_{k ≤ √L} μ(k)/k² ∑_{xyz ≤ L/k²} 1/(xyz)` and the estimate (9) is
applied to each inner sum.
We also prove the majorant `τ(n²) ≤ τ₃(n) ≤ 3 ∑_{d ∣ n, d³ ≤ n²} τ(d)` from the proof of
Lemma 4.4, the bound `∑_{n ≤ N} τ(n²)/n² ≤ ζ(2)³`, and the main term of the Möbius sum
restricted to `(k, M) = 1` that enters Proposition 4.3.
-/

namespace ErdosStraus.DivisorEstimates

open scoped BigOperators

/-! ## Divisor convolutions -/

theorem divisor_card_mul_le (m n : ℕ) :
    (m * n).divisors.card ≤ m.divisors.card * n.divisors.card := by
  rw [Nat.divisors_mul]
  exact Finset.card_mul_le

/-- A Dirichlet convolution of nonnegative functions, summed over `n ≤ Y`, is at most the
product of their partial sums up to `Y`. -/
theorem divisor_convolution_sum_le_product (Y : ℕ) (f g : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) :
    (∑ n ∈ Finset.Icc 1 Y, ∑ d ∈ n.divisors, f d * g (n / d)) ≤
      (∑ d ∈ Finset.Icc 1 Y, f d) * (∑ q ∈ Finset.Icc 1 Y, g q) := by
  classical
  let S := (Finset.Icc 1 Y).sigma (fun n => n.divisors)
  let F : ((n : ℕ) × ℕ) → ℕ × ℕ := fun x => (x.2, x.1 / x.2)
  have hmem : ∀ x ∈ S, F x ∈ (Finset.Icc 1 Y).product (Finset.Icc 1 Y) := by
    intro x hx
    obtain ⟨hn, hd⟩ := Finset.mem_sigma.mp hx
    have hdpos := Nat.pos_of_mem_divisors hd
    have hdle := Nat.divisor_le hd
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hdpos,
      hdle.trans (Finset.mem_Icc.mp hn).2⟩, Finset.mem_Icc.mpr
        ⟨Nat.div_pos hdle hdpos,
          (Nat.div_le_self x.1 x.2).trans (Finset.mem_Icc.mp hn).2⟩⟩
  have hinj : Set.InjOn F S := by
    intro x hx y hy heq
    have hxD := (Finset.mem_sigma.mp hx).2
    have hyD := (Finset.mem_sigma.mp hy).2
    have hxyD : x.2 = y.2 := congrArg Prod.fst heq
    have hxyQ : x.1 / x.2 = y.1 / y.2 := congrArg Prod.snd heq
    have hxyN : x.1 = y.1 := by
      calc
        _ = x.2 * (x.1 / x.2) := (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hxD)).symm
        _ = y.2 * (y.1 / y.2) := congrArg₂ (· * ·) hxyD hxyQ
        _ = _ := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hyD)
    exact Sigma.ext hxyN (by simpa using hxyD)
  calc
    _ = ∑ x ∈ S, f x.2 * g (x.1 / x.2) := Finset.sum_sigma' _ _ _
    _ = ∑ x ∈ S.image F, f x.1 * g x.2 := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑ x ∈ (Finset.Icc 1 Y).product (Finset.Icc 1 Y), f x.1 * g x.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        exact hmem y hy
      · intro x hx hxn
        exact mul_nonneg (hf _) (hg _)
    _ = _ := by
      exact (Finset.sum_product' (Finset.Icc 1 Y) (Finset.Icc 1 Y)
        (fun x y => f x * g y)).trans (Finset.sum_mul_sum _ _ f g).symm

theorem reciprocal_divisor_card_moment_le (Y s : ℕ) :
    (∑ n ∈ Finset.Icc 1 Y, (n.divisors.card : ℝ) / (n : ℝ) ^ s) ≤
      (∑ n ∈ Finset.Icc 1 Y, (1 : ℝ) / (n : ℝ) ^ s) ^ 2 := by
  classical
  have heq : ∀ n ∈ Finset.Icc 1 Y,
      (n.divisors.card : ℝ) / (n : ℝ) ^ s =
        ∑ d ∈ n.divisors, ((1 : ℝ) / (d : ℝ) ^ s) *
          (1 / ((n / d : ℕ) : ℝ) ^ s) := by
    intro n hn
    calc
      _ = ∑ _d ∈ n.divisors, (1 : ℝ) / (n : ℝ) ^ s := by
        simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro d hd
        have hprod : (n : ℝ) = (d : ℝ) * ((n / d : ℕ) : ℝ) := by
          exact_mod_cast (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)).symm
        rw [hprod, mul_pow, one_div_mul_one_div]
  rw [Finset.sum_congr rfl heq]
  have h := divisor_convolution_sum_le_product Y (fun n => (1 : ℝ) / (n : ℝ) ^ s)
    (fun n => (1 : ℝ) / (n : ℝ) ^ s) (by intro n; positivity) (by intro n; positivity)
  simpa only [pow_two] using h

/-! ## The majorant `τ(n²) ≤ 3 ∑_{d ∣ n, d³ ≤ n²} τ(d)` -/

/-- The divisor function `τ₃ = τ * 1`, which counts ordered factorizations `n = abc`. -/
noncomputable def tripleDivisorAF : ArithmeticFunction ℕ :=
  ArithmeticFunction.sigma 0 * ArithmeticFunction.zeta

theorem tripleDivisorAF_eq_sum (n : ℕ) :
    tripleDivisorAF n = ∑ d ∈ n.divisors, d.divisors.card := by
  rw [tripleDivisorAF, ArithmeticFunction.mul_zeta_apply]
  simp only [ArithmeticFunction.sigma_zero_apply]

theorem tripleDivisorAF_multiplicative : tripleDivisorAF.IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_sigma.mul ArithmeticFunction.isMultiplicative_zeta.natCast

theorem tripleDivisorAF_prime_pow (p e : ℕ) (hp : Nat.Prime p) :
    tripleDivisorAF (p ^ e) = ∑ j ∈ Finset.range (e + 1), (j + 1) := by
  rw [tripleDivisorAF, ArithmeticFunction.mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
  simp only [ArithmeticFunction.sigma_zero_apply_prime_pow hp]

theorem two_mul_add_one_le_triple_divisor_prime_power (e : ℕ) :
    2 * e + 1 ≤ ∑ j ∈ Finset.range (e + 1), (j + 1) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ]
    omega

/-- `τ(n²) ≤ τ₃(n)`, the first inequality in the proof of Lemma 4.4. At a prime power it reads
`2e + 1 ≤ ∑_{j ≤ e} (j + 1)`. -/
theorem square_divisor_card_le_tripleDivisorAF {n : ℕ} (hn : n ≠ 0) :
    (n ^ 2).divisors.card ≤ tripleDivisorAF n := by
  classical
  rw [Nat.card_divisors (pow_ne_zero 2 hn),
    tripleDivisorAF_multiplicative.multiplicative_factorization tripleDivisorAF hn]
  rw [Nat.primeFactors_pow n (by norm_num : 2 ≠ 0)]
  rw [Finsupp.prod_of_support_subset _ (s := n.primeFactors) (by rw [n.support_factorization])]
  · apply Finset.prod_le_prod'
    intro p hp
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    rw [tripleDivisorAF_prime_pow p (n.factorization p) (Nat.prime_of_mem_primeFactors hp)]
    exact two_mul_add_one_le_triple_divisor_prime_power _
  · intro p hp
    simp only [pow_zero,
      tripleDivisorAF_multiplicative.map_one]

/-- The pairs `((d, c), (a, b))` with `d * c = n ≠ 0` and `a * b = d`. -/
noncomputable def tripleFactorSigma (n : ℕ) : Finset ((_x : ℕ × ℕ) × (ℕ × ℕ)) :=
  n.divisorsAntidiagonal.sigma (fun x => x.1.divisorsAntidiagonal)

/-- The ordered factorizations `n = a * b * c`, as triples `((a, b), c)`; empty for `n = 0`. -/
noncomputable def factorTriples (n : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (tripleFactorSigma n).image (fun x => (x.2, x.1.2))

theorem mem_factorTriples {n a b c : ℕ} :
    ((a, b), c) ∈ factorTriples n ↔ a * b * c = n ∧ n ≠ 0 := by
  classical
  unfold factorTriples tripleFactorSigma
  simp only [Finset.mem_image, Finset.mem_sigma, Nat.mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨⟨⟨d, e⟩, f, g⟩, ⟨⟨hde, hn⟩, hfg, hd⟩, heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
    exact ⟨by simpa [hfg] using hde, hn⟩
  · rintro ⟨hprod, hn⟩
    refine ⟨⟨(a * b, c), (a, b)⟩, ⟨⟨hprod, hn⟩, rfl, ?_⟩, rfl⟩
    intro hab
    change a * b = 0 at hab
    rw [hab, zero_mul] at hprod
    exact hn hprod.symm

theorem card_divisorsAntidiagonal (n : ℕ) : n.divisorsAntidiagonal.card = n.divisors.card := by
  classical
  rw [Finset.card_eq_sum_ones, Nat.sum_divisorsAntidiagonal' (fun _ _ => (1 : ℕ))]
  simp

theorem flatten_tripleFactorSigma_inj (n : ℕ) :
    Set.InjOn (fun x : (_y : ℕ × ℕ) × (ℕ × ℕ) => (x.2, x.1.2))
      (tripleFactorSigma n) := by
  classical
  intro x hx y hy heq
  obtain ⟨hx1, hx2⟩ := Finset.mem_sigma.mp hx
  obtain ⟨hy1, hy2⟩ := Finset.mem_sigma.mp hy
  have hxy2 : x.2 = y.2 := congrArg Prod.fst heq
  have hxy12 : x.1.2 = y.1.2 := congrArg (fun z : (ℕ × ℕ) × ℕ => z.2) heq
  have hxy11 : x.1.1 = y.1.1 := by
    rw [← (Nat.mem_divisorsAntidiagonal.mp hx2).1,
      ← (Nat.mem_divisorsAntidiagonal.mp hy2).1, hxy2]
  exact Sigma.ext (Prod.ext hxy11 hxy12) (by simpa using hxy2)

theorem factorTriples_card (n : ℕ) : (factorTriples n).card = tripleDivisorAF n := by
  classical
  rw [factorTriples, Finset.card_image_iff.mpr (flatten_tripleFactorSigma_inj n), tripleFactorSigma,
    Finset.card_sigma, tripleDivisorAF_eq_sum]
  simp_rw [card_divisorsAntidiagonal]
  exact Nat.sum_divisorsAntidiagonal (fun d _ => d.divisors.card)

theorem factorTriples_sum_pair_product (n : ℕ) (f : ℕ → ℕ) :
    (∑ t ∈ factorTriples n, f (t.1.1 * t.1.2)) =
      ∑ d ∈ n.divisors, d.divisors.card * f d := by
  classical
  rw [factorTriples, Finset.sum_image (flatten_tripleFactorSigma_inj n)]
  change (∑ x ∈ tripleFactorSigma n, f (x.2.1 * x.2.2)) = _
  unfold tripleFactorSigma
  rw [← Finset.sum_sigma' n.divisorsAntidiagonal
    (fun dc => dc.1.divisorsAntidiagonal) (fun _ ab => f (ab.1 * ab.2))]
  calc
    _ = ∑ dc ∈ n.divisorsAntidiagonal, dc.1.divisors.card * f dc.1 := by
      apply Finset.sum_congr rfl
      intro dc hdc
      have hh : (∑ ab ∈ dc.1.divisorsAntidiagonal, f (ab.1 * ab.2)) =
          ∑ _ab ∈ dc.1.divisorsAntidiagonal, f dc.1 := by
        apply Finset.sum_congr rfl
        intro ab hab
        rw [(Nat.mem_divisorsAntidiagonal.mp hab).1]
      rw [hh, Finset.sum_const, nsmul_eq_mul, card_divisorsAntidiagonal]
      simp
    _ = _ := Nat.sum_divisorsAntidiagonal (fun d _ => d.divisors.card * f d)

theorem factorTriples_short_card (n : ℕ) :
    ((factorTriples n).filter (fun t => (t.1.1 * t.1.2) ^ 3 ≤ n ^ 2)).card =
      ∑ d ∈ n.divisors.filter (fun d => d ^ 3 ≤ n ^ 2), d.divisors.card := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hh := factorTriples_sum_pair_product n (fun d => if d ^ 3 ≤ n ^ 2 then 1 else 0)
  simpa only [Finset.sum_filter, mul_ite, mul_one, mul_zero] using hh

theorem pair_product_cube_le_product_square (a b c : ℕ) (ha : a ≤ c) (hb : b ≤ c) :
    (a * b) ^ 3 ≤ (a * b * c) ^ 2 := by
  have hh := Nat.mul_le_mul_left ((a * b) ^ 2) (Nat.mul_le_mul ha hb)
  nlinarith only [hh]

theorem factorTriple_has_short_pair (a b c n : ℕ) (hprod : a * b * c = n) :
    (a * b) ^ 3 ≤ n ^ 2 ∨ (b * c) ^ 3 ≤ n ^ 2 ∨ (c * a) ^ 3 ≤ n ^ 2 := by
  by_cases hac : a ≤ c
  · by_cases hbc : b ≤ c
    · exact Or.inl (hprod ▸ pair_product_cube_le_product_square a b c hac hbc)
    · right; right
      have hcb : c ≤ b := by omega
      have hab : a ≤ b := hac.trans hcb
      have hp : c * a * b = n := by nlinarith only [hprod]
      exact hp ▸ pair_product_cube_le_product_square c a b hcb hab
  · by_cases hab : a ≤ b
    · right; right
      have hca : c ≤ a := by omega
      have hcb : c ≤ b := hca.trans hab
      have hp : c * a * b = n := by nlinarith only [hprod]
      exact hp ▸ pair_product_cube_le_product_square c a b hcb hab
    · right; left
      have hba : b ≤ a := by omega
      have hca : c ≤ a := by omega
      have hp : b * c * a = n := by nlinarith only [hprod]
      exact hp ▸ pair_product_cube_le_product_square b c a hba hca

theorem tripleDivisorAF_le_three_short_divisor_sum (n : ℕ) :
    tripleDivisorAF n ≤ 3 *
      ∑ d ∈ n.divisors.filter (fun d => d ^ 3 ≤ n ^ 2), d.divisors.card := by
  classical
  let S := factorTriples n
  let A := S.filter (fun t => (t.1.1 * t.1.2) ^ 3 ≤ n ^ 2)
  let B := S.filter (fun t => (t.1.2 * t.2) ^ 3 ≤ n ^ 2)
  let C := S.filter (fun t => (t.2 * t.1.1) ^ 3 ≤ n ^ 2)
  have hcover : S ⊆ (A ∪ B) ∪ C := by
    rintro ⟨⟨a, b⟩, c⟩ ht
    have hp := (mem_factorTriples.mp ht).1
    obtain hh | hh | hh := factorTriple_has_short_pair a b c n hp
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht, hh⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht, hh⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht, hh⟩)
  have hBA : B.card ≤ A.card := by
    apply Finset.card_le_card_of_injOn (fun t : (ℕ × ℕ) × ℕ => ((t.1.2, t.2), t.1.1))
    · rintro ⟨⟨a, b⟩, c⟩ ht
      obtain ⟨htS, htshort⟩ := Finset.mem_filter.mp ht
      obtain ⟨hp, hn⟩ := mem_factorTriples.mp htS
      refine Finset.mem_filter.mpr ⟨mem_factorTriples.mpr ⟨?_, hn⟩, htshort⟩
      nlinarith only [hp]
    · rintro ⟨⟨a, b⟩, c⟩ ht ⟨⟨d, e⟩, f⟩ hu heq
      simp only [Prod.mk.injEq] at heq ⊢
      tauto
  have hCA : C.card ≤ A.card := by
    apply Finset.card_le_card_of_injOn (fun t : (ℕ × ℕ) × ℕ => ((t.2, t.1.1), t.1.2))
    · rintro ⟨⟨a, b⟩, c⟩ ht
      obtain ⟨htS, htshort⟩ := Finset.mem_filter.mp ht
      obtain ⟨hp, hn⟩ := mem_factorTriples.mp htS
      refine Finset.mem_filter.mpr ⟨mem_factorTriples.mpr ⟨?_, hn⟩, htshort⟩
      nlinarith only [hp]
    · rintro ⟨⟨a, b⟩, c⟩ ht ⟨⟨d, e⟩, f⟩ hu heq
      simp only [Prod.mk.injEq] at heq ⊢
      tauto
  have hcard := (Finset.card_le_card hcover).trans (Finset.card_union_le (A ∪ B) C)
  have hab := Finset.card_union_le A B
  have hA : A.card = ∑ d ∈ n.divisors.filter (fun d => d ^ 3 ≤ n ^ 2),
      d.divisors.card := factorTriples_short_card n
  have hS : S.card = tripleDivisorAF n := factorTriples_card n
  omega

/-- The hyperbola majorant `τ(n²) ≤ 3 ∑_{d ∣ n, d ≤ n^{2/3}} τ(d)` from the proof of
Lemma 4.4, with the cutoff written as `d³ ≤ n²`. -/
theorem square_divisor_card_le_three_short_divisor_sum {n : ℕ} (hn : n ≠ 0) :
    (n ^ 2).divisors.card ≤ 3 *
      ∑ d ∈ n.divisors.filter (fun d => d ^ 3 ≤ n ^ 2), d.divisors.card :=
  (square_divisor_card_le_tripleDivisorAF hn).trans
    (tripleDivisorAF_le_three_short_divisor_sum n)

/-! ## The Möbius-weighted cubic harmonic sum

Explicit bounds for the last steps of the proof of Lemma 4.1: replacing `(log (L/k²))³` by
`(log L)³` and completing the sum `∑ μ(k)/k²`. -/

theorem abs_cube_sub_cube_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    |x ^ 3 - y ^ 3| ≤ 3 * y ^ 2 * (y - x) := by
  have hy : 0 ≤ y := hx.trans hxy
  have hpow : x ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ hx hxy 3
  rw [abs_of_nonpos (sub_nonpos.mpr hpow)]
  have hx2 : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx hxy 2
  have hxy2 : x * y ≤ y ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hxy hy]
  have hsum : x ^ 2 + x * y + y ^ 2 ≤ 3 * y ^ 2 := by linarith
  have hh := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hxy)
  nlinarith only [hh]

theorem abs_log_quotient_sq_cube_sub_le {L : ℝ} (hL : 1 ≤ L) {k : ℕ}
    (hk : 1 ≤ k) (hkL : (k : ℝ) ^ 2 ≤ L) :
    |(Real.log (L / (k : ℝ) ^ 2)) ^ 3 - (Real.log L) ^ 3| ≤
      6 * (Real.log L) ^ 2 * Real.log (k : ℝ) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hkp : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq1 : 1 ≤ L / (k : ℝ) ^ 2 := (le_div_iff₀ (sq_pos_of_pos hkp)).mpr (by simpa)
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1
  have hlogq : 0 ≤ Real.log (L / (k : ℝ) ^ 2) := Real.log_nonneg hq1
  have hq : Real.log (L / (k : ℝ) ^ 2) = Real.log L - 2 * Real.log (k : ℝ) := by
    rw [Real.log_div (ne_of_gt hLp) (ne_of_gt (sq_pos_of_pos hkp)), Real.log_pow]
    norm_num
  have hlogle : Real.log (L / (k : ℝ) ^ 2) ≤ Real.log L := by rw [hq]; linarith
  have h := abs_cube_sub_cube_le hlogq hlogle
  rw [hq] at h ⊢
  nlinarith only [h]

/-- `∑_k log k / k²`. -/
noncomputable def logReciprocalSqConstant : ℝ :=
  ∑' k : ℕ, Real.log (k : ℝ) / (k : ℝ) ^ 2

theorem logReciprocalSqConstant_nonneg : 0 ≤ logReciprocalSqConstant := by
  apply tsum_nonneg
  intro k
  exact div_nonneg (Real.log_natCast_nonneg k) (sq_nonneg _)

theorem abs_moebius_log_cube_replacement_le {L : ℝ} (hL : 1 ≤ L)
    (N : ℕ) (hNL : (N : ℝ) ^ 2 ≤ L) :
    |(∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
        (Real.log (L / (k : ℝ) ^ 2)) ^ 3) -
      (Real.log L) ^ 3 *
        (∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2)| ≤
      6 * logReciprocalSqConstant * (Real.log L) ^ 2 := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 N,
        |(ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
          (Real.log (L / (k : ℝ) ^ 2)) ^ 3 -
          (Real.log L) ^ 3 * ((ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 N,
        6 * (Real.log L) ^ 2 * (Real.log (k : ℝ) / (k : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk1 := (Finset.mem_Icc.mp hk).1
      have hkN : (k : ℝ) ≤ N := Nat.cast_le.mpr (Finset.mem_Icc.mp hk).2
      have hkL : (k : ℝ) ^ 2 ≤ L :=
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hkN 2).trans hNL
      have hc := abs_log_quotient_sq_cube_sub_le hL hk1 hkL
      have hμ := abs_moebius_div_sq_le k
      have he : (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
          (Real.log (L / (k : ℝ) ^ 2)) ^ 3 -
          (Real.log L) ^ 3 * ((ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2) =
        ((ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2) *
          ((Real.log (L / (k : ℝ) ^ 2)) ^ 3 - (Real.log L) ^ 3) := by ring
      rw [he, abs_mul]
      have hh := mul_le_mul hμ hc (abs_nonneg _)
        (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg (k : ℝ)))
      convert hh using 1
      ring
    _ = 6 * (Real.log L) ^ 2 *
        ∑ k ∈ Finset.Icc 1 N, Real.log (k : ℝ) / (k : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ 6 * (Real.log L) ^ 2 * logReciprocalSqConstant := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Summable.sum_le_tsum _ (fun k hk =>
        div_nonneg (Real.log_natCast_nonneg k) (sq_nonneg _)) summable_log_div_sq
    _ = _ := by ring

theorem abs_moebius_log_cube_sub_main_le {L : ℝ} (hL : 1 ≤ L)
    (N : ℕ) (hN : 0 < N) (hNL : (N : ℝ) ^ 2 ≤ L)
    (hlogN : Real.log L ≤ 4 * (N : ℝ)) :
    |(∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
        (Real.log (L / (k : ℝ) ^ 2)) ^ 3) -
      (Real.log L) ^ 3 / (Real.pi ^ 2 / 6)| ≤
      (6 * logReciprocalSqConstant + 4) * (Real.log L) ^ 2 := by
  have hreplace := abs_moebius_log_cube_replacement_le hL N hNL
  have hpartial := abs_moebius_reciprocal_sq_partial_sub_constant_le N hN
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hconst : |(Real.log L) ^ 3 *
        (∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2) -
      (Real.log L) ^ 3 / (Real.pi ^ 2 / 6)| ≤ 4 * (Real.log L) ^ 2 := by
    have he : (Real.log L) ^ 3 *
        (∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2) -
        (Real.log L) ^ 3 / (Real.pi ^ 2 / 6) =
      (Real.log L) ^ 3 *
        ((∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2) -
          1 / (Real.pi ^ 2 / 6)) := by ring
    rw [he, abs_mul, abs_of_nonneg (pow_nonneg hlog _)]
    calc
      _ ≤ (Real.log L) ^ 3 * (1 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hpartial (pow_nonneg hlog _)
      _ ≤ 4 * (Real.log L) ^ 2 := by
        rw [mul_one_div]
        apply (div_le_iff₀ hNp).mpr
        have hh := mul_le_mul_of_nonneg_left hlogN (sq_nonneg (Real.log L))
        nlinarith only [hh]
  have ht := abs_add_le
    ((∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
        (Real.log (L / (k : ℝ) ^ 2)) ^ 3) -
      (Real.log L) ^ 3 * (∑ k ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2))
    ((Real.log L) ^ 3 * (∑ k ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2) -
      (Real.log L) ^ 3 / (Real.pi ^ 2 / 6))
  have he : (∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
        (Real.log (L / (k : ℝ) ^ 2)) ^ 3) -
      (Real.log L) ^ 3 * (∑ k ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2) +
      ((Real.log L) ^ 3 * (∑ k ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2) -
      (Real.log L) ^ 3 / (Real.pi ^ 2 / 6)) =
      (∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
        (Real.log (L / (k : ℝ) ^ 2)) ^ 3) -
      (Real.log L) ^ 3 / (Real.pi ^ 2 / 6) := by ring
  rw [he] at ht
  nlinarith only [ht, hreplace, hconst]

/-- `∑_{k ≤ N} μ(k)/k² ∑_{xyz ≤ L/k²} 1/(xyz)`. -/
noncomputable def moebiusHarmonicCubic (L : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
    harmonicTriple (L / (k : ℝ) ^ 2)

theorem abs_moebiusHarmonicCubic_sub_log_sum_le {L : ℝ} (hL : 1 ≤ L)
    (N : ℕ) (hNL : (N : ℝ) ^ 2 ≤ L) :
    |moebiusHarmonicCubic L N -
      (∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
        (Real.log (L / (k : ℝ) ^ 2)) ^ 3) / 6| ≤
      4 * (Real.pi ^ 2 / 6) * (1 + Real.log L) ^ 2 := by
  unfold moebiusHarmonicCubic
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 N,
        |(ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 * harmonicTriple (L / (k : ℝ) ^ 2) -
          ((ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
            (Real.log (L / (k : ℝ) ^ 2)) ^ 3) / 6| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 N,
        4 * (1 + Real.log L) ^ 2 * (1 / (k : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk1 := (Finset.mem_Icc.mp hk).1
      have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have hkpos : (0 : ℝ) < k := zero_lt_one.trans_le hk1R
      have hkN : (k : ℝ) ≤ N := Nat.cast_le.mpr (Finset.mem_Icc.mp hk).2
      have hkL : (k : ℝ) ^ 2 ≤ L := (pow_le_pow_left₀ (Nat.cast_nonneg _) hkN 2).trans hNL
      have hq1 : 1 ≤ L / (k : ℝ) ^ 2 := (le_div_iff₀ (sq_pos_of_pos hkpos)).mpr (by simpa)
      have hqL : L / (k : ℝ) ^ 2 ≤ L := div_le_self (zero_le_one.trans hL) (by nlinarith)
      have hlogq := Real.log_nonneg hq1
      have hlogL : Real.log (L / (k : ℝ) ^ 2) ≤ Real.log L :=
        Real.log_le_log (zero_lt_one.trans_le hq1) hqL
      have hc := abs_harmonicTriple_sub_main_le hq1
      have hc' : |harmonicTriple (L / (k : ℝ) ^ 2) -
          (Real.log (L / (k : ℝ) ^ 2)) ^ 3 / 6| ≤ 4 * (1 + Real.log L) ^ 2 :=
        hc.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) 2)
          (by norm_num))
      have he : (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 * harmonicTriple (L / (k : ℝ) ^ 2) -
          ((ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
            (Real.log (L / (k : ℝ) ^ 2)) ^ 3) / 6 =
        ((ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2) *
          (harmonicTriple (L / (k : ℝ) ^ 2) - (Real.log (L / (k : ℝ) ^ 2)) ^ 3 / 6) := by ring
      rw [he, abs_mul]
      have hh := mul_le_mul (abs_moebius_div_sq_le k) hc' (abs_nonneg _)
        (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg (k : ℝ)))
      convert hh using 1
      ring
    _ = 4 * (1 + Real.log L) ^ 2 * ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ 4 * (1 + Real.log L) ^ 2 * (Real.pi ^ 2 / 6) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← hasSum_zeta_two.tsum_eq]
      exact Summable.sum_le_tsum _ (fun k hk => by positivity) hasSum_zeta_two.summable
    _ = _ := by ring

theorem abs_moebiusHarmonicCubic_sub_main_le {L : ℝ} (hL : 1 ≤ L)
    (N : ℕ) (hN : 0 < N) (hNL : (N : ℝ) ^ 2 ≤ L)
    (hlogN : Real.log L ≤ 4 * (N : ℝ)) :
    |moebiusHarmonicCubic L N - (Real.log L) ^ 3 / (6 * (Real.pi ^ 2 / 6))| ≤
      (4 * (Real.pi ^ 2 / 6) + logReciprocalSqConstant + 1) * (1 + Real.log L) ^ 2 := by
  let S := ∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
    (Real.log (L / (k : ℝ) ^ 2)) ^ 3
  have h₁ := abs_moebiusHarmonicCubic_sub_log_sum_le hL N hNL
  have h₂ := abs_moebius_log_cube_sub_main_le hL N hN hNL hlogN
  change |moebiusHarmonicCubic L N - S / 6| ≤ _ at h₁
  change |S - (Real.log L) ^ 3 / (Real.pi ^ 2 / 6)| ≤ _ at h₂
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hshape : (Real.log L) ^ 2 ≤ (1 + Real.log L) ^ 2 := by nlinarith
  have hc : 0 ≤ logReciprocalSqConstant + 1 := by
    linarith [logReciprocalSqConstant_nonneg]
  have h₂' : |S / 6 - (Real.log L) ^ 3 / (6 * (Real.pi ^ 2 / 6))| ≤
      (logReciprocalSqConstant + 1) * (1 + Real.log L) ^ 2 := by
    have he : S / 6 - (Real.log L) ^ 3 / (6 * (Real.pi ^ 2 / 6)) =
        (S - (Real.log L) ^ 3 / (Real.pi ^ 2 / 6)) / 6 := by ring
    rw [he, abs_div]
    norm_num
    have hh := mul_le_mul_of_nonneg_left hshape hc
    nlinarith only [h₂, hh, sq_nonneg (Real.log L)]
  have ht := abs_add_le (moebiusHarmonicCubic L N - S / 6)
    (S / 6 - (Real.log L) ^ 3 / (6 * (Real.pi ^ 2 / 6)))
  have he : moebiusHarmonicCubic L N - S / 6 +
      (S / 6 - (Real.log L) ^ 3 / (6 * (Real.pi ^ 2 / 6))) =
      moebiusHarmonicCubic L N - (Real.log L) ^ 3 / (6 * (Real.pi ^ 2 / 6)) := by ring
  rw [he] at ht
  nlinarith only [ht, h₁, h₂']

/-- With cutoff `k ≤ ⌊√L⌋`, the Möbius-weighted cubic harmonic sum equals
`(log L)³/(6ζ(2)) + O((1 + log L)²)` with an explicit constant. -/
theorem abs_moebiusHarmonicCubic_sqrt_sub_main_le {L : ℝ} (hL : 1 ≤ L) :
    |moebiusHarmonicCubic L ⌊Real.sqrt L⌋₊ -
        (Real.log L) ^ 3 / (6 * (Real.pi ^ 2 / 6))| ≤
      (4 * (Real.pi ^ 2 / 6) + logReciprocalSqConstant + 1) * (1 + Real.log L) ^ 2 := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hroot : 1 ≤ Real.sqrt L := by simpa using Real.sqrt_le_sqrt hL
  have hN : 0 < ⌊Real.sqrt L⌋₊ := Nat.floor_pos.mpr hroot
  have hN1 : (1 : ℝ) ≤ ⌊Real.sqrt L⌋₊ := by exact_mod_cast hN
  have hfloor := Nat.floor_le (Real.sqrt_nonneg L)
  have hfloor' := Nat.lt_floor_add_one (Real.sqrt L)
  have hsq := Real.sq_sqrt hL0
  have hNL : (⌊Real.sqrt L⌋₊ : ℝ) ^ 2 ≤ L := by
    nlinarith [show (0 : ℝ) ≤ ⌊Real.sqrt L⌋₊ by positivity]
  have hlog : Real.log L ≤ 4 * (⌊Real.sqrt L⌋₊ : ℝ) := by
    have hh := Real.log_le_rpow_div hL0 (by norm_num : 0 < (1 / 2 : ℝ))
    rw [← Real.sqrt_eq_rpow] at hh
    nlinarith
  exact abs_moebiusHarmonicCubic_sub_main_le hL _ hN hNL hlog

/-! ## The asymptotic for `∑_{a ≤ L} τ(a²)/a` -/

theorem residueHarmonicTriple_mod_one (b₁ b₂ b₃ : ℕ) (T : ℝ) :
    residueHarmonicTriple 1 b₁ b₂ b₃ T = harmonicTriple T := by
  simp [residueHarmonicTriple, residueHarmonicDouble, residueHarmonicTransform,
    residueLogMoment, harmonicTriple, harmonicDouble, harmonicTransform, logMoment, Nat.ModEq,
    Nat.mod_one]

theorem localResidueTripleClasses_mod_one (aM u k : ℕ) :
    localResidueTripleClasses 1 aM u k = {((0, 0), 0)} := by
  classical
  have hb : (((Finset.range 1).product (Finset.range 1)).product (Finset.range 1)) =
      {((0, 0), 0)} := by decide
  rw [localResidueTripleClasses, hb]
  apply Finset.filter_true_of_mem
  intro t ht
  have ht' := Finset.mem_singleton.mp ht
  subst t
  constructor <;> simp [Estimates.congMod, Nat.mod_one]

theorem square_divisor_reciprocal_sum_eq_moebius_harmonic_full (N : ℕ) :
    (∑ a ∈ Finset.Icc 1 N, ((a ^ 2).divisors.card : ℝ) / (a : ℝ)) =
      ∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
        harmonicTriple ((N : ℝ) / (k : ℝ) ^ 2) := by
  have h := local_square_divisor_reciprocal_eq_residue_harmonic_triples
    N 1 0 0 (by norm_num)
  simpa [Estimates.congMod, localResidueTripleClasses_mod_one, residueHarmonicTriple_mod_one,
    Finset.sum_const, nsmul_eq_mul, mul_one_div, Nat.mod_one, div_eq_mul_inv] using h

theorem harmonicTriple_eq_zero_of_lt_one {T : ℝ} (hT : T < 1) : harmonicTriple T = 0 := by
  unfold harmonicTriple harmonicTransform
  rw [Nat.floor_eq_zero.mpr hT]
  simp

/-- `∑_{a ≤ N} τ(a²)/a = ∑_{k ≤ √N} μ(k)/k² ∑_{xyz ≤ N/k²} 1/(xyz)`. -/
theorem square_divisor_reciprocal_sum_eq_moebius_harmonic (N : ℕ) :
    (∑ a ∈ Finset.Icc 1 N, ((a ^ 2).divisors.card : ℝ) / (a : ℝ)) =
      moebiusHarmonicCubic (N : ℝ) ⌊Real.sqrt (N : ℝ)⌋₊ := by
  rw [square_divisor_reciprocal_sum_eq_moebius_harmonic_full]
  unfold moebiusHarmonicCubic
  by_cases hN : N = 0
  · simp [hN]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hroot := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hrootnn := Real.sqrt_nonneg (N : ℝ)
  have hfloor := Nat.floor_le hrootnn
  have hsmall : ⌊Real.sqrt (N : ℝ)⌋₊ ≤ N := by
    have hh : (⌊Real.sqrt (N : ℝ)⌋₊ : ℝ) ≤ N := by nlinarith
    exact_mod_cast hh
  apply (Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hsmall) _).symm
  intro k hk hnot
  have hk1 := (Finset.mem_Icc.mp hk).1
  have hkp : (0 : ℝ) < k := Nat.cast_pos.mpr hk1
  have hknot : ⌊Real.sqrt (N : ℝ)⌋₊ < k := by
    simp only [Finset.mem_Icc, hk1, true_and, not_le] at hnot
    exact hnot
  have hkroot : Real.sqrt (N : ℝ) < (k : ℝ) := (Nat.floor_lt hrootnn).mp hknot
  have hk2 : (N : ℝ) < (k : ℝ) ^ 2 := by nlinarith
  rw [harmonicTriple_eq_zero_of_lt_one ((div_lt_one (sq_pos_of_pos hkp)).mpr hk2), mul_zero]

/-- Lemma 4.1 at an integer cutoff `N ≥ 1`:
`|∑_{a ≤ N} τ(a²)/a - (log N)³/(6ζ(2))| ≤ C (1 + log N)²` with an explicit `C`. -/
theorem abs_square_divisor_reciprocal_sum_sub_main_le (N : ℕ) (hN : 0 < N) :
    |(∑ a ∈ Finset.Icc 1 N, ((a ^ 2).divisors.card : ℝ) / (a : ℝ)) -
        (Real.log (N : ℝ)) ^ 3 / (6 * (Real.pi ^ 2 / 6))| ≤
      (4 * (Real.pi ^ 2 / 6) + logReciprocalSqConstant + 1) * (1 + Real.log (N : ℝ)) ^ 2 := by
  rw [square_divisor_reciprocal_sum_eq_moebius_harmonic]
  exact abs_moebiusHarmonicCubic_sqrt_sub_main_le (by exact_mod_cast hN)

/-- The constant in the error term of Lemma 4.1 at a real cutoff. -/
noncomputable def cubicTauSquareErrorConstant : ℝ :=
  4 * (Real.pi ^ 2 / 6) + logReciprocalSqConstant + 1 + 1 / (2 * (Real.pi ^ 2 / 6))

theorem cubicTauSquareErrorConstant_pos : 0 < cubicTauSquareErrorConstant := by
  have hz : (0 : ℝ) < Real.pi ^ 2 / 6 := by positivity
  have hs := logReciprocalSqConstant_nonneg
  unfold cubicTauSquareErrorConstant
  positivity

/-- Lemma 4.1 at a real cutoff `L ≥ 1`:
`|∑_{a ≤ L} τ(a²)/a - (log L)³/(6ζ(2))| ≤ C (1 + log L)²`. -/
theorem abs_square_divisor_reciprocal_real_sum_sub_main_le {L : ℝ} (hL : 1 ≤ L) :
    |(∑ a ∈ Finset.Icc 1 ⌊L⌋₊, ((a ^ 2).divisors.card : ℝ) / (a : ℝ)) -
        (Real.log L) ^ 3 / (6 * (Real.pi ^ 2 / 6))| ≤
      cubicTauSquareErrorConstant * (1 + Real.log L) ^ 2 := by
  let N := ⌊L⌋₊
  let Z : ℝ := Real.pi ^ 2 / 6
  let C : ℝ := 4 * Z + logReciprocalSqConstant + 1
  have hN : 0 < N := Nat.floor_pos.mpr hL
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hNL : (N : ℝ) ≤ L := Nat.floor_le hLpos.le
  have hLN : L < (N : ℝ) + 1 := Nat.lt_floor_add_one L
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlogle : Real.log (N : ℝ) ≤ Real.log L := Real.log_le_log hNp hNL
  have hlogdiff : Real.log L - Real.log (N : ℝ) ≤ 1 := by
    have hbound : L ≤ 2 * (N : ℝ) := by linarith
    have hh := Real.log_le_log hLpos hbound
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hNp)] at hh
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hlog2
    linarith
  have hz : 0 < Z := by dsimp [Z]; positivity
  have hC : 0 ≤ C := by dsimp [C]; linarith [logReciprocalSqConstant_nonneg]
  have hnat := abs_square_divisor_reciprocal_sum_sub_main_le N hN
  change |(∑ a ∈ Finset.Icc 1 N, ((a ^ 2).divisors.card : ℝ) / (a : ℝ)) -
    (Real.log (N : ℝ)) ^ 3 / (6 * Z)| ≤ C * (1 + Real.log (N : ℝ)) ^ 2 at hnat
  have hshapeN : (1 + Real.log (N : ℝ)) ^ 2 ≤ (1 + Real.log L) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hnat' := hnat.trans (mul_le_mul_of_nonneg_left hshapeN hC)
  have hcubes := abs_cube_sub_cube_le hlogN hlogle
  have hcubes' : |(Real.log (N : ℝ)) ^ 3 - (Real.log L) ^ 3| ≤ 3 * (Real.log L) ^ 2 :=
    hcubes.trans (by
      have hh := mul_le_mul_of_nonneg_left hlogdiff
        (show 0 ≤ 3 * (Real.log L) ^ 2 by positivity)
      simpa only [mul_one] using hh)
  have hmain : |(Real.log (N : ℝ)) ^ 3 / (6 * Z) - (Real.log L) ^ 3 / (6 * Z)| ≤
      (1 / (2 * Z)) * (1 + Real.log L) ^ 2 := by
    rw [← sub_div, abs_div, abs_of_pos (by positivity : 0 < 6 * Z)]
    calc
      _ ≤ (3 * (Real.log L) ^ 2) / (6 * Z) :=
        div_le_div_of_nonneg_right hcubes' (by positivity)
      _ = (1 / (2 * Z)) * (Real.log L) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith :
          (Real.log L) ^ 2 ≤ (1 + Real.log L) ^ 2) (by positivity)
  have ht := abs_add_le
    ((∑ a ∈ Finset.Icc 1 N, ((a ^ 2).divisors.card : ℝ) / (a : ℝ)) -
      (Real.log (N : ℝ)) ^ 3 / (6 * Z))
    ((Real.log (N : ℝ)) ^ 3 / (6 * Z) - (Real.log L) ^ 3 / (6 * Z))
  have he : (∑ a ∈ Finset.Icc 1 N, ((a ^ 2).divisors.card : ℝ) / (a : ℝ)) -
      (Real.log (N : ℝ)) ^ 3 / (6 * Z) +
      ((Real.log (N : ℝ)) ^ 3 / (6 * Z) - (Real.log L) ^ 3 / (6 * Z)) =
      (∑ a ∈ Finset.Icc 1 N, ((a ^ 2).divisors.card : ℝ) / (a : ℝ)) -
      (Real.log L) ^ 3 / (6 * Z) := by ring
  rw [he] at ht
  change _ ≤ (C + 1 / (2 * Z)) * (1 + Real.log L) ^ 2
  nlinarith only [ht, hnat', hmain]

/-- Lemma 4.1: `∑_{a ≤ L} τ(a²)/a = (log L)³/(6ζ(2)) + O((log L)²)` for `L ≥ e`. -/
theorem square_divisor_reciprocal_real_sum_cubic_remainder :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, Real.exp 1 ≤ L →
      |(∑ a ∈ Finset.Icc 1 ⌊L⌋₊, ((a ^ 2).divisors.card : ℝ) / (a : ℝ)) -
          (Real.log L) ^ 3 / (6 * (Real.pi ^ 2 / 6))| ≤ C * (Real.log L) ^ 2 := by
  refine ⟨4 * cubicTauSquareErrorConstant,
    mul_pos (by norm_num) cubicTauSquareErrorConstant_pos, ?_⟩
  intro L hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hL
  have hlog : 1 ≤ Real.log L := by
    have hh := Real.log_le_log (Real.exp_pos 1) hL
    simpa only [Real.log_exp] using hh
  have h := abs_square_divisor_reciprocal_real_sum_sub_main_le hL1
  have hshape : (1 + Real.log L) ^ 2 ≤ 4 * (Real.log L) ^ 2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hshape cubicTauSquareErrorConstant_pos.le
  nlinarith only [h, hh]

/-- `∑_{a ≤ L} τ(a²)/a ∼ (log L)³/(6ζ(2))`. -/
theorem square_divisor_reciprocal_real_sum_cubic_limit :
    Filter.Tendsto (fun L : ℝ =>
      (∑ a ∈ Finset.Icc 1 ⌊L⌋₊, ((a ^ 2).divisors.card : ℝ) / (a : ℝ)) /
        (Real.log L) ^ 3) Filter.atTop (nhds (1 / (6 * (Real.pi ^ 2 / 6)))) := by
  obtain ⟨C, hC, hbound⟩ := square_divisor_reciprocal_real_sum_cubic_remainder
  have hlim : Filter.Tendsto (fun L : ℝ => C / Real.log L) Filter.atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul C
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm' _ hlim
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with L hL
  have hlog : 0 < Real.log L := by
    have hh := Real.log_le_log (Real.exp_pos 1) hL
    rw [Real.log_exp] at hh
    linarith
  have h := hbound L hL
  rw [Real.norm_eq_abs]
  have he : (∑ a ∈ Finset.Icc 1 ⌊L⌋₊, ((a ^ 2).divisors.card : ℝ) / (a : ℝ)) /
      (Real.log L) ^ 3 - 1 / (6 * (Real.pi ^ 2 / 6)) =
    ((∑ a ∈ Finset.Icc 1 ⌊L⌋₊, ((a ^ 2).divisors.card : ℝ) / (a : ℝ)) -
      (Real.log L) ^ 3 / (6 * (Real.pi ^ 2 / 6))) / (Real.log L) ^ 3 := by
    field_simp [ne_of_gt hlog, Real.pi_ne_zero]
  rw [he, abs_div, abs_of_pos (pow_pos hlog 3)]
  calc
    _ ≤ (C * (Real.log L) ^ 2) / (Real.log L) ^ 3 :=
      div_le_div_of_nonneg_right h (pow_nonneg hlog.le _)
    _ = C / Real.log L := by field_simp [ne_of_gt hlog]

/-- `∑_{a ≤ L} τ(a²)/a ≍ (log L)³` for all large `L`. -/
theorem square_divisor_reciprocal_real_sum_cubic_bounds :
    ∃ c C L₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ L : ℝ, L₀ ≤ L →
      c * (Real.log L) ^ 3 ≤
        (∑ a ∈ Finset.Icc 1 ⌊L⌋₊, ((a ^ 2).divisors.card : ℝ) / (a : ℝ)) ∧
      (∑ a ∈ Finset.Icc 1 ⌊L⌋₊, ((a ^ 2).divisors.card : ℝ) / (a : ℝ)) ≤
        C * (Real.log L) ^ 3 := by
  let A : ℝ := 1 / (6 * (Real.pi ^ 2 / 6))
  have hA : 0 < A := by dsimp [A]; positivity
  have hlim := square_divisor_reciprocal_real_sum_cubic_limit
  have hlower : ∀ᶠ L : ℝ in Filter.atTop, A / 2 <
      (∑ a ∈ Finset.Icc 1 ⌊L⌋₊, ((a ^ 2).divisors.card : ℝ) / (a : ℝ)) /
        (Real.log L) ^ 3 := hlim.eventually (lt_mem_nhds (by
          change A / 2 < A
          linarith))
  have hupper : ∀ᶠ L : ℝ in Filter.atTop,
      (∑ a ∈ Finset.Icc 1 ⌊L⌋₊, ((a ^ 2).divisors.card : ℝ) / (a : ℝ)) /
        (Real.log L) ^ 3 < 2 * A := hlim.eventually (gt_mem_nhds (by
          change A < 2 * A
          linarith))
  have hall : ∀ᶠ L : ℝ in Filter.atTop,
      A / 2 * (Real.log L) ^ 3 ≤
        (∑ a ∈ Finset.Icc 1 ⌊L⌋₊, ((a ^ 2).divisors.card : ℝ) / (a : ℝ)) ∧
      (∑ a ∈ Finset.Icc 1 ⌊L⌋₊, ((a ^ 2).divisors.card : ℝ) / (a : ℝ)) ≤
        (2 * A) * (Real.log L) ^ 3 := by
    filter_upwards [hlower, hupper, Filter.eventually_ge_atTop (Real.exp 1)] with L hl hu hL
    have hlog : 0 < Real.log L := by
      have hh := Real.log_le_log (Real.exp_pos 1) hL
      rw [Real.log_exp] at hh
      linarith
    exact ⟨((lt_div_iff₀ (pow_pos hlog 3)).mp hl).le,
      ((div_lt_iff₀ (pow_pos hlog 3)).mp hu).le⟩
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp hall
  exact ⟨A / 2, 2 * A, L₀, by positivity, by positivity, hL₀⟩

/-! ## The Möbius sum over `k` prime to `M` -/

/-- `(1/ζ(2)) ∏_{p ∣ M} (1 - p⁻²)⁻¹`, the sum of `μ(k)/k²` over `k` prime to `M`. -/
noncomputable def restrictedMoebiusSquareConstant (M : ℕ) : ℝ :=
  (1 / (Real.pi ^ 2 / 6)) * ∏ p ∈ M.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹

theorem abs_restricted_moebius_log_cube_replacement_le (M : ℕ)
    {L : ℝ} (hL : 1 ≤ L) (N : ℕ) (hNL : (N : ℝ) ^ 2 ≤ L) :
    |(∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.Coprime k M),
        (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
          (Real.log (L / (k : ℝ) ^ 2)) ^ 3) -
      (Real.log L) ^ 3 *
        (∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.Coprime k M),
          (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2)| ≤
      6 * logReciprocalSqConstant * (Real.log L) ^ 2 := by
  classical
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.Coprime k M),
        |(ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
          (Real.log (L / (k : ℝ) ^ 2)) ^ 3 -
          (Real.log L) ^ 3 * ((ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.Coprime k M),
        6 * (Real.log L) ^ 2 * (Real.log (k : ℝ) / (k : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkI := Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
      have hkN : (k : ℝ) ≤ N := Nat.cast_le.mpr hkI.2
      have hkL : (k : ℝ) ^ 2 ≤ L :=
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hkN 2).trans hNL
      have hc := abs_log_quotient_sq_cube_sub_le hL hkI.1 hkL
      have he : (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
          (Real.log (L / (k : ℝ) ^ 2)) ^ 3 -
          (Real.log L) ^ 3 * ((ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2) =
        ((ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2) *
          ((Real.log (L / (k : ℝ) ^ 2)) ^ 3 - (Real.log L) ^ 3) := by ring
      rw [he, abs_mul]
      have hh := mul_le_mul (abs_moebius_div_sq_le k) hc (abs_nonneg _)
        (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg (k : ℝ)))
      (convert hh using 1; ring)
    _ = 6 * (Real.log L) ^ 2 *
        ∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.Coprime k M),
          Real.log (k : ℝ) / (k : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 6 * (Real.log L) ^ 2 * logReciprocalSqConstant := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Summable.sum_le_tsum _ (fun k hk =>
        div_nonneg (Real.log_natCast_nonneg k) (sq_nonneg _)) summable_log_div_sq
    _ = _ := by ring

theorem abs_restricted_moebius_log_cube_sub_main_le (M : ℕ) (hM : 0 < M)
    {L : ℝ} (hL : 1 ≤ L) (N : ℕ) (hN : 0 < N) (hNL : (N : ℝ) ^ 2 ≤ L)
    (hlogN : Real.log L ≤ 4 * (N : ℝ)) :
    |(∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.Coprime k M),
        (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
          (Real.log (L / (k : ℝ) ^ 2)) ^ 3) -
      restrictedMoebiusSquareConstant M * (Real.log L) ^ 3| ≤
      (6 * logReciprocalSqConstant + 4) * (Real.log L) ^ 2 := by
  classical
  let S := ∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.Coprime k M),
    (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2
  have hreplace := abs_restricted_moebius_log_cube_replacement_le M hL N hNL
  have hpartial := abs_restricted_moebius_partial_sub_constant_le M N hM hN
  change |S - restrictedMoebiusSquareConstant M| ≤ 1 / (N : ℝ) at hpartial
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hconst : |(Real.log L) ^ 3 * S -
      restrictedMoebiusSquareConstant M * (Real.log L) ^ 3| ≤ 4 * (Real.log L) ^ 2 := by
    have he : (Real.log L) ^ 3 * S -
        restrictedMoebiusSquareConstant M * (Real.log L) ^ 3 =
        (Real.log L) ^ 3 * (S - restrictedMoebiusSquareConstant M) := by ring
    rw [he, abs_mul, abs_of_nonneg (pow_nonneg hlog _)]
    calc
      _ ≤ (Real.log L) ^ 3 * (1 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hpartial (pow_nonneg hlog _)
      _ ≤ 4 * (Real.log L) ^ 2 := by
        rw [mul_one_div]
        apply (div_le_iff₀ hNp).mpr
        have hh := mul_le_mul_of_nonneg_left hlogN (sq_nonneg (Real.log L))
        nlinarith only [hh]
  have ht := abs_add_le
    ((∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.Coprime k M),
      (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
        (Real.log (L / (k : ℝ) ^ 2)) ^ 3) - (Real.log L) ^ 3 * S)
    ((Real.log L) ^ 3 * S - restrictedMoebiusSquareConstant M * (Real.log L) ^ 3)
  have he :
    ((∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.Coprime k M),
      (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
        (Real.log (L / (k : ℝ) ^ 2)) ^ 3) - (Real.log L) ^ 3 * S) +
    ((Real.log L) ^ 3 * S - restrictedMoebiusSquareConstant M * (Real.log L) ^ 3) =
    (∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.Coprime k M),
      (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
        (Real.log (L / (k : ℝ) ^ 2)) ^ 3) -
      restrictedMoebiusSquareConstant M * (Real.log L) ^ 3 := by ring
  rw [he] at ht
  nlinarith only [ht, hreplace, hconst]

/-- For `M ≥ 1` and `L ≥ 1`,
`∑_{k ≤ √L, (k, M) = 1} μ(k)/k² (log (L/k²))³ = c_M (log L)³ + O((log L)²)`
with an absolute implied constant, where `c_M = restrictedMoebiusSquareConstant M`. -/
theorem abs_restricted_moebius_log_cube_sqrt_sub_main_le (M : ℕ) (hM : 0 < M)
    {L : ℝ} (hL : 1 ≤ L) :
    |(∑ k ∈ (Finset.Icc 1 ⌊Real.sqrt L⌋₊).filter (fun k => Nat.Coprime k M),
        (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
          (Real.log (L / (k : ℝ) ^ 2)) ^ 3) -
      restrictedMoebiusSquareConstant M * (Real.log L) ^ 3| ≤
      (6 * logReciprocalSqConstant + 4) * (Real.log L) ^ 2 := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hroot : 1 ≤ Real.sqrt L := by simpa using Real.sqrt_le_sqrt hL
  have hN : 0 < ⌊Real.sqrt L⌋₊ := Nat.floor_pos.mpr hroot
  have hN1 : (1 : ℝ) ≤ ⌊Real.sqrt L⌋₊ := by exact_mod_cast hN
  have hfloor := Nat.floor_le (Real.sqrt_nonneg L)
  have hfloor' := Nat.lt_floor_add_one (Real.sqrt L)
  have hsq := Real.sq_sqrt hL0
  have hNL : (⌊Real.sqrt L⌋₊ : ℝ) ^ 2 ≤ L := by
    nlinarith [show (0 : ℝ) ≤ ⌊Real.sqrt L⌋₊ by positivity]
  have hlog : Real.log L ≤ 4 * (⌊Real.sqrt L⌋₊ : ℝ) := by
    have hh := Real.log_le_rpow_div hL0 (by norm_num : 0 < (1 / 2 : ℝ))
    rw [← Real.sqrt_eq_rpow] at hh
    nlinarith
  exact abs_restricted_moebius_log_cube_sub_main_le M hM hL _ hN hNL hlog

/-! ## The convergent sum `∑ τ(a²)/a²` -/

/-- `∑_{a ≤ N} τ(a²)/a² ≤ ζ(2)³`, since `τ(a²) ≤ τ₃(a)`. -/
theorem square_divisor_reciprocal_square_sum_le (N : ℕ) :
    (∑ a ∈ Finset.Icc 1 N, ((a ^ 2).divisors.card : ℝ) / (a : ℝ) ^ 2) ≤
      (Real.pi ^ 2 / 6) ^ 3 := by
  classical
  let B : ℝ := ∑ a ∈ Finset.Icc 1 N, (1 : ℝ) / (a : ℝ) ^ 2
  have hB : 0 ≤ B := Finset.sum_nonneg (fun a ha => by positivity)
  have hBZ : B ≤ Real.pi ^ 2 / 6 := by
    rw [← hasSum_zeta_two.tsum_eq]
    exact Summable.sum_le_tsum _ (fun a ha => by positivity) hasSum_zeta_two.summable
  have hfirst : (∑ a ∈ Finset.Icc 1 N,
      ((a ^ 2).divisors.card : ℝ) / (a : ℝ) ^ 2) ≤
      ∑ a ∈ Finset.Icc 1 N,
        ∑ d ∈ a.divisors, ((d.divisors.card : ℝ) / (d : ℝ) ^ 2) *
          (1 / ((a / d : ℕ) : ℝ) ^ 2) := by
    apply Finset.sum_le_sum
    intro a ha
    have ha0 : a ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp ha).1
    have hmajor : ((a ^ 2).divisors.card : ℝ) ≤ (tripleDivisorAF a : ℝ) := by
      exact_mod_cast square_divisor_card_le_tripleDivisorAF ha0
    calc
      _ ≤ (tripleDivisorAF a : ℝ) / (a : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hmajor (sq_nonneg _)
      _ = ∑ d ∈ a.divisors, ((d.divisors.card : ℝ) / (d : ℝ) ^ 2) *
          (1 / ((a / d : ℕ) : ℝ) ^ 2) := by
        rw [tripleDivisorAF_eq_sum, Nat.cast_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro d hd
        have hprod : (a : ℝ) = (d : ℝ) * ((a / d : ℕ) : ℝ) := by
          exact_mod_cast (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)).symm
        rw [hprod, mul_pow]
        ring
  have hconv := divisor_convolution_sum_le_product N
    (fun d => (d.divisors.card : ℝ) / (d : ℝ) ^ 2)
    (fun d => (1 : ℝ) / (d : ℝ) ^ 2)
    (fun d => by positivity) (fun d => by positivity)
  have hmoment := reciprocal_divisor_card_moment_le N 2
  change (∑ d ∈ Finset.Icc 1 N, (d.divisors.card : ℝ) / (d : ℝ) ^ 2) ≤ B ^ 2 at hmoment
  calc
    _ ≤ _ := hfirst.trans hconv
    _ ≤ B ^ 2 * B := mul_le_mul_of_nonneg_right hmoment hB
    _ = B ^ 3 := by ring
    _ ≤ _ := pow_le_pow_left₀ hB hBZ 3

theorem square_divisor_reciprocal_real_square_sum_bounded :
    ∃ B : ℝ, 0 < B ∧ ∀ L : ℝ,
      (∑ a ∈ Finset.Icc 1 ⌊L⌋₊, ((a ^ 2).divisors.card : ℝ) / (a : ℝ) ^ 2) ≤ B := by
  exact ⟨(Real.pi ^ 2 / 6) ^ 3, by positivity, fun L =>
    square_divisor_reciprocal_square_sum_le ⌊L⌋₊⟩

end ErdosStraus.DivisorEstimates

/-! ## The divisor identity -/

namespace ErdosStraus.DivisorEstimates

open Classical
open scoped BigOperators

theorem scaled_triples_at_point (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (hkn : k ^ 2 ∣ n) :
    (scaledLocalDivisorTriples n 1 0 0 k).filter
      (fun t => k ^ 2 * t.1.1 * t.1.2 * t.2 = n) = factorTriples (n / k ^ 2) := by
  ext t
  rcases t with ⟨⟨x, e⟩, y⟩
  have hq : 0 < n / k ^ 2 := Nat.div_pos (Nat.le_of_dvd hn hkn) (pow_pos hk 2)
  simp only [Finset.mem_filter, mem_scaledLocalDivisorTriples hk, mem_factorTriples]
  constructor
  · rintro ⟨⟨hx, he, hy, hle, _, _⟩, heq⟩
    refine ⟨?_, hq.ne'⟩
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hk 2)
    calc
      k ^ 2 * (x * e * y) = n := by nlinarith only [heq]
      _ = k ^ 2 * (n / k ^ 2) := (Nat.mul_div_cancel' hkn).symm
  · rintro ⟨heq, hne⟩
    have hprod : k ^ 2 * x * e * y = n := by
      calc
        _ = k ^ 2 * (x * e * y) := by ring
        _ = n := by rw [heq, Nat.mul_div_cancel' hkn]
    have hp : 0 < x * e * y := heq ▸ hq
    have hx : 0 < x := Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right hp)
    have he : 0 < e := Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_right hp)
    have hy : 0 < y := Nat.pos_of_mul_pos_left hp
    exact ⟨⟨hx, he, hy, hprod.le, by simp [Estimates.congMod, Nat.mod_one],
      by simp [Estimates.congMod, Nat.mod_one]⟩, hprod⟩

/-- The divisor identity of Lemma 4.1: `τ(n²) = ∑_{k² ∣ n} μ(k) τ₃(n/k²)`. -/
theorem tau_square_moebius (n : ℕ) :
    ((n ^ 2).divisors.card : ℝ) =
      ∑ k ∈ (Finset.Icc 1 n).filter (fun k => k ^ 2 ∣ n),
        (ArithmeticFunction.moebius k : ℝ) * tripleDivisorAF (n / k ^ 2) := by
  by_cases hn0 : n = 0
  · simp [hn0]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  let w : ℕ → ℝ := fun a => if a = n then 1 else 0
  have h := local_square_divisor_weighted_reindex n 1 0 0 w
  rw [local_coprime_weighted_moebius] at h
  have hl : (∑ a ∈ (Finset.Icc 1 n).filter (fun a => Estimates.congMod a 0 1),
      ∑ _h ∈ (a ^ 2).divisors.filter (fun h => Estimates.congMod h 0 1), w a) =
      ((n ^ 2).divisors.card : ℝ) := by
    simp [Estimates.congMod, Nat.mod_one, w, Finset.mem_Icc, hn0]
  rw [hl] at h
  rw [h, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hkI
  have hk : 0 < k := (Finset.mem_Icc.mp hkI).1
  rw [← local_divisible_weighted_scale n 1 0 0 k hk]
  have hw : ∀ t, w ((scaleLocalTriple k t).1.1 * (scaleLocalTriple k t).1.2 *
      (scaleLocalTriple k t).2) =
      if k ^ 2 * t.1.1 * t.1.2 * t.2 = n then (1 : ℝ) else 0 := by
    intro t
    unfold w scaleLocalTriple
    congr 1
    ring_nf
  simp_rw [hw]
  rw [← Finset.sum_filter]
  by_cases hkn : k ^ 2 ∣ n
  · rw [if_pos hkn, scaled_triples_at_point n k hn hk hkn]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, factorTriples_card]
  · rw [if_neg hkn]
    have hempty : (scaledLocalDivisorTriples n 1 0 0 k).filter
        (fun t => k ^ 2 * t.1.1 * t.1.2 * t.2 = n) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      have heq := (Finset.mem_filter.mp ht).2
      exact hkn ⟨t.1.1 * t.1.2 * t.2, by nlinarith only [heq]⟩
    rw [hempty, Finset.sum_empty, mul_zero]

end ErdosStraus.DivisorEstimates
