import EscAnalytic.Inputs

/-!
# Finite reciprocal Bombieri--Vinogradov bridges

This module isolates the finite summation-by-parts bookkeeping needed to pass
from maximal Chebyshev progression errors to reciprocal-prime errors.  The
analytic maximal BV estimate remains a named external input; the carrier
conversion is developed here.
-/

namespace EscAnalytic.Inputs

open Classical

noncomputable def thetaAPCoeff (q a n : ℕ) : ℝ :=
  if Nat.Prime n ∧ congMod n a q then Real.log (n : ℝ) else 0

/-- Exact prefix-sum representation of the Chebyshev progression carrier at a
natural cutoff. -/
theorem thetaAP_nat_eq_sum_range (N q a : ℕ) :
    thetaAP (N : ℝ) q a = ∑ n ∈ Finset.range (N + 1), thetaAPCoeff q a n := by
  classical
  simp only [thetaAP, thetaAPCoeff, natWindow, Nat.floor_natCast,
    Finset.sum_filter]
  let f : ℕ → ℝ := fun n =>
    if Nat.Prime n ∧ congMod n a q then Real.log (n : ℝ) else 0
  change (∑ n ∈ Finset.Icc 1 N, if 0 < (n : ℝ) then f n else 0) =
    ∑ n ∈ Finset.range (N + 1), f n
  have hleft : (∑ n ∈ Finset.Icc 1 N, if 0 < (n : ℝ) then f n else 0) =
      ∑ n ∈ Finset.Icc 1 N, f n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn1 := (Finset.mem_Icc.mp hn).1
    simp [show (0 : ℝ) < n by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)]
  rw [hleft]
  have hsum : ∀ M : ℕ, (∑ n ∈ Finset.Icc 1 M, f n) =
      ∑ n ∈ Finset.range (M + 1), f n := by
    intro M
    induction M with
    | zero => simp [f]
    | succ M ih =>
        rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ]
        exact congrArg (fun x => x + f (M + 1)) ih
  exact hsum N

noncomputable def reciprocalBVErrorCoeff (q a n : ℕ) : ℝ :=
  thetaAPCoeff q a n -
    (1 / (Nat.totient q : ℝ)) * thetaAPCoeff 1 0 n

/-- Prefix sums of the signed coefficient carrier are exactly differences of
the two Chebyshev progression carriers. -/
theorem sum_range_reciprocalBVErrorCoeff (N q a : ℕ) :
    (∑ n ∈ Finset.range (N + 1), reciprocalBVErrorCoeff q a n) =
      thetaAP (N : ℝ) q a -
        (1 / (Nat.totient q : ℝ)) * thetaAP (N : ℝ) 1 0 := by
  simp_rw [reciprocalBVErrorCoeff]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← thetaAP_nat_eq_sum_range, ← thetaAP_nat_eq_sum_range]

/-- Maximal BV controls every prefix of the signed coefficient carrier; the
modulus-one term accounts for replacing the continuous main term by the
actual unrestricted prime carrier. -/
theorem abs_sum_range_reciprocalBVErrorCoeff_le
    {x : ℝ} {N q a : ℕ} (hqpos : 0 < q) (ha : Nat.Coprime a q)
    (hN2 : 2 ≤ N) (hNx : (N : ℝ) ≤ x) :
    |∑ n ∈ Finset.range (N + 1), reciprocalBVErrorCoeff q a n| ≤
      bvError x q + (1 / (Nat.totient q : ℝ)) * bvError x 1 := by
  rw [sum_range_reciprocalBVErrorCoeff]
  let c : ℝ := 1 / (Nat.totient q : ℝ)
  let Eq : ℝ := thetaAP (N : ℝ) q a - (N : ℝ) / (Nat.totient q : ℝ)
  let E1 : ℝ := thetaAP (N : ℝ) 1 0 - (N : ℝ)
  have hq : |Eq| ≤ bvError x q :=
    thetaAP_error_le_bvError ha (by exact_mod_cast hN2) hNx
  have h1 : |E1| ≤ bvError x 1 := by
    simpa [E1, Nat.totient_one] using
      (thetaAP_error_le_bvError (x := x) (y := (N : ℝ))
        (q := 1) (a := 0) (by decide) (by exact_mod_cast hN2) hNx)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hrearrange :
      thetaAP (N : ℝ) q a - c * thetaAP (N : ℝ) 1 0 = Eq - c * E1 := by
    dsimp [Eq, E1, c]
    have hphi : (Nat.totient q : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr hqpos).ne'
    field_simp [hphi]
  rw [show (1 / (Nat.totient q : ℝ)) = c by rfl, hrearrange]
  calc
    |Eq - c * E1| ≤ |Eq| + |c * E1| := abs_sub _ _
    _ = |Eq| + c * |E1| := by rw [abs_mul, abs_of_nonneg hc]
    _ ≤ bvError x q + c * bvError x 1 :=
      add_le_add hq (mul_le_mul_of_nonneg_left h1 hc)
    _ = bvError x q +
        (1 / (Nat.totient q : ℝ)) * bvError x 1 := by rfl

noncomputable def reciprocalPrimeWeight (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * Real.log (n : ℝ))

theorem reciprocalPrimeWeight_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < reciprocalPrimeWeight n := by
  unfold reciprocalPrimeWeight
  apply one_div_pos.mpr
  apply mul_pos
  · exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn)
  · exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hn))

theorem reciprocalPrimeWeight_antitone_on_two
    {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    reciprocalPrimeWeight n ≤ reciprocalPrimeWeight m := by
  have hn : 2 ≤ n := hm.trans hmn
  have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hm)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn)
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hm))
  have hlogle : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hmR hmnR
  have hden : (m : ℝ) * Real.log (m : ℝ) ≤
      (n : ℝ) * Real.log (n : ℝ) :=
    mul_le_mul hmnR hlogle
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))) hnR.le
  unfold reciprocalPrimeWeight
  exact one_div_le_one_div_of_le (mul_pos hmR hlogm) hden

theorem reciprocalPrimeWeight_succ_sub_nonpos
    {n : ℕ} (hn : 2 ≤ n) :
    reciprocalPrimeWeight (n + 1) - reciprocalPrimeWeight n ≤ 0 := by
  linarith [reciprocalPrimeWeight_antitone_on_two hn (by omega : n ≤ n + 1)]

theorem reciprocalPrimeWeight_mul_thetaAPCoeff (q a n : ℕ) :
    reciprocalPrimeWeight n * thetaAPCoeff q a n =
      if Nat.Prime n ∧ congMod n a q then (1 : ℝ) / n else 0 := by
  by_cases h : Nat.Prime n ∧ congMod n a q
  · rw [if_pos h]
    simp only [reciprocalPrimeWeight, thetaAPCoeff, if_pos h]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast h.1.pos
    have hn1 : (n : ℝ) ≠ 1 := by exact_mod_cast h.1.ne_one
    have hlog : Real.log (n : ℝ) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one hnpos hn1
    field_simp
    ring
  · simp [reciprocalPrimeWeight, thetaAPCoeff, h]

noncomputable def reciprocalAPWindow (L U : ℝ) (q a : ℕ) : ℝ :=
  ∑ p ∈ (natWindow L U).filter
      (fun p : ℕ => Nat.Prime p ∧ congMod p a q),
    (1 : ℝ) / (p : ℝ)

theorem reciprocalAPWindow_eq_sum_weight_thetaAPCoeff
    (L U : ℝ) (q a : ℕ) :
    reciprocalAPWindow L U q a =
      ∑ n ∈ natWindow L U,
        reciprocalPrimeWeight n * thetaAPCoeff q a n := by
  classical
  unfold reciprocalAPWindow
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [reciprocalPrimeWeight_mul_thetaAPCoeff]

theorem reciprocalAPWindow_error_eq_sum_weight_errorCoeff
    (L U : ℝ) (q a : ℕ) :
    reciprocalAPWindow L U q a -
        (1 / (Nat.totient q : ℝ)) * reciprocalAPWindow L U 1 0 =
      ∑ n ∈ natWindow L U,
        reciprocalPrimeWeight n * reciprocalBVErrorCoeff q a n := by
  rw [reciprocalAPWindow_eq_sum_weight_thetaAPCoeff,
    reciprocalAPWindow_eq_sum_weight_thetaAPCoeff]
  simp_rw [reciprocalBVErrorCoeff, mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

theorem natWindow_eq_Ioc_floor {L U : ℝ} (hL : 0 ≤ L) :
    natWindow L U = Finset.Ioc ⌊L⌋₊ ⌊U⌋₊ := by
  ext n
  simp only [natWindow, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hn1, hnU⟩, hLn⟩
    exact ⟨(Nat.floor_lt hL).2 hLn, hnU⟩
  · rintro ⟨hLn, hnU⟩
    have hn1 : 1 ≤ n := by
      have : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hLn
      omega
    exact ⟨⟨hn1, hnU⟩, (Nat.floor_lt hL).1 hLn⟩

/-- Exact weighted-coefficient representation of the reciprocal prime carrier. -/
theorem btRecip_eq_sum_weight_thetaAPCoeff
    (P : EscAnalytic.Params) (X : ℝ) (q a : ℕ) :
    btRecip P X q a =
      ∑ n ∈ natWindow (X ^ P.β) (X ^ (1 - P.σ)),
        reciprocalPrimeWeight n * thetaAPCoeff q a n := by
  classical
  unfold btRecip
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  rw [reciprocalPrimeWeight_mul_thetaAPCoeff]

/-- The reciprocal progression error is exactly a weighted sum of the signed
Chebyshev coefficients on the paper's prime window. -/
theorem btRecip_error_eq_sum_weight_errorCoeff
    (P : EscAnalytic.Params) (X : ℝ) (q a : ℕ) :
    btRecip P X q a -
        (1 / (Nat.totient q : ℝ)) * btRecip P X 1 0 =
      ∑ n ∈ natWindow (X ^ P.β) (X ^ (1 - P.σ)),
        reciprocalPrimeWeight n * reciprocalBVErrorCoeff q a n := by
  rw [btRecip_eq_sum_weight_thetaAPCoeff,
    btRecip_eq_sum_weight_thetaAPCoeff]
  simp_rw [reciprocalBVErrorCoeff, mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- Scalar form of finite Abel summation on a left-open, right-closed natural
interval.  This is an exact identity, with no analytic assumptions. -/
theorem finite_abel_Ioc_identity
    (f g : ℕ → ℝ) {m n : ℕ} (hmn : m < n) :
    ∑ i ∈ Finset.Ioc m n, f i * g i =
      f n * (∑ k ∈ Finset.range (n + 1), g k) -
        f (m + 1) * (∑ k ∈ Finset.range (m + 1), g k) -
        ∑ i ∈ Finset.Ioc m (n - 1),
          (f (i + 1) - f i) * (∑ k ∈ Finset.range (i + 1), g k) := by
  simpa only [smul_eq_mul] using Finset.sum_Ioc_by_parts f g hmn

theorem sum_Ioc_forward_difference (f : ℕ → ℝ) {m n : ℕ} (hmn : m < n) :
    (∑ i ∈ Finset.Ioc m (n - 1), (f i - f (i + 1))) =
      f (m + 1) - f n := by
  rw [← Nat.Ico_succ_succ]
  simp only [Nat.succ_eq_add_one]
  rw [Nat.sub_add_cancel (Nat.one_le_of_lt hmn),
    Finset.sum_Ico_eq_sub _ (Nat.succ_le_of_lt hmn),
    Finset.sum_range_sub', Finset.sum_range_sub']
  ring

/-- Quantitative finite Abel bound.  A nonnegative decreasing weight and a
uniform bound `B` for the relevant prefix sums give the sharp elementary
estimate `2 f(m+1) B`. -/
theorem abs_sum_Ioc_mul_le_two_mul
    (f g : ℕ → ℝ) {m n : ℕ} {B : ℝ} (hmn : m < n)
    (hf_m : 0 ≤ f (m + 1)) (hf_n : 0 ≤ f n)
    (hmono : ∀ i ∈ Finset.Ioc m (n - 1), f (i + 1) ≤ f i)
    (hprefix : ∀ k, m + 1 ≤ k → k ≤ n + 1 →
      |∑ j ∈ Finset.range k, g j| ≤ B) :
    |∑ i ∈ Finset.Ioc m n, f i * g i| ≤ 2 * f (m + 1) * B := by
  let G : ℕ → ℝ := fun k => ∑ j ∈ Finset.range k, g j
  have hGn : |G (n + 1)| ≤ B := hprefix (n + 1)
    (by omega) le_rfl
  have hGm : |G (m + 1)| ≤ B := hprefix (m + 1) le_rfl
    (by omega)
  have htail :
      |∑ i ∈ Finset.Ioc m (n - 1),
          (f (i + 1) - f i) * G (i + 1)| ≤
        B * (f (m + 1) - f n) := by
    calc
      |∑ i ∈ Finset.Ioc m (n - 1),
          (f (i + 1) - f i) * G (i + 1)|
          ≤ ∑ i ∈ Finset.Ioc m (n - 1),
              |(f (i + 1) - f i) * G (i + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Ioc m (n - 1),
            (f i - f (i + 1)) * B := by
        apply Finset.sum_le_sum
        intro i hi
        have hfi := hmono i hi
        have hiData := Finset.mem_Ioc.mp hi
        have hGi : |G (i + 1)| ≤ B := hprefix (i + 1)
          (by omega) (by omega)
        rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hfi), neg_sub]
        exact mul_le_mul_of_nonneg_left hGi (sub_nonneg.mpr hfi)
      _ = B * (∑ i ∈ Finset.Ioc m (n - 1),
            (f i - f (i + 1))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = B * (f (m + 1) - f n) := by
        rw [sum_Ioc_forward_difference f hmn]
  rw [finite_abel_Ioc_identity f g hmn]
  change |f n * G (n + 1) - f (m + 1) * G (m + 1) -
      ∑ i ∈ Finset.Ioc m (n - 1),
        (f (i + 1) - f i) * G (i + 1)| ≤ _
  calc
    |f n * G (n + 1) - f (m + 1) * G (m + 1) -
        ∑ i ∈ Finset.Ioc m (n - 1),
          (f (i + 1) - f i) * G (i + 1)|
        ≤ |f n * G (n + 1)| + |f (m + 1) * G (m + 1)| +
            |∑ i ∈ Finset.Ioc m (n - 1),
              (f (i + 1) - f i) * G (i + 1)| := by
          let A := f n * G (n + 1)
          let D := f (m + 1) * G (m + 1)
          let T := ∑ i ∈ Finset.Ioc m (n - 1),
            (f (i + 1) - f i) * G (i + 1)
          change |A - D - T| ≤ |A| + |D| + |T|
          have h₁ : |A - D - T| ≤ |A - D| + |T| := abs_sub _ _
          have h₂ : |A - D| ≤ |A| + |D| := abs_sub _ _
          linarith
    _ ≤ f n * B + f (m + 1) * B + B * (f (m + 1) - f n) := by
      apply add_le_add
      · apply add_le_add
        · rw [abs_mul, abs_of_nonneg hf_n]
          exact mul_le_mul_of_nonneg_left hGn hf_n
        · rw [abs_mul, abs_of_nonneg hf_m]
          exact mul_le_mul_of_nonneg_left hGm hf_m
      · exact htail
    _ = 2 * f (m + 1) * B := by ring

/-- Quantitative partial-summation bridge on the exact paper window.  The
reciprocal progression error is bounded by the maximal Chebyshev errors at the
modulus and at modulus one, divided by the lower-window reciprocal weight. -/
theorem abs_btRecip_error_le_bvError
    (P : EscAnalytic.Params) {X : ℝ} {q a : ℕ}
    (hX : 1 < X) (hq : 0 < q) (ha : Nat.Coprime a q)
    (hlower : 2 ≤ ⌊X ^ P.β⌋₊)
    (hfloor : ⌊X ^ P.β⌋₊ < ⌊X ^ (1 - P.σ)⌋₊) :
    |btRecip P X q a -
        (1 / (Nat.totient q : ℝ)) * btRecip P X 1 0| ≤
      2 * reciprocalPrimeWeight (⌊X ^ P.β⌋₊ + 1) *
        (bvError (X ^ (1 - P.σ)) q +
          (1 / (Nat.totient q : ℝ)) *
            bvError (X ^ (1 - P.σ)) 1) := by
  let l := ⌊X ^ P.β⌋₊
  let u := ⌊X ^ (1 - P.σ)⌋₊
  let U := X ^ (1 - P.σ)
  let B := bvError U q +
    (1 / (Nat.totient q : ℝ)) * bvError U 1
  have hU0 : 0 ≤ U := Real.rpow_nonneg (le_trans zero_le_one hX.le) _
  have hprefix : ∀ k, l + 1 ≤ k → k ≤ u + 1 →
      |∑ j ∈ Finset.range k, reciprocalBVErrorCoeff q a j| ≤ B := by
    intro k hlk hku
    let N := k - 1
    have hk1 : 1 ≤ k := by omega
    have hNk : N + 1 = k := Nat.sub_add_cancel hk1
    have hN2 : 2 ≤ N := by dsimp [N]; dsimp [l] at hlk; omega
    have hNu : N ≤ u := by dsimp [N]; omega
    have hNU : (N : ℝ) ≤ U := by
      exact le_trans (by exact_mod_cast hNu) (Nat.floor_le hU0)
    rw [← hNk]
    exact abs_sum_range_reciprocalBVErrorCoeff_le hq ha hN2 hNU
  have hmono : ∀ i ∈ Finset.Ioc l (u - 1),
      reciprocalPrimeWeight (i + 1) ≤ reciprocalPrimeWeight i := by
    intro i hi
    have hiData := Finset.mem_Ioc.mp hi
    have hi2 : 2 ≤ i := by dsimp [l] at hiData; omega
    exact reciprocalPrimeWeight_antitone_on_two hi2 (by omega)
  have hsum := abs_sum_Ioc_mul_le_two_mul reciprocalPrimeWeight
    (reciprocalBVErrorCoeff q a) (m := l) (n := u) (B := B) hfloor
    (reciprocalPrimeWeight_pos (by dsimp [l]; omega)).le
    (reciprocalPrimeWeight_pos (by dsimp [u, l] at *; omega)).le
    hmono hprefix
  rw [btRecip_error_eq_sum_weight_errorCoeff]
  have hL0 : 0 ≤ X ^ P.β :=
    Real.rpow_nonneg (le_trans zero_le_one hX.le) _
  rw [natWindow_eq_Ioc_floor hL0]
  simpa [l, u, U, B] using hsum

/-- Dyadic-ready version of the quantitative reciprocal-error bridge on an
arbitrary positive real window `(L,U]`. -/
theorem abs_reciprocalAPWindow_error_le_bvError
    {L U : ℝ} {q a : ℕ}
    (hL : 0 ≤ L) (hU : 0 ≤ U) (hq : 0 < q) (ha : Nat.Coprime a q)
    (hlower : 2 ≤ ⌊L⌋₊) (hfloor : ⌊L⌋₊ < ⌊U⌋₊) :
    |reciprocalAPWindow L U q a -
        (1 / (Nat.totient q : ℝ)) * reciprocalAPWindow L U 1 0| ≤
      2 * reciprocalPrimeWeight (⌊L⌋₊ + 1) *
        (bvError U q +
          (1 / (Nat.totient q : ℝ)) * bvError U 1) := by
  let l := ⌊L⌋₊
  let u := ⌊U⌋₊
  let B := bvError U q +
    (1 / (Nat.totient q : ℝ)) * bvError U 1
  have hprefix : ∀ k, l + 1 ≤ k → k ≤ u + 1 →
      |∑ j ∈ Finset.range k, reciprocalBVErrorCoeff q a j| ≤ B := by
    intro k hlk hku
    let N := k - 1
    have hk1 : 1 ≤ k := by omega
    have hNk : N + 1 = k := Nat.sub_add_cancel hk1
    have hN2 : 2 ≤ N := by dsimp [N]; dsimp [l] at hlk; omega
    have hNu : N ≤ u := by dsimp [N]; omega
    have hNU : (N : ℝ) ≤ U :=
      le_trans (by exact_mod_cast hNu) (Nat.floor_le hU)
    rw [← hNk]
    exact abs_sum_range_reciprocalBVErrorCoeff_le hq ha hN2 hNU
  have hmono : ∀ i ∈ Finset.Ioc l (u - 1),
      reciprocalPrimeWeight (i + 1) ≤ reciprocalPrimeWeight i := by
    intro i hi
    have hiData := Finset.mem_Ioc.mp hi
    have hi2 : 2 ≤ i := by dsimp [l] at hiData; omega
    exact reciprocalPrimeWeight_antitone_on_two hi2 (by omega)
  have hsum := abs_sum_Ioc_mul_le_two_mul reciprocalPrimeWeight
    (reciprocalBVErrorCoeff q a) (m := l) (n := u) (B := B) hfloor
    (reciprocalPrimeWeight_pos (by dsimp [l]; omega)).le
    (reciprocalPrimeWeight_pos (by dsimp [u, l] at *; omega)).le
    hmono hprefix
  rw [reciprocalAPWindow_error_eq_sum_weight_errorCoeff,
    natWindow_eq_Ioc_floor hL]
  simpa [l, u, B] using hsum

noncomputable def dyadicLogFiber (s : Finset ℕ) (k : ℕ) : Finset ℕ :=
  s.filter (fun n => Nat.log 2 n = k)

/-- Exact finite dyadic partition of a natural window, indexed by the binary
logarithm of each integer. -/
theorem sum_natWindow_eq_sum_dyadicLogFiber
    {M : Type*} [AddCommMonoid M] (L U : ℝ) (f : ℕ → M) :
    (∑ k ∈ Finset.range (Nat.log 2 ⌊U⌋₊ + 1),
        ∑ n ∈ dyadicLogFiber (natWindow L U) k, f n) =
      ∑ n ∈ natWindow L U, f n := by
  classical
  apply Finset.sum_fiberwise_of_maps_to
  intro n hn
  rw [Finset.mem_range]
  have hnIcc : n ∈ Finset.Icc 1 ⌊U⌋₊ := (Finset.mem_filter.mp hn).1
  have hnU : n ≤ ⌊U⌋₊ := (Finset.mem_Icc.mp hnIcc).2
  exact Nat.lt_succ_of_le (Nat.log_mono_right hnU)

theorem mem_dyadicLogFiber_bounds
    {s : Finset ℕ} {k n : ℕ} (hn : n ∈ dyadicLogFiber s k) (hn0 : n ≠ 0) :
    2 ^ k ≤ n ∧ n < 2 ^ (k + 1) := by
  have hlog : Nat.log 2 n = k := (Finset.mem_filter.mp hn).2
  constructor
  · simpa [hlog] using Nat.pow_log_le_self 2 hn0
  · simpa [hlog, Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self
      (by norm_num : 1 < 2) n

theorem dyadicLogFiber_natWindow_eq_filter_bounds
    (L U : ℝ) (k : ℕ) :
    dyadicLogFiber (natWindow L U) k =
      (natWindow L U).filter
        (fun n => 2 ^ k ≤ n ∧ n < 2 ^ (k + 1)) := by
  ext n
  constructor
  · intro hn
    have hnWindow : n ∈ natWindow L U := (Finset.mem_filter.mp hn).1
    have hnIcc : n ∈ Finset.Icc 1 ⌊U⌋₊ := (Finset.mem_filter.mp hnWindow).1
    have hn0 : n ≠ 0 := by
      have hn1 := (Finset.mem_Icc.mp hnIcc).1
      omega
    exact Finset.mem_filter.mpr ⟨hnWindow,
      mem_dyadicLogFiber_bounds hn hn0⟩
  · intro hn
    obtain ⟨hnWindow, hbounds⟩ := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    refine ⟨hnWindow, ?_⟩
    exact Nat.log_eq_of_pow_le_of_lt_pow hbounds.1 (by
      simpa [Nat.succ_eq_add_one] using hbounds.2)

/-- Exact dyadic decomposition of the reciprocal progression error.  No
triangle inequality or analytic estimate has yet been applied. -/
theorem reciprocalAPWindow_error_eq_sum_dyadicLogFiber
    (L U : ℝ) (q a : ℕ) :
    reciprocalAPWindow L U q a -
        (1 / (Nat.totient q : ℝ)) * reciprocalAPWindow L U 1 0 =
      ∑ k ∈ Finset.range (Nat.log 2 ⌊U⌋₊ + 1),
        ∑ n ∈ dyadicLogFiber (natWindow L U) k,
          reciprocalPrimeWeight n * reciprocalBVErrorCoeff q a n := by
  rw [reciprocalAPWindow_error_eq_sum_weight_errorCoeff]
  exact (sum_natWindow_eq_sum_dyadicLogFiber L U
    (fun n => reciprocalPrimeWeight n * reciprocalBVErrorCoeff q a n)).symm

/-- Triangle-inequality form of the exact dyadic decomposition. -/
theorem abs_reciprocalAPWindow_error_le_sum_abs_dyadicLogFiber
    (L U : ℝ) (q a : ℕ) :
    |reciprocalAPWindow L U q a -
        (1 / (Nat.totient q : ℝ)) * reciprocalAPWindow L U 1 0| ≤
      ∑ k ∈ Finset.range (Nat.log 2 ⌊U⌋₊ + 1),
        |∑ n ∈ dyadicLogFiber (natWindow L U) k,
          reciprocalPrimeWeight n * reciprocalBVErrorCoeff q a n| := by
  rw [reciprocalAPWindow_error_eq_sum_dyadicLogFiber]
  exact Finset.abs_sum_le_sum_abs _ _

theorem natWindow_dyadic_eq_Ico (k : ℕ) :
    natWindow ((2 ^ k - 1 : ℕ) : ℝ) ((2 ^ (k + 1) - 1 : ℕ) : ℝ) =
      Finset.Ico (2 ^ k) (2 ^ (k + 1)) := by
  rw [natWindow_eq_Ioc_floor (by positivity)]
  simp only [Nat.floor_natCast]
  ext n
  simp only [Finset.mem_Ioc, Finset.mem_Ico]
  omega

/-- Maximal-BV bound for a complete binary dyadic reciprocal-prime block. -/
theorem abs_dyadic_reciprocalAPWindow_error_le_bvError
    {k q a : ℕ} (hk : 2 ≤ k) (hq : 0 < q) (ha : Nat.Coprime a q) :
    |reciprocalAPWindow ((2 ^ k - 1 : ℕ) : ℝ)
          ((2 ^ (k + 1) - 1 : ℕ) : ℝ) q a -
        (1 / (Nat.totient q : ℝ)) *
          reciprocalAPWindow ((2 ^ k - 1 : ℕ) : ℝ)
            ((2 ^ (k + 1) - 1 : ℕ) : ℝ) 1 0| ≤
      2 * reciprocalPrimeWeight (2 ^ k) *
        (bvError ((2 ^ (k + 1) - 1 : ℕ) : ℝ) q +
          (1 / (Nat.totient q : ℝ)) *
            bvError ((2 ^ (k + 1) - 1 : ℕ) : ℝ) 1) := by
  have hlower : 2 ≤ 2 ^ k - 1 := by
    have : 4 ≤ 2 ^ k := by
      simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
    omega
  have hfloor : 2 ^ k - 1 < 2 ^ (k + 1) - 1 := by
    have hpow : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hpowOne : 1 ≤ 2 ^ k := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  have hfloorLower : ⌊((2 ^ k - 1 : ℕ) : ℝ)⌋₊ = 2 ^ k - 1 :=
    Nat.floor_natCast _
  have hfloorUpper : ⌊((2 ^ (k + 1) - 1 : ℕ) : ℝ)⌋₊ =
      2 ^ (k + 1) - 1 := Nat.floor_natCast _
  simpa only [hfloorLower, hfloorUpper, Nat.sub_add_cancel hpowOne] using
    (abs_reciprocalAPWindow_error_le_bvError
      (L := ((2 ^ k - 1 : ℕ) : ℝ))
      (U := ((2 ^ (k + 1) - 1 : ℕ) : ℝ))
      (q := q) (a := a) (by positivity) (by positivity) hq ha
      (by rw [hfloorLower]; exact hlower)
      (by rw [hfloorLower, hfloorUpper]; exact hfloor))

noncomputable def dyadicReciprocalErrorMax (k q : ℕ) : ℝ := by
  classical
  exact ((Finset.Icc (1 : ℕ) q).filter (fun a => Nat.Coprime a q)).fold max 0
    (fun a =>
      |reciprocalAPWindow ((2 ^ k - 1 : ℕ) : ℝ)
          ((2 ^ (k + 1) - 1 : ℕ) : ℝ) q a -
        (1 / (Nat.totient q : ℝ)) *
          reciprocalAPWindow ((2 ^ k - 1 : ℕ) : ℝ)
            ((2 ^ (k + 1) - 1 : ℕ) : ℝ) 1 0|)

theorem dyadicReciprocalErrorMax_le_bvError
    {k q : ℕ} (hk : 2 ≤ k) (hq : 0 < q) :
    dyadicReciprocalErrorMax k q ≤
      2 * reciprocalPrimeWeight (2 ^ k) *
        (bvError ((2 ^ (k + 1) - 1 : ℕ) : ℝ) q +
          (1 / (Nat.totient q : ℝ)) *
            bvError ((2 ^ (k + 1) - 1 : ℕ) : ℝ) 1) := by
  classical
  unfold dyadicReciprocalErrorMax
  rw [Finset.fold_max_le]
  constructor
  · have hkpow : 2 ≤ 2 ^ k := by
      exact le_trans (by norm_num : 2 ≤ 2 ^ 2)
        (Nat.pow_le_pow_right (by norm_num) hk)
    have hw : 0 ≤ reciprocalPrimeWeight (2 ^ k) :=
      (reciprocalPrimeWeight_pos hkpow).le
    have hphi : 0 ≤ (1 / (Nat.totient q : ℝ)) := by positivity
    exact mul_nonneg (mul_nonneg (by norm_num) hw)
      (add_nonneg (bvError_nonneg _ _)
        (mul_nonneg hphi (bvError_nonneg _ _)))
  · intro a ha
    exact abs_dyadic_reciprocalAPWindow_error_le_bvError hk hq
      (Finset.mem_filter.mp ha).2

noncomputable def weightedBvErrorSumAt (x : ℝ) (K Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc (1 : ℕ) Q, ((tau q : ℝ) ^ K) * bvError x q

noncomputable def divisorPhiMomentAt (K Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc (1 : ℕ) Q,
    ((tau q : ℝ) ^ K) / (Nat.totient q : ℝ)

noncomputable def dyadicWeightedReciprocalErrorSum (k K Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc (1 : ℕ) Q,
    ((tau q : ℝ) ^ K) * dyadicReciprocalErrorMax k q

/-- Finite modulus-sum conversion for a complete dyadic block.  This contains
all reciprocal partial summation and reduced-class-max bookkeeping; only the
two classical Chebyshev BV/divisor-moment carriers remain on the right. -/
theorem dyadicWeightedReciprocalErrorSum_le
    {k K Q : ℕ} (hk : 2 ≤ k) :
    dyadicWeightedReciprocalErrorSum k K Q ≤
      2 * reciprocalPrimeWeight (2 ^ k) *
        (weightedBvErrorSumAt ((2 ^ (k + 1) - 1 : ℕ) : ℝ) K Q +
          bvError ((2 ^ (k + 1) - 1 : ℕ) : ℝ) 1 *
            divisorPhiMomentAt K Q) := by
  classical
  unfold dyadicWeightedReciprocalErrorSum weightedBvErrorSumAt
    divisorPhiMomentAt
  calc
    (∑ q ∈ Finset.Icc (1 : ℕ) Q,
        ((tau q : ℝ) ^ K) * dyadicReciprocalErrorMax k q) ≤
      ∑ q ∈ Finset.Icc (1 : ℕ) Q,
        ((tau q : ℝ) ^ K) *
          (2 * reciprocalPrimeWeight (2 ^ k) *
            (bvError ((2 ^ (k + 1) - 1 : ℕ) : ℝ) q +
              (1 / (Nat.totient q : ℝ)) *
                bvError ((2 ^ (k + 1) - 1 : ℕ) : ℝ) 1)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqpos : 0 < q := by
        have := (Finset.mem_Icc.mp hq).1
        omega
      exact mul_le_mul_of_nonneg_left
        (dyadicReciprocalErrorMax_le_bvError hk hqpos) (by positivity)
    _ = 2 * reciprocalPrimeWeight (2 ^ k) *
        ((∑ q ∈ Finset.Icc (1 : ℕ) Q,
            ((tau q : ℝ) ^ K) *
              bvError ((2 ^ (k + 1) - 1 : ℕ) : ℝ) q) +
          bvError ((2 ^ (k + 1) - 1 : ℕ) : ℝ) 1 *
            (∑ q ∈ Finset.Icc (1 : ℕ) Q,
              ((tau q : ℝ) ^ K) / (Nat.totient q : ℝ))) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _hq
        ring
      · rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _hq
        ring

/-- A fixed integer divisor weight costs only the endpoint power `Q^K` before
applying the ordinary maximal BV modulus sum.  This is the elementary
weight-removal step enabled by the strict half-level margin. -/
theorem weightedBvErrorSumAt_le_cutoff_pow_mul_bvSum
    {x ε : ℝ} {K Q : ℕ}
    (hQ : Q ≤ ⌊x ^ ((1 : ℝ) / 2 - ε)⌋₊) :
    weightedBvErrorSumAt x K Q ≤ (Q : ℝ) ^ K * bvSum x ε := by
  classical
  have hweight : ∀ q ∈ Finset.Icc (1 : ℕ) Q,
      ((tau q : ℝ) ^ K) ≤ (Q : ℝ) ^ K := by
    intro q hq
    have hqQ : q ≤ Q := (Finset.mem_Icc.mp hq).2
    have htauQ : tau q ≤ Q := (tau_le_self q).trans hqQ
    exact_mod_cast Nat.pow_le_pow_left htauQ K
  have hsubset : Finset.Icc (1 : ℕ) Q ⊆
      Finset.Icc (1 : ℕ) ⌊x ^ ((1 : ℝ) / 2 - ε)⌋₊ := by
    intro q hq
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hq).1,
      (Finset.mem_Icc.mp hq).2.trans hQ⟩
  have hsum_subset :
      (∑ q ∈ Finset.Icc (1 : ℕ) Q, bvError x q) ≤ bvSum x ε := by
    unfold bvSum
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro q _hq _hnot
      exact bvError_nonneg x q)
  unfold weightedBvErrorSumAt
  calc
    (∑ q ∈ Finset.Icc (1 : ℕ) Q, ((tau q : ℝ) ^ K) * bvError x q) ≤
        ∑ q ∈ Finset.Icc (1 : ℕ) Q, (Q : ℝ) ^ K * bvError x q := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_right (hweight q hq) (bvError_nonneg x q)
    _ = (Q : ℝ) ^ K *
        (∑ q ∈ Finset.Icc (1 : ℕ) Q, bvError x q) := by
      rw [Finset.mul_sum]
    _ ≤ (Q : ℝ) ^ K * bvSum x ε :=
      mul_le_mul_of_nonneg_left hsum_subset (by positivity)

/-- Exact Abel decomposition of the paper's reciprocal progression error.
This is the central finite carrier conversion from maximal Chebyshev prefixes
to reciprocal-prime errors. -/
theorem btRecip_error_abel_identity
    (P : EscAnalytic.Params) (X : ℝ) (q a : ℕ)
    (hX : 1 < X)
    (hfloor : ⌊X ^ P.β⌋₊ < ⌊X ^ (1 - P.σ)⌋₊) :
    let l := ⌊X ^ P.β⌋₊
    let u := ⌊X ^ (1 - P.σ)⌋₊
    btRecip P X q a -
        (1 / (Nat.totient q : ℝ)) * btRecip P X 1 0 =
      reciprocalPrimeWeight u *
          (∑ k ∈ Finset.range (u + 1), reciprocalBVErrorCoeff q a k) -
        reciprocalPrimeWeight (l + 1) *
          (∑ k ∈ Finset.range (l + 1), reciprocalBVErrorCoeff q a k) -
        ∑ i ∈ Finset.Ioc l (u - 1),
          (reciprocalPrimeWeight (i + 1) - reciprocalPrimeWeight i) *
            (∑ k ∈ Finset.range (i + 1), reciprocalBVErrorCoeff q a k) := by
  dsimp only
  rw [btRecip_error_eq_sum_weight_errorCoeff]
  have hL : 0 ≤ X ^ P.β :=
    Real.rpow_nonneg (le_trans zero_le_one hX.le) _
  rw [natWindow_eq_Ioc_floor hL]
  exact finite_abel_Ioc_identity reciprocalPrimeWeight
    (reciprocalBVErrorCoeff q a) hfloor

end EscAnalytic.Inputs
