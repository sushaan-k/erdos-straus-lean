import ErdosStraus.Estimates.PartialSummation
import ErdosStraus.CubicSums.DivisorIdentity
import ErdosStraus.Estimates.PrimeCounts

/-!
# Lemma 4.4: a divisor sum over primes of the form `4a - 1`

We prove `∑_{a ≤ L, 4a-1 prime} τ(a²)/a ≪ (log L)²` for `L ≥ 3`. Put
`T(x) = ∑_{a ≤ x, 4a-1 prime} τ(a²)`. The hyperbola inequality
`τ(a²) ≤ 3 ∑_{d ∣ a, d ≤ a^{2/3}} τ(d)` and the bound (8) of Lemma 3.5 with `y = 4x`, `q = 4d`
and the class `-1 (mod 4d)` give `T(x) ≪ (x / log x) ∑_{d ≤ x^{2/3}} τ(d)/φ(d)`. The identity
`n/φ(n) = ∑_{k ∣ n} μ²(k)/φ(k)` bounds the last sum by `e² (1 + log x)²`, so `T(x) ≪ x log x`,
and partial summation gives the reciprocal bound.
-/

namespace ErdosStraus.DivisorEstimates

open scoped BigOperators

/-! ## Partial summation -/

private theorem sum_range_shift (f : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, f (i + 1)) = ∑ n ∈ Finset.Icc 1 N, f n := by
  simpa only [Nat.zero_add, Nat.Ico_zero_eq_range, Finset.Ico_add_one_right_eq_Icc, Nat.add_comm] using
    Finset.sum_Ico_add f 0 N 1

/-- If `∑_{n ≤ N} w(n) ≤ A N (1 + log N)` for every `N ≥ 1`, then
`∑_{n ≤ N} w(n)/n ≤ A (1 + log N)²`. -/
theorem reciprocal_bound_of_linear_log_prefix (w : ℕ → ℝ)
    (_hw : ∀ n, 0 ≤ w n) (A : ℝ) (hA : 0 < A)
    (hprefix : ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ Finset.Icc 1 N, w n) ≤ A * (N : ℝ) * (1 + Real.log N))
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, w n / (n : ℝ)) ≤ A * (1 + Real.log N) ^ 2 := by
  let B := A * (1 + Real.log N)
  have hBN : 0 ≤ B := by dsimp [B]; positivity
  have hdom : ∀ k ≤ N,
      (∑ i ∈ Finset.range k, w (i + 1)) ≤ ∑ _i ∈ Finset.range k, B := by
    intro k hk
    rw [sum_range_shift]
    by_cases hk0 : k = 0
    · simp [hk0]
    have hk1 : 1 ≤ k := by omega
    have hkP : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
    have hlog : Real.log (k : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log hkP (by exact_mod_cast hk)
    calc
      _ ≤ A * (k : ℝ) * (1 + Real.log k) := hprefix k hk1
      _ ≤ A * (k : ℝ) * (1 + Real.log N) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by simp [B]; ring
  have hmono : ∀ i, i + 1 < N →
      (1 : ℝ) / ((i + 1 + 1 : ℕ) : ℝ) ≤ 1 / ((i + 1 : ℕ) : ℝ) := by
    intro i _
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.le_succ (i + 1)
  have hsum := SieveEstimates.sum_mul_le_of_prefix_sum_le
    (fun i => w (i + 1)) (fun _ => B) (fun i => 1 / ((i + 1 : ℕ) : ℝ)) N
    hdom (fun _ _ => by positivity) hmono
  have hleft : (∑ i ∈ Finset.range N, (1 / ((i + 1 : ℕ) : ℝ)) * w (i + 1)) =
      ∑ n ∈ Finset.Icc 1 N, w n / (n : ℝ) := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using
      sum_range_shift (fun n => w n / (n : ℝ)) N
  have hright : (∑ i ∈ Finset.range N, (1 / ((i + 1 : ℕ) : ℝ)) * B) =
      B * ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) := by
    rw [← Finset.sum_mul]
    calc
      _ = (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ)) * B :=
        congrArg (fun x : ℝ => x * B) (sum_range_shift (fun n => (1 : ℝ) / (n : ℝ)) N)
      _ = _ := mul_comm _ _
  rw [hleft, hright] at hsum
  have hh := SieveEstimates.sum_Icc_reciprocal_le_log 1 N (by norm_num) hN
  simp only [Nat.cast_one, div_one] at hh
  exact hsum.trans (by
    calc
      B * (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ)) ≤ B * (1 + Real.log N) :=
        mul_le_mul_of_nonneg_left hh hBN
      _ = A * (1 + Real.log N) ^ 2 := by dsimp [B]; ring)

/-! ## The progression count -/

/-- The integers `a ≤ x` with `d ∣ a` and `4a - 1` prime inject, via `a ↦ 4a - 1`,
into the primes `p ≤ 4x` with `p ≡ -1 (mod 4d)`. -/
theorem prime_form_multiples_card_le_primePrefix (x : ℝ) {d : ℕ} (hd : 0 < d) :
    ((Finset.Icc 1 ⌊x⌋₊).filter (fun a => Nat.Prime (4 * a - 1) ∧ d ∣ a)).card ≤
      (BrunHooley.primePrefix (4 * x) (4 * d) (4 * d - 1)).card := by
  apply Finset.card_le_card_of_injOn (fun a => 4 * a - 1)
  · intro a ha
    obtain ⟨haI, hp, hda⟩ := Finset.mem_filter.mp ha
    obtain ⟨ha1, hax⟩ := Finset.mem_Icc.mp haI
    have hx : 0 ≤ x := by
      by_contra hneg
      have h0 := Nat.floor_of_nonpos (le_of_lt (not_le.mp hneg))
      omega
    simp only [Finset.mem_coe]
    rw [BrunHooley.mem_primePrefix]
    refine ⟨?_, hp, ?_⟩
    · apply Nat.le_floor
      have hsub : ((4 * a - 1 : ℕ) : ℝ) ≤ 4 * (a : ℝ) := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        linarith
      have hax' : (a : ℝ) ≤ x := (Nat.cast_le.mpr hax).trans (Nat.floor_le hx)
      linarith
    · obtain ⟨m, rfl⟩ := hda
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (show m ≠ 0 by rintro rfl; simp at ha1)
      have h4 : 4 * (d * (k + 1)) = 4 * d * k + 4 * d := by ring
      have h : 4 * (d * Nat.succ k) - 1 = (4 * d - 1) + 4 * d * k := by
        rw [Nat.succ_eq_add_one, h4]
        omega
      rw [h]
      exact Nat.add_mul_mod_self_left _ _ _
  · intro a ha b hb hab
    have ha1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).1).1
    have hb1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).1).1
    simp only at hab
    omega

/-! ## The hyperbola inequality -/

/-- `T(x) ≤ 3 ∑_{d ≤ x^{2/3}} τ(d) #{a ≤ x : d ∣ a, 4a - 1 prime}`. -/
theorem prime_form_tau_square_sum_le_short_divisor_counts (x : ℝ) (hx : 0 ≤ x) :
    (∑ a ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun a => Nat.Prime (4 * a - 1)),
        ((a ^ 2).divisors.card : ℝ)) ≤
      3 * ∑ d ∈ Finset.Icc 1 ⌊x ^ (2 / 3 : ℝ)⌋₊, (d.divisors.card : ℝ) *
        (((Finset.Icc 1 ⌊x⌋₊).filter
          (fun a => Nat.Prime (4 * a - 1) ∧ d ∣ a)).card : ℝ) := by
  classical
  set S := (Finset.Icc 1 ⌊x⌋₊).filter (fun a => Nat.Prime (4 * a - 1)) with hS
  set I := Finset.Icc 1 ⌊x ^ (2 / 3 : ℝ)⌋₊ with hI
  have hcube : (x ^ (2 / 3 : ℝ)) ^ 3 = x ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  have hpoint : ∀ a ∈ S, ((a ^ 2).divisors.card : ℝ) ≤
      3 * ∑ d ∈ I, if d ∣ a then (d.divisors.card : ℝ) else 0 := by
    intro a ha
    obtain ⟨haI, _⟩ := Finset.mem_filter.mp ha
    obtain ⟨ha1, hax⟩ := Finset.mem_Icc.mp haI
    have hmajor := square_divisor_card_le_three_short_divisor_sum (show a ≠ 0 by omega)
    have hmajorR : ((a ^ 2).divisors.card : ℝ) ≤
        3 * (∑ d ∈ a.divisors.filter (fun d => d ^ 3 ≤ a ^ 2), (d.divisors.card : ℝ)) := by
      exact_mod_cast hmajor
    refine hmajorR.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 3))
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨hdA, hdshort⟩ := Finset.mem_filter.mp hd
      have hax' : (a : ℝ) ≤ x := (Nat.cast_le.mpr hax).trans (Nat.floor_le hx)
      have hd3 : (d : ℝ) ^ 3 ≤ (x ^ (2 / 3 : ℝ)) ^ 3 := by
        rw [hcube]
        calc
          (d : ℝ) ^ 3 ≤ (a : ℝ) ^ 2 := by exact_mod_cast hdshort
          _ ≤ x ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg a) hax' 2
      have hdx : (d : ℝ) ≤ x ^ (2 / 3 : ℝ) :=
        le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg hx _) hd3
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨Nat.pos_of_mem_divisors hdA, Nat.le_floor hdx⟩, Nat.dvd_of_mem_divisors hdA⟩
    · intro d _ _
      positivity
  calc
    _ ≤ ∑ a ∈ S, 3 * ∑ d ∈ I, if d ∣ a then (d.divisors.card : ℝ) else 0 :=
      Finset.sum_le_sum hpoint
    _ = 3 * ∑ d ∈ I, ∑ a ∈ S, if d ∣ a then (d.divisors.card : ℝ) else 0 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hS, Finset.filter_filter,
        mul_comm]

/-! ## A bound for `T(x)` by `∑_{d ≤ x^{2/3}} τ(d)/φ(d)` -/

/-- The first display in the proof of Lemma 4.4: for `x ≥ 2^48`,
`T(x) ≪ (x / log x) ∑_{d ≤ x^{2/3}} τ(d)/φ(d)`. Here `x / d ≥ x^{1/3} ≥ 2^16`, so the
bound (8) of Lemma 3.5 applies to every `d ≤ x^{2/3}`, and `log (x / d) ≥ (1/3) log x`. -/
theorem prime_form_tau_square_sum_le_totient_moment :
    ∃ C > 0, ∀ x : ℝ, (2 : ℝ) ^ 48 ≤ x →
      (∑ a ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun a => Nat.Prime (4 * a - 1)),
          ((a ^ 2).divisors.card : ℝ)) ≤
        C * (x / Real.log x) *
          ∑ d ∈ Finset.Icc 1 ⌊x ^ (2 / 3 : ℝ)⌋₊,
            (d.divisors.card : ℝ) / (Nat.totient d : ℝ) := by
  obtain ⟨K, hK, hBH⟩ := BrunHooley.prime_progression_count_upper
  refine ⟨36 * K, by positivity, ?_⟩
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  set r := x ^ (1 / 3 : ℝ) with hr_def
  have hr0 : 0 < r := Real.rpow_pos_of_pos hx0 _
  have hr3 : r ^ 3 = x := by
    rw [hr_def, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hr2 : x ^ (2 / 3 : ℝ) = r ^ 2 := by
    rw [hr_def, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hr16 : (2 : ℝ) ^ 16 ≤ r := by
    have h : ((2 : ℝ) ^ 16) ^ 3 ≤ r ^ 3 := by
      rw [hr3]
      calc
        ((2 : ℝ) ^ 16) ^ 3 = 2 ^ 48 := by norm_num
        _ ≤ x := hx
    exact le_of_pow_le_pow_left₀ (by norm_num) hr0.le h
  have hr1 : 1 < r := lt_of_lt_of_le (by norm_num) hr16
  have hlogx : Real.log x = 3 * Real.log r := by
    rw [← hr3, Real.log_pow]
    push_cast
    ring
  have hlogr : 0 < Real.log r := Real.log_pos hr1
  have hcount : ∀ d ∈ Finset.Icc 1 ⌊x ^ (2 / 3 : ℝ)⌋₊,
      (((Finset.Icc 1 ⌊x⌋₊).filter
        (fun a => Nat.Prime (4 * a - 1) ∧ d ∣ a)).card : ℝ) ≤
        12 * K * (x / Real.log x) / (Nat.totient d : ℝ) := by
    intro d hd
    obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
    have hdR : (d : ℝ) ≤ r ^ 2 := by
      rw [← hr2]
      exact (Nat.cast_le.mpr hdD).trans (Nat.floor_le (Real.rpow_nonneg hx0.le _))
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hrd : r * (d : ℝ) ≤ x := by
      rw [← hr3]
      nlinarith
    have hrange : (2 : ℝ) ^ 16 * ((4 * d : ℕ) : ℝ) ≤ 4 * x := by
      push_cast
      nlinarith
    have hcop : Nat.Coprime (4 * d - 1) (4 * d) := by
      have h := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right (4 * d - 1))
      rwa [show 4 * d - 1 + 1 = 4 * d by omega] at h
    have hBd := hBH (4 * x) (4 * d) (4 * d - 1) (by omega) hrange hcop
    have hinj := prime_form_multiples_card_le_primePrefix x hd1
    have hlogq : Real.log r ≤ Real.log (4 * x / ((4 * d : ℕ) : ℝ)) := by
      apply Real.log_le_log hr0
      rw [le_div_iff₀ (by positivity)]
      push_cast
      nlinarith
    have hφd : (0 : ℝ) < Nat.totient d := Nat.cast_pos.mpr (Nat.totient_pos.mpr hd1)
    have hφ : (Nat.totient d : ℝ) ≤ Nat.totient (4 * d) :=
      Nat.cast_le.mpr (Nat.le_of_dvd (Nat.totient_pos.mpr (by omega))
        (Nat.totient_dvd_of_dvd (dvd_mul_left d 4)))
    calc
      _ ≤ ((BrunHooley.primePrefix (4 * x) (4 * d) (4 * d - 1)).card : ℝ) :=
        Nat.cast_le.mpr hinj
      _ ≤ K * (4 * x) / ((Nat.totient (4 * d) : ℝ) *
          Real.log (4 * x / ((4 * d : ℕ) : ℝ))) := hBd
      _ ≤ K * (4 * x) / ((Nat.totient d : ℝ) * Real.log r) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul hφ hlogq hlogr.le (by positivity))
      _ = 12 * K * (x / Real.log x) / (Nat.totient d : ℝ) := by
        rw [hlogx]
        field_simp
        ring
  calc
    _ ≤ 3 * ∑ d ∈ Finset.Icc 1 ⌊x ^ (2 / 3 : ℝ)⌋₊, (d.divisors.card : ℝ) *
        (((Finset.Icc 1 ⌊x⌋₊).filter
          (fun a => Nat.Prime (4 * a - 1) ∧ d ∣ a)).card : ℝ) :=
      prime_form_tau_square_sum_le_short_divisor_counts x hx0.le
    _ ≤ 3 * ∑ d ∈ Finset.Icc 1 ⌊x ^ (2 / 3 : ℝ)⌋₊, (d.divisors.card : ℝ) *
        (12 * K * (x / Real.log x) / (Nat.totient d : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (hcount d hd) (Nat.cast_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring

/-! ## The sum `∑_{n ≤ Y} τ(n)/φ(n)` -/

/-- `φ(∏_{p ∈ S} p) = ∏_{p ∈ S} (p - 1)` for a finite set of primes. -/
theorem totient_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ((Nat.totient (∏ p ∈ S, p) : ℕ) : ℝ) = ∏ p ∈ S, ((p : ℝ) - 1) := by
  have h := Nat.totient_mul_prod_primeFactors (∏ p ∈ S, p)
  rw [Nat.primeFactors_prod hS, mul_comm (∏ p ∈ S, p) (∏ p ∈ S, (p - 1))] at h
  have hpos : 0 < ∏ p ∈ S, p := Finset.prod_pos (fun p hp => (hS p hp).pos)
  rw [Nat.eq_of_mul_eq_mul_right hpos h, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (hS p hp).one_le, Nat.cast_one]

/-- `n/φ(n) = ∑_{k ∣ n} μ²(k)/φ(k)`. -/
theorem div_totient_eq_sum_squarefree_divisors {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) / (Nat.totient n : ℝ) =
      ∑ k ∈ n.divisors.filter Squarefree, (1 : ℝ) / (Nat.totient k : ℝ) := by
  classical
  rw [Nat.sum_divisors_filter_squarefree hn]
  have hP : (UniqueFactorizationMonoid.normalizedFactors n).toFinset = n.primeFactors := by
    rw [Nat.factors_eq]
    rfl
  rw [hP]
  have hterm : ∀ S ∈ n.primeFactors.powerset,
      (1 : ℝ) / (Nat.totient S.val.prod : ℝ) = ∏ p ∈ S, ((p : ℝ) - 1)⁻¹ := by
    intro S hS
    have hSp : ∀ p ∈ S, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hS hp)
    have hval : S.val.prod = ∏ p ∈ S, p := by rw [Finset.prod_val]; rfl
    rw [hval, totient_prod_primes hSp, one_div, ← Finset.prod_inv_distrib]
  rw [Finset.sum_congr rfl hterm]
  have hexp := Finset.prod_add (fun p : ℕ => ((p : ℝ) - 1)⁻¹) (fun _ => (1 : ℝ)) n.primeFactors
  simp only [Finset.prod_const_one, mul_one] at hexp
  rw [← hexp]
  have hp1 : ∀ p ∈ n.primeFactors, (0 : ℝ) < (p : ℝ) - 1 := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  have hfactor : ∀ p ∈ n.primeFactors, ((p : ℝ) - 1)⁻¹ + 1 = (p : ℝ) / ((p : ℝ) - 1) := by
    intro p hp
    have h := (hp1 p hp).ne'
    field_simp
    ring
  rw [Finset.prod_congr rfl hfactor, Finset.prod_div_distrib]
  have htot := Nat.totient_mul_prod_primeFactors n
  have hcast : ((∏ p ∈ n.primeFactors, (p - 1) : ℕ) : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  have htotR : (Nat.totient n : ℝ) * ∏ p ∈ n.primeFactors, (p : ℝ) =
      (n : ℝ) * ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    rw [← hcast, ← Nat.cast_prod]
    exact_mod_cast htot
  have hφ : (0 : ℝ) < Nat.totient n := Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn))
  have hden : (0 : ℝ) < ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := Finset.prod_pos hp1
  rw [div_eq_div_iff hφ.ne' hden.ne']
  linarith

/-- For squarefree `k`, `τ(k) = 2^{ω(k)}`. -/
theorem card_divisors_of_squarefree {k : ℕ} (hk : Squarefree k) :
    (k.divisors.card : ℝ) = ∏ _p ∈ k.primeFactors, (2 : ℝ) := by
  have hk0 : k ≠ 0 := hk.ne_zero
  rw [Nat.card_divisors hk0]
  push_cast
  apply Finset.prod_congr rfl
  intro p hp
  have h1 : k.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one hk0).mp hk p
  have h2 : k.factorization p ≠ 0 := by
    rw [← Finsupp.mem_support_iff, Nat.support_factorization]
    exact hp
  have h3 : k.factorization p = 1 := by omega
  rw [h3]
  norm_num

/-- For squarefree `k`, `τ(k)/(k φ(k)) = ∏_{p ∣ k} 2/(p(p-1))`. -/
theorem squarefree_divisor_totient_weight_eq {k : ℕ} (hk : Squarefree k) :
    (k.divisors.card : ℝ) / ((k : ℝ) * Nat.totient k) =
      ∏ p ∈ k.primeFactors, 2 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hS : ∀ p ∈ k.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hkprod : ∏ p ∈ k.primeFactors, p = k := Nat.prod_primeFactors_of_squarefree hk
  have hφ : (Nat.totient k : ℝ) = ∏ p ∈ k.primeFactors, ((p : ℝ) - 1) := by
    have h := totient_prod_primes hS
    rwa [hkprod] at h
  have hkR : (k : ℝ) = ∏ p ∈ k.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, hkprod]
  rw [card_divisors_of_squarefree hk, hφ, hkR, ← Finset.prod_mul_distrib,
    ← Finset.prod_div_distrib]

/-- `∑_{k ≤ Y} μ²(k) τ(k)/(k φ(k)) ≤ ∏_{p ≤ Y} (1 + 2/(p(p-1)))`. -/
theorem squarefree_series_le_euler_product (Y : ℕ) :
    ∑ k ∈ (Finset.Icc 1 Y).filter Squarefree,
        (k.divisors.card : ℝ) / ((k : ℝ) * Nat.totient k) ≤
      ∏ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 1))) := by
  classical
  set A := (Finset.Icc 1 Y).filter Squarefree with hA
  set P := (Finset.Icc 1 Y).filter Nat.Prime with hP
  set g : ℕ → ℝ := fun p => 2 / ((p : ℝ) * ((p : ℝ) - 1)) with hg
  have hg0 : ∀ p ∈ P, 0 ≤ g p := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    have : 0 < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
    exact div_nonneg (by norm_num) this.le
  have hsum : ∑ k ∈ A, (k.divisors.card : ℝ) / ((k : ℝ) * Nat.totient k) =
      ∑ S ∈ A.image Nat.primeFactors, ∏ p ∈ S, g p := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro k hk
      exact squarefree_divisor_totient_weight_eq (Finset.mem_filter.mp hk).2
    · intro k hk l hl hkl
      rw [← Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.mp hk).2,
        ← Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.mp hl).2, hkl]
  have hsub : A.image Nat.primeFactors ⊆ P.powerset := by
    intro S hS
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hS
    rw [Finset.mem_powerset]
    intro p hp
    have hpP := Nat.prime_of_mem_primeFactors hp
    have hpk := Nat.le_of_mem_primeFactors hp
    have hkY := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpP.one_lt.le, hpk.trans hkY⟩, hpP⟩
  have hexp : ∏ p ∈ P, (1 + g p) = ∑ S ∈ P.powerset, ∏ p ∈ S, g p := by
    have h := Finset.prod_add g (fun _ => (1 : ℝ)) P
    simp only [Finset.prod_const_one, mul_one] at h
    rw [← h]
    exact Finset.prod_congr rfl (fun p _ => add_comm _ _)
  rw [hsum, hexp]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun S hS _ =>
    Finset.prod_nonneg (fun p hp => hg0 p (Finset.mem_powerset.mp hS hp)))

/-- `∑_{2 ≤ n ≤ Y} 1/(n(n-1)) ≤ 1`, by telescoping. -/
theorem sum_inv_mul_pred_le_one (Y : ℕ) :
    ∑ n ∈ Finset.Icc 2 Y, 1 / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 := by
  have key : ∀ m : ℕ, ∑ n ∈ Finset.Icc 2 (m + 1), 1 / ((n : ℝ) * ((n : ℝ) - 1)) =
      1 - 1 / ((m : ℝ) + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast
      have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have h2 : (0 : ℝ) < (m : ℝ) + 1 + 1 := by positivity
      field_simp
      ring
  cases Y with
  | zero => simp
  | succ m =>
    rw [key]
    have : 0 ≤ 1 / ((m : ℝ) + 1) := by positivity
    linarith

/-- `∏_{p ≤ Y} (1 + 2/(p(p-1))) ≤ e²`. -/
theorem euler_product_le_exp_two (Y : ℕ) :
    ∏ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 1))) ≤
      Real.exp 2 := by
  set P := (Finset.Icc 1 Y).filter Nat.Prime with hP
  have hpos : ∀ n ∈ Finset.Icc 2 Y, 0 ≤ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    intro n hn
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have : 0 < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    exact div_nonneg (by norm_num) this.le
  have hPsub : P ⊆ Finset.Icc 2 Y := by
    intro p hp
    obtain ⟨hpI, hpP⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨hpP.two_le, (Finset.mem_Icc.mp hpI).2⟩
  calc
    _ ≤ ∏ p ∈ P, Real.exp (2 / ((p : ℝ) * ((p : ℝ) - 1))) := by
      apply Finset.prod_le_prod
      · intro p hp
        linarith [hpos p (hPsub hp)]
      · intro p _
        linarith [Real.add_one_le_exp (2 / ((p : ℝ) * ((p : ℝ) - 1)))]
    _ = Real.exp (∑ p ∈ P, 2 / ((p : ℝ) * ((p : ℝ) - 1))) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp 2 := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ ∑ n ∈ Finset.Icc 2 Y, 2 / ((n : ℝ) * ((n : ℝ) - 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hPsub (fun n hn _ => hpos n hn)
        _ = 2 * ∑ n ∈ Finset.Icc 2 Y, 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          ring
        _ ≤ 2 := by linarith [sum_inv_mul_pred_le_one Y]

/-- `∑_{n ≤ Y} τ(n)/φ(n) ≤ (1 + log Y)² ∑_{k ≤ Y} μ²(k) τ(k)/(k φ(k))`, from
`n/φ(n) = ∑_{k ∣ n} μ²(k)/φ(k)` and `τ(kt) ≤ τ(k) τ(t)`. -/
theorem divisor_totient_sum_le_log_sq_mul_squarefree_series (Y : ℕ) :
    ∑ n ∈ Finset.Icc 1 Y, (n.divisors.card : ℝ) / (Nat.totient n : ℝ) ≤
      (1 + Real.log Y) ^ 2 *
        ∑ k ∈ (Finset.Icc 1 Y).filter Squarefree,
          (k.divisors.card : ℝ) / ((k : ℝ) * Nat.totient k) := by
  classical
  set f : ℕ → ℝ := fun k =>
    if Squarefree k then (k.divisors.card : ℝ) / ((k : ℝ) * Nat.totient k) else 0 with hf
  set g : ℕ → ℝ := fun t => (t.divisors.card : ℝ) / (t : ℝ) with hg
  have hf0 : ∀ k, 0 ≤ f k := by
    intro k
    simp only [hf]
    split_ifs <;> positivity
  have hg0 : ∀ t, 0 ≤ g t := fun t => by simp only [hg]; positivity
  have hpoint : ∀ n ∈ Finset.Icc 1 Y, (n.divisors.card : ℝ) / (Nat.totient n : ℝ) ≤
      ∑ k ∈ n.divisors, f k * g (n / k) := by
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
    have hφn : (0 : ℝ) < Nat.totient n := Nat.cast_pos.mpr (Nat.totient_pos.mpr hn0)
    calc
      _ = ((n.divisors.card : ℝ) / (n : ℝ)) * ((n : ℝ) / (Nat.totient n : ℝ)) := by
        field_simp
      _ = ((n.divisors.card : ℝ) / (n : ℝ)) *
          ∑ k ∈ n.divisors.filter Squarefree, (1 : ℝ) / (Nat.totient k : ℝ) := by
        rw [div_totient_eq_sum_squarefree_divisors hn0.ne']
      _ = ∑ k ∈ n.divisors, if Squarefree k then
            ((n.divisors.card : ℝ) / (n : ℝ)) * ((1 : ℝ) / (Nat.totient k : ℝ)) else 0 := by
        rw [Finset.mul_sum, Finset.sum_filter]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        by_cases hsq : Squarefree k
        · simp only [hf, hg, if_pos hsq]
          have hk0 : 0 < k := Nat.pos_of_mem_divisors hk
          have hprodN := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hk)
          have hm0 : 0 < n / k := Nat.div_pos (Nat.divisor_le hk) hk0
          have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk0
          have hmR : (0 : ℝ) < (n / k : ℕ) := Nat.cast_pos.mpr hm0
          have hφk : (0 : ℝ) < Nat.totient k := Nat.cast_pos.mpr (Nat.totient_pos.mpr hk0)
          have hsub : (n.divisors.card : ℝ) ≤
              (k.divisors.card : ℝ) * ((n / k : ℕ).divisors.card : ℝ) := by
            exact_mod_cast (hprodN ▸ divisor_card_mul_le k (n / k))
          have hprod : (n : ℝ) = (k : ℝ) * ((n / k : ℕ) : ℝ) := by
            exact_mod_cast hprodN.symm
          calc
            _ = (n.divisors.card : ℝ) / ((n : ℝ) * Nat.totient k) := by
              rw [div_mul_div_comm, mul_one]
            _ ≤ ((k.divisors.card : ℝ) * ((n / k : ℕ).divisors.card : ℝ)) /
                ((n : ℝ) * Nat.totient k) :=
              div_le_div_of_nonneg_right hsub (by positivity)
            _ = _ := by
              rw [hprod, div_mul_div_comm]
              congr 1
              ring
        · simp only [hf, if_neg hsq, zero_mul, le_refl]
  have hconv := divisor_convolution_sum_le_product Y f g hf0 hg0
  have hgsum : ∑ t ∈ Finset.Icc 1 Y, g t ≤ (1 + Real.log Y) ^ 2 := by
    have hmom := reciprocal_divisor_card_moment_le Y 1
    have hh : (∑ n ∈ Finset.Icc 1 Y, (1 : ℝ) / (n : ℝ)) = (harmonic Y : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
    simp only [pow_one, hh] at hmom
    have hH0 : (0 : ℝ) ≤ (harmonic Y : ℝ) := by
      rw [← hh]
      positivity
    exact hmom.trans (pow_le_pow_left₀ hH0 (harmonic_le_one_add_log Y) 2)
  have hfsum : ∑ k ∈ Finset.Icc 1 Y, f k = ∑ k ∈ (Finset.Icc 1 Y).filter Squarefree,
      (k.divisors.card : ℝ) / ((k : ℝ) * Nat.totient k) := by
    rw [Finset.sum_filter]
  have hfsum0 : 0 ≤ ∑ k ∈ Finset.Icc 1 Y, f k := Finset.sum_nonneg (fun k _ => hf0 k)
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 Y, ∑ k ∈ n.divisors, f k * g (n / k) := Finset.sum_le_sum hpoint
    _ ≤ (∑ k ∈ Finset.Icc 1 Y, f k) * (∑ t ∈ Finset.Icc 1 Y, g t) := hconv
    _ ≤ (∑ k ∈ Finset.Icc 1 Y, f k) * (1 + Real.log Y) ^ 2 :=
      mul_le_mul_of_nonneg_left hgsum hfsum0
    _ = _ := by rw [hfsum, mul_comm]

/-- `∑_{n ≤ Y} τ(n)/φ(n) ≤ e² (1 + log Y)²`. -/
theorem divisor_totient_sum_le (Y : ℕ) :
    ∑ n ∈ Finset.Icc 1 Y, (n.divisors.card : ℝ) / (Nat.totient n : ℝ) ≤
      Real.exp 2 * (1 + Real.log Y) ^ 2 := by
  calc
    _ ≤ (1 + Real.log Y) ^ 2 *
        ∑ k ∈ (Finset.Icc 1 Y).filter Squarefree,
          (k.divisors.card : ℝ) / ((k : ℝ) * Nat.totient k) :=
      divisor_totient_sum_le_log_sq_mul_squarefree_series Y
    _ ≤ (1 + Real.log Y) ^ 2 * Real.exp 2 :=
      mul_le_mul_of_nonneg_left
        ((squarefree_series_le_euler_product Y).trans (euler_product_le_exp_two Y))
        (sq_nonneg _)
    _ = _ := mul_comm _ _

/-! ## `T(x) ≪ x log x` and partial summation -/

/-- The trivial bound `T(x) ≤ x³`, used on the bounded initial range. -/
theorem prime_form_tau_square_sum_le_cube (x : ℝ) (hx : 0 ≤ x) :
    (∑ a ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun a => Nat.Prime (4 * a - 1)),
        ((a ^ 2).divisors.card : ℝ)) ≤ x ^ 3 := by
  set S := (Finset.Icc 1 ⌊x⌋₊).filter (fun a => Nat.Prime (4 * a - 1)) with hS
  have hterm : ∀ a ∈ S, ((a ^ 2).divisors.card : ℝ) ≤ x ^ 2 := by
    intro a ha
    have hax : (a : ℝ) ≤ x :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2).trans
        (Nat.floor_le hx)
    have hcard : (a ^ 2).divisors.card ≤ a ^ 2 := by
      calc
        (a ^ 2).divisors.card ≤ (Finset.Ico 1 (a ^ 2 + 1)).card := Finset.card_filter_le _ _
        _ = a ^ 2 := by simp
    calc
      ((a ^ 2).divisors.card : ℝ) ≤ (a : ℝ) ^ 2 := by exact_mod_cast hcard
      _ ≤ x ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg a) hax 2
  have hcardS : (S.card : ℝ) ≤ x := by
    have h : S.card ≤ ⌊x⌋₊ := (Finset.card_filter_le _ _).trans (by simp)
    exact (Nat.cast_le.mpr h).trans (Nat.floor_le hx)
  calc
    _ ≤ ∑ _a ∈ S, x ^ 2 := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * x ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ x * x ^ 2 := mul_le_mul_of_nonneg_right hcardS (sq_nonneg x)
    _ = x ^ 3 := by ring

/-- `T(x) ≪ x log x` for `x ≥ 2`. -/
theorem prime_form_tau_square_sum_le_mul_log :
    ∃ C > 0, ∀ x : ℝ, 2 ≤ x →
      (∑ a ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun a => Nat.Prime (4 * a - 1)),
          ((a ^ 2).divisors.card : ℝ)) ≤ C * x * Real.log x := by
  obtain ⟨C₁, hC₁, h₁⟩ := prime_form_tau_square_sum_le_totient_moment
  refine ⟨max (3 * C₁ * Real.exp 2) (2 ^ 97), by positivity, ?_⟩
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this
    linarith
  have hlogx2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlogx0 : 0 < Real.log x := by linarith
  by_cases hbig : (2 : ℝ) ^ 48 ≤ x
  · have hT := h₁ x hbig
    set D := ⌊x ^ (2 / 3 : ℝ)⌋₊ with hD
    have hmom := divisor_totient_sum_le D
    have hlogx1 : 1 ≤ Real.log x := by
      have h48 : Real.log ((2 : ℝ) ^ 48) ≤ Real.log x := Real.log_le_log (by positivity) hbig
      rw [Real.log_pow] at h48
      push_cast at h48
      linarith
    have hlogD0 : 0 ≤ Real.log (D : ℝ) := Real.log_natCast_nonneg D
    have hlogD : Real.log (D : ℝ) ≤ (2 / 3) * Real.log x := by
      rcases Nat.eq_zero_or_pos D with hD0 | hD0
      · rw [hD0, Nat.cast_zero, Real.log_zero]
        positivity
      · have hDle : (D : ℝ) ≤ x ^ (2 / 3 : ℝ) := Nat.floor_le (Real.rpow_nonneg hx0.le _)
        calc
          Real.log (D : ℝ) ≤ Real.log (x ^ (2 / 3 : ℝ)) :=
            Real.log_le_log (Nat.cast_pos.mpr hD0) hDle
          _ = (2 / 3) * Real.log x := Real.log_rpow hx0 _
    have hsq : (1 + Real.log (D : ℝ)) ^ 2 ≤ 3 * (Real.log x) ^ 2 := by
      have h1 : 1 + Real.log (D : ℝ) ≤ (5 / 3) * Real.log x := by linarith
      have h2 : (1 + Real.log (D : ℝ)) ^ 2 ≤ ((5 / 3) * Real.log x) ^ 2 :=
        pow_le_pow_left₀ (by linarith) h1 2
      nlinarith
    have hmom' : ∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) / (Nat.totient d : ℝ) ≤
        Real.exp 2 * (3 * (Real.log x) ^ 2) :=
      hmom.trans (mul_le_mul_of_nonneg_left hsq (Real.exp_pos 2).le)
    calc
      _ ≤ C₁ * (x / Real.log x) *
          ∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) / (Nat.totient d : ℝ) := hT
      _ ≤ C₁ * (x / Real.log x) * (Real.exp 2 * (3 * (Real.log x) ^ 2)) :=
        mul_le_mul_of_nonneg_left hmom' (by positivity)
      _ = (3 * C₁ * Real.exp 2) * x * Real.log x := by
        field_simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hlogx0.le
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hx0.le
  · have hxlt : x < 2 ^ 48 := lt_of_not_ge hbig
    calc
      _ ≤ x ^ 3 := prime_form_tau_square_sum_le_cube x hx0.le
      _ = x * x ^ 2 := by ring
      _ ≤ x * ((2 : ℝ) ^ 48) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0.le hxlt.le 2) hx0.le
      _ = 2 ^ 97 * x * (1 / 2) := by ring
      _ ≤ 2 ^ 97 * x * Real.log x :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hlogx0.le
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hx0.le

/-- The weight `a ↦ 1_{4a-1 prime} τ(a²)`. -/
noncomputable def primeFormTauSquare (a : ℕ) : ℝ :=
  if Nat.Prime (4 * a - 1) then ((a ^ 2).divisors.card : ℝ) else 0

theorem primeFormTauSquare_nonneg (a : ℕ) : 0 ≤ primeFormTauSquare a := by
  unfold primeFormTauSquare
  split_ifs <;> positivity

/-- `∑_{a ≤ N} 1_{4a-1 prime} τ(a²) ≤ A N (1 + log N)` for every `N ≥ 1`. -/
theorem primeFormTauSquare_prefix_le :
    ∃ A > 0, ∀ N : ℕ, 1 ≤ N →
      ∑ a ∈ Finset.Icc 1 N, primeFormTauSquare a ≤ A * N * (1 + Real.log N) := by
  obtain ⟨C, hC, hT⟩ := prime_form_tau_square_sum_le_mul_log
  refine ⟨max C 1, by positivity, ?_⟩
  intro N hN
  have hsum : ∑ a ∈ Finset.Icc 1 N, primeFormTauSquare a =
      ∑ a ∈ (Finset.Icc 1 ⌊(N : ℝ)⌋₊).filter (fun a => Nat.Prime (4 * a - 1)),
        ((a ^ 2).divisors.card : ℝ) := by
    rw [Nat.floor_natCast, Finset.sum_filter]
    rfl
  rw [hsum]
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNR
  rcases Nat.lt_or_ge N 2 with hN2 | hN2
  · have hN1 : N = 1 := by omega
    subst hN1
    calc
      _ ≤ ((1 : ℕ) : ℝ) ^ 3 := prime_form_tau_square_sum_le_cube _ (by norm_num)
      _ = 1 * ((1 : ℕ) : ℝ) * (1 + Real.log ((1 : ℕ) : ℝ)) := by simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by simp)
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by norm_num)
  · have hx : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    calc
      _ ≤ C * N * Real.log N := hT N hx
      _ ≤ max C 1 * N * (1 + Real.log N) := by
        apply mul_le_mul _ (by linarith) hlogN (by positivity)
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- `∑_{a ≤ L, 4a-1 prime} τ(a²)/a ≪ (log L)²` for all sufficiently large `L`. -/
theorem weighted_titchmarsh_divisor_bound :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L : ℝ, L₀ ≤ L →
      |∑ a ∈ (Finset.Icc 1 ⌊L⌋₊).filter (fun a => Nat.Prime (4 * a - 1)),
        ((a ^ 2).divisors.card : ℝ) / (a : ℝ)| ≤ C * (Real.log L) ^ (2 : ℝ) := by
  obtain ⟨A, hA, hprefix⟩ := primeFormTauSquare_prefix_le
  refine ⟨4 * A, Real.exp 1, by positivity, ?_⟩
  intro L hL
  have hsum : (∑ a ∈ (Finset.Icc 1 ⌊L⌋₊).filter (fun a => Nat.Prime (4 * a - 1)),
      ((a ^ 2).divisors.card : ℝ) / (a : ℝ)) =
      ∑ a ∈ Finset.Icc 1 ⌊L⌋₊, primeFormTauSquare a / (a : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hp : Nat.Prime (4 * a - 1) <;> simp [primeFormTauSquare, hp]
  have hLP : 0 < L := (Real.exp_pos 1).trans_le hL
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLP).mpr hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hL
  have hN1 : 1 ≤ ⌊L⌋₊ := (Nat.le_floor_iff hLP.le).mpr (by simpa using hL1)
  have hNP : (0 : ℝ) < (⌊L⌋₊ : ℝ) := by exact_mod_cast (show 0 < ⌊L⌋₊ by omega)
  have hlogN : Real.log (⌊L⌋₊ : ℝ) ≤ Real.log L :=
    Real.log_le_log hNP (Nat.floor_le hLP.le)
  have hlogN0 : 0 ≤ Real.log (⌊L⌋₊ : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  rw [hsum, abs_of_nonneg (Finset.sum_nonneg (fun n _ =>
    div_nonneg (primeFormTauSquare_nonneg n) (Nat.cast_nonneg n))), Real.rpow_two]
  calc
    _ ≤ A * (1 + Real.log (⌊L⌋₊ : ℝ)) ^ 2 :=
      reciprocal_bound_of_linear_log_prefix primeFormTauSquare primeFormTauSquare_nonneg
        A hA hprefix _ hN1
    _ ≤ A * (1 + Real.log L) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) 2) hA.le
    _ ≤ A * (4 * Real.log L ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hA.le
    _ = 4 * A * Real.log L ^ 2 := by ring

/-- Lemma 4.4: for `L ≥ 3`,
`∑_{a ≤ L, 4a-1 prime} τ(a²)/a ≪ (log L)²`. -/
theorem weighted_titchmarsh_divisor_bound_of_three_le :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 3 ≤ L →
      (∑ a ∈ (Finset.Icc 1 ⌊L⌋₊).filter (fun a => Nat.Prime (4 * a - 1)),
        ((a ^ 2).divisors.card : ℝ) / (a : ℝ)) ≤ C * (Real.log L) ^ 2 := by
  obtain ⟨C, L₀, hC, hbound⟩ := weighted_titchmarsh_divisor_bound
  let f : ℝ → ℝ := fun L => ∑ a ∈ (Finset.Icc 1 ⌊L⌋₊).filter (fun a => Nat.Prime (4 * a - 1)),
    ((a ^ 2).divisors.card : ℝ) / (a : ℝ)
  have hmono : ∀ L L' : ℝ, L ≤ L' → f L ≤ f L' := by
    intro L L' h
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset_filter _ (Finset.Icc_subset_Icc le_rfl (Nat.floor_mono h))
    · intro a _ _; positivity
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨max C (f (max L₀ 3) / Real.log 3 ^ 2), lt_max_of_lt_left hC, fun L hL => ?_⟩
  have hlogL : Real.log 3 ≤ Real.log L := Real.log_le_log (by norm_num) hL
  have hsq : Real.log 3 ^ 2 ≤ Real.log L ^ 2 := pow_le_pow_left₀ hlog3.le hlogL 2
  have hf0 : 0 ≤ f L := Finset.sum_nonneg (fun a _ => by positivity)
  by_cases hL₀ : L₀ ≤ L
  · have h := hbound L hL₀
    rw [abs_of_nonneg hf0, Real.rpow_two] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hle : f L ≤ f (max L₀ 3) := hmono _ _ ((not_le.mp hL₀).le.trans (le_max_left _ _))
    have hK0 : 0 ≤ f (max L₀ 3) := Finset.sum_nonneg (fun a _ => by positivity)
    calc f L ≤ f (max L₀ 3) := hle
      _ = f (max L₀ 3) / Real.log 3 ^ 2 * Real.log 3 ^ 2 := by field_simp
      _ ≤ max C (f (max L₀ 3) / Real.log 3 ^ 2) * Real.log L ^ 2 :=
          mul_le_mul (le_max_right _ _) hsq (by positivity) (by positivity)

end ErdosStraus.DivisorEstimates
