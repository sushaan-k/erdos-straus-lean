import Mathlib.Tactic

/-!
# Finite certificate layer

This file contains the exact arithmetic used beneath the analytic argument.
Its principal components are:

* the Type II and divisor-family unit-fraction identities;
* congruence-to-certificate and denominator-scaling lemmas;
* finite CRT compatibility and residual-lcm estimates for event families;
* Brun and Bonferroni inequalities on finite sets;
* interval counts for compatible congruence systems; and
* the worked examples and finite boundary checks used by the verifier.

All statements here are finite algebra or finite combinatorics.  Analytic sieve
estimates, asymptotic distribution theorems, Suen's inequality, and the
geometric statements are kept in the corresponding `EscAnalytic` modules.
-/

namespace EscLeanChecks

/- Cross-multiplied form of m/n = 1/x + 1/y + 1/z with m = 4. -/

def esCross (n x y z : Nat) : Prop :=
  n * (y * z + x * z + x * y) = 4 * x * y * z

def esCrossBool (n x y z : Nat) : Bool :=
  n * (y * z + x * z + x * y) == 4 * x * y * z

theorem esCross_scale
    (n k x y z : Nat)
    (h : esCross n x y z) :
    esCross (k * n) (k * x) (k * y) (k * z) := by
  unfold esCross at h ⊢
  calc
    k * n * (k * y * (k * z) + k * x * (k * z) + k * x * (k * y)) =
        k ^ 3 * (n * (y * z + x * z + x * y)) := by ring
    _ = k ^ 3 * (4 * x * y * z) := by rw [h]
    _ = 4 * (k * x) * (k * y) * (k * z) := by ring

theorem esCross_scale_of_dvd
    (n p x y z : Nat)
    (hp : 0 < p) (hdiv : p ∣ n)
    (h : esCross p x y z) :
    esCross n ((n / p) * x) ((n / p) * y) ((n / p) * z) := by
  rcases hdiv with ⟨k, hk⟩
  have hquot : n / p = k := by
    rw [hk]
    exact Nat.mul_div_right k hp
  have hscaled := esCross_scale p k x y z h
  have htarget : esCross n (k * x) (k * y) (k * z) := by
    simpa [hk, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hscaled
  simpa [hquot] using htarget

theorem esCross_unit_fraction_identity
    (n x y z : Nat)
    (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : esCross n x y z) :
    (4 : ℚ) / (n : ℚ) =
      1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  unfold esCross at h
  have hQ :
      (n : ℚ) * ((y : ℚ) * (z : ℚ) + (x : ℚ) * (z : ℚ) + (x : ℚ) * (y : ℚ)) =
        4 * (x : ℚ) * (y : ℚ) * (z : ℚ) := by
    exact_mod_cast h
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hxQ : (x : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
  have hyQ : (y : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hy)
  have hzQ : (z : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hz)
  field_simp [hnQ, hxQ, hyQ, hzQ]
  ring_nf at hQ ⊢
  nlinarith [hQ]

theorem unit_fraction_scale_of_dvd
    (n p x y z : Nat)
    (hn : 0 < n) (hp : 0 < p)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hdiv : p ∣ n)
    (hident :
      (4 : ℚ) / (p : ℚ) =
        1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) :
    ∃ x' y' z' : Nat,
      0 < x' ∧ 0 < y' ∧ 0 < z' ∧
      (4 : ℚ) / (n : ℚ) =
        1 / (x' : ℚ) + 1 / (y' : ℚ) + 1 / (z' : ℚ) := by
  rcases hdiv with ⟨k, hk⟩
  have hkpos : 0 < k := by
    by_contra hknot
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hknot
    rw [hk, hk0, mul_zero] at hn
    exact (Nat.lt_irrefl 0 hn)
  refine ⟨k * x, k * y, k * z,
    Nat.mul_pos hkpos hx, Nat.mul_pos hkpos hy, Nat.mul_pos hkpos hz, ?_⟩
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hp)
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hkpos)
  have hxQ : (x : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
  have hyQ : (y : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hy)
  have hzQ : (z : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hz)
  rw [hk]
  field_simp [hpQ, hkQ, hxQ, hyQ, hzQ] at hident ⊢
  have hmul := congrArg (fun t : ℚ => (k : ℚ) ^ 3 * t) hident
  ring_nf at hmul ⊢
  nlinarith [hmul]

def esRepresentable (n : Nat) : Prop :=
  ∃ x y z : Nat,
    0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (n : ℚ) =
        1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

def esExceptional (n : Nat) : Prop :=
  ¬ esRepresentable n

theorem esRepresentable_scale_of_dvd
    (n p : Nat)
    (hn : 0 < n) (hp : 0 < p)
    (hdiv : p ∣ n)
    (hrep : esRepresentable p) :
    esRepresentable n := by
  rcases hrep with ⟨x, y, z, hx, hy, hz, hident⟩
  exact unit_fraction_scale_of_dvd n p x y z hn hp hx hy hz hdiv hident

theorem esExceptional_divisor_of_exceptional
    (n p : Nat)
    (hn : 0 < n) (hp : 0 < p)
    (hdiv : p ∣ n)
    (hex : esExceptional n) :
    esExceptional p := by
  intro hrep
  exact hex (esRepresentable_scale_of_dvd n p hn hp hdiv hrep)

theorem esExceptional_prime_divisor_of_exceptional
    (n p : Nat)
    (hn : 0 < n) (hpprime : Nat.Prime p)
    (hdiv : p ∣ n)
    (hex : esExceptional n) :
    esExceptional p := by
  exact esExceptional_divisor_of_exceptional n p hn hpprime.pos hdiv hex

theorem esRepresentable_two : esRepresentable 2 := by
  refine ⟨1, 2, 2, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

theorem esRepresentable_three : esRepresentable 3 := by
  refine ⟨1, 4, 12, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

theorem esRepresentable_five : esRepresentable 5 := by
  refine ⟨2, 5, 10, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

theorem esRepresentable_seven : esRepresentable 7 := by
  refine ⟨2, 28, 28, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

theorem esRepresentable_eleven : esRepresentable 11 := by
  refine ⟨3, 66, 66, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

theorem esRepresentable_of_even
    (n : Nat) (hn : 0 < n) (heven : 2 ∣ n) :
    esRepresentable n :=
  esRepresentable_scale_of_dvd n 2 hn (by norm_num) heven esRepresentable_two

theorem esRepresentable_of_dvd_three
    (n : Nat) (hn : 0 < n) (h3 : 3 ∣ n) :
    esRepresentable n :=
  esRepresentable_scale_of_dvd n 3 hn (by norm_num) h3 esRepresentable_three

theorem esRepresentable_of_dvd_five
    (n : Nat) (hn : 0 < n) (h5 : 5 ∣ n) :
    esRepresentable n :=
  esRepresentable_scale_of_dvd n 5 hn (by norm_num) h5 esRepresentable_five

theorem esRepresentable_of_dvd_seven
    (n : Nat) (hn : 0 < n) (h7 : 7 ∣ n) :
    esRepresentable n :=
  esRepresentable_scale_of_dvd n 7 hn (by norm_num) h7 esRepresentable_seven

theorem esExceptional_not_dvd_two
    (n : Nat) (hn : 0 < n) (hex : esExceptional n) :
    ¬ 2 ∣ n :=
  fun h2 => hex (esRepresentable_of_even n hn h2)

theorem esExceptional_not_dvd_three
    (n : Nat) (hn : 0 < n) (hex : esExceptional n) :
    ¬ 3 ∣ n :=
  fun h3 => hex (esRepresentable_of_dvd_three n hn h3)

theorem esExceptional_not_dvd_five
    (n : Nat) (hn : 0 < n) (hex : esExceptional n) :
    ¬ 5 ∣ n :=
  fun h5 => hex (esRepresentable_of_dvd_five n hn h5)

theorem esExceptional_not_dvd_seven
    (n : Nat) (hn : 0 < n) (hex : esExceptional n) :
    ¬ 7 ∣ n :=
  fun h7 => hex (esRepresentable_of_dvd_seven n hn h7)

theorem esRepresentable_small_two_to_twelve
    (n : Nat) (h2 : 2 ≤ n) (h12 : n ≤ 12) :
    esRepresentable n := by
  interval_cases n
  · exact esRepresentable_two
  · exact esRepresentable_three
  · exact esRepresentable_of_even 4 (by norm_num) (by norm_num)
  · exact esRepresentable_five
  · exact esRepresentable_of_even 6 (by norm_num) (by norm_num)
  · exact esRepresentable_seven
  · exact esRepresentable_of_even 8 (by norm_num) (by norm_num)
  · exact esRepresentable_of_dvd_three 9 (by norm_num) (by norm_num)
  · exact esRepresentable_of_even 10 (by norm_num) (by norm_num)
  · exact esRepresentable_eleven
  · exact esRepresentable_of_even 12 (by norm_num) (by norm_num)

theorem esExceptional_coprime_two
    (n : Nat) (hn : 0 < n) (hex : esExceptional n) :
    Nat.Coprime n 2 :=
  ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 2)).mpr
    (esExceptional_not_dvd_two n hn hex)).symm

theorem esExceptional_coprime_three
    (n : Nat) (hn : 0 < n) (hex : esExceptional n) :
    Nat.Coprime n 3 :=
  ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).mpr
    (esExceptional_not_dvd_three n hn hex)).symm

theorem esExceptional_coprime_five
    (n : Nat) (hn : 0 < n) (hex : esExceptional n) :
    Nat.Coprime n 5 :=
  ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).mpr
    (esExceptional_not_dvd_five n hn hex)).symm

theorem esExceptional_coprime_seven
    (n : Nat) (hn : 0 < n) (hex : esExceptional n) :
    Nat.Coprime n 7 :=
  ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 7)).mpr
    (esExceptional_not_dvd_seven n hn hex)).symm

theorem esExceptional_coprime_210
    (n : Nat) (hn : 0 < n) (hex : esExceptional n) :
    Nat.Coprime n 210 := by
  rw [show (210 : Nat) = 2 * (3 * (5 * 7)) from by norm_num]
  exact (esExceptional_coprime_two n hn hex).mul_right
    ((esExceptional_coprime_three n hn hex).mul_right
      ((esExceptional_coprime_five n hn hex).mul_right
        (esExceptional_coprime_seven n hn hex)))

theorem coprime_mod_right_of_coprime
    (n P : Nat) (hcop : Nat.Coprime n P) :
    Nat.Coprime (n % P) P := by
  rw [Nat.coprime_iff_gcd_eq_one] at hcop ⊢
  rw [← Nat.gcd_rec P n]
  simpa [Nat.gcd_comm] using hcop

theorem esExceptional_odd
    (n : Nat) (hn : 0 < n) (hex : esExceptional n) :
    ¬ Even n := by
  intro ⟨k, hk⟩
  exact esExceptional_not_dvd_two n hn hex ⟨k, by omega⟩

theorem divisor_of_split_right {n s m : Nat} (h : n = s * m) : m ∣ n := by
  refine ⟨s, ?_⟩
  rw [h, Nat.mul_comm]

theorem esRepresentable_of_representable_divisor
    {n d : Nat}
    (hn : 0 < n) (hd : 0 < d) (hdiv : d ∣ n)
    (hrep : esRepresentable d) :
    esRepresentable n :=
  esRepresentable_scale_of_dvd n d hn hd hdiv hrep

theorem esRepresentable_mul_left
    {s n : Nat}
    (hs : 0 < s) (hn : 0 < n)
    (hrep : esRepresentable n) :
    esRepresentable (s * n) := by
  exact esRepresentable_of_representable_divisor
    (n := s * n) (d := n) (Nat.mul_pos hs hn) hn
    (divisor_of_split_right (n := s * n) (s := s) (m := n) rfl) hrep

theorem esRepresentable_mul_right
    {n s : Nat}
    (hn : 0 < n) (hs : 0 < s)
    (hrep : esRepresentable n) :
    esRepresentable (n * s) := by
  simpa [Nat.mul_comm] using
    esRepresentable_mul_left (s := s) (n := n) hs hn hrep

theorem esExceptional_divisor
    {n d : Nat}
    (hn : 0 < n) (hd : 0 < d) (hdiv : d ∣ n)
    (hex : esExceptional n) :
    esExceptional d :=
  esExceptional_divisor_of_exceptional n d hn hd hdiv hex

theorem esExceptional_factor_of_mul_left
    {s m : Nat}
    (hs : 0 < s) (hm : 0 < m)
    (hex : esExceptional (s * m)) :
    esExceptional m := by
  exact esExceptional_divisor
    (n := s * m) (d := m) (Nat.mul_pos hs hm) hm
    (divisor_of_split_right (n := s * m) (s := s) (m := m) rfl) hex

theorem esExceptional_factor_of_mul_right
    {m s : Nat}
    (hm : 0 < m) (hs : 0 < s)
    (hex : esExceptional (m * s)) :
    esExceptional m := by
  simpa [Nat.mul_comm] using
    esExceptional_factor_of_mul_left (s := s) (m := m) hs hm
      (by simpa [Nat.mul_comm] using hex)

theorem esExceptional_prime_factor
    {n p : Nat}
    (hn : 0 < n) (hp : Nat.Prime p) (hdiv : p ∣ n)
    (hex : esExceptional n) :
    esExceptional p :=
  esExceptional_prime_divisor_of_exceptional n p hn hp hdiv hex

def SmoothLiftSplit
    (Smooth Reduced : Nat → Prop) (n s m : Nat) : Prop :=
  n = s * m ∧ Smooth s ∧ Reduced m ∧ 0 < s ∧ 0 < m

def ReducedCoverageAssumption
    (Reduced Small Bad : Nat → Prop) : Prop :=
  ∀ m : Nat, 0 < m → Reduced m → ¬ Small m → ¬ Bad m → esRepresentable m

theorem smoothLiftSplit_n_pos
    {Smooth Reduced : Nat → Prop} {n s m : Nat}
    (hsplit : SmoothLiftSplit Smooth Reduced n s m) :
    0 < n := by
  rcases hsplit with ⟨hfactor, _hsmooth, _hred, hs, hm⟩
  rw [hfactor]
  exact Nat.mul_pos hs hm

theorem smoothLiftSplit_cofactor_dvd
    {Smooth Reduced : Nat → Prop} {n s m : Nat}
    (hsplit : SmoothLiftSplit Smooth Reduced n s m) :
    m ∣ n := by
  rcases hsplit with ⟨hfactor, _hsmooth, _hred, _hs, _hm⟩
  exact divisor_of_split_right hfactor

theorem smoothLiftSplit_cofactor_le
    {Smooth Reduced : Nat → Prop} {n s m : Nat}
    (hsplit : SmoothLiftSplit Smooth Reduced n s m) :
    m ≤ n := by
  rcases hsplit with ⟨hfactor, _hsmooth, _hred, hs, _hm⟩
  rw [hfactor]
  exact Nat.le_mul_of_pos_left m hs

theorem reducedCoverageAssumption_of_ge_two_coverage
    {Reduced Small Bad : Nat → Prop}
    (hcoverage : ∀ m : Nat, 2 ≤ m → Reduced m → esRepresentable m)
    (hsmallGeTwo : ∀ m : Nat, 0 < m → ¬ Small m → 2 ≤ m) :
    ReducedCoverageAssumption Reduced Small Bad := by
  intro m hm hred hnotSmall _hnotBad
  exact hcoverage m (hsmallGeTwo m hm hnotSmall) hred

theorem smoothLift_representable_of_clean_split
    {Smooth Reduced Small Bad : Nat → Prop} {n s m : Nat}
    (hsplit : SmoothLiftSplit Smooth Reduced n s m)
    (hcover : ReducedCoverageAssumption Reduced Small Bad)
    (hsmall : ¬ Small m) (hbad : ¬ Bad m) :
    esRepresentable n := by
  rcases hsplit with ⟨hfactor, _hsmooth, hred, hs, hm⟩
  have hn : 0 < n := by
    rw [hfactor]
    exact Nat.mul_pos hs hm
  have hdiv : m ∣ n := divisor_of_split_right hfactor
  exact esRepresentable_of_representable_divisor
    (n := n) (d := m) hn hm hdiv (hcover m hm hred hsmall hbad)

theorem smoothLift_exceptional_cofactor_exceptional
    {Smooth Reduced : Nat → Prop} {n s m : Nat}
    (hsplit : SmoothLiftSplit Smooth Reduced n s m)
    (hex : esExceptional n) :
    esExceptional m := by
  rcases hsplit with ⟨hfactor, _hsmooth, _hred, hs, hm⟩
  have hn : 0 < n := by
    rw [hfactor]
    exact Nat.mul_pos hs hm
  exact esExceptional_divisor
    (n := n) (d := m) hn hm (divisor_of_split_right hfactor) hex

theorem smoothLift_exceptional_small_or_bad
    {Smooth Reduced Small Bad : Nat → Prop} {n s m : Nat}
    (hsplit : SmoothLiftSplit Smooth Reduced n s m)
    (hcover : ReducedCoverageAssumption Reduced Small Bad)
    (hex : esExceptional n) :
    Small m ∨ Bad m := by
  by_cases hsmall : Small m
  · exact Or.inl hsmall
  · by_cases hbad : Bad m
    · exact Or.inr hbad
    · have hrepn : esRepresentable n :=
        smoothLift_representable_of_clean_split hsplit hcover hsmall hbad
      exact False.elim (hex hrepn)

theorem smoothLift_exceptional_has_small_or_bad_split
    {Smooth Reduced Small Bad : Nat → Prop} {N : Nat}
    (hsplitExists :
      ∀ n : Nat, 0 < n → n ≤ N →
        ∃ s m : Nat, SmoothLiftSplit Smooth Reduced n s m)
    (hcover : ReducedCoverageAssumption Reduced Small Bad) :
    ∀ n : Nat, 0 < n → n ≤ N → esExceptional n →
      ∃ s m : Nat,
        SmoothLiftSplit Smooth Reduced n s m ∧ (Small m ∨ Bad m) := by
  intro n hn hN hex
  rcases hsplitExists n hn hN with ⟨s, m, hsplit⟩
  exact ⟨s, m, hsplit,
    smoothLift_exceptional_small_or_bad
      (Smooth := Smooth) (Reduced := Reduced) (Small := Small) (Bad := Bad)
      (n := n) (s := s) (m := m) hsplit hcover hex⟩

noncomputable def exceptionalCountUpToGeTwo (N : Nat) : Nat := by
  classical
  exact ((Finset.range (N + 1)).filter
    (fun n => 2 ≤ n ∧ esExceptional n)).card

noncomputable def smoothLiftBadSplitCount
    (Smooth Reduced Small Bad : Nat → Prop) (N : Nat) : Nat := by
  classical
  exact ((Finset.range (N + 1)).filter
    (fun n =>
      2 ≤ n ∧
        ∃ s m : Nat,
          SmoothLiftSplit Smooth Reduced n s m ∧ (Small m ∨ Bad m))).card

noncomputable def smoothLiftSmallSplitCount
    (Smooth Reduced Small : Nat → Prop) (N : Nat) : Nat := by
  classical
  exact ((Finset.range (N + 1)).filter
    (fun n =>
      2 ≤ n ∧
        ∃ s m : Nat,
          SmoothLiftSplit Smooth Reduced n s m ∧ Small m)).card

noncomputable def smoothLiftBadCofactorSplitCount
    (Smooth Reduced Bad : Nat → Prop) (N : Nat) : Nat := by
  classical
  exact ((Finset.range (N + 1)).filter
    (fun n =>
      2 ≤ n ∧
        ∃ s m : Nat,
          SmoothLiftSplit Smooth Reduced n s m ∧ Bad m)).card

noncomputable def smoothLiftBadExceptionalCofactorSplitCount
    (Smooth Reduced Bad : Nat → Prop) (N : Nat) : Nat := by
  classical
  exact ((Finset.range (N + 1)).filter
    (fun n =>
      2 ≤ n ∧
        ∃ s m : Nat,
          SmoothLiftSplit Smooth Reduced n s m ∧ Bad m ∧ esExceptional m)).card

theorem smoothLiftBadSplitCount_le_small_add_badCofactor
    {Smooth Reduced Small Bad : Nat → Prop} {N : Nat} :
    smoothLiftBadSplitCount Smooth Reduced Small Bad N ≤
      smoothLiftSmallSplitCount Smooth Reduced Small N +
        smoothLiftBadCofactorSplitCount Smooth Reduced Bad N := by
  classical
  let smallSet : Finset Nat := (Finset.range (N + 1)).filter
    (fun n =>
      2 ≤ n ∧
        ∃ s m : Nat,
          SmoothLiftSplit Smooth Reduced n s m ∧ Small m)
  let badSet : Finset Nat := (Finset.range (N + 1)).filter
    (fun n =>
      2 ≤ n ∧
        ∃ s m : Nat,
          SmoothLiftSplit Smooth Reduced n s m ∧ Bad m)
  let allSet : Finset Nat := (Finset.range (N + 1)).filter
    (fun n =>
      2 ≤ n ∧
        ∃ s m : Nat,
          SmoothLiftSplit Smooth Reduced n s m ∧ (Small m ∨ Bad m))
  have hsubset : allSet ⊆ smallSet ∪ badSet := by
    intro n hn
    rcases Finset.mem_filter.mp hn with
      ⟨hnRange, hnTwo, s, m, hsplit, hsmallOrBad⟩
    cases hsmallOrBad with
    | inl hsmall =>
        exact Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_filter.mpr
            ⟨hnRange, hnTwo, ⟨s, m, hsplit, hsmall⟩⟩
    | inr hbad =>
        exact Finset.mem_union.mpr <| Or.inr <|
          Finset.mem_filter.mpr
            ⟨hnRange, hnTwo, ⟨s, m, hsplit, hbad⟩⟩
  have hcalc : allSet.card ≤ smallSet.card + badSet.card := by
    calc
      allSet.card ≤ (smallSet ∪ badSet).card := Finset.card_le_card hsubset
      _ ≤ smallSet.card + badSet.card := Finset.card_union_le smallSet badSet
  simpa [smoothLiftBadSplitCount, smoothLiftSmallSplitCount,
    smoothLiftBadCofactorSplitCount, allSet, smallSet, badSet] using hcalc

theorem exceptionalCountUpToGeTwo_le_smoothLiftSmall_add_badExceptionalCofactor
    {Smooth Reduced Small Bad : Nat → Prop} {N : Nat}
    (hsplitExists :
      ∀ n : Nat, 0 < n → n ≤ N →
        ∃ s m : Nat, SmoothLiftSplit Smooth Reduced n s m)
    (hcover : ReducedCoverageAssumption Reduced Small Bad) :
    exceptionalCountUpToGeTwo N ≤
      smoothLiftSmallSplitCount Smooth Reduced Small N +
        smoothLiftBadExceptionalCofactorSplitCount Smooth Reduced Bad N := by
  classical
  let exceptionalSet : Finset Nat := (Finset.range (N + 1)).filter
    (fun n => 2 ≤ n ∧ esExceptional n)
  let smallSet : Finset Nat := (Finset.range (N + 1)).filter
    (fun n =>
      2 ≤ n ∧
        ∃ s m : Nat,
          SmoothLiftSplit Smooth Reduced n s m ∧ Small m)
  let badExceptionalSet : Finset Nat := (Finset.range (N + 1)).filter
    (fun n =>
      2 ≤ n ∧
        ∃ s m : Nat,
          SmoothLiftSplit Smooth Reduced n s m ∧ Bad m ∧ esExceptional m)
  have hsubset : exceptionalSet ⊆ smallSet ∪ badExceptionalSet := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnRange, hnTwo, hnEx⟩
    have hnPos : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2) hnTwo
    have hnLe : n ≤ N :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hnRange)
    rcases hsplitExists n hnPos hnLe with ⟨s, m, hsplit⟩
    have hsmallOrBad : Small m ∨ Bad m :=
      smoothLift_exceptional_small_or_bad
        (Smooth := Smooth) (Reduced := Reduced) (Small := Small) (Bad := Bad)
        (n := n) (s := s) (m := m) hsplit hcover hnEx
    cases hsmallOrBad with
    | inl hsmall =>
        exact Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_filter.mpr
            ⟨hnRange, hnTwo, ⟨s, m, hsplit, hsmall⟩⟩
    | inr hbad =>
        have hmEx : esExceptional m :=
          smoothLift_exceptional_cofactor_exceptional
            (Smooth := Smooth) (Reduced := Reduced)
            (n := n) (s := s) (m := m) hsplit hnEx
        exact Finset.mem_union.mpr <| Or.inr <|
          Finset.mem_filter.mpr
            ⟨hnRange, hnTwo, ⟨s, m, hsplit, hbad, hmEx⟩⟩
  have hcalc :
      exceptionalSet.card ≤ smallSet.card + badExceptionalSet.card := by
    calc
      exceptionalSet.card ≤ (smallSet ∪ badExceptionalSet).card :=
        Finset.card_le_card hsubset
      _ ≤ smallSet.card + badExceptionalSet.card :=
        Finset.card_union_le smallSet badExceptionalSet
  simpa [exceptionalCountUpToGeTwo, smoothLiftSmallSplitCount,
    smoothLiftBadExceptionalCofactorSplitCount, exceptionalSet,
    smallSet, badExceptionalSet] using hcalc

theorem exceptionalCountUpToGeTwo_le_smoothLiftBadSplitCount
    {Smooth Reduced Small Bad : Nat → Prop} {N : Nat}
    (hsplitExists :
      ∀ n : Nat, 0 < n → n ≤ N →
        ∃ s m : Nat, SmoothLiftSplit Smooth Reduced n s m)
    (hcover : ReducedCoverageAssumption Reduced Small Bad) :
    exceptionalCountUpToGeTwo N ≤
      smoothLiftBadSplitCount Smooth Reduced Small Bad N := by
  classical
  unfold exceptionalCountUpToGeTwo smoothLiftBadSplitCount
  apply Finset.card_le_card
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hnRange, hnTwo, hnEx⟩
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2) hnTwo
  have hnLe : n ≤ N :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hnRange)
  rcases hsplitExists n hnPos hnLe with ⟨s, m, hsplit⟩
  have hsmallOrBad : Small m ∨ Bad m :=
    smoothLift_exceptional_small_or_bad
      (Smooth := Smooth) (Reduced := Reduced) (Small := Small) (Bad := Bad)
      (n := n) (s := s) (m := m) hsplit hcover hnEx
  exact Finset.mem_filter.mpr
    ⟨hnRange, hnTwo, ⟨s, m, hsplit, hsmallOrBad⟩⟩

theorem exceptionalCountUpToGeTwo_le_smoothLiftSmall_add_badCofactor
    {Smooth Reduced Small Bad : Nat → Prop} {N : Nat}
    (hsplitExists :
      ∀ n : Nat, 0 < n → n ≤ N →
        ∃ s m : Nat, SmoothLiftSplit Smooth Reduced n s m)
    (hcover : ReducedCoverageAssumption Reduced Small Bad) :
    exceptionalCountUpToGeTwo N ≤
      smoothLiftSmallSplitCount Smooth Reduced Small N +
        smoothLiftBadCofactorSplitCount Smooth Reduced Bad N := by
  exact le_trans
    (exceptionalCountUpToGeTwo_le_smoothLiftBadSplitCount
      (Smooth := Smooth) (Reduced := Reduced) (Small := Small) (Bad := Bad)
      (N := N) hsplitExists hcover)
    (smoothLiftBadSplitCount_le_small_add_badCofactor
      (Smooth := Smooth) (Reduced := Reduced) (Small := Small) (Bad := Bad)
      (N := N))

theorem exceptionalCountUpToGeTwo_eq_zero_of_smoothLiftSmall_and_badExceptional_zero
    {Smooth Reduced Small Bad : Nat → Prop} {N : Nat}
    (hsplitExists :
      ∀ n : Nat, 0 < n → n ≤ N →
        ∃ s m : Nat, SmoothLiftSplit Smooth Reduced n s m)
    (hcover : ReducedCoverageAssumption Reduced Small Bad)
    (hsmallZero : smoothLiftSmallSplitCount Smooth Reduced Small N = 0)
    (hbadZero :
      smoothLiftBadExceptionalCofactorSplitCount Smooth Reduced Bad N = 0) :
    exceptionalCountUpToGeTwo N = 0 := by
  have hle :=
    exceptionalCountUpToGeTwo_le_smoothLiftSmall_add_badExceptionalCofactor
      (Smooth := Smooth) (Reduced := Reduced) (Small := Small) (Bad := Bad)
      (N := N) hsplitExists hcover
  omega

theorem forall_esRepresentable_up_to_of_smoothLiftSmall_and_badExceptional_zero
    {Smooth Reduced Small Bad : Nat → Prop} {N : Nat}
    (hsplitExists :
      ∀ n : Nat, 0 < n → n ≤ N →
        ∃ s m : Nat, SmoothLiftSplit Smooth Reduced n s m)
    (hcover : ReducedCoverageAssumption Reduced Small Bad)
    (hsmallZero : smoothLiftSmallSplitCount Smooth Reduced Small N = 0)
    (hbadZero :
      smoothLiftBadExceptionalCofactorSplitCount Smooth Reduced Bad N = 0) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n := by
  classical
  have hzero : exceptionalCountUpToGeTwo N = 0 :=
    exceptionalCountUpToGeTwo_eq_zero_of_smoothLiftSmall_and_badExceptional_zero
      (Smooth := Smooth) (Reduced := Reduced) (Small := Small) (Bad := Bad)
      (N := N) hsplitExists hcover hsmallZero hbadZero
  intro n hnTwo hnLe
  by_contra hnNotRep
  have hnEx : esExceptional n := by
    simpa [esExceptional] using hnNotRep
  have hnRange : n ∈ Finset.range (N + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hnLe)
  have hnFilter :
      n ∈ (Finset.range (N + 1)).filter
        (fun n => 2 ≤ n ∧ esExceptional n) :=
    Finset.mem_filter.mpr ⟨hnRange, hnTwo, hnEx⟩
  have hpos :
      0 < ((Finset.range (N + 1)).filter
        (fun n => 2 ≤ n ∧ esExceptional n)).card :=
    Finset.card_pos.mpr ⟨n, hnFilter⟩
  unfold exceptionalCountUpToGeTwo at hzero
  rw [hzero] at hpos
  omega

theorem forall_esRepresentable_up_to_of_smoothLiftSmall_and_badExceptional_zero_of_ge_two_coverage
    {Smooth Reduced Small Bad : Nat → Prop} {N : Nat}
    (hsplitExists :
      ∀ n : Nat, 0 < n → n ≤ N →
        ∃ s m : Nat, SmoothLiftSplit Smooth Reduced n s m)
    (hcoverage : ∀ m : Nat, 2 ≤ m → Reduced m → esRepresentable m)
    (hsmallGeTwo : ∀ m : Nat, 0 < m → ¬ Small m → 2 ≤ m)
    (hsmallZero : smoothLiftSmallSplitCount Smooth Reduced Small N = 0)
    (hbadZero :
      smoothLiftBadExceptionalCofactorSplitCount Smooth Reduced Bad N = 0) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n :=
  forall_esRepresentable_up_to_of_smoothLiftSmall_and_badExceptional_zero
    (Smooth := Smooth) (Reduced := Reduced) (Small := Small) (Bad := Bad)
    (N := N) hsplitExists
    (reducedCoverageAssumption_of_ge_two_coverage hcoverage hsmallGeTwo)
    hsmallZero hbadZero

theorem exceptionalCountUpToGeTwo_eq_zero_of_smoothLiftBadSplitCount_eq_zero
    {Smooth Reduced Small Bad : Nat → Prop} {N : Nat}
    (hsplitExists :
      ∀ n : Nat, 0 < n → n ≤ N →
        ∃ s m : Nat, SmoothLiftSplit Smooth Reduced n s m)
    (hcover : ReducedCoverageAssumption Reduced Small Bad)
    (hbadZero : smoothLiftBadSplitCount Smooth Reduced Small Bad N = 0) :
    exceptionalCountUpToGeTwo N = 0 := by
  have hle :=
    exceptionalCountUpToGeTwo_le_smoothLiftBadSplitCount
      (Smooth := Smooth) (Reduced := Reduced) (Small := Small) (Bad := Bad)
      (N := N) hsplitExists hcover
  omega

theorem forall_esRepresentable_up_to_of_smoothLiftBadSplitCount_eq_zero
    {Smooth Reduced Small Bad : Nat → Prop} {N : Nat}
    (hsplitExists :
      ∀ n : Nat, 0 < n → n ≤ N →
        ∃ s m : Nat, SmoothLiftSplit Smooth Reduced n s m)
    (hcover : ReducedCoverageAssumption Reduced Small Bad)
    (hbadZero : smoothLiftBadSplitCount Smooth Reduced Small Bad N = 0) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n := by
  classical
  have hzero : exceptionalCountUpToGeTwo N = 0 :=
    exceptionalCountUpToGeTwo_eq_zero_of_smoothLiftBadSplitCount_eq_zero
      (Smooth := Smooth) (Reduced := Reduced) (Small := Small) (Bad := Bad)
      (N := N) hsplitExists hcover hbadZero
  intro n hnTwo hnLe
  by_contra hnNotRep
  have hnEx : esExceptional n := by
    simpa [esExceptional] using hnNotRep
  have hnRange : n ∈ Finset.range (N + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hnLe)
  have hnFilter :
      n ∈ (Finset.range (N + 1)).filter
        (fun n => 2 ≤ n ∧ esExceptional n) :=
    Finset.mem_filter.mpr ⟨hnRange, hnTwo, hnEx⟩
  have hpos :
      0 < ((Finset.range (N + 1)).filter
        (fun n => 2 ≤ n ∧ esExceptional n)).card :=
    Finset.card_pos.mpr ⟨n, hnFilter⟩
  unfold exceptionalCountUpToGeTwo at hzero
  rw [hzero] at hpos
  omega

/- The explicit parameter choice in (5.1):
   eta = 1/100, sigma = 1/20, lambda = 1/10, theta = 3/10, beta = 2/3.
   The inequalities are checked after clearing denominators. -/

def parameterInequalitiesHold : Bool :=
  decide
    ((1 : Nat) + 5 < 10 ∧
     10 + 1 < 30 ∧
     2 * 30 * 3 < 2 * 100 ∧
     2 * 100 < 3 * (100 - 5))

def parameterBoundsHold : Bool :=
  decide
    ((0 : Nat) < 1 ∧ 1 < 100 ∧
     (0 : Nat) < 1 ∧ 1 < 20 ∧
     (0 : Nat) < 1 ∧ 1 < 10 ∧
     (0 : Nat) < 3 ∧ 3 < 10 ∧
     (0 : Nat) < 2 ∧ 2 < 3)

example : parameterInequalitiesHold = true := by
  native_decide

example : parameterBoundsHold = true := by
  native_decide

/-!
## Elementary congruence core for the saturated dependency graph

The analytic proof uses a large-prime uniqueness lemma: two distinct compatible
events cannot share their large prime.  The following finite lemmas formalize the
arithmetic heart of that argument.  They do not formalize the surrounding
asymptotic estimates, but they do check the exact congruence cancellation and
small/rough split uniqueness used in the proof.
-/

def conditionalModulus (dPlus p : Nat) : Nat :=
  dPlus * p

def appendageG (dPlus p L : Nat) : Nat :=
  Nat.gcd (conditionalModulus dPlus p) L

def residueCompatible (q r a b : Nat) : Prop :=
  a ≡ b [MOD Nat.gcd q r]

/-- Data for a saturated residual event.  Its residual row is
`dPlus * p ∣ n + 4 * e`, so compatibility compares the shifted residues
`4 * e`, not bare `e`. -/
structure SatEvent where
  e : Nat
  dMinus : Nat
  dPlus : Nat
  p : Nat
deriving DecidableEq

def satEventRow (event : SatEvent) : Nat × Nat :=
  (event.dPlus, event.p)

def satEventRows (events : List SatEvent) : List (Nat × Nat) :=
  events.map satEventRow

def satEventCompatible (event other : SatEvent) : Prop :=
  residueCompatible
    (conditionalModulus event.dPlus event.p)
    (conditionalModulus other.dPlus other.p)
    (4 * event.e) (4 * other.e)

def satEventHit (n : Nat) (event : SatEvent) : Prop :=
  conditionalModulus event.dPlus event.p ∣ n + 4 * event.e

instance satEventHit_decidable (n : Nat) (event : SatEvent) :
    Decidable (satEventHit n event) := by
  unfold satEventHit
  infer_instance

/-- Congruence row attached to a saturated shifted residual hit
`dPlus * p ∣ n + 4 * e`. -/
def satEventShiftedResidualRow (event : SatEvent) : Nat × Nat :=
  (conditionalModulus event.dPlus event.p, 4 * event.e)

def satEventShiftedResidualRows (events : List SatEvent) : List (Nat × Nat) :=
  events.map satEventShiftedResidualRow

def negModResidue (q a : Nat) : Nat :=
  (q - a % q) % q

/-- Actual congruence row for the saturated shifted residual hit
`dPlus * p ∣ n + 4 * e`, represented as `n ≡ -4e` modulo `dPlus * p`. -/
def satEventResidualHitRow (event : SatEvent) : Nat × Nat :=
  let q := conditionalModulus event.dPlus event.p
  (q, negModResidue q (4 * event.e))

def satEventResidualHitRows (events : List SatEvent) : List (Nat × Nat) :=
  events.map satEventResidualHitRow

def satEventResidualHitRowsFinset (events : Finset SatEvent) : Finset (Nat × Nat) :=
  events.image satEventResidualHitRow

def satEventAdmissible (Pz rho : Nat) (event : SatEvent) : Prop :=
  Nat.Prime event.p ∧
  event.e < event.p ∧
  event.dMinus * event.dPlus < rho ∧
  (event.dMinus * event.dPlus) * event.p + 1 ≡ 0 [MOD 4 * rho] ∧
  0 < event.dMinus ∧
  0 < event.dPlus ∧
  event.dMinus ∣ Pz ∧
  Nat.Coprime event.dPlus Pz

def satEventAdmissibleFor (Pz : Nat) (rhoOf : Nat → Nat)
    (event : SatEvent) : Prop :=
  satEventAdmissible Pz (rhoOf event.e) event

theorem residueCompatible_of_common_shifted_hit
    (m n e f q r : Nat)
    (hqe : q ∣ n + m * e)
    (hrf : r ∣ n + m * f) :
    residueCompatible q r (m * e) (m * f) := by
  have hqeGcd : Nat.gcd q r ∣ n + m * e :=
    (Nat.gcd_dvd_left q r).trans hqe
  have hrfGcd : Nat.gcd q r ∣ n + m * f :=
    (Nat.gcd_dvd_right q r).trans hrf
  have hqeZero : n + m * e ≡ 0 [MOD Nat.gcd q r] :=
    (Nat.modEq_zero_iff_dvd).2 hqeGcd
  have hrfZero : n + m * f ≡ 0 [MOD Nat.gcd q r] :=
    (Nat.modEq_zero_iff_dvd).2 hrfGcd
  have hcommon : n + m * e ≡ n + m * f [MOD Nat.gcd q r] :=
    hqeZero.trans hrfZero.symm
  exact Nat.ModEq.add_left_cancel' n hcommon

theorem satEventCompatible_of_common_hit
    (n : Nat) (event other : SatEvent)
    (hevent : satEventHit n event)
    (hother : satEventHit n other) :
    satEventCompatible event other :=
  residueCompatible_of_common_shifted_hit
    4 n event.e other.e
    (conditionalModulus event.dPlus event.p)
    (conditionalModulus other.dPlus other.p)
    hevent hother

theorem negModResidue_add_modEq_zero (q a : Nat) (hq : 0 < q) :
    negModResidue q a + a ≡ 0 [MOD q] := by
  unfold negModResidue
  have ha : a % q ≤ q := Nat.le_of_lt (Nat.mod_lt a hq)
  have hqa : q - a % q + a % q = q := Nat.sub_add_cancel ha
  have haeq : a ≡ a % q [MOD q] := by
    exact (Nat.mod_modEq a q).symm
  have h1 : (q - a % q) + a ≡ (q - a % q) + (a % q) [MOD q] :=
    Nat.ModEq.add_left (q - a % q) haeq
  have h2 : (q - a % q) + (a % q) ≡ 0 [MOD q] := by
    rw [hqa]
    exact (Nat.modEq_zero_iff_dvd).2 (dvd_refl q)
  have hbase : (q - a % q) + a ≡ 0 [MOD q] := h1.trans h2
  have hmod : (q - a % q) % q ≡ q - a % q [MOD q] :=
    Nat.mod_modEq (q - a % q) q
  exact (Nat.ModEq.add_right a hmod).trans hbase

theorem modEq_negModResidue_iff_dvd_add
    (n q a : Nat) (hq : 0 < q) :
    n ≡ negModResidue q a [MOD q] ↔ q ∣ n + a := by
  constructor
  · intro hn
    have hneg := negModResidue_add_modEq_zero q a hq
    have hnadd : n + a ≡ negModResidue q a + a [MOD q] :=
      Nat.ModEq.add_right a hn
    exact (Nat.modEq_zero_iff_dvd).1 (hnadd.trans hneg)
  · intro hdiv
    have hnzero : n + a ≡ 0 [MOD q] := (Nat.modEq_zero_iff_dvd).2 hdiv
    have hnegzero := negModResidue_add_modEq_zero q a hq
    exact Nat.ModEq.add_right_cancel' a (hnzero.trans hnegzero.symm)

theorem satEventHit_iff_modEq_residualHitRow
    (n : Nat) (event : SatEvent)
    (hq : 0 < conditionalModulus event.dPlus event.p) :
    n ≡ (satEventResidualHitRow event).2
      [MOD (satEventResidualHitRow event).1] ↔
      satEventHit n event := by
  simpa [satEventResidualHitRow, satEventHit] using
    modEq_negModResidue_iff_dvd_add
      n (conditionalModulus event.dPlus event.p) (4 * event.e) hq

theorem residueCompatible_four_mul_iff_of_coprime_first_modulus
    (q r e f : Nat)
    (hq : Nat.gcd q 4 = 1) :
    residueCompatible q r (4 * e) (4 * f) ↔
      residueCompatible q r e f := by
  have hgcdCoprimeFour : Nat.gcd (Nat.gcd q r) 4 = 1 := by
    have hdiv :
        Nat.gcd (Nat.gcd q r) 4 ∣ Nat.gcd q 4 :=
      Nat.dvd_gcd
        ((Nat.gcd_dvd_left (Nat.gcd q r) 4).trans (Nat.gcd_dvd_left q r))
        (Nat.gcd_dvd_right (Nat.gcd q r) 4)
    exact Nat.dvd_one.mp (by simpa [hq] using hdiv)
  constructor
  · intro hcompat
    exact Nat.ModEq.cancel_left_of_coprime hgcdCoprimeFour hcompat
  · intro hcompat
    exact Nat.ModEq.mul_left 4 hcompat

theorem satEventCompatible_iff_residueCompatible_of_coprime_first_modulus
    (event other : SatEvent)
    (hcop :
      Nat.gcd (conditionalModulus event.dPlus event.p) 4 = 1) :
    satEventCompatible event other ↔
      residueCompatible
        (conditionalModulus event.dPlus event.p)
        (conditionalModulus other.dPlus other.p)
        event.e other.e := by
  exact residueCompatible_four_mul_iff_of_coprime_first_modulus
    (conditionalModulus event.dPlus event.p)
    (conditionalModulus other.dPlus other.p)
    event.e other.e hcop

theorem modEq_of_dvd_gcd_of_residueCompatible
    (q r a b s : Nat)
    (hdiv : s ∣ Nat.gcd q r)
    (hcompat : residueCompatible q r a b) :
    a ≡ b [MOD s] :=
  Nat.ModEq.of_dvd hdiv hcompat

theorem modEq_of_residueCompatible_four_mul_of_dvd_gcd_of_coprime
    (q r e f s : Nat)
    (hcompat : residueCompatible q r (4 * e) (4 * f))
    (hdiv : s ∣ Nat.gcd q r)
    (hcop : Nat.gcd s 4 = 1) :
    e ≡ f [MOD s] := by
  have hshiftedAtS : 4 * e ≡ 4 * f [MOD s] :=
    modEq_of_dvd_gcd_of_residueCompatible q r (4 * e) (4 * f) s hdiv hcompat
  exact Nat.ModEq.cancel_left_of_coprime hcop hshiftedAtS

theorem satEvent_modEq_of_compatible_of_dvd_gcd_of_coprime
    (event other : SatEvent) (s : Nat)
    (hcompat : satEventCompatible event other)
    (hdiv :
      s ∣ Nat.gcd
        (conditionalModulus event.dPlus event.p)
        (conditionalModulus other.dPlus other.p))
    (hcop : Nat.gcd s 4 = 1) :
    event.e ≡ other.e [MOD s] :=
  modEq_of_residueCompatible_four_mul_of_dvd_gcd_of_coprime
    (conditionalModulus event.dPlus event.p)
    (conditionalModulus other.dPlus other.p)
    event.e other.e s hcompat hdiv hcop

theorem satEvent_modEq_of_compatible_same_largePrime
    (event other : SatEvent)
    (hcompat : satEventCompatible event other)
    (hsamePrime : event.p = other.p)
    (hcop : Nat.gcd event.p 4 = 1) :
    event.e ≡ other.e [MOD event.p] := by
  have hpDvdEvent :
      event.p ∣ conditionalModulus event.dPlus event.p := by
    simp [conditionalModulus]
  have hpDvdOther :
      event.p ∣ conditionalModulus other.dPlus other.p := by
    simp [conditionalModulus, hsamePrime]
  have hpDvdGcd :
      event.p ∣ Nat.gcd
        (conditionalModulus event.dPlus event.p)
        (conditionalModulus other.dPlus other.p) :=
    Nat.dvd_gcd hpDvdEvent hpDvdOther
  exact satEvent_modEq_of_compatible_of_dvd_gcd_of_coprime
    event other event.p hcompat hpDvdGcd hcop

theorem satEvent_e_eq_of_compatible_same_largePrime_of_lt
    (event other : SatEvent)
    (hcompat : satEventCompatible event other)
    (hsamePrime : event.p = other.p)
    (hcop : Nat.gcd event.p 4 = 1)
    (he : event.e < event.p) (hotherE : other.e < other.p) :
    event.e = other.e := by
  have hmod : event.e ≡ other.e [MOD event.p] :=
    satEvent_modEq_of_compatible_same_largePrime event other hcompat hsamePrime hcop
  have hotherEAtEventP : other.e < event.p := by
    simpa [hsamePrime] using hotherE
  exact hmod.eq_of_lt_of_lt he hotherEAtEventP

/- Rows are `(dPlus, largePrime)` pairs from the saturated fan. -/
def residualLcm (old : List (Nat × Nat)) : Nat :=
  old.foldr (fun row acc => Nat.lcm (conditionalModulus row.1 row.2) acc) 1

/- Rows are `(modulus, residue)` pairs for an abstract congruence system. -/
def congruenceLcm (rows : List (Nat × Nat)) : Nat :=
  rows.foldr (fun row acc => Nat.lcm row.1 acc) 1

def satisfiesCongruenceRows (n : Nat) (rows : List (Nat × Nat)) : Prop :=
  ∀ row ∈ rows, n ≡ row.2 [MOD row.1]

def congruenceRowsModuliPositive (rows : List (Nat × Nat)) : Prop :=
  ∀ row ∈ rows, 0 < row.1

def congruenceRowsPairwiseCompatible (rows : List (Nat × Nat)) : Prop :=
  ∀ rowA ∈ rows, ∀ rowB ∈ rows,
    residueCompatible rowA.1 rowB.1 rowA.2 rowB.2

theorem congruenceLcm_pos_of_rows_positive
    (rows : List (Nat × Nat))
    (hrows : congruenceRowsModuliPositive rows) :
    0 < congruenceLcm rows := by
  induction rows with
  | nil =>
      simp [congruenceLcm]
  | cons row rest ih =>
      have hrow : 0 < row.1 := hrows row (by simp)
      have hrest : congruenceRowsModuliPositive rest := by
        intro r hr
        exact hrows r (by simp [hr])
      have hposRest : 0 < congruenceLcm rest := ih hrest
      simpa [congruenceLcm, List.foldr] using Nat.lcm_pos hrow hposRest

theorem residualLcm_pos
    (old : List (Nat × Nat))
    (hrows : ∀ row ∈ old, 0 < conditionalModulus row.1 row.2) :
    0 < residualLcm old := by
  induction old with
  | nil =>
      simp [residualLcm]
  | cons row rest ih =>
      have hrow : 0 < conditionalModulus row.1 row.2 := hrows row (by simp)
      have hrest : 0 < residualLcm rest := by
        apply ih
        intro r hr
        exact hrows r (by simp [hr])
      simpa [residualLcm, List.foldr] using Nat.lcm_pos hrow hrest

theorem crt_compatibility_of_common_residue
    (q r a b n : Nat)
    (hnq : n ≡ a [MOD q])
    (hnr : n ≡ b [MOD r]) :
    residueCompatible q r a b := by
  have hqa : n ≡ a [MOD Nat.gcd q r] :=
    Nat.ModEq.of_dvd (Nat.gcd_dvd_left q r) hnq
  have hqb : n ≡ b [MOD Nat.gcd q r] :=
    Nat.ModEq.of_dvd (Nat.gcd_dvd_right q r) hnr
  exact hqa.symm.trans hqb

theorem congruenceRowsPairwiseCompatible_of_solution
    (rows : List (Nat × Nat)) (n : Nat)
    (hn : satisfiesCongruenceRows n rows) :
    congruenceRowsPairwiseCompatible rows := by
  intro rowA hA rowB hB
  exact crt_compatibility_of_common_residue rowA.1 rowB.1 rowA.2 rowB.2 n
    (hn rowA hA) (hn rowB hB)

theorem satEvent_pairwiseCompatible_of_common_hit
    (events : List SatEvent) (n : Nat)
    (hhit : ∀ event ∈ events, satEventHit n event) :
    ∀ event ∈ events, ∀ other ∈ events, satEventCompatible event other := by
  intro event hevent other hother
  exact satEventCompatible_of_common_hit n event other
    (hhit event hevent) (hhit other hother)

theorem satEventShiftedResidualRows_pairwiseCompatible_of_pairwiseCompatible
    (events : List SatEvent)
    (hcompat :
      ∀ event ∈ events, ∀ other ∈ events, satEventCompatible event other) :
    congruenceRowsPairwiseCompatible (satEventShiftedResidualRows events) := by
  intro rowA hrowA rowB hrowB
  rcases List.mem_map.mp hrowA with ⟨event, hevent, hrowAeq⟩
  rcases List.mem_map.mp hrowB with ⟨other, hother, hrowBeq⟩
  subst hrowAeq
  subst hrowBeq
  simpa [satEventShiftedResidualRow, satEventCompatible] using
    hcompat event hevent other hother

theorem satEventShiftedResidualRows_pairwiseCompatible_of_common_hit
    (events : List SatEvent) (n : Nat)
    (hhit : ∀ event ∈ events, satEventHit n event) :
    congruenceRowsPairwiseCompatible (satEventShiftedResidualRows events) :=
  satEventShiftedResidualRows_pairwiseCompatible_of_pairwiseCompatible events
    (satEvent_pairwiseCompatible_of_common_hit events n hhit)

theorem residueCompatible_negModResidue_of_residueCompatible
    (q r a b : Nat) (hq : 0 < q) (hr : 0 < r)
    (hcompat : residueCompatible q r a b) :
    residueCompatible q r (negModResidue q a) (negModResidue r b) := by
  have hleft : negModResidue q a + a ≡ 0 [MOD Nat.gcd q r] :=
    Nat.ModEq.of_dvd (Nat.gcd_dvd_left q r)
      (negModResidue_add_modEq_zero q a hq)
  have hright : negModResidue r b + b ≡ 0 [MOD Nat.gcd q r] :=
    Nat.ModEq.of_dvd (Nat.gcd_dvd_right q r)
      (negModResidue_add_modEq_zero r b hr)
  exact Nat.ModEq.add_right_cancel hcompat (hleft.trans hright.symm)

theorem satEventResidualHitRow_compatible_of_satEventCompatible
    (event other : SatEvent)
    (heventMod : 0 < conditionalModulus event.dPlus event.p)
    (hotherMod : 0 < conditionalModulus other.dPlus other.p)
    (hcompat : satEventCompatible event other) :
    residueCompatible
      (satEventResidualHitRow event).1 (satEventResidualHitRow other).1
      (satEventResidualHitRow event).2 (satEventResidualHitRow other).2 := by
  simpa [satEventResidualHitRow, satEventCompatible] using
    residueCompatible_negModResidue_of_residueCompatible
      (conditionalModulus event.dPlus event.p)
      (conditionalModulus other.dPlus other.p)
      (4 * event.e) (4 * other.e) heventMod hotherMod hcompat

theorem satEventResidualHitRows_pairwiseCompatible_of_pairwiseCompatible
    (Pz rho : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hcompat :
      ∀ event ∈ events, ∀ other ∈ events, satEventCompatible event other) :
    congruenceRowsPairwiseCompatible (satEventResidualHitRows events) := by
  intro rowA hrowA rowB hrowB
  rcases List.mem_map.mp hrowA with ⟨event, hevent, hrowAeq⟩
  rcases List.mem_map.mp hrowB with ⟨other, hother, hrowBeq⟩
  subst hrowAeq
  subst hrowBeq
  have hdPlusPos : 0 < event.dPlus :=
    (hadm event hevent).2.2.2.2.2.1
  have hpPos : 0 < event.p := (hadm event hevent).1.pos
  have hotherDPlusPos : 0 < other.dPlus :=
    (hadm other hother).2.2.2.2.2.1
  have hotherPPos : 0 < other.p := (hadm other hother).1.pos
  exact satEventResidualHitRow_compatible_of_satEventCompatible event other
    (Nat.mul_pos hdPlusPos hpPos)
    (Nat.mul_pos hotherDPlusPos hotherPPos)
    (hcompat event hevent other hother)

theorem satEventResidualHitRows_toList_pairwiseCompatible_of_pairwiseCompatible
    (Pz rho : Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hcompat :
      ∀ event ∈ events, ∀ other ∈ events, satEventCompatible event other) :
    congruenceRowsPairwiseCompatible (satEventResidualHitRows events.toList) :=
  satEventResidualHitRows_pairwiseCompatible_of_pairwiseCompatible Pz rho
    events.toList
    (by
      intro event hevent
      exact hadm event (by simpa using hevent))
    (by
      intro event hevent other hother
      exact hcompat event (by simpa using hevent) other (by simpa using hother))

theorem satEventResidualHitRows_moduliPositive_of_admissible
    (Pz rho : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event) :
    congruenceRowsModuliPositive (satEventResidualHitRows events) := by
  intro row hrow
  rcases List.mem_map.mp hrow with ⟨event, hevent, hrowEq⟩
  subst hrowEq
  have hdPlusPos : 0 < event.dPlus :=
    (hadm event hevent).2.2.2.2.2.1
  have hpPos : 0 < event.p := (hadm event hevent).1.pos
  simpa [satEventResidualHitRow, conditionalModulus] using
    Nat.mul_pos hdPlusPos hpPos

theorem satEventResidualHitRowsFinset_moduliPositive_of_admissible
    (Pz rho : Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event) :
    ∀ row ∈ satEventResidualHitRowsFinset events, 0 < row.1 := by
  intro row hrow
  rcases Finset.mem_image.mp hrow with ⟨event, hevent, hrowEq⟩
  subst hrowEq
  have hdPlusPos : 0 < event.dPlus :=
    (hadm event hevent).2.2.2.2.2.1
  have hpPos : 0 < event.p := (hadm event hevent).1.pos
  simpa [satEventResidualHitRowsFinset, satEventResidualHitRow, conditionalModulus] using
    Nat.mul_pos hdPlusPos hpPos

theorem satEventResidualHitRowsFinset_base_coprime_of_admissible
    (Pz rho : Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hpCop : ∀ event ∈ events, Nat.Coprime Pz event.p) :
    ∀ row ∈ satEventResidualHitRowsFinset events, Nat.Coprime Pz row.1 := by
  intro row hrow
  rcases Finset.mem_image.mp hrow with ⟨event, hevent, hrowEq⟩
  subst hrowEq
  rcases hadm event hevent with
    ⟨_hpPrime, _heLt, _hmedium, _hprog,
      _hdMinusPos, _hdPlusPos, _hdMinusDvd, hdPlusCop⟩
  have hdPlusCopBase : Nat.Coprime Pz event.dPlus := hdPlusCop.symm
  have hrowCop : Nat.Coprime Pz (event.dPlus * event.p) :=
    hdPlusCopBase.mul_right (hpCop event hevent)
  simpa [satEventResidualHitRowsFinset, satEventResidualHitRow,
    conditionalModulus] using hrowCop

theorem satEventResidualHitRows_moduliPositive_of_admissibleFor
    (Pz : Nat) (rhoOf : Nat → Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event) :
    congruenceRowsModuliPositive (satEventResidualHitRows events) := by
  intro row hrow
  rcases List.mem_map.mp hrow with ⟨event, hevent, hrowEq⟩
  subst hrowEq
  have heventAdm : satEventAdmissible Pz (rhoOf event.e) event := by
    simpa [satEventAdmissibleFor] using hadm event hevent
  have hdPlusPos : 0 < event.dPlus := heventAdm.2.2.2.2.2.1
  have hpPos : 0 < event.p := heventAdm.1.pos
  simpa [satEventResidualHitRow, conditionalModulus] using
    Nat.mul_pos hdPlusPos hpPos

theorem satEventResidualHitRowsFinset_moduliPositive_of_admissibleFor
    (Pz : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event) :
    ∀ row ∈ satEventResidualHitRowsFinset events, 0 < row.1 := by
  intro row hrow
  rcases Finset.mem_image.mp hrow with ⟨event, hevent, hrowEq⟩
  subst hrowEq
  have heventAdm : satEventAdmissible Pz (rhoOf event.e) event := by
    simpa [satEventAdmissibleFor] using hadm event hevent
  have hdPlusPos : 0 < event.dPlus := heventAdm.2.2.2.2.2.1
  have hpPos : 0 < event.p := heventAdm.1.pos
  simpa [satEventResidualHitRowsFinset, satEventResidualHitRow,
    conditionalModulus] using Nat.mul_pos hdPlusPos hpPos

theorem satEventResidualHitRowsFinset_base_coprime_of_admissibleFor
    (Pz : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hpCop : ∀ event ∈ events, Nat.Coprime Pz event.p) :
    ∀ row ∈ satEventResidualHitRowsFinset events, Nat.Coprime Pz row.1 := by
  intro row hrow
  rcases Finset.mem_image.mp hrow with ⟨event, hevent, hrowEq⟩
  subst hrowEq
  have heventAdm : satEventAdmissible Pz (rhoOf event.e) event := by
    simpa [satEventAdmissibleFor] using hadm event hevent
  have hdPlusCopBase : Nat.Coprime Pz event.dPlus :=
    heventAdm.2.2.2.2.2.2.2.symm
  have hrowCop : Nat.Coprime Pz (event.dPlus * event.p) :=
    hdPlusCopBase.mul_right (hpCop event hevent)
  simpa [satEventResidualHitRowsFinset, satEventResidualHitRow,
    conditionalModulus] using hrowCop

theorem satisfiesCongruenceRows_satEventResidualHitRows_iff_hits
    (Pz rho n : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event) :
    satisfiesCongruenceRows n (satEventResidualHitRows events) ↔
      ∀ event ∈ events, satEventHit n event := by
  constructor
  · intro hs event hevent
    have hrow : satEventResidualHitRow event ∈ satEventResidualHitRows events := by
      exact List.mem_map.mpr ⟨event, hevent, rfl⟩
    have hdPlusPos : 0 < event.dPlus :=
      (hadm event hevent).2.2.2.2.2.1
    have hpPos : 0 < event.p := (hadm event hevent).1.pos
    have hq : 0 < conditionalModulus event.dPlus event.p :=
      Nat.mul_pos hdPlusPos hpPos
    exact (satEventHit_iff_modEq_residualHitRow n event hq).1
      (hs (satEventResidualHitRow event) hrow)
  · intro hhit row hrow
    rcases List.mem_map.mp hrow with ⟨event, hevent, hrowEq⟩
    subst hrowEq
    have hdPlusPos : 0 < event.dPlus :=
      (hadm event hevent).2.2.2.2.2.1
    have hpPos : 0 < event.p := (hadm event hevent).1.pos
    have hq : 0 < conditionalModulus event.dPlus event.p :=
      Nat.mul_pos hdPlusPos hpPos
    exact (satEventHit_iff_modEq_residualHitRow n event hq).2
      (hhit event hevent)

theorem satEventResidualHitRows_pairwiseCompatible_of_common_hit
    (Pz rho n : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hhit : ∀ event ∈ events, satEventHit n event) :
    congruenceRowsPairwiseCompatible (satEventResidualHitRows events) := by
  exact congruenceRowsPairwiseCompatible_of_solution
    (satEventResidualHitRows events) n
    ((satisfiesCongruenceRows_satEventResidualHitRows_iff_hits
      Pz rho n events hadm).2 hhit)

theorem satisfiesCongruenceRows_satEventResidualHitRows_iff_hits_admissibleFor
    (Pz : Nat) (rhoOf : Nat → Nat) (n : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event) :
    satisfiesCongruenceRows n (satEventResidualHitRows events) ↔
      ∀ event ∈ events, satEventHit n event := by
  constructor
  · intro hs event hevent
    have hrow : satEventResidualHitRow event ∈ satEventResidualHitRows events :=
      List.mem_map.mpr ⟨event, hevent, rfl⟩
    have heventAdm : satEventAdmissible Pz (rhoOf event.e) event := by
      simpa [satEventAdmissibleFor] using hadm event hevent
    have hq : 0 < conditionalModulus event.dPlus event.p :=
      Nat.mul_pos heventAdm.2.2.2.2.2.1 heventAdm.1.pos
    exact (satEventHit_iff_modEq_residualHitRow n event hq).1
      (hs (satEventResidualHitRow event) hrow)
  · intro hhit row hrow
    rcases List.mem_map.mp hrow with ⟨event, hevent, hrowEq⟩
    subst hrowEq
    have heventAdm : satEventAdmissible Pz (rhoOf event.e) event := by
      simpa [satEventAdmissibleFor] using hadm event hevent
    have hq : 0 < conditionalModulus event.dPlus event.p :=
      Nat.mul_pos heventAdm.2.2.2.2.2.1 heventAdm.1.pos
    exact (satEventHit_iff_modEq_residualHitRow n event hq).2
      (hhit event hevent)

theorem satEventResidualHitRows_pairwiseCompatible_of_common_hit_admissibleFor
    (Pz : Nat) (rhoOf : Nat → Nat) (n : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hhit : ∀ event ∈ events, satEventHit n event) :
    congruenceRowsPairwiseCompatible (satEventResidualHitRows events) := by
  exact congruenceRowsPairwiseCompatible_of_solution
    (satEventResidualHitRows events) n
    ((satisfiesCongruenceRows_satEventResidualHitRows_iff_hits_admissibleFor
      Pz rhoOf n events hadm).2 hhit)

theorem gcd_lcm_distrib_left_of_pos
    (q m L : Nat) (hq : 0 < q) (hm : 0 < m) (hL : 0 < L) :
    Nat.gcd q (Nat.lcm m L) =
      Nat.lcm (Nat.gcd q m) (Nat.gcd q L) := by
  apply Nat.eq_of_factorization_eq
  · exact ne_of_gt (Nat.gcd_pos_of_pos_left (Nat.lcm m L) hq)
  · exact ne_of_gt (Nat.lcm_pos
      (Nat.gcd_pos_of_pos_left m hq)
      (Nat.gcd_pos_of_pos_left L hq))
  · intro p
    have hqne : q ≠ 0 := ne_of_gt hq
    have hmne : m ≠ 0 := ne_of_gt hm
    have hLne : L ≠ 0 := ne_of_gt hL
    have hlcmne : Nat.lcm m L ≠ 0 := ne_of_gt (Nat.lcm_pos hm hL)
    have hgqmne : Nat.gcd q m ≠ 0 :=
      ne_of_gt (Nat.gcd_pos_of_pos_left m hq)
    have hgqLne : Nat.gcd q L ≠ 0 :=
      ne_of_gt (Nat.gcd_pos_of_pos_left L hq)
    rw [Nat.factorization_gcd hqne hlcmne,
      Nat.factorization_lcm hmne hLne,
      Nat.factorization_lcm hgqmne hgqLne,
      Nat.factorization_gcd hqne hmne,
      Nat.factorization_gcd hqne hLne]
    simp [Pi.inf_apply, Pi.sup_apply, inf_sup_left]

theorem congruenceRow_compatible_with_solution_lcm
    (row : Nat × Nat) (rows : List (Nat × Nat)) (y : Nat)
    (hrowpos : 0 < row.1)
    (hrowspos : congruenceRowsModuliPositive rows)
    (hcompat : ∀ tail ∈ rows,
      residueCompatible row.1 tail.1 row.2 tail.2)
    (hy : satisfiesCongruenceRows y rows) :
    residueCompatible row.1 (congruenceLcm rows) row.2 y := by
  induction rows with
  | nil =>
      simpa [residueCompatible, congruenceLcm] using
        (Nat.modEq_one : row.2 ≡ y [MOD 1])
  | cons head rest ih =>
      have hheadpos : 0 < head.1 := hrowspos head (by simp)
      have hrestpos : congruenceRowsModuliPositive rest := by
        intro tail htail
        exact hrowspos tail (by simp [htail])
      have hLrest : 0 < congruenceLcm rest :=
        congruenceLcm_pos_of_rows_positive rest hrestpos
      have hheadCompat : row.2 ≡ head.2 [MOD Nat.gcd row.1 head.1] :=
        hcompat head (by simp)
      have hyhead : y ≡ head.2 [MOD head.1] := hy head (by simp)
      have hyheadG : y ≡ head.2 [MOD Nat.gcd row.1 head.1] :=
        Nat.ModEq.of_dvd (Nat.gcd_dvd_right row.1 head.1) hyhead
      have hhead : row.2 ≡ y [MOD Nat.gcd row.1 head.1] :=
        hheadCompat.trans hyheadG.symm
      have hyrest : satisfiesCongruenceRows y rest := by
        intro tail htail
        exact hy tail (by simp [htail])
      have hrestCompat : ∀ tail ∈ rest,
          residueCompatible row.1 tail.1 row.2 tail.2 := by
        intro tail htail
        exact hcompat tail (by simp [htail])
      have hrest : row.2 ≡ y [MOD Nat.gcd row.1 (congruenceLcm rest)] :=
        ih hrestpos hrestCompat hyrest
      have hcombined : row.2 ≡ y
          [MOD Nat.lcm (Nat.gcd row.1 head.1)
            (Nat.gcd row.1 (congruenceLcm rest))] :=
        Nat.mod_lcm hhead hrest
      have hdist := gcd_lcm_distrib_left_of_pos
        row.1 head.1 (congruenceLcm rest) hrowpos hheadpos hLrest
      change row.2 ≡ y [MOD Nat.gcd row.1 (Nat.lcm head.1 (congruenceLcm rest))]
      rw [hdist]
      exact hcombined

theorem crt_common_residue_exists
    (q r a b : Nat)
    (hcompat : residueCompatible q r a b) :
    ∃ k : Nat, k ≡ a [MOD q] ∧ k ≡ b [MOD r] := by
  exact ⟨Nat.chineseRemainder' hcompat, (Nat.chineseRemainder' hcompat).property⟩

theorem crt_common_residue_exists_lt_lcm
    (q r a b : Nat)
    (hq : q ≠ 0) (hr : r ≠ 0)
    (hcompat : residueCompatible q r a b) :
    ∃ k : Nat, k < Nat.lcm q r ∧ k ≡ a [MOD q] ∧ k ≡ b [MOD r] := by
  refine ⟨Nat.chineseRemainder' hcompat, ?_, ?_⟩
  · exact Nat.chineseRemainder'_lt_lcm hcompat hq hr
  · exact (Nat.chineseRemainder' hcompat).property

theorem crt_common_residue_unique_mod_lcm
    (q r a b x y : Nat)
    (hxq : x ≡ a [MOD q]) (hyq : y ≡ a [MOD q])
    (hxr : x ≡ b [MOD r]) (hyr : y ≡ b [MOD r]) :
    x ≡ y [MOD Nat.lcm q r] := by
  exact Nat.mod_lcm (hxq.trans hyq.symm) (hxr.trans hyr.symm)

theorem crt_common_residue_modEq_chineseRemainder
    (q r a b z : Nat)
    (hcompat : residueCompatible q r a b)
    (hzq : z ≡ a [MOD q])
    (hzr : z ≡ b [MOD r]) :
    z ≡ (Nat.chineseRemainder' hcompat : Nat) [MOD Nat.lcm q r] := by
  exact crt_common_residue_unique_mod_lcm q r a b z
    (Nat.chineseRemainder' hcompat) hzq
    (Nat.chineseRemainder' hcompat).property.1 hzr
    (Nat.chineseRemainder' hcompat).property.2

theorem congruenceRow_modulus_dvd_lcm
    (rows : List (Nat × Nat)) (row : Nat × Nat)
    (hrow : row ∈ rows) :
    row.1 ∣ congruenceLcm rows := by
  induction rows with
  | nil =>
      simp at hrow
  | cons head rest ih =>
      rcases (List.mem_cons.mp hrow) with hsame | htail
      · subst hsame
        simp [congruenceLcm, Nat.dvd_lcm_left]
      · have hrest : row.1 ∣ congruenceLcm rest := ih htail
        exact hrest.trans (Nat.dvd_lcm_right head.1 (congruenceLcm rest))

theorem congruenceLcm_dvd_of_forall_modulus_dvd
    (rows : List (Nat × Nat)) (L : Nat)
    (h : ∀ row ∈ rows, row.1 ∣ L) :
    congruenceLcm rows ∣ L := by
  induction rows with
  | nil =>
      simp [congruenceLcm]
  | cons row rest ih =>
      have hrow : row.1 ∣ L := h row (by simp)
      have hrest : congruenceLcm rest ∣ L := by
        apply ih
        intro tail htail
        exact h tail (by simp [htail])
      simpa [congruenceLcm] using Nat.lcm_dvd hrow hrest

theorem congruenceLcm_satEventResidualHitRowsFinset_toList_eq
    (events : Finset SatEvent) :
    congruenceLcm (satEventResidualHitRowsFinset events).toList =
      congruenceLcm (satEventResidualHitRows events.toList) := by
  apply Nat.dvd_antisymm
  · apply congruenceLcm_dvd_of_forall_modulus_dvd
    intro row hrowList
    have hrowFin : row ∈ satEventResidualHitRowsFinset events := by
      simpa using hrowList
    rcases Finset.mem_image.mp hrowFin with ⟨event, hevent, hrowEq⟩
    subst hrowEq
    exact congruenceRow_modulus_dvd_lcm
      (satEventResidualHitRows events.toList) (satEventResidualHitRow event)
      (List.mem_map.mpr ⟨event, by simpa using hevent, rfl⟩)
  · apply congruenceLcm_dvd_of_forall_modulus_dvd
    intro row hrowList
    rcases List.mem_map.mp hrowList with ⟨event, hevent, hrowEq⟩
    subst hrowEq
    exact congruenceRow_modulus_dvd_lcm
      (satEventResidualHitRowsFinset events).toList (satEventResidualHitRow event)
      (by
        have hrowFin : satEventResidualHitRow event ∈
            satEventResidualHitRowsFinset events :=
          Finset.mem_image.mpr ⟨event, by simpa using hevent, rfl⟩
        simpa using hrowFin)

/-- Adding one saturated event adjoins its residual modulus to the lcm,
independently of the ordering chosen by `Finset.toList`. -/
theorem congruenceLcm_satEventResidualHitRows_insert_eq_lcm
    (old : Finset SatEvent) (event : SatEvent) :
    congruenceLcm (satEventResidualHitRows (insert event old).toList) =
      Nat.lcm (conditionalModulus event.dPlus event.p)
        (congruenceLcm (satEventResidualHitRows old.toList)) := by
  classical
  apply Nat.dvd_antisymm
  · apply congruenceLcm_dvd_of_forall_modulus_dvd
    intro row hrow
    rcases List.mem_map.mp hrow with ⟨other, hother, rfl⟩
    have hotherFin : other ∈ insert event old := by simpa using hother
    rcases Finset.mem_insert.mp hotherFin with heq | hold
    · subst heq
      exact Nat.dvd_lcm_left _ _
    · exact (congruenceRow_modulus_dvd_lcm
        (satEventResidualHitRows old.toList)
        (satEventResidualHitRow other)
        (List.mem_map.mpr ⟨other, by simpa using hold, rfl⟩)).trans
          (Nat.dvd_lcm_right _ _)
  · apply Nat.lcm_dvd
    · exact congruenceRow_modulus_dvd_lcm
        (satEventResidualHitRows (insert event old).toList)
        (satEventResidualHitRow event)
        (List.mem_map.mpr ⟨event, by simp, rfl⟩)
    · apply congruenceLcm_dvd_of_forall_modulus_dvd
      intro row hrow
      rcases List.mem_map.mp hrow with ⟨other, hother, rfl⟩
      exact congruenceRow_modulus_dvd_lcm
        (satEventResidualHitRows (insert event old).toList)
        (satEventResidualHitRow other)
        (List.mem_map.mpr ⟨other, by simp [by simpa using hother], rfl⟩)

/-- A prime divides the lcm of a finite congruence system exactly when it
divides one of its row moduli. -/
theorem prime_dvd_congruenceLcm_iff
    (ell : ℕ) (hell : Nat.Prime ell) (rows : List (ℕ × ℕ)) :
    ell ∣ congruenceLcm rows ↔ ∃ row ∈ rows, ell ∣ row.1 := by
  induction rows with
  | nil =>
      simp [congruenceLcm, hell.not_dvd_one]
  | cons row rows ih =>
      have hlcm : ell ∣ Nat.lcm row.1 (congruenceLcm rows) ↔
          ell ∣ row.1 ∨ ell ∣ congruenceLcm rows := by
        constructor
        · intro h
          have hprod : ell ∣ row.1 * congruenceLcm rows :=
            h.trans (Nat.lcm_dvd_mul row.1 (congruenceLcm rows))
          exact hell.dvd_mul.mp hprod
        · intro h
          rcases h with hleft | hright
          · exact hleft.trans (Nat.dvd_lcm_left row.1 (congruenceLcm rows))
          · exact hright.trans (Nat.dvd_lcm_right row.1 (congruenceLcm rows))
      change ell ∣ Nat.lcm row.1 (congruenceLcm rows) ↔
        ∃ row' ∈ row :: rows, ell ∣ row'.1
      rw [hlcm, ih]
      simp

theorem congruenceRows_unique_mod_lcm
    (rows : List (Nat × Nat)) (x y : Nat)
    (hx : satisfiesCongruenceRows x rows)
    (hy : satisfiesCongruenceRows y rows) :
    x ≡ y [MOD congruenceLcm rows] := by
  induction rows with
  | nil =>
      simpa [congruenceLcm] using (Nat.modEq_one : x ≡ y [MOD 1])
  | cons head rest ih =>
      have hxhead : x ≡ head.2 [MOD head.1] := hx head (by simp)
      have hyhead : y ≡ head.2 [MOD head.1] := hy head (by simp)
      have hhead : x ≡ y [MOD head.1] := hxhead.trans hyhead.symm
      have hxrest : satisfiesCongruenceRows x rest := by
        intro row hrow
        exact hx row (by simp [hrow])
      have hyrest : satisfiesCongruenceRows y rest := by
        intro row hrow
        exact hy row (by simp [hrow])
      have hrest : x ≡ y [MOD congruenceLcm rest] := ih hxrest hyrest
      simpa [congruenceLcm] using Nat.mod_lcm hhead hrest

theorem congruenceRows_of_modEq_lcm
    (rows : List (Nat × Nat)) (x y : Nat)
    (hx : satisfiesCongruenceRows x rows)
    (hxy : y ≡ x [MOD congruenceLcm rows]) :
    satisfiesCongruenceRows y rows := by
  intro row hrow
  have hdiv : row.1 ∣ congruenceLcm rows :=
    congruenceRow_modulus_dvd_lcm rows row hrow
  have hmod : y ≡ x [MOD row.1] := Nat.ModEq.of_dvd hdiv hxy
  exact hmod.trans (hx row hrow)

theorem congruenceRows_solution_iff_modEq_lcm
    (rows : List (Nat × Nat)) (x y : Nat)
    (hx : satisfiesCongruenceRows x rows) :
    satisfiesCongruenceRows y rows ↔
      y ≡ x [MOD congruenceLcm rows] := by
  constructor
  · intro hy
    exact congruenceRows_unique_mod_lcm rows y x hy hx
  · intro hxy
    exact congruenceRows_of_modEq_lcm rows x y hx hxy

theorem congruenceLcm_coprime_of_rows_coprime
    (P : Nat) (rows : List (Nat × Nat))
    (hP : 0 < P)
    (hpos : congruenceRowsModuliPositive rows)
    (hcopRows : ∀ row ∈ rows, Nat.Coprime P row.1) :
    Nat.Coprime P (congruenceLcm rows) := by
  induction rows with
  | nil =>
      simp [congruenceLcm, Nat.coprime_one_right]
  | cons head rest ih =>
      have hheadpos : 0 < head.1 := hpos head (by simp)
      have hrestpos : congruenceRowsModuliPositive rest := by
        intro row hrow
        exact hpos row (by simp [hrow])
      have hLrest : 0 < congruenceLcm rest :=
        congruenceLcm_pos_of_rows_positive rest hrestpos
      have hheadgcd : Nat.gcd P head.1 = 1 :=
        Nat.coprime_iff_gcd_eq_one.mp (hcopRows head (by simp))
      have hrestgcd : Nat.gcd P (congruenceLcm rest) = 1 := by
        exact Nat.coprime_iff_gcd_eq_one.mp
          (ih hrestpos (by
            intro row hrow
            exact hcopRows row (by simp [hrow])))
      have hdist := gcd_lcm_distrib_left_of_pos
        P head.1 (congruenceLcm rest) hP hheadpos hLrest
      apply Nat.coprime_iff_gcd_eq_one.mpr
      change Nat.gcd P (Nat.lcm head.1 (congruenceLcm rest)) = 1
      rw [hdist, hheadgcd, hrestgcd]
      simp

theorem congruenceRows_solution_exists_of_pairwiseCompatible
    (rows : List (Nat × Nat))
    (hpos : congruenceRowsModuliPositive rows)
    (hcompat : congruenceRowsPairwiseCompatible rows) :
    ∃ x, satisfiesCongruenceRows x rows := by
  induction rows with
  | nil =>
      exact ⟨0, by simp [satisfiesCongruenceRows]⟩
  | cons head rest ih =>
      have hheadpos : 0 < head.1 := hpos head (by simp)
      have hrestpos : congruenceRowsModuliPositive rest := by
        intro row hrow
        exact hpos row (by simp [hrow])
      have hrestcompat : congruenceRowsPairwiseCompatible rest := by
        intro rowA hA rowB hB
        exact hcompat rowA (by simp [hA]) rowB (by simp [hB])
      rcases ih hrestpos hrestcompat with ⟨y, hy⟩
      have hheadTail : residueCompatible head.1 (congruenceLcm rest) head.2 y :=
        congruenceRow_compatible_with_solution_lcm head rest y hheadpos hrestpos
          (by
            intro tail htail
            exact hcompat head (by simp) tail (by simp [htail]))
          hy
      let kSubtype := Nat.chineseRemainder' hheadTail
      let k : Nat := kSubtype
      have hkhead : k ≡ head.2 [MOD head.1] := kSubtype.property.1
      have hktail : k ≡ y [MOD congruenceLcm rest] := kSubtype.property.2
      refine ⟨k, ?_⟩
      intro row hrow
      rcases (List.mem_cons.mp hrow) with hsame | htail
      · subst hsame
        exact hkhead
      · have hksatRest : satisfiesCongruenceRows k rest :=
          congruenceRows_of_modEq_lcm rest y k hy hktail
        exact hksatRest row htail

theorem congruenceRowsPairwiseCompatible_iff_exists_solution
    (rows : List (Nat × Nat))
    (hpos : congruenceRowsModuliPositive rows) :
    congruenceRowsPairwiseCompatible rows ↔
      ∃ x, satisfiesCongruenceRows x rows := by
  constructor
  · exact congruenceRows_solution_exists_of_pairwiseCompatible rows hpos
  · rintro ⟨x, hx⟩
    exact congruenceRowsPairwiseCompatible_of_solution rows x hx

theorem baseResidualRows_solution_exists_of_pairwiseCompatible
    (Pz b : Nat) (rows : List (Nat × Nat))
    (hPz : 0 < Pz)
    (hpos : congruenceRowsModuliPositive rows)
    (hcompat : congruenceRowsPairwiseCompatible ((Pz, b) :: rows)) :
    ∃ x, x ≡ b [MOD Pz] ∧ satisfiesCongruenceRows x rows := by
  have hposAll : congruenceRowsModuliPositive ((Pz, b) :: rows) := by
    intro row hrow
    rcases (List.mem_cons.mp hrow) with hsame | htail
    · subst hsame
      exact hPz
    · exact hpos row htail
  rcases congruenceRows_solution_exists_of_pairwiseCompatible
      ((Pz, b) :: rows) hposAll hcompat with ⟨x, hx⟩
  exact ⟨x, hx (Pz, b) (by simp), by
    intro row hrow
    exact hx row (by simp [hrow])⟩

theorem baseResidualRows_pairwiseCompatible_iff_exists_solution
    (Pz b : Nat) (rows : List (Nat × Nat))
    (hPz : 0 < Pz)
    (hpos : congruenceRowsModuliPositive rows) :
    congruenceRowsPairwiseCompatible ((Pz, b) :: rows) ↔
      ∃ x, x ≡ b [MOD Pz] ∧ satisfiesCongruenceRows x rows := by
  constructor
  · exact baseResidualRows_solution_exists_of_pairwiseCompatible Pz b rows hPz hpos
  · rintro ⟨x, hxbase, hxrows⟩
    exact congruenceRowsPairwiseCompatible_of_solution ((Pz, b) :: rows) x (by
      intro row hrow
      rcases (List.mem_cons.mp hrow) with hsame | htail
      · subst hsame
        exact hxbase
      · exact hxrows row htail)

theorem satEventResidualHitRows_satisfied_by_common_hit
    (Pz rho n : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hhit : ∀ event ∈ events, satEventHit n event) :
    satisfiesCongruenceRows n (satEventResidualHitRows events) :=
  (satisfiesCongruenceRows_satEventResidualHitRows_iff_hits
    Pz rho n events hadm).2 hhit

theorem satEventResidualHitRows_satisfied_by_common_hit_admissibleFor
    (Pz : Nat) (rhoOf : Nat → Nat) (n : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hhit : ∀ event ∈ events, satEventHit n event) :
    satisfiesCongruenceRows n (satEventResidualHitRows events) :=
  (satisfiesCongruenceRows_satEventResidualHitRows_iff_hits_admissibleFor
    Pz rhoOf n events hadm).2 hhit

theorem satEventResidualHitRows_solution_witness_of_common_hit
    (Pz rho n : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hhit : ∀ event ∈ events, satEventHit n event) :
    ∃ x, satisfiesCongruenceRows x (satEventResidualHitRows events) := by
  exact ⟨n, satEventResidualHitRows_satisfied_by_common_hit
    Pz rho n events hadm hhit⟩

theorem satEventResidualHitRows_solution_witness_of_common_hit_admissibleFor
    (Pz : Nat) (rhoOf : Nat → Nat) (n : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hhit : ∀ event ∈ events, satEventHit n event) :
    ∃ x, satisfiesCongruenceRows x (satEventResidualHitRows events) := by
  exact ⟨n, satEventResidualHitRows_satisfied_by_common_hit_admissibleFor
    Pz rhoOf n events hadm hhit⟩

theorem satEventResidualHitRows_compatible_and_positive_of_common_hit
    (Pz rho n : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hhit : ∀ event ∈ events, satEventHit n event) :
    congruenceRowsPairwiseCompatible (satEventResidualHitRows events) ∧
      congruenceRowsModuliPositive (satEventResidualHitRows events) :=
  ⟨satEventResidualHitRows_pairwiseCompatible_of_common_hit
      Pz rho n events hadm hhit,
    satEventResidualHitRows_moduliPositive_of_admissible Pz rho events hadm⟩

theorem satEventResidualHitRows_crt_solution_exists_of_common_hit
    (Pz rho n : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hhit : ∀ event ∈ events, satEventHit n event) :
    ∃ x, satisfiesCongruenceRows x (satEventResidualHitRows events) := by
  exact satEventResidualHitRows_solution_witness_of_common_hit
    Pz rho n events hadm hhit

theorem satEventResidualHitRows_common_hits_modEq_lcm
    (Pz rho n m : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hhitN : ∀ event ∈ events, satEventHit n event)
    (hhitM : ∀ event ∈ events, satEventHit m event) :
    n ≡ m [MOD congruenceLcm (satEventResidualHitRows events)] := by
  exact congruenceRows_unique_mod_lcm (satEventResidualHitRows events) n m
    (satEventResidualHitRows_satisfied_by_common_hit
      Pz rho n events hadm hhitN)
    (satEventResidualHitRows_satisfied_by_common_hit
      Pz rho m events hadm hhitM)

theorem satEventResidualHitRows_crt_solution_lt_lcm_of_common_hit
    (Pz rho n : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hhit : ∀ event ∈ events, satEventHit n event) :
    ∃ x, x < congruenceLcm (satEventResidualHitRows events) ∧
      satisfiesCongruenceRows x (satEventResidualHitRows events) := by
  have hpos :=
    satEventResidualHitRows_moduliPositive_of_admissible Pz rho events hadm
  have hcompat :=
    satEventResidualHitRows_pairwiseCompatible_of_common_hit
      Pz rho n events hadm hhit
  have hLpos : 0 < congruenceLcm (satEventResidualHitRows events) :=
    congruenceLcm_pos_of_rows_positive (satEventResidualHitRows events) hpos
  rcases congruenceRows_solution_exists_of_pairwiseCompatible
      (satEventResidualHitRows events) hpos hcompat with ⟨y, hy⟩
  refine ⟨y % congruenceLcm (satEventResidualHitRows events),
    Nat.mod_lt y hLpos, ?_⟩
  apply congruenceRows_of_modEq_lcm (satEventResidualHitRows events) y
  · exact hy
  · exact Nat.mod_modEq y (congruenceLcm (satEventResidualHitRows events))

theorem satEventResidualHitRows_mod_lcm_solution_lt_of_common_hit
    (Pz rho n : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hhit : ∀ event ∈ events, satEventHit n event) :
    ∃ x, x < congruenceLcm (satEventResidualHitRows events) ∧
      satisfiesCongruenceRows x (satEventResidualHitRows events) ∧
      x ≡ n [MOD congruenceLcm (satEventResidualHitRows events)] := by
  have hpos :=
    satEventResidualHitRows_moduliPositive_of_admissible Pz rho events hadm
  have hLpos : 0 < congruenceLcm (satEventResidualHitRows events) :=
    congruenceLcm_pos_of_rows_positive (satEventResidualHitRows events) hpos
  have hn :=
    satEventResidualHitRows_satisfied_by_common_hit Pz rho n events hadm hhit
  refine ⟨n % congruenceLcm (satEventResidualHitRows events),
    Nat.mod_lt n hLpos, ?_, ?_⟩
  · exact congruenceRows_of_modEq_lcm (satEventResidualHitRows events) n
      (n % congruenceLcm (satEventResidualHitRows events)) hn
      (Nat.mod_modEq n (congruenceLcm (satEventResidualHitRows events)))
  · exact Nat.mod_modEq n (congruenceLcm (satEventResidualHitRows events))

theorem satEventResidualHitRows_mod_lcm_solution_lt_of_common_hit_admissibleFor
    (Pz : Nat) (rhoOf : Nat → Nat) (n : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hhit : ∀ event ∈ events, satEventHit n event) :
    ∃ x, x < congruenceLcm (satEventResidualHitRows events) ∧
      satisfiesCongruenceRows x (satEventResidualHitRows events) ∧
      x ≡ n [MOD congruenceLcm (satEventResidualHitRows events)] := by
  have hpos :=
    satEventResidualHitRows_moduliPositive_of_admissibleFor Pz rhoOf events hadm
  have hLpos : 0 < congruenceLcm (satEventResidualHitRows events) :=
    congruenceLcm_pos_of_rows_positive (satEventResidualHitRows events) hpos
  have hn :=
    satEventResidualHitRows_satisfied_by_common_hit_admissibleFor
      Pz rhoOf n events hadm hhit
  refine ⟨n % congruenceLcm (satEventResidualHitRows events),
    Nat.mod_lt n hLpos, ?_, ?_⟩
  · exact congruenceRows_of_modEq_lcm (satEventResidualHitRows events) n
      (n % congruenceLcm (satEventResidualHitRows events)) hn
      (Nat.mod_modEq n (congruenceLcm (satEventResidualHitRows events)))
  · exact Nat.mod_modEq n (congruenceLcm (satEventResidualHitRows events))

theorem baseResidualHitRows_pairwiseCompatible_of_common_hit
    (Pz rho b n : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hbase : n ≡ b [MOD Pz])
    (hhit : ∀ event ∈ events, satEventHit n event) :
    congruenceRowsPairwiseCompatible
      ((Pz, b) :: satEventResidualHitRows events) := by
  apply congruenceRowsPairwiseCompatible_of_solution
    ((Pz, b) :: satEventResidualHitRows events) n
  intro row hrow
  rcases List.mem_cons.mp hrow with hsame | htail
  · subst hsame
    exact hbase
  · exact satEventResidualHitRows_satisfied_by_common_hit
      Pz rho n events hadm hhit row htail

theorem baseResidualHitRows_crt_solution_of_common_hit
    (Pz rho b n : Nat) (events : List SatEvent)
    (hPz : 0 < Pz)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hbase : n ≡ b [MOD Pz])
    (hhit : ∀ event ∈ events, satEventHit n event) :
    ∃ x, x ≡ b [MOD Pz] ∧
      satisfiesCongruenceRows x (satEventResidualHitRows events) := by
  have hpos :=
    satEventResidualHitRows_moduliPositive_of_admissible Pz rho events hadm
  have hcompat :=
    baseResidualHitRows_pairwiseCompatible_of_common_hit
      Pz rho b n events hadm hbase hhit
  exact baseResidualRows_solution_exists_of_pairwiseCompatible
    Pz b (satEventResidualHitRows events) hPz hpos hcompat

theorem baseResidualHitRows_solution_witness_of_common_hit
    (Pz rho b n : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hbase : n ≡ b [MOD Pz])
    (hhit : ∀ event ∈ events, satEventHit n event) :
    ∃ x, x ≡ b [MOD Pz] ∧
      satisfiesCongruenceRows x (satEventResidualHitRows events) := by
  exact ⟨n, hbase,
    satEventResidualHitRows_satisfied_by_common_hit
      Pz rho n events hadm hhit⟩

theorem baseResidualHitRows_solution_witness_of_common_hit_admissibleFor
    (Pz b n : Nat) (rhoOf : Nat → Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hbase : n ≡ b [MOD Pz])
    (hhit : ∀ event ∈ events, satEventHit n event) :
    ∃ x, x ≡ b [MOD Pz] ∧
      satisfiesCongruenceRows x (satEventResidualHitRows events) := by
  exact ⟨n, hbase,
    satEventResidualHitRows_satisfied_by_common_hit_admissibleFor
      Pz rhoOf n events hadm hhit⟩

theorem congruenceRowsPairwiseCompatible_append_of_common_solution
    (rows1 rows2 : List (Nat × Nat)) (n : Nat)
    (hn1 : satisfiesCongruenceRows n rows1)
    (hn2 : satisfiesCongruenceRows n rows2) :
    congruenceRowsPairwiseCompatible (rows1 ++ rows2) := by
  apply congruenceRowsPairwiseCompatible_of_solution (rows1 ++ rows2) n
  intro row hrow
  rcases List.mem_append.mp hrow with h1 | h2
  · exact hn1 row h1
  · exact hn2 row h2

theorem congruenceRows_append_solution_exists_of_common_solution
    (rows1 rows2 : List (Nat × Nat)) (n : Nat)
    (hn1 : satisfiesCongruenceRows n rows1)
    (hn2 : satisfiesCongruenceRows n rows2) :
    ∃ x, satisfiesCongruenceRows x (rows1 ++ rows2) := by
  refine ⟨n, ?_⟩
  intro row hrow
  rcases List.mem_append.mp hrow with h1 | h2
  · exact hn1 row h1
  · exact hn2 row h2

theorem congruenceRows_solution_exists_append_of_common_solution
    (rows1 rows2 : List (Nat × Nat)) (n : Nat)
    (hpos : congruenceRowsModuliPositive (rows1 ++ rows2))
    (hn1 : satisfiesCongruenceRows n rows1)
    (hn2 : satisfiesCongruenceRows n rows2) :
    ∃ x, satisfiesCongruenceRows x (rows1 ++ rows2) :=
  congruenceRows_solution_exists_of_pairwiseCompatible (rows1 ++ rows2) hpos
    (congruenceRowsPairwiseCompatible_append_of_common_solution
      rows1 rows2 n hn1 hn2)

theorem congruenceLcm_residualHitRows_coprime_base_of_admissible
    (Pz rho : Nat) (events : List SatEvent)
    (hPz : 0 < Pz)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hpCop : ∀ event ∈ events, Nat.Coprime Pz event.p) :
    Nat.Coprime Pz (congruenceLcm (satEventResidualHitRows events)) := by
  apply congruenceLcm_coprime_of_rows_coprime Pz
    (satEventResidualHitRows events) hPz
  · exact satEventResidualHitRows_moduliPositive_of_admissible
      Pz rho events hadm
  · intro row hrow
    rcases List.mem_map.mp hrow with ⟨event, hevent, hrowEq⟩
    subst hrowEq
    rcases hadm event hevent with
      ⟨_hpPrime, _heLt, _hmedium, _hprog,
        _hdMinusPos, _hdPlusPos, _hdMinusDvd, hdPlusCop⟩
    have hdPlusCopBase : Nat.Coprime Pz event.dPlus := hdPlusCop.symm
    have hrowCop : Nat.Coprime Pz (event.dPlus * event.p) :=
      hdPlusCopBase.mul_right (hpCop event hevent)
    simpa [satEventResidualHitRow, conditionalModulus] using hrowCop

theorem product_dvd_of_coprime_dvd_same
    (a b N : Nat)
    (hcop : Nat.Coprime a b)
    (ha : a ∣ N) (hb : b ∣ N) :
    a * b ∣ N := by
  rw [← hcop.lcm_eq_mul]
  exact Nat.lcm_dvd ha hb

theorem fullCongruence_of_base_and_residual
    (m n e dMinus q : Nat)
    (hcop : Nat.Coprime dMinus q)
    (hbase : dMinus ∣ n + m * e)
    (hresidual : q ∣ n + m * e) :
    dMinus * q ∣ n + m * e :=
  product_dvd_of_coprime_dvd_same dMinus q (n + m * e) hcop hbase hresidual

theorem fullCongruence_of_base_and_residual_modEq
    (m n e dMinus q : Nat)
    (hcop : Nat.Coprime dMinus q)
    (hbase : n + m * e ≡ 0 [MOD dMinus])
    (hresidual : n + m * e ≡ 0 [MOD q]) :
    n + m * e ≡ 0 [MOD dMinus * q] := by
  exact (Nat.modEq_zero_iff_dvd).2
    (fullCongruence_of_base_and_residual m n e dMinus q hcop
      ((Nat.modEq_zero_iff_dvd).1 hbase)
      ((Nat.modEq_zero_iff_dvd).1 hresidual))

theorem conditionedBaseCongruence_modEq
    (m n e Pz b dMinus : Nat)
    (hdMinusDvdPz : dMinus ∣ Pz)
    (hnbase : n ≡ b [MOD Pz])
    (hsmall : b + m * e ≡ 0 [MOD dMinus]) :
    n + m * e ≡ 0 [MOD dMinus] := by
  have hnbaseD : n ≡ b [MOD dMinus] :=
    Nat.ModEq.of_dvd hdMinusDvdPz hnbase
  exact (Nat.ModEq.add_right (m * e) hnbaseD).trans hsmall

theorem conditionedBaseCongruence_dvd
    (m n e Pz b dMinus : Nat)
    (hdMinusDvdPz : dMinus ∣ Pz)
    (hnbase : n ≡ b [MOD Pz])
    (hsmall : b + m * e ≡ 0 [MOD dMinus]) :
    dMinus ∣ n + m * e :=
  (Nat.modEq_zero_iff_dvd).1
    (conditionedBaseCongruence_modEq
      m n e Pz b dMinus hdMinusDvdPz hnbase hsmall)

theorem mediumProduct_eq_of_coprime_progression
    (d d' p rho : Nat)
    (hd : d < 4 * rho) (hd' : d' < 4 * rho)
    (hcop : Nat.gcd (4 * rho) p = 1)
    (hprog : d * p + 1 ≡ 0 [MOD 4 * rho])
    (hprog' : d' * p + 1 ≡ 0 [MOD 4 * rho]) :
    d = d' := by
  have hmulPlus : d * p + 1 ≡ d' * p + 1 [MOD 4 * rho] := by
    exact hprog.trans hprog'.symm
  have hmul : d * p ≡ d' * p [MOD 4 * rho] := by
    exact Nat.ModEq.add_right_cancel' (c := 1) hmulPlus
  have hmediumMod : d ≡ d' [MOD 4 * rho] := by
    exact Nat.ModEq.cancel_right_of_coprime hcop hmul
  exact hmediumMod.eq_of_lt_of_lt hd hd'

theorem mediumProduct_eq_of_coprime_progression_of_rho_bound
    (d d' p rho : Nat)
    (hd : d < rho) (hd' : d' < rho)
    (hcop : Nat.gcd (4 * rho) p = 1)
    (hprog : d * p + 1 ≡ 0 [MOD 4 * rho])
    (hprog' : d' * p + 1 ≡ 0 [MOD 4 * rho]) :
    d = d' := by
  have hd4 : d < 4 * rho := by omega
  have hd4' : d' < 4 * rho := by omega
  exact mediumProduct_eq_of_coprime_progression d d' p rho
    hd4 hd4' hcop hprog hprog'

theorem largePrimeUniqueness_medium_core
    (e f d d' p rho : Nat)
    (he : e < p) (hf : f < p)
    (hcompatAtP : e ≡ f [MOD p])
    (hd : d < 4 * rho) (hd' : d' < 4 * rho)
    (hcop : Nat.gcd (4 * rho) p = 1)
    (hprog : d * p + 1 ≡ 0 [MOD 4 * rho])
    (hprog' : d' * p + 1 ≡ 0 [MOD 4 * rho]) :
    e = f ∧ d = d' := by
  have hef : e = f := hcompatAtP.eq_of_lt_of_lt he hf
  have hdd : d = d' :=
    mediumProduct_eq_of_coprime_progression d d' p rho hd hd' hcop hprog hprog'
  exact ⟨hef, hdd⟩

theorem largePrimeUniqueness_of_rho_bound
    (e f d d' p rho : Nat)
    (he : e < p) (hf : f < p)
    (hcompatAtP : e ≡ f [MOD p])
    (hd : d < rho) (hd' : d' < rho)
    (hcop : Nat.gcd (4 * rho) p = 1)
    (hprog : d * p + 1 ≡ 0 [MOD 4 * rho])
    (hprog' : d' * p + 1 ≡ 0 [MOD 4 * rho]) :
    e = f ∧ d = d' := by
  have hprod : d = d' :=
    mediumProduct_eq_of_coprime_progression_of_rho_bound d d' p rho
      hd hd' hcop hprog hprog'
  exact ⟨hcompatAtP.eq_of_lt_of_lt he hf, hprod⟩

theorem smallRough_split_unique
    (Pz dMinus dPlus dMinus' dPlus' : Nat)
    (hdMinusPos : 0 < dMinus)
    (hprod : dMinus * dPlus = dMinus' * dPlus')
    (hdMinusDvd : dMinus ∣ Pz) (hdMinus'Dvd : dMinus' ∣ Pz)
    (hdPlusCop : Nat.Coprime dPlus Pz)
    (hdPlus'Cop : Nat.Coprime dPlus' Pz) :
    dMinus = dMinus' ∧ dPlus = dPlus' := by
  have hdMinus_cop_dPlus' : Nat.Coprime dMinus dPlus' := by
    exact hdPlus'Cop.symm.coprime_dvd_left hdMinusDvd
  have hdMinus_dvd_prod : dMinus ∣ dPlus' * dMinus' := by
    rw [mul_comm dPlus' dMinus', ← hprod]
    exact dvd_mul_right dMinus dPlus
  have hdMinus_dvd_dMinus' : dMinus ∣ dMinus' := by
    exact (hdMinus_cop_dPlus'.dvd_mul_left).1 hdMinus_dvd_prod
  have hdMinus'_cop_dPlus : Nat.Coprime dMinus' dPlus := by
    exact hdPlusCop.symm.coprime_dvd_left hdMinus'Dvd
  have hdMinus'_dvd_prod : dMinus' ∣ dPlus * dMinus := by
    rw [mul_comm dPlus dMinus, hprod]
    exact dvd_mul_right dMinus' dPlus'
  have hdMinus'_dvd_dMinus : dMinus' ∣ dMinus := by
    exact (hdMinus'_cop_dPlus.dvd_mul_left).1 hdMinus'_dvd_prod
  have hdMinusEq : dMinus = dMinus' :=
    Nat.dvd_antisymm hdMinus_dvd_dMinus' hdMinus'_dvd_dMinus
  have hdPlusEq : dPlus = dPlus' := by
    have hprod' : dMinus * dPlus = dMinus * dPlus' := by
      simpa [hdMinusEq] using hprod
    exact Nat.eq_of_mul_eq_mul_left hdMinusPos hprod'
  exact ⟨hdMinusEq, hdPlusEq⟩

theorem largePrimeUniqueness_with_split
    (e f dMinus dPlus dMinus' dPlus' p rho Pz : Nat)
    (he : e < p) (hf : f < p)
    (hcompatAtP : e ≡ f [MOD p])
    (hmedium : dMinus * dPlus < rho)
    (hmedium' : dMinus' * dPlus' < rho)
    (hcop : Nat.gcd (4 * rho) p = 1)
    (hprog : (dMinus * dPlus) * p + 1 ≡ 0 [MOD 4 * rho])
    (hprog' : (dMinus' * dPlus') * p + 1 ≡ 0 [MOD 4 * rho])
    (hdMinusPos : 0 < dMinus)
    (hdMinusDvd : dMinus ∣ Pz) (hdMinus'Dvd : dMinus' ∣ Pz)
    (hdPlusCop : Nat.Coprime dPlus Pz)
    (hdPlus'Cop : Nat.Coprime dPlus' Pz) :
    e = f ∧ dMinus = dMinus' ∧ dPlus = dPlus' := by
  rcases largePrimeUniqueness_of_rho_bound
      e f (dMinus * dPlus) (dMinus' * dPlus') p rho
      he hf hcompatAtP hmedium hmedium' hcop hprog hprog' with
    ⟨hef, hprod⟩
  rcases smallRough_split_unique Pz dMinus dPlus dMinus' dPlus'
      hdMinusPos hprod hdMinusDvd hdMinus'Dvd hdPlusCop hdPlus'Cop with
    ⟨hdMinusEq, hdPlusEq⟩
  exact ⟨hef, hdMinusEq, hdPlusEq⟩

theorem satEvent_eq_of_compatible_same_largePrime
    (Pz rho : Nat) (event other : SatEvent)
    (hcompat : satEventCompatible event other)
    (hsamePrime : event.p = other.p)
    (he : event.e < event.p) (hotherE : other.e < other.p)
    (hmedium : event.dMinus * event.dPlus < rho)
    (hmediumOther : other.dMinus * other.dPlus < rho)
    (hcop : Nat.gcd (4 * rho) event.p = 1)
    (hprog :
      (event.dMinus * event.dPlus) * event.p + 1 ≡ 0 [MOD 4 * rho])
    (hprogOther :
      (other.dMinus * other.dPlus) * other.p + 1 ≡ 0 [MOD 4 * rho])
    (hdMinusPos : 0 < event.dMinus)
    (hdMinusDvd : event.dMinus ∣ Pz) (hdMinusOtherDvd : other.dMinus ∣ Pz)
    (hdPlusCop : Nat.Coprime event.dPlus Pz)
    (hdPlusOtherCop : Nat.Coprime other.dPlus Pz) :
    event = other := by
  have hcopFour : Nat.gcd event.p 4 = 1 := by
    have hgcdDvd :
        Nat.gcd event.p 4 ∣ Nat.gcd (4 * rho) event.p :=
      Nat.dvd_gcd
        ((Nat.gcd_dvd_right event.p 4).trans (Nat.dvd_mul_right 4 rho))
        (Nat.gcd_dvd_left event.p 4)
    exact Nat.dvd_one.mp (by simpa [hcop] using hgcdDvd)
  have hcompatAtP : event.e ≡ other.e [MOD event.p] :=
    satEvent_modEq_of_compatible_same_largePrime event other hcompat hsamePrime hcopFour
  have hotherEAtEventP : other.e < event.p := by
    simpa [hsamePrime] using hotherE
  have hprogOther' :
      (other.dMinus * other.dPlus) * event.p + 1 ≡ 0 [MOD 4 * rho] := by
    simpa [hsamePrime] using hprogOther
  rcases largePrimeUniqueness_with_split
      event.e other.e event.dMinus event.dPlus other.dMinus other.dPlus
      event.p rho Pz he hotherEAtEventP hcompatAtP hmedium hmediumOther hcop hprog
      hprogOther' hdMinusPos hdMinusDvd hdMinusOtherDvd hdPlusCop
      hdPlusOtherCop with
    ⟨heq, hdMinusEq, hdPlusEq⟩
  rcases event with ⟨e, dMinus, dPlus, p⟩
  rcases other with ⟨f, dMinus', dPlus', p'⟩
  simp only at heq hdMinusEq hdPlusEq hsamePrime ⊢
  subst f
  subst dMinus'
  subst dPlus'
  subst p'
  rfl

theorem satEvent_largePrime_ne_of_compatible_ne
    (Pz rho : Nat) (event other : SatEvent)
    (hcompat : satEventCompatible event other)
    (hne : event ≠ other)
    (he : event.e < event.p) (hotherE : other.e < other.p)
    (hmedium : event.dMinus * event.dPlus < rho)
    (hmediumOther : other.dMinus * other.dPlus < rho)
    (hcop : Nat.gcd (4 * rho) event.p = 1)
    (hprog :
      (event.dMinus * event.dPlus) * event.p + 1 ≡ 0 [MOD 4 * rho])
    (hprogOther :
      (other.dMinus * other.dPlus) * other.p + 1 ≡ 0 [MOD 4 * rho])
    (hdMinusPos : 0 < event.dMinus)
    (hdMinusDvd : event.dMinus ∣ Pz) (hdMinusOtherDvd : other.dMinus ∣ Pz)
    (hdPlusCop : Nat.Coprime event.dPlus Pz)
    (hdPlusOtherCop : Nat.Coprime other.dPlus Pz) :
    event.p ≠ other.p := by
  intro hsamePrime
  exact hne (satEvent_eq_of_compatible_same_largePrime
    Pz rho event other hcompat hsamePrime he hotherE hmedium hmediumOther hcop
    hprog hprogOther hdMinusPos hdMinusDvd hdMinusOtherDvd hdPlusCop
    hdPlusOtherCop)

theorem satEvent_largePrime_ne_of_common_hit_ne
    (Pz rho n : Nat) (event other : SatEvent)
    (heventHit : satEventHit n event)
    (hotherHit : satEventHit n other)
    (hne : event ≠ other)
    (he : event.e < event.p) (hotherE : other.e < other.p)
    (hmedium : event.dMinus * event.dPlus < rho)
    (hmediumOther : other.dMinus * other.dPlus < rho)
    (hcop : Nat.gcd (4 * rho) event.p = 1)
    (hprog :
      (event.dMinus * event.dPlus) * event.p + 1 ≡ 0 [MOD 4 * rho])
    (hprogOther :
      (other.dMinus * other.dPlus) * other.p + 1 ≡ 0 [MOD 4 * rho])
    (hdMinusPos : 0 < event.dMinus)
    (hdMinusDvd : event.dMinus ∣ Pz) (hdMinusOtherDvd : other.dMinus ∣ Pz)
    (hdPlusCop : Nat.Coprime event.dPlus Pz)
    (hdPlusOtherCop : Nat.Coprime other.dPlus Pz) :
    event.p ≠ other.p := by
  exact satEvent_largePrime_ne_of_compatible_ne Pz rho event other
    (satEventCompatible_of_common_hit n event other heventHit hotherHit) hne
    he hotherE hmedium hmediumOther hcop hprog hprogOther hdMinusPos
    hdMinusDvd hdMinusOtherDvd hdPlusCop hdPlusOtherCop

theorem appendageCommonDivisor_dvd_medium
    (dPlus p L : Nat)
    (hcop : Nat.Coprime p L) :
    appendageG dPlus p L ∣ dPlus := by
  let g := appendageG dPlus p L
  have hgDvdQ : g ∣ conditionalModulus dPlus p :=
    Nat.gcd_dvd_left (conditionalModulus dPlus p) L
  have hgDvdL : g ∣ L :=
    Nat.gcd_dvd_right (conditionalModulus dPlus p) L
  have hgCopP : Nat.Coprime g p := by
    exact hcop.symm.coprime_dvd_left hgDvdL
  exact (hgCopP.dvd_mul_right).1 (by
    simpa [conditionalModulus] using hgDvdQ)

theorem prime_coprime_lcm
    (p a b : Nat) (hp : Nat.Prime p)
    (hpa : Nat.Coprime p a) (hpb : Nat.Coprime p b) :
    Nat.Coprime p (Nat.lcm a b) := by
  rw [hp.coprime_iff_not_dvd] at hpa hpb ⊢
  intro hdiv
  have hmul : p ∣ a * b := hdiv.trans (Nat.lcm_dvd_mul a b)
  rcases (hp.dvd_mul).1 hmul with hpa' | hpb'
  · exact hpa hpa'
  · exact hpb hpb'

theorem prime_coprime_of_lt
    (p n : Nat) (hp : Nat.Prime p) (hnPos : 0 < n) (hnLt : n < p) :
    Nat.Coprime p n := by
  exact hp.coprime_iff_not_dvd.2 (by
    intro hdiv
    have hpLeN : p ≤ n := Nat.le_of_dvd hnPos hdiv
    omega)

theorem satEvent_base_coprime_of_admissibleFor_largePrime
    (Pz : Nat) (rhoOf : Nat → Nat) (event : SatEvent)
    (hPz : 0 < Pz)
    (hadm : satEventAdmissibleFor Pz rhoOf event)
    (hlarge : Pz < event.p) :
    Nat.Coprime Pz event.p := by
  exact (prime_coprime_of_lt event.p Pz hadm.1 hPz hlarge).symm

theorem prime_gcd_four_mul_eq_one_of_gt
    (p rho : Nat)
    (hp : Nat.Prime p)
    (hrhoPos : 0 < rho)
    (hgt : 4 * rho < p) :
    Nat.gcd (4 * rho) p = 1 := by
  have hfourRhoPos : 0 < 4 * rho := by
    exact Nat.mul_pos (by norm_num) hrhoPos
  have hnotDvd : ¬ p ∣ 4 * rho := by
    intro hdiv
    have hp_le : p ≤ 4 * rho := Nat.le_of_dvd hfourRhoPos hdiv
    omega
  have hcop : Nat.Coprime p (4 * rho) :=
    hp.coprime_iff_not_dvd.mpr hnotDvd
  exact Nat.coprime_iff_gcd_eq_one.mp hcop.symm

theorem rho_le_of_four_mul_lt
    (rho p : Nat)
    (hgt : 4 * rho < p) :
    rho ≤ p := by
  have hrho_le_four : rho ≤ 4 * rho := by
    have hmul := Nat.mul_le_mul_right rho (by norm_num : 1 ≤ 4)
    simpa using hmul
  exact le_trans hrho_le_four (le_of_lt hgt)

theorem satEventDPlus_lt_of_medium_of_le_largePrime
    (rho p : Nat) (event : SatEvent)
    (hdMinusPos : 0 < event.dMinus)
    (hmedium : event.dMinus * event.dPlus < rho)
    (hrho_le_p : rho ≤ p) :
    event.dPlus < p := by
  have hdMinusOne : 1 ≤ event.dMinus := by omega
  have hdPlus_le_product : event.dPlus ≤ event.dMinus * event.dPlus := by
    have hmul := Nat.mul_le_mul_right event.dPlus hdMinusOne
    simpa using hmul
  have hdPlus_lt_rho : event.dPlus < rho :=
    lt_of_le_of_lt hdPlus_le_product hmedium
  exact lt_of_lt_of_le hdPlus_lt_rho hrho_le_p

theorem satEvent_largePrime_ne_of_common_hit_ne_of_gt
    (Pz rho n : Nat) (event other : SatEvent)
    (hp : Nat.Prime event.p)
    (hrhoPos : 0 < rho)
    (hlarge : 4 * rho < event.p)
    (heventHit : satEventHit n event)
    (hotherHit : satEventHit n other)
    (hne : event ≠ other)
    (he : event.e < event.p) (hotherE : other.e < other.p)
    (hmedium : event.dMinus * event.dPlus < rho)
    (hmediumOther : other.dMinus * other.dPlus < rho)
    (hprog :
      (event.dMinus * event.dPlus) * event.p + 1 ≡ 0 [MOD 4 * rho])
    (hprogOther :
      (other.dMinus * other.dPlus) * other.p + 1 ≡ 0 [MOD 4 * rho])
    (hdMinusPos : 0 < event.dMinus)
    (hdMinusDvd : event.dMinus ∣ Pz) (hdMinusOtherDvd : other.dMinus ∣ Pz)
    (hdPlusCop : Nat.Coprime event.dPlus Pz)
    (hdPlusOtherCop : Nat.Coprime other.dPlus Pz) :
    event.p ≠ other.p := by
  have hcop : Nat.gcd (4 * rho) event.p = 1 :=
    prime_gcd_four_mul_eq_one_of_gt event.p rho hp hrhoPos hlarge
  exact satEvent_largePrime_ne_of_common_hit_ne Pz rho n event other
    heventHit hotherHit hne he hotherE hmedium hmediumOther hcop hprog hprogOther
    hdMinusPos hdMinusDvd hdMinusOtherDvd hdPlusCop hdPlusOtherCop

theorem satEvent_eq_of_compatible_same_largePrime_admissible
    (Pz rho : Nat) (event other : SatEvent)
    (hcompat : satEventCompatible event other)
    (hsamePrime : event.p = other.p)
    (hcop : Nat.gcd (4 * rho) event.p = 1)
    (heventAdm : satEventAdmissible Pz rho event)
    (hotherAdm : satEventAdmissible Pz rho other) :
    event = other := by
  rcases heventAdm with
    ⟨_hp, he, hmedium, hprog, hdMinusPos, _hdPlusPos, hdMinusDvd, hdPlusCop⟩
  rcases hotherAdm with
    ⟨_hpOther, hotherE, hmediumOther, hprogOther, _hdMinusOtherPos,
      _hdPlusOtherPos, hdMinusOtherDvd, hdPlusOtherCop⟩
  exact satEvent_eq_of_compatible_same_largePrime
    Pz rho event other hcompat hsamePrime he hotherE hmedium hmediumOther hcop
    hprog hprogOther hdMinusPos hdMinusDvd hdMinusOtherDvd hdPlusCop
    hdPlusOtherCop

theorem satEvent_eq_of_compatible_same_largePrime_admissible_of_gt
    (Pz rho : Nat) (event other : SatEvent)
    (hcompat : satEventCompatible event other)
    (hsamePrime : event.p = other.p)
    (hrhoPos : 0 < rho)
    (hlarge : 4 * rho < event.p)
    (heventAdm : satEventAdmissible Pz rho event)
    (hotherAdm : satEventAdmissible Pz rho other) :
    event = other := by
  have hcop : Nat.gcd (4 * rho) event.p = 1 :=
    prime_gcd_four_mul_eq_one_of_gt event.p rho heventAdm.1 hrhoPos hlarge
  exact satEvent_eq_of_compatible_same_largePrime_admissible
    Pz rho event other hcompat hsamePrime hcop heventAdm hotherAdm

theorem satEvent_largePrime_ne_of_compatible_ne_admissible
    (Pz rho : Nat) (event other : SatEvent)
    (hcompat : satEventCompatible event other)
    (hne : event ≠ other)
    (hcop : Nat.gcd (4 * rho) event.p = 1)
    (heventAdm : satEventAdmissible Pz rho event)
    (hotherAdm : satEventAdmissible Pz rho other) :
    event.p ≠ other.p := by
  intro hsamePrime
  exact hne (satEvent_eq_of_compatible_same_largePrime_admissible
    Pz rho event other hcompat hsamePrime hcop heventAdm hotherAdm)

theorem satEvent_largePrime_ne_of_compatible_ne_admissible_of_gt
    (Pz rho : Nat) (event other : SatEvent)
    (hcompat : satEventCompatible event other)
    (hne : event ≠ other)
    (hrhoPos : 0 < rho)
    (hlarge : 4 * rho < event.p)
    (heventAdm : satEventAdmissible Pz rho event)
    (hotherAdm : satEventAdmissible Pz rho other) :
    event.p ≠ other.p := by
  intro hsamePrime
  exact hne (satEvent_eq_of_compatible_same_largePrime_admissible_of_gt
    Pz rho event other hcompat hsamePrime hrhoPos hlarge heventAdm hotherAdm)

theorem satEvent_largePrime_ne_of_common_hit_ne_admissible
    (Pz rho n : Nat) (event other : SatEvent)
    (heventHit : satEventHit n event)
    (hotherHit : satEventHit n other)
    (hne : event ≠ other)
    (hcop : Nat.gcd (4 * rho) event.p = 1)
    (heventAdm : satEventAdmissible Pz rho event)
    (hotherAdm : satEventAdmissible Pz rho other) :
    event.p ≠ other.p := by
  exact satEvent_largePrime_ne_of_compatible_ne_admissible
    Pz rho event other
    (satEventCompatible_of_common_hit n event other heventHit hotherHit)
    hne hcop heventAdm hotherAdm

theorem satEvent_largePrime_ne_of_common_hit_ne_admissible_of_gt
    (Pz rho n : Nat) (event other : SatEvent)
    (heventHit : satEventHit n event)
    (hotherHit : satEventHit n other)
    (hne : event ≠ other)
    (hrhoPos : 0 < rho)
    (hlarge : 4 * rho < event.p)
    (heventAdm : satEventAdmissible Pz rho event)
    (hotherAdm : satEventAdmissible Pz rho other) :
    event.p ≠ other.p := by
  exact satEvent_largePrime_ne_of_compatible_ne_admissible_of_gt
    Pz rho event other
    (satEventCompatible_of_common_hit n event other heventHit hotherHit)
    hne hrhoPos hlarge heventAdm hotherAdm

theorem prime_not_dvd_conditionalModulus
    (p dPlusOld pOld : Nat)
    (hp : Nat.Prime p) (hpOld : Nat.Prime pOld)
    (hdpos : 0 < dPlusOld) (hdlt : dPlusOld < p)
    (hpne : p ≠ pOld) :
    ¬ p ∣ conditionalModulus dPlusOld pOld := by
  intro h
  have hcases := (hp.dvd_mul).1 (by simpa [conditionalModulus] using h)
  rcases hcases with hdp | hpo
  · have hp_le_d : p ≤ dPlusOld := Nat.le_of_dvd hdpos hdp
    omega
  · have hpeq : p = pOld := (Nat.prime_dvd_prime_iff_eq hp hpOld).1 hpo
    exact hpne hpeq

theorem prime_coprime_conditionalModulus
    (p dPlusOld pOld : Nat)
    (hp : Nat.Prime p) (hpOld : Nat.Prime pOld)
    (hdpos : 0 < dPlusOld) (hdlt : dPlusOld < p)
    (hpne : p ≠ pOld) :
    Nat.Coprime p (conditionalModulus dPlusOld pOld) := by
  exact hp.coprime_iff_not_dvd.2
    (prime_not_dvd_conditionalModulus p dPlusOld pOld hp hpOld hdpos hdlt hpne)

theorem prime_coprime_residualLcm
    (p : Nat) (old : List (Nat × Nat))
    (hp : Nat.Prime p)
    (holdPrime : ∀ row ∈ old, Nat.Prime row.2)
    (holdDPlusPos : ∀ row ∈ old, 0 < row.1)
    (holdDPlusLt : ∀ row ∈ old, row.1 < p)
    (holdLargePrimeNe : ∀ row ∈ old, p ≠ row.2) :
    Nat.Coprime p (residualLcm old) := by
  induction old with
  | nil =>
      simp [residualLcm]
  | cons row rest ih =>
      have hrowPrime : Nat.Prime row.2 := holdPrime row (by simp)
      have hrowPos : 0 < row.1 := holdDPlusPos row (by simp)
      have hrowLt : row.1 < p := holdDPlusLt row (by simp)
      have hrowNe : p ≠ row.2 := holdLargePrimeNe row (by simp)
      have hrowCop : Nat.Coprime p (conditionalModulus row.1 row.2) :=
        prime_coprime_conditionalModulus p row.1 row.2 hp hrowPrime hrowPos hrowLt hrowNe
      have hrestCop : Nat.Coprime p (residualLcm rest) := by
        apply ih
        · intro r hr
          exact holdPrime r (by simp [hr])
        · intro r hr
          exact holdDPlusPos r (by simp [hr])
        · intro r hr
          exact holdDPlusLt r (by simp [hr])
        · intro r hr
          exact holdLargePrimeNe r (by simp [hr])
      simpa [residualLcm, List.foldr] using
        prime_coprime_lcm p (conditionalModulus row.1 row.2) (residualLcm rest)
          hp hrowCop hrestCop

theorem appendageCommonDivisor_dvd_medium_of_oldList
    (dPlus p : Nat) (old : List (Nat × Nat))
    (hp : Nat.Prime p)
    (holdPrime : ∀ row ∈ old, Nat.Prime row.2)
    (holdDPlusPos : ∀ row ∈ old, 0 < row.1)
    (holdDPlusLt : ∀ row ∈ old, row.1 < p)
    (holdLargePrimeNe : ∀ row ∈ old, p ≠ row.2) :
    appendageG dPlus p (residualLcm old) ∣ dPlus := by
  have hcop : Nat.Coprime p (residualLcm old) :=
    prime_coprime_residualLcm p old hp holdPrime holdDPlusPos holdDPlusLt
      holdLargePrimeNe
  exact appendageCommonDivisor_dvd_medium dPlus p (residualLcm old) hcop

/-- If a new saturated event is compatible with each old event and is distinct
from each of them, large-prime uniqueness rules out sharing the new large prime
with any old row.  The remaining hypotheses are the small/rough split,
progression, positivity, and size conditions needed to invoke that uniqueness
theorem for each old event and then prove coprimality with the old residual lcm.
-/
theorem appendageCommonDivisor_dvd_medium_of_compatible_events
    (Pz rho : Nat) (event : SatEvent) (old : List SatEvent)
    (hp : Nat.Prime event.p)
    (he : event.e < event.p)
    (hmedium : event.dMinus * event.dPlus < rho)
    (hcop : Nat.gcd (4 * rho) event.p = 1)
    (hprog :
      (event.dMinus * event.dPlus) * event.p + 1 ≡ 0 [MOD 4 * rho])
    (hdMinusPos : 0 < event.dMinus)
    (hdMinusDvd : event.dMinus ∣ Pz)
    (hdPlusCop : Nat.Coprime event.dPlus Pz)
    (holdPrime : ∀ other ∈ old, Nat.Prime other.p)
    (holdE : ∀ other ∈ old, other.e < other.p)
    (holdMedium : ∀ other ∈ old, other.dMinus * other.dPlus < rho)
    (holdProg : ∀ other ∈ old,
      (other.dMinus * other.dPlus) * other.p + 1 ≡ 0 [MOD 4 * rho])
    (holdDMinusDvd : ∀ other ∈ old, other.dMinus ∣ Pz)
    (holdDPlusCop : ∀ other ∈ old, Nat.Coprime other.dPlus Pz)
    (holdDPlusPos : ∀ other ∈ old, 0 < other.dPlus)
    (holdDPlusLt : ∀ other ∈ old, other.dPlus < event.p)
    (hcompat : ∀ other ∈ old, satEventCompatible event other)
    (hdistinct : ∀ other ∈ old, event ≠ other) :
    appendageG event.dPlus event.p (residualLcm (satEventRows old)) ∣
      event.dPlus := by
  apply appendageCommonDivisor_dvd_medium_of_oldList
  · exact hp
  · intro row hrow
    rcases List.mem_map.mp hrow with ⟨other, hother, hrowEq⟩
    subst hrowEq
    exact holdPrime other hother
  · intro row hrow
    rcases List.mem_map.mp hrow with ⟨other, hother, hrowEq⟩
    subst hrowEq
    exact holdDPlusPos other hother
  · intro row hrow
    rcases List.mem_map.mp hrow with ⟨other, hother, hrowEq⟩
    subst hrowEq
    exact holdDPlusLt other hother
  · intro row hrow
    rcases List.mem_map.mp hrow with ⟨other, hother, hrowEq⟩
    subst hrowEq
    exact satEvent_largePrime_ne_of_compatible_ne
      Pz rho event other (hcompat other hother) (hdistinct other hother)
      he (holdE other hother) hmedium (holdMedium other hother) hcop hprog
      (holdProg other hother) hdMinusPos hdMinusDvd (holdDMinusDvd other hother)
      hdPlusCop (holdDPlusCop other hother)

/-- Bundled admissibility form of the compatible-event appendage wrapper.  This
keeps the compatibility hypotheses explicit but projects all event regularity,
progression, split, and positivity assumptions from `satEventAdmissible`. -/
theorem appendageCommonDivisor_dvd_medium_of_compatible_events_admissible
    (Pz rho : Nat) (event : SatEvent) (old : List SatEvent)
    (hcop : Nat.gcd (4 * rho) event.p = 1)
    (heventAdm : satEventAdmissible Pz rho event)
    (holdAdm : ∀ other ∈ old, satEventAdmissible Pz rho other)
    (holdDPlusLt : ∀ other ∈ old, other.dPlus < event.p)
    (hcompat : ∀ other ∈ old, satEventCompatible event other)
    (hdistinct : ∀ other ∈ old, event ≠ other) :
    appendageG event.dPlus event.p (residualLcm (satEventRows old)) ∣
      event.dPlus := by
  rcases heventAdm with
    ⟨hp, he, hmedium, hprog, hdMinusPos, _hdPlusPos, hdMinusDvd, hdPlusCop⟩
  apply appendageCommonDivisor_dvd_medium_of_compatible_events
  · exact hp
  · exact he
  · exact hmedium
  · exact hcop
  · exact hprog
  · exact hdMinusPos
  · exact hdMinusDvd
  · exact hdPlusCop
  · intro other hother
    exact (holdAdm other hother).1
  · intro other hother
    exact (holdAdm other hother).2.1
  · intro other hother
    exact (holdAdm other hother).2.2.1
  · intro other hother
    exact (holdAdm other hother).2.2.2.1
  · intro other hother
    exact (holdAdm other hother).2.2.2.2.2.2.1
  · intro other hother
    exact (holdAdm other hother).2.2.2.2.2.2.2
  · intro other hother
    exact (holdAdm other hother).2.2.2.2.2.1
  · exact holdDPlusLt
  · exact hcompat
  · exact hdistinct

/-- Large-prime-bound version of the admissible compatible-event appendage
wrapper.  The inequality `4 * rho < event.p` supplies both the progression
coprimality input and the old-row size bound needed for residual-lcm
coprimality. -/
theorem appendageCommonDivisor_dvd_medium_of_compatible_events_admissible_of_gt
    (Pz rho : Nat) (event : SatEvent) (old : List SatEvent)
    (hrhoPos : 0 < rho)
    (hlarge : 4 * rho < event.p)
    (heventAdm : satEventAdmissible Pz rho event)
    (holdAdm : ∀ other ∈ old, satEventAdmissible Pz rho other)
    (hcompat : ∀ other ∈ old, satEventCompatible event other)
    (hdistinct : ∀ other ∈ old, event ≠ other) :
    appendageG event.dPlus event.p (residualLcm (satEventRows old)) ∣
      event.dPlus := by
  have hcop : Nat.gcd (4 * rho) event.p = 1 :=
    prime_gcd_four_mul_eq_one_of_gt event.p rho heventAdm.1 hrhoPos hlarge
  have hrho_le_p : rho ≤ event.p :=
    rho_le_of_four_mul_lt rho event.p hlarge
  apply appendageCommonDivisor_dvd_medium_of_compatible_events_admissible
  · exact hcop
  · exact heventAdm
  · exact holdAdm
  · intro other hother
    exact satEventDPlus_lt_of_medium_of_le_largePrime rho event.p other
      ((holdAdm other hother).2.2.2.2.1) ((holdAdm other hother).2.2.1)
      hrho_le_p
  · exact hcompat
  · exact hdistinct

/-- If a new event and each old event have a common shifted residual hit at the
same integer `n`, then the compatibility hypotheses needed for the appendage
divisibility wrapper follow from those hits. -/
theorem appendageCommonDivisor_dvd_medium_of_common_hits
    (Pz rho n : Nat) (event : SatEvent) (old : List SatEvent)
    (hp : Nat.Prime event.p)
    (he : event.e < event.p)
    (hmedium : event.dMinus * event.dPlus < rho)
    (hcop : Nat.gcd (4 * rho) event.p = 1)
    (hprog :
      (event.dMinus * event.dPlus) * event.p + 1 ≡ 0 [MOD 4 * rho])
    (hdMinusPos : 0 < event.dMinus)
    (hdMinusDvd : event.dMinus ∣ Pz)
    (hdPlusCop : Nat.Coprime event.dPlus Pz)
    (holdPrime : ∀ other ∈ old, Nat.Prime other.p)
    (holdE : ∀ other ∈ old, other.e < other.p)
    (holdMedium : ∀ other ∈ old, other.dMinus * other.dPlus < rho)
    (holdProg : ∀ other ∈ old,
      (other.dMinus * other.dPlus) * other.p + 1 ≡ 0 [MOD 4 * rho])
    (holdDMinusDvd : ∀ other ∈ old, other.dMinus ∣ Pz)
    (holdDPlusCop : ∀ other ∈ old, Nat.Coprime other.dPlus Pz)
    (holdDPlusPos : ∀ other ∈ old, 0 < other.dPlus)
    (holdDPlusLt : ∀ other ∈ old, other.dPlus < event.p)
    (heventHit : satEventHit n event)
    (holdHit : ∀ other ∈ old, satEventHit n other)
    (hdistinct : ∀ other ∈ old, event ≠ other) :
    appendageG event.dPlus event.p (residualLcm (satEventRows old)) ∣
      event.dPlus := by
  apply appendageCommonDivisor_dvd_medium_of_compatible_events
  · exact hp
  · exact he
  · exact hmedium
  · exact hcop
  · exact hprog
  · exact hdMinusPos
  · exact hdMinusDvd
  · exact hdPlusCop
  · exact holdPrime
  · exact holdE
  · exact holdMedium
  · exact holdProg
  · exact holdDMinusDvd
  · exact holdDPlusCop
  · exact holdDPlusPos
  · exact holdDPlusLt
  · intro other hother
    exact satEventCompatible_of_common_hit n event other heventHit
      (holdHit other hother)
  · exact hdistinct

/-- A large-prime lower bound supplies the coprimality and old-row size inputs
for the common-hit appendage wrapper.  The remaining assumptions are the
event-level regularity, progression, split, and common-hit hypotheses used by
large-prime uniqueness. -/
theorem appendageCommonDivisor_dvd_medium_of_common_hits_largePrime
    (Pz rho n : Nat) (event : SatEvent) (old : List SatEvent)
    (hp : Nat.Prime event.p)
    (he : event.e < event.p)
    (hmedium : event.dMinus * event.dPlus < rho)
    (hrhoPos : 0 < rho)
    (hlarge : 4 * rho < event.p)
    (hprog :
      (event.dMinus * event.dPlus) * event.p + 1 ≡ 0 [MOD 4 * rho])
    (hdMinusPos : 0 < event.dMinus)
    (hdMinusDvd : event.dMinus ∣ Pz)
    (hdPlusCop : Nat.Coprime event.dPlus Pz)
    (holdPrime : ∀ other ∈ old, Nat.Prime other.p)
    (holdE : ∀ other ∈ old, other.e < other.p)
    (holdMedium : ∀ other ∈ old, other.dMinus * other.dPlus < rho)
    (holdProg : ∀ other ∈ old,
      (other.dMinus * other.dPlus) * other.p + 1 ≡ 0 [MOD 4 * rho])
    (holdDMinusPos : ∀ other ∈ old, 0 < other.dMinus)
    (holdDMinusDvd : ∀ other ∈ old, other.dMinus ∣ Pz)
    (holdDPlusCop : ∀ other ∈ old, Nat.Coprime other.dPlus Pz)
    (holdDPlusPos : ∀ other ∈ old, 0 < other.dPlus)
    (heventHit : satEventHit n event)
    (holdHit : ∀ other ∈ old, satEventHit n other)
    (hdistinct : ∀ other ∈ old, event ≠ other) :
    appendageG event.dPlus event.p (residualLcm (satEventRows old)) ∣
      event.dPlus := by
  have hcop : Nat.gcd (4 * rho) event.p = 1 :=
    prime_gcd_four_mul_eq_one_of_gt event.p rho hp hrhoPos hlarge
  have hrho_le_p : rho ≤ event.p :=
    rho_le_of_four_mul_lt rho event.p hlarge
  apply appendageCommonDivisor_dvd_medium_of_common_hits
  · exact hp
  · exact he
  · exact hmedium
  · exact hcop
  · exact hprog
  · exact hdMinusPos
  · exact hdMinusDvd
  · exact hdPlusCop
  · exact holdPrime
  · exact holdE
  · exact holdMedium
  · exact holdProg
  · exact holdDMinusDvd
  · exact holdDPlusCop
  · exact holdDPlusPos
  · intro other hother
    exact satEventDPlus_lt_of_medium_of_le_largePrime rho event.p other
      (holdDMinusPos other hother) (holdMedium other hother) hrho_le_p
  · exact heventHit
  · exact holdHit
  · exact hdistinct

/-- Bundled admissibility form of the common-hit appendage wrapper.  The
separate row regularity, progression, split, and positivity hypotheses are
projected from `satEventAdmissible`; the only extra global input is the
large-prime bound for the new event. -/
theorem appendageCommonDivisor_dvd_medium_of_common_hits_admissible
    (Pz rho n : Nat) (event : SatEvent) (old : List SatEvent)
    (hrhoPos : 0 < rho)
    (hlarge : 4 * rho < event.p)
    (heventAdm : satEventAdmissible Pz rho event)
    (holdAdm : ∀ other ∈ old, satEventAdmissible Pz rho other)
    (heventHit : satEventHit n event)
    (holdHit : ∀ other ∈ old, satEventHit n other)
    (hdistinct : ∀ other ∈ old, event ≠ other) :
    appendageG event.dPlus event.p (residualLcm (satEventRows old)) ∣
      event.dPlus := by
  rcases heventAdm with
    ⟨hp, he, hmedium, hprog, hdMinusPos, _hdPlusPos, hdMinusDvd, hdPlusCop⟩
  apply appendageCommonDivisor_dvd_medium_of_common_hits_largePrime
  · exact hp
  · exact he
  · exact hmedium
  · exact hrhoPos
  · exact hlarge
  · exact hprog
  · exact hdMinusPos
  · exact hdMinusDvd
  · exact hdPlusCop
  · intro other hother
    exact (holdAdm other hother).1
  · intro other hother
    exact (holdAdm other hother).2.1
  · intro other hother
    exact (holdAdm other hother).2.2.1
  · intro other hother
    exact (holdAdm other hother).2.2.2.1
  · intro other hother
    exact (holdAdm other hother).2.2.2.2.1
  · intro other hother
    exact (holdAdm other hother).2.2.2.2.2.2.1
  · intro other hother
    exact (holdAdm other hother).2.2.2.2.2.2.2
  · intro other hother
    exact (holdAdm other hother).2.2.2.2.2.1
  · exact heventHit
  · exact holdHit
  · exact hdistinct

theorem totient_divisor_identity (g : Nat) :
    (Nat.divisors g).sum Nat.totient = g := by
  exact Nat.sum_totient g

theorem appendageG_totient_expansion (dPlus p L : Nat) :
    (Nat.divisors (appendageG dPlus p L)).sum Nat.totient =
      appendageG dPlus p L := by
  exact totient_divisor_identity (appendageG dPlus p L)

/-- Finite weighted divisor switch used in the appendage argument.  If every
positive integer `g i` lies in `[1,B]`, expanding `g i` by
`sum_{D | g i} phi(D)` and reversing the two finite sums gives the displayed
divisor-restricted masses. -/
theorem weighted_sum_eq_totient_divisor_mass
    {α : Type} [DecidableEq α]
    (U : Finset α) (w : α → ℚ) (g : α → ℕ) (B : ℕ)
    (hgpos : ∀ i ∈ U, 0 < g i)
    (hgle : ∀ i ∈ U, g i ≤ B) :
    (∑ i ∈ U, w i * (g i : ℚ)) =
      ∑ D ∈ Finset.Icc 1 B, (Nat.totient D : ℚ) *
        ∑ i ∈ U.filter (fun i => D ∣ g i), w i := by
  classical
  have hdivisors : ∀ i ∈ U,
      (Finset.Icc 1 B).filter (fun D => D ∣ g i) = (g i).divisors := by
    intro i hi
    ext D
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · intro h
      exact ⟨h.2, (hgpos i hi).ne'⟩
    · intro h
      have hDpos : 0 < D := Nat.pos_of_dvd_of_pos h.1 (hgpos i hi)
      exact
        ⟨⟨hDpos, (Nat.le_of_dvd (hgpos i hi) h.1).trans (hgle i hi)⟩, h.1⟩
  calc
    (∑ i ∈ U, w i * (g i : ℚ)) =
        ∑ i ∈ U, ∑ D ∈ Finset.Icc 1 B,
          if D ∣ g i then (Nat.totient D : ℚ) * w i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter, hdivisors i hi, ← Finset.sum_mul]
      rw [← Nat.cast_sum, totient_divisor_identity]
      ring
    _ = ∑ D ∈ Finset.Icc 1 B, ∑ i ∈ U,
          if D ∣ g i then (Nat.totient D : ℚ) * w i else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ D ∈ Finset.Icc 1 B, (Nat.totient D : ℚ) *
          ∑ i ∈ U.filter (fun i => D ∣ g i), w i := by
      apply Finset.sum_congr rfl
      intro D _hD
      rw [Finset.mul_sum, ← Finset.sum_filter]

/-- Primes in the finite interval `[2,B]`. -/
def primeFinsetUpTo (B : ℕ) : Finset ℕ :=
  (Finset.Icc 2 B).filter Nat.Prime

/-- If every prime divisor of `n` is at least `q`, then the product of one
copy of `q` for each distinct prime divisor is at most `n`. -/
theorem lowerBound_pow_primeFactors_card_le_self
    (n q : ℕ) (hn : 0 < n)
    (hq : ∀ p ∈ n.primeFactors, q ≤ p) :
    q ^ n.primeFactors.card ≤ n := by
  classical
  have hprod : ∏ p ∈ n.primeFactors, q ≤ ∏ p ∈ n.primeFactors, p :=
    Finset.prod_le_prod (fun _ _ => Nat.zero_le q) hq
  calc
    q ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, q := by
      simp [Finset.prod_const, nsmul_eq_mul]
    _ ≤ ∏ p ∈ n.primeFactors, p := hprod
    _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

/-- Reciprocal prime-divisor sum bounded by the number of distinct prime
divisors when all of them are at least `q`. -/
theorem primeFactors_recip_sum_le_card_div
    (n q : ℕ) (hqpos : 0 < q)
    (hq : ∀ p ∈ n.primeFactors, q ≤ p) :
    (∑ p ∈ n.primeFactors, (1 : ℝ) / (p : ℝ)) ≤
      (n.primeFactors.card : ℝ) / (q : ℝ) := by
  calc
    (∑ p ∈ n.primeFactors, (1 : ℝ) / (p : ℝ)) ≤
        ∑ _p ∈ n.primeFactors, (1 : ℝ) / (q : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le (by exact_mod_cast hqpos)
        (by exact_mod_cast hq p hp)
    _ = (n.primeFactors.card : ℝ) / (q : ℝ) := by
      simp [div_eq_mul_inv]

/-- Elementary rough-prime estimate: if every prime divisor of `n` is at
least `q ≥ 2`, its reciprocal prime-divisor sum is bounded by
`(log n / log q) / q`. -/
theorem primeFactors_recip_sum_le_log_div_log_div
    (n q : ℕ) (hn : 0 < n) (hq2 : 2 ≤ q)
    (hq : ∀ p ∈ n.primeFactors, q ≤ p) :
    (∑ p ∈ n.primeFactors, (1 : ℝ) / (p : ℝ)) ≤
      (Real.log (n : ℝ) / Real.log (q : ℝ)) / (q : ℝ) := by
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_two hq2
  have hpow := lowerBound_pow_primeFactors_card_le_self n q hn hq
  have hpowpos : 0 < (((q ^ n.primeFactors.card : ℕ) : ℝ)) := by
    exact_mod_cast Nat.pos_pow_of_pos n.primeFactors.card hqpos
  have hlogpow :
      Real.log (((q ^ n.primeFactors.card : ℕ) : ℝ)) ≤
        Real.log (n : ℝ) :=
    Real.log_le_log hpowpos (by exact_mod_cast hpow)
  have hlogqpos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast hq2)
  have hcard : (n.primeFactors.card : ℝ) ≤
      Real.log (n : ℝ) / Real.log (q : ℝ) := by
    apply (le_div_iff₀ hlogqpos).mpr
    rw [← Real.log_pow]
    simpa [Nat.cast_pow] using hlogpow
  calc
    (∑ p ∈ n.primeFactors, (1 : ℝ) / (p : ℝ)) ≤
        (n.primeFactors.card : ℝ) / (q : ℝ) :=
      primeFactors_recip_sum_le_card_div n q hqpos hq
    _ ≤ (Real.log (n : ℝ) / Real.log (q : ℝ)) / (q : ℝ) :=
      div_le_div_of_nonneg_right hcard (by positivity)

/-- Exact finite change of variables `n = D t` in a reciprocal sum.  This is
the algebraic `D⁻¹` extracted from the rough `dplus` coordinate in the
event-tensor argument; all range and coprimality conditions remain encoded in
the quotient image on the right. -/
theorem reciprocal_sum_multiples_eq_divisor_inv_mul_quotient_image
    (U : Finset ℕ) (D : ℕ) (hD : 0 < D)
    (hUpos : ∀ n ∈ U, 0 < n) :
    (∑ n ∈ U.filter (fun n => D ∣ n), (1 : ℝ) / (n : ℝ)) =
      (1 / (D : ℝ)) *
        ∑ t ∈ (U.filter (fun n => D ∣ n)).image (fun n => n / D),
          (1 : ℝ) / (t : ℝ) := by
  classical
  let S := U.filter (fun n => D ∣ n)
  have hinj : Set.InjOn (fun n : ℕ => n / D) (S : Set ℕ) := by
    intro a ha b hb hab
    have haD : D ∣ a := (Finset.mem_filter.mp ha).2
    have hbD : D ∣ b := (Finset.mem_filter.mp hb).2
    calc
      a = D * (a / D) := (Nat.mul_div_cancel' haD).symm
      _ = D * (b / D) := congrArg (fun t : ℕ => D * t) hab
      _ = b := Nat.mul_div_cancel' hbD
  have hterm : ∀ n ∈ S,
      (1 : ℝ) / (n : ℝ) =
        (1 / (D : ℝ)) * (1 / ((n / D : ℕ) : ℝ)) := by
    intro n hn
    have hnD : D ∣ n := (Finset.mem_filter.mp hn).2
    have hnpos : 0 < n := hUpos n (Finset.mem_of_mem_filter n hn)
    have htpos : 0 < n / D := Nat.div_pos (Nat.le_of_dvd hnpos hnD) hD
    rw [← Nat.mul_div_cancel' hnD, Nat.cast_mul]
    field_simp [show (D : ℝ) ≠ 0 by exact_mod_cast hD.ne',
      show ((n / D : ℕ) : ℝ) ≠ 0 by exact_mod_cast htpos.ne']
  change (∑ n ∈ S, (1 : ℝ) / (n : ℝ)) = _
  calc
    (∑ n ∈ S, (1 : ℝ) / (n : ℝ)) =
        ∑ n ∈ S, (1 / (D : ℝ)) *
          (1 / ((n / D : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hterm n hn
    _ = (1 / (D : ℝ)) *
        ∑ n ∈ S, (1 / ((n / D : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
    _ = (1 / (D : ℝ)) *
        ∑ t ∈ S.image (fun n => n / D), (1 : ℝ) / (t : ℝ) := by
      rw [Finset.sum_image hinj]

/-- The truncated squarefree divisor sum is bounded by its full finite Euler
product.  The proof injects each squarefree `D` into its prime-factor set and
then enlarges to the entire powerset of the primes up to `B`. -/
theorem squarefree_primeFactor_sum_le_eulerProduct
    (B : ℕ) (a : ℕ → ℚ)
    (ha : ∀ p ∈ primeFinsetUpTo B, 0 ≤ a p) :
    (∑ D ∈ (Finset.Icc 1 B).filter Squarefree,
      ∏ p ∈ D.primeFactors, a p) ≤
        ∏ p ∈ primeFinsetUpTo B, (1 + a p) := by
  classical
  let domain := (Finset.Icc 1 B).filter Squarefree
  let code : ℕ → Finset ℕ := fun D => D.primeFactors
  let weight : Finset ℕ → ℚ := fun t => ∏ p ∈ t, a p
  have hmap : ∀ D ∈ domain, code D ∈ (primeFinsetUpTo B).powerset := by
    intro D hD
    rw [Finset.mem_powerset]
    intro p hp
    dsimp [domain] at hD
    dsimp [code] at hp
    rcases Finset.mem_filter.mp hD with ⟨hDIcc, _hDsqf⟩
    have hpData := Nat.mem_primeFactors.mp hp
    rw [primeFinsetUpTo, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hpData.1.two_le,
      (Nat.le_of_dvd (Finset.mem_Icc.mp hDIcc).1 hpData.2.1).trans
        (Finset.mem_Icc.mp hDIcc).2⟩, hpData.1⟩
  have hinj : Set.InjOn code (domain : Set ℕ) := by
    intro D hD E hE hcode
    change D ∈ domain at hD
    change E ∈ domain at hE
    dsimp [domain] at hD hE
    dsimp [code] at hcode
    have hDsqf := (Finset.mem_filter.mp hD).2
    have hEsqf := (Finset.mem_filter.mp hE).2
    calc
      D = ∏ p ∈ D.primeFactors, p :=
        (Nat.prod_primeFactors_of_squarefree hDsqf).symm
      _ = ∏ p ∈ E.primeFactors, p := by rw [hcode]
      _ = E := Nat.prod_primeFactors_of_squarefree hEsqf
  have hnonneg : ∀ t ∈ (primeFinsetUpTo B).powerset,
      0 ≤ weight t := by
    intro t ht
    unfold weight
    apply Finset.prod_nonneg
    intro p hp
    exact ha p ((Finset.mem_powerset.mp ht) hp)
  calc
    (∑ D ∈ (Finset.Icc 1 B).filter Squarefree,
        ∏ p ∈ D.primeFactors, a p) =
      ∑ t ∈ domain.image code, weight t := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ t ∈ (primeFinsetUpTo B).powerset, weight t := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro t ht
        rcases Finset.mem_image.mp ht with ⟨D, hD, rfl⟩
        exact hmap D hD
      · intro t ht _hnot
        exact hnonneg t ht
    _ = ∏ p ∈ primeFinsetUpTo B, (a p + 1) := by
      rw [Finset.prod_add]
      simp [weight]
    _ = ∏ p ∈ primeFinsetUpTo B, (1 + a p) := by
      apply Finset.prod_congr rfl
      intro p _hp
      ring

theorem totient_over_square_le_recip
    (D : Nat) (hD : 0 < D) :
    (Nat.totient D : ℚ) / ((D : ℚ) ^ 2) ≤ 1 / (D : ℚ) := by
  have hle : (Nat.totient D : ℚ) ≤ (D : ℚ) := by
    exact_mod_cast Nat.totient_le D
  have hDposQ : 0 < (D : ℚ) := by exact_mod_cast hD
  have hDne : (D : ℚ) ≠ 0 := ne_of_gt hDposQ
  have hDsqNonneg : 0 ≤ (D : ℚ) ^ 2 := le_of_lt (sq_pos_of_pos hDposQ)
  calc
    (Nat.totient D : ℚ) / ((D : ℚ) ^ 2) ≤
        (D : ℚ) / ((D : ℚ) ^ 2) := by
      exact div_le_div_of_nonneg_right hle hDsqNonneg
    _ = 1 / (D : ℚ) := by
      field_simp [hDne]
      ring

theorem lcm_recip_identity
    (L q : Nat) (hL : 0 < L) (hq : 0 < q) :
    (1 : ℚ) / (Nat.lcm L q : ℚ) =
      (Nat.gcd L q : ℚ) / ((L : ℚ) * (q : ℚ)) := by
  have hlcmpos : 0 < Nat.lcm L q := Nat.lcm_pos hL hq
  have hprodNat : Nat.gcd L q * Nat.lcm L q = L * q := by
    exact Nat.gcd_mul_lcm L q
  have hprodQ :
      (Nat.gcd L q : ℚ) * (Nat.lcm L q : ℚ) = (L : ℚ) * (q : ℚ) := by
    exact_mod_cast hprodNat
  have hgcdPos : 0 < Nat.gcd L q := Nat.gcd_pos_of_pos_left q hL
  have hgcdQ : (Nat.gcd L q : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hgcdPos)
  have hlcmQ : (Nat.lcm L q : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hlcmpos)
  have hLQ : (L : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  field_simp [hgcdQ, hlcmQ, hLQ, hqQ]
  ring_nf at hprodQ ⊢
  nlinarith [hprodQ]

theorem brun_lcm_weight_identity
    (L q : Nat) (hL : 0 < L) (hq : 0 < q) :
    (1 : ℚ) / (Nat.lcm L q : ℚ) =
      (1 / (L : ℚ)) * (1 / (q : ℚ)) * (Nat.gcd L q : ℚ) := by
  have h := lcm_recip_identity L q hL hq
  have hLQ : (L : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  rw [h]
  field_simp [hLQ, hqQ]

theorem residualLcm_cons_lcm_weight_identity
    (old : List (Nat × Nat)) (dPlus p : Nat)
    (hL : 0 < residualLcm old)
    (hdPlus : 0 < dPlus) (hp : 0 < p) :
    (1 : ℚ) / (residualLcm ((dPlus, p) :: old) : ℚ) =
      (1 / (residualLcm old : ℚ)) *
        (1 / (conditionalModulus dPlus p : ℚ)) *
          (appendageG dPlus p (residualLcm old) : ℚ) := by
  have hq : 0 < conditionalModulus dPlus p := by
    simpa [conditionalModulus] using Nat.mul_pos hdPlus hp
  have h := brun_lcm_weight_identity
    (residualLcm old) (conditionalModulus dPlus p) hL hq
  simpa [residualLcm, appendageG, Nat.lcm_comm, Nat.gcd_comm, mul_assoc] using h

theorem residualLcm_cons_recip_le_recip_largePrime_of_appendage_dvd
    (old : List (Nat × Nat)) (dPlus p : Nat)
    (hL : 0 < residualLcm old)
    (hdPlus : 0 < dPlus) (hp : 0 < p)
    (happend : appendageG dPlus p (residualLcm old) ∣ dPlus) :
    (1 : ℚ) / (residualLcm ((dPlus, p) :: old) : ℚ) ≤
      (1 / (residualLcm old : ℚ)) * (1 / (p : ℚ)) := by
  have hidentity := residualLcm_cons_lcm_weight_identity old dPlus p hL hdPlus hp
  rw [hidentity]
  let g := appendageG dPlus p (residualLcm old)
  have hgLeNat : g ≤ dPlus :=
    Nat.le_of_dvd hdPlus (by simpa [g] using happend)
  have hgLe : (g : ℚ) ≤ (dPlus : ℚ) := by exact_mod_cast hgLeNat
  have hLposQ : 0 < (residualLcm old : ℚ) := by exact_mod_cast hL
  have hpPosQ : 0 < (p : ℚ) := by exact_mod_cast hp
  have hdPosQ : 0 < (dPlus : ℚ) := by exact_mod_cast hdPlus
  have hleftFactorNonneg : 0 ≤ (1 : ℚ) / (residualLcm old : ℚ) :=
    div_nonneg zero_le_one (le_of_lt hLposQ)
  have hcore :
      (1 / (conditionalModulus dPlus p : ℚ)) * (g : ℚ) ≤
        1 / (p : ℚ) := by
    calc
      (1 / (conditionalModulus dPlus p : ℚ)) * (g : ℚ)
          ≤ (1 / (conditionalModulus dPlus p : ℚ)) * (dPlus : ℚ) := by
            exact mul_le_mul_of_nonneg_left hgLe (by positivity)
      _ = 1 / (p : ℚ) := by
            field_simp [conditionalModulus, ne_of_gt hdPosQ, ne_of_gt hpPosQ]
  calc
    (1 / (residualLcm old : ℚ)) *
        (1 / (conditionalModulus dPlus p : ℚ)) * (g : ℚ)
        = (1 / (residualLcm old : ℚ)) *
            ((1 / (conditionalModulus dPlus p : ℚ)) * (g : ℚ)) := by
          ring
    _ ≤ (1 / (residualLcm old : ℚ)) * (1 / (p : ℚ)) := by
          exact mul_le_mul_of_nonneg_left hcore hleftFactorNonneg

theorem rho_pos_of_satEventAdmissible
    (Pz rho : Nat) (event : SatEvent)
    (hadm : satEventAdmissible Pz rho event) :
    0 < rho := by
  have hmedium : event.dMinus * event.dPlus < rho := hadm.2.2.1
  have hdMinusPos : 0 < event.dMinus := hadm.2.2.2.2.1
  have hdPlusPos : 0 < event.dPlus := hadm.2.2.2.2.2.1
  exact lt_trans (Nat.mul_pos hdMinusPos hdPlusPos) hmedium

theorem satEvent_gcd_four_mul_prime_eq_one_of_admissible
    (Pz rho : Nat) (event : SatEvent)
    (hadm : satEventAdmissible Pz rho event) :
    Nat.gcd (4 * rho) event.p = 1 := by
  have hp : Nat.Prime event.p := hadm.1
  have hprog :
      (event.dMinus * event.dPlus) * event.p + 1 ≡ 0 [MOD 4 * rho] :=
    hadm.2.2.2.1
  have hprogDvd :
      4 * rho ∣ (event.dMinus * event.dPlus) * event.p + 1 :=
    (Nat.modEq_zero_iff_dvd).1 hprog
  have hnotDvd : ¬ event.p ∣ 4 * rho := by
    intro hpDvdMod
    have hpDvdProg :
        event.p ∣ (event.dMinus * event.dPlus) * event.p + 1 :=
      hpDvdMod.trans hprogDvd
    have hpDvdMul : event.p ∣ (event.dMinus * event.dPlus) * event.p :=
      Nat.dvd_mul_left event.p (event.dMinus * event.dPlus)
    have hpDvdOne : event.p ∣ 1 :=
      (Nat.dvd_add_iff_right hpDvdMul).mpr hpDvdProg
    exact hp.not_dvd_one hpDvdOne
  have hcop : Nat.Coprime event.p (4 * rho) :=
    hp.coprime_iff_not_dvd.mpr hnotDvd
  exact Nat.coprime_iff_gcd_eq_one.mp hcop.symm

theorem satEvent_eq_of_compatible_same_largePrime_admissible_autoCoprime
    (Pz rho : Nat) (event other : SatEvent)
    (hcompat : satEventCompatible event other)
    (hsamePrime : event.p = other.p)
    (heventAdm : satEventAdmissible Pz rho event)
    (hotherAdm : satEventAdmissible Pz rho other) :
    event = other := by
  exact satEvent_eq_of_compatible_same_largePrime_admissible
    Pz rho event other hcompat hsamePrime
    (satEvent_gcd_four_mul_prime_eq_one_of_admissible Pz rho event heventAdm)
    heventAdm hotherAdm

theorem satEvent_largePrime_ne_of_compatible_ne_admissible_autoCoprime
    (Pz rho : Nat) (event other : SatEvent)
    (hcompat : satEventCompatible event other)
    (hne : event ≠ other)
    (heventAdm : satEventAdmissible Pz rho event)
    (hotherAdm : satEventAdmissible Pz rho other) :
    event.p ≠ other.p := by
  intro hsamePrime
  exact hne (satEvent_eq_of_compatible_same_largePrime_admissible_autoCoprime
    Pz rho event other hcompat hsamePrime heventAdm hotherAdm)

theorem satEvent_largePrime_ne_of_common_hit_ne_admissible_autoCoprime
    (Pz rho n : Nat) (event other : SatEvent)
    (heventHit : satEventHit n event)
    (hotherHit : satEventHit n other)
    (hne : event ≠ other)
    (heventAdm : satEventAdmissible Pz rho event)
    (hotherAdm : satEventAdmissible Pz rho other) :
    event.p ≠ other.p := by
  exact satEvent_largePrime_ne_of_compatible_ne_admissible_autoCoprime
    Pz rho event other
    (satEventCompatible_of_common_hit n event other heventHit hotherHit)
    hne heventAdm hotherAdm

theorem satEvent_eq_of_compatible_same_largePrime_admissibleFor_autoCoprime
    (Pz : Nat) (rhoOf : Nat → Nat) (event other : SatEvent)
    (hcompat : satEventCompatible event other)
    (hsamePrime : event.p = other.p)
    (heventAdm : satEventAdmissibleFor Pz rhoOf event)
    (hotherAdm : satEventAdmissibleFor Pz rhoOf other) :
    event = other := by
  have heventAdm' : satEventAdmissible Pz (rhoOf event.e) event := by
    simpa [satEventAdmissibleFor] using heventAdm
  have hotherAdm' : satEventAdmissible Pz (rhoOf other.e) other := by
    simpa [satEventAdmissibleFor] using hotherAdm
  have hcopFour : Nat.gcd event.p 4 = 1 := by
    have hcop :
        Nat.gcd (4 * rhoOf event.e) event.p = 1 :=
      satEvent_gcd_four_mul_prime_eq_one_of_admissible
        Pz (rhoOf event.e) event heventAdm'
    have hgcdDvd :
        Nat.gcd event.p 4 ∣ Nat.gcd (4 * rhoOf event.e) event.p :=
      Nat.dvd_gcd
        ((Nat.gcd_dvd_right event.p 4).trans
          (Nat.dvd_mul_right 4 (rhoOf event.e)))
        (Nat.gcd_dvd_left event.p 4)
    exact Nat.dvd_one.mp (by simpa [hcop] using hgcdDvd)
  have hcompatAtP : event.e ≡ other.e [MOD event.p] :=
    satEvent_modEq_of_compatible_same_largePrime event other hcompat hsamePrime
      hcopFour
  have hotherELtAtEventP : other.e < event.p := by
    simpa [hsamePrime] using hotherAdm'.2.1
  have heEq : event.e = other.e :=
    hcompatAtP.eq_of_lt_of_lt heventAdm'.2.1 hotherELtAtEventP
  have hotherAdmAtEventRho : satEventAdmissible Pz (rhoOf event.e) other := by
    simpa [heEq] using hotherAdm'
  exact satEvent_eq_of_compatible_same_largePrime_admissible_autoCoprime
    Pz (rhoOf event.e) event other hcompat hsamePrime heventAdm'
    hotherAdmAtEventRho

theorem satEvent_largePrime_ne_of_compatible_ne_admissibleFor_autoCoprime
    (Pz : Nat) (rhoOf : Nat → Nat) (event other : SatEvent)
    (hcompat : satEventCompatible event other)
    (hne : event ≠ other)
    (heventAdm : satEventAdmissibleFor Pz rhoOf event)
    (hotherAdm : satEventAdmissibleFor Pz rhoOf other) :
    event.p ≠ other.p := by
  intro hsamePrime
  exact hne (satEvent_eq_of_compatible_same_largePrime_admissibleFor_autoCoprime
    Pz rhoOf event other hcompat hsamePrime heventAdm hotherAdm)

theorem satEvent_largePrime_ne_of_common_hit_ne_admissibleFor_autoCoprime
    (Pz : Nat) (rhoOf : Nat → Nat) (n : Nat) (event other : SatEvent)
    (heventHit : satEventHit n event)
    (hotherHit : satEventHit n other)
    (hne : event ≠ other)
    (heventAdm : satEventAdmissibleFor Pz rhoOf event)
    (hotherAdm : satEventAdmissibleFor Pz rhoOf other) :
    event.p ≠ other.p := by
  exact satEvent_largePrime_ne_of_compatible_ne_admissibleFor_autoCoprime
    Pz rhoOf event other
    (satEventCompatible_of_common_hit n event other heventHit hotherHit)
    hne heventAdm hotherAdm

theorem appendageCommonDivisor_dvd_medium_of_compatible_events_admissible_autoCoprime
    (Pz rho : Nat) (event : SatEvent) (old : List SatEvent)
    (heventAdm : satEventAdmissible Pz rho event)
    (holdAdm : ∀ other ∈ old, satEventAdmissible Pz rho other)
    (holdDPlusLt : ∀ other ∈ old, other.dPlus < event.p)
    (hcompat : ∀ other ∈ old, satEventCompatible event other)
    (hdistinct : ∀ other ∈ old, event ≠ other) :
    appendageG event.dPlus event.p (residualLcm (satEventRows old)) ∣
      event.dPlus := by
  exact appendageCommonDivisor_dvd_medium_of_compatible_events_admissible
    Pz rho event old
    (satEvent_gcd_four_mul_prime_eq_one_of_admissible Pz rho event heventAdm)
    heventAdm holdAdm holdDPlusLt hcompat hdistinct

theorem appendageCommonDivisor_dvd_medium_of_compatible_events_admissible_of_gt_autoRho
    (Pz rho : Nat) (event : SatEvent) (old : List SatEvent)
    (hlarge : 4 * rho < event.p)
    (heventAdm : satEventAdmissible Pz rho event)
    (holdAdm : ∀ other ∈ old, satEventAdmissible Pz rho other)
    (hcompat : ∀ other ∈ old, satEventCompatible event other)
    (hdistinct : ∀ other ∈ old, event ≠ other) :
    appendageG event.dPlus event.p (residualLcm (satEventRows old)) ∣
      event.dPlus := by
  exact appendageCommonDivisor_dvd_medium_of_compatible_events_admissible_of_gt
    Pz rho event old
    (rho_pos_of_satEventAdmissible Pz rho event heventAdm)
    hlarge heventAdm holdAdm hcompat hdistinct

theorem appendageCommonDivisor_dvd_medium_of_common_hits_admissible_autoRho
    (Pz rho n : Nat) (event : SatEvent) (old : List SatEvent)
    (hlarge : 4 * rho < event.p)
    (heventAdm : satEventAdmissible Pz rho event)
    (holdAdm : ∀ other ∈ old, satEventAdmissible Pz rho other)
    (heventHit : satEventHit n event)
    (holdHit : ∀ other ∈ old, satEventHit n other)
    (hdistinct : ∀ other ∈ old, event ≠ other) :
    appendageG event.dPlus event.p (residualLcm (satEventRows old)) ∣
      event.dPlus := by
  exact appendageCommonDivisor_dvd_medium_of_common_hits_admissible
    Pz rho n event old
    (rho_pos_of_satEventAdmissible Pz rho event heventAdm)
    hlarge heventAdm holdAdm heventHit holdHit hdistinct

theorem appendageCommonDivisor_dvd_medium_of_compatible_events_admissibleFor_autoCoprime
    (Pz : Nat) (rhoOf : Nat → Nat) (event : SatEvent) (old : List SatEvent)
    (heventAdm : satEventAdmissibleFor Pz rhoOf event)
    (holdAdm : ∀ other ∈ old, satEventAdmissibleFor Pz rhoOf other)
    (holdDPlusLt : ∀ other ∈ old, other.dPlus < event.p)
    (hcompat : ∀ other ∈ old, satEventCompatible event other)
    (hdistinct : ∀ other ∈ old, event ≠ other) :
    appendageG event.dPlus event.p (residualLcm (satEventRows old)) ∣
      event.dPlus := by
  have heventAdm' : satEventAdmissible Pz (rhoOf event.e) event := by
    simpa [satEventAdmissibleFor] using heventAdm
  apply appendageCommonDivisor_dvd_medium_of_oldList
  · exact heventAdm'.1
  · intro row hrow
    rcases List.mem_map.mp hrow with ⟨other, hother, hrowEq⟩
    subst hrowEq
    have hotherAdm' : satEventAdmissible Pz (rhoOf other.e) other := by
      simpa [satEventAdmissibleFor] using holdAdm other hother
    exact hotherAdm'.1
  · intro row hrow
    rcases List.mem_map.mp hrow with ⟨other, hother, hrowEq⟩
    subst hrowEq
    have hotherAdm' : satEventAdmissible Pz (rhoOf other.e) other := by
      simpa [satEventAdmissibleFor] using holdAdm other hother
    exact hotherAdm'.2.2.2.2.2.1
  · intro row hrow
    rcases List.mem_map.mp hrow with ⟨other, hother, hrowEq⟩
    subst hrowEq
    exact holdDPlusLt other hother
  · intro row hrow
    rcases List.mem_map.mp hrow with ⟨other, hother, hrowEq⟩
    subst hrowEq
    exact satEvent_largePrime_ne_of_compatible_ne_admissibleFor_autoCoprime
      Pz rhoOf event other (hcompat other hother) (hdistinct other hother)
      heventAdm (holdAdm other hother)

theorem appendageCommonDivisor_dvd_medium_of_common_hits_admissibleFor_autoCoprime
    (Pz : Nat) (rhoOf : Nat → Nat) (n : Nat) (event : SatEvent)
    (old : List SatEvent)
    (heventAdm : satEventAdmissibleFor Pz rhoOf event)
    (holdAdm : ∀ other ∈ old, satEventAdmissibleFor Pz rhoOf other)
    (holdDPlusLt : ∀ other ∈ old, other.dPlus < event.p)
    (heventHit : satEventHit n event)
    (holdHit : ∀ other ∈ old, satEventHit n other)
    (hdistinct : ∀ other ∈ old, event ≠ other) :
    appendageG event.dPlus event.p (residualLcm (satEventRows old)) ∣
      event.dPlus := by
  apply appendageCommonDivisor_dvd_medium_of_compatible_events_admissibleFor_autoCoprime
  · exact heventAdm
  · exact holdAdm
  · exact holdDPlusLt
  · intro other hother
    exact satEventCompatible_of_common_hit n event other heventHit
      (holdHit other hother)
  · exact hdistinct

theorem residualLcm_satEventRows_pos_of_admissible
    (Pz rho : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event) :
    0 < residualLcm (satEventRows events) := by
  apply residualLcm_pos
  intro row hrow
  rcases List.mem_map.mp hrow with ⟨event, hevent, hrowEq⟩
  subst hrowEq
  have hdPlusPos : 0 < event.dPlus :=
    (hadm event hevent).2.2.2.2.2.1
  have hpPos : 0 < event.p := (hadm event hevent).1.pos
  simpa [satEventRow, conditionalModulus] using Nat.mul_pos hdPlusPos hpPos

theorem residualLcm_satEventRows_pos_of_admissibleFor
    (Pz : Nat) (rhoOf : Nat → Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event) :
    0 < residualLcm (satEventRows events) := by
  apply residualLcm_pos
  intro row hrow
  rcases List.mem_map.mp hrow with ⟨event, hevent, hrowEq⟩
  subst hrowEq
  have hadm' : satEventAdmissible Pz (rhoOf event.e) event := by
    simpa [satEventAdmissibleFor] using hadm event hevent
  have hdPlusPos : 0 < event.dPlus := hadm'.2.2.2.2.2.1
  have hpPos : 0 < event.p := hadm'.1.pos
  simpa [satEventRow, conditionalModulus] using Nat.mul_pos hdPlusPos hpPos

theorem residualLcm_satEventRows_cons_recip_le_recip_largePrime_of_compatible_admissible_of_gt
    (Pz rho : Nat) (event : SatEvent) (old : List SatEvent)
    (hlarge : 4 * rho < event.p)
    (heventAdm : satEventAdmissible Pz rho event)
    (holdAdm : ∀ other ∈ old, satEventAdmissible Pz rho other)
    (hcompat : ∀ other ∈ old, satEventCompatible event other)
    (hdistinct : ∀ other ∈ old, event ≠ other) :
    (1 : ℚ) / (residualLcm (satEventRows (event :: old)) : ℚ) ≤
      (1 / (residualLcm (satEventRows old) : ℚ)) * (1 / (event.p : ℚ)) := by
  have hrhoPos : 0 < rho :=
    rho_pos_of_satEventAdmissible Pz rho event heventAdm
  have happend :
      appendageG event.dPlus event.p (residualLcm (satEventRows old)) ∣
        event.dPlus :=
    appendageCommonDivisor_dvd_medium_of_compatible_events_admissible_of_gt
      Pz rho event old hrhoPos hlarge heventAdm holdAdm hcompat hdistinct
  have hL : 0 < residualLcm (satEventRows old) :=
    residualLcm_satEventRows_pos_of_admissible Pz rho old holdAdm
  have hdPlusPos : 0 < event.dPlus := heventAdm.2.2.2.2.2.1
  have hpPos : 0 < event.p := heventAdm.1.pos
  simpa [satEventRows, satEventRow] using
    residualLcm_cons_recip_le_recip_largePrime_of_appendage_dvd
      (satEventRows old) event.dPlus event.p hL hdPlusPos hpPos happend

theorem residualLcm_satEventRows_cons_recip_le_recip_largePrime_of_compatible_admissibleFor
    (Pz : Nat) (rhoOf : Nat → Nat) (event : SatEvent) (old : List SatEvent)
    (heventAdm : satEventAdmissibleFor Pz rhoOf event)
    (holdAdm : ∀ other ∈ old, satEventAdmissibleFor Pz rhoOf other)
    (holdDPlusLt : ∀ other ∈ old, other.dPlus < event.p)
    (hcompat : ∀ other ∈ old, satEventCompatible event other)
    (hdistinct : ∀ other ∈ old, event ≠ other) :
    (1 : ℚ) / (residualLcm (satEventRows (event :: old)) : ℚ) ≤
      (1 / (residualLcm (satEventRows old) : ℚ)) * (1 / (event.p : ℚ)) := by
  have heventAdm' : satEventAdmissible Pz (rhoOf event.e) event := by
    simpa [satEventAdmissibleFor] using heventAdm
  have happend :
      appendageG event.dPlus event.p (residualLcm (satEventRows old)) ∣
        event.dPlus :=
    appendageCommonDivisor_dvd_medium_of_compatible_events_admissibleFor_autoCoprime
      Pz rhoOf event old heventAdm holdAdm holdDPlusLt hcompat hdistinct
  have hL : 0 < residualLcm (satEventRows old) :=
    residualLcm_satEventRows_pos_of_admissibleFor Pz rhoOf old holdAdm
  have hdPlusPos : 0 < event.dPlus := heventAdm'.2.2.2.2.2.1
  have hpPos : 0 < event.p := heventAdm'.1.pos
  simpa [satEventRows, satEventRow] using
    residualLcm_cons_recip_le_recip_largePrime_of_appendage_dvd
      (satEventRows old) event.dPlus event.p hL hdPlusPos hpPos happend

theorem residualLcm_satEventRows_cons_recip_le_recip_largePrime_of_common_hits_admissible
    (Pz rho n : Nat) (event : SatEvent) (old : List SatEvent)
    (hlarge : 4 * rho < event.p)
    (heventAdm : satEventAdmissible Pz rho event)
    (holdAdm : ∀ other ∈ old, satEventAdmissible Pz rho other)
    (heventHit : satEventHit n event)
    (holdHit : ∀ other ∈ old, satEventHit n other)
    (hdistinct : ∀ other ∈ old, event ≠ other) :
    (1 : ℚ) / (residualLcm (satEventRows (event :: old)) : ℚ) ≤
      (1 / (residualLcm (satEventRows old) : ℚ)) * (1 / (event.p : ℚ)) := by
  have hcompat : ∀ other ∈ old, satEventCompatible event other := by
    intro other hother
    exact satEventCompatible_of_common_hit n event other heventHit (holdHit other hother)
  exact
    residualLcm_satEventRows_cons_recip_le_recip_largePrime_of_compatible_admissible_of_gt
      Pz rho event old hlarge heventAdm holdAdm hcompat hdistinct

def satEventOrderedDPlusLtLargePrime : List SatEvent → Prop
  | [] => True
  | event :: old =>
      (∀ other ∈ old, other.dPlus < event.p) ∧
        satEventOrderedDPlusLtLargePrime old

theorem residualLcm_satEventRows_recip_le_primeRecipProduct_of_pairwiseCompatible_admissibleFor_ordered
    (Pz : Nat) (rhoOf : Nat → Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hordered : satEventOrderedDPlusLtLargePrime events)
    (hcompat : ∀ event ∈ events, ∀ other ∈ events,
      event ≠ other → satEventCompatible event other)
    (hnodup : events.Nodup) :
    (1 : ℚ) / (residualLcm (satEventRows events) : ℚ) ≤
      (events.map (fun event => (1 : ℚ) / (event.p : ℚ))).prod := by
  induction events with
  | nil =>
      simp [satEventRows, residualLcm]
  | cons event old ih =>
      have hnodupParts := List.nodup_cons.mp hnodup
      have horderedHead : ∀ other ∈ old, other.dPlus < event.p :=
        hordered.1
      have horderedOld : satEventOrderedDPlusLtLargePrime old :=
        hordered.2
      have heventAdm : satEventAdmissibleFor Pz rhoOf event :=
        hadm event (by simp)
      have holdAdm : ∀ other ∈ old, satEventAdmissibleFor Pz rhoOf other := by
        intro other hother
        exact hadm other (by simp [hother])
      have hcompatHead : ∀ other ∈ old, satEventCompatible event other := by
        intro other hother
        exact hcompat event (by simp) other (by simp [hother])
          (by
            intro heq
            exact hnodupParts.1 (by simpa [heq] using hother))
      have hdistinctHead : ∀ other ∈ old, event ≠ other := by
        intro other hother heq
        exact hnodupParts.1 (by simpa [heq] using hother)
      have hstep :
          (1 : ℚ) / (residualLcm (satEventRows (event :: old)) : ℚ) ≤
            (1 / (residualLcm (satEventRows old) : ℚ)) *
              (1 / (event.p : ℚ)) :=
        residualLcm_satEventRows_cons_recip_le_recip_largePrime_of_compatible_admissibleFor
          Pz rhoOf event old heventAdm holdAdm horderedHead hcompatHead
          hdistinctHead
      have hih :
          (1 : ℚ) / (residualLcm (satEventRows old) : ℚ) ≤
            (old.map (fun event => (1 : ℚ) / (event.p : ℚ))).prod :=
        ih holdAdm horderedOld
          (by
            intro other hother other' hother' hne
            exact hcompat other (by simp [hother]) other' (by simp [hother'])
              hne)
          hnodupParts.2
      have hpInvNonneg : 0 ≤ (1 : ℚ) / (event.p : ℚ) := by
        exact div_nonneg zero_le_one (by exact_mod_cast Nat.zero_le event.p)
      have hmul :
          (1 / (residualLcm (satEventRows old) : ℚ)) *
              (1 / (event.p : ℚ)) ≤
            (old.map (fun event => (1 : ℚ) / (event.p : ℚ))).prod *
              (1 / (event.p : ℚ)) :=
        mul_le_mul_of_nonneg_right hih hpInvNonneg
      calc
        (1 : ℚ) / (residualLcm (satEventRows (event :: old)) : ℚ) ≤
            (1 / (residualLcm (satEventRows old) : ℚ)) *
              (1 / (event.p : ℚ)) := hstep
        _ ≤ (old.map (fun event => (1 : ℚ) / (event.p : ℚ))).prod *
              (1 / (event.p : ℚ)) := hmul
        _ = ((event :: old).map
              (fun event => (1 : ℚ) / (event.p : ℚ))).prod := by
            simp [mul_comm, mul_left_comm, mul_assoc]

theorem residualLcm_satEventRows_recip_le_primeRecipProduct_of_common_hits_admissibleFor_ordered
    (Pz : Nat) (rhoOf : Nat → Nat) (n : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hordered : satEventOrderedDPlusLtLargePrime events)
    (hhit : ∀ event ∈ events, satEventHit n event)
    (hnodup : events.Nodup) :
    (1 : ℚ) / (residualLcm (satEventRows events) : ℚ) ≤
      (events.map (fun event => (1 : ℚ) / (event.p : ℚ))).prod :=
  residualLcm_satEventRows_recip_le_primeRecipProduct_of_pairwiseCompatible_admissibleFor_ordered
    Pz rhoOf events hadm hordered
    (by
      intro event hevent other hother hne
      exact satEventCompatible_of_common_hit n event other
        (hhit event hevent) (hhit other hother))
    hnodup

theorem residualLcm_satEventRows_recip_le_primeRecipProduct_of_pairwiseCompatible_admissible_of_gt
    (Pz rho : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hlarge : ∀ event ∈ events, 4 * rho < event.p)
    (hcompat : ∀ event ∈ events, ∀ other ∈ events,
      event ≠ other → satEventCompatible event other)
    (hnodup : events.Nodup) :
    (1 : ℚ) / (residualLcm (satEventRows events) : ℚ) ≤
      (events.map (fun event => (1 : ℚ) / (event.p : ℚ))).prod := by
  induction events with
  | nil =>
      simp [satEventRows, residualLcm]
  | cons event old ih =>
      have hnodupParts := List.nodup_cons.mp hnodup
      have heventAdm : satEventAdmissible Pz rho event :=
        hadm event (by simp)
      have holdAdm : ∀ other ∈ old, satEventAdmissible Pz rho other := by
        intro other hother
        exact hadm other (by simp [hother])
      have heventLarge : 4 * rho < event.p :=
        hlarge event (by simp)
      have hcompatHead : ∀ other ∈ old, satEventCompatible event other := by
        intro other hother
        exact hcompat event (by simp) other (by simp [hother])
          (by
            intro heq
            exact hnodupParts.1 (by simpa [heq] using hother))
      have hdistinctHead : ∀ other ∈ old, event ≠ other := by
        intro other hother heq
        exact hnodupParts.1 (by simpa [heq] using hother)
      have hstep :
          (1 : ℚ) / (residualLcm (satEventRows (event :: old)) : ℚ) ≤
            (1 / (residualLcm (satEventRows old) : ℚ)) *
              (1 / (event.p : ℚ)) :=
        residualLcm_satEventRows_cons_recip_le_recip_largePrime_of_compatible_admissible_of_gt
          Pz rho event old heventLarge heventAdm holdAdm hcompatHead hdistinctHead
      have hih :
          (1 : ℚ) / (residualLcm (satEventRows old) : ℚ) ≤
            (old.map (fun event => (1 : ℚ) / (event.p : ℚ))).prod :=
        ih holdAdm
          (by
            intro other hother
            exact hlarge other (by simp [hother]))
          (by
            intro other hother other' hother' hne
            exact hcompat other (by simp [hother]) other' (by simp [hother'])
              hne)
          hnodupParts.2
      have hpInvNonneg : 0 ≤ (1 : ℚ) / (event.p : ℚ) := by
        exact div_nonneg zero_le_one (by exact_mod_cast Nat.zero_le event.p)
      have hmul :
          (1 / (residualLcm (satEventRows old) : ℚ)) *
              (1 / (event.p : ℚ)) ≤
            (old.map (fun event => (1 : ℚ) / (event.p : ℚ))).prod *
              (1 / (event.p : ℚ)) :=
        mul_le_mul_of_nonneg_right hih hpInvNonneg
      calc
        (1 : ℚ) / (residualLcm (satEventRows (event :: old)) : ℚ) ≤
            (1 / (residualLcm (satEventRows old) : ℚ)) *
              (1 / (event.p : ℚ)) := hstep
        _ ≤ (old.map (fun event => (1 : ℚ) / (event.p : ℚ))).prod *
              (1 / (event.p : ℚ)) := hmul
        _ = ((event :: old).map (fun event => (1 : ℚ) / (event.p : ℚ))).prod := by
              simp [mul_comm, mul_left_comm, mul_assoc]

theorem residualLcm_satEventRows_recip_le_primeRecipProduct_of_common_hits_admissible
    (Pz rho n : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hlarge : ∀ event ∈ events, 4 * rho < event.p)
    (hhit : ∀ event ∈ events, satEventHit n event)
    (hnodup : events.Nodup) :
    (1 : ℚ) / (residualLcm (satEventRows events) : ℚ) ≤
      (events.map (fun event => (1 : ℚ) / (event.p : ℚ))).prod := by
  exact
    residualLcm_satEventRows_recip_le_primeRecipProduct_of_pairwiseCompatible_admissible_of_gt
      Pz rho events hadm hlarge
      (by
        intro event hevent other hother _hne
        exact satEventCompatible_of_common_hit n event other
          (hhit event hevent) (hhit other hother))
      hnodup

theorem residualLcm_satEventRows_toList_recip_le_primeRecipProduct_of_pairwiseCompatible_admissible_of_gt
    (Pz rho : Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hlarge : ∀ event ∈ events, 4 * rho < event.p)
    (hcompat : ∀ event ∈ events, ∀ other ∈ events,
      event ≠ other → satEventCompatible event other) :
    (1 : ℚ) / (residualLcm (satEventRows events.toList) : ℚ) ≤
      ∏ event ∈ events, (1 : ℚ) / (event.p : ℚ) := by
  classical
  have hlist :
      (1 : ℚ) / (residualLcm (satEventRows events.toList) : ℚ) ≤
        (events.toList.map (fun event => (1 : ℚ) / (event.p : ℚ))).prod :=
    residualLcm_satEventRows_recip_le_primeRecipProduct_of_pairwiseCompatible_admissible_of_gt
      Pz rho events.toList
      (by
        intro event hevent
        exact hadm event (by simpa using hevent))
      (by
        intro event hevent
        exact hlarge event (by simpa using hevent))
      (by
        intro event hevent other hother hne
        exact hcompat event (by simpa using hevent) other (by simpa using hother) hne)
      events.nodup_toList
  simpa using hlist

theorem residualLcm_satEventRows_toList_recip_le_primeRecipProduct_of_common_hits_admissible
    (Pz rho n : Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hlarge : ∀ event ∈ events, 4 * rho < event.p)
    (hhit : ∀ event ∈ events, satEventHit n event) :
    (1 : ℚ) / (residualLcm (satEventRows events.toList) : ℚ) ≤
      ∏ event ∈ events, (1 : ℚ) / (event.p : ℚ) := by
  exact
    residualLcm_satEventRows_toList_recip_le_primeRecipProduct_of_pairwiseCompatible_admissible_of_gt
      Pz rho events hadm hlarge
      (by
        intro event hevent other hother _hne
        exact satEventCompatible_of_common_hit n event other
          (hhit event hevent) (hhit other hother))

theorem congruenceLcm_satEventShiftedResidualRows_eq_residualLcm_satEventRows
    (events : List SatEvent) :
    congruenceLcm (satEventShiftedResidualRows events) =
      residualLcm (satEventRows events) := by
  induction events with
  | nil =>
      simp [satEventShiftedResidualRows, satEventRows, congruenceLcm, residualLcm]
  | cons event rest ih =>
      simpa [satEventShiftedResidualRows, satEventRows, satEventShiftedResidualRow,
        satEventRow, congruenceLcm, residualLcm, conditionalModulus] using
        congrArg (fun L => Nat.lcm (event.dPlus * event.p) L) ih

theorem congruenceLcm_satEventShiftedResidualRows_recip_le_primeRecipProduct_of_pairwiseCompatible_admissible_of_gt
    (Pz rho : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hlarge : ∀ event ∈ events, 4 * rho < event.p)
    (hcompat : ∀ event ∈ events, ∀ other ∈ events,
      event ≠ other → satEventCompatible event other)
    (hnodup : events.Nodup) :
    (1 : ℚ) / (congruenceLcm (satEventShiftedResidualRows events) : ℚ) ≤
      (events.map (fun event => (1 : ℚ) / (event.p : ℚ))).prod := by
  rw [congruenceLcm_satEventShiftedResidualRows_eq_residualLcm_satEventRows]
  exact
    residualLcm_satEventRows_recip_le_primeRecipProduct_of_pairwiseCompatible_admissible_of_gt
      Pz rho events hadm hlarge hcompat hnodup

theorem congruenceLcm_satEventShiftedResidualRows_recip_le_primeRecipProduct_of_common_hits_admissible
    (Pz rho n : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hlarge : ∀ event ∈ events, 4 * rho < event.p)
    (hhit : ∀ event ∈ events, satEventHit n event)
    (hnodup : events.Nodup) :
    (1 : ℚ) / (congruenceLcm (satEventShiftedResidualRows events) : ℚ) ≤
      (events.map (fun event => (1 : ℚ) / (event.p : ℚ))).prod := by
  rw [congruenceLcm_satEventShiftedResidualRows_eq_residualLcm_satEventRows]
  exact
    residualLcm_satEventRows_recip_le_primeRecipProduct_of_common_hits_admissible
      Pz rho n events hadm hlarge hhit hnodup

theorem congruenceLcm_satEventShiftedResidualRows_toList_recip_le_primeRecipProduct_of_pairwiseCompatible_admissible_of_gt
    (Pz rho : Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hlarge : ∀ event ∈ events, 4 * rho < event.p)
    (hcompat : ∀ event ∈ events, ∀ other ∈ events,
      event ≠ other → satEventCompatible event other) :
    (1 : ℚ) / (congruenceLcm (satEventShiftedResidualRows events.toList) : ℚ) ≤
      ∏ event ∈ events, (1 : ℚ) / (event.p : ℚ) := by
  rw [congruenceLcm_satEventShiftedResidualRows_eq_residualLcm_satEventRows]
  exact
    residualLcm_satEventRows_toList_recip_le_primeRecipProduct_of_pairwiseCompatible_admissible_of_gt
      Pz rho events hadm hlarge hcompat

theorem congruenceLcm_satEventShiftedResidualRows_toList_recip_le_primeRecipProduct_of_common_hits_admissible
    (Pz rho n : Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hlarge : ∀ event ∈ events, 4 * rho < event.p)
    (hhit : ∀ event ∈ events, satEventHit n event) :
    (1 : ℚ) / (congruenceLcm (satEventShiftedResidualRows events.toList) : ℚ) ≤
      ∏ event ∈ events, (1 : ℚ) / (event.p : ℚ) := by
  rw [congruenceLcm_satEventShiftedResidualRows_eq_residualLcm_satEventRows]
  exact
    residualLcm_satEventRows_toList_recip_le_primeRecipProduct_of_common_hits_admissible
      Pz rho n events hadm hlarge hhit

theorem congruenceLcm_satEventResidualHitRows_eq_residualLcm_satEventRows
    (events : List SatEvent) :
    congruenceLcm (satEventResidualHitRows events) =
      residualLcm (satEventRows events) := by
  induction events with
  | nil =>
      simp [satEventResidualHitRows, satEventRows, congruenceLcm, residualLcm]
  | cons event rest ih =>
      simpa [satEventResidualHitRows, satEventRows, satEventResidualHitRow,
        satEventRow, congruenceLcm, residualLcm, conditionalModulus] using
        congrArg (fun L => Nat.lcm (event.dPlus * event.p) L) ih

theorem congruenceLcm_satEventResidualHitRows_recip_le_primeRecipProduct_of_pairwiseCompatible_admissible_of_gt
    (Pz rho : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hlarge : ∀ event ∈ events, 4 * rho < event.p)
    (hcompat : ∀ event ∈ events, ∀ other ∈ events,
      event ≠ other → satEventCompatible event other)
    (hnodup : events.Nodup) :
    (1 : ℚ) / (congruenceLcm (satEventResidualHitRows events) : ℚ) ≤
      (events.map (fun event => (1 : ℚ) / (event.p : ℚ))).prod := by
  rw [congruenceLcm_satEventResidualHitRows_eq_residualLcm_satEventRows]
  exact
    residualLcm_satEventRows_recip_le_primeRecipProduct_of_pairwiseCompatible_admissible_of_gt
      Pz rho events hadm hlarge hcompat hnodup

theorem congruenceLcm_satEventResidualHitRows_recip_le_primeRecipProduct_of_common_hits_admissible
    (Pz rho n : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hlarge : ∀ event ∈ events, 4 * rho < event.p)
    (hhit : ∀ event ∈ events, satEventHit n event)
    (hnodup : events.Nodup) :
    (1 : ℚ) / (congruenceLcm (satEventResidualHitRows events) : ℚ) ≤
      (events.map (fun event => (1 : ℚ) / (event.p : ℚ))).prod := by
  rw [congruenceLcm_satEventResidualHitRows_eq_residualLcm_satEventRows]
  exact
    residualLcm_satEventRows_recip_le_primeRecipProduct_of_common_hits_admissible
      Pz rho n events hadm hlarge hhit hnodup

theorem congruenceLcm_satEventResidualHitRows_recip_le_primeRecipProduct_of_pairwiseCompatible_admissibleFor_ordered
    (Pz : Nat) (rhoOf : Nat → Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hordered : satEventOrderedDPlusLtLargePrime events)
    (hcompat : ∀ event ∈ events, ∀ other ∈ events,
      event ≠ other → satEventCompatible event other)
    (hnodup : events.Nodup) :
    (1 : ℚ) / (congruenceLcm (satEventResidualHitRows events) : ℚ) ≤
      (events.map (fun event => (1 : ℚ) / (event.p : ℚ))).prod := by
  rw [congruenceLcm_satEventResidualHitRows_eq_residualLcm_satEventRows]
  exact
    residualLcm_satEventRows_recip_le_primeRecipProduct_of_pairwiseCompatible_admissibleFor_ordered
      Pz rhoOf events hadm hordered hcompat hnodup

theorem congruenceLcm_satEventResidualHitRows_recip_le_primeRecipProduct_of_common_hits_admissibleFor_ordered
    (Pz : Nat) (rhoOf : Nat → Nat) (n : Nat) (events : List SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hordered : satEventOrderedDPlusLtLargePrime events)
    (hhit : ∀ event ∈ events, satEventHit n event)
    (hnodup : events.Nodup) :
    (1 : ℚ) / (congruenceLcm (satEventResidualHitRows events) : ℚ) ≤
      (events.map (fun event => (1 : ℚ) / (event.p : ℚ))).prod := by
  rw [congruenceLcm_satEventResidualHitRows_eq_residualLcm_satEventRows]
  exact
    residualLcm_satEventRows_recip_le_primeRecipProduct_of_common_hits_admissibleFor_ordered
      Pz rhoOf n events hadm hordered hhit hnodup

theorem congruenceLcm_satEventResidualHitRows_toList_recip_le_primeRecipProduct_of_pairwiseCompatible_admissible_of_gt
    (Pz rho : Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hlarge : ∀ event ∈ events, 4 * rho < event.p)
    (hcompat : ∀ event ∈ events, ∀ other ∈ events,
      event ≠ other → satEventCompatible event other) :
    (1 : ℚ) / (congruenceLcm (satEventResidualHitRows events.toList) : ℚ) ≤
      ∏ event ∈ events, (1 : ℚ) / (event.p : ℚ) := by
  rw [congruenceLcm_satEventResidualHitRows_eq_residualLcm_satEventRows]
  exact
    residualLcm_satEventRows_toList_recip_le_primeRecipProduct_of_pairwiseCompatible_admissible_of_gt
      Pz rho events hadm hlarge hcompat

theorem congruenceLcm_satEventResidualHitRows_toList_recip_le_primeRecipProduct_of_common_hits_admissible
    (Pz rho n : Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hlarge : ∀ event ∈ events, 4 * rho < event.p)
    (hhit : ∀ event ∈ events, satEventHit n event) :
    (1 : ℚ) / (congruenceLcm (satEventResidualHitRows events.toList) : ℚ) ≤
      ∏ event ∈ events, (1 : ℚ) / (event.p : ℚ) := by
  rw [congruenceLcm_satEventResidualHitRows_eq_residualLcm_satEventRows]
  exact
    residualLcm_satEventRows_toList_recip_le_primeRecipProduct_of_common_hits_admissible
      Pz rho n events hadm hlarge hhit

/-- Weighted deletion double count.  Every eligible rank-`r` subset is counted
once for each of its `r` elements; deleting the distinguished element gives an
eligible rank-`r-1` subset together with an admissible extension, and insertion
is the inverse map. -/
theorem weighted_subset_deletion_sum
    {α : Type*} [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) (f : Finset α → ℚ)
    [DecidablePred P]
    (r : Nat) (hr : 0 < r)
    (hPerase : ∀ T, P T → ∀ i ∈ T, P (T.erase i)) :
    (r : ℚ) * (∑ T ∈ (U.powersetCard r).filter P, f T) =
      ∑ S ∈ (U.powersetCard (r - 1)).filter P,
        ∑ i ∈ U.filter (fun i => i ∉ S ∧ P (insert i S)), f (insert i S) := by
  classical
  let large : Finset (Finset α) := (U.powersetCard r).filter P
  let small : Finset (Finset α) := (U.powersetCard (r - 1)).filter P
  let extensions : Finset α → Finset α :=
    fun S => U.filter (fun i => i ∉ S ∧ P (insert i S))
  let domain : Finset (Σ _T : Finset α, α) := large.sigma fun T => T
  let codomain : Finset (Σ _S : Finset α, α) := small.sigma extensions
  have hleft :
      (r : ℚ) * (∑ T ∈ large, f T) =
        ∑ T ∈ large, ∑ _i ∈ T, f T := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    have hcard : T.card = r :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
    simp [hcard]
  rw [show (U.powersetCard r).filter P = large from rfl,
    show (U.powersetCard (r - 1)).filter P = small from rfl]
  change (r : ℚ) * (∑ T ∈ large, f T) =
    ∑ S ∈ small, ∑ i ∈ extensions S, f (insert i S)
  rw [hleft]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  change (∑ x ∈ domain, f x.1) =
    ∑ y ∈ codomain, f (insert y.2 y.1)
  refine Finset.sum_bij'
    (fun x _hx => ⟨x.1.erase x.2, x.2⟩)
    (fun y _hy => ⟨insert y.2 y.1, y.2⟩) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨hT, hiT⟩
    apply Finset.mem_sigma.mpr
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_powersetCard.mpr
        have hTU : x.1 ⊆ U :=
          (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).1
        have hcardT : x.1.card = r :=
          (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
        constructor
        · exact (Finset.erase_subset _ _).trans hTU
        · rw [Finset.card_erase_of_mem hiT, hcardT]
      · exact hPerase x.1 (Finset.mem_filter.mp hT).2 x.2 hiT
    · apply Finset.mem_filter.mpr
      constructor
      · exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).1 hiT
      · constructor
        · exact Finset.not_mem_erase x.2 x.1
        · simpa [Finset.insert_erase hiT] using (Finset.mem_filter.mp hT).2
  · intro y hy
    rcases Finset.mem_sigma.mp hy with ⟨hS, hiExt⟩
    have hiData := Finset.mem_filter.mp hiExt
    apply Finset.mem_sigma.mpr
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_powersetCard.mpr
        have hSU : y.1 ⊆ U :=
          (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).1
        have hcardS : y.1.card = r - 1 :=
          (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).2
        constructor
        · exact Finset.insert_subset hiData.1 hSU
        · rw [Finset.card_insert_of_not_mem hiData.2.1, hcardS]
          omega
      · exact hiData.2.2
    · exact Finset.mem_insert_self _ _
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨_hT, hiT⟩
    apply Sigma.ext
    · exact Finset.insert_erase hiT
    · simp
  · intro y hy
    rcases Finset.mem_sigma.mp hy with ⟨_hS, hiExt⟩
    have hnot := (Finset.mem_filter.mp hiExt).2.1
    apply Sigma.ext
    · exact Finset.erase_insert hnot
    · simp
  · intro x hx
    have hiT := (Finset.mem_sigma.mp hx).2
    simp [Finset.insert_erase hiT]

theorem brun_recurrence_iterated_bound
    (F : Nat → ℚ) (M : ℚ)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hrec : ∀ r : Nat, 1 ≤ r →
      F r ≤ (M / (r : ℚ)) * F (r - 1)) :
    ∀ r : Nat, F r ≤ M ^ r / (Nat.factorial r : ℚ) := by
  intro r
  induction r with
  | zero =>
      simpa using hF0
  | succ r ih =>
      have hstep : F (r + 1) ≤
          (M / ((r + 1 : Nat) : ℚ)) * F ((r + 1) - 1) :=
        hrec (r + 1) (Nat.succ_le_succ (Nat.zero_le r))
      have hcoef : 0 ≤ M / ((r + 1 : Nat) : ℚ) := by
        exact div_nonneg hM (by positivity)
      have hmul :
          (M / ((r + 1 : Nat) : ℚ)) * F r ≤
            (M / ((r + 1 : Nat) : ℚ)) *
              (M ^ r / (Nat.factorial r : ℚ)) := by
        exact mul_le_mul_of_nonneg_left ih hcoef
      calc
        F (r + 1) ≤ (M / ((r + 1 : Nat) : ℚ)) * F ((r + 1) - 1) := hstep
        _ = (M / ((r + 1 : Nat) : ℚ)) * F r := by simp
        _ ≤ (M / ((r + 1 : Nat) : ℚ)) *
              (M ^ r / (Nat.factorial r : ℚ)) := hmul
        _ = M ^ (r + 1) / (Nat.factorial (r + 1) : ℚ) := by
          have hrpos : ((r + 1 : Nat) : ℚ) ≠ 0 := by positivity
          have hfactpos : (Nat.factorial r : ℚ) ≠ 0 := by positivity
          field_simp [Nat.factorial_succ, hrpos, hfactpos, pow_succ]
          ring

theorem brun_recurrence_iterated_bound_from_mul
    (F : Nat → ℚ) (M : ℚ)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * F r ≤ M * F (r - 1)) :
    ∀ r : Nat, F r ≤ M ^ r / (Nat.factorial r : ℚ) := by
  apply brun_recurrence_iterated_bound F M hM hF0
  intro r hr
  have hrpos : 0 < (r : ℚ) := by exact_mod_cast hr
  have hstep := hrec r hr
  have hrne : (r : ℚ) ≠ 0 := ne_of_gt hrpos
  have hdiv : F r ≤ (M * F (r - 1)) / (r : ℚ) := by
    rw [le_div_iff₀ hrpos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hstep
  calc
    F r ≤ (M * F (r - 1)) / (r : ℚ) := hdiv
    _ = (M / (r : ℚ)) * F (r - 1) := by
      field_simp [hrne]

theorem finite_error_sum_le_factorial_series
    (F : Nat → ℚ) (X M : ℚ) (m : Nat)
    (hX : 0 ≤ X)
    (hF : ∀ r : Nat, r ≤ m → F r ≤ M ^ r / (Nat.factorial r : ℚ)) :
    (∑ r ∈ Finset.range (m + 1), X ^ r * F r) ≤
      ∑ r ∈ Finset.range (m + 1), (X * M) ^ r / (Nat.factorial r : ℚ) := by
  classical
  apply Finset.sum_le_sum
  intro r hr
  have hrle : r ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  have hxpow : 0 ≤ X ^ r := pow_nonneg hX r
  have hterm :
      X ^ r * F r ≤ X ^ r * (M ^ r / (Nat.factorial r : ℚ)) := by
    exact mul_le_mul_of_nonneg_left (hF r hrle) hxpow
  calc
    X ^ r * F r ≤ X ^ r * (M ^ r / (Nat.factorial r : ℚ)) := hterm
    _ = (X * M) ^ r / (Nat.factorial r : ℚ) := by
      rw [mul_pow]
      ring

theorem finite_error_sum_le_factorial_series_from_brun
    (F : Nat → ℚ) (X M : ℚ) (m : Nat)
    (hX : 0 ≤ X)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * F r ≤ M * F (r - 1)) :
    (∑ r ∈ Finset.range (m + 1), X ^ r * F r) ≤
      ∑ r ∈ Finset.range (m + 1), (X * M) ^ r / (Nat.factorial r : ℚ) := by
  exact finite_error_sum_le_factorial_series F X M m hX
    (fun r _hr => brun_recurrence_iterated_bound_from_mul F M hM hF0 hrec r)

theorem negOnePow_le_one_rat (r : Nat) : (-1 : ℚ) ^ r ≤ 1 := by
  rcases neg_one_pow_eq_or ℚ r with h | h <;> simp [h]

theorem negOnePow_mul_le_of_nonneg_rat (r : Nat) (a : ℚ) (ha : 0 ≤ a) :
    ((-1 : ℚ) ^ r) * a ≤ a := by
  calc
    (-1 : ℚ) ^ r * a ≤ 1 * a :=
      mul_le_mul_of_nonneg_right (negOnePow_le_one_rat r) ha
    _ = a := one_mul a

theorem brun_signed_sum_le_partial_exp
    (F : Nat → ℚ) (M : ℚ) (m : Nat)
    (hM : 0 ≤ M) (hF0 : F 0 ≤ 1)
    (hFnonneg : ∀ r : Nat, 0 ≤ F r)
    (hrec : ∀ r : Nat, 1 ≤ r → (r : ℚ) * F r ≤ M * F (r - 1)) :
    (∑ r ∈ Finset.range (m + 1), ((-1 : ℚ) ^ r) * F r) ≤
      ∑ r ∈ Finset.range (m + 1), M ^ r / (Nat.factorial r : ℚ) := by
  have hbrun := brun_recurrence_iterated_bound_from_mul F M hM hF0 hrec
  calc
    ∑ r ∈ Finset.range (m + 1), ((-1 : ℚ) ^ r) * F r
        ≤ ∑ r ∈ Finset.range (m + 1), F r := by
          apply Finset.sum_le_sum
          intro r _hr
          exact negOnePow_mul_le_of_nonneg_rat r (F r) (hFnonneg r)
    _ ≤ ∑ r ∈ Finset.range (m + 1), M ^ r / (Nat.factorial r : ℚ) := by
          apply Finset.sum_le_sum
          intro r _hr
          exact hbrun r

theorem brun_bonferroni_sum_le_partial_exp
    (F : Nat → ℚ) (M : ℚ) (R : Nat)
    (hM : 0 ≤ M) (hF0 : F 0 ≤ 1)
    (hFnonneg : ∀ r : Nat, 0 ≤ F r)
    (hrec : ∀ r : Nat, 1 ≤ r → (r : ℚ) * F r ≤ M * F (r - 1)) :
    (∑ r ∈ Finset.range (2 * R + 1), ((-1 : ℚ) ^ r) * F r) ≤
      ∑ r ∈ Finset.range (2 * R + 1), M ^ r / (Nat.factorial r : ℚ) :=
  brun_signed_sum_le_partial_exp F M (2 * R) hM hF0 hFnonneg hrec

theorem brun_signed_weighted_sum_le_partial_exp
    (F : Nat → ℚ) (X M : ℚ) (m : Nat)
    (hX : 0 ≤ X) (hM : 0 ≤ M) (hF0 : F 0 ≤ 1)
    (hFnonneg : ∀ r : Nat, 0 ≤ F r)
    (hrec : ∀ r : Nat, 1 ≤ r → (r : ℚ) * F r ≤ M * F (r - 1)) :
    (∑ r ∈ Finset.range (m + 1), ((-1 : ℚ) ^ r) * X ^ r * F r) ≤
      ∑ r ∈ Finset.range (m + 1), (X * M) ^ r / (Nat.factorial r : ℚ) := by
  calc
    ∑ r ∈ Finset.range (m + 1), (-1 : ℚ) ^ r * X ^ r * F r
        ≤ ∑ r ∈ Finset.range (m + 1), X ^ r * F r := by
          apply Finset.sum_le_sum
          intro r _hr
          rw [mul_assoc]
          exact negOnePow_mul_le_of_nonneg_rat r (X ^ r * F r)
            (mul_nonneg (pow_nonneg hX r) (hFnonneg r))
    _ ≤ ∑ r ∈ Finset.range (m + 1), (X * M) ^ r / (Nat.factorial r : ℚ) :=
          finite_error_sum_le_factorial_series_from_brun F X M m hX hM hF0 hrec

theorem finite_weighted_sum_le_top_power_mul_sum
    (F : Nat → ℚ) (X : ℚ) (m : Nat)
    (hX : 1 ≤ X)
    (hFnonneg : ∀ r : Nat, r ≤ m → 0 ≤ F r) :
    (∑ r ∈ Finset.range (m + 1), X ^ r * F r) ≤
      X ^ m * ∑ r ∈ Finset.range (m + 1), F r := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hrle : r ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  have hpow : X ^ r ≤ X ^ m := pow_le_pow_right₀ hX hrle
  exact mul_le_mul_of_nonneg_right hpow (hFnonneg r hrle)

theorem finite_error_sum_le_top_power_factorial_series_from_brun
    (F : Nat → ℚ) (X M : ℚ) (m : Nat)
    (hX : 1 ≤ X)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hFnonneg : ∀ r : Nat, r ≤ m → 0 ≤ F r)
    (hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * F r ≤ M * F (r - 1)) :
    (∑ r ∈ Finset.range (m + 1), X ^ r * F r) ≤
      X ^ m * ∑ r ∈ Finset.range (m + 1),
        M ^ r / (Nat.factorial r : ℚ) := by
  classical
  have htop := finite_weighted_sum_le_top_power_mul_sum F X m hX hFnonneg
  have hbound : ∀ r : Nat, F r ≤ M ^ r / (Nat.factorial r : ℚ) :=
    brun_recurrence_iterated_bound_from_mul F M hM hF0 hrec
  have hsum :
      (∑ r ∈ Finset.range (m + 1), F r) ≤
        ∑ r ∈ Finset.range (m + 1), M ^ r / (Nat.factorial r : ℚ) := by
    apply Finset.sum_le_sum
    intro r _hr
    exact hbound r
  have hXnonneg : 0 ≤ X := by linarith
  have hpowNonneg : 0 ≤ X ^ m := pow_nonneg hXnonneg m
  calc
    (∑ r ∈ Finset.range (m + 1), X ^ r * F r) ≤
        X ^ m * ∑ r ∈ Finset.range (m + 1), F r := htop
    _ ≤ X ^ m * ∑ r ∈ Finset.range (m + 1),
        M ^ r / (Nat.factorial r : ℚ) :=
          mul_le_mul_of_nonneg_left hsum hpowNonneg

noncomputable def elemSymmList : List ℚ → Nat → ℚ
  | _, 0 => 1
  | [], (_ + 1) => 0
  | x :: xs, (r + 1) => elemSymmList xs (r + 1) + x * elemSymmList xs r

@[simp]
theorem elemSymmList_zero (xs : List ℚ) : elemSymmList xs 0 = 1 := by
  cases xs <;> rfl

@[simp]
theorem elemSymmList_nil_succ (r : Nat) : elemSymmList [] (r + 1) = 0 := rfl

theorem elemSymmList_cons_succ (x : ℚ) (xs : List ℚ) (r : Nat) :
    elemSymmList (x :: xs) (r + 1) =
      elemSymmList xs (r + 1) + x * elemSymmList xs r := rfl

theorem elemSymmList_nonneg (xs : List ℚ) (r : Nat)
    (hnn : ∀ x ∈ xs, 0 ≤ x) :
    0 ≤ elemSymmList xs r := by
  induction xs generalizing r with
  | nil =>
      cases r <;> simp
  | cons x xs ih =>
      cases r with
      | zero => simp
      | succ r =>
          rw [elemSymmList_cons_succ]
          have hnnTail : ∀ y ∈ xs, 0 ≤ y :=
            fun y hy => hnn y (List.mem_cons_of_mem x hy)
          exact add_nonneg (ih (r + 1) hnnTail)
            (mul_nonneg (hnn x (List.mem_cons_self x xs))
              (ih r hnnTail))

theorem elemSymmList_one (xs : List ℚ) :
    elemSymmList xs 1 = xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [elemSymmList_cons_succ, ih, elemSymmList_zero, mul_one,
        List.sum_cons, add_comm]

theorem newton_ineq_elemSymmList
    (xs : List ℚ) (r : Nat) (hr : 1 ≤ r)
    (hnn : ∀ x ∈ xs, 0 ≤ x) :
    (r : ℚ) * elemSymmList xs r ≤ xs.sum * elemSymmList xs (r - 1) := by
  induction xs generalizing r with
  | nil =>
      cases r with
      | zero => omega
      | succ r => simp
  | cons x xs ih =>
      have hx : 0 ≤ x := hnn x (List.mem_cons_self x xs)
      have hnnTail : ∀ y ∈ xs, 0 ≤ y :=
        fun y hy => hnn y (List.mem_cons_of_mem x hy)
      rcases r with _ | r
      · omega
      rcases r with _ | r'
      · simp [elemSymmList_cons_succ, elemSymmList_one, List.sum_cons]
      · rw [show (r' + 2 : Nat) - 1 = r' + 1 from by omega]
        rw [elemSymmList_cons_succ x xs (r' + 1)]
        rw [elemSymmList_cons_succ x xs r']
        rw [List.sum_cons]
        set A2 := elemSymmList xs (r' + 2) with hA2
        set A1 := elemSymmList xs (r' + 1) with hA1
        set A0 := elemSymmList xs r' with hA0
        set S := xs.sum with hS
        have hih1 : ((r' + 2 : Nat) : ℚ) * A2 ≤ S * A1 := by
          have h := ih (r' + 2) (by omega) hnnTail
          simpa [hA2, hA1, hS] using h
        have hih2 : ((r' + 1 : Nat) : ℚ) * A1 ≤ S * A0 := by
          have h := ih (r' + 1) (by omega) hnnTail
          simpa [hA1, hA0, hS] using h
        have he0 : 0 ≤ A0 := by
          simpa [hA0] using elemSymmList_nonneg xs r' hnnTail
        suffices hdiff : 0 ≤
            (x + S) * (A1 + x * A0) -
              ((r' + 2 : Nat) : ℚ) * (A2 + x * A1) by
          linarith
        have hdecomp :
            (x + S) * (A1 + x * A0) -
              ((r' + 2 : Nat) : ℚ) * (A2 + x * A1)
            =
              (S * A1 - ((r' + 2 : Nat) : ℚ) * A2)
              + x * (S * A0 - ((r' + 1 : Nat) : ℚ) * A1)
              + x * x * A0 := by
          push_cast
          ring
        rw [hdecomp]
        have t1 : 0 ≤ S * A1 - ((r' + 2 : Nat) : ℚ) * A2 :=
          sub_nonneg.mpr hih1
        have t2 : 0 ≤ x * (S * A0 - ((r' + 1 : Nat) : ℚ) * A1) :=
          mul_nonneg hx (sub_nonneg.mpr hih2)
        have t3 : 0 ≤ x * x * A0 := mul_nonneg (mul_nonneg hx hx) he0
        linarith

theorem elemSymmList_brun_recurrence
    (xs : List ℚ) (hnn : ∀ x ∈ xs, 0 ≤ x) :
    ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * elemSymmList xs r ≤ xs.sum * elemSymmList xs (r - 1) :=
  fun r hr => newton_ineq_elemSymmList xs r hr hnn

theorem elemSymmList_le_sum_pow_div_factorial
    (xs : List ℚ) (r : Nat) (hnn : ∀ x ∈ xs, 0 ≤ x) :
    elemSymmList xs r ≤ xs.sum ^ r / (Nat.factorial r : ℚ) :=
  brun_recurrence_iterated_bound_from_mul
    (elemSymmList xs) xs.sum
    (List.sum_nonneg (fun y hy => hnn y hy))
    (by simp)
    (elemSymmList_brun_recurrence xs hnn)
    r

theorem elemSymmList_le_mass_pow_div_factorial
    (xs : List ℚ) (M : ℚ) (r : Nat)
    (hnn : ∀ x ∈ xs, 0 ≤ x) (hmass : xs.sum ≤ M) :
    elemSymmList xs r ≤ M ^ r / (Nat.factorial r : ℚ) := by
  have hbase := elemSymmList_le_sum_pow_div_factorial xs r hnn
  have hsumNonneg : 0 ≤ xs.sum := List.sum_nonneg hnn
  have hpow : xs.sum ^ r ≤ M ^ r :=
    pow_le_pow_left₀ hsumNonneg hmass r
  have hdiv :
      xs.sum ^ r / (Nat.factorial r : ℚ) ≤
        M ^ r / (Nat.factorial r : ℚ) := by
    exact div_le_div_of_nonneg_right hpow (by positivity)
  exact le_trans hbase hdiv

/-!
## Pointwise even Bonferroni arithmetic

The finite-interval transfer uses the elementary pointwise inequality
`∑_{r ≤ 2R} (-1)^r (W choose r) ≤ 1_{W=0} + (W choose 2R)`.  The proof below
is purely algebraic: a truncated alternating binomial sum is either the full
alternating binomial sum or the standard prefix
`(-1)^m * ((W - 1) choose m)`.
-/

def alternatingChoosePrefix (W m : Nat) : Int :=
  ∑ r ∈ Finset.range (m + 1), ((-1 : Int) ^ r) * (Nat.choose W r : Int)

theorem alternatingChoosePrefix_eq_of_lt
    (W m : Nat) (hm : m < W) :
    alternatingChoosePrefix W m =
      ((-1 : Int) ^ m) * (Nat.choose (W - 1) m : Int) := by
  unfold alternatingChoosePrefix
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hm_lt_W : m < W := Nat.lt_trans (Nat.lt_succ_self m) hm
      have ihm := ih hm_lt_W
      rw [Finset.sum_range_succ]
      rw [ihm]
      have hW : W = (W - 1).succ := by omega
      have hchoose : Nat.choose W (m + 1) =
          Nat.choose (W - 1) m + Nat.choose (W - 1) (m + 1) := by
        rw [hW]
        exact Nat.choose_succ_succ (W - 1) m
      rw [hchoose, Nat.cast_add]
      have hsign : (-1 : Int) ^ (m + 1) = -((-1 : Int) ^ m) := by
        rw [pow_succ]
        ring
      rw [hsign]
      ring

theorem alternatingChoosePrefix_eq_full_of_le
    (W m : Nat) (h : W ≤ m) :
    alternatingChoosePrefix W m =
      ∑ r ∈ Finset.range (W + 1), ((-1 : Int) ^ r) *
        (Nat.choose W r : Int) := by
  unfold alternatingChoosePrefix
  symm
  apply Finset.sum_subset
  · intro r hr
    have hrleW : r ≤ W := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_trans hrleW h))
  · intro r _ hrNotSmall
    have hWlt : W < r := by
      by_contra hnot
      have hrleW : r ≤ W := Nat.le_of_not_gt hnot
      exact hrNotSmall (Finset.mem_range.mpr (Nat.lt_succ_of_le hrleW))
    simp [Nat.choose_eq_zero_of_lt hWlt]

theorem alternatingChoosePrefix_eq_if_of_le
    (W m : Nat) (h : W ≤ m) :
    alternatingChoosePrefix W m = if W = 0 then 1 else 0 := by
  rw [alternatingChoosePrefix_eq_full_of_le W m h]
  exact Int.alternating_sum_range_choose

theorem even_bonferroni_nohit_le_prefix (W R : Nat) :
    (if W = 0 then (1 : Int) else 0) ≤ alternatingChoosePrefix W (2 * R) := by
  by_cases hlt : 2 * R < W
  · have hprefix := alternatingChoosePrefix_eq_of_lt W (2 * R) hlt
    rw [hprefix]
    have hpow : (-1 : Int) ^ (2 * R) = 1 := by
      rw [pow_mul]
      norm_num
    rw [hpow, one_mul]
    have hif : (if W = 0 then (1 : Int) else 0) = 0 := by
      have hWne : W ≠ 0 := by omega
      simp [hWne]
    rw [hif]
    exact_mod_cast Nat.zero_le (Nat.choose (W - 1) (2 * R))
  · have hle : W ≤ 2 * R := Nat.le_of_not_gt hlt
    rw [alternatingChoosePrefix_eq_if_of_le W (2 * R) hle]

theorem even_bonferroni_arithmetic_bound (W R : Nat) :
    alternatingChoosePrefix W (2 * R) ≤
      (if W = 0 then (1 : Int) else 0) + (Nat.choose W (2 * R) : Int) := by
  by_cases hlt : 2 * R < W
  · have hprefix := alternatingChoosePrefix_eq_of_lt W (2 * R) hlt
    rw [hprefix]
    have hpow : (-1 : Int) ^ (2 * R) = 1 := by
      rw [pow_mul]
      norm_num
    rw [hpow, one_mul]
    have hif : (if W = 0 then (1 : Int) else 0) = 0 := by
      have hWne : W ≠ 0 := by omega
      simp [hWne]
    rw [hif, zero_add]
    have hleW : W - 1 ≤ W := Nat.sub_le W 1
    have hchoosele :
        Nat.choose (W - 1) (2 * R) ≤ Nat.choose W (2 * R) :=
      Nat.choose_le_choose (2 * R) hleW
    exact_mod_cast hchoosele
  · have hle : W ≤ 2 * R := Nat.le_of_not_gt hlt
    have hprefix := alternatingChoosePrefix_eq_if_of_le W (2 * R) hle
    rw [hprefix]
    have hnonneg : 0 ≤ (Nat.choose W (2 * R) : Int) := by
      exact_mod_cast Nat.zero_le _
    exact le_add_of_nonneg_right hnonneg

/-!
## Finite hit-subset binomial identity

For a fixed point in a finite event model, let `hit` be the predicate that an
event contains the point.  The number of `r`-subsets of hit events is
`(W choose r)`, where `W` is the number of hit events.  This is the finite
counting identity that turns the Bonferroni subset sum into the alternating
binomial prefix above.
-/

noncomputable def hitEventCount {α : Type*} (events : Finset α) (hit : α → Prop)
    [DecidablePred hit] : Nat :=
  (events.filter hit).card

theorem hitEventCount_image_eq_zero_iff
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (events : Finset α) (f : α → β)
    (hitα : α → Prop) (hitβ : β → Prop)
    [DecidablePred hitα] [DecidablePred hitβ]
    (hiff : ∀ a ∈ events, hitα a ↔ hitβ (f a)) :
    hitEventCount (events.image f) hitβ = 0 ↔
      hitEventCount events hitα = 0 := by
  unfold hitEventCount
  constructor
  · intro h
    rw [Finset.card_eq_zero] at h ⊢
    rw [Finset.filter_eq_empty_iff] at h ⊢
    intro a ha hhit
    exact h (Finset.mem_image.mpr ⟨a, ha, rfl⟩) ((hiff a ha).1 hhit)
  · intro h
    rw [Finset.card_eq_zero] at h ⊢
    rw [Finset.filter_eq_empty_iff] at h ⊢
    intro b hb hhit
    rcases Finset.mem_image.mp hb with ⟨a, ha, hba⟩
    subst hba
    exact h ha ((hiff a ha).2 hhit)

noncomputable def hitEventSubsetsOfCard {α : Type*} [DecidableEq α]
    (events : Finset α) (hit : α → Prop) [DecidablePred hit] (r : Nat) :
    Finset (Finset α) :=
  (events.powersetCard r).filter (fun s => ∀ i ∈ s, hit i)

theorem hitEventSubsetsOfCard_eq_powersetCard_filter
    {α : Type*} [DecidableEq α] (events : Finset α) (hit : α → Prop)
    [DecidablePred hit] (r : Nat) :
    hitEventSubsetsOfCard events hit r = (events.filter hit).powersetCard r := by
  ext s
  simp only [hitEventSubsetsOfCard, Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · intro h
    exact ⟨fun x hx => Finset.mem_filter.mpr ⟨h.1.1 hx, h.2 x hx⟩, h.1.2⟩
  · intro h
    exact ⟨⟨fun x hx => (Finset.mem_filter.mp (h.1 hx)).1, h.2⟩,
      fun x hx => (Finset.mem_filter.mp (h.1 hx)).2⟩

theorem hitEventSubsetsOfCard_card_eq_choose
    {α : Type*} [DecidableEq α] (events : Finset α) (hit : α → Prop)
    [DecidablePred hit] (r : Nat) :
    (hitEventSubsetsOfCard events hit r).card =
      Nat.choose (hitEventCount events hit) r := by
  rw [hitEventSubsetsOfCard_eq_powersetCard_filter]
  simp [hitEventCount, Finset.card_powersetCard]

theorem hitEventSubsets_alternating_sum_eq_prefix
    {α : Type*} [DecidableEq α] (events : Finset α) (hit : α → Prop)
    [DecidablePred hit] (m : Nat) :
    (∑ r ∈ Finset.range (m + 1),
        ((-1 : Int) ^ r) * ((hitEventSubsetsOfCard events hit r).card : Int)) =
      alternatingChoosePrefix (hitEventCount events hit) m := by
  unfold alternatingChoosePrefix
  apply Finset.sum_congr rfl
  intro r _hr
  rw [hitEventSubsetsOfCard_card_eq_choose]

noncomputable def eventSubsetCommonHitCount {α β : Type*}
    (points : Finset β) (contains : β → α → Prop)
    [∀ x i, Decidable (contains x i)] (s : Finset α) : Nat :=
  (points.filter (fun x => ∀ i ∈ s, contains x i)).card

theorem hitEventSubsets_double_count
    {α β : Type*} [DecidableEq α] (points : Finset β) (events : Finset α)
    (contains : β → α → Prop) [∀ x i, Decidable (contains x i)] (r : Nat) :
    (∑ x ∈ points, (hitEventSubsetsOfCard events (fun i => contains x i) r).card) =
      ∑ s ∈ events.powersetCard r, eventSubsetCommonHitCount points contains s := by
  unfold hitEventSubsetsOfCard eventSubsetCommonHitCount
  calc
    (∑ x ∈ points,
        ((events.powersetCard r).filter (fun s => ∀ i ∈ s, contains x i)).card)
        = ∑ x ∈ points,
            ∑ s ∈ events.powersetCard r,
              if (∀ i ∈ s, contains x i) then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro x _hx
          rw [Finset.card_filter]
    _ = ∑ s ∈ events.powersetCard r,
          ∑ x ∈ points, if (∀ i ∈ s, contains x i) then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ s ∈ events.powersetCard r,
          (points.filter (fun x => ∀ i ∈ s, contains x i)).card := by
          apply Finset.sum_congr rfl
          intro s _hs
          rw [Finset.card_filter]

theorem hitEventSubsets_alternating_double_count
    {α β : Type*} [DecidableEq α] (points : Finset β) (events : Finset α)
    (contains : β → α → Prop) [∀ x i, Decidable (contains x i)] (m : Nat) :
    (∑ x ∈ points,
        alternatingChoosePrefix (hitEventCount events (fun i => contains x i)) m) =
      ∑ r ∈ Finset.range (m + 1),
        ((-1 : Int) ^ r) *
          ((∑ s ∈ events.powersetCard r,
              eventSubsetCommonHitCount points contains s : Nat) : Int) := by
  calc
    (∑ x ∈ points,
        alternatingChoosePrefix (hitEventCount events (fun i => contains x i)) m)
        = ∑ x ∈ points,
            ∑ r ∈ Finset.range (m + 1),
              ((-1 : Int) ^ r) *
                ((hitEventSubsetsOfCard events
                  (fun i => contains x i) r).card : Int) := by
          apply Finset.sum_congr rfl
          intro x _hx
          rw [← hitEventSubsets_alternating_sum_eq_prefix]
    _ = ∑ r ∈ Finset.range (m + 1),
          ∑ x ∈ points,
            ((-1 : Int) ^ r) *
              ((hitEventSubsetsOfCard events
                (fun i => contains x i) r).card : Int) := by
          rw [Finset.sum_comm]
    _ = ∑ r ∈ Finset.range (m + 1),
          ((-1 : Int) ^ r) *
            ((∑ s ∈ events.powersetCard r,
              eventSubsetCommonHitCount points contains s : Nat) : Int) := by
          apply Finset.sum_congr rfl
          intro r _hr
          rw [← Finset.mul_sum]
          have h := hitEventSubsets_double_count points events contains r
          have hInt :
              ((∑ x ∈ points,
                (hitEventSubsetsOfCard events
                  (fun i => contains x i) r).card) : Int) =
              ((∑ s ∈ events.powersetCard r,
                eventSubsetCommonHitCount points contains s : Nat) : Int) := by
            exact_mod_cast h
          simpa using congrArg (fun t : Int => ((-1 : Int) ^ r) * t) hInt

theorem hitEventSubsets_bonferroni_lower_double_count
    {α β : Type*} [DecidableEq α]
    (points : Finset β) (events : Finset α)
    (contains : β → α → Prop) [∀ x i, Decidable (contains x i)] (R : Nat) :
    (∑ x ∈ points,
        (if hitEventCount events (fun i => contains x i) = 0 then (1 : Int) else 0)) ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((-1 : Int) ^ r) *
          ((∑ s ∈ events.powersetCard r,
              eventSubsetCommonHitCount points contains s : Nat) : Int) := by
  classical
  have hpoint :
      (∑ x ∈ points,
          (if hitEventCount events (fun i => contains x i) = 0 then (1 : Int) else 0)) ≤
        ∑ x ∈ points,
          alternatingChoosePrefix (hitEventCount events (fun i => contains x i)) (2 * R) := by
    apply Finset.sum_le_sum
    intro x _hx
    exact even_bonferroni_nohit_le_prefix
      (hitEventCount events (fun i => contains x i)) R
  have hdouble := hitEventSubsets_alternating_double_count points events contains (2 * R)
  calc
    (∑ x ∈ points,
        (if hitEventCount events (fun i => contains x i) = 0 then (1 : Int) else 0)) ≤
        ∑ x ∈ points,
          alternatingChoosePrefix (hitEventCount events (fun i => contains x i)) (2 * R) := hpoint
    _ = ∑ r ∈ Finset.range (2 * R + 1),
        ((-1 : Int) ^ r) *
          ((∑ s ∈ events.powersetCard r,
              eventSubsetCommonHitCount points contains s : Nat) : Int) := hdouble

theorem hitEventSubsets_bonferroni_upper_double_count
    {α β : Type*} [DecidableEq α]
    (points : Finset β) (events : Finset α)
    (contains : β → α → Prop) [∀ x i, Decidable (contains x i)] (R : Nat) :
    (∑ x ∈ points,
        alternatingChoosePrefix (hitEventCount events (fun i => contains x i)) (2 * R)) ≤
      (∑ x ∈ points,
        (if hitEventCount events (fun i => contains x i) = 0 then (1 : Int) else 0)) +
      (∑ s ∈ events.powersetCard (2 * R),
        (eventSubsetCommonHitCount points contains s : Int)) := by
  classical
  have hpoint :
      (∑ x ∈ points,
          alternatingChoosePrefix (hitEventCount events (fun i => contains x i)) (2 * R)) ≤
        ∑ x ∈ points,
          ((if hitEventCount events (fun i => contains x i) = 0 then (1 : Int) else 0) +
            (Nat.choose (hitEventCount events (fun i => contains x i)) (2 * R) : Int)) := by
    apply Finset.sum_le_sum
    intro x _hx
    exact even_bonferroni_arithmetic_bound
      (hitEventCount events (fun i => contains x i)) R
  have hchooseNat :
      (∑ x ∈ points, Nat.choose (hitEventCount events (fun i => contains x i)) (2 * R)) =
        ∑ s ∈ events.powersetCard (2 * R), eventSubsetCommonHitCount points contains s := by
    calc
      (∑ x ∈ points,
          Nat.choose (hitEventCount events (fun i => contains x i)) (2 * R)) =
          ∑ x ∈ points,
            (hitEventSubsetsOfCard events (fun i => contains x i) (2 * R)).card := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [hitEventSubsetsOfCard_card_eq_choose]
      _ = ∑ s ∈ events.powersetCard (2 * R),
            eventSubsetCommonHitCount points contains s := by
        exact hitEventSubsets_double_count points events contains (2 * R)
  have hchooseInt :
      (∑ x ∈ points,
        (Nat.choose (hitEventCount events (fun i => contains x i)) (2 * R) : Int)) =
        ∑ s ∈ events.powersetCard (2 * R),
          (eventSubsetCommonHitCount points contains s : Int) := by
    exact_mod_cast hchooseNat
  calc
    (∑ x ∈ points,
        alternatingChoosePrefix (hitEventCount events (fun i => contains x i)) (2 * R)) ≤
        ∑ x ∈ points,
          ((if hitEventCount events (fun i => contains x i) = 0 then (1 : Int) else 0) +
            (Nat.choose (hitEventCount events (fun i => contains x i)) (2 * R) : Int)) := hpoint
    _ = (∑ x ∈ points,
        (if hitEventCount events (fun i => contains x i) = 0 then (1 : Int) else 0)) +
      (∑ x ∈ points,
        (Nat.choose (hitEventCount events (fun i => contains x i)) (2 * R) : Int)) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ x ∈ points,
        (if hitEventCount events (fun i => contains x i) = 0 then (1 : Int) else 0)) +
      (∑ s ∈ events.powersetCard (2 * R),
        (eventSubsetCommonHitCount points contains s : Int)) := by
      rw [hchooseInt]

/-!
## Finite residue-class interval count

The finite-interval transfer in the manuscript uses that one residue class
modulo a modulus contributes `N / q + O(1)` integers up to `N`; in the paper the
modulus is positive.  The next lemma formalizes the exact finite bound behind
that `O(1)` term.
-/

def residueClassCountUpTo (N q a : Nat) : Nat :=
  ((Finset.range (N + 1)).filter (fun n => n ≡ a [MOD q])).card

theorem residueClassCountUpTo_le_div_add_one
    (N q a : Nat) (hq : 0 < q) :
    residueClassCountUpTo N q a ≤ N / q + 1 := by
  classical
  have _ : q ≠ 0 := Nat.ne_of_gt hq
  let s : Finset Nat := (Finset.range (N + 1)).filter (fun n => n ≡ a [MOD q])
  let t : Finset Nat := Finset.range (N / q + 1)
  have hmaps : ∀ n ∈ s, n / q ∈ t := by
    intro n hn
    have hnrange : n ∈ Finset.range (N + 1) := (Finset.mem_filter.mp hn).1
    have hnle : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hnrange)
    have hdivle : n / q ≤ N / q := Nat.div_le_div_right hnle
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hdivle)
  have hinj : (s : Set Nat).InjOn (fun n => n / q) := by
    intro x hx y hy hdiv
    have hxmem : x ∈ s := hx
    have hymem : y ∈ s := hy
    have hxmoda : x ≡ a [MOD q] := (Finset.mem_filter.mp hxmem).2
    have hymoda : y ≡ a [MOD q] := (Finset.mem_filter.mp hymem).2
    have hxyMod : x ≡ y [MOD q] := hxmoda.trans hymoda.symm
    change x / q = y / q at hdiv
    unfold Nat.ModEq at hxyMod
    calc
      x = x % q + q * (x / q) := (Nat.mod_add_div x q).symm
      _ = y % q + q * (y / q) := by rw [hxyMod, hdiv]
      _ = y := Nat.mod_add_div y q
  have hcard : s.card ≤ t.card :=
    Finset.card_le_card_of_injOn (fun n => n / q) hmaps hinj
  simpa [residueClassCountUpTo, s, t] using hcard

theorem residueClassCountUpTo_cast_le_div_add_one
    (N q a : Nat) (hq : 0 < q) :
    (residueClassCountUpTo N q a : ℚ) ≤
      (N / q : Nat) + 1 := by
  exact_mod_cast residueClassCountUpTo_le_div_add_one N q a hq

/-- Every residue class modulo a positive modulus occurs at least `N / q`
times in `[0, N]`.  The representatives `a % q + kq`, for `k < N / q`, give
an explicit injection into the counted class. -/
theorem div_le_residueClassCountUpTo
    (N q a : Nat) (hq : 0 < q) :
    N / q ≤ residueClassCountUpTo N q a := by
  classical
  let source : Finset Nat := Finset.range (N / q)
  let target : Finset Nat :=
    (Finset.range (N + 1)).filter (fun n => n ≡ a [MOD q])
  let f : Nat → Nat := fun k => a % q + k * q
  have hmaps : ∀ k ∈ source, f k ∈ target := by
    intro k hk
    have hklt : k < N / q := Finset.mem_range.mp hk
    have hksucc : k + 1 ≤ N / q := Nat.succ_le_iff.mpr hklt
    have hmodlt : a % q < q := Nat.mod_lt a hq
    have hflt : f k < (k + 1) * q := by
      dsimp [f]
      rw [Nat.add_mul]
      simpa [Nat.one_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        Nat.add_lt_add_right hmodlt (k * q)
    have hmulLe : (k + 1) * q ≤ (N / q) * q :=
      Nat.mul_le_mul_right q hksucc
    have hN : (N / q) * q ≤ N := Nat.div_mul_le_self N q
    have hfLe : f k ≤ N := (hflt.le.trans hmulLe).trans hN
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hfLe)
    · unfold Nat.ModEq
      simp [f, Nat.add_mod, Nat.mul_mod]
  have hinj : (source : Set Nat).InjOn f := by
    intro x _hx y _hy hxy
    have hmul : x * q = y * q := Nat.add_left_cancel hxy
    exact Nat.eq_of_mul_eq_mul_right hq hmul
  have hcard : source.card ≤ target.card :=
    Finset.card_le_card_of_injOn f hmaps hinj
  simpa [residueClassCountUpTo, source, target] using hcard

/-- Rational lower endpoint estimate paired with
`residueClassCountUpTo_cast_le_div_add_one`: one residue class contributes at
least `N / q - 1`. -/
theorem div_sub_one_le_residueClassCountUpTo_cast
    (N q a : Nat) (hq : 0 < q) :
    (N : ℚ) / (q : ℚ) - 1 ≤ (residueClassCountUpTo N q a : ℚ) := by
  have hqRat : 0 < (q : ℚ) := by exact_mod_cast hq
  have hdecomp : (N : ℚ) =
      ((N % q : Nat) : ℚ) + (q : ℚ) * ((N / q : Nat) : ℚ) := by
    exact_mod_cast (Nat.mod_add_div N q).symm
  have hremLe : ((N % q : Nat) : ℚ) / (q : ℚ) ≤ 1 := by
    apply (div_le_one hqRat).2
    exact_mod_cast (Nat.mod_lt N hq).le
  have hfloorLe : ((N / q : Nat) : ℚ) ≤
      (residueClassCountUpTo N q a : ℚ) := by
    exact_mod_cast div_le_residueClassCountUpTo N q a hq
  calc
    (N : ℚ) / (q : ℚ) - 1 =
        ((N / q : Nat) : ℚ) + ((N % q : Nat) : ℚ) / (q : ℚ) - 1 := by
      rw [hdecomp]
      field_simp [ne_of_gt hqRat]
      ring
    _ ≤ ((N / q : Nat) : ℚ) := by linarith
    _ ≤ (residueClassCountUpTo N q a : ℚ) := hfloorLe

noncomputable def congruenceRowsCountUpTo (N : Nat) (rows : List (Nat × Nat)) : Nat := by
  classical
  exact ((Finset.range (N + 1)).filter (fun n => satisfiesCongruenceRows n rows)).card

theorem congruenceRowsCountUpTo_eq_zero_of_not_pairwiseCompatible
    (N : Nat) (rows : List (Nat × Nat))
    (hnot : ¬ congruenceRowsPairwiseCompatible rows) :
    congruenceRowsCountUpTo N rows = 0 := by
  classical
  unfold congruenceRowsCountUpTo
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n _hnrange hsat
  exact hnot (congruenceRowsPairwiseCompatible_of_solution rows n hsat)

theorem congruenceRowsCountUpTo_eq_zero_of_incompatible_pair
    (N : Nat) (rows : List (Nat × Nat)) (rowA rowB : Nat × Nat)
    (hA : rowA ∈ rows) (hB : rowB ∈ rows)
    (hincomp : ¬ residueCompatible rowA.1 rowB.1 rowA.2 rowB.2) :
    congruenceRowsCountUpTo N rows = 0 := by
  exact congruenceRowsCountUpTo_eq_zero_of_not_pairwiseCompatible N rows (by
    intro hcompat
    exact hincomp (hcompat rowA hA rowB hB))

theorem congruenceRowsCountUpTo_eq_residueClassCountUpTo_of_solution
    (N x : Nat) (rows : List (Nat × Nat))
    (hx : satisfiesCongruenceRows x rows) :
    congruenceRowsCountUpTo N rows =
      residueClassCountUpTo N (congruenceLcm rows) x := by
  classical
  unfold congruenceRowsCountUpTo residueClassCountUpTo
  apply congrArg Finset.card
  ext n
  simp [congruenceRows_solution_iff_modEq_lcm rows x n hx]

theorem congruenceRowsCountUpTo_le_div_add_one_of_solution
    (N x : Nat) (rows : List (Nat × Nat))
    (hL : 0 < congruenceLcm rows)
    (hx : satisfiesCongruenceRows x rows) :
    congruenceRowsCountUpTo N rows ≤ N / congruenceLcm rows + 1 := by
  classical
  let L := congruenceLcm rows
  let s : Finset Nat :=
    (Finset.range (N + 1)).filter (fun n => satisfiesCongruenceRows n rows)
  let t : Finset Nat := (Finset.range (N + 1)).filter (fun n => n ≡ x [MOD L])
  have hmaps : ∀ n ∈ s, n ∈ t := by
    intro n hn
    have hnrange : n ∈ Finset.range (N + 1) := (Finset.mem_filter.mp hn).1
    have hsat : satisfiesCongruenceRows n rows := (Finset.mem_filter.mp hn).2
    have hmod : n ≡ x [MOD L] := by
      simpa [L] using congruenceRows_unique_mod_lcm rows n x hsat hx
    exact Finset.mem_filter.mpr ⟨hnrange, hmod⟩
  have hinj : (s : Set Nat).InjOn (fun n => n) := by
    intro a _ b _ h
    exact h
  have hcard : s.card ≤ t.card :=
    Finset.card_le_card_of_injOn (fun n => n) hmaps hinj
  calc
    congruenceRowsCountUpTo N rows = s.card := by
      simp [congruenceRowsCountUpTo, s]
    _ ≤ t.card := hcard
    _ = residueClassCountUpTo N L x := by
      simp [residueClassCountUpTo, t]
    _ ≤ N / L + 1 := residueClassCountUpTo_le_div_add_one N L x (by simpa [L] using hL)

theorem congruenceRowsCountUpTo_cast_le_div_add_one_of_solution
    (N x : Nat) (rows : List (Nat × Nat))
    (hL : 0 < congruenceLcm rows)
    (hx : satisfiesCongruenceRows x rows) :
    (congruenceRowsCountUpTo N rows : ℚ) ≤
      (N / congruenceLcm rows : Nat) + 1 := by
  exact_mod_cast congruenceRowsCountUpTo_le_div_add_one_of_solution N x rows hL hx

noncomputable def baseResidualRowsCountUpTo
    (N Pz b : Nat) (rows : List (Nat × Nat)) : Nat := by
  classical
  exact ((Finset.range (N + 1)).filter
    (fun n => n ≡ b [MOD Pz] ∧ satisfiesCongruenceRows n rows)).card

theorem baseResidualRowsCountUpTo_eq_zero_of_not_pairwiseCompatible
    (N Pz b : Nat) (rows : List (Nat × Nat))
    (hnot : ¬ congruenceRowsPairwiseCompatible rows) :
    baseResidualRowsCountUpTo N Pz b rows = 0 := by
  classical
  unfold baseResidualRowsCountUpTo
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n _hnrange hsat
  exact hnot (congruenceRowsPairwiseCompatible_of_solution rows n hsat.2)

theorem baseResidualRowsCountUpTo_eq_zero_of_incompatible_pair
    (N Pz b : Nat) (rows : List (Nat × Nat)) (rowA rowB : Nat × Nat)
    (hA : rowA ∈ rows) (hB : rowB ∈ rows)
    (hincomp : ¬ residueCompatible rowA.1 rowB.1 rowA.2 rowB.2) :
    baseResidualRowsCountUpTo N Pz b rows = 0 := by
  exact baseResidualRowsCountUpTo_eq_zero_of_not_pairwiseCompatible N Pz b rows (by
    intro hcompat
    exact hincomp (hcompat rowA hA rowB hB))

theorem baseResidualRowsCountUpTo_eq_zero_of_not_base_pairwiseCompatible
    (N Pz b : Nat) (rows : List (Nat × Nat))
    (hnot : ¬ congruenceRowsPairwiseCompatible ((Pz, b) :: rows)) :
    baseResidualRowsCountUpTo N Pz b rows = 0 := by
  classical
  unfold baseResidualRowsCountUpTo
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n _hnrange hsat
  exact hnot (congruenceRowsPairwiseCompatible_of_solution
    ((Pz, b) :: rows) n (by
      intro row hrow
      rcases List.mem_cons.mp hrow with hbase | htail
      · subst hbase
        exact hsat.1
      · exact hsat.2 row htail))

theorem baseResidualRows_unique_mod_product
    (Pz b : Nat) (rows : List (Nat × Nat)) (x y : Nat)
    (hcop : Nat.Coprime Pz (congruenceLcm rows))
    (hxbase : x ≡ b [MOD Pz]) (hybase : y ≡ b [MOD Pz])
    (hxrows : satisfiesCongruenceRows x rows)
    (hyrows : satisfiesCongruenceRows y rows) :
    x ≡ y [MOD Pz * congruenceLcm rows] := by
  have hbase : x ≡ y [MOD Pz] := hxbase.trans hybase.symm
  have hrows : x ≡ y [MOD congruenceLcm rows] :=
    congruenceRows_unique_mod_lcm rows x y hxrows hyrows
  have hprod : x ≡ y [MOD Nat.lcm Pz (congruenceLcm rows)] :=
    Nat.mod_lcm hbase hrows
  simpa [hcop.lcm_eq_mul] using hprod

theorem baseResidualRows_solution_iff_modEq_product
    (Pz b : Nat) (rows : List (Nat × Nat)) (x n : Nat)
    (hcop : Nat.Coprime Pz (congruenceLcm rows))
    (hxbase : x ≡ b [MOD Pz])
    (hxrows : satisfiesCongruenceRows x rows) :
    (n ≡ b [MOD Pz] ∧ satisfiesCongruenceRows n rows) ↔
      n ≡ x [MOD Pz * congruenceLcm rows] := by
  constructor
  · intro h
    exact baseResidualRows_unique_mod_product Pz b rows n x hcop
      h.1 hxbase h.2 hxrows
  · intro hn
    constructor
    · have hnPz : n ≡ x [MOD Pz] :=
        Nat.ModEq.of_dvd (Nat.dvd_mul_right Pz (congruenceLcm rows)) hn
      exact hnPz.trans hxbase
    · have hnL : n ≡ x [MOD congruenceLcm rows] :=
        Nat.ModEq.of_dvd (Nat.dvd_mul_left (congruenceLcm rows) Pz) hn
      exact congruenceRows_of_modEq_lcm rows x n hxrows hnL

theorem baseResidualRowsCountUpTo_eq_residueClassCountUpTo_of_solution
    (N Pz b x : Nat) (rows : List (Nat × Nat))
    (hcop : Nat.Coprime Pz (congruenceLcm rows))
    (hxbase : x ≡ b [MOD Pz])
    (hxrows : satisfiesCongruenceRows x rows) :
    baseResidualRowsCountUpTo N Pz b rows =
      residueClassCountUpTo N (Pz * congruenceLcm rows) x := by
  classical
  unfold baseResidualRowsCountUpTo residueClassCountUpTo
  apply congrArg Finset.card
  ext n
  simp [baseResidualRows_solution_iff_modEq_product Pz b rows x n
    hcop hxbase hxrows]

theorem baseResidualRowsCountUpTo_le_div_add_one_of_solution
    (N Pz b x : Nat) (rows : List (Nat × Nat))
    (hPz : 0 < Pz)
    (hL : 0 < congruenceLcm rows)
    (hcop : Nat.Coprime Pz (congruenceLcm rows))
    (hxbase : x ≡ b [MOD Pz])
    (hxrows : satisfiesCongruenceRows x rows) :
    baseResidualRowsCountUpTo N Pz b rows ≤
      N / (Pz * congruenceLcm rows) + 1 := by
  classical
  let L := congruenceLcm rows
  let s : Finset Nat := (Finset.range (N + 1)).filter
    (fun n => n ≡ b [MOD Pz] ∧ satisfiesCongruenceRows n rows)
  let t : Finset Nat := (Finset.range (N + 1)).filter
    (fun n => n ≡ x [MOD Pz * L])
  have hmaps : ∀ n ∈ s, n ∈ t := by
    intro n hn
    have hnrange : n ∈ Finset.range (N + 1) := (Finset.mem_filter.mp hn).1
    have hbase : n ≡ b [MOD Pz] := (Finset.mem_filter.mp hn).2.1
    have hrows : satisfiesCongruenceRows n rows := (Finset.mem_filter.mp hn).2.2
    have hmod : n ≡ x [MOD Pz * L] := by
      simpa [L] using
        baseResidualRows_unique_mod_product Pz b rows n x hcop
          hbase hxbase hrows hxrows
    exact Finset.mem_filter.mpr ⟨hnrange, hmod⟩
  have hinj : (s : Set Nat).InjOn (fun n => n) := by
    intro a _ b _ h
    exact h
  have hcard : s.card ≤ t.card :=
    Finset.card_le_card_of_injOn (fun n => n) hmaps hinj
  calc
    baseResidualRowsCountUpTo N Pz b rows = s.card := by
      simp [baseResidualRowsCountUpTo, s]
    _ ≤ t.card := hcard
    _ = residueClassCountUpTo N (Pz * L) x := by
      simp [residueClassCountUpTo, t]
    _ ≤ N / (Pz * L) + 1 :=
      residueClassCountUpTo_le_div_add_one N (Pz * L) x
        (Nat.mul_pos hPz (by simpa [L] using hL))

theorem baseResidualRowsCountUpTo_cast_le_div_add_one_of_solution
    (N Pz b x : Nat) (rows : List (Nat × Nat))
    (hPz : 0 < Pz)
    (hL : 0 < congruenceLcm rows)
    (hcop : Nat.Coprime Pz (congruenceLcm rows))
    (hxbase : x ≡ b [MOD Pz])
    (hxrows : satisfiesCongruenceRows x rows) :
    (baseResidualRowsCountUpTo N Pz b rows : ℚ) ≤
      (N / (Pz * congruenceLcm rows) : Nat) + 1 := by
  exact_mod_cast
    baseResidualRowsCountUpTo_le_div_add_one_of_solution
      N Pz b x rows hPz hL hcop hxbase hxrows

/-!
## Congruence-row event specialization

The generic point/event identities above are enough to express the finite
Bonferroni step for arbitrary finite event families.  The next definitions
specialize them to congruence-row events on the interval `0 <= n <= N`, and to
the same interval after imposing a base class `b (mod Pz)`.
-/

noncomputable def rowEventCommonHitCountUpTo
    (N : Nat) (s : Finset (Nat × Nat)) : Nat :=
  eventSubsetCommonHitCount (Finset.range (N + 1))
    (fun n row => n ≡ row.2 [MOD row.1]) s

theorem rowEventCommonHitCountUpTo_eq_congruenceRowsCountUpTo_toList
    (N : Nat) (s : Finset (Nat × Nat)) :
    rowEventCommonHitCountUpTo N s =
      congruenceRowsCountUpTo N s.toList := by
  classical
  unfold rowEventCommonHitCountUpTo eventSubsetCommonHitCount
    congruenceRowsCountUpTo satisfiesCongruenceRows
  apply congrArg Finset.card
  ext n
  simp

theorem rowEventCommonHitCountUpTo_eq_residueClassCountUpTo_of_solution
    (N x : Nat) (s : Finset (Nat × Nat))
    (hx : satisfiesCongruenceRows x s.toList) :
    rowEventCommonHitCountUpTo N s =
      residueClassCountUpTo N (congruenceLcm s.toList) x := by
  rw [rowEventCommonHitCountUpTo_eq_congruenceRowsCountUpTo_toList]
  exact congruenceRowsCountUpTo_eq_residueClassCountUpTo_of_solution
    N x s.toList hx

noncomputable def baseRowEventCommonHitCountUpTo
    (N Pz b : Nat) (s : Finset (Nat × Nat)) : Nat :=
  eventSubsetCommonHitCount
    ((Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz]))
    (fun n row => n ≡ row.2 [MOD row.1]) s

theorem baseRowEventCommonHitCountUpTo_eq_baseResidualRowsCountUpTo_toList
    (N Pz b : Nat) (s : Finset (Nat × Nat)) :
    baseRowEventCommonHitCountUpTo N Pz b s =
      baseResidualRowsCountUpTo N Pz b s.toList := by
  classical
  unfold baseRowEventCommonHitCountUpTo eventSubsetCommonHitCount
    baseResidualRowsCountUpTo satisfiesCongruenceRows
  apply congrArg Finset.card
  ext n
  simp [and_assoc, and_left_comm, and_comm]

theorem baseRowEventCommonHitCountUpTo_eq_residueClassCountUpTo_of_solution
    (N Pz b x : Nat) (s : Finset (Nat × Nat))
    (hcop : Nat.Coprime Pz (congruenceLcm s.toList))
    (hxbase : x ≡ b [MOD Pz])
    (hxrows : satisfiesCongruenceRows x s.toList) :
    baseRowEventCommonHitCountUpTo N Pz b s =
      residueClassCountUpTo N (Pz * congruenceLcm s.toList) x := by
  rw [baseRowEventCommonHitCountUpTo_eq_baseResidualRowsCountUpTo_toList]
  exact baseResidualRowsCountUpTo_eq_residueClassCountUpTo_of_solution
    N Pz b x s.toList hcop hxbase hxrows

noncomputable def satEventCommonHitCountUpTo
    (N : Nat) (events : Finset SatEvent) : Nat := by
  classical
  exact eventSubsetCommonHitCount (Finset.range (N + 1))
    (fun n event => satEventHit n event) events

noncomputable def baseSatEventCommonHitCountUpTo
    (N Pz b : Nat) (events : Finset SatEvent) : Nat := by
  classical
  exact eventSubsetCommonHitCount
    ((Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz]))
    (fun n event => satEventHit n event) events

theorem satEventCommonHitCountUpTo_eq_rowEventCommonHitCountUpTo
    (N Pz rho : Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event) :
    satEventCommonHitCountUpTo N events =
      rowEventCommonHitCountUpTo N (satEventResidualHitRowsFinset events) := by
  classical
  unfold satEventCommonHitCountUpTo rowEventCommonHitCountUpTo
    eventSubsetCommonHitCount
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, and_congr_right_iff]
  intro _hn
  constructor
  · intro h row hrow
    rcases Finset.mem_image.mp hrow with ⟨event, hevent, hrowEq⟩
    subst hrowEq
    have hdPlusPos : 0 < event.dPlus :=
      (hadm event hevent).2.2.2.2.2.1
    have hpPos : 0 < event.p := (hadm event hevent).1.pos
    have hq : 0 < conditionalModulus event.dPlus event.p :=
      Nat.mul_pos hdPlusPos hpPos
    exact (satEventHit_iff_modEq_residualHitRow n event hq).2
      (h event hevent)
  · intro h event hevent
    have hrow : satEventResidualHitRow event ∈ satEventResidualHitRowsFinset events :=
      Finset.mem_image.mpr ⟨event, hevent, rfl⟩
    have hdPlusPos : 0 < event.dPlus :=
      (hadm event hevent).2.2.2.2.2.1
    have hpPos : 0 < event.p := (hadm event hevent).1.pos
    have hq : 0 < conditionalModulus event.dPlus event.p :=
      Nat.mul_pos hdPlusPos hpPos
    exact (satEventHit_iff_modEq_residualHitRow n event hq).1
      (h (satEventResidualHitRow event) hrow)

theorem baseSatEventCommonHitCountUpTo_eq_baseRowEventCommonHitCountUpTo
    (N Pz b rho : Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event) :
    baseSatEventCommonHitCountUpTo N Pz b events =
      baseRowEventCommonHitCountUpTo N Pz b (satEventResidualHitRowsFinset events) := by
  classical
  unfold baseSatEventCommonHitCountUpTo baseRowEventCommonHitCountUpTo
    eventSubsetCommonHitCount
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, and_assoc]
  constructor
  · intro h
    refine ⟨h.1, h.2.1, ?_⟩
    intro row hrow
    rcases Finset.mem_image.mp hrow with ⟨event, hevent, hrowEq⟩
    subst hrowEq
    have hdPlusPos : 0 < event.dPlus :=
      (hadm event hevent).2.2.2.2.2.1
    have hpPos : 0 < event.p := (hadm event hevent).1.pos
    have hq : 0 < conditionalModulus event.dPlus event.p :=
      Nat.mul_pos hdPlusPos hpPos
    exact (satEventHit_iff_modEq_residualHitRow n event hq).2
      (h.2.2 event hevent)
  · intro h
    refine ⟨h.1, h.2.1, ?_⟩
    intro event hevent
    have hrow : satEventResidualHitRow event ∈ satEventResidualHitRowsFinset events :=
      Finset.mem_image.mpr ⟨event, hevent, rfl⟩
    have hdPlusPos : 0 < event.dPlus :=
      (hadm event hevent).2.2.2.2.2.1
    have hpPos : 0 < event.p := (hadm event hevent).1.pos
    have hq : 0 < conditionalModulus event.dPlus event.p :=
      Nat.mul_pos hdPlusPos hpPos
    exact (satEventHit_iff_modEq_residualHitRow n event hq).1
      (h.2.2 (satEventResidualHitRow event) hrow)

theorem satEventCommonHitCountUpTo_eq_rowEventCommonHitCountUpTo_admissibleFor
    (N Pz : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event) :
    satEventCommonHitCountUpTo N events =
      rowEventCommonHitCountUpTo N (satEventResidualHitRowsFinset events) := by
  classical
  unfold satEventCommonHitCountUpTo rowEventCommonHitCountUpTo
    eventSubsetCommonHitCount
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, and_congr_right_iff]
  intro _hn
  constructor
  · intro h row hrow
    rcases Finset.mem_image.mp hrow with ⟨event, hevent, hrowEq⟩
    subst hrowEq
    have heventAdm : satEventAdmissible Pz (rhoOf event.e) event := by
      simpa [satEventAdmissibleFor] using hadm event hevent
    have hq : 0 < conditionalModulus event.dPlus event.p :=
      Nat.mul_pos heventAdm.2.2.2.2.2.1 heventAdm.1.pos
    exact (satEventHit_iff_modEq_residualHitRow n event hq).2
      (h event hevent)
  · intro h event hevent
    have hrow : satEventResidualHitRow event ∈ satEventResidualHitRowsFinset events :=
      Finset.mem_image.mpr ⟨event, hevent, rfl⟩
    have heventAdm : satEventAdmissible Pz (rhoOf event.e) event := by
      simpa [satEventAdmissibleFor] using hadm event hevent
    have hq : 0 < conditionalModulus event.dPlus event.p :=
      Nat.mul_pos heventAdm.2.2.2.2.2.1 heventAdm.1.pos
    exact (satEventHit_iff_modEq_residualHitRow n event hq).1
      (h (satEventResidualHitRow event) hrow)

theorem baseSatEventCommonHitCountUpTo_eq_baseRowEventCommonHitCountUpTo_admissibleFor
    (N Pz b : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event) :
    baseSatEventCommonHitCountUpTo N Pz b events =
      baseRowEventCommonHitCountUpTo N Pz b (satEventResidualHitRowsFinset events) := by
  classical
  unfold baseSatEventCommonHitCountUpTo baseRowEventCommonHitCountUpTo
    eventSubsetCommonHitCount
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, and_assoc]
  constructor
  · intro h
    refine ⟨h.1, h.2.1, ?_⟩
    intro row hrow
    rcases Finset.mem_image.mp hrow with ⟨event, hevent, hrowEq⟩
    subst hrowEq
    have heventAdm : satEventAdmissible Pz (rhoOf event.e) event := by
      simpa [satEventAdmissibleFor] using hadm event hevent
    have hq : 0 < conditionalModulus event.dPlus event.p :=
      Nat.mul_pos heventAdm.2.2.2.2.2.1 heventAdm.1.pos
    exact (satEventHit_iff_modEq_residualHitRow n event hq).2
      (h.2.2 event hevent)
  · intro h
    refine ⟨h.1, h.2.1, ?_⟩
    intro event hevent
    have hrow : satEventResidualHitRow event ∈ satEventResidualHitRowsFinset events :=
      Finset.mem_image.mpr ⟨event, hevent, rfl⟩
    have heventAdm : satEventAdmissible Pz (rhoOf event.e) event := by
      simpa [satEventAdmissibleFor] using hadm event hevent
    have hq : 0 < conditionalModulus event.dPlus event.p :=
      Nat.mul_pos heventAdm.2.2.2.2.2.1 heventAdm.1.pos
    exact (satEventHit_iff_modEq_residualHitRow n event hq).1
      (h.2.2 (satEventResidualHitRow event) hrow)

theorem rowEventCommonHitCountUpTo_eq_zero_of_incompatible_pair
    (N : Nat) (s : Finset (Nat × Nat)) (rowA rowB : Nat × Nat)
    (hA : rowA ∈ s) (hB : rowB ∈ s)
    (hincomp : ¬ residueCompatible rowA.1 rowB.1 rowA.2 rowB.2) :
    rowEventCommonHitCountUpTo N s = 0 := by
  rw [rowEventCommonHitCountUpTo_eq_congruenceRowsCountUpTo_toList]
  exact congruenceRowsCountUpTo_eq_zero_of_incompatible_pair N s.toList rowA rowB
    (by simpa using hA) (by simpa using hB) hincomp

theorem baseRowEventCommonHitCountUpTo_eq_zero_of_incompatible_pair
    (N Pz b : Nat) (s : Finset (Nat × Nat)) (rowA rowB : Nat × Nat)
    (hA : rowA ∈ s) (hB : rowB ∈ s)
    (hincomp : ¬ residueCompatible rowA.1 rowB.1 rowA.2 rowB.2) :
    baseRowEventCommonHitCountUpTo N Pz b s = 0 := by
  rw [baseRowEventCommonHitCountUpTo_eq_baseResidualRowsCountUpTo_toList]
  exact baseResidualRowsCountUpTo_eq_zero_of_incompatible_pair N Pz b s.toList
    rowA rowB (by simpa using hA) (by simpa using hB) hincomp

theorem satEventCommonHitCountUpTo_eq_zero_of_incompatible_pair
    (N Pz rho : Nat) (events : Finset SatEvent) (rowA rowB : Nat × Nat)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hA : rowA ∈ satEventResidualHitRowsFinset events)
    (hB : rowB ∈ satEventResidualHitRowsFinset events)
    (hincomp : ¬ residueCompatible rowA.1 rowB.1 rowA.2 rowB.2) :
    satEventCommonHitCountUpTo N events = 0 := by
  rw [satEventCommonHitCountUpTo_eq_rowEventCommonHitCountUpTo
    N Pz rho events hadm]
  exact rowEventCommonHitCountUpTo_eq_zero_of_incompatible_pair
    N (satEventResidualHitRowsFinset events) rowA rowB hA hB hincomp

theorem baseSatEventCommonHitCountUpTo_eq_zero_of_incompatible_pair
    (N Pz b rho : Nat) (events : Finset SatEvent) (rowA rowB : Nat × Nat)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hA : rowA ∈ satEventResidualHitRowsFinset events)
    (hB : rowB ∈ satEventResidualHitRowsFinset events)
    (hincomp : ¬ residueCompatible rowA.1 rowB.1 rowA.2 rowB.2) :
    baseSatEventCommonHitCountUpTo N Pz b events = 0 := by
  rw [baseSatEventCommonHitCountUpTo_eq_baseRowEventCommonHitCountUpTo
    N Pz b rho events hadm]
  exact baseRowEventCommonHitCountUpTo_eq_zero_of_incompatible_pair
    N Pz b (satEventResidualHitRowsFinset events) rowA rowB hA hB hincomp

theorem satEventCommonHitCountUpTo_eq_zero_of_incompatible_pair_admissibleFor
    (N Pz : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (rowA rowB : Nat × Nat)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hA : rowA ∈ satEventResidualHitRowsFinset events)
    (hB : rowB ∈ satEventResidualHitRowsFinset events)
    (hincomp : ¬ residueCompatible rowA.1 rowB.1 rowA.2 rowB.2) :
    satEventCommonHitCountUpTo N events = 0 := by
  rw [satEventCommonHitCountUpTo_eq_rowEventCommonHitCountUpTo_admissibleFor
    N Pz rhoOf events hadm]
  exact rowEventCommonHitCountUpTo_eq_zero_of_incompatible_pair
    N (satEventResidualHitRowsFinset events) rowA rowB hA hB hincomp

theorem baseSatEventCommonHitCountUpTo_eq_zero_of_incompatible_pair_admissibleFor
    (N Pz b : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (rowA rowB : Nat × Nat)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hA : rowA ∈ satEventResidualHitRowsFinset events)
    (hB : rowB ∈ satEventResidualHitRowsFinset events)
    (hincomp : ¬ residueCompatible rowA.1 rowB.1 rowA.2 rowB.2) :
    baseSatEventCommonHitCountUpTo N Pz b events = 0 := by
  rw [baseSatEventCommonHitCountUpTo_eq_baseRowEventCommonHitCountUpTo_admissibleFor
    N Pz b rhoOf events hadm]
  exact baseRowEventCommonHitCountUpTo_eq_zero_of_incompatible_pair
    N Pz b (satEventResidualHitRowsFinset events) rowA rowB hA hB hincomp

theorem rowEventCommonHitCountUpTo_eq_zero_of_not_pairwiseCompatible
    (N : Nat) (s : Finset (Nat × Nat))
    (hnot : ¬ congruenceRowsPairwiseCompatible s.toList) :
    rowEventCommonHitCountUpTo N s = 0 := by
  rw [rowEventCommonHitCountUpTo_eq_congruenceRowsCountUpTo_toList]
  exact congruenceRowsCountUpTo_eq_zero_of_not_pairwiseCompatible N s.toList hnot

theorem satEventCommonHitCountUpTo_eq_zero_of_not_pairwiseCompatible_admissibleFor
    (N Pz : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hnot : ¬ congruenceRowsPairwiseCompatible
      (satEventResidualHitRowsFinset events).toList) :
    satEventCommonHitCountUpTo N events = 0 := by
  rw [satEventCommonHitCountUpTo_eq_rowEventCommonHitCountUpTo_admissibleFor
    N Pz rhoOf events hadm]
  exact rowEventCommonHitCountUpTo_eq_zero_of_not_pairwiseCompatible
    N (satEventResidualHitRowsFinset events) hnot

theorem satEventSubsets_double_count
    (N r : Nat) (events : Finset SatEvent) :
    (∑ n ∈ Finset.range (N + 1),
        (hitEventSubsetsOfCard events
          (fun event => satEventHit n event) r).card) =
      ∑ s ∈ events.powersetCard r, satEventCommonHitCountUpTo N s := by
  classical
  simpa [satEventCommonHitCountUpTo] using
    (hitEventSubsets_double_count (Finset.range (N + 1)) events
      (fun n event => satEventHit n event) r)

theorem baseSatEventSubsets_double_count
    (N Pz b r : Nat) (events : Finset SatEvent) :
    (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz]),
        (hitEventSubsetsOfCard events
          (fun event => satEventHit n event) r).card) =
      ∑ s ∈ events.powersetCard r,
        baseSatEventCommonHitCountUpTo N Pz b s := by
  classical
  simpa [baseSatEventCommonHitCountUpTo] using
    (hitEventSubsets_double_count
      ((Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz])) events
      (fun n event => satEventHit n event) r)

theorem satEventSubsets_bonferroni_lower_double_count
    (N R : Nat) (events : Finset SatEvent) :
    (∑ n ∈ Finset.range (N + 1),
        (if hitEventCount events (fun event => satEventHit n event) = 0
          then (1 : Int) else 0)) ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((-1 : Int) ^ r) *
          ((∑ s ∈ events.powersetCard r,
              satEventCommonHitCountUpTo N s : Nat) : Int) := by
  classical
  simpa [satEventCommonHitCountUpTo] using
    (hitEventSubsets_bonferroni_lower_double_count
      (Finset.range (N + 1)) events
      (fun n event => satEventHit n event) R)

theorem satEventSubsets_bonferroni_upper_double_count
    (N R : Nat) (events : Finset SatEvent) :
    (∑ n ∈ Finset.range (N + 1),
        alternatingChoosePrefix
          (hitEventCount events (fun event => satEventHit n event)) (2 * R)) ≤
      (∑ n ∈ Finset.range (N + 1),
        (if hitEventCount events (fun event => satEventHit n event) = 0
          then (1 : Int) else 0)) +
      (∑ s ∈ events.powersetCard (2 * R),
        (satEventCommonHitCountUpTo N s : Int)) := by
  classical
  simpa [satEventCommonHitCountUpTo] using
    (hitEventSubsets_bonferroni_upper_double_count
      (Finset.range (N + 1)) events
      (fun n event => satEventHit n event) R)

theorem baseSatEventSubsets_bonferroni_lower_double_count
    (N Pz b R : Nat) (events : Finset SatEvent) :
    (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz]),
        (if hitEventCount events (fun event => satEventHit n event) = 0
          then (1 : Int) else 0)) ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((-1 : Int) ^ r) *
          ((∑ s ∈ events.powersetCard r,
              baseSatEventCommonHitCountUpTo N Pz b s : Nat) : Int) := by
  classical
  simpa [baseSatEventCommonHitCountUpTo] using
    (hitEventSubsets_bonferroni_lower_double_count
      ((Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz])) events
      (fun n event => satEventHit n event) R)

theorem baseSatEventSubsets_bonferroni_upper_double_count
    (N Pz b R : Nat) (events : Finset SatEvent) :
    (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz]),
        alternatingChoosePrefix
          (hitEventCount events (fun event => satEventHit n event)) (2 * R)) ≤
      (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz]),
        (if hitEventCount events (fun event => satEventHit n event) = 0
          then (1 : Int) else 0)) +
      (∑ s ∈ events.powersetCard (2 * R),
        (baseSatEventCommonHitCountUpTo N Pz b s : Int)) := by
  classical
  simpa [baseSatEventCommonHitCountUpTo] using
    (hitEventSubsets_bonferroni_upper_double_count
      ((Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz])) events
      (fun n event => satEventHit n event) R)

theorem baseRowEventCommonHitCountUpTo_eq_zero_of_not_base_pairwiseCompatible
    (N Pz b : Nat) (s : Finset (Nat × Nat))
    (hnot : ¬ congruenceRowsPairwiseCompatible ((Pz, b) :: s.toList)) :
    baseRowEventCommonHitCountUpTo N Pz b s = 0 := by
  rw [baseRowEventCommonHitCountUpTo_eq_baseResidualRowsCountUpTo_toList]
  exact baseResidualRowsCountUpTo_eq_zero_of_not_base_pairwiseCompatible
    N Pz b s.toList hnot

theorem baseSatEventCommonHitCountUpTo_eq_zero_of_not_base_pairwiseCompatible_admissibleFor
    (N Pz b : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hnot : ¬ congruenceRowsPairwiseCompatible
      ((Pz, b) :: (satEventResidualHitRowsFinset events).toList)) :
    baseSatEventCommonHitCountUpTo N Pz b events = 0 := by
  rw [baseSatEventCommonHitCountUpTo_eq_baseRowEventCommonHitCountUpTo_admissibleFor
    N Pz b rhoOf events hadm]
  exact baseRowEventCommonHitCountUpTo_eq_zero_of_not_base_pairwiseCompatible
    N Pz b (satEventResidualHitRowsFinset events) hnot

theorem rowEventSubsets_double_count
    (N r : Nat) (events : Finset (Nat × Nat)) :
    (∑ n ∈ Finset.range (N + 1),
        (hitEventSubsetsOfCard events
          (fun row => n ≡ row.2 [MOD row.1]) r).card) =
      ∑ s ∈ events.powersetCard r, rowEventCommonHitCountUpTo N s := by
  classical
  simpa [rowEventCommonHitCountUpTo] using
    (hitEventSubsets_double_count (Finset.range (N + 1)) events
      (fun n row => n ≡ row.2 [MOD row.1]) r)

theorem baseRowEventSubsets_double_count
    (N Pz b r : Nat) (events : Finset (Nat × Nat)) :
    (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz]),
        (hitEventSubsetsOfCard events
          (fun row => n ≡ row.2 [MOD row.1]) r).card) =
      ∑ s ∈ events.powersetCard r,
        baseRowEventCommonHitCountUpTo N Pz b s := by
  classical
  simpa [baseRowEventCommonHitCountUpTo] using
    (hitEventSubsets_double_count
      ((Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz])) events
      (fun n row => n ≡ row.2 [MOD row.1]) r)

theorem rowEventSubsets_bonferroni_lower_double_count
    (N R : Nat) (events : Finset (Nat × Nat)) :
    (∑ n ∈ Finset.range (N + 1),
        (if hitEventCount events (fun row => n ≡ row.2 [MOD row.1]) = 0
          then (1 : Int) else 0)) ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((-1 : Int) ^ r) *
          ((∑ s ∈ events.powersetCard r,
              rowEventCommonHitCountUpTo N s : Nat) : Int) := by
  classical
  simpa [rowEventCommonHitCountUpTo] using
    (hitEventSubsets_bonferroni_lower_double_count
      (Finset.range (N + 1)) events
      (fun n row => n ≡ row.2 [MOD row.1]) R)

theorem rowEventSubsets_bonferroni_upper_double_count
    (N R : Nat) (events : Finset (Nat × Nat)) :
    (∑ n ∈ Finset.range (N + 1),
        alternatingChoosePrefix
          (hitEventCount events (fun row => n ≡ row.2 [MOD row.1])) (2 * R)) ≤
      (∑ n ∈ Finset.range (N + 1),
        (if hitEventCount events (fun row => n ≡ row.2 [MOD row.1]) = 0
          then (1 : Int) else 0)) +
      (∑ s ∈ events.powersetCard (2 * R),
        (rowEventCommonHitCountUpTo N s : Int)) := by
  classical
  simpa [rowEventCommonHitCountUpTo] using
    (hitEventSubsets_bonferroni_upper_double_count
      (Finset.range (N + 1)) events
      (fun n row => n ≡ row.2 [MOD row.1]) R)

theorem baseRowEventSubsets_bonferroni_lower_double_count
    (N Pz b R : Nat) (events : Finset (Nat × Nat)) :
    (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz]),
        (if hitEventCount events (fun row => n ≡ row.2 [MOD row.1]) = 0
          then (1 : Int) else 0)) ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((-1 : Int) ^ r) *
          ((∑ s ∈ events.powersetCard r,
              baseRowEventCommonHitCountUpTo N Pz b s : Nat) : Int) := by
  classical
  simpa [baseRowEventCommonHitCountUpTo] using
    (hitEventSubsets_bonferroni_lower_double_count
      ((Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz])) events
      (fun n row => n ≡ row.2 [MOD row.1]) R)

theorem baseRowEventSubsets_bonferroni_upper_double_count
    (N Pz b R : Nat) (events : Finset (Nat × Nat)) :
    (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz]),
        alternatingChoosePrefix
          (hitEventCount events (fun row => n ≡ row.2 [MOD row.1])) (2 * R)) ≤
      (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz]),
        (if hitEventCount events (fun row => n ≡ row.2 [MOD row.1]) = 0
          then (1 : Int) else 0)) +
      (∑ s ∈ events.powersetCard (2 * R),
        (baseRowEventCommonHitCountUpTo N Pz b s : Int)) := by
  classical
  simpa [baseRowEventCommonHitCountUpTo] using
    (hitEventSubsets_bonferroni_upper_double_count
      ((Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz])) events
      (fun n row => n ≡ row.2 [MOD row.1]) R)

theorem rowEventCommonHitCountUpTo_le_div_add_one_of_solution
    (N x : Nat) (s : Finset (Nat × Nat))
    (hL : 0 < congruenceLcm s.toList)
    (hx : satisfiesCongruenceRows x s.toList) :
    rowEventCommonHitCountUpTo N s ≤ N / congruenceLcm s.toList + 1 := by
  rw [rowEventCommonHitCountUpTo_eq_congruenceRowsCountUpTo_toList]
  exact congruenceRowsCountUpTo_le_div_add_one_of_solution N x s.toList hL hx

theorem rowEventCommonHitCountUpTo_cast_le_div_add_one_of_solution
    (N x : Nat) (s : Finset (Nat × Nat))
    (hL : 0 < congruenceLcm s.toList)
    (hx : satisfiesCongruenceRows x s.toList) :
    (rowEventCommonHitCountUpTo N s : ℚ) ≤
      (N / congruenceLcm s.toList : Nat) + 1 := by
  exact_mod_cast
    rowEventCommonHitCountUpTo_le_div_add_one_of_solution N x s hL hx

theorem baseRowEventCommonHitCountUpTo_le_div_add_one_of_solution
    (N Pz b x : Nat) (s : Finset (Nat × Nat))
    (hPz : 0 < Pz)
    (hL : 0 < congruenceLcm s.toList)
    (hcop : Nat.Coprime Pz (congruenceLcm s.toList))
    (hxbase : x ≡ b [MOD Pz])
    (hxrows : satisfiesCongruenceRows x s.toList) :
    baseRowEventCommonHitCountUpTo N Pz b s ≤
      N / (Pz * congruenceLcm s.toList) + 1 := by
  rw [baseRowEventCommonHitCountUpTo_eq_baseResidualRowsCountUpTo_toList]
  exact baseResidualRowsCountUpTo_le_div_add_one_of_solution
    N Pz b x s.toList hPz hL hcop hxbase hxrows

theorem baseRowEventCommonHitCountUpTo_cast_le_div_add_one_of_solution
    (N Pz b x : Nat) (s : Finset (Nat × Nat))
    (hPz : 0 < Pz)
    (hL : 0 < congruenceLcm s.toList)
    (hcop : Nat.Coprime Pz (congruenceLcm s.toList))
    (hxbase : x ≡ b [MOD Pz])
    (hxrows : satisfiesCongruenceRows x s.toList) :
    (baseRowEventCommonHitCountUpTo N Pz b s : ℚ) ≤
      (N / (Pz * congruenceLcm s.toList) : Nat) + 1 := by
  exact_mod_cast
    baseRowEventCommonHitCountUpTo_le_div_add_one_of_solution
      N Pz b x s hPz hL hcop hxbase hxrows

noncomputable def rowCompatibleSubsetsOfCard
    (events : Finset (Nat × Nat)) (r : Nat) : Finset (Finset (Nat × Nat)) := by
  classical
  exact (events.powersetCard r).filter
    (fun s => congruenceRowsPairwiseCompatible s.toList)

noncomputable def baseRowCompatibleSubsetsOfCard
    (Pz b : Nat) (events : Finset (Nat × Nat)) (r : Nat) :
    Finset (Finset (Nat × Nat)) := by
  classical
  exact (events.powersetCard r).filter
    (fun s => congruenceRowsPairwiseCompatible ((Pz, b) :: s.toList))

theorem congruenceRowsModuliPositive_toList_of_forall_mem
    (s : Finset (Nat × Nat))
    (hpos : ∀ row ∈ s, 0 < row.1) :
    congruenceRowsModuliPositive s.toList := by
  intro row hrow
  exact hpos row (by simpa using hrow)

theorem congruenceRowsModuliPositive_of_subset
    (events s : Finset (Nat × Nat))
    (hs : s ⊆ events)
    (hpos : ∀ row ∈ events, 0 < row.1) :
    congruenceRowsModuliPositive s.toList :=
  congruenceRowsModuliPositive_toList_of_forall_mem s (by
    intro row hrow
    exact hpos row (hs hrow))

theorem satEventCommonHitCountUpTo_le_div_add_one_of_common_hit
    (N Pz rho x : Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hhit : ∀ event ∈ events, satEventHit x event) :
    satEventCommonHitCountUpTo N events ≤
      N / congruenceLcm (satEventResidualHitRowsFinset events).toList + 1 := by
  rw [satEventCommonHitCountUpTo_eq_rowEventCommonHitCountUpTo
    N Pz rho events hadm]
  have hpos : ∀ row ∈ satEventResidualHitRowsFinset events, 0 < row.1 :=
    satEventResidualHitRowsFinset_moduliPositive_of_admissible Pz rho events hadm
  have hposList : congruenceRowsModuliPositive
      (satEventResidualHitRowsFinset events).toList :=
    congruenceRowsModuliPositive_toList_of_forall_mem
      (satEventResidualHitRowsFinset events) hpos
  have hL : 0 < congruenceLcm (satEventResidualHitRowsFinset events).toList :=
    congruenceLcm_pos_of_rows_positive _ hposList
  have hx : satisfiesCongruenceRows x
      (satEventResidualHitRowsFinset events).toList := by
    intro row hrow
    have hrowFin : row ∈ satEventResidualHitRowsFinset events := by
      simpa using hrow
    rcases Finset.mem_image.mp hrowFin with ⟨event, hevent, hrowEq⟩
    subst hrowEq
    have hdPlusPos : 0 < event.dPlus :=
      (hadm event hevent).2.2.2.2.2.1
    have hpPos : 0 < event.p := (hadm event hevent).1.pos
    have hq : 0 < conditionalModulus event.dPlus event.p :=
      Nat.mul_pos hdPlusPos hpPos
    exact (satEventHit_iff_modEq_residualHitRow x event hq).2
      (hhit event hevent)
  exact rowEventCommonHitCountUpTo_le_div_add_one_of_solution
    N x (satEventResidualHitRowsFinset events) hL hx

theorem baseSatEventCommonHitCountUpTo_le_div_add_one_of_common_hit
    (N Pz b rho x : Nat) (events : Finset SatEvent)
    (hPz : 0 < Pz)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hpCop : ∀ event ∈ events, Nat.Coprime Pz event.p)
    (hxbase : x ≡ b [MOD Pz])
    (hhit : ∀ event ∈ events, satEventHit x event) :
    baseSatEventCommonHitCountUpTo N Pz b events ≤
      N / (Pz * congruenceLcm (satEventResidualHitRowsFinset events).toList) + 1 := by
  rw [baseSatEventCommonHitCountUpTo_eq_baseRowEventCommonHitCountUpTo
    N Pz b rho events hadm]
  have hpos : ∀ row ∈ satEventResidualHitRowsFinset events, 0 < row.1 :=
    satEventResidualHitRowsFinset_moduliPositive_of_admissible Pz rho events hadm
  have hposList : congruenceRowsModuliPositive
      (satEventResidualHitRowsFinset events).toList :=
    congruenceRowsModuliPositive_toList_of_forall_mem
      (satEventResidualHitRowsFinset events) hpos
  have hL : 0 < congruenceLcm (satEventResidualHitRowsFinset events).toList :=
    congruenceLcm_pos_of_rows_positive _ hposList
  have hcopRows : ∀ row ∈ satEventResidualHitRowsFinset events,
      Nat.Coprime Pz row.1 :=
    satEventResidualHitRowsFinset_base_coprime_of_admissible
      Pz rho events hadm hpCop
  have hcop : Nat.Coprime Pz
      (congruenceLcm (satEventResidualHitRowsFinset events).toList) :=
    congruenceLcm_coprime_of_rows_coprime Pz
      (satEventResidualHitRowsFinset events).toList hPz hposList (by
        intro row hrow
        exact hcopRows row (by simpa using hrow))
  have hxrows : satisfiesCongruenceRows x
      (satEventResidualHitRowsFinset events).toList := by
    intro row hrow
    have hrowFin : row ∈ satEventResidualHitRowsFinset events := by
      simpa using hrow
    rcases Finset.mem_image.mp hrowFin with ⟨event, hevent, hrowEq⟩
    subst hrowEq
    have hdPlusPos : 0 < event.dPlus :=
      (hadm event hevent).2.2.2.2.2.1
    have hpPos : 0 < event.p := (hadm event hevent).1.pos
    have hq : 0 < conditionalModulus event.dPlus event.p :=
      Nat.mul_pos hdPlusPos hpPos
    exact (satEventHit_iff_modEq_residualHitRow x event hq).2
      (hhit event hevent)
  exact baseRowEventCommonHitCountUpTo_le_div_add_one_of_solution
    N Pz b x (satEventResidualHitRowsFinset events) hPz hL hcop hxbase hxrows

theorem satEventCommonHitCountUpTo_le_div_add_one_of_common_hit_admissibleFor
    (N Pz x : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hhit : ∀ event ∈ events, satEventHit x event) :
    satEventCommonHitCountUpTo N events ≤
      N / congruenceLcm (satEventResidualHitRowsFinset events).toList + 1 := by
  rw [satEventCommonHitCountUpTo_eq_rowEventCommonHitCountUpTo_admissibleFor
    N Pz rhoOf events hadm]
  have hpos : ∀ row ∈ satEventResidualHitRowsFinset events, 0 < row.1 :=
    satEventResidualHitRowsFinset_moduliPositive_of_admissibleFor
      Pz rhoOf events hadm
  have hposList : congruenceRowsModuliPositive
      (satEventResidualHitRowsFinset events).toList :=
    congruenceRowsModuliPositive_toList_of_forall_mem
      (satEventResidualHitRowsFinset events) hpos
  have hL : 0 < congruenceLcm (satEventResidualHitRowsFinset events).toList :=
    congruenceLcm_pos_of_rows_positive _ hposList
  have hx : satisfiesCongruenceRows x
      (satEventResidualHitRowsFinset events).toList := by
    intro row hrow
    have hrowFin : row ∈ satEventResidualHitRowsFinset events := by
      simpa using hrow
    rcases Finset.mem_image.mp hrowFin with ⟨event, hevent, hrowEq⟩
    subst hrowEq
    have heventAdm : satEventAdmissible Pz (rhoOf event.e) event := by
      simpa [satEventAdmissibleFor] using hadm event hevent
    have hq : 0 < conditionalModulus event.dPlus event.p :=
      Nat.mul_pos heventAdm.2.2.2.2.2.1 heventAdm.1.pos
    exact (satEventHit_iff_modEq_residualHitRow x event hq).2
      (hhit event hevent)
  exact rowEventCommonHitCountUpTo_le_div_add_one_of_solution
    N x (satEventResidualHitRowsFinset events) hL hx

theorem baseSatEventCommonHitCountUpTo_le_div_add_one_of_common_hit_admissibleFor
    (N Pz b x : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hPz : 0 < Pz)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hpCop : ∀ event ∈ events, Nat.Coprime Pz event.p)
    (hxbase : x ≡ b [MOD Pz])
    (hhit : ∀ event ∈ events, satEventHit x event) :
    baseSatEventCommonHitCountUpTo N Pz b events ≤
      N / (Pz * congruenceLcm (satEventResidualHitRowsFinset events).toList) + 1 := by
  rw [baseSatEventCommonHitCountUpTo_eq_baseRowEventCommonHitCountUpTo_admissibleFor
    N Pz b rhoOf events hadm]
  have hpos : ∀ row ∈ satEventResidualHitRowsFinset events, 0 < row.1 :=
    satEventResidualHitRowsFinset_moduliPositive_of_admissibleFor
      Pz rhoOf events hadm
  have hposList : congruenceRowsModuliPositive
      (satEventResidualHitRowsFinset events).toList :=
    congruenceRowsModuliPositive_toList_of_forall_mem
      (satEventResidualHitRowsFinset events) hpos
  have hL : 0 < congruenceLcm (satEventResidualHitRowsFinset events).toList :=
    congruenceLcm_pos_of_rows_positive _ hposList
  have hcopRows : ∀ row ∈ satEventResidualHitRowsFinset events,
      Nat.Coprime Pz row.1 :=
    satEventResidualHitRowsFinset_base_coprime_of_admissibleFor
      Pz rhoOf events hadm hpCop
  have hcop : Nat.Coprime Pz
      (congruenceLcm (satEventResidualHitRowsFinset events).toList) :=
    congruenceLcm_coprime_of_rows_coprime Pz
      (satEventResidualHitRowsFinset events).toList hPz hposList (by
        intro row hrow
        exact hcopRows row (by simpa using hrow))
  have hxrows : satisfiesCongruenceRows x
      (satEventResidualHitRowsFinset events).toList := by
    intro row hrow
    have hrowFin : row ∈ satEventResidualHitRowsFinset events := by
      simpa using hrow
    rcases Finset.mem_image.mp hrowFin with ⟨event, hevent, hrowEq⟩
    subst hrowEq
    have heventAdm : satEventAdmissible Pz (rhoOf event.e) event := by
      simpa [satEventAdmissibleFor] using hadm event hevent
    have hq : 0 < conditionalModulus event.dPlus event.p :=
      Nat.mul_pos heventAdm.2.2.2.2.2.1 heventAdm.1.pos
    exact (satEventHit_iff_modEq_residualHitRow x event hq).2
      (hhit event hevent)
  exact baseRowEventCommonHitCountUpTo_le_div_add_one_of_solution
    N Pz b x (satEventResidualHitRowsFinset events) hPz hL hcop hxbase hxrows

/-- Matching rational lower endpoint estimate for a nonempty compatible
conditioned intersection.  Together with the preceding upper bound, this is
the exact `N / (Pz L) + O(1)` statement used by finite transfer. -/
theorem baseSatEventCommonHitCountUpTo_rat_lower_of_common_hit_admissibleFor
    (N Pz b x : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hPz : 0 < Pz)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hpCop : ∀ event ∈ events, Nat.Coprime Pz event.p)
    (hxbase : x ≡ b [MOD Pz])
    (hhit : ∀ event ∈ events, satEventHit x event) :
    (N : ℚ) /
          ((Pz * congruenceLcm
            (satEventResidualHitRowsFinset events).toList : Nat) : ℚ) - 1 ≤
      (baseSatEventCommonHitCountUpTo N Pz b events : ℚ) := by
  have hpos : ∀ row ∈ satEventResidualHitRowsFinset events, 0 < row.1 :=
    satEventResidualHitRowsFinset_moduliPositive_of_admissibleFor
      Pz rhoOf events hadm
  have hposList : congruenceRowsModuliPositive
      (satEventResidualHitRowsFinset events).toList :=
    congruenceRowsModuliPositive_toList_of_forall_mem
      (satEventResidualHitRowsFinset events) hpos
  have hL : 0 < congruenceLcm
      (satEventResidualHitRowsFinset events).toList :=
    congruenceLcm_pos_of_rows_positive _ hposList
  have hcopRows : ∀ row ∈ satEventResidualHitRowsFinset events,
      Nat.Coprime Pz row.1 :=
    satEventResidualHitRowsFinset_base_coprime_of_admissibleFor
      Pz rhoOf events hadm hpCop
  have hcop : Nat.Coprime Pz
      (congruenceLcm (satEventResidualHitRowsFinset events).toList) :=
    congruenceLcm_coprime_of_rows_coprime Pz
      (satEventResidualHitRowsFinset events).toList hPz hposList (by
        intro row hrow
        exact hcopRows row (by simpa using hrow))
  have hxrows : satisfiesCongruenceRows x
      (satEventResidualHitRowsFinset events).toList := by
    intro row hrow
    have hrowFin : row ∈ satEventResidualHitRowsFinset events := by
      simpa using hrow
    rcases Finset.mem_image.mp hrowFin with ⟨event, hevent, hrowEq⟩
    subst hrowEq
    have heventAdm : satEventAdmissible Pz (rhoOf event.e) event := by
      simpa [satEventAdmissibleFor] using hadm event hevent
    have hq : 0 < conditionalModulus event.dPlus event.p :=
      Nat.mul_pos heventAdm.2.2.2.2.2.1 heventAdm.1.pos
    exact (satEventHit_iff_modEq_residualHitRow x event hq).2
      (hhit event hevent)
  rw [baseSatEventCommonHitCountUpTo_eq_baseRowEventCommonHitCountUpTo_admissibleFor
    N Pz b rhoOf events hadm]
  rw [baseRowEventCommonHitCountUpTo_eq_residueClassCountUpTo_of_solution
    N Pz b x (satEventResidualHitRowsFinset events) hcop hxbase hxrows]
  exact div_sub_one_le_residueClassCountUpTo_cast
    N (Pz * congruenceLcm (satEventResidualHitRowsFinset events).toList) x
      (Nat.mul_pos hPz hL)

theorem satEventCommonHitCountUpTo_eq_zero_of_no_common_hit
    (N : Nat) (events : Finset SatEvent)
    (hnone : ¬ ∃ x : Nat, ∀ event ∈ events, satEventHit x event) :
    satEventCommonHitCountUpTo N events = 0 := by
  classical
  unfold satEventCommonHitCountUpTo eventSubsetCommonHitCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _hxrange hxhit
  exact hnone ⟨x, hxhit⟩

theorem baseSatEventCommonHitCountUpTo_eq_zero_of_no_common_base_hit
    (N Pz b : Nat) (events : Finset SatEvent)
    (hnone :
      ¬ ∃ x : Nat, x ≡ b [MOD Pz] ∧
        ∀ event ∈ events, satEventHit x event) :
    baseSatEventCommonHitCountUpTo N Pz b events = 0 := by
  classical
  unfold baseSatEventCommonHitCountUpTo eventSubsetCommonHitCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hxrange hxhit
  have hxbase : x ≡ b [MOD Pz] := (Finset.mem_filter.mp hxrange).2
  exact hnone ⟨x, hxbase, hxhit⟩

theorem satEventCommonHitSum_le_event_lcm_bound
    (N Pz rho r : Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event) :
    (∑ s ∈ events.powersetCard r, satEventCommonHitCountUpTo N s) ≤
      ∑ s ∈ events.powersetCard r,
        (N / congruenceLcm (satEventResidualHitRowsFinset s).toList + 1) := by
  classical
  apply Finset.sum_le_sum
  intro s hs
  have hsubset : s ⊆ events := (Finset.mem_powersetCard.mp hs).1
  have hsadm : ∀ event ∈ s, satEventAdmissible Pz rho event := by
    intro event hevent
    exact hadm event (hsubset hevent)
  by_cases hhit : ∃ x : Nat, ∀ event ∈ s, satEventHit x event
  · rcases hhit with ⟨x, hxhit⟩
    exact satEventCommonHitCountUpTo_le_div_add_one_of_common_hit
      N Pz rho x s hsadm hxhit
  · have hzero :
        satEventCommonHitCountUpTo N s = 0 :=
      satEventCommonHitCountUpTo_eq_zero_of_no_common_hit N s hhit
    simp [hzero]

theorem baseSatEventCommonHitSum_le_event_lcm_bound
    (N Pz b rho r : Nat) (events : Finset SatEvent)
    (hPz : 0 < Pz)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hpCop : ∀ event ∈ events, Nat.Coprime Pz event.p) :
    (∑ s ∈ events.powersetCard r, baseSatEventCommonHitCountUpTo N Pz b s) ≤
      ∑ s ∈ events.powersetCard r,
        (N / (Pz * congruenceLcm (satEventResidualHitRowsFinset s).toList) + 1) := by
  classical
  apply Finset.sum_le_sum
  intro s hs
  have hsubset : s ⊆ events := (Finset.mem_powersetCard.mp hs).1
  have hsadm : ∀ event ∈ s, satEventAdmissible Pz rho event := by
    intro event hevent
    exact hadm event (hsubset hevent)
  have hsCop : ∀ event ∈ s, Nat.Coprime Pz event.p := by
    intro event hevent
    exact hpCop event (hsubset hevent)
  by_cases hhit :
      ∃ x : Nat, x ≡ b [MOD Pz] ∧
        ∀ event ∈ s, satEventHit x event
  · rcases hhit with ⟨x, hxbase, hxhit⟩
    exact baseSatEventCommonHitCountUpTo_le_div_add_one_of_common_hit
      N Pz b rho x s hPz hsadm hsCop hxbase hxhit
  · have hzero :
        baseSatEventCommonHitCountUpTo N Pz b s = 0 :=
      baseSatEventCommonHitCountUpTo_eq_zero_of_no_common_base_hit
        N Pz b s hhit
    simp [hzero]

theorem satEventCommonHitSum_le_event_lcm_bound_admissibleFor
    (N Pz r : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event) :
    (∑ s ∈ events.powersetCard r, satEventCommonHitCountUpTo N s) ≤
      ∑ s ∈ events.powersetCard r,
        (N / congruenceLcm (satEventResidualHitRowsFinset s).toList + 1) := by
  classical
  apply Finset.sum_le_sum
  intro s hs
  have hsubset : s ⊆ events := (Finset.mem_powersetCard.mp hs).1
  have hsadm : ∀ event ∈ s, satEventAdmissibleFor Pz rhoOf event := by
    intro event hevent
    exact hadm event (hsubset hevent)
  by_cases hhit : ∃ x : Nat, ∀ event ∈ s, satEventHit x event
  · rcases hhit with ⟨x, hxhit⟩
    exact satEventCommonHitCountUpTo_le_div_add_one_of_common_hit_admissibleFor
      N Pz x rhoOf s hsadm hxhit
  · have hzero :
        satEventCommonHitCountUpTo N s = 0 :=
      satEventCommonHitCountUpTo_eq_zero_of_no_common_hit N s hhit
    simp [hzero]

theorem baseSatEventCommonHitSum_le_event_lcm_bound_admissibleFor
    (N Pz b r : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hPz : 0 < Pz)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hpCop : ∀ event ∈ events, Nat.Coprime Pz event.p) :
    (∑ s ∈ events.powersetCard r, baseSatEventCommonHitCountUpTo N Pz b s) ≤
      ∑ s ∈ events.powersetCard r,
        (N / (Pz * congruenceLcm (satEventResidualHitRowsFinset s).toList) + 1) := by
  classical
  apply Finset.sum_le_sum
  intro s hs
  have hsubset : s ⊆ events := (Finset.mem_powersetCard.mp hs).1
  have hsadm : ∀ event ∈ s, satEventAdmissibleFor Pz rhoOf event := by
    intro event hevent
    exact hadm event (hsubset hevent)
  have hsCop : ∀ event ∈ s, Nat.Coprime Pz event.p := by
    intro event hevent
    exact hpCop event (hsubset hevent)
  by_cases hhit :
      ∃ x : Nat, x ≡ b [MOD Pz] ∧
        ∀ event ∈ s, satEventHit x event
  · rcases hhit with ⟨x, hxbase, hxhit⟩
    exact baseSatEventCommonHitCountUpTo_le_div_add_one_of_common_hit_admissibleFor
      N Pz b x rhoOf s hPz hsadm hsCop hxbase hxhit
  · have hzero :
        baseSatEventCommonHitCountUpTo N Pz b s = 0 :=
      baseSatEventCommonHitCountUpTo_eq_zero_of_no_common_base_hit
        N Pz b s hhit
    simp [hzero]

theorem rowEventCommonHitSum_le_compatible_lcm_bound
    (N r : Nat) (events : Finset (Nat × Nat))
    (hpos : ∀ row ∈ events, 0 < row.1) :
    (∑ s ∈ events.powersetCard r, rowEventCommonHitCountUpTo N s) ≤
      ∑ s ∈ rowCompatibleSubsetsOfCard events r,
        (N / congruenceLcm s.toList + 1) := by
  classical
  calc
    (∑ s ∈ events.powersetCard r, rowEventCommonHitCountUpTo N s) ≤
        ∑ s ∈ events.powersetCard r,
          if congruenceRowsPairwiseCompatible s.toList then
            N / congruenceLcm s.toList + 1
          else 0 := by
            apply Finset.sum_le_sum
            intro s hs
            by_cases hcompat : congruenceRowsPairwiseCompatible s.toList
            · simp [hcompat]
              have hsubset : s ⊆ events := (Finset.mem_powersetCard.mp hs).1
              have hposList : congruenceRowsModuliPositive s.toList :=
                congruenceRowsModuliPositive_of_subset events s hsubset hpos
              have hL : 0 < congruenceLcm s.toList :=
                congruenceLcm_pos_of_rows_positive s.toList hposList
              rcases congruenceRows_solution_exists_of_pairwiseCompatible
                  s.toList hposList hcompat with ⟨x, hx⟩
              exact rowEventCommonHitCountUpTo_le_div_add_one_of_solution
                N x s hL hx
            · have hzero :
                  rowEventCommonHitCountUpTo N s = 0 := by
                rw [rowEventCommonHitCountUpTo_eq_congruenceRowsCountUpTo_toList]
                exact congruenceRowsCountUpTo_eq_zero_of_not_pairwiseCompatible
                  N s.toList hcompat
              simp [hcompat, hzero]
    _ = ∑ s ∈ rowCompatibleSubsetsOfCard events r,
        (N / congruenceLcm s.toList + 1) := by
          exact (Finset.sum_filter
            (s := events.powersetCard r)
            (p := fun s => congruenceRowsPairwiseCompatible s.toList)
            (f := fun s => N / congruenceLcm s.toList + 1)).symm

theorem baseRowEventCommonHitSum_le_compatible_lcm_bound
    (N Pz b r : Nat) (events : Finset (Nat × Nat))
    (hPz : 0 < Pz)
    (hpos : ∀ row ∈ events, 0 < row.1)
    (hcopRows : ∀ row ∈ events, Nat.Coprime Pz row.1) :
    (∑ s ∈ events.powersetCard r, baseRowEventCommonHitCountUpTo N Pz b s) ≤
      ∑ s ∈ baseRowCompatibleSubsetsOfCard Pz b events r,
        (N / (Pz * congruenceLcm s.toList) + 1) := by
  classical
  calc
    (∑ s ∈ events.powersetCard r, baseRowEventCommonHitCountUpTo N Pz b s) ≤
        ∑ s ∈ events.powersetCard r,
          if congruenceRowsPairwiseCompatible ((Pz, b) :: s.toList) then
            N / (Pz * congruenceLcm s.toList) + 1
          else 0 := by
            apply Finset.sum_le_sum
            intro s hs
            by_cases hcompat :
                congruenceRowsPairwiseCompatible ((Pz, b) :: s.toList)
            · simp [hcompat]
              have hsubset : s ⊆ events := (Finset.mem_powersetCard.mp hs).1
              have hposList : congruenceRowsModuliPositive s.toList :=
                congruenceRowsModuliPositive_of_subset events s hsubset hpos
              have hL : 0 < congruenceLcm s.toList :=
                congruenceLcm_pos_of_rows_positive s.toList hposList
              have hcop : Nat.Coprime Pz (congruenceLcm s.toList) :=
                congruenceLcm_coprime_of_rows_coprime Pz s.toList hPz
                  hposList (by
                    intro row hrow
                    have hsrow : row ∈ s := by simpa using hrow
                    exact hcopRows row (hsubset hsrow))
              rcases baseResidualRows_solution_exists_of_pairwiseCompatible
                  Pz b s.toList hPz hposList hcompat with ⟨x, hxbase, hxrows⟩
              exact baseRowEventCommonHitCountUpTo_le_div_add_one_of_solution
                N Pz b x s hPz hL hcop hxbase hxrows
            · have hzero :
                  baseRowEventCommonHitCountUpTo N Pz b s = 0 :=
                baseRowEventCommonHitCountUpTo_eq_zero_of_not_base_pairwiseCompatible
                  N Pz b s hcompat
              simp [hcompat, hzero]
    _ = ∑ s ∈ baseRowCompatibleSubsetsOfCard Pz b events r,
        (N / (Pz * congruenceLcm s.toList) + 1) := by
          exact (Finset.sum_filter
            (s := events.powersetCard r)
            (p := fun s => congruenceRowsPairwiseCompatible ((Pz, b) :: s.toList))
            (f := fun s => N / (Pz * congruenceLcm s.toList) + 1)).symm

noncomputable def rowNoHitIndicatorSumUpTo
    (N : Nat) (events : Finset (Nat × Nat)) : Int :=
  ∑ n ∈ Finset.range (N + 1),
    if hitEventCount events (fun row => n ≡ row.2 [MOD row.1]) = 0
    then (1 : Int) else 0

noncomputable def baseRowNoHitIndicatorSumUpTo
    (N Pz b : Nat) (events : Finset (Nat × Nat)) : Int :=
  ∑ n ∈ (Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz]),
    if hitEventCount events (fun row => n ≡ row.2 [MOD row.1]) = 0
    then (1 : Int) else 0

noncomputable def satEventNoHitIndicatorSumUpTo
    (N : Nat) (events : Finset SatEvent) : Int := by
  classical
  exact ∑ n ∈ Finset.range (N + 1),
    if hitEventCount events (fun event => satEventHit n event) = 0
    then (1 : Int) else 0

noncomputable def baseSatEventNoHitIndicatorSumUpTo
    (N Pz b : Nat) (events : Finset SatEvent) : Int := by
  classical
  exact ∑ n ∈ (Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz]),
    if hitEventCount events (fun event => satEventHit n event) = 0
    then (1 : Int) else 0

theorem exists_hit_of_noHitIndicatorSum_lt_card
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (points : Finset β) (events : Finset α)
    (contains : β → α → Prop) [∀ x i, Decidable (contains x i)]
    (B : Int)
    (hbound :
      (∑ x ∈ points,
        if hitEventCount events (fun i => contains x i) = 0
        then (1 : Int) else 0) ≤ B)
    (hlt : B < (points.card : Int)) :
    ∃ x ∈ points, ∃ event ∈ events, contains x event := by
  classical
  by_contra hnone
  have hallZero :
      ∀ x ∈ points, hitEventCount events (fun i => contains x i) = 0 := by
    intro x hx
    unfold hitEventCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro event hevent hcontains
    exact hnone ⟨x, hx, event, hevent, hcontains⟩
  have hsumEq :
      (∑ x ∈ points,
        if hitEventCount events (fun i => contains x i) = 0
        then (1 : Int) else 0) = (points.card : Int) := by
    calc
      (∑ x ∈ points,
        if hitEventCount events (fun i => contains x i) = 0
        then (1 : Int) else 0) =
          ∑ _x ∈ points, (1 : Int) := by
            apply Finset.sum_congr rfl
            intro x hx
            simp [hallZero x hx]
      _ = (points.card : Int) := by
            simp
  have hcardLeB : (points.card : Int) ≤ B := by
    simpa [hsumEq] using hbound
  exact (not_lt_of_ge hcardLeB) hlt

theorem exists_hit_of_noHitIndicatorSum_rat_lt_card
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (points : Finset β) (events : Finset α)
    (contains : β → α → Prop) [∀ x i, Decidable (contains x i)]
    (B : ℚ)
    (hbound :
      ((∑ x ∈ points,
        if hitEventCount events (fun i => contains x i) = 0
        then (1 : Int) else 0) : ℚ) ≤ B)
    (hlt : B < (points.card : ℚ)) :
    ∃ x ∈ points, ∃ event ∈ events, contains x event := by
  classical
  by_contra hnone
  have hallZero :
      ∀ x ∈ points, hitEventCount events (fun i => contains x i) = 0 := by
    intro x hx
    unfold hitEventCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro event hevent hcontains
    exact hnone ⟨x, hx, event, hevent, hcontains⟩
  have hsumEq :
      (∑ x ∈ points,
        if hitEventCount events (fun i => contains x i) = 0
        then (1 : ℚ) else 0) = (points.card : ℚ) := by
    calc
      (∑ x ∈ points,
        if hitEventCount events (fun i => contains x i) = 0
        then (1 : ℚ) else 0) =
          ∑ _x ∈ points, (1 : ℚ) := by
            apply Finset.sum_congr rfl
            intro x hx
            simp [hallZero x hx]
      _ = (points.card : ℚ) := by
            simp
  have hcardLeB : (points.card : ℚ) ≤ B := by
    rw [← hsumEq]
    exact hbound
  exact (not_lt_of_ge hcardLeB) hlt

theorem exists_satEventHit_of_noHitIndicatorSum_lt
    (N : Nat) (events : Finset SatEvent) (B : Int)
    (hbound : satEventNoHitIndicatorSumUpTo N events ≤ B)
    (hlt : B < ((N + 1 : Nat) : Int)) :
    ∃ n : Nat, n ≤ N ∧ ∃ event ∈ events, satEventHit n event := by
  classical
  rcases exists_hit_of_noHitIndicatorSum_lt_card
      (Finset.range (N + 1)) events
      (fun n event => satEventHit n event) B
      (by simpa [satEventNoHitIndicatorSumUpTo] using hbound)
      (by simpa using hlt) with
    ⟨n, hnRange, event, hevent, hhit⟩
  have hnLe : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hnRange)
  exact ⟨n, hnLe, event, hevent, hhit⟩

theorem exists_satEventHit_of_noHitIndicatorSum_rat_lt
    (N : Nat) (events : Finset SatEvent) (B : ℚ)
    (hbound : (satEventNoHitIndicatorSumUpTo N events : ℚ) ≤ B)
    (hlt : B < ((N + 1 : Nat) : ℚ)) :
    ∃ n : Nat, n ≤ N ∧ ∃ event ∈ events, satEventHit n event := by
  classical
  rcases exists_hit_of_noHitIndicatorSum_rat_lt_card
      (Finset.range (N + 1)) events
      (fun n event => satEventHit n event) B
      (by simpa [satEventNoHitIndicatorSumUpTo] using hbound)
      (by simpa using hlt) with
    ⟨n, hnRange, event, hevent, hhit⟩
  have hnLe : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hnRange)
  exact ⟨n, hnLe, event, hevent, hhit⟩

theorem exists_baseSatEventHit_of_baseNoHitIndicatorSum_lt
    (N Pz b : Nat) (events : Finset SatEvent) (B : Int)
    (hbound : baseSatEventNoHitIndicatorSumUpTo N Pz b events ≤ B)
    (hlt :
      B <
        (((Finset.range (N + 1)).filter
          (fun n => n ≡ b [MOD Pz])).card : Int)) :
    ∃ n : Nat, n ≤ N ∧ n ≡ b [MOD Pz] ∧
      ∃ event ∈ events, satEventHit n event := by
  classical
  rcases exists_hit_of_noHitIndicatorSum_lt_card
      ((Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz]))
      events
      (fun n event => satEventHit n event) B
      (by simpa [baseSatEventNoHitIndicatorSumUpTo] using hbound)
      hlt with
    ⟨n, hnFilter, event, hevent, hhit⟩
  have hnRange : n ∈ Finset.range (N + 1) :=
    (Finset.mem_filter.mp hnFilter).1
  have hnBase : n ≡ b [MOD Pz] :=
    (Finset.mem_filter.mp hnFilter).2
  have hnLe : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hnRange)
  exact ⟨n, hnLe, hnBase, event, hevent, hhit⟩

theorem exists_baseSatEventHit_of_baseNoHitIndicatorSum_rat_lt
    (N Pz b : Nat) (events : Finset SatEvent) (B : ℚ)
    (hbound : (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤ B)
    (hlt :
      B <
        (((Finset.range (N + 1)).filter
          (fun n => n ≡ b [MOD Pz])).card : ℚ)) :
    ∃ n : Nat, n ≤ N ∧ n ≡ b [MOD Pz] ∧
      ∃ event ∈ events, satEventHit n event := by
  classical
  rcases exists_hit_of_noHitIndicatorSum_rat_lt_card
      ((Finset.range (N + 1)).filter (fun n => n ≡ b [MOD Pz]))
      events
      (fun n event => satEventHit n event) B
      (by simpa [baseSatEventNoHitIndicatorSumUpTo] using hbound)
      hlt with
    ⟨n, hnFilter, event, hevent, hhit⟩
  have hnRange : n ∈ Finset.range (N + 1) :=
    (Finset.mem_filter.mp hnFilter).1
  have hnBase : n ≡ b [MOD Pz] :=
    (Finset.mem_filter.mp hnFilter).2
  have hnLe : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hnRange)
  exact ⟨n, hnLe, hnBase, event, hevent, hhit⟩

noncomputable def satEventSignedCommonHitSumUpTo
    (N R : Nat) (events : Finset SatEvent) : Int :=
  ∑ r ∈ Finset.range (2 * R + 1),
    ((-1 : Int) ^ r) *
      ((∑ s ∈ events.powersetCard r,
          satEventCommonHitCountUpTo N s : Nat) : Int)

noncomputable def baseSatEventSignedCommonHitSumUpTo
    (N Pz b R : Nat) (events : Finset SatEvent) : Int :=
  ∑ r ∈ Finset.range (2 * R + 1),
    ((-1 : Int) ^ r) *
      ((∑ s ∈ events.powersetCard r,
          baseSatEventCommonHitCountUpTo N Pz b s : Nat) : Int)

theorem satEventFiniteIntervalTransfer_bonferroni_skeleton
    (N R : Nat) (events : Finset SatEvent) :
    satEventNoHitIndicatorSumUpTo N events ≤
      satEventSignedCommonHitSumUpTo N R events := by
  simpa [satEventNoHitIndicatorSumUpTo, satEventSignedCommonHitSumUpTo] using
    satEventSubsets_bonferroni_lower_double_count N R events

theorem baseSatEventFiniteIntervalTransfer_bonferroni_skeleton
    (N Pz b R : Nat) (events : Finset SatEvent) :
    baseSatEventNoHitIndicatorSumUpTo N Pz b events ≤
      baseSatEventSignedCommonHitSumUpTo N Pz b R events := by
  simpa [baseSatEventNoHitIndicatorSumUpTo,
    baseSatEventSignedCommonHitSumUpTo] using
    baseSatEventSubsets_bonferroni_lower_double_count N Pz b R events

theorem satEventFiniteIntervalTransfer_of_signed_bound
    (N R : Nat) (events : Finset SatEvent) (B : Int)
    (hsigned : satEventSignedCommonHitSumUpTo N R events ≤ B) :
    satEventNoHitIndicatorSumUpTo N events ≤ B :=
  le_trans (satEventFiniteIntervalTransfer_bonferroni_skeleton N R events)
    hsigned

theorem baseSatEventFiniteIntervalTransfer_of_signed_bound
    (N Pz b R : Nat) (events : Finset SatEvent) (B : Int)
    (hsigned : baseSatEventSignedCommonHitSumUpTo N Pz b R events ≤ B) :
    baseSatEventNoHitIndicatorSumUpTo N Pz b events ≤ B :=
  le_trans (baseSatEventFiniteIntervalTransfer_bonferroni_skeleton
    N Pz b R events) hsigned

theorem satEventFiniteIntervalTransfer_of_rank_signed_bounds
    (N R : Nat) (events : Finset SatEvent) (B : Nat → Int)
    (hrank : ∀ r ∈ Finset.range (2 * R + 1),
      ((-1 : Int) ^ r) *
        ((∑ s ∈ events.powersetCard r,
            satEventCommonHitCountUpTo N s : Nat) : Int) ≤ B r) :
    satEventNoHitIndicatorSumUpTo N events ≤
      ∑ r ∈ Finset.range (2 * R + 1), B r := by
  apply le_trans (satEventFiniteIntervalTransfer_bonferroni_skeleton
    N R events)
  unfold satEventSignedCommonHitSumUpTo
  apply Finset.sum_le_sum
  intro r hr
  exact hrank r hr

theorem baseSatEventFiniteIntervalTransfer_of_rank_signed_bounds
    (N Pz b R : Nat) (events : Finset SatEvent) (B : Nat → Int)
    (hrank : ∀ r ∈ Finset.range (2 * R + 1),
      ((-1 : Int) ^ r) *
        ((∑ s ∈ events.powersetCard r,
            baseSatEventCommonHitCountUpTo N Pz b s : Nat) : Int) ≤ B r) :
    baseSatEventNoHitIndicatorSumUpTo N Pz b events ≤
      ∑ r ∈ Finset.range (2 * R + 1), B r := by
  apply le_trans (baseSatEventFiniteIntervalTransfer_bonferroni_skeleton
    N Pz b R events)
  unfold baseSatEventSignedCommonHitSumUpTo
  apply Finset.sum_le_sum
  intro r hr
  exact hrank r hr

theorem satEventFiniteIntervalTransfer_rat_of_rank_signed_bounds
    (N R : Nat) (events : Finset SatEvent) (B : Nat → ℚ)
    (hrank : ∀ r ∈ Finset.range (2 * R + 1),
      (((-1 : Int) ^ r) *
        ((∑ s ∈ events.powersetCard r,
            satEventCommonHitCountUpTo N s : Nat) : Int) : ℚ) ≤ B r) :
    (satEventNoHitIndicatorSumUpTo N events : ℚ) ≤
      ∑ r ∈ Finset.range (2 * R + 1), B r := by
  have hskeleton :=
    satEventFiniteIntervalTransfer_bonferroni_skeleton N R events
  calc
    (satEventNoHitIndicatorSumUpTo N events : ℚ) ≤
        (satEventSignedCommonHitSumUpTo N R events : ℚ) := by
          exact_mod_cast hskeleton
    _ = ∑ r ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ r) *
          ((∑ s ∈ events.powersetCard r,
              satEventCommonHitCountUpTo N s : Nat) : Int) : ℚ) := by
          simp [satEventSignedCommonHitSumUpTo]
    _ ≤ ∑ r ∈ Finset.range (2 * R + 1), B r := by
          apply Finset.sum_le_sum
          intro r hr
          exact hrank r hr

theorem baseSatEventFiniteIntervalTransfer_rat_of_rank_signed_bounds
    (N Pz b R : Nat) (events : Finset SatEvent) (B : Nat → ℚ)
    (hrank : ∀ r ∈ Finset.range (2 * R + 1),
      (((-1 : Int) ^ r) *
        ((∑ s ∈ events.powersetCard r,
            baseSatEventCommonHitCountUpTo N Pz b s : Nat) : Int) : ℚ) ≤ B r) :
    (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤
      ∑ r ∈ Finset.range (2 * R + 1), B r := by
  have hskeleton :=
    baseSatEventFiniteIntervalTransfer_bonferroni_skeleton N Pz b R events
  calc
    (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤
        (baseSatEventSignedCommonHitSumUpTo N Pz b R events : ℚ) := by
          exact_mod_cast hskeleton
    _ = ∑ r ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ r) *
          ((∑ s ∈ events.powersetCard r,
              baseSatEventCommonHitCountUpTo N Pz b s : Nat) : Int) : ℚ) := by
          simp [baseSatEventSignedCommonHitSumUpTo]
    _ ≤ ∑ r ∈ Finset.range (2 * R + 1), B r := by
          apply Finset.sum_le_sum
          intro r hr
          exact hrank r hr

theorem negOnePow_mul_natCast_le_of_even_or_odd_budget
    (r n : Nat) (B : ℚ)
    (heven : Even r → (n : ℚ) ≤ B)
    (hodd : Odd r → 0 ≤ B) :
    (((-1 : Int) ^ r) * (n : Int) : ℚ) ≤ B := by
  rcases Nat.even_or_odd r with hr | hr
  · change ((-1 : ℚ) ^ r) * (n : ℚ) ≤ B
    have hpow : ((-1 : ℚ) ^ r) = 1 := hr.neg_one_pow
    simpa [hpow] using heven hr
  · change ((-1 : ℚ) ^ r) * (n : ℚ) ≤ B
    have hpow : ((-1 : ℚ) ^ r) = -1 := hr.neg_one_pow
    have hn : 0 ≤ (n : ℚ) := by exact_mod_cast Nat.zero_le n
    calc
      ((-1 : ℚ) ^ r) * (n : ℚ) ≤ 0 := by
        simp [hpow, hn]
      _ ≤ B := hodd hr

theorem negOnePow_mul_intCast_rat_eq_of_even
    (r : Nat) (n : Int) (hr : Even r) :
    (((-1 : Int) ^ r) * n : ℚ) = (n : ℚ) := by
  change ((-1 : ℚ) ^ r) * (n : ℚ) = (n : ℚ)
  have hpow : ((-1 : ℚ) ^ r) = 1 := hr.neg_one_pow
  simp [hpow]

theorem negOnePow_mul_intCast_rat_eq_neg_of_odd
    (r : Nat) (n : Int) (hr : Odd r) :
    (((-1 : Int) ^ r) * n : ℚ) = - (n : ℚ) := by
  change ((-1 : ℚ) ^ r) * (n : ℚ) = - (n : ℚ)
  have hpow : ((-1 : ℚ) ^ r) = -1 := hr.neg_one_pow
  simp [hpow]

theorem negOnePow_mul_intCast_le_of_even_upper_odd_lower
    (r : Nat) (n : Int) (upper lower : ℚ)
    (heven : Even r → (n : ℚ) ≤ upper)
    (hodd : Odd r → lower ≤ (n : ℚ)) :
    (((-1 : Int) ^ r) * n : ℚ) ≤
      if Even r then upper else - lower := by
  rcases Nat.even_or_odd r with hr | hr
  · rw [negOnePow_mul_intCast_rat_eq_of_even r n hr]
    simpa [hr] using heven hr
  · have hnotEven : ¬ Even r := by
      intro he
      rcases he with ⟨a, ha⟩
      rcases hr with ⟨b, hb⟩
      omega
    rw [negOnePow_mul_intCast_rat_eq_neg_of_odd r n hr]
    simpa [hnotEven] using neg_le_neg (hodd hr)

theorem negOnePow_mul_natCast_le_of_even_upper_odd_lower
    (r n : Nat) (upper lower : ℚ)
    (heven : Even r → (n : ℚ) ≤ upper)
    (hodd : Odd r → lower ≤ (n : ℚ)) :
    (((-1 : Int) ^ r) * (n : Int) : ℚ) ≤
      if Even r then upper else - lower :=
  negOnePow_mul_intCast_le_of_even_upper_odd_lower
    r (n : Int) upper lower
    (fun hr => by simpa using heven hr)
    (fun hr => by simpa using hodd hr)

theorem satEventFiniteIntervalTransfer_rat_of_even_upper_odd_lower_rank_bounds
    (N R : Nat) (events : Finset SatEvent) (upper lower : Nat → ℚ)
    (heven : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          satEventCommonHitCountUpTo N s : Nat) : ℚ) ≤ upper r)
    (hodd : ∀ r ∈ Finset.range (2 * R + 1), Odd r →
      lower r ≤
        ((∑ s ∈ events.powersetCard r,
          satEventCommonHitCountUpTo N s : Nat) : ℚ)) :
    (satEventNoHitIndicatorSumUpTo N events : ℚ) ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        if Even r then upper r else - lower r :=
  satEventFiniteIntervalTransfer_rat_of_rank_signed_bounds
    N R events (fun r => if Even r then upper r else - lower r) (by
      intro r hr
      exact negOnePow_mul_natCast_le_of_even_upper_odd_lower r
        (∑ s ∈ events.powersetCard r, satEventCommonHitCountUpTo N s)
        (upper r) (lower r) (heven r hr) (hodd r hr))

theorem baseSatEventFiniteIntervalTransfer_rat_of_even_upper_odd_lower_rank_bounds
    (N Pz b R : Nat) (events : Finset SatEvent) (upper lower : Nat → ℚ)
    (heven : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          baseSatEventCommonHitCountUpTo N Pz b s : Nat) : ℚ) ≤ upper r)
    (hodd : ∀ r ∈ Finset.range (2 * R + 1), Odd r →
      lower r ≤
        ((∑ s ∈ events.powersetCard r,
          baseSatEventCommonHitCountUpTo N Pz b s : Nat) : ℚ)) :
    (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        if Even r then upper r else - lower r :=
  baseSatEventFiniteIntervalTransfer_rat_of_rank_signed_bounds
    N Pz b R events (fun r => if Even r then upper r else - lower r) (by
      intro r hr
      exact negOnePow_mul_natCast_le_of_even_upper_odd_lower r
        (∑ s ∈ events.powersetCard r,
          baseSatEventCommonHitCountUpTo N Pz b s)
        (upper r) (lower r) (heven r hr) (hodd r hr))

theorem satEventFiniteIntervalTransfer_rat_of_even_rank_bounds
    (N R : Nat) (events : Finset SatEvent) (B : Nat → ℚ)
    (heven : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          satEventCommonHitCountUpTo N s : Nat) : ℚ) ≤ B r)
    (hodd : ∀ r ∈ Finset.range (2 * R + 1), Odd r → 0 ≤ B r) :
    (satEventNoHitIndicatorSumUpTo N events : ℚ) ≤
      ∑ r ∈ Finset.range (2 * R + 1), B r :=
  satEventFiniteIntervalTransfer_rat_of_rank_signed_bounds
    N R events B (by
      intro r hr
      exact negOnePow_mul_natCast_le_of_even_or_odd_budget r
        (∑ s ∈ events.powersetCard r, satEventCommonHitCountUpTo N s)
        (B r) (heven r hr) (hodd r hr))

theorem baseSatEventFiniteIntervalTransfer_rat_of_even_rank_bounds
    (N Pz b R : Nat) (events : Finset SatEvent) (B : Nat → ℚ)
    (heven : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          baseSatEventCommonHitCountUpTo N Pz b s : Nat) : ℚ) ≤ B r)
    (hodd : ∀ r ∈ Finset.range (2 * R + 1), Odd r → 0 ≤ B r) :
    (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤
      ∑ r ∈ Finset.range (2 * R + 1), B r :=
  baseSatEventFiniteIntervalTransfer_rat_of_rank_signed_bounds
    N Pz b R events B (by
      intro r hr
      exact negOnePow_mul_natCast_le_of_even_or_odd_budget r
        (∑ s ∈ events.powersetCard r,
          baseSatEventCommonHitCountUpTo N Pz b s)
        (B r) (heven r hr) (hodd r hr))

theorem satEventFiniteIntervalTransfer_rat_le_main_plus_brun_error_of_even_rank_bounds
    (N R : Nat) (events : Finset SatEvent)
    (main F : Nat → ℚ) (X M : ℚ)
    (hX : 0 ≤ X)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * F r ≤ M * F (r - 1))
    (hevenRank : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          satEventCommonHitCountUpTo N s : Nat) : ℚ) ≤
        main r + X ^ r * F r)
    (hoddBudget : ∀ r ∈ Finset.range (2 * R + 1), Odd r →
      0 ≤ main r + X ^ r * F r) :
    (satEventNoHitIndicatorSumUpTo N events : ℚ) ≤
      (∑ r ∈ Finset.range (2 * R + 1), main r) +
        (∑ r ∈ Finset.range (2 * R + 1),
          (X * M) ^ r / (Nat.factorial r : ℚ)) := by
  have htransfer :=
    satEventFiniteIntervalTransfer_rat_of_even_rank_bounds
      N R events (fun r => main r + X ^ r * F r)
      hevenRank hoddBudget
  have herror :=
    finite_error_sum_le_factorial_series_from_brun F X M (2 * R)
      hX hM hF0 hrec
  calc
    (satEventNoHitIndicatorSumUpTo N events : ℚ) ≤
        ∑ r ∈ Finset.range (2 * R + 1), (main r + X ^ r * F r) := htransfer
    _ = (∑ r ∈ Finset.range (2 * R + 1), main r) +
        ∑ r ∈ Finset.range (2 * R + 1), X ^ r * F r := by
          rw [Finset.sum_add_distrib]
    _ ≤ (∑ r ∈ Finset.range (2 * R + 1), main r) +
        ∑ r ∈ Finset.range (2 * R + 1),
          (X * M) ^ r / (Nat.factorial r : ℚ) := by
          exact add_le_add_left herror _

theorem baseSatEventFiniteIntervalTransfer_rat_le_main_plus_brun_error_of_even_rank_bounds
    (N Pz b R : Nat) (events : Finset SatEvent)
    (main F : Nat → ℚ) (X M : ℚ)
    (hX : 0 ≤ X)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * F r ≤ M * F (r - 1))
    (hevenRank : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          baseSatEventCommonHitCountUpTo N Pz b s : Nat) : ℚ) ≤
        main r + X ^ r * F r)
    (hoddBudget : ∀ r ∈ Finset.range (2 * R + 1), Odd r →
      0 ≤ main r + X ^ r * F r) :
    (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤
      (∑ r ∈ Finset.range (2 * R + 1), main r) +
        (∑ r ∈ Finset.range (2 * R + 1),
          (X * M) ^ r / (Nat.factorial r : ℚ)) := by
  have htransfer :=
    baseSatEventFiniteIntervalTransfer_rat_of_even_rank_bounds
      N Pz b R events (fun r => main r + X ^ r * F r)
      hevenRank hoddBudget
  have herror :=
    finite_error_sum_le_factorial_series_from_brun F X M (2 * R)
      hX hM hF0 hrec
  calc
    (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤
        ∑ r ∈ Finset.range (2 * R + 1), (main r + X ^ r * F r) := htransfer
    _ = (∑ r ∈ Finset.range (2 * R + 1), main r) +
        ∑ r ∈ Finset.range (2 * R + 1), X ^ r * F r := by
          rw [Finset.sum_add_distrib]
    _ ≤ (∑ r ∈ Finset.range (2 * R + 1), main r) +
        ∑ r ∈ Finset.range (2 * R + 1),
          (X * M) ^ r / (Nat.factorial r : ℚ) := by
          exact add_le_add_left herror _

theorem satEventFiniteIntervalTransfer_rat_le_of_even_rank_brun_error_budget
    (N R : Nat) (events : Finset SatEvent)
    (main F : Nat → ℚ) (X M A E : ℚ)
    (hX : 0 ≤ X)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * F r ≤ M * F (r - 1))
    (hevenRank : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          satEventCommonHitCountUpTo N s : Nat) : ℚ) ≤
        main r + X ^ r * F r)
    (hoddBudget : ∀ r ∈ Finset.range (2 * R + 1), Odd r →
      0 ≤ main r + X ^ r * F r)
    (hmain : (∑ r ∈ Finset.range (2 * R + 1), main r) ≤ A)
    (herror : (∑ r ∈ Finset.range (2 * R + 1),
        (X * M) ^ r / (Nat.factorial r : ℚ)) ≤ E) :
    (satEventNoHitIndicatorSumUpTo N events : ℚ) ≤ A + E := by
  have hbase :=
    satEventFiniteIntervalTransfer_rat_le_main_plus_brun_error_of_even_rank_bounds
      N R events main F X M hX hM hF0 hrec hevenRank hoddBudget
  exact le_trans hbase (add_le_add hmain herror)

theorem baseSatEventFiniteIntervalTransfer_rat_le_of_even_rank_brun_error_budget
    (N Pz b R : Nat) (events : Finset SatEvent)
    (main F : Nat → ℚ) (X M A E : ℚ)
    (hX : 0 ≤ X)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * F r ≤ M * F (r - 1))
    (hevenRank : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          baseSatEventCommonHitCountUpTo N Pz b s : Nat) : ℚ) ≤
        main r + X ^ r * F r)
    (hoddBudget : ∀ r ∈ Finset.range (2 * R + 1), Odd r →
      0 ≤ main r + X ^ r * F r)
    (hmain : (∑ r ∈ Finset.range (2 * R + 1), main r) ≤ A)
    (herror : (∑ r ∈ Finset.range (2 * R + 1),
        (X * M) ^ r / (Nat.factorial r : ℚ)) ≤ E) :
    (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤ A + E := by
  have hbase :=
    baseSatEventFiniteIntervalTransfer_rat_le_main_plus_brun_error_of_even_rank_bounds
      N Pz b R events main F X M hX hM hF0 hrec hevenRank hoddBudget
  exact le_trans hbase (add_le_add hmain herror)

theorem satEventFiniteIntervalTransfer_rat_le_of_even_rank_elemSymm_mass_brun_error_budget
    (N R : Nat) (events : Finset SatEvent)
    (main : Nat → ℚ) (weights : List ℚ) (X M A E : ℚ)
    (hX : 0 ≤ X)
    (hnn : ∀ w ∈ weights, 0 ≤ w)
    (hmass : weights.sum ≤ M)
    (hevenRank : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          satEventCommonHitCountUpTo N s : Nat) : ℚ) ≤
        main r + X ^ r * elemSymmList weights r)
    (hoddBudget : ∀ r ∈ Finset.range (2 * R + 1), Odd r →
      0 ≤ main r + X ^ r * elemSymmList weights r)
    (hmain : (∑ r ∈ Finset.range (2 * R + 1), main r) ≤ A)
    (herror : (∑ r ∈ Finset.range (2 * R + 1),
        (X * M) ^ r / (Nat.factorial r : ℚ)) ≤ E) :
    (satEventNoHitIndicatorSumUpTo N events : ℚ) ≤ A + E := by
  have hsumNonneg : 0 ≤ weights.sum := List.sum_nonneg hnn
  have hM : 0 ≤ M := le_trans hsumNonneg hmass
  have hF0 : elemSymmList weights 0 ≤ 1 := by simp
  have hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * elemSymmList weights r ≤
        M * elemSymmList weights (r - 1) := by
    intro r hr
    have hnewton :=
      elemSymmList_brun_recurrence weights hnn r hr
    have hnonneg : 0 ≤ elemSymmList weights (r - 1) :=
      elemSymmList_nonneg weights (r - 1) hnn
    exact le_trans hnewton
      (mul_le_mul_of_nonneg_right hmass hnonneg)
  exact satEventFiniteIntervalTransfer_rat_le_of_even_rank_brun_error_budget
    N R events main (elemSymmList weights) X M A E
    hX hM hF0 hrec hevenRank hoddBudget hmain herror

theorem baseSatEventFiniteIntervalTransfer_rat_le_of_even_rank_elemSymm_mass_brun_error_budget
    (N Pz b R : Nat) (events : Finset SatEvent)
    (main : Nat → ℚ) (weights : List ℚ) (X M A E : ℚ)
    (hX : 0 ≤ X)
    (hnn : ∀ w ∈ weights, 0 ≤ w)
    (hmass : weights.sum ≤ M)
    (hevenRank : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          baseSatEventCommonHitCountUpTo N Pz b s : Nat) : ℚ) ≤
        main r + X ^ r * elemSymmList weights r)
    (hoddBudget : ∀ r ∈ Finset.range (2 * R + 1), Odd r →
      0 ≤ main r + X ^ r * elemSymmList weights r)
    (hmain : (∑ r ∈ Finset.range (2 * R + 1), main r) ≤ A)
    (herror : (∑ r ∈ Finset.range (2 * R + 1),
        (X * M) ^ r / (Nat.factorial r : ℚ)) ≤ E) :
    (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤ A + E := by
  have hsumNonneg : 0 ≤ weights.sum := List.sum_nonneg hnn
  have hM : 0 ≤ M := le_trans hsumNonneg hmass
  have hF0 : elemSymmList weights 0 ≤ 1 := by simp
  have hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * elemSymmList weights r ≤
        M * elemSymmList weights (r - 1) := by
    intro r hr
    have hnewton :=
      elemSymmList_brun_recurrence weights hnn r hr
    have hnonneg : 0 ≤ elemSymmList weights (r - 1) :=
      elemSymmList_nonneg weights (r - 1) hnn
    exact le_trans hnewton
      (mul_le_mul_of_nonneg_right hmass hnonneg)
  exact baseSatEventFiniteIntervalTransfer_rat_le_of_even_rank_brun_error_budget
    N Pz b R events main (elemSymmList weights) X M A E
    hX hM hF0 hrec hevenRank hoddBudget hmain herror

theorem satEventFiniteIntervalTransfer_rat_le_main_plus_top_power_brun_error_of_even_rank_bounds
    (N R : Nat) (events : Finset SatEvent)
    (main F : Nat → ℚ) (X M : ℚ)
    (hX : 1 ≤ X)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hFnonneg : ∀ r : Nat, r ≤ 2 * R → 0 ≤ F r)
    (hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * F r ≤ M * F (r - 1))
    (hevenRank : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          satEventCommonHitCountUpTo N s : Nat) : ℚ) ≤
        main r + X ^ r * F r)
    (hoddBudget : ∀ r ∈ Finset.range (2 * R + 1), Odd r →
      0 ≤ main r + X ^ r * F r) :
    (satEventNoHitIndicatorSumUpTo N events : ℚ) ≤
      (∑ r ∈ Finset.range (2 * R + 1), main r) +
        X ^ (2 * R) *
          (∑ r ∈ Finset.range (2 * R + 1),
            M ^ r / (Nat.factorial r : ℚ)) := by
  have htransfer :=
    satEventFiniteIntervalTransfer_rat_of_even_rank_bounds
      N R events (fun r => main r + X ^ r * F r)
      hevenRank hoddBudget
  have herror :=
    finite_error_sum_le_top_power_factorial_series_from_brun
      F X M (2 * R) hX hM hF0 hFnonneg hrec
  calc
    (satEventNoHitIndicatorSumUpTo N events : ℚ) ≤
        ∑ r ∈ Finset.range (2 * R + 1), (main r + X ^ r * F r) := htransfer
    _ = (∑ r ∈ Finset.range (2 * R + 1), main r) +
        ∑ r ∈ Finset.range (2 * R + 1), X ^ r * F r := by
          rw [Finset.sum_add_distrib]
    _ ≤ (∑ r ∈ Finset.range (2 * R + 1), main r) +
        X ^ (2 * R) *
          (∑ r ∈ Finset.range (2 * R + 1),
            M ^ r / (Nat.factorial r : ℚ)) := by
          exact add_le_add_left herror _

theorem baseSatEventFiniteIntervalTransfer_rat_le_main_plus_top_power_brun_error_of_even_rank_bounds
    (N Pz b R : Nat) (events : Finset SatEvent)
    (main F : Nat → ℚ) (X M : ℚ)
    (hX : 1 ≤ X)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hFnonneg : ∀ r : Nat, r ≤ 2 * R → 0 ≤ F r)
    (hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * F r ≤ M * F (r - 1))
    (hevenRank : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          baseSatEventCommonHitCountUpTo N Pz b s : Nat) : ℚ) ≤
        main r + X ^ r * F r)
    (hoddBudget : ∀ r ∈ Finset.range (2 * R + 1), Odd r →
      0 ≤ main r + X ^ r * F r) :
    (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤
      (∑ r ∈ Finset.range (2 * R + 1), main r) +
        X ^ (2 * R) *
          (∑ r ∈ Finset.range (2 * R + 1),
            M ^ r / (Nat.factorial r : ℚ)) := by
  have htransfer :=
    baseSatEventFiniteIntervalTransfer_rat_of_even_rank_bounds
      N Pz b R events (fun r => main r + X ^ r * F r)
      hevenRank hoddBudget
  have herror :=
    finite_error_sum_le_top_power_factorial_series_from_brun
      F X M (2 * R) hX hM hF0 hFnonneg hrec
  calc
    (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤
        ∑ r ∈ Finset.range (2 * R + 1), (main r + X ^ r * F r) := htransfer
    _ = (∑ r ∈ Finset.range (2 * R + 1), main r) +
        ∑ r ∈ Finset.range (2 * R + 1), X ^ r * F r := by
          rw [Finset.sum_add_distrib]
    _ ≤ (∑ r ∈ Finset.range (2 * R + 1), main r) +
        X ^ (2 * R) *
          (∑ r ∈ Finset.range (2 * R + 1),
            M ^ r / (Nat.factorial r : ℚ)) := by
          exact add_le_add_left herror _

theorem satEventFiniteIntervalTransfer_rat_le_top_power_brun_error_budget_of_even_rank_bounds
    (N R : Nat) (events : Finset SatEvent)
    (main F : Nat → ℚ) (X M E : ℚ)
    (hX : 1 ≤ X)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hFnonneg : ∀ r : Nat, r ≤ 2 * R → 0 ≤ F r)
    (hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * F r ≤ M * F (r - 1))
    (hevenRank : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          satEventCommonHitCountUpTo N s : Nat) : ℚ) ≤
        main r + X ^ r * F r)
    (hoddBudget : ∀ r ∈ Finset.range (2 * R + 1), Odd r →
      0 ≤ main r + X ^ r * F r)
    (henvelope : (∑ r ∈ Finset.range (2 * R + 1),
      M ^ r / (Nat.factorial r : ℚ)) ≤ E) :
    (satEventNoHitIndicatorSumUpTo N events : ℚ) ≤
      (∑ r ∈ Finset.range (2 * R + 1), main r) + X ^ (2 * R) * E := by
  have htransfer :=
    satEventFiniteIntervalTransfer_rat_le_main_plus_top_power_brun_error_of_even_rank_bounds
      N R events main F X M hX hM hF0 hFnonneg hrec
      hevenRank hoddBudget
  have hXnonneg : 0 ≤ X := by linarith
  have hpowNonneg : 0 ≤ X ^ (2 * R) := pow_nonneg hXnonneg (2 * R)
  exact le_trans htransfer
    (add_le_add_left (mul_le_mul_of_nonneg_left henvelope hpowNonneg) _)

theorem baseSatEventFiniteIntervalTransfer_rat_le_top_power_brun_error_budget_of_even_rank_bounds
    (N Pz b R : Nat) (events : Finset SatEvent)
    (main F : Nat → ℚ) (X M E : ℚ)
    (hX : 1 ≤ X)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hFnonneg : ∀ r : Nat, r ≤ 2 * R → 0 ≤ F r)
    (hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * F r ≤ M * F (r - 1))
    (hevenRank : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          baseSatEventCommonHitCountUpTo N Pz b s : Nat) : ℚ) ≤
        main r + X ^ r * F r)
    (hoddBudget : ∀ r ∈ Finset.range (2 * R + 1), Odd r →
      0 ≤ main r + X ^ r * F r)
    (henvelope : (∑ r ∈ Finset.range (2 * R + 1),
      M ^ r / (Nat.factorial r : ℚ)) ≤ E) :
    (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤
      (∑ r ∈ Finset.range (2 * R + 1), main r) + X ^ (2 * R) * E := by
  have htransfer :=
    baseSatEventFiniteIntervalTransfer_rat_le_main_plus_top_power_brun_error_of_even_rank_bounds
      N Pz b R events main F X M hX hM hF0 hFnonneg hrec
      hevenRank hoddBudget
  have hXnonneg : 0 ≤ X := by linarith
  have hpowNonneg : 0 ≤ X ^ (2 * R) := pow_nonneg hXnonneg (2 * R)
  exact le_trans htransfer
    (add_le_add_left (mul_le_mul_of_nonneg_left henvelope hpowNonneg) _)

theorem satEventFiniteIntervalTransfer_rat_le_of_even_rank_elemSymm_mass_top_power_brun_error_budget
    (N R : Nat) (events : Finset SatEvent)
    (main : Nat → ℚ) (weights : List ℚ) (X M E : ℚ)
    (hX : 1 ≤ X)
    (hnn : ∀ w ∈ weights, 0 ≤ w)
    (hmass : weights.sum ≤ M)
    (hevenRank : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          satEventCommonHitCountUpTo N s : Nat) : ℚ) ≤
        main r + X ^ r * elemSymmList weights r)
    (hoddBudget : ∀ r ∈ Finset.range (2 * R + 1), Odd r →
      0 ≤ main r + X ^ r * elemSymmList weights r)
    (henvelope : (∑ r ∈ Finset.range (2 * R + 1),
      M ^ r / (Nat.factorial r : ℚ)) ≤ E) :
    (satEventNoHitIndicatorSumUpTo N events : ℚ) ≤
      (∑ r ∈ Finset.range (2 * R + 1), main r) + X ^ (2 * R) * E := by
  have hsumNonneg : 0 ≤ weights.sum := List.sum_nonneg hnn
  have hM : 0 ≤ M := le_trans hsumNonneg hmass
  have hF0 : elemSymmList weights 0 ≤ 1 := by simp
  have hFnonneg : ∀ r : Nat, r ≤ 2 * R → 0 ≤ elemSymmList weights r := by
    intro r _hr
    exact elemSymmList_nonneg weights r hnn
  have hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * elemSymmList weights r ≤
        M * elemSymmList weights (r - 1) := by
    intro r hr
    have hnewton :=
      elemSymmList_brun_recurrence weights hnn r hr
    have hnonneg : 0 ≤ elemSymmList weights (r - 1) :=
      elemSymmList_nonneg weights (r - 1) hnn
    exact le_trans hnewton
      (mul_le_mul_of_nonneg_right hmass hnonneg)
  exact satEventFiniteIntervalTransfer_rat_le_top_power_brun_error_budget_of_even_rank_bounds
    N R events main (elemSymmList weights) X M E
    hX hM hF0 hFnonneg hrec hevenRank hoddBudget henvelope

theorem baseSatEventFiniteIntervalTransfer_rat_le_of_even_rank_elemSymm_mass_top_power_brun_error_budget
    (N Pz b R : Nat) (events : Finset SatEvent)
    (main : Nat → ℚ) (weights : List ℚ) (X M E : ℚ)
    (hX : 1 ≤ X)
    (hnn : ∀ w ∈ weights, 0 ≤ w)
    (hmass : weights.sum ≤ M)
    (hevenRank : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          baseSatEventCommonHitCountUpTo N Pz b s : Nat) : ℚ) ≤
        main r + X ^ r * elemSymmList weights r)
    (hoddBudget : ∀ r ∈ Finset.range (2 * R + 1), Odd r →
      0 ≤ main r + X ^ r * elemSymmList weights r)
    (henvelope : (∑ r ∈ Finset.range (2 * R + 1),
      M ^ r / (Nat.factorial r : ℚ)) ≤ E) :
    (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤
      (∑ r ∈ Finset.range (2 * R + 1), main r) + X ^ (2 * R) * E := by
  have hsumNonneg : 0 ≤ weights.sum := List.sum_nonneg hnn
  have hM : 0 ≤ M := le_trans hsumNonneg hmass
  have hF0 : elemSymmList weights 0 ≤ 1 := by simp
  have hFnonneg : ∀ r : Nat, r ≤ 2 * R → 0 ≤ elemSymmList weights r := by
    intro r _hr
    exact elemSymmList_nonneg weights r hnn
  have hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * elemSymmList weights r ≤
        M * elemSymmList weights (r - 1) := by
    intro r hr
    have hnewton :=
      elemSymmList_brun_recurrence weights hnn r hr
    have hnonneg : 0 ≤ elemSymmList weights (r - 1) :=
      elemSymmList_nonneg weights (r - 1) hnn
    exact le_trans hnewton
      (mul_le_mul_of_nonneg_right hmass hnonneg)
  exact baseSatEventFiniteIntervalTransfer_rat_le_top_power_brun_error_budget_of_even_rank_bounds
    N Pz b R events main (elemSymmList weights) X M E
    hX hM hF0 hFnonneg hrec hevenRank hoddBudget henvelope

theorem satEventFiniteIntervalTransfer_rat_le_of_even_rank_elemSymm_mass_top_power_brun_envelope
    (N R : Nat) (events : Finset SatEvent)
    (main : Nat → ℚ) (weights : List ℚ) (X M A E : ℚ)
    (hX : 1 ≤ X)
    (hnn : ∀ w ∈ weights, 0 ≤ w)
    (hmass : weights.sum ≤ M)
    (hevenRank : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          satEventCommonHitCountUpTo N s : Nat) : ℚ) ≤
        main r + X ^ r * elemSymmList weights r)
    (hoddBudget : ∀ r ∈ Finset.range (2 * R + 1), Odd r →
      0 ≤ main r + X ^ r * elemSymmList weights r)
    (hmain : (∑ r ∈ Finset.range (2 * R + 1), main r) ≤ A)
    (henvelope : (∑ r ∈ Finset.range (2 * R + 1),
      M ^ r / (Nat.factorial r : ℚ)) ≤ E) :
    (satEventNoHitIndicatorSumUpTo N events : ℚ) ≤ A + X ^ (2 * R) * E := by
  have hbase :=
    satEventFiniteIntervalTransfer_rat_le_of_even_rank_elemSymm_mass_top_power_brun_error_budget
      N R events main weights X M E hX hnn hmass
      hevenRank hoddBudget henvelope
  exact le_trans hbase (add_le_add_right hmain _)

theorem baseSatEventFiniteIntervalTransfer_rat_le_of_even_rank_elemSymm_mass_top_power_brun_envelope
    (N Pz b R : Nat) (events : Finset SatEvent)
    (main : Nat → ℚ) (weights : List ℚ) (X M A E : ℚ)
    (hX : 1 ≤ X)
    (hnn : ∀ w ∈ weights, 0 ≤ w)
    (hmass : weights.sum ≤ M)
    (hevenRank : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          baseSatEventCommonHitCountUpTo N Pz b s : Nat) : ℚ) ≤
        main r + X ^ r * elemSymmList weights r)
    (hoddBudget : ∀ r ∈ Finset.range (2 * R + 1), Odd r →
      0 ≤ main r + X ^ r * elemSymmList weights r)
    (hmain : (∑ r ∈ Finset.range (2 * R + 1), main r) ≤ A)
    (henvelope : (∑ r ∈ Finset.range (2 * R + 1),
      M ^ r / (Nat.factorial r : ℚ)) ≤ E) :
    (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤
      A + X ^ (2 * R) * E := by
  have hbase :=
    baseSatEventFiniteIntervalTransfer_rat_le_of_even_rank_elemSymm_mass_top_power_brun_error_budget
      N Pz b R events main weights X M E hX hnn hmass
      hevenRank hoddBudget henvelope
  exact le_trans hbase (add_le_add_right hmain _)

theorem satEventFiniteIntervalTransfer_rat_le_of_even_rank_elemSymm_mass_top_power_brun_partial_exp
    (N R : Nat) (events : Finset SatEvent)
    (main : Nat → ℚ) (weights : List ℚ) (X M A : ℚ)
    (hX : 1 ≤ X)
    (hnn : ∀ w ∈ weights, 0 ≤ w)
    (hmass : weights.sum ≤ M)
    (hevenRank : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          satEventCommonHitCountUpTo N s : Nat) : ℚ) ≤
        main r + X ^ r * elemSymmList weights r)
    (hoddBudget : ∀ r ∈ Finset.range (2 * R + 1), Odd r →
      0 ≤ main r + X ^ r * elemSymmList weights r)
    (hmain : (∑ r ∈ Finset.range (2 * R + 1), main r) ≤ A) :
    (satEventNoHitIndicatorSumUpTo N events : ℚ) ≤
      A + X ^ (2 * R) *
        (∑ r ∈ Finset.range (2 * R + 1),
          M ^ r / (Nat.factorial r : ℚ)) := by
  exact satEventFiniteIntervalTransfer_rat_le_of_even_rank_elemSymm_mass_top_power_brun_envelope
    N R events main weights X M A
    (∑ r ∈ Finset.range (2 * R + 1),
      M ^ r / (Nat.factorial r : ℚ))
    hX hnn hmass hevenRank hoddBudget hmain le_rfl

theorem baseSatEventFiniteIntervalTransfer_rat_le_of_even_rank_elemSymm_mass_top_power_brun_partial_exp
    (N Pz b R : Nat) (events : Finset SatEvent)
    (main : Nat → ℚ) (weights : List ℚ) (X M A : ℚ)
    (hX : 1 ≤ X)
    (hnn : ∀ w ∈ weights, 0 ≤ w)
    (hmass : weights.sum ≤ M)
    (hevenRank : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          baseSatEventCommonHitCountUpTo N Pz b s : Nat) : ℚ) ≤
        main r + X ^ r * elemSymmList weights r)
    (hoddBudget : ∀ r ∈ Finset.range (2 * R + 1), Odd r →
      0 ≤ main r + X ^ r * elemSymmList weights r)
    (hmain : (∑ r ∈ Finset.range (2 * R + 1), main r) ≤ A) :
    (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤
      A + X ^ (2 * R) *
        (∑ r ∈ Finset.range (2 * R + 1),
          M ^ r / (Nat.factorial r : ℚ)) := by
  exact baseSatEventFiniteIntervalTransfer_rat_le_of_even_rank_elemSymm_mass_top_power_brun_envelope
    N Pz b R events main weights X M A
    (∑ r ∈ Finset.range (2 * R + 1),
      M ^ r / (Nat.factorial r : ℚ))
    hX hnn hmass hevenRank hoddBudget hmain le_rfl

theorem satEventFiniteIntervalTransfer_rat_le_main_plus_brun_error
    (N R : Nat) (events : Finset SatEvent)
    (main F : Nat → ℚ) (X M : ℚ)
    (hX : 0 ≤ X)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * F r ≤ M * F (r - 1))
    (hrank : ∀ r ∈ Finset.range (2 * R + 1),
      (((-1 : Int) ^ r) *
        ((∑ s ∈ events.powersetCard r,
            satEventCommonHitCountUpTo N s : Nat) : Int) : ℚ) ≤
          main r + X ^ r * F r) :
    (satEventNoHitIndicatorSumUpTo N events : ℚ) ≤
      (∑ r ∈ Finset.range (2 * R + 1), main r) +
        (∑ r ∈ Finset.range (2 * R + 1),
          (X * M) ^ r / (Nat.factorial r : ℚ)) := by
  have htransfer :=
    satEventFiniteIntervalTransfer_rat_of_rank_signed_bounds
      N R events (fun r => main r + X ^ r * F r) hrank
  have herror :=
    finite_error_sum_le_factorial_series_from_brun F X M (2 * R)
      hX hM hF0 hrec
  calc
    (satEventNoHitIndicatorSumUpTo N events : ℚ) ≤
        ∑ r ∈ Finset.range (2 * R + 1), (main r + X ^ r * F r) := htransfer
    _ = (∑ r ∈ Finset.range (2 * R + 1), main r) +
        ∑ r ∈ Finset.range (2 * R + 1), X ^ r * F r := by
          rw [Finset.sum_add_distrib]
    _ ≤ (∑ r ∈ Finset.range (2 * R + 1), main r) +
        ∑ r ∈ Finset.range (2 * R + 1),
          (X * M) ^ r / (Nat.factorial r : ℚ) := by
          exact add_le_add_left herror _

theorem baseSatEventFiniteIntervalTransfer_rat_le_main_plus_brun_error
    (N Pz b R : Nat) (events : Finset SatEvent)
    (main F : Nat → ℚ) (X M : ℚ)
    (hX : 0 ≤ X)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * F r ≤ M * F (r - 1))
    (hrank : ∀ r ∈ Finset.range (2 * R + 1),
      (((-1 : Int) ^ r) *
        ((∑ s ∈ events.powersetCard r,
            baseSatEventCommonHitCountUpTo N Pz b s : Nat) : Int) : ℚ) ≤
          main r + X ^ r * F r) :
    (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤
      (∑ r ∈ Finset.range (2 * R + 1), main r) +
        (∑ r ∈ Finset.range (2 * R + 1),
          (X * M) ^ r / (Nat.factorial r : ℚ)) := by
  have htransfer :=
    baseSatEventFiniteIntervalTransfer_rat_of_rank_signed_bounds
      N Pz b R events (fun r => main r + X ^ r * F r) hrank
  have herror :=
    finite_error_sum_le_factorial_series_from_brun F X M (2 * R)
      hX hM hF0 hrec
  calc
    (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤
        ∑ r ∈ Finset.range (2 * R + 1), (main r + X ^ r * F r) := htransfer
    _ = (∑ r ∈ Finset.range (2 * R + 1), main r) +
        ∑ r ∈ Finset.range (2 * R + 1), X ^ r * F r := by
          rw [Finset.sum_add_distrib]
    _ ≤ (∑ r ∈ Finset.range (2 * R + 1), main r) +
        ∑ r ∈ Finset.range (2 * R + 1),
          (X * M) ^ r / (Nat.factorial r : ℚ) := by
          exact add_le_add_left herror _

theorem satEventFiniteIntervalTransfer_rat_le_of_main_sum_bound_and_brun_error
    (N R : Nat) (events : Finset SatEvent)
    (main F : Nat → ℚ) (X M A : ℚ)
    (hX : 0 ≤ X)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * F r ≤ M * F (r - 1))
    (hrank : ∀ r ∈ Finset.range (2 * R + 1),
      (((-1 : Int) ^ r) *
        ((∑ s ∈ events.powersetCard r,
            satEventCommonHitCountUpTo N s : Nat) : Int) : ℚ) ≤
          main r + X ^ r * F r)
    (hmain : (∑ r ∈ Finset.range (2 * R + 1), main r) ≤ A) :
    (satEventNoHitIndicatorSumUpTo N events : ℚ) ≤
      A + ∑ r ∈ Finset.range (2 * R + 1),
        (X * M) ^ r / (Nat.factorial r : ℚ) := by
  have hbase :=
    satEventFiniteIntervalTransfer_rat_le_main_plus_brun_error
      N R events main F X M hX hM hF0 hrec hrank
  exact le_trans hbase (add_le_add_right hmain _)

theorem baseSatEventFiniteIntervalTransfer_rat_le_of_main_sum_bound_and_brun_error
    (N Pz b R : Nat) (events : Finset SatEvent)
    (main F : Nat → ℚ) (X M A : ℚ)
    (hX : 0 ≤ X)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * F r ≤ M * F (r - 1))
    (hrank : ∀ r ∈ Finset.range (2 * R + 1),
      (((-1 : Int) ^ r) *
        ((∑ s ∈ events.powersetCard r,
            baseSatEventCommonHitCountUpTo N Pz b s : Nat) : Int) : ℚ) ≤
          main r + X ^ r * F r)
    (hmain : (∑ r ∈ Finset.range (2 * R + 1), main r) ≤ A) :
    (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤
      A + ∑ r ∈ Finset.range (2 * R + 1),
        (X * M) ^ r / (Nat.factorial r : ℚ) := by
  have hbase :=
    baseSatEventFiniteIntervalTransfer_rat_le_main_plus_brun_error
      N Pz b R events main F X M hX hM hF0 hrec hrank
  exact le_trans hbase (add_le_add_right hmain _)

theorem satEventFiniteIntervalTransfer_rat_le_of_brun_error_budget
    (N R : Nat) (events : Finset SatEvent)
    (main F : Nat → ℚ) (X M A E : ℚ)
    (hX : 0 ≤ X)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * F r ≤ M * F (r - 1))
    (hrank : ∀ r ∈ Finset.range (2 * R + 1),
      (((-1 : Int) ^ r) *
        ((∑ s ∈ events.powersetCard r,
            satEventCommonHitCountUpTo N s : Nat) : Int) : ℚ) ≤
          main r + X ^ r * F r)
    (hmain : (∑ r ∈ Finset.range (2 * R + 1), main r) ≤ A)
    (herror : (∑ r ∈ Finset.range (2 * R + 1),
        (X * M) ^ r / (Nat.factorial r : ℚ)) ≤ E) :
    (satEventNoHitIndicatorSumUpTo N events : ℚ) ≤ A + E := by
  have hbase :=
    satEventFiniteIntervalTransfer_rat_le_of_main_sum_bound_and_brun_error
      N R events main F X M A hX hM hF0 hrec hrank hmain
  exact le_trans hbase (add_le_add_left herror A)

theorem baseSatEventFiniteIntervalTransfer_rat_le_of_brun_error_budget
    (N Pz b R : Nat) (events : Finset SatEvent)
    (main F : Nat → ℚ) (X M A E : ℚ)
    (hX : 0 ≤ X)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * F r ≤ M * F (r - 1))
    (hrank : ∀ r ∈ Finset.range (2 * R + 1),
      (((-1 : Int) ^ r) *
        ((∑ s ∈ events.powersetCard r,
            baseSatEventCommonHitCountUpTo N Pz b s : Nat) : Int) : ℚ) ≤
          main r + X ^ r * F r)
    (hmain : (∑ r ∈ Finset.range (2 * R + 1), main r) ≤ A)
    (herror : (∑ r ∈ Finset.range (2 * R + 1),
        (X * M) ^ r / (Nat.factorial r : ℚ)) ≤ E) :
    (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤ A + E := by
  have hbase :=
    baseSatEventFiniteIntervalTransfer_rat_le_of_main_sum_bound_and_brun_error
      N Pz b R events main F X M A hX hM hF0 hrec hrank hmain
  exact le_trans hbase (add_le_add_left herror A)

theorem satEventFiniteIntervalTransfer_rat_le_of_elemSymm_mass_brun_error_budget
    (N R : Nat) (events : Finset SatEvent)
    (main : Nat → ℚ) (weights : List ℚ) (X M A E : ℚ)
    (hX : 0 ≤ X)
    (hnn : ∀ w ∈ weights, 0 ≤ w)
    (hmass : weights.sum ≤ M)
    (hrank : ∀ r ∈ Finset.range (2 * R + 1),
      (((-1 : Int) ^ r) *
        ((∑ s ∈ events.powersetCard r,
            satEventCommonHitCountUpTo N s : Nat) : Int) : ℚ) ≤
          main r + X ^ r * elemSymmList weights r)
    (hmain : (∑ r ∈ Finset.range (2 * R + 1), main r) ≤ A)
    (herror : (∑ r ∈ Finset.range (2 * R + 1),
        (X * M) ^ r / (Nat.factorial r : ℚ)) ≤ E) :
    (satEventNoHitIndicatorSumUpTo N events : ℚ) ≤ A + E := by
  have hsumNonneg : 0 ≤ weights.sum := List.sum_nonneg hnn
  have hM : 0 ≤ M := le_trans hsumNonneg hmass
  have hF0 : elemSymmList weights 0 ≤ 1 := by simp
  have hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * elemSymmList weights r ≤
        M * elemSymmList weights (r - 1) := by
    intro r hr
    have hnewton :=
      elemSymmList_brun_recurrence weights hnn r hr
    have hnonneg : 0 ≤ elemSymmList weights (r - 1) :=
      elemSymmList_nonneg weights (r - 1) hnn
    exact le_trans hnewton
      (mul_le_mul_of_nonneg_right hmass hnonneg)
  exact satEventFiniteIntervalTransfer_rat_le_of_brun_error_budget
    N R events main (elemSymmList weights) X M A E
    hX hM hF0 hrec hrank hmain herror

theorem baseSatEventFiniteIntervalTransfer_rat_le_of_elemSymm_mass_brun_error_budget
    (N Pz b R : Nat) (events : Finset SatEvent)
    (main : Nat → ℚ) (weights : List ℚ) (X M A E : ℚ)
    (hX : 0 ≤ X)
    (hnn : ∀ w ∈ weights, 0 ≤ w)
    (hmass : weights.sum ≤ M)
    (hrank : ∀ r ∈ Finset.range (2 * R + 1),
      (((-1 : Int) ^ r) *
        ((∑ s ∈ events.powersetCard r,
            baseSatEventCommonHitCountUpTo N Pz b s : Nat) : Int) : ℚ) ≤
          main r + X ^ r * elemSymmList weights r)
    (hmain : (∑ r ∈ Finset.range (2 * R + 1), main r) ≤ A)
    (herror : (∑ r ∈ Finset.range (2 * R + 1),
        (X * M) ^ r / (Nat.factorial r : ℚ)) ≤ E) :
    (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤ A + E := by
  have hsumNonneg : 0 ≤ weights.sum := List.sum_nonneg hnn
  have hM : 0 ≤ M := le_trans hsumNonneg hmass
  have hF0 : elemSymmList weights 0 ≤ 1 := by simp
  have hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * elemSymmList weights r ≤
        M * elemSymmList weights (r - 1) := by
    intro r hr
    have hnewton :=
      elemSymmList_brun_recurrence weights hnn r hr
    have hnonneg : 0 ≤ elemSymmList weights (r - 1) :=
      elemSymmList_nonneg weights (r - 1) hnn
    exact le_trans hnewton
      (mul_le_mul_of_nonneg_right hmass hnonneg)
  exact baseSatEventFiniteIntervalTransfer_rat_le_of_brun_error_budget
    N Pz b R events main (elemSymmList weights) X M A E
    hX hM hF0 hrec hrank hmain herror

theorem brun_weighted_error_le_factorial_envelope
    (F : Nat → ℚ) (X M E : ℚ) (m : Nat)
    (hX : 0 ≤ X)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * F r ≤ M * F (r - 1))
    (henvelope : (∑ r ∈ Finset.range (m + 1),
      (X * M) ^ r / (Nat.factorial r : ℚ)) ≤ E) :
    (∑ r ∈ Finset.range (m + 1), X ^ r * F r) ≤ E :=
  le_trans
    (finite_error_sum_le_factorial_series_from_brun
      F X M m hX hM hF0 hrec)
    henvelope

theorem brun_elemSymm_weighted_error_le_mass_factorial_envelope
    (weights : List ℚ) (X M E : ℚ) (m : Nat)
    (hX : 0 ≤ X)
    (hnn : ∀ w ∈ weights, 0 ≤ w)
    (hmass : weights.sum ≤ M)
    (henvelope : (∑ r ∈ Finset.range (m + 1),
      (X * M) ^ r / (Nat.factorial r : ℚ)) ≤ E) :
    (∑ r ∈ Finset.range (m + 1),
      X ^ r * elemSymmList weights r) ≤ E := by
  have hsumNonneg : 0 ≤ weights.sum := List.sum_nonneg hnn
  have hM : 0 ≤ M := le_trans hsumNonneg hmass
  have hF0 : elemSymmList weights 0 ≤ 1 := by simp
  have hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * elemSymmList weights r ≤
        M * elemSymmList weights (r - 1) := by
    intro r hr
    have hnewton :=
      elemSymmList_brun_recurrence weights hnn r hr
    have hnonneg : 0 ≤ elemSymmList weights (r - 1) :=
      elemSymmList_nonneg weights (r - 1) hnn
    exact le_trans hnewton
      (mul_le_mul_of_nonneg_right hmass hnonneg)
  exact brun_weighted_error_le_factorial_envelope
    (elemSymmList weights) X M E m hX hM hF0 hrec henvelope

theorem brun_elemSymm_weighted_error_le_mass_factorial_series
    (weights : List ℚ) (X M : ℚ) (m : Nat)
    (hX : 0 ≤ X)
    (hnn : ∀ w ∈ weights, 0 ≤ w)
    (hmass : weights.sum ≤ M) :
    (∑ r ∈ Finset.range (m + 1),
      X ^ r * elemSymmList weights r) ≤
        ∑ r ∈ Finset.range (m + 1),
          (X * M) ^ r / (Nat.factorial r : ℚ) := by
  exact brun_elemSymm_weighted_error_le_mass_factorial_envelope
    weights X M
    (∑ r ∈ Finset.range (m + 1),
      (X * M) ^ r / (Nat.factorial r : ℚ))
    m hX hnn hmass le_rfl

theorem brun_elemSymm_weighted_error_le_exact_mass_factorial_series
    (weights : List ℚ) (X : ℚ) (m : Nat)
    (hX : 0 ≤ X)
    (hnn : ∀ w ∈ weights, 0 ≤ w) :
    (∑ r ∈ Finset.range (m + 1),
      X ^ r * elemSymmList weights r) ≤
        ∑ r ∈ Finset.range (m + 1),
          (X * weights.sum) ^ r / (Nat.factorial r : ℚ) := by
  exact brun_elemSymm_weighted_error_le_mass_factorial_series
    weights X weights.sum m hX hnn le_rfl

theorem brun_weighted_error_le_top_power_factorial_envelope
    (F : Nat → ℚ) (X M E : ℚ) (m : Nat)
    (hX : 1 ≤ X)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hFnonneg : ∀ r : Nat, r ≤ m → 0 ≤ F r)
    (hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * F r ≤ M * F (r - 1))
    (henvelope : (∑ r ∈ Finset.range (m + 1),
      M ^ r / (Nat.factorial r : ℚ)) ≤ E) :
    (∑ r ∈ Finset.range (m + 1), X ^ r * F r) ≤ X ^ m * E := by
  have htop :=
    finite_error_sum_le_top_power_factorial_series_from_brun
      F X M m hX hM hF0 hFnonneg hrec
  have hXnonneg : 0 ≤ X := by linarith
  have hpowNonneg : 0 ≤ X ^ m := pow_nonneg hXnonneg m
  exact le_trans htop (mul_le_mul_of_nonneg_left henvelope hpowNonneg)

theorem brun_elemSymm_weighted_error_le_top_power_mass_factorial_envelope
    (weights : List ℚ) (X M E : ℚ) (m : Nat)
    (hX : 1 ≤ X)
    (hnn : ∀ w ∈ weights, 0 ≤ w)
    (hmass : weights.sum ≤ M)
    (henvelope : (∑ r ∈ Finset.range (m + 1),
      M ^ r / (Nat.factorial r : ℚ)) ≤ E) :
    (∑ r ∈ Finset.range (m + 1),
      X ^ r * elemSymmList weights r) ≤ X ^ m * E := by
  have hsumNonneg : 0 ≤ weights.sum := List.sum_nonneg hnn
  have hM : 0 ≤ M := le_trans hsumNonneg hmass
  have hF0 : elemSymmList weights 0 ≤ 1 := by simp
  have hFnonneg : ∀ r : Nat, r ≤ m → 0 ≤ elemSymmList weights r := by
    intro r _hr
    exact elemSymmList_nonneg weights r hnn
  have hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * elemSymmList weights r ≤
        M * elemSymmList weights (r - 1) := by
    intro r hr
    have hnewton :=
      elemSymmList_brun_recurrence weights hnn r hr
    have hnonneg : 0 ≤ elemSymmList weights (r - 1) :=
      elemSymmList_nonneg weights (r - 1) hnn
    exact le_trans hnewton
      (mul_le_mul_of_nonneg_right hmass hnonneg)
  exact brun_weighted_error_le_top_power_factorial_envelope
    (elemSymmList weights) X M E m hX hM hF0 hFnonneg hrec henvelope

theorem brun_elemSymm_weighted_error_le_top_power_mass_factorial_series
    (weights : List ℚ) (X M : ℚ) (m : Nat)
    (hX : 1 ≤ X)
    (hnn : ∀ w ∈ weights, 0 ≤ w)
    (hmass : weights.sum ≤ M) :
    (∑ r ∈ Finset.range (m + 1),
      X ^ r * elemSymmList weights r) ≤
        X ^ m *
          (∑ r ∈ Finset.range (m + 1),
            M ^ r / (Nat.factorial r : ℚ)) := by
  exact brun_elemSymm_weighted_error_le_top_power_mass_factorial_envelope
    weights X M
    (∑ r ∈ Finset.range (m + 1),
      M ^ r / (Nat.factorial r : ℚ))
    m hX hnn hmass le_rfl

theorem brun_elemSymm_weighted_error_le_top_power_exact_mass_factorial_series
    (weights : List ℚ) (X : ℚ) (m : Nat)
    (hX : 1 ≤ X)
    (hnn : ∀ w ∈ weights, 0 ≤ w) :
    (∑ r ∈ Finset.range (m + 1),
      X ^ r * elemSymmList weights r) ≤
        X ^ m *
          (∑ r ∈ Finset.range (m + 1),
            weights.sum ^ r / (Nat.factorial r : ℚ)) := by
  exact brun_elemSymm_weighted_error_le_top_power_mass_factorial_series
    weights X weights.sum m hX hnn le_rfl

theorem satEventFiniteIntervalTransfer_rat_le_main_plus_top_power_brun_error
    (N R : Nat) (events : Finset SatEvent)
    (main F : Nat → ℚ) (X M : ℚ)
    (hX : 1 ≤ X)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hFnonneg : ∀ r : Nat, r ≤ 2 * R → 0 ≤ F r)
    (hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * F r ≤ M * F (r - 1))
    (hrank : ∀ r ∈ Finset.range (2 * R + 1),
      (((-1 : Int) ^ r) *
        ((∑ s ∈ events.powersetCard r,
            satEventCommonHitCountUpTo N s : Nat) : Int) : ℚ) ≤
          main r + X ^ r * F r) :
    (satEventNoHitIndicatorSumUpTo N events : ℚ) ≤
      (∑ r ∈ Finset.range (2 * R + 1), main r) +
        X ^ (2 * R) *
          (∑ r ∈ Finset.range (2 * R + 1),
            M ^ r / (Nat.factorial r : ℚ)) := by
  have htransfer :=
    satEventFiniteIntervalTransfer_rat_of_rank_signed_bounds
      N R events (fun r => main r + X ^ r * F r) hrank
  have herror :=
    finite_error_sum_le_top_power_factorial_series_from_brun
      F X M (2 * R) hX hM hF0 hFnonneg hrec
  calc
    (satEventNoHitIndicatorSumUpTo N events : ℚ) ≤
        ∑ r ∈ Finset.range (2 * R + 1), (main r + X ^ r * F r) := htransfer
    _ = (∑ r ∈ Finset.range (2 * R + 1), main r) +
        ∑ r ∈ Finset.range (2 * R + 1), X ^ r * F r := by
          rw [Finset.sum_add_distrib]
    _ ≤ (∑ r ∈ Finset.range (2 * R + 1), main r) +
        X ^ (2 * R) *
          (∑ r ∈ Finset.range (2 * R + 1),
            M ^ r / (Nat.factorial r : ℚ)) := by
          exact add_le_add_left herror _

theorem baseSatEventFiniteIntervalTransfer_rat_le_main_plus_top_power_brun_error
    (N Pz b R : Nat) (events : Finset SatEvent)
    (main F : Nat → ℚ) (X M : ℚ)
    (hX : 1 ≤ X)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hFnonneg : ∀ r : Nat, r ≤ 2 * R → 0 ≤ F r)
    (hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * F r ≤ M * F (r - 1))
    (hrank : ∀ r ∈ Finset.range (2 * R + 1),
      (((-1 : Int) ^ r) *
        ((∑ s ∈ events.powersetCard r,
            baseSatEventCommonHitCountUpTo N Pz b s : Nat) : Int) : ℚ) ≤
          main r + X ^ r * F r) :
    (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤
      (∑ r ∈ Finset.range (2 * R + 1), main r) +
        X ^ (2 * R) *
          (∑ r ∈ Finset.range (2 * R + 1),
            M ^ r / (Nat.factorial r : ℚ)) := by
  have htransfer :=
    baseSatEventFiniteIntervalTransfer_rat_of_rank_signed_bounds
      N Pz b R events (fun r => main r + X ^ r * F r) hrank
  have herror :=
    finite_error_sum_le_top_power_factorial_series_from_brun
      F X M (2 * R) hX hM hF0 hFnonneg hrec
  calc
    (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤
        ∑ r ∈ Finset.range (2 * R + 1), (main r + X ^ r * F r) := htransfer
    _ = (∑ r ∈ Finset.range (2 * R + 1), main r) +
        ∑ r ∈ Finset.range (2 * R + 1), X ^ r * F r := by
          rw [Finset.sum_add_distrib]
    _ ≤ (∑ r ∈ Finset.range (2 * R + 1), main r) +
        X ^ (2 * R) *
          (∑ r ∈ Finset.range (2 * R + 1),
            M ^ r / (Nat.factorial r : ℚ)) := by
          exact add_le_add_left herror _

theorem satEventFiniteIntervalTransfer_rat_le_top_power_brun_error_budget
    (N R : Nat) (events : Finset SatEvent)
    (main F : Nat → ℚ) (X M E : ℚ)
    (hX : 1 ≤ X)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hFnonneg : ∀ r : Nat, r ≤ 2 * R → 0 ≤ F r)
    (hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * F r ≤ M * F (r - 1))
    (hrank : ∀ r ∈ Finset.range (2 * R + 1),
      (((-1 : Int) ^ r) *
        ((∑ s ∈ events.powersetCard r,
            satEventCommonHitCountUpTo N s : Nat) : Int) : ℚ) ≤
          main r + X ^ r * F r)
    (henvelope : (∑ r ∈ Finset.range (2 * R + 1),
      M ^ r / (Nat.factorial r : ℚ)) ≤ E) :
    (satEventNoHitIndicatorSumUpTo N events : ℚ) ≤
      (∑ r ∈ Finset.range (2 * R + 1), main r) + X ^ (2 * R) * E := by
  have htransfer :=
    satEventFiniteIntervalTransfer_rat_le_main_plus_top_power_brun_error
      N R events main F X M hX hM hF0 hFnonneg hrec hrank
  have hXnonneg : 0 ≤ X := by linarith
  have hpowNonneg : 0 ≤ X ^ (2 * R) := pow_nonneg hXnonneg (2 * R)
  exact le_trans htransfer
    (add_le_add_left (mul_le_mul_of_nonneg_left henvelope hpowNonneg) _)

theorem baseSatEventFiniteIntervalTransfer_rat_le_top_power_brun_error_budget
    (N Pz b R : Nat) (events : Finset SatEvent)
    (main F : Nat → ℚ) (X M E : ℚ)
    (hX : 1 ≤ X)
    (hM : 0 ≤ M)
    (hF0 : F 0 ≤ 1)
    (hFnonneg : ∀ r : Nat, r ≤ 2 * R → 0 ≤ F r)
    (hrec : ∀ r : Nat, 1 ≤ r →
      (r : ℚ) * F r ≤ M * F (r - 1))
    (hrank : ∀ r ∈ Finset.range (2 * R + 1),
      (((-1 : Int) ^ r) *
        ((∑ s ∈ events.powersetCard r,
            baseSatEventCommonHitCountUpTo N Pz b s : Nat) : Int) : ℚ) ≤
          main r + X ^ r * F r)
    (henvelope : (∑ r ∈ Finset.range (2 * R + 1),
      M ^ r / (Nat.factorial r : ℚ)) ≤ E) :
    (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤
      (∑ r ∈ Finset.range (2 * R + 1), main r) + X ^ (2 * R) * E := by
  have htransfer :=
    baseSatEventFiniteIntervalTransfer_rat_le_main_plus_top_power_brun_error
      N Pz b R events main F X M hX hM hF0 hFnonneg hrec hrank
  have hXnonneg : 0 ≤ X := by linarith
  have hpowNonneg : 0 ≤ X ^ (2 * R) := pow_nonneg hXnonneg (2 * R)
  exact le_trans htransfer
    (add_le_add_left (mul_le_mul_of_nonneg_left henvelope hpowNonneg) _)

theorem satEventNoHitIndicatorSumUpTo_eq_rowNoHitIndicatorSumUpTo
    (N Pz rho : Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event) :
    satEventNoHitIndicatorSumUpTo N events =
      rowNoHitIndicatorSumUpTo N (satEventResidualHitRowsFinset events) := by
  classical
  unfold satEventNoHitIndicatorSumUpTo rowNoHitIndicatorSumUpTo
  apply Finset.sum_congr rfl
  intro n _hn
  have hzero :
      hitEventCount (satEventResidualHitRowsFinset events)
          (fun row => n ≡ row.2 [MOD row.1]) = 0 ↔
        hitEventCount events (fun event => satEventHit n event) = 0 := by
    simpa [satEventResidualHitRowsFinset] using
      (hitEventCount_image_eq_zero_iff events satEventResidualHitRow
        (fun event => satEventHit n event)
        (fun row : Nat × Nat => n ≡ row.2 [MOD row.1])
        (by
          intro event hevent
          have hdPlusPos : 0 < event.dPlus :=
            (hadm event hevent).2.2.2.2.2.1
          have hpPos : 0 < event.p := (hadm event hevent).1.pos
          have hq : 0 < conditionalModulus event.dPlus event.p :=
            Nat.mul_pos hdPlusPos hpPos
          exact (satEventHit_iff_modEq_residualHitRow n event hq).symm))
  by_cases hevents : hitEventCount events (fun event => satEventHit n event) = 0
  · have hrows : hitEventCount (satEventResidualHitRowsFinset events)
          (fun row => n ≡ row.2 [MOD row.1]) = 0 := hzero.mpr hevents
    simp [hevents, hrows]
  · have hrows : hitEventCount (satEventResidualHitRowsFinset events)
          (fun row => n ≡ row.2 [MOD row.1]) ≠ 0 := by
        intro h
        exact hevents (hzero.mp h)
    simp [hevents, hrows]

theorem baseSatEventNoHitIndicatorSumUpTo_eq_baseRowNoHitIndicatorSumUpTo
    (N Pz b rho : Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event) :
    baseSatEventNoHitIndicatorSumUpTo N Pz b events =
      baseRowNoHitIndicatorSumUpTo N Pz b (satEventResidualHitRowsFinset events) := by
  classical
  unfold baseSatEventNoHitIndicatorSumUpTo baseRowNoHitIndicatorSumUpTo
  apply Finset.sum_congr rfl
  intro n _hn
  have hzero :
      hitEventCount (satEventResidualHitRowsFinset events)
          (fun row => n ≡ row.2 [MOD row.1]) = 0 ↔
        hitEventCount events (fun event => satEventHit n event) = 0 := by
    simpa [satEventResidualHitRowsFinset] using
      (hitEventCount_image_eq_zero_iff events satEventResidualHitRow
        (fun event => satEventHit n event)
        (fun row : Nat × Nat => n ≡ row.2 [MOD row.1])
        (by
          intro event hevent
          have hdPlusPos : 0 < event.dPlus :=
            (hadm event hevent).2.2.2.2.2.1
          have hpPos : 0 < event.p := (hadm event hevent).1.pos
          have hq : 0 < conditionalModulus event.dPlus event.p :=
            Nat.mul_pos hdPlusPos hpPos
          exact (satEventHit_iff_modEq_residualHitRow n event hq).symm))
  by_cases hevents : hitEventCount events (fun event => satEventHit n event) = 0
  · have hrows : hitEventCount (satEventResidualHitRowsFinset events)
          (fun row => n ≡ row.2 [MOD row.1]) = 0 := hzero.mpr hevents
    simp [hevents, hrows]
  · have hrows : hitEventCount (satEventResidualHitRowsFinset events)
          (fun row => n ≡ row.2 [MOD row.1]) ≠ 0 := by
        intro h
        exact hevents (hzero.mp h)
    simp [hevents, hrows]

theorem satEventNoHitIndicatorSumUpTo_eq_rowNoHitIndicatorSumUpTo_admissibleFor
    (N Pz : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event) :
    satEventNoHitIndicatorSumUpTo N events =
      rowNoHitIndicatorSumUpTo N (satEventResidualHitRowsFinset events) := by
  classical
  unfold satEventNoHitIndicatorSumUpTo rowNoHitIndicatorSumUpTo
  apply Finset.sum_congr rfl
  intro n _hn
  have hzero :
      hitEventCount (satEventResidualHitRowsFinset events)
          (fun row => n ≡ row.2 [MOD row.1]) = 0 ↔
        hitEventCount events (fun event => satEventHit n event) = 0 := by
    simpa [satEventResidualHitRowsFinset] using
      (hitEventCount_image_eq_zero_iff events satEventResidualHitRow
        (fun event => satEventHit n event)
        (fun row : Nat × Nat => n ≡ row.2 [MOD row.1])
        (by
          intro event hevent
          have heventAdm : satEventAdmissible Pz (rhoOf event.e) event := by
            simpa [satEventAdmissibleFor] using hadm event hevent
          have hq : 0 < conditionalModulus event.dPlus event.p :=
            Nat.mul_pos heventAdm.2.2.2.2.2.1 heventAdm.1.pos
          exact (satEventHit_iff_modEq_residualHitRow n event hq).symm))
  by_cases hevents : hitEventCount events (fun event => satEventHit n event) = 0
  · have hrows : hitEventCount (satEventResidualHitRowsFinset events)
          (fun row => n ≡ row.2 [MOD row.1]) = 0 := hzero.mpr hevents
    simp [hevents, hrows]
  · have hrows : hitEventCount (satEventResidualHitRowsFinset events)
          (fun row => n ≡ row.2 [MOD row.1]) ≠ 0 := by
        intro h
        exact hevents (hzero.mp h)
    simp [hevents, hrows]

theorem baseSatEventNoHitIndicatorSumUpTo_eq_baseRowNoHitIndicatorSumUpTo_admissibleFor
    (N Pz b : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event) :
    baseSatEventNoHitIndicatorSumUpTo N Pz b events =
      baseRowNoHitIndicatorSumUpTo N Pz b (satEventResidualHitRowsFinset events) := by
  classical
  unfold baseSatEventNoHitIndicatorSumUpTo baseRowNoHitIndicatorSumUpTo
  apply Finset.sum_congr rfl
  intro n _hn
  have hzero :
      hitEventCount (satEventResidualHitRowsFinset events)
          (fun row => n ≡ row.2 [MOD row.1]) = 0 ↔
        hitEventCount events (fun event => satEventHit n event) = 0 := by
    simpa [satEventResidualHitRowsFinset] using
      (hitEventCount_image_eq_zero_iff events satEventResidualHitRow
        (fun event => satEventHit n event)
        (fun row : Nat × Nat => n ≡ row.2 [MOD row.1])
        (by
          intro event hevent
          have heventAdm : satEventAdmissible Pz (rhoOf event.e) event := by
            simpa [satEventAdmissibleFor] using hadm event hevent
          have hq : 0 < conditionalModulus event.dPlus event.p :=
            Nat.mul_pos heventAdm.2.2.2.2.2.1 heventAdm.1.pos
          exact (satEventHit_iff_modEq_residualHitRow n event hq).symm))
  by_cases hevents : hitEventCount events (fun event => satEventHit n event) = 0
  · have hrows : hitEventCount (satEventResidualHitRowsFinset events)
          (fun row => n ≡ row.2 [MOD row.1]) = 0 := hzero.mpr hevents
    simp [hevents, hrows]
  · have hrows : hitEventCount (satEventResidualHitRowsFinset events)
          (fun row => n ≡ row.2 [MOD row.1]) ≠ 0 := by
        intro h
        exact hevents (hzero.mp h)
    simp [hevents, hrows]

theorem exists_satEventHit_of_rowNoHitIndicatorSum_lt_admissibleFor
    (N Pz : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent) (B : Int)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hbound :
      rowNoHitIndicatorSumUpTo N (satEventResidualHitRowsFinset events) ≤ B)
    (hlt : B < ((N + 1 : Nat) : Int)) :
    ∃ n : Nat, n ≤ N ∧ ∃ event ∈ events, satEventHit n event := by
  apply exists_satEventHit_of_noHitIndicatorSum_lt N events B
  · rwa [satEventNoHitIndicatorSumUpTo_eq_rowNoHitIndicatorSumUpTo_admissibleFor
      N Pz rhoOf events hadm]
  · exact hlt

theorem exists_satEventHit_of_rowNoHitIndicatorSum_rat_lt_admissibleFor
    (N Pz : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent) (B : ℚ)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hbound :
      (rowNoHitIndicatorSumUpTo N
        (satEventResidualHitRowsFinset events) : ℚ) ≤ B)
    (hlt : B < ((N + 1 : Nat) : ℚ)) :
    ∃ n : Nat, n ≤ N ∧ ∃ event ∈ events, satEventHit n event := by
  apply exists_satEventHit_of_noHitIndicatorSum_rat_lt N events B
  · rwa [satEventNoHitIndicatorSumUpTo_eq_rowNoHitIndicatorSumUpTo_admissibleFor
      N Pz rhoOf events hadm]
  · exact hlt

theorem exists_baseSatEventHit_of_baseRowNoHitIndicatorSum_lt_admissibleFor
    (N Pz b : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent) (B : Int)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hbound :
      baseRowNoHitIndicatorSumUpTo N Pz b
        (satEventResidualHitRowsFinset events) ≤ B)
    (hlt :
      B <
        (((Finset.range (N + 1)).filter
          (fun n => n ≡ b [MOD Pz])).card : Int)) :
    ∃ n : Nat, n ≤ N ∧ n ≡ b [MOD Pz] ∧
      ∃ event ∈ events, satEventHit n event := by
  apply exists_baseSatEventHit_of_baseNoHitIndicatorSum_lt N Pz b events B
  · rwa [baseSatEventNoHitIndicatorSumUpTo_eq_baseRowNoHitIndicatorSumUpTo_admissibleFor
      N Pz b rhoOf events hadm]
  · exact hlt

theorem exists_baseSatEventHit_of_baseRowNoHitIndicatorSum_rat_lt_admissibleFor
    (N Pz b : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent) (B : ℚ)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hbound :
      (baseRowNoHitIndicatorSumUpTo N Pz b
        (satEventResidualHitRowsFinset events) : ℚ) ≤ B)
    (hlt :
      B <
        (((Finset.range (N + 1)).filter
          (fun n => n ≡ b [MOD Pz])).card : ℚ)) :
    ∃ n : Nat, n ≤ N ∧ n ≡ b [MOD Pz] ∧
      ∃ event ∈ events, satEventHit n event := by
  apply exists_baseSatEventHit_of_baseNoHitIndicatorSum_rat_lt N Pz b events B
  · rwa [baseSatEventNoHitIndicatorSumUpTo_eq_baseRowNoHitIndicatorSumUpTo_admissibleFor
      N Pz b rhoOf events hadm]
  · exact hlt

noncomputable def rowSignedCommonHitSumUpTo
    (N R : Nat) (events : Finset (Nat × Nat)) : Int :=
  ∑ r ∈ Finset.range (2 * R + 1),
    ((-1 : Int) ^ r) *
      ((∑ s ∈ events.powersetCard r,
          rowEventCommonHitCountUpTo N s : Nat) : Int)

noncomputable def baseRowSignedCommonHitSumUpTo
    (N Pz b R : Nat) (events : Finset (Nat × Nat)) : Int :=
  ∑ r ∈ Finset.range (2 * R + 1),
    ((-1 : Int) ^ r) *
      ((∑ s ∈ events.powersetCard r,
          baseRowEventCommonHitCountUpTo N Pz b s : Nat) : Int)

theorem rowFiniteIntervalTransfer_bonferroni_skeleton
    (N R : Nat) (events : Finset (Nat × Nat)) :
    rowNoHitIndicatorSumUpTo N events ≤
      rowSignedCommonHitSumUpTo N R events := by
  simpa [rowNoHitIndicatorSumUpTo, rowSignedCommonHitSumUpTo] using
    rowEventSubsets_bonferroni_lower_double_count N R events

theorem baseFiniteIntervalTransfer_bonferroni_skeleton
    (N Pz b R : Nat) (events : Finset (Nat × Nat)) :
    baseRowNoHitIndicatorSumUpTo N Pz b events ≤
      baseRowSignedCommonHitSumUpTo N Pz b R events := by
  simpa [baseRowNoHitIndicatorSumUpTo, baseRowSignedCommonHitSumUpTo] using
    baseRowEventSubsets_bonferroni_lower_double_count N Pz b R events

theorem baseFiniteIntervalTransfer_of_signed_bound
    (N Pz b R : Nat) (events : Finset (Nat × Nat)) (B : Int)
    (hsigned : baseRowSignedCommonHitSumUpTo N Pz b R events ≤ B) :
    baseRowNoHitIndicatorSumUpTo N Pz b events ≤ B :=
  le_trans (baseFiniteIntervalTransfer_bonferroni_skeleton N Pz b R events) hsigned

theorem rowFiniteIntervalTransfer_of_signed_bound
    (N R : Nat) (events : Finset (Nat × Nat)) (B : Int)
    (hsigned : rowSignedCommonHitSumUpTo N R events ≤ B) :
    rowNoHitIndicatorSumUpTo N events ≤ B :=
  le_trans (rowFiniteIntervalTransfer_bonferroni_skeleton N R events) hsigned

theorem rowFiniteIntervalTransfer_of_rank_signed_bounds
    (N R : Nat) (events : Finset (Nat × Nat)) (B : Nat → Int)
    (hrank : ∀ r ∈ Finset.range (2 * R + 1),
      ((-1 : Int) ^ r) *
        ((∑ s ∈ events.powersetCard r,
            rowEventCommonHitCountUpTo N s : Nat) : Int) ≤ B r) :
    rowNoHitIndicatorSumUpTo N events ≤
      ∑ r ∈ Finset.range (2 * R + 1), B r := by
  apply le_trans (rowFiniteIntervalTransfer_bonferroni_skeleton N R events)
  unfold rowSignedCommonHitSumUpTo
  apply Finset.sum_le_sum
  intro r hr
  exact hrank r hr

theorem baseFiniteIntervalTransfer_of_rank_signed_bounds
    (N Pz b R : Nat) (events : Finset (Nat × Nat)) (B : Nat → Int)
    (hrank : ∀ r ∈ Finset.range (2 * R + 1),
      ((-1 : Int) ^ r) *
        ((∑ s ∈ events.powersetCard r,
            baseRowEventCommonHitCountUpTo N Pz b s : Nat) : Int) ≤ B r) :
    baseRowNoHitIndicatorSumUpTo N Pz b events ≤
      ∑ r ∈ Finset.range (2 * R + 1), B r := by
  apply le_trans (baseFiniteIntervalTransfer_bonferroni_skeleton N Pz b R events)
  unfold baseRowSignedCommonHitSumUpTo
  apply Finset.sum_le_sum
  intro r hr
  exact hrank r hr

theorem rowFiniteIntervalTransfer_rat_of_rank_signed_bounds
    (N R : Nat) (events : Finset (Nat × Nat)) (B : Nat → ℚ)
    (hrank : ∀ r ∈ Finset.range (2 * R + 1),
      (((-1 : Int) ^ r) *
        ((∑ s ∈ events.powersetCard r,
            rowEventCommonHitCountUpTo N s : Nat) : Int) : ℚ) ≤ B r) :
    (rowNoHitIndicatorSumUpTo N events : ℚ) ≤
      ∑ r ∈ Finset.range (2 * R + 1), B r := by
  have hskeleton := rowFiniteIntervalTransfer_bonferroni_skeleton N R events
  calc
    (rowNoHitIndicatorSumUpTo N events : ℚ) ≤
        (rowSignedCommonHitSumUpTo N R events : ℚ) := by
          exact_mod_cast hskeleton
    _ = ∑ r ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ r) *
          ((∑ s ∈ events.powersetCard r,
              rowEventCommonHitCountUpTo N s : Nat) : Int) : ℚ) := by
          simp [rowSignedCommonHitSumUpTo]
    _ ≤ ∑ r ∈ Finset.range (2 * R + 1), B r := by
          apply Finset.sum_le_sum
          intro r hr
          exact hrank r hr

theorem baseFiniteIntervalTransfer_rat_of_rank_signed_bounds
    (N Pz b R : Nat) (events : Finset (Nat × Nat)) (B : Nat → ℚ)
    (hrank : ∀ r ∈ Finset.range (2 * R + 1),
      (((-1 : Int) ^ r) *
        ((∑ s ∈ events.powersetCard r,
            baseRowEventCommonHitCountUpTo N Pz b s : Nat) : Int) : ℚ) ≤ B r) :
    (baseRowNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤
      ∑ r ∈ Finset.range (2 * R + 1), B r := by
  have hskeleton := baseFiniteIntervalTransfer_bonferroni_skeleton N Pz b R events
  calc
    (baseRowNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤
        (baseRowSignedCommonHitSumUpTo N Pz b R events : ℚ) := by
          exact_mod_cast hskeleton
    _ = ∑ r ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ r) *
          ((∑ s ∈ events.powersetCard r,
              baseRowEventCommonHitCountUpTo N Pz b s : Nat) : Int) : ℚ) := by
          simp [baseRowSignedCommonHitSumUpTo]
    _ ≤ ∑ r ∈ Finset.range (2 * R + 1), B r := by
          apply Finset.sum_le_sum
          intro r hr
          exact hrank r hr

theorem rowFiniteIntervalTransfer_rat_of_even_rank_bounds
    (N R : Nat) (events : Finset (Nat × Nat)) (B : Nat → ℚ)
    (heven : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          rowEventCommonHitCountUpTo N s : Nat) : ℚ) ≤ B r)
    (hodd : ∀ r ∈ Finset.range (2 * R + 1), Odd r → 0 ≤ B r) :
    (rowNoHitIndicatorSumUpTo N events : ℚ) ≤
      ∑ r ∈ Finset.range (2 * R + 1), B r :=
  rowFiniteIntervalTransfer_rat_of_rank_signed_bounds N R events B (by
    intro r hr
    exact negOnePow_mul_natCast_le_of_even_or_odd_budget r
      (∑ s ∈ events.powersetCard r, rowEventCommonHitCountUpTo N s)
      (B r) (heven r hr) (hodd r hr))

theorem baseFiniteIntervalTransfer_rat_of_even_rank_bounds
    (N Pz b R : Nat) (events : Finset (Nat × Nat)) (B : Nat → ℚ)
    (heven : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          baseRowEventCommonHitCountUpTo N Pz b s : Nat) : ℚ) ≤ B r)
    (hodd : ∀ r ∈ Finset.range (2 * R + 1), Odd r → 0 ≤ B r) :
    (baseRowNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤
      ∑ r ∈ Finset.range (2 * R + 1), B r :=
  baseFiniteIntervalTransfer_rat_of_rank_signed_bounds N Pz b R events B (by
    intro r hr
    exact negOnePow_mul_natCast_le_of_even_or_odd_budget r
      (∑ s ∈ events.powersetCard r, baseRowEventCommonHitCountUpTo N Pz b s)
      (B r) (heven r hr) (hodd r hr))

theorem rowFiniteIntervalTransfer_rat_of_even_upper_odd_lower_rank_bounds
    (N R : Nat) (events : Finset (Nat × Nat)) (upper lower : Nat → ℚ)
    (heven : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          rowEventCommonHitCountUpTo N s : Nat) : ℚ) ≤ upper r)
    (hodd : ∀ r ∈ Finset.range (2 * R + 1), Odd r →
      lower r ≤
        ((∑ s ∈ events.powersetCard r,
          rowEventCommonHitCountUpTo N s : Nat) : ℚ)) :
    (rowNoHitIndicatorSumUpTo N events : ℚ) ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        if Even r then upper r else - lower r :=
  rowFiniteIntervalTransfer_rat_of_rank_signed_bounds
    N R events (fun r => if Even r then upper r else - lower r) (by
      intro r hr
      exact negOnePow_mul_natCast_le_of_even_upper_odd_lower r
        (∑ s ∈ events.powersetCard r, rowEventCommonHitCountUpTo N s)
        (upper r) (lower r) (heven r hr) (hodd r hr))

theorem baseFiniteIntervalTransfer_rat_of_even_upper_odd_lower_rank_bounds
    (N Pz b R : Nat) (events : Finset (Nat × Nat)) (upper lower : Nat → ℚ)
    (heven : ∀ r ∈ Finset.range (2 * R + 1), Even r →
      ((∑ s ∈ events.powersetCard r,
          baseRowEventCommonHitCountUpTo N Pz b s : Nat) : ℚ) ≤ upper r)
    (hodd : ∀ r ∈ Finset.range (2 * R + 1), Odd r →
      lower r ≤
        ((∑ s ∈ events.powersetCard r,
          baseRowEventCommonHitCountUpTo N Pz b s : Nat) : ℚ)) :
    (baseRowNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        if Even r then upper r else - lower r :=
  baseFiniteIntervalTransfer_rat_of_rank_signed_bounds
    N Pz b R events (fun r => if Even r then upper r else - lower r) (by
      intro r hr
      exact negOnePow_mul_natCast_le_of_even_upper_odd_lower r
        (∑ s ∈ events.powersetCard r,
          baseRowEventCommonHitCountUpTo N Pz b s)
        (upper r) (lower r) (heven r hr) (hodd r hr))

/-- Each signed Bonferroni term is bounded above by its unsigned common-hit
count.  This is the finite point where no cancellation is claimed. -/
theorem negOnePow_mul_natCast_le_natCast (r n : Nat) :
    ((-1 : Int) ^ r) * (n : Int) ≤ (n : Int) := by
  rcases neg_one_pow_eq_or Int r with h | h
  · rw [h]
    simp
  · rw [h]
    have hn : 0 ≤ (n : Int) := by exact_mod_cast Nat.zero_le n
    linarith

theorem satEventSignedCommonHitSumUpTo_le_event_lcm_bound
    (N Pz rho R : Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event) :
    satEventSignedCommonHitSumUpTo N R events ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ events.powersetCard r,
          (N / congruenceLcm (satEventResidualHitRowsFinset s).toList + 1)
            : Nat) : Int) := by
  classical
  unfold satEventSignedCommonHitSumUpTo
  calc
    (∑ r ∈ Finset.range (2 * R + 1),
        (-1 : Int) ^ r *
          ((∑ s ∈ events.powersetCard r,
            satEventCommonHitCountUpTo N s : Nat) : Int)) ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ events.powersetCard r,
          satEventCommonHitCountUpTo N s : Nat) : Int) := by
        apply Finset.sum_le_sum
        intro r _hr
        exact negOnePow_mul_natCast_le_natCast r
          (∑ s ∈ events.powersetCard r, satEventCommonHitCountUpTo N s)
    _ ≤ ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ events.powersetCard r,
          (N / congruenceLcm (satEventResidualHitRowsFinset s).toList + 1)
            : Nat) : Int) := by
        apply Finset.sum_le_sum
        intro r _hr
        exact_mod_cast satEventCommonHitSum_le_event_lcm_bound
          N Pz rho r events hadm

theorem baseSatEventSignedCommonHitSumUpTo_le_event_lcm_bound
    (N Pz b rho R : Nat) (events : Finset SatEvent)
    (hPz : 0 < Pz)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hpCop : ∀ event ∈ events, Nat.Coprime Pz event.p) :
    baseSatEventSignedCommonHitSumUpTo N Pz b R events ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ events.powersetCard r,
          (N / (Pz * congruenceLcm (satEventResidualHitRowsFinset s).toList) + 1)
            : Nat) : Int) := by
  classical
  unfold baseSatEventSignedCommonHitSumUpTo
  calc
    (∑ r ∈ Finset.range (2 * R + 1),
        (-1 : Int) ^ r *
          ((∑ s ∈ events.powersetCard r,
            baseSatEventCommonHitCountUpTo N Pz b s : Nat) : Int)) ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ events.powersetCard r,
          baseSatEventCommonHitCountUpTo N Pz b s : Nat) : Int) := by
        apply Finset.sum_le_sum
        intro r _hr
        exact negOnePow_mul_natCast_le_natCast r
          (∑ s ∈ events.powersetCard r,
            baseSatEventCommonHitCountUpTo N Pz b s)
    _ ≤ ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ events.powersetCard r,
          (N / (Pz * congruenceLcm (satEventResidualHitRowsFinset s).toList) + 1)
            : Nat) : Int) := by
        apply Finset.sum_le_sum
        intro r _hr
        exact_mod_cast baseSatEventCommonHitSum_le_event_lcm_bound
          N Pz b rho r events hPz hadm hpCop

theorem satEventSignedCommonHitSumUpTo_le_event_lcm_bound_admissibleFor
    (N Pz R : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event) :
    satEventSignedCommonHitSumUpTo N R events ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ events.powersetCard r,
          (N / congruenceLcm (satEventResidualHitRowsFinset s).toList + 1)
            : Nat) : Int) := by
  classical
  unfold satEventSignedCommonHitSumUpTo
  calc
    (∑ r ∈ Finset.range (2 * R + 1),
        (-1 : Int) ^ r *
          ((∑ s ∈ events.powersetCard r,
            satEventCommonHitCountUpTo N s : Nat) : Int)) ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ events.powersetCard r,
          satEventCommonHitCountUpTo N s : Nat) : Int) := by
        apply Finset.sum_le_sum
        intro r _hr
        exact negOnePow_mul_natCast_le_natCast r
          (∑ s ∈ events.powersetCard r, satEventCommonHitCountUpTo N s)
    _ ≤ ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ events.powersetCard r,
          (N / congruenceLcm (satEventResidualHitRowsFinset s).toList + 1)
            : Nat) : Int) := by
        apply Finset.sum_le_sum
        intro r _hr
        exact_mod_cast satEventCommonHitSum_le_event_lcm_bound_admissibleFor
          N Pz r rhoOf events hadm

theorem baseSatEventSignedCommonHitSumUpTo_le_event_lcm_bound_admissibleFor
    (N Pz b R : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hPz : 0 < Pz)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hpCop : ∀ event ∈ events, Nat.Coprime Pz event.p) :
    baseSatEventSignedCommonHitSumUpTo N Pz b R events ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ events.powersetCard r,
          (N / (Pz * congruenceLcm (satEventResidualHitRowsFinset s).toList) + 1)
            : Nat) : Int) := by
  classical
  unfold baseSatEventSignedCommonHitSumUpTo
  calc
    (∑ r ∈ Finset.range (2 * R + 1),
        (-1 : Int) ^ r *
          ((∑ s ∈ events.powersetCard r,
            baseSatEventCommonHitCountUpTo N Pz b s : Nat) : Int)) ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ events.powersetCard r,
          baseSatEventCommonHitCountUpTo N Pz b s : Nat) : Int) := by
        apply Finset.sum_le_sum
        intro r _hr
        exact negOnePow_mul_natCast_le_natCast r
          (∑ s ∈ events.powersetCard r,
            baseSatEventCommonHitCountUpTo N Pz b s)
    _ ≤ ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ events.powersetCard r,
          (N / (Pz * congruenceLcm (satEventResidualHitRowsFinset s).toList) + 1)
            : Nat) : Int) := by
        apply Finset.sum_le_sum
        intro r _hr
        exact_mod_cast baseSatEventCommonHitSum_le_event_lcm_bound_admissibleFor
          N Pz b r rhoOf events hPz hadm hpCop

theorem satEventFiniteIntervalTransfer_le_event_lcm_bound
    (N Pz rho R : Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event) :
    satEventNoHitIndicatorSumUpTo N events ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ events.powersetCard r,
          (N / congruenceLcm (satEventResidualHitRowsFinset s).toList + 1)
            : Nat) : Int) :=
  le_trans (satEventFiniteIntervalTransfer_bonferroni_skeleton N R events)
    (satEventSignedCommonHitSumUpTo_le_event_lcm_bound N Pz rho R events hadm)

theorem baseSatEventFiniteIntervalTransfer_le_event_lcm_bound
    (N Pz b rho R : Nat) (events : Finset SatEvent)
    (hPz : 0 < Pz)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hpCop : ∀ event ∈ events, Nat.Coprime Pz event.p) :
    baseSatEventNoHitIndicatorSumUpTo N Pz b events ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ events.powersetCard r,
          (N / (Pz * congruenceLcm (satEventResidualHitRowsFinset s).toList) + 1)
            : Nat) : Int) :=
  le_trans (baseSatEventFiniteIntervalTransfer_bonferroni_skeleton
    N Pz b R events)
    (baseSatEventSignedCommonHitSumUpTo_le_event_lcm_bound
      N Pz b rho R events hPz hadm hpCop)

theorem satEventFiniteIntervalTransfer_le_event_lcm_bound_admissibleFor
    (N Pz R : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event) :
    satEventNoHitIndicatorSumUpTo N events ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ events.powersetCard r,
          (N / congruenceLcm (satEventResidualHitRowsFinset s).toList + 1)
            : Nat) : Int) :=
  le_trans (satEventFiniteIntervalTransfer_bonferroni_skeleton N R events)
    (satEventSignedCommonHitSumUpTo_le_event_lcm_bound_admissibleFor
      N Pz R rhoOf events hadm)

theorem baseSatEventFiniteIntervalTransfer_le_event_lcm_bound_admissibleFor
    (N Pz b R : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hPz : 0 < Pz)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hpCop : ∀ event ∈ events, Nat.Coprime Pz event.p) :
    baseSatEventNoHitIndicatorSumUpTo N Pz b events ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ events.powersetCard r,
          (N / (Pz * congruenceLcm (satEventResidualHitRowsFinset s).toList) + 1)
            : Nat) : Int) :=
  le_trans (baseSatEventFiniteIntervalTransfer_bonferroni_skeleton
    N Pz b R events)
    (baseSatEventSignedCommonHitSumUpTo_le_event_lcm_bound_admissibleFor
      N Pz b R rhoOf events hPz hadm hpCop)

theorem rowSignedCommonHitSumUpTo_le_unsignedCommonHitSumUpTo
    (N R : Nat) (events : Finset (Nat × Nat)) :
    rowSignedCommonHitSumUpTo N R events ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ events.powersetCard r,
          rowEventCommonHitCountUpTo N s : Nat) : Int) := by
  classical
  unfold rowSignedCommonHitSumUpTo
  apply Finset.sum_le_sum
  intro r _hr
  exact negOnePow_mul_natCast_le_natCast r
    (∑ s ∈ events.powersetCard r, rowEventCommonHitCountUpTo N s)

theorem baseRowSignedCommonHitSumUpTo_le_unsignedCommonHitSumUpTo
    (N Pz b R : Nat) (events : Finset (Nat × Nat)) :
    baseRowSignedCommonHitSumUpTo N Pz b R events ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ events.powersetCard r,
          baseRowEventCommonHitCountUpTo N Pz b s : Nat) : Int) := by
  classical
  unfold baseRowSignedCommonHitSumUpTo
  apply Finset.sum_le_sum
  intro r _hr
  exact negOnePow_mul_natCast_le_natCast r
    (∑ s ∈ events.powersetCard r, baseRowEventCommonHitCountUpTo N Pz b s)

/-- Exact finite transfer bound after discarding Bonferroni cancellation and
keeping only compatible residual intersections.  This packages the pointwise
Bonferroni inequality, finite double counting, CRT emptiness for incompatible
row systems, and the one-residue-class interval bound. -/
theorem rowFiniteIntervalTransfer_le_compatible_lcm_bound
    (N R : Nat) (events : Finset (Nat × Nat))
    (hpos : ∀ row ∈ events, 0 < row.1) :
    rowNoHitIndicatorSumUpTo N events ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ rowCompatibleSubsetsOfCard events r,
          (N / congruenceLcm s.toList + 1) : Nat) : Int) := by
  classical
  have hsigned :
      rowNoHitIndicatorSumUpTo N events ≤ rowSignedCommonHitSumUpTo N R events :=
    rowFiniteIntervalTransfer_bonferroni_skeleton N R events
  have hunsigned :
      rowSignedCommonHitSumUpTo N R events ≤
        ∑ r ∈ Finset.range (2 * R + 1),
          ((∑ s ∈ events.powersetCard r,
            rowEventCommonHitCountUpTo N s : Nat) : Int) :=
    rowSignedCommonHitSumUpTo_le_unsignedCommonHitSumUpTo N R events
  have hlcm :
      (∑ r ∈ Finset.range (2 * R + 1),
          ((∑ s ∈ events.powersetCard r,
            rowEventCommonHitCountUpTo N s : Nat) : Int)) ≤
        ∑ r ∈ Finset.range (2 * R + 1),
          ((∑ s ∈ rowCompatibleSubsetsOfCard events r,
            (N / congruenceLcm s.toList + 1) : Nat) : Int) := by
    apply Finset.sum_le_sum
    intro r _hr
    exact_mod_cast
      rowEventCommonHitSum_le_compatible_lcm_bound N r events hpos
  exact le_trans hsigned (le_trans hunsigned hlcm)

/-- Base-conditioned version of the exact finite transfer bound.  The explicit
right-hand side runs only over subsets compatible with the imposed base class,
and each compatible subset is charged by the modulus `Pz * lcm`. -/
theorem baseFiniteIntervalTransfer_le_compatible_lcm_bound
    (N Pz b R : Nat) (events : Finset (Nat × Nat))
    (hPz : 0 < Pz)
    (hpos : ∀ row ∈ events, 0 < row.1)
    (hcopRows : ∀ row ∈ events, Nat.Coprime Pz row.1) :
    baseRowNoHitIndicatorSumUpTo N Pz b events ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ baseRowCompatibleSubsetsOfCard Pz b events r,
          (N / (Pz * congruenceLcm s.toList) + 1) : Nat) : Int) := by
  classical
  have hsigned :
      baseRowNoHitIndicatorSumUpTo N Pz b events ≤
        baseRowSignedCommonHitSumUpTo N Pz b R events :=
    baseFiniteIntervalTransfer_bonferroni_skeleton N Pz b R events
  have hunsigned :
      baseRowSignedCommonHitSumUpTo N Pz b R events ≤
        ∑ r ∈ Finset.range (2 * R + 1),
          ((∑ s ∈ events.powersetCard r,
            baseRowEventCommonHitCountUpTo N Pz b s : Nat) : Int) :=
    baseRowSignedCommonHitSumUpTo_le_unsignedCommonHitSumUpTo N Pz b R events
  have hlcm :
      (∑ r ∈ Finset.range (2 * R + 1),
          ((∑ s ∈ events.powersetCard r,
            baseRowEventCommonHitCountUpTo N Pz b s : Nat) : Int)) ≤
        ∑ r ∈ Finset.range (2 * R + 1),
          ((∑ s ∈ baseRowCompatibleSubsetsOfCard Pz b events r,
            (N / (Pz * congruenceLcm s.toList) + 1) : Nat) : Int) := by
    apply Finset.sum_le_sum
    intro r _hr
    exact_mod_cast
      baseRowEventCommonHitSum_le_compatible_lcm_bound
        N Pz b r events hPz hpos hcopRows
  exact le_trans hsigned (le_trans hunsigned hlcm)

theorem satEventFiniteIntervalTransfer_le_compatible_lcm_bound
    (N Pz rho R : Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event) :
    satEventNoHitIndicatorSumUpTo N events ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ rowCompatibleSubsetsOfCard
            (satEventResidualHitRowsFinset events) r,
          (N / congruenceLcm s.toList + 1) : Nat) : Int) := by
  rw [satEventNoHitIndicatorSumUpTo_eq_rowNoHitIndicatorSumUpTo N Pz rho
    events hadm]
  exact rowFiniteIntervalTransfer_le_compatible_lcm_bound
    N R (satEventResidualHitRowsFinset events)
    (satEventResidualHitRowsFinset_moduliPositive_of_admissible
      Pz rho events hadm)

theorem baseSatEventFiniteIntervalTransfer_le_compatible_lcm_bound
    (N Pz b rho R : Nat) (events : Finset SatEvent)
    (hPz : 0 < Pz)
    (hadm : ∀ event ∈ events, satEventAdmissible Pz rho event)
    (hpCop : ∀ event ∈ events, Nat.Coprime Pz event.p) :
    baseSatEventNoHitIndicatorSumUpTo N Pz b events ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ baseRowCompatibleSubsetsOfCard Pz b
            (satEventResidualHitRowsFinset events) r,
          (N / (Pz * congruenceLcm s.toList) + 1) : Nat) : Int) := by
  rw [baseSatEventNoHitIndicatorSumUpTo_eq_baseRowNoHitIndicatorSumUpTo
    N Pz b rho events hadm]
  exact baseFiniteIntervalTransfer_le_compatible_lcm_bound
    N Pz b R (satEventResidualHitRowsFinset events) hPz
    (satEventResidualHitRowsFinset_moduliPositive_of_admissible
      Pz rho events hadm)
    (satEventResidualHitRowsFinset_base_coprime_of_admissible
      Pz rho events hadm hpCop)

theorem satEventFiniteIntervalTransfer_le_compatible_lcm_bound_admissibleFor
    (N Pz R : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event) :
    satEventNoHitIndicatorSumUpTo N events ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ rowCompatibleSubsetsOfCard
            (satEventResidualHitRowsFinset events) r,
          (N / congruenceLcm s.toList + 1) : Nat) : Int) := by
  rw [satEventNoHitIndicatorSumUpTo_eq_rowNoHitIndicatorSumUpTo_admissibleFor
    N Pz rhoOf events hadm]
  exact rowFiniteIntervalTransfer_le_compatible_lcm_bound
    N R (satEventResidualHitRowsFinset events)
    (satEventResidualHitRowsFinset_moduliPositive_of_admissibleFor
      Pz rhoOf events hadm)

theorem baseSatEventFiniteIntervalTransfer_le_compatible_lcm_bound_admissibleFor
    (N Pz b R : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hPz : 0 < Pz)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hpCop : ∀ event ∈ events, Nat.Coprime Pz event.p) :
    baseSatEventNoHitIndicatorSumUpTo N Pz b events ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ baseRowCompatibleSubsetsOfCard Pz b
            (satEventResidualHitRowsFinset events) r,
          (N / (Pz * congruenceLcm s.toList) + 1) : Nat) : Int) := by
  rw [baseSatEventNoHitIndicatorSumUpTo_eq_baseRowNoHitIndicatorSumUpTo_admissibleFor
    N Pz b rhoOf events hadm]
  exact baseFiniteIntervalTransfer_le_compatible_lcm_bound
    N Pz b R (satEventResidualHitRowsFinset events) hPz
    (satEventResidualHitRowsFinset_moduliPositive_of_admissibleFor
      Pz rhoOf events hadm)
    (satEventResidualHitRowsFinset_base_coprime_of_admissibleFor
      Pz rhoOf events hadm hpCop)

theorem baseSatEventCommonHitCountUpTo_le_div_add_one_of_common_hit_largePrime_admissibleFor
    (N Pz b x : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hPz : 0 < Pz)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hlarge : ∀ event ∈ events, Pz < event.p)
    (hxbase : x ≡ b [MOD Pz])
    (hhit : ∀ event ∈ events, satEventHit x event) :
    baseSatEventCommonHitCountUpTo N Pz b events ≤
      N / (Pz * congruenceLcm (satEventResidualHitRowsFinset events).toList) + 1 := by
  exact
    baseSatEventCommonHitCountUpTo_le_div_add_one_of_common_hit_admissibleFor
      N Pz b x rhoOf events hPz hadm
      (fun event hevent =>
        satEvent_base_coprime_of_admissibleFor_largePrime
          Pz rhoOf event hPz (hadm event hevent) (hlarge event hevent))
      hxbase hhit

theorem baseSatEventCommonHitSum_le_event_lcm_bound_largePrime_admissibleFor
    (N Pz b r : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hPz : 0 < Pz)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hlarge : ∀ event ∈ events, Pz < event.p) :
    (∑ s ∈ events.powersetCard r, baseSatEventCommonHitCountUpTo N Pz b s) ≤
      ∑ s ∈ events.powersetCard r,
        (N / (Pz * congruenceLcm (satEventResidualHitRowsFinset s).toList) + 1) := by
  exact
    baseSatEventCommonHitSum_le_event_lcm_bound_admissibleFor
      N Pz b r rhoOf events hPz hadm
      (fun event hevent =>
        satEvent_base_coprime_of_admissibleFor_largePrime
          Pz rhoOf event hPz (hadm event hevent) (hlarge event hevent))

theorem baseSatEventSignedCommonHitSumUpTo_le_event_lcm_bound_largePrime_admissibleFor
    (N Pz b R : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hPz : 0 < Pz)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hlarge : ∀ event ∈ events, Pz < event.p) :
    baseSatEventSignedCommonHitSumUpTo N Pz b R events ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ events.powersetCard r,
          (N / (Pz * congruenceLcm (satEventResidualHitRowsFinset s).toList) + 1)
            : Nat) : Int) := by
  exact
    baseSatEventSignedCommonHitSumUpTo_le_event_lcm_bound_admissibleFor
      N Pz b R rhoOf events hPz hadm
      (fun event hevent =>
        satEvent_base_coprime_of_admissibleFor_largePrime
          Pz rhoOf event hPz (hadm event hevent) (hlarge event hevent))

theorem baseSatEventFiniteIntervalTransfer_le_event_lcm_bound_largePrime_admissibleFor
    (N Pz b R : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hPz : 0 < Pz)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hlarge : ∀ event ∈ events, Pz < event.p) :
    baseSatEventNoHitIndicatorSumUpTo N Pz b events ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ events.powersetCard r,
          (N / (Pz * congruenceLcm (satEventResidualHitRowsFinset s).toList) + 1)
            : Nat) : Int) := by
  exact
    baseSatEventFiniteIntervalTransfer_le_event_lcm_bound_admissibleFor
      N Pz b R rhoOf events hPz hadm
      (fun event hevent =>
        satEvent_base_coprime_of_admissibleFor_largePrime
          Pz rhoOf event hPz (hadm event hevent) (hlarge event hevent))

theorem baseSatEventFiniteIntervalTransfer_le_compatible_lcm_bound_largePrime_admissibleFor
    (N Pz b R : Nat) (rhoOf : Nat → Nat) (events : Finset SatEvent)
    (hPz : 0 < Pz)
    (hadm : ∀ event ∈ events, satEventAdmissibleFor Pz rhoOf event)
    (hlarge : ∀ event ∈ events, Pz < event.p) :
    baseSatEventNoHitIndicatorSumUpTo N Pz b events ≤
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ baseRowCompatibleSubsetsOfCard Pz b
            (satEventResidualHitRowsFinset events) r,
          (N / (Pz * congruenceLcm s.toList) + 1) : Nat) : Int) := by
  exact
    baseSatEventFiniteIntervalTransfer_le_compatible_lcm_bound_admissibleFor
      N Pz b R rhoOf events hPz hadm
      (fun event hevent =>
        satEvent_base_coprime_of_admissibleFor_largePrime
          Pz rhoOf event hPz (hadm event hevent) (hlarge event hevent))

/-!
## Reduced base-class summation

After the finite-transfer estimate is proved in each reduced base class, the
manuscript sums over reduced residues modulo `P(z)`.  The next theorem checks
the exact finite partition behind that step: the sum of the base-class no-hit
indicator sums over reduced residues is the no-hit sum over integers whose
residue modulo `P` is reduced, with the event family chosen from that residue.
-/

noncomputable def reducedResiduesMod (P : Nat) : Finset Nat := by
  classical
  exact (Finset.range P).filter (fun b => Nat.Coprime b P)

theorem mem_reducedResiduesMod_iff (P b : Nat) :
    b ∈ reducedResiduesMod P ↔ b < P ∧ Nat.Coprime b P := by
  classical
  simp [reducedResiduesMod]

theorem modEq_iff_mod_eq_of_lt (P n b : Nat) (hb : b < P) :
    n ≡ b [MOD P] ↔ n % P = b := by
  unfold Nat.ModEq
  rw [Nat.mod_eq_of_lt hb]

/-- Integers `0 <= n <= N` whose residue modulo `P` is reduced.  For `P = 1`
this set contains `0`, so representation-level callers must either work with a
positive range or supply a separate positivity hypothesis. -/
noncomputable def reducedBasePointSet (N P : Nat) : Finset Nat := by
  classical
  exact (Finset.range (N + 1)).filter (fun n => Nat.Coprime (n % P) P)

theorem reducedBasePointSet_pos_of_one_lt_P
    (N P : Nat) (hP : 1 < P) :
    ∀ n ∈ reducedBasePointSet N P, 0 < n := by
  intro n hn
  by_contra hnNotPos
  have hnZero : n = 0 := Nat.eq_zero_of_not_pos hnNotPos
  have hnCop : Nat.Coprime (n % P) P := (Finset.mem_filter.mp hn).2
  have hzeroCop : Nat.Coprime 0 P := by
    simpa [hnZero] using hnCop
  have hPone : P = 1 := (Nat.coprime_zero_left P).mp hzeroCop
  omega

theorem esRepresentable_of_reducedBasePointSet_coverage_mod_210
    (N n : Nat)
    (hn : 2 ≤ n) (hnLe : n ≤ N)
    (hcover : ∀ m ∈ reducedBasePointSet N 210, 2 ≤ m → esRepresentable m) :
    esRepresentable n := by
  by_contra hnNotRep
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2) hn
  have hex : esExceptional n := by
    simpa [esExceptional] using hnNotRep
  have hcop : Nat.Coprime n 210 :=
    esExceptional_coprime_210 n hnPos hex
  have hcopMod : Nat.Coprime (n % 210) 210 :=
    coprime_mod_right_of_coprime n 210 hcop
  have hnMem : n ∈ reducedBasePointSet N 210 := by
    unfold reducedBasePointSet
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hnLe), hcopMod⟩
  exact hnNotRep (hcover n hnMem hn)

theorem forall_esRepresentable_of_reducedBasePointSet_coverage_mod_210
    (N : Nat)
    (hcover : ∀ n ∈ reducedBasePointSet N 210, 2 ≤ n → esRepresentable n) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n := by
  intro n hn hnLe
  exact esRepresentable_of_reducedBasePointSet_coverage_mod_210
    N n hn hnLe hcover

noncomputable def reducedBaseNoHitIndicatorSumUpTo
    (N P : Nat) (eventsByBase : Nat → Finset (Nat × Nat)) : Int :=
  ∑ n ∈ reducedBasePointSet N P,
    if hitEventCount (eventsByBase (n % P))
      (fun row => n ≡ row.2 [MOD row.1]) = 0
    then (1 : Int) else 0

noncomputable def reducedBaseSatEventNoHitIndicatorSumUpTo
    (N P : Nat) (eventsByBase : Nat → Finset SatEvent) : Int :=
  ∑ n ∈ reducedBasePointSet N P,
    if hitEventCount (eventsByBase (n % P))
      (fun event => satEventHit n event) = 0
    then (1 : Int) else 0

theorem reducedBaseNoHitIndicatorSum_eq_sum_base
    (N P : Nat) (eventsByBase : Nat → Finset (Nat × Nat))
    (hP : 0 < P) :
    (∑ b ∈ reducedResiduesMod P,
      baseRowNoHitIndicatorSumUpTo N P b (eventsByBase b)) =
      reducedBaseNoHitIndicatorSumUpTo N P eventsByBase := by
  classical
  let pointTerm : Nat → Nat → Int := fun b n =>
    if hitEventCount (eventsByBase b)
      (fun row => n ≡ row.2 [MOD row.1]) = 0
    then (1 : Int) else 0
  have hrewrite :
      (∑ b ∈ reducedResiduesMod P,
        baseRowNoHitIndicatorSumUpTo N P b (eventsByBase b)) =
        ∑ b ∈ reducedResiduesMod P,
          ∑ n ∈ Finset.range (N + 1),
            if n ≡ b [MOD P] then pointTerm b n else 0 := by
    apply Finset.sum_congr rfl
    intro b _hb
    unfold baseRowNoHitIndicatorSumUpTo
    change
      (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n ≡ b [MOD P]),
        pointTerm b n) =
      ∑ n ∈ Finset.range (N + 1),
        if n ≡ b [MOD P] then pointTerm b n else 0
    rw [Finset.sum_filter]
  rw [hrewrite]
  rw [Finset.sum_comm]
  unfold reducedBaseNoHitIndicatorSumUpTo reducedBasePointSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hcop : Nat.Coprime (n % P) P
  · have hmem : n % P ∈ reducedResiduesMod P := by
      exact (mem_reducedResiduesMod_iff P (n % P)).2
        ⟨Nat.mod_lt n hP, hcop⟩
    have hsingle :
        (∑ b ∈ reducedResiduesMod P,
          if n ≡ b [MOD P] then pointTerm b n else 0) =
          pointTerm (n % P) n := by
      have hsum := Finset.sum_eq_single_of_mem
        (s := reducedResiduesMod P)
        (f := fun b => if n ≡ b [MOD P] then pointTerm b n else 0)
        (n % P) hmem (by
          intro b hb hbne
          by_cases hmod : n ≡ b [MOD P]
          · have hbLt : b < P := (mem_reducedResiduesMod_iff P b).1 hb |>.1
            have heq : n % P = b := (modEq_iff_mod_eq_of_lt P n b hbLt).1 hmod
            exact (hbne heq.symm).elim
          · simp [hmod])
      have hself : n ≡ n % P [MOD P] :=
        (modEq_iff_mod_eq_of_lt P n (n % P) (Nat.mod_lt n hP)).2 rfl
      simpa [hself] using hsum
    rw [hsingle]
    by_cases hhit :
        hitEventCount (eventsByBase (n % P))
          (fun row => n ≡ row.2 [MOD row.1]) = 0
    · simp [hhit, pointTerm]
      rw [if_pos hcop]
    · simp [hhit, pointTerm]
  · have hzero :
        (∑ b ∈ reducedResiduesMod P,
          if n ≡ b [MOD P] then pointTerm b n else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      by_cases hmod : n ≡ b [MOD P]
      · have hbLt : b < P := (mem_reducedResiduesMod_iff P b).1 hb |>.1
        have hbcop : Nat.Coprime b P := (mem_reducedResiduesMod_iff P b).1 hb |>.2
        have heq : n % P = b := (modEq_iff_mod_eq_of_lt P n b hbLt).1 hmod
        exact (hcop (by simpa [heq] using hbcop)).elim
      · simp [hmod]
    rw [hzero]
    simp [hcop]

theorem reducedBaseNoHitIndicatorSum_le_of_base_bounds
    (N P : Nat) (eventsByBase : Nat → Finset (Nat × Nat)) (B : Nat → Int)
    (hP : 0 < P)
    (hbase : ∀ b ∈ reducedResiduesMod P,
      baseRowNoHitIndicatorSumUpTo N P b (eventsByBase b) ≤ B b) :
    reducedBaseNoHitIndicatorSumUpTo N P eventsByBase ≤
      ∑ b ∈ reducedResiduesMod P, B b := by
  rw [← reducedBaseNoHitIndicatorSum_eq_sum_base N P eventsByBase hP]
  exact Finset.sum_le_sum hbase

theorem reducedBaseSatEventNoHitIndicatorSum_eq_sum_base
    (N P : Nat) (eventsByBase : Nat → Finset SatEvent)
    (hP : 0 < P) :
    (∑ b ∈ reducedResiduesMod P,
      baseSatEventNoHitIndicatorSumUpTo N P b (eventsByBase b)) =
      reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase := by
  classical
  let pointTerm : Nat → Nat → Int := fun b n =>
    if hitEventCount (eventsByBase b)
      (fun event => satEventHit n event) = 0
    then (1 : Int) else 0
  have hrewrite :
      (∑ b ∈ reducedResiduesMod P,
        baseSatEventNoHitIndicatorSumUpTo N P b (eventsByBase b)) =
        ∑ b ∈ reducedResiduesMod P,
          ∑ n ∈ Finset.range (N + 1),
            if n ≡ b [MOD P] then pointTerm b n else 0 := by
    apply Finset.sum_congr rfl
    intro b _hb
    unfold baseSatEventNoHitIndicatorSumUpTo
    change
      (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n ≡ b [MOD P]),
        pointTerm b n) =
      ∑ n ∈ Finset.range (N + 1),
        if n ≡ b [MOD P] then pointTerm b n else 0
    rw [Finset.sum_filter]
  rw [hrewrite]
  rw [Finset.sum_comm]
  unfold reducedBaseSatEventNoHitIndicatorSumUpTo reducedBasePointSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hcop : Nat.Coprime (n % P) P
  · have hmem : n % P ∈ reducedResiduesMod P := by
      exact (mem_reducedResiduesMod_iff P (n % P)).2
        ⟨Nat.mod_lt n hP, hcop⟩
    have hsingle :
        (∑ b ∈ reducedResiduesMod P,
          if n ≡ b [MOD P] then pointTerm b n else 0) =
          pointTerm (n % P) n := by
      have hsum := Finset.sum_eq_single_of_mem
        (s := reducedResiduesMod P)
        (f := fun b => if n ≡ b [MOD P] then pointTerm b n else 0)
        (n % P) hmem (by
          intro b hb hbne
          by_cases hmod : n ≡ b [MOD P]
          · have hbLt : b < P := (mem_reducedResiduesMod_iff P b).1 hb |>.1
            have heq : n % P = b := (modEq_iff_mod_eq_of_lt P n b hbLt).1 hmod
            exact (hbne heq.symm).elim
          · simp [hmod])
      have hself : n ≡ n % P [MOD P] :=
        (modEq_iff_mod_eq_of_lt P n (n % P) (Nat.mod_lt n hP)).2 rfl
      simpa [hself] using hsum
    rw [hsingle]
    by_cases hhit :
        hitEventCount (eventsByBase (n % P))
          (fun event => satEventHit n event) = 0
    · simp [hhit, pointTerm]
      rw [if_pos hcop]
    · simp [hhit, pointTerm]
  · have hzero :
        (∑ b ∈ reducedResiduesMod P,
          if n ≡ b [MOD P] then pointTerm b n else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      by_cases hmod : n ≡ b [MOD P]
      · have hbLt : b < P := (mem_reducedResiduesMod_iff P b).1 hb |>.1
        have hbcop : Nat.Coprime b P := (mem_reducedResiduesMod_iff P b).1 hb |>.2
        have heq : n % P = b := (modEq_iff_mod_eq_of_lt P n b hbLt).1 hmod
        exact (hcop (by simpa [heq] using hbcop)).elim
      · simp [hmod]
    rw [hzero]
    simp [hcop]

theorem reducedBaseSatEventNoHitIndicatorSum_eq_reducedBaseNoHitIndicatorSum_admissibleFor
    (N P : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event) :
    reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase =
      reducedBaseNoHitIndicatorSumUpTo N P
        (fun b => satEventResidualHitRowsFinset (eventsByBase b)) := by
  classical
  unfold reducedBaseSatEventNoHitIndicatorSumUpTo reducedBaseNoHitIndicatorSumUpTo
  apply Finset.sum_congr rfl
  intro n _hn
  have hzero :
      hitEventCount (satEventResidualHitRowsFinset (eventsByBase (n % P)))
          (fun row => n ≡ row.2 [MOD row.1]) = 0 ↔
        hitEventCount (eventsByBase (n % P))
          (fun event => satEventHit n event) = 0 := by
    simpa [satEventResidualHitRowsFinset] using
      (hitEventCount_image_eq_zero_iff (eventsByBase (n % P)) satEventResidualHitRow
        (fun event => satEventHit n event)
        (fun row : Nat × Nat => n ≡ row.2 [MOD row.1])
        (by
          intro event hevent
          have heventAdm : satEventAdmissible P (rhoOf event.e) event := by
            simpa [satEventAdmissibleFor] using hadm (n % P) event hevent
          have hq : 0 < conditionalModulus event.dPlus event.p :=
            Nat.mul_pos heventAdm.2.2.2.2.2.1 heventAdm.1.pos
          exact (satEventHit_iff_modEq_residualHitRow n event hq).symm))
  by_cases hevents :
      hitEventCount (eventsByBase (n % P))
        (fun event => satEventHit n event) = 0
  · have hrows :
        hitEventCount (satEventResidualHitRowsFinset (eventsByBase (n % P)))
          (fun row => n ≡ row.2 [MOD row.1]) = 0 := hzero.mpr hevents
    simp [hevents, hrows]
  · have hrows :
        hitEventCount (satEventResidualHitRowsFinset (eventsByBase (n % P)))
          (fun row => n ≡ row.2 [MOD row.1]) ≠ 0 := by
        intro h
        exact hevents (hzero.mp h)
    simp [hevents, hrows]

theorem exists_reducedBaseRowHit_of_reducedBaseNoHitIndicatorSum_lt
    (N P : Nat) (eventsByBase : Nat → Finset (Nat × Nat)) (B : Int)
    (hbound : reducedBaseNoHitIndicatorSumUpTo N P eventsByBase ≤ B)
    (hlt : B < (reducedBasePointSet N P).card) :
    ∃ n : Nat, n ≤ N ∧ Nat.Coprime (n % P) P ∧
      ∃ row ∈ eventsByBase (n % P), n ≡ row.2 [MOD row.1] := by
  classical
  by_contra hnone
  have hallZero :
      ∀ n ∈ reducedBasePointSet N P,
        hitEventCount (eventsByBase (n % P))
          (fun row => n ≡ row.2 [MOD row.1]) = 0 := by
    intro n hn
    unfold hitEventCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro row hrow hhit
    have hnLe : n ≤ N := by
      have hnRange : n ∈ Finset.range (N + 1) :=
        (Finset.mem_filter.mp hn).1
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hnRange)
    have hnCop : Nat.Coprime (n % P) P :=
      (Finset.mem_filter.mp hn).2
    exact hnone ⟨n, hnLe, hnCop, row, hrow, hhit⟩
  have hsumEq :
      reducedBaseNoHitIndicatorSumUpTo N P eventsByBase =
        (reducedBasePointSet N P).card := by
    unfold reducedBaseNoHitIndicatorSumUpTo
    calc
      (∑ n ∈ reducedBasePointSet N P,
        if hitEventCount (eventsByBase (n % P))
          (fun row => n ≡ row.2 [MOD row.1]) = 0
        then (1 : Int) else 0) =
          ∑ _n ∈ reducedBasePointSet N P, (1 : Int) := by
            apply Finset.sum_congr rfl
            intro n hn
            simp [hallZero n hn]
      _ = ((reducedBasePointSet N P).card : Int) := by
            simp
  have hcardLeB : ((reducedBasePointSet N P).card : Int) ≤ B := by
    simpa [hsumEq] using hbound
  exact (not_lt_of_ge hcardLeB) hlt

theorem exists_positive_reducedBaseRowHit_of_reducedBaseNoHitIndicatorSum_lt
    (N P : Nat) (eventsByBase : Nat → Finset (Nat × Nat)) (B : Int)
    (hpointPos : ∀ n ∈ reducedBasePointSet N P, 0 < n)
    (hbound : reducedBaseNoHitIndicatorSumUpTo N P eventsByBase ≤ B)
    (hlt : B < (reducedBasePointSet N P).card) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      ∃ row ∈ eventsByBase (n % P), n ≡ row.2 [MOD row.1] := by
  rcases exists_reducedBaseRowHit_of_reducedBaseNoHitIndicatorSum_lt
      N P eventsByBase B hbound hlt with
    ⟨n, hnLe, hnCop, hhit⟩
  have hnMem : n ∈ reducedBasePointSet N P := by
    unfold reducedBasePointSet
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hnLe), hnCop⟩
  exact ⟨n, hnLe, hpointPos n hnMem, hnCop, hhit⟩

theorem exists_reducedBaseRowHit_of_reducedBaseNoHitIndicatorSum_rat_lt
    (N P : Nat) (eventsByBase : Nat → Finset (Nat × Nat)) (B : ℚ)
    (hbound : (reducedBaseNoHitIndicatorSumUpTo N P eventsByBase : ℚ) ≤ B)
    (hlt : B < ((reducedBasePointSet N P).card : ℚ)) :
    ∃ n : Nat, n ≤ N ∧ Nat.Coprime (n % P) P ∧
      ∃ row ∈ eventsByBase (n % P), n ≡ row.2 [MOD row.1] := by
  classical
  by_contra hnone
  have hallZero :
      ∀ n ∈ reducedBasePointSet N P,
        hitEventCount (eventsByBase (n % P))
          (fun row => n ≡ row.2 [MOD row.1]) = 0 := by
    intro n hn
    unfold hitEventCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro row hrow hhit
    have hnLe : n ≤ N := by
      have hnRange : n ∈ Finset.range (N + 1) :=
        (Finset.mem_filter.mp hn).1
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hnRange)
    have hnCop : Nat.Coprime (n % P) P :=
      (Finset.mem_filter.mp hn).2
    exact hnone ⟨n, hnLe, hnCop, row, hrow, hhit⟩
  have hsumEqInt :
      reducedBaseNoHitIndicatorSumUpTo N P eventsByBase =
        (reducedBasePointSet N P).card := by
    unfold reducedBaseNoHitIndicatorSumUpTo
    calc
      (∑ n ∈ reducedBasePointSet N P,
        if hitEventCount (eventsByBase (n % P))
          (fun row => n ≡ row.2 [MOD row.1]) = 0
        then (1 : Int) else 0) =
          ∑ _n ∈ reducedBasePointSet N P, (1 : Int) := by
            apply Finset.sum_congr rfl
            intro n hn
            simp [hallZero n hn]
      _ = ((reducedBasePointSet N P).card : Int) := by
            simp
  have hsumEq :
      (reducedBaseNoHitIndicatorSumUpTo N P eventsByBase : ℚ) =
        ((reducedBasePointSet N P).card : ℚ) := by
    exact_mod_cast hsumEqInt
  have hcardLeB : ((reducedBasePointSet N P).card : ℚ) ≤ B := by
    simpa [hsumEq] using hbound
  exact (not_lt_of_ge hcardLeB) hlt

theorem exists_positive_reducedBaseRowHit_of_reducedBaseNoHitIndicatorSum_rat_lt
    (N P : Nat) (eventsByBase : Nat → Finset (Nat × Nat)) (B : ℚ)
    (hpointPos : ∀ n ∈ reducedBasePointSet N P, 0 < n)
    (hbound : (reducedBaseNoHitIndicatorSumUpTo N P eventsByBase : ℚ) ≤ B)
    (hlt : B < ((reducedBasePointSet N P).card : ℚ)) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      ∃ row ∈ eventsByBase (n % P), n ≡ row.2 [MOD row.1] := by
  rcases exists_reducedBaseRowHit_of_reducedBaseNoHitIndicatorSum_rat_lt
      N P eventsByBase B hbound hlt with
    ⟨n, hnLe, hnCop, hhit⟩
  have hnMem : n ∈ reducedBasePointSet N P := by
    unfold reducedBasePointSet
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hnLe), hnCop⟩
  exact ⟨n, hnLe, hpointPos n hnMem, hnCop, hhit⟩

theorem exists_reducedBaseSatEventHit_of_reducedBaseSatEventNoHitIndicatorSum_lt
    (N P : Nat) (eventsByBase : Nat → Finset SatEvent) (B : Int)
    (hbound : reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase ≤ B)
    (hlt : B < (reducedBasePointSet N P).card) :
    ∃ n : Nat, n ≤ N ∧ Nat.Coprime (n % P) P ∧
      ∃ event ∈ eventsByBase (n % P), satEventHit n event := by
  classical
  by_contra hnone
  have hallZero :
      ∀ n ∈ reducedBasePointSet N P,
        hitEventCount (eventsByBase (n % P))
          (fun event => satEventHit n event) = 0 := by
    intro n hn
    unfold hitEventCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro event hevent hhit
    have hnLe : n ≤ N := by
      have hnRange : n ∈ Finset.range (N + 1) :=
        (Finset.mem_filter.mp hn).1
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hnRange)
    have hnCop : Nat.Coprime (n % P) P :=
      (Finset.mem_filter.mp hn).2
    exact hnone ⟨n, hnLe, hnCop, event, hevent, hhit⟩
  have hsumEq :
      reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase =
        (reducedBasePointSet N P).card := by
    unfold reducedBaseSatEventNoHitIndicatorSumUpTo
    calc
      (∑ n ∈ reducedBasePointSet N P,
        if hitEventCount (eventsByBase (n % P))
          (fun event => satEventHit n event) = 0
        then (1 : Int) else 0) =
          ∑ _n ∈ reducedBasePointSet N P, (1 : Int) := by
            apply Finset.sum_congr rfl
            intro n hn
            simp [hallZero n hn]
      _ = ((reducedBasePointSet N P).card : Int) := by
            simp
  have hcardLeB : ((reducedBasePointSet N P).card : Int) ≤ B := by
    simpa [hsumEq] using hbound
  exact (not_lt_of_ge hcardLeB) hlt

theorem exists_positive_reducedBaseSatEventHit_of_reducedBaseSatEventNoHitIndicatorSum_lt
    (N P : Nat) (eventsByBase : Nat → Finset SatEvent) (B : Int)
    (hpointPos : ∀ n ∈ reducedBasePointSet N P, 0 < n)
    (hbound : reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase ≤ B)
    (hlt : B < (reducedBasePointSet N P).card) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      ∃ event ∈ eventsByBase (n % P), satEventHit n event := by
  rcases exists_reducedBaseSatEventHit_of_reducedBaseSatEventNoHitIndicatorSum_lt
      N P eventsByBase B hbound hlt with
    ⟨n, hnLe, hnCop, hhit⟩
  have hnMem : n ∈ reducedBasePointSet N P := by
    unfold reducedBasePointSet
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hnLe), hnCop⟩
  exact ⟨n, hnLe, hpointPos n hnMem, hnCop, hhit⟩

theorem exists_reducedBaseSatEventHit_of_reducedBaseSatEventNoHitIndicatorSum_rat_lt
    (N P : Nat) (eventsByBase : Nat → Finset SatEvent) (B : ℚ)
    (hbound : (reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase : ℚ) ≤ B)
    (hlt : B < ((reducedBasePointSet N P).card : ℚ)) :
    ∃ n : Nat, n ≤ N ∧ Nat.Coprime (n % P) P ∧
      ∃ event ∈ eventsByBase (n % P), satEventHit n event := by
  classical
  by_contra hnone
  have hallZero :
      ∀ n ∈ reducedBasePointSet N P,
        hitEventCount (eventsByBase (n % P))
          (fun event => satEventHit n event) = 0 := by
    intro n hn
    unfold hitEventCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro event hevent hhit
    have hnLe : n ≤ N := by
      have hnRange : n ∈ Finset.range (N + 1) :=
        (Finset.mem_filter.mp hn).1
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hnRange)
    have hnCop : Nat.Coprime (n % P) P :=
      (Finset.mem_filter.mp hn).2
    exact hnone ⟨n, hnLe, hnCop, event, hevent, hhit⟩
  have hsumEqInt :
      reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase =
        (reducedBasePointSet N P).card := by
    unfold reducedBaseSatEventNoHitIndicatorSumUpTo
    calc
      (∑ n ∈ reducedBasePointSet N P,
        if hitEventCount (eventsByBase (n % P))
          (fun event => satEventHit n event) = 0
        then (1 : Int) else 0) =
          ∑ _n ∈ reducedBasePointSet N P, (1 : Int) := by
            apply Finset.sum_congr rfl
            intro n hn
            simp [hallZero n hn]
      _ = ((reducedBasePointSet N P).card : Int) := by
            simp
  have hsumEq :
      (reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase : ℚ) =
        ((reducedBasePointSet N P).card : ℚ) := by
    exact_mod_cast hsumEqInt
  have hcardLeB : ((reducedBasePointSet N P).card : ℚ) ≤ B := by
    simpa [hsumEq] using hbound
  exact (not_lt_of_ge hcardLeB) hlt

theorem exists_positive_reducedBaseSatEventHit_of_reducedBaseSatEventNoHitIndicatorSum_rat_lt
    (N P : Nat) (eventsByBase : Nat → Finset SatEvent) (B : ℚ)
    (hpointPos : ∀ n ∈ reducedBasePointSet N P, 0 < n)
    (hbound : (reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase : ℚ) ≤ B)
    (hlt : B < ((reducedBasePointSet N P).card : ℚ)) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      ∃ event ∈ eventsByBase (n % P), satEventHit n event := by
  rcases exists_reducedBaseSatEventHit_of_reducedBaseSatEventNoHitIndicatorSum_rat_lt
      N P eventsByBase B hbound hlt with
    ⟨n, hnLe, hnCop, hhit⟩
  have hnMem : n ∈ reducedBasePointSet N P := by
    unfold reducedBasePointSet
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hnLe), hnCop⟩
  exact ⟨n, hnLe, hpointPos n hnMem, hnCop, hhit⟩

theorem exists_reducedBaseSatEventHit_of_reducedBaseRowNoHitIndicatorSum_lt_admissibleFor
    (N P : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Int)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hbound :
      reducedBaseNoHitIndicatorSumUpTo N P
        (fun b => satEventResidualHitRowsFinset (eventsByBase b)) ≤ B)
    (hlt : B < (reducedBasePointSet N P).card) :
    ∃ n : Nat, n ≤ N ∧ Nat.Coprime (n % P) P ∧
      ∃ event ∈ eventsByBase (n % P), satEventHit n event := by
  apply exists_reducedBaseSatEventHit_of_reducedBaseSatEventNoHitIndicatorSum_lt
    N P eventsByBase B
  · rwa [reducedBaseSatEventNoHitIndicatorSum_eq_reducedBaseNoHitIndicatorSum_admissibleFor
      N P rhoOf eventsByBase hadm]
  · exact hlt

theorem exists_positive_reducedBaseSatEventHit_of_reducedBaseRowNoHitIndicatorSum_lt_admissibleFor
    (N P : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Int)
    (hpointPos : ∀ n ∈ reducedBasePointSet N P, 0 < n)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hbound :
      reducedBaseNoHitIndicatorSumUpTo N P
        (fun b => satEventResidualHitRowsFinset (eventsByBase b)) ≤ B)
    (hlt : B < (reducedBasePointSet N P).card) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      ∃ event ∈ eventsByBase (n % P), satEventHit n event := by
  rcases exists_reducedBaseSatEventHit_of_reducedBaseRowNoHitIndicatorSum_lt_admissibleFor
      N P rhoOf eventsByBase B hadm hbound hlt with
    ⟨n, hnLe, hnCop, hhit⟩
  have hnMem : n ∈ reducedBasePointSet N P := by
    unfold reducedBasePointSet
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hnLe), hnCop⟩
  exact ⟨n, hnLe, hpointPos n hnMem, hnCop, hhit⟩

theorem exists_reducedBaseSatEventHit_of_reducedBaseRowNoHitIndicatorSum_rat_lt_admissibleFor
    (N P : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : ℚ)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hbound :
      (reducedBaseNoHitIndicatorSumUpTo N P
        (fun b => satEventResidualHitRowsFinset (eventsByBase b)) : ℚ) ≤ B)
    (hlt : B < ((reducedBasePointSet N P).card : ℚ)) :
    ∃ n : Nat, n ≤ N ∧ Nat.Coprime (n % P) P ∧
      ∃ event ∈ eventsByBase (n % P), satEventHit n event := by
  apply exists_reducedBaseSatEventHit_of_reducedBaseSatEventNoHitIndicatorSum_rat_lt
    N P eventsByBase B
  · rwa [reducedBaseSatEventNoHitIndicatorSum_eq_reducedBaseNoHitIndicatorSum_admissibleFor
      N P rhoOf eventsByBase hadm]
  · exact hlt

theorem exists_positive_reducedBaseSatEventHit_of_reducedBaseRowNoHitIndicatorSum_rat_lt_admissibleFor
    (N P : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : ℚ)
    (hpointPos : ∀ n ∈ reducedBasePointSet N P, 0 < n)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hbound :
      (reducedBaseNoHitIndicatorSumUpTo N P
        (fun b => satEventResidualHitRowsFinset (eventsByBase b)) : ℚ) ≤ B)
    (hlt : B < ((reducedBasePointSet N P).card : ℚ)) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      ∃ event ∈ eventsByBase (n % P), satEventHit n event := by
  rcases exists_reducedBaseSatEventHit_of_reducedBaseRowNoHitIndicatorSum_rat_lt_admissibleFor
      N P rhoOf eventsByBase B hadm hbound hlt with
    ⟨n, hnLe, hnCop, hhit⟩
  have hnMem : n ∈ reducedBasePointSet N P := by
    unfold reducedBasePointSet
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hnLe), hnCop⟩
  exact ⟨n, hnLe, hpointPos n hnMem, hnCop, hhit⟩

theorem reducedBaseNoHitIndicatorSum_rat_le_of_base_bounds
    (N P : Nat) (eventsByBase : Nat → Finset (Nat × Nat)) (B : Nat → ℚ)
    (hP : 0 < P)
    (hbase : ∀ b ∈ reducedResiduesMod P,
      (baseRowNoHitIndicatorSumUpTo N P b (eventsByBase b) : ℚ) ≤ B b) :
    (reducedBaseNoHitIndicatorSumUpTo N P eventsByBase : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P, B b := by
  have hsumEq := reducedBaseNoHitIndicatorSum_eq_sum_base N P eventsByBase hP
  calc
    (reducedBaseNoHitIndicatorSumUpTo N P eventsByBase : ℚ) =
        ((∑ b ∈ reducedResiduesMod P,
          baseRowNoHitIndicatorSumUpTo N P b (eventsByBase b)) : Int) := by
          exact_mod_cast hsumEq.symm
    _ = ∑ b ∈ reducedResiduesMod P,
        (baseRowNoHitIndicatorSumUpTo N P b (eventsByBase b) : ℚ) := by
          simp
    _ ≤ ∑ b ∈ reducedResiduesMod P, B b := by
          exact Finset.sum_le_sum hbase

theorem reducedBaseSatEventNoHitIndicatorSum_rat_le_of_base_bounds
    (N P : Nat) (eventsByBase : Nat → Finset SatEvent) (B : Nat → ℚ)
    (hP : 0 < P)
    (hbase : ∀ b ∈ reducedResiduesMod P,
      (baseSatEventNoHitIndicatorSumUpTo N P b (eventsByBase b) : ℚ) ≤ B b) :
    (reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P, B b := by
  have hsumEq := reducedBaseSatEventNoHitIndicatorSum_eq_sum_base
    N P eventsByBase hP
  calc
    (reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase : ℚ) =
        ((∑ b ∈ reducedResiduesMod P,
          baseSatEventNoHitIndicatorSumUpTo N P b (eventsByBase b)) : Int) := by
          exact_mod_cast hsumEq.symm
    _ = ∑ b ∈ reducedResiduesMod P,
        (baseSatEventNoHitIndicatorSumUpTo N P b (eventsByBase b) : ℚ) := by
          simp
    _ ≤ ∑ b ∈ reducedResiduesMod P, B b := by
          exact Finset.sum_le_sum hbase

theorem reducedBaseNoHitIndicatorSum_rat_le_of_base_even_rank_bounds
    (N P R : Nat) (eventsByBase : Nat → Finset (Nat × Nat))
    (B : Nat → Nat → ℚ)
    (hP : 0 < P)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1), Even r →
        ((∑ s ∈ (eventsByBase b).powersetCard r,
            baseRowEventCommonHitCountUpTo N P b s : Nat) : ℚ) ≤ B b r)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1), Odd r → 0 ≤ B b r) :
    (reducedBaseNoHitIndicatorSumUpTo N P eventsByBase : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), B b r := by
  apply reducedBaseNoHitIndicatorSum_rat_le_of_base_bounds
    N P eventsByBase
    (fun b => ∑ r ∈ Finset.range (2 * R + 1), B b r) hP
  intro b hb
  exact baseFiniteIntervalTransfer_rat_of_even_rank_bounds
    N P b R (eventsByBase b) (B b) (heven b hb) (hodd b hb)

theorem reducedBaseSatEventNoHitIndicatorSum_rat_le_of_base_even_rank_bounds
    (N P R : Nat) (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hP : 0 < P)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1), Even r →
        ((∑ s ∈ (eventsByBase b).powersetCard r,
            baseSatEventCommonHitCountUpTo N P b s : Nat) : ℚ) ≤ B b r)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1), Odd r → 0 ≤ B b r) :
    (reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), B b r := by
  apply reducedBaseSatEventNoHitIndicatorSum_rat_le_of_base_bounds
    N P eventsByBase
    (fun b => ∑ r ∈ Finset.range (2 * R + 1), B b r) hP
  intro b hb
  exact baseSatEventFiniteIntervalTransfer_rat_of_even_rank_bounds
    N P b R (eventsByBase b) (B b) (heven b hb) (hodd b hb)

theorem reducedBaseSatEventNoHitIndicatorSum_rat_le_of_base_signed_rank_bounds
    (N P R : Nat) (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hP : 0 < P)
    (hrank : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ r) *
          ((∑ s ∈ (eventsByBase b).powersetCard r,
              baseSatEventCommonHitCountUpTo N P b s : Nat) : Int) : ℚ) ≤
            B b r) :
    (reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), B b r := by
  apply reducedBaseSatEventNoHitIndicatorSum_rat_le_of_base_bounds
    N P eventsByBase
    (fun b => ∑ r ∈ Finset.range (2 * R + 1), B b r) hP
  intro b hb
  exact baseSatEventFiniteIntervalTransfer_rat_of_rank_signed_bounds
    N P b R (eventsByBase b) (B b) (hrank b hb)

theorem reducedBaseNoHitIndicatorSum_rat_le_of_base_even_upper_odd_lower_rank_bounds
    (N P R : Nat) (eventsByBase : Nat → Finset (Nat × Nat))
    (upper lower : Nat → Nat → ℚ)
    (hP : 0 < P)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1), Even r →
        ((∑ s ∈ (eventsByBase b).powersetCard r,
            baseRowEventCommonHitCountUpTo N P b s : Nat) : ℚ) ≤ upper b r)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1), Odd r →
        lower b r ≤
          ((∑ s ∈ (eventsByBase b).powersetCard r,
            baseRowEventCommonHitCountUpTo N P b s : Nat) : ℚ)) :
    (reducedBaseNoHitIndicatorSumUpTo N P eventsByBase : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1),
          if Even r then upper b r else - lower b r := by
  apply reducedBaseNoHitIndicatorSum_rat_le_of_base_bounds
    N P eventsByBase
    (fun b =>
      ∑ r ∈ Finset.range (2 * R + 1),
        if Even r then upper b r else - lower b r) hP
  intro b hb
  exact baseFiniteIntervalTransfer_rat_of_even_upper_odd_lower_rank_bounds
    N P b R (eventsByBase b) (upper b) (lower b)
    (heven b hb) (hodd b hb)

theorem reducedBaseSatEventNoHitIndicatorSum_rat_le_of_base_even_upper_odd_lower_rank_bounds
    (N P R : Nat) (eventsByBase : Nat → Finset SatEvent)
    (upper lower : Nat → Nat → ℚ)
    (hP : 0 < P)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1), Even r →
        ((∑ s ∈ (eventsByBase b).powersetCard r,
            baseSatEventCommonHitCountUpTo N P b s : Nat) : ℚ) ≤ upper b r)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1), Odd r →
        lower b r ≤
          ((∑ s ∈ (eventsByBase b).powersetCard r,
            baseSatEventCommonHitCountUpTo N P b s : Nat) : ℚ)) :
    (reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1),
          if Even r then upper b r else - lower b r := by
  apply reducedBaseSatEventNoHitIndicatorSum_rat_le_of_base_bounds
    N P eventsByBase
    (fun b =>
      ∑ r ∈ Finset.range (2 * R + 1),
        if Even r then upper b r else - lower b r) hP
  intro b hb
  exact baseSatEventFiniteIntervalTransfer_rat_of_even_upper_odd_lower_rank_bounds
    N P b R (eventsByBase b) (upper b) (lower b)
    (heven b hb) (hodd b hb)

theorem baseSatEventFiniteIntervalTransfer_rat_of_commonHitSum_eq_signed_budget
    (N Pz b R : Nat) (events : Finset SatEvent)
    (C : Nat → Nat) (B : Nat → ℚ)
    (hC : ∀ r ∈ Finset.range (2 * R + 1),
      (∑ s ∈ events.powersetCard r,
        baseSatEventCommonHitCountUpTo N Pz b s) = C r)
    (hB : ∀ r ∈ Finset.range (2 * R + 1),
      (((-1 : Int) ^ r) * (C r : Int) : ℚ) ≤ B r) :
    (baseSatEventNoHitIndicatorSumUpTo N Pz b events : ℚ) ≤
      ∑ r ∈ Finset.range (2 * R + 1), B r :=
  baseSatEventFiniteIntervalTransfer_rat_of_rank_signed_bounds
    N Pz b R events B (by
      intro r hr
      rw [hC r hr]
      exact hB r hr)

theorem reducedBaseSatEventNoHitIndicatorSum_rat_le_of_base_commonHitSum_eq_signed_budget
    (N P R : Nat) (eventsByBase : Nat → Finset SatEvent)
    (C : Nat → Nat → Nat) (B : Nat → Nat → ℚ)
    (hP : 0 < P)
    (hC : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1),
        (∑ s ∈ (eventsByBase b).powersetCard r,
          baseSatEventCommonHitCountUpTo N P b s) = C b r)
    (hB : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ r) * (C b r : Int) : ℚ) ≤ B b r) :
    (reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), B b r := by
  apply reducedBaseSatEventNoHitIndicatorSum_rat_le_of_base_bounds
    N P eventsByBase
    (fun b => ∑ r ∈ Finset.range (2 * R + 1), B b r) hP
  intro b hb
  exact
    baseSatEventFiniteIntervalTransfer_rat_of_commonHitSum_eq_signed_budget
      N P b R (eventsByBase b) (C b) (B b) (hC b hb) (hB b hb)

theorem reducedBaseSatEventNoHitIndicatorSum_rat_le_of_base_compatible_lcm_bound_admissibleFor
    (N P R : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent)
    (hP : 0 < P)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hpCop : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime P event.p) :
    (reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1),
          ((∑ s ∈ baseRowCompatibleSubsetsOfCard P b
              (satEventResidualHitRowsFinset (eventsByBase b)) r,
            (N / (P * congruenceLcm s.toList) + 1) : Nat) : ℚ) := by
  apply reducedBaseSatEventNoHitIndicatorSum_rat_le_of_base_bounds
    N P eventsByBase
    (fun b =>
      ∑ r ∈ Finset.range (2 * R + 1),
        ((∑ s ∈ baseRowCompatibleSubsetsOfCard P b
            (satEventResidualHitRowsFinset (eventsByBase b)) r,
          (N / (P * congruenceLcm s.toList) + 1) : Nat) : ℚ))
    hP
  intro b _hb
  have hbase :=
    baseSatEventFiniteIntervalTransfer_le_compatible_lcm_bound_admissibleFor
      N P b R rhoOf (eventsByBase b) hP
      (fun event hevent => hadm b event hevent)
      (fun event hevent => hpCop b event hevent)
  have hbaseRat :
      (baseSatEventNoHitIndicatorSumUpTo N P b (eventsByBase b) : ℚ) ≤
        ((∑ r ∈ Finset.range (2 * R + 1),
          ((∑ s ∈ baseRowCompatibleSubsetsOfCard P b
              (satEventResidualHitRowsFinset (eventsByBase b)) r,
            (N / (P * congruenceLcm s.toList) + 1) : Nat) : Int)) : ℚ) := by
    exact_mod_cast hbase
  simpa using hbaseRat

theorem reducedBaseSatEventNoHitIndicatorSum_rat_le_of_base_compatible_lcm_bound_largePrime_admissibleFor
    (N P R : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent)
    (hP : 0 < P)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hlargeBase : ∀ b event, event ∈ eventsByBase b →
      P < event.p) :
    (reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1),
          ((∑ s ∈ baseRowCompatibleSubsetsOfCard P b
              (satEventResidualHitRowsFinset (eventsByBase b)) r,
            (N / (P * congruenceLcm s.toList) + 1) : Nat) : ℚ) := by
  exact
    reducedBaseSatEventNoHitIndicatorSum_rat_le_of_base_compatible_lcm_bound_admissibleFor
      N P R rhoOf eventsByBase hP hadm
      (fun b event hevent =>
        satEvent_base_coprime_of_admissibleFor_largePrime
          P rhoOf event hP (hadm b event hevent) (hlargeBase b event hevent))

/- Linear Type II certificate.  If (4deA-1)B = Ap+d, the displayed
   denominators give a cross-multiplied Erdős--Straus identity. -/

def typeIIEquation (p d e A B : Nat) : Prop :=
  (4 * d * e * A - 1) * B = A * p + d

def typeIIX (p d e A : Nat) : Nat :=
  p * d * e * A

def typeIIY (p e A B : Nat) : Nat :=
  p * e * A * B

def typeIIZ (d e B : Nat) : Nat :=
  d * e * B

def typeIIESBool (p d e A B : Nat) : Bool :=
  esCrossBool p (typeIIX p d e A) (typeIIY p e A B) (typeIIZ d e B)

example : typeIIEquation 2521 4 1 3 161 := by
  unfold typeIIEquation
  native_decide

example : typeIIX 2521 4 1 3 = 30252 := by
  native_decide

example : typeIIY 2521 1 3 161 = 1217643 := by
  native_decide

example : typeIIZ 4 1 161 = 644 := by
  native_decide

example : typeIIESBool 2521 4 1 3 161 = true := by
  native_decide

/- Divisor-fan certificate predicates and the explicit denominator formulas
   used in the manuscript. -/

def qOf (a : Nat) : Nat :=
  4 * a - 1

def interiorDivisor (a h : Nat) : Prop :=
  h ∣ a ^ 2 ∧ h ≠ 1 ∧ h ≠ a ∧ h ≠ a ^ 2

def fanCongruence (n a h : Nat) : Prop :=
  qOf a ∣ n + 4 * h

def fanWitness (n a h : Nat) : Prop :=
  a > 0 ∧ h > 0 ∧ interiorDivisor a h ∧ fanCongruence n a h

def fanWitnessBool (n a h : Nat) : Bool :=
  decide (a > 0) &&
  decide (h > 0) &&
  decide (h ∣ a ^ 2) &&
  (h != 1) &&
  (h != a) &&
  (h != a ^ 2) &&
  decide (qOf a ∣ n + 4 * h)

theorem fanWitnessBool_eq_true (n a h : Nat) :
    fanWitnessBool n a h = true ↔ fanWitness n a h := by
  simp only [fanWitnessBool, fanWitness, interiorDivisor, fanCongruence,
    Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne]
  tauto

def boundaryDivisor (a h : Nat) : Prop :=
  h = 1 ∨ h = a ∨ h = a ^ 2

def boundaryDivisorBool (a h : Nat) : Bool :=
  (h == 1) || (h == a) || (h == a ^ 2)

theorem boundaryDivisorBool_eq_true (a h : Nat) :
    boundaryDivisorBool a h = true ↔ boundaryDivisor a h := by
  unfold boundaryDivisorBool boundaryDivisor
  simp only [beq_iff_eq, Bool.or_eq_true]
  constructor
  · intro hb
    rcases hb with hleft | hsquare
    · rcases hleft with hone | ha
      · exact Or.inl hone
      · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr hsquare)
  · intro hb
    rcases hb with hone | ha | hsquare
    · exact Or.inl (Or.inl hone)
    · exact Or.inl (Or.inr ha)
    · exact Or.inr hsquare

def fanX (n a : Nat) : Nat :=
  a * n

def fanY (n a h : Nat) : Nat :=
  (a * n + h) / qOf a

def fanZ (n a h : Nat) : Nat :=
  (a * n + (a ^ 2 * n ^ 2) / h) / qOf a

def fanESBool (n a h : Nat) : Bool :=
  esCrossBool n (fanX n a) (fanY n a h) (fanZ n a h)

example : qOf 12 = 47 := by
  native_decide

example : fanWitnessBool 2521 12 16 = true := by
  native_decide

example : fanY 2521 12 16 = 644 := by
  native_decide

example : fanZ 2521 12 16 = 1217643 := by
  native_decide

example : fanESBool 2521 12 16 = true := by
  native_decide

/- Fixed-numerator certificate examples for m/n. -/

def fixedQ (m a : Nat) : Nat :=
  m * a - 1

def fixedFanX (n a : Nat) : Nat :=
  a * n

def fixedFanY (m n a e : Nat) : Nat :=
  (a * n + e) / fixedQ m a

def fixedFanZ (m n a e : Nat) : Nat :=
  (a * n + (a ^ 2 * n ^ 2) / e) / fixedQ m a

def fixedCross (m n x y z : Nat) : Prop :=
  n * (y * z + x * z + x * y) = m * x * y * z

def fixedCrossBool (m n x y z : Nat) : Bool :=
  n * (y * z + x * z + x * y) == m * x * y * z

/-!
## Universal rational certificate algebra

The finite checks below verify concrete witnesses.  The next lemmas formalize the
algebraic certificate identities used in the manuscript over `ℚ`, where unit
fractions and denominator clearing are natural.  Positivity and integrality of
the displayed integer formulas remain separate arithmetic obligations.
-/

def typeIINumeratorEquationQ (p d e A B : ℚ) : Prop :=
  B + d + A * p = 4 * d * e * A * B

theorem typeII_rational_identity
    (p d e A B : ℚ)
    (h : typeIINumeratorEquationQ p d e A B)
    (hp : p ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) :
    4 / p = 1 / (p * d * e * A) + 1 / (p * e * A * B) + 1 / (d * e * B) := by
  unfold typeIINumeratorEquationQ at h
  field_simp [hp, hd, he, hA, hB]
  ring_nf at *
  have hmul := congrArg (fun t : ℚ => p ^ 2 * d * e ^ 2 * A * B * t) h
  ring_nf at hmul
  exact hmul.symm

theorem typeII_numerator_equationQ_of_nat
    (p d e A B : Nat)
    (hd : 0 < d) (he : 0 < e) (hA : 0 < A)
    (h : typeIIEquation p d e A B) :
    typeIINumeratorEquationQ (p : ℚ) (d : ℚ) (e : ℚ) (A : ℚ) (B : ℚ) := by
  unfold typeIIEquation at h
  have hdea : 0 < d * e * A := Nat.mul_pos (Nat.mul_pos hd he) hA
  have hprod : 1 ≤ 4 * d * e * A := by
    have hpos : 0 < 4 * (d * e * A) := Nat.mul_pos (by norm_num) hdea
    nlinarith
  have hqNat : (4 * d * e * A - 1) + 1 = 4 * d * e * A := by
    omega
  have hqQ :
      ((4 * d * e * A - 1 : Nat) : ℚ) =
        4 * (d : ℚ) * (e : ℚ) * (A : ℚ) - 1 := by
    have hcast :
        ((4 * d * e * A - 1 : Nat) : ℚ) + 1 =
          4 * (d : ℚ) * (e : ℚ) * (A : ℚ) := by
      exact_mod_cast hqNat
    linarith
  have hQ :
      ((4 * d * e * A - 1 : Nat) : ℚ) * (B : ℚ) =
        (A : ℚ) * (p : ℚ) + (d : ℚ) := by
    exact_mod_cast h
  unfold typeIINumeratorEquationQ
  rw [hqQ] at hQ
  ring_nf at hQ ⊢
  nlinarith [hQ]

theorem typeII_nat_certificate
    (p d e A B : Nat)
    (hp : 0 < p) (hd : 0 < d) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (h : typeIIEquation p d e A B) :
    0 < typeIIX p d e A ∧
    0 < typeIIY p e A B ∧
    0 < typeIIZ d e B ∧
    (4 : ℚ) / (p : ℚ) =
      1 / (typeIIX p d e A : ℚ) +
      1 / (typeIIY p e A B : ℚ) +
      1 / (typeIIZ d e B : ℚ) := by
  have hnum :
      typeIINumeratorEquationQ (p : ℚ) (d : ℚ) (e : ℚ) (A : ℚ) (B : ℚ) :=
    typeII_numerator_equationQ_of_nat p d e A B hd he hA h
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hp)
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have heq : (e : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt he)
  have hAq : (A : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hA)
  have hBq : (B : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hB)
  have hident := typeII_rational_identity
    (p := (p : ℚ)) (d := (d : ℚ)) (e := (e : ℚ)) (A := (A : ℚ)) (B := (B : ℚ))
    hnum hpq hdq heq hAq hBq
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold typeIIX
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp hd) he) hA
  · unfold typeIIY
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp he) hA) hB
  · unfold typeIIZ
    exact Nat.mul_pos (Nat.mul_pos hd he) hB
  · dsimp [typeIIX, typeIIY, typeIIZ] at hident ⊢
    norm_num at hident ⊢
    ring_nf at hident ⊢
    exact hident

theorem typeII_nat_unit_fraction_identity
    (p d e A B : Nat)
    (hp : 0 < p) (hd : 0 < d) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (h : typeIIEquation p d e A B) :
    (4 : ℚ) / (p : ℚ) =
      1 / (typeIIX p d e A : ℚ) +
      1 / (typeIIY p e A B : ℚ) +
      1 / (typeIIZ d e B : ℚ) :=
  (typeII_nat_certificate p d e A B hp hd he hA hB h).2.2.2

theorem typeII_esCross_of_equation
    (p d e A B : Nat)
    (hd : 0 < d) (he : 0 < e) (hA : 0 < A)
    (h : typeIIEquation p d e A B) :
    esCross p (typeIIX p d e A) (typeIIY p e A B) (typeIIZ d e B) := by
  unfold typeIIEquation at h
  have hdea : 0 < d * e * A := Nat.mul_pos (Nat.mul_pos hd he) hA
  have hprod : 1 ≤ 4 * d * e * A := by
    have hpos : 0 < 4 * (d * e * A) := Nat.mul_pos (by norm_num) hdea
    nlinarith
  have hqNat : (4 * d * e * A - 1) + 1 = 4 * d * e * A := by
    omega
  have hqInt :
      ((4 * d * e * A - 1 : Nat) : ℤ) =
        4 * (d : ℤ) * (e : ℤ) * (A : ℤ) - 1 := by
    have hcast :
        ((4 * d * e * A - 1 : Nat) : ℤ) + 1 =
          4 * (d : ℤ) * (e : ℤ) * (A : ℤ) := by
      exact_mod_cast hqNat
    linarith
  have hInt :
      ((4 * d * e * A - 1 : Nat) : ℤ) * (B : ℤ) =
        (A : ℤ) * (p : ℤ) + (d : ℤ) := by
    exact_mod_cast h
  rw [hqInt] at hInt
  have hsum :
      (B : ℤ) + (d : ℤ) + (A : ℤ) * (p : ℤ) =
        4 * (d : ℤ) * (e : ℤ) * (A : ℤ) * (B : ℤ) := by
    linarith
  have hCrossInt :
      (p : ℤ) *
          (((typeIIY p e A B : Nat) : ℤ) * ((typeIIZ d e B : Nat) : ℤ) +
            ((typeIIX p d e A : Nat) : ℤ) * ((typeIIZ d e B : Nat) : ℤ) +
            ((typeIIX p d e A : Nat) : ℤ) * ((typeIIY p e A B : Nat) : ℤ)) =
        4 * ((typeIIX p d e A : Nat) : ℤ) * ((typeIIY p e A B : Nat) : ℤ) *
          ((typeIIZ d e B : Nat) : ℤ) := by
    unfold typeIIX typeIIY typeIIZ
    norm_num [Nat.cast_mul]
    calc
      (p : ℤ) *
          (((p : ℤ) * (e : ℤ) * (A : ℤ) * (B : ℤ)) *
              ((d : ℤ) * (e : ℤ) * (B : ℤ)) +
            ((p : ℤ) * (d : ℤ) * (e : ℤ) * (A : ℤ)) *
              ((d : ℤ) * (e : ℤ) * (B : ℤ)) +
            ((p : ℤ) * (d : ℤ) * (e : ℤ) * (A : ℤ)) *
              ((p : ℤ) * (e : ℤ) * (A : ℤ) * (B : ℤ))) =
          (p : ℤ) ^ 2 * (d : ℤ) * (e : ℤ) ^ 2 * (A : ℤ) * (B : ℤ) *
            ((B : ℤ) + (d : ℤ) + (A : ℤ) * (p : ℤ)) := by
        ring
      _ =
          (p : ℤ) ^ 2 * (d : ℤ) * (e : ℤ) ^ 2 * (A : ℤ) * (B : ℤ) *
            (4 * (d : ℤ) * (e : ℤ) * (A : ℤ) * (B : ℤ)) := by
        rw [hsum]
      _ =
          4 * ((p : ℤ) * (d : ℤ) * (e : ℤ) * (A : ℤ)) *
            ((p : ℤ) * (e : ℤ) * (A : ℤ) * (B : ℤ)) *
            ((d : ℤ) * (e : ℤ) * (B : ℤ)) := by
        ring
  unfold esCross
  exact_mod_cast hCrossInt

theorem typeII_B_pos_of_equation
    (p d e A B : Nat) (hp : 0 < p) (hd : 0 < d) (hA : 0 < A)
    (h : typeIIEquation p d e A B) : 0 < B := by
  by_contra hnot
  have hB0 : B = 0 := Nat.eq_zero_of_not_pos hnot
  unfold typeIIEquation at h
  have hrhs : 0 < A * p + d := by
    have hAp : 0 < A * p := Nat.mul_pos hA hp
    omega
  rw [hB0, mul_zero] at h
  omega

theorem typeII_positive_unit_fractions
    (p d e A B : Nat)
    (hp : 0 < p) (hd : 0 < d) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (h : typeIIEquation p d e A B) :
    ∃ x y z : Nat,
      0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (p : ℚ) =
        1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  rcases typeII_nat_certificate p d e A B hp hd he hA hB h with
    ⟨hx, hy, hz, hident⟩
  exact ⟨typeIIX p d e A, typeIIY p e A B, typeIIZ d e B, hx, hy, hz, hident⟩

theorem completeFan_decomposition_of_dvd_square
    (a h : Nat) (ha : 0 < a) (hh : 0 < h) (hdvd : h ∣ a ^ 2) :
    ∃ d e A : Nat,
      0 < d ∧ 0 < e ∧ 0 < A ∧
      a = d * e * A ∧ h = d ^ 2 * e := by
  let g := Nat.gcd h a
  let d := h / g
  let e := (g * g) / h
  let A := a / g
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left a hh
  have hgDvdH : g ∣ h := Nat.gcd_dvd_left h a
  have hgDvdA : g ∣ a := Nat.gcd_dvd_right h a
  have hEqGD : g * d = h := by
    dsimp [d]
    exact Nat.mul_div_cancel' hgDvdH
  have aEqGA : g * A = a := by
    dsimp [A]
    exact Nat.mul_div_cancel' hgDvdA
  have hDvdAA : h ∣ a * a := by
    simpa [pow_two] using hdvd
  have hDvdG2 : h ∣ g * g := by
    exact (Nat.dvd_gcd_mul_gcd_iff_dvd_mul (x := h) (n := a) (m := a)).2 hDvdAA
  have g2EqHE : g * g = h * e := by
    dsimp [e]
    exact (Nat.mul_div_cancel' hDvdG2).symm
  have gEqDE : g = d * e := by
    have hmul : g * g = g * (d * e) := by
      rw [g2EqHE, ← hEqGD]
      ring
    exact Nat.eq_of_mul_eq_mul_left hgpos hmul
  have hdpos : 0 < d := by
    by_contra hnot
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hd0, mul_zero] at hEqGD
    omega
  have hepos : 0 < e := by
    by_contra hnot
    have he0 : e = 0 := Nat.eq_zero_of_not_pos hnot
    rw [he0, mul_zero] at gEqDE
    omega
  have hApos : 0 < A := by
    by_contra hnot
    have hA0 : A = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hA0, mul_zero] at aEqGA
    omega
  have hAeq : a = d * e * A := by
    calc
      a = g * A := aEqGA.symm
      _ = (d * e) * A := by rw [gEqDE]
      _ = d * e * A := by ring
  have hheq : h = d ^ 2 * e := by
    calc
      h = g * d := hEqGD.symm
      _ = (d * e) * d := by rw [gEqDE]
      _ = d ^ 2 * e := by ring
  exact ⟨d, e, A, hdpos, hepos, hApos, hAeq, hheq⟩

theorem typeIIEquation_of_completeFan_decomposition
    (p d e A : Nat) (hd : 0 < d) (he : 0 < e) (hA : 0 < A)
    (hcong : qOf (d * e * A) ∣ p + 4 * (d ^ 2 * e)) :
    ∃ B : Nat, typeIIEquation p d e A B := by
  have hcongQ : (4 * d * e * A - 1) ∣ p + 4 * (d ^ 2 * e) := by
    simpa [qOf, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcong
  have hdea : 0 < d * e * A := Nat.mul_pos (Nat.mul_pos hd he) hA
  have hprod : 1 ≤ 4 * d * e * A := by
    have hpos : 0 < 4 * (d * e * A) := Nat.mul_pos (by norm_num) hdea
    nlinarith
  have hqNat : (4 * d * e * A - 1) + 1 = 4 * d * e * A := by
    omega
  have hqInt :
      ((4 * d * e * A - 1 : Nat) : ℤ) =
        4 * (d : ℤ) * (e : ℤ) * (A : ℤ) - 1 := by
    have hcast :
        ((4 * d * e * A - 1 : Nat) : ℤ) + 1 =
          4 * (d : ℤ) * (e : ℤ) * (A : ℤ) := by
      exact_mod_cast hqNat
    linarith
  have hDvdNat : (4 * d * e * A - 1) ∣ A * p + d := by
    rw [← Int.ofNat_dvd]
    rw [← Int.ofNat_dvd] at hcongQ
    rcases hcongQ with ⟨k, hk⟩
    use (A : ℤ) * k - (d : ℤ)
    have hk' :
        (p : ℤ) + 4 * ((d ^ 2 * e : Nat) : ℤ) =
          ((4 * d * e * A - 1 : Nat) : ℤ) * k := by
      exact hk
    rw [hqInt] at hk'
    change
      (A : ℤ) * (p : ℤ) + (d : ℤ) =
        ((4 * d * e * A - 1 : Nat) : ℤ) * ((A : ℤ) * k - (d : ℤ))
    rw [hqInt]
    norm_num [Nat.cast_mul, Nat.cast_pow] at hk' ⊢
    ring_nf at hk' ⊢
    nlinarith [hk']
  rcases hDvdNat with ⟨B, hB⟩
  exact ⟨B, hB.symm⟩

theorem completeFan_modulus_coprime_A
    (d e A : Nat) (hd : 0 < d) (he : 0 < e) (hA : 0 < A) :
    Nat.Coprime (qOf (d * e * A)) A := by
  have hdea : 0 < d * e * A := Nat.mul_pos (Nat.mul_pos hd he) hA
  have hprod : 1 ≤ 4 * d * e * A := by
    have hpos : 0 < 4 * (d * e * A) := Nat.mul_pos (by norm_num) hdea
    nlinarith
  have hcopProd : Nat.Coprime (4 * d * e * A - 1) (4 * d * e * A) := by
    exact (Nat.coprime_self_sub_left (m := 1) (n := 4 * d * e * A) hprod).2 (by simp)
  have hAdvd : A ∣ 4 * d * e * A := by
    exact ⟨4 * d * e, by ring⟩
  have hcopA : Nat.Coprime (4 * d * e * A - 1) A :=
    hcopProd.coprime_dvd_right hAdvd
  simpa [qOf, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcopA

theorem completeFan_scaled_congruence_of_typeIIEquation_decomposition
    (p d e A B : Nat) (hd : 0 < d) (he : 0 < e) (hA : 0 < A)
    (h : typeIIEquation p d e A B) :
    qOf (d * e * A) ∣ A * (p + 4 * (d ^ 2 * e)) := by
  have hdea : 0 < d * e * A := Nat.mul_pos (Nat.mul_pos hd he) hA
  have hprod : 1 ≤ 4 * d * e * A := by
    have hpos : 0 < 4 * (d * e * A) := Nat.mul_pos (by norm_num) hdea
    nlinarith
  have hqNat : (4 * d * e * A - 1) + 1 = 4 * d * e * A := by
    omega
  have hqInt :
      ((4 * d * e * A - 1 : Nat) : ℤ) =
        4 * (d : ℤ) * (e : ℤ) * (A : ℤ) - 1 := by
    have hcast :
        ((4 * d * e * A - 1 : Nat) : ℤ) + 1 =
          4 * (d : ℤ) * (e : ℤ) * (A : ℤ) := by
      exact_mod_cast hqNat
    linarith
  have hqOfEq : qOf (d * e * A) = 4 * d * e * A - 1 := by
    simp [qOf, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  unfold typeIIEquation at h
  have hInt :
      ((4 * d * e * A - 1 : Nat) : ℤ) * (B : ℤ) =
        (A : ℤ) * (p : ℤ) + (d : ℤ) := by
    exact_mod_cast h
  refine ⟨B + d, ?_⟩
  rw [hqOfEq]
  have hEqInt :
      ((A * (p + 4 * (d ^ 2 * e)) : Nat) : ℤ) =
        ((4 * d * e * A - 1 : Nat) : ℤ) * ((B + d : Nat) : ℤ) := by
    rw [hqInt] at hInt ⊢
    norm_num [Nat.cast_mul, Nat.cast_pow] at hInt ⊢
    ring_nf at hInt ⊢
    nlinarith [hInt]
  exact_mod_cast hEqInt

theorem completeFan_congruence_of_typeIIEquation_decomposition
    (p d e A B : Nat) (hd : 0 < d) (he : 0 < e) (hA : 0 < A)
    (h : typeIIEquation p d e A B) :
    qOf (d * e * A) ∣ p + 4 * (d ^ 2 * e) := by
  have hscaled :=
    completeFan_scaled_congruence_of_typeIIEquation_decomposition p d e A B hd he hA h
  have hcop := completeFan_modulus_coprime_A d e A hd he hA
  exact (hcop.dvd_mul_left).1 hscaled

theorem completeFan_congruence_iff_typeIIEquation_decomposition
    (p d e A : Nat) (hd : 0 < d) (he : 0 < e) (hA : 0 < A) :
    qOf (d * e * A) ∣ p + 4 * (d ^ 2 * e) ↔
      ∃ B : Nat, typeIIEquation p d e A B := by
  constructor
  · exact typeIIEquation_of_completeFan_decomposition p d e A hd he hA
  · rintro ⟨B, hB⟩
    exact completeFan_congruence_of_typeIIEquation_decomposition p d e A B hd he hA hB

theorem fixedSlice_typeIIEquation_iff_dvd
    (p d e A : Nat) :
    (∃ B : Nat, typeIIEquation p d e A B) ↔
      qOf (d * e * A) ∣ A * p + d := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    simpa [typeIIEquation, qOf, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      using hB.symm
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    simpa [typeIIEquation, qOf, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      using hB.symm

theorem fixedSlice_typeIIEquation_iff_modEq_zero
    (p d e A : Nat) :
    (∃ B : Nat, typeIIEquation p d e A B) ↔
      A * p + d ≡ 0 [MOD qOf (d * e * A)] := by
  rw [fixedSlice_typeIIEquation_iff_dvd]
  constructor
  · intro h
    exact (Nat.modEq_zero_iff_dvd).2 h
  · intro h
    exact (Nat.modEq_zero_iff_dvd).1 h

theorem typeII_positive_unit_fractions_of_completeFan_decomposition
    (p d e A : Nat) (hp : 0 < p) (hd : 0 < d) (he : 0 < e) (hA : 0 < A)
    (hcong : qOf (d * e * A) ∣ p + 4 * (d ^ 2 * e)) :
    ∃ x y z : Nat,
      0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (p : ℚ) =
        1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  rcases typeIIEquation_of_completeFan_decomposition p d e A hd he hA hcong with
    ⟨B, hBlin⟩
  have hBpos : 0 < B := typeII_B_pos_of_equation p d e A B hp hd hA hBlin
  exact typeII_positive_unit_fractions p d e A B hp hd he hA hBpos hBlin

theorem typeIIEquation_of_completeFan
    (p a h : Nat) (ha : 0 < a) (hh : 0 < h)
    (hdvd : h ∣ a ^ 2) (hcong : qOf a ∣ p + 4 * h) :
    ∃ d e A B : Nat,
      0 < d ∧ 0 < e ∧ 0 < A ∧
      a = d * e * A ∧ h = d ^ 2 * e ∧
      typeIIEquation p d e A B := by
  rcases completeFan_decomposition_of_dvd_square a h ha hh hdvd with
    ⟨d, e, A, hd, he, hA, haeq, hheq⟩
  have hcong' : qOf (d * e * A) ∣ p + 4 * (d ^ 2 * e) := by
    simpa [haeq, hheq] using hcong
  rcases typeIIEquation_of_completeFan_decomposition p d e A hd he hA hcong' with
    ⟨B, hB⟩
  exact ⟨d, e, A, B, hd, he, hA, haeq, hheq, hB⟩

theorem completeFan_esCross_of_fanCongruence
    (p a h : Nat) (ha : 0 < a) (hh : 0 < h)
    (hdvd : h ∣ a ^ 2) (hcong : fanCongruence p a h) :
    ∃ d e A B : Nat,
      0 < d ∧ 0 < e ∧ 0 < A ∧
      a = d * e * A ∧ h = d ^ 2 * e ∧
      typeIIEquation p d e A B ∧
      esCross p (typeIIX p d e A) (typeIIY p e A B) (typeIIZ d e B) := by
  rcases typeIIEquation_of_completeFan p a h ha hh hdvd hcong with
    ⟨d, e, A, B, hd, he, hA, haeq, hheq, hB⟩
  exact ⟨d, e, A, B, hd, he, hA, haeq, hheq, hB,
    typeII_esCross_of_equation p d e A B hd he hA hB⟩

theorem completeFan_congruence_iff_typeIIEquation_first_denominator
    (p a : Nat) (ha : 0 < a) :
    (∃ h : Nat, 0 < h ∧ h ∣ a ^ 2 ∧ qOf a ∣ p + 4 * h) ↔
      ∃ d e A B : Nat,
        0 < d ∧ 0 < e ∧ 0 < A ∧
        a = d * e * A ∧
        typeIIEquation p d e A B ∧
        typeIIX p d e A = p * a := by
  constructor
  · rintro ⟨h, hh, hdvd, hcong⟩
    rcases typeIIEquation_of_completeFan p a h ha hh hdvd hcong with
      ⟨d, e, A, B, hd, he, hA, haeq, _hheq, hB⟩
    have hxEq : typeIIX p d e A = p * a := by
      simp [typeIIX, haeq, Nat.mul_assoc]
    exact ⟨d, e, A, B, hd, he, hA, haeq, hB, hxEq⟩
  · rintro ⟨d, e, A, B, hd, he, hA, haeq, hB, _hxEq⟩
    refine ⟨d ^ 2 * e, ?_, ?_, ?_⟩
    · exact Nat.mul_pos (pow_pos hd 2) he
    · rw [haeq]
      refine ⟨e * A ^ 2, ?_⟩
      ring
    · have hcong :=
        completeFan_congruence_of_typeIIEquation_decomposition p d e A B hd he hA hB
      simpa [haeq] using hcong

theorem typeII_positive_unit_fractions_of_completeFan
    (p a h : Nat) (hp : 0 < p) (ha : 0 < a) (hh : 0 < h)
    (hdvd : h ∣ a ^ 2) (hcong : qOf a ∣ p + 4 * h) :
    ∃ x y z : Nat,
      0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (p : ℚ) =
        1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  rcases typeIIEquation_of_completeFan p a h ha hh hdvd hcong with
    ⟨d, e, A, B, hd, he, hA, _haeq, _hheq, hBlin⟩
  have hBpos : 0 < B := typeII_B_pos_of_equation p d e A B hp hd hA hBlin
  exact typeII_positive_unit_fractions p d e A B hp hd he hA hBpos hBlin

theorem esRepresentable_of_completeFan
    (p a h : Nat) (hp : 0 < p) (ha : 0 < a) (hh : 0 < h)
    (hdvd : h ∣ a ^ 2) (hcong : fanCongruence p a h) :
    esRepresentable p := by
  simpa [esRepresentable, fanCongruence] using
    typeII_positive_unit_fractions_of_completeFan p a h hp ha hh hdvd hcong

theorem completeFan_h_pos_of_pos_dvd_square
    (a h : Nat) (ha : 0 < a) (hdvd : h ∣ a ^ 2) : 0 < h := by
  by_contra hnot
  have hh0 : h = 0 := Nat.eq_zero_of_not_pos hnot
  subst h
  rcases hdvd with ⟨k, hk⟩
  have hsqpos : 0 < a ^ 2 := pow_pos ha 2
  rw [zero_mul] at hk
  omega

theorem esRepresentable_of_fanCongruence_dvd_square
    (p a h : Nat) (hp : 0 < p) (ha : 0 < a)
    (hdvd : h ∣ a ^ 2) (hcong : fanCongruence p a h) :
    esRepresentable p := by
  have hh : 0 < h := completeFan_h_pos_of_pos_dvd_square a h ha hdvd
  exact esRepresentable_of_completeFan p a h hp ha hh hdvd hcong

theorem esRepresentable_of_exists_fanCongruence
    (p : Nat) (hp : 0 < p)
    (hcert : ∃ a h : Nat,
      0 < a ∧ h ∣ a ^ 2 ∧ fanCongruence p a h) :
    esRepresentable p := by
  rcases hcert with ⟨a, h, ha, hdvd, hcong⟩
  exact esRepresentable_of_fanCongruence_dvd_square p a h hp ha hdvd hcong

theorem completeFan_first_denominator_certificate
    (p a h : Nat) (hp : 0 < p) (ha : 0 < a) (hh : 0 < h)
    (hdvd : h ∣ a ^ 2) (hcong : qOf a ∣ p + 4 * h) :
    ∃ d e A B : Nat,
      0 < d ∧ 0 < e ∧ 0 < A ∧ 0 < B ∧
      a = d * e * A ∧ h = d ^ 2 * e ∧
      typeIIEquation p d e A B ∧
      typeIIX p d e A = p * a ∧
      0 < typeIIX p d e A ∧
      0 < typeIIY p e A B ∧
      0 < typeIIZ d e B ∧
      (4 : ℚ) / (p : ℚ) =
        1 / ((p * a : Nat) : ℚ) +
        1 / (typeIIY p e A B : ℚ) +
        1 / (typeIIZ d e B : ℚ) := by
  rcases typeIIEquation_of_completeFan p a h ha hh hdvd hcong with
    ⟨d, e, A, B, hd, he, hA, haeq, hheq, hBlin⟩
  have hBpos : 0 < B := typeII_B_pos_of_equation p d e A B hp hd hA hBlin
  rcases typeII_nat_certificate p d e A B hp hd he hA hBpos hBlin with
    ⟨hx, hy, hz, hident⟩
  have hxEq : typeIIX p d e A = p * a := by
    simp [typeIIX, haeq, Nat.mul_assoc]
  rw [hxEq] at hident
  exact ⟨d, e, A, B, hd, he, hA, hBpos, haeq, hheq, hBlin, hxEq, hx, hy, hz,
    hident⟩

theorem completeFan_congruence_iff_positive_first_denominator_certificate
    (p a : Nat) (hp : 0 < p) (ha : 0 < a) :
    (∃ h : Nat, 0 < h ∧ h ∣ a ^ 2 ∧ qOf a ∣ p + 4 * h) ↔
      ∃ d e A B : Nat,
        0 < d ∧ 0 < e ∧ 0 < A ∧ 0 < B ∧
        a = d * e * A ∧
        typeIIEquation p d e A B ∧
        typeIIX p d e A = p * a ∧
        0 < p * a ∧
        0 < typeIIY p e A B ∧
        0 < typeIIZ d e B ∧
        (4 : ℚ) / (p : ℚ) =
          1 / ((p * a : Nat) : ℚ) +
          1 / (typeIIY p e A B : ℚ) +
          1 / (typeIIZ d e B : ℚ) := by
  constructor
  · rintro ⟨h, hh, hdvd, hcong⟩
    rcases completeFan_first_denominator_certificate p a h hp ha hh hdvd hcong with
      ⟨d, e, A, B, hd, he, hA, hBpos, haeq, _hheq, hBlin, hxEq, _hx, hy, hz,
        hident⟩
    exact ⟨d, e, A, B, hd, he, hA, hBpos, haeq, hBlin, hxEq, Nat.mul_pos hp ha,
      hy, hz, hident⟩
  · rintro ⟨d, e, A, B, hd, he, hA, _hBpos, haeq, hBlin, hxEq, _hpa, _hy, _hz,
      _hident⟩
    exact (completeFan_congruence_iff_typeIIEquation_first_denominator p a ha).2
      ⟨d, e, A, B, hd, he, hA, haeq, hBlin, hxEq⟩

theorem fan_product_of_denominator_equations
    (A e q y z : ℚ)
    (hy : q * y = A + e)
    (hz : q * z = A + A ^ 2 / e)
    (he : e ≠ 0) :
    (q * y - A) * (q * z - A) = A ^ 2 := by
  have hySub : q * y - A = e := by linarith
  have hzSub : q * z - A = A ^ 2 / e := by linarith
  rw [hySub, hzSub]
  field_simp [he]

theorem fan_hyperbola_of_product
    (A q y z : ℚ)
    (hq : q ≠ 0)
    (h : (q * y - A) * (q * z - A) = A ^ 2) :
    q * y * z = A * (y + z) := by
  have h0 : q * (q * y * z - A * (y + z)) = 0 := by
    ring_nf at h ⊢
    nlinarith [h]
  have h1 : q * y * z - A * (y + z) = 0 := by
    exact (mul_eq_zero.mp h0).resolve_left hq
  linarith

theorem fan_product_of_hyperbola
    (A q y z : ℚ)
    (h : q * y * z = A * (y + z)) :
    (q * y - A) * (q * z - A) = A ^ 2 := by
  have hmul := congrArg (fun t : ℚ => q * t) h
  ring_nf at hmul ⊢
  nlinarith [hmul]

theorem fan_hyperbola_iff_product
    (A q y z : ℚ)
    (hq : q ≠ 0) :
    q * y * z = A * (y + z) ↔
      (q * y - A) * (q * z - A) = A ^ 2 := by
  constructor
  · exact fan_product_of_hyperbola A q y z
  · exact fan_hyperbola_of_product A q y z hq

theorem fan_two_fraction_identity
    (A q y z : ℚ)
    (h : q * y * z = A * (y + z))
    (hA : A ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    1 / y + 1 / z = q / A := by
  field_simp [hA, hy, hz]
  ring_nf at *
  exact h.symm

theorem fixedNumerator_identity_from_hyperbola
    (m n a q y z : ℚ)
    (hq : q = m * a - 1)
    (hhyper : q * y * z = (a * n) * (y + z))
    (hn : n ≠ 0) (ha : a ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    m / n = 1 / (a * n) + 1 / y + 1 / z := by
  subst q
  field_simp [hn, ha, hy, hz]
  ring_nf at *
  have hmul := congrArg (fun t : ℚ => n * t) hhyper
  ring_nf at hmul
  linarith [hmul]

theorem fixedNumerator_identity_from_denominator_equations
    (m n a q e y z : ℚ)
    (hqdef : q = m * a - 1)
    (hyEq : q * y = a * n + e)
    (hzEq : q * z = a * n + (a * n) ^ 2 / e)
    (hq : q ≠ 0) (he : e ≠ 0)
    (hn : n ≠ 0) (ha : a ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    m / n = 1 / (a * n) + 1 / y + 1 / z := by
  have hprod :
      (q * y - a * n) * (q * z - a * n) = (a * n) ^ 2 :=
    fan_product_of_denominator_equations (A := a * n) (e := e)
      (q := q) (y := y) (z := z) hyEq hzEq he
  have hhyper : q * y * z = (a * n) * (y + z) :=
    fan_hyperbola_of_product (A := a * n) (q := q) (y := y) (z := z) hq hprod
  exact fixedNumerator_identity_from_hyperbola
    (m := m) (n := n) (a := a) (q := q) (y := y) (z := z)
    hqdef hhyper hn ha hy hz

theorem divisorFan_identity_from_denominator_equations
    (n a q e y z : ℚ)
    (hqdef : q = 4 * a - 1)
    (hyEq : q * y = a * n + e)
    (hzEq : q * z = a * n + (a * n) ^ 2 / e)
    (hq : q ≠ 0) (he : e ≠ 0)
    (hn : n ≠ 0) (ha : a ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    4 / n = 1 / (a * n) + 1 / y + 1 / z := by
  exact fixedNumerator_identity_from_denominator_equations
    (m := 4) (n := n) (a := a) (q := q) (e := e) (y := y) (z := z)
    hqdef hyEq hzEq hq he hn ha hy hz

/-!
The next theorem is the elementary integer bridge behind the fixed-numerator fan:
from `q = ma - 1`, an exact congruence quotient for `n + me`, and an exact
quotient for `e ∣ a^2`, it constructs integral denominator equations.  It avoids
integer division by naming the two quotients explicitly.
-/

theorem fixedFan_integer_denominator_equations
    (m n a e q s k : ℤ)
    (hq : q = m * a - 1)
    (hs : a ^ 2 = e * s)
    (hk : n + m * e = q * k) :
    ∃ y z : ℤ, q * y = a * n + e ∧ q * z = a * n + s * n ^ 2 := by
  use a * k - e
  use a * k + s * q * k ^ 2 - 2 * s * k * m * e + e * m * a
  have hn : n = q * k - m * e := by linarith
  constructor
  · rw [hn, hq]
    ring
  · rw [hn]
    have hrem :
        a * (q * k - m * e) + s * (q * k - m * e) ^ 2 =
          q * (a * k + s * q * k ^ 2 - 2 * s * k * m * e + e * m * a) +
            m * e * (m * e * s - a * (q + 1)) := by
      ring
    have hs' : e * s = a ^ 2 := by rw [← hs]
    have hzero : m * e * (m * e * s - a * (m * a - 1 + 1)) = 0 := by
      calc
        m * e * (m * e * s - a * (m * a - 1 + 1)) =
            m ^ 2 * e * (e * s - a ^ 2) := by ring
        _ = 0 := by rw [hs']; ring
    rw [hrem]
    rw [hq]
    rw [hzero]
    ring

theorem divisorFan_integer_denominator_equations
    (n a e q s k : ℤ)
    (hq : q = 4 * a - 1)
    (hs : a ^ 2 = e * s)
    (hk : n + 4 * e = q * k) :
    ∃ y z : ℤ, q * y = a * n + e ∧ q * z = a * n + s * n ^ 2 := by
  exact fixedFan_integer_denominator_equations
    (m := 4) (n := n) (a := a) (e := e) (q := q) (s := s) (k := k)
    hq hs hk

theorem fixedFan_y_dvd_of_congruence
    (m n a e : Nat) (hm : 2 ≤ m) (ha : 0 < a)
    (hcong : fixedQ m a ∣ n + m * e) :
    fixedQ m a ∣ a * n + e := by
  rcases hcong with ⟨k, hk⟩
  rw [← Int.ofNat_dvd]
  use (a : ℤ) * (k : ℤ) - (e : ℤ)
  have hma : 2 ≤ m * a := by nlinarith [hm, ha]
  have hqNat : fixedQ m a + 1 = m * a := by
    unfold fixedQ
    omega
  have hqInt : (fixedQ m a : ℤ) = (m : ℤ) * (a : ℤ) - 1 := by
    have hcast : (fixedQ m a : ℤ) + 1 = (m : ℤ) * (a : ℤ) := by
      exact_mod_cast hqNat
    linarith
  have hkInt : (n : ℤ) + (m : ℤ) * (e : ℤ) = (fixedQ m a : ℤ) * (k : ℤ) := by
    exact_mod_cast hk
  have hmul := congrArg (fun t : ℤ => (a : ℤ) * t) hkInt
  change (a : ℤ) * (n : ℤ) + (e : ℤ) =
    (fixedQ m a : ℤ) * ((a : ℤ) * (k : ℤ) - (e : ℤ))
  rw [hqInt] at hmul ⊢
  ring_nf at hmul ⊢
  nlinarith [hmul]

theorem fixedFan_inner_div_eq
    (a e s n : Nat) (he : 0 < e) (hs : a ^ 2 = e * s) :
    (a ^ 2 * n ^ 2) / e = s * n ^ 2 := by
  rw [hs]
  rw [mul_assoc]
  exact Nat.mul_div_right (s * n ^ 2) he

theorem exactDivisor_dvd_square_of_conductor_dvd
    (r s a : Nat) (hcond : r * s ∣ a) :
    r * s ^ 2 ∣ a ^ 2 := by
  rcases hcond with ⟨t, rfl⟩
  use r * t ^ 2
  ring

/-!
The next certificate theorem closes the Nat-division layer for the displayed
fixed-numerator fan formulas.  Under the manuscript's congruence and divisibility
hypotheses, the actual `Nat` divisions defining `fixedFanY` and `fixedFanZ`
are exact, the denominators are positive, and the rational unit-fraction identity
holds for those denominators.
-/

theorem fixedFan_nat_certificate
    (m n a e : Nat)
    (hm : 2 ≤ m) (hn : 0 < n) (ha : 0 < a) (he : 0 < e)
    (hedvd : e ∣ a ^ 2)
    (hcong : fixedQ m a ∣ n + m * e) :
    0 < fixedFanX n a ∧
    0 < fixedFanY m n a e ∧
    0 < fixedFanZ m n a e ∧
    (m : ℚ) / (n : ℚ) =
      1 / (fixedFanX n a : ℚ) +
      1 / (fixedFanY m n a e : ℚ) +
      1 / (fixedFanZ m n a e : ℚ) := by
  rcases hedvd with ⟨s, hs⟩
  rcases hcong with ⟨k, hk⟩
  let q := fixedQ m a
  let y := fixedFanY m n a e
  let z := fixedFanZ m n a e
  have hma : 2 ≤ m * a := by nlinarith [hm, ha]
  have hqpos : 0 < q := by
    dsimp [q]
    unfold fixedQ
    omega
  have hqNat : q + 1 = m * a := by
    dsimp [q]
    unfold fixedQ
    omega
  have hqQ : (q : ℚ) = (m : ℚ) * (a : ℚ) - 1 := by
    have hcast : (q : ℚ) + 1 = (m : ℚ) * (a : ℚ) := by
      exact_mod_cast hqNat
    linarith
  have hyDvd : q ∣ a * n + e := by
    dsimp [q]
    exact fixedFan_y_dvd_of_congruence m n a e hm ha ⟨k, hk⟩
  have hyNat : q * y = a * n + e := by
    dsimp [y]
    unfold fixedFanY
    dsimp [q]
    exact Nat.mul_div_cancel' hyDvd
  have hinner : (a ^ 2 * n ^ 2) / e = s * n ^ 2 :=
    fixedFan_inner_div_eq a e s n he hs
  have hsqDvd : e ∣ a ^ 2 * n ^ 2 := by
    use s * n ^ 2
    rw [hs]
    ring
  have hzDvdSimple : q ∣ a * n + s * n ^ 2 := by
    rw [← Int.ofNat_dvd]
    have hqInt : (q : ℤ) = (m : ℤ) * (a : ℤ) - 1 := by
      have hcast : (q : ℤ) + 1 = (m : ℤ) * (a : ℤ) := by
        exact_mod_cast hqNat
      linarith
    have hsInt : (a : ℤ) ^ 2 = (e : ℤ) * (s : ℤ) := by
      exact_mod_cast hs
    have hkInt : (n : ℤ) + (m : ℤ) * (e : ℤ) = (q : ℤ) * (k : ℤ) := by
      exact_mod_cast hk
    rcases fixedFan_integer_denominator_equations
      (m := (m : ℤ)) (n := (n : ℤ)) (a := (a : ℤ)) (e := (e : ℤ))
      (q := (q : ℤ)) (s := (s : ℤ)) (k := (k : ℤ)) hqInt hsInt hkInt with
      ⟨_, zi, _, hzi⟩
    use zi
    change (a : ℤ) * (n : ℤ) + (s : ℤ) * (n : ℤ) ^ 2 = (q : ℤ) * zi
    exact hzi.symm
  have hzDvd : q ∣ a * n + (a ^ 2 * n ^ 2) / e := by
    rw [hinner]
    exact hzDvdSimple
  have hzNat : q * z = a * n + (a ^ 2 * n ^ 2) / e := by
    dsimp [z]
    unfold fixedFanZ
    dsimp [q]
    exact Nat.mul_div_cancel' hzDvd
  have hypos : 0 < y := by
    by_contra hnot
    have hy0 : y = 0 := Nat.eq_zero_of_not_pos hnot
    have hrhs : 0 < a * n + e := by
      have han : 0 < a * n := Nat.mul_pos ha hn
      omega
    rw [hy0, mul_zero] at hyNat
    omega
  have hzpos : 0 < z := by
    by_contra hnot
    have hz0 : z = 0 := Nat.eq_zero_of_not_pos hnot
    have hrhs : 0 < a * n + (a ^ 2 * n ^ 2) / e := by
      have han : 0 < a * n := Nat.mul_pos ha hn
      omega
    rw [hz0, mul_zero] at hzNat
    omega
  have hyQ : (q : ℚ) * (y : ℚ) = (a : ℚ) * (n : ℚ) + (e : ℚ) := by
    exact_mod_cast hyNat
  have hzQ :
      (q : ℚ) * (z : ℚ) =
        (a : ℚ) * (n : ℚ) + ((a : ℚ) * (n : ℚ)) ^ 2 / (e : ℚ) := by
    have hzCast :
        (q : ℚ) * (z : ℚ) = (a : ℚ) * (n : ℚ) +
          ((a ^ 2 * n ^ 2) / e : Nat) := by
      exact_mod_cast hzNat
    rw [hzCast]
    rw [Nat.cast_div_charZero hsqDvd]
    norm_num
    ring
  have hqne : (q : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
  have hene : (e : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt he)
  have hnne : (n : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hane : (a : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
  have hyne : (y : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hypos)
  have hzne : (z : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hzpos)
  have hident := fixedNumerator_identity_from_denominator_equations
    (m := (m : ℚ)) (n := (n : ℚ)) (a := (a : ℚ)) (q := (q : ℚ))
    (e := (e : ℚ)) (y := (y : ℚ)) (z := (z : ℚ))
    hqQ hyQ hzQ hqne hene hnne hane hyne hzne
  refine ⟨?_, hypos, hzpos, ?_⟩
  · unfold fixedFanX
    exact Nat.mul_pos ha hn
  · dsimp [fixedFanX, y, z] at hident ⊢
    simpa [Nat.cast_mul] using hident

theorem fixedFan_nat_unit_fraction_identity
    (m n a e : Nat)
    (hm : 2 ≤ m) (hn : 0 < n) (ha : 0 < a) (he : 0 < e)
    (hedvd : e ∣ a ^ 2)
    (hcong : fixedQ m a ∣ n + m * e) :
    (m : ℚ) / (n : ℚ) =
      1 / (fixedFanX n a : ℚ) +
      1 / (fixedFanY m n a e : ℚ) +
      1 / (fixedFanZ m n a e : ℚ) :=
  (fixedFan_nat_certificate m n a e hm hn ha he hedvd hcong).2.2.2

theorem fixedFan_positive_unit_fractions
    (m n a e : Nat)
    (hm : 2 ≤ m) (hn : 0 < n) (ha : 0 < a) (he : 0 < e)
    (hedvd : e ∣ a ^ 2)
    (hcong : fixedQ m a ∣ n + m * e) :
    ∃ x y z : Nat,
      0 < x ∧ 0 < y ∧ 0 < z ∧
      (m : ℚ) / (n : ℚ) =
        1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  rcases fixedFan_nat_certificate m n a e hm hn ha he hedvd hcong with
    ⟨hx, hy, hz, hident⟩
  exact ⟨fixedFanX n a, fixedFanY m n a e, fixedFanZ m n a e, hx, hy, hz, hident⟩

theorem fixedFan_nat_certificate_of_saturated_progression
    (m n Q r s : Nat)
    (hm : 2 ≤ m) (hn : 0 < n) (hr : 0 < r) (hs : 0 < s)
    (hprogression : m * (r * s) ∣ Q + 1)
    (hcong : Q ∣ n + m * (r * s ^ 2)) :
    ∃ a : Nat,
      0 < a ∧ m * a = Q + 1 ∧
      fixedQ m a = Q ∧
      r * s ∣ a ∧ r * s ^ 2 ∣ a ^ 2 ∧
      0 < fixedFanX n a ∧
      0 < fixedFanY m n a (r * s ^ 2) ∧
      0 < fixedFanZ m n a (r * s ^ 2) ∧
      (m : ℚ) / (n : ℚ) =
        1 / (fixedFanX n a : ℚ) +
        1 / (fixedFanY m n a (r * s ^ 2) : ℚ) +
        1 / (fixedFanZ m n a (r * s ^ 2) : ℚ) := by
  rcases hprogression with ⟨t, ht⟩
  let a := (r * s) * t
  have htpos : 0 < t := by
    by_contra hnot
    have ht0 : t = 0 := Nat.eq_zero_of_not_pos hnot
    rw [ht0, mul_zero] at ht
    omega
  have ha : 0 < a := by
    dsimp [a]
    exact Nat.mul_pos (Nat.mul_pos hr hs) htpos
  have hma : m * a = Q + 1 := by
    dsimp [a]
    rw [ht]
    ring
  have hQ : fixedQ m a = Q := by
    unfold fixedQ
    omega
  have hcond : r * s ∣ a := by
    exact ⟨t, rfl⟩
  have he : 0 < r * s ^ 2 := by
    exact Nat.mul_pos hr (pow_pos hs 2)
  have hedvd : r * s ^ 2 ∣ a ^ 2 :=
    exactDivisor_dvd_square_of_conductor_dvd r s a hcond
  have hcong' : fixedQ m a ∣ n + m * (r * s ^ 2) := by
    simpa [hQ] using hcong
  rcases fixedFan_nat_certificate
      m n a (r * s ^ 2) hm hn ha he hedvd hcong' with
    ⟨hx, hy, hz, hident⟩
  exact ⟨a, ha, hma, hQ, hcond, hedvd, hx, hy, hz, hident⟩

theorem fixedFan_positive_unit_fractions_of_saturated_progression
    (m n Q r s : Nat)
    (hm : 2 ≤ m) (hn : 0 < n) (hr : 0 < r) (hs : 0 < s)
    (hprogression : m * (r * s) ∣ Q + 1)
    (hcong : Q ∣ n + m * (r * s ^ 2)) :
    ∃ a x y z : Nat,
      0 < a ∧ m * a = Q + 1 ∧
      0 < x ∧ 0 < y ∧ 0 < z ∧
      (m : ℚ) / (n : ℚ) =
        1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  rcases fixedFan_nat_certificate_of_saturated_progression
      m n Q r s hm hn hr hs hprogression hcong with
    ⟨a, ha, hma, _hQ, _hcond, _hedvd, hx, hy, hz, hident⟩
  exact ⟨a, fixedFanX n a, fixedFanY m n a (r * s ^ 2),
    fixedFanZ m n a (r * s ^ 2), ha, hma, hx, hy, hz, hident⟩

theorem fixedFan_positive_unit_fractions_of_base_residual_progression
    (m n dMinus dPlus p r s : Nat)
    (hm : 2 ≤ m) (hn : 0 < n) (hr : 0 < r) (hs : 0 < s)
    (hcop : Nat.Coprime dMinus (dPlus * p))
    (hprogression : m * (r * s) ∣ dMinus * (dPlus * p) + 1)
    (hbase : dMinus ∣ n + m * (r * s ^ 2))
    (hresidual : dPlus * p ∣ n + m * (r * s ^ 2)) :
    ∃ a x y z : Nat,
      0 < a ∧ m * a = dMinus * (dPlus * p) + 1 ∧
      0 < x ∧ 0 < y ∧ 0 < z ∧
      (m : ℚ) / (n : ℚ) =
        1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  have hfull : dMinus * (dPlus * p) ∣ n + m * (r * s ^ 2) :=
    fullCongruence_of_base_and_residual
      m n (r * s ^ 2) dMinus (dPlus * p) hcop hbase hresidual
  exact fixedFan_positive_unit_fractions_of_saturated_progression
    m n (dMinus * (dPlus * p)) r s hm hn hr hs hprogression hfull

theorem fixedFan_positive_unit_fractions_of_conditioned_base_residual_hit
    (m n Pz b dMinus dPlus p r s : Nat)
    (hm : 2 ≤ m) (hn : 0 < n) (hr : 0 < r) (hs : 0 < s)
    (hcop : Nat.Coprime dMinus (dPlus * p))
    (hdMinusDvdPz : dMinus ∣ Pz)
    (hnbase : n ≡ b [MOD Pz])
    (hsmall : b + m * (r * s ^ 2) ≡ 0 [MOD dMinus])
    (hprogression : m * (r * s) ∣ dMinus * (dPlus * p) + 1)
    (hresidual : dPlus * p ∣ n + m * (r * s ^ 2)) :
    ∃ a x y z : Nat,
      0 < a ∧ m * a = dMinus * (dPlus * p) + 1 ∧
      0 < x ∧ 0 < y ∧ 0 < z ∧
      (m : ℚ) / (n : ℚ) =
        1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  have hbase : dMinus ∣ n + m * (r * s ^ 2) :=
    conditionedBaseCongruence_dvd
      m n (r * s ^ 2) Pz b dMinus hdMinusDvdPz hnbase hsmall
  exact fixedFan_positive_unit_fractions_of_base_residual_progression
    m n dMinus dPlus p r s hm hn hr hs hcop hprogression hbase hresidual

theorem divisorFan_positive_unit_fractions_of_conditioned_base_residual_hit
    (n Pz b dMinus dPlus p r s : Nat)
    (hn : 0 < n) (hr : 0 < r) (hs : 0 < s)
    (hcop : Nat.Coprime dMinus (dPlus * p))
    (hdMinusDvdPz : dMinus ∣ Pz)
    (hnbase : n ≡ b [MOD Pz])
    (hsmall : b + 4 * (r * s ^ 2) ≡ 0 [MOD dMinus])
    (hprogression : 4 * (r * s) ∣ dMinus * (dPlus * p) + 1)
    (hresidual : dPlus * p ∣ n + 4 * (r * s ^ 2)) :
    ∃ a x y z : Nat,
      0 < a ∧ 4 * a = dMinus * (dPlus * p) + 1 ∧
      0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (n : ℚ) =
        1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  exact fixedFan_positive_unit_fractions_of_conditioned_base_residual_hit
    4 n Pz b dMinus dPlus p r s (by norm_num) hn hr hs hcop
    hdMinusDvdPz hnbase hsmall hprogression hresidual

theorem esRepresentable_of_conditioned_saturated_hit
    (n Pz b dMinus dPlus p r s : Nat)
    (hn : 0 < n) (hr : 0 < r) (hs : 0 < s)
    (hcop : Nat.Coprime dMinus (dPlus * p))
    (hdMinusDvdPz : dMinus ∣ Pz)
    (hnbase : n ≡ b [MOD Pz])
    (hsmall : b + 4 * (r * s ^ 2) ≡ 0 [MOD dMinus])
    (hprogression : 4 * (r * s) ∣ dMinus * (dPlus * p) + 1)
    (hresidual : dPlus * p ∣ n + 4 * (r * s ^ 2)) :
    esRepresentable n := by
  rcases divisorFan_positive_unit_fractions_of_conditioned_base_residual_hit
      n Pz b dMinus dPlus p r s hn hr hs hcop hdMinusDvdPz hnbase
      hsmall hprogression hresidual with
    ⟨_a, x, y, z, _ha, _hprogression, hx, hy, hz, hident⟩
  exact ⟨x, y, z, hx, hy, hz, hident⟩

theorem esRepresentable_of_conditioned_satEvent_hit
    (n Pz b r s : Nat) (event : SatEvent)
    (hn : 0 < n) (hr : 0 < r) (hs : 0 < s)
    (hevent : event.e = r * s ^ 2)
    (hcop : Nat.Coprime event.dMinus (event.dPlus * event.p))
    (hdMinusDvdPz : event.dMinus ∣ Pz)
    (hnbase : n ≡ b [MOD Pz])
    (hsmall : b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hprogression : 4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1)
    (hresidual : event.dPlus * event.p ∣ n + 4 * event.e) :
    esRepresentable n := by
  exact esRepresentable_of_conditioned_saturated_hit
    n Pz b event.dMinus event.dPlus event.p r s hn hr hs hcop
    hdMinusDvdPz hnbase (by simpa [hevent] using hsmall) hprogression
    (by simpa [hevent] using hresidual)

theorem esRepresentable_of_conditioned_satEvent_hit_named
    (n Pz b r s : Nat) (event : SatEvent)
    (hn : 0 < n) (hr : 0 < r) (hs : 0 < s)
    (hevent : event.e = r * s ^ 2)
    (hcop : Nat.Coprime event.dMinus (event.dPlus * event.p))
    (hdMinusDvdPz : event.dMinus ∣ Pz)
    (hnbase : n ≡ b [MOD Pz])
    (hsmall : b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hprogression : 4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1)
    (hhit : satEventHit n event) :
    esRepresentable n := by
  exact esRepresentable_of_conditioned_satEvent_hit
    n Pz b r s event hn hr hs hevent hcop hdMinusDvdPz hnbase hsmall
    hprogression (by simpa [satEventHit, conditionalModulus] using hhit)

theorem esRepresentable_of_conditioned_satEvent_of_satEventHit
    (n Pz b r s : Nat) (event : SatEvent)
    (hn : 0 < n) (hr : 0 < r) (hs : 0 < s)
    (hevent : event.e = r * s ^ 2)
    (hcop : Nat.Coprime event.dMinus (event.dPlus * event.p))
    (hdMinusDvdPz : event.dMinus ∣ Pz)
    (hnbase : n ≡ b [MOD Pz])
    (hsmall : b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hprogression : 4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1)
    (hhit : satEventHit n event) :
    esRepresentable n :=
  esRepresentable_of_conditioned_satEvent_hit_named
    n Pz b r s event hn hr hs hevent hcop hdMinusDvdPz hnbase hsmall
    hprogression hhit

theorem exists_hit_of_hitEventCount_pos
    {α : Type*} [DecidableEq α] (events : Finset α) (hit : α → Prop)
    [DecidablePred hit]
    (hpos : 0 < hitEventCount events hit) :
    ∃ event ∈ events, hit event := by
  classical
  unfold hitEventCount at hpos
  rw [Finset.card_pos] at hpos
  rcases hpos with ⟨event, hevent⟩
  exact ⟨event, (Finset.mem_filter.mp hevent).1,
    (Finset.mem_filter.mp hevent).2⟩

theorem esRepresentable_of_conditioned_uniform_satEvent_exists_hit
    (n Pz b r s : Nat) (events : Finset SatEvent)
    (hn : 0 < n) (hr : 0 < r) (hs : 0 < s)
    (hhit : ∃ event ∈ events, satEventHit n event)
    (hevent : ∀ event ∈ events, event.e = r * s ^ 2)
    (hcop : ∀ event ∈ events,
      Nat.Coprime event.dMinus (event.dPlus * event.p))
    (hdMinusDvdPz : ∀ event ∈ events, event.dMinus ∣ Pz)
    (hnbase : n ≡ b [MOD Pz])
    (hsmall : ∀ event ∈ events,
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hprogression : ∀ event ∈ events,
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    esRepresentable n := by
  rcases hhit with ⟨event, hmem, heventHit⟩
  exact esRepresentable_of_conditioned_satEvent_of_satEventHit
    n Pz b r s event hn hr hs (hevent event hmem) (hcop event hmem)
    (hdMinusDvdPz event hmem) hnbase (hsmall event hmem)
    (hprogression event hmem) heventHit

theorem esRepresentable_of_conditioned_uniform_satEvent_hitCount_pos
    (n Pz b r s : Nat) (events : Finset SatEvent)
    (hn : 0 < n) (hr : 0 < r) (hs : 0 < s)
    (hcount : 0 < hitEventCount events (fun event => satEventHit n event))
    (hevent : ∀ event ∈ events, event.e = r * s ^ 2)
    (hcop : ∀ event ∈ events,
      Nat.Coprime event.dMinus (event.dPlus * event.p))
    (hdMinusDvdPz : ∀ event ∈ events, event.dMinus ∣ Pz)
    (hnbase : n ≡ b [MOD Pz])
    (hsmall : ∀ event ∈ events,
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hprogression : ∀ event ∈ events,
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    esRepresentable n := by
  classical
  have hhit :=
    exists_hit_of_hitEventCount_pos events
      (fun event => satEventHit n event) hcount
  exact esRepresentable_of_conditioned_uniform_satEvent_exists_hit
    n Pz b r s events hn hr hs hhit hevent hcop hdMinusDvdPz hnbase
    hsmall hprogression

theorem exists_esRepresentable_of_reducedBaseSatEventNoHitIndicatorSum_lt_conditioned_uniform
    (N P r s : Nat) (eventsByBase : Nat → Finset SatEvent) (B : Int)
    (hr : 0 < r) (hs : 0 < s)
    (hpointPos : ∀ n ∈ reducedBasePointSet N P, 0 < n)
    (hbound : reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase ≤ B)
    (hlt : B < (reducedBasePointSet N P).card)
    (hevent : ∀ b event, event ∈ eventsByBase b → event.e = r * s ^ 2)
    (hcop : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.dMinus (event.dPlus * event.p))
    (hdMinusDvdPz : ∀ b event, event ∈ eventsByBase b →
      event.dMinus ∣ P)
    (hsmall : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
  (hprogression : ∀ b event, event ∈ eventsByBase b →
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      esRepresentable n := by
  rcases exists_positive_reducedBaseSatEventHit_of_reducedBaseSatEventNoHitIndicatorSum_lt
      N P eventsByBase B hpointPos hbound hlt with
    ⟨n, hnLe, hnPos, hnCop, hhit⟩
  have hnbase : n ≡ n % P [MOD P] :=
    (Nat.mod_modEq n P).symm
  have hrep : esRepresentable n :=
    esRepresentable_of_conditioned_uniform_satEvent_exists_hit
      n P (n % P) r s (eventsByBase (n % P)) hnPos hr hs hhit
      (fun event heventMem => hevent (n % P) event heventMem)
      (fun event heventMem => hcop (n % P) event heventMem)
      (fun event heventMem => hdMinusDvdPz (n % P) event heventMem)
      hnbase
      (fun event heventMem => hsmall (n % P) event heventMem)
      (fun event heventMem => hprogression (n % P) event heventMem)
  exact ⟨n, hnLe, hnPos, hnCop, hrep⟩

theorem exists_esRepresentable_of_reducedBaseSatEventNoHitIndicatorSum_rat_lt_conditioned_uniform
    (N P r s : Nat) (eventsByBase : Nat → Finset SatEvent) (B : ℚ)
    (hr : 0 < r) (hs : 0 < s)
    (hpointPos : ∀ n ∈ reducedBasePointSet N P, 0 < n)
    (hbound : (reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase : ℚ) ≤ B)
    (hlt : B < ((reducedBasePointSet N P).card : ℚ))
    (hevent : ∀ b event, event ∈ eventsByBase b → event.e = r * s ^ 2)
    (hcop : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.dMinus (event.dPlus * event.p))
    (hdMinusDvdPz : ∀ b event, event ∈ eventsByBase b →
      event.dMinus ∣ P)
    (hsmall : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hprogression : ∀ b event, event ∈ eventsByBase b →
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      esRepresentable n := by
  rcases exists_positive_reducedBaseSatEventHit_of_reducedBaseSatEventNoHitIndicatorSum_rat_lt
      N P eventsByBase B hpointPos hbound hlt with
    ⟨n, hnLe, hnPos, hnCop, hhit⟩
  have hnbase : n ≡ n % P [MOD P] :=
    (Nat.mod_modEq n P).symm
  have hrep : esRepresentable n :=
    esRepresentable_of_conditioned_uniform_satEvent_exists_hit
      n P (n % P) r s (eventsByBase (n % P)) hnPos hr hs hhit
      (fun event heventMem => hevent (n % P) event heventMem)
      (fun event heventMem => hcop (n % P) event heventMem)
      (fun event heventMem => hdMinusDvdPz (n % P) event heventMem)
      hnbase
      (fun event heventMem => hsmall (n % P) event heventMem)
      (fun event heventMem => hprogression (n % P) event heventMem)
  exact ⟨n, hnLe, hnPos, hnCop, hrep⟩

theorem exists_esRepresentable_of_reducedBaseRowNoHitIndicatorSum_lt_conditioned_uniform_admissibleFor
    (N P r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Int)
    (hr : 0 < r) (hs : 0 < s)
    (hpointPos : ∀ n ∈ reducedBasePointSet N P, 0 < n)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hbound :
      reducedBaseNoHitIndicatorSumUpTo N P
        (fun b => satEventResidualHitRowsFinset (eventsByBase b)) ≤ B)
    (hlt : B < (reducedBasePointSet N P).card)
    (hevent : ∀ b event, event ∈ eventsByBase b → event.e = r * s ^ 2)
    (hcop : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.dMinus (event.dPlus * event.p))
    (hdMinusDvdPz : ∀ b event, event ∈ eventsByBase b →
      event.dMinus ∣ P)
    (hsmall : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hprogression : ∀ b event, event ∈ eventsByBase b →
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      esRepresentable n := by
  apply exists_esRepresentable_of_reducedBaseSatEventNoHitIndicatorSum_lt_conditioned_uniform
    N P r s eventsByBase B hr hs hpointPos
  · rwa [reducedBaseSatEventNoHitIndicatorSum_eq_reducedBaseNoHitIndicatorSum_admissibleFor
      N P rhoOf eventsByBase hadm]
  · exact hlt
  · exact hevent
  · exact hcop
  · exact hdMinusDvdPz
  · exact hsmall
  · exact hprogression

theorem exists_esRepresentable_of_reducedBaseRowNoHitIndicatorSum_rat_lt_conditioned_uniform_admissibleFor
    (N P r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : ℚ)
    (hr : 0 < r) (hs : 0 < s)
    (hpointPos : ∀ n ∈ reducedBasePointSet N P, 0 < n)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hbound :
      (reducedBaseNoHitIndicatorSumUpTo N P
        (fun b => satEventResidualHitRowsFinset (eventsByBase b)) : ℚ) ≤ B)
    (hlt : B < ((reducedBasePointSet N P).card : ℚ))
    (hevent : ∀ b event, event ∈ eventsByBase b → event.e = r * s ^ 2)
    (hcop : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.dMinus (event.dPlus * event.p))
    (hdMinusDvdPz : ∀ b event, event ∈ eventsByBase b →
      event.dMinus ∣ P)
    (hsmall : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hprogression : ∀ b event, event ∈ eventsByBase b →
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      esRepresentable n := by
  apply exists_esRepresentable_of_reducedBaseSatEventNoHitIndicatorSum_rat_lt_conditioned_uniform
    N P r s eventsByBase B hr hs hpointPos
  · rwa [reducedBaseSatEventNoHitIndicatorSum_eq_reducedBaseNoHitIndicatorSum_admissibleFor
      N P rhoOf eventsByBase hadm]
  · exact hlt
  · exact hevent
  · exact hcop
  · exact hdMinusDvdPz
  · exact hsmall
  · exact hprogression

theorem satEventCertificateData_of_admissibleFor
    (Pz b r s : Nat) (rhoOf : Nat → Nat) (event : SatEvent)
    (hadm : satEventAdmissibleFor Pz rhoOf event)
    (hrho : rhoOf event.e = r * s)
    (hpBase : Nat.Coprime event.p Pz)
    (hbase : b + 4 * event.e ≡ 0 [MOD event.dMinus]) :
    Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
      event.dMinus ∣ Pz ∧
      b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1 := by
  rcases hadm with
    ⟨_hp, _he, _hmedium, hprog, _hdMinusPos, _hdPlusPos,
      hdMinusDvd, hdPlusCop⟩
  have hdMinusCopDPlus : Nat.Coprime event.dMinus event.dPlus :=
    hdPlusCop.symm.coprime_dvd_left hdMinusDvd
  have hdMinusCopP : Nat.Coprime event.dMinus event.p :=
    hpBase.symm.coprime_dvd_left hdMinusDvd
  have hcop : Nat.Coprime event.dMinus (event.dPlus * event.p) :=
    hdMinusCopDPlus.mul_right hdMinusCopP
  have hprogDvd :
      4 * rhoOf event.e ∣ (event.dMinus * event.dPlus) * event.p + 1 :=
    (Nat.modEq_zero_iff_dvd).1 hprog
  have hprogression :
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1 := by
    simpa [hrho, Nat.mul_assoc] using hprogDvd
  exact ⟨hcop, hdMinusDvd, hbase, hprogression⟩

theorem satEventCertificateData_of_admissibleFor_largePrime
    (Pz b r s : Nat) (rhoOf : Nat → Nat) (event : SatEvent)
    (hPzPos : 0 < Pz)
    (hadm : satEventAdmissibleFor Pz rhoOf event)
    (hrho : rhoOf event.e = r * s)
    (hlargeBase : Pz < event.p)
    (hbase : b + 4 * event.e ≡ 0 [MOD event.dMinus]) :
    Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
      event.dMinus ∣ Pz ∧
      b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1 := by
  have hpBase : Nat.Coprime event.p Pz :=
    prime_coprime_of_lt event.p Pz hadm.1 hPzPos hlargeBase
  exact satEventCertificateData_of_admissibleFor
    Pz b r s rhoOf event hadm hrho hpBase hbase

theorem exists_esRepresentable_of_reducedBaseSatEvent_even_rank_bounds_conditioned_uniform
    (N P R r s : Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Nat → ℚ)
    (hP : 0 < P) (hr : 0 < r) (hs : 0 < s)
    (hpointPos : ∀ n ∈ reducedBasePointSet N P, 0 < n)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Even k →
        ((∑ t ∈ (eventsByBase b).powersetCard k,
            baseSatEventCommonHitCountUpTo N P b t : Nat) : ℚ) ≤ B b k)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Odd k → 0 ≤ B b k)
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) <
          ((reducedBasePointSet N P).card : ℚ))
    (hevent : ∀ b event, event ∈ eventsByBase b → event.e = r * s ^ 2)
    (hcop : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.dMinus (event.dPlus * event.p))
    (hdMinusDvdPz : ∀ b event, event ∈ eventsByBase b →
      event.dMinus ∣ P)
    (hsmall : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hprogression : ∀ b event, event ∈ eventsByBase b →
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      esRepresentable n := by
  have hbound :=
    reducedBaseSatEventNoHitIndicatorSum_rat_le_of_base_even_rank_bounds
      N P R eventsByBase B hP heven hodd
  exact
    exists_esRepresentable_of_reducedBaseSatEventNoHitIndicatorSum_rat_lt_conditioned_uniform
      N P r s eventsByBase
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k)
      hr hs hpointPos hbound hbudget hevent hcop hdMinusDvdPz hsmall
      hprogression

theorem exists_esRepresentable_of_reducedBaseSatEvent_signed_rank_bounds_conditioned_uniform
    (N P R r s : Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Nat → ℚ)
    (hP : 0 < P) (hr : 0 < r) (hs : 0 < s)
    (hpointPos : ∀ n ∈ reducedBasePointSet N P, 0 < n)
    (hrank : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ k) *
          ((∑ t ∈ (eventsByBase b).powersetCard k,
              baseSatEventCommonHitCountUpTo N P b t : Nat) : Int) : ℚ) ≤
            B b k)
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) <
          ((reducedBasePointSet N P).card : ℚ))
    (hevent : ∀ b event, event ∈ eventsByBase b → event.e = r * s ^ 2)
    (hcop : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.dMinus (event.dPlus * event.p))
    (hdMinusDvdPz : ∀ b event, event ∈ eventsByBase b →
      event.dMinus ∣ P)
    (hsmall : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hprogression : ∀ b event, event ∈ eventsByBase b →
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      esRepresentable n := by
  have hbound :=
    reducedBaseSatEventNoHitIndicatorSum_rat_le_of_base_signed_rank_bounds
      N P R eventsByBase B hP hrank
  exact
    exists_esRepresentable_of_reducedBaseSatEventNoHitIndicatorSum_rat_lt_conditioned_uniform
      N P r s eventsByBase
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k)
      hr hs hpointPos hbound hbudget hevent hcop hdMinusDvdPz hsmall
      hprogression

theorem exists_esRepresentable_of_reducedBaseSatEvent_even_rank_bounds_conditioned_uniform_admissibleFor
    (N P R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Nat → ℚ)
    (hP : 0 < P) (hr : 0 < r) (hs : 0 < s)
    (hpointPos : ∀ n ∈ reducedBasePointSet N P, 0 < n)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Even k →
        ((∑ t ∈ (eventsByBase b).powersetCard k,
            baseSatEventCommonHitCountUpTo N P b t : Nat) : ℚ) ≤ B b k)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Odd k → 0 ≤ B b k)
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) <
          ((reducedBasePointSet N P).card : ℚ))
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b → event.e = r * s ^ 2)
    (hpBase : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.p P)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus]) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      esRepresentable n := by
  exact
    exists_esRepresentable_of_reducedBaseSatEvent_even_rank_bounds_conditioned_uniform
      N P R r s eventsByBase B hP hr hs hpointPos heven hodd hbudget
      hevent
      (fun b event heventMem =>
        (satEventCertificateData_of_admissibleFor
          P b r s rhoOf event (hadm b event heventMem)
          (hrho b event heventMem) (hpBase b event heventMem)
          (hbase b event heventMem)).1)
      (fun b event heventMem =>
        (satEventCertificateData_of_admissibleFor
          P b r s rhoOf event (hadm b event heventMem)
          (hrho b event heventMem) (hpBase b event heventMem)
          (hbase b event heventMem)).2.1)
      (fun b event heventMem =>
        (satEventCertificateData_of_admissibleFor
          P b r s rhoOf event (hadm b event heventMem)
          (hrho b event heventMem) (hpBase b event heventMem)
          (hbase b event heventMem)).2.2.1)
      (fun b event heventMem =>
        (satEventCertificateData_of_admissibleFor
          P b r s rhoOf event (hadm b event heventMem)
          (hrho b event heventMem) (hpBase b event heventMem)
          (hbase b event heventMem)).2.2.2)

theorem exists_esRepresentable_of_reducedBaseSatEvent_signed_rank_bounds_conditioned_uniform_admissibleFor
    (N P R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Nat → ℚ)
    (hP : 0 < P) (hr : 0 < r) (hs : 0 < s)
    (hpointPos : ∀ n ∈ reducedBasePointSet N P, 0 < n)
    (hrank : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ k) *
          ((∑ t ∈ (eventsByBase b).powersetCard k,
              baseSatEventCommonHitCountUpTo N P b t : Nat) : Int) : ℚ) ≤
            B b k)
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) <
          ((reducedBasePointSet N P).card : ℚ))
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b → event.e = r * s ^ 2)
    (hpBase : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.p P)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus]) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      esRepresentable n := by
  exact
    exists_esRepresentable_of_reducedBaseSatEvent_signed_rank_bounds_conditioned_uniform
      N P R r s eventsByBase B hP hr hs hpointPos hrank hbudget
      hevent
      (fun b event heventMem =>
        (satEventCertificateData_of_admissibleFor
          P b r s rhoOf event (hadm b event heventMem)
          (hrho b event heventMem) (hpBase b event heventMem)
          (hbase b event heventMem)).1)
      (fun b event heventMem =>
        (satEventCertificateData_of_admissibleFor
          P b r s rhoOf event (hadm b event heventMem)
          (hrho b event heventMem) (hpBase b event heventMem)
          (hbase b event heventMem)).2.1)
      (fun b event heventMem =>
        (satEventCertificateData_of_admissibleFor
          P b r s rhoOf event (hadm b event heventMem)
          (hrho b event heventMem) (hpBase b event heventMem)
          (hbase b event heventMem)).2.2.1)
      (fun b event heventMem =>
        (satEventCertificateData_of_admissibleFor
          P b r s rhoOf event (hadm b event heventMem)
          (hrho b event heventMem) (hpBase b event heventMem)
          (hbase b event heventMem)).2.2.2)

theorem exists_esRepresentable_of_reducedBaseSatEvent_even_rank_bounds_conditioned_uniform_largePrime_admissibleFor
    (N P R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Nat → ℚ)
    (hP : 0 < P) (hr : 0 < r) (hs : 0 < s)
    (hpointPos : ∀ n ∈ reducedBasePointSet N P, 0 < n)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Even k →
        ((∑ t ∈ (eventsByBase b).powersetCard k,
            baseSatEventCommonHitCountUpTo N P b t : Nat) : ℚ) ≤ B b k)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Odd k → 0 ≤ B b k)
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) <
          ((reducedBasePointSet N P).card : ℚ))
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b → event.e = r * s ^ 2)
    (hlargeBase : ∀ b event, event ∈ eventsByBase b →
      P < event.p)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus]) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      esRepresentable n := by
  exact
    exists_esRepresentable_of_reducedBaseSatEvent_even_rank_bounds_conditioned_uniform
      N P R r s eventsByBase B hP hr hs hpointPos heven hodd hbudget
      hevent
      (fun b event heventMem =>
        (satEventCertificateData_of_admissibleFor_largePrime
          P b r s rhoOf event hP (hadm b event heventMem)
          (hrho b event heventMem) (hlargeBase b event heventMem)
          (hbase b event heventMem)).1)
      (fun b event heventMem =>
        (satEventCertificateData_of_admissibleFor_largePrime
          P b r s rhoOf event hP (hadm b event heventMem)
          (hrho b event heventMem) (hlargeBase b event heventMem)
          (hbase b event heventMem)).2.1)
      (fun b event heventMem =>
        (satEventCertificateData_of_admissibleFor_largePrime
          P b r s rhoOf event hP (hadm b event heventMem)
          (hrho b event heventMem) (hlargeBase b event heventMem)
          (hbase b event heventMem)).2.2.1)
      (fun b event heventMem =>
        (satEventCertificateData_of_admissibleFor_largePrime
          P b r s rhoOf event hP (hadm b event heventMem)
          (hrho b event heventMem) (hlargeBase b event heventMem)
          (hbase b event heventMem)).2.2.2)

theorem exists_esRepresentable_of_reducedBaseSatEvent_signed_rank_bounds_conditioned_uniform_largePrime_admissibleFor
    (N P R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Nat → ℚ)
    (hP : 0 < P) (hr : 0 < r) (hs : 0 < s)
    (hpointPos : ∀ n ∈ reducedBasePointSet N P, 0 < n)
    (hrank : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ k) *
          ((∑ t ∈ (eventsByBase b).powersetCard k,
              baseSatEventCommonHitCountUpTo N P b t : Nat) : Int) : ℚ) ≤
            B b k)
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) <
          ((reducedBasePointSet N P).card : ℚ))
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b → event.e = r * s ^ 2)
    (hlargeBase : ∀ b event, event ∈ eventsByBase b →
      P < event.p)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus]) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      esRepresentable n := by
  exact
    exists_esRepresentable_of_reducedBaseSatEvent_signed_rank_bounds_conditioned_uniform
      N P R r s eventsByBase B hP hr hs hpointPos hrank hbudget
      hevent
      (fun b event heventMem =>
        (satEventCertificateData_of_admissibleFor_largePrime
          P b r s rhoOf event hP (hadm b event heventMem)
          (hrho b event heventMem) (hlargeBase b event heventMem)
          (hbase b event heventMem)).1)
      (fun b event heventMem =>
        (satEventCertificateData_of_admissibleFor_largePrime
          P b r s rhoOf event hP (hadm b event heventMem)
          (hrho b event heventMem) (hlargeBase b event heventMem)
          (hbase b event heventMem)).2.1)
      (fun b event heventMem =>
        (satEventCertificateData_of_admissibleFor_largePrime
          P b r s rhoOf event hP (hadm b event heventMem)
          (hrho b event heventMem) (hlargeBase b event heventMem)
          (hbase b event heventMem)).2.2.1)
      (fun b event heventMem =>
        (satEventCertificateData_of_admissibleFor_largePrime
          P b r s rhoOf event hP (hadm b event heventMem)
          (hrho b event heventMem) (hlargeBase b event heventMem)
          (hbase b event heventMem)).2.2.2)

theorem exists_esRepresentable_of_reducedBase_even_rank_bounds_conditioned_uniform_admissibleFor
    (N P R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Nat → ℚ)
    (hP : 0 < P) (hr : 0 < r) (hs : 0 < s)
    (hpointPos : ∀ n ∈ reducedBasePointSet N P, 0 < n)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Even k →
        ((∑ t ∈ (satEventResidualHitRowsFinset (eventsByBase b)).powersetCard k,
            baseRowEventCommonHitCountUpTo N P b t : Nat) : ℚ) ≤ B b k)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Odd k → 0 ≤ B b k)
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) <
          ((reducedBasePointSet N P).card : ℚ))
    (hevent : ∀ b event, event ∈ eventsByBase b → event.e = r * s ^ 2)
    (hcop : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.dMinus (event.dPlus * event.p))
    (hdMinusDvdPz : ∀ b event, event ∈ eventsByBase b →
      event.dMinus ∣ P)
    (hsmall : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hprogression : ∀ b event, event ∈ eventsByBase b →
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      esRepresentable n := by
  have hbound :=
    reducedBaseNoHitIndicatorSum_rat_le_of_base_even_rank_bounds
      N P R (fun b => satEventResidualHitRowsFinset (eventsByBase b))
      B hP heven hodd
  exact
    exists_esRepresentable_of_reducedBaseRowNoHitIndicatorSum_rat_lt_conditioned_uniform_admissibleFor
      N P r s rhoOf eventsByBase
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k)
      hr hs hpointPos hadm hbound hbudget hevent hcop hdMinusDvdPz
      hsmall hprogression

theorem exists_positive_reducedBaseRowHit_of_reducedBaseNoHitIndicatorSum_lt_of_one_lt_P
    (N P : Nat) (eventsByBase : Nat → Finset (Nat × Nat)) (B : Int)
    (hP : 1 < P)
    (hbound : reducedBaseNoHitIndicatorSumUpTo N P eventsByBase ≤ B)
    (hlt : B < (reducedBasePointSet N P).card) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      ∃ row ∈ eventsByBase (n % P), n ≡ row.2 [MOD row.1] := by
  exact exists_positive_reducedBaseRowHit_of_reducedBaseNoHitIndicatorSum_lt
    N P eventsByBase B (reducedBasePointSet_pos_of_one_lt_P N P hP)
    hbound hlt

theorem exists_positive_reducedBaseRowHit_of_reducedBaseNoHitIndicatorSum_rat_lt_of_one_lt_P
    (N P : Nat) (eventsByBase : Nat → Finset (Nat × Nat)) (B : ℚ)
    (hP : 1 < P)
    (hbound : (reducedBaseNoHitIndicatorSumUpTo N P eventsByBase : ℚ) ≤ B)
    (hlt : B < ((reducedBasePointSet N P).card : ℚ)) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      ∃ row ∈ eventsByBase (n % P), n ≡ row.2 [MOD row.1] := by
  exact exists_positive_reducedBaseRowHit_of_reducedBaseNoHitIndicatorSum_rat_lt
    N P eventsByBase B (reducedBasePointSet_pos_of_one_lt_P N P hP)
    hbound hlt

theorem exists_positive_reducedBaseSatEventHit_of_reducedBaseSatEventNoHitIndicatorSum_lt_of_one_lt_P
    (N P : Nat) (eventsByBase : Nat → Finset SatEvent) (B : Int)
    (hP : 1 < P)
    (hbound : reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase ≤ B)
    (hlt : B < (reducedBasePointSet N P).card) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      ∃ event ∈ eventsByBase (n % P), satEventHit n event := by
  exact exists_positive_reducedBaseSatEventHit_of_reducedBaseSatEventNoHitIndicatorSum_lt
    N P eventsByBase B (reducedBasePointSet_pos_of_one_lt_P N P hP)
    hbound hlt

theorem exists_positive_reducedBaseSatEventHit_of_reducedBaseSatEventNoHitIndicatorSum_rat_lt_of_one_lt_P
    (N P : Nat) (eventsByBase : Nat → Finset SatEvent) (B : ℚ)
    (hP : 1 < P)
    (hbound : (reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase : ℚ) ≤ B)
    (hlt : B < ((reducedBasePointSet N P).card : ℚ)) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      ∃ event ∈ eventsByBase (n % P), satEventHit n event := by
  exact exists_positive_reducedBaseSatEventHit_of_reducedBaseSatEventNoHitIndicatorSum_rat_lt
    N P eventsByBase B (reducedBasePointSet_pos_of_one_lt_P N P hP)
    hbound hlt

theorem exists_positive_reducedBaseSatEventHit_of_reducedBaseRowNoHitIndicatorSum_lt_admissibleFor_of_one_lt_P
    (N P : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Int)
    (hP : 1 < P)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hbound :
      reducedBaseNoHitIndicatorSumUpTo N P
        (fun b => satEventResidualHitRowsFinset (eventsByBase b)) ≤ B)
    (hlt : B < (reducedBasePointSet N P).card) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      ∃ event ∈ eventsByBase (n % P), satEventHit n event := by
  exact exists_positive_reducedBaseSatEventHit_of_reducedBaseRowNoHitIndicatorSum_lt_admissibleFor
    N P rhoOf eventsByBase B (reducedBasePointSet_pos_of_one_lt_P N P hP)
    hadm hbound hlt

theorem exists_positive_reducedBaseSatEventHit_of_reducedBaseRowNoHitIndicatorSum_rat_lt_admissibleFor_of_one_lt_P
    (N P : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : ℚ)
    (hP : 1 < P)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hbound :
      (reducedBaseNoHitIndicatorSumUpTo N P
        (fun b => satEventResidualHitRowsFinset (eventsByBase b)) : ℚ) ≤ B)
    (hlt : B < ((reducedBasePointSet N P).card : ℚ)) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      ∃ event ∈ eventsByBase (n % P), satEventHit n event := by
  exact exists_positive_reducedBaseSatEventHit_of_reducedBaseRowNoHitIndicatorSum_rat_lt_admissibleFor
    N P rhoOf eventsByBase B (reducedBasePointSet_pos_of_one_lt_P N P hP)
    hadm hbound hlt

theorem exists_esRepresentable_of_reducedBaseSatEventNoHitIndicatorSum_lt_conditioned_uniform_of_one_lt_P
    (N P r s : Nat) (eventsByBase : Nat → Finset SatEvent) (B : Int)
    (hP : 1 < P) (hr : 0 < r) (hs : 0 < s)
    (hbound : reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase ≤ B)
    (hlt : B < (reducedBasePointSet N P).card)
    (hevent : ∀ b event, event ∈ eventsByBase b → event.e = r * s ^ 2)
    (hcop : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.dMinus (event.dPlus * event.p))
    (hdMinusDvdPz : ∀ b event, event ∈ eventsByBase b →
      event.dMinus ∣ P)
    (hsmall : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hprogression : ∀ b event, event ∈ eventsByBase b →
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      esRepresentable n := by
  exact
    exists_esRepresentable_of_reducedBaseSatEventNoHitIndicatorSum_lt_conditioned_uniform
      N P r s eventsByBase B hr hs
      (reducedBasePointSet_pos_of_one_lt_P N P hP)
      hbound hlt hevent hcop hdMinusDvdPz hsmall hprogression

theorem exists_esRepresentable_of_reducedBaseSatEventNoHitIndicatorSum_rat_lt_conditioned_uniform_of_one_lt_P
    (N P r s : Nat) (eventsByBase : Nat → Finset SatEvent) (B : ℚ)
    (hP : 1 < P) (hr : 0 < r) (hs : 0 < s)
    (hbound : (reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase : ℚ) ≤ B)
    (hlt : B < ((reducedBasePointSet N P).card : ℚ))
    (hevent : ∀ b event, event ∈ eventsByBase b → event.e = r * s ^ 2)
    (hcop : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.dMinus (event.dPlus * event.p))
    (hdMinusDvdPz : ∀ b event, event ∈ eventsByBase b →
      event.dMinus ∣ P)
    (hsmall : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hprogression : ∀ b event, event ∈ eventsByBase b →
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      esRepresentable n := by
  exact
    exists_esRepresentable_of_reducedBaseSatEventNoHitIndicatorSum_rat_lt_conditioned_uniform
      N P r s eventsByBase B hr hs
      (reducedBasePointSet_pos_of_one_lt_P N P hP)
      hbound hlt hevent hcop hdMinusDvdPz hsmall hprogression

theorem exists_esRepresentable_of_reducedBaseRowNoHitIndicatorSum_lt_conditioned_uniform_admissibleFor_of_one_lt_P
    (N P r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Int)
    (hP : 1 < P) (hr : 0 < r) (hs : 0 < s)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hbound :
      reducedBaseNoHitIndicatorSumUpTo N P
        (fun b => satEventResidualHitRowsFinset (eventsByBase b)) ≤ B)
    (hlt : B < (reducedBasePointSet N P).card)
    (hevent : ∀ b event, event ∈ eventsByBase b → event.e = r * s ^ 2)
    (hcop : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.dMinus (event.dPlus * event.p))
    (hdMinusDvdPz : ∀ b event, event ∈ eventsByBase b →
      event.dMinus ∣ P)
    (hsmall : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hprogression : ∀ b event, event ∈ eventsByBase b →
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      esRepresentable n := by
  exact
    exists_esRepresentable_of_reducedBaseRowNoHitIndicatorSum_lt_conditioned_uniform_admissibleFor
      N P r s rhoOf eventsByBase B hr hs
      (reducedBasePointSet_pos_of_one_lt_P N P hP)
      hadm hbound hlt hevent hcop hdMinusDvdPz hsmall hprogression

theorem exists_esRepresentable_of_reducedBaseRowNoHitIndicatorSum_rat_lt_conditioned_uniform_admissibleFor_of_one_lt_P
    (N P r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : ℚ)
    (hP : 1 < P) (hr : 0 < r) (hs : 0 < s)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hbound :
      (reducedBaseNoHitIndicatorSumUpTo N P
        (fun b => satEventResidualHitRowsFinset (eventsByBase b)) : ℚ) ≤ B)
    (hlt : B < ((reducedBasePointSet N P).card : ℚ))
    (hevent : ∀ b event, event ∈ eventsByBase b → event.e = r * s ^ 2)
    (hcop : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.dMinus (event.dPlus * event.p))
    (hdMinusDvdPz : ∀ b event, event ∈ eventsByBase b →
      event.dMinus ∣ P)
    (hsmall : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hprogression : ∀ b event, event ∈ eventsByBase b →
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      esRepresentable n := by
  exact
    exists_esRepresentable_of_reducedBaseRowNoHitIndicatorSum_rat_lt_conditioned_uniform_admissibleFor
      N P r s rhoOf eventsByBase B hr hs
      (reducedBasePointSet_pos_of_one_lt_P N P hP)
      hadm hbound hlt hevent hcop hdMinusDvdPz hsmall hprogression

theorem exists_esRepresentable_of_reducedBaseSatEvent_even_rank_bounds_conditioned_uniform_of_one_lt_P
    (N P R r s : Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Nat → ℚ)
    (hP : 1 < P) (hr : 0 < r) (hs : 0 < s)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Even k →
        ((∑ t ∈ (eventsByBase b).powersetCard k,
            baseSatEventCommonHitCountUpTo N P b t : Nat) : ℚ) ≤ B b k)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Odd k → 0 ≤ B b k)
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) <
          ((reducedBasePointSet N P).card : ℚ))
    (hevent : ∀ b event, event ∈ eventsByBase b → event.e = r * s ^ 2)
    (hcop : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.dMinus (event.dPlus * event.p))
    (hdMinusDvdPz : ∀ b event, event ∈ eventsByBase b →
      event.dMinus ∣ P)
    (hsmall : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hprogression : ∀ b event, event ∈ eventsByBase b →
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      esRepresentable n := by
  exact
    exists_esRepresentable_of_reducedBaseSatEvent_even_rank_bounds_conditioned_uniform
      N P R r s eventsByBase B (Nat.lt_trans Nat.zero_lt_one hP)
      hr hs (reducedBasePointSet_pos_of_one_lt_P N P hP)
      heven hodd hbudget hevent hcop hdMinusDvdPz hsmall hprogression

theorem exists_esRepresentable_of_reducedBaseSatEvent_signed_rank_bounds_conditioned_uniform_of_one_lt_P
    (N P R r s : Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Nat → ℚ)
    (hP : 1 < P) (hr : 0 < r) (hs : 0 < s)
    (hrank : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ k) *
          ((∑ t ∈ (eventsByBase b).powersetCard k,
              baseSatEventCommonHitCountUpTo N P b t : Nat) : Int) : ℚ) ≤
            B b k)
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) <
          ((reducedBasePointSet N P).card : ℚ))
    (hevent : ∀ b event, event ∈ eventsByBase b → event.e = r * s ^ 2)
    (hcop : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.dMinus (event.dPlus * event.p))
    (hdMinusDvdPz : ∀ b event, event ∈ eventsByBase b →
      event.dMinus ∣ P)
    (hsmall : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hprogression : ∀ b event, event ∈ eventsByBase b →
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      esRepresentable n := by
  exact
    exists_esRepresentable_of_reducedBaseSatEvent_signed_rank_bounds_conditioned_uniform
      N P R r s eventsByBase B (Nat.lt_trans Nat.zero_lt_one hP)
      hr hs (reducedBasePointSet_pos_of_one_lt_P N P hP)
      hrank hbudget hevent hcop hdMinusDvdPz hsmall hprogression

theorem exists_esRepresentable_of_reducedBaseSatEvent_even_rank_bounds_conditioned_uniform_admissibleFor_of_one_lt_P
    (N P R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Nat → ℚ)
    (hP : 1 < P) (hr : 0 < r) (hs : 0 < s)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Even k →
        ((∑ t ∈ (eventsByBase b).powersetCard k,
            baseSatEventCommonHitCountUpTo N P b t : Nat) : ℚ) ≤ B b k)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Odd k → 0 ≤ B b k)
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) <
          ((reducedBasePointSet N P).card : ℚ))
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b → event.e = r * s ^ 2)
    (hpBase : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.p P)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus]) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      esRepresentable n := by
  exact
    exists_esRepresentable_of_reducedBaseSatEvent_even_rank_bounds_conditioned_uniform_admissibleFor
      N P R r s rhoOf eventsByBase B (Nat.lt_trans Nat.zero_lt_one hP)
      hr hs (reducedBasePointSet_pos_of_one_lt_P N P hP)
      heven hodd hbudget hadm hrho hevent hpBase hbase

theorem exists_esRepresentable_of_reducedBaseSatEvent_signed_rank_bounds_conditioned_uniform_admissibleFor_of_one_lt_P
    (N P R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Nat → ℚ)
    (hP : 1 < P) (hr : 0 < r) (hs : 0 < s)
    (hrank : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ k) *
          ((∑ t ∈ (eventsByBase b).powersetCard k,
              baseSatEventCommonHitCountUpTo N P b t : Nat) : Int) : ℚ) ≤
            B b k)
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) <
          ((reducedBasePointSet N P).card : ℚ))
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b → event.e = r * s ^ 2)
    (hpBase : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.p P)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus]) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      esRepresentable n := by
  exact
    exists_esRepresentable_of_reducedBaseSatEvent_signed_rank_bounds_conditioned_uniform_admissibleFor
      N P R r s rhoOf eventsByBase B (Nat.lt_trans Nat.zero_lt_one hP)
      hr hs (reducedBasePointSet_pos_of_one_lt_P N P hP)
      hrank hbudget hadm hrho hevent hpBase hbase

theorem exists_esRepresentable_of_reducedBaseSatEvent_even_rank_bounds_conditioned_uniform_largePrime_admissibleFor_of_one_lt_P
    (N P R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Nat → ℚ)
    (hP : 1 < P) (hr : 0 < r) (hs : 0 < s)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Even k →
        ((∑ t ∈ (eventsByBase b).powersetCard k,
            baseSatEventCommonHitCountUpTo N P b t : Nat) : ℚ) ≤ B b k)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Odd k → 0 ≤ B b k)
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) <
          ((reducedBasePointSet N P).card : ℚ))
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b → event.e = r * s ^ 2)
    (hlargeBase : ∀ b event, event ∈ eventsByBase b →
      P < event.p)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus]) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      esRepresentable n := by
  exact
    exists_esRepresentable_of_reducedBaseSatEvent_even_rank_bounds_conditioned_uniform_largePrime_admissibleFor
      N P R r s rhoOf eventsByBase B (Nat.lt_trans Nat.zero_lt_one hP)
      hr hs (reducedBasePointSet_pos_of_one_lt_P N P hP)
      heven hodd hbudget hadm hrho hevent hlargeBase hbase

theorem exists_esRepresentable_of_reducedBaseSatEvent_signed_rank_bounds_conditioned_uniform_largePrime_admissibleFor_of_one_lt_P
    (N P R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Nat → ℚ)
    (hP : 1 < P) (hr : 0 < r) (hs : 0 < s)
    (hrank : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ k) *
          ((∑ t ∈ (eventsByBase b).powersetCard k,
              baseSatEventCommonHitCountUpTo N P b t : Nat) : Int) : ℚ) ≤
            B b k)
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) <
          ((reducedBasePointSet N P).card : ℚ))
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b → event.e = r * s ^ 2)
    (hlargeBase : ∀ b event, event ∈ eventsByBase b →
      P < event.p)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus]) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      esRepresentable n := by
  exact
    exists_esRepresentable_of_reducedBaseSatEvent_signed_rank_bounds_conditioned_uniform_largePrime_admissibleFor
      N P R r s rhoOf eventsByBase B (Nat.lt_trans Nat.zero_lt_one hP)
      hr hs (reducedBasePointSet_pos_of_one_lt_P N P hP)
      hrank hbudget hadm hrho hevent hlargeBase hbase

theorem exists_esRepresentable_of_reducedBase_even_rank_bounds_conditioned_uniform_admissibleFor_of_one_lt_P
    (N P R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Nat → ℚ)
    (hP : 1 < P) (hr : 0 < r) (hs : 0 < s)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Even k →
        ((∑ t ∈ (satEventResidualHitRowsFinset (eventsByBase b)).powersetCard k,
            baseRowEventCommonHitCountUpTo N P b t : Nat) : ℚ) ≤ B b k)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Odd k → 0 ≤ B b k)
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) <
          ((reducedBasePointSet N P).card : ℚ))
    (hevent : ∀ b event, event ∈ eventsByBase b → event.e = r * s ^ 2)
    (hcop : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.dMinus (event.dPlus * event.p))
    (hdMinusDvdPz : ∀ b event, event ∈ eventsByBase b →
      event.dMinus ∣ P)
    (hsmall : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hprogression : ∀ b event, event ∈ eventsByBase b →
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    ∃ n : Nat, n ≤ N ∧ 0 < n ∧ Nat.Coprime (n % P) P ∧
      esRepresentable n := by
  exact
    exists_esRepresentable_of_reducedBase_even_rank_bounds_conditioned_uniform_admissibleFor
      N P R r s rhoOf eventsByBase B (Nat.lt_trans Nat.zero_lt_one hP)
      hr hs (reducedBasePointSet_pos_of_one_lt_P N P hP)
      hadm heven hodd hbudget hevent hcop hdMinusDvdPz hsmall hprogression

noncomputable def reducedBaseExceptionalCount (N P : Nat) : Nat := by
  classical
  exact ((reducedBasePointSet N P).filter esExceptional).card

noncomputable def reducedBaseExceptionalCountGeTwo (N P : Nat) : Nat := by
  classical
  exact ((reducedBasePointSet N P).filter
    (fun n => 2 ≤ n ∧ esExceptional n)).card

theorem reducedBaseExceptionalCount_le_reducedBaseSatEventNoHitIndicatorSum_of_variable_certs
    (N P : Nat) (eventsByBase : Nat → Finset SatEvent)
    (hpointPos : ∀ n ∈ reducedBasePointSet N P, 0 < n)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ P ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    (reducedBaseExceptionalCount N P : Int) ≤
      reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase := by
  classical
  have hcardEq :
      (reducedBaseExceptionalCount N P : Int) =
        ∑ n ∈ reducedBasePointSet N P,
          if esExceptional n then (1 : Int) else 0 := by
    unfold reducedBaseExceptionalCount
    rw [Finset.card_filter]
    norm_num
  rw [hcardEq]
  unfold reducedBaseSatEventNoHitIndicatorSumUpTo
  apply Finset.sum_le_sum
  intro n hn
  by_cases hnEx : esExceptional n
  · have hzero :
        hitEventCount (eventsByBase (n % P))
          (fun event => satEventHit n event) = 0 := by
      by_contra hnonzero
      have hpos :
          0 < hitEventCount (eventsByBase (n % P))
            (fun event => satEventHit n event) := Nat.pos_of_ne_zero hnonzero
      rcases exists_hit_of_hitEventCount_pos (eventsByBase (n % P))
          (fun event => satEventHit n event) hpos with
        ⟨event, heventMem, heventHit⟩
      rcases hcert (n % P) event heventMem with
        ⟨r, s, hr, hs, heventEq, hcop, hdMinusDvdP,
          hsmall, hprogression⟩
      have hnbase : n ≡ n % P [MOD P] :=
        (Nat.mod_modEq n P).symm
      have hrep : esRepresentable n :=
        esRepresentable_of_conditioned_satEvent_of_satEventHit
          n P (n % P) r s event (hpointPos n hn) hr hs heventEq hcop
          hdMinusDvdP hnbase hsmall hprogression heventHit
      have hnotRep : ¬ esRepresentable n := by
        simpa [esExceptional] using hnEx
      exact hnotRep hrep
    simp [hnEx, hzero]
  · by_cases hzero :
        hitEventCount (eventsByBase (n % P))
          (fun event => satEventHit n event) = 0
    · simp [hnEx, hzero]
    · simp [hnEx, hzero]

theorem reducedBaseExceptionalCountGeTwo_le_reducedBaseSatEventNoHitIndicatorSum_of_variable_certs
    (N P : Nat) (eventsByBase : Nat → Finset SatEvent)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ P ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    (reducedBaseExceptionalCountGeTwo N P : Int) ≤
      reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase := by
  classical
  have hcardEq :
      (reducedBaseExceptionalCountGeTwo N P : Int) =
        ∑ n ∈ reducedBasePointSet N P,
          if 2 ≤ n ∧ esExceptional n then (1 : Int) else 0 := by
    unfold reducedBaseExceptionalCountGeTwo
    rw [Finset.card_filter]
    norm_num
  rw [hcardEq]
  unfold reducedBaseSatEventNoHitIndicatorSumUpTo
  apply Finset.sum_le_sum
  intro n hn
  by_cases hbad : 2 ≤ n ∧ esExceptional n
  · rcases hbad with ⟨hnTwo, hnEx⟩
    have hzero :
        hitEventCount (eventsByBase (n % P))
          (fun event => satEventHit n event) = 0 := by
      by_contra hnonzero
      have hpos :
          0 < hitEventCount (eventsByBase (n % P))
            (fun event => satEventHit n event) := Nat.pos_of_ne_zero hnonzero
      rcases exists_hit_of_hitEventCount_pos (eventsByBase (n % P))
          (fun event => satEventHit n event) hpos with
        ⟨event, heventMem, heventHit⟩
      rcases hcert (n % P) event heventMem with
        ⟨r, s, hr, hs, heventEq, hcop, hdMinusDvdP,
          hsmall, hprogression⟩
      have hnbase : n ≡ n % P [MOD P] :=
        (Nat.mod_modEq n P).symm
      have hnPos : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2) hnTwo
      have hrep : esRepresentable n :=
        esRepresentable_of_conditioned_satEvent_of_satEventHit
          n P (n % P) r s event hnPos hr hs heventEq hcop
          hdMinusDvdP hnbase hsmall hprogression heventHit
      have hnotRep : ¬ esRepresentable n := by
        simpa [esExceptional] using hnEx
      exact hnotRep hrep
    simp [hnTwo, hnEx, hzero]
  · by_cases hzero :
        hitEventCount (eventsByBase (n % P))
          (fun event => satEventHit n event) = 0
    · simp [hbad, hzero]
    · simp [hbad, hzero]

theorem reducedBaseExceptionalCount_le_of_base_row_bounds_variable_certs
    (N P : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Int)
    (hP : 0 < P)
    (hpointPos : ∀ n ∈ reducedBasePointSet N P, 0 < n)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hbase : ∀ b ∈ reducedResiduesMod P,
      baseRowNoHitIndicatorSumUpTo N P b
        (satEventResidualHitRowsFinset (eventsByBase b)) ≤ B b)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ P ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    (reducedBaseExceptionalCount N P : Int) ≤
      ∑ b ∈ reducedResiduesMod P, B b := by
  calc
    (reducedBaseExceptionalCount N P : Int) ≤
        reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase :=
          reducedBaseExceptionalCount_le_reducedBaseSatEventNoHitIndicatorSum_of_variable_certs
            N P eventsByBase hpointPos hcert
    _ = reducedBaseNoHitIndicatorSumUpTo N P
        (fun b => satEventResidualHitRowsFinset (eventsByBase b)) := by
          exact reducedBaseSatEventNoHitIndicatorSum_eq_reducedBaseNoHitIndicatorSum_admissibleFor
            N P rhoOf eventsByBase hadm
    _ ≤ ∑ b ∈ reducedResiduesMod P, B b :=
          reducedBaseNoHitIndicatorSum_le_of_base_bounds
            N P (fun b => satEventResidualHitRowsFinset (eventsByBase b))
            B hP hbase

theorem reducedBaseExceptionalCount_le_of_base_row_bounds_variable_certs_of_one_lt_P
    (N P : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Int)
    (hP : 1 < P)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hbase : ∀ b ∈ reducedResiduesMod P,
      baseRowNoHitIndicatorSumUpTo N P b
        (satEventResidualHitRowsFinset (eventsByBase b)) ≤ B b)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ P ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    (reducedBaseExceptionalCount N P : Int) ≤
      ∑ b ∈ reducedResiduesMod P, B b := by
  exact
    reducedBaseExceptionalCount_le_of_base_row_bounds_variable_certs
      N P rhoOf eventsByBase B (Nat.lt_trans Nat.zero_lt_one hP)
      (reducedBasePointSet_pos_of_one_lt_P N P hP)
      hadm hbase hcert

theorem reducedBaseExceptionalCount_rat_le_of_base_satEvent_even_rank_bounds_variable_certs
    (N P R : Nat) (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hP : 0 < P)
    (hpointPos : ∀ n ∈ reducedBasePointSet N P, 0 < n)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1), Even r →
        ((∑ s ∈ (eventsByBase b).powersetCard r,
            baseSatEventCommonHitCountUpTo N P b s : Nat) : ℚ) ≤ B b r)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1), Odd r → 0 ≤ B b r)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ P ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    (reducedBaseExceptionalCount N P : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), B b r := by
  have hcountNoHit :
    (reducedBaseExceptionalCount N P : Int) ≤
        reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase :=
    reducedBaseExceptionalCount_le_reducedBaseSatEventNoHitIndicatorSum_of_variable_certs
      N P eventsByBase hpointPos hcert
  have hcountNoHitRat :
      (reducedBaseExceptionalCount N P : ℚ) ≤
        (reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase : ℚ) := by
    exact_mod_cast hcountNoHit
  exact le_trans hcountNoHitRat
    (reducedBaseSatEventNoHitIndicatorSum_rat_le_of_base_even_rank_bounds
      N P R eventsByBase B hP heven hodd)

theorem reducedBaseExceptionalCount_rat_le_of_base_satEvent_even_rank_bounds_variable_certs_of_one_lt_P
    (N P R : Nat) (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hP : 1 < P)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1), Even r →
        ((∑ s ∈ (eventsByBase b).powersetCard r,
            baseSatEventCommonHitCountUpTo N P b s : Nat) : ℚ) ≤ B b r)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1), Odd r → 0 ≤ B b r)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ P ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    (reducedBaseExceptionalCount N P : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), B b r := by
  exact
    reducedBaseExceptionalCount_rat_le_of_base_satEvent_even_rank_bounds_variable_certs
      N P R eventsByBase B (Nat.lt_trans Nat.zero_lt_one hP)
      (reducedBasePointSet_pos_of_one_lt_P N P hP)
      heven hodd hcert

theorem reducedBaseExceptionalCountGeTwo_rat_le_of_base_satEvent_even_rank_bounds_variable_certs
    (N P R : Nat) (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hP : 0 < P)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1), Even r →
        ((∑ s ∈ (eventsByBase b).powersetCard r,
            baseSatEventCommonHitCountUpTo N P b s : Nat) : ℚ) ≤ B b r)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1), Odd r → 0 ≤ B b r)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ P ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    (reducedBaseExceptionalCountGeTwo N P : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), B b r := by
  have hcountNoHit :
    (reducedBaseExceptionalCountGeTwo N P : Int) ≤
        reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase :=
    reducedBaseExceptionalCountGeTwo_le_reducedBaseSatEventNoHitIndicatorSum_of_variable_certs
      N P eventsByBase hcert
  have hcountNoHitRat :
      (reducedBaseExceptionalCountGeTwo N P : ℚ) ≤
        (reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase : ℚ) := by
    exact_mod_cast hcountNoHit
  exact le_trans hcountNoHitRat
    (reducedBaseSatEventNoHitIndicatorSum_rat_le_of_base_even_rank_bounds
      N P R eventsByBase B hP heven hodd)

theorem reducedBaseExceptionalCountGeTwo_rat_le_of_base_satEvent_even_rank_bounds_variable_certs_of_one_lt_P
    (N P R : Nat) (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hP : 1 < P)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1), Even r →
        ((∑ s ∈ (eventsByBase b).powersetCard r,
            baseSatEventCommonHitCountUpTo N P b s : Nat) : ℚ) ≤ B b r)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1), Odd r → 0 ≤ B b r)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ P ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    (reducedBaseExceptionalCountGeTwo N P : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), B b r := by
  exact
    reducedBaseExceptionalCountGeTwo_rat_le_of_base_satEvent_even_rank_bounds_variable_certs
      N P R eventsByBase B (Nat.lt_trans Nat.zero_lt_one hP)
      heven hodd hcert

theorem reducedBaseExceptionalCountGeTwo_rat_le_of_base_satEvent_signed_rank_bounds_variable_certs
    (N P R : Nat) (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hP : 0 < P)
    (hrank : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ r) *
          ((∑ s ∈ (eventsByBase b).powersetCard r,
              baseSatEventCommonHitCountUpTo N P b s : Nat) : Int) : ℚ) ≤
            B b r)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ P ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    (reducedBaseExceptionalCountGeTwo N P : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), B b r := by
  have hcountNoHit :
    (reducedBaseExceptionalCountGeTwo N P : Int) ≤
        reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase :=
    reducedBaseExceptionalCountGeTwo_le_reducedBaseSatEventNoHitIndicatorSum_of_variable_certs
      N P eventsByBase hcert
  have hcountNoHitRat :
      (reducedBaseExceptionalCountGeTwo N P : ℚ) ≤
        (reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase : ℚ) := by
    exact_mod_cast hcountNoHit
  exact le_trans hcountNoHitRat
    (reducedBaseSatEventNoHitIndicatorSum_rat_le_of_base_signed_rank_bounds
      N P R eventsByBase B hP hrank)

theorem reducedBaseExceptionalCountGeTwo_rat_le_of_base_satEvent_signed_rank_bounds_variable_certs_of_one_lt_P
    (N P R : Nat) (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hP : 1 < P)
    (hrank : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ r) *
          ((∑ s ∈ (eventsByBase b).powersetCard r,
              baseSatEventCommonHitCountUpTo N P b s : Nat) : Int) : ℚ) ≤
            B b r)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ P ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    (reducedBaseExceptionalCountGeTwo N P : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), B b r := by
  exact
    reducedBaseExceptionalCountGeTwo_rat_le_of_base_satEvent_signed_rank_bounds_variable_certs
      N P R eventsByBase B (Nat.lt_trans Nat.zero_lt_one hP)
      hrank hcert

theorem reducedBaseExceptionalCountGeTwo_rat_le_of_base_compatible_lcm_bound_variable_certs
    (N P R : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent)
    (hP : 0 < P)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hpCop : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime P event.p)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ P ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    (reducedBaseExceptionalCountGeTwo N P : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1),
          ((∑ t ∈ baseRowCompatibleSubsetsOfCard P b
              (satEventResidualHitRowsFinset (eventsByBase b)) k,
            (N / (P * congruenceLcm t.toList) + 1) : Nat) : ℚ) := by
  have hcountNoHit :
    (reducedBaseExceptionalCountGeTwo N P : Int) ≤
        reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase :=
    reducedBaseExceptionalCountGeTwo_le_reducedBaseSatEventNoHitIndicatorSum_of_variable_certs
      N P eventsByBase hcert
  have hcountNoHitRat :
      (reducedBaseExceptionalCountGeTwo N P : ℚ) ≤
        (reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase : ℚ) := by
    exact_mod_cast hcountNoHit
  exact le_trans hcountNoHitRat
    (reducedBaseSatEventNoHitIndicatorSum_rat_le_of_base_compatible_lcm_bound_admissibleFor
      N P R rhoOf eventsByBase hP hadm hpCop)

theorem reducedBaseExceptionalCountGeTwo_rat_le_of_base_compatible_lcm_bound_largePrime_variable_certs
    (N P R : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent)
    (hP : 0 < P)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hlargeBase : ∀ b event, event ∈ eventsByBase b →
      P < event.p)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ P ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1) :
    (reducedBaseExceptionalCountGeTwo N P : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1),
          ((∑ t ∈ baseRowCompatibleSubsetsOfCard P b
              (satEventResidualHitRowsFinset (eventsByBase b)) k,
            (N / (P * congruenceLcm t.toList) + 1) : Nat) : ℚ) := by
  exact
    reducedBaseExceptionalCountGeTwo_rat_le_of_base_compatible_lcm_bound_variable_certs
      N P R rhoOf eventsByBase hP hadm
      (fun b event hevent =>
        satEvent_base_coprime_of_admissibleFor_largePrime
          P rhoOf event hP (hadm b event hevent) (hlargeBase b event hevent))
      hcert

theorem reducedBaseExceptionalCount_eq_zero_of_rat_lt_one
    (N P : Nat) (B : ℚ)
    (hbound : (reducedBaseExceptionalCount N P : ℚ) ≤ B)
    (hlt : B < 1) :
    reducedBaseExceptionalCount N P = 0 := by
  by_contra hne
  have hpos : 0 < reducedBaseExceptionalCount N P := Nat.pos_of_ne_zero hne
  have honeLeCount : (1 : ℚ) ≤ (reducedBaseExceptionalCount N P : ℚ) := by
    exact_mod_cast (Nat.succ_le_of_lt hpos)
  have honeLtOne : (1 : ℚ) < 1 := lt_of_le_of_lt (le_trans honeLeCount hbound) hlt
  norm_num at honeLtOne

theorem reducedBaseExceptionalCountGeTwo_eq_zero_of_rat_lt_one
    (N P : Nat) (B : ℚ)
    (hbound : (reducedBaseExceptionalCountGeTwo N P : ℚ) ≤ B)
    (hlt : B < 1) :
    reducedBaseExceptionalCountGeTwo N P = 0 := by
  by_contra hne
  have hpos : 0 < reducedBaseExceptionalCountGeTwo N P := Nat.pos_of_ne_zero hne
  have honeLeCount : (1 : ℚ) ≤ (reducedBaseExceptionalCountGeTwo N P : ℚ) := by
    exact_mod_cast (Nat.succ_le_of_lt hpos)
  have honeLtOne : (1 : ℚ) < 1 := lt_of_le_of_lt (le_trans honeLeCount hbound) hlt
  norm_num at honeLtOne

theorem forall_esRepresentable_of_reducedBaseExceptionalCount_eq_zero
    (N P : Nat)
    (hcount : reducedBaseExceptionalCount N P = 0) :
    ∀ n ∈ reducedBasePointSet N P, esRepresentable n := by
  classical
  intro n hn
  by_contra hnNotRep
  have hnEx : esExceptional n := by
    simpa [esExceptional] using hnNotRep
  have hnFilter : n ∈ (reducedBasePointSet N P).filter esExceptional :=
    Finset.mem_filter.mpr ⟨hn, hnEx⟩
  have hpos : 0 < ((reducedBasePointSet N P).filter esExceptional).card :=
    Finset.card_pos.mpr ⟨n, hnFilter⟩
  unfold reducedBaseExceptionalCount at hcount
  rw [hcount] at hpos
  omega

theorem forall_esRepresentable_ge_two_of_reducedBaseExceptionalCountGeTwo_eq_zero
    (N P : Nat)
    (hcount : reducedBaseExceptionalCountGeTwo N P = 0) :
    ∀ n ∈ reducedBasePointSet N P, 2 ≤ n → esRepresentable n := by
  classical
  intro n hn hnTwo
  by_contra hnNotRep
  have hnEx : esExceptional n := by
    simpa [esExceptional] using hnNotRep
  have hnFilter :
      n ∈ (reducedBasePointSet N P).filter
        (fun n => 2 ≤ n ∧ esExceptional n) :=
    Finset.mem_filter.mpr ⟨hn, hnTwo, hnEx⟩
  have hpos :
      0 < ((reducedBasePointSet N P).filter
        (fun n => 2 ≤ n ∧ esExceptional n)).card :=
    Finset.card_pos.mpr ⟨n, hnFilter⟩
  unfold reducedBaseExceptionalCountGeTwo at hcount
  rw [hcount] at hpos
  omega

theorem forall_esRepresentable_ge_two_of_base_compatible_lcm_budget_lt_one_variable_certs
    (N P R : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent)
    (hP : 0 < P)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hpCop : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime P event.p)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ P ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1)
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1),
          ((∑ t ∈ baseRowCompatibleSubsetsOfCard P b
              (satEventResidualHitRowsFinset (eventsByBase b)) k,
            (N / (P * congruenceLcm t.toList) + 1) : Nat) : ℚ)) < 1) :
    ∀ n ∈ reducedBasePointSet N P, 2 ≤ n → esRepresentable n := by
  have hcountBound :=
    reducedBaseExceptionalCountGeTwo_rat_le_of_base_compatible_lcm_bound_variable_certs
      N P R rhoOf eventsByBase hP hadm hpCop hcert
  have hcountZero :=
    reducedBaseExceptionalCountGeTwo_eq_zero_of_rat_lt_one
      N P
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1),
          ((∑ t ∈ baseRowCompatibleSubsetsOfCard P b
              (satEventResidualHitRowsFinset (eventsByBase b)) k,
            (N / (P * congruenceLcm t.toList) + 1) : Nat) : ℚ))
      hcountBound hbudget
  exact forall_esRepresentable_ge_two_of_reducedBaseExceptionalCountGeTwo_eq_zero
    N P hcountZero

theorem forall_esRepresentable_ge_two_of_base_compatible_lcm_budget_lt_one_largePrime_variable_certs
    (N P R : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent)
    (hP : 0 < P)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hlargeBase : ∀ b event, event ∈ eventsByBase b →
      P < event.p)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ P ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1)
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1),
          ((∑ t ∈ baseRowCompatibleSubsetsOfCard P b
              (satEventResidualHitRowsFinset (eventsByBase b)) k,
            (N / (P * congruenceLcm t.toList) + 1) : Nat) : ℚ)) < 1) :
    ∀ n ∈ reducedBasePointSet N P, 2 ≤ n → esRepresentable n := by
  have hcountBound :=
    reducedBaseExceptionalCountGeTwo_rat_le_of_base_compatible_lcm_bound_largePrime_variable_certs
      N P R rhoOf eventsByBase hP hadm hlargeBase hcert
  have hcountZero :=
    reducedBaseExceptionalCountGeTwo_eq_zero_of_rat_lt_one
      N P
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1),
          ((∑ t ∈ baseRowCompatibleSubsetsOfCard P b
              (satEventResidualHitRowsFinset (eventsByBase b)) k,
            (N / (P * congruenceLcm t.toList) + 1) : Nat) : ℚ))
      hcountBound hbudget
  exact forall_esRepresentable_ge_two_of_reducedBaseExceptionalCountGeTwo_eq_zero
    N P hcountZero

theorem reducedBaseExceptionalCountGeTwo_rat_le_of_base_commonHitSum_eq_signed_budget_variable_certs
    (N P R : Nat) (eventsByBase : Nat → Finset SatEvent)
    (C : Nat → Nat → Nat) (B : Nat → Nat → ℚ)
    (hP : 0 < P)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ P ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1)
    (hC : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1),
        (∑ s ∈ (eventsByBase b).powersetCard r,
          baseSatEventCommonHitCountUpTo N P b s) = C b r)
    (hB : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ r) * (C b r : Int) : ℚ) ≤ B b r) :
    (reducedBaseExceptionalCountGeTwo N P : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), B b r := by
  have hcountNoHit :
      (reducedBaseExceptionalCountGeTwo N P : Int) ≤
        reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase :=
    reducedBaseExceptionalCountGeTwo_le_reducedBaseSatEventNoHitIndicatorSum_of_variable_certs
      N P eventsByBase hcert
  have hcountNoHitRat :
      (reducedBaseExceptionalCountGeTwo N P : ℚ) ≤
        (reducedBaseSatEventNoHitIndicatorSumUpTo N P eventsByBase : ℚ) := by
    exact_mod_cast hcountNoHit
  exact le_trans hcountNoHitRat
    (reducedBaseSatEventNoHitIndicatorSum_rat_le_of_base_commonHitSum_eq_signed_budget
      N P R eventsByBase C B hP hC hB)

theorem forall_esRepresentable_ge_two_of_base_commonHitSum_eq_signed_budget_variable_certs
    (N P R : Nat) (eventsByBase : Nat → Finset SatEvent)
    (C : Nat → Nat → Nat) (B : Nat → Nat → ℚ)
    (hP : 0 < P)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ P ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1)
    (hC : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1),
        (∑ s ∈ (eventsByBase b).powersetCard r,
          baseSatEventCommonHitCountUpTo N P b s) = C b r)
    (hB : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ r) * (C b r : Int) : ℚ) ≤ B b r)
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), B b r) < 1) :
    ∀ n ∈ reducedBasePointSet N P, 2 ≤ n → esRepresentable n := by
  have hcountBound :=
    reducedBaseExceptionalCountGeTwo_rat_le_of_base_commonHitSum_eq_signed_budget_variable_certs
      N P R eventsByBase C B hP hcert hC hB
  have hcountZero :=
    reducedBaseExceptionalCountGeTwo_eq_zero_of_rat_lt_one
      N P (∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), B b r)
      hcountBound hbudget
  exact forall_esRepresentable_ge_two_of_reducedBaseExceptionalCountGeTwo_eq_zero
    N P hcountZero

structure SatEventExactCommonHitBudgetCertificate (N P R : Nat) where
  eventsByBase : Nat → Finset SatEvent
  C : Nat → Nat → Nat
  B : Nat → Nat → ℚ
  hP : 0 < P
  hcert : ∀ b event, event ∈ eventsByBase b →
    ∃ r s : Nat,
      0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
      Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
      event.dMinus ∣ P ∧
      b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1
  hC : ∀ b ∈ reducedResiduesMod P,
    ∀ r ∈ Finset.range (2 * R + 1),
      (∑ s ∈ (eventsByBase b).powersetCard r,
        baseSatEventCommonHitCountUpTo N P b s) = C b r
  hB : ∀ b ∈ reducedResiduesMod P,
    ∀ r ∈ Finset.range (2 * R + 1),
      (((-1 : Int) ^ r) * (C b r : Int) : ℚ) ≤ B b r
  hbudget :
    (∑ b ∈ reducedResiduesMod P,
      ∑ r ∈ Finset.range (2 * R + 1), B b r) < 1

theorem reducedBaseExceptionalCountGeTwo_rat_le_of_exactCommonHitBudgetCertificate
    (N P R : Nat)
    (cert : SatEventExactCommonHitBudgetCertificate N P R) :
    (reducedBaseExceptionalCountGeTwo N P : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), cert.B b r :=
  reducedBaseExceptionalCountGeTwo_rat_le_of_base_commonHitSum_eq_signed_budget_variable_certs
    N P R cert.eventsByBase cert.C cert.B cert.hP cert.hcert cert.hC cert.hB

theorem reducedBaseExceptionalCountGeTwo_eq_zero_of_exactCommonHitBudgetCertificate
    (N P R : Nat)
    (cert : SatEventExactCommonHitBudgetCertificate N P R) :
    reducedBaseExceptionalCountGeTwo N P = 0 := by
  exact
    reducedBaseExceptionalCountGeTwo_eq_zero_of_rat_lt_one
      N P (∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), cert.B b r)
      (reducedBaseExceptionalCountGeTwo_rat_le_of_exactCommonHitBudgetCertificate
        N P R cert)
      cert.hbudget

theorem forall_esRepresentable_ge_two_of_exactCommonHitBudgetCertificate
    (N P R : Nat)
    (cert : SatEventExactCommonHitBudgetCertificate N P R) :
    ∀ n ∈ reducedBasePointSet N P, 2 ≤ n → esRepresentable n :=
  forall_esRepresentable_ge_two_of_reducedBaseExceptionalCountGeTwo_eq_zero
    N P (reducedBaseExceptionalCountGeTwo_eq_zero_of_exactCommonHitBudgetCertificate
      N P R cert)

theorem forall_esRepresentable_up_to_of_reducedBaseExceptionalCountGeTwo_eq_zero_mod_210
    (N : Nat)
    (hcount : reducedBaseExceptionalCountGeTwo N 210 = 0) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n := by
  have hcover :
      ∀ n ∈ reducedBasePointSet N 210, 2 ≤ n → esRepresentable n :=
    forall_esRepresentable_ge_two_of_reducedBaseExceptionalCountGeTwo_eq_zero
      N 210 hcount
  exact forall_esRepresentable_of_reducedBasePointSet_coverage_mod_210
    N hcover

theorem forall_esRepresentable_up_to_of_base_commonHitSum_eq_signed_budget_variable_certs_mod_210
    (N R : Nat) (eventsByBase : Nat → Finset SatEvent)
    (C : Nat → Nat → Nat) (B : Nat → Nat → ℚ)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ 210 ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1)
    (hC : ∀ b ∈ reducedResiduesMod 210,
      ∀ r ∈ Finset.range (2 * R + 1),
        (∑ s ∈ (eventsByBase b).powersetCard r,
          baseSatEventCommonHitCountUpTo N 210 b s) = C b r)
    (hB : ∀ b ∈ reducedResiduesMod 210,
      ∀ r ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ r) * (C b r : Int) : ℚ) ≤ B b r)
    (hbudget :
      (∑ b ∈ reducedResiduesMod 210,
        ∑ r ∈ Finset.range (2 * R + 1), B b r) < 1) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n := by
  have hcountBound :=
    reducedBaseExceptionalCountGeTwo_rat_le_of_base_commonHitSum_eq_signed_budget_variable_certs
      N 210 R eventsByBase C B (by norm_num) hcert hC hB
  have hcountZero :=
    reducedBaseExceptionalCountGeTwo_eq_zero_of_rat_lt_one
      N 210 (∑ b ∈ reducedResiduesMod 210,
        ∑ r ∈ Finset.range (2 * R + 1), B b r)
      hcountBound hbudget
  exact forall_esRepresentable_up_to_of_reducedBaseExceptionalCountGeTwo_eq_zero_mod_210
    N hcountZero

theorem forall_esRepresentable_up_to_of_exactCommonHitBudgetCertificate_mod_210
    (N R : Nat)
    (cert : SatEventExactCommonHitBudgetCertificate N 210 R) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n :=
  forall_esRepresentable_up_to_of_base_commonHitSum_eq_signed_budget_variable_certs_mod_210
    N R cert.eventsByBase cert.C cert.B cert.hcert cert.hC cert.hB
    cert.hbudget

theorem forall_esRepresentable_of_base_satEvent_even_rank_budget_lt_one_variable_certs_of_one_lt_P
    (N P R : Nat) (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hP : 1 < P)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1), Even r →
        ((∑ s ∈ (eventsByBase b).powersetCard r,
            baseSatEventCommonHitCountUpTo N P b s : Nat) : ℚ) ≤ B b r)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1), Odd r → 0 ≤ B b r)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ P ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1)
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), B b r) < 1) :
    ∀ n ∈ reducedBasePointSet N P, esRepresentable n := by
  have hcountBound :=
    reducedBaseExceptionalCount_rat_le_of_base_satEvent_even_rank_bounds_variable_certs_of_one_lt_P
      N P R eventsByBase B hP heven hodd hcert
  have hcountZero :=
    reducedBaseExceptionalCount_eq_zero_of_rat_lt_one
      N P (∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), B b r)
      hcountBound hbudget
  exact forall_esRepresentable_of_reducedBaseExceptionalCount_eq_zero
    N P hcountZero

theorem forall_esRepresentable_ge_two_of_base_satEvent_even_rank_budget_lt_one_variable_certs_of_one_lt_P
    (N P R : Nat) (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hP : 1 < P)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1), Even r →
        ((∑ s ∈ (eventsByBase b).powersetCard r,
            baseSatEventCommonHitCountUpTo N P b s : Nat) : ℚ) ≤ B b r)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1), Odd r → 0 ≤ B b r)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ P ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1)
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), B b r) < 1) :
    ∀ n ∈ reducedBasePointSet N P, 2 ≤ n → esRepresentable n := by
  have hcountBound :=
    reducedBaseExceptionalCountGeTwo_rat_le_of_base_satEvent_even_rank_bounds_variable_certs_of_one_lt_P
      N P R eventsByBase B hP heven hodd hcert
  have hcountZero :=
    reducedBaseExceptionalCountGeTwo_eq_zero_of_rat_lt_one
      N P (∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), B b r)
      hcountBound hbudget
  exact forall_esRepresentable_ge_two_of_reducedBaseExceptionalCountGeTwo_eq_zero
    N P hcountZero

theorem forall_esRepresentable_ge_two_of_base_satEvent_signed_rank_budget_lt_one_variable_certs_of_one_lt_P
    (N P R : Nat) (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hP : 1 < P)
    (hrank : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ r) *
          ((∑ s ∈ (eventsByBase b).powersetCard r,
              baseSatEventCommonHitCountUpTo N P b s : Nat) : Int) : ℚ) ≤
            B b r)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ P ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1)
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), B b r) < 1) :
    ∀ n ∈ reducedBasePointSet N P, 2 ≤ n → esRepresentable n := by
  have hcountBound :=
    reducedBaseExceptionalCountGeTwo_rat_le_of_base_satEvent_signed_rank_bounds_variable_certs_of_one_lt_P
      N P R eventsByBase B hP hrank hcert
  have hcountZero :=
    reducedBaseExceptionalCountGeTwo_eq_zero_of_rat_lt_one
      N P (∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), B b r)
      hcountBound hbudget
  exact forall_esRepresentable_ge_two_of_reducedBaseExceptionalCountGeTwo_eq_zero
    N P hcountZero

structure SatEventRankBudgetCertificate (N P R : Nat) where
  eventsByBase : Nat → Finset SatEvent
  B : Nat → Nat → ℚ
  hP : 1 < P
  hrank : ∀ b ∈ reducedResiduesMod P,
    ∀ r ∈ Finset.range (2 * R + 1),
      (((-1 : Int) ^ r) *
        ((∑ s ∈ (eventsByBase b).powersetCard r,
            baseSatEventCommonHitCountUpTo N P b s : Nat) : Int) : ℚ) ≤
          B b r
  hcert : ∀ b event, event ∈ eventsByBase b →
    ∃ r s : Nat,
      0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
      Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
      event.dMinus ∣ P ∧
      b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1
  hbudget :
    (∑ b ∈ reducedResiduesMod P,
      ∑ r ∈ Finset.range (2 * R + 1), B b r) < 1

theorem reducedBaseExceptionalCountGeTwo_rat_le_of_SatEventRankBudgetCertificate
    (N P R : Nat)
    (cert : SatEventRankBudgetCertificate N P R) :
    (reducedBaseExceptionalCountGeTwo N P : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), cert.B b r :=
  reducedBaseExceptionalCountGeTwo_rat_le_of_base_satEvent_signed_rank_bounds_variable_certs_of_one_lt_P
    N P R cert.eventsByBase cert.B cert.hP cert.hrank cert.hcert

theorem reducedBaseExceptionalCountGeTwo_eq_zero_of_SatEventRankBudgetCertificate
    (N P R : Nat)
    (cert : SatEventRankBudgetCertificate N P R) :
    reducedBaseExceptionalCountGeTwo N P = 0 := by
  exact
    reducedBaseExceptionalCountGeTwo_eq_zero_of_rat_lt_one
      N P (∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), cert.B b r)
      (reducedBaseExceptionalCountGeTwo_rat_le_of_SatEventRankBudgetCertificate
        N P R cert)
      cert.hbudget

theorem forall_esRepresentable_ge_two_of_SatEventRankBudgetCertificate
    (N P R : Nat)
    (cert : SatEventRankBudgetCertificate N P R) :
    ∀ n ∈ reducedBasePointSet N P, 2 ≤ n → esRepresentable n :=
  forall_esRepresentable_ge_two_of_base_satEvent_signed_rank_budget_lt_one_variable_certs_of_one_lt_P
    N P R cert.eventsByBase cert.B cert.hP cert.hrank cert.hcert
    cert.hbudget

theorem forall_esRepresentable_up_to_of_SatEventRankBudgetCertificate_mod_210
    (N R : Nat)
    (cert : SatEventRankBudgetCertificate N 210 R) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n := by
  have hcover :
      ∀ n ∈ reducedBasePointSet N 210, 2 ≤ n → esRepresentable n :=
    forall_esRepresentable_ge_two_of_SatEventRankBudgetCertificate
      N 210 R cert
  exact forall_esRepresentable_of_reducedBasePointSet_coverage_mod_210
    N hcover

theorem forall_esRepresentable_up_to_of_smoothLiftSmall_and_badExceptional_zero_of_reducedBase_count_zero
    {Smooth Small Bad : Nat → Prop} {N M P : Nat}
    (hsplitExists :
      ∀ n : Nat, 0 < n → n ≤ N →
        ∃ s m : Nat,
          SmoothLiftSplit Smooth
            (fun m => m ∈ reducedBasePointSet M P) n s m)
    (hsmallGeTwo : ∀ m : Nat, 0 < m → ¬ Small m → 2 ≤ m)
    (hcount : reducedBaseExceptionalCountGeTwo M P = 0)
    (hsmallZero :
      smoothLiftSmallSplitCount Smooth
        (fun m => m ∈ reducedBasePointSet M P) Small N = 0)
    (hbadZero :
      smoothLiftBadExceptionalCofactorSplitCount Smooth
        (fun m => m ∈ reducedBasePointSet M P) Bad N = 0) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n := by
  have hcoverage :
      ∀ m : Nat, 2 ≤ m → m ∈ reducedBasePointSet M P →
        esRepresentable m := by
    intro m hmTwo hmReduced
    exact
      forall_esRepresentable_ge_two_of_reducedBaseExceptionalCountGeTwo_eq_zero
        M P hcount m hmReduced hmTwo
  exact
    forall_esRepresentable_up_to_of_smoothLiftSmall_and_badExceptional_zero_of_ge_two_coverage
      (Smooth := Smooth)
      (Reduced := fun m => m ∈ reducedBasePointSet M P)
      (Small := Small) (Bad := Bad) (N := N)
      hsplitExists hcoverage hsmallGeTwo hsmallZero hbadZero

theorem forall_esRepresentable_up_to_of_smoothLiftSmall_and_badExceptional_zero_of_exactCommonHitBudgetCertificate
    {Smooth Small Bad : Nat → Prop}
    (N M P R : Nat)
    (cert : SatEventExactCommonHitBudgetCertificate M P R)
    (hsplitExists :
      ∀ n : Nat, 0 < n → n ≤ N →
        ∃ s m : Nat,
          SmoothLiftSplit Smooth
            (fun m => m ∈ reducedBasePointSet M P) n s m)
    (hsmallGeTwo : ∀ m : Nat, 0 < m → ¬ Small m → 2 ≤ m)
    (hsmallZero :
      smoothLiftSmallSplitCount Smooth
        (fun m => m ∈ reducedBasePointSet M P) Small N = 0)
    (hbadZero :
      smoothLiftBadExceptionalCofactorSplitCount Smooth
        (fun m => m ∈ reducedBasePointSet M P) Bad N = 0) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n := by
  have hcoverage :
      ∀ m : Nat, 2 ≤ m → m ∈ reducedBasePointSet M P →
        esRepresentable m := by
    intro m hmTwo hmReduced
    exact
      forall_esRepresentable_ge_two_of_exactCommonHitBudgetCertificate
        M P R cert m hmReduced hmTwo
  exact
    forall_esRepresentable_up_to_of_smoothLiftSmall_and_badExceptional_zero_of_ge_two_coverage
      (Smooth := Smooth)
      (Reduced := fun m => m ∈ reducedBasePointSet M P)
      (Small := Small) (Bad := Bad) (N := N)
      hsplitExists hcoverage hsmallGeTwo hsmallZero hbadZero

theorem forall_esRepresentable_up_to_of_smoothLiftSmall_and_badExceptional_zero_of_base_satEvent_even_rank_budget_lt_one_variable_certs
    {Smooth Small Bad : Nat → Prop}
    (N M P R : Nat) (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hP : 1 < P)
    (hsplitExists :
      ∀ n : Nat, 0 < n → n ≤ N →
        ∃ s m : Nat,
          SmoothLiftSplit Smooth
            (fun m => m ∈ reducedBasePointSet M P) n s m)
    (hsmallGeTwo : ∀ m : Nat, 0 < m → ¬ Small m → 2 ≤ m)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1), Even r →
        ((∑ s ∈ (eventsByBase b).powersetCard r,
            baseSatEventCommonHitCountUpTo M P b s : Nat) : ℚ) ≤ B b r)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1), Odd r → 0 ≤ B b r)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ P ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1)
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), B b r) < 1)
    (hsmallZero :
      smoothLiftSmallSplitCount Smooth
        (fun m => m ∈ reducedBasePointSet M P) Small N = 0)
    (hbadZero :
      smoothLiftBadExceptionalCofactorSplitCount Smooth
        (fun m => m ∈ reducedBasePointSet M P) Bad N = 0) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n := by
  have hcoverage :
      ∀ m : Nat, 2 ≤ m → m ∈ reducedBasePointSet M P →
        esRepresentable m := by
    intro m hmTwo hmReduced
    exact
      forall_esRepresentable_ge_two_of_base_satEvent_even_rank_budget_lt_one_variable_certs_of_one_lt_P
        M P R eventsByBase B hP heven hodd hcert hbudget
        m hmReduced hmTwo
  exact
    forall_esRepresentable_up_to_of_smoothLiftSmall_and_badExceptional_zero_of_ge_two_coverage
      (Smooth := Smooth)
      (Reduced := fun m => m ∈ reducedBasePointSet M P)
      (Small := Small) (Bad := Bad) (N := N)
      hsplitExists hcoverage hsmallGeTwo hsmallZero hbadZero

theorem forall_esRepresentable_up_to_of_smoothLiftSmall_and_badExceptional_zero_of_base_satEvent_signed_rank_budget_lt_one_variable_certs
    {Smooth Small Bad : Nat → Prop}
    (N M P R : Nat) (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hP : 1 < P)
    (hsplitExists :
      ∀ n : Nat, 0 < n → n ≤ N →
        ∃ s m : Nat,
          SmoothLiftSplit Smooth
            (fun m => m ∈ reducedBasePointSet M P) n s m)
    (hsmallGeTwo : ∀ m : Nat, 0 < m → ¬ Small m → 2 ≤ m)
    (hrank : ∀ b ∈ reducedResiduesMod P,
      ∀ r ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ r) *
          ((∑ s ∈ (eventsByBase b).powersetCard r,
              baseSatEventCommonHitCountUpTo M P b s : Nat) : Int) : ℚ) ≤
            B b r)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ P ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1)
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ r ∈ Finset.range (2 * R + 1), B b r) < 1)
    (hsmallZero :
      smoothLiftSmallSplitCount Smooth
        (fun m => m ∈ reducedBasePointSet M P) Small N = 0)
    (hbadZero :
      smoothLiftBadExceptionalCofactorSplitCount Smooth
        (fun m => m ∈ reducedBasePointSet M P) Bad N = 0) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n := by
  have hcoverage :
      ∀ m : Nat, 2 ≤ m → m ∈ reducedBasePointSet M P →
        esRepresentable m := by
    intro m hmTwo hmReduced
    exact
      forall_esRepresentable_ge_two_of_base_satEvent_signed_rank_budget_lt_one_variable_certs_of_one_lt_P
        M P R eventsByBase B hP hrank hcert hbudget
        m hmReduced hmTwo
  exact
    forall_esRepresentable_up_to_of_smoothLiftSmall_and_badExceptional_zero_of_ge_two_coverage
      (Smooth := Smooth)
      (Reduced := fun m => m ∈ reducedBasePointSet M P)
      (Small := Small) (Bad := Bad) (N := N)
      hsplitExists hcoverage hsmallGeTwo hsmallZero hbadZero

theorem forall_esRepresentable_up_to_of_base_satEvent_even_rank_budget_lt_one_variable_certs_mod_210
    (N R : Nat) (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (heven : ∀ b ∈ reducedResiduesMod 210,
      ∀ r ∈ Finset.range (2 * R + 1), Even r →
        ((∑ s ∈ (eventsByBase b).powersetCard r,
            baseSatEventCommonHitCountUpTo N 210 b s : Nat) : ℚ) ≤ B b r)
    (hodd : ∀ b ∈ reducedResiduesMod 210,
      ∀ r ∈ Finset.range (2 * R + 1), Odd r → 0 ≤ B b r)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ 210 ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1)
    (hbudget :
      (∑ b ∈ reducedResiduesMod 210,
        ∑ r ∈ Finset.range (2 * R + 1), B b r) < 1) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n := by
  have hcover :
      ∀ n ∈ reducedBasePointSet N 210, 2 ≤ n → esRepresentable n :=
    forall_esRepresentable_ge_two_of_base_satEvent_even_rank_budget_lt_one_variable_certs_of_one_lt_P
      N 210 R eventsByBase B (by norm_num) heven hodd hcert hbudget
  exact forall_esRepresentable_of_reducedBasePointSet_coverage_mod_210
    N hcover

theorem forall_esRepresentable_up_to_of_base_satEvent_signed_rank_budget_lt_one_variable_certs_mod_210
    (N R : Nat) (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hrank : ∀ b ∈ reducedResiduesMod 210,
      ∀ r ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ r) *
          ((∑ s ∈ (eventsByBase b).powersetCard r,
              baseSatEventCommonHitCountUpTo N 210 b s : Nat) : Int) : ℚ) ≤
            B b r)
    (hcert : ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ 210 ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1)
    (hbudget :
      (∑ b ∈ reducedResiduesMod 210,
        ∑ r ∈ Finset.range (2 * R + 1), B b r) < 1) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n := by
  have hcover :
      ∀ n ∈ reducedBasePointSet N 210, 2 ≤ n → esRepresentable n :=
    forall_esRepresentable_ge_two_of_base_satEvent_signed_rank_budget_lt_one_variable_certs_of_one_lt_P
      N 210 R eventsByBase B (by norm_num) hrank hcert hbudget
  exact forall_esRepresentable_of_reducedBasePointSet_coverage_mod_210
    N hcover

theorem satEventVariableCert_of_admissibleFor
    (Pz b r s : Nat) (rhoOf : Nat → Nat) (event : SatEvent)
    (hr : 0 < r) (hs : 0 < s)
    (hadm : satEventAdmissibleFor Pz rhoOf event)
    (hrho : rhoOf event.e = r * s)
    (hevent : event.e = r * s ^ 2)
    (hpBase : Nat.Coprime event.p Pz)
    (hbase : b + 4 * event.e ≡ 0 [MOD event.dMinus]) :
    ∃ r s : Nat,
      0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
      Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
      event.dMinus ∣ Pz ∧
      b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1 := by
  rcases satEventCertificateData_of_admissibleFor
      Pz b r s rhoOf event hadm hrho hpBase hbase with
    ⟨hcop, hdMinusDvd, hbase, hprogression⟩
  exact ⟨r, s, hr, hs, hevent, hcop, hdMinusDvd, hbase, hprogression⟩

theorem satEventVariableCerts_of_admissibleFor_uniform
    (Pz r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent)
    (hr : 0 < r) (hs : 0 < s)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor Pz rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b →
      event.e = r * s ^ 2)
    (hpBase : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.p Pz)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus]) :
    ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ Pz ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1 := by
  intro b event heventMem
  exact satEventVariableCert_of_admissibleFor
    Pz b r s rhoOf event hr hs (hadm b event heventMem)
    (hrho b event heventMem) (hevent b event heventMem)
    (hpBase b event heventMem) (hbase b event heventMem)

theorem satEventVariableCert_of_admissibleFor_largePrime
    (Pz b r s : Nat) (rhoOf : Nat → Nat) (event : SatEvent)
    (hPzPos : 0 < Pz) (hr : 0 < r) (hs : 0 < s)
    (hadm : satEventAdmissibleFor Pz rhoOf event)
    (hrho : rhoOf event.e = r * s)
    (hevent : event.e = r * s ^ 2)
    (hlargeBase : Pz < event.p)
    (hbase : b + 4 * event.e ≡ 0 [MOD event.dMinus]) :
    ∃ r s : Nat,
      0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
      Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
      event.dMinus ∣ Pz ∧
      b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1 := by
  have hpBase : Nat.Coprime event.p Pz :=
    prime_coprime_of_lt event.p Pz hadm.1 hPzPos hlargeBase
  exact satEventVariableCert_of_admissibleFor
    Pz b r s rhoOf event hr hs hadm hrho hevent hpBase hbase

theorem satEventVariableCerts_of_admissibleFor_largePrime_uniform
    (Pz r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent)
    (hPzPos : 0 < Pz) (hr : 0 < r) (hs : 0 < s)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor Pz rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b →
      event.e = r * s ^ 2)
    (hlargeBase : ∀ b event, event ∈ eventsByBase b →
      Pz < event.p)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus]) :
    ∀ b event, event ∈ eventsByBase b →
      ∃ r s : Nat,
        0 < r ∧ 0 < s ∧ event.e = r * s ^ 2 ∧
        Nat.Coprime event.dMinus (event.dPlus * event.p) ∧
        event.dMinus ∣ Pz ∧
        b + 4 * event.e ≡ 0 [MOD event.dMinus] ∧
        4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1 := by
  intro b event heventMem
  exact satEventVariableCert_of_admissibleFor_largePrime
    Pz b r s rhoOf event hPzPos hr hs (hadm b event heventMem)
    (hrho b event heventMem) (hevent b event heventMem)
    (hlargeBase b event heventMem) (hbase b event heventMem)

theorem reducedBaseExceptionalCountGeTwo_rat_le_of_baseSatEvent_even_rank_bounds_admissibleFor_uniform_certs
    (N P R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Nat → ℚ)
    (hP : 0 < P) (hr : 0 < r) (hs : 0 < s)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Even k →
        ((∑ t ∈ (eventsByBase b).powersetCard k,
            baseSatEventCommonHitCountUpTo N P b t : Nat) : ℚ) ≤ B b k)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Odd k → 0 ≤ B b k)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b →
      event.e = r * s ^ 2)
    (hpBase : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.p P)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus]) :
    (reducedBaseExceptionalCountGeTwo N P : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k := by
  exact
    reducedBaseExceptionalCountGeTwo_rat_le_of_base_satEvent_even_rank_bounds_variable_certs
      N P R eventsByBase B hP heven hodd
      (satEventVariableCerts_of_admissibleFor_uniform
        P r s rhoOf eventsByBase hr hs hadm hrho hevent hpBase hbase)

theorem reducedBaseExceptionalCountGeTwo_rat_le_of_baseSatEvent_signed_rank_bounds_admissibleFor_uniform_certs
    (N P R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Nat → ℚ)
    (hP : 0 < P) (hr : 0 < r) (hs : 0 < s)
    (hrank : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ k) *
          ((∑ t ∈ (eventsByBase b).powersetCard k,
              baseSatEventCommonHitCountUpTo N P b t : Nat) : Int) : ℚ) ≤
            B b k)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b →
      event.e = r * s ^ 2)
    (hpBase : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.p P)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus]) :
    (reducedBaseExceptionalCountGeTwo N P : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k := by
  exact
    reducedBaseExceptionalCountGeTwo_rat_le_of_base_satEvent_signed_rank_bounds_variable_certs
      N P R eventsByBase B hP hrank
      (satEventVariableCerts_of_admissibleFor_uniform
        P r s rhoOf eventsByBase hr hs hadm hrho hevent hpBase hbase)

theorem reducedBaseExceptionalCountGeTwo_rat_le_of_baseSatEvent_even_rank_bounds_largePrime_admissibleFor_uniform_certs
    (N P R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Nat → ℚ)
    (hP : 0 < P) (hr : 0 < r) (hs : 0 < s)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Even k →
        ((∑ t ∈ (eventsByBase b).powersetCard k,
            baseSatEventCommonHitCountUpTo N P b t : Nat) : ℚ) ≤ B b k)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Odd k → 0 ≤ B b k)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b →
      event.e = r * s ^ 2)
    (hlargeBase : ∀ b event, event ∈ eventsByBase b →
      P < event.p)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus]) :
    (reducedBaseExceptionalCountGeTwo N P : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k := by
  exact
    reducedBaseExceptionalCountGeTwo_rat_le_of_baseSatEvent_even_rank_bounds_admissibleFor_uniform_certs
      N P R r s rhoOf eventsByBase B hP hr hs heven hodd hadm hrho hevent
      (fun b event heventMem =>
        prime_coprime_of_lt event.p P (hadm b event heventMem).1 hP
          (hlargeBase b event heventMem))
      hbase

theorem reducedBaseExceptionalCountGeTwo_rat_le_of_baseSatEvent_signed_rank_bounds_largePrime_admissibleFor_uniform_certs
    (N P R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Nat → ℚ)
    (hP : 0 < P) (hr : 0 < r) (hs : 0 < s)
    (hrank : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ k) *
          ((∑ t ∈ (eventsByBase b).powersetCard k,
              baseSatEventCommonHitCountUpTo N P b t : Nat) : Int) : ℚ) ≤
            B b k)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b →
      event.e = r * s ^ 2)
    (hlargeBase : ∀ b event, event ∈ eventsByBase b →
      P < event.p)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus]) :
    (reducedBaseExceptionalCountGeTwo N P : ℚ) ≤
      ∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k := by
  exact
    reducedBaseExceptionalCountGeTwo_rat_le_of_baseSatEvent_signed_rank_bounds_admissibleFor_uniform_certs
      N P R r s rhoOf eventsByBase B hP hr hs hrank hadm hrho hevent
      (fun b event heventMem =>
        prime_coprime_of_lt event.p P (hadm b event heventMem).1 hP
          (hlargeBase b event heventMem))
      hbase

theorem forall_esRepresentable_ge_two_of_baseSatEvent_even_rank_budget_lt_one_admissible_uniform_certs_of_one_lt_P
    (N P R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hP : 1 < P) (hr : 0 < r) (hs : 0 < s)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Even k →
        ((∑ t ∈ (eventsByBase b).powersetCard k,
            baseSatEventCommonHitCountUpTo N P b t : Nat) : ℚ) ≤ B b k)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Odd k → 0 ≤ B b k)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b →
      event.e = r * s ^ 2)
    (hpBase : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.p P)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) < 1) :
    ∀ n ∈ reducedBasePointSet N P, 2 ≤ n → esRepresentable n := by
  exact
    forall_esRepresentable_ge_two_of_base_satEvent_even_rank_budget_lt_one_variable_certs_of_one_lt_P
      N P R eventsByBase B hP heven hodd
      (satEventVariableCerts_of_admissibleFor_uniform
        P r s rhoOf eventsByBase hr hs hadm hrho hevent hpBase hbase)
      hbudget

theorem forall_esRepresentable_ge_two_of_baseSatEvent_signed_rank_budget_lt_one_admissible_uniform_certs_of_one_lt_P
    (N P R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hP : 1 < P) (hr : 0 < r) (hs : 0 < s)
    (hrank : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ k) *
          ((∑ t ∈ (eventsByBase b).powersetCard k,
              baseSatEventCommonHitCountUpTo N P b t : Nat) : Int) : ℚ) ≤
            B b k)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b →
      event.e = r * s ^ 2)
    (hpBase : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.p P)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) < 1) :
    ∀ n ∈ reducedBasePointSet N P, 2 ≤ n → esRepresentable n := by
  exact
    forall_esRepresentable_ge_two_of_base_satEvent_signed_rank_budget_lt_one_variable_certs_of_one_lt_P
      N P R eventsByBase B hP hrank
      (satEventVariableCerts_of_admissibleFor_uniform
        P r s rhoOf eventsByBase hr hs hadm hrho hevent hpBase hbase)
      hbudget

theorem forall_esRepresentable_ge_two_of_baseSatEvent_even_rank_budget_lt_one_largePrime_admissible_uniform_certs_of_one_lt_P
    (N P R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hP : 1 < P) (hr : 0 < r) (hs : 0 < s)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Even k →
        ((∑ t ∈ (eventsByBase b).powersetCard k,
            baseSatEventCommonHitCountUpTo N P b t : Nat) : ℚ) ≤ B b k)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Odd k → 0 ≤ B b k)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b →
      event.e = r * s ^ 2)
    (hlargeBase : ∀ b event, event ∈ eventsByBase b →
      P < event.p)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) < 1) :
    ∀ n ∈ reducedBasePointSet N P, 2 ≤ n → esRepresentable n := by
  exact
    forall_esRepresentable_ge_two_of_base_satEvent_even_rank_budget_lt_one_variable_certs_of_one_lt_P
      N P R eventsByBase B hP heven hodd
      (satEventVariableCerts_of_admissibleFor_largePrime_uniform
        P r s rhoOf eventsByBase (Nat.lt_trans Nat.zero_lt_one hP)
        hr hs hadm hrho hevent hlargeBase hbase)
      hbudget

theorem forall_esRepresentable_ge_two_of_baseSatEvent_signed_rank_budget_lt_one_largePrime_admissible_uniform_certs_of_one_lt_P
    (N P R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hP : 1 < P) (hr : 0 < r) (hs : 0 < s)
    (hrank : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ k) *
          ((∑ t ∈ (eventsByBase b).powersetCard k,
              baseSatEventCommonHitCountUpTo N P b t : Nat) : Int) : ℚ) ≤
            B b k)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b →
      event.e = r * s ^ 2)
    (hlargeBase : ∀ b event, event ∈ eventsByBase b →
      P < event.p)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) < 1) :
    ∀ n ∈ reducedBasePointSet N P, 2 ≤ n → esRepresentable n := by
  exact
    forall_esRepresentable_ge_two_of_base_satEvent_signed_rank_budget_lt_one_variable_certs_of_one_lt_P
      N P R eventsByBase B hP hrank
      (satEventVariableCerts_of_admissibleFor_largePrime_uniform
        P r s rhoOf eventsByBase (Nat.lt_trans Nat.zero_lt_one hP)
        hr hs hadm hrho hevent hlargeBase hbase)
      hbudget

theorem forall_esRepresentable_up_to_of_smoothLiftSmall_and_badExceptional_zero_of_baseSatEvent_even_rank_budget_lt_one_admissible_uniform_certs
    {Smooth Small Bad : Nat → Prop}
    (N M P R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Nat → ℚ)
    (hP : 1 < P) (hr : 0 < r) (hs : 0 < s)
    (hsplitExists :
      ∀ n : Nat, 0 < n → n ≤ N →
        ∃ s m : Nat,
          SmoothLiftSplit Smooth
            (fun m => m ∈ reducedBasePointSet M P) n s m)
    (hsmallGeTwo : ∀ m : Nat, 0 < m → ¬ Small m → 2 ≤ m)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Even k →
        ((∑ t ∈ (eventsByBase b).powersetCard k,
            baseSatEventCommonHitCountUpTo M P b t : Nat) : ℚ) ≤ B b k)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Odd k → 0 ≤ B b k)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b →
      event.e = r * s ^ 2)
    (hpBase : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.p P)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) < 1)
    (hsmallZero :
      smoothLiftSmallSplitCount Smooth
        (fun m => m ∈ reducedBasePointSet M P) Small N = 0)
    (hbadZero :
      smoothLiftBadExceptionalCofactorSplitCount Smooth
        (fun m => m ∈ reducedBasePointSet M P) Bad N = 0) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n := by
  have hcoverage :
      ∀ m : Nat, 2 ≤ m → m ∈ reducedBasePointSet M P →
        esRepresentable m := by
    intro m hmTwo hmReduced
    exact
      forall_esRepresentable_ge_two_of_baseSatEvent_even_rank_budget_lt_one_admissible_uniform_certs_of_one_lt_P
        M P R r s rhoOf eventsByBase B hP hr hs heven hodd hadm
        hrho hevent hpBase hbase hbudget m hmReduced hmTwo
  exact
    forall_esRepresentable_up_to_of_smoothLiftSmall_and_badExceptional_zero_of_ge_two_coverage
      (Smooth := Smooth)
      (Reduced := fun m => m ∈ reducedBasePointSet M P)
      (Small := Small) (Bad := Bad) (N := N)
      hsplitExists hcoverage hsmallGeTwo hsmallZero hbadZero

theorem forall_esRepresentable_up_to_of_smoothLiftSmall_and_badExceptional_zero_of_baseSatEvent_signed_rank_budget_lt_one_admissible_uniform_certs
    {Smooth Small Bad : Nat → Prop}
    (N M P R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Nat → ℚ)
    (hP : 1 < P) (hr : 0 < r) (hs : 0 < s)
    (hsplitExists :
      ∀ n : Nat, 0 < n → n ≤ N →
        ∃ s m : Nat,
          SmoothLiftSplit Smooth
            (fun m => m ∈ reducedBasePointSet M P) n s m)
    (hsmallGeTwo : ∀ m : Nat, 0 < m → ¬ Small m → 2 ≤ m)
    (hrank : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ k) *
          ((∑ t ∈ (eventsByBase b).powersetCard k,
              baseSatEventCommonHitCountUpTo M P b t : Nat) : Int) : ℚ) ≤
            B b k)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b →
      event.e = r * s ^ 2)
    (hpBase : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.p P)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) < 1)
    (hsmallZero :
      smoothLiftSmallSplitCount Smooth
        (fun m => m ∈ reducedBasePointSet M P) Small N = 0)
    (hbadZero :
      smoothLiftBadExceptionalCofactorSplitCount Smooth
        (fun m => m ∈ reducedBasePointSet M P) Bad N = 0) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n := by
  have hcoverage :
      ∀ m : Nat, 2 ≤ m → m ∈ reducedBasePointSet M P →
        esRepresentable m := by
    intro m hmTwo hmReduced
    exact
      forall_esRepresentable_ge_two_of_baseSatEvent_signed_rank_budget_lt_one_admissible_uniform_certs_of_one_lt_P
        M P R r s rhoOf eventsByBase B hP hr hs hrank hadm
        hrho hevent hpBase hbase hbudget m hmReduced hmTwo
  exact
    forall_esRepresentable_up_to_of_smoothLiftSmall_and_badExceptional_zero_of_ge_two_coverage
      (Smooth := Smooth)
      (Reduced := fun m => m ∈ reducedBasePointSet M P)
      (Small := Small) (Bad := Bad) (N := N)
      hsplitExists hcoverage hsmallGeTwo hsmallZero hbadZero

theorem forall_esRepresentable_up_to_of_smoothLiftSmall_and_badExceptional_zero_of_baseSatEvent_even_rank_budget_lt_one_largePrime_admissible_uniform_certs
    {Smooth Small Bad : Nat → Prop}
    (N M P R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Nat → ℚ)
    (hP : 1 < P) (hr : 0 < r) (hs : 0 < s)
    (hsplitExists :
      ∀ n : Nat, 0 < n → n ≤ N →
        ∃ s m : Nat,
          SmoothLiftSplit Smooth
            (fun m => m ∈ reducedBasePointSet M P) n s m)
    (hsmallGeTwo : ∀ m : Nat, 0 < m → ¬ Small m → 2 ≤ m)
    (heven : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Even k →
        ((∑ t ∈ (eventsByBase b).powersetCard k,
            baseSatEventCommonHitCountUpTo M P b t : Nat) : ℚ) ≤ B b k)
    (hodd : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1), Odd k → 0 ≤ B b k)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b →
      event.e = r * s ^ 2)
    (hlargeBase : ∀ b event, event ∈ eventsByBase b →
      P < event.p)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) < 1)
    (hsmallZero :
      smoothLiftSmallSplitCount Smooth
        (fun m => m ∈ reducedBasePointSet M P) Small N = 0)
    (hbadZero :
      smoothLiftBadExceptionalCofactorSplitCount Smooth
        (fun m => m ∈ reducedBasePointSet M P) Bad N = 0) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n := by
  have hcoverage :
      ∀ m : Nat, 2 ≤ m → m ∈ reducedBasePointSet M P →
        esRepresentable m := by
    intro m hmTwo hmReduced
    exact
      forall_esRepresentable_ge_two_of_baseSatEvent_even_rank_budget_lt_one_largePrime_admissible_uniform_certs_of_one_lt_P
        M P R r s rhoOf eventsByBase B hP hr hs heven hodd hadm
        hrho hevent hlargeBase hbase hbudget m hmReduced hmTwo
  exact
    forall_esRepresentable_up_to_of_smoothLiftSmall_and_badExceptional_zero_of_ge_two_coverage
      (Smooth := Smooth)
      (Reduced := fun m => m ∈ reducedBasePointSet M P)
      (Small := Small) (Bad := Bad) (N := N)
      hsplitExists hcoverage hsmallGeTwo hsmallZero hbadZero

theorem forall_esRepresentable_up_to_of_smoothLiftSmall_and_badExceptional_zero_of_baseSatEvent_signed_rank_budget_lt_one_largePrime_admissible_uniform_certs
    {Smooth Small Bad : Nat → Prop}
    (N M P R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent) (B : Nat → Nat → ℚ)
    (hP : 1 < P) (hr : 0 < r) (hs : 0 < s)
    (hsplitExists :
      ∀ n : Nat, 0 < n → n ≤ N →
        ∃ s m : Nat,
          SmoothLiftSplit Smooth
            (fun m => m ∈ reducedBasePointSet M P) n s m)
    (hsmallGeTwo : ∀ m : Nat, 0 < m → ¬ Small m → 2 ≤ m)
    (hrank : ∀ b ∈ reducedResiduesMod P,
      ∀ k ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ k) *
          ((∑ t ∈ (eventsByBase b).powersetCard k,
              baseSatEventCommonHitCountUpTo M P b t : Nat) : Int) : ℚ) ≤
            B b k)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor P rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b →
      event.e = r * s ^ 2)
    (hlargeBase : ∀ b event, event ∈ eventsByBase b →
      P < event.p)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hbudget :
      (∑ b ∈ reducedResiduesMod P,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) < 1)
    (hsmallZero :
      smoothLiftSmallSplitCount Smooth
        (fun m => m ∈ reducedBasePointSet M P) Small N = 0)
    (hbadZero :
      smoothLiftBadExceptionalCofactorSplitCount Smooth
        (fun m => m ∈ reducedBasePointSet M P) Bad N = 0) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n := by
  have hcoverage :
      ∀ m : Nat, 2 ≤ m → m ∈ reducedBasePointSet M P →
        esRepresentable m := by
    intro m hmTwo hmReduced
    exact
      forall_esRepresentable_ge_two_of_baseSatEvent_signed_rank_budget_lt_one_largePrime_admissible_uniform_certs_of_one_lt_P
        M P R r s rhoOf eventsByBase B hP hr hs hrank hadm
        hrho hevent hlargeBase hbase hbudget m hmReduced hmTwo
  exact
    forall_esRepresentable_up_to_of_smoothLiftSmall_and_badExceptional_zero_of_ge_two_coverage
      (Smooth := Smooth)
      (Reduced := fun m => m ∈ reducedBasePointSet M P)
      (Small := Small) (Bad := Bad) (N := N)
      hsplitExists hcoverage hsmallGeTwo hsmallZero hbadZero

theorem forall_esRepresentable_up_to_of_baseSatEvent_even_rank_budget_lt_one_uniform_certs_mod_210
    (N R r s : Nat) (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hr : 0 < r) (hs : 0 < s)
    (heven : ∀ b ∈ reducedResiduesMod 210,
      ∀ k ∈ Finset.range (2 * R + 1), Even k →
        ((∑ t ∈ (eventsByBase b).powersetCard k,
            baseSatEventCommonHitCountUpTo N 210 b t : Nat) : ℚ) ≤ B b k)
    (hodd : ∀ b ∈ reducedResiduesMod 210,
      ∀ k ∈ Finset.range (2 * R + 1), Odd k → 0 ≤ B b k)
    (hevent : ∀ b event, event ∈ eventsByBase b →
      event.e = r * s ^ 2)
    (hcop : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.dMinus (event.dPlus * event.p))
    (hdMinusDvd210 : ∀ b event, event ∈ eventsByBase b →
      event.dMinus ∣ 210)
    (hsmall : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hprogression : ∀ b event, event ∈ eventsByBase b →
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1)
    (hbudget :
      (∑ b ∈ reducedResiduesMod 210,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) < 1) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n := by
  exact
    forall_esRepresentable_up_to_of_base_satEvent_even_rank_budget_lt_one_variable_certs_mod_210
      N R eventsByBase B heven hodd
      (by
        intro b event heventMem
        exact
          ⟨r, s, hr, hs, hevent b event heventMem,
            hcop b event heventMem, hdMinusDvd210 b event heventMem,
            hsmall b event heventMem, hprogression b event heventMem⟩)
      hbudget

theorem forall_esRepresentable_up_to_of_baseSatEvent_signed_rank_budget_lt_one_uniform_certs_mod_210
    (N R r s : Nat) (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hr : 0 < r) (hs : 0 < s)
    (hrank : ∀ b ∈ reducedResiduesMod 210,
      ∀ k ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ k) *
          ((∑ t ∈ (eventsByBase b).powersetCard k,
              baseSatEventCommonHitCountUpTo N 210 b t : Nat) : Int) : ℚ) ≤
            B b k)
    (hevent : ∀ b event, event ∈ eventsByBase b →
      event.e = r * s ^ 2)
    (hcop : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.dMinus (event.dPlus * event.p))
    (hdMinusDvd210 : ∀ b event, event ∈ eventsByBase b →
      event.dMinus ∣ 210)
    (hsmall : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hprogression : ∀ b event, event ∈ eventsByBase b →
      4 * (r * s) ∣ event.dMinus * (event.dPlus * event.p) + 1)
    (hbudget :
      (∑ b ∈ reducedResiduesMod 210,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) < 1) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n := by
  exact
    forall_esRepresentable_up_to_of_base_satEvent_signed_rank_budget_lt_one_variable_certs_mod_210
      N R eventsByBase B hrank
      (by
        intro b event heventMem
        exact
          ⟨r, s, hr, hs, hevent b event heventMem,
            hcop b event heventMem, hdMinusDvd210 b event heventMem,
            hsmall b event heventMem, hprogression b event heventMem⟩)
      hbudget

theorem forall_esRepresentable_up_to_of_baseSatEvent_even_rank_budget_lt_one_admissible_uniform_certs_mod_210
    (N R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hr : 0 < r) (hs : 0 < s)
    (heven : ∀ b ∈ reducedResiduesMod 210,
      ∀ k ∈ Finset.range (2 * R + 1), Even k →
        ((∑ t ∈ (eventsByBase b).powersetCard k,
            baseSatEventCommonHitCountUpTo N 210 b t : Nat) : ℚ) ≤ B b k)
    (hodd : ∀ b ∈ reducedResiduesMod 210,
      ∀ k ∈ Finset.range (2 * R + 1), Odd k → 0 ≤ B b k)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor 210 rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b →
      event.e = r * s ^ 2)
    (hpBase : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.p 210)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hbudget :
      (∑ b ∈ reducedResiduesMod 210,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) < 1) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n := by
  exact
    forall_esRepresentable_up_to_of_base_satEvent_even_rank_budget_lt_one_variable_certs_mod_210
      N R eventsByBase B heven hodd
      (satEventVariableCerts_of_admissibleFor_uniform
        210 r s rhoOf eventsByBase hr hs hadm hrho hevent hpBase hbase)
      hbudget

theorem forall_esRepresentable_up_to_of_baseSatEvent_signed_rank_budget_lt_one_admissible_uniform_certs_mod_210
    (N R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hr : 0 < r) (hs : 0 < s)
    (hrank : ∀ b ∈ reducedResiduesMod 210,
      ∀ k ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ k) *
          ((∑ t ∈ (eventsByBase b).powersetCard k,
              baseSatEventCommonHitCountUpTo N 210 b t : Nat) : Int) : ℚ) ≤
            B b k)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor 210 rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b →
      event.e = r * s ^ 2)
    (hpBase : ∀ b event, event ∈ eventsByBase b →
      Nat.Coprime event.p 210)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hbudget :
      (∑ b ∈ reducedResiduesMod 210,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) < 1) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n := by
  exact
    forall_esRepresentable_up_to_of_base_satEvent_signed_rank_budget_lt_one_variable_certs_mod_210
      N R eventsByBase B hrank
      (satEventVariableCerts_of_admissibleFor_uniform
        210 r s rhoOf eventsByBase hr hs hadm hrho hevent hpBase hbase)
      hbudget

theorem forall_esRepresentable_up_to_of_baseSatEvent_even_rank_budget_lt_one_largePrime_admissible_uniform_certs_mod_210
    (N R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hr : 0 < r) (hs : 0 < s)
    (heven : ∀ b ∈ reducedResiduesMod 210,
      ∀ k ∈ Finset.range (2 * R + 1), Even k →
        ((∑ t ∈ (eventsByBase b).powersetCard k,
            baseSatEventCommonHitCountUpTo N 210 b t : Nat) : ℚ) ≤ B b k)
    (hodd : ∀ b ∈ reducedResiduesMod 210,
      ∀ k ∈ Finset.range (2 * R + 1), Odd k → 0 ≤ B b k)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor 210 rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b →
      event.e = r * s ^ 2)
    (hlargeBase : ∀ b event, event ∈ eventsByBase b →
      210 < event.p)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hbudget :
      (∑ b ∈ reducedResiduesMod 210,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) < 1) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n := by
  exact
    forall_esRepresentable_up_to_of_base_satEvent_even_rank_budget_lt_one_variable_certs_mod_210
      N R eventsByBase B heven hodd
      (satEventVariableCerts_of_admissibleFor_largePrime_uniform
        210 r s rhoOf eventsByBase (by norm_num) hr hs
        hadm hrho hevent hlargeBase hbase)
      hbudget

theorem forall_esRepresentable_up_to_of_baseSatEvent_signed_rank_budget_lt_one_largePrime_admissible_uniform_certs_mod_210
    (N R r s : Nat) (rhoOf : Nat → Nat)
    (eventsByBase : Nat → Finset SatEvent)
    (B : Nat → Nat → ℚ)
    (hr : 0 < r) (hs : 0 < s)
    (hrank : ∀ b ∈ reducedResiduesMod 210,
      ∀ k ∈ Finset.range (2 * R + 1),
        (((-1 : Int) ^ k) *
          ((∑ t ∈ (eventsByBase b).powersetCard k,
              baseSatEventCommonHitCountUpTo N 210 b t : Nat) : Int) : ℚ) ≤
            B b k)
    (hadm : ∀ b event, event ∈ eventsByBase b →
      satEventAdmissibleFor 210 rhoOf event)
    (hrho : ∀ b event, event ∈ eventsByBase b →
      rhoOf event.e = r * s)
    (hevent : ∀ b event, event ∈ eventsByBase b →
      event.e = r * s ^ 2)
    (hlargeBase : ∀ b event, event ∈ eventsByBase b →
      210 < event.p)
    (hbase : ∀ b event, event ∈ eventsByBase b →
      b + 4 * event.e ≡ 0 [MOD event.dMinus])
    (hbudget :
      (∑ b ∈ reducedResiduesMod 210,
        ∑ k ∈ Finset.range (2 * R + 1), B b k) < 1) :
    ∀ n : Nat, 2 ≤ n → n ≤ N → esRepresentable n := by
  exact
    forall_esRepresentable_up_to_of_base_satEvent_signed_rank_budget_lt_one_variable_certs_mod_210
      N R eventsByBase B hrank
      (satEventVariableCerts_of_admissibleFor_largePrime_uniform
        210 r s rhoOf eventsByBase (by norm_num) hr hs
        hadm hrho hevent hlargeBase hbase)
      hbudget

theorem divisorFan_positive_unit_fractions_of_saturated_progression
    (n Q r s : Nat)
    (hn : 0 < n) (hr : 0 < r) (hs : 0 < s)
    (hprogression : 4 * (r * s) ∣ Q + 1)
    (hcong : Q ∣ n + 4 * (r * s ^ 2)) :
    ∃ a x y z : Nat,
      0 < a ∧ 4 * a = Q + 1 ∧
      0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (n : ℚ) =
        1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  exact fixedFan_positive_unit_fractions_of_saturated_progression
    4 n Q r s (by norm_num) hn hr hs hprogression hcong

theorem divisorFan_nat_certificate
    (n a e : Nat)
    (hn : 0 < n) (ha : 0 < a) (he : 0 < e)
    (hedvd : e ∣ a ^ 2)
    (hcong : qOf a ∣ n + 4 * e) :
    0 < fanX n a ∧
    0 < fanY n a e ∧
    0 < fanZ n a e ∧
    (4 : ℚ) / (n : ℚ) =
      1 / (fanX n a : ℚ) +
      1 / (fanY n a e : ℚ) +
      1 / (fanZ n a e : ℚ) := by
  have h := fixedFan_nat_certificate
    (m := 4) (n := n) (a := a) (e := e)
    (by norm_num) hn ha he hedvd (by
      simpa [fixedQ, qOf] using hcong)
  simpa [fixedFanX, fixedFanY, fixedFanZ, fixedQ, fanX, fanY, fanZ, qOf] using h

theorem divisorFan_nat_unit_fraction_identity
    (n a e : Nat)
    (hn : 0 < n) (ha : 0 < a) (he : 0 < e)
    (hedvd : e ∣ a ^ 2)
    (hcong : qOf a ∣ n + 4 * e) :
    (4 : ℚ) / (n : ℚ) =
      1 / (fanX n a : ℚ) +
      1 / (fanY n a e : ℚ) +
      1 / (fanZ n a e : ℚ) :=
  (divisorFan_nat_certificate n a e hn ha he hedvd hcong).2.2.2

theorem divisorFan_positive_unit_fractions
    (n a e : Nat)
    (hn : 0 < n) (ha : 0 < a) (he : 0 < e)
    (hedvd : e ∣ a ^ 2)
    (hcong : qOf a ∣ n + 4 * e) :
    ∃ x y z : Nat,
      0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (n : ℚ) =
        1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  rcases divisorFan_nat_certificate n a e hn ha he hedvd hcong with
    ⟨hx, hy, hz, hident⟩
  exact ⟨fanX n a, fanY n a e, fanZ n a e, hx, hy, hz, hident⟩

theorem fanWitness_esRepresentable
    (n a h : Nat) (hn : 0 < n)
    (hw : fanWitness n a h) :
    esRepresentable n := by
  rcases hw with ⟨ha, hh, hinterior, hcong⟩
  exact divisorFan_positive_unit_fractions n a h hn ha hh hinterior.1 hcong

theorem fanWitnessBool_true_esRepresentable
    (n a h : Nat) (hn : 0 < n)
    (hw : fanWitnessBool n a h = true) :
    esRepresentable n := by
  exact fanWitness_esRepresentable n a h hn ((fanWitnessBool_eq_true n a h).mp hw)

theorem boundaryDivisor_pos_dvd_square
    (a h : Nat) (ha : 0 < a) (hb : boundaryDivisor a h) :
    0 < h ∧ h ∣ a ^ 2 := by
  rcases hb with rfl | rfl | rfl
  · exact ⟨by norm_num, by simp⟩
  · exact ⟨ha, by
      use h
      ring⟩
  · exact ⟨pow_pos ha 2, by simp⟩

theorem divisorFan_positive_unit_fractions_of_boundary
    (n a h : Nat)
    (hn : 0 < n) (ha : 0 < a)
    (hb : boundaryDivisor a h)
    (hcong : qOf a ∣ n + 4 * h) :
    ∃ x y z : Nat,
      0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (n : ℚ) =
        1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  rcases boundaryDivisor_pos_dvd_square a h ha hb with ⟨hh, hdvd⟩
  exact divisorFan_positive_unit_fractions n a h hn ha hh hdvd hcong

theorem divisorFan_positive_unit_fractions_boundary_one
    (n a : Nat)
    (hn : 0 < n) (ha : 0 < a)
    (hcong : qOf a ∣ n + 4) :
    ∃ x y z : Nat,
      0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (n : ℚ) =
        1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  simpa using
    divisorFan_positive_unit_fractions_of_boundary
      n a 1 hn ha (Or.inl rfl) hcong

theorem esRepresentable_of_two_mod_three
    (n : Nat) (hn : 0 < n) (hmod : n % 3 = 2) :
    esRepresentable n := by
  rcases divisorFan_positive_unit_fractions_boundary_one
      n 1 hn (by norm_num)
      (by
        unfold qOf
        exact ⟨(n + 4) / 3, by omega⟩) with
    ⟨x, y, z, hx, hy, hz, hident⟩
  exact ⟨x, y, z, hx, hy, hz, hident⟩

theorem esRepresentable_of_not_one_mod_three
    (n : Nat) (hn : 2 ≤ n) (hmod : n % 3 ≠ 1) :
    esRepresentable n := by
  by_cases hzero : n % 3 = 0
  · exact esRepresentable_of_dvd_three n (lt_of_lt_of_le (by norm_num) hn)
      (Nat.dvd_iff_mod_eq_zero.mpr hzero)
  · have htwo : n % 3 = 2 := by
      have hlt : n % 3 < 3 := Nat.mod_lt n (by norm_num)
      omega
    exact esRepresentable_of_two_mod_three n (lt_of_lt_of_le (by norm_num) hn) htwo

theorem divisorFan_positive_unit_fractions_boundary_a
    (n a : Nat)
    (hn : 0 < n) (ha : 0 < a)
    (hcong : qOf a ∣ n + 4 * a) :
    ∃ x y z : Nat,
      0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (n : ℚ) =
        1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  exact
    divisorFan_positive_unit_fractions_of_boundary
      n a a hn ha (Or.inr (Or.inl rfl)) hcong

theorem divisorFan_positive_unit_fractions_boundary_square
    (n a : Nat)
    (hn : 0 < n) (ha : 0 < a)
    (hcong : qOf a ∣ n + 4 * a ^ 2) :
    ∃ x y z : Nat,
      0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (n : ℚ) =
        1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  exact
    divisorFan_positive_unit_fractions_of_boundary
      n a (a ^ 2) hn ha (Or.inr (Or.inr rfl)) hcong

theorem qOf_add_one_of_pos (a : Nat) (ha : 0 < a) :
    qOf a + 1 = 4 * a := by
  unfold qOf
  omega

theorem qOf_pos_of_pos (a : Nat) (ha : 0 < a) : 0 < qOf a := by
  unfold qOf
  omega

theorem qOf_cast_of_pos (a : Nat) (ha : 0 < a) :
    (qOf a : ℚ) = 4 * (a : ℚ) - 1 := by
  have hcast : (qOf a : ℚ) + 1 = 4 * (a : ℚ) := by
    exact_mod_cast qOf_add_one_of_pos a ha
  linarith

theorem interiorDivisor_pos_of_pos
    (a h : Nat) (ha : 0 < a) (hi : interiorDivisor a h) :
    0 < h := by
  rcases hi with ⟨hdvd, _hneOne, _hneA, _hneSq⟩
  rcases hdvd with ⟨k, hk⟩
  by_contra hnot
  have hzero : h = 0 := Nat.eq_zero_of_not_pos hnot
  have haSqPos : 0 < a ^ 2 := pow_pos ha 2
  rw [hzero, zero_mul] at hk
  omega

theorem interiorDivisor_pos_dvd_square
    (a h : Nat) (ha : 0 < a) (hi : interiorDivisor a h) :
    0 < h ∧ h ∣ a ^ 2 :=
  ⟨interiorDivisor_pos_of_pos a h ha hi, hi.1⟩

theorem completeFan_decomposition_of_interiorDivisor
    (a h : Nat) (ha : 0 < a) (hi : interiorDivisor a h) :
    ∃ d e A : Nat,
      0 < d ∧ 0 < e ∧ 0 < A ∧
      a = d * e * A ∧ h = d ^ 2 * e := by
  exact completeFan_decomposition_of_dvd_square a h ha
    (interiorDivisor_pos_of_pos a h ha hi) hi.1

theorem fanCongruence_iff_typeIIEquation_of_divisor
    (p a h : Nat) (ha : 0 < a) (hh : 0 < h)
    (hdvd : h ∣ a ^ 2) :
    fanCongruence p a h ↔
      ∃ d e A B : Nat,
        0 < d ∧ 0 < e ∧ 0 < A ∧
        a = d * e * A ∧ h = d ^ 2 * e ∧
        typeIIEquation p d e A B := by
  constructor
  · intro hcong
    exact typeIIEquation_of_completeFan p a h ha hh hdvd hcong
  · rintro ⟨d, e, A, B, hd, he, hA, haeq, hheq, hB⟩
    have hcong :=
      completeFan_congruence_of_typeIIEquation_decomposition
        p d e A B hd he hA hB
    simpa [fanCongruence, haeq, hheq] using hcong

theorem fanCongruence_iff_positive_first_denominator_certificate_of_divisor
    (p a h : Nat) (hp : 0 < p) (ha : 0 < a) (hh : 0 < h)
    (hdvd : h ∣ a ^ 2) :
    fanCongruence p a h ↔
      ∃ d e A B : Nat,
        0 < d ∧ 0 < e ∧ 0 < A ∧ 0 < B ∧
        a = d * e * A ∧ h = d ^ 2 * e ∧
        typeIIEquation p d e A B ∧
        typeIIX p d e A = p * a ∧
        0 < p * a ∧
        0 < typeIIY p e A B ∧
        0 < typeIIZ d e B ∧
        (4 : ℚ) / (p : ℚ) =
          1 / ((p * a : Nat) : ℚ) +
          1 / (typeIIY p e A B : ℚ) +
          1 / (typeIIZ d e B : ℚ) := by
  constructor
  · intro hcong
    rcases completeFan_first_denominator_certificate
        p a h hp ha hh hdvd hcong with
      ⟨d, e, A, B, hd, he, hA, hBpos, haeq, hheq, hBlin, hxEq,
        _hx, hy, hz, hident⟩
    exact ⟨d, e, A, B, hd, he, hA, hBpos, haeq, hheq, hBlin, hxEq,
      Nat.mul_pos hp ha, hy, hz, hident⟩
  · rintro ⟨d, e, A, B, hd, he, hA, _hBpos, haeq, hheq, hBlin, _hxEq,
      _hpa, _hy, _hz, _hident⟩
    have hcong :=
      completeFan_congruence_of_typeIIEquation_decomposition
        p d e A B hd he hA hBlin
    simpa [fanCongruence, haeq, hheq] using hcong

theorem typeIIEquation_of_interior_fanCongruence
    (p a h : Nat) (ha : 0 < a)
    (hi : interiorDivisor a h) (hcong : fanCongruence p a h) :
    ∃ d e A B : Nat,
      0 < d ∧ 0 < e ∧ 0 < A ∧
      a = d * e * A ∧ h = d ^ 2 * e ∧
      typeIIEquation p d e A B := by
  exact typeIIEquation_of_completeFan p a h ha
    (interiorDivisor_pos_of_pos a h ha hi) hi.1 hcong

theorem typeIIEquation_of_boundary_fanCongruence
    (p a h : Nat) (ha : 0 < a)
    (hb : boundaryDivisor a h) (hcong : fanCongruence p a h) :
    ∃ d e A B : Nat,
      0 < d ∧ 0 < e ∧ 0 < A ∧
      a = d * e * A ∧ h = d ^ 2 * e ∧
      typeIIEquation p d e A B := by
  rcases boundaryDivisor_pos_dvd_square a h ha hb with ⟨hh, hdvd⟩
  exact typeIIEquation_of_completeFan p a h ha hh hdvd hcong

theorem completeFan_first_denominator_certificate_of_interior
    (p a h : Nat) (hp : 0 < p) (ha : 0 < a)
    (hi : interiorDivisor a h) (hcong : fanCongruence p a h) :
    ∃ d e A B : Nat,
      0 < d ∧ 0 < e ∧ 0 < A ∧ 0 < B ∧
      a = d * e * A ∧ h = d ^ 2 * e ∧
      typeIIEquation p d e A B ∧
      typeIIX p d e A = p * a ∧
      0 < typeIIX p d e A ∧
      0 < typeIIY p e A B ∧
      0 < typeIIZ d e B ∧
      (4 : ℚ) / (p : ℚ) =
        1 / ((p * a : Nat) : ℚ) +
        1 / (typeIIY p e A B : ℚ) +
        1 / (typeIIZ d e B : ℚ) := by
  exact completeFan_first_denominator_certificate p a h hp ha
    (interiorDivisor_pos_of_pos a h ha hi) hi.1 hcong

theorem completeFan_first_denominator_certificate_of_boundary
    (p a h : Nat) (hp : 0 < p) (ha : 0 < a)
    (hb : boundaryDivisor a h) (hcong : fanCongruence p a h) :
    ∃ d e A B : Nat,
      0 < d ∧ 0 < e ∧ 0 < A ∧ 0 < B ∧
      a = d * e * A ∧ h = d ^ 2 * e ∧
      typeIIEquation p d e A B ∧
      typeIIX p d e A = p * a ∧
      0 < typeIIX p d e A ∧
      0 < typeIIY p e A B ∧
      0 < typeIIZ d e B ∧
      (4 : ℚ) / (p : ℚ) =
        1 / ((p * a : Nat) : ℚ) +
        1 / (typeIIY p e A B : ℚ) +
        1 / (typeIIZ d e B : ℚ) := by
  rcases boundaryDivisor_pos_dvd_square a h ha hb with ⟨hh, hdvd⟩
  exact completeFan_first_denominator_certificate p a h hp ha hh hdvd hcong

theorem divisorFan_nat_certificate_of_interior
    (n a h : Nat) (hn : 0 < n) (ha : 0 < a)
    (hi : interiorDivisor a h) (hcong : fanCongruence n a h) :
    0 < fanX n a ∧
    0 < fanY n a h ∧
    0 < fanZ n a h ∧
    (4 : ℚ) / (n : ℚ) =
      1 / (fanX n a : ℚ) +
      1 / (fanY n a h : ℚ) +
      1 / (fanZ n a h : ℚ) := by
  exact divisorFan_nat_certificate n a h hn ha
    (interiorDivisor_pos_of_pos a h ha hi) hi.1 hcong

theorem divisorFan_nat_certificate_of_boundary
    (n a h : Nat) (hn : 0 < n) (ha : 0 < a)
    (hb : boundaryDivisor a h) (hcong : fanCongruence n a h) :
    0 < fanX n a ∧
    0 < fanY n a h ∧
    0 < fanZ n a h ∧
    (4 : ℚ) / (n : ℚ) =
      1 / (fanX n a : ℚ) +
      1 / (fanY n a h : ℚ) +
      1 / (fanZ n a h : ℚ) := by
  rcases boundaryDivisor_pos_dvd_square a h ha hb with ⟨hh, hdvd⟩
  exact divisorFan_nat_certificate n a h hn ha hh hdvd hcong

theorem esRepresentable_of_interior_fanCongruence
    (n a h : Nat) (hn : 0 < n) (ha : 0 < a)
    (hi : interiorDivisor a h) (hcong : fanCongruence n a h) :
    esRepresentable n := by
  rcases divisorFan_nat_certificate_of_interior n a h hn ha hi hcong with
    ⟨hx, hy, hz, hident⟩
  exact ⟨fanX n a, fanY n a h, fanZ n a h, hx, hy, hz, hident⟩

theorem esRepresentable_of_boundary_fanCongruence
    (n a h : Nat) (hn : 0 < n) (ha : 0 < a)
    (hb : boundaryDivisor a h) (hcong : fanCongruence n a h) :
    esRepresentable n := by
  rcases divisorFan_nat_certificate_of_boundary n a h hn ha hb hcong with
    ⟨hx, hy, hz, hident⟩
  exact ⟨fanX n a, fanY n a h, fanZ n a h, hx, hy, hz, hident⟩

theorem fanWitness_nat_certificate
    (n a h : Nat) (hn : 0 < n) (hw : fanWitness n a h) :
    0 < fanX n a ∧
    0 < fanY n a h ∧
    0 < fanZ n a h ∧
    (4 : ℚ) / (n : ℚ) =
      1 / (fanX n a : ℚ) +
      1 / (fanY n a h : ℚ) +
      1 / (fanZ n a h : ℚ) := by
  rcases hw with ⟨ha, _hh, hi, hcong⟩
  exact divisorFan_nat_certificate_of_interior n a h hn ha hi hcong

theorem fanWitness_completeFan_first_denominator_certificate
    (p a h : Nat) (hp : 0 < p) (hw : fanWitness p a h) :
    ∃ d e A B : Nat,
      0 < d ∧ 0 < e ∧ 0 < A ∧ 0 < B ∧
      a = d * e * A ∧ h = d ^ 2 * e ∧
      typeIIEquation p d e A B ∧
      typeIIX p d e A = p * a ∧
      0 < typeIIX p d e A ∧
      0 < typeIIY p e A B ∧
      0 < typeIIZ d e B ∧
      (4 : ℚ) / (p : ℚ) =
        1 / ((p * a : Nat) : ℚ) +
        1 / (typeIIY p e A B : ℚ) +
        1 / (typeIIZ d e B : ℚ) := by
  rcases hw with ⟨ha, _hh, hi, hcong⟩
  exact completeFan_first_denominator_certificate_of_interior p a h hp ha hi hcong

theorem fanWitnessBool_true_completeFan_first_denominator_certificate
    (p a h : Nat) (hp : 0 < p) (hw : fanWitnessBool p a h = true) :
    ∃ d e A B : Nat,
      0 < d ∧ 0 < e ∧ 0 < A ∧ 0 < B ∧
      a = d * e * A ∧ h = d ^ 2 * e ∧
      typeIIEquation p d e A B ∧
      typeIIX p d e A = p * a ∧
      0 < typeIIX p d e A ∧
      0 < typeIIY p e A B ∧
      0 < typeIIZ d e B ∧
      (4 : ℚ) / (p : ℚ) =
        1 / ((p * a : Nat) : ℚ) +
        1 / (typeIIY p e A B : ℚ) +
        1 / (typeIIZ d e B : ℚ) := by
  exact fanWitness_completeFan_first_denominator_certificate p a h hp
    ((fanWitnessBool_eq_true p a h).mp hw)

theorem divisorFan_hyperbola_of_fanCongruence
    (n a h : Nat) (hn : 0 < n) (ha : 0 < a) (hh : 0 < h)
    (hdvd : h ∣ a ^ 2) (hcong : fanCongruence n a h) :
    (qOf a : ℚ) * (fanY n a h : ℚ) * (fanZ n a h : ℚ) =
      ((a * n : Nat) : ℚ) *
        ((fanY n a h : ℚ) + (fanZ n a h : ℚ)) := by
  rcases divisorFan_nat_certificate n a h hn ha hh hdvd hcong with
    ⟨_hx, hy, hz, hident⟩
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
  have hyQ : (fanY n a h : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hy)
  have hzQ : (fanZ n a h : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hz)
  simp [fanX, Nat.cast_mul] at hident
  rw [qOf_cast_of_pos a ha]
  field_simp [hnQ, haQ, hyQ, hzQ] at hident
  have hnPosQ : 0 < (n : ℚ) := by exact_mod_cast hn
  have hmul :
      ((4 * (a : ℚ) - 1) * (fanY n a h : ℚ) * (fanZ n a h : ℚ)) *
          (n : ℚ) =
        (((a * n : Nat) : ℚ) *
          ((fanY n a h : ℚ) + (fanZ n a h : ℚ))) * (n : ℚ) := by
    ring_nf at hident ⊢
    norm_num [Nat.cast_mul] at hident ⊢
    nlinarith [hident]
  ring_nf at hmul ⊢
  norm_num [Nat.cast_mul] at hmul ⊢
  nlinarith [hmul, hnPosQ]

theorem divisorFan_product_curve_of_fanCongruence
    (n a h : Nat) (hn : 0 < n) (ha : 0 < a) (hh : 0 < h)
    (hdvd : h ∣ a ^ 2) (hcong : fanCongruence n a h) :
    ((qOf a : ℚ) * (fanY n a h : ℚ) - ((a * n : Nat) : ℚ)) *
      ((qOf a : ℚ) * (fanZ n a h : ℚ) - ((a * n : Nat) : ℚ)) =
        ((a * n : Nat) : ℚ) ^ 2 := by
  exact fan_product_of_hyperbola
    (A := ((a * n : Nat) : ℚ)) (q := (qOf a : ℚ))
    (y := (fanY n a h : ℚ)) (z := (fanZ n a h : ℚ))
    (divisorFan_hyperbola_of_fanCongruence n a h hn ha hh hdvd hcong)

theorem divisorFan_hyperbola_of_interior_fanCongruence
    (n a h : Nat) (hn : 0 < n) (ha : 0 < a)
    (hi : interiorDivisor a h) (hcong : fanCongruence n a h) :
    (qOf a : ℚ) * (fanY n a h : ℚ) * (fanZ n a h : ℚ) =
      ((a * n : Nat) : ℚ) *
        ((fanY n a h : ℚ) + (fanZ n a h : ℚ)) := by
  exact divisorFan_hyperbola_of_fanCongruence n a h hn ha
    (interiorDivisor_pos_of_pos a h ha hi) hi.1 hcong

theorem divisorFan_product_curve_of_boundary_fanCongruence
    (n a h : Nat) (hn : 0 < n) (ha : 0 < a)
    (hb : boundaryDivisor a h) (hcong : fanCongruence n a h) :
    ((qOf a : ℚ) * (fanY n a h : ℚ) - ((a * n : Nat) : ℚ)) *
      ((qOf a : ℚ) * (fanZ n a h : ℚ) - ((a * n : Nat) : ℚ)) =
        ((a * n : Nat) : ℚ) ^ 2 := by
  rcases boundaryDivisor_pos_dvd_square a h ha hb with ⟨hh, hdvd⟩
  exact divisorFan_product_curve_of_fanCongruence n a h hn ha hh hdvd hcong

def fixedFanESBool (m n a e : Nat) : Bool :=
  fixedCrossBool m n (fixedFanX n a) (fixedFanY m n a e) (fixedFanZ m n a e)

example : fixedQ 5 2 = 9 := by
  native_decide

example : fixedQ 7 1 = 6 := by
  native_decide

example : fixedQ 11 1 = 10 := by
  native_decide

example : fixedFanY 5 4 2 1 = 1 := by
  native_decide

example : fixedFanZ 5 4 2 1 = 8 := by
  native_decide

example : fixedFanESBool 5 4 2 1 = true := by
  native_decide

example : fixedFanESBool 7 5 1 1 = true := by
  native_decide

example : fixedFanESBool 11 9 1 1 = true := by
  native_decide

/- Boundary proxy worked example factorizations. -/

example : 4 * 2521 + 1 = 5 * 2017 := by
  native_decide

example : (2521 + 1) / 2 = 13 * 97 := by
  native_decide

example : 2521 + 4 = 5 ^ 2 * 101 := by
  native_decide

/-!
## Finite boundary-ray divisor tests

For a target integer `m`, a boundary ray can only see divisors of the form
`4 * a - 1`, equivalently divisors congruent to `3` modulo `4`.  These finite
checks support the manuscript's distinction between the boundary `S1` proxy and
literal failure of the three boundary-ray divisibility tests.
-/

def hasDivisorThreeModFourBool (m : Nat) : Bool :=
  (List.range (m + 1)).any
    (fun d => decide (1 < d) && (d % 4 == 3) && (m % d == 0))

def boundaryProxyTargets (p : Nat) : List Nat :=
  [4 * p + 1, (p + 1) / 2, p + 4]

def boundaryProxyTargetsHaveThreeModFourDivisorBool (p : Nat) : Bool :=
  (boundaryProxyTargets p).any hasDivisorThreeModFourBool

example : boundaryProxyTargets 2521 = [10085, 1261, 2525] := by
  native_decide

example : boundaryProxyTargetsHaveThreeModFourDivisorBool 2521 = false := by
  native_decide

example : boundaryDivisorBool 12 16 = false := by
  native_decide

example : fanWitnessBool 2521 12 16 = true := by
  native_decide

example : boundaryProxyTargets 97 = [389, 49, 101] := by
  native_decide

example : hasDivisorThreeModFourBool ((97 + 1) / 2) = true := by
  native_decide

example : qOf 2 = 7 := by
  native_decide

example : boundaryDivisorBool 2 2 = true := by
  native_decide

example : fanCongruence 97 2 2 := by
  unfold fanCongruence qOf
  norm_num

/- Saved verifier rows: each reported prime attaining the current row maximum
   has a Lean-checked interior fan witness with the displayed h. -/

structure BoundaryRow where
  bound : Nat
  count : Nat
  maxa : Nat
  argp : Nat
  h : Nat
deriving Repr, DecidableEq

def savedRows : List BoundaryRow :=
  [{ bound := 100000, count := 184, maxa := 42, argp := 90841, h := 294 },
   { bound := 1000000, count := 1216, maxa := 84, argp := 954409, h := 504 },
   { bound := 10000000, count := 8196, maxa := 624, argp := 2031121, h := 576 },
   { bound := 100000000, count := 59079, maxa := 624, argp := 2031121, h := 576 }]

def rowFanWitness (row : BoundaryRow) : Bool :=
  fanWitnessBool row.argp row.maxa row.h

def maxNatList (xs : List Nat) : Nat :=
  xs.foldl Nat.max 0

example : savedRows.length = 4 := by
  native_decide

theorem savedRows_all_rowFanWitness :
    savedRows.all rowFanWitness = true := by
  native_decide

theorem savedRows_rowFanWitness
    (row : BoundaryRow) (hrow : row ∈ savedRows) :
    fanWitness row.argp row.maxa row.h := by
  simp [savedRows] at hrow
  rcases hrow with rfl | rfl | rfl | rfl
  · rw [← fanWitnessBool_eq_true]
    native_decide
  · rw [← fanWitnessBool_eq_true]
    native_decide
  · rw [← fanWitnessBool_eq_true]
    native_decide
  · rw [← fanWitnessBool_eq_true]
    native_decide

example : fanWitness 90841 42 294 := by
  rw [← fanWitnessBool_eq_true]
  native_decide

example : fanWitness 954409 84 504 := by
  rw [← fanWitnessBool_eq_true]
  native_decide

example : fanWitness 2031121 624 576 := by
  rw [← fanWitnessBool_eq_true]
  native_decide

example : esRepresentable 90841 := by
  exact fanWitnessBool_true_esRepresentable 90841 42 294 (by norm_num) (by native_decide)

example : esRepresentable 954409 := by
  exact fanWitnessBool_true_esRepresentable 954409 84 504 (by norm_num) (by native_decide)

example : esRepresentable 2031121 := by
  exact fanWitnessBool_true_esRepresentable 2031121 624 576 (by norm_num) (by native_decide)

theorem savedRows_argp_esRepresentable
    (row : BoundaryRow) (hrow : row ∈ savedRows) :
    esRepresentable row.argp := by
  simp [savedRows] at hrow
  rcases hrow with rfl | rfl | rfl | rfl
  · exact fanWitnessBool_true_esRepresentable 90841 42 294 (by norm_num) (by native_decide)
  · exact fanWitnessBool_true_esRepresentable 954409 84 504 (by norm_num) (by native_decide)
  · exact fanWitnessBool_true_esRepresentable 2031121 624 576 (by norm_num) (by native_decide)
  · exact fanWitnessBool_true_esRepresentable 2031121 624 576 (by norm_num) (by native_decide)

example : savedRows.map (fun row => row.count) = [184, 1216, 8196, 59079] := by
  native_decide

example : maxNatList (savedRows.map (fun row => row.maxa)) = 624 := by
  native_decide

example : fanESBool 90841 42 294 = true := by
  native_decide

example : fanESBool 954409 84 504 = true := by
  native_decide

example : fanESBool 2031121 624 576 = true := by
  native_decide

/- Boundary `S1`-proxy local envelope: these finite predicates encode the local
   necessary envelope used in the manuscript modulo 4, 8, and 9, not full `S1`
   membership or literal failure of every boundary ray. -/

def exactOneThreeFactorBool (n : Nat) : Bool :=
  (n % 3 == 0) && (n % 9 != 0)

def noLocalSintObstructionBool (n : Nat) : Bool :=
  (n % 4 != 3) && !exactOneThreeFactorBool n

def boundaryEnvelopeResidue72Bool (r : Nat) : Bool :=
  (r % 2 == 1) &&
  (r % 3 != 0) &&
  noLocalSintObstructionBool (r + 4) &&
  noLocalSintObstructionBool ((r + 1) / 2)

def boundaryEnvelopeResidues72 : List Nat :=
  (List.range 72).filter boundaryEnvelopeResidue72Bool

theorem boundaryEnvelopeResidues72_eq :
    boundaryEnvelopeResidues72 = [1, 25, 49] := by
  native_decide

theorem boundaryEnvelopeResidue72_mod24_of_mem
    (r : Nat) (hr : r ∈ boundaryEnvelopeResidues72) :
    r % 24 = 1 := by
  rw [boundaryEnvelopeResidues72_eq] at hr
  simp at hr
  rcases hr with rfl | rfl | rfl <;> native_decide

theorem boundaryEnvelopeResidue72_mod24
    (p : Nat)
    (hp : boundaryEnvelopeResidue72Bool (p % 72) = true) :
    p % 24 = 1 := by
  have hmem : p % 72 ∈ boundaryEnvelopeResidues72 := by
    unfold boundaryEnvelopeResidues72
    simp [hp, Nat.mod_lt p (by norm_num : 0 < 72)]
  have hres := boundaryEnvelopeResidue72_mod24_of_mem (p % 72) hmem
  simpa [Nat.mod_mod_of_dvd p (by norm_num : 24 ∣ 72)] using hres

example : boundaryEnvelopeResidues72.all (fun r => r % 24 == 1) = true := by
  native_decide

/- Boundary proxy envelope: the verifier's 24 residues are exactly the units
   modulo 840 that are congruent to 1 modulo 24. -/

def boundaryResidues : List Nat :=
  [1, 73, 97, 121, 169, 193, 241, 289, 313, 337, 361, 409,
   433, 457, 481, 529, 577, 601, 649, 673, 697, 769, 793, 817]

def isBoundaryResidue (r : Nat) : Prop :=
  r < 840 ∧ r % 24 = 1 ∧ Nat.gcd r 840 = 1

def isBoundaryResidueBool (r : Nat) : Bool :=
  decide (r < 840) && (r % 24 == 1) && (Nat.gcd r 840 == 1)

theorem isBoundaryResidueBool_eq_true (r : Nat) :
    isBoundaryResidueBool r = true ↔ isBoundaryResidue r := by
  simp only [isBoundaryResidueBool, isBoundaryResidue, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  constructor
  · intro H
    rcases H with ⟨⟨hrange, hmod⟩, hunit⟩
    exact ⟨hrange, hmod, hunit⟩
  · intro H
    rcases H with ⟨hrange, hmod, hunit⟩
    exact ⟨⟨hrange, hmod⟩, hunit⟩

def filteredBoundaryResidues : List Nat :=
  (List.range 840).filter isBoundaryResidueBool

theorem filteredBoundaryResidues_eq_boundaryResidues :
    filteredBoundaryResidues = boundaryResidues := by
  native_decide

theorem mem_boundaryResidues_iff_isBoundaryResidue (r : Nat) :
    r ∈ boundaryResidues ↔ isBoundaryResidue r := by
  classical
  rw [← filteredBoundaryResidues_eq_boundaryResidues]
  unfold filteredBoundaryResidues
  constructor
  · intro hr
    exact (isBoundaryResidueBool_eq_true r).mp (List.mem_filter.mp hr).2
  · intro hr
    exact List.mem_filter.mpr ⟨List.mem_range.mpr hr.1,
      (isBoundaryResidueBool_eq_true r).mpr hr⟩

example : boundaryResidues.length = 24 := by
  native_decide

example : boundaryResidues.all (fun r => r % 24 = 1) = true := by
  native_decide

example : boundaryResidues.all (fun r => Nat.gcd r 840 = 1) = true := by
  native_decide

example : boundaryResidues.all (fun r => r < 840) = true := by
  native_decide

example : boundaryResidues.contains (2031121 % 840) = true := by
  native_decide

def boundarySearchNoDivFrom : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | fuel + 1, n, d =>
      if n < d * d then true
      else if n % d = 0 then false
      else boundarySearchNoDivFrom fuel n (d + 1)

def boundarySearchPrimeBool (n : Nat) : Bool :=
  if n < 2 then false else boundarySearchNoDivFrom n n 2

def boundarySearchStripAll : Nat → Nat → Nat → Nat × Nat
  | 0, y, _ => (y, 0)
  | fuel + 1, y, d =>
      if 2 ≤ d ∧ y % d = 0 then
        let r := boundarySearchStripAll fuel (y / d) d
        (r.1, r.2 + 1)
      else (y, 0)

def boundarySearchS1Aux : Nat → Nat → Nat → Bool
  | 0, y, _ => decide (y % 4 ≠ 3)
  | fuel + 1, y, d =>
      if y ≤ 1 then true
      else if y < d * d then decide (y % 4 ≠ 3)
      else
        let r := boundarySearchStripAll y y d
        (decide (d % 4 ≠ 3) || decide (r.2 % 2 = 0)) &&
          boundarySearchS1Aux fuel r.1 (d + 1)

def boundarySearchS1Bool (x : Nat) : Bool :=
  boundarySearchS1Aux x x 2

def boundarySearchInteriorFanWitnessAtBool (p a : Nat) : Bool :=
  (List.range (a * a)).any (fun h => fanWitnessBool p a h)

def boundarySearchInteriorFanWitnessUpToBool (p Lmax : Nat) : Bool :=
  (List.range (Lmax + 1)).any
    (fun a => decide (2 ≤ a) && boundarySearchInteriorFanWitnessAtBool p a)

def boundarySearchProxyPrimeBool (p : Nat) : Bool :=
  boundarySearchPrimeBool p &&
    boundarySearchS1Bool (4 * p + 1) &&
    boundarySearchS1Bool ((p + 1) / 2) &&
    boundarySearchS1Bool (p + 4)

structure BoundarySearchProxyPrime (p : Nat) : Prop where
  primeTest : boundarySearchPrimeBool p = true
  fourPPlusOneS1 : boundarySearchS1Bool (4 * p + 1) = true
  halfPPlusOneS1 : boundarySearchS1Bool ((p + 1) / 2) = true
  pPlusFourS1 : boundarySearchS1Bool (p + 4) = true

theorem boundarySearchProxyPrimeBool_eq_true_iff (p : Nat) :
    boundarySearchProxyPrimeBool p = true ↔ BoundarySearchProxyPrime p := by
  unfold boundarySearchProxyPrimeBool
  constructor
  · intro h
    rcases Bool.and_eq_true_iff.mp h with ⟨h123, h4⟩
    rcases Bool.and_eq_true_iff.mp h123 with ⟨h12, h3⟩
    rcases Bool.and_eq_true_iff.mp h12 with ⟨h1, h2⟩
    exact ⟨h1, h2, h3, h4⟩
  · intro h
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr
        ⟨Bool.and_eq_true_iff.mpr
          ⟨h.primeTest, h.fourPPlusOneS1⟩,
          h.halfPPlusOneS1⟩,
        h.pPlusFourS1⟩

def boundarySearchMissZeroUpToBool (N0 Lmax : Nat) : Bool :=
  (List.range N0).all
    (fun p => (! boundarySearchProxyPrimeBool p) ||
      boundarySearchInteriorFanWitnessUpToBool p Lmax)

def boundarySearchProxyCountUpTo (N0 : Nat) : Nat :=
  ((List.range N0).filter boundarySearchProxyPrimeBool).length

structure BoundarySearchMissZeroCertificate (N0 Lmax count : Nat) where
  proxyCount : boundarySearchProxyCountUpTo N0 = count
  missZero : boundarySearchMissZeroUpToBool N0 Lmax = true

theorem exists_fanWitnessBool_of_boundarySearchInteriorFanWitnessUpToBool
    {p Lmax : Nat}
    (hwit : boundarySearchInteriorFanWitnessUpToBool p Lmax = true) :
    ∃ a h : Nat,
      a ∈ List.range (Lmax + 1) ∧
      h ∈ List.range (a * a) ∧
      fanWitnessBool p a h = true := by
  unfold boundarySearchInteriorFanWitnessUpToBool at hwit
  rcases (List.any_eq_true.mp hwit) with ⟨a, haRange, haHit⟩
  rcases Bool.and_eq_true_iff.mp haHit with ⟨_haTwo, haWitness⟩
  unfold boundarySearchInteriorFanWitnessAtBool at haWitness
  rcases (List.any_eq_true.mp haWitness) with ⟨h, hhRange, hfan⟩
  exact ⟨a, h, haRange, hhRange, hfan⟩

theorem exists_fanWitness_of_boundarySearchInteriorFanWitnessUpToBool
    {p Lmax : Nat}
    (hwit : boundarySearchInteriorFanWitnessUpToBool p Lmax = true) :
    ∃ a h : Nat, a ≤ Lmax ∧ fanWitness p a h := by
  rcases exists_fanWitnessBool_of_boundarySearchInteriorFanWitnessUpToBool
      (p := p) (Lmax := Lmax) hwit with
    ⟨a, h, haRange, _hhRange, hfan⟩
  have haLe : a ≤ Lmax :=
    Nat.lt_succ_iff.mp (List.mem_range.mp haRange)
  exact ⟨a, h, haLe, (fanWitnessBool_eq_true p a h).mp hfan⟩

theorem exists_completeFanCertificate_of_boundarySearchInteriorFanWitnessUpToBool
    {p Lmax : Nat}
    (hp : 0 < p)
    (hwit : boundarySearchInteriorFanWitnessUpToBool p Lmax = true) :
    ∃ a h d e A B : Nat,
      a ≤ Lmax ∧
      0 < d ∧ 0 < e ∧ 0 < A ∧ 0 < B ∧
      a = d * e * A ∧ h = d ^ 2 * e ∧
      typeIIEquation p d e A B ∧
      typeIIX p d e A = p * a ∧
      0 < typeIIX p d e A ∧
      0 < typeIIY p e A B ∧
      0 < typeIIZ d e B ∧
      (4 : ℚ) / (p : ℚ) =
        1 / ((p * a : Nat) : ℚ) +
        1 / (typeIIY p e A B : ℚ) +
        1 / (typeIIZ d e B : ℚ) := by
  rcases exists_fanWitness_of_boundarySearchInteriorFanWitnessUpToBool
      (p := p) (Lmax := Lmax) hwit with
    ⟨a, h, haLe, hfan⟩
  rcases fanWitness_completeFan_first_denominator_certificate p a h hp hfan with
    ⟨d, e, A, B, hd, he, hA, hB, haeq, hheq, htypeII, hxEq,
      hxPos, hyPos, hzPos, hident⟩
  exact ⟨a, h, d, e, A, B, haLe, hd, he, hA, hB, haeq, hheq,
    htypeII, hxEq, hxPos, hyPos, hzPos, hident⟩

theorem esRepresentable_of_boundarySearchInteriorFanWitnessUpToBool
    {p Lmax : Nat}
    (hp : 0 < p)
    (hwit : boundarySearchInteriorFanWitnessUpToBool p Lmax = true) :
    esRepresentable p := by
  rcases exists_fanWitness_of_boundarySearchInteriorFanWitnessUpToBool
      (p := p) (Lmax := Lmax) hwit with
    ⟨a, h, _haLe, hfan⟩
  exact fanWitness_esRepresentable p a h hp hfan

theorem esRepresentable_of_boundarySearchMissZeroUpToBool
    {N0 Lmax p : Nat}
    (hp : 0 < p)
    (hpRange : p < N0)
    (hproxy : boundarySearchProxyPrimeBool p = true)
    (hmiss : boundarySearchMissZeroUpToBool N0 Lmax = true) :
    esRepresentable p := by
  unfold boundarySearchMissZeroUpToBool at hmiss
  have hpMem : p ∈ List.range N0 := List.mem_range.mpr hpRange
  have hchecked :
      ((! boundarySearchProxyPrimeBool p) ||
        boundarySearchInteriorFanWitnessUpToBool p Lmax) = true :=
    (List.all_eq_true.mp hmiss) p hpMem
  have hwit : boundarySearchInteriorFanWitnessUpToBool p Lmax = true := by
    rcases Bool.or_eq_true_iff.mp hchecked with hnotProxy | hhit
    · rw [hproxy] at hnotProxy
      cases hnotProxy
    · exact hhit
  exact esRepresentable_of_boundarySearchInteriorFanWitnessUpToBool hp hwit

theorem exists_fanWitness_of_boundarySearchMissZeroUpToBool
    {N0 Lmax p : Nat}
    (hpRange : p < N0)
    (hproxy : boundarySearchProxyPrimeBool p = true)
    (hmiss : boundarySearchMissZeroUpToBool N0 Lmax = true) :
    ∃ a h : Nat, a ≤ Lmax ∧ fanWitness p a h := by
  unfold boundarySearchMissZeroUpToBool at hmiss
  have hpMem : p ∈ List.range N0 := List.mem_range.mpr hpRange
  have hchecked :
      ((! boundarySearchProxyPrimeBool p) ||
        boundarySearchInteriorFanWitnessUpToBool p Lmax) = true :=
    (List.all_eq_true.mp hmiss) p hpMem
  have hwit : boundarySearchInteriorFanWitnessUpToBool p Lmax = true := by
    rcases Bool.or_eq_true_iff.mp hchecked with hnotProxy | hhit
    · rw [hproxy] at hnotProxy
      cases hnotProxy
    · exact hhit
  exact exists_fanWitness_of_boundarySearchInteriorFanWitnessUpToBool hwit

theorem exists_completeFanCertificate_of_boundarySearchMissZeroUpToBool
    {N0 Lmax p : Nat}
    (hp : 0 < p)
    (hpRange : p < N0)
    (hproxy : boundarySearchProxyPrimeBool p = true)
    (hmiss : boundarySearchMissZeroUpToBool N0 Lmax = true) :
    ∃ a h d e A B : Nat,
      a ≤ Lmax ∧
      0 < d ∧ 0 < e ∧ 0 < A ∧ 0 < B ∧
      a = d * e * A ∧ h = d ^ 2 * e ∧
      typeIIEquation p d e A B ∧
      typeIIX p d e A = p * a ∧
      0 < typeIIX p d e A ∧
      0 < typeIIY p e A B ∧
      0 < typeIIZ d e B ∧
      (4 : ℚ) / (p : ℚ) =
        1 / ((p * a : Nat) : ℚ) +
        1 / (typeIIY p e A B : ℚ) +
        1 / (typeIIZ d e B : ℚ) := by
  rcases exists_fanWitness_of_boundarySearchMissZeroUpToBool
      (N0 := N0) (Lmax := Lmax) (p := p) hpRange hproxy hmiss with
    ⟨a, h, haLe, hfan⟩
  rcases fanWitness_completeFan_first_denominator_certificate p a h hp hfan with
    ⟨d, e, A, B, hd, he, hA, hB, haeq, hheq, htypeII, hxEq,
      hxPos, hyPos, hzPos, hident⟩
  exact ⟨a, h, d, e, A, B, haLe, hd, he, hA, hB, haeq, hheq,
    htypeII, hxEq, hxPos, hyPos, hzPos, hident⟩

example : boundarySearchProxyPrimeBool 97 = true := by
  native_decide

example : boundarySearchProxyPrimeBool 2521 = true := by
  native_decide

example : boundarySearchInteriorFanWitnessUpToBool 2521 50 = true := by
  native_decide

theorem boundarySearchProxyCountUpTo_10000 :
    boundarySearchProxyCountUpTo 10000 = 25 := by
  native_decide

theorem boundarySearchMissZeroUpTo_10000 :
    boundarySearchMissZeroUpToBool 10000 50 = true := by
  native_decide

theorem boundarySearchProxyCountUpTo_100000 :
    boundarySearchProxyCountUpTo 100000 = 184 := by
  native_decide

theorem boundarySearchMissZeroUpTo_100000 :
    boundarySearchMissZeroUpToBool 100000 50 = true := by
  native_decide

theorem boundarySearchProxyCountUpTo_1000000 :
    boundarySearchProxyCountUpTo 1000000 = 1216 := by
  native_decide

theorem boundarySearchMissZeroUpTo_1000000 :
    boundarySearchMissZeroUpToBool 1000000 84 = true := by
  native_decide

theorem esRepresentable_of_boundarySearchProxyPrime_lt_10000
    {p : Nat}
    (hp : 0 < p)
    (hpRange : p < 10000)
    (hproxy : boundarySearchProxyPrimeBool p = true) :
    esRepresentable p :=
  esRepresentable_of_boundarySearchMissZeroUpToBool
    hp hpRange hproxy boundarySearchMissZeroUpTo_10000

theorem esRepresentable_of_BoundarySearchMissZeroCertificate
    {N0 Lmax count p : Nat}
    (cert : BoundarySearchMissZeroCertificate N0 Lmax count)
    (hp : 0 < p)
    (hpRange : p < N0)
    (hproxy : BoundarySearchProxyPrime p) :
    esRepresentable p :=
  esRepresentable_of_boundarySearchMissZeroUpToBool
    hp hpRange ((boundarySearchProxyPrimeBool_eq_true_iff p).mpr hproxy)
    cert.missZero

theorem exists_fanWitness_of_BoundarySearchMissZeroCertificate
    {N0 Lmax count p : Nat}
    (cert : BoundarySearchMissZeroCertificate N0 Lmax count)
    (hpRange : p < N0)
    (hproxy : BoundarySearchProxyPrime p) :
    ∃ a h : Nat, a ≤ Lmax ∧ fanWitness p a h :=
  exists_fanWitness_of_boundarySearchMissZeroUpToBool
    hpRange ((boundarySearchProxyPrimeBool_eq_true_iff p).mpr hproxy)
    cert.missZero

theorem exists_completeFanCertificate_of_BoundarySearchMissZeroCertificate
    {N0 Lmax count p : Nat}
    (cert : BoundarySearchMissZeroCertificate N0 Lmax count)
    (hp : 0 < p)
    (hpRange : p < N0)
    (hproxy : BoundarySearchProxyPrime p) :
    ∃ a h d e A B : Nat,
      a ≤ Lmax ∧
      0 < d ∧ 0 < e ∧ 0 < A ∧ 0 < B ∧
      a = d * e * A ∧ h = d ^ 2 * e ∧
      typeIIEquation p d e A B ∧
      typeIIX p d e A = p * a ∧
      0 < typeIIX p d e A ∧
      0 < typeIIY p e A B ∧
      0 < typeIIZ d e B ∧
      (4 : ℚ) / (p : ℚ) =
        1 / ((p * a : Nat) : ℚ) +
        1 / (typeIIY p e A B : ℚ) +
        1 / (typeIIZ d e B : ℚ) :=
  exists_completeFanCertificate_of_boundarySearchMissZeroUpToBool
    hp hpRange ((boundarySearchProxyPrimeBool_eq_true_iff p).mpr hproxy)
    cert.missZero

def boundarySearchMissZeroCertificate_10000 :
    BoundarySearchMissZeroCertificate 10000 50 25 :=
  ⟨boundarySearchProxyCountUpTo_10000, boundarySearchMissZeroUpTo_10000⟩

theorem esRepresentable_of_BoundarySearchProxyPrime_lt_10000
    {p : Nat}
    (hp : 0 < p)
    (hpRange : p < 10000)
    (hproxy : BoundarySearchProxyPrime p) :
    esRepresentable p :=
  esRepresentable_of_BoundarySearchMissZeroCertificate
    boundarySearchMissZeroCertificate_10000 hp hpRange hproxy

theorem exists_fanWitness_of_BoundarySearchProxyPrime_lt_10000
    {p : Nat}
    (hpRange : p < 10000)
    (hproxy : BoundarySearchProxyPrime p) :
    ∃ a h : Nat, a ≤ 50 ∧ fanWitness p a h :=
  exists_fanWitness_of_BoundarySearchMissZeroCertificate
    boundarySearchMissZeroCertificate_10000 hpRange hproxy

theorem exists_completeFanCertificate_of_BoundarySearchProxyPrime_lt_10000
    {p : Nat}
    (hp : 0 < p)
    (hpRange : p < 10000)
    (hproxy : BoundarySearchProxyPrime p) :
    ∃ a h d e A B : Nat,
      a ≤ 50 ∧
      0 < d ∧ 0 < e ∧ 0 < A ∧ 0 < B ∧
      a = d * e * A ∧ h = d ^ 2 * e ∧
      typeIIEquation p d e A B ∧
      typeIIX p d e A = p * a ∧
      0 < typeIIX p d e A ∧
      0 < typeIIY p e A B ∧
      0 < typeIIZ d e B ∧
      (4 : ℚ) / (p : ℚ) =
        1 / ((p * a : Nat) : ℚ) +
        1 / (typeIIY p e A B : ℚ) +
        1 / (typeIIZ d e B : ℚ) :=
  exists_completeFanCertificate_of_BoundarySearchMissZeroCertificate
    boundarySearchMissZeroCertificate_10000 hp hpRange hproxy

theorem esRepresentable_of_boundarySearchProxyPrime_lt_100000
    {p : Nat}
    (hp : 0 < p)
    (hpRange : p < 100000)
    (hproxy : boundarySearchProxyPrimeBool p = true) :
    esRepresentable p :=
  esRepresentable_of_boundarySearchMissZeroUpToBool
    hp hpRange hproxy boundarySearchMissZeroUpTo_100000

def boundarySearchMissZeroCertificate_100000 :
    BoundarySearchMissZeroCertificate 100000 50 184 :=
  ⟨boundarySearchProxyCountUpTo_100000, boundarySearchMissZeroUpTo_100000⟩

def boundarySearchMissZeroCertificate_1000000 :
    BoundarySearchMissZeroCertificate 1000000 84 1216 :=
  ⟨boundarySearchProxyCountUpTo_1000000, boundarySearchMissZeroUpTo_1000000⟩

theorem esRepresentable_of_BoundarySearchProxyPrime_lt_100000
    {p : Nat}
    (hp : 0 < p)
    (hpRange : p < 100000)
    (hproxy : BoundarySearchProxyPrime p) :
    esRepresentable p :=
  esRepresentable_of_BoundarySearchMissZeroCertificate
    boundarySearchMissZeroCertificate_100000 hp hpRange hproxy

theorem exists_fanWitness_of_BoundarySearchProxyPrime_lt_100000
    {p : Nat}
    (hpRange : p < 100000)
    (hproxy : BoundarySearchProxyPrime p) :
    ∃ a h : Nat, a ≤ 50 ∧ fanWitness p a h :=
  exists_fanWitness_of_BoundarySearchMissZeroCertificate
    boundarySearchMissZeroCertificate_100000 hpRange hproxy

theorem exists_completeFanCertificate_of_BoundarySearchProxyPrime_lt_100000
    {p : Nat}
    (hp : 0 < p)
    (hpRange : p < 100000)
    (hproxy : BoundarySearchProxyPrime p) :
    ∃ a h d e A B : Nat,
      a ≤ 50 ∧
      0 < d ∧ 0 < e ∧ 0 < A ∧ 0 < B ∧
      a = d * e * A ∧ h = d ^ 2 * e ∧
      typeIIEquation p d e A B ∧
      typeIIX p d e A = p * a ∧
      0 < typeIIX p d e A ∧
      0 < typeIIY p e A B ∧
      0 < typeIIZ d e B ∧
      (4 : ℚ) / (p : ℚ) =
        1 / ((p * a : Nat) : ℚ) +
        1 / (typeIIY p e A B : ℚ) +
        1 / (typeIIZ d e B : ℚ) :=
  exists_completeFanCertificate_of_BoundarySearchMissZeroCertificate
    boundarySearchMissZeroCertificate_100000 hp hpRange hproxy

theorem esRepresentable_of_boundarySearchProxyPrime_lt_1000000
    {p : Nat}
    (hp : 0 < p)
    (hpRange : p < 1000000)
    (hproxy : boundarySearchProxyPrimeBool p = true) :
    esRepresentable p :=
  esRepresentable_of_boundarySearchMissZeroUpToBool
    hp hpRange hproxy boundarySearchMissZeroUpTo_1000000

theorem esRepresentable_of_BoundarySearchProxyPrime_lt_1000000
    {p : Nat}
    (hp : 0 < p)
    (hpRange : p < 1000000)
    (hproxy : BoundarySearchProxyPrime p) :
    esRepresentable p :=
  esRepresentable_of_BoundarySearchMissZeroCertificate
    boundarySearchMissZeroCertificate_1000000 hp hpRange hproxy

theorem exists_fanWitness_of_BoundarySearchProxyPrime_lt_1000000
    {p : Nat}
    (hpRange : p < 1000000)
    (hproxy : BoundarySearchProxyPrime p) :
    ∃ a h : Nat, a ≤ 84 ∧ fanWitness p a h :=
  exists_fanWitness_of_BoundarySearchMissZeroCertificate
    boundarySearchMissZeroCertificate_1000000 hpRange hproxy

theorem exists_completeFanCertificate_of_BoundarySearchProxyPrime_lt_1000000
    {p : Nat}
    (hp : 0 < p)
    (hpRange : p < 1000000)
    (hproxy : BoundarySearchProxyPrime p) :
    ∃ a h d e A B : Nat,
      a ≤ 84 ∧
      0 < d ∧ 0 < e ∧ 0 < A ∧ 0 < B ∧
      a = d * e * A ∧ h = d ^ 2 * e ∧
      typeIIEquation p d e A B ∧
      typeIIX p d e A = p * a ∧
      0 < typeIIX p d e A ∧
      0 < typeIIY p e A B ∧
      0 < typeIIZ d e B ∧
      (4 : ℚ) / (p : ℚ) =
        1 / ((p * a : Nat) : ℚ) +
        1 / (typeIIY p e A B : ℚ) +
        1 / (typeIIZ d e B : ℚ) :=
  exists_completeFanCertificate_of_BoundarySearchMissZeroCertificate
    boundarySearchMissZeroCertificate_1000000 hp hpRange hproxy

end EscLeanChecks
