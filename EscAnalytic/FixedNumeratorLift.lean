import EscAnalytic.Applications
import EscAnalytic.LiftCount

/-!
# Fixed-numerator smooth/rough lifting

This file is the fixed-`m` analogue of the finite smooth/rough decomposition in
`EscAnalytic.LiftCount`.  The analytic estimates are still supplied elsewhere;
the content here is the exact finite counting bridge from `m/r` to `m/n` when
`r ∣ n`, and the resulting two-range split for the fixed-numerator exceptional
carrier.
-/

namespace EscAnalytic

open Nat Finset
open Classical

/-- Scaling for the fixed-numerator unit-fraction predicate.  If `m / p` has a
positive three-term unit-fraction representation and `p ∣ n`, then `m / n` has
one by multiplying all three denominators by `n / p`. -/
theorem fixedNumeratorRepresentable_scale_of_dvd
    (m n p : ℕ)
    (hn : 0 < n) (hp : 0 < p)
    (hdiv : p ∣ n)
    (hrep : fixedNumeratorRepresentable m p) :
    fixedNumeratorRepresentable m n := by
  rcases hrep with ⟨x, y, z, hx, hy, hz, hident⟩
  rcases hdiv with ⟨k, hk⟩
  have hkpos : 0 < k := by
    by_contra hknot
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hknot
    rw [hk, hk0, mul_zero] at hn
    exact (Nat.lt_irrefl 0 hn)
  refine ⟨k * x, k * y, k * z,
    Nat.mul_pos hkpos hx, Nat.mul_pos hkpos hy, Nat.mul_pos hkpos hz, ?_⟩
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hkpos)
  have hxQ : (x : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hx)
  have hyQ : (y : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hy)
  have hzQ : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz)
  rw [hk]
  field_simp [hpQ, hkQ, hxQ, hyQ, hzQ] at hident ⊢
  have hmul := congrArg (fun t : ℚ => (k : ℚ) ^ 3 * t) hident
  ring_nf at hmul ⊢
  nlinarith [hmul]

/-- Contrapositive fixed-numerator lifting along a divisor. -/
theorem fixedNumeratorExceptional_divisor_of_exceptional
    (m n p : ℕ)
    (hn : 0 < n) (hp : 0 < p)
    (hdiv : p ∣ n)
    (hex : ¬ fixedNumeratorRepresentable m n) :
    ¬ fixedNumeratorRepresentable m p := by
  intro hrep
  exact hex (fixedNumeratorRepresentable_scale_of_dvd m n p hn hp hdiv hrep)

/-- If `n` is fixed-`m` exceptional, then its rough part is fixed-`m`
exceptional. -/
theorem fixedNumeratorExceptional_lift {m z n : ℕ} (hn : 0 < n)
    (hex : ¬ fixedNumeratorRepresentable m n) :
    ¬ fixedNumeratorRepresentable m (roughPart z n) :=
  fixedNumeratorExceptional_divisor_of_exceptional m n (roughPart z n)
    hn rough_pos (rough_dvd z n) hex

/-- Fixed-numerator reduced-exceptional count: rough denominators up to `N`
whose fixed-`m` fraction remains exceptional. -/
noncomputable def fixedNumeratorReducedExceptionalCount (m z N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter
    (fun r => IsRough z r ∧ ¬ fixedNumeratorRepresentable m r)).card

/-- Canonical reduced-class set: the actual image of the reduced exceptional
carrier under the chosen class map. -/
noncomputable def fixedNumeratorReducedCanonicalClasses
    {κ : Type*} [DecidableEq κ] (m z N : ℕ) (classOf : ℕ → κ) : Finset κ :=
  ((Finset.Icc 1 N).filter
    (fun r => IsRough z r ∧ ¬ fixedNumeratorRepresentable m r)).image classOf

/-- Every reduced exceptional denominator lands in the canonical reduced-class
set. -/
theorem fixedNumeratorReducedCanonicalClasses_mem
    {κ : Type*} [DecidableEq κ] (m z N : ℕ) (classOf : ℕ → κ) :
    ∀ r ∈ ((Finset.Icc 1 N).filter
      (fun r => IsRough z r ∧ ¬ fixedNumeratorRepresentable m r)),
        classOf r ∈ fixedNumeratorReducedCanonicalClasses m z N classOf := by
  intro r hr
  rw [fixedNumeratorReducedCanonicalClasses]
  exact Finset.mem_image.mpr ⟨r, hr, rfl⟩

/-- Each canonical class fiber is bounded by the total reduced exceptional
count.  This supplies a completely finite uniform class majorant when the
majorant is chosen to be the whole reduced carrier. -/
theorem fixedNumeratorReducedClassFiber_le_total
    {κ : Type*} [DecidableEq κ] (m z N : ℕ) (classOf : ℕ → κ) (b : κ) :
    ((((Finset.Icc 1 N).filter
      (fun r => (IsRough z r ∧ ¬ fixedNumeratorRepresentable m r) ∧
        classOf r = b)).card : ℕ) : ℝ) ≤
      (fixedNumeratorReducedExceptionalCount m z N : ℝ) := by
  have hcard :
      ((Finset.Icc 1 N).filter
        (fun r => (IsRough z r ∧ ¬ fixedNumeratorRepresentable m r) ∧
          classOf r = b)).card ≤
        ((Finset.Icc 1 N).filter
          (fun r => IsRough z r ∧ ¬ fixedNumeratorRepresentable m r)).card := by
    apply Finset.card_le_card
    intro r hr
    rw [Finset.mem_filter] at hr ⊢
    exact ⟨hr.1, hr.2.1⟩
  exact_mod_cast hcard

/-- The reduced-sum carrier appearing in the fixed-numerator rough lifting
argument. -/
noncomputable def fixedNumeratorReducedSumCount (m z N : ℕ) : ℕ :=
  ∑ s ∈ Finset.Icc 1 N, fixedNumeratorReducedExceptionalCount m z (N / s)

/-- Casting the named reduced-sum carrier recovers the paper's real-valued
finite sum. -/
theorem fixedNumeratorReducedSumCount_cast (m z N : ℕ) :
    (fixedNumeratorReducedSumCount m z N : ℝ) =
      ∑ s ∈ Finset.Icc 1 N,
        (fixedNumeratorReducedExceptionalCount m z (N / s) : ℝ) := by
  rw [fixedNumeratorReducedSumCount]
  norm_num

/-- The paper's reduced sum is bounded by any Euler factor at least one times
the named reduced-sum carrier.  This is the finite-initial tautology used when
the reduced carrier is enlarged on a fixed finite range. -/
theorem fixedNumeratorReduced_sum_le_euler_mul_self
    {m z N : ℕ} {euler : ℝ} (heuler : 1 ≤ euler) :
    ((∑ s ∈ Finset.Icc 1 N,
      fixedNumeratorReducedExceptionalCount m z (N / s)) : ℝ) ≤
        euler * (fixedNumeratorReducedSumCount m z N : ℝ) := by
  have hcast :
      ((∑ s ∈ Finset.Icc 1 N,
        fixedNumeratorReducedExceptionalCount m z (N / s)) : ℝ) =
        (fixedNumeratorReducedSumCount m z N : ℝ) := by
    rw [fixedNumeratorReducedSumCount]
    norm_num
  rw [hcast]
  calc
    (fixedNumeratorReducedSumCount m z N : ℝ)
        = 1 * (fixedNumeratorReducedSumCount m z N : ℝ) := by ring
    _ ≤ euler * (fixedNumeratorReducedSumCount m z N : ℝ) :=
        mul_le_mul_of_nonneg_right heuler (Nat.cast_nonneg _)

/-- A smooth-part fiber of a fixed-numerator exceptional set injects, via the
rough-part map, into the fixed-numerator reduced-exceptional set at scale
`N / s`. -/
theorem fixedNumeratorFiber_card_le_reduced
    (m z N s : ℕ) [DecidablePred (fun n => smoothPart z n = s)]
    (E : Finset ℕ)
    (hEex : ∀ n ∈ E, ¬ fixedNumeratorRepresentable m n)
    (hErange : ∀ n ∈ E, 1 ≤ n ∧ n ≤ N) :
    (E.filter (fun n => smoothPart z n = s)).card ≤
      fixedNumeratorReducedExceptionalCount m z (N / s) := by
  classical
  rw [fixedNumeratorReducedExceptionalCount]
  apply Finset.card_le_card_of_injOn (fun n => roughPart z n)
  · intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnE, hfeq⟩ := hn
    obtain ⟨hn1, hN⟩ := hErange n hnE
    have hex := hEex n hnE
    have hpos : 0 < n := by omega
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨rough_pos, ?_⟩, roughPart_isRough z n,
      fixedNumeratorExceptional_lift hpos hex⟩
    have hsmr : smoothPart z n * roughPart z n = n := smooth_mul_rough z hpos.ne'
    rw [Nat.le_div_iff_mul_le (by rw [← hfeq]; exact smooth_pos), ← hfeq]
    calc roughPart z n * smoothPart z n = smoothPart z n * roughPart z n := by ring
      _ = n := hsmr
      _ ≤ N := hN
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
    obtain ⟨haE, hfa⟩ := ha
    obtain ⟨hbE, hfb⟩ := hb
    have hapos : 0 < a := by have := (hErange a haE).1; omega
    have hbpos : 0 < b := by have := (hErange b hbE).1; omega
    have hra : smoothPart z a * roughPart z a = a := smooth_mul_rough z hapos.ne'
    have hrb : smoothPart z b * roughPart z b = b := smooth_mul_rough z hbpos.ne'
    simp only [] at hab
    rw [← hra, ← hrb, hfa, hfb, hab]

/-- Fixed-numerator smooth range: fixed-`m` exceptional denominators whose rough
part is at most `√N`. -/
noncomputable def fixedNumeratorSmoothRangeCount (m z N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter
    (fun n => ¬ fixedNumeratorRepresentable m n ∧ roughPart z n ≤ Nat.sqrt N)).card

/-- Fixed-numerator rough-large range: fixed-`m` exceptional denominators whose
rough part is larger than `√N`. -/
noncomputable def fixedNumeratorRoughLargeCount (m z N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter
    (fun n => ¬ fixedNumeratorRepresentable m n ∧ ¬ roughPart z n ≤ Nat.sqrt N)).card

/-- The fixed-numerator smooth-range carrier is nonnegative after casting. -/
theorem fixedNumeratorSmoothRangeCount_nonneg (m z N : ℕ) :
    0 ≤ (fixedNumeratorSmoothRangeCount m z N : ℝ) := by
  exact Nat.cast_nonneg _

/-- The fixed-numerator rough-large carrier is nonnegative after casting. -/
theorem fixedNumeratorRoughLargeCount_nonneg (m z N : ℕ) :
    0 ≤ (fixedNumeratorRoughLargeCount m z N : ℝ) := by
  exact Nat.cast_nonneg _

/-- The exact fixed-numerator two-range split. -/
theorem fixedNumeratorExceptionalCount_eq_smoothRange_add_roughLarge
    (m z N : ℕ) :
    fixedNumeratorExceptionalCount m N =
      fixedNumeratorSmoothRangeCount m z N + fixedNumeratorRoughLargeCount m z N := by
  classical
  rw [fixedNumeratorSmoothRangeCount, fixedNumeratorRoughLargeCount,
    fixedNumeratorExceptionalCount,
    ← Finset.filter_filter
      (fun n => ¬ fixedNumeratorRepresentable m n) (fun n => roughPart z n ≤ Nat.sqrt N),
    ← Finset.filter_filter
      (fun n => ¬ fixedNumeratorRepresentable m n) (fun n => ¬ roughPart z n ≤ Nat.sqrt N),
    Finset.filter_card_add_filter_neg_card_eq_card]

/-- Fixed-numerator lifting field from the two quantitative range estimates. -/
theorem fixedNumerator_lift_of_range_bounds {m z N : ℕ}
    {smooth euler Ered : ℝ}
    (hsmooth : (fixedNumeratorSmoothRangeCount m z N : ℝ) ≤ smooth)
    (hrough : (fixedNumeratorRoughLargeCount m z N : ℝ) ≤ euler * Ered) :
    (fixedNumeratorExceptionalCount m N : ℝ) ≤ smooth + euler * Ered := by
  have hsplit := fixedNumeratorExceptionalCount_eq_smoothRange_add_roughLarge m z N
  have : (fixedNumeratorExceptionalCount m N : ℝ) =
      (fixedNumeratorSmoothRangeCount m z N : ℝ) +
        (fixedNumeratorRoughLargeCount m z N : ℝ) := by
    rw [hsplit]
    push_cast
    ring
  rw [this]
  exact add_le_add hsmooth hrough

/-- Fixed-numerator rough-large range controlled by a reduced-exceptional sum.
This is the fixed-`m` analogue of `roughLargeCount_le_sum_reduced`. -/
theorem fixedNumeratorRoughLargeCount_le_sum_reduced (m z N : ℕ) :
    fixedNumeratorRoughLargeCount m z N ≤
      ∑ s ∈ Finset.Icc 1 N, fixedNumeratorReducedExceptionalCount m z (N / s) := by
  classical
  set R : Finset ℕ :=
    (Finset.Icc 1 N).filter
      (fun n => ¬ fixedNumeratorRepresentable m n ∧ ¬ roughPart z n ≤ Nat.sqrt N) with hR
  have hmem : ∀ n ∈ R, smoothPart z n ∈ Finset.Icc 1 N := by
    intro n hn
    rw [hR, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hN⟩, _⟩ := hn
    have hpos : 0 < n := by omega
    rw [Finset.mem_Icc]
    exact ⟨smooth_pos, le_trans (smooth_le hpos) hN⟩
  have hfib := Finset.card_eq_sum_card_fiberwise (f := fun n => smoothPart z n)
    (s := R) (t := Finset.Icc 1 N) hmem
  have hRex : ∀ n ∈ R, ¬ fixedNumeratorRepresentable m n := by
    intro n hn; rw [hR, Finset.mem_filter] at hn; exact hn.2.1
  have hRrange : ∀ n ∈ R, 1 ≤ n ∧ n ≤ N := by
    intro n hn; rw [hR, Finset.mem_filter, Finset.mem_Icc] at hn; exact hn.1
  rw [show fixedNumeratorRoughLargeCount m z N = R.card from rfl, hfib]
  apply Finset.sum_le_sum
  intro s _hs
  exact fixedNumeratorFiber_card_le_reduced m z N s R hRex hRrange

/-- Fixed-numerator lifting field from a smooth-range bound and a reduced-sum
rough-range bound. -/
theorem fixedNumerator_lift_of_smooth_and_reduced_sum_bounds {m z N : ℕ}
    {smooth euler Ered : ℝ}
    (hsmooth : (fixedNumeratorSmoothRangeCount m z N : ℝ) ≤ smooth)
    (hreduced : ((∑ s ∈ Finset.Icc 1 N,
        fixedNumeratorReducedExceptionalCount m z (N / s)) : ℝ) ≤ euler * Ered) :
    (fixedNumeratorExceptionalCount m N : ℝ) ≤ smooth + euler * Ered := by
  have hrough_nat := fixedNumeratorRoughLargeCount_le_sum_reduced m z N
  have hrough_sum :
      (fixedNumeratorRoughLargeCount m z N : ℝ) ≤
        ((∑ s ∈ Finset.Icc 1 N,
          fixedNumeratorReducedExceptionalCount m z (N / s)) : ℝ) := by
    exact_mod_cast hrough_nat
  exact fixedNumerator_lift_of_range_bounds hsmooth (le_trans hrough_sum hreduced)

/-- A pointwise majorant for every smooth-part fiber gives the corresponding
fixed-numerator reduced-sum bound.  This is finite bookkeeping: analytic work
may be organized per `s`, and this lemma performs the summation. -/
theorem fixedNumeratorReduced_sum_le_of_pointwise_majorant
    {m z N : ℕ} {B : ℕ → ℝ} {euler Ered : ℝ}
    (hpoint : ∀ s ∈ Finset.Icc 1 N,
      (fixedNumeratorReducedExceptionalCount m z (N / s) : ℝ) ≤ B s)
    (hsum : (∑ s ∈ Finset.Icc 1 N, B s) ≤ euler * Ered) :
    ((∑ s ∈ Finset.Icc 1 N,
      fixedNumeratorReducedExceptionalCount m z (N / s)) : ℝ) ≤ euler * Ered := by
  have hsum_point :
      (∑ s ∈ Finset.Icc 1 N,
        (fixedNumeratorReducedExceptionalCount m z (N / s) : ℝ))
          ≤ ∑ s ∈ Finset.Icc 1 N, B s := by
    exact Finset.sum_le_sum hpoint
  have hcast :
      ((∑ s ∈ Finset.Icc 1 N,
        fixedNumeratorReducedExceptionalCount m z (N / s)) : ℝ)
        =
      ∑ s ∈ Finset.Icc 1 N,
        (fixedNumeratorReducedExceptionalCount m z (N / s) : ℝ) := by
    norm_num
  rw [hcast]
  exact le_trans hsum_point hsum

/-- A reduced fixed-numerator count is bounded by summing per-class majorants
over any finite class set that contains the class of every counted reduced
integer.  This is the finite bookkeeping behind the manuscript's summation over
reduced base classes. -/
theorem fixedNumeratorReducedExceptionalCount_le_sum_class_majorants
    {ι : Type*} [DecidableEq ι]
    {m z N : ℕ} (cls : Finset ι) (classOf : ℕ → ι) (M : ι → ℝ)
    (hmem : ∀ r ∈ ((Finset.Icc 1 N).filter
      (fun r => IsRough z r ∧ ¬ fixedNumeratorRepresentable m r)),
        classOf r ∈ cls)
    (hclass : ∀ b ∈ cls,
      ((((Finset.Icc 1 N).filter
        (fun r => (IsRough z r ∧ ¬ fixedNumeratorRepresentable m r) ∧
          classOf r = b)).card : ℕ) : ℝ) ≤ M b) :
    (fixedNumeratorReducedExceptionalCount m z N : ℝ) ≤
      ∑ b ∈ cls, M b := by
  classical
  set R : Finset ℕ :=
    (Finset.Icc 1 N).filter
      (fun r => IsRough z r ∧ ¬ fixedNumeratorRepresentable m r) with hR
  have hfib :=
    Finset.card_eq_sum_card_fiberwise (f := classOf) (s := R) (t := cls)
      (by
        intro r hr
        exact hmem r (by simpa [hR] using hr))
  have hclass' : ∀ b ∈ cls, ((R.filter (fun r => classOf r = b)).card : ℝ) ≤ M b := by
    intro b hb
    have hfilter :
        R.filter (fun r => classOf r = b) =
          (Finset.Icc 1 N).filter
            (fun r => (IsRough z r ∧ ¬ fixedNumeratorRepresentable m r) ∧
              classOf r = b) := by
      ext r
      simp [hR, and_left_comm, and_assoc]
    rw [hfilter]
    exact hclass b hb
  have hsum_class :
      (∑ b ∈ cls, ((R.filter (fun r => classOf r = b)).card : ℝ)) ≤
        ∑ b ∈ cls, M b := by
    exact Finset.sum_le_sum hclass'
  have hcast :
      (fixedNumeratorReducedExceptionalCount m z N : ℝ) =
        ∑ b ∈ cls, ((R.filter (fun r => classOf r = b)).card : ℝ) := by
    rw [fixedNumeratorReducedExceptionalCount, ← hR, hfib]
    norm_num
  rw [hcast]
  exact hsum_class

/-- Smooth-part reduced sums can be assembled from per-class majorants at every
smooth-part scale.  This is the class-summed version of
`fixedNumeratorReduced_sum_le_of_pointwise_majorant`. -/
theorem fixedNumeratorReduced_sum_le_of_class_majorants
    {ι : Type*} [DecidableEq ι]
    {m z N : ℕ} {euler Ered : ℝ}
    (cls : ℕ → Finset ι) (classOf : ℕ → ℕ → ι) (M : ℕ → ι → ℝ)
    (hmem : ∀ s ∈ Finset.Icc 1 N, ∀ r ∈ ((Finset.Icc 1 (N / s)).filter
      (fun r => IsRough z r ∧ ¬ fixedNumeratorRepresentable m r)),
        classOf s r ∈ cls s)
    (hclass : ∀ s ∈ Finset.Icc 1 N, ∀ b ∈ cls s,
      ((((Finset.Icc 1 (N / s)).filter
        (fun r => (IsRough z r ∧ ¬ fixedNumeratorRepresentable m r) ∧
          classOf s r = b)).card : ℕ) : ℝ) ≤ M s b)
    (hsum : (∑ s ∈ Finset.Icc 1 N, ∑ b ∈ cls s, M s b) ≤ euler * Ered) :
    ((∑ s ∈ Finset.Icc 1 N,
      fixedNumeratorReducedExceptionalCount m z (N / s)) : ℝ) ≤ euler * Ered :=
  fixedNumeratorReduced_sum_le_of_pointwise_majorant
    (m := m) (z := z) (N := N) (B := fun s => ∑ b ∈ cls s, M s b)
    (euler := euler) (Ered := Ered)
    (fun s hs =>
      fixedNumeratorReducedExceptionalCount_le_sum_class_majorants
        (m := m) (z := z) (N := N / s)
        (cls s) (classOf s) (M s) (hmem s hs) (hclass s hs))
    hsum

/-- Uniform per-class majorants imply the corresponding class-summed
reduced-sum bound.  This is the finite bookkeeping form used when the analytic
estimate gives a single envelope for every reduced class at a fixed smooth-part
scale. -/
theorem fixedNumeratorReduced_sum_le_of_class_uniform_majorants
    {ι : Type*} [DecidableEq ι]
    {m z N : ℕ} {euler Ered : ℝ}
    (cls : ℕ → Finset ι) (classOf : ℕ → ℕ → ι) (U : ℕ → ℝ)
    (hmem : ∀ s ∈ Finset.Icc 1 N, ∀ r ∈ ((Finset.Icc 1 (N / s)).filter
      (fun r => IsRough z r ∧ ¬ fixedNumeratorRepresentable m r)),
        classOf s r ∈ cls s)
    (hclass : ∀ s ∈ Finset.Icc 1 N, ∀ b ∈ cls s,
      ((((Finset.Icc 1 (N / s)).filter
        (fun r => (IsRough z r ∧ ¬ fixedNumeratorRepresentable m r) ∧
          classOf s r = b)).card : ℕ) : ℝ) ≤ U s)
    (hsum : (∑ s ∈ Finset.Icc 1 N, ((cls s).card : ℝ) * U s) ≤ euler * Ered) :
    ((∑ s ∈ Finset.Icc 1 N,
      fixedNumeratorReducedExceptionalCount m z (N / s)) : ℝ) ≤ euler * Ered :=
  fixedNumeratorReduced_sum_le_of_class_majorants
    (m := m) (z := z) (N := N) (euler := euler) (Ered := Ered)
    cls classOf (fun s _b => U s) hmem hclass
    (by
      have hsum_const :
          (∑ s ∈ Finset.Icc 1 N, ∑ b ∈ cls s, U s) =
            ∑ s ∈ Finset.Icc 1 N, ((cls s).card : ℝ) * U s := by
        refine Finset.sum_congr rfl ?_
        intro s _hs
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [hsum_const]
      exact hsum)

/-- The canonical reduced-class cardinality sum dominates the raw reduced sum.

For each smooth-part scale `s`, the canonical class set is the image of the
actual reduced exceptional carrier, and the uniform majorant is the total
reduced carrier at that scale.  This finite theorem is the bookkeeping core of
the canonical class-summed reduced-envelope route. -/
theorem fixedNumeratorReduced_sum_le_canonical_class_count_mul_total
    {ι : Type*} [DecidableEq ι]
    {m z N : ℕ} (classOf : ℕ → ℕ → ι) :
    ((∑ s ∈ Finset.Icc 1 N,
      fixedNumeratorReducedExceptionalCount m z (N / s)) : ℝ) ≤
        ∑ s ∈ Finset.Icc 1 N,
          ((fixedNumeratorReducedCanonicalClasses m z (N / s)
            (classOf s)).card : ℝ) *
            (fixedNumeratorReducedExceptionalCount m z (N / s) : ℝ) := by
  have hcast :
      ((∑ s ∈ Finset.Icc 1 N,
        fixedNumeratorReducedExceptionalCount m z (N / s)) : ℝ) =
          ∑ s ∈ Finset.Icc 1 N,
            (fixedNumeratorReducedExceptionalCount m z (N / s) : ℝ) := by
    norm_num
  rw [hcast]
  apply Finset.sum_le_sum
  intro s _hs
  calc
    (fixedNumeratorReducedExceptionalCount m z (N / s) : ℝ)
        ≤ ∑ b ∈ fixedNumeratorReducedCanonicalClasses m z (N / s) (classOf s),
            (fixedNumeratorReducedExceptionalCount m z (N / s) : ℝ) := by
          exact fixedNumeratorReducedExceptionalCount_le_sum_class_majorants
            (m := m) (z := z) (N := N / s)
            (fixedNumeratorReducedCanonicalClasses m z (N / s) (classOf s))
            (classOf s)
            (fun _b => (fixedNumeratorReducedExceptionalCount m z (N / s) : ℝ))
            (fixedNumeratorReducedCanonicalClasses_mem m z (N / s) (classOf s))
            (fun b _hb =>
              fixedNumeratorReducedClassFiber_le_total m z (N / s) (classOf s) b)
    _ = ((fixedNumeratorReducedCanonicalClasses m z (N / s) (classOf s)).card : ℝ) *
          (fixedNumeratorReducedExceptionalCount m z (N / s) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]

/-- Smooth-range control plus uniform reduced-class majorants directly bound
the fixed-numerator exceptional count.

This packages the finite bookkeeping used in the paper's fixed-`m` lift: the
rough-large range is injected into reduced rough carriers, the reduced carriers
are summed by smooth-part scale and reduced class, and the smooth range is
added separately. -/
theorem fixedNumeratorExceptionalCount_le_smoothRange_add_class_uniform_majorants
    {ι : Type*} [DecidableEq ι]
    {m z N : ℕ} {smooth euler Ered : ℝ}
    (cls : ℕ → Finset ι) (classOf : ℕ → ℕ → ι) (U : ℕ → ℝ)
    (hsmooth : (fixedNumeratorSmoothRangeCount m z N : ℝ) ≤ smooth)
    (hmem : ∀ s ∈ Finset.Icc 1 N, ∀ r ∈ ((Finset.Icc 1 (N / s)).filter
      (fun r => IsRough z r ∧ ¬ fixedNumeratorRepresentable m r)),
        classOf s r ∈ cls s)
    (hclass : ∀ s ∈ Finset.Icc 1 N, ∀ b ∈ cls s,
      ((((Finset.Icc 1 (N / s)).filter
        (fun r => (IsRough z r ∧ ¬ fixedNumeratorRepresentable m r) ∧
          classOf s r = b)).card : ℕ) : ℝ) ≤ U s)
    (hsum : (∑ s ∈ Finset.Icc 1 N, ((cls s).card : ℝ) * U s) ≤ euler * Ered) :
    (fixedNumeratorExceptionalCount m N : ℝ) ≤ smooth + euler * Ered :=
  fixedNumerator_lift_of_smooth_and_reduced_sum_bounds
    (m := m) (z := z) (N := N) (smooth := smooth)
    (euler := euler) (Ered := Ered)
    hsmooth
    (fixedNumeratorReduced_sum_le_of_class_uniform_majorants
      (m := m) (z := z) (N := N) (euler := euler) (Ered := Ered)
      cls classOf U hmem hclass hsum)

/-- The fixed-numerator smooth range is bounded by the same finite smooth-part
envelope as the ordinary smooth range: forget the exceptional predicate and fiber
by the rough part. -/
theorem fixedNumeratorSmoothRangeCount_le_sum_smoothPartCount (m z N : ℕ) :
    fixedNumeratorSmoothRangeCount m z N ≤
      ∑ r ∈ Finset.Icc 1 (Nat.sqrt N), smoothPartCount z (N / r) := by
  classical
  set S : Finset ℕ :=
    (Finset.Icc 1 N).filter
      (fun n => ¬ fixedNumeratorRepresentable m n ∧ roughPart z n ≤ Nat.sqrt N) with hS
  have hmem : ∀ n ∈ S, roughPart z n ∈ Finset.Icc 1 (Nat.sqrt N) := by
    intro n hn
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hn
    have hrough_pos : 0 < roughPart z n := rough_pos
    exact Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hrough_pos, hn.2.2⟩
  have hfib := Finset.card_eq_sum_card_fiberwise (f := fun n => roughPart z n)
    (s := S) (t := Finset.Icc 1 (Nat.sqrt N)) hmem
  rw [show fixedNumeratorSmoothRangeCount m z N = S.card from rfl, hfib]
  apply Finset.sum_le_sum
  intro r _hr
  rw [smoothPartCount]
  apply Finset.card_le_card_of_injOn (fun n => smoothPart z n)
  · intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnS, hfeq⟩ := hn
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hnS
    obtain ⟨⟨hn1, hN⟩, _hex, _hrough⟩ := hnS
    have hpos : 0 < n := by omega
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨smooth_pos, ?_⟩, smoothPart_isSmooth z n⟩
    have hsmr : smoothPart z n * roughPart z n = n := smooth_mul_rough z hpos.ne'
    rw [Nat.le_div_iff_mul_le (by rw [← hfeq]; exact rough_pos), ← hfeq]
    calc smoothPart z n * roughPart z n = n := hsmr
      _ ≤ N := hN
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
    obtain ⟨haS, hfa⟩ := ha
    obtain ⟨hbS, hfb⟩ := hb
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at haS hbS
    have hapos : 0 < a := by have := haS.1.1; omega
    have hbpos : 0 < b := by have := hbS.1.1; omega
    have hra : smoothPart z a * roughPart z a = a := smooth_mul_rough z hapos.ne'
    have hrb : smoothPart z b * roughPart z b = b := smooth_mul_rough z hbpos.ne'
    simp only [] at hab
    rw [← hra, ← hrb, hab, hfa, hfb]

end EscAnalytic
