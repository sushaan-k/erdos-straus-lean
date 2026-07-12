import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.SmoothNumbers
import EscAnalytic.Counting

/-!
# Smooth-number lifting

This file proves the finite smooth-number lifting used by the main theorem:

> For each `n ≤ N`, write `n = s·m`, where every prime factor of `s` is at most
> `z` (the smooth part) and `(m, P(z)) = 1` (the rough part).  **If `m` has a
> representation, then `n` has one after multiplying all denominators by `s`.**

The key implication is proved by `esRepresentable_of_rough` and
`exceptional_lift`, using the
divisor-scaling lemma `EscLeanChecks.esRepresentable_scale_of_dvd`, using that the
rough part `m` divides `n`.

## Contents

* **Step 1 — the smooth/rough decomposition.**  `smoothPart z n` and
  `roughPart z n` are defined from `Nat.factorization` as the products of the
  prime powers `p^{v_p(n)}` over the primes `p ≤ z` resp. `p > z`.  We prove
  `smoothPart z n * roughPart z n = n` (`smooth_mul_rough`), positivity, the
  bounds `smoothPart, roughPart ≤ n`, that every prime factor of `smoothPart z n`
  is `≤ z` (`smoothPart_isSmooth`) and every prime `p ≤ z` is coprime to
  `roughPart z n` (`roughPart_isRough`) — i.e. `(m, P(z)) = 1`.

* **Step 2 — lifting.**
  `esRepresentable_of_rough : esRepresentable (roughPart z n) → esRepresentable n`
  and its contrapositive `exceptional_lift`.

* **Step 3 — the counting reduction.**  An exceptional `n ≤ N`
  forces its rough part `m = roughPart z n` to be *reduced-exceptional*
  (`IsRough z m ∧ esExceptional m`).  Mapping `n ↦ m` and fibering by the smooth
  part `s = smoothPart z n` gives the inequality
  `exceptionalCount N ≤ ∑_{s ≤ N} reducedExceptionalCount z (N / s)`
  (`exceptionalCount_le_sum_reduced`), the Lean form of the line
  `E(N) ≤ ∑_s E_red(N/s; z)` underlying tex 2057–2069.  We also give the
  manuscript's exact two-range split by the size of the rough part `m`
  (`exceptionalCount_eq_smoothRange_add_roughLarge`): the `m ≤ √N` range
  (`smoothRangeCount`, bounded by Rankin in the paper) and the `m > √N` range
  (`roughLargeCount`, controlled by the reduced bound), with the latter bounded by
  the same smooth-part sum (`roughLargeCount_le_sum_reduced`).

The *quantitative* absorptions of the two ranges (Rankin's `N^{3/4+o(1)}` and the
`log z`-sized Euler product) are isolated in `EscAnalytic.AbstractMain` as the smooth and
Euler bounds, plus the corresponding range estimates used by
`EscAnalytic.Assembly.main_modulo_range_bounds`.  This file supplies the
finite combinatorial backbone: the bundled lifting inequality follows from
those two range estimates and the exact smooth/rough split, rather than being an
independent analytic input.
-/

namespace EscAnalytic

open Nat Finset
open Classical

/-! ## Step 1 — the smooth part and the rough part of `n` at threshold `z`. -/

/-- The **`z`-smooth part** of `n`: the product `∏_{p ≤ z} p^{v_p(n)}` of the prime
powers of `n` supported on primes `≤ z`.  (tex 2055: "every prime factor of `s` is
at most `z`".) -/
noncomputable def smoothPart (z n : ℕ) : ℕ :=
  ∏ p ∈ n.factorization.support.filter (· ≤ z), p ^ n.factorization p

/-- The **`z`-rough part** of `n`: the product `∏_{p > z} p^{v_p(n)}` of the prime
powers of `n` supported on primes `> z`.  This is the manuscript's `m` with
`(m, P(z)) = 1` (tex 2055). -/
noncomputable def roughPart (z n : ℕ) : ℕ :=
  ∏ p ∈ n.factorization.support.filter (fun p => ¬ p ≤ z), p ^ n.factorization p

/-- `∏_{p ∣ n} p^{v_p(n)} = n` over the (full) prime support, for `n ≠ 0`.  This is
`Nat.factorization_prod_pow_eq_self` rewritten as a `Finset.prod` over the support. -/
theorem prod_support_eq {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ n.factorization.support, p ^ n.factorization p = n := by
  have := Nat.factorization_prod_pow_eq_self hn
  rwa [Finsupp.prod] at this

/-- **The decomposition `n = s·m`** (tex 2055): `smoothPart z n * roughPart z n = n`
for `n ≠ 0`. -/
theorem smooth_mul_rough (z : ℕ) {n : ℕ} (hn : n ≠ 0) :
    smoothPart z n * roughPart z n = n := by
  unfold smoothPart roughPart
  rw [Finset.prod_filter_mul_prod_filter_not n.factorization.support (· ≤ z)]
  exact prod_support_eq hn

/-- The rough part is always positive: it is a finite product of positive prime
powers, with empty product `1`. -/
theorem rough_pos {z n : ℕ} : 0 < roughPart z n := by
  unfold roughPart
  apply Finset.prod_pos
  intro p hp
  rw [Finset.mem_filter, Nat.support_factorization] at hp
  exact pow_pos (Nat.prime_of_mem_primeFactors hp.1).pos _

/-- The smooth part is always positive: it is a finite product of positive prime
powers, with empty product `1`. -/
theorem smooth_pos {z n : ℕ} : 0 < smoothPart z n := by
  unfold smoothPart
  apply Finset.prod_pos
  intro p hp
  rw [Finset.mem_filter, Nat.support_factorization] at hp
  exact pow_pos (Nat.prime_of_mem_primeFactors hp.1).pos _

/-- `roughPart z n ≤ n` (it is a divisor with positive cofactor). -/
theorem rough_le {z n : ℕ} (hn : 0 < n) : roughPart z n ≤ n := by
  have h := smooth_mul_rough z hn.ne'
  calc roughPart z n ≤ smoothPart z n * roughPart z n :=
        Nat.le_mul_of_pos_left _ smooth_pos
    _ = n := h

/-- `smoothPart z n ≤ n` (it is a divisor with positive cofactor). -/
theorem smooth_le {z n : ℕ} (hn : 0 < n) : smoothPart z n ≤ n := by
  have h := smooth_mul_rough z hn.ne'
  calc smoothPart z n ≤ smoothPart z n * roughPart z n :=
        Nat.le_mul_of_pos_right _ rough_pos
    _ = n := h

/-- The rough part divides `n`. -/
theorem rough_dvd (z n : ℕ) : roughPart z n ∣ n := by
  by_cases hn : n = 0
  · simp [hn]
  · exact Dvd.intro_left _ (smooth_mul_rough z (by simpa using hn))

/-- The smooth part divides `n`. -/
theorem smooth_dvd (z n : ℕ) : smoothPart z n ∣ n := by
  by_cases hn : n = 0
  · simp [hn]
  · exact Dvd.intro _ (smooth_mul_rough z (by simpa using hn))

/-- **`z`-smoothness predicate**: every prime factor of `m` is `≤ z`. -/
def IsSmooth (z m : ℕ) : Prop := ∀ p, Nat.Prime p → p ∣ m → p ≤ z

/-- **`z`-roughness predicate** ((m, P(z)) = 1 in the manuscript): no prime `≤ z`
divides `m`. -/
def IsRough (z m : ℕ) : Prop := ∀ p, Nat.Prime p → p ≤ z → ¬ p ∣ m

/-- Every prime `p ≤ z` is coprime to the rough part of `n` (it does not appear in
the rough product, which collects only primes `> z`). -/
theorem prime_le_coprime_rough {z n p : ℕ} (hp : Nat.Prime p) (hpz : p ≤ z) :
    Nat.Coprime p (roughPart z n) := by
  unfold roughPart
  apply Nat.Coprime.prod_right
  intro q hq
  rw [Finset.mem_filter, Nat.support_factorization] at hq
  have hqprime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq.1
  have hne : p ≠ q := by rintro rfl; exact hq.2 hpz
  exact (Nat.coprime_primes hp hqprime).mpr hne |>.pow_right _

/-- **`(m, P(z)) = 1`** (tex 2055): the rough part of `n` is `z`-rough. -/
theorem roughPart_isRough (z n : ℕ) : IsRough z (roughPart z n) := by
  intro p hp hpz hdvd
  have hcop := prime_le_coprime_rough (z := z) (n := n) hp hpz
  have : p ∣ Nat.gcd p (roughPart z n) := Nat.dvd_gcd dvd_rfl hdvd
  rw [Nat.Coprime] at hcop; rw [hcop] at this
  exact Nat.Prime.one_lt hp |>.ne' (Nat.dvd_one.mp this)

/-- **`s` is `z`-smooth** (tex 2055: "every prime factor of `s` is at most `z`"):
every prime factor of the smooth part of `n` is `≤ z`. -/
theorem smoothPart_isSmooth (z n : ℕ) : IsSmooth z (smoothPart z n) := by
  intro p hp hdvd
  -- `p` divides a product `∏_{q ≤ z, q ∣ n} q^{v_q n}`, so `p ∣ q^…` for some `q ≤ z`,
  -- whence `p = q ≤ z`.
  unfold smoothPart at hdvd
  obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hp).exists_mem_finset_dvd hdvd
  rw [Finset.mem_filter, Nat.support_factorization] at hq
  have hqprime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq.1
  have hpdvdq : p ∣ q := hp.dvd_of_dvd_pow hpq
  have : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp hpdvdq
  rw [this]; exact hq.2

/-! ## Step 2 — the lifting (the manuscript's own argument, tex 2055–2056). -/

/-- **The smooth-number lifting (tex 2055–2056, the heart of `thm:main`'s lifting
step).**  If the rough part `m = roughPart z n` of `n` is representable, then `n`
itself is representable: "after multiplying all denominators by `s`."

Proof: `m ∣ n`, so `EscLeanChecks.esRepresentable_scale_of_dvd` lifts a
representation of `m` to one of `n`. -/
theorem esRepresentable_of_rough {z n : ℕ} (hn : 0 < n)
    (hrep : EscLeanChecks.esRepresentable (roughPart z n)) :
    EscLeanChecks.esRepresentable n :=
  EscLeanChecks.esRepresentable_scale_of_dvd n (roughPart z n) hn rough_pos
    (rough_dvd z n) hrep

/-- **Contrapositive of the lifting (tex 2055–2056).**  If `n` is exceptional then
its rough part is exceptional: an exceptional `n` forces its rough part `m` to be
reduced-exceptional.  This is the implication used to reduce `E(N)` to a count over
reduced integers. -/
theorem exceptional_lift {z n : ℕ} (hn : 0 < n)
    (hex : EscLeanChecks.esExceptional n) :
    EscLeanChecks.esExceptional (roughPart z n) := by
  intro hrep
  exact hex (esRepresentable_of_rough hn hrep)

/-! ## Step 3 — the counting reduction (tex 2055–2069). -/

/-- **Reduced-exceptional count** `E_red(N; z)` in the Lean encoding used by the
lifting: the number of `m` with `1 ≤ m ≤ N`, `(m, P(z)) = 1` (`IsRough z m`), and
`m` exceptional.  (Manuscript `E_red(N; z)`, tex 2036–2043.) -/
noncomputable def reducedExceptionalCount (z N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter
    (fun m => IsRough z m ∧ EscLeanChecks.esExceptional m)).card

/-- A fiber of the smooth-part map over an exceptional set maps injectively, via
`n ↦ roughPart z n`, into the reduced-exceptional set at scale `N / s`.  This is the
combinatorial core of the reduction; factored out for reuse in the two-range split.

The fiber is `E.filter (smoothPart z · = s)` for a finset `E` whose members are
exceptional `n ∈ [2, N]` (the two hypotheses `hEex`, `hErange`).  Stating it for an
arbitrary such `E` keeps the decidability instances of the caller's filters. -/
theorem fiber_card_le_reduced (z N s : ℕ) [DecidablePred (fun n => smoothPart z n = s)]
    (E : Finset ℕ)
    (hEex : ∀ n ∈ E, EscLeanChecks.esExceptional n)
    (hErange : ∀ n ∈ E, 2 ≤ n ∧ n ≤ N) :
    (E.filter (fun n => smoothPart z n = s)).card ≤ reducedExceptionalCount z (N / s) := by
  classical
  rw [reducedExceptionalCount]
  apply Finset.card_le_card_of_injOn (fun n => roughPart z n)
  · intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnE, hfeq⟩ := hn
    obtain ⟨h2, hN⟩ := hErange n hnE
    have hex := hEex n hnE
    have hpos : 0 < n := by omega
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨rough_pos, ?_⟩, roughPart_isRough z n, exceptional_lift hpos hex⟩
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

/-- **The counting reduction (tex 2057–2069).**  The exceptional count is at most
the sum, over smooth parts `s ≤ N`, of the reduced-exceptional count at scale
`N / s`:
`E(N) ≤ ∑_{s ≤ N} E_red(N/s; z)`.

Proved in Lean: fiber the exceptional set by the smooth part `s = smoothPart z n`
(`Finset.card_eq_sum_card_fiberwise`), then bound each fiber by
`reducedExceptionalCount z (N / s)` via `fiber_card_le_reduced` (the map
`n ↦ roughPart z n`).  This is the line `E(N) ≤ ∑_s E_red(N/s; z)` underlying the
manuscript's two displayed ranges. -/
theorem exceptionalCount_le_sum_reduced (z N : ℕ) :
    exceptionalCount N ≤
      ∑ s ∈ Finset.Icc 1 N, reducedExceptionalCount z (N / s) := by
  classical
  set E : Finset ℕ :=
    (Finset.Icc 2 N).filter (fun n => EscLeanChecks.esExceptional n) with hE
  have hmem : ∀ n ∈ E, smoothPart z n ∈ Finset.Icc 1 N := by
    intro n hn
    rw [hE, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨h2, hN⟩, _⟩ := hn
    have hpos : 0 < n := by omega
    rw [Finset.mem_Icc]
    exact ⟨smooth_pos, le_trans (smooth_le hpos) hN⟩
  have hfib := Finset.card_eq_sum_card_fiberwise (f := fun n => smoothPart z n)
    (s := E) (t := Finset.Icc 1 N) hmem
  have hEex : ∀ n ∈ E, EscLeanChecks.esExceptional n := by
    intro n hn; rw [hE, Finset.mem_filter] at hn; exact hn.2
  have hErange : ∀ n ∈ E, 2 ≤ n ∧ n ≤ N := by
    intro n hn; rw [hE, Finset.mem_filter, Finset.mem_Icc] at hn; exact hn.1
  rw [show exceptionalCount N = E.card from rfl, hfib]
  apply Finset.sum_le_sum
  intro s _hs
  exact fiber_card_le_reduced z N s E hEex hErange

/-! ## The manuscript's exact two-range split by the size of the rough part. -/

/-- Count of positive `z`-smooth integers up to `B`.  This is the finite carrier
that appears in the Rankin estimate after fibering the smooth range by the rough
part `m`. -/
noncomputable def smoothPartCount (z B : ℕ) : ℕ :=
  ((Finset.Icc 1 B).filter (fun s => IsSmooth z s)).card

/-- The project-side `≤ z` smoothness predicate is exactly mathlib's
`(z+1)`-smooth predicate, whose convention is strict `< z+1` on prime factors. -/
theorem isSmooth_iff_mem_smoothNumbers_succ (z s : ℕ) :
    IsSmooth z s ↔ s ∈ Nat.smoothNumbers (z + 1) := by
  rw [Nat.mem_smoothNumbers']
  constructor
  · intro hs p hp hpd
    exact Nat.lt_succ_iff.mpr (hs p hp hpd)
  · intro hs p hp hpd
    exact Nat.lt_succ_iff.mp (hs p hp hpd)

/-- The finite `smoothPartCount` carrier embeds in mathlib's smooth-number finset.
This discharges the carrier-level translation; sharp Rankin/de Bruijn asymptotics
remain separate analytic input. -/
theorem smoothPartCount_le_smoothNumbersUpTo (z B : ℕ) :
    smoothPartCount z B ≤ (Nat.smoothNumbersUpTo B (z + 1)).card := by
  classical
  unfold smoothPartCount
  apply Finset.card_le_card
  intro s hs
  rw [Finset.mem_filter, Finset.mem_Icc] at hs
  rw [Nat.mem_smoothNumbersUpTo]
  exact ⟨hs.1.2, (isSmooth_iff_mem_smoothNumbers_succ z s).mp hs.2⟩

/-- Library-backed crude smooth-number bound for the exact finite carrier.  It is
not sharp enough for the manuscript's `z_N = (log N)^4` Rankin step, but it removes
any custom finite-combinatorial content from the smooth-number carrier. -/
theorem smoothPartCount_le_mathlib_smooth_bound (z B : ℕ) :
    smoothPartCount z B ≤ 2 ^ (z + 1).primesBelow.card * Nat.sqrt B := by
  exact (smoothPartCount_le_smoothNumbersUpTo z B).trans
    (Nat.smoothNumbersUpTo_card_le B (z + 1))

/-- **Smooth range** (tex 2057–2063): exceptional `n ≤ N` whose rough part is small,
`roughPart z n ≤ √N`.  In the manuscript this range is `∑_{m ≤ N^{1/2}} Ψ(N/m, z)`,
bounded by a smooth-number estimate to `N^{3/4+o(1)}`.  The abstract
`MainInputs.smooth` field records that quantitative input; the concrete
`zNatScale` route uses the summatory input
`Assembly.rankin_smoothRange_zNatScale_bound`. -/
noncomputable def smoothRangeCount (z N : ℕ) : ℕ :=
  ((Finset.Icc 2 N).filter
    (fun n => EscLeanChecks.esExceptional n ∧ roughPart z n ≤ Nat.sqrt N)).card

/-- **Rough-large range** (tex 2064–2078): exceptional `n ≤ N` whose rough part is
large, `roughPart z n > √N`.  In the manuscript this range is bounded by the reduced
missed count scaled by the Euler product `∏_{p ≤ z}(1-1/p)^{-1} ≪ log z`. -/
noncomputable def roughLargeCount (z N : ℕ) : ℕ :=
  ((Finset.Icc 2 N).filter
    (fun n => EscLeanChecks.esExceptional n ∧ ¬ roughPart z n ≤ Nat.sqrt N)).card

/-- The smooth-range carrier is a finite count, hence nonnegative after casting
to `ℝ`. -/
theorem smoothRangeCount_nonneg (z N : ℕ) : 0 ≤ (smoothRangeCount z N : ℝ) := by
  exact Nat.cast_nonneg _

/-- The rough-large carrier is a finite count, hence nonnegative after casting to
`ℝ`. -/
theorem roughLargeCount_nonneg (z N : ℕ) : 0 ≤ (roughLargeCount z N : ℝ) := by
  exact Nat.cast_nonneg _

/-- The rough-large carrier is contained in the interval `[2,N]`, so its
cardinality is at most `N`. -/
theorem roughLargeCount_le_N (z N : ℕ) : roughLargeCount z N ≤ N := by
  classical
  unfold roughLargeCount
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Nat.card_Icc]
  omega

/-- Real-valued absolute-value form of `roughLargeCount_le_N`. -/
theorem abs_roughLargeCount_le_N (z N : ℕ) :
    |(roughLargeCount z N : ℝ)| ≤ (N : ℝ) := by
  rw [abs_of_nonneg (roughLargeCount_nonneg z N)]
  exact_mod_cast roughLargeCount_le_N z N

/-- **Smooth-range finite envelope** (tex 2057).  Before applying Rankin, the
smooth range is bounded by summing, over rough parts `m ≤ √N`, the number of
`z`-smooth possible smooth parts `s ≤ N/m`.

This is a purely combinatorial fibering statement: an exceptional `n` in the
smooth range gives `m = roughPart z n` and `s = smoothPart z n`, with
`s*m = n ≤ N`, `m ≤ √N`, and `s` `z`-smooth.  Injectivity follows from the exact
factorization `smoothPart z n * roughPart z n = n`. -/
theorem smoothRangeCount_le_sum_smoothPartCount (z N : ℕ) :
    smoothRangeCount z N ≤
      ∑ m ∈ Finset.Icc 1 (Nat.sqrt N), smoothPartCount z (N / m) := by
  classical
  set S : Finset ℕ :=
    (Finset.Icc 2 N).filter
      (fun n => EscLeanChecks.esExceptional n ∧ roughPart z n ≤ Nat.sqrt N) with hS
  have hmem : ∀ n ∈ S, roughPart z n ∈ Finset.Icc 1 (Nat.sqrt N) := by
    intro n hn
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨h2, _hN⟩, _hex, hrough⟩ := hn
    have hpos : 0 < n := by omega
    rw [Finset.mem_Icc]
    exact ⟨rough_pos, hrough⟩
  have hfib := Finset.card_eq_sum_card_fiberwise (f := fun n => roughPart z n)
    (s := S) (t := Finset.Icc 1 (Nat.sqrt N)) hmem
  rw [show smoothRangeCount z N = S.card from rfl, hfib]
  apply Finset.sum_le_sum
  intro m _hm
  rw [smoothPartCount]
  apply Finset.card_le_card_of_injOn (fun n => smoothPart z n)
  · intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnS, hfeq⟩ := hn
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hnS
    obtain ⟨⟨h2, hN⟩, _hex, _hrough⟩ := hnS
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

/-- Summed version of the mathlib carrier bound for the smooth range.  The
remaining external Rankin input is precisely the sharper asymptotic replacement
for this crude bound at the manuscript cutoff. -/
theorem smoothRangeCount_le_sum_mathlib_smooth_bound (z N : ℕ) :
    smoothRangeCount z N ≤
      ∑ m ∈ Finset.Icc 1 (Nat.sqrt N),
        2 ^ (z + 1).primesBelow.card * Nat.sqrt (N / m) := by
  refine (smoothRangeCount_le_sum_smoothPartCount z N).trans ?_
  apply Finset.sum_le_sum
  intro m _hm
  exact smoothPartCount_le_mathlib_smooth_bound z (N / m)

/-- **The exact two-range split (tex 2055).**  `E(N)` is exactly the smooth range
plus the rough-large range. -/
theorem exceptionalCount_eq_smoothRange_add_roughLarge (z N : ℕ) :
    exceptionalCount N = smoothRangeCount z N + roughLargeCount z N := by
  classical
  rw [smoothRangeCount, roughLargeCount, exceptionalCount,
    ← Finset.filter_filter
      (fun n => EscLeanChecks.esExceptional n) (fun n => roughPart z n ≤ Nat.sqrt N),
    ← Finset.filter_filter
      (fun n => EscLeanChecks.esExceptional n) (fun n => ¬ roughPart z n ≤ Nat.sqrt N),
    Finset.filter_card_add_filter_neg_card_eq_card]

/-- Each side of the smooth/rough split is bounded by the full exceptional count:
smooth side. -/
theorem smoothRangeCount_le_exceptionalCount (z N : ℕ) :
    smoothRangeCount z N ≤ exceptionalCount N := by
  rw [exceptionalCount_eq_smoothRange_add_roughLarge z N]
  omega

/-- Each side of the smooth/rough split is bounded by the full exceptional count:
rough-large side. -/
theorem roughLargeCount_le_exceptionalCount (z N : ℕ) :
    roughLargeCount z N ≤ exceptionalCount N := by
  rw [exceptionalCount_eq_smoothRange_add_roughLarge z N]
  omega

/-- Real-valued form of `smoothRangeCount_le_exceptionalCount`. -/
theorem smoothRangeCount_cast_le_exceptionalCount (z N : ℕ) :
    (smoothRangeCount z N : ℝ) ≤ (exceptionalCount N : ℝ) := by
  exact_mod_cast smoothRangeCount_le_exceptionalCount z N

/-- Real-valued form of `roughLargeCount_le_exceptionalCount`. -/
theorem roughLargeCount_cast_le_exceptionalCount (z N : ℕ) :
    (roughLargeCount z N : ℝ) ≤ (exceptionalCount N : ℝ) := by
  exact_mod_cast roughLargeCount_le_exceptionalCount z N

/-- **The rough-large range is controlled by the reduced sum (tex 2064–2069).**
`roughLargeCount z N ≤ ∑_{s ≤ N} E_red(N/s; z)`.  Same fibering as
`exceptionalCount_le_sum_reduced`, restricted to the `m > √N` predicate via
`fiber_card_le_reduced` with `P := fun n => ¬ roughPart z n ≤ √N`. -/
theorem roughLargeCount_le_sum_reduced (z N : ℕ) :
    roughLargeCount z N ≤
      ∑ s ∈ Finset.Icc 1 N, reducedExceptionalCount z (N / s) := by
  classical
  set R : Finset ℕ :=
    (Finset.Icc 2 N).filter
      (fun n => EscLeanChecks.esExceptional n ∧ ¬ roughPart z n ≤ Nat.sqrt N) with hR
  have hmem : ∀ n ∈ R, smoothPart z n ∈ Finset.Icc 1 N := by
    intro n hn
    rw [hR, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨h2, hN⟩, _⟩ := hn
    have hpos : 0 < n := by omega
    rw [Finset.mem_Icc]
    exact ⟨smooth_pos, le_trans (smooth_le hpos) hN⟩
  have hfib := Finset.card_eq_sum_card_fiberwise (f := fun n => smoothPart z n)
    (s := R) (t := Finset.Icc 1 N) hmem
  have hRex : ∀ n ∈ R, EscLeanChecks.esExceptional n := by
    intro n hn; rw [hR, Finset.mem_filter] at hn; exact hn.2.1
  have hRrange : ∀ n ∈ R, 2 ≤ n ∧ n ≤ N := by
    intro n hn; rw [hR, Finset.mem_filter, Finset.mem_Icc] at hn; exact hn.1
  rw [show roughLargeCount z N = R.card from rfl, hfib]
  apply Finset.sum_le_sum
  intro s _hs
  exact fiber_card_le_reduced z N s R hRex hRrange

/-! ## Provability of the `MainInputs` lifting field from a reduced-class bound.

The following records the precise sense in which the combinatorial backbone above
makes `MainInputs.lift` provable: once the smooth range is bounded by the cited
Rankin estimate (`hsmooth`) and the rough-large range is bounded by the
Euler-product × reduced-class estimate (`hrough`), the master lifting inequality
of `thm:main` (tex 2057–2078) follows by the **exact** two-range split
`exceptionalCount_eq_smoothRange_add_roughLarge`.  No `sorry`, no axiom: this is the
genuine bookkeeping that `MainInputs.lift` summarizes. -/
theorem lift_of_range_bounds {z N : ℕ}
    {smooth euler Ered : ℝ}
    (hsmooth : (smoothRangeCount z N : ℝ) ≤ smooth)
    (hrough : (roughLargeCount z N : ℝ) ≤ euler * Ered) :
    (exceptionalCount N : ℝ) ≤ smooth + euler * Ered := by
  have hsplit := exceptionalCount_eq_smoothRange_add_roughLarge z N
  have : (exceptionalCount N : ℝ)
      = (smoothRangeCount z N : ℝ) + (roughLargeCount z N : ℝ) := by
    rw [hsplit]; push_cast; ring
  rw [this]
  exact add_le_add hsmooth hrough

end EscAnalytic
