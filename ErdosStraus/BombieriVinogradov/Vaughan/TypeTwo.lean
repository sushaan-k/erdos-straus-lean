import ErdosStraus.BombieriVinogradov.Vaughan.HyperbolicCutoff
import ErdosStraus.BombieriVinogradov.Reduction.ConductorSplit

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

/-!
# Type-II sums in Vaughan's identity

On each active dyadic rectangle `(k, l)` the Type-II block
`∑_{d e m ≤ y} μ(d) Λ(e) χ(d e m)` is a rectangular sum `∑_{d t ≤ y} a_d b_t χ(d t)`
with `a_d = μ(d)` and `b_t = ∑_{e ∣ t} Λ(e)`. The prefix-maximal large sieve bounds
its normalized primitive-character mean over a conductor cell `(i, 2i]` by
`10^6 log(4N+4)^15 (N/i + N/√(u+1) + N/√(v+1) + i √N)`. Summing over the dyadic cells
bounds the full Type-II mean over the conductors `R < q ≤ Q`, `R = ⌊(log N)^C⌋`.
-/

namespace BombieriVinogradov

open Classical Finset
open scoped BigOperators ArithmeticFunction
noncomputable section

/-! ## The Type-II block as a rectangular sum -/

/-- `a_d = μ(d)` on the dyadic block of level `k`, and `0` elsewhere. -/
def vaughanTypeIIRectLeftCoeff (N u k : ℕ) (d : ℤ) : ℂ :=
  if d.toNat ∈ vaughanCanonicalDyadicBlock N u k then
    vaughanMoebiusCoeff d.toNat else 0

/-- `b_t = ∑_{e ∣ t} Λ(e)`, with `e` running over the dyadic block of level `l`. -/
def vaughanTypeIIRectRightCoeff (N v l : ℕ) (t : ℤ) : ℂ :=
  ∑ e ∈ vaughanCanonicalDyadicBlock N v l,
    if e ∣ t.toNat then vaughanMangoldtCoeff e else 0

/-- If `d t ≤ y`, collecting the pairs `(e, m)` with `e m = t` and `d e m ≤ y`
gives the coefficient `b_t = ∑_{e ∣ t} Λ(e)`. -/
theorem vaughanBilinearTensorCoeff_one_eq_rectRightCoeff
    (N v l y d : ℕ) (t : ℤ)
    (hd : 0 < d) (ht : 1 ≤ t) (hdt : (d : ℤ) * t ≤ y) :
    vaughanBilinearTensorCoeff vaughanMangoldtCoeff (fun _ => 1) y d
        (vaughanCanonicalDyadicBlock N v l) t =
      vaughanTypeIIRectRightCoeff N v l t := by
  rw [vaughanBilinearTensorCoeff_eq_fiber]
  · unfold vaughanTypeIIRectRightCoeff vaughanTensorFiber
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e he
    have he0 : 0 < e := (mem_vaughanCanonicalDyadicBlock.mp he).1
    have ht0 : 0 ≤ t := le_trans (by norm_num) ht
    have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht0
    by_cases het : e ∣ t.toNat
    · rw [if_pos het, if_pos]
      · simp
      · obtain ⟨m, hm⟩ := het
        have htNatPos : 0 < t.toNat := by
          rw [← Int.natCast_pos, htcast]
          omega
        have hm0 : 0 < m := by
          by_contra hm0
          simp only [not_lt, Nat.le_zero] at hm0
          subst m
          simp at hm htNatPos
          omega
        have hmet : ((e * m : ℕ) : ℤ) = t := by
          rw [← hm, htcast]
        refine ⟨m, Finset.mem_Icc.mpr ⟨hm0, ?_⟩, ?_⟩
        · apply (Nat.le_div_iff_mul_le (Nat.mul_pos hd he0)).2
          exact_mod_cast (show (m : ℤ) * ((d : ℤ) * e) ≤ y by
            calc
              (m : ℤ) * ((d : ℤ) * e) = (d : ℤ) * (e * m) := by ring
              _ = (d : ℤ) * t := by rw [← Nat.cast_mul, hmet]
              _ ≤ y := hdt)
        · exact hmet
    · rw [if_neg het, if_neg]
      rintro ⟨m, hm, hprod⟩
      apply het
      refine ⟨m, ?_⟩
      apply Int.ofNat_inj.mp
      rw [htcast]
      simpa using hprod.symm
  · intro e he
    exact (mem_vaughanCanonicalDyadicBlock.mp he).1

private theorem vaughanBilinearTensorCoeff_one_eq_ite_rectRightCoeff
    (N v l y d : ℕ) (t : ℤ) (hd : 0 < d) (ht : 1 ≤ t) :
    vaughanBilinearTensorCoeff vaughanMangoldtCoeff (fun _ => 1) y d
        (vaughanCanonicalDyadicBlock N v l) t =
      if (d : ℤ) * t ≤ y then vaughanTypeIIRectRightCoeff N v l t else 0 := by
  by_cases hdt : (d : ℤ) * t ≤ y
  · rw [if_pos hdt]
    exact vaughanBilinearTensorCoeff_one_eq_rectRightCoeff N v l y d t hd ht hdt
  · rw [if_neg hdt]
    unfold vaughanBilinearTensorCoeff
    apply Finset.sum_eq_zero
    intro e he
    apply Finset.sum_eq_zero
    intro m hm
    rw [if_neg]
    intro hem
    apply hdt
    have he0 : 0 < e := (mem_vaughanCanonicalDyadicBlock.mp he).1
    have hde : 0 < d * e := Nat.mul_pos hd he0
    have hprod : d * e * m ≤ y := by
      simpa [mul_comm] using
        (Nat.le_div_iff_mul_le hde).mp (Finset.mem_Icc.mp hm).2
    exact_mod_cast (show (d : ℤ) * t ≤ y by
      rw [← hem]
      exact_mod_cast (by simpa [mul_assoc] using hprod))

private theorem vaughanTypeIIRectRightCoeff_eq_zero_of_lt
    (N v l : ℕ) (t : ℤ) (ht : 1 ≤ t) (hlt : t < (2 ^ l : ℕ)) :
    vaughanTypeIIRectRightCoeff N v l t = 0 := by
  unfold vaughanTypeIIRectRightCoeff
  apply Finset.sum_eq_zero
  intro e he
  rw [if_neg]
  intro het
  have hepow : 2 ^ l ≤ e := (vaughanCanonicalDyadicBlock_pow_bounds he).1
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have htpos : 0 < t.toNat := by
    rw [← Int.natCast_pos, Int.toNat_of_nonneg ht0]
    omega
  have hetle : e ≤ t.toNat := Nat.le_of_dvd htpos het
  have htcast := Int.toNat_of_nonneg ht0
  exact (not_lt_of_ge (show (2 ^ l : ℤ) ≤ t by
    rw [← htcast]
    exact_mod_cast hepow.trans hetle)) hlt

private theorem sum_Icc_natCast_eq_int
    (A B : ℕ) (f : ℤ → ℂ) :
    (∑ n ∈ Finset.Icc A B, f n) =
      ∑ z ∈ Finset.Icc (A : ℤ) (B : ℤ), f z := by
  refine Finset.sum_nbij' (fun n : ℕ => (n : ℤ)) Int.toNat ?_ ?_ ?_ ?_
    (fun _ _ => rfl)
  · intro n hn
    simpa only [Finset.mem_Icc, Nat.cast_le] using hn
  · intro z hz
    obtain ⟨hA, hB⟩ := Finset.mem_Icc.mp hz
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro n hn
    exact Int.toNat_natCast n
  · intro z hz
    exact Int.toNat_of_nonneg
      ((Nat.cast_nonneg A).trans (Finset.mem_Icc.mp hz).1)

/-- On an active rectangle `(k, l)` and for `y ≤ N`, the Type-II block equals
`∑_{d t ≤ y} a_d b_t χ(d t)` over `2^k ≤ d < 2^{k+1}` and `2^l ≤ t ≤ N / 2^k`. -/
theorem vaughanTypeIICanonicalBilinearBlock_eq_rectangularSharp
    (y N u v k l q : ℕ) (χ : PrimitiveCharacter q)
    (hyN : y ≤ N)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    vaughanTypeIICanonicalBilinearBlock (fun _ => 1) y N u v k l q χ =
      rectangularSharpHyperbolicCharacterSum
        (vaughanTypeIIRectLeftCoeff N u k)
        (vaughanTypeIIRectRightCoeff N v l) y
        ((2 ^ k : ℤ) - 1) ((2 ^ l : ℤ) - 1)
        (2 ^ k) (N / 2 ^ k - 2 ^ l + 1) q χ := by
  have hDS : ∀ d ∈ vaughanCanonicalDyadicBlock N u k, 0 < d :=
    fun d hd => (mem_vaughanCanonicalDyadicBlock.mp hd).1
  have hES : ∀ e ∈ vaughanCanonicalDyadicBlock N v l, 0 < e :=
    fun e he => (mem_vaughanCanonicalDyadicBlock.mp he).1
  have hactive' : 2 ^ k * 2 ^ l ≤ N := by
    simpa using (mem_vaughanTypeIIActiveCanonicalRectangles.mp hactive).2
  have hlDiv : 2 ^ l ≤ N / 2 ^ k :=
    (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ k)).2 (by
      simpa [mul_comm] using hactive')
  let F : ℕ → ℤ → ℂ := fun d t =>
    (vaughanMoebiusCoeff d * χ.1 (d : ZMod q)) *
      ((if (d : ℤ) * t ≤ y then vaughanTypeIIRectRightCoeff N v l t else 0) *
        χ.1 (t : ZMod q))
  change vaughanBilinearBlockOn vaughanMoebiusCoeff vaughanMangoldtCoeff
    (fun _ => 1) y (vaughanCanonicalDyadicBlock N u k)
      (vaughanCanonicalDyadicBlock N v l) q χ = _
  rw [vaughanBilinearBlockOn_eq_tensor _ _ _ _ _ _ _ _ hDS hES]
  have hleft :
      (∑ d ∈ vaughanCanonicalDyadicBlock N u k,
        (vaughanMoebiusCoeff d * χ.1 (d : ZMod q)) *
          ∑ t ∈ Finset.Icc (1 : ℤ) y,
            vaughanBilinearTensorCoeff vaughanMangoldtCoeff (fun _ => 1) y d
              (vaughanCanonicalDyadicBlock N v l) t * χ.1 (t : ZMod q)) =
      ∑ d ∈ vaughanCanonicalDyadicBlock N u k,
        ∑ t ∈ Finset.Icc (1 : ℤ) N, F d t := by
    apply Finset.sum_congr rfl
    intro d hdmem
    rw [Finset.mul_sum]
    have hsub : Finset.Icc (1 : ℤ) y ⊆ Finset.Icc (1 : ℤ) N :=
      Finset.Icc_subset_Icc_right (by exact_mod_cast hyN)
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro t htmem
      rw [vaughanBilinearTensorCoeff_one_eq_ite_rectRightCoeff
        N v l y d t (hDS d hdmem) (Finset.mem_Icc.mp htmem).1]
    · intro t htN hty
      have htgt : (y : ℤ) < t := by
        simp only [Finset.mem_Icc] at hty
        have := (Finset.mem_Icc.mp htN).1
        omega
      have hnot : ¬ (d : ℤ) * t ≤ y := by
        have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast hDS d hdmem
        nlinarith
      simp [F, hnot]
  rw [hleft]
  have hkEnd : (2 ^ k : ℤ) - 1 + (2 ^ k : ℕ) =
      ((2 ^ (k + 1) - 1 : ℕ) : ℤ) := by
    have hone : 1 ≤ 2 ^ (k + 1) := by
      have hpos : 0 < (2 : ℕ) ^ (k + 1) := pow_pos (by norm_num) _
      omega
    rw [Nat.cast_sub hone]
    push_cast
    rw [pow_succ]
    ring
  have hlEnd : (2 ^ l : ℤ) - 1 + (N / 2 ^ k - 2 ^ l + 1 : ℕ) =
      (N / 2 ^ k : ℕ) := by
    rw [Nat.cast_add, Nat.cast_sub hlDiv]
    push_cast
    ring
  unfold rectangularSharpHyperbolicCharacterSum
  rw [show (2 ^ k : ℤ) - 1 + 1 = ((2 ^ k : ℕ) : ℤ) by norm_num,
    hkEnd, show (2 ^ l : ℤ) - 1 + 1 = ((2 ^ l : ℕ) : ℤ) by norm_num, hlEnd]
  rw [← sum_Icc_natCast_eq_int (2 ^ k) (2 ^ (k + 1) - 1)]
  have hdSubset : vaughanCanonicalDyadicBlock N u k ⊆
      Finset.Icc (2 ^ k) (2 ^ (k + 1) - 1) := by
    intro d hdmem
    have hb := vaughanCanonicalDyadicBlock_pow_bounds hdmem
    exact Finset.mem_Icc.mpr ⟨hb.1, by omega⟩
  rw [← Finset.sum_subset hdSubset]
  · apply Finset.sum_congr rfl
    intro d hdmem
    have hdpos := hDS d hdmem
    simp only [vaughanTypeIIRectLeftCoeff, Int.toNat_natCast, if_pos hdmem]
    refine Eq.trans (sum_Icc_natCast_eq_int 1 N (F d)).symm ?_
    refine Eq.trans ?_ (sum_Icc_natCast_eq_int (2 ^ l) (N / 2 ^ k)
      (fun x => vaughanMoebiusCoeff d * vaughanTypeIIRectRightCoeff N v l x *
        χ.1 (((d : ℤ) * x : ℤ) : ZMod q) *
          if (d : ℤ) * x ≤ y then 1 else 0))
    have htSubset : Finset.Icc (2 ^ l : ℕ) (N / 2 ^ k) ⊆
        Finset.Icc (1 : ℕ) N := by
      intro t htmem
      have htI := Finset.mem_Icc.mp htmem
      have hlpos : 0 < (2 : ℕ) ^ l := pow_pos (by norm_num) _
      exact Finset.mem_Icc.mpr ⟨hlpos.trans_le htI.1,
        htI.2.trans (Nat.div_le_self _ _)⟩
    rw [← Finset.sum_subset htSubset]
    · apply Finset.sum_congr rfl
      intro t htmem
      dsimp [F]
      by_cases hdt : (d : ℤ) * (t : ℤ) ≤ y
      · simp [hdt]
        ring
      · simp [hdt]
    · intro t htN htRect
      have htN' := Finset.mem_Icc.mp htN
      simp only [Finset.mem_Icc] at htRect
      by_cases hlow : (t : ℕ) < 2 ^ l
      · dsimp [F]
        rw [vaughanTypeIIRectRightCoeff_eq_zero_of_lt N v l t]
        · simp []
        · exact_mod_cast htN'.1
        · exact_mod_cast hlow
      · have hhigh : N / 2 ^ k < t := by omega
        have hdk : 2 ^ k ≤ d := (vaughanCanonicalDyadicBlock_pow_bounds hdmem).1
        have hnot : ¬ (d : ℤ) * (t : ℤ) ≤ y := by
          have hmul : N < d * t := by
            have hbase : N < t * 2 ^ k :=
              (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ k)).mp hhigh
            have hbase' : N < 2 ^ k * t := by simpa [mul_comm] using hbase
            exact hbase'.trans_le (Nat.mul_le_mul_right t hdk)
          exact_mod_cast (not_le_of_gt (hyN.trans_lt hmul))
        simp [F, hnot]
  · intro d hdFull hdNot
    simp [vaughanTypeIIRectLeftCoeff, hdNot]

/-! ## The prefix-maximal large sieve on one rectangle -/

/-- `max_{y ≤ N} |∑_{d e m ≤ y} μ(d) Λ(e) χ(d e m)|` on the dyadic rectangle `(k, l)`. -/
def vaughanTypeIIRectAmplitude
    (N u v k l q : ℕ) (χ : PrimitiveCharacter q) : ℝ :=
  Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ)

/-- `∑_{q ∈ S} (q / φ(q)) ∑_χ` of that maximum, over primitive `χ` mod `q`. -/
def vaughanTypeIIRectWeightedMean
    (N u v k l : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
    ∑ χ : PrimitiveCharacter q,
      vaughanTypeIIRectAmplitude N u v k l q χ

/-- On an active rectangle the maximum equals `max_{Y ≤ N} |∑_{d t ≤ Y} a_d b_t χ(d t)|`. -/
theorem vaughanTypeIIRectAmplitude_eq_sharp
    (N u v k l q : ℕ) (χ : PrimitiveCharacter q)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    vaughanTypeIIRectAmplitude N u v k l q χ =
      rectangularSharpHyperbolicPrefixMaxAmplitudeUpTo
        (vaughanTypeIIRectLeftCoeff N u k)
        (vaughanTypeIIRectRightCoeff N v l) N
        ((2 ^ k : ℤ) - 1) ((2 ^ l : ℤ) - 1)
        (2 ^ k) (N / 2 ^ k - 2 ^ l + 1) q χ := by
  unfold vaughanTypeIIRectAmplitude
  unfold rectangularSharpHyperbolicPrefixMaxAmplitudeUpTo
  congr 1
  unfold vaughanCanonicalCollectedPrefixMaxSquare
  unfold rectangularSharpHyperbolicPrefixMaxSquareUpTo
  congr 1
  apply Finset.image_congr
  intro Y hY
  dsimp only
  rw [vaughanTypeIICanonicalBilinearBlock_eq_rectangularSharp
    Y N u v k l q χ (Nat.le_of_lt_succ (Finset.mem_range.mp hY)) hactive]

theorem vaughanTypeIIRectWeightedMean_eq_sharp
    (N u v k l : ℕ) (S : Finset ℕ)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    vaughanTypeIIRectWeightedMean N u v k l S =
      rectangularSharpHyperbolicPrefixMaxWeightedPrimitiveMeanUpTo
        (vaughanTypeIIRectLeftCoeff N u k)
        (vaughanTypeIIRectRightCoeff N v l) N
        ((2 ^ k : ℤ) - 1) ((2 ^ l : ℤ) - 1)
        (2 ^ k) (N / 2 ^ k - 2 ^ l + 1) S := by
  unfold vaughanTypeIIRectWeightedMean
  unfold rectangularSharpHyperbolicPrefixMaxWeightedPrimitiveMeanUpTo
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  apply Finset.sum_congr rfl
  intro χ hχ
  exact vaughanTypeIIRectAmplitude_eq_sharp
    N u v k l q χ hactive

/-- The large sieve on one active rectangle, for conductors `S ⊆ [1, Q]`: the weighted
mean is a logarithmic multiple of the rank-one large-sieve term, plus
`8 / (2πN)` times `(∑ |a_d|) (∑ |b_t|)` times the mass of the primitive family. -/
theorem vaughanTypeIIRectWeightedMean_le
    (N Q u v k l : ℕ) (hN : 3 ≤ N) (hQ : 0 < Q)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    vaughanTypeIIRectWeightedMean N u v k l S ≤
      (1 / 2 + (14 * Real.log ((2 * N : ℕ) : ℝ) + 4) / Real.pi) *
        rankOneRectangularLSRHS
          (vaughanTypeIIRectLeftCoeff N u k)
          (vaughanTypeIIRectRightCoeff N v l)
          ((2 ^ k : ℤ) - 1) ((2 ^ l : ℤ) - 1)
          (2 ^ k) (N / 2 ^ k - 2 ^ l + 1) Q +
      (8 / (Real.pi * ((2 * N : ℕ) : ℝ))) *
        rectangularCoefficientL1
          (vaughanTypeIIRectLeftCoeff N u k)
          (vaughanTypeIIRectRightCoeff N v l)
          ((2 ^ k : ℤ) - 1) ((2 ^ l : ℤ) - 1)
          (2 ^ k) (N / 2 ^ k - 2 ^ l + 1) *
        weightedPrimitiveFamilyMass S := by
  rw [vaughanTypeIIRectWeightedMean_eq_sharp
    N u v k l S hactive]
  have hcorner : 2 ^ k * 2 ^ l ≤ N :=
    (mem_vaughanTypeIIActiveCanonicalRectangles.mp hactive).2
  have hkpos : 0 < 2 ^ k := by positivity
  have hlpos : 0 < 2 ^ l := by positivity
  have hkN : 2 ^ k ≤ N := by
    exact (le_mul_of_one_le_right (Nat.zero_le _) (Nat.one_le_iff_ne_zero.mpr
      (pow_ne_zero _ (by norm_num)))).trans hcorner
  have hlDiv : 2 ^ l ≤ N / 2 ^ k :=
    (Nat.le_div_iff_mul_le hkpos).2 (by simpa [mul_comm] using hcorner)
  have hkone : (1 : ℤ) ≤ (2 ^ k : ℕ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)))
  have hlone : (1 : ℤ) ≤ (2 ^ l : ℕ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)))
  have hmEnd : (2 ^ k : ℤ) - 1 + (2 ^ k : ℕ) =
      (2 : ℤ) * (2 ^ k : ℕ) - 1 := by
    push_cast
    ring
  have hnEnd : (2 ^ l : ℤ) - 1 + (N / 2 ^ k - 2 ^ l + 1 : ℕ) =
      (N / 2 ^ k : ℕ) := by
    rw [Nat.cast_add, Nat.cast_sub hlDiv]
    push_cast
    ring
  have hmBounds : ∀ m ∈ Finset.Icc ((2 ^ k : ℤ) - 1 + 1)
      ((2 ^ k : ℤ) - 1 + (2 ^ k : ℕ)),
      1 ≤ m ∧ m ≤ (2 : ℤ) * (2 ^ k : ℕ) - 1 := by
    intro m hm
    have hm' := Finset.mem_Icc.mp hm
    rw [hmEnd] at hm'
    omega
  have hnBounds : ∀ n ∈ Finset.Icc ((2 ^ l : ℤ) - 1 + 1)
      ((2 ^ l : ℤ) - 1 + (N / 2 ^ k - 2 ^ l + 1 : ℕ)),
      1 ≤ n ∧ n ≤ (N / 2 ^ k : ℕ) := by
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    rw [hnEnd] at hn'
    omega
  apply rectangularSharpPrefixMaxMean_le
    (vaughanTypeIIRectLeftCoeff N u k)
    (vaughanTypeIIRectRightCoeff N v l)
    ((2 ^ k : ℤ) - 1) ((2 ^ l : ℤ) - 1)
    (2 ^ k) (N / 2 ^ k - 2 ^ l + 1) Q N (2 * N)
    hQ S hS (by omega) (by omega)
  · intro m hm
    exact (hmBounds m hm).1
  · intro m hm
    have hmUpper := (hmBounds m hm).2
    have hkcast : ((2 ^ k : ℕ) : ℤ) ≤ N := by exact_mod_cast hkN
    omega
  · intro n hn
    exact (hnBounds n hn).1
  · intro n hn
    have hnUpper := (hnBounds n hn).2
    have hdivN : N / 2 ^ k ≤ N := Nat.div_le_self _ _
    have hdivN' : ((N / 2 ^ k : ℕ) : ℤ) ≤ N := by exact_mod_cast hdivN
    omega
  · intro m hm n hn
    nlinarith only [(hmBounds m hm).1, (hnBounds n hn).1]
  · intro m hm n hn
    have hm' := hmBounds m hm
    have hn' := hnBounds n hn
    have hmUpper : m ≤ (2 : ℤ) * (2 ^ k : ℕ) := by omega
    have hnUpper : n ≤ (N / 2 ^ k : ℕ) := hn'.2
    have hmulDiv : 2 ^ k * (N / 2 ^ k) ≤ N := Nat.mul_div_le N (2 ^ k)
    have hnnonneg : 0 ≤ n := by omega
    calc
      m * n ≤ ((2 : ℤ) * (2 ^ k : ℕ)) * n :=
        mul_le_mul_of_nonneg_right hmUpper hnnonneg
      _ ≤ ((2 : ℤ) * (2 ^ k : ℕ)) * (N / 2 ^ k : ℕ) :=
        mul_le_mul_of_nonneg_left hnUpper (by positivity)
      _ = (2 : ℤ) * ((2 ^ k : ℕ) * (N / 2 ^ k : ℕ)) := by ring
      _ ≤ (2 : ℤ) * N := by
        gcongr
        exact_mod_cast hmulDiv

/-! ## Coefficient energies -/

theorem finite_norm_sum_sq_le_card_mul_energy
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (a : ι → ℂ) :
    (∑ x ∈ S, ‖a x‖) ^ 2 ≤
      (S.card : ℝ) * ∑ x ∈ S, Complex.normSq (a x) := by
  calc
    (∑ x ∈ S, ‖a x‖) ^ 2 ≤
        (∑ x ∈ S, ‖a x‖ ^ 2) * (∑ _x ∈ S, (1 : ℝ) ^ 2) := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq S
        (fun x => ‖a x‖) (fun _ => (1 : ℝ))
    _ = (S.card : ℝ) * ∑ x ∈ S, Complex.normSq (a x) := by
      simp [Complex.normSq_eq_norm_sq, mul_comm]

/-- `∑ |a_d|^2 ≤ 2^k` over `2^k ≤ d < 2^{k+1}`, since `|μ(d)| ≤ 1`. -/
theorem vaughanTypeIIRectLeftCoeff_energy_le
    (N u k : ℕ) :
    (∑ d ∈ Finset.Icc ((2 ^ k : ℕ) : ℤ)
        (((2 ^ (k + 1) - 1 : ℕ) : ℤ)),
      Complex.normSq (vaughanTypeIIRectLeftCoeff N u k d)) ≤
      ((2 ^ k : ℕ) : ℝ) := by
  calc
    _ ≤ ∑ _d ∈ Finset.Icc ((2 ^ k : ℕ) : ℤ)
        (((2 ^ (k + 1) - 1 : ℕ) : ℤ)), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      unfold vaughanTypeIIRectLeftCoeff
      split_ifs with h
      · rw [Complex.normSq_eq_norm_sq]
        rcases ArithmeticFunction.moebius_eq_or d.toNat with hμ | hμ | hμ <;>
          simp [vaughanMoebiusCoeff, hμ]
      · simp
    _ = ((2 ^ k : ℕ) : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      norm_cast
      rw [Int.card_Icc]
      have hp : 1 ≤ 2 ^ (k + 1) := (Nat.one_le_iff_ne_zero).2 (pow_ne_zero _ (by norm_num))
      rw [Nat.cast_sub hp]
      have heq : (((2 ^ (k + 1) : ℕ) : ℤ) - (1 : ℕ) + 1 -
          ((2 ^ k : ℕ) : ℤ)) = ((2 ^ k : ℕ) : ℤ) := by
        push_cast
        rw [pow_succ]
        ring
      rw [heq, Int.toNat_natCast]

theorem normSq_finset_sum_le_card_mul_energy
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (a : ι → ℂ) :
    Complex.normSq (∑ x ∈ S, a x) ≤
      (S.card : ℝ) * ∑ x ∈ S, Complex.normSq (a x) := by
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖∑ x ∈ S, a x‖ ^ 2 ≤ (∑ x ∈ S, ‖a x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S a) 2
    _ ≤ _ := finite_norm_sum_sq_le_card_mul_energy S a

private theorem vaughanTypeIIRectRightCoeff_normSq_le_divisor
    (N v l X : ℕ) (t : ℤ) (ht : t ∈ Finset.Icc (1 : ℤ) X) :
    Complex.normSq (vaughanTypeIIRectRightCoeff N v l t) ≤
      (t.toNat.divisors.card : ℝ) ^ 2 * Real.log (X + 1 : ℕ) ^ 2 := by
  let S := (vaughanCanonicalDyadicBlock N v l).filter (fun e => e ∣ t.toNat)
  have htI := Finset.mem_Icc.mp ht
  have htpos : 0 < t := lt_of_lt_of_le Int.zero_lt_one htI.1
  have htnatpos : 0 < t.toNat := by omega
  have htX : t.toNat ≤ X := by
    have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg htpos.le
    exact_mod_cast htcast.trans_le htI.2
  have hSsub : S ⊆ t.toNat.divisors := by
    intro e he
    have he' := Finset.mem_filter.mp he
    exact Nat.mem_divisors.mpr ⟨he'.2, htnatpos.ne'⟩
  have hcard : (S.card : ℝ) ≤ (t.toNat.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hSsub
  have hterm : ∀ e ∈ S,
      Complex.normSq (vaughanMangoldtCoeff e) ≤ Real.log (X + 1 : ℕ) ^ 2 := by
    intro e he
    have he' := Finset.mem_filter.mp he
    have hepos : 0 < e := (mem_vaughanCanonicalDyadicBlock.mp he'.1).1
    have het : e ≤ t.toNat := Nat.le_of_dvd htnatpos he'.2
    have hlog : Real.log (e : ℝ) ≤ Real.log (X + 1 : ℕ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · show (0 : ℝ) < e
        exact_mod_cast hepos
      · show (0 : ℝ) < (X + 1 : ℕ)
        positivity
      · exact_mod_cast (het.trans htX).trans (Nat.le_succ X)
    rw [Complex.normSq_eq_norm_sq]
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    calc
      ‖vaughanMangoldtCoeff e‖ = ArithmeticFunction.vonMangoldt e := by
        simp [vaughanMangoldtCoeff,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      _ ≤ Real.log (e : ℝ) := ArithmeticFunction.vonMangoldt_le_log
      _ ≤ Real.log (X + 1 : ℕ) := hlog
  have henergy : (∑ e ∈ S, Complex.normSq (vaughanMangoldtCoeff e)) ≤
      (S.card : ℝ) * Real.log (X + 1 : ℕ) ^ 2 := by
    calc
      _ ≤ ∑ _e ∈ S, Real.log (X + 1 : ℕ) ^ 2 := Finset.sum_le_sum hterm
      _ = _ := by simp
  have hrewrite : vaughanTypeIIRectRightCoeff N v l t =
      ∑ e ∈ S, vaughanMangoldtCoeff e := by
    unfold vaughanTypeIIRectRightCoeff S
    rw [Finset.sum_filter]
  rw [hrewrite]
  calc
    Complex.normSq (∑ e ∈ S, vaughanMangoldtCoeff e) ≤
        (S.card : ℝ) * ∑ e ∈ S, Complex.normSq (vaughanMangoldtCoeff e) :=
      normSq_finset_sum_le_card_mul_energy S _
    _ ≤ (S.card : ℝ) * ((S.card : ℝ) * Real.log (X + 1 : ℕ) ^ 2) := by
      gcongr
    _ ≤ (t.toNat.divisors.card : ℝ) *
        ((t.toNat.divisors.card : ℝ) * Real.log (X + 1 : ℕ) ^ 2) := by
      gcongr
    _ = (t.toNat.divisors.card : ℝ) ^ 2 * Real.log (X + 1 : ℕ) ^ 2 := by ring

/-- `∑ |b_t|^2 ≤ 27 X log(X+1)^5` over `2^l ≤ t ≤ X = N / 2^k`, from
`|b_t| ≤ τ(t) log(X+1)` and `∑_{t ≤ X} τ(t)^2 ≤ 27 X log(X+1)^3`. -/
theorem vaughanTypeIIRectRightCoeff_energy_le
    (N v k l : ℕ) :
    (∑ t ∈ Finset.Icc ((2 ^ l : ℕ) : ℤ) ((N / 2 ^ k : ℕ) : ℤ),
      Complex.normSq (vaughanTypeIIRectRightCoeff N v l t)) ≤
      27 * ((N / 2 ^ k : ℕ) : ℝ) *
        Real.log (N / 2 ^ k + 1 : ℕ) ^ 5 := by
  let X := N / 2 ^ k
  have hsub : Finset.Icc ((2 ^ l : ℕ) : ℤ) (X : ℤ) ⊆
      Finset.Icc (1 : ℤ) (X : ℤ) := by
    intro t ht
    have hpow : 1 ≤ 2 ^ l :=
      (Nat.one_le_iff_ne_zero).2 (pow_ne_zero _ (by norm_num))
    exact Finset.mem_Icc.mpr ⟨
      (show (1 : ℤ) ≤ (2 ^ l : ℕ) by exact_mod_cast hpow).trans
        (Finset.mem_Icc.mp ht).1,
      (Finset.mem_Icc.mp ht).2⟩
  calc
    (∑ t ∈ Finset.Icc ((2 ^ l : ℕ) : ℤ) (X : ℤ),
        Complex.normSq (vaughanTypeIIRectRightCoeff N v l t)) ≤
      ∑ t ∈ Finset.Icc (1 : ℤ) (X : ℤ),
        Complex.normSq (vaughanTypeIIRectRightCoeff N v l t) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun t ht hnot => Complex.normSq_nonneg _)
    _ ≤ ∑ t ∈ Finset.Icc (1 : ℤ) (X : ℤ),
        (t.toNat.divisors.card : ℝ) ^ 2 * Real.log (X + 1 : ℕ) ^ 2 := by
          exact Finset.sum_le_sum fun t ht =>
            vaughanTypeIIRectRightCoeff_normSq_le_divisor N v l X t ht
    _ = divisorSquarePrefix X * Real.log (X + 1 : ℕ) ^ 2 := by
          unfold divisorSquarePrefix
          rw [Finset.sum_mul]
    _ ≤ (27 * (X : ℝ) * Real.log (X + 1 : ℕ) ^ 3) *
        Real.log (X + 1 : ℕ) ^ 2 := by
          gcongr
          exact divisorSquareMomentBound_27 X
    _ = 27 * (X : ℝ) * Real.log (X + 1 : ℕ) ^ 5 := by ring
    _ = 27 * ((N / 2 ^ k : ℕ) : ℝ) *
        Real.log (N / 2 ^ k + 1 : ℕ) ^ 5 := by rfl

/-!
## Explicit bound for one rectangle

The coefficient energies and the `L¹` mass are replaced by explicit bounds in terms
of `D = 2^k`, `X = N / 2^k` and `T = X - 2^l + 1`.
-/

/-- `X = N / 2^k`, the upper end of the `t`-range. -/
def vaughanTypeIIRectangularX (N k : ℕ) : ℕ := N / 2 ^ k

/-- `D = 2^k`, the length of the `d`-range. -/
def vaughanTypeIIRectangularD (k : ℕ) : ℕ := 2 ^ k

/-- `T = X - 2^l + 1`, the length of the `t`-range. -/
def vaughanTypeIIRectangularT (N k l : ℕ) : ℕ :=
  vaughanTypeIIRectangularX N k - 2 ^ l + 1

/-- `E = 27 X log(X+1)^5`, the bound for `∑ |b_t|^2`. -/
def vaughanTypeIIRectangularEright (N k : ℕ) : ℝ :=
  27 * (vaughanTypeIIRectangularX N k : ℝ) *
    Real.log (vaughanTypeIIRectangularX N k + 1 : ℕ) ^ 5

/-- `√(Δ(D) D) √(Δ(T) E)` with `Δ(M) = largeSieveBound M (1/Q^2)`: the rank-one
large-sieve term with the coefficient energies replaced by `D` and `E`. -/
def vaughanTypeIIRectangularRexp (N k l Q : ℕ) : ℝ :=
  Real.sqrt (largeSieveBound (vaughanTypeIIRectangularD k)
      (1 / (Q : ℝ) ^ 2) * (vaughanTypeIIRectangularD k : ℝ)) *
    Real.sqrt (largeSieveBound (vaughanTypeIIRectangularT N k l)
      (1 / (Q : ℝ) ^ 2) * vaughanTypeIIRectangularEright N k)

/-- `√(D D) √(T E)`, the Cauchy–Schwarz bound for `(∑ |a_d|) (∑ |b_t|)`. -/
def vaughanTypeIIRectangularL1exp (N k l : ℕ) : ℝ :=
  Real.sqrt ((vaughanTypeIIRectangularD k : ℝ) *
      (vaughanTypeIIRectangularD k : ℝ)) *
    Real.sqrt ((vaughanTypeIIRectangularT N k l : ℝ) *
      vaughanTypeIIRectangularEright N k)

private theorem active_geometry
    (N u v k l : ℕ)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    2 ^ l ≤ N / 2 ^ k := by
  have hcorner : 2 ^ k * 2 ^ l ≤ N :=
    (mem_vaughanTypeIIActiveCanonicalRectangles.mp hactive).2
  exact (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ k)).2
    (by simpa [mul_comm] using hcorner)

private theorem left_upper_endpoint (k : ℕ) :
    (2 ^ k : ℤ) - 1 + (2 ^ k : ℕ) =
      (((2 ^ (k + 1) - 1 : ℕ) : ℤ)) := by
  have hp : 1 ≤ 2 ^ (k + 1) :=
    (Nat.one_le_iff_ne_zero).2 (pow_ne_zero _ (by norm_num))
  rw [Nat.cast_sub hp, pow_succ]
  push_cast
  ring

private theorem right_upper_endpoint
    (N u v k l : ℕ)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    (2 ^ l : ℤ) - 1 + (N / 2 ^ k - 2 ^ l + 1 : ℕ) =
      ((N / 2 ^ k : ℕ) : ℤ) := by
  have hl := active_geometry N u v k l hactive
  rw [Nat.cast_add, Nat.cast_sub hl]
  push_cast
  ring

private theorem rectangular_cards
    (N u v k l : ℕ)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    (Finset.Icc ((2 ^ k : ℕ) : ℤ)
        (((2 ^ (k + 1) - 1 : ℕ) : ℤ))).card = 2 ^ k ∧
    (Finset.Icc ((2 ^ l : ℕ) : ℤ)
        ((N / 2 ^ k : ℕ) : ℤ)).card =
      N / 2 ^ k - 2 ^ l + 1 := by
  have hl := active_geometry N u v k l hactive
  constructor
  · rw [Int.card_Icc]
    have hp : 1 ≤ 2 ^ (k + 1) :=
      (Nat.one_le_iff_ne_zero).2 (pow_ne_zero _ (by norm_num))
    have heq : ((((2 ^ (k + 1) - 1 : ℕ) : ℤ) + 1 - (2 ^ k : ℕ))) =
        ((2 ^ k : ℕ) : ℤ) := by
      rw [Nat.cast_sub hp, pow_succ]
      push_cast
      ring
    rw [heq, Int.toNat_natCast]
  · rw [Int.card_Icc]
    have heq : (((N / 2 ^ k : ℕ) : ℤ) + 1 - (2 ^ l : ℕ)) =
        ((N / 2 ^ k - 2 ^ l + 1 : ℕ) : ℤ) := by
      rw [Nat.cast_add, Nat.cast_sub hl]
      push_cast
      ring
    rw [heq, Int.toNat_natCast]

theorem vaughanTypeIIRectangular_rankOneRectangularLSRHS_le_Rexp
    (N u v k l Q : ℕ) (hQ : 0 < Q)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    rankOneRectangularLSRHS
        (vaughanTypeIIRectLeftCoeff N u k)
        (vaughanTypeIIRectRightCoeff N v l)
        ((2 ^ k : ℤ) - 1) ((2 ^ l : ℤ) - 1)
        (2 ^ k) (N / 2 ^ k - 2 ^ l + 1) Q ≤
      vaughanTypeIIRectangularRexp N k l Q := by
  have hleft := vaughanTypeIIRectLeftCoeff_energy_le N u k
  have hright := vaughanTypeIIRectRightCoeff_energy_le N v k l
  have hdelta : 0 < (1 / (Q : ℝ) ^ 2) := by positivity
  have hCD : 0 ≤ largeSieveBound (2 ^ k) (1 / (Q : ℝ) ^ 2) :=
    largeSieveBound_nonneg _ hdelta
  have hCT : 0 ≤ largeSieveBound (N / 2 ^ k - 2 ^ l + 1)
      (1 / (Q : ℝ) ^ 2) := largeSieveBound_nonneg _ hdelta
  unfold rankOneRectangularLSRHS vaughanTypeIIRectangularRexp
    vaughanTypeIIRectangularD vaughanTypeIIRectangularT
    vaughanTypeIIRectangularEright vaughanTypeIIRectangularX
  rw [show (2 ^ k : ℤ) - 1 + 1 = ((2 ^ k : ℕ) : ℤ) by norm_num,
    left_upper_endpoint k,
    show (2 ^ l : ℤ) - 1 + 1 = ((2 ^ l : ℕ) : ℤ) by norm_num,
    right_upper_endpoint N u v k l hactive]
  apply mul_le_mul
  · apply Real.sqrt_le_sqrt
    apply mul_le_mul_of_nonneg_left _ hCD
    simpa [Complex.normSq_eq_norm_sq] using hleft
  · apply Real.sqrt_le_sqrt
    apply mul_le_mul_of_nonneg_left _ hCT
    simpa [Complex.normSq_eq_norm_sq] using hright
  · positivity
  · positivity

theorem vaughanTypeIIRectangular_rectangularCoefficientL1_le_L1exp
    (N u v k l : ℕ)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    rectangularCoefficientL1
        (vaughanTypeIIRectLeftCoeff N u k)
        (vaughanTypeIIRectRightCoeff N v l)
        ((2 ^ k : ℤ) - 1) ((2 ^ l : ℤ) - 1)
        (2 ^ k) (N / 2 ^ k - 2 ^ l + 1) ≤
      vaughanTypeIIRectangularL1exp N k l := by
  let A : ℝ := ∑ m ∈ Finset.Icc ((2 ^ k : ℕ) : ℤ)
      (((2 ^ (k + 1) - 1 : ℕ) : ℤ)), ‖vaughanTypeIIRectLeftCoeff N u k m‖
  let B : ℝ := ∑ n ∈ Finset.Icc ((2 ^ l : ℕ) : ℤ)
      ((N / 2 ^ k : ℕ) : ℤ),
      ‖vaughanTypeIIRectRightCoeff N v l n‖
  have hcards := rectangular_cards N u v k l hactive
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hAsq := finite_norm_sum_sq_le_card_mul_energy
    (Finset.Icc ((2 ^ k : ℕ) : ℤ) (((2 ^ (k + 1) - 1 : ℕ) : ℤ)))
    (vaughanTypeIIRectLeftCoeff N u k)
  have hBsq := finite_norm_sum_sq_le_card_mul_energy
    (Finset.Icc ((2 ^ l : ℕ) : ℤ) ((N / 2 ^ k : ℕ) : ℤ))
    (vaughanTypeIIRectRightCoeff N v l)
  rw [hcards.1] at hAsq
  rw [hcards.2] at hBsq
  have hleft := vaughanTypeIIRectLeftCoeff_energy_le N u k
  have hright := vaughanTypeIIRectRightCoeff_energy_le N v k l
  have hAle : A ≤ Real.sqrt (((2 ^ k : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ)) := by
    apply Real.le_sqrt_of_sq_le
    exact hAsq.trans (mul_le_mul_of_nonneg_left hleft (by positivity))
  have hBle : B ≤ Real.sqrt (((N / 2 ^ k - 2 ^ l + 1 : ℕ) : ℝ) *
      vaughanTypeIIRectangularEright N k) := by
    apply Real.le_sqrt_of_sq_le
    exact hBsq.trans (mul_le_mul_of_nonneg_left hright (by positivity))
  unfold rectangularCoefficientL1 vaughanTypeIIRectangularL1exp
    vaughanTypeIIRectangularD vaughanTypeIIRectangularT
  rw [show (2 ^ k : ℤ) - 1 + 1 = ((2 ^ k : ℕ) : ℤ) by norm_num,
    left_upper_endpoint k,
    show (2 ^ l : ℤ) - 1 + 1 = ((2 ^ l : ℕ) : ℤ) by norm_num,
    right_upper_endpoint N u v k l hactive]
  change A * B ≤ _
  exact mul_le_mul hAle hBle hB0 (Real.sqrt_nonneg _)

/-- The large sieve on one active rectangle, with the explicit bounds
`vaughanTypeIIRectangularRexp` and `vaughanTypeIIRectangularL1exp`. -/
theorem vaughanTypeIIRectWeightedMean_le_explicit
    (N Q u v k l : ℕ) (hN : 3 ≤ N) (hQ : 0 < Q)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    vaughanTypeIIRectWeightedMean N u v k l S ≤
      (1 / 2 + (14 * Real.log ((2 * N : ℕ) : ℝ) + 4) / Real.pi) *
        vaughanTypeIIRectangularRexp N k l Q +
      (8 / (Real.pi * ((2 * N : ℕ) : ℝ))) *
        vaughanTypeIIRectangularL1exp N k l * weightedPrimitiveFamilyMass S := by
  calc
    vaughanTypeIIRectWeightedMean N u v k l S ≤
        (1 / 2 + (14 * Real.log ((2 * N : ℕ) : ℝ) + 4) / Real.pi) *
          rankOneRectangularLSRHS
            (vaughanTypeIIRectLeftCoeff N u k)
            (vaughanTypeIIRectRightCoeff N v l)
            ((2 ^ k : ℤ) - 1) ((2 ^ l : ℤ) - 1)
            (2 ^ k) (N / 2 ^ k - 2 ^ l + 1) Q +
        (8 / (Real.pi * ((2 * N : ℕ) : ℝ))) *
          rectangularCoefficientL1
            (vaughanTypeIIRectLeftCoeff N u k)
            (vaughanTypeIIRectRightCoeff N v l)
            ((2 ^ k : ℤ) - 1) ((2 ^ l : ℤ) - 1)
            (2 ^ k) (N / 2 ^ k - 2 ^ l + 1) * weightedPrimitiveFamilyMass S :=
      vaughanTypeIIRectWeightedMean_le N Q u v k l hN hQ S hS hactive
    _ ≤ _ := by
      have hR := vaughanTypeIIRectangular_rankOneRectangularLSRHS_le_Rexp
        N u v k l Q hQ hactive
      have hL := vaughanTypeIIRectangular_rectangularCoefficientL1_le_L1exp
        N u v k l hactive
      have hdamp : 0 ≤
          (1 / 2 + (14 * Real.log ((2 * N : ℕ) : ℝ) + 4) / Real.pi) := by
        have hlog : 0 ≤ Real.log ((2 * N : ℕ) : ℝ) := by
          apply Real.log_nonneg
          exact_mod_cast (show 1 ≤ 2 * N by omega)
        positivity
      have herr : 0 ≤ 8 / (Real.pi * ((2 * N : ℕ) : ℝ)) := by positivity
      have hmass : 0 ≤ weightedPrimitiveFamilyMass S := by
        unfold weightedPrimitiveFamilyMass
        positivity
      gcongr

/-!
## Bound on one conductor cell

On a cell `S ⊆ (i, 2i]` we take `Q = 2i`, use `1/φ(q) ≤ (1/i) (q/φ(q))`, and expand
`largeSieveBound M (1/Q^2) = M + c Q^2` with `c ≤ 15 log(4N+4)`.
-/

/-- `∑_{q ∈ S} φ(q)^{-1} ∑_χ max_{y ≤ N} |∑_{d e m ≤ y} μ(d) Λ(e) χ(d e m)|` on the
rectangle `(k, l)`, over primitive `χ` mod `q`. -/
def apNormalizedVaughanTypeIIRectMeanOn
    (N u v k l : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ q ∈ S, ((q.totient : ℝ)⁻¹) *
    ∑ χ : PrimitiveCharacter q,
      Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ)

/-- If every `q ∈ S` has `q ≥ i`, then `1/φ(q) = (1/q) (q/φ(q)) ≤ (1/i) (q/φ(q))`. -/
theorem apNormalizedVaughanTypeIIRectMeanOn_le_inv_mul
    (N u v k l i : ℕ) (S : Finset ℕ) (hi : 0 < i)
    (hlevels : ∀ q ∈ S, i ≤ q) :
    apNormalizedVaughanTypeIIRectMeanOn N u v k l S ≤
      (1 / (i : ℝ)) *
        vaughanTypeIIRectWeightedMean N u v k l S := by
  unfold apNormalizedVaughanTypeIIRectMeanOn
    vaughanTypeIIRectWeightedMean
    vaughanTypeIIRectAmplitude
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hq0 : 0 < q := hi.trans_le (hlevels q hq)
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr hq0
  have hsum : 0 ≤ ∑ χ : PrimitiveCharacter q,
      Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ) := by
    positivity
  have hinv : (1 / (q : ℝ)) ≤ 1 / (i : ℝ) :=
    one_div_le_one_div_of_le (by exact_mod_cast hi)
      (by exact_mod_cast hlevels q hq)
  calc
    ((q.totient : ℝ)⁻¹) *
        (∑ χ : PrimitiveCharacter q,
          Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ)) =
      (1 / (q : ℝ)) *
        (((q : ℝ) / (q.totient : ℝ)) *
          (∑ χ : PrimitiveCharacter q,
            Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ))) := by
        field_simp
    _ ≤ (1 / (i : ℝ)) *
        (((q : ℝ) / (q.totient : ℝ)) *
          (∑ χ : PrimitiveCharacter q,
            Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ))) := by
      exact mul_le_mul_of_nonneg_right hinv
        (mul_nonneg (div_nonneg (by positivity) (by positivity)) hsum)

set_option maxHeartbeats 1600000

private lemma allAspect_log_ge_two (N : ℕ) (hN : 9 ≤ N) :
    2 ≤ Real.log (4 * N + 4 : ℕ) := by
  have harg : (16 : ℝ) ≤ (4 * N + 4 : ℕ) := by
    exact_mod_cast (show 16 ≤ 4 * N + 4 by omega)
  have hlog : Real.log (16 : ℝ) ≤ Real.log (4 * N + 4 : ℕ) :=
    Real.log_le_log (by norm_num) harg
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  rw [hlog16] at hlog
  nlinarith [Real.log_two_gt_d9]

private lemma allAspect_qFactor_le
    (N i : ℕ) (hN : 9 ≤ N) (hi : 0 < i) (h2i : 2 * i ≤ N) :
    primitiveBilinearQFactor (2 * i) ≤ 15 * Real.log (4 * N + 4 : ℕ) := by
  let L := Real.log (4 * N + 4 : ℕ)
  have hQ : 0 < 2 * i := Nat.mul_pos (by omega) hi
  have hQ1 : 1 ≤ 2 * i := hQ
  have hlog2half : (1 / 2 : ℝ) ≤ Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogpow : Real.log (((2 * i : ℕ) : ℝ) ^ 2) =
      2 * Real.log ((2 * i : ℕ) : ℝ) := by rw [Real.log_pow]; norm_num
  have hlogpow0 : 0 ≤ Real.log (((2 * i : ℕ) : ℝ) ^ 2) := by
    rw [hlogpow]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hQ1))
  have harg0 : 0 ≤ Real.log (((2 * i : ℕ) : ℝ) ^ 2) / Real.log 2 :=
    div_nonneg hlogpow0 hlog2pos.le
  have hceil := (Nat.ceil_lt_add_one harg0).le
  have hratio : Real.log (((2 * i : ℕ) : ℝ) ^ 2) / Real.log 2 ≤
      2 * Real.log (((2 * i : ℕ) : ℝ) ^ 2) := by
    apply (div_le_iff₀ hlog2pos).2
    nlinarith
  have hlogQL : Real.log ((2 * i : ℕ) : ℝ) ≤ L := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (h2i.trans (show N ≤ 4 * N + 4 by omega))
  have hlogpowL : Real.log (((2 * i : ℕ) : ℝ) ^ 2) ≤ 2 * L := by
    rw [hlogpow]
    linarith
  have hceilL :
      (Nat.ceil (Real.log (((2 * i : ℕ) : ℝ) ^ 2) / Real.log 2) : ℝ) ≤
        4 * L + 1 := hceil.trans (by linarith)
  have hL2 : 2 ≤ L := allAspect_log_ge_two N hN
  unfold primitiveBilinearQFactor
  linarith

private lemma allAspect_active_geometry
    (N u v k l : ℕ)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    1 ≤ vaughanTypeIIRectangularX N k ∧
    vaughanTypeIIRectangularT N k l ≤ vaughanTypeIIRectangularX N k ∧
    vaughanTypeIIRectangularD k * vaughanTypeIIRectangularX N k ≤ N := by
  have hcorner := (mem_vaughanTypeIIActiveCanonicalRectangles.mp hactive).2
  have hl : 2 ^ l ≤ N / 2 ^ k :=
    (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ k)).2
      (by simpa [mul_comm] using hcorner)
  constructor
  · simpa [vaughanTypeIIRectangularX] using
      (show 1 ≤ N / 2 ^ k from
        (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))).trans hl)
  constructor
  · unfold vaughanTypeIIRectangularT vaughanTypeIIRectangularX
    have hlone : 1 ≤ 2 ^ l :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
    omega
  · simpa [vaughanTypeIIRectangularD, vaughanTypeIIRectangularX] using
      Nat.mul_div_le N (2 ^ k)

private lemma allAspect_shell_lower_bounds
    (N u v k l : ℕ)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    u + 1 ≤ 2 * vaughanTypeIIRectangularD k ∧
    v + 1 ≤ 2 * 2 ^ l := by
  have hrect := (mem_vaughanTypeIIActiveCanonicalRectangles.mp hactive).1
  rw [vaughanCanonicalDyadicRectangles, Finset.mem_product] at hrect
  have hk := hrect.1
  have hl := hrect.2
  rw [mem_vaughanCanonicalDyadicBases_iff] at hk hl
  obtain ⟨d, hd, -⟩ := hk
  obtain ⟨e, he, -⟩ := hl
  have hdmem := mem_vaughanCanonicalDyadicBlock.mp hd
  have hemel := mem_vaughanCanonicalDyadicBlock.mp he
  have hdpow := (vaughanCanonicalDyadicBlock_pow_bounds hd).2
  have hepow := (vaughanCanonicalDyadicBlock_pow_bounds he).2
  constructor
  · unfold vaughanTypeIIRectangularD
    rw [pow_succ] at hdpow
    have hu' : u + 1 ≤ d := by omega
    exact hu'.trans (by simpa [mul_comm] using hdpow.le)
  · rw [pow_succ] at hepow
    have hv' : v + 1 ≤ e := by omega
    exact hv'.trans (by simpa [mul_comm] using hepow.le)

private lemma allAspect_smoothing_le (N : ℕ) (hN : 9 ≤ N) :
    1 / 2 + (14 * Real.log ((2 * N : ℕ) : ℝ) + 4) / Real.pi ≤
      8 * Real.log (4 * N + 4 : ℕ) := by
  let L := Real.log (4 * N + 4 : ℕ)
  have hL2 : 2 ≤ L := allAspect_log_ge_two N hN
  have hlog0 : 0 ≤ Real.log ((2 * N : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * N by omega))
  have hlogL : Real.log ((2 * N : ℕ) : ℝ) ≤ L := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show 2 * N ≤ 4 * N + 4 by omega)
  have hdiv : (14 * Real.log ((2 * N : ℕ) : ℝ) + 4) / Real.pi ≤
      (14 * L + 4) / 3 := by
    apply (div_le_iff₀ Real.pi_pos).2
    have hnum : 0 ≤ 14 * L + 4 := by positivity
    nlinarith [Real.pi_gt_three]
  linarith

/-- Expansion of `vaughanTypeIIRectangularRexp`, using
`largeSieveBound M (1/Q^2) = M + c Q^2` with `c = primitiveBilinearQFactor Q` and `T ≤ X`. -/
theorem vaughanTypeIIRectangularRexp_le
    (N Q u v k l : ℕ) (hQ : 0 < Q)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    vaughanTypeIIRectangularRexp N k l Q ≤
      Real.sqrt (27 * Real.log (vaughanTypeIIRectangularX N k + 1 : ℕ) ^ 5) *
        ((vaughanTypeIIRectangularD k : ℝ) * vaughanTypeIIRectangularX N k +
          primitiveBilinearQFactor Q * Q *
            ((vaughanTypeIIRectangularD k : ℝ) *
                Real.sqrt (vaughanTypeIIRectangularX N k) +
              (vaughanTypeIIRectangularX N k : ℝ) *
                Real.sqrt (vaughanTypeIIRectangularD k)) +
          primitiveBilinearQFactor Q ^ 2 * (Q : ℝ) ^ 2 *
            Real.sqrt (vaughanTypeIIRectangularD k) *
            Real.sqrt (vaughanTypeIIRectangularX N k)) := by
  let d : ℝ := vaughanTypeIIRectangularD k
  let x : ℝ := vaughanTypeIIRectangularX N k
  let t : ℝ := vaughanTypeIIRectangularT N k l
  let q : ℝ := Q
  let c : ℝ := primitiveBilinearQFactor Q
  let z : ℝ := Real.log (vaughanTypeIIRectangularX N k + 1 : ℕ) ^ 5
  let rd := Real.sqrt d
  let rx := Real.sqrt x
  have hd : 0 ≤ d := by positivity
  have hx : 0 ≤ x := by positivity
  have ht : 0 ≤ t := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hc : 1 ≤ c := by simpa [c] using one_le_primitiveBilinearQFactor Q
  have hc0 : 0 ≤ c := by linarith
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have htx : t ≤ x := by
    dsimp [t, x]
    exact_mod_cast (allAspect_active_geometry N u v k l hactive).2.1
  have hrd : 0 ≤ rd := Real.sqrt_nonneg _
  have hrx : 0 ≤ rx := Real.sqrt_nonneg _
  have hrd2 : rd ^ 2 = d := Real.sq_sqrt hd
  have hrx2 : rx ^ 2 = x := Real.sq_sqrt hx
  have hLSD : largeSieveBound (vaughanTypeIIRectangularD k)
      (1 / (Q : ℝ) ^ 2) = d + c * q ^ 2 := by
    simpa only [vaughanBilinearLargeSieveConstant, d, q, c,
      primitiveBilinearQFactor] using
      vaughanBilinearLargeSieveConstant_eq_explicit
        (vaughanTypeIIRectangularD k) Q hQ
  have hLST : largeSieveBound (vaughanTypeIIRectangularT N k l)
      (1 / (Q : ℝ) ^ 2) = t + c * q ^ 2 := by
    simpa only [vaughanBilinearLargeSieveConstant, t, q, c,
      primitiveBilinearQFactor] using
      vaughanBilinearLargeSieveConstant_eq_explicit
        (vaughanTypeIIRectangularT N k l) Q hQ
  let B : ℝ := d * x + c * q * (d * rx + x * rd) + c ^ 2 * q ^ 2 * rd * rx
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hdmaj : d + c * q ^ 2 ≤ (rd + c * q) ^ 2 := by
    rw [show d = rd ^ 2 by rw [hrd2]]
    nlinarith [mul_nonneg hc0 hq0, sq_nonneg (c - 1)]
  have hxmaj : x + c * q ^ 2 ≤ (rx + c * q) ^ 2 := by
    rw [show x = rx ^ 2 by rw [hrx2]]
    nlinarith [mul_nonneg hc0 hq0, sq_nonneg (c - 1)]
  have hcore : d * x * (d + c * q ^ 2) * (t + c * q ^ 2) ≤ B ^ 2 := by
    have htmaj : t + c * q ^ 2 ≤ x + c * q ^ 2 := add_le_add htx le_rfl
    calc
      _ ≤ d * x * (d + c * q ^ 2) * (x + c * q ^ 2) := by gcongr
      _ ≤ d * x * (rd + c * q) ^ 2 * (rx + c * q) ^ 2 := by gcongr
      _ = B ^ 2 := by dsimp [B]; rw [← hrd2, ← hrx2]; ring
  have hrad1 : 0 ≤ (d + c * q ^ 2) * d := by positivity
  have hrad2 : 0 ≤ (t + c * q ^ 2) * (27 * x * z) := by positivity
  have hradZ : 0 ≤ 27 * z := by positivity
  unfold vaughanTypeIIRectangularRexp vaughanTypeIIRectangularEright at ⊢
  rw [hLSD, hLST]
  change Real.sqrt ((d + c * q ^ 2) * d) *
      Real.sqrt ((t + c * q ^ 2) * (27 * x * z)) ≤ Real.sqrt (27 * z) * B
  have hlhs : 0 ≤ Real.sqrt ((d + c * q ^ 2) * d) *
      Real.sqrt ((t + c * q ^ 2) * (27 * x * z)) := by positivity
  have hrhs : 0 ≤ Real.sqrt (27 * z) * B := by positivity
  have hsq :
      (Real.sqrt ((d + c * q ^ 2) * d) *
        Real.sqrt ((t + c * q ^ 2) * (27 * x * z))) ^ 2 ≤
      (Real.sqrt (27 * z) * B) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hrad1, Real.sq_sqrt hrad2,
      mul_pow, Real.sq_sqrt hradZ]
    calc
      _ = 27 * z * (d * x * (d + c * q ^ 2) * (t + c * q ^ 2)) := by ring
      _ ≤ 27 * z * B ^ 2 := mul_le_mul_of_nonneg_left hcore (by positivity)
  exact le_of_sq_le_sq hsq hrhs

private lemma allAspect_root_log_le
    (N u v k l : ℕ) (hN : 9 ≤ N)
    (_hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    Real.sqrt (27 * Real.log (vaughanTypeIIRectangularX N k + 1 : ℕ) ^ 5) ≤
      6 * Real.log (4 * N + 4 : ℕ) ^ 3 := by
  let L := Real.log (4 * N + 4 : ℕ)
  let LX := Real.log (vaughanTypeIIRectangularX N k + 1 : ℕ)
  have hLX0 : 0 ≤ LX := by
    exact Real.log_nonneg (by exact_mod_cast
      (show 1 ≤ vaughanTypeIIRectangularX N k + 1 by omega))
  have hXL : vaughanTypeIIRectangularX N k + 1 ≤ 4 * N + 4 := by
    calc
      vaughanTypeIIRectangularX N k + 1 ≤ N + 1 :=
        Nat.add_le_add_right (by
          unfold vaughanTypeIIRectangularX
          exact Nat.div_le_self N (2 ^ k)) 1
      _ ≤ 4 * N + 4 := by omega
  have hLXL : LX ≤ L := Real.log_le_log (by positivity) (by exact_mod_cast hXL)
  have hL2 : 2 ≤ L := allAspect_log_ge_two N hN
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · calc
      27 * LX ^ 5 ≤ 27 * L ^ 5 := by gcongr
      _ ≤ (6 * L ^ 3) ^ 2 := by
        have hL0 : 0 ≤ L := by linarith
        nlinarith [mul_nonneg (pow_nonneg hL0 5) (sub_nonneg.mpr hL2)]

private lemma allAspect_L1exp_le
    (N u v k l : ℕ) (hN : 9 ≤ N)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    vaughanTypeIIRectangularL1exp N k l ≤
      8 * (N : ℝ) * Real.log (4 * N + 4 : ℕ) ^ 3 := by
  let L := Real.log (4 * N + 4 : ℕ)
  let X := vaughanTypeIIRectangularX N k
  let D := vaughanTypeIIRectangularD k
  let T := vaughanTypeIIRectangularT N k l
  have hg := allAspect_active_geometry N u v k l hactive
  have hTX : (T : ℝ) ≤ X := by exact_mod_cast hg.2.1
  have hDX : (D : ℝ) * X ≤ N := by exact_mod_cast hg.2.2
  have hlog0 : 0 ≤ Real.log (X + 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X + 1 by omega))
  have hlogL : Real.log (X + 1 : ℕ) ≤ L := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show X + 1 ≤ 4 * N + 4 by
      calc
        X + 1 ≤ N + 1 := Nat.add_le_add_right (by
          dsimp [X]
          unfold vaughanTypeIIRectangularX
          exact Nat.div_le_self N (2 ^ k)) 1
        _ ≤ 4 * N + 4 := by omega)
  have hL2 : 2 ≤ L := allAspect_log_ge_two N hN
  have hsqrtD : Real.sqrt ((D : ℝ) * D) = D := by
    rw [show (D : ℝ) * D = (D : ℝ) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  unfold vaughanTypeIIRectangularL1exp vaughanTypeIIRectangularEright
  change Real.sqrt ((D : ℝ) * D) *
      Real.sqrt ((T : ℝ) * (27 * (X : ℝ) * Real.log (X + 1 : ℕ) ^ 5)) ≤ _
  rw [hsqrtD]
  have hroot : Real.sqrt ((T : ℝ) *
      (27 * (X : ℝ) * Real.log (X + 1 : ℕ) ^ 5)) ≤ 8 * X * L ^ 3 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · calc
        _ ≤ (X : ℝ) * (27 * X * L ^ 5) := by gcongr
        _ ≤ (8 * X * L ^ 3) ^ 2 := by
          have hL0 : 0 ≤ L := by linarith
          nlinarith [mul_nonneg (sq_nonneg (X : ℝ)) (pow_nonneg hL0 5)]
  calc
    _ ≤ D * (8 * X * L ^ 3) := mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = (8 * L ^ 3) * (D * X) := by ring
    _ ≤ (8 * L ^ 3) * N := mul_le_mul_of_nonneg_left hDX (by positivity)
    _ = _ := by ring

private lemma allAspect_sharpTerm_le
    (N Q C u v k l i : ℕ) (G : ConductorBlockPartition N Q C)
    (hN : 9 ≤ N) (hi : 0 < i)
    (hcell : G.cell i ⊆ Finset.Ioc i (2 * i))
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    (1 / (i : ℝ)) * ((8 / (Real.pi * ((2 * N : ℕ) : ℝ))) *
      vaughanTypeIIRectangularL1exp N k l * weightedPrimitiveFamilyMass (G.cell i)) ≤
      32 * (i : ℝ) * Real.log (4 * N + 4 : ℕ) ^ 3 := by
  let L := Real.log (4 * N + 4 : ℕ)
  have hS : G.cell i ⊆ Finset.Icc 1 (2 * i) := by
    intro q hq
    have h := Finset.mem_Ioc.mp (hcell hq)
    exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
  have hm := weightedPrimitiveFamilyMass_le_triangular (2 * i) (G.cell i) hS
  have hm' : weightedPrimitiveFamilyMass (G.cell i) ≤ 3 * (i : ℝ) ^ 2 := by
    calc
      _ ≤ ((2 * i : ℕ) : ℝ) * (((2 * i : ℕ) : ℝ) + 1) / 2 := hm
      _ ≤ 3 * (i : ℝ) ^ 2 := by
        push_cast
        have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
        nlinarith
  have hL1 := allAspect_L1exp_le N u v k l hN hactive
  have hcoef : 8 / (Real.pi * ((2 * N : ℕ) : ℝ)) ≤ 4 / (3 * (N : ℝ)) := by
    push_cast
    apply (div_le_div_iff₀ (mul_pos Real.pi_pos (by positivity))
      (mul_pos (by norm_num) (by exact_mod_cast (show 0 < N by omega)))).2
    nlinarith [Real.pi_gt_three]
  calc
    _ ≤ (1 / (i : ℝ)) * ((4 / (3 * (N : ℝ))) *
        (8 * (N : ℝ) * L ^ 3) * (3 * (i : ℝ) ^ 2)) := by
      have hm0 : 0 ≤ weightedPrimitiveFamilyMass (G.cell i) := by
        unfold weightedPrimitiveFamilyMass
        positivity
      have hL10 : 0 ≤ vaughanTypeIIRectangularL1exp N k l := by
        unfold vaughanTypeIIRectangularL1exp
        positivity
      gcongr
    _ = _ := by field_simp; ring

/-- For an active rectangle and a conductor cell `S ⊆ (i, 2i]` with `2i ≤ N`, the
normalized mean is at most `10^6 log(4N+4)^15 (N/i + N/√(u+1) + N/√(v+1) + i √N)`. -/
theorem apNormalizedVaughanTypeIIRectMeanOn_cell_le
    (N Q C u v k l i : ℕ) (G : ConductorBlockPartition N Q C)
    (_hiG : i ∈ G.index) (hcell : G.cell i ⊆ Finset.Ioc i (2 * i))
    (hN : 9 ≤ N) (hi : 0 < i) (h2i : 2 * i ≤ N)
    (_hu : u < N) (_hv : v < N)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    apNormalizedVaughanTypeIIRectMeanOn N u v k l (G.cell i) ≤
      1000000 * Real.log (4 * N + 4 : ℕ) ^ 15 *
        ((N : ℝ) / i + (N : ℝ) / Real.sqrt (u + 1 : ℕ) +
          (N : ℝ) / Real.sqrt (v + 1 : ℕ) + (i : ℝ) * Real.sqrt N) := by
  classical
  let L : ℝ := Real.log (4 * N + 4 : ℕ)
  let D : ℝ := vaughanTypeIIRectangularD k
  let X : ℝ := vaughanTypeIIRectangularX N k
  let A : ℝ := (N : ℝ) / i + (N : ℝ) / Real.sqrt (u + 1 : ℕ) +
    (N : ℝ) / Real.sqrt (v + 1 : ℕ) + (i : ℝ) * Real.sqrt N
  have hL : 1 ≤ L := le_trans (by norm_num) (allAspect_log_ge_two N hN)
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hDX : D * X ≤ N := by
    dsimp [D, X]
    exact_mod_cast (allAspect_active_geometry N u v k l hactive).2.2
  have hcorner : 2 ^ l ≤ vaughanTypeIIRectangularX N k := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ k)).2
    simpa [mul_comm] using (mem_vaughanTypeIIActiveCanonicalRectangles.mp hactive).2
  obtain ⟨huD, hvX⟩ := allAspect_shell_lower_bounds N u v k l hactive
  have hvX' : (v + 1 : ℕ) ≤ 2 * vaughanTypeIIRectangularX N k :=
    hvX.trans (Nat.mul_le_mul_left 2 hcorner)
  -- One estimate handles both cross terms `D √X` and `X √D`.
  have cross (a b w : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hw : 0 < w)
      (hab : a * b ≤ N) (hwb : w ≤ 2 * b) :
      a * Real.sqrt b ≤ 2 * (N : ℝ) / Real.sqrt w := by
    have hs : Real.sqrt b * Real.sqrt w ≤ 2 * b := by
      calc
        Real.sqrt b * Real.sqrt w = Real.sqrt (b * w) := (Real.sqrt_mul hb w).symm
        _ ≤ Real.sqrt ((2 * b) ^ 2) := by
          apply Real.sqrt_le_sqrt
          nlinarith [mul_le_mul_of_nonneg_left hwb hb]
        _ = 2 * b := Real.sqrt_sq (by positivity)
    apply (le_div_iff₀ (Real.sqrt_pos.2 hw)).2
    nlinarith [mul_le_mul_of_nonneg_left hs ha]
  have hcrossX : D * Real.sqrt X ≤ 2 * (N : ℝ) / Real.sqrt (v + 1 : ℕ) :=
    cross D X (v + 1 : ℕ) hD hX (by positivity) hDX (by dsimp [X]; exact_mod_cast hvX')
  have hcrossD : X * Real.sqrt D ≤ 2 * (N : ℝ) / Real.sqrt (u + 1 : ℕ) :=
    cross X D (u + 1 : ℕ) hX hD (by positivity)
      (by simpa [mul_comm] using hDX) (by dsimp [D]; exact_mod_cast huD)
  have hroots : Real.sqrt D * Real.sqrt X ≤ Real.sqrt N := by
    rw [← Real.sqrt_mul hD]
    exact Real.sqrt_le_sqrt hDX
  have hparts : (N : ℝ) / i ≤ A ∧
      (N : ℝ) / Real.sqrt (u + 1 : ℕ) ≤ A ∧
      (N : ℝ) / Real.sqrt (v + 1 : ℕ) ≤ A ∧
      (i : ℝ) * Real.sqrt N ≤ A := by
    have h0 : (0 : ℝ) ≤ (N : ℝ) / i := by positivity
    have h1 : (0 : ℝ) ≤ (N : ℝ) / Real.sqrt (u + 1 : ℕ) := by positivity
    have h2 : (0 : ℝ) ≤ (N : ℝ) / Real.sqrt (v + 1 : ℕ) := by positivity
    have h3 : (0 : ℝ) ≤ (i : ℝ) * Real.sqrt N := by positivity
    dsimp [A]
    constructor; linarith
    constructor; linarith
    constructor <;> linarith
  have hNA : (N : ℝ) ≤ (i : ℝ) * A := by
    simpa [mul_comm] using (div_le_iff₀ hiR).1 hparts.1
  have huA : (N : ℝ) / Real.sqrt (u + 1 : ℕ) ≤ A := hparts.2.1
  have hvA : (N : ℝ) / Real.sqrt (v + 1 : ℕ) ≤ A := hparts.2.2.1
  have hiA : (i : ℝ) * Real.sqrt N ≤ A := hparts.2.2.2
  have hiA' : (i : ℝ) ≤ A := by
    have hs : 1 ≤ Real.sqrt (N : ℝ) := by
      exact Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ N by omega))
    nlinarith
  have hq := allAspect_qFactor_le N i hN hi h2i
  have hq0 : 0 ≤ primitiveBilinearQFactor (2 * i) := by
    unfold primitiveBilinearQFactor
    positivity
  have hR : vaughanTypeIIRectangularRexp N k l (2 * i) ≤
      12000 * L ^ 5 * (i : ℝ) * A := by
    refine (vaughanTypeIIRectangularRexp_le
      N (2 * i) u v k l (by omega) hactive).trans ?_
    have hroot := allAspect_root_log_le N u v k l hN hactive
    change _ ≤ 12000 * L ^ 5 * (i : ℝ) * A
    have hsum : D * Real.sqrt X + X * Real.sqrt D ≤ 4 * A := by
      simp only [mul_div_assoc] at hcrossX hcrossD
      nlinarith
    have hbody : D * X + primitiveBilinearQFactor (2 * i) * (2 * i : ℕ) *
        (D * Real.sqrt X + X * Real.sqrt D) +
        primitiveBilinearQFactor (2 * i) ^ 2 * (2 * i : ℕ) ^ 2 *
          Real.sqrt D * Real.sqrt X ≤ 2000 * L ^ 2 * (i : ℝ) * A := by
      calc
        _ ≤ (i : ℝ) * A + (15 * L) * (2 * i : ℕ) * (4 * A) +
            (15 * L) ^ 2 * (2 * i : ℕ) ^ 2 * Real.sqrt N := by
          rw [mul_assoc (_ ^ 2 * _ ^ 2)]
          apply add_le_add
          · apply add_le_add (hDX.trans hNA)
            gcongr
          · gcongr
        _ ≤ 2000 * L ^ 2 * (i : ℝ) * A := by
          push_cast
          have hlast := mul_le_mul_of_nonneg_left hiA
            (show 0 ≤ 900 * L ^ 2 * (i : ℝ) by positivity)
          have hL2 : L ≤ L ^ 2 := by nlinarith
          nlinarith [mul_nonneg (show 0 ≤ L ^ 2 - 1 by nlinarith)
            (show 0 ≤ (i : ℝ) * A by positivity),
            mul_nonneg (show 0 ≤ L ^ 2 - L by nlinarith)
            (show 0 ≤ (i : ℝ) * A by positivity)]
    calc
      _ ≤ (6 * L ^ 3) * (2000 * L ^ 2 * (i : ℝ) * A) := by
        exact mul_le_mul hroot hbody (by positivity) (by positivity)
      _ = _ := by ring
  have hS : G.cell i ⊆ Finset.Icc 1 (2 * i) := by
    intro q hqS
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp (hcell hqS)
    exact Finset.mem_Icc.mpr ⟨by omega, hhi⟩
  have hn := apNormalizedVaughanTypeIIRectMeanOn_le_inv_mul
    N u v k l i (G.cell i) hi (fun q hqS => (Finset.mem_Ioc.mp (hcell hqS)).1.le)
  have he := vaughanTypeIIRectWeightedMean_le_explicit
    N (2 * i) u v k l (by omega) (by omega) (G.cell i) hS hactive
  have hs := allAspect_smoothing_le N hN
  have hsharp := allAspect_sharpTerm_le N Q C u v k l i G hN hi hcell hactive
  have hLP : L ^ 6 ≤ L ^ 15 := pow_le_pow_right₀ hL (by omega)
  have hLP3 : L ^ 3 ≤ L ^ 15 := pow_le_pow_right₀ hL (by omega)
  have hmain : (1 / (i : ℝ)) *
      ((1 / 2 + (14 * Real.log (2 * N : ℕ) + 4) / Real.pi) *
        vaughanTypeIIRectangularRexp N k l (2 * i)) ≤ 96000 * L ^ 6 * A := by
    calc
      _ ≤ (1 / (i : ℝ)) * ((8 * L) * (12000 * L ^ 5 * (i : ℝ) * A)) := by
        have hR0 : 0 ≤ vaughanTypeIIRectangularRexp N k l (2 * i) := by
          unfold vaughanTypeIIRectangularRexp
          positivity
        gcongr
      _ = _ := by field_simp; ring
  have htotal := hn.trans (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 1 / (i : ℝ)))
  rw [mul_add] at htotal
  change _ ≤ 1000000 * L ^ 15 * A
  have hpay := mul_le_mul_of_nonneg_right hLP hA
  have hpay3 := mul_le_mul_of_nonneg_right hLP3 hA
  have hsharp' := mul_le_mul_of_nonneg_right hiA' (show 0 ≤ L ^ 3 by positivity)
  nlinarith

theorem sum_activeRectangles_cell_le_card_mul_allAspect_scalar
    (N Q C u v i : ℕ) (G : ConductorBlockPartition N Q C)
    (hiG : i ∈ G.index) (hcell : G.cell i ⊆ Finset.Ioc i (2 * i))
    (hN : 9 ≤ N) (hi : 0 < i) (h2i : 2 * i ≤ N) (hu : u < N) (hv : v < N) :
    (∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
      apNormalizedVaughanTypeIIRectMeanOn N u v kl.1 kl.2 (G.cell i)) ≤
      ((vaughanTypeIIActiveCanonicalRectangles N u v).card : ℝ) *
        (1000000 * Real.log (4 * N + 4 : ℕ) ^ 15 *
          ((N : ℝ) / i + (N : ℝ) / Real.sqrt (u + 1 : ℕ) +
            (N : ℝ) / Real.sqrt (v + 1 : ℕ) + (i : ℝ) * Real.sqrt N)) := by
  calc
    _ ≤ ∑ _kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
        1000000 * Real.log (4 * N + 4 : ℕ) ^ 15 *
          ((N : ℝ) / i + (N : ℝ) / Real.sqrt (u + 1 : ℕ) +
            (N : ℝ) / Real.sqrt (v + 1 : ℕ) + (i : ℝ) * Real.sqrt N) := by
      apply Finset.sum_le_sum
      intro kl hkl
      exact apNormalizedVaughanTypeIIRectMeanOn_cell_le
        N Q C u v kl.1 kl.2 i G hiG hcell hN hi h2i hu hv hkl
    _ = _ := by simp

end

end BombieriVinogradov

/-!
## The Type-II mean over the high conductors

The Type-II mean is at most the sum of the rectangle means. We bound it on each
dyadic conductor cell and sum, using `∑ 1/i ≤ 2/R` and `∑ i ≤ 2Q` over the cells.
-/

namespace BombieriVinogradov

open Classical Finset
open scoped BigOperators ArithmeticFunction
noncomputable section

set_option maxHeartbeats 1600000

/-- `∑_{q ∈ S} φ(q)^{-1} ∑_χ max_{y ≤ N} |∑_{n ≤ y} a_n χ(n)|`, where `a_n` is the
Type-II part of Vaughan's identity for `Λ` with parameters `u, v`, over primitive
`χ` mod `q`. -/
def apNormalizedVaughanTypeIIMeanOn
    (N u v : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ q ∈ S, ((q.totient : ℝ)⁻¹) *
    ∑ χ : PrimitiveCharacter q,
      primitivePrefixAmplitude
        (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N q χ

/-- The Type-II mean is at most the sum over the active rectangles of their means. -/
theorem apNormalizedVaughanTypeIIMeanOn_le_active_collected_shells
    (N u v : ℕ) (S : Finset ℕ) :
    apNormalizedVaughanTypeIIMeanOn N u v S ≤
      ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
        apNormalizedVaughanTypeIIRectMeanOn
          N u v kl.1 kl.2 S := by
  unfold apNormalizedVaughanTypeIIMeanOn
    apNormalizedVaughanTypeIIRectMeanOn
  calc
    _ ≤ ∑ q ∈ S, ((q.totient : ℝ)⁻¹) *
        ∑ χ : PrimitiveCharacter q,
          ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
            Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare
              N u v kl.1 kl.2 q χ) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun χ _ =>
          primitivePrefixAmplitude_vaughanTypeII_le_sum
            N u v q χ
      · positivity
    _ = ∑ q ∈ S,
        ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
          ((q.totient : ℝ)⁻¹) *
            ∑ χ : PrimitiveCharacter q,
              Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare
                N u v kl.1 kl.2 q χ) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.sum_comm, Finset.mul_sum]
    _ = _ := by rw [Finset.sum_comm]

/-- On a conductor cell `S ⊆ (i, 2i]` with `2i ≤ N`, the Type-II mean is at most the
number of active rectangles times `10^6 log(4N+4)^15 (N/i + N/√(u+1) + N/√(v+1) + i √N)`. -/
theorem apNormalizedVaughanTypeIIMeanOn_cell_le
    (N Q C u v i : ℕ) (G : ConductorBlockPartition N Q C)
    (hiG : i ∈ G.index) (hcell : G.cell i ⊆ Finset.Ioc i (2 * i))
    (hN : 9 ≤ N) (hi : 0 < i) (h2i : 2 * i ≤ N)
    (hu : u < N) (hv : v < N) :
    apNormalizedVaughanTypeIIMeanOn N u v (G.cell i) ≤
      ((vaughanTypeIIActiveCanonicalRectangles N u v).card : ℝ) *
        (1000000 * Real.log (4 * N + 4 : ℕ) ^ 15 *
          ((N : ℝ) / i + (N : ℝ) / Real.sqrt (u + 1 : ℕ) +
            (N : ℝ) / Real.sqrt (v + 1 : ℕ) +
            (i : ℝ) * Real.sqrt N)) := by
  exact (apNormalizedVaughanTypeIIMeanOn_le_active_collected_shells
    N u v (G.cell i)).trans
      (sum_activeRectangles_cell_le_card_mul_allAspect_scalar
        N Q C u v i G hiG hcell hN hi h2i hu hv)

/-- The Type-II mean over the conductors `R < q ≤ Q`, where `R = ⌊(log N)^C⌋`, is at most
the number of active rectangles times `10^6 log(4N+4)^15` times
`2N/R + J (N/√(u+1) + N/√(v+1)) + 2Q √N`, with `J` the number of dyadic conductor cells. -/
theorem apNormalizedVaughanTypeIIMeanOn_high_le
    (N Q C u v : ℕ)
    (hN : 9 ≤ N)
    (hR : 0 < logConductorThreshold N C)
    (hQ : Q ≤ N / 2)
    (hu : u < N) (hv : v < N) :
    apNormalizedVaughanTypeIIMeanOn N u v (highConductorSet N Q C) ≤
      ((vaughanTypeIIActiveCanonicalRectangles N u v).card : ℝ) *
        (1000000 * Real.log (4 * N + 4 : ℕ) ^ 15) *
          (2 * (N : ℝ) / logConductorThreshold N C +
            (((dyadicConductorBlocks N Q C hR).index.card : ℕ) : ℝ) *
              ((N : ℝ) / Real.sqrt (u + 1 : ℕ) +
                (N : ℝ) / Real.sqrt (v + 1 : ℕ)) +
            2 * (Q : ℝ) * Real.sqrt N) := by
  let G := dyadicConductorBlocks N Q C hR
  let A : ℝ := ((vaughanTypeIIActiveCanonicalRectangles N u v).card : ℝ)
  let K : ℝ := 1000000 * Real.log (4 * N + 4 : ℕ) ^ 15
  let U : ℝ := (N : ℝ) / Real.sqrt (u + 1 : ℕ)
  let V : ℝ := (N : ℝ) / Real.sqrt (v + 1 : ℕ)
  let R : ℝ := logConductorThreshold N C
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hAK0 : 0 ≤ A * K := mul_nonneg hA0 hK0
  have hQ2 : 2 * Q ≤ N := by omega
  -- An empty cell contributes zero; a nonempty one contains some `q ≤ Q`, so `2i ≤ N`.
  have hcell (i : ℕ) (hi : i ∈ G.index) :
      apNormalizedVaughanTypeIIMeanOn N u v (G.cell i) ≤
        A * K * ((N : ℝ) / i + U + V + (i : ℝ) * Real.sqrt N) := by
    by_cases hempty : G.cell i = ∅
    · simp only [hempty, apNormalizedVaughanTypeIIMeanOn, Finset.sum_empty]
      exact mul_nonneg hAK0 (by positivity)
    · obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hIoc : G.cell i ⊆ Finset.Ioc i (2 * i) := by
        dsimp [G]
        exact dyadicConductorBlocks_cell_subset_Ioc N Q C hR i
      have hiq : i < q := (Finset.mem_Ioc.mp (hIoc hq)).1
      have hqHigh : q ∈ highConductorSet N Q C := by
        rw [← G.cover]
        exact Finset.mem_biUnion.mpr ⟨i, hi, hq⟩
      have hqQ : q ≤ Q :=
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hqHigh).1).2
      have h2i : 2 * i ≤ N := by omega
      convert
        apNormalizedVaughanTypeIIMeanOn_cell_le
          N Q C u v i G hi hIoc hN (G.lower_pos i hi) h2i hu hv using 1;
        dsimp [A, K, U, V]; ring
  -- The cells partition the high conductors.
  have hreindex :
      apNormalizedVaughanTypeIIMeanOn N u v (highConductorSet N Q C) =
        ∑ i ∈ G.index,
          apNormalizedVaughanTypeIIMeanOn N u v (G.cell i) := by
    unfold apNormalizedVaughanTypeIIMeanOn
    rw [← G.cover, Finset.sum_biUnion G.pairwise]
  rw [hreindex]
  calc
    _ ≤ ∑ i ∈ G.index,
        A * K * ((N : ℝ) / i + U + V + (i : ℝ) * Real.sqrt N) := by
      exact Finset.sum_le_sum fun i hi => hcell i hi
    _ = A * K *
        ((N : ℝ) * (∑ i ∈ G.index, ((i : ℝ)⁻¹)) +
          (G.index.card : ℝ) * (U + V) +
          (∑ i ∈ G.index, (i : ℝ)) * Real.sqrt N) := by
      calc
        _ = A * K * (∑ i ∈ G.index,
            ((N : ℝ) / i + U + V + (i : ℝ) * Real.sqrt N)) := by
              rw [Finset.mul_sum]
        _ = _ := by
          simp only [div_eq_mul_inv, Finset.sum_add_distrib,
            Finset.sum_const, nsmul_eq_mul]
          rw [← Finset.mul_sum, ← Finset.sum_mul]
          ring
    _ ≤ A * K *
        ((N : ℝ) * (2 / R) + (G.index.card : ℝ) * (U + V) +
          (2 * (Q : ℝ)) * Real.sqrt N) := by
      apply mul_le_mul_of_nonneg_left _ hAK0
      have hinv : (∑ i ∈ G.index, ((i : ℝ)⁻¹)) ≤ 2 / R := by
        simpa [G, R] using G.inv_lower_sum_le
      have hsum : (∑ i ∈ G.index, (i : ℝ)) ≤ 2 * (Q : ℝ) := G.lower_sum_le
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg N)) le_rfl)
        (mul_le_mul_of_nonneg_right hsum (Real.sqrt_nonneg N))
    _ = ((vaughanTypeIIActiveCanonicalRectangles N u v).card : ℝ) *
        (1000000 * Real.log (4 * N + 4 : ℕ) ^ 15) *
          (2 * (N : ℝ) / logConductorThreshold N C +
            (((dyadicConductorBlocks N Q C hR).index.card : ℕ) : ℝ) *
              ((N : ℝ) / Real.sqrt (u + 1 : ℕ) +
                (N : ℝ) / Real.sqrt (v + 1 : ℕ)) +
            2 * (Q : ℝ) * Real.sqrt N) := by
      dsimp [A, K, U, V, R, G]
      ring

end

end BombieriVinogradov
