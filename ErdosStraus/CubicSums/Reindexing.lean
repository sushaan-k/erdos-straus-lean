import Mathlib.Data.Int.CardIntervalMod
import ErdosStraus.Basic
import ErdosStraus.Estimates.Progressions
import ErdosStraus.CubicSums.HarmonicSums

/-!
# The Möbius decomposition of a divisor sum with local restrictions

For a modulus `M` and residues `a_M`, `u` we rewrite the sum
`∑_{a ≤ N, a ≡ a_M} ∑_{h ∣ a², h ≡ u} 1/a` from the proof of Proposition 4.3 as
`∑_{k ≤ N} μ(k)/k² ∑_r ∑_{xyz ≤ N/k², (x,y,z) ≡ r} 1/(xyz)`, the inner sum running over the
residue triples `r` modulo `M` that solve `k²xyz ≡ a_M` and `k²x²z ≡ u`. Each pair `(a, h)` with
`h ∣ a²` is written uniquely as `a = deA`, `h = d²e` with `(d, A) = 1`; the condition
`(d, A) = 1` is expanded by Möbius inversion, and `d = kx`, `A = ky`.
-/

open scoped BigOperators

namespace ErdosStraus.DivisorEstimates

attribute [local instance] Classical.propDecidable

/-! ## The coordinates `a = deA`, `h = d²e` -/

/-- With `g = gcd(h, a)`, the triple `(d, e, A) = (h/g, g²/h, a/g)`. For `a, h > 0` with
`h ∣ a²` it satisfies `a = deA`, `h = d²e` and `(d, A) = 1`. -/
noncomputable def squareDivisorCoordinates (a h : ℕ) : (ℕ × ℕ) × ℕ :=
  ((h / Nat.gcd h a, (Nat.gcd h a * Nat.gcd h a) / h), a / Nat.gcd h a)

theorem squareDivisorCoordinates_spec (a h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hdvd : h ∣ a ^ 2) :
    let t := squareDivisorCoordinates a h
    0 < t.1.1 ∧ 0 < t.1.2 ∧ 0 < t.2 ∧ Nat.Coprime t.1.1 t.2 ∧
      a = t.1.1 * t.1.2 * t.2 ∧ h = t.1.1 ^ 2 * t.1.2 := by
  let g := Nat.gcd h a
  let d := h / g
  let e := (g * g) / h
  let A := a / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left a hh
  have hgh : g ∣ h := Nat.gcd_dvd_left h a
  have hga : g ∣ a := Nat.gcd_dvd_right h a
  have hgd : g * d = h := Nat.mul_div_cancel' hgh
  have hgaA : g * A = a := Nat.mul_div_cancel' hga
  have hdivgg : h ∣ g * g :=
    (Nat.dvd_gcd_mul_gcd_iff_dvd_mul (k := h) (n := a) (m := a)).mpr
      (by simpa only [pow_two] using hdvd)
  have hgge : g * g = h * e := (Nat.mul_div_cancel' hdivgg).symm
  have hgde : g = d * e := by
    apply Nat.eq_of_mul_eq_mul_left hg
    calc
      g * g = h * e := hgge
      _ = g * (d * e) := by rw [← hgd]; ring
  have hd : 0 < d := Nat.pos_of_mul_pos_left (hgd ▸ hh)
  have he : 0 < e := Nat.pos_of_mul_pos_left (hgde ▸ hg)
  have hA : 0 < A := Nat.pos_of_mul_pos_left (hgaA ▸ ha)
  have hcop : Nat.Coprime d A := Nat.coprime_div_gcd_div_gcd hg
  change 0 < d ∧ 0 < e ∧ 0 < A ∧ Nat.Coprime d A ∧ a = d * e * A ∧ h = d ^ 2 * e
  refine ⟨hd, he, hA, hcop, ?_, ?_⟩
  · rw [← hgaA, hgde]
  · rw [← hgd, hgde]
    ring

theorem gcd_square_divisor_triple (d e A : ℕ) (hcop : Nat.Coprime d A) :
    Nat.gcd (d ^ 2 * e) (d * e * A) = d * e := by
  calc
    _ = Nat.gcd ((d * e) * d) ((d * e) * A) := by congr 1; ring
    _ = (d * e) * Nat.gcd d A := Nat.gcd_mul_left _ _ _
    _ = _ := by rw [hcop.gcd_eq_one, mul_one]

theorem squareDivisorCoordinates_of_triple (d e A : ℕ)
    (hd : 0 < d) (he : 0 < e) (_hA : 0 < A) (hcop : Nat.Coprime d A) :
    squareDivisorCoordinates (d * e * A) (d ^ 2 * e) = ((d, e), A) := by
  have hde : 0 < d * e := Nat.mul_pos hd he
  have hd2e : 0 < d ^ 2 * e := by positivity
  unfold squareDivisorCoordinates
  rw [gcd_square_divisor_triple d e A hcop]
  have h1 : d ^ 2 * e / (d * e) = d := by
    have hh : d ^ 2 * e = d * (d * e) := by ring
    rw [hh, Nat.mul_div_cancel _ hde]
  have h2 : (d * e * (d * e)) / (d ^ 2 * e) = e := by
    have hh : d * e * (d * e) = e * (d ^ 2 * e) := by ring
    rw [hh, Nat.mul_div_cancel _ hd2e]
  have h3 : d * e * A / (d * e) = A := Nat.mul_div_cancel_left A hde
  rw [h1, h2, h3]

/-- The pairs `(a, h)` with `1 ≤ a ≤ N`, `a ≡ a_M`, `h ∣ a²` and `h ≡ u (mod M)`. -/
noncomputable def localSquareDivisorPairs (N M aM u : ℕ) :
    Finset ((_a : ℕ) × ℕ) :=
  ((Finset.Icc 1 N).filter (fun a => Estimates.congMod a aM M)).sigma
    (fun a => (a ^ 2).divisors.filter (fun h => Estimates.congMod h u M))

/-- The triples `(d, e, A)` of positive integers with `deA ≤ N`, `(d, A) = 1`, `deA ≡ a_M`
and `d²e ≡ u (mod M)`. -/
noncomputable def localCoprimeDivisorTriples (N M aM u : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (((Finset.Icc 1 N).product (Finset.Icc 1 N)).product (Finset.Icc 1 N)).filter
    (fun t => t.1.1 * t.1.2 * t.2 ≤ N ∧ Nat.Coprime t.1.1 t.2 ∧
      Estimates.congMod (t.1.1 * t.1.2 * t.2) aM M ∧
      Estimates.congMod (t.1.1 ^ 2 * t.1.2) u M)

theorem mem_localCoprimeDivisorTriples {N M aM u d e A : ℕ} :
    ((d, e), A) ∈ localCoprimeDivisorTriples N M aM u ↔
      0 < d ∧ 0 < e ∧ 0 < A ∧ d * e * A ≤ N ∧ Nat.Coprime d A ∧
        Estimates.congMod (d * e * A) aM M ∧ Estimates.congMod (d ^ 2 * e) u M := by
  unfold localCoprimeDivisorTriples
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hbox, hprod, hcop, haM, hhu⟩
    obtain ⟨hde, hA⟩ := Finset.mem_product.mp hbox
    obtain ⟨hd, he⟩ := Finset.mem_product.mp hde
    exact ⟨(Finset.mem_Icc.mp hd).1, (Finset.mem_Icc.mp he).1,
      (Finset.mem_Icc.mp hA).1, hprod, hcop, haM, hhu⟩
  · rintro ⟨hd, he, hA, hprod, hcop, haM, hhu⟩
    have hdle : d ≤ N := (Nat.le_mul_of_pos_right d (Nat.mul_pos he hA)).trans
      (by simpa only [mul_assoc] using hprod)
    have hele : e ≤ N := (Nat.le_mul_of_pos_left e hd).trans
      ((Nat.le_mul_of_pos_right (d * e) hA).trans hprod)
    have hAle : A ≤ N := (Nat.le_mul_of_pos_left A (Nat.mul_pos hd he)).trans hprod
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hd, hdle⟩, Finset.mem_Icc.mpr ⟨he, hele⟩⟩,
      Finset.mem_Icc.mpr ⟨hA, hAle⟩⟩, hprod, hcop, haM, hhu⟩

/-- Reindexing by `(a, h) ↦ (d, e, A)`, a bijection onto `localCoprimeDivisorTriples`. -/
theorem local_square_divisor_weighted_reindex (N M aM u : ℕ) (w : ℕ → ℝ) :
    (∑ a ∈ (Finset.Icc 1 N).filter (fun a => Estimates.congMod a aM M),
      ∑ _h ∈ (a ^ 2).divisors.filter (fun h => Estimates.congMod h u M), w a) =
      ∑ t ∈ localCoprimeDivisorTriples N M aM u, w (t.1.1 * t.1.2 * t.2) := by
  classical
  rw [Finset.sum_sigma']
  change (∑ p ∈ localSquareDivisorPairs N M aM u, w p.1) = _
  apply Finset.sum_bij (fun p hp => squareDivisorCoordinates p.1 p.2)
  · intro p hp
    obtain ⟨hpA, hpH⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hpAI, hpAM⟩ := Finset.mem_filter.mp hpA
    obtain ⟨hpHD, hpHU⟩ := Finset.mem_filter.mp hpH
    have ha : 0 < p.1 := (Finset.mem_Icc.mp hpAI).1
    have hh : 0 < p.2 := Nat.pos_of_mem_divisors hpHD
    obtain ⟨hd, he, hA, hcop, haeq, hheq⟩ :=
      squareDivisorCoordinates_spec p.1 p.2 ha hh (Nat.dvd_of_mem_divisors hpHD)
    apply mem_localCoprimeDivisorTriples.mpr
    exact ⟨hd, he, hA, haeq ▸ (Finset.mem_Icc.mp hpAI).2, hcop,
      haeq ▸ hpAM, hheq ▸ hpHU⟩
  · intro p hp q hq heq
    obtain ⟨hpA, hpH⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hqA, hqH⟩ := Finset.mem_sigma.mp hq
    have hpSpec := squareDivisorCoordinates_spec p.1 p.2
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hpA).1).1
      (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hpH).1)
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hpH).1)
    have hqSpec := squareDivisorCoordinates_spec q.1 q.2
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hqA).1).1
      (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hqH).1)
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hqH).1)
    have haeq : p.1 = q.1 := by rw [hpSpec.2.2.2.2.1, hqSpec.2.2.2.2.1, heq]
    have hheq : p.2 = q.2 := by rw [hpSpec.2.2.2.2.2, hqSpec.2.2.2.2.2, heq]
    exact Sigma.ext haeq (by simpa using hheq)
  · rintro ⟨⟨d, e⟩, A⟩ ht
    obtain ⟨hd, he, hA, hprod, hcop, haM, hhu⟩ := mem_localCoprimeDivisorTriples.mp ht
    refine ⟨⟨d * e * A, d ^ 2 * e⟩, ?_, squareDivisorCoordinates_of_triple d e A hd he hA hcop⟩
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.mul_pos (Nat.mul_pos hd he) hA, hprod⟩, haM⟩,
      Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_,
        (pow_pos (Nat.mul_pos (Nat.mul_pos hd he) hA) 2).ne'⟩, hhu⟩⟩
    exact ⟨e * A ^ 2, by ring⟩
  · intro p hp
    obtain ⟨hpA, hpH⟩ := Finset.mem_sigma.mp hp
    have hpSpec := squareDivisorCoordinates_spec p.1 p.2
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hpA).1).1
      (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hpH).1)
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hpH).1)
    exact congrArg w hpSpec.2.2.2.2.1

/-! ## Möbius inversion of the condition `(d, A) = 1` -/

/-- The triples `(d, e, A)` of positive integers with `deA ≤ N`, `deA ≡ a_M` and
`d²e ≡ u (mod M)`. -/
noncomputable def localAllDivisorTriples (N M aM u : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (((Finset.Icc 1 N).product (Finset.Icc 1 N)).product (Finset.Icc 1 N)).filter
    (fun t => t.1.1 * t.1.2 * t.2 ≤ N ∧
      Estimates.congMod (t.1.1 * t.1.2 * t.2) aM M ∧
      Estimates.congMod (t.1.1 ^ 2 * t.1.2) u M)

theorem mem_localAllDivisorTriples {N M aM u d e A : ℕ} :
    ((d, e), A) ∈ localAllDivisorTriples N M aM u ↔
      0 < d ∧ 0 < e ∧ 0 < A ∧ d * e * A ≤ N ∧
        Estimates.congMod (d * e * A) aM M ∧ Estimates.congMod (d ^ 2 * e) u M := by
  unfold localAllDivisorTriples
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hbox, hprod, haM, hhu⟩
    obtain ⟨hde, hA⟩ := Finset.mem_product.mp hbox
    obtain ⟨hd, he⟩ := Finset.mem_product.mp hde
    exact ⟨(Finset.mem_Icc.mp hd).1, (Finset.mem_Icc.mp he).1,
      (Finset.mem_Icc.mp hA).1, hprod, haM, hhu⟩
  · rintro ⟨hd, he, hA, hprod, haM, hhu⟩
    have hdle : d ≤ N := (Nat.le_mul_of_pos_right d (Nat.mul_pos he hA)).trans
      (by simpa only [mul_assoc] using hprod)
    have hele : e ≤ N := (Nat.le_mul_of_pos_left e hd).trans
      ((Nat.le_mul_of_pos_right (d * e) hA).trans hprod)
    have hAle : A ≤ N := (Nat.le_mul_of_pos_left A (Nat.mul_pos hd he)).trans hprod
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hd, hdle⟩, Finset.mem_Icc.mpr ⟨he, hele⟩⟩,
      Finset.mem_Icc.mpr ⟨hA, hAle⟩⟩, hprod, haM, hhu⟩

theorem coprime_indicator_eq_bounded_moebius_sum (d A N : ℕ)
    (hA : 0 < A) (hAN : A ≤ N) :
    (if Nat.Coprime d A then (1 : ℝ) else 0) =
      ∑ k ∈ Finset.Icc 1 N,
        if k ∣ d ∧ k ∣ A then (ArithmeticFunction.moebius k : ℝ) else 0 := by
  classical
  rw [ProgressionEstimates.coprime_indicator_eq_moebius_sum d hA.ne']
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hkA, _⟩, hkd⟩
    have hk0 : 0 < k := Nat.pos_of_dvd_of_pos hkA hA
    exact ⟨⟨hk0, (Nat.le_of_dvd hA hkA).trans hAN⟩, hkd, hkA⟩
  · rintro ⟨⟨hk, hkN⟩, hkd, hkA⟩
    exact ⟨⟨hkA, hA.ne'⟩, hkd⟩

theorem local_coprime_weighted_moebius (N M aM u : ℕ) (w : ((ℕ × ℕ) × ℕ) → ℝ) :
    (∑ t ∈ localCoprimeDivisorTriples N M aM u, w t) =
      ∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℝ) *
        ∑ t ∈ (localAllDivisorTriples N M aM u).filter
          (fun t => k ∣ t.1.1 ∧ k ∣ t.2), w t := by
  classical
  have hset : localCoprimeDivisorTriples N M aM u =
      (localAllDivisorTriples N M aM u).filter (fun t => Nat.Coprime t.1.1 t.2) := by
    ext t
    rcases t with ⟨⟨d, e⟩, A⟩
    simp only [mem_localCoprimeDivisorTriples, Finset.mem_filter, mem_localAllDivisorTriples]
    tauto
  rw [hset, Finset.sum_filter]
  have hpoint : ∀ t ∈ localAllDivisorTriples N M aM u,
      (if Nat.Coprime t.1.1 t.2 then w t else 0) =
        ∑ k ∈ Finset.Icc 1 N,
          if k ∣ t.1.1 ∧ k ∣ t.2 then (ArithmeticFunction.moebius k : ℝ) * w t else 0 := by
    rintro ⟨⟨d, e⟩, A⟩ ht
    have htI := (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).2
    have hA := (Finset.mem_Icc.mp htI).1
    have hAN := (Finset.mem_Icc.mp htI).2
    have hh := congrArg (fun x : ℝ => x * w ((d, e), A))
      (coprime_indicator_eq_bounded_moebius_sum d A N hA hAN)
    rw [Finset.sum_mul] at hh
    simpa only [ite_mul, one_mul, zero_mul] using hh
  rw [Finset.sum_congr rfl hpoint, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum, Finset.sum_filter]

/-- The triples `(x, e, y) ∈ [1, N]³` with `k²xey ≤ N`, `k²xey ≡ a_M` and
`k²x²e ≡ u (mod M)`. -/
noncomputable def scaledLocalDivisorTriples (N M aM u k : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (((Finset.Icc 1 N).product (Finset.Icc 1 N)).product (Finset.Icc 1 N)).filter
    (fun t => k ^ 2 * t.1.1 * t.1.2 * t.2 ≤ N ∧
      Estimates.congMod (k ^ 2 * t.1.1 * t.1.2 * t.2) aM M ∧
      Estimates.congMod (k ^ 2 * t.1.1 ^ 2 * t.1.2) u M)

/-- `(x, e, y) ↦ (kx, e, ky)`. -/
def scaleLocalTriple (k : ℕ) (t : (ℕ × ℕ) × ℕ) : (ℕ × ℕ) × ℕ :=
  ((k * t.1.1, t.1.2), k * t.2)

theorem mem_scaledLocalDivisorTriples {N M aM u k x e y : ℕ} (hk : 0 < k) :
    ((x, e), y) ∈ scaledLocalDivisorTriples N M aM u k ↔
      0 < x ∧ 0 < e ∧ 0 < y ∧ k ^ 2 * x * e * y ≤ N ∧
        Estimates.congMod (k ^ 2 * x * e * y) aM M ∧
        Estimates.congMod (k ^ 2 * x ^ 2 * e) u M := by
  unfold scaledLocalDivisorTriples
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hbox, hprod, haM, hhu⟩
    obtain ⟨hxe, hy⟩ := Finset.mem_product.mp hbox
    obtain ⟨hx, he⟩ := Finset.mem_product.mp hxe
    exact ⟨(Finset.mem_Icc.mp hx).1, (Finset.mem_Icc.mp he).1,
      (Finset.mem_Icc.mp hy).1, hprod, haM, hhu⟩
  · rintro ⟨hx, he, hy, hprod, haM, hhu⟩
    have hbase : x * e * y ≤ N := by
      have h1 : 1 ≤ k ^ 2 := Nat.one_le_pow 2 k hk
      have hh := Nat.mul_le_mul_right (x * e * y) h1
      nlinarith only [hh, hprod]
    have hxN : x ≤ N := (Nat.le_mul_of_pos_right x (Nat.mul_pos he hy)).trans
      (by simpa only [mul_assoc] using hbase)
    have heN : e ≤ N := (Nat.le_mul_of_pos_left e hx).trans
      ((Nat.le_mul_of_pos_right (x * e) hy).trans hbase)
    have hyN : y ≤ N := (Nat.le_mul_of_pos_left y (Nat.mul_pos hx he)).trans hbase
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hx, hxN⟩, Finset.mem_Icc.mpr ⟨he, heN⟩⟩,
      Finset.mem_Icc.mpr ⟨hy, hyN⟩⟩, hprod, haM, hhu⟩

theorem local_divisible_weighted_scale (N M aM u k : ℕ) (hk : 0 < k)
    (w : ((ℕ × ℕ) × ℕ) → ℝ) :
    (∑ t ∈ scaledLocalDivisorTriples N M aM u k, w (scaleLocalTriple k t)) =
      ∑ t ∈ (localAllDivisorTriples N M aM u).filter
        (fun t => k ∣ t.1.1 ∧ k ∣ t.2), w t := by
  classical
  apply Finset.sum_bij (fun t _ => scaleLocalTriple k t)
  · rintro ⟨⟨x, e⟩, y⟩ ht
    obtain ⟨hx, he, hy, hprod, haM, hhu⟩ := (mem_scaledLocalDivisorTriples hk).mp ht
    have hprodEq : (k * x) * e * (k * y) = k ^ 2 * x * e * y := by ring
    have hhEq : (k * x) ^ 2 * e = k ^ 2 * x ^ 2 * e := by ring
    apply Finset.mem_filter.mpr
    refine ⟨mem_localAllDivisorTriples.mpr ⟨Nat.mul_pos hk hx, he, Nat.mul_pos hk hy,
      ?_, ?_, ?_⟩, dvd_mul_right k x, dvd_mul_right k y⟩
    · rwa [hprodEq]
    · rwa [hprodEq]
    · rwa [hhEq]
  · rintro ⟨⟨x, e⟩, y⟩ ht ⟨⟨x', e'⟩, y'⟩ hu heq
    change ((k * x, e), k * y) = ((k * x', e'), k * y') at heq
    simp only [Prod.mk.injEq] at heq ⊢
    exact ⟨⟨Nat.eq_of_mul_eq_mul_left hk heq.1.1, heq.1.2⟩,
      Nat.eq_of_mul_eq_mul_left hk heq.2⟩
  · rintro ⟨⟨d, e⟩, A⟩ ht
    obtain ⟨htA, hkd, hkA⟩ := Finset.mem_filter.mp ht
    obtain ⟨hd, he, hA, hprod, haM, hhu⟩ := mem_localAllDivisorTriples.mp htA
    have hkx : k * (d / k) = d := Nat.mul_div_cancel' hkd
    have hky : k * (A / k) = A := Nat.mul_div_cancel' hkA
    have hprodEq : k ^ 2 * (d / k) * e * (A / k) = d * e * A := by
      calc
        _ = (k * (d / k)) * e * (k * (A / k)) := by ring
        _ = _ := by rw [hkx, hky]
    have hhEq : k ^ 2 * (d / k) ^ 2 * e = d ^ 2 * e := by
      calc
        _ = (k * (d / k)) ^ 2 * e := by ring
        _ = _ := by rw [hkx]
    refine ⟨((d / k, e), A / k), (mem_scaledLocalDivisorTriples hk).mpr
      ⟨Nat.div_pos (Nat.le_of_dvd hd hkd) hk, he,
        Nat.div_pos (Nat.le_of_dvd hA hkA) hk, hprodEq ▸ hprod,
        hprodEq ▸ haM, hhEq ▸ hhu⟩, ?_⟩
    change ((k * (d / k), e), k * (A / k)) = ((d, e), A)
    rw [hkx, hky]
  · intro t ht
    rfl

/-- `∑_{a ≤ N, a ≡ a_M} ∑_{h ∣ a², h ≡ u} 1/a = ∑_{k ≤ N} μ(k)/k² ∑ 1/(xey)`, the inner sum
over the triples `(x, e, y)` with `k²xey ≤ N`, `k²xey ≡ a_M` and `k²x²e ≡ u (mod M)`. -/
theorem local_square_divisor_reciprocal_moebius_reindex (N M aM u : ℕ) :
    (∑ a ∈ (Finset.Icc 1 N).filter (fun a => Estimates.congMod a aM M),
      ∑ _h ∈ (a ^ 2).divisors.filter (fun h => Estimates.congMod h u M),
        (1 : ℝ) / (a : ℝ)) =
      ∑ k ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2) *
        ∑ t ∈ scaledLocalDivisorTriples N M aM u k,
          (1 : ℝ) / ((t.1.1 * t.1.2 * t.2 : ℕ) : ℝ) := by
  rw [local_square_divisor_weighted_reindex,
    local_coprime_weighted_moebius]
  apply Finset.sum_congr rfl
  intro k hk
  have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
  rw [← local_divisible_weighted_scale N M aM u k hkpos,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  unfold scaleLocalTriple
  push_cast
  ring

/-! ## Residue triples -/

/-- The triples `(x, y, z)` of positive integers with `xyz ≤ T`, indexed as in the nested sum
`∑_{x ≤ T} ∑_{y ≤ T/x} ∑_{z ≤ T/(xy)}`. -/
noncomputable def harmonicTripleSupport (T : ℝ) : Finset ((_x : ℕ) × (_y : ℕ) × ℕ) :=
  (Finset.Icc 1 ⌊T⌋₊).sigma (fun x =>
    (Finset.Icc 1 ⌊T / (x : ℝ)⌋₊).sigma (fun y =>
      Finset.Icc 1 ⌊T / (x : ℝ) / (y : ℝ)⌋₊))

theorem mem_harmonicTripleSupport {T : ℝ} (hT : 0 ≤ T) {x y z : ℕ} :
    ⟨x, ⟨y, z⟩⟩ ∈ harmonicTripleSupport T ↔
      0 < x ∧ 0 < y ∧ 0 < z ∧ (x : ℝ) * (y : ℝ) * (z : ℝ) ≤ T := by
  unfold harmonicTripleSupport
  simp only [Finset.mem_sigma, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hx, hxT⟩, ⟨hy, hyT⟩, hz, hzT⟩
    have hxR : (0 : ℝ) < x := Nat.cast_pos.mpr hx
    have hyR : (0 : ℝ) < y := Nat.cast_pos.mpr hy
    have hzR := (Nat.le_floor_iff (div_nonneg (div_nonneg hT hxR.le) hyR.le)).mp hzT
    rw [le_div_iff₀ hyR, le_div_iff₀ hxR] at hzR
    exact ⟨hx, hy, hz, by nlinarith only [hzR]⟩
  · rintro ⟨hx, hy, hz, hprod⟩
    have hxR : (0 : ℝ) < x := Nat.cast_pos.mpr hx
    have hyR : (0 : ℝ) < y := Nat.cast_pos.mpr hy
    have hzR : (0 : ℝ) < z := Nat.cast_pos.mpr hz
    have hx1 : (1 : ℝ) ≤ x := Nat.one_le_cast.mpr hx
    have hy1 : (1 : ℝ) ≤ y := Nat.one_le_cast.mpr hy
    have hz1 : (1 : ℝ) ≤ z := Nat.one_le_cast.mpr hz
    have hxy : (x : ℝ) * (y : ℝ) ≤ T := by
      have hh := mul_le_mul_of_nonneg_left hz1 (mul_nonneg hxR.le hyR.le)
      nlinarith only [hh, hprod]
    have hxT : (x : ℝ) ≤ T := by
      have hh := mul_le_mul_of_nonneg_left hy1 hxR.le
      nlinarith only [hh, hxy]
    refine ⟨⟨hx, Nat.le_floor hxT⟩, ⟨hy, Nat.le_floor ?_⟩, hz, Nat.le_floor ?_⟩
    · rw [le_div_iff₀ hxR]
      nlinarith only [hxy]
    · rw [le_div_iff₀ hyR, le_div_iff₀ hxR]
      nlinarith only [hprod]

/-- The box `[1, N]³`. -/
noncomputable def boundedTripleBox (N : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  ((Finset.Icc 1 N).product (Finset.Icc 1 N)).product (Finset.Icc 1 N)

theorem bounded_triple_sum_eq_nested (N : ℕ) {T : ℝ} (hT : 0 ≤ T) (hTN : T ≤ N)
    (w : ((ℕ × ℕ) × ℕ) → ℝ) :
    (∑ t ∈ (boundedTripleBox N).filter
      (fun t => (t.1.1 : ℝ) * (t.1.2 : ℝ) * (t.2 : ℝ) ≤ T), w t) =
      ∑ x ∈ Finset.Icc 1 ⌊T⌋₊,
        ∑ y ∈ Finset.Icc 1 ⌊T / (x : ℝ)⌋₊,
          ∑ z ∈ Finset.Icc 1 ⌊T / (x : ℝ) / (y : ℝ)⌋₊, w ((x, y), z) := by
  classical
  have hnested : (∑ x ∈ Finset.Icc 1 ⌊T⌋₊,
      ∑ y ∈ Finset.Icc 1 ⌊T / (x : ℝ)⌋₊,
        ∑ z ∈ Finset.Icc 1 ⌊T / (x : ℝ) / (y : ℝ)⌋₊, w ((x, y), z)) =
      ∑ t ∈ harmonicTripleSupport T, w ((t.1, t.2.1), t.2.2) := by
    unfold harmonicTripleSupport
    calc
      _ = ∑ x ∈ Finset.Icc 1 ⌊T⌋₊,
          ∑ yz ∈ (Finset.Icc 1 ⌊T / (x : ℝ)⌋₊).sigma
            (fun y => Finset.Icc 1 ⌊T / (x : ℝ) / (y : ℝ)⌋₊), w ((x, yz.1), yz.2) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact Finset.sum_sigma' _ _ _
      _ = _ := Finset.sum_sigma' _ _ _
  rw [hnested]
  apply Finset.sum_bij (fun t _ => (⟨t.1.1, ⟨t.1.2, t.2⟩⟩ : (x : ℕ) × (y : ℕ) × ℕ))
  · rintro ⟨⟨x, y⟩, z⟩ ht
    obtain ⟨hbox, hprod⟩ := Finset.mem_filter.mp ht
    obtain ⟨hxy, hz⟩ := Finset.mem_product.mp hbox
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
    exact (mem_harmonicTripleSupport hT).mpr
      ⟨(Finset.mem_Icc.mp hx).1, (Finset.mem_Icc.mp hy).1, (Finset.mem_Icc.mp hz).1, hprod⟩
  · rintro ⟨⟨x, y⟩, z⟩ ht ⟨⟨x', y'⟩, z'⟩ hu heq
    cases heq
    rfl
  · rintro ⟨x, ⟨y, z⟩⟩ ht
    obtain ⟨hx, hy, hz, hprod⟩ := (mem_harmonicTripleSupport hT).mp ht
    have hprodN : (x : ℝ) * (y : ℝ) * (z : ℝ) ≤ N := hprod.trans hTN
    have hprodNN : x * y * z ≤ N := by exact_mod_cast hprodN
    have hxN : x ≤ N := (Nat.le_mul_of_pos_right x (Nat.mul_pos hy hz)).trans
      (by simpa only [mul_assoc] using hprodNN)
    have hyN : y ≤ N := (Nat.le_mul_of_pos_left y hx).trans
      ((Nat.le_mul_of_pos_right (x * y) hz).trans hprodNN)
    have hzN : z ≤ N := (Nat.le_mul_of_pos_left z (Nat.mul_pos hx hy)).trans hprodNN
    refine ⟨((x, y), z), Finset.mem_filter.mpr ⟨?_, hprod⟩, rfl⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hx, hxN⟩, Finset.mem_Icc.mpr ⟨hy, hyN⟩⟩,
      Finset.mem_Icc.mpr ⟨hz, hzN⟩⟩
  · intro t ht
    rfl

theorem residueHarmonicTriple_eq_bounded_box (N M bx by_ bz : ℕ) {T : ℝ}
    (hT : 0 ≤ T) (hTN : T ≤ N) :
    residueHarmonicTriple M bx by_ bz T =
      ∑ t ∈ (boundedTripleBox N).filter (fun t =>
        (t.1.1 : ℝ) * (t.1.2 : ℝ) * (t.2 : ℝ) ≤ T ∧
          t.1.1 ≡ bx [MOD M] ∧ t.1.2 ≡ by_ [MOD M] ∧ t.2 ≡ bz [MOD M]),
        (1 : ℝ) / ((t.1.1 : ℝ) * (t.1.2 : ℝ) * (t.2 : ℝ)) := by
  classical
  rw [residueHarmonicTriple_eq_nested_sum]
  have hset : (boundedTripleBox N).filter (fun t =>
      (t.1.1 : ℝ) * (t.1.2 : ℝ) * (t.2 : ℝ) ≤ T ∧
        t.1.1 ≡ bx [MOD M] ∧ t.1.2 ≡ by_ [MOD M] ∧ t.2 ≡ bz [MOD M]) =
      ((boundedTripleBox N).filter
        (fun t => (t.1.1 : ℝ) * (t.1.2 : ℝ) * (t.2 : ℝ) ≤ T)).filter
        (fun t => t.1.1 ≡ bx [MOD M] ∧ t.1.2 ≡ by_ [MOD M] ∧ t.2 ≡ bz [MOD M]) := by
    ext t
    simp only [Finset.mem_filter]
    tauto
  conv_rhs => rw [hset, Finset.sum_filter, bounded_triple_sum_eq_nested N hT hTN]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hxM : x ≡ bx [MOD M]
  · simp only [hxM, true_and, if_true]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hyM : y ≡ by_ [MOD M]
    · simp only [hyM, true_and, if_true]
      rw [Finset.sum_filter]
    · simp [hyM]
  · simp [hxM]

/-- For `t = (x, y, z)`: `k²xyz ≡ a_M` and `k²x²z ≡ u (mod M)`. -/
def localCompositeCongruences (M aM u k : ℕ) (t : (ℕ × ℕ) × ℕ) : Prop :=
  Estimates.congMod (k ^ 2 * t.1.1 * t.1.2 * t.2) aM M ∧
    Estimates.congMod (k ^ 2 * t.1.1 ^ 2 * t.2) u M

/-- The residue triples in `[0, M)³` that satisfy `localCompositeCongruences M aM u k`. -/
noncomputable def localResidueTripleClasses (M aM u k : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (((Finset.range M).product (Finset.range M)).product (Finset.range M)).filter
    (localCompositeCongruences M aM u k)

/-- Coordinatewise reduction modulo `M`. -/
def tripleResidues (M : ℕ) (t : (ℕ × ℕ) × ℕ) : (ℕ × ℕ) × ℕ :=
  ((t.1.1 % M, t.1.2 % M), t.2 % M)

theorem localCompositeCongruences_congr {M aM u k : ℕ} {t r : (ℕ × ℕ) × ℕ}
    (hx : t.1.1 ≡ r.1.1 [MOD M]) (hy : t.1.2 ≡ r.1.2 [MOD M])
    (hz : t.2 ≡ r.2 [MOD M]) :
    localCompositeCongruences M aM u k t ↔ localCompositeCongruences M aM u k r := by
  have h1 : k ^ 2 * t.1.1 * t.1.2 * t.2 ≡ k ^ 2 * r.1.1 * r.1.2 * r.2 [MOD M] :=
    (((Nat.ModEq.refl (k ^ 2)).mul hx).mul hy).mul hz
  have h2 : k ^ 2 * t.1.1 ^ 2 * t.2 ≡ k ^ 2 * r.1.1 ^ 2 * r.2 [MOD M] :=
    ((Nat.ModEq.refl (k ^ 2)).mul (hx.pow 2)).mul hz
  constructor
  · rintro ⟨ht1, ht2⟩
    exact ⟨h1.symm.trans ht1, h2.symm.trans ht2⟩
  · rintro ⟨hr1, hr2⟩
    exact ⟨h1.trans hr1, h2.trans hr2⟩

theorem tripleResidues_mem_localResidueTripleClasses {M aM u k : ℕ}
    (hM : 0 < M) {t : (ℕ × ℕ) × ℕ} (ht : localCompositeCongruences M aM u k t) :
    tripleResidues M t ∈ localResidueTripleClasses M aM u k := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (Nat.mod_lt _ hM), Finset.mem_range.mpr (Nat.mod_lt _ hM)⟩,
    Finset.mem_range.mpr (Nat.mod_lt _ hM)⟩, ?_⟩
  exact (localCompositeCongruences_congr
    (by simp [tripleResidues, Nat.ModEq]) (by simp [tripleResidues, Nat.ModEq])
    (by simp [tripleResidues, Nat.ModEq])).mp ht

theorem local_composite_harmonic_eq_residue_sum (N M aM u k : ℕ) (hM : 0 < M)
    {T : ℝ} (hT : 0 ≤ T) (hTN : T ≤ N) :
    (∑ t ∈ (boundedTripleBox N).filter (fun t =>
      (t.1.1 : ℝ) * (t.1.2 : ℝ) * (t.2 : ℝ) ≤ T ∧
        localCompositeCongruences M aM u k t),
      (1 : ℝ) / ((t.1.1 : ℝ) * (t.1.2 : ℝ) * (t.2 : ℝ))) =
      ∑ r ∈ localResidueTripleClasses M aM u k,
        residueHarmonicTriple M r.1.1 r.1.2 r.2 T := by
  classical
  let S := (boundedTripleBox N).filter (fun t =>
    (t.1.1 : ℝ) * (t.1.2 : ℝ) * (t.2 : ℝ) ≤ T ∧
      localCompositeCongruences M aM u k t)
  have hmaps : ∀ t ∈ S, tripleResidues M t ∈ localResidueTripleClasses M aM u k := by
    intro t ht
    exact tripleResidues_mem_localResidueTripleClasses hM (Finset.mem_filter.mp ht).2.2
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps
    (fun t => (1 : ℝ) / ((t.1.1 : ℝ) * (t.1.2 : ℝ) * (t.2 : ℝ)))
  change (∑ t ∈ S, _) = _
  rw [← hfib]
  apply Finset.sum_congr rfl
  intro r hr
  have hrbox := (Finset.mem_filter.mp hr).1
  have hrcond := (Finset.mem_filter.mp hr).2
  obtain ⟨hrxy, hrz⟩ := Finset.mem_product.mp hrbox
  obtain ⟨hrx, hry⟩ := Finset.mem_product.mp hrxy
  have hrxM : r.1.1 < M := Finset.mem_range.mp hrx
  have hryM : r.1.2 < M := Finset.mem_range.mp hry
  have hrzM : r.2 < M := Finset.mem_range.mp hrz
  rw [residueHarmonicTriple_eq_bounded_box N M r.1.1 r.1.2 r.2 hT hTN]
  apply Finset.sum_congr
  · ext t
    simp only [Finset.mem_filter, S]
    constructor
    · rintro ⟨⟨htbox, htbound, htcond⟩, htr⟩
      have hx := congrArg (fun z : (ℕ × ℕ) × ℕ => z.1.1) htr
      have hy := congrArg (fun z : (ℕ × ℕ) × ℕ => z.1.2) htr
      have hz := congrArg (fun z : (ℕ × ℕ) × ℕ => z.2) htr
      refine ⟨htbox, htbound, ?_, ?_, ?_⟩
      · simpa [tripleResidues, Nat.ModEq, Nat.mod_eq_of_lt hrxM] using hx
      · simpa [tripleResidues, Nat.ModEq, Nat.mod_eq_of_lt hryM] using hy
      · simpa [tripleResidues, Nat.ModEq, Nat.mod_eq_of_lt hrzM] using hz
    · rintro ⟨htbox, htbound, hx, hy, hz⟩
      have htcond := (localCompositeCongruences_congr hx hy hz).mpr hrcond
      refine ⟨⟨htbox, htbound, htcond⟩, ?_⟩
      apply Prod.ext
      · apply Prod.ext
        · simpa [tripleResidues, Nat.ModEq, Nat.mod_eq_of_lt hrxM] using hx
        · simpa [tripleResidues, Nat.ModEq, Nat.mod_eq_of_lt hryM] using hy
      · simpa [tripleResidues, Nat.ModEq, Nat.mod_eq_of_lt hrzM] using hz
  · intro t ht
    rfl

theorem scaled_local_harmonic_eq_residue_sum (N M aM u k : ℕ) (hM : 0 < M)
    (hk : 0 < k) :
    (∑ t ∈ scaledLocalDivisorTriples N M aM u k,
      (1 : ℝ) / ((t.1.1 * t.1.2 * t.2 : ℕ) : ℝ)) =
      ∑ r ∈ localResidueTripleClasses M aM u k,
        residueHarmonicTriple M r.1.1 r.1.2 r.2 ((N : ℝ) / (k : ℝ) ^ 2) := by
  classical
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hT : (0 : ℝ) ≤ (N : ℝ) / (k : ℝ) ^ 2 := by positivity
  have hTN : (N : ℝ) / (k : ℝ) ^ 2 ≤ N := by
    have hk1 : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr hk
    apply (div_le_iff₀ (sq_pos_of_pos hkR)).mpr
    have hksq : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    simpa using mul_le_mul_of_nonneg_left hksq (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  rw [← local_composite_harmonic_eq_residue_sum N M aM u k hM hT hTN]
  apply Finset.sum_bij (fun t _ => ((t.1.1, t.2), t.1.2))
  · rintro ⟨⟨x, e⟩, y⟩ ht
    obtain ⟨hx, he, hy, hprod, haM, hhu⟩ := (mem_scaledLocalDivisorTriples hk).mp ht
    have hbox := (Finset.mem_filter.mp ht).1
    obtain ⟨hxe, hyN⟩ := Finset.mem_product.mp hbox
    obtain ⟨hxN, heN⟩ := Finset.mem_product.mp hxe
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨hxN, hyN⟩, heN⟩, ?_, ?_⟩
    · rw [le_div_iff₀ (sq_pos_of_pos hkR)]
      have hh : (k : ℝ) ^ 2 * (x : ℝ) * (e : ℝ) * (y : ℝ) ≤ N := by exact_mod_cast hprod
      nlinarith only [hh]
    · constructor
      · (convert haM using 1; ring)
      · exact hhu
  · rintro ⟨⟨x, e⟩, y⟩ ht ⟨⟨x', e'⟩, y'⟩ hu heq
    simp only [Prod.mk.injEq] at heq ⊢
    tauto
  · rintro ⟨⟨x, y⟩, e⟩ ht
    obtain ⟨hbox, hbound, hcond⟩ := Finset.mem_filter.mp ht
    obtain ⟨hxy, heN⟩ := Finset.mem_product.mp hbox
    obtain ⟨hxN, hyN⟩ := Finset.mem_product.mp hxy
    have hx := (Finset.mem_Icc.mp hxN).1
    have hy := (Finset.mem_Icc.mp hyN).1
    have he := (Finset.mem_Icc.mp heN).1
    have hscaled : k ^ 2 * x * e * y ≤ N := by
      rw [le_div_iff₀ (sq_pos_of_pos hkR)] at hbound
      have hh : (k : ℝ) ^ 2 * (x : ℝ) * (e : ℝ) * (y : ℝ) ≤ N := by nlinarith only [hbound]
      exact_mod_cast hh
    refine ⟨((x, e), y), (mem_scaledLocalDivisorTriples hk).mpr
      ⟨hx, he, hy, hscaled, ?_, hcond.2⟩, rfl⟩
    (convert hcond.1 using 1; ring)
  · rintro ⟨⟨x, e⟩, y⟩ ht
    push_cast
    ring

/-- The Möbius decomposition of `H_{M,c}` in the proof of Proposition 4.3:
`∑_{a ≤ N, a ≡ a_M} ∑_{h ∣ a², h ≡ u} 1/a` equals
`∑_{k ≤ N} μ(k)/k² ∑_r ∑_{xyz ≤ N/k², (x,y,z) ≡ r} 1/(xyz)`, the inner sum
running over the residue triples `r ∈ localResidueTripleClasses M aM u k`. -/
theorem local_square_divisor_reciprocal_eq_residue_harmonic_triples
    (N M aM u : ℕ) (hM : 0 < M) :
    (∑ a ∈ (Finset.Icc 1 N).filter (fun a => Estimates.congMod a aM M),
      ∑ _h ∈ (a ^ 2).divisors.filter (fun h => Estimates.congMod h u M),
        (1 : ℝ) / (a : ℝ)) =
      ∑ k ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2) *
        ∑ r ∈ localResidueTripleClasses M aM u k,
          residueHarmonicTriple M r.1.1 r.1.2 r.2 ((N : ℝ) / (k : ℝ) ^ 2) := by
  rw [local_square_divisor_reciprocal_moebius_reindex]
  apply Finset.sum_congr rfl
  intro k hk
  rw [scaled_local_harmonic_eq_residue_sum N M aM u k hM (Finset.mem_Icc.mp hk).1]

end ErdosStraus.DivisorEstimates
