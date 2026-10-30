import ErdosStraus.Congruences.Certificates

/-!
# Theorems 2.1 and 2.2: Type II representations

Let `p` be a prime and `m ≥ 4`. A Type II representation
`m/p = 1/(pu) + 1/(pv) + 1/w` with `p ∤ w` has the normal form `u = deA`,
`v = eAB`, `w = deB` with `mdeAB = Ap + d + B` (Theorem 2.1). Consequently such a
representation with `u = a` exists if and only if `ma - 1 ∣ p + mh` for some
`h ∣ a²` (Theorem 2.2).
-/

namespace ErdosStraus.FixedNumeratorTypeII

open ErdosStraus.Arithmetic

/-- `m/p = 1/(pa) + 1/(pv) + 1/w` for some positive `v, w` with `p ∤ w`, in the
cross-multiplied form `fixedCross`. -/
def WithFirstDenominator (m p a : ℕ) : Prop :=
  ∃ v w : ℕ, 0 < v ∧ 0 < w ∧ ¬ p ∣ w ∧
    fixedCross m p (p * a) (p * v) w

theorem cross_iff_unit_fractions (m n x y z : ℕ)
    (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    fixedCross m n x y z ↔
      (m : ℚ) / n = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  have hx0 : (x : ℚ) ≠ 0 := by positivity
  have hy0 : (y : ℚ) ≠ 0 := by positivity
  have hz0 : (z : ℚ) ≠ 0 := by positivity
  unfold fixedCross
  constructor
  · intro h
    have hQ : (n : ℚ) * (y * z + x * z + x * y) = m * x * y * z := by
      exact_mod_cast h
    field_simp [hn0, hx0, hy0, hz0]
    nlinarith only [hQ]
  · intro h
    field_simp [hn0, hx0, hy0, hz0] at h
    have hQ : (n : ℚ) * (y * z + x * z + x * y) = m * x * y * z := by
      nlinarith only [h]
    exact_mod_cast hQ

/-- For `m ≥ 4`, the three denominators of `m/p` cannot all be multiples of `p`,
since otherwise the sum is at most `3/p`. -/
theorem not_all_denominators_multiples (m p u v t : ℕ)
    (hm : 4 ≤ m) (hp : 0 < p) (hu : 0 < u) (hv : 0 < v) (ht : 0 < t) :
    ¬ fixedCross m p (p * u) (p * v) (p * t) := by
  intro h
  have hcancel : (p * p * p) * (m * u * v * t) =
      (p * p * p) * (u * v + u * t + v * t) := by
    unfold fixedCross at h
    nlinarith only [h]
  have heq := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < p * p * p) hcancel
  have h1 : u * v ≤ u * v * t := Nat.le_mul_of_pos_right _ ht
  have h2 : u * t ≤ u * v * t := by
    have hh := Nat.le_mul_of_pos_right (u * t) hv
    nlinarith only [hh]
  have h3 : v * t ≤ u * v * t := by
    have hh := Nat.le_mul_of_pos_left (v * t) hu
    nlinarith only [hh]
  have hprod : 0 < u * v * t := by positivity
  have hmul := Nat.mul_le_mul_right (u * v * t) hm
  nlinarith

/-- Theorem 2.1: if `mdeAB = Ap + d + B`, then
`m/p = 1/(pdeA) + 1/(peAB) + 1/(deB)` in cross-multiplied form. -/
theorem cross_of_linear (m p d e A B : ℕ)
    (h : m * d * e * A * B = A * p + d + B) :
    fixedCross m p (p * (d * e * A)) (p * (e * A * B)) (d * e * B) := by
  unfold fixedCross
  calc
    _ = p ^ 2 * d * e ^ 2 * A * B * (A * p + d + B) := by ring
    _ = p ^ 2 * d * e ^ 2 * A * B * (m * d * e * A * B) := by rw [h]
    _ = _ := by ring

/-- The converse in Theorem 2.1: every Type II representation
`m/p = 1/(pu) + 1/(pv) + 1/w` with `p ∤ w` has `u = deA`, `v = eAB`, `w = deB` and
`mdeAB = Ap + d + B` for some positive `d, e, A, B`. -/
theorem normal_form_of_representation (m p u v w : ℕ)
    (hp : p.Prime) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hpw : ¬ p ∣ w) (h : fixedCross m p (p * u) (p * v) w) :
    ∃ d e A B : ℕ, 0 < d ∧ 0 < e ∧ 0 < A ∧ 0 < B ∧
      u = d * e * A ∧ v = e * A * B ∧ w = d * e * B ∧
      m * d * e * A * B = A * p + d + B := by
  have hpPos : 0 < p := hp.pos
  obtain ⟨g, d, B, hg, hdB, huEq, hvEq⟩ :=
    Nat.exists_coprime' (Nat.gcd_pos_of_pos_left v hu)
  have hd : 0 < d := Nat.pos_of_mul_pos_right (huEq ▸ hu)
  have hB : 0 < B := Nat.pos_of_mul_pos_right (hvEq ▸ hv)
  have hbase : m * g * d * B * w = w * (d + B) + p * g * d * B := by
    have hcancel : (p * p * g) * (m * g * d * B * w) =
        (p * p * g) * (w * (d + B) + p * g * d * B) := by
      unfold fixedCross at h
      rw [huEq, hvEq] at h
      nlinarith only [h]
    exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < p * p * g) hcancel
  have hdwB : d ∣ w * B := by
    have hleft : d ∣ m * g * d * B * w := ⟨m * g * B * w, by ring⟩
    rw [hbase, mul_add] at hleft
    have h0 : d ∣ w * d := dvd_mul_left d w
    have h1 : d ∣ p * g * d * B := ⟨p * g * B, by ring⟩
    exact (Nat.dvd_add_right h0).mp ((Nat.dvd_add_left h1).mp hleft)
  have hBwd : B ∣ w * d := by
    have hleft : B ∣ m * g * d * B * w := ⟨m * g * d * w, by ring⟩
    rw [hbase, mul_add, add_comm (w * d) (w * B)] at hleft
    have h0 : B ∣ w * B := dvd_mul_left B w
    have h1 : B ∣ p * g * d * B := dvd_mul_left B (p * g * d)
    exact (Nat.dvd_add_right h0).mp ((Nat.dvd_add_left h1).mp hleft)
  have hdw : d ∣ w := hdB.dvd_of_dvd_mul_right hdwB
  have hBw : B ∣ w := hdB.symm.dvd_of_dvd_mul_right hBwd
  obtain ⟨e, hwEq⟩ := hdB.mul_dvd_of_dvd_of_dvd hdw hBw
  have he : 0 < e := Nat.pos_of_mul_pos_left (hwEq ▸ hw)
  have hwEq' : w = d * e * B := by rw [hwEq]; ring
  have hsecond : m * g * d * e * B = e * (d + B) + p * g := by
    have hcancel : (d * B) * (m * g * d * e * B) =
        (d * B) * (e * (d + B) + p * g) := by
      rw [hwEq'] at hbase
      nlinarith only [hbase]
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hd hB) hcancel
  have hep : Nat.Coprime e p :=
    (hp.coprime_iff_not_dvd.mpr (fun hpe =>
      hpw (hpe.trans ⟨d * B, by rw [hwEq']; ring⟩))).symm
  have hepg : e ∣ p * g := by
    have hleft : e ∣ m * g * d * e * B := ⟨m * g * d * B, by ring⟩
    rw [hsecond] at hleft
    exact (Nat.dvd_add_right (dvd_mul_right e (d + B))).mp hleft
  obtain ⟨A, hgEq⟩ := hep.dvd_of_dvd_mul_left hepg
  have hA : 0 < A := Nat.pos_of_mul_pos_left (hgEq ▸ hg)
  have hlinear : m * d * e * A * B = A * p + d + B := by
    have hcancel : e * (m * d * e * A * B) = e * (A * p + d + B) := by
      rw [hgEq] at hsecond
      nlinarith only [hsecond]
    exact Nat.eq_of_mul_eq_mul_left he hcancel
  refine ⟨d, e, A, B, hd, he, hA, hB, ?_, ?_, hwEq', hlinear⟩
  · rw [huEq, hgEq]; ring
  · rw [hvEq, hgEq]; ring

theorem modulus_add_one (m a : ℕ) (hm : 0 < m) (ha : 0 < a) :
    fixedQ m a + 1 = m * a := by
  unfold fixedQ
  have : 0 < m * a := Nat.mul_pos hm ha
  omega

/-- For `a = deA`: `ma - 1 ∣ p + md²e` if and only if `mdeAB = Ap + d + B` for some
`B`. -/
theorem congruence_iff_linear (m p d e A : ℕ) (hm : 0 < m)
    (hd : 0 < d) (he : 0 < e) (hA : 0 < A) :
    fixedQ m (d * e * A) ∣ p + m * (d ^ 2 * e) ↔
      ∃ B : ℕ, m * d * e * A * B = A * p + d + B := by
  let q := fixedQ m (d * e * A)
  have hq : q + 1 = m * d * e * A := by
    simpa [q, Nat.mul_assoc] using modulus_add_one m (d * e * A) hm (by positivity)
  have hidentity : A * (p + m * (d ^ 2 * e)) = A * p + d + q * d := by
    calc
      _ = A * p + d * (m * d * e * A) := by ring
      _ = A * p + d * (q + 1) := by rw [hq]
      _ = _ := by ring
  constructor
  · intro hc
    have hs : q ∣ A * (p + m * (d ^ 2 * e)) := dvd_mul_of_dvd_right hc A
    rw [hidentity] at hs
    obtain ⟨B, hB⟩ := (Nat.dvd_add_left (dvd_mul_right q d)).mp hs
    exact ⟨B, by nlinarith [hB]⟩
  · rintro ⟨B, hB⟩
    have hs : q ∣ A * (p + m * (d ^ 2 * e)) := by
      refine ⟨B + d, ?_⟩
      rw [hidentity]
      nlinarith [hB]
    have hprod : 1 ≤ m * (d * e * A) :=
      Nat.mul_pos hm (Nat.mul_pos (Nat.mul_pos hd he) hA)
    have hcopProd : Nat.Coprime q (m * (d * e * A)) := by
      exact (Nat.coprime_self_sub_left (m := 1) (n := m * (d * e * A)) hprod).2
        (by simp)
    have hcop : Nat.Coprime q A := hcopProd.coprime_dvd_right
      ⟨m * d * e, by ring⟩
    exact (hcop.dvd_mul_left).mp hs

/-- Theorem 2.2: there is a Type II representation of `m/p` with first denominator
`pa` if and only if `ma - 1 ∣ p + mh` for some positive `h ∣ a²`. -/
theorem completeFan_congruence_iff_typeII_representation
    (m p a : ℕ) (hm : 4 ≤ m) (hp : p.Prime) (ha : 0 < a) :
    (∃ h : ℕ, 0 < h ∧ h ∣ a ^ 2 ∧ fixedQ m a ∣ p + m * h) ↔
      WithFirstDenominator m p a := by
  constructor
  · rintro ⟨h, hh, hdiv, hc⟩
    obtain ⟨d, e, A, hd, he, hA, haEq, hhEq⟩ :=
      completeFan_decomposition_of_dvd_square a h ha hh hdiv
    obtain ⟨B, hlinear⟩ := (congruence_iff_linear m p d e A (by omega) hd he hA).mp
      (by simpa [haEq, hhEq] using hc)
    have hB : 0 < B := by
      by_contra hb
      have : B = 0 := Nat.eq_zero_of_not_pos hb
      simp only [this, mul_zero, add_zero] at hlinear
      omega
    have hcross := cross_of_linear m p d e A B hlinear
    have hpw : ¬ p ∣ d * e * B := by
      rintro ⟨t, htEq⟩
      have ht : 0 < t := Nat.pos_of_mul_pos_left
        (htEq ▸ (show 0 < d * e * B by positivity))
      rw [htEq] at hcross
      exact not_all_denominators_multiples m p (d * e * A) (e * A * B) t
        hm hp.pos (by positivity) (by positivity) ht hcross
    exact ⟨e * A * B, d * e * B, by positivity, by positivity, hpw,
      by simpa [haEq] using hcross⟩
  · rintro ⟨v, w, hv, hw, hpw, hc⟩
    obtain ⟨d, e, A, B, hd, he, hA, _hB, haEq, _hvEq, _hwEq, hlinear⟩ :=
      normal_form_of_representation m p a v w hp ha hv hw hpw hc
    refine ⟨d ^ 2 * e, by positivity, ?_, ?_⟩
    · rw [haEq]
      exact ⟨e * A ^ 2, by ring⟩
    · simpa [haEq] using
        (congruence_iff_linear m p d e A (by omega) hd he hA).mpr ⟨B, hlinear⟩

/-- Theorem 2.2 stated with unit fractions. -/
theorem completeFan_congruence_iff_typeII_unit_fractions
    (m p a : ℕ) (hm : 4 ≤ m) (hp : p.Prime) (ha : 0 < a) :
    (∃ h : ℕ, 0 < h ∧ h ∣ a ^ 2 ∧ fixedQ m a ∣ p + m * h) ↔
      ∃ v w : ℕ, 0 < v ∧ 0 < w ∧ ¬ p ∣ w ∧
        (m : ℚ) / p =
          1 / ((p * a : ℕ) : ℚ) + 1 / ((p * v : ℕ) : ℚ) + 1 / (w : ℚ) := by
  rw [completeFan_congruence_iff_typeII_representation m p a hm hp ha]
  unfold WithFirstDenominator
  constructor <;> rintro ⟨v, w, hv, hw, hpw, h⟩ <;>
    refine ⟨v, w, hv, hw, hpw, ?_⟩
  · exact (cross_iff_unit_fractions m p (p * a) (p * v) w
      hp.pos (Nat.mul_pos hp.pos ha) (Nat.mul_pos hp.pos hv) hw).mp h
  · exact (cross_iff_unit_fractions m p (p * a) (p * v) w
      hp.pos (Nat.mul_pos hp.pos ha) (Nat.mul_pos hp.pos hv) hw).mpr h

end ErdosStraus.FixedNumeratorTypeII
