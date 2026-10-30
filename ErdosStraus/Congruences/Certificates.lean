import Mathlib.Tactic

/-!
# Lemma 2.3 and finite congruence systems

Lemma 2.3: if `q = ma - 1`, `e ∣ a²` and `q ∣ n + me`, then `m/n` is a sum of three
positive unit fractions, with denominators `an`, `(an + e)/q` and `(an + (an)²/e)/q`.
The file also contains the finite arithmetic used in Sections 5 and 6: the Chinese
remainder theorem for lists of congruences, the deletion identity behind Lemma 5.1,
the even Bonferroni inequalities of Theorem 5.4, and counts of residue classes in
`[0, N]` (Lemma 5.3).
-/

namespace ErdosStraus.Arithmetic

/-- `4/n = 1/x + 1/y + 1/z` for some positive integers `x, y, z`. -/
def esRepresentable (n : Nat) : Prop :=
  ∃ x y z : Nat,
    0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (n : ℚ) =
        1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

/-- `n` is exceptional: `4/n` is not a sum of three positive unit fractions. -/
def esExceptional (n : Nat) : Prop :=
  ¬ esRepresentable n

/-!
## Compatible congruences

The congruences `n ≡ a (mod q)` and `n ≡ b (mod r)` are compatible when
`a ≡ b (mod gcd(q, r))`. A list of pairwise compatible congruences with positive
moduli has a solution, unique modulo the lcm of the moduli.
-/

/-- `a ≡ b (mod gcd(q, r))`. -/
def residueCompatible (q r a b : Nat) : Prop :=
  a ≡ b [MOD Nat.gcd q r]

/-- The data `(e, d₋, d₊, p)` of an event in Section 6. The event is
`d₊p ∣ n + me`, so compatibility of two events compares the residues of `me`. -/
structure SatEvent where
  e : Nat
  dMinus : Nat
  dPlus : Nat
  p : Nat
deriving DecidableEq

/-- The residue of `-a` modulo `q`, in `[0, q)`. -/
def negModResidue (q a : Nat) : Nat :=
  (q - a % q) % q

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

/-- The lcm of the moduli of a list of congruences `n ≡ c (mod q)`, each given as
the pair `(q, c)`. -/
def congruenceLcm (rows : List (Nat × Nat)) : Nat :=
  rows.foldr (fun row acc => Nat.lcm row.1 acc) 1

/-- `n` satisfies every congruence of the list. -/
def satisfiesCongruenceRows (n : Nat) (rows : List (Nat × Nat)) : Prop :=
  ∀ row ∈ rows, n ≡ row.2 [MOD row.1]

def congruenceRowsModuliPositive (rows : List (Nat × Nat)) : Prop :=
  ∀ row ∈ rows, 0 < row.1

/-- Any two congruences of the list are compatible. -/
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
    simp [inf_sup_left]

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
      simp [congruenceLcm]
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

/-- The primes `p ≤ B`. -/
def primeFinsetUpTo (B : ℕ) : Finset ℕ :=
  (Finset.Icc 2 B).filter Nat.Prime

theorem lowerBound_pow_primeFactors_card_le_self
    (n q : ℕ) (hn : 0 < n)
    (hq : ∀ p ∈ n.primeFactors, q ≤ p) :
    q ^ n.primeFactors.card ≤ n := by
  classical
  have hprod : ∏ p ∈ n.primeFactors, q ≤ ∏ p ∈ n.primeFactors, p :=
    Finset.prod_le_prod (fun _ _ => Nat.zero_le q) hq
  calc
    q ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, q := by
      simp [Finset.prod_const]
    _ ≤ ∏ p ∈ n.primeFactors, p := hprod
    _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

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

/-- If every prime factor of `n` is at least `q ≥ 2`, then `n` has at most
`log n / log q` prime factors, so `∑_{p ∣ n} 1/p ≤ (log n / log q) / q`. -/
theorem primeFactors_recip_sum_le_log_div_log_div
    (n q : ℕ) (hn : 0 < n) (hq2 : 2 ≤ q)
    (hq : ∀ p ∈ n.primeFactors, q ≤ p) :
    (∑ p ∈ n.primeFactors, (1 : ℝ) / (p : ℝ)) ≤
      (Real.log (n : ℝ) / Real.log (q : ℝ)) / (q : ℝ) := by
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_two hq2
  have hpow := lowerBound_pow_primeFactors_card_le_self n q hn hq
  have hpowpos : 0 < (((q ^ n.primeFactors.card : ℕ) : ℝ)) := by
    exact_mod_cast Nat.pow_pos (n := n.primeFactors.card) hqpos
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

/-- The substitution `n = Dt`: `∑_{n ∈ U, D ∣ n} 1/n = D⁻¹ ∑ 1/t`, where `t` runs
over the quotients `n/D`. -/
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
    rw [← Nat.mul_div_cancel' hnD, Nat.cast_mul,
      Nat.mul_div_cancel_left (n / D) hD]
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

/-- For `a ≥ 0` on primes, `∑_{D ≤ B squarefree} ∏_{p ∣ D} a(p) ≤ ∏_{p ≤ B} (1 + a(p))`.
A squarefree `D` is determined by its set of prime factors, and the right side
is the sum over all sets of primes up to `B`. -/
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

/-- `1/lcm(L, q) = (1/L)(1/q) gcd(L, q)`, as in the proof of Lemma 5.1. -/
theorem brun_lcm_weight_identity
    (L q : Nat) (hL : 0 < L) (hq : 0 < q) :
    (1 : ℚ) / (Nat.lcm L q : ℚ) =
      (1 / (L : ℚ)) * (1 / (q : ℚ)) * (Nat.gcd L q : ℚ) := by
  have h := lcm_recip_identity L q hL hq
  have hLQ : (L : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  rw [h]
  field_simp [hLQ, hqQ]

/-- The deletion identity of Lemma 5.1: for a property `P` of finite sets that is
preserved by deleting elements,
`r ∑_{|T| = r, P T} f(T) = ∑_{|S| = r-1, P S} ∑_{i ∉ S, P (S ∪ {i})} f(S ∪ {i})`.
Both sides count the pairs `(T, i)` with `i ∈ T`. -/
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
        · exact Finset.notMem_erase x.2 x.1
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
        · rw [Finset.card_insert_of_notMem hiData.2.1, hcardS]
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

/-!
## Even Bonferroni inequalities

For every `W` and `R`,
`1_{W=0} ≤ ∑_{r ≤ 2R} (-1)^r (W choose r) ≤ 1_{W=0} + (W choose 2R)`,
as used in the proof of Theorem 5.4. For `m < W` the truncated alternating sum is
`(-1)^m (W - 1 choose m)`, and for `m ≥ W` it is the full sum `1_{W=0}`.
-/

/-- `∑_{r ≤ m} (-1)^r (W choose r)`. -/
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
## Subsets of events through a point

If `W` events contain a point, the number of `r`-subsets of these events is
`(W choose r)`. Summing over the points turns the Bonferroni inequalities into
bounds for the number of points lying in no event, in terms of the sums over
`r`-subsets `S` of the number of points lying in every event of `S`.
-/

/-- The number of events `i` with `hit i`. -/
noncomputable def hitEventCount {α : Type*} (events : Finset α) (hit : α → Prop)
    [DecidablePred hit] : Nat :=
  (events.filter hit).card

/-- The `r`-subsets of events all of whose members satisfy `hit`. -/
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

/-- The number of points lying in every event of `s`. -/
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
## Residue classes in `[0, N]`

A residue class modulo `q > 0` contains between `N/q - 1` and `N/q + 1` integers
of `[0, N]`; this is the error term `O(1)` in Lemma 5.3.
-/

/-- The number of `n ∈ [0, N]` with `n ≡ a (mod q)`. -/
def residueClassCountUpTo (N q a : Nat) : Nat :=
  ((Finset.range (N + 1)).filter (fun n => n ≡ a [MOD q])).card

theorem residueClassCountUpTo_le_div_add_one
    (N q a : Nat) (_hq : 0 < q) :
    residueClassCountUpTo N q a ≤ N / q + 1 := by
  classical
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

/-- The integers `a % q + kq` with `k < N / q` lie in the class. -/
theorem div_le_residueClassCountUpTo
    (N q a : Nat) (hq : 0 < q) :
    N / q ≤ residueClassCountUpTo N q a := by
  classical
  let reps : Finset Nat := Finset.range (N / q)
  let cls : Finset Nat :=
    (Finset.range (N + 1)).filter (fun n => n ≡ a [MOD q])
  let f : Nat → Nat := fun k => a % q + k * q
  have hmaps : ∀ k ∈ reps, f k ∈ cls := by
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
      simp [f, Nat.add_mod]
  have hinj : (reps : Set Nat).InjOn f := by
    intro x _hx y _hy hxy
    have hmul : x * q = y * q := Nat.add_left_cancel hxy
    exact Nat.eq_of_mul_eq_mul_right hq hmul
  have hcard : reps.card ≤ cls.card :=
    Finset.card_le_card_of_injOn f hmaps hinj
  simpa [residueClassCountUpTo, reps, cls] using hcard

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

/-- The number of `n ∈ [0, N]` with `n ≡ b (mod P)` that satisfy every congruence
of `rows`. -/
noncomputable def baseResidualRowsCountUpTo
    (N Pz b : Nat) (rows : List (Nat × Nat)) : Nat := by
  classical
  exact ((Finset.range (N + 1)).filter
    (fun n => n ≡ b [MOD Pz] ∧ satisfiesCongruenceRows n rows)).card

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

theorem baseResidualRowsCountUpTo_eq_residueClassCountUpTo
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

/-- The reduced residues `0 ≤ b < P`, `(b, P) = 1`; the classes `b (mod P(z))` of
Section 6 run over them. -/
noncomputable def reducedResiduesMod (P : Nat) : Finset Nat := by
  classical
  exact (Finset.range P).filter (fun b => Nat.Coprime b P)

theorem mem_reducedResiduesMod_iff (P b : Nat) :
    b ∈ reducedResiduesMod P ↔ b < P ∧ Nat.Coprime b P := by
  classical
  simp [reducedResiduesMod]

/-!
## Lemma 2.3

For `q = ma - 1`, `e ∣ a²` and `q ∣ n + me`, the denominators `x = an`,
`y = (an + e)/q` and `z = (an + (an)²/e)/q` are positive integers with
`qy - x = e`, `qz - x = x²/e`, hence `(qy - x)(qz - x) = x²` and
`m/n = 1/x + 1/y + 1/z`.
-/

/-- `q_a = ma - 1`. -/
def fixedQ (m a : Nat) : Nat :=
  m * a - 1

/-- The first denominator `x = an` of Lemma 2.3. -/
def fixedFanX (n a : Nat) : Nat :=
  a * n

/-- The second denominator `y = (an + e)/(ma - 1)` of Lemma 2.3. -/
def fixedFanY (m n a e : Nat) : Nat :=
  (a * n + e) / fixedQ m a

/-- The third denominator `z = (an + a²n²/e)/(ma - 1)` of Lemma 2.3. -/
def fixedFanZ (m n a e : Nat) : Nat :=
  (a * n + (a ^ 2 * n ^ 2) / e) / fixedQ m a

/-- `n(yz + xz + xy) = mxyz`, that is, `m/n = 1/x + 1/y + 1/z` with the
denominators cleared. -/
def fixedCross (m n x y z : Nat) : Prop :=
  n * (y * z + x * z + x * y) = m * x * y * z

/-- If `h ∣ a²`, then `a = deA` and `h = d²e` with `d, e, A` positive: take
`g = gcd(h, a)`, `d = h/g`, `e = g²/h` and `A = a/g` (proof of Theorem 2.2). -/
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
    exact (Nat.dvd_gcd_mul_gcd_iff_dvd_mul (k := h) (n := a) (m := a)).2 hDvdAA
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

/-- Integrality in Lemma 2.3 over `ℤ`: if `q = ma - 1`, `a² = es` and
`n + me = qk`, then `q` divides `an + e` and `an + sn²`. -/
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

/-- Lemma 2.3 for the denominators `fixedFanX`, `fixedFanY` and `fixedFanZ`: they
are positive and `m/n = 1/x + 1/y + 1/z`. -/
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

/-- Lemma 2.3: if `e ∣ a²` and `ma - 1 ∣ n + me`, then `m/n` is a sum of three
positive unit fractions. -/
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

/-- The application of Lemma 2.3 in Section 6: if `m·rs ∣ Q + 1` and
`Q ∣ n + m·rs²`, then `a = (Q + 1)/m` satisfies `ma - 1 = Q`, `rs ∣ a` and
`rs² ∣ a²`, and Lemma 2.3 applies with `e = rs²`. -/
theorem fixedFan_nat_certificate_of_certificate_progression
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

theorem fixedFan_positive_unit_fractions_of_certificate_progression
    (m n Q r s : Nat)
    (hm : 2 ≤ m) (hn : 0 < n) (hr : 0 < r) (hs : 0 < s)
    (hprogression : m * (r * s) ∣ Q + 1)
    (hcong : Q ∣ n + m * (r * s ^ 2)) :
    ∃ a x y z : Nat,
      0 < a ∧ m * a = Q + 1 ∧
      0 < x ∧ 0 < y ∧ 0 < z ∧
      (m : ℚ) / (n : ℚ) =
        1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  rcases fixedFan_nat_certificate_of_certificate_progression
      m n Q r s hm hn hr hs hprogression hcong with
    ⟨a, ha, hma, _hQ, _hcond, _hedvd, hx, hy, hz, hident⟩
  exact ⟨a, fixedFanX n a, fixedFanY m n a (r * s ^ 2),
    fixedFanZ m n a (r * s ^ 2), ha, hma, hx, hy, hz, hident⟩

theorem fixedFan_positive_unit_fractions_of_coprime_split
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
  exact fixedFan_positive_unit_fractions_of_certificate_progression
    m n (dMinus * (dPlus * p)) r s hm hn hr hs hprogression hfull

/-- An event `(e, d₋, d₊, p)` of Section 6, with `e = rs²`, `(d₋, d₊p) = 1` and
`m·rs ∣ d₋d₊p + 1`, gives a representation of `m/n` whenever `n ≡ b (mod P)`,
`d₋ ∣ P`, `b ≡ -me (mod d₋)` and `d₊p ∣ n + me`. -/
theorem fixedFan_positive_unit_fractions_of_base_class
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
  exact fixedFan_positive_unit_fractions_of_coprime_split
    m n dMinus dPlus p r s hm hn hr hs hcop hprogression hbase hresidual

end ErdosStraus.Arithmetic
