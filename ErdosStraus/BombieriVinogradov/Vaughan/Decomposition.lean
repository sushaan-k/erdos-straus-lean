import ErdosStraus.BombieriVinogradov.LargeSieve.BombieriDavenport

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

/-!
# Vaughan's decomposition of `Λ`

For every `n` and all cutoffs `u, v`,
`Λ(n) = TypeI(n; u, v) + TypeII(n; u, v) + Small(n; v)`, where `Small(n; v)` is
`Λ(n)` for `n ≤ v` and `0` otherwise. If `b = bI + bII + bSmall`, the maximal squared
prefix sum of `b` twisted by a primitive character is at most three times the sum of
the maxima for the three pieces. The file also bounds the energy of the small piece,
compares a character with the primitive character inducing it, and rewrites the Type I
prefix sums as short sums over `d ≤ u` (and `e ≤ v`) of character sums over a long
variable.
-/

namespace BombieriVinogradov

open Classical Finset
open scoped BigOperators ArithmeticFunction
noncomputable section

/-- The Type I part of Vaughan's identity,
`∑_{d ∣ n, d ≤ u} μ(d) log(n/d) - ∑_{d ∣ n, d ≤ u} ∑_{e ∣ n/d, e ≤ v} μ(d) Λ(e)`. -/
def vaughanTypeI (n u v : ℕ) : ℝ :=
  vaughanFirst n u - vaughanMiddle n u v

/-- The Type II part of Vaughan's identity,
`∑_{d ∣ n, d > u} ∑_{e ∣ n/d, e > v} μ(d) Λ(e)`. -/
def vaughanTypeII (n u v : ℕ) : ℝ :=
  vaughanThird n u v

/-- `Λ(n)` for `n ≤ v` and `0` otherwise. With this term the identity holds for
every `n`, not only for `n > v`. -/
def vaughanSmall (n v : ℕ) : ℝ :=
  if n ≤ v then ArithmeticFunction.vonMangoldt n else 0

/-- Vaughan's identity `Λ(n) = TypeI(n; u, v) + TypeII(n; u, v) + Small(n; v)`,
for every `n` and all cutoffs `u, v`. -/
theorem vaughanIdentity_typeI_typeII_small (n u v : ℕ) :
    ArithmeticFunction.vonMangoldt n =
      vaughanTypeI n u v + vaughanTypeII n u v + vaughanSmall n v := by
  have hsplit :
      (∑ d ∈ n.divisors,
          ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v),
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
              ArithmeticFunction.vonMangoldt e) =
        vaughanSecond n u v + vaughanMiddle n u v := by
    unfold vaughanSecond vaughanMiddle
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := n.divisors) (p := fun d => u < d)]
    simp only [not_lt]
  have hsecond : vaughanSecond n u v =
      vaughanSmall n v - vaughanMiddle n u v := by
    have hfull := vaughanFullSecondSum n v
    rw [hsplit] at hfull
    have hsum : vaughanSecond n u v + vaughanMiddle n u v =
        vaughanSmall n v := by
      simpa [vaughanSmall] using hfull
    linarith
  rw [vaughanIdentity, hsecond]
  simp only [vaughanTypeI, vaughanTypeII]
  ring

/-- The sequence `b(n) Λ(n)`. -/
def vaughanLambdaCoeff (b : ℤ → ℂ) (n : ℤ) : ℂ :=
  b n * (ArithmeticFunction.vonMangoldt n.toNat : ℂ)

/-- The sequence `b(n) TypeI(n; u, v)`. -/
def vaughanTypeICoeff (b : ℤ → ℂ) (u v : ℕ) (n : ℤ) : ℂ :=
  b n * (vaughanTypeI n.toNat u v : ℂ)

/-- The sequence `b(n) TypeII(n; u, v)`. -/
def vaughanTypeIICoeff (b : ℤ → ℂ) (u v : ℕ) (n : ℤ) : ℂ :=
  b n * (vaughanTypeII n.toNat u v : ℂ)

/-- The sequence `b(n) Small(n; v)`. -/
def vaughanSmallCoeff (b : ℤ → ℂ) (v : ℕ) (n : ℤ) : ℂ :=
  b n * (vaughanSmall n.toNat v : ℂ)

theorem vaughanLambdaCoeff_eq (b : ℤ → ℂ) (u v : ℕ) (n : ℤ) :
    vaughanLambdaCoeff b n =
      vaughanTypeICoeff b u v n + vaughanTypeIICoeff b u v n +
        vaughanSmallCoeff b v n := by
  rw [vaughanLambdaCoeff, vaughanTypeICoeff, vaughanTypeIICoeff,
    vaughanSmallCoeff, vaughanIdentity_typeI_typeII_small]
  push_cast
  ring

private theorem norm_add_add_sq_le_three (x y z : ℂ) :
    ‖x + y + z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
  have hnorm : ‖x + y + z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ := by
    calc
      ‖x + y + z‖ ≤ ‖x + y‖ + ‖z‖ := norm_add_le _ _
      _ ≤ (‖x‖ + ‖y‖) + ‖z‖ := by gcongr; exact norm_add_le _ _
  have hsq : ‖x + y + z‖ ^ 2 ≤ (‖x‖ + ‖y‖ + ‖z‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hcauchy : (‖x‖ + ‖y‖ + ‖z‖) ^ 2 ≤
      3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖x‖ - ‖z‖),
      sq_nonneg (‖y‖ - ‖z‖)]
  exact hsq.trans hcauchy

/-- If `b = bI + bII + bSmall` on `[1, N]`, then for every primitive character `χ`
the maximal squared prefix sum of `b χ` over `[1, N]` is at most three times the sum
of those of `bI χ`, `bII χ` and `bSmall χ`. -/
theorem primitiveCharacterPrefixMaxSquare_le_three
    (b bI bII bSmall : ℤ → ℂ) (N q : ℕ) (χ : PrimitiveCharacter q)
    (hdecomp : ∀ n ∈ Finset.Icc (1 : ℤ) N,
      b n = bI n + bII n + bSmall n) :
    primitiveCharacterPrefixMaxSquare b 0 N q χ ≤
      3 * (primitiveCharacterPrefixMaxSquare bI 0 N q χ +
        primitiveCharacterPrefixMaxSquare bII 0 N q χ +
        primitiveCharacterPrefixMaxSquare bSmall 0 N q χ) := by
  unfold primitiveCharacterPrefixMaxSquare
  apply Finset.max'_le
  intro s hs
  rcases Finset.mem_image.mp hs with ⟨y, hy, rfl⟩
  have hyN : y ≤ N := by simpa [Finset.mem_range] using hy
  let xI := ∑ n ∈ Finset.Icc (1 : ℤ) y, bI n * χ.1 (n : ZMod q)
  let xII := ∑ n ∈ Finset.Icc (1 : ℤ) y, bII n * χ.1 (n : ZMod q)
  let xSmall := ∑ n ∈ Finset.Icc (1 : ℤ) y, bSmall n * χ.1 (n : ZMod q)
  have hsum :
      (∑ n ∈ Finset.Icc (1 : ℤ) y, b n * χ.1 (n : ZMod q)) =
        xI + xII + xSmall := by
    simp only [xI, xII, xSmall, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hdecomp n]
    · ring
    · rw [Finset.mem_Icc] at hn ⊢
      exact ⟨hn.1, hn.2.trans (by exact_mod_cast hyN)⟩
  simp only [primitiveCharacterPrefixSquare, zero_add]
  change ‖∑ n ∈ Finset.Icc (1 : ℤ) (y : ℤ),
      b n * χ.1 (n : ZMod q)‖ ^ 2 ≤ _
  rw [hsum]
  have hI := primitiveCharacterPrefixSquare_le_max bI 0 hyN χ
  have hII := primitiveCharacterPrefixSquare_le_max bII 0 hyN χ
  have hSmall := primitiveCharacterPrefixSquare_le_max bSmall 0 hyN χ
  dsimp [primitiveCharacterPrefixSquare] at hI hII hSmall
  simp only [zero_add] at hI hII hSmall
  refine (norm_add_add_sq_le_three xI xII xSmall).trans ?_
  gcongr
  · simpa [xI, primitiveCharacterPrefixMaxSquare,
      primitiveCharacterPrefixSquare] using hI
  · simpa [xII, primitiveCharacterPrefixMaxSquare,
      primitiveCharacterPrefixSquare] using hII
  · simpa [xSmall, primitiveCharacterPrefixMaxSquare,
      primitiveCharacterPrefixSquare] using hSmall

/-! ## The small piece -/

/-- The integers `n ∈ [1, N]` with `n ≤ v`, which contain the support of
`b(n) Small(n; v)` in `[1, N]`. -/
def vaughanSmallSupport (N v : ℕ) : Finset ℤ :=
  (Finset.Icc (1 : ℤ) N).filter (fun n => n.toNat ≤ v)

@[simp]
theorem mem_vaughanSmallSupport {N v : ℕ} {n : ℤ} :
    n ∈ vaughanSmallSupport N v ↔ 1 ≤ n ∧ n ≤ N ∧ n.toNat ≤ v := by
  simp [vaughanSmallSupport, and_assoc]

theorem vaughanSmallCoeff_eq_zero_of_v_lt_toNat
    (b : ℤ → ℂ) (v : ℕ) {n : ℤ} (hn : v < n.toNat) :
    vaughanSmallCoeff b v n = 0 := by
  simp [vaughanSmallCoeff, vaughanSmall, not_le.mpr hn]

theorem vaughanSmallCoeff_eq_of_toNat_le
    (b : ℤ → ℂ) (v : ℕ) {n : ℤ} (hn : n.toNat ≤ v) :
    vaughanSmallCoeff b v n =
      b n * (ArithmeticFunction.vonMangoldt n.toNat : ℂ) := by
  simp [vaughanSmallCoeff, vaughanSmall, hn]

theorem card_vaughanSmallSupport_le (N v : ℕ) :
    (vaughanSmallSupport N v).card ≤ v := by
  have hsub : vaughanSmallSupport N v ⊆ Finset.Icc (1 : ℤ) (v : ℤ) := by
    intro n hn
    rw [mem_vaughanSmallSupport] at hn
    rw [Finset.mem_Icc]
    refine ⟨hn.1, ?_⟩
    have hn0 : 0 ≤ n := by omega
    rw [← Int.toNat_of_nonneg hn0]
    exact_mod_cast hn.2.2
  calc
    (vaughanSmallSupport N v).card ≤ (Finset.Icc (1 : ℤ) (v : ℤ)).card :=
      Finset.card_le_card hsub
    _ = v := by simp

theorem vaughanSmallCoeff_energy_eq_support (b : ℤ → ℂ) (N v : ℕ) :
    (∑ n ∈ Finset.Icc (1 : ℤ) N, ‖vaughanSmallCoeff b v n‖ ^ 2) =
      ∑ n ∈ vaughanSmallSupport N v,
        ‖b n‖ ^ 2 * ArithmeticFunction.vonMangoldt n.toNat ^ 2 := by
  calc
    (∑ n ∈ Finset.Icc (1 : ℤ) N, ‖vaughanSmallCoeff b v n‖ ^ 2) =
        ∑ n ∈ Finset.Icc (1 : ℤ) N,
          if n.toNat ≤ v then
            ‖b n‖ ^ 2 * ArithmeticFunction.vonMangoldt n.toNat ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hnv : n.toNat ≤ v
      · rw [if_pos hnv, vaughanSmallCoeff_eq_of_toNat_le b v hnv,
          norm_mul, mul_pow]
        simp only [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      · rw [if_neg hnv, vaughanSmallCoeff_eq_zero_of_v_lt_toNat b v
          (Nat.lt_of_not_ge hnv)]
        simp
    _ = _ := by
      rw [← Finset.sum_filter]
      rfl

theorem vonMangoldt_le_log_v_succ {n : ℤ} {v : ℕ}
    (hn : 1 ≤ n) (hnv : n.toNat ≤ v) :
    ArithmeticFunction.vonMangoldt n.toNat ≤ Real.log ((v + 1 : ℕ) : ℝ) := by
  have hn0 : 0 ≤ n := by omega
  have hnpos : (0 : ℝ) < n.toNat := by
    have : 0 < n.toNat := by omega
    exact_mod_cast this
  have hnv' : (n.toNat : ℝ) ≤ ((v + 1 : ℕ) : ℝ) := by
    exact_mod_cast (hnv.trans (Nat.le_succ v))
  exact ArithmeticFunction.vonMangoldt_le_log.trans
    (Real.strictMonoOn_log.monotoneOn (by simpa using hnpos)
      (by simp only [Set.mem_Ioi]; positivity) hnv')

/-- `∑_{1 ≤ n ≤ N} |b(n) Small(n; v)|² ≤ log(v+1)² ∑_{1 ≤ n ≤ min(N, v)} |b(n)|²`. -/
theorem vaughanSmallCoeff_energy_le_log_support (b : ℤ → ℂ) (N v : ℕ) :
    (∑ n ∈ Finset.Icc (1 : ℤ) N, ‖vaughanSmallCoeff b v n‖ ^ 2) ≤
      Real.log ((v + 1 : ℕ) : ℝ) ^ 2 *
        ∑ n ∈ vaughanSmallSupport N v, ‖b n‖ ^ 2 := by
  rw [vaughanSmallCoeff_energy_eq_support, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [mem_vaughanSmallSupport] at hn
  have hΛ := vonMangoldt_le_log_v_succ hn.1 hn.2.2
  have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n.toNat)
  have hlog0 : 0 ≤ Real.log ((v + 1 : ℕ) : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le v))
  have hsq : ArithmeticFunction.vonMangoldt n.toNat ^ 2 ≤
      Real.log ((v + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  nlinarith [sq_nonneg ‖b n‖]

/-- If `|b(n)| ≤ B` for `1 ≤ n ≤ min(N, v)`, then
`∑_{1 ≤ n ≤ N} |b(n) Small(n; v)|² ≤ v B² log(v+1)²`. -/
theorem vaughanSmallCoeff_energy_le_v_mul_log_sq
    (b : ℤ → ℂ) (N v : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ n ∈ vaughanSmallSupport N v, ‖b n‖ ≤ B) :
    (∑ n ∈ Finset.Icc (1 : ℤ) N, ‖vaughanSmallCoeff b v n‖ ^ 2) ≤
      (v : ℝ) * B ^ 2 * Real.log ((v + 1 : ℕ) : ℝ) ^ 2 := by
  have hsupport : (∑ n ∈ vaughanSmallSupport N v, ‖b n‖ ^ 2) ≤
      (v : ℝ) * B ^ 2 := by
    calc
      (∑ n ∈ vaughanSmallSupport N v, ‖b n‖ ^ 2) ≤
          ∑ _n ∈ vaughanSmallSupport N v, B ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        exact (sq_le_sq₀ (norm_nonneg _) hB).2 (hb n hn)
      _ = ((vaughanSmallSupport N v).card : ℝ) * B ^ 2 := by simp
      _ ≤ (v : ℝ) * B ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast card_vaughanSmallSupport_le N v) (sq_nonneg B)
  calc
    (∑ n ∈ Finset.Icc (1 : ℤ) N, ‖vaughanSmallCoeff b v n‖ ^ 2) ≤
        Real.log ((v + 1 : ℕ) : ℝ) ^ 2 *
          ∑ n ∈ vaughanSmallSupport N v, ‖b n‖ ^ 2 :=
      vaughanSmallCoeff_energy_le_log_support b N v
    _ ≤ Real.log ((v + 1 : ℕ) : ℝ) ^ 2 * ((v : ℝ) * B ^ 2) :=
      mul_le_mul_of_nonneg_left hsupport (sq_nonneg _)
    _ = (v : ℝ) * B ^ 2 * Real.log ((v + 1 : ℕ) : ℝ) ^ 2 :=
      mul_comm _ _

/-! ## Principal characters and conductors -/

/-- The nonprincipal Dirichlet characters modulo `q`. -/
noncomputable def nonprincipalCharacters (q : ℕ) :
    Finset (DirichletCharacter ℂ q) :=
  Finset.univ.erase 1

@[simp]
theorem mem_nonprincipalCharacters {q : ℕ} {χ : DirichletCharacter ℂ q} :
    χ ∈ nonprincipalCharacters q ↔ χ ≠ 1 := by
  simp [nonprincipalCharacters]

theorem sum_allCharacters_eq_principal_add_nonprincipal
    {q : ℕ} {A : Type*} [AddCommMonoid A]
    (F : DirichletCharacter ℂ q → A) :
    (∑ χ : DirichletCharacter ℂ q, F χ) =
      F 1 + ∑ χ ∈ nonprincipalCharacters q, F χ := by
  exact (Finset.add_sum_erase Finset.univ F
    (Finset.mem_univ (1 : DirichletCharacter ℂ q))).symm

theorem mem_nonprincipalCharacters_iff_conductor_ne_one
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} :
    χ ∈ nonprincipalCharacters q ↔ χ.conductor ≠ 1 := by
  rw [mem_nonprincipalCharacters]
  exact not_congr DirichletCharacter.eq_one_iff_conductor_eq_one

/-- `b(n) χ(n) - b(n) χ*(n)`, where `χ*` is the primitive character modulo the
conductor of `χ` that induces `χ`. -/
def conductorChangeLevelError {q : ℕ} (χ : DirichletCharacter ℂ q)
    (b : ℤ → ℂ) (n : ℤ) : ℂ :=
  b n * χ (n : ZMod q) -
    b n * χ.primitiveCharacter (n : ZMod χ.conductor)

theorem conductorChangeLevelError_eq_zero_of_isCoprime
    {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℤ → ℂ) {n : ℤ}
    (hn : IsCoprime n q) :
    conductorChangeLevelError χ b n = 0 := by
  unfold conductorChangeLevelError
  rw [χ.primitiveCharacter_apply_of_isCoprime hn]
  ring

theorem characterTerm_eq_conductorPrimitive_add_error
    {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℤ → ℂ) (n : ℤ) :
    b n * χ (n : ZMod q) =
      b n * χ.primitiveCharacter (n : ZMod χ.conductor) +
        conductorChangeLevelError χ b n := by
  unfold conductorChangeLevelError
  ring

/-- Over an interval, the sum of `b(n) χ(n)` is the sum of `b(n) χ*(n)` plus a
correction supported on the `n` not coprime to `q`. -/
theorem characterInterval_eq_conductorPrimitive_add_error
    {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Icc (M + 1) (M + N), b n * χ (n : ZMod q)) =
      (∑ n ∈ Finset.Icc (M + 1) (M + N),
        b n * χ.primitiveCharacter (n : ZMod χ.conductor)) +
      ∑ n ∈ Finset.Icc (M + 1) (M + N),
        conductorChangeLevelError χ b n := by
  calc
    _ = ∑ n ∈ Finset.Icc (M + 1) (M + N),
          (b n * χ.primitiveCharacter (n : ZMod χ.conductor) +
            conductorChangeLevelError χ b n) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact characterTerm_eq_conductorPrimitive_add_error χ b n
    _ = _ := by rw [Finset.sum_add_distrib]

/-! ## Multiples and the Vaughan weights -/

/-- The substitution `n = k m` in a sum over the multiples of `k` in `[1, y]`. -/
theorem sum_multiples_Icc_reindex {R : Type*} [AddCommMonoid R]
    (F : ℕ → R) {k y : ℕ} (hk : 0 < k) :
    (∑ n ∈ (Finset.Icc 1 y).filter (fun n => k ∣ n), F n) =
      ∑ m ∈ Finset.Icc 1 (y / k), F (k * m) := by
  refine Finset.sum_bij (fun n _ => n / k) ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter] at hn
    have hnI := Finset.mem_Icc.mp hn.1
    rw [Finset.mem_Icc]
    constructor
    · exact Nat.div_pos (Nat.le_of_dvd hnI.1 hn.2) hk
    · exact Nat.div_le_div_right hnI.2
  · intro n₁ hn₁ n₂ hn₂ h
    rw [Finset.mem_filter] at hn₁ hn₂
    calc
      n₁ = k * (n₁ / k) := (Nat.mul_div_cancel' hn₁.2).symm
      _ = k * (n₂ / k) := by rw [h]
      _ = n₂ := Nat.mul_div_cancel' hn₂.2
  · intro m hm
    rw [Finset.mem_Icc] at hm
    refine ⟨k * m, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · constructor
        · exact Nat.mul_pos hk hm.1
        · simpa [mul_comm] using (Nat.le_div_iff_mul_le hk).mp hm.2
      · exact dvd_mul_right k m
    · exact Nat.mul_div_cancel_left m hk
  · intro n hn
    rw [Finset.mem_filter] at hn
    rw [Nat.mul_div_cancel' hn.2]

/-- The weight `μ(d)` on the variable `d` in Vaughan's identity. -/
def vaughanMoebiusCoeff (d : ℕ) : ℂ := ((ArithmeticFunction.moebius d : ℤ) : ℂ)

/-- The weight `Λ(e)` on the variable `e` in Vaughan's identity. -/
def vaughanMangoldtCoeff (e : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt e : ℂ)

/-!
## Type I sums in the long variable

Substituting `n = d m` and `n = d e m` turns each Type I prefix sum into a sum over
the short variables `d ≤ u` and `e ≤ v` of character sums over the long variable `m`.
-/

/-- The range `1 ≤ d ≤ min(y, u)` of a short variable in a prefix of length `y`. -/
def vaughanTypeIShortRange (y u : ℕ) : Finset ℕ := Finset.Icc 1 (min y u)

@[simp] theorem mem_vaughanTypeIShortRange {y u d : ℕ} :
    d ∈ vaughanTypeIShortRange y u ↔ 0 < d ∧ d ≤ y ∧ d ≤ u := by
  simp [vaughanTypeIShortRange, Nat.succ_le_iff]

/-- `∑_{d ∣ n, d ≤ u} μ(d) log(n/d)`, as a complex number. -/
def vaughanTypeIFirstAt (n u : ℕ) : ℂ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ u),
    (((ArithmeticFunction.moebius d : ℤ) : ℂ) * Real.log ((n / d : ℕ) : ℝ))

/-- `∑_{d ∣ n, d ≤ u} ∑_{e ∣ n/d, e ≤ v} μ(d) Λ(e)`, as a complex number. -/
def vaughanTypeIMiddleAt (n u v : ℕ) : ℂ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ u),
    ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v),
      (((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (ArithmeticFunction.vonMangoldt e : ℂ))

@[simp] theorem vaughanTypeIFirstAt_eq_cast (n u : ℕ) :
    vaughanTypeIFirstAt n u = (vaughanFirst n u : ℂ) := by
  unfold vaughanTypeIFirstAt vaughanFirst
  push_cast
  rfl

@[simp] theorem vaughanTypeIMiddleAt_eq_cast (n u v : ℕ) :
    vaughanTypeIMiddleAt n u v = (vaughanMiddle n u v : ℂ) := by
  unfold vaughanTypeIMiddleAt vaughanMiddle
  push_cast
  rfl

private lemma divisors_filter_eq_shortRange
    {n y u : ℕ} (hn : 0 < n) (hny : n ≤ y) :
    n.divisors.filter (fun d => d ≤ u) =
      (vaughanTypeIShortRange y u).filter (fun d => d ∣ n) := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdn, _⟩, hdu⟩
    have hdpos := Nat.pos_of_dvd_of_pos hdn hn
    exact ⟨mem_vaughanTypeIShortRange.mpr
      ⟨hdpos, (Nat.le_of_dvd hn hdn).trans hny, hdu⟩, hdn⟩
  · rintro ⟨hd, hdn⟩
    exact ⟨⟨hdn, hn.ne'⟩, (mem_vaughanTypeIShortRange.mp hd).2.2⟩

theorem vaughanTypeIFirstAt_eq_bounded {n y u : ℕ} (hn : 0 < n) (hny : n ≤ y) :
    vaughanTypeIFirstAt n u =
      ∑ d ∈ vaughanTypeIShortRange y u,
        if d ∣ n then
          (((ArithmeticFunction.moebius d : ℤ) : ℂ) * Real.log ((n / d : ℕ) : ℝ))
        else 0 := by
  unfold vaughanTypeIFirstAt
  rw [divisors_filter_eq_shortRange hn hny, Finset.sum_filter]

/-- For `0 < n ≤ y` the middle factor is a sum over a fixed range of `(d, e)`,
with the condition `e ∣ n/d` replaced by `d e ∣ n`. -/
theorem vaughanTypeIMiddleAt_eq_bounded {n y u v : ℕ} (hn : 0 < n) (hny : n ≤ y) :
    vaughanTypeIMiddleAt n u v =
      ∑ d ∈ vaughanTypeIShortRange y u,
        ∑ e ∈ vaughanTypeIShortRange y v,
          if d * e ∣ n then
            (((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              (ArithmeticFunction.vonMangoldt e : ℂ))
          else 0 := by
  unfold vaughanTypeIMiddleAt
  rw [divisors_filter_eq_shortRange hn hny, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdn : d ∣ n
  · simp only [if_pos hdn]
    have hdpos : 0 < d := (mem_vaughanTypeIShortRange.mp hd).1
    have hndpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hdpos
    have heset : (n / d).divisors.filter (fun e => e ≤ v) =
        (vaughanTypeIShortRange y v).filter (fun e => d * e ∣ n) := by
      rw [divisors_filter_eq_shortRange hndpos ((Nat.div_le_self n d).trans hny)]
      simp_rw [Nat.dvd_div_iff_mul_dvd hdn]
    rw [heset, Finset.sum_filter]
  · have hde : ∀ e : ℕ, ¬ d * e ∣ n := by
      intro e h
      exact hdn ((dvd_mul_right d e).trans h)
    simp [hdn, hde]

/-- `∑_{n ≤ y} b(n) χ(n) ∑_{d ∣ n, d ≤ u} μ(d) log(n/d)`. -/
def vaughanTypeIFirstPrefix
    (b : ℕ → ℂ) (y u q : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y,
    b n * χ.1 (n : ZMod q) * vaughanTypeIFirstAt n u

/-- `∑_{d ≤ min(y, u)} μ(d) χ(d) ∑_{m ≤ y/d} b(d m) log(m) χ(m)`. -/
def vaughanTypeIFirstLong
    (b : ℕ → ℂ) (y u q : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  ∑ d ∈ vaughanTypeIShortRange y u,
    ((((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ.1 (d : ZMod q)) *
      ∑ m ∈ Finset.Icc 1 (y / d),
        (b (d * m) * Real.log (m : ℝ)) * χ.1 (m : ZMod q))

/-- The substitution `n = d m` in the first Type I prefix sum. -/
theorem vaughanTypeIFirstPrefix_eq_long
    (b : ℕ → ℂ) (y u q : ℕ) (χ : PrimitiveCharacter q) :
    vaughanTypeIFirstPrefix b y u q χ = vaughanTypeIFirstLong b y u q χ := by
  unfold vaughanTypeIFirstPrefix vaughanTypeIFirstLong
  calc
    (∑ n ∈ Finset.Icc 1 y, b n * χ.1 (n : ZMod q) * vaughanTypeIFirstAt n u) =
        ∑ n ∈ Finset.Icc 1 y, b n * χ.1 (n : ZMod q) *
          ∑ d ∈ vaughanTypeIShortRange y u,
            if d ∣ n then (((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              Real.log ((n / d : ℕ) : ℝ)) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [vaughanTypeIFirstAt_eq_bounded (Finset.mem_Icc.mp hn).1
        (Finset.mem_Icc.mp hn).2]
    _ = ∑ d ∈ vaughanTypeIShortRange y u,
        ∑ n ∈ Finset.Icc 1 y,
          if d ∣ n then b n * χ.1 (n : ZMod q) *
            (((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              Real.log ((n / d : ℕ) : ℝ)) else 0 := by
      simp_rw [Finset.mul_sum, mul_ite, mul_zero]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos := (mem_vaughanTypeIShortRange.mp hd).1
      rw [← Finset.sum_filter]
      rw [sum_multiples_Icc_reindex
        (fun n => b n * χ.1 (n : ZMod q) *
          (((ArithmeticFunction.moebius d : ℤ) : ℂ) *
            Real.log ((n / d : ℕ) : ℝ))) hdpos]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Nat.mul_div_cancel_left m hdpos]
      rw [show ((d * m : ℕ) : ZMod q) = (d : ZMod q) * (m : ZMod q) by
        simp only [Nat.cast_mul], map_mul]
      ring

/-- `∑_{n ≤ y} b(n) χ(n) ∑_{d ∣ n, d ≤ u} ∑_{e ∣ n/d, e ≤ v} μ(d) Λ(e)`. -/
def vaughanTypeIMiddlePrefix
    (b : ℕ → ℂ) (y u v q : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y,
    b n * χ.1 (n : ZMod q) * vaughanTypeIMiddleAt n u v

/-- `∑_{d ≤ min(y, u)} ∑_{e ≤ min(y, v)} μ(d) Λ(e) χ(d) χ(e) ∑_{m ≤ y/(d e)} b(d e m) χ(m)`,
the middle prefix sum after substituting `n = d e m`. -/
def vaughanTypeIMiddleLong
    (b : ℕ → ℂ) (y u v q : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  ∑ d ∈ vaughanTypeIShortRange y u,
    ∑ e ∈ vaughanTypeIShortRange y v,
      (((((ArithmeticFunction.moebius d : ℤ) : ℂ) *
          (ArithmeticFunction.vonMangoldt e : ℂ)) *
          χ.1 (d : ZMod q) * χ.1 (e : ZMod q)) *
        ∑ m ∈ Finset.Icc 1 (y / (d * e)),
          b (d * e * m) * χ.1 (m : ZMod q))

/-- The substitution `n = d e m` in the middle Type I prefix sum. -/
theorem vaughanTypeIMiddlePrefix_eq_long
    (b : ℕ → ℂ) (y u v q : ℕ) (χ : PrimitiveCharacter q) :
    vaughanTypeIMiddlePrefix b y u v q χ =
      vaughanTypeIMiddleLong b y u v q χ := by
  unfold vaughanTypeIMiddlePrefix vaughanTypeIMiddleLong
  calc
    (∑ n ∈ Finset.Icc 1 y, b n * χ.1 (n : ZMod q) * vaughanTypeIMiddleAt n u v) =
        ∑ n ∈ Finset.Icc 1 y, b n * χ.1 (n : ZMod q) *
          ∑ d ∈ vaughanTypeIShortRange y u,
            ∑ e ∈ vaughanTypeIShortRange y v,
              if d * e ∣ n then (((ArithmeticFunction.moebius d : ℤ) : ℂ) *
                (ArithmeticFunction.vonMangoldt e : ℂ)) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [vaughanTypeIMiddleAt_eq_bounded (Finset.mem_Icc.mp hn).1
        (Finset.mem_Icc.mp hn).2]
    _ = ∑ d ∈ vaughanTypeIShortRange y u,
        ∑ e ∈ vaughanTypeIShortRange y v,
          ∑ n ∈ Finset.Icc 1 y,
            if d * e ∣ n then b n * χ.1 (n : ZMod q) *
              ((((ArithmeticFunction.moebius d : ℤ) : ℂ) *
                (ArithmeticFunction.vonMangoldt e : ℂ))) else 0 := by
      simp_rw [Finset.mul_sum, mul_ite, mul_zero]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      have hdpos := (mem_vaughanTypeIShortRange.mp hd).1
      have hepos := (mem_vaughanTypeIShortRange.mp he).1
      have hde : 0 < d * e := Nat.mul_pos hdpos hepos
      rw [← Finset.sum_filter]
      rw [sum_multiples_Icc_reindex
        (fun n => b n * χ.1 (n : ZMod q) *
          ((((ArithmeticFunction.moebius d : ℤ) : ℂ) *
            (ArithmeticFunction.vonMangoldt e : ℂ)))) hde]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [show ((d * e * m : ℕ) : ZMod q) =
        (d : ZMod q) * (e : ZMod q) * (m : ZMod q) by
          simp only [Nat.cast_mul], map_mul, map_mul]
      ring

/-- The Type I prefix sum in the long variable: the first sum minus the middle one. -/
def vaughanTypeILongPrefix
    (b : ℕ → ℂ) (y u v q : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  vaughanTypeIFirstLong b y u q χ - vaughanTypeIMiddleLong b y u v q χ

/-- `∑_{n ≤ y} b(n) χ(n) TypeI(n; u, v)` equals its long-variable form. -/
theorem vaughanTypeIPrefix_eq_long
    (b : ℕ → ℂ) (y u v q : ℕ) (χ : PrimitiveCharacter q) :
    (∑ n ∈ Finset.Icc 1 y,
      b n * χ.1 (n : ZMod q) * (vaughanTypeI n u v : ℂ)) =
      vaughanTypeILongPrefix b y u v q χ := by
  simp only [vaughanTypeI]
  push_cast
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  unfold vaughanTypeILongPrefix
  exact congrArg₂ (· - ·)
    (by simpa [vaughanTypeIFirstPrefix] using
      vaughanTypeIFirstPrefix_eq_long b y u q χ)
    (by simpa [vaughanTypeIMiddlePrefix] using
      vaughanTypeIMiddlePrefix_eq_long b y u v q χ)

/-- The sequence `b(n) TypeI(n; u, v)` on the integers. -/
def vaughanTypeILongCoeff (b : ℤ → ℂ) (u v : ℕ) (n : ℤ) : ℂ :=
  b n * (vaughanTypeI n.toNat u v : ℂ)

/-- Each squared prefix sum of `b(n) TypeI(n; u, v) χ(n)` equals the square of
its long-variable form. -/
theorem primitiveCharacterPrefixSquare_typeI_eq_long
    (b : ℤ → ℂ) (y u v q : ℕ) (χ : PrimitiveCharacter q) :
    primitiveCharacterPrefixSquare (vaughanTypeILongCoeff b u v) 0 y q χ =
      ‖vaughanTypeILongPrefix (fun n => b n) y u v q χ‖ ^ 2 := by
  unfold primitiveCharacterPrefixSquare
  simp only [zero_add]
  have hsum := sum_Ioc_nat_eq_sum_Icc_int 0 0 y
    (fun z => vaughanTypeILongCoeff b u v z * χ.1 (z : ZMod q))
  have hsum' :
      (∑ n ∈ Finset.Ioc 0 y,
        vaughanTypeILongCoeff b u v (n : ℤ) * χ.1 (n : ZMod q)) =
      ∑ z ∈ Finset.Icc (1 : ℤ) y,
        vaughanTypeILongCoeff b u v z * χ.1 (z : ZMod q) := by
    simpa using hsum
  rw [← hsum']
  have hset : Finset.Ioc 0 y = Finset.Icc 1 y := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hset]
  rw [← vaughanTypeIPrefix_eq_long (fun n => b n) y u v q χ]
  congr 2
  apply Finset.sum_congr rfl
  intro n hn
  simp only [vaughanTypeILongCoeff, Int.toNat_natCast]
  ring

end

end BombieriVinogradov
