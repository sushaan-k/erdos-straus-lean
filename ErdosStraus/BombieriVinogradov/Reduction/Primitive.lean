import ErdosStraus.BombieriVinogradov.Vaughan.Decomposition

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

namespace BombieriVinogradov

open Classical Finset
open scoped BigOperators
noncomputable section

/-!
# Reduction to primitive characters

A character `χ` modulo `q` is induced by a primitive character `χ*` modulo its
conductor `d ∣ q`, and `χ(n) = χ*(n)` whenever `(n, q) = 1`. The maximal prefix
sums of `b(n) χ(n)` are bounded by those of `b(n) χ*(n)` plus a correction
supported on `(n, q) ≠ 1`, whose prefix sums for `b = Λ` on `[1, N]` are
`O(log q · log² N)`. Sums over nonprincipal characters regroup by conductor
`d ≥ 2`, and the conductor multiplicity satisfies
`∑_{q ≤ Q, d ∣ q} 1/φ(q) ≤ H_Q² / φ(d)` with `H_Q = ∑_{e ≤ Q} 1/e ≤ 1 + log Q`.
-/

/-- For the primitive character `χ*` inducing `χ`, the correction
`b(n) χ(n) - b(n) χ*(n)` has squared norm at most `4 ‖b(n)‖²`. -/
theorem conductorChangeLevelError_norm_sq_le
    {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℤ → ℂ) (n : ℤ) :
    ‖conductorChangeLevelError χ b n‖ ^ 2 ≤ 4 * ‖b n‖ ^ 2 := by
  have hq := χ.norm_le_one (n : ZMod q)
  have hc := χ.primitiveCharacter.norm_le_one (n : ZMod χ.conductor)
  have h₁ : ‖b n * χ (n : ZMod q)‖ ≤ ‖b n‖ := by
    rw [norm_mul]
    nlinarith [norm_nonneg (b n)]
  have h₂ : ‖b n * χ.primitiveCharacter (n : ZMod χ.conductor)‖ ≤ ‖b n‖ := by
    rw [norm_mul]
    nlinarith [norm_nonneg (b n)]
  have he : ‖conductorChangeLevelError χ b n‖ ≤ 2 * ‖b n‖ := by
    unfold conductorChangeLevelError
    exact (norm_sub_le _ _).trans (by linarith)
  nlinarith [norm_nonneg (conductorChangeLevelError χ b n), norm_nonneg (b n)]

/-- `‖∑_{M < n ≤ M + y} (b(n) χ(n) - b(n) χ*(n))‖²`, where `χ*` is the primitive
character inducing `χ`. -/
def conductorErrorPrefixSquare {q : ℕ} (χ : DirichletCharacter ℂ q)
    (b : ℤ → ℂ) (M : ℤ) (y : ℕ) : ℝ :=
  ‖∑ n ∈ Finset.Icc (M + 1) (M + y), conductorChangeLevelError χ b n‖ ^ 2

/-- The maximum of `conductorErrorPrefixSquare` over `0 ≤ y ≤ N`. -/
def conductorErrorPrefixMaxSquare {q : ℕ} (χ : DirichletCharacter ℂ q)
    (b : ℤ → ℂ) (M : ℤ) (N : ℕ) : ℝ :=
  ((Finset.range (N + 1)).image (fun y => conductorErrorPrefixSquare χ b M y)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- `‖∑_{M < n ≤ M + y} b(n) χ(n)‖²` for any character `χ` modulo `q`, primitive or not. -/
def characterPrefixSquare {q : ℕ} (χ : DirichletCharacter ℂ q)
    (b : ℤ → ℂ) (M : ℤ) (y : ℕ) : ℝ :=
  ‖∑ n ∈ Finset.Icc (M + 1) (M + y), b n * χ (n : ZMod q)‖ ^ 2

/-- The maximum of `characterPrefixSquare` over `0 ≤ y ≤ N`. -/
def characterPrefixMaxSquare {q : ℕ} (χ : DirichletCharacter ℂ q)
    (b : ℤ → ℂ) (M : ℤ) (N : ℕ) : ℝ :=
  ((Finset.range (N + 1)).image (fun y => characterPrefixSquare χ b M y)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

private theorem norm_add_sq_le_two (x y : ℂ) :
    ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have h := norm_add_le x y
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg (x + y),
    norm_nonneg x, norm_nonneg y]

/-- The maximal prefix sum for `χ` is at most twice the maximal prefix sum for the
primitive character `χ*` inducing `χ` plus twice the maximal correction. -/
theorem characterPrefixMaxSquare_le_conductor_add_error
    {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    characterPrefixMaxSquare χ b M N ≤
      2 * (primitiveCharacterPrefixMaxSquare b M N χ.conductor
          (conductorPrimitiveCharacter χ) +
        conductorErrorPrefixMaxSquare χ b M N) := by
  unfold characterPrefixMaxSquare
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  have hyN : y ≤ N := by simpa [Finset.mem_range] using hy
  rw [characterPrefixSquare, characterInterval_eq_conductorPrimitive_add_error]
  refine (norm_add_sq_le_two _ _).trans ?_
  gcongr
  · exact primitiveCharacterPrefixSquare_le_max b M hyN
      (conductorPrimitiveCharacter χ)
  · unfold conductorErrorPrefixMaxSquare
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩

/-- The divisors `d ≥ 2` of `q`, the possible conductors of nonprincipal characters
modulo `q`. -/
def nonprincipalConductors (q : ℕ) : Finset ℕ :=
  q.divisors.filter (fun d => 2 ≤ d)

/-- For `q > 0`, the map `χ ↦ χ*` is a bijection from the nonprincipal characters
modulo `q` onto the primitive characters modulo the divisors `d ≥ 2` of `q`, so a
sum over nonprincipal characters regroups by conductor. -/
theorem sum_nonprincipal_by_conductor
    {q : ℕ} (hq : 0 < q)
    (F : (d : ℕ) → PrimitiveCharacter d → ℝ) :
    (∑ χ ∈ nonprincipalCharacters q,
        F χ.conductor (conductorPrimitiveCharacter χ)) =
      ∑ d ∈ nonprincipalConductors q, ∑ ψ : PrimitiveCharacter d, F d ψ := by
  let : NeZero q := ⟨hq.ne'⟩
  rw [Finset.sum_sigma' (s := nonprincipalConductors q)
    (t := fun d => Finset.univ) (f := F)]
  let T := (nonprincipalConductors q).sigma
    (fun d => (Finset.univ : Finset (PrimitiveCharacter d)))
  let lift : (p : Σ d, PrimitiveCharacter d) → p ∈ T →
      DirichletCharacter ℂ q := fun p hp =>
    DirichletCharacter.changeLevel
      ((Finset.mem_filter.mp (Finset.mem_sigma.mp hp).1).1 |>
        Nat.mem_divisors.mp |>.1) p.2.1
  have lift_injective : ∀ (p p' : Σ d, PrimitiveCharacter d)
      (hp : p ∈ T) (hp' : p' ∈ T), lift p hp = lift p' hp' → p = p' := by
    intro p p' hp hp' h
    rcases p with ⟨d, ψ⟩
    rcases p' with ⟨d', ψ'⟩
    have hdq : d ∣ q :=
      (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).1).1 |>
        Nat.mem_divisors.mp |>.1
    have hdq' : d' ∣ q :=
      (Finset.mem_filter.mp (Finset.mem_sigma.mp hp').1).1 |>
        Nat.mem_divisors.mp |>.1
    have hd : d = d' := by
      calc
        d = (lift ⟨d, ψ⟩ hp).conductor := by
          simp only [lift, DirichletCharacter.conductor_changeLevel,
            primitive_conductor]
        _ = (lift ⟨d', ψ'⟩ hp').conductor := congrArg (·.conductor) h
        _ = d' := by
          simp only [lift, DirichletCharacter.conductor_changeLevel,
            primitive_conductor]
    subst d'
    have hψ : ψ = ψ' := by
      apply Subtype.ext
      apply DirichletCharacter.changeLevel_injective hdq
      exact h
    exact congrArg (Sigma.mk d) hψ
  have encode_mem : ∀ χ ∈ nonprincipalCharacters q,
      (⟨χ.conductor, conductorPrimitiveCharacter χ⟩ : Σ d, PrimitiveCharacter d) ∈ T := by
    intro χ hχ
    rw [Finset.mem_sigma]
    refine ⟨?_, Finset.mem_univ _⟩
    change χ.conductor ∈ nonprincipalConductors q
    rw [nonprincipalConductors, Finset.mem_filter]
    refine ⟨Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, hq.ne'⟩, ?_⟩
    have hc1 : χ.conductor ≠ 1 :=
      mem_nonprincipalCharacters_iff_conductor_ne_one.mp hχ
    have hcpos : 0 < χ.conductor := Nat.pos_of_dvd_of_pos χ.conductor_dvd_level hq
    omega
  have lift_mem : ∀ p (hp : p ∈ T), lift p hp ∈ nonprincipalCharacters q := by
    intro p hp
    rw [mem_nonprincipalCharacters_iff_conductor_ne_one]
    have hdmem : p.1 ∈ nonprincipalConductors q := (Finset.mem_sigma.mp hp).1
    have hd2 : 2 ≤ p.1 := (Finset.mem_filter.mp hdmem).2
    simp only [lift, DirichletCharacter.conductor_changeLevel, primitive_conductor]
    omega
  refine Finset.sum_bij'
    (fun χ hχ => ⟨χ.conductor, conductorPrimitiveCharacter χ⟩)
    lift encode_mem lift_mem ?_ ?_ ?_
  · intro χ hχ
    exact changeLevel_conductorPrimitiveCharacter χ
  · intro p hp
    apply lift_injective _ _ (encode_mem _ (lift_mem p hp)) hp
    exact changeLevel_conductorPrimitiveCharacter (lift p hp)
  · intro χ hχ
    rfl

theorem not_isCoprime_iff_exists_primeFactor_dvd
    {q : ℕ} (hq : 0 < q) (n : ℤ) :
    ¬ IsCoprime n q ↔ ∃ p ∈ q.primeFactors, (p : ℤ) ∣ n := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  constructor
  · intro hg
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
    refine ⟨p, Nat.mem_primeFactors.mpr ⟨hp, ?_, hq.ne'⟩, ?_⟩
    · have hpqz : (p : ℤ) ∣ (q : ℤ) := (Int.dvd_gcd_iff.mp hpg).2
      simpa using (Int.natCast_dvd.mp hpqz)
    · exact (Int.dvd_gcd_iff.mp hpg).1
  · rintro ⟨p, hpq, hpn⟩ hg
    have hp := (Nat.mem_primeFactors.mp hpq).1
    have hpq' : (p : ℤ) ∣ (q : ℤ) := by
      exact_mod_cast (Nat.mem_primeFactors.mp hpq).2.1
    have hpg : p ∣ n.gcd q := Int.dvd_gcd hpn hpq'
    rw [hg] at hpg
    exact hp.not_dvd_one hpg

end

end BombieriVinogradov

/-!
## The correction for the von Mangoldt function

For `b = Λ` on `[1, N]`, the correction vanishes except at the prime powers `p^k ≤ N`
with `p ∣ q`. There are at most `log₂ q · (log₂ N + 1)` of these, so every correction
prefix sum over `[1, y]`, `y ≤ N`, is `O(log q · log² N)`.
-/

namespace BombieriVinogradov

open Classical Finset
open scoped BigOperators ArithmeticFunction
noncomputable section

/-- `Λ(n)` for `n ≥ 1`, and `0` for `n ≤ 0`. -/
def vonMangoldtIntegerCoeff (n : ℤ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n.toNat : ℂ)

/-- The integers `n ∈ [1, N]` with `Λ(n) ≠ 0` and `(n, q) ≠ 1`. -/
def vonMangoldtBadSupport (q N : ℕ) : Finset ℤ :=
  (Finset.Icc (1 : ℤ) N).filter fun n =>
    ArithmeticFunction.vonMangoldt n.toNat ≠ 0 ∧ ¬ IsCoprime n q

@[simp] theorem mem_vonMangoldtBadSupport {q N : ℕ} {n : ℤ} :
    n ∈ vonMangoldtBadSupport q N ↔
      1 ≤ n ∧ n ≤ N ∧ ArithmeticFunction.vonMangoldt n.toNat ≠ 0 ∧
        ¬ IsCoprime n q := by
  simp [vonMangoldtBadSupport, and_assoc]

/-- The prime powers `p^(k+1)` with `p ∣ q` prime and `k ≤ log₂ N`. -/
def vonMangoldtBadPrimePowers (q N : ℕ) : Finset ℤ :=
  q.primeFactors.biUnion fun p =>
    (Finset.range (Nat.log2 N + 1)).image fun k => ((p ^ (k + 1) : ℕ) : ℤ)

/-- If `n ∈ [1, N]`, `Λ(n) ≠ 0` and `(n, q) ≠ 1`, then `n` is a power of a prime
divisor of `q`. -/
theorem vonMangoldtBadSupport_subset_primePowers
    {q : ℕ} (hq : 0 < q) (N : ℕ) :
    vonMangoldtBadSupport q N ⊆ vonMangoldtBadPrimePowers q N := by
  intro n hn
  rw [mem_vonMangoldtBadSupport] at hn
  have hn0 : 0 ≤ n := by omega
  have hnN : n.toNat ≤ N := by omega
  have hpp : IsPrimePow n.toNat :=
    ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hn.2.2.1
  obtain ⟨p, k, hp, hk, hpow⟩ := (isPrimePow_nat_iff _).mp hpp
  obtain ⟨r, hrq, hrn⟩ :=
    (not_isCoprime_iff_exists_primeFactor_dvd hq n).mp hn.2.2.2
  have hr : r.Prime := (Nat.mem_primeFactors.mp hrq).1
  have hrn' : r ∣ n.toNat := by
    rw [← Int.toNat_of_nonneg hn0] at hrn
    exact_mod_cast hrn
  have hrp : r ∣ p := by
    rw [← hpow] at hrn'
    exact hr.dvd_of_dvd_pow hrn'
  have hr_eq : r = p := (Nat.dvd_prime hp).mp hrp |>.resolve_left hr.ne_one
  have htwo : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
  have hkle : k ≤ Nat.log2 N := by
    rw [Nat.log2_eq_log_two]
    apply Nat.le_log_of_pow_le Nat.one_lt_two
    calc
      2 ^ k ≤ p ^ k := htwo
      _ = n.toNat := hpow
      _ ≤ N := hnN
  rw [vonMangoldtBadPrimePowers, Finset.mem_biUnion]
  refine ⟨p, hr_eq ▸ hrq, Finset.mem_image.mpr ?_⟩
  refine ⟨k - 1, ?_, ?_⟩
  · simp only [Finset.mem_range]
    omega
  · rw [Nat.sub_add_cancel hk]
    calc
      ((p ^ k : ℕ) : ℤ) = (n.toNat : ℤ) := by exact_mod_cast hpow
      _ = n := Int.toNat_of_nonneg hn0

theorem card_primeFactors_le_log2 {q : ℕ} (hq : 0 < q) :
    q.primeFactors.card ≤ Nat.log2 q := by
  rw [Nat.log2_eq_log_two]
  apply Nat.le_log_of_pow_le Nat.one_lt_two
  calc
    2 ^ q.primeFactors.card = ∏ _p ∈ q.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ q.primeFactors, p := by
      exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
        (fun p hp => (Nat.mem_primeFactors.mp hp).1.two_le)
    _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)

theorem card_vonMangoldtBadSupport_le {q : ℕ} (hq : 0 < q) (N : ℕ) :
    (vonMangoldtBadSupport q N).card ≤
      q.primeFactors.card * (Nat.log2 N + 1) := by
  calc
    (vonMangoldtBadSupport q N).card ≤ (vonMangoldtBadPrimePowers q N).card :=
      Finset.card_le_card (vonMangoldtBadSupport_subset_primePowers hq N)
    _ ≤ ∑ p ∈ q.primeFactors,
        ((Finset.range (Nat.log2 N + 1)).image
          fun k => ((p ^ (k + 1) : ℕ) : ℤ)).card := by
      unfold vonMangoldtBadPrimePowers
      exact Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ q.primeFactors, (Nat.log2 N + 1) := by
      exact Finset.sum_le_sum fun _ _ =>
        Finset.card_image_le.trans_eq (Finset.card_range _)
    _ = q.primeFactors.card * (Nat.log2 N + 1) := by
      simp [Nat.mul_add]

/-- For `n ∈ [1, N]`, the correction for `Λ` at `n` has norm at most `2 log N`, and
it vanishes unless `Λ(n) ≠ 0` and `(n, q) ≠ 1`. -/
theorem vonMangoldt_changeLevelError_norm_le
    {q : ℕ} (χ : DirichletCharacter ℂ q) {N : ℕ} {n : ℤ}
    (hn : n ∈ Finset.Icc (1 : ℤ) N) :
    ‖conductorChangeLevelError χ vonMangoldtIntegerCoeff n‖ ≤
      if n ∈ vonMangoldtBadSupport q N then 2 * Real.log (N : ℝ) else 0 := by
  by_cases hbad : n ∈ vonMangoldtBadSupport q N
  · rw [if_pos hbad]
    have hn0 : 0 ≤ n := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    have hnpos : 0 < n.toNat := by
      have hn1 := (Finset.mem_Icc.mp hn).1
      omega
    have hnN : n.toNat ≤ N := Int.toNat_le.mpr (Finset.mem_Icc.mp hn).2
    have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n.toNat)
    have hΛN : ArithmeticFunction.vonMangoldt n.toNat ≤ Real.log (N : ℝ) := by
      exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hnpos) (by exact_mod_cast hnN))
    have he := conductorChangeLevelError_norm_sq_le χ vonMangoldtIntegerCoeff n
    have hb : ‖vonMangoldtIntegerCoeff n‖ =
        ArithmeticFunction.vonMangoldt n.toNat := by
      simp [vonMangoldtIntegerCoeff, abs_of_nonneg hΛ0]
    rw [hb] at he
    nlinarith only [he, hΛ0, hΛN,
      norm_nonneg (conductorChangeLevelError χ vonMangoldtIntegerCoeff n)]
  · rw [if_neg hbad]
    have hm := Finset.mem_Icc.mp hn
    simp only [mem_vonMangoldtBadSupport, hm.1, hm.2, true_and] at hbad
    rcases not_and_or.mp hbad with hΛ | hcop
    · have hcoeff : vonMangoldtIntegerCoeff n = 0 := by
        simp [vonMangoldtIntegerCoeff, not_not.mp hΛ]
      simp [conductorChangeLevelError, hcoeff]
    · exact le_of_eq (norm_eq_zero.mpr
        (conductorChangeLevelError_eq_zero_of_isCoprime χ _ (not_not.mp hcop)))

/-- For `y ≤ N`, the correction prefix sum for `Λ` over `[1, y]` has norm at most
`2 log₂ q · (log₂ N + 1) · log N`. -/
theorem vonMangoldt_conductorErrorPrefixSquare_le
    {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (N : ℕ) {y : ℕ} (hy : y ≤ N) :
    conductorErrorPrefixSquare χ vonMangoldtIntegerCoeff 0 y ≤
      (2 * (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ)) ^ 2 := by
  have hsub : Finset.Icc (1 : ℤ) y ⊆ Finset.Icc (1 : ℤ) N := by
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans (by exact_mod_cast hy)⟩
  have hnorm : ‖∑ n ∈ Finset.Icc (1 : ℤ) y,
      conductorChangeLevelError χ vonMangoldtIntegerCoeff n‖ ≤
      2 * (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) := by
    calc
      ‖∑ n ∈ Finset.Icc (1 : ℤ) y,
          conductorChangeLevelError χ vonMangoldtIntegerCoeff n‖ ≤
          ∑ n ∈ Finset.Icc (1 : ℤ) y,
            ‖conductorChangeLevelError χ vonMangoldtIntegerCoeff n‖ :=
        norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc (1 : ℤ) y,
          if n ∈ vonMangoldtBadSupport q N then 2 * Real.log (N : ℝ) else 0 := by
        exact Finset.sum_le_sum fun n hn =>
          vonMangoldt_changeLevelError_norm_le χ (hsub hn)
      _ ≤ ((vonMangoldtBadSupport q N).card : ℝ) *
          (2 * Real.log (N : ℝ)) := by
        rw [← Finset.sum_filter]
        calc
          (∑ _n ∈ (Finset.Icc (1 : ℤ) y).filter
              (fun n => n ∈ vonMangoldtBadSupport q N), 2 * Real.log (N : ℝ)) =
              (((Finset.Icc (1 : ℤ) y).filter
                (fun n => n ∈ vonMangoldtBadSupport q N)).card : ℝ) *
                (2 * Real.log (N : ℝ)) := by simp
          _ ≤ ((vonMangoldtBadSupport q N).card : ℝ) *
                (2 * Real.log (N : ℝ)) := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast Finset.card_le_card (by
                intro n hn
                exact (Finset.mem_filter.mp hn).2)
            · positivity
      _ ≤ (q.primeFactors.card : ℝ) * (Nat.log2 N + 1 : ℝ) *
          (2 * Real.log (N : ℝ)) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast card_vonMangoldtBadSupport_le hq N
        · positivity
      _ ≤ (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) *
          (2 * Real.log (N : ℝ)) := by
        gcongr
        exact_mod_cast card_primeFactors_le_log2 hq
      _ = _ := by ring
  unfold conductorErrorPrefixSquare
  simpa using (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm

/-- The same bound for the maximum over `0 ≤ y ≤ N`. -/
theorem vonMangoldt_conductorErrorPrefixMaxSquare_le
    {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q) (N : ℕ) :
    conductorErrorPrefixMaxSquare χ vonMangoldtIntegerCoeff 0 N ≤
      (2 * (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ)) ^ 2 := by
  unfold conductorErrorPrefixMaxSquare
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  exact vonMangoldt_conductorErrorPrefixSquare_le hq χ N
    (by simpa [Finset.mem_range] using hy)

end

end BombieriVinogradov

namespace BombieriVinogradov

open Classical Finset
open scoped BigOperators
noncomputable section

/-!
## Harmonic sums and the totient function

The harmonic sum `H_R = ∑_{e ≤ R} 1/e` satisfies `H_R ≤ 1 + log R`, and
`n = ∑_{d ∣ n} φ(d)` gives `n / φ(n) ≤ τ(n)`.
-/

/-- The harmonic sum `H_R = ∑_{1 ≤ e ≤ R} 1/e`. -/
def conductorHarmonicFactor (R : ℕ) : ℝ :=
  ∑ e ∈ Finset.Icc 1 R, (e : ℝ)⁻¹

theorem conductorHarmonicFactor_nonneg (R : ℕ) :
    0 ≤ conductorHarmonicFactor R := by
  unfold conductorHarmonicFactor
  positivity

private theorem harmonic_step (k : ℕ) (hk : 0 < k) :
    (((k + 1 : ℕ) : ℝ)⁻¹) ≤
      Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkspos : (0 : ℝ) < k + 1 := by positivity
  have hratio : (0 : ℝ) < (k : ℝ) / (k + 1 : ℝ) := div_pos hkpos hkspos
  have hlog := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div (ne_of_gt hkpos) (ne_of_gt hkspos)] at hlog
  have hid : (k : ℝ) / (k + 1 : ℝ) - 1 = -((k + 1 : ℝ)⁻¹) := by
    field_simp
    ring
  rw [hid] at hlog
  norm_num only [Nat.cast_add, Nat.cast_one] at hlog ⊢
  linarith

/-- `H_R ≤ 1 + log R`, by telescoping `1/(k+1) ≤ log(k+1) - log k`. -/
theorem conductorHarmonicFactor_le (R : ℕ) :
    conductorHarmonicFactor R ≤ 1 + Real.log (R : ℝ) := by
  induction R with
  | zero => simp [conductorHarmonicFactor]
  | succ R ih =>
      by_cases hR : R = 0
      · subst R; norm_num [conductorHarmonicFactor]
      · rw [conductorHarmonicFactor, Finset.sum_Icc_succ_top (by omega)]
        rw [conductorHarmonicFactor] at ih
        have hs := harmonic_step R (Nat.pos_of_ne_zero hR)
        norm_num only [Nat.cast_add, Nat.cast_one] at hs ⊢
        linarith

/-- `n / φ(n) ≤ τ(n)`, since `n = ∑_{d ∣ n} φ(d)` and `φ(d) ≤ φ(n)` for `d ∣ n`. -/
theorem totientRatio_le_card_divisors (n : ℕ) (hn : 0 < n) :
    (n : ℝ) / (n.totient : ℝ) ≤ (n.divisors.card : ℝ) := by
  have hφ : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  nth_rw 1 [← Nat.sum_totient n]
  rw [Nat.cast_sum, Finset.sum_div]
  calc
    (∑ d ∈ n.divisors, (d.totient : ℝ) / (n.totient : ℝ))
      ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        apply (div_le_one hφ).2
        exact_mod_cast Nat.le_of_dvd (Nat.totient_pos.mpr hn)
          (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
    _ = (n.divisors.card : ℝ) := by simp

/-- There are `⌊R/e⌋` multiples of `e` in `[1, R]`. -/
theorem sum_dvd_indicator_Icc (R e : ℕ) (he : 0 < e) :
    (∑ r ∈ Finset.Icc 1 R, if e ∣ r then (1 : ℝ) else 0) = (R / e : ℕ) := by
  symm
  rw [← Finset.sum_filter]
  calc
    ((R / e : ℕ) : ℝ) = ∑ k ∈ Finset.Icc 1 (R / e), (1 : ℝ) := by simp
    _ = ∑ r ∈ (Finset.Icc 1 R).filter (fun r => e ∣ r), (1 : ℝ) := by
      refine Finset.sum_bij (fun k _ => e * k) ?_ ?_ ?_ ?_
      · intro k hk
        rw [Finset.mem_filter, Finset.mem_Icc]
        rw [Finset.mem_Icc] at hk
        exact ⟨⟨Nat.mul_pos he hk.1,
          (Nat.mul_le_mul_left e hk.2).trans (Nat.mul_div_le R e)⟩,
          dvd_mul_right e k⟩
      · intro k₁ hk₁ k₂ hk₂ h
        exact Nat.eq_of_mul_eq_mul_left he h
      · intro r hr
        rw [Finset.mem_filter, Finset.mem_Icc] at hr
        refine ⟨r / e, ?_, ?_⟩
        · rw [Finset.mem_Icc]
          exact ⟨Nat.div_pos (Nat.le_of_dvd hr.1.1 hr.2) he,
            Nat.div_le_div_right hr.1.2⟩
        · exact Nat.mul_div_cancel' hr.2
      · intro k hk
        simp

/-!
## Conductor multiplicity

When each character modulo `q ≤ Q` carries weight `1/φ(q)`, a primitive character
modulo `d` occurs with total weight `∑_{q ≤ Q, d ∣ q} 1/φ(q) ≤ H_Q² / φ(d)`.
-/

/-- `∑_{q ≤ Q, d ∣ q} 1/φ(q)`. -/
def directConductorWeight (Q d : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q with d ∣ q, ((q.totient : ℝ)⁻¹)

theorem directConductorWeight_eq_sum_multiples
    (Q d : ℕ) (hd : 0 < d) :
    directConductorWeight Q d =
      ∑ r ∈ Finset.Icc 1 (Q / d), (((d * r).totient : ℝ)⁻¹) := by
  rw [directConductorWeight]
  symm
  refine Finset.sum_bij (fun r _ => d * r) ?_ ?_ ?_ ?_
  · intro r hr
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hr' := Finset.mem_Icc.mp hr
    exact ⟨⟨Nat.mul_pos hd hr'.1,
      (Nat.mul_le_mul_left d hr'.2).trans (Nat.mul_div_le Q d)⟩,
      dvd_mul_right d r⟩
  · intro r₁ hr₁ r₂ hr₂ h
    exact Nat.eq_of_mul_eq_mul_left hd h
  · intro q hq
    have hq' := Finset.mem_filter.mp hq
    refine ⟨q / d, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨Nat.div_pos (Nat.le_of_dvd (Finset.mem_Icc.mp hq'.1).1 hq'.2) hd,
        Nat.div_le_div_right (Finset.mem_Icc.mp hq'.1).2⟩
    · exact Nat.mul_div_cancel' hq'.2
  · intro r hr
    rfl

theorem multiple_inv_totient_le_product
    (d r : ℕ) (hd : 0 < d) (hr : 0 < r) :
    (((d * r).totient : ℝ)⁻¹) ≤
      ((d.totient : ℝ)⁻¹) * ((r.totient : ℝ)⁻¹) := by
  have hφnat : d.totient * r.totient ≤ (d * r).totient :=
    Nat.totient_super_multiplicative d r
  have hφ : (d.totient : ℝ) * (r.totient : ℝ) ≤ ((d * r).totient : ℝ) := by
    exact_mod_cast hφnat
  have hprod : (0 : ℝ) < (d.totient : ℝ) * (r.totient : ℝ) := by positivity
  calc
    (((d * r).totient : ℝ)⁻¹)
      ≤ (((d.totient : ℝ) * (r.totient : ℝ))⁻¹) :=
        inv_anti₀ hprod hφ
    _ = ((d.totient : ℝ)⁻¹) * ((r.totient : ℝ)⁻¹) := by
      rw [mul_inv]

theorem inv_totient_le_card_divisors_div
    (r : ℕ) (hr : 0 < r) :
    ((r.totient : ℝ)⁻¹) ≤ (r.divisors.card : ℝ) / r := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h := totientRatio_le_card_divisors r hr
  calc
    ((r.totient : ℝ)⁻¹) = ((r : ℝ) / (r.totient : ℝ)) / r := by
      field_simp
    _ ≤ (r.divisors.card : ℝ) / r :=
      div_le_div_of_nonneg_right h hrR.le

private theorem sum_inv_multiples_Icc (R e : ℕ) (he : 0 < e) :
    (∑ r ∈ Finset.Icc 1 R, if e ∣ r then ((r : ℝ)⁻¹) else 0) =
      (e : ℝ)⁻¹ * conductorHarmonicFactor (R / e) := by
  rw [← Finset.sum_filter]
  symm
  rw [conductorHarmonicFactor, Finset.mul_sum]
  refine Finset.sum_bij (fun k _ => e * k) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc]
    rw [Finset.mem_Icc] at hk
    exact ⟨⟨Nat.mul_pos he hk.1,
      (Nat.mul_le_mul_left e hk.2).trans (Nat.mul_div_le R e)⟩,
      dvd_mul_right e k⟩
  · intro k₁ hk₁ k₂ hk₂ h
    exact Nat.eq_of_mul_eq_mul_left he h
  · intro r hr
    rw [Finset.mem_filter, Finset.mem_Icc] at hr
    refine ⟨r / e, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨Nat.div_pos (Nat.le_of_dvd hr.1.1 hr.2) he,
        Nat.div_le_div_right hr.1.2⟩
    · exact Nat.mul_div_cancel' hr.2
  · intro k hk
    push_cast
    rw [← mul_inv]

/-- `∑_{r ≤ R} τ(r)/r ≤ H_R²`, by writing `τ(r) = ∑_{e ∣ r} 1` and swapping the sums. -/
theorem sum_card_divisors_div_le_harmonic_sq (R : ℕ) :
    (∑ r ∈ Finset.Icc 1 R, (r.divisors.card : ℝ) / r) ≤
      conductorHarmonicFactor R ^ 2 := by
  calc
    (∑ r ∈ Finset.Icc 1 R, (r.divisors.card : ℝ) / r)
      = ∑ r ∈ Finset.Icc 1 R,
          ∑ e ∈ Finset.Icc 1 R, if e ∣ r then ((r : ℝ)⁻¹) else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        have hset : r.divisors = (Finset.Icc 1 R).filter (fun e => e ∣ r) := by
          ext e
          rw [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
          constructor
          · intro he
            exact ⟨⟨Nat.pos_of_dvd_of_pos he.1 (Finset.mem_Icc.mp hr).1,
              (Nat.le_of_dvd (by omega : 0 < r) he.1).trans
                (Finset.mem_Icc.mp hr).2⟩, he.1⟩
          · intro he
            exact ⟨he.2, Nat.ne_of_gt (Finset.mem_Icc.mp hr).1⟩
        rw [hset, div_eq_mul_inv]
        rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul,
          Finset.sum_filter]
        simp
    _ = ∑ e ∈ Finset.Icc 1 R,
          ∑ r ∈ Finset.Icc 1 R, if e ∣ r then ((r : ℝ)⁻¹) else 0 := by
        exact Finset.sum_comm
    _ = ∑ e ∈ Finset.Icc 1 R,
          (e : ℝ)⁻¹ * conductorHarmonicFactor (R / e) := by
        apply Finset.sum_congr rfl
        intro e he
        exact sum_inv_multiples_Icc R e (Finset.mem_Icc.mp he).1
    _ ≤ ∑ e ∈ Finset.Icc 1 R,
          (e : ℝ)⁻¹ * conductorHarmonicFactor R := by
        apply Finset.sum_le_sum
        intro e he
        apply mul_le_mul_of_nonneg_left
        · unfold conductorHarmonicFactor
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.Icc_subset_Icc_right (Nat.div_le_self R e)
          · intro k hk hnot
            positivity
        · positivity
    _ = conductorHarmonicFactor R ^ 2 := by
        rw [conductorHarmonicFactor, ← Finset.sum_mul]
        ring

/-- `∑_{r ≤ R} 1/φ(r) ≤ H_R²`, since `1/φ(r) ≤ τ(r)/r`. -/
theorem sum_inv_totient_le_harmonic_sq (R : ℕ) :
    (∑ r ∈ Finset.Icc 1 R, ((r.totient : ℝ)⁻¹)) ≤
      conductorHarmonicFactor R ^ 2 := by
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 R, (r.divisors.card : ℝ) / r := by
      apply Finset.sum_le_sum
      intro r hr
      exact inv_totient_le_card_divisors_div r (Finset.mem_Icc.mp hr).1
    _ ≤ _ := sum_card_divisors_div_le_harmonic_sq R

theorem conductorHarmonicFactor_mono {R S : ℕ} (hRS : R ≤ S) :
    conductorHarmonicFactor R ≤ conductorHarmonicFactor S := by
  unfold conductorHarmonicFactor
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc_right hRS
  · intro e he hnot
    positivity

/-- `∑_{q ≤ Q, d ∣ q} 1/φ(q) ≤ H_Q² / φ(d)` for every `d`; the sum is empty when
`d = 0` or `d > Q`. Write `q = d r` and use `φ(d) φ(r) ≤ φ(d r)`. -/
theorem directConductorWeight_le (Q d : ℕ) :
    directConductorWeight Q d ≤
      conductorHarmonicFactor Q ^ 2 / (d.totient : ℝ) := by
  by_cases hd : d = 0
  · subst d
    have hempty : (Finset.Icc 1 Q).filter (fun q => 0 ∣ q) = ∅ := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty,
        iff_false]
      intro hq
      obtain ⟨c, hc⟩ := hq.2
      simp only [Nat.zero_mul] at hc
      omega
    rw [directConductorWeight, hempty]
    simp
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  rw [directConductorWeight_eq_sum_multiples Q d hdpos]
  calc
    (∑ r ∈ Finset.Icc 1 (Q / d), (((d * r).totient : ℝ)⁻¹))
      ≤ ∑ r ∈ Finset.Icc 1 (Q / d),
          ((d.totient : ℝ)⁻¹) * ((r.totient : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro r hr
        exact multiple_inv_totient_le_product d r hdpos (Finset.mem_Icc.mp hr).1
    _ = ((d.totient : ℝ)⁻¹) *
          ∑ r ∈ Finset.Icc 1 (Q / d), ((r.totient : ℝ)⁻¹) := by
        rw [Finset.mul_sum]
    _ ≤ ((d.totient : ℝ)⁻¹) * conductorHarmonicFactor (Q / d) ^ 2 := by
        gcongr
        exact sum_inv_totient_le_harmonic_sq (Q / d)
    _ ≤ ((d.totient : ℝ)⁻¹) * conductorHarmonicFactor Q ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · exact (sq_le_sq₀
            (conductorHarmonicFactor_nonneg _) (conductorHarmonicFactor_nonneg _)).2
              (conductorHarmonicFactor_mono (Nat.div_le_self Q d))
        · positivity
    _ = conductorHarmonicFactor Q ^ 2 / (d.totient : ℝ) := by
        rw [div_eq_mul_inv]
        ring

end

end BombieriVinogradov
