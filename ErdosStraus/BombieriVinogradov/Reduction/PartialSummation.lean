import ErdosStraus.BombieriVinogradov.Reduction.Orthogonality

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

/-!
# Partial summation from `ψ(y; q, a)` to `π(y; q, a)`

Abel summation against the weights `1 / log n` writes `π(y; q, a)` in terms of
`θ(n; q, a)` for `n ≤ y`, and `θ` differs from `ψ` only at prime powers `p^k` with `k ≥ 2`.
The main result `primeAPPrefixMaxError_le_lambda` bounds
`max_{y ≤ N} max_{(a,q)=1} |π(y; q, a) - li(y)/φ(q)|` by
`A(N) (E_ψ(N, q) + E_pp(N, q)) + E_li(N) / φ(q)`, with the terms defined there.
The prime-power term satisfies `E_pp(N, q) ≤ (√N + 1)(log₂ N + 1) log N`.
-/

namespace BombieriVinogradov

open Classical Finset
open scoped BigOperators ArithmeticFunction
noncomputable section

/-- The partial sum `∑_{n ≤ y} c(n)`. -/
def realPrefix (c : ℕ → ℝ) (y : ℕ) : ℝ :=
  ∑ n ∈ range (y + 1), c n

/-- Abel summation: `∑_{n ≤ y} w(n) c(n) = w(y) C(y) + ∑_{n < y} (w(n) - w(n+1)) C(n)`,
where `C(n) = ∑_{m ≤ n} c(m)`. -/
theorem sum_range_mul_eq_discreteAbel (c w : ℕ → ℝ) (y : ℕ) :
    (∑ n ∈ range (y + 1), w n * c n) =
      w y * realPrefix c y +
        ∑ n ∈ range y, (w n - w (n + 1)) * realPrefix c n := by
  induction y with
  | zero => simp [realPrefix]
  | succ y ih =>
      simp only [Finset.sum_range_succ, realPrefix] at ih ⊢
      rw [ih]
      ring

/-- The weight `1 / log n` for `n ≥ 2`, set to `0` at `n = 0, 1`. -/
def reciprocalLogWeight (n : ℕ) : ℝ :=
  if 2 ≤ n then (Real.log (n : ℝ))⁻¹ else 0

/-- `log n` if `n` is a prime with `n ≡ a mod q`, and `0` otherwise. -/
def primeThetaAPIncrement (q a n : ℕ) : ℝ :=
  if n.Prime ∧ n ≡ a [MOD q] then Real.log (n : ℝ) else 0

/-- `1` if `n` is a prime with `n ≡ a mod q`, and `0` otherwise. -/
def primeAPIncrement (q a n : ℕ) : ℝ :=
  if n.Prime ∧ n ≡ a [MOD q] then 1 else 0

/-- `θ(y; q, a) = ∑_{p ≤ y, p ≡ a mod q} log p`. -/
def primeThetaAPPrefix (y q a : ℕ) : ℝ :=
  realPrefix (primeThetaAPIncrement q a) y

theorem reciprocalLogWeight_mul_primeThetaAPIncrement (q a n : ℕ) :
    reciprocalLogWeight n * primeThetaAPIncrement q a n = primeAPIncrement q a n := by
  unfold reciprocalLogWeight primeThetaAPIncrement primeAPIncrement
  by_cases h : n.Prime ∧ n ≡ a [MOD q]
  · rw [if_pos h, if_pos h]
    have hn2 : 2 ≤ n := h.1.two_le
    rw [if_pos hn2]
    have hlog : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast h.1.one_lt)).ne'
    field_simp
  · simp [h]

theorem cast_primesInAP_eq_sum_primeAPIncrement (y q a : ℕ) :
    (BombieriVinogradov.primesInAP y q a : ℝ) =
      ∑ n ∈ range (y + 1), primeAPIncrement q a n := by
  simp [BombieriVinogradov.primesInAP, primeAPIncrement]

/-- Abel summation for primes in a progression:
`π(y; q, a) = θ(y; q, a) / log y + ∑_{n < y} (1/log n - 1/log (n+1)) θ(n; q, a)`.
Setting the weight to `0` at `n = 0, 1` is harmless since there are no primes there. -/
theorem primesInAP_eq_discreteAbel (y q a : ℕ) :
    (BombieriVinogradov.primesInAP y q a : ℝ) =
      reciprocalLogWeight y * primeThetaAPPrefix y q a +
        ∑ n ∈ range y,
          (reciprocalLogWeight n - reciprocalLogWeight (n + 1)) *
            primeThetaAPPrefix n q a := by
  rw [cast_primesInAP_eq_sum_primeAPIncrement]
  simp_rw [← reciprocalLogWeight_mul_primeThetaAPIncrement q a]
  exact sum_range_mul_eq_discreteAbel _ _ _

/-- The same Abel sum applied to the main term `y`:
`y / log y + ∑_{n < y} (1/log n - 1/log (n+1)) n`, which equals `∑_{2 ≤ n ≤ y} 1/log n`. -/
def discreteAbelLiMain (y : ℕ) : ℝ :=
  reciprocalLogWeight y * y +
    ∑ n ∈ range y,
      (reciprocalLogWeight n - reciprocalLogWeight (n + 1)) * n

/-- The total variation `1/log y + ∑_{n < y} |1/log n - 1/log (n+1)|` of the weights
on `[0, y]`. -/
def discreteAbelAmplifier (y : ℕ) : ℝ :=
  |reciprocalLogWeight y| +
    ∑ n ∈ range y, |reciprocalLogWeight n - reciprocalLogWeight (n + 1)|

/-- The error `θ(y; q, a) - y/φ(q)`. -/
def thetaAPMainError (y q a : ℕ) : ℝ :=
  primeThetaAPPrefix y q a - (q.totient : ℝ)⁻¹ * y

/-- The difference `ψ(y; q, a) - θ(y; q, a)`, the contribution of the prime powers `p^k`
with `k ≥ 2`. -/
def lambdaPrimePowerCorrection (y q a : ℕ) : ℂ :=
  lambdaAPPrefix y q a - (primeThetaAPPrefix y q a : ℂ)

theorem lambdaPrimePowerCorrection_eq_nonprime_sum (y q a : ℕ) :
    lambdaPrimePowerCorrection y q a =
      ∑ n ∈ range (y + 1),
        if (n : ZMod q) = (a : ZMod q) ∧ ¬ n.Prime then lambdaNatCoeff n else 0 := by
  unfold lambdaPrimePowerCorrection lambdaAPPrefix primeThetaAPPrefix realPrefix
    primeThetaAPIncrement
  rw [Finset.sum_filter]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hr : (n : ZMod q) = (a : ZMod q)
  · have hmod : n ≡ a [MOD q] :=
      (ZMod.natCast_eq_natCast_iff n a q).mp hr
    by_cases hp : n.Prime
    · simp [hr, hmod, hp, lambdaNatCoeff,
        ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [hr, hmod, hp]
  · have hnotmod : ¬ n ≡ a [MOD q] := by
      simpa only [ZMod.natCast_eq_natCast_iff] using hr
    simp [hr, hnotmod]

theorem abs_thetaAPMainError_le_lambda_add_primePower (y q a : ℕ) :
    |thetaAPMainError y q a| ≤
      ‖lambdaAPMainError y q a‖ + ‖lambdaPrimePowerCorrection y q a‖ := by
  have hid : ((thetaAPMainError y q a : ℝ) : ℂ) =
      lambdaAPMainError y q a - lambdaPrimePowerCorrection y q a := by
    unfold thetaAPMainError lambdaAPMainError lambdaPrimePowerCorrection
    push_cast
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hid]
  exact norm_sub_le _ _

/-- The distance `|∑_{2 ≤ n ≤ y} 1/log n - li(y)|` between the discrete main term and the
logarithmic integral. It does not depend on `q` or `a`. -/
def liDiscreteError (y : ℕ) : ℝ :=
  |discreteAbelLiMain y -
    BombieriVinogradov.logIntegral y|

/-- If `|E(n)| ≤ M` for all `n ≤ y`, the Abel sum of `E` is at most `M` times the total
variation of the weights. -/
theorem abs_discreteAbel_le
    (E : ℕ → ℝ) (M : ℝ) (y : ℕ)
    (hE : ∀ n ≤ y, |E n| ≤ M) :
    |reciprocalLogWeight y * E y +
        ∑ n ∈ range y,
          (reciprocalLogWeight n - reciprocalLogWeight (n + 1)) * E n| ≤
      discreteAbelAmplifier y * M := by
  calc
    _ ≤ |reciprocalLogWeight y * E y| +
        ∑ n ∈ range y,
          |(reciprocalLogWeight n - reciprocalLogWeight (n + 1)) * E n| :=
      (abs_add_le _ _).trans (add_le_add le_rfl (abs_sum_le_sum_abs _ _))
    _ ≤ |reciprocalLogWeight y| * M +
        ∑ n ∈ range y,
          |reciprocalLogWeight n - reciprocalLogWeight (n + 1)| * M := by
      simp only [abs_mul]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (hE y le_rfl) (abs_nonneg _)
      · exact sum_le_sum fun n hn =>
          mul_le_mul_of_nonneg_left (hE n (Nat.le_of_lt (mem_range.mp hn))) (abs_nonneg _)
    _ = _ := by
      unfold discreteAbelAmplifier
      rw [add_mul, sum_mul]

/-- `max_{y ≤ N} |θ(y; q, a) - y/φ(q)|`. -/
def thetaAPResiduePrefixMaxError (N q a : ℕ) : ℝ :=
  ((range (N + 1)).image (fun y => |thetaAPMainError y q a|)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

theorem abs_thetaAPMainError_le_residuePrefixMax
    {y N q a : ℕ} (hy : y ≤ N) :
    |thetaAPMainError y q a| ≤ thetaAPResiduePrefixMaxError N q a := by
  unfold thetaAPResiduePrefixMaxError
  exact Finset.le_max'
    ((range (N + 1)).image (fun y : ℕ => |thetaAPMainError y q a|)) _
    (Finset.mem_image.mpr ⟨y, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hy), rfl⟩)

private theorem thetaAPResiduePrefixMaxError_mono
    {y N q a : ℕ} (hy : y ≤ N) :
    thetaAPResiduePrefixMaxError y q a ≤ thetaAPResiduePrefixMaxError N q a := by
  unfold thetaAPResiduePrefixMaxError
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨n, hn, rfl⟩
  exact abs_thetaAPMainError_le_residuePrefixMax
    ((Nat.le_of_lt_succ (Finset.mem_range.mp hn)).trans hy)

/-- Partial summation in one residue class: `|π(y; q, a) - li(y)/φ(q)|` is at most the total
variation of the weights times `max_{n ≤ y} |θ(n; q, a) - n/φ(q)|`, plus
`|∑_{2 ≤ n ≤ y} 1/log n - li(y)| / φ(q)`. -/
theorem abs_primeAPError_le_abel
    {y q a : ℕ} (hq : 0 < q) :
    |BombieriVinogradov.primeAPError y q a| ≤
      discreteAbelAmplifier y * thetaAPResiduePrefixMaxError y q a +
        (q.totient : ℝ)⁻¹ * liDiscreteError y := by
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr hq
  let E : ℕ → ℝ := fun n => thetaAPMainError n q a
  have hrewrite (n : ℕ) :
      primeThetaAPPrefix n q a = (q.totient : ℝ)⁻¹ * n + E n := by
    dsimp [E]
    unfold thetaAPMainError
    ring
  have heq :
      BombieriVinogradov.primeAPError y q a =
        (reciprocalLogWeight y * E y +
          ∑ n ∈ range y,
            (reciprocalLogWeight n - reciprocalLogWeight (n + 1)) * E n) +
        (q.totient : ℝ)⁻¹ *
          (discreteAbelLiMain y -
            BombieriVinogradov.logIntegral y) := by
    rw [BombieriVinogradov.primeAPError,
      primesInAP_eq_discreteAbel]
    simp_rw [hrewrite, mul_add]
    rw [sum_add_distrib]
    unfold discreteAbelLiMain
    have hfactor :
        (∑ n ∈ range y,
          (reciprocalLogWeight n - reciprocalLogWeight (n + 1)) *
            ((q.totient : ℝ)⁻¹ * n)) =
        (q.totient : ℝ)⁻¹ *
          ∑ n ∈ range y,
            (reciprocalLogWeight n - reciprocalLogWeight (n + 1)) * n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    rw [hfactor]
    ring
  rw [heq]
  calc
    _ ≤ |reciprocalLogWeight y * E y +
          ∑ n ∈ range y,
            (reciprocalLogWeight n - reciprocalLogWeight (n + 1)) * E n| +
        |(q.totient : ℝ)⁻¹ *
          (discreteAbelLiMain y -
            BombieriVinogradov.logIntegral y)| :=
      abs_add_le _ _
    _ ≤ discreteAbelAmplifier y * thetaAPResiduePrefixMaxError y q a +
        (q.totient : ℝ)⁻¹ * liDiscreteError y := by
      apply add_le_add
      · apply abs_discreteAbel_le
        intro n hn
        exact abs_thetaAPMainError_le_residuePrefixMax hn
      · rw [abs_mul, abs_of_pos (inv_pos.mpr hφ)]
        unfold liDiscreteError
        rfl

/-- The maximum of `0` and the values `|ψ(y; q, a) - θ(y; q, a)|` for `y ≤ N` and reduced
residues `a`. -/
def lambdaPrimePowerCorrectionPrefixMaxError (N q : ℕ) : ℝ :=
  (insert 0 (((range (N + 1)).product
    (BombieriVinogradov.unitResidues q)).image
      (fun p => ‖lambdaPrimePowerCorrection p.1 q p.2‖))).max' (by simp)

/-- The maximum over `y ≤ N` of the total variation of the weights on `[0, y]`. -/
def discreteAbelAmplifierPrefixMax (N : ℕ) : ℝ :=
  ((range (N + 1)).image discreteAbelAmplifier).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- `max_{y ≤ N} |∑_{2 ≤ n ≤ y} 1/log n - li(y)|`. -/
def liDiscretePrefixMaxError (N : ℕ) : ℝ :=
  ((range (N + 1)).image liDiscreteError).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

private theorem norm_lambdaAPMainError_le_prefixMax
    {y N q a : ℕ} (hy : y ≤ N)
    (ha : a ∈ BombieriVinogradov.unitResidues q) :
    ‖lambdaAPMainError y q a‖ ≤ lambdaAPPrefixMaxError N q := by
  unfold lambdaAPPrefixMaxError
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨(y, a), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hy), ha⟩, rfl⟩)

private theorem norm_primePowerCorrection_le_prefixMax
    {y N q a : ℕ} (hy : y ≤ N)
    (ha : a ∈ BombieriVinogradov.unitResidues q) :
    ‖lambdaPrimePowerCorrection y q a‖ ≤
      lambdaPrimePowerCorrectionPrefixMaxError N q := by
  unfold lambdaPrimePowerCorrectionPrefixMaxError
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨(y, a), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hy), ha⟩, rfl⟩)

private theorem discreteAbelAmplifier_le_prefixMax
    {y N : ℕ} (hy : y ≤ N) :
    discreteAbelAmplifier y ≤ discreteAbelAmplifierPrefixMax N := by
  unfold discreteAbelAmplifierPrefixMax
  exact Finset.le_max' _ _ (Finset.mem_image.mpr
    ⟨y, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hy), rfl⟩)

private theorem discreteAbelAmplifier_nonneg (y : ℕ) :
    0 ≤ discreteAbelAmplifier y := by
  unfold discreteAbelAmplifier
  exact add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem discreteAbelAmplifierPrefixMax_nonneg (N : ℕ) :
    0 ≤ discreteAbelAmplifierPrefixMax N :=
  (discreteAbelAmplifier_nonneg 0).trans
    (discreteAbelAmplifier_le_prefixMax (Nat.zero_le N))

private theorem liDiscreteError_le_prefixMax
    {y N : ℕ} (hy : y ≤ N) :
    liDiscreteError y ≤
      liDiscretePrefixMaxError N := by
  unfold liDiscretePrefixMaxError
  exact Finset.le_max' _ _ (Finset.mem_image.mpr
    ⟨y, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hy), rfl⟩)

theorem thetaAPResiduePrefixMaxError_le_lambda_add_primePower
    {N q a : ℕ} (ha : a ∈ BombieriVinogradov.unitResidues q) :
    thetaAPResiduePrefixMaxError N q a ≤
      lambdaAPPrefixMaxError N q +
        lambdaPrimePowerCorrectionPrefixMaxError N q := by
  unfold thetaAPResiduePrefixMaxError
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  have hyN : y ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hy)
  exact (abs_thetaAPMainError_le_lambda_add_primePower y q a).trans
    (add_le_add (norm_lambdaAPMainError_le_prefixMax hyN ha)
      (norm_primePowerCorrection_le_prefixMax hyN ha))

private theorem insertZeroMax_nonneg (S : Finset ℝ) :
    0 ≤ (insert 0 S).max' (by simp) :=
  Finset.le_max' (insert 0 S) 0 (Finset.mem_insert_self 0 S)

private theorem abelBound_nonneg (N q : ℕ) :
    0 ≤ discreteAbelAmplifierPrefixMax N *
        (lambdaAPPrefixMaxError N q +
          lambdaPrimePowerCorrectionPrefixMaxError N q) +
      (q.totient : ℝ)⁻¹ * liDiscretePrefixMaxError N := by
  have hA := discreteAbelAmplifierPrefixMax_nonneg N
  have hL : 0 ≤ lambdaAPPrefixMaxError N q := by
    unfold lambdaAPPrefixMaxError
    exact insertZeroMax_nonneg _
  have hP : 0 ≤ lambdaPrimePowerCorrectionPrefixMaxError N q := by
    unfold lambdaPrimePowerCorrectionPrefixMaxError
    exact insertZeroMax_nonneg _
  have hS : 0 ≤ liDiscretePrefixMaxError N :=
    (abs_nonneg _).trans (liDiscreteError_le_prefixMax (Nat.zero_le N))
  positivity

/-- The bound of `primeAPPrefixMaxError_le_lambda` for a single `y ≤ N` and
reduced residue `a`. -/
theorem abs_primeAPError_le_lambda
    {y N q a : ℕ} (hq : 0 < q) (hy : y ≤ N)
    (ha : a ∈ BombieriVinogradov.unitResidues q) :
    |BombieriVinogradov.primeAPError y q a| ≤
      discreteAbelAmplifierPrefixMax N *
        (lambdaAPPrefixMaxError N q +
          lambdaPrimePowerCorrectionPrefixMaxError N q) +
      (q.totient : ℝ)⁻¹ * liDiscretePrefixMaxError N := by
  refine (abs_primeAPError_le_abel hq).trans ?_
  apply add_le_add
  · have hTheta : 0 ≤ thetaAPResiduePrefixMaxError y q a :=
      (abs_nonneg (thetaAPMainError 0 q a)).trans
        (abs_thetaAPMainError_le_residuePrefixMax (Nat.zero_le y))
    exact mul_le_mul
      (discreteAbelAmplifier_le_prefixMax hy)
      ((thetaAPResiduePrefixMaxError_mono hy).trans
        (thetaAPResiduePrefixMaxError_le_lambda_add_primePower ha))
      hTheta (discreteAbelAmplifierPrefixMax_nonneg N)
  · exact mul_le_mul_of_nonneg_left (liDiscreteError_le_prefixMax hy)
      (inv_nonneg.mpr (Nat.cast_nonneg q.totient))

/-- Partial summation bound: `max_{y ≤ N} max_{(a,q)=1} |π(y; q, a) - li(y)/φ(q)|` is at most
`A(N) (E_ψ(N, q) + E_pp(N, q)) + E_li(N) / φ(q)`, where `A(N)` is the maximum over `y ≤ N`
of the total variation of the weights `1 / log n` on `[0, y]`, `E_ψ` and `E_pp` are the
maxima of `|ψ(y; q, a) - y/φ(q)|` and `|ψ(y; q, a) - θ(y; q, a)|` over `y ≤ N` and reduced
`a`, and `E_li(N) = max_{y ≤ N} |∑_{2 ≤ n ≤ y} 1/log n - li(y)|`. -/
theorem primeAPPrefixMaxError_le_lambda
    {N q : ℕ} (hq : 0 < q) :
    BombieriVinogradov.primeAPPrefixMaxError N q ≤
      discreteAbelAmplifierPrefixMax N *
        (lambdaAPPrefixMaxError N q +
          lambdaPrimePowerCorrectionPrefixMaxError N q) +
      (q.totient : ℝ)⁻¹ * liDiscretePrefixMaxError N := by
  unfold BombieriVinogradov.primeAPPrefixMaxError
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  have hyN : y ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hy)
  unfold BombieriVinogradov.primeAPMaxError
  dsimp only
  split_ifs with hS
  · apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨a, ha, rfl⟩
    exact abs_primeAPError_le_lambda hq hyN ha
  · exact abelBound_nonneg N q

/-- The same bound with `E_ψ(N, q)` replaced by its character majorant
`φ(q)⁻¹ (max_{y ≤ N} |ψ(y, χ₀) - y| + ∑_{χ ≠ χ₀} max_{y ≤ N} |ψ(y, χ)|)`, where `χ₀` is the
principal character mod `q`. -/
theorem primeAPPrefixMaxError_le_characters
    {N q : ℕ} (hq : 0 < q) :
    BombieriVinogradov.primeAPPrefixMaxError N q ≤
      discreteAbelAmplifierPrefixMax N *
        ((q.totient : ℝ)⁻¹ *
            (principalLambdaPrefixMaxError N q +
              ∑ χ ∈ nonprincipalCharacters q,
                lambdaCharacterPrefixMaxAmplitude N q χ) +
          lambdaPrimePowerCorrectionPrefixMaxError N q) +
      (q.totient : ℝ)⁻¹ * liDiscretePrefixMaxError N := by
  refine (primeAPPrefixMaxError_le_lambda hq).trans ?_
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (discreteAbelAmplifierPrefixMax_nonneg N)
    exact add_le_add (lambdaAPPrefixMaxError_le_character_majorant hq) le_rfl
  · exact le_rfl

end

end BombieriVinogradov

/-! ## The prime-power term

A nonprime `n ≤ N` with `Λ(n) ≠ 0` is `p^k` with `k ≥ 2`, so `p ≤ √N` and `k ≤ log₂ N`.
Hence `|ψ(y; q, a) - θ(y; q, a)| ≤ (√N + 1)(log₂ N + 1) log N` for `y ≤ N`, uniformly in `q`
and `a`.
-/

namespace BombieriVinogradov

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology
noncomputable section

/-- The nonprime `n ≤ N` with `Λ(n) ≠ 0`, that is, the prime powers `p^k ≤ N` with
`k ≥ 2`. -/
def higherPrimePowerSupport (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun n =>
    ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0

/-- The numbers `b^(j+2)` with `b ≤ √N` and `j ≤ log₂ N`. They include every `p^k ≤ N` with
`k ≥ 2`. -/
def higherPrimePowerEnvelope (N : ℕ) : Finset ℕ :=
  ((Finset.range (N.sqrt + 1)).product
    (Finset.range (Nat.log2 N + 1))).image fun pk => pk.1 ^ (pk.2 + 2)

lemma higherPrimePowerSupport_subset_envelope (N : ℕ) :
    higherPrimePowerSupport N ⊆ higherPrimePowerEnvelope N := by
  intro n hn
  rw [higherPrimePowerSupport, Finset.mem_filter] at hn
  obtain ⟨p, k, hp, hk, hpow⟩ :=
    (isPrimePow_nat_iff n).mp
      (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hn.2.2)
  have hk2 : 2 ≤ k := by
    have hk1 : k ≠ 1 := by
      intro h
      subst k
      simp only [pow_one] at hpow
      exact hn.2.1 (hpow ▸ hp)
    omega
  have hnN : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hn.1)
  have hp2k : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
  have hpsqrt : p ≤ N.sqrt := by
    rw [Nat.le_sqrt']
    calc
      p ^ 2 ≤ p ^ k := hp2k
      _ = n := hpow
      _ ≤ N := hnN
  have hklog : k ≤ Nat.log2 N := by
    rw [Nat.log2_eq_log_two]
    apply Nat.le_log_of_pow_le Nat.one_lt_two
    calc
      2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
      _ = n := hpow
      _ ≤ N := hnN
  rw [higherPrimePowerEnvelope, Finset.mem_image]
  refine ⟨(p, k - 2), ?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hpsqrt),
      Finset.mem_range.mpr (by omega)⟩
  · simp only
    rw [Nat.sub_add_cancel hk2, hpow]

/-- There are at most `(√N + 1)(log₂ N + 1)` prime powers `p^k ≤ N` with `k ≥ 2`. -/
theorem card_higherPrimePowerSupport_le (N : ℕ) :
    (higherPrimePowerSupport N).card ≤
      (N.sqrt + 1) * (Nat.log2 N + 1) := by
  calc
    (higherPrimePowerSupport N).card ≤ (higherPrimePowerEnvelope N).card :=
      Finset.card_le_card (higherPrimePowerSupport_subset_envelope N)
    _ ≤ (((Finset.range (N.sqrt + 1)).product
        (Finset.range (Nat.log2 N + 1))).card) := Finset.card_image_le
    _ = _ := by simp

private lemma vonMangoldt_zero_local : ArithmeticFunction.vonMangoldt 0 = 0 := by
  simp only [ArithmeticFunction.map_zero]

lemma lambda_norm_le_log_of_le {n N : ℕ} (hn : n ≤ N) (hN : 2 ≤ N) :
    ‖lambdaNatCoeff n‖ ≤ Real.log (N : ℝ) := by
  by_cases hnz : n = 0
  · subst n
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    simp [lambdaNatCoeff, Real.log_nonneg hN1]
  have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hnz
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [lambdaNatCoeff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ0]
  exact ArithmeticFunction.vonMangoldt_le_log.trans
    (Real.strictMonoOn_log.monotoneOn hnpos hNpos (by exact_mod_cast hn))

/-- `|ψ(y; q, a) - θ(y; q, a)| ≤ (√N + 1)(log₂ N + 1) log N` for `y ≤ N`, uniformly in `q`
and `a`. -/
theorem norm_lambdaPrimePowerCorrection_le_explicit
    {y N q a : ℕ} (hy : y ≤ N) :
    ‖lambdaPrimePowerCorrection y q a‖ ≤
      ((N.sqrt + 1 : ℕ) : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) := by
  by_cases hN : 2 ≤ N
  · have hlog : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    rw [lambdaPrimePowerCorrection_eq_nonprime_sum]
    calc
      _ ≤ ∑ n ∈ Finset.range (y + 1),
          ‖if (n : ZMod q) = (a : ZMod q) ∧ ¬ n.Prime then lambdaNatCoeff n else 0‖ :=
        norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range (y + 1),
          if n ∈ higherPrimePowerSupport N then Real.log (N : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro n hn
        have hnN : n ≤ N :=
          (Nat.le_of_lt_succ (Finset.mem_range.mp hn)).trans hy
        by_cases hr : (n : ZMod q) = (a : ZMod q) ∧ ¬ n.Prime
        · rw [if_pos hr]
          by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
          · simp [lambdaNatCoeff, hΛ, higherPrimePowerSupport]
          · rw [if_pos]
            · exact lambda_norm_le_log_of_le hnN hN
            · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
                (Nat.lt_succ_iff.mpr hnN), hr.2, hΛ⟩
        · simp only [if_neg hr, norm_zero]
          by_cases hm : n ∈ higherPrimePowerSupport N <;> simp [hm, hlog]
      _ ≤ ((higherPrimePowerSupport N).card : ℝ) * Real.log (N : ℝ) := by
        rw [← Finset.sum_filter]
        calc
          (∑ _n ∈ (Finset.range (y + 1)).filter
              (fun n => n ∈ higherPrimePowerSupport N), Real.log (N : ℝ)) =
              (((Finset.range (y + 1)).filter
                (fun n => n ∈ higherPrimePowerSupport N)).card : ℝ) *
                Real.log (N : ℝ) := by simp
          _ ≤ ((higherPrimePowerSupport N).card : ℝ) * Real.log (N : ℝ) := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast Finset.card_le_card (by
                intro n hn
                exact (Finset.mem_filter.mp hn).2)
            · exact hlog
      _ ≤ ((N.sqrt + 1 : ℕ) : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast card_higherPrimePowerSupport_le N
        · exact hlog

  · have hNle : N ≤ 1 := by omega
    have hcorr : lambdaPrimePowerCorrection y q a = 0 := by
      rw [lambdaPrimePowerCorrection_eq_nonprime_sum]
      apply Finset.sum_eq_zero
      intro n hn
      have hn1 : n ≤ 1 :=
        (Nat.le_of_lt_succ (Finset.mem_range.mp hn)).trans (hy.trans hNle)
      have hΛ : ArithmeticFunction.vonMangoldt n = 0 := by
        interval_cases n
        · exact vonMangoldt_zero_local
        · exact ArithmeticFunction.vonMangoldt_apply_one
      simp [lambdaNatCoeff, hΛ]
    rw [hcorr, norm_zero]
    interval_cases N <;> norm_num

/-- The same bound for the maximum over `y ≤ N` and reduced residues `a`. -/
theorem lambdaPrimePowerCorrectionPrefixMaxError_le_explicit (N q : ℕ) :
    lambdaPrimePowerCorrectionPrefixMaxError N q ≤
      ((N.sqrt + 1 : ℕ) : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) := by
  unfold lambdaPrimePowerCorrectionPrefixMaxError
  apply Finset.max'_le
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_image] at hz
  rcases hz with rfl | ⟨p, hp, rfl⟩
  · positivity
  · rcases Finset.mem_product.mp hp with ⟨hy, ha⟩
    exact norm_lambdaPrimePowerCorrection_le_explicit
      (Nat.le_of_lt_succ (Finset.mem_range.mp hy))

/-- The bound `(√N + 1)(log₂ N + 1) log N` for `|ψ(y; q, a) - θ(y; q, a)|` with `y ≤ N`. -/
def primePowerCorrectionExplicitBound (N : ℕ) : ℝ :=
  ((N.sqrt + 1 : ℕ) : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ)

/-- Summed over `1 ≤ q ≤ Q`, the prime-power maxima are at most
`Q (√N + 1)(log₂ N + 1) log N`. -/
theorem sum_lambdaPrimePowerCorrectionPrefixMaxError_le
    (N Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, lambdaPrimePowerCorrectionPrefixMaxError N q) ≤
      (Q : ℝ) * primePowerCorrectionExplicitBound N := by
  calc
    _ ≤ ∑ _q ∈ Finset.Icc 1 Q, primePowerCorrectionExplicitBound N := by
      exact Finset.sum_le_sum fun q _ =>
        lambdaPrimePowerCorrectionPrefixMaxError_le_explicit N q
    _ = (Q : ℝ) * primePowerCorrectionExplicitBound N := by simp

/-! ## Error terms independent of the modulus -/

/-- The error terms that do not depend on `q`: `A(N) max_{y ≤ N} |ψ(y) - y| + E_li(N)`,
where `A(N)` is the maximum over `y ≤ N` of the total variation of the weights `1 / log n`
and `E_li(N) = max_{y ≤ N} |∑_{2 ≤ n ≤ y} 1/log n - li(y)|`. -/
def globalPartialSummationError (N : ℕ) : ℝ :=
  discreteAbelAmplifierPrefixMax N * principalLambdaPrefixMaxError N 1 +
    liDiscretePrefixMaxError N

/-- The statement that the `q`-independent error terms are `O_A(N / log^A N)`: for every
`A > 0` there is `C > 0` with `globalPartialSummationError N ≤ C N / (log N)^A` for all
large `N`. -/
def GlobalPartialSummationBound : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in Filter.atTop, 2 ≤ N →
        globalPartialSummationError N ≤
          C * (N : ℝ) / Real.log N ^ A

end

end BombieriVinogradov
