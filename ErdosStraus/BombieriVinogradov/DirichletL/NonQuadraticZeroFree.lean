import ErdosStraus.BombieriVinogradov.DirichletL.Bounds

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

section

/-!
# Zero-free region for nonquadratic Dirichlet L-functions

Let `χ` be a Dirichlet character mod `q` with `χ² ≠ 1` and put `M = q (⌊|t|⌋ + 1)`. Then
`L(β + it, χ) ≠ 0` for `1 - 1/(2³⁸ (1 + log M)⁹) ≤ β < 1`. The proof applies the `(3,4,1)`
inequality at `1 + x + it` and compares `L(1 + x + it, χ)` with `L(β + it, χ)` using
`|L'(σ + it, χ)| ≤ 64 (1 + log M)²`. We deduce a zero-free rectangle `[σ₀, 2] × [-T, T]` and a
lower bound for `|L(β + it, χ)|` in a slightly narrower region.
-/

open Complex Set

namespace BombieriVinogradov

open BombieriVinogradov.LValueBound
open BombieriVinogradov.LDerivBound
open BombieriVinogradov.WeakStripDifference

lemma dirichletLHeightBlock_two_mul_le (t : ℝ) :
    dirichletLHeightBlock (2 * t) ≤ 2 * dirichletLHeightBlock t := by
  have hfloor : (⌊|2 * t|⌋₊ : ℝ) ≤ |2 * t| := Nat.floor_le (abs_nonneg _)
  have habs : |2 * t| = 2 * |t| := by rw [abs_mul]; norm_num
  have ht := abs_lt_heightBlock t
  have hltR : (⌊|2 * t|⌋₊ : ℝ) < 2 * dirichletLHeightBlock t := by
    calc
      (⌊|2 * t|⌋₊ : ℝ) ≤ |2 * t| := hfloor
      _ = 2 * |t| := habs
      _ < 2 * dirichletLHeightBlock t := by nlinarith
  have hltN : ⌊|2 * t|⌋₊ < 2 * dirichletLHeightBlock t := by exact_mod_cast hltR
  simpa only [dirichletLHeightBlock] using (Nat.add_one_le_iff.mpr hltN)

/-- `M(q, 2t) ≤ M(q, t)²` for `M(q, t) = q (⌊|t|⌋ + 1)`. The character is used only to
know that `M(q, t) ≥ 2`. -/
lemma dirichletLConductorHeightCutoff_two_mul_le_sq
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    dirichletLConductorHeightCutoff q (2 * t) ≤
      (dirichletLConductorHeightCutoff q t) ^ 2 := by
  let m := dirichletLConductorHeightCutoff q t
  have hm : 2 ≤ m := two_le_conductorHeightCutoff χ hχ t
  have hblock := dirichletLHeightBlock_two_mul_le t
  have htwo : dirichletLConductorHeightCutoff q (2 * t) ≤ 2 * m := by
    dsimp only [m, dirichletLConductorHeightCutoff]
    nlinarith [Nat.mul_le_mul_left q hblock]
  calc
    dirichletLConductorHeightCutoff q (2 * t) ≤ 2 * m := htwo
    _ ≤ m ^ 2 := by nlinarith

/-- If `χ² ≠ 1` and `M = q (⌊|t|⌋ + 1)`, then `L(β + it, χ) ≠ 0` for
`1 - 1/(2³⁸ (1 + log M)⁹) ≤ β < 1`. -/
theorem norm_LFunction_ne_zero_of_nonquadratic_conductorLog
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχsq : χ ^ 2 ≠ 1)
    {β t : ℝ}
    (hβ : β ∈ Set.Ico
      (1 - 1 / (274877906944 *
        (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 9)) 1) :
    χ.LFunction (β + I * t) ≠ 0 := by
  let m : ℕ := dirichletLConductorHeightCutoff q t
  let L : ℝ := 1 + Real.log m
  let x : ℝ := 1 / (274877906944 * L ^ 9)
  have hχ : χ ≠ 1 := by
    intro h
    apply hχsq
    rw [h, one_pow]
  have hm : 2 ≤ m := by
    simpa only [m] using two_le_conductorHeightCutoff χ hχ t
  have hlogm : 0 < Real.log (m : ℝ) := by
    simpa only [m] using log_conductorHeightCutoff_pos χ hχ t
  have hL : 1 < L := by dsimp only [L]; linarith
  have hL0 : 0 < L := lt_trans zero_lt_one hL
  have hx : 0 < x := by dsimp only [x]; positivity
  have hxhalf : x ≤ 1 / 2 := by
    dsimp only [x]
    rw [div_le_iff₀ (show 0 < 274877906944 * L ^ 9 by positivity)]
    have hLpow : 1 ≤ L ^ 9 := one_le_pow₀ hL.le
    nlinarith
  have hxlog : x ≤ 1 / Real.log m := by
    apply one_div_le_one_div_of_le hlogm
    calc
      Real.log (m : ℝ) ≤ L := by dsimp only [L]; linarith
      _ = L ^ 1 := by ring
      _ ≤ L ^ 9 := pow_le_pow_right₀ hL.le (by norm_num)
      _ ≤ 274877906944 * L ^ 9 :=
        le_mul_of_one_le_left (pow_nonneg hL0.le 9) (by norm_num)
  have hσ : 1 < 1 + x := by linarith
  have hσtwo : 1 + x ≤ 2 := by linarith
  have hχsqvalue :
      ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖ ≤ 64 * L := by
    let m₂ := dirichletLConductorHeightCutoff q (2 * t)
    have hm₂ : 2 ≤ m₂ := by
      simpa only [m₂] using two_le_conductorHeightCutoff (χ ^ 2) hχsq (2 * t)
    have hlogm₂ : 0 < Real.log (m₂ : ℝ) := Real.log_pos (by exact_mod_cast hm₂)
    have hm₂m : m₂ ≤ m ^ 2 := by
      simpa only [m₂, m] using
        dirichletLConductorHeightCutoff_two_mul_le_sq χ hχ t
    have hlogle : Real.log (m₂ : ℝ) ≤ 2 * Real.log (m : ℝ) := by
      calc
        Real.log (m₂ : ℝ) ≤ Real.log ((m : ℕ) ^ 2 : ℕ) :=
          Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hm₂))
            (by exact_mod_cast hm₂m)
        _ = 2 * Real.log (m : ℝ) := by
          push_cast
          rw [Real.log_pow]
          norm_num
    have hnear₂ : 1 - 1 / Real.log m₂ ≤ 1 + x := by
      have : 0 < 1 / Real.log m₂ := one_div_pos.mpr hlogm₂
      linarith
    have hv :=
      norm_LFunction_le_one_add_log
        (χ ^ 2) hχsq (σ := 1 + x) (t := 2 * t)
        (by linarith) hσtwo (by simpa only [m₂] using hnear₂)
    calc
      ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖
          ≤ 32 * (1 + Real.log m₂) := by
            convert hv using 1; push_cast; ring
      _ ≤ 64 * L := by
        dsimp only [L]
        nlinarith
  have htriv : ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ≤ 2 / x := by
    rw [DirichletCharacter.LFunctionTrivChar]
    calc
      ‖(1 : DirichletCharacter ℂ q).LFunction (1 + x)‖ ≤ 1 + 1 / x := by
        convert norm_dirichletLFunction_le
          (1 : DirichletCharacter ℂ q) (1 + x) 0 hσ using 1 <;> norm_num
      _ ≤ 2 / x := by
        rw [le_div_iff₀ hx]
        field_simp [ne_of_gt hx]
        linarith
  have hprod : 1 ≤
      ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ^ 3 *
        ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
        ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖ := by
    have hp := χ.norm_LFunction_product_ge_one hx t
    convert (show 1 ≤
        ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ^ 3 *
          ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
          ‖(χ ^ 2).LFunction (1 + x + 2 * I * t)‖ by
        simpa only [norm_mul, norm_pow] using hp) using 1; ring_nf
  have hmajor : 1 ≤
      (2 / x) ^ 3 * ‖χ.LFunction (1 + x + I * t)‖ ^ 4 * (64 * L) := by
    calc
      1 ≤ ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ^ 3 *
          ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
          ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖ := hprod
      _ ≤ (2 / x) ^ 3 * ‖χ.LFunction (1 + x + I * t)‖ ^ 4 * (64 * L) := by
        gcongr
  have hlower : x ^ 3 ≤ 512 * L * ‖χ.LFunction (1 + x + I * t)‖ ^ 4 := by
    have hs := mul_le_mul_of_nonneg_left hmajor (pow_nonneg hx.le 3)
    calc
      x ^ 3 = x ^ 3 * 1 := by ring
      _ ≤ x ^ 3 * ((2 / x) ^ 3 *
          ‖χ.LFunction (1 + x + I * t)‖ ^ 4 * (64 * L)) := hs
      _ = 512 * L * ‖χ.LFunction (1 + x + I * t)‖ ^ 4 := by
        field_simp [ne_of_gt hx]
        ring
  intro hzero
  have hβleft : 1 - x ≤ β := by simpa only [x, L, m] using hβ.1
  have hβlower : 1 / 2 ≤ β := by linarith
  have hβright : β < 1 + x := by linarith [hβ.2]
  have hdiff :
      ‖χ.LFunction (((1 + x : ℝ) : ℂ) + t * I) -
          χ.LFunction ((β : ℂ) + t * I)‖ ≤
        (64 * L ^ 2) * (1 + x - β) := by
    rw [← integral_deriv_LFunction_eq_sub χ hχ β (1 + x) t]
    convert intervalIntegral.norm_integral_le_of_norm_le_const ?_ using 1
    · congr
      rw [_root_.abs_of_nonneg (sub_nonneg.mpr hβright.le)]
    · intro σ hσpath
      rw [uIoc_of_le hβright.le, mem_Ioc] at hσpath
      have hnear : 1 - 1 / Real.log m ≤ σ := by
        have : 1 - 1 / Real.log m ≤ 1 - x := by linarith
        exact this.trans (hβleft.trans hσpath.1.le)
      have hd :=
        norm_deriv_LFunction_le_one_add_log_sq
          χ hχ (σ := σ) (t := t)
          (hβlower.trans hσpath.1.le) (hσpath.2.trans hσtwo)
          (by simpa only [m] using hnear)
      convert hd using 1; ring_nf
  have hright : ‖χ.LFunction (1 + x + I * t)‖ ≤ 128 * L ^ 2 * x := by
    have hzero' : χ.LFunction (β + t * I) = 0 := by
      convert hzero using 1; ring_nf
    rw [hzero', sub_zero] at hdiff
    have harg : (((1 + x : ℝ) : ℂ) + t * I) = 1 + x + I * t := by
      push_cast
      ring
    rw [harg] at hdiff
    calc
      ‖χ.LFunction (1 + x + I * t)‖ ≤ (64 * L ^ 2) * (1 + x - β) := hdiff
      _ ≤ (64 * L ^ 2) * (2 * x) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 128 * L ^ 2 * x := by ring
  have hcontr : x ^ 3 ≤ 512 * 128 ^ 4 * L ^ 9 * x ^ 4 := by
    calc
      x ^ 3 ≤ 512 * L * ‖χ.LFunction (1 + x + I * t)‖ ^ 4 := hlower
      _ ≤ 512 * L * (128 * L ^ 2 * x) ^ 4 := by gcongr
      _ = 512 * 128 ^ 4 * L ^ 9 * x ^ 4 := by ring
  have hpay : 512 * 128 ^ 4 * L ^ 9 * x ^ 4 = x ^ 3 / 2 := by
    dsimp only [x]
    field_simp [ne_of_gt hL0]
    ring
  rw [hpay] at hcontr
  have hx3 : 0 < x ^ 3 := pow_pos hx 3
  linarith

end BombieriVinogradov

end

section

/-!
## A zero-free rectangle

For `|t| ≤ T` the cutoff `q (⌊|t|⌋ + 1)` is at most `q (⌊T⌋ + 1)`, so the region above contains
a rectangle `[σ₀, 2] × [-T, T]` with `σ₀` depending only on `q` and `T`.
-/

open Complex Set

namespace BombieriVinogradov

open BombieriVinogradov.LValueBound

/-- `⌊T⌋ + 1`, an upper bound for `⌊|t|⌋ + 1` when `|t| ≤ T`. -/
noncomputable def dirichletLNonquadraticConductorLogHeightBlock (T : ℝ) : ℕ :=
  ⌊T⌋₊ + 1

/-- `M(q, T) = q (⌊T⌋ + 1)`, an upper bound for `q (⌊|t|⌋ + 1)` when `|t| ≤ T`. -/
noncomputable def dirichletLNonquadraticConductorLogCutoff (q : ℕ) (T : ℝ) : ℕ :=
  q * dirichletLNonquadraticConductorLogHeightBlock T

/-- `σ₀ = 1 - 1/(2³⁸ (1 + log M)⁹)` with `M = q (⌊T⌋ + 1)`. -/
noncomputable def dirichletLNonquadraticConductorLogLeftEdge (q : ℕ) (T : ℝ) : ℝ :=
  1 - 1 / (274877906944 *
    (1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)) ^ 9)

/-- The closed rectangle `[σ₀, 2] × [-T, T]`, with corners `σ₀ - iT` and `2 + iT`. -/
def dirichletLNonquadraticConductorLogRectangle (q : ℕ) (T : ℝ) : Set ℂ :=
  ((dirichletLNonquadraticConductorLogLeftEdge q T : ℂ) - I * T).Rectangle
    (2 + I * T)

lemma dirichletLHeightBlock_le_fixedHeightBlock {t T : ℝ} (ht : |t| ≤ T) :
    dirichletLHeightBlock t ≤ dirichletLNonquadraticConductorLogHeightBlock T := by
  unfold dirichletLHeightBlock dirichletLNonquadraticConductorLogHeightBlock
  exact Nat.add_le_add_right (Nat.floor_mono ht) 1

lemma dirichletLConductorHeightCutoff_le_fixedHeightCutoff
    {q : ℕ} {t T : ℝ} (ht : |t| ≤ T) :
    dirichletLConductorHeightCutoff q t ≤
      dirichletLNonquadraticConductorLogCutoff q T := by
  unfold dirichletLConductorHeightCutoff dirichletLNonquadraticConductorLogCutoff
  exact Nat.mul_le_mul_left q (dirichletLHeightBlock_le_fixedHeightBlock ht)

lemma four_le_dirichletLNonquadraticConductorLogCutoff
    {q : ℕ} [NeZero q] {T : ℝ} (hT : 3 ≤ T) :
    4 ≤ dirichletLNonquadraticConductorLogCutoff q T := by
  have hfloor : 3 ≤ ⌊T⌋₊ := Nat.le_floor hT
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  unfold dirichletLNonquadraticConductorLogCutoff
  have hblock : 4 ≤ dirichletLNonquadraticConductorLogHeightBlock T := by
    unfold dirichletLNonquadraticConductorLogHeightBlock
    omega
  nlinarith

theorem one_half_lt_dirichletLNonquadraticConductorLogLeftEdge
    {q : ℕ} [NeZero q] {T : ℝ} (hT : 3 ≤ T) :
    (1 / 2 : ℝ) < dirichletLNonquadraticConductorLogLeftEdge q T := by
  let M := dirichletLNonquadraticConductorLogCutoff q T
  let L : ℝ := 1 + Real.log M
  have hM : 4 ≤ M := by
    simpa only [M] using four_le_dirichletLNonquadraticConductorLogCutoff hT
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hL : 1 < L := by dsimp only [L]; linarith
  have hLpow : 1 ≤ L ^ 9 := one_le_pow₀ hL.le
  have hden : (2 : ℝ) < 274877906944 * L ^ 9 := by nlinarith
  have hwidth : 1 / (274877906944 * L ^ 9) < (1 / 2 : ℝ) :=
    one_div_lt_one_div_of_lt (by norm_num) hden
  dsimp only [dirichletLNonquadraticConductorLogLeftEdge, L, M] at hwidth ⊢
  linarith

/-- If `χ² ≠ 1` and `T ≥ 3`, then `L(s, χ)` has no zeros on the rectangle
`[σ₀, 2] × [-T, T]`. -/
theorem LFunction_ne_zero_on_nonquadratic_conductorLogRectangle
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ}
    (hχsq : χ ^ 2 ≠ 1) (hT : 3 ≤ T) :
    ∀ s ∈ dirichletLNonquadraticConductorLogRectangle q T, χ.LFunction s ≠ 0 := by
  intro s hs
  have hχ : χ ≠ 1 := by
    intro hχ
    apply hχsq
    rw [hχ, one_pow]
  have hcoords :
      s.re ∈ Set.uIcc (dirichletLNonquadraticConductorLogLeftEdge q T) 2 ∧
        s.im ∈ Set.uIcc (-T) T := by
    rw [dirichletLNonquadraticConductorLogRectangle, Complex.Rectangle,
      Complex.mem_reProdIm] at hs
    simpa using hs
  have hTnonneg : 0 ≤ T := by linarith
  have hleft : (1 / 2 : ℝ) < dirichletLNonquadraticConductorLogLeftEdge q T :=
    one_half_lt_dirichletLNonquadraticConductorLogLeftEdge hT
  have hM : 4 ≤ dirichletLNonquadraticConductorLogCutoff q T :=
    four_le_dirichletLNonquadraticConductorLogCutoff hT
  have hlogM : 0 < Real.log (dirichletLNonquadraticConductorLogCutoff q T : ℝ) :=
    Real.log_pos (by exact_mod_cast (show
      1 < dirichletLNonquadraticConductorLogCutoff q T by omega))
  have hleftOne : dirichletLNonquadraticConductorLogLeftEdge q T < 1 := by
    unfold dirichletLNonquadraticConductorLogLeftEdge
    have : 0 < 1 / (274877906944 *
        (1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)) ^ 9) := by
      positivity
    linarith
  rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hcoords
  by_cases hre : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) hre
  · have hrelt : s.re < 1 := lt_of_not_ge hre
    have himabs : |s.im| ≤ T := (abs_le).2 hcoords.2
    let m := dirichletLConductorHeightCutoff q s.im
    let M := dirichletLNonquadraticConductorLogCutoff q T
    let Lm : ℝ := 1 + Real.log m
    let LM : ℝ := 1 + Real.log M
    have hm : 2 ≤ m := by
      simpa only [m] using two_le_conductorHeightCutoff χ hχ s.im
    have hmM : m ≤ M := by
      simpa only [m, M] using
        dirichletLConductorHeightCutoff_le_fixedHeightCutoff himabs
    have hlogm : 0 < Real.log (m : ℝ) := by
      simpa only [m] using log_conductorHeightCutoff_pos χ hχ s.im
    have hlogle : Real.log (m : ℝ) ≤ Real.log (M : ℝ) :=
      Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hm))
        (by exact_mod_cast hmM)
    have hLm : 0 < Lm := by dsimp only [Lm]; linarith
    have hLM : 0 < LM := by dsimp only [LM]; linarith
    have hpowle : Lm ^ 9 ≤ LM ^ 9 := by
      apply pow_le_pow_left₀ hLm.le
      · dsimp only [Lm, LM]
        linarith
    have hdenle : 274877906944 * Lm ^ 9 ≤ 274877906944 * LM ^ 9 := by
      gcongr
    have hlocalden : 0 < (274877906944 : ℝ) * Lm ^ 9 := by positivity
    have hwidth : 1 / (274877906944 * LM ^ 9) ≤
        1 / (274877906944 * Lm ^ 9) :=
      one_div_le_one_div_of_le hlocalden hdenle
    have hsre : s.re ∈ Set.Ico
        (1 - 1 / (274877906944 *
          (1 + Real.log (dirichletLConductorHeightCutoff q s.im)) ^ 9)) 1 := by
      refine ⟨?_, hrelt⟩
      have hfixed := (sub_le_sub_left hwidth 1).trans hcoords.1.1
      simpa only [dirichletLNonquadraticConductorLogLeftEdge, LM, Lm, M, m] using hfixed
    have hzero := norm_LFunction_ne_zero_of_nonquadratic_conductorLog χ hχsq hsre
    have hsrepr : ((s.re : ℂ) + I * s.im) = s := by
      apply Complex.ext <;> simp
    simpa only [hsrepr] using hzero

/-- If `χ² ≠ 1` and `T ≥ 3`, then `L'(s, χ)/L(s, χ)` is holomorphic on `[σ₀, 2] × [-T, T]`. -/
theorem logDerivative_holomorphicOn_nonquadratic
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ}
    (hχsq : χ ^ 2 ≠ 1) (hT : 3 ≤ T) :
    HolomorphicOn (fun s => deriv χ.LFunction s / χ.LFunction s)
      (dirichletLNonquadraticConductorLogRectangle q T) := by
  have hχ : χ ≠ 1 := by
    intro hχ
    apply hχsq
    rw [hχ, one_pow]
  have hL : Differentiable ℂ χ.LFunction :=
    DirichletCharacter.differentiable_LFunction hχ
  exact hL.deriv.differentiableOn.div hL.differentiableOn
    (LFunction_ne_zero_on_nonquadratic_conductorLogRectangle χ hχsq hT)

end BombieriVinogradov

end

section

/-!
## A lower bound for `|L(β + it, χ)|`

The argument above, run with the narrower width `x = 1/(2⁴² (1 + log M)⁹)`, shows that
`|L(β + it, χ)|` is at least `128 (1 + log M)² x = 1/(2³⁵ (1 + log M)⁷)` for `1 - x ≤ β < 1`.
-/

open Complex Set

namespace BombieriVinogradov

open BombieriVinogradov.LValueBound
open BombieriVinogradov.LDerivBound
open BombieriVinogradov.WeakStripDifference

private lemma nonquadraticConductorLogWidth_bounds {m : ℕ}
    (hlogm : 0 < Real.log (m : ℝ)) :
    let L : ℝ := 1 + Real.log m
    let x : ℝ := 1 / (4398046511104 * L ^ 9)
    0 < x ∧ x ≤ 1 / 2 ∧ x ≤ 1 / Real.log m := by
  let L : ℝ := 1 + Real.log m
  have hL : 1 < L := by dsimp only [L]; linarith only [hlogm]
  have hL0 : 0 < L := lt_trans zero_lt_one hL
  have hLpow : 1 ≤ L ^ 9 := one_le_pow₀ hL.le
  have hden : L ≤ 4398046511104 * L ^ 9 := by
    calc
      L = L ^ 1 := by ring
      _ ≤ L ^ 9 := pow_le_pow_right₀ hL.le (by norm_num)
      _ ≤ 4398046511104 * L ^ 9 :=
        le_mul_of_one_le_left (pow_nonneg hL0.le 9) (by norm_num)
  refine ⟨by positivity, ?_, ?_⟩
  · apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
    change 2 ≤ 4398046511104 * L ^ 9
    linarith only [hLpow]
  · apply one_div_le_one_div_of_le hlogm
    change Real.log (m : ℝ) ≤ 4398046511104 * L ^ 9
    have hlogL : Real.log (m : ℝ) ≤ L := by dsimp only [L]; linarith
    exact hlogL.trans hden

/-- If `χ² ≠ 1`, `M = q (⌊|t|⌋ + 1)` and `x = 1/(2⁴² (1 + log M)⁹)`, then
`|L(β + it, χ)| ≥ 128 (1 + log M)² x` for `1 - x ≤ β < 1`. -/
theorem norm_LFunction_lower_of_nonquadratic_conductorLog
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχsq : χ ^ 2 ≠ 1)
    {β t : ℝ}
    (hβ : β ∈ Set.Ico
      (1 - 1 / (4398046511104 *
        (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 9)) 1) :
    128 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 *
        (1 / (4398046511104 *
          (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 9)) ≤
      ‖χ.LFunction (β + I * t)‖ := by
  let m : ℕ := dirichletLConductorHeightCutoff q t
  let L : ℝ := 1 + Real.log m
  let x : ℝ := 1 / (4398046511104 * L ^ 9)
  have hχ : χ ≠ 1 := by
    intro h
    apply hχsq
    rw [h, one_pow]
  have hm : 2 ≤ m := by
    simpa only [m] using two_le_conductorHeightCutoff χ hχ t
  have hlogm : 0 < Real.log (m : ℝ) := by
    simpa only [m] using log_conductorHeightCutoff_pos χ hχ t
  have hL : 1 < L := by dsimp only [L]; linarith
  have hL0 : 0 < L := lt_trans zero_lt_one hL
  have hwidth := nonquadraticConductorLogWidth_bounds hlogm
  have hx : 0 < x := hwidth.1
  have hxhalf : x ≤ 1 / 2 := hwidth.2.1
  have hxlog : x ≤ 1 / Real.log m := hwidth.2.2
  have hσ : 1 < 1 + x := by linarith
  have hσtwo : 1 + x ≤ 2 := by linarith
  have hχsqvalue :
      ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖ ≤ 64 * L := by
    let m₂ := dirichletLConductorHeightCutoff q (2 * t)
    have hm₂ : 2 ≤ m₂ := by
      simpa only [m₂] using two_le_conductorHeightCutoff (χ ^ 2) hχsq (2 * t)
    have hlogm₂ : 0 < Real.log (m₂ : ℝ) := Real.log_pos (by exact_mod_cast hm₂)
    have hm₂m : m₂ ≤ m ^ 2 := by
      simpa only [m₂, m] using
        dirichletLConductorHeightCutoff_two_mul_le_sq χ hχ t
    have hlogle : Real.log (m₂ : ℝ) ≤ 2 * Real.log (m : ℝ) := by
      calc
        Real.log (m₂ : ℝ) ≤ Real.log ((m : ℕ) ^ 2 : ℕ) :=
          Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hm₂))
            (by exact_mod_cast hm₂m)
        _ = 2 * Real.log (m : ℝ) := by
          push_cast
          rw [Real.log_pow]
          norm_num
    have hnear₂ : 1 - 1 / Real.log m₂ ≤ 1 + x := by
      have : 0 < 1 / Real.log m₂ := one_div_pos.mpr hlogm₂
      linarith
    have hv :=
      norm_LFunction_le_one_add_log
        (χ ^ 2) hχsq (σ := 1 + x) (t := 2 * t)
        (by linarith) hσtwo (by simpa only [m₂] using hnear₂)
    calc
      ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖
          ≤ 32 * (1 + Real.log m₂) := by
            convert hv using 1; push_cast; ring
      _ ≤ 64 * L := by
        dsimp only [L]
        nlinarith
  have htriv : ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ≤ 2 / x := by
    rw [DirichletCharacter.LFunctionTrivChar]
    calc
      ‖(1 : DirichletCharacter ℂ q).LFunction (1 + x)‖ ≤ 1 + 1 / x := by
        convert norm_dirichletLFunction_le
          (1 : DirichletCharacter ℂ q) (1 + x) 0 hσ using 1 <;> norm_num
      _ ≤ 2 / x := by
        rw [le_div_iff₀ hx]
        field_simp [ne_of_gt hx]
        linarith
  have hprod : 1 ≤
      ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ^ 3 *
        ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
        ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖ := by
    have hp := χ.norm_LFunction_product_ge_one hx t
    convert (show 1 ≤
        ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ^ 3 *
          ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
          ‖(χ ^ 2).LFunction (1 + x + 2 * I * t)‖ by
        simpa only [norm_mul, norm_pow] using hp) using 1; ring_nf
  have hmajor : 1 ≤
      (2 / x) ^ 3 * ‖χ.LFunction (1 + x + I * t)‖ ^ 4 * (64 * L) := by
    calc
      1 ≤ ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ^ 3 *
          ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
          ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖ := hprod
      _ ≤ (2 / x) ^ 3 * ‖χ.LFunction (1 + x + I * t)‖ ^ 4 * (64 * L) := by
        gcongr
  have hlower : x ^ 3 ≤ 512 * L * ‖χ.LFunction (1 + x + I * t)‖ ^ 4 := by
    have hs := mul_le_mul_of_nonneg_left hmajor (pow_nonneg hx.le 3)
    calc
      x ^ 3 = x ^ 3 * 1 := by ring
      _ ≤ x ^ 3 * ((2 / x) ^ 3 *
          ‖χ.LFunction (1 + x + I * t)‖ ^ 4 * (64 * L)) := hs
      _ = 512 * L * ‖χ.LFunction (1 + x + I * t)‖ ^ 4 := by
        field_simp [ne_of_gt hx]
        ring
  have hβleft : 1 - x ≤ β := by simpa only [x, L, m] using hβ.1
  have hβlower : 1 / 2 ≤ β := by linarith
  have hβright : β < 1 + x := by linarith [hβ.2]
  have hdiff :
      ‖χ.LFunction (((1 + x : ℝ) : ℂ) + t * I) -
          χ.LFunction ((β : ℂ) + t * I)‖ ≤
        (64 * L ^ 2) * (1 + x - β) := by
    rw [← integral_deriv_LFunction_eq_sub χ hχ β (1 + x) t]
    convert intervalIntegral.norm_integral_le_of_norm_le_const ?_ using 1
    · congr
      rw [_root_.abs_of_nonneg (sub_nonneg.mpr hβright.le)]
    · intro σ hσpath
      rw [uIoc_of_le hβright.le, mem_Ioc] at hσpath
      have hnear : 1 - 1 / Real.log m ≤ σ := by
        have : 1 - 1 / Real.log m ≤ 1 - x := by linarith
        exact this.trans (hβleft.trans hσpath.1.le)
      have hd :=
        norm_deriv_LFunction_le_one_add_log_sq
          χ hχ (σ := σ) (t := t)
          (hβlower.trans hσpath.1.le) (hσpath.2.trans hσtwo)
          (by simpa only [m] using hnear)
      convert hd using 1; ring_nf
  have hdiff' :
      ‖χ.LFunction (1 + x + I * t) - χ.LFunction (β + I * t)‖ ≤
        128 * L ^ 2 * x := by
    have harg₁ : (((1 + x : ℝ) : ℂ) + t * I) = 1 + x + I * t := by
      push_cast
      ring
    have hargβ : ((β : ℂ) + t * I) = β + I * t := by
      ring
    rw [harg₁, hargβ] at hdiff
    calc
      _ ≤ (64 * L ^ 2) * (1 + x - β) := hdiff
      _ ≤ (64 * L ^ 2) * (2 * x) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 128 * L ^ 2 * x := by ring
  change 128 * L ^ 2 * x ≤ ‖χ.LFunction (β + I * t)‖
  by_contra hnot
  have hleft : ‖χ.LFunction (β + I * t)‖ < 128 * L ^ 2 * x := lt_of_not_ge hnot
  have hright : ‖χ.LFunction (1 + x + I * t)‖ < 256 * L ^ 2 * x := by
    calc
      ‖χ.LFunction (1 + x + I * t)‖ ≤
          ‖χ.LFunction (1 + x + I * t) - χ.LFunction (β + I * t)‖ +
            ‖χ.LFunction (β + I * t)‖ := by
              simpa only [sub_add_cancel] using norm_add_le
                (χ.LFunction (1 + x + I * t) - χ.LFunction (β + I * t))
                (χ.LFunction (β + I * t))
      _ < 128 * L ^ 2 * x + 128 * L ^ 2 * x := add_lt_add_of_le_of_lt hdiff' hleft
      _ = 256 * L ^ 2 * x := by ring
  have hpow : ‖χ.LFunction (1 + x + I * t)‖ ^ 4 <
      (256 * L ^ 2 * x) ^ 4 :=
    pow_lt_pow_left₀ hright (norm_nonneg _) (by norm_num)
  have hcontr : x ^ 3 < 512 * 256 ^ 4 * L ^ 9 * x ^ 4 := by
    calc
      x ^ 3 ≤ 512 * L * ‖χ.LFunction (1 + x + I * t)‖ ^ 4 := hlower
      _ < 512 * L * (256 * L ^ 2 * x) ^ 4 :=
        mul_lt_mul_of_pos_left hpow (by positivity)
      _ = 512 * 256 ^ 4 * L ^ 9 * x ^ 4 := by ring
  have hpay : 512 * 256 ^ 4 * L ^ 9 * x ^ 4 = x ^ 3 / 2 := by
    dsimp only [x]
    field_simp [ne_of_gt hL0]
    ring
  rw [hpay] at hcontr
  have hx3 : 0 < x ^ 3 := pow_pos hx 3
  linarith

end BombieriVinogradov

end
