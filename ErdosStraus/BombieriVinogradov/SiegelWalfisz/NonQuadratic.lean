import ErdosStraus.BombieriVinogradov.SiegelWalfisz.SmoothedPerron
import ErdosStraus.BombieriVinogradov.DirichletL.NonQuadraticZeroFree
import ErdosStraus.BombieriVinogradov.Reduction.ConductorSplit

/-
Adapted from goldbach-lean (https://github.com/subfish-zhou/goldbach-lean, commit 9d4c3a4),
Copyright 2026 UyNewNas, released under the Apache License 2.0. Modified: reduced to the
proof of the Bombieri–Vinogradov theorem, reorganized, renamed and recommented.
-/

/-!
# Siegel–Walfisz bound for characters with `χ² ≠ 1`

Let `χ` be a Dirichlet character mod `q` with `χ² ≠ 1` and `q ≤ (log N)^C`. We prove
`|∑_{n ≤ y} Λ(n) χ(n)| ≤ K N / (log N)^D` uniformly for `y ≤ N`. The smoothed Perron
integral is shifted to the line `Re s = 1 - w/4` with `w = 1 / (2^42 (1 + log M)^9)` and
`M = q (⌊T⌋ + 1)`, which lies to the right of every zero of `L(s, χ)` with `|Im s| ≤ T`.
The height `T`, the smoothing width `ε` and the distance `d` of the right edge from `1` are
powers of `log N`.
-/

/-! ## Holomorphy on the rectangle -/

section

open Set Function Filter Complex Real MeasureTheory

namespace BombieriVinogradov

open BombieriVinogradov.LValueBound

/-- The conductor-height cutoff `M(q, T) = q (⌊T⌋ + 1)`. -/
noncomputable def dirichletLTwistedSmoothedConductorLogCutoff (q : ℕ) (T : ℝ) : ℕ :=
  dirichletLNonquadraticConductorLogCutoff q T

/-- The quantity `1 + log M(q, T)`. -/
noncomputable def dirichletLTwistedSmoothedConductorLogLM (q : ℕ) (T : ℝ) : ℝ :=
  1 + Real.log (dirichletLTwistedSmoothedConductorLogCutoff q T)

/-- The left edge `1 - 1 / (2^42 (1 + log M)^9)`. -/
noncomputable def dirichletLTwistedSmoothedConductorLogLeftEdge
    (q : ℕ) (T : ℝ) : ℝ :=
  1 - 1 / (4398046511104 *
    (dirichletLTwistedSmoothedConductorLogLM q T) ^ 9)

/-- The closed rectangle with real part between the left edge and `2` and imaginary part
in `[-T, T]`. -/
def dirichletLTwistedSmoothedConductorLogRectangle (q : ℕ) (T : ℝ) : Set ℂ :=
  ((dirichletLTwistedSmoothedConductorLogLeftEdge q T : ℂ) - I * T).Rectangle
    (2 + I * T)

private theorem one_lt_conductorLogLM
    {q : ℕ} [NeZero q] {T : ℝ} (hT : 3 ≤ T) :
    1 < dirichletLTwistedSmoothedConductorLogLM q T := by
  have hM : 4 ≤ dirichletLTwistedSmoothedConductorLogCutoff q T := by
    simpa only [dirichletLTwistedSmoothedConductorLogCutoff] using
      four_le_dirichletLNonquadraticConductorLogCutoff hT
  have hlogM : 0 < Real.log (dirichletLTwistedSmoothedConductorLogCutoff q T : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < dirichletLTwistedSmoothedConductorLogCutoff q T by omega))
  dsimp only [dirichletLTwistedSmoothedConductorLogLM]
  linarith only [hlogM]

theorem one_half_lt_dirichletLTwistedSmoothedConductorLogLeftEdge
    {q : ℕ} [NeZero q] {T : ℝ} (hT : 3 ≤ T) :
    (1 / 2 : ℝ) < dirichletLTwistedSmoothedConductorLogLeftEdge q T := by
  let M := dirichletLTwistedSmoothedConductorLogCutoff q T
  let LM : ℝ := 1 + Real.log M
  have hLM : 1 < LM := one_lt_conductorLogLM hT
  have hLMpow : 1 ≤ LM ^ 9 := one_le_pow₀ hLM.le
  have hden : (2 : ℝ) < 4398046511104 * LM ^ 9 := by nlinarith
  have hwidth : 1 / (4398046511104 * LM ^ 9) < (1 / 2 : ℝ) :=
    one_div_lt_one_div_of_lt (by norm_num) hden
  dsimp only [dirichletLTwistedSmoothedConductorLogLeftEdge,
    dirichletLTwistedSmoothedConductorLogLM, LM, M] at hwidth ⊢
  linarith

theorem dirichletLTwistedSmoothedConductorLogLeftEdge_lt_one
    {q : ℕ} [NeZero q] {T : ℝ} (hT : 3 ≤ T) :
    dirichletLTwistedSmoothedConductorLogLeftEdge q T < 1 := by
  let M := dirichletLTwistedSmoothedConductorLogCutoff q T
  let LM : ℝ := 1 + Real.log M
  have hLM : 0 < LM := zero_lt_one.trans (one_lt_conductorLogLM hT)
  have hwidth : 0 < 1 / (4398046511104 * LM ^ 9) := by positivity
  dsimp only [dirichletLTwistedSmoothedConductorLogLeftEdge,
    dirichletLTwistedSmoothedConductorLogLM, LM, M]
  linarith

/-- The rectangle lies inside the zero-free rectangle for `χ² ≠ 1`, whose left edge is
`1 - 1 / (2^38 (1 + log M)^9)`. -/
theorem dirichletLTwistedSmoothedConductorLogRectangle_subset
    (q : ℕ) [NeZero q] (T : ℝ) (hT : 3 ≤ T) :
    dirichletLTwistedSmoothedConductorLogRectangle q T ⊆
      dirichletLNonquadraticConductorLogRectangle q T := by
  let M := dirichletLTwistedSmoothedConductorLogCutoff q T
  let LM : ℝ := 1 + Real.log M
  have hLM : 0 < LM := zero_lt_one.trans (one_lt_conductorLogLM hT)
  have hnewDen : 0 < (4398046511104 : ℝ) * LM ^ 9 := by positivity
  have holdDen : 0 < (274877906944 : ℝ) * LM ^ 9 := by positivity
  have hdenle : (274877906944 : ℝ) * LM ^ 9 ≤ 4398046511104 * LM ^ 9 := by
    nlinarith [pow_pos hLM 9]
  have hwidth : 1 / (4398046511104 * LM ^ 9) ≤
      1 / (274877906944 * LM ^ 9) :=
    one_div_le_one_div_of_le holdDen hdenle
  have hedges : dirichletLNonquadraticConductorLogLeftEdge q T ≤
      dirichletLTwistedSmoothedConductorLogLeftEdge q T := by
    dsimp only [dirichletLNonquadraticConductorLogLeftEdge,
      dirichletLTwistedSmoothedConductorLogLeftEdge,
      dirichletLTwistedSmoothedConductorLogLM, LM, M,
      dirichletLTwistedSmoothedConductorLogCutoff] at hwidth ⊢
    linarith
  have hnewTwo : dirichletLTwistedSmoothedConductorLogLeftEdge q T ≤ 2 := by
    linarith [dirichletLTwistedSmoothedConductorLogLeftEdge_lt_one
      (q := q) (T := T) hT]
  have holdTwo : dirichletLNonquadraticConductorLogLeftEdge q T ≤ 2 :=
    hedges.trans hnewTwo
  intro s hs
  rw [dirichletLTwistedSmoothedConductorLogRectangle, Complex.Rectangle,
    Complex.mem_reProdIm] at hs
  norm_num at hs
  rw [Set.uIcc_of_le hnewTwo] at hs
  rw [dirichletLNonquadraticConductorLogRectangle, Complex.Rectangle,
    Complex.mem_reProdIm]
  norm_num
  rw [Set.uIcc_of_le holdTwo]
  exact ⟨⟨hedges.trans hs.1.1, hs.1.2⟩, hs.2⟩

theorem logDerivative_holomorphicOn_perronRectangle
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ}
    (hχsq : χ ^ 2 ≠ 1) (hT : 3 ≤ T) :
    HolomorphicOn (fun s => deriv χ.LFunction s / χ.LFunction s)
      (dirichletLTwistedSmoothedConductorLogRectangle q T) :=
  (logDerivative_holomorphicOn_nonquadratic χ hχsq hT).mono
    (dirichletLTwistedSmoothedConductorLogRectangle_subset q T hT)

/-- If `χ² ≠ 1`, the smoothed Perron integrand `-(L'/L)(s, χ) 𝓜(ν_ε)(s) X^s` is
holomorphic on the rectangle. Here `ν_ε` is the indicator of `(0, 1]` smoothed by `ν` at
scale `ε`. -/
theorem perronIntegrand_holomorphicOn_nonquadratic
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ}
    (hχsq : χ ^ 2 ≠ 1) (hT : 3 ≤ T)
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {X : ℝ} (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) :
    HolomorphicOn (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
      (dirichletLTwistedSmoothedConductorLogRectangle q T) := by
  have hlog : HolomorphicOn
      (fun s => -deriv χ.LFunction s / χ.LFunction s)
      (dirichletLTwistedSmoothedConductorLogRectangle q T) := by
    rw [(by
      ext s
      simp only [Pi.neg_apply, neg_div] :
      (fun s => -deriv χ.LFunction s / χ.LFunction s) =
        -(fun s => deriv χ.LFunction s / χ.LFunction s))]
    exact (logDerivative_holomorphicOn_perronRectangle
      χ hχsq hT).neg
  apply DifferentiableOn.mul
  · apply DifferentiableOn.mul hlog
    intro s hs
    apply DifferentiableAt.differentiableWithinAt
    apply Smooth1MellinDifferentiable diffν suppν ⟨εpos, ε_lt_one⟩ νpos mass_one
    rw [dirichletLTwistedSmoothedConductorLogRectangle, Complex.Rectangle,
      Complex.mem_reProdIm] at hs
    norm_num at hs
    rw [Set.uIcc_of_le (by
      linarith [dirichletLTwistedSmoothedConductorLogLeftEdge_lt_one
        (q := q) (T := T) hT])] at hs
    have hedge : (1 / 2 : ℝ) <
        dirichletLTwistedSmoothedConductorLogLeftEdge q T :=
      one_half_lt_dirichletLTwistedSmoothedConductorLogLeftEdge
        (q := q) (T := T) hT
    exact lt_of_lt_of_le (by linarith : (0 : ℝ) <
      dirichletLTwistedSmoothedConductorLogLeftEdge q T) hs.1.1
  · intro s _
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.const_cpow (by fun_prop)
    left
    norm_cast
    exact ne_of_gt X_pos

end BombieriVinogradov

end

/-! ## The contour shift and the bound for `L'/L` -/

section

open Set Function Filter Complex Real MeasureTheory
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace BombieriVinogradov

open BombieriVinogradov.LValueBound
open BombieriVinogradov.LDerivBound

/-- The width `w = 1 / (2^42 (1 + log M)^9)`. -/
noncomputable def dirichletLTwistedSmoothedConductorLogEdgeWidth
    (q : ℕ) (T : ℝ) : ℝ :=
  1 / (4398046511104 * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 9)

/-- The left edge `1 - w/4` of the contour. -/
noncomputable def dirichletLTwistedSmoothedConductorLogFinalLeft
    (q : ℕ) (T : ℝ) : ℝ :=
  1 - dirichletLTwistedSmoothedConductorLogEdgeWidth q T / 4

/-- The right edge `1 + d` of the contour. -/
def dirichletLTwistedSmoothedConductorLogRight (d : ℝ) : ℝ := 1 + d

/-- The rectangle `[1 - w/4, 1 + d] × [-T, T]`. -/
def dirichletLTwistedSmoothedConductorLogEdgeRectangle
    (q : ℕ) (T d : ℝ) : Set ℂ :=
  ((dirichletLTwistedSmoothedConductorLogFinalLeft q T : ℂ) - I * T).Rectangle
    (dirichletLTwistedSmoothedConductorLogRight d + I * T)

private theorem edge_parameters
    {q : ℕ} [NeZero q] {T : ℝ} (hT : 3 ≤ T) :
    let LM := dirichletLTwistedSmoothedConductorLogLM q T
    let w := dirichletLTwistedSmoothedConductorLogEdgeWidth q T
    1 < LM ∧ 0 < w ∧ w ≤ 1 / 2 := by
  let M := dirichletLTwistedSmoothedConductorLogCutoff q T
  let LM := dirichletLTwistedSmoothedConductorLogLM q T
  let w := dirichletLTwistedSmoothedConductorLogEdgeWidth q T
  have hM : 4 ≤ M := by
    simpa only [M, dirichletLTwistedSmoothedConductorLogCutoff] using
      four_le_dirichletLNonquadraticConductorLogCutoff hT
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hLM : 1 < LM := by
    dsimp only [LM, dirichletLTwistedSmoothedConductorLogLM, M]
    linarith
  have hw : 0 < w := by
    dsimp only [w, dirichletLTwistedSmoothedConductorLogEdgeWidth]
    positivity
  have hw2 : w ≤ 1 / 2 := by
    dsimp only [w, dirichletLTwistedSmoothedConductorLogEdgeWidth]
    rw [div_le_iff₀ (show 0 < 4398046511104 * LM ^ 9 by positivity)]
    have hp : 1 ≤ LM ^ 9 := one_le_pow₀ hLM.le
    nlinarith
  exact ⟨hLM, hw, hw2⟩

theorem dirichletLTwistedSmoothedConductorLogEdgeRectangle_subset
    (q : ℕ) [NeZero q] (T d : ℝ) (hT : 3 ≤ T) (hd0 : 0 < d) (hd1 : d ≤ 1) :
    dirichletLTwistedSmoothedConductorLogEdgeRectangle q T d ⊆
      dirichletLTwistedSmoothedConductorLogRectangle q T := by
  obtain ⟨hLM, hw, hw2⟩ := edge_parameters (q := q) hT
  have hleft : dirichletLTwistedSmoothedConductorLogLeftEdge q T ≤
      dirichletLTwistedSmoothedConductorLogFinalLeft q T := by
    dsimp only [dirichletLTwistedSmoothedConductorLogLeftEdge,
      dirichletLTwistedSmoothedConductorLogLM,
      dirichletLTwistedSmoothedConductorLogFinalLeft]
    change 1 - dirichletLTwistedSmoothedConductorLogEdgeWidth q T ≤
      1 - dirichletLTwistedSmoothedConductorLogEdgeWidth q T / 4
    linarith
  have hfinalright : dirichletLTwistedSmoothedConductorLogFinalLeft q T ≤
      dirichletLTwistedSmoothedConductorLogRight d := by
    dsimp only [dirichletLTwistedSmoothedConductorLogFinalLeft,
      dirichletLTwistedSmoothedConductorLogRight]
    linarith
  have hright : dirichletLTwistedSmoothedConductorLogRight d ≤ 2 := by
    dsimp only [dirichletLTwistedSmoothedConductorLogRight]
    linarith
  have holdright : dirichletLTwistedSmoothedConductorLogLeftEdge q T ≤ 2 :=
    hleft.trans (hfinalright.trans hright)
  intro s hs
  rw [dirichletLTwistedSmoothedConductorLogEdgeRectangle, Complex.Rectangle,
    Complex.mem_reProdIm] at hs
  norm_num at hs
  rw [Set.uIcc_of_le hfinalright] at hs
  rw [dirichletLTwistedSmoothedConductorLogRectangle, Complex.Rectangle,
    Complex.mem_reProdIm]
  norm_num
  rw [Set.uIcc_of_le holdright]
  exact ⟨⟨hleft.trans hs.1.1, hs.1.2.trans hright⟩, hs.2⟩

theorem perronIntegrand_holomorphicOn_nonquadraticEdge
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T d : ℝ}
    (hχsq : χ ^ 2 ≠ 1) (hT : 3 ≤ T) (hd0 : 0 < d) (hd1 : d ≤ 1)
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {X : ℝ} (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) :
    HolomorphicOn (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
      (dirichletLTwistedSmoothedConductorLogEdgeRectangle q T d) :=
  (perronIntegrand_holomorphicOn_nonquadratic
    χ hχsq hT diffν νpos suppν mass_one X_pos εpos ε_lt_one).mono
      (dirichletLTwistedSmoothedConductorLogEdgeRectangle_subset
        q T d hT hd0 hd1)

/-- By Cauchy's theorem, the integral of the Perron integrand around the rectangle
vanishes. -/
theorem rectangleIntegral_perronIntegrand_eq_zero
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T d : ℝ}
    (hχsq : χ ^ 2 ≠ 1) (hT : 3 ≤ T) (hd0 : 0 < d) (hd1 : d ≤ 1)
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {X : ℝ} (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) :
    RectangleIntegral
      (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
      ((dirichletLTwistedSmoothedConductorLogFinalLeft q T : ℂ) - I * T)
      (dirichletLTwistedSmoothedConductorLogRight d + I * T) = 0 :=
  (perronIntegrand_holomorphicOn_nonquadraticEdge
    χ hχsq hT hd0 hd1 diffν νpos suppν mass_one X_pos εpos ε_lt_one).vanishesOnRectangle
      (by rfl)

/-- The contour shift: the right edge integral minus the left edge integral equals the
top edge integral minus the bottom edge integral. -/
theorem perronContourIdentity_nonquadratic
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T d : ℝ}
    (hχsq : χ ^ 2 ≠ 1) (hT : 3 ≤ T) (hd0 : 0 < d) (hd1 : d ≤ 1)
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {X : ℝ} (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) :
    VIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
        (dirichletLTwistedSmoothedConductorLogRight d) (-T) T -
      VIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
        (dirichletLTwistedSmoothedConductorLogFinalLeft q T) (-T) T =
      HIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
        (dirichletLTwistedSmoothedConductorLogFinalLeft q T)
          (dirichletLTwistedSmoothedConductorLogRight d) T -
      HIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
        (dirichletLTwistedSmoothedConductorLogFinalLeft q T)
          (dirichletLTwistedSmoothedConductorLogRight d) (-T) := by
  have hz := rectangleIntegral_perronIntegrand_eq_zero
    χ hχsq hT hd0 hd1 diffν νpos suppν mass_one X_pos εpos ε_lt_one
  norm_num [RectangleIntegral] at hz
  linear_combination hz

/-- For `σ > 1`, `|L(σ + it, χ)| ≥ (σ - 1) / σ`, since
`1 / L(s, χ) = ∑ μ(n) χ(n) n^(-s)`. -/
theorem norm_dirichletLFunction_ge_sub_one_div
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ t : ℝ} (hσ : 1 < σ) :
    (σ - 1) / σ ≤ ‖χ.LFunction (σ + I * t)‖ := by
  let s : ℂ := σ + I * t
  have hs : 1 < s.re := by
    dsimp only [s]
    norm_num
    exact hσ
  have hχsum : LSeriesSummable ↗χ s :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hμsum : LSeriesSummable ↗ArithmeticFunction.moebius s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hmul : LSeries ↗χ s *
      LSeries (↗χ * ↗ArithmeticFunction.moebius) s = 1 := by
    rw [← LSeries_convolution' hχsum (DirichletCharacter.LSeriesSummable_mul χ hμsum),
      DirichletCharacter.convolution_mul_moebius, LSeries_delta, Pi.one_apply]
  have hsum : LSeriesSummable (↗χ * ↗ArithmeticFunction.moebius) s :=
    DirichletCharacter.LSeriesSummable_mul χ hμsum
  have hnormsum : ‖LSeries (↗χ * ↗ArithmeticFunction.moebius) s‖ ≤
      1 + 1 / (σ - 1) := by
    have hnorm := norm_tsum_le_tsum_norm hsum.norm
    refine hnorm.trans ((hsum.norm).tsum_le_tsum (fun n => ?_)
      (Real.summable_nat_rpow.mpr (by linarith : -σ < -1)) |>.trans
        (tsum_nat_rpow_neg_le σ hσ))
    by_cases hn : n = 0
    · subst n
      simp [LSeries.term, Real.zero_rpow (by linarith : -σ ≠ 0)]
    · rw [LSeries.term, if_neg hn, norm_div,
        norm_natCast_cpow_of_re_ne_zero n (by
          dsimp only [s]
          norm_num
          linarith)]
      simp only [Pi.mul_apply, norm_mul]
      have hμ : |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
        rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]
      have hχ := χ.norm_le_one n
      norm_num [s]
      calc
        ‖χ n‖ * |((ArithmeticFunction.moebius n : ℤ) : ℝ)| / (n : ℝ) ^ σ
            ≤ 1 / (n : ℝ) ^ σ := by
              apply div_le_div_of_nonneg_right
              · simpa only [one_mul] using
                  (mul_le_mul hχ hμ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
              · positivity
        _ = (n : ℝ) ^ (-σ) := by
          rw [Real.rpow_neg (Nat.cast_nonneg n)]
          simp only [one_div]
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hprod : ‖LSeries ↗χ s‖ * ‖LSeries (↗χ * ↗ArithmeticFunction.moebius) s‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  have hσ0 : 0 < σ := lt_trans zero_lt_one hσ
  have hd : 0 < σ - 1 := sub_pos.mpr hσ
  have hmajor : 1 + 1 / (σ - 1) = σ / (σ - 1) := by field_simp; ring
  rw [hmajor] at hnormsum
  have hscaled := mul_le_mul_of_nonneg_left hnormsum (norm_nonneg (LSeries ↗χ s))
  rw [hprod] at hscaled
  have hscaled' : 1 ≤ ‖LSeries ↗χ s‖ * σ / (σ - 1) := by
    simpa only [mul_div_assoc] using hscaled
  have hscaled'' : σ - 1 ≤ ‖LSeries ↗χ s‖ * σ := by
    simpa only [one_mul] using (le_div_iff₀ hd).mp hscaled'
  rw [div_le_iff₀ hσ0]
  simpa only [mul_comm] using hscaled''

/-- On the rectangle `[1 - w/4, 1 + d] × [-T, T]`, `|L'/L(s, χ)| ≤ 2^51 (1 + log M)^11`.
For `σ ≤ 1 + w/4` this follows from the lower bound for `|L|` at `1 - w/4` and the bound
`|L'| ≤ 64 (1 + log M)^2` on a segment of length at most `w/2`. For `σ > 1 + w/4` it
follows from `|L(s, χ)| ≥ (σ - 1) / σ`. -/
theorem norm_logDeriv_LFunction_le_on_conductorLogEdgeRectangle
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T d η σ : ℝ}
    (hχsq : χ ^ 2 ≠ 1) (hT : 3 ≤ T) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hη : |η| ≤ T)
    (hσleft : dirichletLTwistedSmoothedConductorLogFinalLeft q T ≤ σ)
    (hσright : σ ≤ dirichletLTwistedSmoothedConductorLogRight d) :
    ‖deriv χ.LFunction (σ + I * η) / χ.LFunction (σ + I * η)‖ ≤
      2251799813685248 * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 := by
  let m := dirichletLConductorHeightCutoff q η
  let M := dirichletLTwistedSmoothedConductorLogCutoff q T
  let Lm : ℝ := 1 + Real.log m
  let LM : ℝ := 1 + Real.log M
  let w : ℝ := 1 / (4398046511104 * LM ^ 9)
  let a : ℝ := 1 - w / 4
  have hχ : χ ≠ 1 := by
    intro h
    apply hχsq
    rw [h, one_pow]
  have hm : 2 ≤ m := by
    simpa only [m] using two_le_conductorHeightCutoff χ hχ η
  have hM : 4 ≤ M := by
    simpa only [M, dirichletLTwistedSmoothedConductorLogCutoff] using
      four_le_dirichletLNonquadraticConductorLogCutoff hT
  have hmM : m ≤ M := by
    simpa only [m, M, dirichletLTwistedSmoothedConductorLogCutoff] using
      dirichletLConductorHeightCutoff_le_fixedHeightCutoff hη
  have hlogm : 0 < Real.log (m : ℝ) := by
    simpa only [m] using log_conductorHeightCutoff_pos χ hχ η
  have hlogle : Real.log (m : ℝ) ≤ Real.log (M : ℝ) :=
    Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hm))
      (by exact_mod_cast hmM)
  have hLm : 1 < Lm := by dsimp only [Lm]; linarith
  have hLM : 1 < LM := by dsimp only [LM]; linarith
  have hLmLM : Lm ≤ LM := by dsimp only [Lm, LM]; linarith
  have hw : 0 < w := by dsimp only [w]; positivity
  have hw2 : w ≤ 1 / 2 := by
    dsimp only [w]
    rw [div_le_iff₀ (show 0 < 4398046511104 * LM ^ 9 by positivity)]
    nlinarith [one_le_pow₀ hLM.le (n := 9)]
  have hxlog : 1 / (4398046511104 * Lm ^ 9) ≤ 1 / Real.log m := by
    have hlogLm : Real.log (m : ℝ) < Lm := by dsimp only [Lm]; linarith
    calc
      1 / (4398046511104 * Lm ^ 9) ≤ 1 / Lm := by
        rw [one_div_le_one_div (by positivity) (by positivity)]
        have hp : Lm ≤ Lm ^ 9 := by
          calc Lm = Lm ^ 1 := by ring
               _ ≤ Lm ^ 9 := pow_le_pow_right₀ hLm.le (by norm_num)
        nlinarith [pow_pos (by linarith : 0 < Lm) 9]
      _ ≤ 1 / Real.log m := one_div_le_one_div_of_le hlogm hlogLm.le
  have hwlocal : w ≤ 1 / (4398046511104 * Lm ^ 9) := by
    dsimp only [w]
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  have ha_def : a = dirichletLTwistedSmoothedConductorLogFinalLeft q T := by
    rfl
  have ha_half : 1 / 2 ≤ a := by dsimp only [a]; linarith
  have ha_one : a < 1 := by dsimp only [a]; linarith
  have ha_strip : a ∈ Set.Ico
      (1 - 1 / (4398046511104 * Lm ^ 9)) 1 := by
    refine ⟨?_, ha_one⟩
    dsimp only [a]
    linarith
  have hanchorRaw : 128 * Lm ^ 2 *
      (1 / (4398046511104 * Lm ^ 9)) ≤ ‖χ.LFunction (a + I * η)‖ := by
    simpa only [Lm, m] using
      norm_LFunction_lower_of_nonquadratic_conductorLog χ hχsq ha_strip
  have hinv7 : 1 / (4398046511104 * LM ^ 7) ≤
      1 / (4398046511104 * Lm ^ 7) := by
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  have hanchor : 128 * LM ^ 2 * w ≤ ‖χ.LFunction (a + I * η)‖ := by
    have hlocalId : 128 * Lm ^ 2 *
        (1 / (4398046511104 * Lm ^ 9)) =
        128 * (1 / (4398046511104 * Lm ^ 7)) := by
      field_simp [ne_of_gt hLm]
    have hglobalId : 128 * LM ^ 2 * w =
        128 * (1 / (4398046511104 * LM ^ 7)) := by
      dsimp only [w]
      field_simp [ne_of_gt hLM]
    rw [hglobalId]
    calc
      128 * (1 / (4398046511104 * LM ^ 7)) ≤
          128 * (1 / (4398046511104 * Lm ^ 7)) :=
        mul_le_mul_of_nonneg_left hinv7 (by norm_num)
      _ = 128 * Lm ^ 2 * (1 / (4398046511104 * Lm ^ 9)) := hlocalId.symm
      _ ≤ ‖χ.LFunction (a + I * η)‖ := hanchorRaw
  have hσtwo : σ ≤ 2 := by
    dsimp only [dirichletLTwistedSmoothedConductorLogRight] at hσright
    linarith
  have ha_near : 1 - 1 / Real.log m ≤ a := by
    dsimp only [a]
    linarith
  -- `|L'| ≤ 64 (1 + log M)^2` on the segment from `1 - w/4` to `σ`.
  have hderivOnSegment (u : ℝ) (hau : a ≤ u) (huσ : u ≤ σ) :
      ‖deriv χ.LFunction (u + I * η)‖ ≤ 64 * LM ^ 2 := by
    have hd := norm_deriv_LFunction_le_one_add_log_sq
      χ hχ (σ := u) (t := η) (ha_half.trans hau) (huσ.trans hσtwo)
      (by simpa only [m] using ha_near.trans hau)
    calc
      _ ≤ 64 * Lm ^ 2 := by simpa only [Lm, m] using hd
      _ ≤ 64 * LM ^ 2 := by gcongr
  have hderiv : ‖deriv χ.LFunction (σ + I * η)‖ ≤ 64 * LM ^ 2 :=
    hderivOnSegment σ (ha_def ▸ hσleft) le_rfl
  by_cases hbranch : σ ≤ 1 + w / 4
  · have haσ : a ≤ σ := by simpa only [ha_def] using hσleft
    have hdist : σ - a ≤ w / 2 := by dsimp only [a] at *; linarith
    have hdiff : ‖χ.LFunction (σ + I * η) - χ.LFunction (a + I * η)‖ ≤
        64 * LM ^ 2 * (σ - a) := by
      have heq := BombieriVinogradov.WeakStripDifference.integral_deriv_LFunction_eq_sub
        χ hχ a σ η
      have heq' : (∫ u in a..σ, deriv χ.LFunction (u + I * η)) =
          χ.LFunction (σ + I * η) - χ.LFunction (a + I * η) := by
        simpa only [mul_comm] using heq
      rw [← heq']
      convert intervalIntegral.norm_integral_le_of_norm_le_const ?_ using 1
      · rw [_root_.abs_of_nonneg (sub_nonneg.mpr haσ)]
      · intro u hu
        rw [uIoc_of_le haσ, mem_Ioc] at hu
        exact hderivOnSegment u hu.1.le hu.2
    have hdiff' : ‖χ.LFunction (σ + I * η) - χ.LFunction (a + I * η)‖ ≤
        32 * LM ^ 2 * w := by
      calc
        _ ≤ 64 * LM ^ 2 * (σ - a) := hdiff
        _ ≤ 64 * LM ^ 2 * (w / 2) := by gcongr
        _ = 32 * LM ^ 2 * w := by ring
    have hlower : 96 * LM ^ 2 * w ≤ ‖χ.LFunction (σ + I * η)‖ := by
      have htri : ‖χ.LFunction (a + I * η)‖ ≤
          ‖χ.LFunction (σ + I * η) - χ.LFunction (a + I * η)‖ +
            ‖χ.LFunction (σ + I * η)‖ := by
        simpa only [sub_add_cancel, norm_sub_rev] using norm_add_le
          (χ.LFunction (a + I * η) - χ.LFunction (σ + I * η))
          (χ.LFunction (σ + I * η))
      rw [norm_sub_rev] at hdiff'
      nlinarith
    have hden : 0 < 96 * LM ^ 2 * w := by positivity
    rw [norm_div]
    calc
      _ ≤ (64 * LM ^ 2) / (96 * LM ^ 2 * w) :=
        div_le_div₀ (by positivity) hderiv hden hlower
      _ ≤ 2251799813685248 * LM ^ 11 := by
        dsimp only [w]
        field_simp [ne_of_gt hLM]
        nlinarith [one_le_pow₀ hLM.le (n := 11)]
      _ = 2251799813685248 *
          (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 := by rfl
  · have hσthreshold : 1 + w / 4 < σ := lt_of_not_ge hbranch
    have hrhp := norm_dirichletLFunction_ge_sub_one_div χ (t := η)
      (by linarith : 1 < σ)
    have hlower : w / 8 ≤ ‖χ.LFunction (σ + I * η)‖ := by
      have hσpos : 0 < σ := by linarith
      have hratio : w / 8 ≤ (σ - 1) / σ := by
        rw [div_le_div_iff₀ (by norm_num) hσpos]
        nlinarith
      exact hratio.trans hrhp
    have hden : 0 < w / 8 := by positivity
    rw [norm_div]
    calc
      _ ≤ (64 * LM ^ 2) / (w / 8) :=
        div_le_div₀ (by positivity) hderiv hden hlower
      _ = 2251799813685248 * LM ^ 11 := by
        dsimp only [w]
        field_simp [ne_of_gt hLM]
        ring
      _ = 2251799813685248 *
          (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 := by rfl

 end BombieriVinogradov

end

/-! ## The edge integrals -/

section

open Set Function Filter Complex Real MeasureTheory

namespace BombieriVinogradov

local notation "𝓜" => mellin

private theorem conductorLog_parameters_pos
    {q : ℕ} [NeZero q] {T : ℝ} (hT : 3 ≤ T) :
    0 < dirichletLTwistedSmoothedConductorLogLM q T ∧
      0 < dirichletLTwistedSmoothedConductorLogEdgeWidth q T := by
  have hM : 4 ≤ dirichletLTwistedSmoothedConductorLogCutoff q T := by
    simpa only [dirichletLTwistedSmoothedConductorLogCutoff] using
      four_le_dirichletLNonquadraticConductorLogCutoff hT
  have hlog : 0 < Real.log (dirichletLTwistedSmoothedConductorLogCutoff q T : ℝ) :=
    Real.log_pos (by exact_mod_cast
      (show 1 < dirichletLTwistedSmoothedConductorLogCutoff q T by omega))
  have hLM : 0 < dirichletLTwistedSmoothedConductorLogLM q T := by
    dsimp only [dirichletLTwistedSmoothedConductorLogLM]
    linarith
  refine ⟨hLM, ?_⟩
  dsimp only [dirichletLTwistedSmoothedConductorLogEdgeWidth]
  positivity

private theorem one_half_lt_conductorLogFinalLeft
    {q : ℕ} [NeZero q] {T : ℝ} (hT : 3 ≤ T) :
    (1 / 2 : ℝ) < dirichletLTwistedSmoothedConductorLogFinalLeft q T := by
  have hold := one_half_lt_dirichletLTwistedSmoothedConductorLogLeftEdge
    (q := q) (T := T) hT
  have hw := (conductorLog_parameters_pos (q := q) hT).2
  have hle : dirichletLTwistedSmoothedConductorLogLeftEdge q T ≤
      dirichletLTwistedSmoothedConductorLogFinalLeft q T := by
    change 1 - dirichletLTwistedSmoothedConductorLogEdgeWidth q T ≤
      1 - dirichletLTwistedSmoothedConductorLogEdgeWidth q T / 4
    linarith
  exact hold.trans_le hle

/-- Bound for the horizontal integral of the Perron integrand from `a` to `b` at height
`|t| = T`, given `‖𝓜(ν_ε)(s)‖ ≤ M / (ε |s|^2)` and `|L'/L| ≤ J` on the segment. -/
theorem norm_twistedSmoothedPerron_horizontal_le_of_logDeriv_bound
    {ν : ℝ → ℝ} {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε)
    (hMellin : ∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ M * (ε * ‖s‖ ^ 2)⁻¹)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a b T t X J : ℝ} (ha : (1 / 2 : ℝ) ≤ a) (hab : a ≤ b)
    (hb : b ≤ 2) (hT : 1 ≤ T) (ht : |t| = T) (hX : 1 ≤ X) (hJ : 0 ≤ J)
    (hlog : ∀ σ : ℝ, a ≤ σ → σ ≤ b →
      ‖deriv χ.LFunction (σ + t * I) / χ.LFunction (σ + t * I)‖ ≤ J) :
    ‖HIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X) a b t‖ ≤
      4 * M * J * X ^ b / (ε * (1 + T ^ 2)) := by
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hT0 : 0 < T := by linarith
  have hpoint (σ : ℝ) (hσa : a ≤ σ) (hσb : σ ≤ b) :
      ‖DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X (σ + t * I)‖ ≤
        J * (2 * M / (ε * (1 + T ^ 2))) * X ^ b := by
    have hm := hMellin (σ + t * I) (by simp; linarith) (by simp; exact hσb.trans hb)
    have hnormsq : T ^ 2 ≤ ‖(σ : ℂ) + t * I‖ ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
      have ht2 := congrArg (fun u : ℝ => u ^ 2) ht
      rw [sq_abs] at ht2
      nlinarith [sq_nonneg σ]
    have hinvDen : (T ^ 2)⁻¹ ≤ 2 * (1 + T ^ 2)⁻¹ := by
      rw [show (T ^ 2)⁻¹ = 1 / T ^ 2 by rw [one_div],
        show 2 * (1 + T ^ 2)⁻¹ = 2 / (1 + T ^ 2) by rw [div_eq_mul_inv]]
      rw [div_le_div_iff₀ (sq_pos_of_pos hT0) (by positivity)]
      nlinarith [sq_nonneg T]
    have hm' : ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I)‖ ≤
        2 * M / (ε * (1 + T ^ 2)) := by
      calc
        _ ≤ M * (ε * ‖(σ : ℂ) + t * I‖ ^ 2)⁻¹ := hm
        _ ≤ M * (2 / (ε * (1 + T ^ 2))) := by
          gcongr
          rw [mul_inv_rev]
          calc
            (‖(σ : ℂ) + t * I‖ ^ 2)⁻¹ * ε⁻¹ ≤
                (2 * (1 + T ^ 2)⁻¹) * ε⁻¹ := by
              gcongr
              exact (inv_anti₀ (sq_pos_of_pos hT0) hnormsq).trans hinvDen
            _ = 2 / (ε * (1 + T ^ 2)) := by field_simp [hε.ne']
        _ = 2 * M / (ε * (1 + T ^ 2)) := by ring
    have hXnorm : ‖(X : ℂ) ^ ((σ : ℂ) + t * I)‖ = X ^ σ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX0]
      simp
    have hXpow : X ^ σ ≤ X ^ b := Real.rpow_le_rpow_of_exponent_le hX hσb
    have hlog' : ‖-deriv χ.LFunction (σ + t * I) / χ.LFunction (σ + t * I)‖ ≤ J := by
      simpa only [neg_div, norm_neg] using hlog σ hσa hσb
    dsimp only [DirichletCharacter.twistedSmoothedPerronIntegrand]
    rw [norm_mul, norm_mul, hXnorm]
    calc
      _ ≤ J * (2 * M / (ε * (1 + T ^ 2))) * X ^ σ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hlog' hm' (norm_nonneg _) hJ) (Real.rpow_nonneg hX0.le _)
      _ ≤ _ := by gcongr
  rw [HIntegral]
  calc
    _ ≤ (J * (2 * M / (ε * (1 + T ^ 2))) * X ^ b) * |b - a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro σ hσ
      rw [uIoc_of_le hab] at hσ
      exact hpoint σ hσ.1.le hσ.2
    _ ≤ (J * (2 * M / (ε * (1 + T ^ 2))) * X ^ b) * 2 := by
      have hlen : |b - a| ≤ 2 := by
        rw [abs_of_nonneg (sub_nonneg.mpr hab)]
        linarith
      gcongr
    _ = _ := by ring

/-- Bounds for the integrals over the left edge and the two horizontal edges of the
rectangle. The constant `C` depends only on the smoothing function `ν`. -/
theorem exists_dirichletLTwistedSmoothedContourNormBounds
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : support ν ⊆ Icc (1 / 2) 2) :
    ∃ C > 0, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
      {T d ε X : ℝ}, χ ^ 2 ≠ 1 → 3 ≤ T → 0 < d → d ≤ 1 →
      0 < ε → ε < 1 → 1 ≤ X →
      ‖VIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
          (dirichletLTwistedSmoothedConductorLogFinalLeft q T) (-T) T‖ ≤
        C * T * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 *
          X ^ (dirichletLTwistedSmoothedConductorLogFinalLeft q T) / ε ∧
      ‖HIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
          (dirichletLTwistedSmoothedConductorLogFinalLeft q T)
          (dirichletLTwistedSmoothedConductorLogRight d) T‖ ≤
        C * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 * X ^ (1 + d) /
          (ε * (1 + T ^ 2)) ∧
      ‖HIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
          (dirichletLTwistedSmoothedConductorLogFinalLeft q T)
          (dirichletLTwistedSmoothedConductorLogRight d) (-T)‖ ≤
        C * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 * X ^ (1 + d) /
          (ε * (1 + T ^ 2)) := by
  obtain ⟨A, hA, hMellin⟩ := MellinOfSmooth1b diffν suppν
  refine ⟨36028797018963968 * A, by positivity, ?_⟩
  intro q _ χ T d ε X hχsq hT hd hd1 hε hε1 hX
  let LM := dirichletLTwistedSmoothedConductorLogLM q T
  let a := dirichletLTwistedSmoothedConductorLogFinalLeft q T
  let b := dirichletLTwistedSmoothedConductorLogRight d
  obtain ⟨hLM, hwidth⟩ := conductorLog_parameters_pos (q := q) hT
  change 0 < LM at hLM
  have ha : (1 / 2 : ℝ) < a := by
    simpa only [a] using one_half_lt_conductorLogFinalLeft (q := q) hT
  have hab : a ≤ b := by
    dsimp only [a, b, dirichletLTwistedSmoothedConductorLogFinalLeft,
      dirichletLTwistedSmoothedConductorLogRight]
    linarith
  have hb2 : b ≤ 2 := by
    simp only [b, dirichletLTwistedSmoothedConductorLogRight]
    linarith
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have verticalPoint (t : ℝ) (ht : |t| ≤ T) :
      ‖DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X (a + t * I)‖ ≤
        2251799813685248 * LM ^ 11 * (4 * A / ε) * X ^ a := by
    have hlog := norm_logDeriv_LFunction_le_on_conductorLogEdgeRectangle
      χ hχsq hT hd hd1 ht (le_refl a) hab
    have hm := hMellin (1 / 2) (by norm_num) (a + t * I)
      (by simp; norm_num at ha ⊢; exact ha.le)
      (by simp; exact (hab.trans hb2)) ε hε hε1
    have hnormsq : (1 / 4 : ℝ) ≤ ‖(a : ℂ) + t * I‖ ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
      nlinarith [sq_nonneg t]
    have hinv : (ε * ‖(a : ℂ) + t * I‖ ^ 2)⁻¹ ≤ 4 / ε := by
      rw [mul_inv_rev]
      have hi : (‖(a : ℂ) + t * I‖ ^ 2)⁻¹ ≤ (4 : ℝ) := by
        have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 4) hnormsq
        norm_num at this ⊢
        exact this
      calc
        (‖(a : ℂ) + t * I‖ ^ 2)⁻¹ * ε⁻¹ ≤ 4 * ε⁻¹ :=
          mul_le_mul_of_nonneg_right hi (inv_nonneg.mpr hε.le)
        _ = 4 / ε := by rw [div_eq_mul_inv]
    have hm' : ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (a + t * I)‖ ≤ 4 * A / ε := by
      calc
        _ ≤ A * (ε * ‖(a : ℂ) + t * I‖ ^ 2)⁻¹ := hm
        _ ≤ A * (4 / ε) := mul_le_mul_of_nonneg_left hinv hA.le
        _ = 4 * A / ε := by ring
    have hXnorm : ‖(X : ℂ) ^ ((a : ℂ) + t * I)‖ = X ^ a := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX0]
      simp
    have hlog' :
        ‖-deriv χ.LFunction (a + t * I) / χ.LFunction (a + t * I)‖ ≤
          2251799813685248 * LM ^ 11 := by
      simpa only [neg_div, norm_neg, LM, mul_comm] using hlog
    dsimp only [DirichletCharacter.twistedSmoothedPerronIntegrand]
    rw [norm_mul, norm_mul, hXnorm]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hlog' hm' (norm_nonneg _) (by positivity)) (Real.rpow_nonneg hX0.le _)
  have hvertical :
      ‖VIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
          a (-T) T‖ ≤
        (36028797018963968 * A) * T * LM ^ 11 * X ^ a / ε := by
    rw [VIntegral, norm_smul, norm_I, one_mul]
    calc
      ‖∫ t in -T..T,
          DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X (a + t * I)‖
          ≤ (2251799813685248 * LM ^ 11 * (4 * A / ε) * X ^ a) *
              |T - (-T)| := by
            apply intervalIntegral.norm_integral_le_of_norm_le_const
            intro t ht
            rw [uIoc_of_le (by linarith)] at ht
            apply verticalPoint t
            rw [abs_le]
            exact ⟨ht.1.le, ht.2⟩
      _ ≤ (36028797018963968 * A) * T * LM ^ 11 * X ^ a / ε := by
        rw [abs_of_nonneg (by linarith)]
        field_simp [hε.ne']
        nlinarith [Real.rpow_nonneg hX0.le a, pow_pos hLM 11]
  have horizontalBound (η : ℝ) (hη : |η| ≤ T) (hηsq : η ^ 2 = T ^ 2) :
      ‖HIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
          a b η‖ ≤
        (36028797018963968 * A) * LM ^ 11 * X ^ (1 + d) /
          (ε * (1 + T ^ 2)) := by
    have ht : |η| = T := by
      nlinarith [sq_abs η, abs_nonneg η]
    have hbound := norm_twistedSmoothedPerron_horizontal_le_of_logDeriv_bound hA.le hε
      (fun s hs hs2 => hMellin (1 / 2) (by norm_num) s hs hs2 ε hε hε1)
      χ ha.le hab hb2 (by linarith) ht hX
      (show 0 ≤ 2251799813685248 * LM ^ 11 by positivity)
      (fun σ hσa hσb => by
        simpa only [LM, mul_comm] using
          norm_logDeriv_LFunction_le_on_conductorLogEdgeRectangle
            χ hχsq hT hd hd1 hη hσa hσb)
    calc
      _ ≤ 4 * A * (2251799813685248 * LM ^ 11) * X ^ b /
          (ε * (1 + T ^ 2)) := hbound
      _ ≤ _ := by
        dsimp only [b, dirichletLTwistedSmoothedConductorLogRight]
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [mul_nonneg (mul_nonneg hA.le (pow_nonneg hLM.le 11))
          (Real.rpow_nonneg hX0.le (1 + d))]
  simpa only [a, b, LM] using
    ⟨hvertical, horizontalBound T (by simp [abs_of_nonneg hT0.le]) (by rfl),
      horizontalBound (-T) (by rw [abs_neg, abs_of_nonneg hT0.le]) (by ring)⟩

end BombieriVinogradov

end

/-! ## The smoothed sum -/

section

open Set Function Filter Complex Real MeasureTheory

namespace BombieriVinogradov

theorem integral_lower_middle_upper
    (f : ℝ → ℂ) {T : ℝ} (hf : Integrable f) (hT : 0 ≤ T) :
    (∫ t in Iic (-T), f t) + (∫ t in Ioc (-T) T, f t) +
        (∫ t in Ici T, f t) = ∫ t, f t := by
  have h₁ := integral_add_compl (μ := volume) (s := Iic (-T)) measurableSet_Iic hf
  have h₂ := integral_add_compl (μ := volume.restrict (Ioi (-T)))
    (s := Iic T) measurableSet_Iic hf.integrableOn
  rw [integral_Ici_eq_integral_Ioi]
  simp only [compl_Iic] at h₁ h₂
  have hi : Iic T ∩ Ioi (-T) = Ioc (-T) T := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_Ioc]
    tauto
  have hc : Ioi T ∩ Ioi (-T) = Ioi T := by
    ext x
    simp only [mem_inter_iff, mem_Ioi]
    constructor
    · exact fun hx => hx.1
    · intro hx
      exact ⟨hx, by linarith⟩
  rw [Measure.restrict_restrict measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Ioi] at h₂
  rw [hi, hc] at h₂
  linear_combination h₁ + h₂

/-- Given the contour shift identity, bounds for the other three edges and for the two
tails `|t| ≥ T` of the line `Re s = b` give a bound for the normalized integral over that
line. -/
theorem norm_verticalIntegral'_le_of_finite_contour_bounds
    (F : ℂ → ℂ) {a b T Vl Hu Hl Tl Tu : ℝ} (hT : 0 ≤ T)
    (hf : Integrable (fun t : ℝ => F ((b : ℂ) + t * I)))
    (hshift : VIntegral F b (-T) T - VIntegral F a (-T) T =
      HIntegral F a b T - HIntegral F a b (-T))
    (hleft : ‖VIntegral F a (-T) T‖ ≤ Vl)
    (htop : ‖HIntegral F a b T‖ ≤ Hu)
    (hbottom : ‖HIntegral F a b (-T)‖ ≤ Hl)
    (htlow : ‖∫ t in Iic (-T), F ((b : ℂ) + t * I)‖ ≤ Tl)
    (htupper : ‖∫ t in Ici T, F ((b : ℂ) + t * I)‖ ≤ Tu) :
    ‖VerticalIntegral' F b‖ ≤ Tl + (Vl + Hu + Hl) + Tu := by
  have hsplit := integral_lower_middle_upper
    (fun t : ℝ => F ((b : ℂ) + t * I)) hf hT
  have hmid :
      ‖∫ t in Ioc (-T) T, F ((b : ℂ) + t * I)‖ =
        ‖VIntegral F b (-T) T‖ := by
    rw [VIntegral, norm_smul, norm_I, one_mul,
      intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  have hv : ‖VIntegral F b (-T) T‖ ≤ Vl + Hu + Hl := by
    have heq : VIntegral F b (-T) T =
        VIntegral F a (-T) T + HIntegral F a b T - HIntegral F a b (-T) := by
      linear_combination hshift
    rw [heq]
    exact ((norm_sub_le _ _).trans
      (add_le_add (norm_add_le _ _) (le_refl _))).trans
        (add_le_add (add_le_add hleft htop) hbottom)
  have hfull : ‖∫ t : ℝ, F ((b : ℂ) + t * I)‖ ≤ Tl + (Vl + Hu + Hl) + Tu := by
    rw [← hsplit]
    calc
      _ ≤ ‖∫ t in Iic (-T), F ((b : ℂ) + t * I)‖ +
          ‖∫ t in Ioc (-T) T, F ((b : ℂ) + t * I)‖ +
          ‖∫ t in Ici T, F ((b : ℂ) + t * I)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
      _ ≤ _ := by
        rw [hmid]
        exact add_le_add (add_le_add htlow hv) htupper
  have hnorm : ‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, norm_I]
    norm_num
    rw [abs_of_pos Real.pi_pos]
    have hinv : Real.pi⁻¹ ≤ 1 :=
      (inv_le_one₀ Real.pi_pos).2 (by linarith [Real.pi_gt_three])
    nlinarith [inv_nonneg.mpr Real.pi_pos.le]
  have hnormalized : ‖VerticalIntegral' F b‖ ≤
      ‖∫ t : ℝ, F ((b : ℂ) + t * I)‖ := by
    rw [VerticalIntegral', VerticalIntegral, norm_smul, norm_smul, norm_I, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hnorm
  exact hnormalized.trans hfull

/-- Bound for the smoothed sum `∑ Λ(n) χ(n) ν_ε(n / X)` when `χ² ≠ 1`. The three terms
come from the left edge, the two horizontal edges and the two tails of the line
`Re s = 1 + d`. -/
theorem exists_dirichletLTwistedSmoothedNonquadraticErrorAssembly
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1) :
    ∃ K > 0, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
      {T d ε X : ℝ}, χ ^ 2 ≠ 1 → 3 ≤ T → 0 < d → d ≤ 1 →
      0 < ε → ε < 1 → 1 ≤ X →
      ‖DirichletCharacter.twistedSmoothedPsi χ ν ε X‖ ≤
        K * (T * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 *
              X ^ (dirichletLTwistedSmoothedConductorLogFinalLeft q T) / ε +
          (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 * X ^ (1 + d) /
              (ε * (1 + T ^ 2)) +
          X ^ (1 + d) * (1 + d⁻¹ ^ 2) / (ε * T)) := by
  obtain ⟨C, hC, hcontour⟩ :=
    exists_dirichletLTwistedSmoothedContourNormBounds diffν suppν
  obtain ⟨c, hc, htails⟩ :=
    DirichletCharacter.twistedSmoothedPerron_right_tails_quantitative
      diffν νpos suppν mass_one
  refine ⟨2 * (C + c), by positivity, ?_⟩
  intro q _ χ T d ε X hχsq hT hd hd1 hε hε1 hX
  let F := DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X
  let a := dirichletLTwistedSmoothedConductorLogFinalLeft q T
  let b := dirichletLTwistedSmoothedConductorLogRight d
  let LM := dirichletLTwistedSmoothedConductorLogLM q T
  let A := T * LM ^ 11 * X ^ a / ε
  let B := LM ^ 11 * X ^ (1 + d) / (ε * (1 + T ^ 2))
  let D := X ^ (1 + d) * (1 + d⁻¹ ^ 2) / (ε * T)
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hT1 : 1 ≤ T := by linarith

  have hf : Integrable (fun t : ℝ => F ((b : ℂ) + t * I)) := by
    simpa only [F, b, dirichletLTwistedSmoothedConductorLogRight] using
      (DirichletCharacter.twistedSmoothedPerronIntegrand_integrable_right
        (q := q) (σ := 1 + d) (X := X) (ε := ε) χ diffν νpos suppν mass_one
        hX0 hε hε1 (by linarith) (by linarith))
  have hp := DirichletCharacter.twistedSmoothedPerron χ diffν νpos suppν mass_one
    hX0 hε hε1 (σ := 1 + d) (by linarith) (by linarith)
  have ht := htails χ hd hd1 hε hε1 hX0 hT1
  have hct := hcontour χ hχsq hT hd hd1 hε hε1 hX
  have hshift := perronContourIdentity_nonquadratic
    χ hχsq hT hd hd1 diffν νpos suppν mass_one hX0 hε hε1
  have htlow : ‖∫ t in Iic (-T), F ((b : ℂ) + t * I)‖ ≤ c * D := by
    dsimp only [F, b, D, dirichletLTwistedSmoothedConductorLogRight]
    convert ht.1 using 1; (try ring)
  have htupper : ‖∫ t in Ici T, F ((b : ℂ) + t * I)‖ ≤ c * D := by
    dsimp only [F, b, D, dirichletLTwistedSmoothedConductorLogRight]
    convert ht.2 using 1; (try ring)
  have hleft : ‖VIntegral F a (-T) T‖ ≤ C * A := by
    dsimp only [F, a, A, LM]
    convert hct.1 using 1; (try ring)
  have htop : ‖HIntegral F a b T‖ ≤ C * B := by
    dsimp only [F, a, b, B, LM]
    convert hct.2.1 using 1; (try ring)
  have hbottom : ‖HIntegral F a b (-T)‖ ≤ C * B := by
    dsimp only [F, a, b, B, LM]
    convert hct.2.2 using 1; (try ring)
  have hfull := norm_verticalIntegral'_le_of_finite_contour_bounds F hT0.le hf
    hshift hleft htop hbottom htlow htupper
  have hLM0 : 0 < LM := by
    have hM : 4 ≤ dirichletLTwistedSmoothedConductorLogCutoff q T := by
      simpa only [dirichletLTwistedSmoothedConductorLogCutoff] using
        four_le_dirichletLNonquadraticConductorLogCutoff hT
    have hlog : 0 < Real.log (dirichletLTwistedSmoothedConductorLogCutoff q T : ℝ) :=
      Real.log_pos (by exact_mod_cast
        (show 1 < dirichletLTwistedSmoothedConductorLogCutoff q T by omega))
    dsimp only [LM, dirichletLTwistedSmoothedConductorLogLM]
    positivity
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    positivity
  rw [hp]
  change ‖VerticalIntegral' F b‖ ≤ _
  calc
    ‖VerticalIntegral' F b‖ ≤ c * D + (C * A + C * B + C * B) + c * D := hfull
    _ ≤ 2 * (C + c) * (A + B + D) := by
      nlinarith [mul_nonneg hC.le hA0, mul_nonneg hC.le hB0,
        mul_nonneg hC.le hD0, mul_nonneg hc.le hA0,
        mul_nonneg hc.le hB0, mul_nonneg hc.le hD0]
    _ = _ := by rfl

end BombieriVinogradov

end

/-! ## Choice of parameters -/

section

namespace BombieriVinogradov

theorem pointwiseSW_horizontal_le_tail
    {X ε T Q L : ℝ} (hX : 0 ≤ X) (hε : 0 < ε) (hT : 0 < T)
    (hQ : Q ≤ T) :
    Q * X / (ε * (1 + T ^ 2)) ≤ X * (1 + L ^ 2) / (ε * T) := by
  calc
    Q * X / (ε * (1 + T ^ 2)) ≤ T * X / (ε * (1 + T ^ 2)) := by
      gcongr
    _ ≤ X / (ε * T) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith [mul_nonneg hX hε.le]
    _ ≤ X * (1 + L ^ 2) / (ε * T) := by
      gcongr
      nlinarith [sq_nonneg L]

end BombieriVinogradov

end

section

open Set Function Filter Complex Real MeasureTheory

namespace BombieriVinogradov

noncomputable section

/-- The exponent `2D + 30` of the contour height. -/
def nonquadraticPointwiseSWHeightExponent (D : ℕ) : ℕ := 2 * D + 30

/-- The contour height `T = (log N)^(2D + 30)`. -/
def nonquadraticPointwiseSWHeight (D N : ℕ) : ℝ :=
  Real.log (N : ℝ) ^ nonquadraticPointwiseSWHeightExponent D

/-- The smoothing width `ε = (log N)^(-(D + 3))`. -/
def nonquadraticPointwiseSWEpsilon (D N : ℕ) : ℝ :=
  (Real.log (N : ℝ) ^ (D + 3))⁻¹

/-- The distance `d = 1 / log N` of the right edge from `1`. -/
def nonquadraticPointwiseSWDelta (N : ℕ) : ℝ :=
  (Real.log (N : ℝ))⁻¹

/-- If `q ≤ (log N)^C` and `T = (log N)^B` with `B = 2D + 30`, then
`1 + log M(q, T) ≤ (C + B + 3) log log N`. -/
theorem dirichletLTwistedSmoothedConductorLogLM_le_loglog_pointwise
    (C D N q : ℕ) [NeZero q] (hlog : Real.exp 1 ≤ Real.log (N : ℝ))
    (hq : q ≤ logConductorThreshold N C) :
    dirichletLTwistedSmoothedConductorLogLM q
        (nonquadraticPointwiseSWHeight D N) ≤
      (C + nonquadraticPointwiseSWHeightExponent D + 3 : ℕ) *
        Real.log (Real.log (N : ℝ)) := by
  let L := Real.log (N : ℝ)
  let B := nonquadraticPointwiseSWHeightExponent D
  have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hlog
  have hL1 : 1 ≤ L := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).le.trans hlog
  have hlogL1 : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLpos).2 hlog
  have hqR : (q : ℝ) ≤ L ^ C := by
    calc
      (q : ℝ) ≤ logConductorThreshold N C := by exact_mod_cast hq
      _ ≤ L ^ C := by
        dsimp only [logConductorThreshold, L]
        simpa only [L] using
          (Nat.floor_le (pow_nonneg hLpos.le C))
  have hfloor :
      (⌊nonquadraticPointwiseSWHeight D N⌋₊ : ℝ) ≤
        nonquadraticPointwiseSWHeight D N := by
    exact Nat.floor_le (by
      dsimp only [nonquadraticPointwiseSWHeight]
      positivity)
  have hheight :
      (dirichletLNonquadraticConductorLogHeightBlock
          (nonquadraticPointwiseSWHeight D N) : ℝ) ≤ 2 * L ^ B := by
    dsimp only [dirichletLNonquadraticConductorLogHeightBlock]
    rw [Nat.cast_add, Nat.cast_one]
    calc
      (⌊nonquadraticPointwiseSWHeight D N⌋₊ : ℝ) + 1 ≤
          nonquadraticPointwiseSWHeight D N + 1 := by linarith
      _ = L ^ B + 1 := by rfl
      _ ≤ 2 * L ^ B := by
        have hpow : 1 ≤ L ^ B := one_le_pow₀ hL1
        linarith
  have hcut :
      (dirichletLTwistedSmoothedConductorLogCutoff q
          (nonquadraticPointwiseSWHeight D N) : ℝ) ≤
        2 * L ^ (C + B) := by
    dsimp only [dirichletLTwistedSmoothedConductorLogCutoff,
      dirichletLNonquadraticConductorLogCutoff]
    rw [Nat.cast_mul]
    calc
      (q : ℝ) * dirichletLNonquadraticConductorLogHeightBlock
          (nonquadraticPointwiseSWHeight D N) ≤ L ^ C * (2 * L ^ B) :=
        mul_le_mul hqR hheight (by positivity) (by positivity)
      _ = 2 * L ^ (C + B) := by rw [pow_add]; ring
  have hcutpos :
      0 < (dirichletLTwistedSmoothedConductorLogCutoff q
          (nonquadraticPointwiseSWHeight D N) : ℝ) := by
    have hq0 : 0 < q := NeZero.pos q
    have hh0 : 0 < dirichletLNonquadraticConductorLogHeightBlock
        (nonquadraticPointwiseSWHeight D N) := by
      dsimp only [dirichletLNonquadraticConductorLogHeightBlock]
      omega
    dsimp only [dirichletLTwistedSmoothedConductorLogCutoff,
      dirichletLNonquadraticConductorLogCutoff]
    exact_mod_cast Nat.mul_pos hq0 hh0
  have hlogcut := Real.log_le_log hcutpos hcut
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero _ (ne_of_gt hLpos)),
    Real.log_pow] at hlogcut
  norm_num only [Nat.cast_add] at hlogcut
  have hlog2 : Real.log (2 : ℝ) ≤ Real.log L := by
    apply Real.log_le_log (by norm_num)
    exact (show (2 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]).trans hlog
  dsimp only [dirichletLTwistedSmoothedConductorLogLM]
  calc
    1 + Real.log (dirichletLTwistedSmoothedConductorLogCutoff q
        (nonquadraticPointwiseSWHeight D N) : ℝ) ≤
        1 + (Real.log 2 + (C + B) * Real.log L) := by linarith
    _ ≤ (C + B + 3 : ℕ) * Real.log L := by
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      nlinarith

/-- For `q ≤ (log N)^C` and large `N`, the left edge `σ₀ = 1 - w/4` satisfies
`N^σ₀ ≤ N / (log N)^E`. Since `w ≫ (log log N)^(-9)`, the factor `N^(-w/4)` beats any power
of `log N`. -/
theorem eventually_nonquadraticPointwiseSW_leftEdge
    (C D E : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ∀ _inst : NeZero q,
      q ≤ logConductorThreshold N C →
      (N : ℝ) ^ (dirichletLTwistedSmoothedConductorLogFinalLeft q
          (nonquadraticPointwiseSWHeight D N)) ≤
        (N : ℝ) / Real.log (N : ℝ) ^ E := by
  let B := nonquadraticPointwiseSWHeightExponent D
  let A : ℝ := C + B + 3
  let M : ℝ := E + 1
  have hA : 0 < A := by dsimp only [A]; positivity
  have hM : 0 < M := by dsimp only [M]; positivity
  let c : ℝ := (4 * 4398046511104 * A ^ 9 * M)⁻¹
  have hc : 0 < c := by dsimp only [c]; positivity
  have hsmall := (isLittleO_log_rpow_rpow_atTop (10 : ℝ) (by norm_num : (0 : ℝ) < 1)).bound hc
  have hlogtop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmallN : ∀ᶠ N : ℕ in atTop,
      ‖Real.log (Real.log (N : ℝ)) ^ (10 : ℝ)‖ ≤
        c * ‖Real.log (N : ℝ) ^ (1 : ℝ)‖ := hlogtop.eventually hsmall
  filter_upwards [hsmallN,
      hlogtop.eventually (eventually_ge_atTop (Real.exp 1)),
      eventually_gt_atTop (0 : ℕ)] with N hsmallN hlog hN0
  intro q _inst hq
  let L := Real.log (N : ℝ)
  let z := Real.log L
  let LM := dirichletLTwistedSmoothedConductorLogLM q
    (nonquadraticPointwiseSWHeight D N)
  have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hlog
  have hz1 : 1 ≤ z := (Real.le_log_iff_exp_le hLpos).2 hlog
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have hLM := dirichletLTwistedSmoothedConductorLogLM_le_loglog_pointwise
    C D N q hlog hq
  have hLMpos : 0 < LM := by
    dsimp only [LM, dirichletLTwistedSmoothedConductorLogLM]
    have hcut : 0 < (dirichletLTwistedSmoothedConductorLogCutoff q
        (nonquadraticPointwiseSWHeight D N) : ℝ) := by
      have hq0 : 0 < q := NeZero.pos q
      have hh0 : 0 < dirichletLNonquadraticConductorLogHeightBlock
          (nonquadraticPointwiseSWHeight D N) := by
        dsimp only [dirichletLNonquadraticConductorLogHeightBlock]
        omega
      dsimp only [dirichletLTwistedSmoothedConductorLogCutoff,
        dirichletLNonquadraticConductorLogCutoff]
      exact_mod_cast Nat.mul_pos hq0 hh0
    have hcut1 : 1 ≤ dirichletLTwistedSmoothedConductorLogCutoff q
        (nonquadraticPointwiseSWHeight D N) := by exact_mod_cast hcut
    have hlogcut : 0 ≤ Real.log (dirichletLTwistedSmoothedConductorLogCutoff q
        (nonquadraticPointwiseSWHeight D N) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hcut1)
    linarith
  have hLM' : LM ≤ A * z := by
    simpa only [LM, A, B, z, Nat.cast_add, Nat.cast_ofNat] using hLM
  have hLM9 : LM ^ 9 ≤ A ^ 9 * z ^ 9 := by
    calc
      LM ^ 9 ≤ (A * z) ^ 9 := pow_le_pow_left₀ hLMpos.le hLM' 9
      _ = A ^ 9 * z ^ 9 := by rw [mul_pow]
  have hsmall' : z ^ 10 ≤ c * L := by
    have hsmallR : z ^ (10 : ℝ) ≤ c * L := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hzpos.le 10),
        Real.norm_of_nonneg (Real.rpow_nonneg hLpos.le 1), Real.rpow_one] at hsmallN
      exact hsmallN
    rw [← Real.rpow_natCast]
    exact hsmallR
  have hkey : 4 * 4398046511104 * LM ^ 9 * M * z ≤ L := by
    calc
      4 * 4398046511104 * LM ^ 9 * M * z ≤
          4 * 4398046511104 * (A ^ 9 * z ^ 9) * M * z := by gcongr
      _ = (4 * 4398046511104 * A ^ 9 * M) * z ^ 10 := by ring
      _ ≤ (4 * 4398046511104 * A ^ 9 * M) * (c * L) := by gcongr
      _ = L := by
        dsimp only [c]
        field_simp
  have hwidth : M * z ≤
      dirichletLTwistedSmoothedConductorLogEdgeWidth q
          (nonquadraticPointwiseSWHeight D N) / 4 * L := by
    dsimp only [dirichletLTwistedSmoothedConductorLogEdgeWidth]
    change M * z ≤ (1 / (4398046511104 * LM ^ 9)) / 4 * L
    rw [div_mul_eq_mul_div, one_div, inv_mul_eq_div, div_div]
    rw [le_div_iff₀ (show 0 < (4398046511104 * LM ^ 9) * 4 by positivity)]
    nlinarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hexp : Real.exp (-(dirichletLTwistedSmoothedConductorLogEdgeWidth q
      (nonquadraticPointwiseSWHeight D N) / 4 * L)) ≤ Real.exp (-M * z) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hL1 : 1 ≤ L := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).le.trans hlog
  have hpow : Real.exp (-M * z) ≤ (Real.log (N : ℝ) ^ E)⁻¹ := by
    calc
      Real.exp (-M * z) = L ^ (-M) := by
        rw [Real.rpow_def_of_pos hLpos]
        congr 1
        dsimp only [z]
        ring
      _ ≤ L ^ (-(E : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by dsimp only [M]; linarith)
      _ = (Real.log (N : ℝ) ^ E)⁻¹ := by
        rw [Real.rpow_neg hLpos.le, Real.rpow_natCast]
  rw [dirichletLTwistedSmoothedConductorLogFinalLeft,
    Real.rpow_def_of_pos hNpos]
  rw [show Real.log (N : ℝ) *
      (1 - dirichletLTwistedSmoothedConductorLogEdgeWidth q
        (nonquadraticPointwiseSWHeight D N) / 4) =
      Real.log (N : ℝ) +
        (-(dirichletLTwistedSmoothedConductorLogEdgeWidth q
          (nonquadraticPointwiseSWHeight D N) / 4 * L)) by
      dsimp only [L]; ring, Real.exp_add, Real.exp_log hNpos]
  calc
    (N : ℝ) * Real.exp (-(dirichletLTwistedSmoothedConductorLogEdgeWidth q
        (nonquadraticPointwiseSWHeight D N) / 4 * L)) ≤
        (N : ℝ) * Real.exp (-M * z) := by gcongr
    _ ≤ (N : ℝ) * (Real.log (N : ℝ) ^ E)⁻¹ := by gcongr
    _ = (N : ℝ) / Real.log (N : ℝ) ^ E := by rw [div_eq_mul_inv]

theorem rpow_one_add_inv_log_nat (N : ℕ) (hN : 1 < N) :
    (N : ℝ) ^ (1 + (Real.log (N : ℝ))⁻¹) = Real.exp 1 * N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [Real.rpow_add hNr, Real.rpow_one, Real.rpow_def_of_pos hNr]
  rw [mul_inv_cancel₀ hlog]
  ring

/-- Chebyshev's bound `|∑_{n ≤ N} Λ(n) χ(n)| ≤ ψ(N) ≤ (log 4 + 4) N`. -/
theorem norm_lambdaCharacterPrefix_le_const_mul_self
    (N q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖lambdaCharacterPrefix N q χ‖ ≤ (Real.log 4 + 4) * N := by
  rw [lambdaCharacterPrefix]
  calc
    ‖∑ n ∈ Finset.range (N + 1), DirichletCharacter.twistedVonMangoldtCoeff χ n‖ ≤
        ∑ n ∈ Finset.range (N + 1), ‖DirichletCharacter.twistedVonMangoldtCoeff χ n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [DirichletCharacter.twistedVonMangoldtCoeff, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
        (DirichletCharacter.norm_le_one χ n)
    _ = Chebyshev.psi (N : ℝ) := by
      rw [Chebyshev.psi_eq_sum_range]
      norm_num
    _ ≤ (Real.log 4 + 4) * N :=
      Chebyshev.psi_le_const_mul_self (by positivity)

/-- Replacing the cutoff `n ≤ X` by the smooth weight `ν_ε(n / X)` changes the twisted
sum by `O(ε X log X)`, with a constant independent of `q` and `χ`. -/
theorem exists_uniform_twistedSmoothedPsiClose
    {SmoothingF : ℝ → ℝ} (_diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
      (X : ℝ), 3 < X → ∀ (ε : ℝ), 0 < ε → ε < 1 → 2 < X * ε →
      ‖DirichletCharacter.twistedSmoothedPsi χ SmoothingF ε X -
        lambdaCharacterPrefix ⌊X⌋₊ q χ‖ ≤ C * ε * X * Real.log X := by
  obtain ⟨c₁, c₁_pos, c₁_eq, hc₁⟩ :=
    Smooth1Properties_below suppSmoothingF mass_one
  obtain ⟨c₂, c₂_pos, c₂_eq, hc₂⟩ :=
    Smooth1Properties_above suppSmoothingF
  have c₁_lt : c₁ < 1 := by
    rw [c₁_eq]
    exact lt_trans Real.log_two_lt_d9 (by norm_num)
  have c₂_lt : c₂ < 2 := by
    rw [c₂_eq]
    nth_rewrite 3 [← mul_one 2]
    apply mul_lt_mul'
    · rfl
    · exact lt_trans Real.log_two_lt_d9 (by norm_num)
    · exact Real.log_nonneg (by norm_num)
    · positivity
  let C₀ : ℝ := 6 * (3 * c₁ + c₂)
  have C₀_pos : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨2 * C₀, mul_pos (by norm_num) C₀_pos, ?_⟩
  intro q _ χ X X_gt_three ε ε_pos ε_lt_one Xε_gt_two
  have X_pos : 0 < X := by linarith
  have n_div_X_pos {n : ℕ} (hn : 0 < n) : 0 < (n : ℝ) / X := by positivity
  have smoothAbove (n : ℕ) (hn : 0 < n) :
      Smooth1 SmoothingF ε (n / X) ≤ 1 :=
    Smooth1LeOne SmoothingFnonneg mass_one ε_pos (n_div_X_pos hn)
  have smoothBelow (n : ℕ) (hn : 0 < n) :
      0 ≤ Smooth1 SmoothingF ε (n / X) :=
    Smooth1Nonneg SmoothingFnonneg (n_div_X_pos hn) ε_pos
  have smoothOne (n : ℕ) (hn : 0 < n)
      (hnle : (n : ℝ) ≤ X * (1 - c₁ * ε)) :
      Smooth1 SmoothingF ε (n / X) = 1 := by
    apply hc₁ (ε := ε) (n / X) ε_pos (n_div_X_pos hn)
    exact (div_le_iff₀' X_pos).mpr hnle
  have smoothZero (n : ℕ)
      (hn : 1 + c₂ * ε ≤ (n : ℝ) / X) :
      Smooth1 SmoothingF ε (n / X) = 0 :=
    hc₂ (ε := ε) (n / X) ⟨ε_pos, ε_lt_one⟩ hn
  have X_bound_1 : 1 ≤ X * ε * c₁ := by
    rw [c₁_eq, ← div_le_iff₀]
    · have h : 1 / Real.log 2 < 2 := by
        nth_rewrite 2 [← one_div_one_div 2]
        rw [one_div_lt_one_div]
        · exact lt_of_le_of_lt (by norm_num) Real.log_two_gt_d9
        · exact Real.log_pos (by norm_num)
        · norm_num
      exact le_of_lt (h.trans Xε_gt_two)
    · exact Real.log_pos (by norm_num)
  have X_bound_2 : 1 ≤ X * ε * c₂ := by
    rw [c₂_eq, ← div_le_iff₀]
    · have h : 1 / (2 * Real.log 2) < 2 := by
        nth_rewrite 3 [← one_div_one_div 2]
        rw [one_div_lt_one_div, ← one_mul (1 / 2)]
        · apply mul_lt_mul
          · norm_num
          · exact le_of_lt (lt_trans (by norm_num) Real.log_two_gt_d9)
          · norm_num
          · norm_num
        · norm_num
          exact Real.log_pos (by norm_num)
        · norm_num
      exact le_of_lt (h.trans Xε_gt_two)
    · norm_num
      exact Real.log_pos (by norm_num)
  exact DirichletCharacter.twistedSmoothedPsiClose_aux
    SmoothingF c₁ c₁_pos c₁_lt c₂ c₂_pos c₂_lt hc₂ C₀ rfl
    ε ε_pos ε_lt_one X X_pos X_gt_three X_bound_1 X_bound_2
    smoothAbove smoothBelow smoothOne smoothZero χ

/-- If `χ² ≠ 1` and the left edge, horizontal edge, tail and smoothing terms are each at
most `R`, then `|∑_{n ≤ X} Λ(n) χ(n)| ≤ K R`, where `K` depends only on `ν`. -/
theorem exists_nonquadraticPrefix_le_of_bounds
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1) :
    ∃ K > 0, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
      {T d ε X R : ℝ}, χ ^ 2 ≠ 1 → 3 ≤ T → 0 < d → d ≤ 1 →
      0 < ε → ε < 1 → 3 < X → 2 < X * ε → 0 ≤ R →
      T * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 *
          X ^ (dirichletLTwistedSmoothedConductorLogFinalLeft q T) / ε ≤ R →
      (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 * X ^ (1 + d) /
          (ε * (1 + T ^ 2)) ≤ R →
      X ^ (1 + d) * (1 + d⁻¹ ^ 2) / (ε * T) ≤ R →
      ε * X * Real.log X ≤ R →
      ‖lambdaCharacterPrefix ⌊X⌋₊ q χ‖ ≤ K * R := by
  obtain ⟨K₀, hK₀, hcontour⟩ :=
    exists_dirichletLTwistedSmoothedNonquadraticErrorAssembly
      diffν νpos suppν mass_one
  obtain ⟨C₀, hC₀, hclose⟩ :=
    exists_uniform_twistedSmoothedPsiClose diffν suppν νpos mass_one
  let K := 3 * K₀ + C₀ + 1
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro q _ χ T d ε X R hχ hT hd hd1 hε hε1 hX hXε hR
    hleft hhoriz htail hsmooth
  have hs := hcontour (X := X) χ hχ hT hd hd1 hε hε1 (by linarith)
  have hc := hclose χ X hX ε hε hε1 hXε
  have hsmoothed : ‖DirichletCharacter.twistedSmoothedPsi χ ν ε X‖ ≤
      3 * K₀ * R := by
    calc
      _ ≤ K₀ *
          (T * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 *
                X ^ (dirichletLTwistedSmoothedConductorLogFinalLeft q T) / ε +
            (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 * X ^ (1 + d) /
                (ε * (1 + T ^ 2)) +
            X ^ (1 + d) * (1 + d⁻¹ ^ 2) / (ε * T)) := hs
      _ ≤ K₀ * (R + R + R) := by gcongr
      _ = 3 * K₀ * R := by ring
  have hremove :
      ‖DirichletCharacter.twistedSmoothedPsi χ ν ε X -
          lambdaCharacterPrefix ⌊X⌋₊ q χ‖ ≤ C₀ * R := by
    calc
      _ ≤ C₀ * ε * X * Real.log X := hc
      _ = C₀ * (ε * X * Real.log X) := by ring
      _ ≤ C₀ * R := mul_le_mul_of_nonneg_left hsmooth hC₀.le
  calc
    ‖lambdaCharacterPrefix ⌊X⌋₊ q χ‖ =
        ‖DirichletCharacter.twistedSmoothedPsi χ ν ε X -
          (DirichletCharacter.twistedSmoothedPsi χ ν ε X -
            lambdaCharacterPrefix ⌊X⌋₊ q χ)‖ := by ring_nf
    _ ≤ ‖DirichletCharacter.twistedSmoothedPsi χ ν ε X‖ +
        ‖DirichletCharacter.twistedSmoothedPsi χ ν ε X -
          lambdaCharacterPrefix ⌊X⌋₊ q χ‖ := norm_sub_le _ _
    _ ≤ 3 * K₀ * R + C₀ * R := add_le_add hsmoothed hremove
    _ ≤ K * R := by dsimp only [K]; nlinarith

private theorem eventually_log_pow_le_sqrt_nat (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ^ k ≤ Real.sqrt N := by
  exact log_pow_le_sqrt_eventually k

/-- With `ε = L^(-(P + 3))`, `T = L^(2P + 30)` and `P ≥ D + 20`, the tail term and the
smoothing term are both at most `X / L^D`. -/
theorem pointwiseSW_tail_smoothing_le
    {X L : ℝ} {D P : ℕ} (hX : 0 ≤ X) (hL : 2 ≤ L) (hDP : D + 20 ≤ P) :
    Real.exp 1 * X * (1 + L ^ 2) /
        ((L ^ (P + 3))⁻¹ * L ^ (2 * P + 30)) ≤ X / L ^ D ∧
      (L ^ (P + 3))⁻¹ * X * L ≤ X / L ^ D := by
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have htailPower : 8 * L ^ 2 ≤ L ^ (2 * P + 30) / (L ^ D * L ^ (P + 3)) := by
    apply (le_div_iff₀ (by positivity)).2
    have h8 : (8 : ℝ) ≤ L ^ 3 := by
      calc
        (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL 3
    calc
      _ ≤ (L ^ 3 * L ^ 2) * (L ^ D * L ^ (P + 3)) := by gcongr
      _ = L ^ (D + (P + 3) + 5) := by
        simp only [← pow_add]
        congr 1
        omega
      _ ≤ L ^ (2 * P + 30) := pow_le_pow_right₀ hL1 (by omega)
  constructor
  · rw [div_le_iff₀ (by positivity : 0 < (L ^ (P + 3))⁻¹ * L ^ (2 * P + 30))]
    calc
      Real.exp 1 * X * (1 + L ^ 2) ≤ 8 * X * L ^ 2 := by
        have he : Real.exp 1 ≤ 4 := Real.exp_one_lt_d9.le.trans (by norm_num)
        have htwo : 1 + L ^ 2 ≤ 2 * L ^ 2 := by nlinarith [sq_nonneg L]
        calc
          _ ≤ 4 * X * (2 * L ^ 2) := by gcongr
          _ = _ := by ring
      _ = X * (8 * L ^ 2) := by ring
      _ ≤ X * (L ^ (2 * P + 30) / (L ^ D * L ^ (P + 3))) :=
        mul_le_mul_of_nonneg_left htailPower hX
      _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
  · have hsmoothPower : L * L ^ D ≤ L ^ (P + 3) := by
      rw [← pow_succ']
      exact pow_le_pow_right₀ hL1 (by omega)
    have hratio : L / L ^ (P + 3) ≤ 1 / L ^ D := by
      apply (div_le_div_iff₀ (pow_pos hLpos _) (pow_pos hLpos _)).2
      simpa only [one_mul] using hsmoothPower
    calc
      (L ^ (P + 3))⁻¹ * X * L = X * (L / L ^ (P + 3)) := by ring
      _ ≤ X * (1 / L ^ D) := mul_le_mul_of_nonneg_left hratio hX
      _ = X / L ^ D := by ring

/-- Take `P = D + 20`, `T = (log N)^(2P + 30)`, `d = 1 / log N` and
`ε = (log N)^(-(P + 3))`. For large `N` and all `q ≤ (log N)^C`, the left edge, horizontal
edge, tail and smoothing terms are each at most `N / (log N)^D`. -/
theorem eventually_nonquadraticPointwiseSW_terms_le (C D : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ∀ _inst : NeZero q,
      q ≤ logConductorThreshold N C →
      let P := D + 20
      let T := nonquadraticPointwiseSWHeight P N
      let d := nonquadraticPointwiseSWDelta N
      let ε := nonquadraticPointwiseSWEpsilon P N
      let R := (N : ℝ) / Real.log (N : ℝ) ^ D
      3 ≤ T ∧ 0 < d ∧ d ≤ 1 ∧ 0 < ε ∧ ε < 1 ∧ 3 < (N : ℝ) ∧
      2 < (N : ℝ) * ε ∧ 0 ≤ R ∧
      T * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 *
          (N : ℝ) ^ (dirichletLTwistedSmoothedConductorLogFinalLeft q T) / ε ≤ R ∧
      (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 *
          (N : ℝ) ^ (1 + d) / (ε * (1 + T ^ 2)) ≤ R ∧
      (N : ℝ) ^ (1 + d) * (1 + d⁻¹ ^ 2) / (ε * T) ≤ R ∧
      ε * (N : ℝ) * Real.log (N : ℝ) ≤ R := by
  let P := D + 20
  let B := nonquadraticPointwiseSWHeightExponent P
  let A : ℝ := C + B + 3
  let E := B + P + D + 20
  have hleft := eventually_nonquadraticPointwiseSW_leftEdge C P E
  have hlogtop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpoly := hlogtop.eventually
    (eventually_ge_atTop (max (Real.exp 1) (max (A ^ 11) 4)))
  have hsqrt := eventually_log_pow_le_sqrt_nat (P + 4)
  filter_upwards [hleft, hpoly, hsqrt, eventually_ge_atTop (4 : ℕ)] with
      N hleft hLlarge hsqrt hN
  intro q _inst hq
  let L := Real.log (N : ℝ)
  let T := nonquadraticPointwiseSWHeight P N
  let d := nonquadraticPointwiseSWDelta N
  let ε := nonquadraticPointwiseSWEpsilon P N
  let R := (N : ℝ) / L ^ D
  have hexpL : Real.exp 1 ≤ L := (le_max_left _ _).trans hLlarge
  have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hexpL
  have hL1 : 1 ≤ L := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).le.trans
    hexpL
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hA11 : A ^ 11 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hLlarge)
  have h4L : (4 : ℝ) ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hLlarge)
  have hlogL : Real.log L ≤ L := Real.log_le_self hLpos.le
  have hLM0 := dirichletLTwistedSmoothedConductorLogLM_le_loglog_pointwise
    C P N q hexpL hq
  have hLM : dirichletLTwistedSmoothedConductorLogLM q T ≤ A * L := by
    calc
      _ ≤ (C + nonquadraticPointwiseSWHeightExponent P + 3 : ℕ) * L :=
        hLM0.trans (mul_le_mul_of_nonneg_left hlogL (by positivity))
      _ = A * L := by norm_num [A, B]
  have hLMpos : 0 < dirichletLTwistedSmoothedConductorLogLM q T := by
    dsimp only [dirichletLTwistedSmoothedConductorLogLM]
    have hc : (1 : ℝ) ≤ dirichletLTwistedSmoothedConductorLogCutoff q T := by
      exact_mod_cast (show 1 ≤ dirichletLTwistedSmoothedConductorLogCutoff q T by
        dsimp only [dirichletLTwistedSmoothedConductorLogCutoff,
          dirichletLNonquadraticConductorLogCutoff,
          dirichletLNonquadraticConductorLogHeightBlock]
        exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne q) (by omega)))
    linarith [Real.log_nonneg hc]
  have hLM11 : (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 ≤ L ^ 12 := by
    calc
      _ ≤ (A * L) ^ 11 := pow_le_pow_left₀ hLMpos.le hLM 11
      _ = A ^ 11 * L ^ 11 := by rw [mul_pow]
      _ ≤ L * L ^ 11 := mul_le_mul_of_nonneg_right hA11 (pow_nonneg hLpos.le _)
      _ = L ^ 12 := by ring
  have hT : T = L ^ B := rfl
  have hd : d = L⁻¹ := rfl
  have heps : ε = (L ^ (P + 3))⁻¹ := rfl
  have hNpos : (0 : ℝ) < N := by positivity
  have hNpow : (N : ℝ) ^ (1 + d) = Real.exp 1 * N := by
    simpa only [hd] using rpow_one_add_inv_log_nat N (by omega)
  have hR0 : 0 ≤ R := div_nonneg (by positivity) (pow_nonneg hLpos.le _)
  have hleftN := hleft q _inst hq
  have hleftPay :
      T * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 *
          (N : ℝ) ^ (dirichletLTwistedSmoothedConductorLogFinalLeft q T) / ε ≤ R := by
    rw [hT, heps, div_inv_eq_mul]
    calc
      L ^ B * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 *
          (N : ℝ) ^ (dirichletLTwistedSmoothedConductorLogFinalLeft q T) * L ^ (P + 3) ≤
          L ^ B * L ^ 12 * ((N : ℝ) / L ^ E) * L ^ (P + 3) := by gcongr
      _ ≤ (N : ℝ) / L ^ D := by
        rw [div_eq_mul_inv]
        field_simp
        dsimp only [E, B, P, nonquadraticPointwiseSWHeightExponent]
        ring_nf
        gcongr
        omega
  have hcommon := pointwiseSW_tail_smoothing_le (X := (N : ℝ))
    (D := D) (P := P) hNpos.le (by linarith : 2 ≤ L) (by dsimp only [P]; omega)
  have htailPay :
      (N : ℝ) ^ (1 + d) * (1 + d⁻¹ ^ 2) / (ε * T) ≤ R := by
    rw [hNpow, hd, heps, hT, inv_inv]
    exact hcommon.1
  have hhorizPay :
      (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 *
          (N : ℝ) ^ (1 + d) / (ε * (1 + T ^ 2)) ≤ R := by
    apply (pointwiseSW_horizontal_le_tail (L := d⁻¹)
      (Real.rpow_nonneg hNpos.le _) (by rw [heps]; positivity)
      (by rw [hT]; positivity) ?_).trans htailPay
    exact hLM11.trans (by
      rw [hT]
      exact pow_le_pow_right₀ hL1 (by
        dsimp only [B, P, nonquadraticPointwiseSWHeightExponent]; omega))
  have hsmoothPay : ε * (N : ℝ) * L ≤ R := hcommon.2
  have hT3 : 3 ≤ T := by
    rw [hT]
    have hLB : L ≤ L ^ B := by
      simpa only [pow_one] using pow_le_pow_right₀ hL1 (show 1 ≤ B by
        dsimp only [B, nonquadraticPointwiseSWHeightExponent]; omega)
    exact (show (3 : ℝ) ≤ 4 by norm_num).trans (h4L.trans hLB)
  have hdpos : 0 < d := by rw [hd]; positivity
  have hd1 : d ≤ 1 := by rw [hd]; exact (inv_le_one₀ hLpos).2 hL1
  have hepspos : 0 < ε := by rw [heps]; positivity
  have heps1 : ε < 1 := by
    rw [heps]
    have hLgt1 : 1 < L := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hexpL
    exact (inv_lt_one₀ (pow_pos hLpos _)).2 (one_lt_pow₀ hLgt1 (by omega))
  have hXeps : 2 < (N : ℝ) * ε := by
    rw [heps]
    have hsqrtpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by positivity)
    rw [← div_eq_mul_inv]
    apply (lt_div_iff₀ (pow_pos hLpos _)).2
    have h2L : (2 : ℝ) ≤ L := (show (2 : ℝ) ≤ 4 by norm_num).trans h4L
    calc
      2 * L ^ (P + 3) ≤ L * L ^ (P + 3) :=
        mul_le_mul_of_nonneg_right h2L (pow_nonneg hLpos.le _)
      _ = L ^ (P + 4) := by rw [← pow_succ']
      _ ≤ Real.sqrt (N : ℝ) := hsqrt
      _ < (N : ℝ) := by
        have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
        exact Real.sqrt_lt_self_iff.mpr hNr
  exact ⟨hT3, hdpos, hd1, hepspos, heps1, by exact_mod_cast (show 3 < N by omega),
    hXeps, hR0, hleftPay, hhorizPay, htailPay, hsmoothPay⟩

/-- Siegel–Walfisz bound for `χ² ≠ 1`: if `q ≤ (log N)^C`, then
`|∑_{n ≤ y} Λ(n) χ(n)| ≤ K N / (log N)^D` for all `y ≤ N`. For `y > 2√N` the contour
parameters are chosen in terms of `N`; for `y ≤ 2√N` Chebyshev's bound suffices. -/
theorem exists_nonquadraticPointwiseSiegelWalfisz_uniform
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    (C D : ℕ) :
    ∃ K > 0, ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ∀ _inst : NeZero q,
      q ≤ logConductorThreshold N C → ∀ χ : DirichletCharacter ℂ q,
        χ ^ 2 ≠ 1 → ∀ y : ℕ, y ≤ N →
          ‖lambdaCharacterPrefix y q χ‖ ≤
            K * (N : ℝ) / Real.log (N : ℝ) ^ D := by
  obtain ⟨K₀, hK₀, hexact⟩ :=
    exists_nonquadraticPrefix_le_of_bounds diffν νpos suppν mass_one
  let c : ℝ := Real.log 4 + 4
  let K : ℝ := K₀ + 2 * c
  refine ⟨K, by dsimp only [K, c]; positivity, ?_⟩
  have hpay := eventually_nonquadraticPointwiseSW_terms_le C D
  have hsqrt := eventually_log_pow_le_sqrt_nat D
  let P := D + 20
  have hsqrtStrong := eventually_log_pow_le_sqrt_nat (P + 4)
  have hlogtop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog4ev := hlogtop.eventually (eventually_ge_atTop (4 : ℝ))
  filter_upwards [hpay, hsqrt, hsqrtStrong, hlog4ev,
      eventually_ge_atTop (4 : ℕ)] with N hpay hsqrt hsqrtStrong hlog4 hN
  intro q _inst hq χ hχ y hy
  let T := nonquadraticPointwiseSWHeight P N
  let d := nonquadraticPointwiseSWDelta N
  let ε := nonquadraticPointwiseSWEpsilon P N
  let R := (N : ℝ) / Real.log (N : ℝ) ^ D
  obtain ⟨hT, hd, hd1, hε, hε1, hN3, hNε, hR,
    hleft, hhoriz, htail, hsmooth⟩ := hpay q _inst hq
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < N by omega))
  have hRpos : 0 < R := div_pos (by positivity) (pow_pos hlogpos _)
  by_cases hsmall : (y : ℝ) ≤ 2 * Real.sqrt N
  · have helem := norm_lambdaCharacterPrefix_le_const_mul_self y q χ
    have hsqrtN : Real.sqrt (N : ℝ) * Real.sqrt N = N := by
      rw [← pow_two, Real.sq_sqrt (by positivity)]
    have hsmallR : 2 * c * Real.sqrt N ≤ 2 * c * R := by
      have hc : 0 ≤ c := by dsimp only [c]; positivity
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hc)
      rw [show R = (N : ℝ) / Real.log (N : ℝ) ^ D by rfl,
        le_div_iff₀ (pow_pos hlogpos _)]
      calc
        Real.sqrt N * Real.log (N : ℝ) ^ D ≤ Real.sqrt N * Real.sqrt N := by gcongr
        _ = N := hsqrtN
    calc
      ‖lambdaCharacterPrefix y q χ‖ ≤ c * y := helem
      _ ≤ c * (2 * Real.sqrt N) := by gcongr
      _ = 2 * c * Real.sqrt N := by ring
      _ ≤ 2 * c * R := hsmallR
      _ ≤ K * R := by dsimp only [K]; nlinarith
      _ = K * (N : ℝ) / Real.log (N : ℝ) ^ D := by rw [show R = (N : ℝ) /
          Real.log (N : ℝ) ^ D by rfl, mul_div_assoc]
  · have hlarge : 2 * Real.sqrt N < (y : ℝ) := lt_of_not_ge hsmall
    have hypos : (0 : ℝ) < y := lt_trans (by positivity : (0 : ℝ) < 2 * Real.sqrt N) hlarge
    have hNr4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
    have hsqrt2 : (2 : ℝ) ≤ Real.sqrt N := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity), Real.sqrt_nonneg (N : ℝ)]
    have hy3 : (3 : ℝ) < y := by nlinarith
    have hyN : (y : ℝ) ≤ N := by exact_mod_cast hy
    have hLMone : 1 ≤ dirichletLTwistedSmoothedConductorLogLM q T := by
      dsimp only [dirichletLTwistedSmoothedConductorLogLM]
      have hc : (1 : ℝ) ≤ dirichletLTwistedSmoothedConductorLogCutoff q T := by
        exact_mod_cast (show 1 ≤ dirichletLTwistedSmoothedConductorLogCutoff q T by
          dsimp only [dirichletLTwistedSmoothedConductorLogCutoff,
            dirichletLNonquadraticConductorLogCutoff,
            dirichletLNonquadraticConductorLogHeightBlock]
          exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne q) (by omega)))
      linarith [Real.log_nonneg hc]
    have hfinal0 : 0 ≤ dirichletLTwistedSmoothedConductorLogFinalLeft q T := by
      dsimp only [dirichletLTwistedSmoothedConductorLogFinalLeft,
        dirichletLTwistedSmoothedConductorLogEdgeWidth]
      have hp9 : 1 ≤ (dirichletLTwistedSmoothedConductorLogLM q T) ^ 9 :=
        one_le_pow₀ hLMone
      have hden : (4 : ℝ) ≤ 4 * (4398046511104 *
          (dirichletLTwistedSmoothedConductorLogLM q T) ^ 9) := by nlinarith
      rw [div_div]
      have hden' : (1 : ℝ) ≤ 4398046511104 *
          (dirichletLTwistedSmoothedConductorLogLM q T) ^ 9 * 4 := by
        nlinarith
      exact sub_nonneg.mpr ((div_le_one (by positivity)).2 hden')
    have hrpowLeft :
        (y : ℝ) ^ dirichletLTwistedSmoothedConductorLogFinalLeft q T ≤
          (N : ℝ) ^ dirichletLTwistedSmoothedConductorLogFinalLeft q T :=
      Real.rpow_le_rpow (by positivity) hyN hfinal0
    have hrpowRight : (y : ℝ) ^ (1 + d) ≤ (N : ℝ) ^ (1 + d) := by
      apply Real.rpow_le_rpow (by positivity) hyN
      linarith
    have hleftY : T * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 *
        (y : ℝ) ^ (dirichletLTwistedSmoothedConductorLogFinalLeft q T) / ε ≤ R := by
      apply le_trans _ hleft
      gcongr
    have hhorizY : (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 *
        (y : ℝ) ^ (1 + d) / (ε * (1 + T ^ 2)) ≤ R := by
      apply le_trans _ hhoriz
      gcongr
    have htailY : (y : ℝ) ^ (1 + d) * (1 + d⁻¹ ^ 2) / (ε * T) ≤ R := by
      apply le_trans _ htail
      gcongr
    have hsmoothY : ε * (y : ℝ) * Real.log (y : ℝ) ≤ R := by
      apply le_trans _ hsmooth
      have hlogy : Real.log (y : ℝ) ≤ Real.log (N : ℝ) := Real.log_le_log hypos hyN
      gcongr
    have hyε : 2 < (y : ℝ) * ε := by
      have hεdef : ε = (Real.log (N : ℝ) ^ (P + 3))⁻¹ := rfl
      rw [hεdef, ← div_eq_mul_inv]
      apply (lt_div_iff₀ (pow_pos hlogpos _)).2
      calc
        2 * Real.log (N : ℝ) ^ (P + 3) ≤
            2 * Real.log (N : ℝ) ^ (P + 4) := by
              exact mul_le_mul_of_nonneg_left
                (pow_le_pow_right₀ (by linarith [hlog4]) (by omega)) (by norm_num)
        _ ≤ 2 * Real.sqrt N := by gcongr
        _ < (y : ℝ) := hlarge
    have hbound := hexact χ (T := T) (d := d) (ε := ε) (X := (y : ℝ)) (R := R)
      hχ hT hd hd1 hε hε1 hy3 hyε hR hleftY hhorizY htailY hsmoothY
    have hfloor : ⌊(y : ℝ)⌋₊ = y := Nat.floor_natCast y
    rw [hfloor] at hbound
    calc
      ‖lambdaCharacterPrefix y q χ‖ ≤ K₀ * R := hbound
      _ ≤ K * R := by
        apply mul_le_mul_of_nonneg_right _ hR
        dsimp only [K, c]
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 4)]
      _ = K * (N : ℝ) / Real.log (N : ℝ) ^ D := by rw [show R = (N : ℝ) /
          Real.log (N : ℝ) ^ D by rfl, mul_div_assoc]

end

end BombieriVinogradov

end
