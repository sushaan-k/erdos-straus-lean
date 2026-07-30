import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Tactic
import EscAnalytic.Core
import EscAnalytic.Inputs

/-!
# Mass and tensor estimates

This module provides the abstract mass and tensor estimates used by `prop:M`,
`thm:tensor-e`, `prop:mu`, and `prop:event-tensor`.  The principal conclusions
are the quadratic exact-divisor mass `M₁, M_φ ≍ (log X)²`, the cubic event mass
`μ_b ≍ (log X)³`, and the corresponding one- and two-modulus tensor bounds.

## Structure

The analytic factors are represented by explicit `FactorAsymp` data.  The
product calculation in `mass_law` proves the cancellation of `log z` between
the small-prime factor and the rough reciprocal factor.  The tensor bounds then
reuse the same constants.  Concrete carrier reductions are supplied for
`Inputs.sAvgRecip`, `Inputs.sAvgPhi`, and `Inputs.rough_sqf_recip`.

Asymptotics `f ≍ g` are rendered as a two-sided constant sandwich
`c·g ≤ f ≤ C·g` valid for `X` large (the manuscript's `≍`); `f ≪ g` as a
one-sided `f ≤ C·g`.  This module declares no axioms.
-/

namespace EscAnalytic

open Filter
open scoped BigOperators

/-! ## Event-mass factor asymptotics

The prop:mu proof factors the certificate mass through three
nested sums whose individual asymptotics are quoted from the cited inputs:

* the small-prime medium factor (the `d₋`-sum folded with the `1/φ(4ρ(e))`
  exact-divisor mass), `Σ_b ≍ (log X)² · log z`  (`lem:small-certificate-average`);
* the rough cofactor reciprocal `d₊`-sum, `≍ (log X)/(log z)`
  (`lem:rough-initial` / `eq:rough-recip-uniform`);

and the product of these is `μ_b ≍ (log X)³` after the `log z` cancels.

We package each manuscript factor-asymptotic as a `FactorAsymp` datum: a function
`f : ℝ → ℝ`, a reference shape `g : ℝ → ℝ`, two constants `0 < c ≤ C`, a
threshold `X₀`, and the two-sided sandwich together with nonnegativity of `f`.
This is the direct Lean formulation of "`f ≍ g` uniformly for large `X`". -/

/-- A two-sided asymptotic `f ≍ g` valid for `X ≥ X₀`, with explicit positive
constants and a sign on `f` (the manuscript's `≍`, encoded for `Filter.atTop`).

This bundles *data* (the two constants and the threshold) with proofs, so it lives
in `Type`, not `Prop`. -/
structure FactorAsymp (f g : ℝ → ℝ) where
  /-- lower constant -/
  c : ℝ
  /-- upper constant -/
  C : ℝ
  /-- threshold beyond which the sandwich holds -/
  X₀ : ℝ
  c_pos : 0 < c
  C_pos : 0 < C
  /-- `f` is nonnegative for large `X` (the sums are reciprocal sums). -/
  f_nonneg : ∀ X : ℝ, X₀ ≤ X → 0 ≤ f X
  /-- the two-sided sandwich `c·g ≤ f ≤ C·g`. -/
  sandwich : ∀ X : ℝ, X₀ ≤ X → c * g X ≤ f X ∧ f X ≤ C * g X

namespace FactorAsymp

/-- The lower bound `c·g X ≤ f X` of a `FactorAsymp`. -/
theorem lower {f g : ℝ → ℝ} (h : FactorAsymp f g) {X : ℝ} (hX : h.X₀ ≤ X) :
    h.c * g X ≤ f X := (h.sandwich X hX).1

/-- The upper bound `f X ≤ C·g X` of a `FactorAsymp`. -/
theorem upper {f g : ℝ → ℝ} (h : FactorAsymp f g) {X : ℝ} (hX : h.X₀ ≤ X) :
    f X ≤ h.C * g X := (h.sandwich X hX).2

/-- Transfer a factor asymptotic across an eventual equality of carriers. -/
noncomputable def of_eventually_eq {f f' g : ℝ → ℝ}
    (h : FactorAsymp f g) (Xeq : ℝ)
    (heq : ∀ X : ℝ, Xeq ≤ X → f' X = f X) :
    FactorAsymp f' g :=
  { c := h.c
    C := h.C
    X₀ := max h.X₀ Xeq
    c_pos := h.c_pos
    C_pos := h.C_pos
    f_nonneg := fun X hX => by
      have hXh : h.X₀ ≤ X := le_trans (le_max_left _ _) hX
      have hXe : Xeq ≤ X := le_trans (le_max_right _ _) hX
      rw [heq X hXe]
      exact h.f_nonneg X hXh
    sandwich := fun X hX => by
      have hXh : h.X₀ ≤ X := le_trans (le_max_left _ _) hX
      have hXe : Xeq ≤ X := le_trans (le_max_right _ _) hX
      rw [heq X hXe]
      exact h.sandwich X hXh }

/-- Transfer a factor asymptotic across an eventual two-sided comparison by
fixed positive constants.

This is the formal finite-Euler-factor-deletion principle used by the fixed-`m`
route: after deleting a fixed set of prime factors or inserting a fixed
multiplier, the modified reciprocal carrier need only be sandwiched between
constant multiples of the original carrier.  The asymptotic shape is unchanged;
only the constants and threshold change. -/
noncomputable def of_eventual_const_comparable {f f' g : ℝ → ℝ}
    (h : FactorAsymp f g) (Xcmp a A : ℝ)
    (ha : 0 < a) (hA : 0 < A)
    (hcmp : ∀ X : ℝ, Xcmp ≤ X → a * f X ≤ f' X ∧ f' X ≤ A * f X) :
    FactorAsymp f' g :=
  { c := a * h.c
    C := A * h.C
    X₀ := max h.X₀ Xcmp
    c_pos := mul_pos ha h.c_pos
    C_pos := mul_pos hA h.C_pos
    f_nonneg := fun X hX => by
      have hXh : h.X₀ ≤ X := le_trans (le_max_left _ _) hX
      have hXcmp : Xcmp ≤ X := le_trans (le_max_right _ _) hX
      have hf_nonneg : 0 ≤ f X := h.f_nonneg X hXh
      exact le_trans (mul_nonneg ha.le hf_nonneg) (hcmp X hXcmp).1
    sandwich := fun X hX => by
      have hXh : h.X₀ ≤ X := le_trans (le_max_left _ _) hX
      have hXcmp : Xcmp ≤ X := le_trans (le_max_right _ _) hX
      have hlo := h.lower hXh
      have hhi := h.upper hXh
      have hcmpX := hcmp X hXcmp
      refine ⟨?_, ?_⟩
      · calc
          (a * h.c) * g X = a * (h.c * g X) := by ring
          _ ≤ a * f X := mul_le_mul_of_nonneg_left hlo ha.le
          _ ≤ f' X := hcmpX.1
      · calc
          f' X ≤ A * f X := hcmpX.2
          _ ≤ A * (h.C * g X) := mul_le_mul_of_nonneg_left hhi hA.le
          _ = (A * h.C) * g X := by ring }

end FactorAsymp

/-! ## The certificate mass `μ_b`, encoded as the factored product.

Following `eq:certificate-mass-main` and the closing display, the certificate mass at scale `X` is, up to absolute constants,
the product of the small-prime certificate average `Σ_b` (the folded `d₋`/exact
divisor mass, `≍ (log X)² log z`) and the rough `d₊`-reciprocal factor
(`≍ (log X)/(log z)`).  We record `μ_b` as exactly this product of the two
constituent functions. -/

/-- The certificate mass `μ_b` (`eq:mub-def`, factored as
`eq:certificate-mass-main`).  Encoded as the product of the
small-prime certificate average `sigmaSmall` (`Σ_b`, `lem:small-certificate-average`)
and the rough `d₊`-reciprocal factor `roughFactor`.  The base class `b` and the
modulus `P(z)` are carried as parameters but the manuscript's asymptotic is
uniform in `b`, so they only fix which constituent functions are used. -/
noncomputable def muB (_P : Params) (_b : ℕ) (sigmaSmall roughFactor : ℝ → ℝ)
    (X : ℝ) : ℝ :=
  sigmaSmall X * roughFactor X

/-- The reference shape `(log X)³`. -/
noncomputable def logCube (X : ℝ) : ℝ := (Real.log X) ^ 3

/-- The reference shape `(log X)²`. -/
noncomputable def logSq (X : ℝ) : ℝ := (Real.log X) ^ 2

/-- The reference shape `(log X)² · log z` of the small-prime certificate average
`Σ_b` (`lem:small-certificate-average`).  Here `z = zScale X`. -/
noncomputable def sigmaShape (X : ℝ) : ℝ := (Real.log X) ^ 2 * Real.log (zScale X)

/-- The reference shape `(log X)/(log z)` of the rough `d₊`-reciprocal factor
(`eq:rough-recip-uniform`).  Here `z = zScale X`. -/
noncomputable def roughShape (X : ℝ) : ℝ := Real.log X / Real.log (zScale X)

/-! ## The key cancellation: `sigmaShape · roughShape = (log X)³`.

This is the algebraic heart of `prop:mu`:
`((log X)² · log z) · ((log X)/(log z)) = (log X)³`, where the `log z` cancels.
It holds whenever `log z ≠ 0` (i.e. `z = (log X)⁴ ≠ 1`, true for large `X`). -/

/-- `sigmaShape X · roughShape X = (log X)³` whenever
`log (zScale X) ≠ 0`; the `log z` factors cancel. -/
theorem sigmaShape_mul_roughShape (X : ℝ) (hz : Real.log (zScale X) ≠ 0) :
    sigmaShape X * roughShape X = logCube X := by
  unfold sigmaShape roughShape logCube
  field_simp
  ring

/-! ## `prop:mu`: the event-mass law `μ_b ≍ (log X)³`

From the two constituent factor-asymptotics
`Σ_b ≍ (log X)² log z` (`lem:small-certificate-average`) and
`d₊-factor ≍ (log X)/(log z)` (`eq:rough-recip-uniform`), the product
`μ_b = Σ_b · (d₊-factor) ≍ (log X)³` by the cancellation above. -/

/-- **Certificate cubic event mass** (`prop:mu`).

Given:
* the small-prime certificate average `Σ_b = sigmaSmall ≍ (log X)² log z`
  (`lem:small-certificate-average`), and
* the rough `d₊`-reciprocal factor `roughFactor ≍ (log X)/(log z)`
  (the inner `d₊`-sum of `eq:certificate-mass-main`, asymptotically evaluated via
  `lem:rough-initial`/`eq:rough-recip-uniform`),

the certificate mass `μ_b = Σ_b · roughFactor` satisfies `μ_b ≍ (log X)³`:
there are `c₁, c₂ > 0` and a threshold `X₀` with
`c₁ (log X)³ ≤ μ_b ≤ c₂ (log X)³` for all `X ≥ X₀`.

The two-sided constants are explicit products of the constituent constants, and
the `log z` cancels in the proof — exactly the manuscript's
`μ_b ≍ (log X / log z)(log X)² log z ≍ (log X)³`. -/
theorem muB_lower_from_factor_bounds
    (P : Params) (b : ℕ) (sigmaSmall roughFactor : ℝ → ℝ)
    (hSig : FactorAsymp sigmaSmall sigmaShape)
    (hR : FactorAsymp roughFactor roughShape) :
    ∀ X : ℝ, max hSig.X₀ (max hR.X₀ (Real.exp 2)) ≤ X →
      (hSig.c * hR.c) * logCube X ≤ muB P b sigmaSmall roughFactor X := by
  intro X hX
  have hXSig : hSig.X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXR : hR.X₀ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXexp : Real.exp 2 ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 2) hXexp
  have hlogX2 : (2 : ℝ) ≤ Real.log X :=
    (Real.le_log_iff_exp_le hXpos).mpr hXexp
  have hlogX1 : 1 < Real.log X := lt_of_lt_of_le one_lt_two hlogX2
  have hz_pos : 0 < Real.log (zScale X) := by
    unfold zScale
    rw [Real.log_pow]
    have : 0 < Real.log (Real.log X) := Real.log_pos hlogX1
    positivity
  have hz_ne : Real.log (zScale X) ≠ 0 := ne_of_gt hz_pos
  have hrshape_nonneg : 0 ≤ roughShape X := by
    unfold roughShape
    exact div_nonneg (lt_trans one_pos hlogX1).le hz_pos.le
  obtain ⟨hσlo, _hσhi⟩ := hSig.sandwich X hXSig
  obtain ⟨hrlo, _hrhi⟩ := hR.sandwich X hXR
  have hσnonneg : 0 ≤ sigmaSmall X := hSig.f_nonneg X hXSig
  have hcancel : sigmaShape X * roughShape X = logCube X :=
    sigmaShape_mul_roughShape X hz_ne
  calc
    (hSig.c * hR.c) * logCube X
        = (hSig.c * sigmaShape X) * (hR.c * roughShape X) := by
          rw [← hcancel]
          ring
    _ ≤ sigmaSmall X * roughFactor X := by
          apply mul_le_mul hσlo hrlo
          · exact mul_nonneg hR.c_pos.le hrshape_nonneg
          · exact hσnonneg
    _ = muB P b sigmaSmall roughFactor X := rfl

/-- One-sided upper half of `mass_law`, with the same explicit constants and
threshold. -/
theorem muB_upper_from_factor_bounds
    (P : Params) (b : ℕ) (sigmaSmall roughFactor : ℝ → ℝ)
    (hSig : FactorAsymp sigmaSmall sigmaShape)
    (hR : FactorAsymp roughFactor roughShape) :
    ∀ X : ℝ, max hSig.X₀ (max hR.X₀ (Real.exp 2)) ≤ X →
      muB P b sigmaSmall roughFactor X ≤ (hSig.C * hR.C) * logCube X := by
  intro X hX
  have hXSig : hSig.X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXR : hR.X₀ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXexp : Real.exp 2 ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 2) hXexp
  have hlogX2 : (2 : ℝ) ≤ Real.log X :=
    (Real.le_log_iff_exp_le hXpos).mpr hXexp
  have hlogX1 : 1 < Real.log X := lt_of_lt_of_le one_lt_two hlogX2
  have hlogX0 : 0 < Real.log X := lt_trans one_pos hlogX1
  have hz_pos : 0 < Real.log (zScale X) := by
    unfold zScale
    rw [Real.log_pow]
    have : 0 < Real.log (Real.log X) := Real.log_pos hlogX1
    positivity
  have hz_ne : Real.log (zScale X) ≠ 0 := ne_of_gt hz_pos
  have hσshape_nonneg : 0 ≤ sigmaShape X := by
    unfold sigmaShape
    positivity
  obtain ⟨_hσlo, hσhi⟩ := hSig.sandwich X hXSig
  obtain ⟨_hrlo, hrhi⟩ := hR.sandwich X hXR
  have hrnonneg : 0 ≤ roughFactor X := hR.f_nonneg X hXR
  have hcancel : sigmaShape X * roughShape X = logCube X :=
    sigmaShape_mul_roughShape X hz_ne
  calc
    muB P b sigmaSmall roughFactor X
        = sigmaSmall X * roughFactor X := rfl
    _ ≤ (hSig.C * sigmaShape X) * (hR.C * roughShape X) := by
          apply mul_le_mul hσhi hrhi hrnonneg
          exact mul_nonneg hSig.C_pos.le hσshape_nonneg
    _ = (hSig.C * hR.C) * logCube X := by
          rw [← hcancel]
          ring

/-- Two-sided certificate mass law, assembled from the one-sided factor bounds. -/
theorem mass_law (P : Params) (b : ℕ) (sigmaSmall roughFactor : ℝ → ℝ)
    (hSig : FactorAsymp sigmaSmall sigmaShape)
    (hR : FactorAsymp roughFactor roughShape) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      c₁ * logCube X ≤ muB P b sigmaSmall roughFactor X
        ∧ muB P b sigmaSmall roughFactor X ≤ c₂ * logCube X := by
  refine ⟨hSig.c * hR.c, mul_pos hSig.c_pos hR.c_pos,
          hSig.C * hR.C, mul_pos hSig.C_pos hR.C_pos,
          max hSig.X₀ (max hR.X₀ (Real.exp 2)), fun X hX => ?_⟩
  exact ⟨muB_lower_from_factor_bounds P b sigmaSmall roughFactor hSig hR X hX,
    muB_upper_from_factor_bounds P b sigmaSmall roughFactor hSig hR X hX⟩

/-- Fixed finite modifications of both constituent factors preserve the
certificate cubic mass law.

This is the mass-law form of the fixed-`m` finite-Euler-factor deletion
argument in `prop:fixed-m-transfer`: once the modified small-side carrier and
modified rough-side carrier are each eventually comparable to the original
carrier by fixed positive constants, the resulting fixed-`m` mass still satisfies
`μ_{m,b} ≍ (log X)^3`, with constants allowed to depend on `m`. -/
theorem mass_law_of_factor_comparable
    (P : Params) (b : ℕ)
    (sigmaSmall roughFactor sigmaSmall' roughFactor' : ℝ → ℝ)
    (hSig : FactorAsymp sigmaSmall sigmaShape)
    (hR : FactorAsymp roughFactor roughShape)
    (Xsig Xrough aSig ASig aR AR : ℝ)
    (haSig : 0 < aSig) (hASig : 0 < ASig)
    (haR : 0 < aR) (hAR : 0 < AR)
    (hSigCmp : ∀ X : ℝ, Xsig ≤ X →
      aSig * sigmaSmall X ≤ sigmaSmall' X ∧ sigmaSmall' X ≤ ASig * sigmaSmall X)
    (hRoughCmp : ∀ X : ℝ, Xrough ≤ X →
      aR * roughFactor X ≤ roughFactor' X ∧ roughFactor' X ≤ AR * roughFactor X) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      c₁ * logCube X ≤ muB P b sigmaSmall' roughFactor' X
        ∧ muB P b sigmaSmall' roughFactor' X ≤ c₂ * logCube X := by
  exact mass_law P b sigmaSmall' roughFactor'
    (FactorAsymp.of_eventual_const_comparable hSig Xsig aSig ASig haSig hASig hSigCmp)
    (FactorAsymp.of_eventual_const_comparable hR Xrough aR AR haR hAR hRoughCmp)

/-! ## Provenance of the two constituent factors from the cited inputs.

The two `FactorAsymp` data fed to `mass_law` are exactly the manuscript's two
quoted asymptotics.  We record their *standard* shapes (matching `Σ_b` and the
rough `d₊`-factor) and tie them, where the abstract interface allows, to the
`EscAnalytic.Inputs` finite carriers.  The constituent asymptotics remain
explicit inputs; the algebraic combination is proved by `mass_law` above. -/

/-- Transfer a no-auxiliary-modulus rough factor asymptotic to any fixed
auxiliary modulus.

For fixed `M`, the rough modulus `P((log X)^4)` eventually contains every prime
factor of `M`; after that threshold the `(n,M)=1` condition is redundant once
`(n,P((log X)^4))=1` is imposed.  Thus a theorem for the `M=1` rough carrier
automatically gives the fixed-`M` rough factor used by the mass law. -/
noncomputable def roughFactor_asymp_of_modulus_one_absorption
    (M : ℕ) (a b : ℝ)
    (hR1 : FactorAsymp (fun X => Inputs.roughRecip X 1 a b) roughShape) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  FactorAsymp.of_eventually_eq hR1
    (Real.exp ((Inputs.auxiliaryModulus M : ℕ) : ℝ))
    (fun X hX =>
      Inputs.roughRecip_eq_modulus_one_of_exp_auxiliary_le X M a b hX)

/-- Package a reciprocal estimate for one fixed rough carrier as the rough
factor asymptotic used by `mass_law`.

This avoids the older uniform-in-auxiliary-modulus interface when a proof only
supplies the fixed carrier actually consumed downstream. -/
noncomputable def roughFactor_asymp_of_fixed_bound
    (M : ℕ) (a b : ℝ)
    (c C Xbase : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hrough :
      ∀ X : ℝ, Xbase ≤ X →
        c * (Real.log X / Real.log (zScale X)) ≤ Inputs.roughRecip X M a b
          ∧ Inputs.roughRecip X M a b
              ≤ C * (Real.log X / Real.log (zScale X))) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  { c := c
    C := C
    X₀ := max Xbase (Real.exp 2)
    c_pos := hc
    C_pos := hC
    f_nonneg := fun X _ => Inputs.roughRecip_nonneg X M a b
    sandwich := fun X hX => by
      have hXbase : Xbase ≤ X := le_trans (le_max_left _ _) hX
      simpa [roughShape] using hrough X hXbase }

/-- Existential version of `roughFactor_asymp_of_fixed_bound`.  Since
`FactorAsymp` carries constants as data, a propositionally-packaged estimate
can only construct a propositionally-packaged witness. -/
theorem roughFactor_asymp_nonempty_of_fixed_bound
    (M : ℕ) (a b : ℝ)
    (hrough :
      ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        c * (Real.log X / Real.log (zScale X)) ≤ Inputs.roughRecip X M a b
          ∧ Inputs.roughRecip X M a b
              ≤ C * (Real.log X / Real.log (zScale X))) :
    Nonempty (FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape) := by
  rcases hrough with ⟨c, C, Xbase, hc, hC, hbound⟩
  exact ⟨roughFactor_asymp_of_fixed_bound M a b c C Xbase hc hC hbound⟩

/-- A fixed `M=1` reciprocal estimate transfers to the fixed auxiliary modulus
`M` rough factor after the rough modulus absorbs `M`. -/
noncomputable def roughFactor_asymp_of_modulus_one_fixed_bound
    (M : ℕ) (a b : ℝ)
    (c C Xbase : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hrough :
      ∀ X : ℝ, Xbase ≤ X →
        c * (Real.log X / Real.log (zScale X)) ≤ Inputs.roughRecip X 1 a b
          ∧ Inputs.roughRecip X 1 a b
              ≤ C * (Real.log X / Real.log (zScale X))) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  roughFactor_asymp_of_modulus_one_absorption M a b
    (roughFactor_asymp_of_fixed_bound 1 a b c C Xbase hc hC hrough)

/-- Existential version of
`roughFactor_asymp_of_modulus_one_fixed_bound`. -/
theorem roughFactor_asymp_nonempty_of_modulus_one_fixed_bound
    (M : ℕ) (a b : ℝ)
    (hrough :
      ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        c * (Real.log X / Real.log (zScale X)) ≤ Inputs.roughRecip X 1 a b
          ∧ Inputs.roughRecip X 1 a b
              ≤ C * (Real.log X / Real.log (zScale X))) :
    Nonempty (FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape) := by
  rcases hrough with ⟨c, C, Xbase, hc, hC, hbound⟩
  exact ⟨roughFactor_asymp_of_modulus_one_fixed_bound M a b c C Xbase hc hC hbound⟩

/-- The rough `d₊`-reciprocal factor's asymptotic is the manuscript-shaped
theorem `eq:rough-recip-uniform` (`EscAnalytic.Inputs.rough_sqf_recip`), now derived from the named standard rough-sieve input: the inner `d₊`-sum
is `≍ (log X)/(log z) = roughShape`. Passing to the checked carrier-bound form
of `rough_sqf_recip` as a `FactorAsymp` on the slot `roughRecip X 1 a b`
for a fixed admissible window `[a,b]` below `σ`.

We expose this as a constructor: given the manuscript window
`X^{σ/2} < d₊ ≤ X^σ/(log X)⁸`, `rough_sqf_recip` produces the
`FactorAsymp roughFactor roughShape` consumed by `mass_law`.  Because the result
carries the chosen constants as *data*, it is a `noncomputable def` extracting
them from the cited input via `Classical.choose`. -/
noncomputable def roughFactor_asymp (P : Params) (a₀ b₀ c₁ C₀ : ℝ)
    (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁ : 0 < c₁)
    (M : ℕ) (a b : ℝ)
    (ha : a₀ ≤ a) (haltb : a < b) (hb : b ≤ b₀) (hgap : c₁ ≤ b - a)
    (hM : ∀ X : ℝ, (M : ℝ) ≤ X ^ C₀) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  { c := (Inputs.rough_sqf_recip_with_carrier_bounds P a₀ b₀ c₁ C₀ ha₀ hab hc₁).choose
    C := (Inputs.rough_sqf_recip_with_carrier_bounds P a₀ b₀ c₁ C₀ ha₀ hab hc₁).choose_spec.choose
    X₀ :=
      (Inputs.rough_sqf_recip_with_carrier_bounds P a₀ b₀ c₁ C₀ ha₀ hab hc₁).choose_spec.choose_spec.choose
    c_pos :=
      (Inputs.rough_sqf_recip_with_carrier_bounds P a₀ b₀ c₁ C₀ ha₀ hab hc₁).choose_spec.choose_spec.choose_spec.1
    C_pos :=
      (Inputs.rough_sqf_recip_with_carrier_bounds P a₀ b₀ c₁ C₀ ha₀ hab hc₁).choose_spec.choose_spec.choose_spec.2.1
    f_nonneg := fun X _ => Inputs.roughRecip_nonneg X M a b
    sandwich := fun X hX => by
      -- `roughShape X = log X / log z`, identical to the Inputs bound's shape.
      have h :=
        (Inputs.rough_sqf_recip_with_carrier_bounds P a₀ b₀ c₁ C₀ ha₀ hab hc₁).choose_spec.choose_spec.choose_spec.2.2
          X hX M (hM X) a b ha haltb hb hgap
      rcases h with ⟨_hlogX, _hlogZ, _hshape, _hcarrier, hlower, hupper, _habsolute⟩
      exact ⟨hlower, hupper⟩ }

/-- Eventual-size version of `roughFactor_asymp`.

The cited rough reciprocal estimate only needs the auxiliary modulus bound on
the eventual range where the asymptotic is applied.  This removes the stronger
global hypothesis `∀ X, M ≤ X^C₀` from downstream mass-law routes. -/
noncomputable def roughFactor_asymp_eventual_modulus
    (P : Params) (a₀ b₀ c₁ C₀ : ℝ)
    (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁ : 0 < c₁)
    (M : ℕ) (a b : ℝ)
    (ha : a₀ ≤ a) (haltb : a < b) (hb : b ≤ b₀) (hgap : c₁ ≤ b - a)
    (XM : ℝ) (hM : ∀ X : ℝ, XM ≤ X → (M : ℝ) ≤ X ^ C₀) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  { c := (Inputs.rough_sqf_recip_with_carrier_bounds P a₀ b₀ c₁ C₀ ha₀ hab hc₁).choose
    C := (Inputs.rough_sqf_recip_with_carrier_bounds P a₀ b₀ c₁ C₀ ha₀ hab hc₁).choose_spec.choose
    X₀ :=
      max
        (Inputs.rough_sqf_recip_with_carrier_bounds P a₀ b₀ c₁ C₀ ha₀ hab hc₁).choose_spec.choose_spec.choose
        XM
    c_pos :=
      (Inputs.rough_sqf_recip_with_carrier_bounds P a₀ b₀ c₁ C₀ ha₀ hab hc₁).choose_spec.choose_spec.choose_spec.1
    C_pos :=
      (Inputs.rough_sqf_recip_with_carrier_bounds P a₀ b₀ c₁ C₀ ha₀ hab hc₁).choose_spec.choose_spec.choose_spec.2.1
    f_nonneg := fun X _ => Inputs.roughRecip_nonneg X M a b
    sandwich := fun X hX => by
      have hXbase :
          (Inputs.rough_sqf_recip_with_carrier_bounds P a₀ b₀ c₁ C₀ ha₀ hab hc₁).choose_spec.choose_spec.choose
            ≤ X :=
        le_trans (le_max_left _ _) hX
      have hXM : XM ≤ X := le_trans (le_max_right _ _) hX
      have h :=
        (Inputs.rough_sqf_recip_with_carrier_bounds P a₀ b₀ c₁ C₀ ha₀ hab hc₁).choose_spec.choose_spec.choose_spec.2.2
          X hXbase M (hM X hXM) a b ha haltb hb hgap
      rcases h with ⟨_hlogX, _hlogZ, _hshape, _hcarrier, hlower, hupper, _habsolute⟩
      exact ⟨hlower, hupper⟩ }

/-- Any fixed natural auxiliary modulus is eventually below every positive power
`X^C`. -/
theorem fixedNat_le_rpow_eventually_threshold
    (M : ℕ) {C : ℝ} (hC : 0 < C) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → (M : ℝ) ≤ X ^ C := by
  exact Filter.eventually_atTop.mp
    ((_root_.tendsto_rpow_atTop hC).eventually
      (Filter.eventually_ge_atTop (M : ℝ)))

/-- Package a caller-supplied rough reciprocal estimate as the `roughShape`
`FactorAsymp` used by `mass_law`.

This is the theorem-level version of `roughFactor_asymp`: all carrier
nonnegativity and logarithm side conditions are checked here, while the actual
linear-sieve estimate is supplied explicitly as `hrough`. -/
noncomputable def roughFactor_asymp_of_bound
    (a₀ b₀ c₁ C₀ : ℝ)
    (M : ℕ) (a b : ℝ)
    (ha : a₀ ≤ a) (haltb : a < b) (hb : b ≤ b₀) (hgap : c₁ ≤ b - a)
    (hM : ∀ X : ℝ, (M : ℝ) ≤ X ^ C₀)
    (hrough :
      ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        ∀ (M : ℕ), (M : ℝ) ≤ X ^ C₀ →
        ∀ a b : ℝ, a₀ ≤ a → a < b → b ≤ b₀ → c₁ ≤ b - a →
          c * (Real.log X / Real.log (EscAnalytic.zScale X)) ≤ Inputs.roughRecip X M a b
            ∧ Inputs.roughRecip X M a b
                ≤ C * (Real.log X / Real.log (EscAnalytic.zScale X))) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  let hcarrier := Inputs.rough_sqf_recip_with_carrier_bounds_of_bound
    (a₀ := a₀) (b₀ := b₀) (c₁ := c₁) (C₀ := C₀) hrough
  { c := hcarrier.choose
    C := hcarrier.choose_spec.choose
    X₀ := hcarrier.choose_spec.choose_spec.choose
    c_pos := hcarrier.choose_spec.choose_spec.choose_spec.1
    C_pos := hcarrier.choose_spec.choose_spec.choose_spec.2.1
    f_nonneg := fun X _ => Inputs.roughRecip_nonneg X M a b
    sandwich := fun X hX => by
      have h :=
        hcarrier.choose_spec.choose_spec.choose_spec.2.2
          X hX M (hM X) a b ha haltb hb hgap
      rcases h with ⟨_hlogX, _hlogZ, _hshape, _hcarrier, hlower, hupper, _habsolute⟩
      exact ⟨hlower, hupper⟩ }

/-- Eventual-modulus version of `roughFactor_asymp_of_bound`.

The rough reciprocal estimate is asymptotic in `X`, so a fixed auxiliary modulus
only needs to satisfy `M ≤ X^C₀` after a threshold.  This version folds that
threshold into the resulting `FactorAsymp` datum. -/
noncomputable def roughFactor_asymp_of_bound_eventual_modulus
    (a₀ b₀ c₁ C₀ : ℝ)
    (M : ℕ) (a b : ℝ)
    (ha : a₀ ≤ a) (haltb : a < b) (hb : b ≤ b₀) (hgap : c₁ ≤ b - a)
    (XM : ℝ) (hM : ∀ X : ℝ, XM ≤ X → (M : ℝ) ≤ X ^ C₀)
    (hrough :
      ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        ∀ (M : ℕ), (M : ℝ) ≤ X ^ C₀ →
        ∀ a b : ℝ, a₀ ≤ a → a < b → b ≤ b₀ → c₁ ≤ b - a →
          c * (Real.log X / Real.log (EscAnalytic.zScale X)) ≤ Inputs.roughRecip X M a b
            ∧ Inputs.roughRecip X M a b
                ≤ C * (Real.log X / Real.log (EscAnalytic.zScale X))) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  let hcarrier := Inputs.rough_sqf_recip_with_carrier_bounds_of_bound
    (a₀ := a₀) (b₀ := b₀) (c₁ := c₁) (C₀ := C₀) hrough
  { c := hcarrier.choose
    C := hcarrier.choose_spec.choose
    X₀ := max hcarrier.choose_spec.choose_spec.choose XM
    c_pos := hcarrier.choose_spec.choose_spec.choose_spec.1
    C_pos := hcarrier.choose_spec.choose_spec.choose_spec.2.1
    f_nonneg := fun X _ => Inputs.roughRecip_nonneg X M a b
    sandwich := fun X hX => by
      have hXbase : hcarrier.choose_spec.choose_spec.choose ≤ X :=
        le_trans (le_max_left _ _) hX
      have hXM : XM ≤ X := le_trans (le_max_right _ _) hX
      have h :=
        hcarrier.choose_spec.choose_spec.choose_spec.2.2
          X hXbase M (hM X hXM) a b ha haltb hb hgap
      rcases h with ⟨_hlogX, _hlogZ, _hshape, _hcarrier, hlower, hupper, _habsolute⟩
      exact ⟨hlower, hupper⟩ }

/-- Rough-factor constructor from bounded Mertens defect and normalized
rough-count discrepancy.

This is the mass-tensor wrapper around the conventional-input bridge proved in
`Inputs`; it packages the rough reciprocal estimate into the `FactorAsymp` datum
consumed by `mass_law`. -/
noncomputable def roughFactor_asymp_of_defectIsBigOOne_and_normalized
    (P : Params) (a₀ b₀ c₁ C₀ : ℝ)
    (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁ : 0 < c₁)
    (M : ℕ) (a b : ℝ)
    (ha : a₀ ≤ a) (haltb : a < b) (hb : b ≤ b₀) (hgap : c₁ ≤ b - a)
    (hM : ∀ X : ℝ, (M : ℝ) ≤ X ^ C₀)
    (hmertens : Inputs.PrimeRecipSharpMertensNatDefectIsBigOOne)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  roughFactor_asymp_of_bound a₀ b₀ c₁ C₀ M a b ha haltb hb hgap hM
    (Inputs.rough_sqf_recip_of_defectIsBigOOne_and_normalized
      P a₀ b₀ c₁ C₀ ha₀ hab hc₁ hmertens hdisc)

/-- Eventual-modulus version of
`roughFactor_asymp_of_defectIsBigOOne_and_normalized`. -/
noncomputable def roughFactor_asymp_of_defectIsBigOOne_and_normalized_eventual_modulus
    (P : Params) (a₀ b₀ c₁ C₀ : ℝ)
    (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁ : 0 < c₁)
    (M : ℕ) (a b : ℝ)
    (ha : a₀ ≤ a) (haltb : a < b) (hb : b ≤ b₀) (hgap : c₁ ≤ b - a)
    (XM : ℝ) (hM : ∀ X : ℝ, XM ≤ X → (M : ℝ) ≤ X ^ C₀)
    (hmertens : Inputs.PrimeRecipSharpMertensNatDefectIsBigOOne)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  roughFactor_asymp_of_bound_eventual_modulus a₀ b₀ c₁ C₀ M a b ha haltb hb
    hgap XM hM
    (Inputs.rough_sqf_recip_of_defectIsBigOOne_and_normalized
      P a₀ b₀ c₁ C₀ ha₀ hab hc₁ hmertens hdisc)

/-- Rough-factor constructor from the one-sided Mertens upper bound actually
needed for the finite rough Euler-product lower bound, together with normalized
rough-count discrepancy. -/
noncomputable def roughFactor_asymp_of_defectEventuallyUpperBound_and_normalized
    (P : Params) (a₀ b₀ c₁ C₀ : ℝ)
    (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁ : 0 < c₁)
    (M : ℕ) (a b : ℝ)
    (ha : a₀ ≤ a) (haltb : a < b) (hb : b ≤ b₀) (hgap : c₁ ≤ b - a)
    (hM : ∀ X : ℝ, (M : ℝ) ≤ X ^ C₀)
    (hmertens : Inputs.PrimeRecipSharpMertensNatDefectEventuallyUpperBound)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  roughFactor_asymp_of_bound a₀ b₀ c₁ C₀ M a b ha haltb hb hgap hM
    (Inputs.rough_sqf_recip_of_defectEventuallyUpperBound_and_normalized
      P a₀ b₀ c₁ C₀ ha₀ hab hc₁ hmertens hdisc)

/-- Eventual-modulus version of
`roughFactor_asymp_of_defectEventuallyUpperBound_and_normalized`. -/
noncomputable def roughFactor_asymp_of_defectEventuallyUpperBound_and_normalized_eventual_modulus
    (P : Params) (a₀ b₀ c₁ C₀ : ℝ)
    (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁ : 0 < c₁)
    (M : ℕ) (a b : ℝ)
    (ha : a₀ ≤ a) (haltb : a < b) (hb : b ≤ b₀) (hgap : c₁ ≤ b - a)
    (XM : ℝ) (hM : ∀ X : ℝ, XM ≤ X → (M : ℝ) ≤ X ^ C₀)
    (hmertens : Inputs.PrimeRecipSharpMertensNatDefectEventuallyUpperBound)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  roughFactor_asymp_of_bound_eventual_modulus a₀ b₀ c₁ C₀ M a b ha haltb hb
    hgap XM hM
    (Inputs.rough_sqf_recip_of_defectEventuallyUpperBound_and_normalized
      P a₀ b₀ c₁ C₀ ha₀ hab hc₁ hmertens hdisc)

/-- Rough-factor constructor from the coefficient-one dyadic prime-reciprocal
block formulation of Mertens, together with normalized rough-count
discrepancy. -/
noncomputable def roughFactor_asymp_of_dyadicBlocksSharpUpperBound_and_normalized
    (P : Params) (a₀ b₀ c₁ C₀ : ℝ)
    (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁ : 0 < c₁)
    (M : ℕ) (a b : ℝ)
    (ha : a₀ ≤ a) (haltb : a < b) (hb : b ≤ b₀) (hgap : c₁ ≤ b - a)
    (hM : ∀ X : ℝ, (M : ℝ) ≤ X ^ C₀)
    (hmertens : Inputs.PrimeRecipDyadicBlocksSharpUpperBound)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  roughFactor_asymp_of_bound a₀ b₀ c₁ C₀ M a b ha haltb hb hgap hM
    (Inputs.rough_sqf_recip_of_dyadicBlocksSharpUpperBound_and_normalized
      P a₀ b₀ c₁ C₀ ha₀ hab hc₁ hmertens hdisc)

/-- Eventual-modulus version of
`roughFactor_asymp_of_dyadicBlocksSharpUpperBound_and_normalized`. -/
noncomputable def roughFactor_asymp_of_dyadicBlocksSharpUpperBound_and_normalized_eventual_modulus
    (P : Params) (a₀ b₀ c₁ C₀ : ℝ)
    (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁ : 0 < c₁)
    (M : ℕ) (a b : ℝ)
    (ha : a₀ ≤ a) (haltb : a < b) (hb : b ≤ b₀) (hgap : c₁ ≤ b - a)
    (XM : ℝ) (hM : ∀ X : ℝ, XM ≤ X → (M : ℝ) ≤ X ^ C₀)
    (hmertens : Inputs.PrimeRecipDyadicBlocksSharpUpperBound)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  roughFactor_asymp_of_bound_eventual_modulus a₀ b₀ c₁ C₀ M a b ha haltb hb
    hgap XM hM
    (Inputs.rough_sqf_recip_of_dyadicBlocksSharpUpperBound_and_normalized
      P a₀ b₀ c₁ C₀ ha₀ hab hc₁ hmertens hdisc)

/-- Rough-factor constructor from eventual absolute Mertens control and
normalized rough-count discrepancy. -/
noncomputable def roughFactor_asymp_of_eventuallyAbsBound_and_normalized
    (P : Params) (a₀ b₀ c₁ C₀ : ℝ)
    (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁ : 0 < c₁)
    (M : ℕ) (a b : ℝ)
    (ha : a₀ ≤ a) (haltb : a < b) (hb : b ≤ b₀) (hgap : c₁ ≤ b - a)
    (hM : ∀ X : ℝ, (M : ℝ) ≤ X ^ C₀)
    (hmertens : Inputs.PrimeRecipSharpMertensNatDefectEventuallyAbsBound)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  roughFactor_asymp_of_bound a₀ b₀ c₁ C₀ M a b ha haltb hb hgap hM
    (Inputs.rough_sqf_recip_of_eventuallyAbsBound_and_normalized
      P a₀ b₀ c₁ C₀ ha₀ hab hc₁ hmertens hdisc)

/-- Eventual-modulus version of
`roughFactor_asymp_of_eventuallyAbsBound_and_normalized`. -/
noncomputable def roughFactor_asymp_of_eventuallyAbsBound_and_normalized_eventual_modulus
    (P : Params) (a₀ b₀ c₁ C₀ : ℝ)
    (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁ : 0 < c₁)
    (M : ℕ) (a b : ℝ)
    (ha : a₀ ≤ a) (haltb : a < b) (hb : b ≤ b₀) (hgap : c₁ ≤ b - a)
    (XM : ℝ) (hM : ∀ X : ℝ, XM ≤ X → (M : ℝ) ≤ X ^ C₀)
    (hmertens : Inputs.PrimeRecipSharpMertensNatDefectEventuallyAbsBound)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  roughFactor_asymp_of_bound_eventual_modulus a₀ b₀ c₁ C₀ M a b ha haltb hb
    hgap XM hM
    (Inputs.rough_sqf_recip_of_eventuallyAbsBound_and_normalized
      P a₀ b₀ c₁ C₀ ha₀ hab hc₁ hmertens hdisc)

/-- Rough-factor constructor from two-sided Mertens control and normalized
rough-count discrepancy. -/
noncomputable def roughFactor_asymp_of_twoSided_and_normalized
    (P : Params) (a₀ b₀ c₁ C₀ : ℝ)
    (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁ : 0 < c₁)
    (M : ℕ) (a b : ℝ)
    (ha : a₀ ≤ a) (haltb : a < b) (hb : b ≤ b₀) (hgap : c₁ ≤ b - a)
    (hM : ∀ X : ℝ, (M : ℝ) ≤ X ^ C₀)
    (hmertens : Inputs.PrimeRecipSharpMertensNatDefectEventuallyTwoSidedBound)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  roughFactor_asymp_of_bound a₀ b₀ c₁ C₀ M a b ha haltb hb hgap hM
    (Inputs.rough_sqf_recip_of_twoSided_and_normalized
      P a₀ b₀ c₁ C₀ ha₀ hab hc₁ hmertens hdisc)

/-- Eventual-modulus version of
`roughFactor_asymp_of_twoSided_and_normalized`. -/
noncomputable def roughFactor_asymp_of_twoSided_and_normalized_eventual_modulus
    (P : Params) (a₀ b₀ c₁ C₀ : ℝ)
    (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁ : 0 < c₁)
    (M : ℕ) (a b : ℝ)
    (ha : a₀ ≤ a) (haltb : a < b) (hb : b ≤ b₀) (hgap : c₁ ≤ b - a)
    (XM : ℝ) (hM : ∀ X : ℝ, XM ≤ X → (M : ℝ) ≤ X ^ C₀)
    (hmertens : Inputs.PrimeRecipSharpMertensNatDefectEventuallyTwoSidedBound)
    (hdisc : Inputs.RoughDyadicCountDiscrepancyUniformNormalizedSmallBound) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  roughFactor_asymp_of_bound_eventual_modulus a₀ b₀ c₁ C₀ M a b ha haltb hb
    hgap XM hM
    (Inputs.rough_sqf_recip_of_twoSided_and_normalized
      P a₀ b₀ c₁ C₀ ha₀ hab hc₁ hmertens hdisc)

/-- Rough-factor constructor from a normalized dyadic-density hypothesis.

The density/count conversion and dyadic partial summation are proved in
`Inputs`; this wrapper only packages the resulting reciprocal estimate in the
shape required by `mass_law`. -/
noncomputable def roughFactor_asymp_of_roughDyadicDensity_bound
    (P : Params) (a₀ b₀ c₁ C₀ : ℝ)
    (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁ : 0 < c₁)
    (M : ℕ) (a b : ℝ)
    (ha : a₀ ≤ a) (haltb : a < b) (hb : b ≤ b₀) (hgap : c₁ ≤ b - a)
    (hM : ∀ X : ℝ, (M : ℝ) ≤ X ^ C₀)
    (hdensity :
      ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        ∀ (M : ℕ), (M : ℝ) ≤ X ^ C₀ →
        ∀ t : ℝ, X ^ a₀ ≤ t → t ≤ 2 * X ^ b₀ → 0 < t →
          0 < Real.log (EscAnalytic.zScale X) ∧
            c / Real.log (EscAnalytic.zScale X) ≤ Inputs.roughDyadicDensity X M t ∧
            Inputs.roughDyadicDensity X M t ≤ C / Real.log (EscAnalytic.zScale X)) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  roughFactor_asymp_of_bound a₀ b₀ c₁ C₀ M a b ha haltb hb hgap hM
    (Inputs.rough_sqf_recip_of_roughDyadicDensity_bound P a₀ b₀ c₁ C₀
      ha₀ hab hc₁ hdensity)

/-- Rough-factor constructor from finite bad-prime main-term dominance.

This bypasses the named rough-sieve primitive: the finite-product/count
reduction is proved in `Inputs`, and this wrapper only packages it as the
`FactorAsymp` object consumed by the tensor mass law. -/
noncomputable def roughFactor_asymp_of_badPrimeProductMainTermDominatesError
    (P : Params) (a₀ b₀ c₁ C₀ : ℝ)
    (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁ : 0 < c₁)
    (M : ℕ) (a b : ℝ)
    (ha : a₀ ≤ a) (haltb : a < b) (hb : b ≤ b₀) (hgap : c₁ ≤ b - a)
    (hM : ∀ X : ℝ, (M : ℝ) ≤ X ^ C₀)
    (h : Inputs.roughDyadicBadPrimeProductMainTermDominatesErrorBound a₀ b₀ C₀) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  roughFactor_asymp_of_bound a₀ b₀ c₁ C₀ M a b ha haltb hb hgap hM
    (Inputs.rough_sqf_recip_of_badPrimeProductMainTermDominatesError P a₀ b₀ c₁ C₀
      ha₀ hab hc₁ h)

/-- Rough-factor constructor from finite Euler-product/error control. -/
noncomputable def roughFactor_asymp_of_badPrimeEulerProductError
    (P : Params) (a₀ b₀ c₁ C₀ : ℝ)
    (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁ : 0 < c₁)
    (M : ℕ) (a b : ℝ)
    (ha : a₀ ≤ a) (haltb : a < b) (hb : b ≤ b₀) (hgap : c₁ ≤ b - a)
    (hM : ∀ X : ℝ, (M : ℝ) ≤ X ^ C₀)
    (h : Inputs.roughDyadicBadPrimeEulerProductErrorBound a₀ b₀ C₀) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  roughFactor_asymp_of_bound a₀ b₀ c₁ C₀ M a b ha haltb hb hgap hM
    (Inputs.rough_sqf_recip_of_badPrimeEulerProductError P a₀ b₀ c₁ C₀
      ha₀ hab hc₁ h)

/-- Rough-factor constructor from split finite Euler-product/error control. -/
noncomputable def roughFactor_asymp_of_splitEulerProductError
    (P : Params) (a₀ b₀ c₁ C₀ : ℝ)
    (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁ : 0 < c₁)
    (M : ℕ) (a b : ℝ)
    (ha : a₀ ≤ a) (haltb : a < b) (hb : b ≤ b₀) (hgap : c₁ ≤ b - a)
    (hM : ∀ X : ℝ, (M : ℝ) ≤ X ^ C₀)
    (h : Inputs.roughDyadicBadPrimeSplitEulerProductErrorBound a₀ b₀ C₀) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  roughFactor_asymp_of_bound a₀ b₀ c₁ C₀ M a b ha haltb hb hgap hM
    (Inputs.rough_sqf_recip_of_splitEulerProductError P a₀ b₀ c₁ C₀
      ha₀ hab hc₁ h)

/-- Rough-factor constructor from standalone finite-product lower control and
standalone exact-error control.  The finite-product upper half is supplied
unconditionally in `Inputs`. -/
noncomputable def roughFactor_asymp_of_productLower_and_error
    (P : Params) (a₀ b₀ c₁ C₀ : ℝ)
    (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁ : 0 < c₁)
    (M : ℕ) (a b : ℝ)
    (ha : a₀ ≤ a) (haltb : a < b) (hb : b ≤ b₀) (hgap : c₁ ≤ b - a)
    (hM : ∀ X : ℝ, (M : ℝ) ≤ X ^ C₀)
    {c E Xprod Xerr : ℝ}
    (hc : 0 < c) (hE_lt : E < c)
    (hprod : ∀ X : ℝ, Xprod ≤ X →
      c / Real.log (EscAnalytic.zScale X) ≤
        Inputs.roughDyadicBadPrimeMainEulerProduct X)
    (herr : Inputs.roughDyadicBadPrimeProductErrorBound a₀ b₀ C₀ E Xerr) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  roughFactor_asymp_of_bound a₀ b₀ c₁ C₀ M a b ha haltb hb hgap hM
    (Inputs.rough_sqf_recip_of_productLower_and_error P a₀ b₀ c₁ C₀
      ha₀ hab hc₁ hc hE_lt hprod herr)

/-- Rough-factor constructor from separated finite Euler-product/error control. -/
noncomputable def roughFactor_asymp_of_separatedEulerProductError
    (P : Params) (a₀ b₀ c₁ C₀ : ℝ)
    (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁ : 0 < c₁)
    (M : ℕ) (a b : ℝ)
    (ha : a₀ ≤ a) (haltb : a < b) (hb : b ≤ b₀) (hgap : c₁ ≤ b - a)
    (hM : ∀ X : ℝ, (M : ℝ) ≤ X ^ C₀)
    (h : Inputs.roughDyadicBadPrimeSeparatedEulerProductErrorBound a₀ b₀ C₀) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  roughFactor_asymp_of_bound a₀ b₀ c₁ C₀ M a b ha haltb hb hgap hM
    (Inputs.rough_sqf_recip_of_separatedEulerProductError P a₀ b₀ c₁ C₀
      ha₀ hab hc₁ h)

/-- Diagnostic rough-factor constructor from lower finite Euler-product/error
control plus the overstrong quotient-envelope upper bound.

The envelope premise contains the empty-subset term at ambient scale, so this
constructor records a formal implication rather than a viable unconditional
route to the rough factor. -/
noncomputable def roughFactor_asymp_of_lowerEulerProductError_and_envelope
    (P : Params) (a₀ b₀ c₁ C₀ : ℝ)
    (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁ : 0 < c₁)
    (M : ℕ) (a b : ℝ)
    (ha : a₀ ≤ a) (haltb : a < b) (hb : b ≤ b₀) (hgap : c₁ ≤ b - a)
    (hM : ∀ X : ℝ, (M : ℝ) ≤ X ^ C₀)
    (hLower : Inputs.roughDyadicBadPrimeLowerEulerProductErrorBound a₀ b₀ C₀)
    (hEnv : Inputs.roughDyadicBadPrimeProductEnvelopeUpperBound a₀ b₀ C₀) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  roughFactor_asymp_of_bound a₀ b₀ c₁ C₀ M a b ha haltb hb hgap hM
    (Inputs.rough_sqf_recip_of_lowerEulerProductError_and_envelope
      P a₀ b₀ c₁ C₀ ha₀ hab hc₁ hLower hEnv)

/-- Diagnostic rough-factor constructor from split finite Euler-product/error
control plus the overstrong quotient-envelope upper bound.

The split product upper estimate is not used here; the upper half is supplied by
`hEnv`.  Because the quotient envelope itself is overlarge, this should be read
as an implication sanity check, not as a target for total formalization. -/
noncomputable def roughFactor_asymp_of_splitLowerEulerProductError_and_envelope
    (P : Params) (a₀ b₀ c₁ C₀ : ℝ)
    (ha₀ : 0 < a₀) (hab : a₀ < b₀) (hc₁ : 0 < c₁)
    (M : ℕ) (a b : ℝ)
    (ha : a₀ ≤ a) (haltb : a < b) (hb : b ≤ b₀) (hgap : c₁ ≤ b - a)
    (hM : ∀ X : ℝ, (M : ℝ) ≤ X ^ C₀)
    (hSplit : Inputs.roughDyadicBadPrimeSplitEulerProductErrorBound a₀ b₀ C₀)
    (hEnv : Inputs.roughDyadicBadPrimeProductEnvelopeUpperBound a₀ b₀ C₀) :
    FactorAsymp (fun X => Inputs.roughRecip X M a b) roughShape :=
  roughFactor_asymp_of_bound a₀ b₀ c₁ C₀ M a b ha haltb hb hgap hM
    (Inputs.rough_sqf_recip_of_splitLowerEulerProductError_and_envelope
      P a₀ b₀ c₁ C₀ ha₀ hab hc₁ hSplit hEnv)

/-! ## `prop:M` — quadratic exact-divisor mass `M₁, M_φ ≍ (log X)²`.

The exact-divisor masses `M₁ = ∑ 1/ρ(e)` and `M_φ = ∑ 1/φ(ρ(e))` are both
`≍ (log X)²`.  The manuscript proof combines the
ordinary squarefree reciprocal sum over the slanted region (`lem:ordinary-sqf`)
with the squarefree-conductor average `lem:s-average` (which gives `log S ≍ log X`,
contributing one `log X`) and the slanted-region length (the other `log X`).

We encode `M₁, M_φ` as `FactorAsymp _ logSq` and provide, as the headline of
`prop:M`, the two-sided constant sandwich packaged from those constituent inputs.
As with `mass_law`, the heavy nested-sum identity to the opaque `Inputs` sums is
threaded as a `FactorAsymp` hypothesis.  The conclusion is the
`≍ (log X)²` statement together with the `M_φ`-from-`M₁` comparison. -/

/-! `prop:M` and `thm:tensor-e` are not proved in this file.  Their current
checked concrete carriers live in `EscAnalytic.MassEstimates`: `prop:M` is
represented by the exact-divisor raw/fiber identities, mass-shape comparison
bridges, and quadratic-mass output capstones, while `thm:tensor-e` is represented
by the endpoint-safe tensor-fiber summation bounds culminating in
`exactDivisorTensorPaperOutputs`.  This file consumes those results only through
the explicit assembled log-cube bounds used by `prop:event-tensor`. -/

/-! ## `prop:event-tensor` — certificate event-level tensorisation.

For squarefree `D ≤ Y` with `(D,P(z))=1` and `(c,D)=1`,
`B^{(b)}_{D,c} ≪ μ_b/D²` and `∑_{D∣d₊} w ≪ μ_b/D`.

The manuscript proof assembles the bound from:
* `lem:BT-recip`: the inner prime sum is `≪ 1/(d₊ φ(4ρ(e)))`;
* the change of variables `d₊ = D t`, contributing one `1/D` to the rough
  reciprocal `d₊`-sum;
* `thm:tensor-e`: the combined `e`-congruence mod `D` (with the `d₋`-congruence)
  contributes `≪ M_φ/(D d₋)`;
* summing `1/d₋` over `d₋ ∣ P(z)` gives `≪ log z`;
* finally `M_φ/D · log z · (1/D)(log X/log z) ≪ (log X)³/D² ≍ μ_b/D²`.

The two `1/D` factors (one from `d₊ = Dt`, one from `thm:tensor-e`) give `D²` in
the full event-level bound and a single `D` in the variant.  We encode the bound
as a real-algebra theorem in the assembled constants, threading the upstream
`thm:tensor-e`/`lem:BT-recip` bounds together with the mass law as hypotheses. -/

/-- **Certificate event-level tensorisation** (`prop:event-tensor`).

Let `μ_b ≍ (log X)³` (`mass_law`, recorded as the two constants `cμ, Cμ` and a
threshold) and let `B` (resp. `Bsingle`) be the event-mass restricted by
`e ≡ c (D)` (resp. only `D ∣ d₊`).  Suppose the assembled upstream bound holds:
`B X D ≤ Kassemb · (logCube X / D²)` and
`Bsingle X D ≤ Kassemb · (logCube X / D)` before using
`(log X)³ ≍ μ_b`.
Then, using the mass-law sandwich's lower constant `cμ > 0`
(so `(log X)³ ≤ μ_b/cμ`), we conclude
`B X D ≤ (Kassemb/cμ) · (μ_b X / D²)` and
`Bsingle X D ≤ (Kassemb/cμ) · (μ_b X / D)` — i.e. `B ≪ μ_b/D²` and
`Bsingle ≪ μ_b/D`. -/
theorem logCube_le_div_of_mass_lower
    (μb : ℝ → ℝ) (cμ X₀ : ℝ) (hcμ : 0 < cμ)
    (hmass_lower : ∀ X : ℝ, X₀ ≤ X → cμ * logCube X ≤ μb X) :
    ∀ X : ℝ, X₀ ≤ X → logCube X ≤ μb X / cμ := by
  intro X hX
  have hlow : cμ * logCube X ≤ μb X := hmass_lower X hX
  rw [le_div_iff₀ hcμ]
  linarith [hlow]

/-- The log-cube shape is nonnegative on the eventual range used by the mass law. -/
theorem logCube_nonneg_of_exp_one_le {X : ℝ} (hX : Real.exp 1 ≤ X) :
    0 ≤ logCube X := by
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hlog : 1 ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hX
  unfold logCube
  positivity

/-- One-sided `D²` event tensor bound, extracted from `event_tensor`. -/
theorem event_tensor_double_from_logCube_bound
    (μb : ℝ → ℝ) (B : ℝ → ℕ → ℝ)
    (cμ Kassemb X₀ : ℝ) (hcμ : 0 < cμ) (hKassemb : 0 ≤ Kassemb)
    (hmass_lower : ∀ X : ℝ, X₀ ≤ X → cμ * logCube X ≤ μb X)
    (hassemb : ∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)) :
    ∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
      B X D ≤ (Kassemb / cμ) * (μb X / (D : ℝ) ^ 2) := by
  intro X hX D hD
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < (D : ℝ) := lt_of_lt_of_le one_pos hD1
  have hD2pos : (0 : ℝ) < (D : ℝ) ^ 2 := by positivity
  have hcube_le : logCube X ≤ μb X / cμ :=
    logCube_le_div_of_mass_lower μb cμ X₀ hcμ hmass_lower X hX
  calc B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2) := hassemb X hX D hD
    _ ≤ Kassemb * ((μb X / cμ) / (D : ℝ) ^ 2) := by
        gcongr
    _ = (Kassemb / cμ) * (μb X / (D : ℝ) ^ 2) := by ring

/-- One-sided `D` event tensor bound, extracted from `event_tensor`. -/
theorem event_tensor_single_from_logCube_bound
    (μb : ℝ → ℝ) (Bsingle : ℝ → ℕ → ℝ)
    (cμ Kassemb X₀ : ℝ) (hcμ : 0 < cμ) (hKassemb : 0 ≤ Kassemb)
    (hmass_lower : ∀ X : ℝ, X₀ ≤ X → cμ * logCube X ≤ μb X)
    (hassemb : ∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
      Bsingle X D ≤ (Kassemb / cμ) * (μb X / (D : ℝ)) := by
  intro X hX D hD
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < (D : ℝ) := lt_of_lt_of_le one_pos hD1
  have hcube_le : logCube X ≤ μb X / cμ :=
    logCube_le_div_of_mass_lower μb cμ X₀ hcμ hmass_lower X hX
  calc Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ)) := hassemb X hX D hD
    _ ≤ Kassemb * ((μb X / cμ) / (D : ℝ)) := by
        gcongr
    _ = (Kassemb / cμ) * (μb X / (D : ℝ)) := by ring

/-- **Certificate event-level tensorisation** (`prop:event-tensor`).

Bundled form of the one-sided `D²` and `D` tensor bounds. -/
theorem event_tensor
    (μb : ℝ → ℝ) (B Bsingle : ℝ → ℕ → ℝ)
    (cμ Kassemb X₀ : ℝ) (hcμ : 0 < cμ) (hKassemb : 0 ≤ Kassemb)
    -- the mass-law lower bound `cμ (log X)³ ≤ μ_b` (from `mass_law`)
    (hmass_lower : ∀ X : ℝ, X₀ ≤ X → cμ * logCube X ≤ μb X)
    -- the assembled `(log X)³`-form bounds (from `thm:tensor-e` + `lem:BT-recip`)
    (hassemb : ∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
      B X D ≤ (Kassemb / cμ) * (μb X / (D : ℝ) ^ 2)
        ∧ Bsingle X D ≤ (Kassemb / cμ) * (μb X / (D : ℝ)) := by
  intro X hX D hD
  exact
    ⟨event_tensor_double_from_logCube_bound μb B cμ Kassemb X₀ hcμ hKassemb
        hmass_lower (fun X hX D hD => (hassemb X hX D hD).1) X hX D hD,
      event_tensor_single_from_logCube_bound μb Bsingle cμ Kassemb X₀ hcμ hKassemb
        hmass_lower (fun X hX D hD => (hassemb X hX D hD).2) X hX D hD⟩

/-- Range-restricted version of `event_tensor`.

This is the form used when the paper only needs the event tensor on an
admissible modulus range, such as squarefree odd `D≤YU`. -/
theorem event_tensor_on_range
    (μb : ℝ → ℝ) (B Bsingle : ℝ → ℕ → ℝ) (R : ℝ → ℕ → Prop)
    (cμ Kassemb X₀ : ℝ) (hcμ : 0 < cμ) (hKassemb : 0 ≤ Kassemb)
    (hmass_lower : ∀ X : ℝ, X₀ ≤ X → cμ * logCube X ≤ μb X)
    (hassemb : ∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D → R X D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D → R X D →
      B X D ≤ (Kassemb / cμ) * (μb X / (D : ℝ) ^ 2)
        ∧ Bsingle X D ≤ (Kassemb / cμ) * (μb X / (D : ℝ)) := by
  intro X hX D hD hR
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < (D : ℝ) := lt_of_lt_of_le one_pos hD1
  have hD2pos : (0 : ℝ) < (D : ℝ) ^ 2 := by positivity
  have hcube_le : logCube X ≤ μb X / cμ :=
    logCube_le_div_of_mass_lower μb cμ X₀ hcμ hmass_lower X hX
  rcases hassemb X hX D hD hR with ⟨hdouble, hsingle⟩
  constructor
  · calc
      B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2) := hdouble
      _ ≤ Kassemb * ((μb X / cμ) / (D : ℝ) ^ 2) := by
          gcongr
      _ = (Kassemb / cμ) * (μb X / (D : ℝ) ^ 2) := by ring
  · calc
      Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ)) := hsingle
      _ ≤ Kassemb * ((μb X / cμ) / (D : ℝ)) := by
          gcongr
      _ = (Kassemb / cμ) * (μb X / (D : ℝ)) := by ring

/-! ## Headline corollary: the mass law in `μ_b ≍ (log X)³` ≍-packaged form.

For downstream files (`Optimization`, `BrunSuen`), the clean consumable form is
the two-sided sandwich with explicit positive constants, plus the event-tensor
bounds expressed against `μ_b` itself.  We package both. -/

/-- The mass law together with the event-tensor bounds, assembled from the same
constituent inputs, as a single consumable bundle (`prop:mu` + `prop:event-tensor`).
This is the form fed to `EscAnalytic.Optimization` (`mu_asymp_N`) and
`EscAnalytic.BrunSuen` (`mass_dependency_scale`, `delta_Delta_bounds`). -/
theorem mass_law_and_event_tensor
    (P : Params) (b : ℕ) (sigmaSmall roughFactor : ℝ → ℝ)
    (hSig : FactorAsymp sigmaSmall sigmaShape)
    (hR : FactorAsymp roughFactor roughShape)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X ≤ muB P b sigmaSmall roughFactor X
          ∧ muB P b sigmaSmall roughFactor X ≤ c₂ * logCube X)
      ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b sigmaSmall roughFactor X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b sigmaSmall roughFactor X / (D : ℝ))) := by
  obtain ⟨c₁, hc₁, c₂, hc₂, Xm, hmass⟩ := mass_law P b sigmaSmall roughFactor hSig hR
  refine ⟨c₁, hc₁, c₂, hc₂, Kassemb / c₁, by positivity,
          max Xm XB, ?_, ?_⟩
  · intro X hX
    exact hmass X (le_trans (le_max_left _ _) hX)
  · intro X hX D hD
    have hXm : Xm ≤ X := le_trans (le_max_left _ _) hX
    have hXB : XB ≤ X := le_trans (le_max_right _ _) hX
    have hmass_lower : c₁ * logCube X ≤ muB P b sigmaSmall roughFactor X :=
      (hmass X hXm).1
    exact event_tensor (muB P b sigmaSmall roughFactor) B Bsingle c₁ Kassemb
      (max Xm XB) hc₁ hKassemb
      (fun X hX => by
        have : c₁ * logCube X ≤ muB P b sigmaSmall roughFactor X :=
          (hmass X (le_trans (le_max_left _ _) hX)).1
        exact this)
      (fun X hX D hD => hassemb X (le_trans (le_max_right _ _) hX) D hD)
      X hX D hD

/-- Range-restricted mass-law plus event-tensor bundle.

This is the form used when the assembled event bounds are proved only on the
manuscript's admissible modulus range.  The mass law remains global for large
`X`; the event conclusion carries the same range predicate `R`. -/
theorem mass_law_and_event_tensor_on_range
    (P : Params) (b : ℕ) (sigmaSmall roughFactor : ℝ → ℝ)
    (hSig : FactorAsymp sigmaSmall sigmaShape)
    (hR : FactorAsymp roughFactor roughShape)
    (B Bsingle : ℝ → ℕ → ℝ) (R : ℝ → ℕ → Prop)
    (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D → R X D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X ≤ muB P b sigmaSmall roughFactor X
          ∧ muB P b sigmaSmall roughFactor X ≤ c₂ * logCube X)
      ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D → R X D →
        B X D ≤ Kev * (muB P b sigmaSmall roughFactor X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b sigmaSmall roughFactor X / (D : ℝ))) := by
  obtain ⟨c₁, hc₁, c₂, hc₂, Xm, hmass⟩ := mass_law P b sigmaSmall roughFactor hSig hR
  refine ⟨c₁, hc₁, c₂, hc₂, Kassemb / c₁, by positivity,
          max Xm XB, ?_, ?_⟩
  · intro X hX
    exact hmass X (le_trans (le_max_left _ _) hX)
  · intro X hX D hD hRD
    exact event_tensor_on_range (muB P b sigmaSmall roughFactor) B Bsingle R
      c₁ Kassemb (max Xm XB) hc₁ hKassemb
      (fun X hX => by
        exact (hmass X (le_trans (le_max_left _ _) hX)).1)
      (fun X hX D hD hRD =>
        hassemb X (le_trans (le_max_right _ _) hX) D hD hRD)
      X hX D hD hRD

/-- Event-tensor bundle with the sign of the assembled event constant discharged
internally.

The assembled upstream estimate can be stated with an arbitrary constant
`Kassemb`.  On the eventual range `logCube X / D^j` is nonnegative, so replacing
`Kassemb` by `max Kassemb 0` weakens the premise only by a checked algebraic
step and removes the separate hypothesis `0 ≤ Kassemb`. -/
theorem mass_law_and_event_tensor_of_arbitrary_event_constant
    (P : Params) (b : ℕ) (sigmaSmall roughFactor : ℝ → ℝ)
    (hSig : FactorAsymp sigmaSmall sigmaShape)
    (hR : FactorAsymp roughFactor roughShape)
    (B Bsingle : ℝ → ℕ → ℝ) (Kassemb XB : ℝ)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X ≤ muB P b sigmaSmall roughFactor X
          ∧ muB P b sigmaSmall roughFactor X ≤ c₂ * logCube X)
      ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kev * (muB P b sigmaSmall roughFactor X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kev * (muB P b sigmaSmall roughFactor X / (D : ℝ))) := by
  let Kpos : ℝ := max Kassemb 0
  let XBpos : ℝ := max XB (Real.exp 1)
  refine mass_law_and_event_tensor P b sigmaSmall roughFactor hSig hR
    B Bsingle Kpos XBpos (le_max_right _ _) ?_
  intro X hX D hD
  have hXB : XB ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < (D : ℝ) := lt_of_lt_of_le one_pos hD1
  have hD2pos : (0 : ℝ) < (D : ℝ) ^ 2 := by positivity
  have hcube_nonneg : 0 ≤ logCube X := logCube_nonneg_of_exp_one_le hXexp
  have hshape2_nonneg : 0 ≤ logCube X / (D : ℝ) ^ 2 :=
    div_nonneg hcube_nonneg hD2pos.le
  have hshape1_nonneg : 0 ≤ logCube X / (D : ℝ) :=
    div_nonneg hcube_nonneg hDpos.le
  have hKle : Kassemb ≤ Kpos := le_max_left _ _
  rcases hassemb X hXB D hD with ⟨hB, hsingle⟩
  refine ⟨?_, ?_⟩
  · calc
      B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2) := hB
      _ ≤ Kpos * (logCube X / (D : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hKle hshape2_nonneg
  · calc
      Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ)) := hsingle
      _ ≤ Kpos * (logCube X / (D : ℝ)) :=
        mul_le_mul_of_nonneg_right hKle hshape1_nonneg

/-- Fixed finite modifications of the factors and event carriers preserve the
mass-law plus event-tensor package.

This is the event-tensor companion to `mass_law_of_factor_comparable` for the
fixed-`m` route in `prop:fixed-m-transfer`.  The modified small and rough
factors are only required to be eventually comparable to the original factors,
and the modified event carriers are only required to be eventually bounded by a
fixed multiple of the original assembled carriers.  The conclusion is the same
`μ ≍ (log X)^3`, `B_{D,c} ≪ μ/D^2`, and `D ∣ d_+` `≪ μ/D` package, with
constants allowed to change. -/
theorem mass_law_and_event_tensor_of_factor_event_comparable
    (P : Params) (b : ℕ)
    (sigmaSmall roughFactor sigmaSmall' roughFactor' : ℝ → ℝ)
    (hSig : FactorAsymp sigmaSmall sigmaShape)
    (hR : FactorAsymp roughFactor roughShape)
    (Xsig Xrough aSig ASig aR AR : ℝ)
    (haSig : 0 < aSig) (hASig : 0 < ASig)
    (haR : 0 < aR) (hAR : 0 < AR)
    (hSigCmp : ∀ X : ℝ, Xsig ≤ X →
      aSig * sigmaSmall X ≤ sigmaSmall' X ∧ sigmaSmall' X ≤ ASig * sigmaSmall X)
    (hRoughCmp : ∀ X : ℝ, Xrough ≤ X →
      aR * roughFactor X ≤ roughFactor' X ∧ roughFactor' X ≤ AR * roughFactor X)
    (B Bsingle B' Bsingle' : ℝ → ℕ → ℝ)
    (Xevent Aevent : ℝ) (hAevent : 0 ≤ Aevent)
    (hEventCmp : ∀ X : ℝ, Xevent ≤ X → ∀ D : ℕ, 1 ≤ D →
      B' X D ≤ Aevent * B X D ∧ Bsingle' X D ≤ Aevent * Bsingle X D)
    (Kassemb XB : ℝ) (hKassemb : 0 ≤ Kassemb)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X ≤ muB P b sigmaSmall' roughFactor' X
          ∧ muB P b sigmaSmall' roughFactor' X ≤ c₂ * logCube X)
      ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B' X D ≤ Kev * (muB P b sigmaSmall' roughFactor' X / (D : ℝ) ^ 2)
          ∧ Bsingle' X D ≤ Kev * (muB P b sigmaSmall' roughFactor' X / (D : ℝ))) := by
  obtain ⟨c₁, hc₁, c₂, hc₂, Xm, hmass⟩ :=
    mass_law_of_factor_comparable P b sigmaSmall roughFactor sigmaSmall' roughFactor'
      hSig hR Xsig Xrough aSig ASig aR AR haSig hASig haR hAR hSigCmp hRoughCmp
  refine ⟨c₁, hc₁, c₂, hc₂, (Aevent * Kassemb) / c₁,
          div_nonneg (mul_nonneg hAevent hKassemb) hc₁.le,
          max Xm (max XB Xevent), ?_, ?_⟩
  · intro X hX
    exact hmass X (le_trans (le_max_left _ _) hX)
  · intro X hX D hD
    exact event_tensor (muB P b sigmaSmall' roughFactor') B' Bsingle'
      c₁ (Aevent * Kassemb) (max Xm (max XB Xevent)) hc₁
      (mul_nonneg hAevent hKassemb)
      (fun X hX => by
        have hXm : Xm ≤ X := le_trans (le_max_left _ _) hX
        exact (hmass X hXm).1)
      (fun X hX D hD => by
        have hXB : XB ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
        have hXe : Xevent ≤ X :=
          le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
        have hold := hassemb X hXB D hD
        have hcmp := hEventCmp X hXe D hD
        constructor
        · calc
            B' X D ≤ Aevent * B X D := hcmp.1
            _ ≤ Aevent * (Kassemb * (logCube X / (D : ℝ) ^ 2)) := by
              exact mul_le_mul_of_nonneg_left hold.1 hAevent
            _ = (Aevent * Kassemb) * (logCube X / (D : ℝ) ^ 2) := by ring
        · calc
            Bsingle' X D ≤ Aevent * Bsingle X D := hcmp.2
            _ ≤ Aevent * (Kassemb * (logCube X / (D : ℝ))) := by
              exact mul_le_mul_of_nonneg_left hold.2 hAevent
            _ = (Aevent * Kassemb) * (logCube X / (D : ℝ)) := by ring)
      X hX D hD

/-- Fixed finite modifications preserve the mass/event package without asking
separately that the assembled event constant is nonnegative.

This is the sign-free companion to
`mass_law_and_event_tensor_of_factor_event_comparable`: the comparison constant
`Aevent` still has to be nonnegative because it multiplies an inequality, but the
upstream log-cube event constant is absorbed by
`mass_law_and_event_tensor_of_arbitrary_event_constant`. -/
theorem mass_law_and_event_tensor_of_factor_event_comparable_arbitrary_event_constant
    (P : Params) (b : ℕ)
    (sigmaSmall roughFactor sigmaSmall' roughFactor' : ℝ → ℝ)
    (hSig : FactorAsymp sigmaSmall sigmaShape)
    (hR : FactorAsymp roughFactor roughShape)
    (Xsig Xrough aSig ASig aR AR : ℝ)
    (haSig : 0 < aSig) (hASig : 0 < ASig)
    (haR : 0 < aR) (hAR : 0 < AR)
    (hSigCmp : ∀ X : ℝ, Xsig ≤ X →
      aSig * sigmaSmall X ≤ sigmaSmall' X ∧ sigmaSmall' X ≤ ASig * sigmaSmall X)
    (hRoughCmp : ∀ X : ℝ, Xrough ≤ X →
      aR * roughFactor X ≤ roughFactor' X ∧ roughFactor' X ≤ AR * roughFactor X)
    (B Bsingle B' Bsingle' : ℝ → ℕ → ℝ)
    (Xevent Aevent : ℝ) (hAevent : 0 ≤ Aevent)
    (hEventCmp : ∀ X : ℝ, Xevent ≤ X → ∀ D : ℕ, 1 ≤ D →
      B' X D ≤ Aevent * B X D ∧ Bsingle' X D ≤ Aevent * Bsingle X D)
    (Kassemb XB : ℝ)
    (hassemb : ∀ X : ℝ, XB ≤ X → ∀ D : ℕ, 1 ≤ D →
        B X D ≤ Kassemb * (logCube X / (D : ℝ) ^ 2)
          ∧ Bsingle X D ≤ Kassemb * (logCube X / (D : ℝ))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ Kev : ℝ, 0 ≤ Kev ∧ ∃ X₀ : ℝ,
      (∀ X : ℝ, X₀ ≤ X →
        c₁ * logCube X ≤ muB P b sigmaSmall' roughFactor' X
          ∧ muB P b sigmaSmall' roughFactor' X ≤ c₂ * logCube X)
      ∧ (∀ X : ℝ, X₀ ≤ X → ∀ D : ℕ, 1 ≤ D →
        B' X D ≤ Kev * (muB P b sigmaSmall' roughFactor' X / (D : ℝ) ^ 2)
          ∧ Bsingle' X D ≤ Kev * (muB P b sigmaSmall' roughFactor' X / (D : ℝ))) := by
  let hSig' : FactorAsymp sigmaSmall' sigmaShape :=
    FactorAsymp.of_eventual_const_comparable hSig Xsig aSig ASig
      haSig hASig hSigCmp
  let hR' : FactorAsymp roughFactor' roughShape :=
    FactorAsymp.of_eventual_const_comparable hR Xrough aR AR
      haR hAR hRoughCmp
  refine mass_law_and_event_tensor_of_arbitrary_event_constant P b sigmaSmall'
    roughFactor' hSig' hR' B' Bsingle' (Aevent * Kassemb) (max XB Xevent) ?_
  intro X hX D hD
  have hXB : XB ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Xevent ≤ X := le_trans (le_max_right _ _) hX
  have hold := hassemb X hXB D hD
  have hcmp := hEventCmp X hXe D hD
  constructor
  · calc
      B' X D ≤ Aevent * B X D := hcmp.1
      _ ≤ Aevent * (Kassemb * (logCube X / (D : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hold.1 hAevent
      _ = (Aevent * Kassemb) * (logCube X / (D : ℝ) ^ 2) := by ring
  · calc
      Bsingle' X D ≤ Aevent * Bsingle X D := hcmp.2
      _ ≤ Aevent * (Kassemb * (logCube X / (D : ℝ))) :=
        mul_le_mul_of_nonneg_left hold.2 hAevent
      _ = (Aevent * Kassemb) * (logCube X / (D : ℝ)) := by ring

end EscAnalytic
