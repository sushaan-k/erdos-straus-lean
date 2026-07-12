import Mathlib.Tactic
import EscAnalytic.Core

/-!
# Fan-curve geometry

This module proves the algebraic content of the divisor-fan curve theorem in
`esc.tex`, namely

* `lem:fan`              (divisor-fan certificate, tex lines ~294–323),
* `thm:fan-curves`       (divisor-fan curves on the Cayley compactification,
                          tex lines ~325–354),
* `eq:fan-curve-hyperbola`  `q y z = a n (y+z)` and its product form
                          `(q y - a n)(q z - a n) = a²n²`  (tex lines ~331–335),
* `eq:fan-curve-param`   the `𝔾ₘ` rational parametrization
                          `u ↦ (a n, (a n + u)/q, (a n + a²n²/u)/q)` with inverse
                          `u = q y - a n`  (tex lines ~336–341),
* the algebraic core of `cor:geometric-main`  (the certificate-to-curve
  identification, tex lines ~356–366).

The Erdős–Straus surface is `U_n : 4xyz = n(xy + xz + yz) ⊂ 𝔸³` (tex line 326);
the fan curve is the plane section `C_{n,a} = U_n ∩ {x = a n}` (tex line 328).

This is pure field algebra and uses no analytic input.  The identities are
proved with `ring` and `field_simp`.
The statements are aligned with the manuscript and are proved first over a
general `Field` (the geometric content) and then specialized to `ℚ` for the
unit-fraction identity `4/n = 1/x + 1/y + 1/z`.
-/

namespace EscAnalytic.Geometry

open scoped BigOperators

/-! ## The Erdős–Straus cubic surface and its fan section.

We encode the surface `U_n : 4xyz = n(xy + xz + yz)` (tex line 326) over a general
field, with the section condition `x = a n` substituted in. -/

/-- The Erdős–Straus surface equation `U_n` (tex line 326):
`4 x y z = n (x y + x z + y z)`, over a general field. -/
def onSurface {K : Type*} [Field K] (n x y z : K) : Prop :=
  4 * x * y * z = n * (x * y + x * z + y * z)

/-- The fan-curve hyperbola `eq:fan-curve-hyperbola` (tex line 332):
`q y z = a n (y + z)` with `q = 4 a - 1`. -/
def onHyperbola {K : Type*} [Field K] (a n q y z : K) : Prop :=
  q * y * z = a * n * (y + z)

/-- The product form of the fan curve `eq:fan-curve-hyperbola` (tex line 334):
`(q y - a n)(q z - a n) = a²n²`. -/
def onProductCurve {K : Type*} [Field K] (a n q y z : K) : Prop :=
  (q * y - a * n) * (q * z - a * n) = (a * n) ^ 2

/-! ## Step 1: the substitution `x = a n` (tex lines 345–349).

Substituting `x = a n` into `4 x y z = n (x y + x z + y z)` and using `q = 4 a - 1`
yields the hyperbola `q y z = a n (y + z)`.  The manuscript intermediate form is
`4 a y z = a n (y + z) + y z` (tex line 347), which is exactly the surface equation
after dividing by `n` and substituting `x = a n`; clearing it gives the hyperbola. -/

/-- The substitution `x = a n` turns the surface equation `U_n` into the fan-curve
hyperbola.  This is the forward direction of the first line of the proof of
`thm:fan-curves` (tex lines 345–349): with `q = 4 a - 1`, the point `(a n, y, z)`
lies on `U_n` (for `n ≠ 0`) iff `q y z = a n (y + z)`. -/
theorem onSurface_section_iff_onHyperbola {K : Type*} [Field K]
    (a n q y z : K) (hq : q = 4 * a - 1) (hn : n ≠ 0) :
    onSurface n (a * n) y z ↔ onHyperbola a n q y z := by
  subst hq
  unfold onSurface onHyperbola
  constructor
  · intro h
    -- `4 a n y z = n (a n y + a n z + y z)`; cancel one `n` to get `(4a-1) y z = a n (y+z)`.
    have h' : n * ((4 * a - 1) * y * z) = n * (a * n * (y + z)) := by linear_combination h
    exact mul_left_cancel₀ hn h'
  · intro h
    -- Conversely, `n · h` is exactly the surface equation with `x = a n`.
    linear_combination n * h

/-! ## Step 2: equivalence of the hyperbola and product forms (tex lines 349–351).

Multiplying the hyperbola by `q` and completing the product gives
`(q y - a n)(q z - a n) = q² y z - a n q (y + z) + a²n² = a²n²`. -/

/-- The product form follows from the hyperbola form (tex lines 349–351):
`q y z = a n (y + z) ⟹ (q y - a n)(q z - a n) = a²n²`.  (No nonvanishing
hypothesis needed in this direction.) -/
theorem onProductCurve_of_onHyperbola {K : Type*} [Field K]
    (a n q y z : K) (h : onHyperbola a n q y z) :
    onProductCurve a n q y z := by
  unfold onHyperbola at h
  unfold onProductCurve
  -- `(q y - a n)(q z - a n) = q² y z - a n q (y+z) + a²n²`; substitute `q y z = a n (y+z)`.
  linear_combination q * h

/-- The hyperbola form follows from the product form when `q ≠ 0`
(tex line 351, read backwards):
`(q y - a n)(q z - a n) = a²n² ⟹ q y z = a n (y + z)`. -/
theorem onHyperbola_of_onProductCurve {K : Type*} [Field K]
    (a n q y z : K) (hq : q ≠ 0) (h : onProductCurve a n q y z) :
    onHyperbola a n q y z := by
  unfold onProductCurve at h
  unfold onHyperbola
  have h0 : q * (q * y * z - a * n * (y + z)) = 0 := by linear_combination h
  have h1 : q * y * z - a * n * (y + z) = 0 := (mul_eq_zero.mp h0).resolve_left hq
  linear_combination h1

/-- Hyperbola form `⇔` product form, for `q ≠ 0` (eq:fan-curve-hyperbola,
tex lines 331–335). -/
theorem onHyperbola_iff_onProductCurve {K : Type*} [Field K]
    (a n q y z : K) (hq : q ≠ 0) :
    onHyperbola a n q y z ↔ onProductCurve a n q y z :=
  ⟨onProductCurve_of_onHyperbola a n q y z, onHyperbola_of_onProductCurve a n q y z hq⟩

/-! ## Step 3: the `𝔾ₘ` rational parametrization (eq:fan-curve-param, tex lines 336–341).

The map `u ↦ (a n, (a n + u)/q, (a n + a²n²/u)/q)` parametrizes the fan curve,
with inverse `u = q y - a n`. -/

/-- The second coordinate of the parametrization `eq:fan-curve-param` (tex line 339):
`y(u) = (a n + u)/q`. -/
def paramY {K : Type*} [Field K] (a n q u : K) : K := (a * n + u) / q

/-- The third coordinate of the parametrization `eq:fan-curve-param` (tex line 339):
`z(u) = (a n + a²n²/u)/q`. -/
def paramZ {K : Type*} [Field K] (a n q u : K) : K := (a * n + (a * n) ^ 2 / u) / q

/-- Key intermediate identities of the parametrization (tex line 314 / line 353):
`q · y(u) = a n + u` and `q · z(u) = a n + a²n²/u`.  These are the "denominator
equations" that make `u` a rational parameter. -/
theorem param_denominator_equations {K : Type*} [Field K]
    (a n q u : K) (hq : q ≠ 0) :
    q * paramY a n q u = a * n + u ∧
      q * paramZ a n q u = a * n + (a * n) ^ 2 / u := by
  unfold paramY paramZ
  refine ⟨?_, ?_⟩ <;> field_simp

/-- The image of `u` under the parametrization lies on the product curve
(tex line 353, "every point of the displayed form satisfies eq:fan-curve-hyperbola").
Requires `u ≠ 0` (the `𝔾ₘ` condition). -/
theorem param_onProductCurve {K : Type*} [Field K]
    (a n q u : K) (hq : q ≠ 0) (hu : u ≠ 0) :
    onProductCurve a n q (paramY a n q u) (paramZ a n q u) := by
  obtain ⟨hY, hZ⟩ := param_denominator_equations a n q u hq
  unfold onProductCurve
  have hYsub : q * paramY a n q u - a * n = u := by rw [hY]; ring
  have hZsub : q * paramZ a n q u - a * n = (a * n) ^ 2 / u := by rw [hZ]; ring
  rw [hYsub, hZsub]
  field_simp

/-- Consequently the image lies on the hyperbola too (eq:fan-curve-hyperbola). -/
theorem param_onHyperbola {K : Type*} [Field K]
    (a n q u : K) (hq : q ≠ 0) (hu : u ≠ 0) :
    onHyperbola a n q (paramY a n q u) (paramZ a n q u) :=
  onHyperbola_of_onProductCurve a n q _ _ hq (param_onProductCurve a n q u hq hu)

/-- The inverse map `u = q y - a n` recovers the second coordinate (tex line 341):
applying the parametrization to `u = q y - a n` returns `y`.  This is the left
inverse on the `y`-coordinate. -/
theorem paramY_inverse {K : Type*} [Field K]
    (a n q y : K) (hq : q ≠ 0) :
    paramY a n q (q * y - a * n) = y := by
  unfold paramY
  field_simp

/-- The inverse map also recovers the third coordinate when the point lies on the
hyperbola: if `(a n, y, z)` is on the fan curve and `y, z, q ≠ 0`, then applying the
parametrization to `u = q y - a n` returns `z`.  This together with
`paramY_inverse` shows `u ↦ (paramY, paramZ)` is a bijection onto the curve, with
inverse `u = q y - a n` (eq:fan-curve-param, tex line 341). -/
theorem paramZ_inverse {K : Type*} [Field K]
    (a n q y z : K) (hq : q ≠ 0) (hy : y ≠ 0) (_hz : z ≠ 0)
    (h : onHyperbola a n q y z) :
    paramZ a n q (q * y - a * n) = z := by
  unfold onHyperbola at h
  unfold paramZ
  -- From the product form, `(q y - a n)(q z - a n) = a²n²`, so
  -- `a²n²/(q y - a n) = q z - a n`, giving `paramZ(...) = z`.
  have hprod : (q * y - a * n) * (q * z - a * n) = (a * n) ^ 2 :=
    onProductCurve_of_onHyperbola a n q y z h
  -- `q y - a n ≠ 0`: otherwise `a²n² = 0` and then `q z - a n = ?`; handle via cases.
  rcases eq_or_ne (q * y - a * n) 0 with hu0 | hu0
  · -- then `(a n)^2 = 0`, i.e. `a*n = 0`; combined with `q*y - a*n = 0` gives `q*y = 0`,
    -- contradicting `q ≠ 0`, `y ≠ 0`.
    rw [hu0, zero_mul] at hprod
    have han : a * n = 0 := by
      have := sq_eq_zero_iff.mp hprod.symm
      exact this
    rw [han, sub_zero] at hu0
    exact absurd hu0 (mul_ne_zero hq hy)
  · have hzval : (a * n) ^ 2 / (q * y - a * n) = q * z - a * n := by
      rw [← hprod]; field_simp
    rw [hzval]
    field_simp

/-! ## Step 4: the unit-fraction identity over `ℚ` (lem:fan, tex lines 318–321).

From the fan curve we recover `4/n = 1/x + 1/y + 1/z` with `x = a n`.  The
manuscript derives `1/y + 1/z = q/A` from `q y z = A (y + z)` (`A = a n`, tex line
318), then `1/x + 1/y + 1/z = (1+q)/(a n) = 4/n` since `1 + q = 4 a` (tex line 320). -/

/-- The two-fraction identity (tex line 318): from the hyperbola
`q y z = a n (y + z)`, with `a n, y, z ≠ 0`, one gets `1/y + 1/z = q/(a n)`.
Proved over a general field. -/
theorem two_fraction_identity {K : Type*} [Field K]
    (a n q y z : K) (h : onHyperbola a n q y z)
    (han : a * n ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    1 / y + 1 / z = q / (a * n) := by
  unfold onHyperbola at h
  rw [div_add_div _ _ hy hz, div_eq_div_iff (mul_ne_zero hy hz) han]
  -- `(z + y) * (a n) = q * (y z)`; this is `h` rearranged.
  linear_combination -h

/-- The full unit-fraction identity (lem:fan, tex lines 318–321), over `ℚ`.
With `x = a n`, `q = 4 a - 1`, and a point on the fan-curve hyperbola, we have
`4/n = 1/x + 1/y + 1/z`. -/
theorem unit_fraction_identity_of_onHyperbola
    (a n q y z : ℚ) (hq : q = 4 * a - 1)
    (h : onHyperbola a n q y z)
    (hn : n ≠ 0) (ha : a ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    (4 : ℚ) / n = 1 / (a * n) + 1 / y + 1 / z := by
  subst hq
  unfold onHyperbola at h
  have han : a * n ≠ 0 := mul_ne_zero ha hn
  -- Rewrite the RHS as a single fraction and clear denominators against `4/n`.
  rw [div_add_div _ _ han hy, div_add_div _ _ (mul_ne_zero han hy) hz,
      div_eq_div_iff hn (mul_ne_zero (mul_ne_zero han hy) hz)]
  linear_combination n * h

/-- The same identity directly from the `𝔾ₘ` parameter `u` (combining `eq:fan-curve-param`
with `lem:fan`): for `u ≠ 0`, the point `(a n, paramY u, paramZ u)` satisfies
`4/n = 1/(a n) + 1/paramY u + 1/paramZ u`.  This is the unit-fraction certificate
attached to the parameter value `u` (the integral subfamily of tex line 341 takes
`u = e` with `e ∣ a²` and `n ≡ -4e mod q`). -/
theorem unit_fraction_identity_of_param
    (a n q u : ℚ) (hq : q = 4 * a - 1) (hqne : q ≠ 0)
    (hn : n ≠ 0) (ha : a ≠ 0) (hu : u ≠ 0)
    (hY : paramY a n q u ≠ 0) (hZ : paramZ a n q u ≠ 0) :
    (4 : ℚ) / n = 1 / (a * n) + 1 / paramY a n q u + 1 / paramZ a n q u := by
  have hhyp : onHyperbola a n q (paramY a n q u) (paramZ a n q u) :=
    param_onHyperbola a n q u hqne hu
  exact unit_fraction_identity_of_onHyperbola a n q _ _ hq hhyp hn ha hY hZ

end EscAnalytic.Geometry
