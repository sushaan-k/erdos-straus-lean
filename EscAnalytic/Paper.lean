import EscAnalytic.MainTheorem
import EscAnalytic.Geometry

/-!
# Paper-facing theorems

This is the public entry point for the formalization.  The implementation files
retain detailed intermediate statements, while this module exposes the closed
main theorem and its closed consequences under short, stable names.

The analytic results imported as external inputs are listed in
`EscAnalytic.Inputs`.  The exact dependency set of the declarations below is
checked by `scripts/check_public_capstone_frontier.lean`.
-/

namespace EscAnalytic

/-- The main exceptional-set theorem (`thm:main` in `esc.tex`). -/
theorem erdos_straus_exceptional_set_bound :
    IsMainBound exceptionalCount :=
  actualPaperFamily_exceptionalCount_mainBound_explicit

/-- The prime exceptional-set bound (`cor:prime-exceptional`). -/
theorem erdos_straus_prime_exceptional_set_bound :
    IsMainBound primeExceptionalCount :=
  prime_exceptional_of_main erdos_straus_exceptional_set_bound

/-- Prime-counting normalization of `cor:prime-exceptional`. -/
theorem erdos_straus_prime_exceptional_pi_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      (primeExceptionalCount N : ℝ) ≤
        C * (primePi N : ℝ) * saving c N :=
  prime_exceptional_le_primePi_saving erdos_straus_exceptional_set_bound

/-- The exceptional primes have relative density zero. -/
theorem erdos_straus_prime_exceptional_relative_density_zero :
    Filter.Tendsto
      (fun N : ℕ => (primeExceptionalCount N : ℝ) / (primePi N : ℝ))
      Filter.atTop (nhds 0) :=
  prime_exceptional_relative_density_zero_of_main
    erdos_straus_exceptional_set_bound

/-- Quantitative large-prime-factor consequence (`prop:large-prime-factor`). -/
theorem erdos_straus_large_prime_factor_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N Y : ℕ, 3 ≤ Y → Y ≤ N →
      (exceptionalGtYCount N Y : ℝ) ≤
        C * (N : ℝ) * (1 + Real.log N) * saving c Y :=
  exceptionalGtY_quantitative_of_main erdos_straus_exceptional_set_bound

/-- Power-threshold specialization of the large-prime-factor bound. -/
theorem erdos_straus_large_prime_factor_power_bound
    {η : ℝ} (hη : 0 < η) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N Y : ℕ,
      3 ≤ N → 3 ≤ Y → Y ≤ N → (N : ℝ) ^ η ≤ (Y : ℝ) →
        (exceptionalGtYCount N Y : ℝ) ≤ C * (N : ℝ) * saving c N :=
  exceptionalGtY_power_threshold_of_main
    erdos_straus_exceptional_set_bound hη

/-- Exponential-threshold specialization of the large-prime-factor bound. -/
theorem erdos_straus_large_prime_factor_exp_log_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N Y : ℕ,
      3 ≤ N → 3 ≤ Y → Y ≤ N →
      Real.exp ((Real.log (N : ℝ)) ^ ((3 : ℝ) / 4)) ≤ (Y : ℝ) →
        (exceptionalGtYCount N Y : ℝ) ≤
          C * (N : ℝ) * savingNineSixteen c N :=
  exceptionalGtY_exp_log_threshold_of_main
    erdos_straus_exceptional_set_bound

/-- Geometric form of the main bound (`cor:geometric-main`). -/
theorem erdos_straus_geometric_exceptional_set_bound :
    IsMainBound geometricExceptionalCount :=
  geometric_exceptional_of_main erdos_straus_exceptional_set_bound

end EscAnalytic
