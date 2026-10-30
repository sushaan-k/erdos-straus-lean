import ErdosStraus.Family.Completion

/-!
# Theorems 1 and 2: exceptional sets for the Erdős–Straus equation

The number `E(N)` of `2 ≤ n ≤ N` for which `4/n` is not a sum of three unit fractions
satisfies `E(N) ≪ N exp(-c (log N)^{3/4})` (Theorem 1), and the same bound holds for
every fixed numerator `m ≥ 4` (Theorem 2). The file also records the bound relative to
the primes and Example 1.1.
-/

namespace ErdosStraus

/-- Theorem 1: `E(N) ≪ N exp(-c (log N)^{3/4})` for `N ≥ 3`. -/
theorem erdos_straus_exceptional_set_bound :
    IsMainBound exceptionalCount :=
  FixedNumeratorMain.ordinary_main_bound Params.explicit

/-- Theorem 2: for fixed `m ≥ 4`,
`E_m(N) ≪_m N exp(-c_m (log N)^{3/4})` for `N ≥ 3`. -/
theorem erdos_straus_fixed_numerator_exceptional_set_bound
    (m : ℕ) (hm : 4 ≤ m) :
    IsMainBound (fixedNumeratorExceptionalCount m) :=
  FixedNumeratorMain.main_bound m (by omega) Params.explicit

/-- The exceptional primes up to `N` number `≪ π(N) exp(-c (log N)^{3/4})`. -/
theorem erdos_straus_prime_exceptional_pi_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N : ℕ, 3 ≤ N →
      (primeExceptionalCount N : ℝ) ≤
        C * (primePi N : ℝ) * saving c N :=
  prime_exceptional_le_primePi_saving erdos_straus_exceptional_set_bound

/-- Example 1.1: for `n = 2521`, `a = 12` and `h = 16`, the denominators of
Lemma 2.3 are `30252`, `644` and `1217643`, and
`4/2521 = 1/644 + 1/30252 + 1/1217643`. -/
theorem example_2521 :
    16 ∣ 12 ^ 2 ∧ 4 * 12 - 1 = 47 ∧ 2521 + 4 * 16 = 47 * 55 ∧
      ErdosStraus.Arithmetic.fixedFanX 2521 12 = 30252 ∧
      ErdosStraus.Arithmetic.fixedFanY 4 2521 12 16 = 644 ∧
      ErdosStraus.Arithmetic.fixedFanZ 4 2521 12 16 = 1217643 ∧
      (4 : ℚ) / 2521 = 1 / 644 + 1 / 30252 + 1 / 1217643 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, by norm_num⟩ <;>
    simp [Arithmetic.fixedFanX, Arithmetic.fixedFanY, Arithmetic.fixedFanZ, Arithmetic.fixedQ]

end ErdosStraus
