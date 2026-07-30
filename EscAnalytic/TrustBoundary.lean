import EscAnalytic.Paper

/-!
# Trust-boundary check

This module fails to compile if the public main theorem gains or loses an
axiom dependency.  Its expected list consists of Lean's three foundational
axioms and the nine named statements recorded in `FORMALIZATION.md`.
-/

open Lean

namespace EscAnalytic.TrustBoundary

def expectedAxioms : List Name :=
  [``propext,
   ``Classical.choice,
   ``Quot.sound,
   ``Inputs.standard_brun_titchmarsh_reciprocal_bound,
   ``Inputs.standard_modular_suen_correlation_inequality,
   ``Inputs.standard_ordinary_squarefree_progression_coprime_density_lower_long,
   ``Inputs.standard_ordinary_squarefree_progression_coprime_density_upper_yu,
   ``Inputs.standard_prime_product_log_power_rough_window_count_discrepancy_uniform_normalized_small_bound,
   ``Inputs.standard_prime_recip_sharp_mertens_nat_defect_eventually_upper_bound,
   ``Inputs.standard_prime_recip_window_mertens_lower_bound,
   ``Inputs.standard_reciprocal_bombieri_vinogradov_weighted_same_carrier,
   ``Inputs.standard_selberg_upper_long_progressions]

def constantDependencies (info : ConstantInfo) : List Name :=
  let used (expr : Expr) := expr.getUsedConstants.toList
  match info with
  | .axiomInfo _ => []
  | .defnInfo info => used info.type ++ used info.value
  | .thmInfo info => used info.type ++ used info.value
  | .opaqueInfo info => used info.type ++ used info.value
  | .ctorInfo info => used info.type
  | .recInfo info => used info.type
  | .inductInfo info => used info.type ++ info.ctors
  | .quotInfo _ => []

def environmentConstantCount (env : Environment) : Nat :=
  env.constants.fold (init := 0) fun count _ _ => count + 1

/-- A declaration contributes at most two expression dependency sets and, for
an inductive declaration, one constructor list. Each contains at most all
constants in the environment. The traversal reports failure if this budget is
ever exhausted. -/
def traversalWorkBudget (env : Environment) : Nat :=
  let count := environmentConstantCount env
  3 * count * count + 1

def collectAxiomsAux (env : Environment) :
    Nat → List Name → NameSet → NameSet → List Name × NameSet × NameSet
  | 0, pending, visited, found => (pending, visited, found)
  | _ + 1, [], visited, found => ([], visited, found)
  | fuel + 1, name :: pending, visited, found =>
      if visited.contains name then
        collectAxiomsAux env fuel pending visited found
      else
        let visited := visited.insert name
        match env.find? name with
        | some (.axiomInfo _) =>
            collectAxiomsAux env fuel pending visited (found.insert name)
        | some info =>
            collectAxiomsAux env fuel
              (constantDependencies info ++ pending) visited found
        | none =>
            collectAxiomsAux env fuel pending visited found

def collectAxioms
    (env : Environment) (root : Name) : Option (NameSet × NameSet) :=
  let (pending, visited, found) :=
    collectAxiomsAux env (traversalWorkBudget env) [root] {} {}
  if pending.isEmpty then some (visited, found) else none

def sortedNames (names : List Name) : List String :=
  (names.map Name.toString).mergeSort (· < ·)

#eval show CoreM Unit from do
  let env ← getEnv
  let result :=
    collectAxioms env ``EscAnalytic.erdos_straus_exceptional_set_bound
  let (_, found) ←
    match result with
    | some state => pure state
    | none => throwError "trust-boundary traversal exhausted its work budget"
  let foundNames := env.constants.fold (init := []) fun names name info =>
    if found.contains name then
      match info with
      | ConstantInfo.axiomInfo _ => name :: names
      | _ => names
    else
      names
  let expected := sortedNames expectedAxioms
  let actual := sortedNames foundNames
  unless actual == expected do
    throwError m!"main-theorem trust boundary changed\nexpected: {expected}\nactual: {actual}"
  logInfo "Main-theorem trust boundary verified: three Lean axioms and nine named statements."

end EscAnalytic.TrustBoundary
