import EscAnalytic.Paper

/-!
# Trust-boundary check

This module fails to compile if the public main theorem gains or loses an
axiom dependency.  Its expected list consists of Lean's three foundational
axioms and the nine external theorems recorded in `FORMALIZATION.md`.
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

partial def collectAxioms
    (env : Environment) (name : Name) (visited found : NameSet) :
    NameSet × NameSet :=
  if visited.contains name then
    (visited, found)
  else
    let visited := visited.insert name
    match env.find? name with
    | some (ConstantInfo.axiomInfo _) => (visited, found.insert name)
    | some (ConstantInfo.defnInfo info) =>
        let state := collectExpr env info.type visited found
        collectExpr env info.value state.1 state.2
    | some (ConstantInfo.thmInfo info) =>
        let state := collectExpr env info.type visited found
        collectExpr env info.value state.1 state.2
    | some (ConstantInfo.opaqueInfo info) =>
        let state := collectExpr env info.type visited found
        collectExpr env info.value state.1 state.2
    | some (ConstantInfo.ctorInfo info) => collectExpr env info.type visited found
    | some (ConstantInfo.recInfo info) => collectExpr env info.type visited found
    | some (ConstantInfo.inductInfo info) =>
        let state := collectExpr env info.type visited found
        info.ctors.foldl
          (fun state ctor => collectAxioms env ctor state.1 state.2)
          state
    | some (ConstantInfo.quotInfo _) | none => (visited, found)
where
  collectExpr
      (env : Environment) (expr : Expr) (visited found : NameSet) :
      NameSet × NameSet :=
    expr.getUsedConstants.foldl
      (fun state used => collectAxioms env used state.1 state.2)
      (visited, found)

def sortedNames (names : List Name) : List String :=
  (names.map Name.toString).mergeSort (· < ·)

#eval show CoreM Unit from do
  let env ← getEnv
  let (_, found) := collectAxioms env
    ``EscAnalytic.erdos_straus_exceptional_set_bound {} {}
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
  logInfo "Main-theorem trust boundary verified: three Lean axioms and nine external theorems."

end EscAnalytic.TrustBoundary
