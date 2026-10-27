import PaperVerifier.ADComplete.PaperAxiomAudit
import MultiSymmetric.Audit
import Lean.Util.CollectAxioms
set_option autoImplicit false

/-! A declaration audit of the complete original and multiple-generator proof closure. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let required := [
    `MultiSymmetric.Rigidity.invariant_subspace_constant_rank,
    `MultiSymmetric.Rigidity.constant_and_invariant_rank,
    `MultiSymmetric.Krylov.polynomialVector_rationalKrylov,
    `MultiSymmetric.Spanning.rank_sensitive_spanning,
    `MultiSymmetric.Public.spectral_rank_prefix,
    `MultiSymmetric.Public.spectral_full_family,
    `MultiSymmetric.Recurrence.index_card,
    `MultiSymmetric.Recurrence.probe_mem_wordSpan,
    `MultiSymmetric.Recurrence.universalRow_evaluate,
    `MultiSymmetric.Recurrence.row_coeff_mulVec,
    `MultiSymmetric.Recurrence.universal_probe_response,
    `MultiSymmetric.Recurrence.row_one_eq_original,
    `MultiSymmetric.Circuit.complete_family_circuit,
    `MultiSymmetric.Circuit.familyRun_scalars_bound,
    `MultiSymmetric.Circuit.scalar_bit_bound]
  for name in required do
    match env.find? name with
    | some (.thmInfo _) => logInfo m!"COMBINED_REQUIRED_THEOREM {name}"
    | _ => throwError "Required endpoint is not a theorem: {name}"
  let mut checked : Nat := 0
  let mut bodies : Nat := 0
  let mut added : Nat := 0
  for (name, info) in env.constants.toList do
    let ns := name.toString
    let isNew := ns.contains "MultiSymmetric"
    let isProject := isNew || ns.contains "ADComplete" ||
      ns.contains "CircuitAudit" || ns.contains "PrincipalMomentAudit"
    if isProject then
      match info with
      | .axiomInfo _ => throwError "Unexpected project-local axiom: {name}"
      | _ =>
        let axioms ← collectAxioms name
        let bad := axioms.filter (fun a =>
          a != `propext && a != `Classical.choice && a != `Quot.sound)
        if !bad.isEmpty then
          throwError "Rejected transitive axiom dependency for {name}: {bad}"
        match info with
        | .thmInfo _ | .defnInfo _ | .opaqueInfo _ => bodies := bodies + 1
        | _ => pure ()
        checked := checked + 1
        if isNew then added := added + 1
        logInfo m!"COMBINED_AXIOM_AUDIT {name}: {axioms}"
  if checked = 0 ∨ bodies = 0 ∨ added = 0 then
    throwError "Empty combined declaration scan"
  logInfo m!"COMBINED_AXIOM_AUDIT_PASSED declarations={checked} bodies={bodies} added={added}"
