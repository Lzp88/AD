import PaperVerifier.ADComplete.FinalTreeSeparation
import PaperVerifier.ADComplete.SpectralUniformProbes
import PaperVerifier.ADComplete.SpectralRankSensitiveProbes
import PaperVerifier.ADComplete.SpectralRigidity
import PaperVerifier.ADComplete.RealDegreeWitness
import PaperVerifier.ADComplete.InstructionPolynomial
import PaperVerifier.ADComplete.MainResourceEndpoints
import PaperVerifier.ADComplete.FixedPointedTables
import PaperVerifier.ADComplete.PointedPolynomialCoordinates
import PaperVerifier.ADComplete.PSDTreeRepresentative
import PaperVerifier.ADComplete.PSDFactoryResources
import PaperVerifier.ADComplete.PSDFactoryCounts
import PaperVerifier.ADComplete.SpiderRealPolynomialLowerBound
import PaperVerifier.ADComplete.FrobeniusTreeTables
import PaperVerifier.ADComplete.FullTraceTrees
import PaperVerifier.ADComplete.FullRepresentationResources
import PaperVerifier.ADComplete.FullTraceBits
import PaperVerifier.ADComplete.CircuitExports
import Lean.Util.CollectAxioms

/-! One frozen import closure and every project-local declaration therein.
The source-to-statement table records exact semantics and cited proof inputs. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut bodies : Nat := 0
  for (name, info) in env.constants.toList do
    let isProject := name.toString.contains "ADComplete" ||
      name.toString.contains "CircuitAudit" || name.toString.contains "PrincipalMomentAudit"
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
        logInfo m!"PAPER_AXIOM_AUDIT {name}: {axioms}"
  if checked = 0 ∨ bodies = 0 then
    throwError "Paper declaration scan was empty"
  logInfo m!"PAPER_AXIOM_AUDIT_PASSED declarations={checked} bodies={bodies}"

#check @ADComplete.SmallResidueRigidity.small_residue_rigidity
#check @ADComplete.Spanning.uniform_probes_of_spectral_diameter
#check @ADComplete.Spanning.rank_sensitive_probes_of_spectral_diameter
#check @ADComplete.ProbeDegreeLowerBound.exists_probe_of_degree_at_least
#check @ADComplete.FixedPointedTables.public_fixed_three_tables_iff_pointed_isometry
#check @ADComplete.PointedPolynomialCoordinates.tablePolynomial_evaluation
#check @ADComplete.PointedPolynomialCoordinates.actual_three_tables_have_bidegree
#check @PrincipalMomentAudit.WrittenProof.public_theorem_5_4_word_version
#check @ADComplete.TreeDistance.actual_allOnes_expression_identity
#check @ADComplete.InstructionDegrees.literal_polynomial_eq_written
#check @ADComplete.InstructionDegrees.literal_polynomial_self_adjoint
#check @ADComplete.InstructionDegrees.polynomial_evaluation
#check @ADComplete.FinalTreeSeparation.public_compiled_trace_classifies_trees
#check @ADComplete.InstructionHeights.compiled_gate_bound
#check @ADComplete.InstructionDegrees.compiled_all_degrees
#check @ADComplete.InstructionHeights.actual_register_sharp_bits
#check @ADComplete.MainResourceEndpoints.main_scalar_label_bits
#check @ADComplete.MainResourceEndpoints.probe_prefix_scalar_label_bits
#check @ADComplete.MainResourceEndpoints.actual_tree_final_trace_bits
#check @ADComplete.PSDFoldedFrame.fixed_folded_prefix
#check @ADComplete.PSDBird.compiler_determinant
#check @ADComplete.PSDFactory.compiled_value_folded
#check @ADComplete.PSDFactory.public_psd_factory_on_trees
#check @ADComplete.PSDPairStar.integerPolynomial_self_adjoint
#check @ADComplete.PSDPairStar.compiled_sum_of_squares
#check @ADComplete.PSDPairStar.compiled_posSemidef
#check @ADComplete.PSDFactory.compiled_safe_degree
#check @ADComplete.PSDFactory.compiled_gate_bound
#check @ADComplete.PSDFactory.compiled_scalar_labels_bits
#check @ADComplete.PSDFactory.actual_register_entry_bits
#check @ADComplete.SpiderGraph.actual_spider_polynomial_obstruction
#check @ADComplete.SpiderGraph.single_trace_degree_lower_bound
#check @ADComplete.SpiderGraph.witness_short_word_trace_eq
#check @ADComplete.Frobenius.public_full_three_tables_classify_trees
#check @ADComplete.FullRepresentationCompiler.actual_compiled_trace_iff_graphIso
#check @ADComplete.FullRepresentationCompiler.compiled_gate_bound
#check @ADComplete.FullRepresentationCompiler.compiled_all_degrees
#check @ADComplete.FullRepresentationCompiler.compiled_scalar_labels_bits
#check @ADComplete.FullRepresentationCompiler.actual_register_entry_bits
#check @ADComplete.FullRepresentationCompiler.polynomial_self_adjoint
#check @ADComplete.FullRepresentationCompiler.polynomial_evaluation
#check @ADComplete.FullRepresentationCompiler.actual_final_trace_bits
