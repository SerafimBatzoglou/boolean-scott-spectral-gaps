module
import BooleanScott
import Lean.Util.CollectAxioms

#print axioms BooleanScott.unitFlow_iff_branch
#print axioms BooleanScott.branchless_not_analytic
#print axioms BooleanScott.borel_bf
#print axioms BooleanScott.clopen_threshold
#print axioms BooleanScott.unique_anchor_limit
#print axioms BooleanScott.negativeResolution_of_construction

#print axioms BooleanScott.clopen_array_iff
#print axioms BooleanScott.compactArrayHomeomorph
#print axioms BooleanScott.ledgerArrayHomeomorph
#print axioms BooleanScott.edge_conservation
#print axioms BooleanScott.fragment_markedRows
#print axioms BooleanScott.stoneRepresentation
#print axioms BooleanScott.stone_secondCountable
#print axioms BooleanScott.algebra_absorption_iff
#print axioms BooleanScott.borel_presentsBoolean
#print axioms BooleanScott.AtLevel.relative
#print axioms BooleanScott.relative_models_clopen
#print axioms BooleanScott.clopen_tree_membership
#print axioms BooleanScott.countable_array_clopens
#print axioms BooleanScott.countable_back_and_forth
#print axioms BooleanScott.chartScott_of_finite_types
#print axioms BooleanScott.second_derivative_formula
#print axioms BooleanScott.tower_height
#print axioms BooleanScott.mixed_private_mark
#print axioms BooleanScott.mixed_open_embedding_index
#print axioms BooleanScott.mixed_absorbs_tower
#print axioms BooleanScott.mixed_absorbs_cantor
#print axioms BooleanScott.repeated_basis
#print axioms BooleanScott.clopen_tuple_of_signs
#print axioms BooleanScott.mixed_stone
#print axioms BooleanScott.cantorScott
#print axioms BooleanScott.cantor_nonempty_clopen
#print axioms BooleanScott.fragments_repeated
#print axioms BooleanScott.spaceType_eq_iff
#print axioms BooleanScott.mixed_clopen_form
#print axioms BooleanScott.towerForm_determined
#print axioms BooleanScott.mixed_clopens_determined
#print axioms BooleanScott.isolatedClosure_finiteHit
#print axioms BooleanScott.signTerm_eval
#print axioms BooleanScott.scott_of_finite_counts
#print axioms BooleanScott.mixed_finite_scott
#print axioms BooleanScott.private_finiteHit
#print axioms BooleanScott.row_private_derivative
#print axioms BooleanScott.chart_second_tag
#print axioms BooleanScott.finite_ledger_rows
#print axioms BooleanScott.tagRoot_chart_row
#print axioms BooleanScott.finite_roots_outside
#print axioms BooleanScott.witness_stone
#print axioms BooleanScott.witness_named_anchors
#print axioms BooleanScott.witness_guard
#print axioms BooleanScott.GuardData.vertex_limit
#print axioms BooleanScott.GuardData.near_limit_reserve
#print axioms BooleanScott.finiteAnchors_test
#print axioms BooleanScott.guardClauses_iff
#print axioms BooleanScott.guardSentence
#print axioms BooleanScott.negativeResolution_of_tree_geometry
#print axioms BooleanScott.diagramBF_iff
#print axioms BooleanScott.measurable_diagramBF
#print axioms BooleanScott.chartRestrict_surjective
#print axioms BooleanScott.chartDiagram_measurable
#print axioms BooleanScott.codedChartMatch_iff
#print axioms BooleanScott.geometric_borel_of_chart_isolation
#print axioms BooleanScott.negativeResolution_of_chart_isolation_and_absorption
#print axioms BooleanScott.finiteIso_add
#print axioms BooleanScott.array_fragment_away
#print axioms BooleanScott.chart_root_free_comparison
#print axioms BooleanScott.chart_ledger_count
#print axioms BooleanScott.chart_fragment_ledger
#print axioms BooleanScott.row_clopen_balance
#print axioms BooleanScott.chart_clopen_balance
#print axioms BooleanScott.disjoint_vertex_sectors
#print axioms BooleanScott.TagCurrents.hasBranch
#print axioms BooleanScott.fixes_guard_vertex
#print axioms BooleanScott.shifted_sector
#print axioms BooleanScott.crossing_balance
#print axioms BooleanScott.image_exterior
#print axioms BooleanScott.guarded_absorption_implies_branch
#print axioms BooleanScott.negativeResolution_of_chart_isolation_and_branch_realization
#print axioms BooleanScott.match_row_arrays
#print axioms BooleanScott.slice_type
#print axioms BooleanScott.rowTail_type
#print axioms BooleanScott.chart_tail_spec
#print axioms BooleanScott.ChartTailSpec.core_type
#print axioms BooleanScott.retained_equiv
#print axioms BooleanScott.ChartTailSpec.core_matches
#print axioms BooleanScott.ChartTailSpec.remainder
#print axioms BooleanScott.row_absorbs_tag
#print axioms BooleanScott.ChartTailSpec.core_absorbs_pure
#print axioms BooleanScott.rooted_chart_comparison
#print axioms BooleanScott.vertex_chart_scott
#print axioms BooleanScott.chart_isolation
#print axioms BooleanScott.negativeResolution_of_branch_realization
#print axioms BooleanScott.vertex_row_exchange
#print axioms BooleanScott.row_prefix
#print axioms BooleanScott.GuardData.reserve_prefix
#print axioms BooleanScott.GuardData.allocate_block
#print axioms BooleanScott.GuardData.convergent_blocks
#print axioms BooleanScott.block_sum_absorption
#print axioms BooleanScott.ray_absorption
#print axioms BooleanScott.guarded_branch_implies_absorption
#print axioms BooleanScott.guarded_absorption_iff_branch
#print axioms BooleanScott.negativeResolution
#print axioms BooleanScott.booleanLawSentence_models
#print axioms BooleanScott.rankAtMost_of_operationRank
#print axioms BooleanScott.trivial_rankAtMost
#print axioms BooleanScott.pure_boolean_counterexample

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, info) in env.constants do
    if info.isTheorem || info.isAxiom then
      if let some idx := env.getModuleIdxFor? name then
        if (`BooleanScott).isPrefixOf env.header.moduleNames[idx.toNat]! then
          let bad := (← collectAxioms name).filter fun ax => !allowed.contains ax
          unless bad.isEmpty do throwError "{name} depends on unexpected axioms {bad}"
          checked := checked + 1
  unless checked > 0 do throwError "No project declarations were audited"
  logInfo m!"Axiom audit passed for {checked} imported project theorem and axiom declarations."
