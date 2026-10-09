#!/usr/bin/env python3
"""Compile tracked and non-ignored untracked Lean tests under BranchingProcessTest."""

import argparse
from pathlib import Path
import re
import subprocess
import sys
import tempfile


AXIOM_EXPECTATIONS = {
    Path("BranchingProcessTest/Probability/Distributions/Stable/Gaussian.lean"): (
        "ProbabilityTheory.IsStrictlyAlphaStable.exists_gaussianReal_zero",
    ),
    Path("BranchingProcessTest/DomainOfAttraction/NormalAttraction.lean"): (
        "ProbabilityTheory.IsInDomainOfAttractionAlong.gaussian_defect_data",
        "ProbabilityTheory.isStableNorming_two_of_integrable_sq",
        "ProbabilityTheory.IsInDomainOfAttractionAlong.tendsto_symmetrizedClosedAbsTail_div_normDefect_atTop_of_gaussian",
        "ProbabilityTheory.IsInDomainOfAttractionAlong.tendsto_closedAbsTail_div_normDefect_atTop_of_gaussian",
    ),
    Path("BranchingProcessTest/Normal/RandomWalkPathLimit.lean"): (
        "ProbabilityTheory.Process.Path.Cadlag.pathMap_ae_eval_eq",
        "ProbabilityTheory.IsBrownianReal.isStableClockProcessLaw_cadlagunitIntervalProcessPathLaw",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Normal.tendsto_normalizedStepPathLaw_of_gaussian",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Normal.tendsto_normalizedStepPathLaw_of_gaussian_of_brownian",
    ),
    Path("BranchingProcessTest/Normal/RandomWalkBrownianLimit.lean"): (
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.isInDomainOfAttractionAlong_gaussianReal_zero_one",
        "ProbabilityTheory.Process.Path.Cadlag.aemeasurable_pathMap",
        "ProbabilityTheory.IsBrownianReal.isStableClockProcessLaw_cadlagunitIntervalProcessPathLaw",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Normal.tendsto_normalizedStepPathLaw_of_gaussian_of_brownian",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Normal.tendsto_normalizedStepCadlagPathIcc_of_centeredUnitSecondMoment_of_brownian",
    ),
    Path("BranchingProcessTest/Mogulskii/LinearTubeAxioms.lean"): (
        "ProbabilityTheory.IsStableClockProcessLaw.measure_linearPathBall_pos",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.exists_cyclicPartialSum_mem_Icc_of_linearTube",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.exists_cyclicPartialSum_mem_Icc_of_negativeLinearTube",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.measure_le_card_smul_of_finiteRotationCover",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.TendstoInDistribution.measure_openEvent_le_liminf",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.eventually_measure_normalizedStep_linearBall_pos",
        "ProbabilityTheory.iidSequenceLaw_map_finPrefix",
        "ProbabilityTheory.measure_pi_preimage_eq_of_reindex",
        "ProbabilityTheory.measure_pi_event_le_card_smul_of_reindexCover",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.cyclicPartialSum_removeLinearDrift",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.offsetCorridorPath_removeLinearDrift_iff_moving",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteNormalizedStepPath_apply_grid",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.iidSequenceLaw_measure_linearPathBall_eq_pi",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteLinearBall_subset_cyclicOffsetCover_lowerEdge",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.measure_pi_offsetCorridor_ge_div_of_linearTube",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.cyclicCoordinateReindex_isCyclicPartialSumReindex",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteLinearBall_subset_cyclicOffsetCover_lowerEdge_modular",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.measure_pi_offsetCorridor_ge_div_of_linearTube_modular",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.exists_offsetCorridorPath_of_linearTube_allOffsets",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.eventually_measure_normalizedStep_linearBall_pos_on_Icc_of_centeredSecondMoment",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteDriftRemovedOffsetCorridorEvent_iff_finiteMovingEntranceEvent",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.measure_pi_finiteMovingEntranceEvent_ge_div_of_uniformLinearBall",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.exists_eventually_measure_pi_finiteMovingEntranceEvent_ge_div_of_centeredSecondMoment",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.exists_eventually_iidSequenceLaw_finiteMovingEntranceEvent_ge_div_of_centeredSecondMoment",
    ),
    Path("BranchingProcessTest/Mogulskii/EntranceErrorBudget.lean"): (
        "ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.exists_eventually_iidSequenceLaw_finiteMovingEntranceEvent_ge_exp_of_centeredSecondMoment",
    ),
    Path("BranchingProcessTest/Branching/RestartSiblingTrial.lean"): (
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.sigma_firstGrowth_secondReserve_factorization",
        "ProbabilityTheory.BranchingRandomWalk.selectedPopulationFirstSplitSubtrees_measurable",
        "ProbabilityTheory.BranchingRandomWalk.selectedPopulationFirstSplitSubtrees_map_eq_product",
        "ProbabilityTheory.BranchingRandomWalk.recursiveReserveFailure_measurable",
        "ProbabilityTheory.BranchingRandomWalk.measure_recursiveReserveFailure_succ",
        "ProbabilityTheory.BranchingRandomWalk.measure_recursiveReserveFailure_eq_pow",
        "ProbabilityTheory.BranchingRandomWalk.BasicBranchingAssumptions.rawSplitEvent_measure_pos",
        "ProbabilityTheory.BranchingRandomWalk.exists_nat_cutoff_positive_boundedSelectedSplit",
        "ProbabilityTheory.BranchingRandomWalk.selectedPopulationSplitCompletion_ae_finite_of_nonempty_and_split_pos",
        "concrete_reserve_split_completion_ae_finite",
    ),
    Path("BranchingProcessTest/Branching/RestartCausalReserveCoupling.lean"): (
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartSource_finiteSlices",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartSource_card_le",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineCandidate_root_at_split",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartCoupledInjection_ae",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartCoupledPopulation_card_ge_of_candidate_success_ae",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineCandidate_subset_restartSource_at_endpoint",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartCoupled_position_witness_ae",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartCoupledCandidate_position_witness_ae",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineCandidateSuccessEvent_measurable",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineFirstSuccessfulCandidateCompletion_isStoppingTime",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartCoupledPopulation_card_ge_of_candidateSuccessEvent_ae",
        "ProbabilityTheory.BranchingRandomWalk.measurable_particleRankVectorAtStoppingTime",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartEndpointTime_isStoppingTime",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartEndpointRankVector_measurable",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartEndpointFreshRoots_measurable",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartEndpointFreshRoots_depth",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartEndpointFreshRoots_injective",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartEndpointFreshRoots_eq_target_ae",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartEndpointFreshField_factorization_on_finite",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartEndpointTargetFreshField_factorization_on_finite",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartEndpointPositionFreshField_jointLaw_on_finite",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartEndpointFixedHorizonObservable_law_on_finite",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartEndpointFixedHorizonPopulation_law_on_finite",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartEndpointPopulation_law_on_finite",
    ),
    Path("BranchingProcessTest/Branching/RestartSpineSplits.lean"): (
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineSplitCount_eq_sum_indicators",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineSplitCount_measurable",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineSplitCompletion_isStoppingTime",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpinePath_decompose_at_split_field",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineMark_decompose_at_split_field",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineAlive_decompose_at_split_field",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineCandidate_root_at_recursive_split",
    ),
    Path("BranchingProcessTest/Branching/RestartGoodSplitBoundedEdges.lean"): (
        "ProbabilityTheory.BranchingRandomWalk.reserveSelectionBelowPotential_split_iff_boundedSecond",
        "ProbabilityTheory.BranchingRandomWalk.reserveSelectionBelowPotential_split_edgePotentials_le_of_ordered",
        "ProbabilityTheory.BranchingRandomWalk.reserveSelectionBelowPotential_split_edgePotentials_le_sorted_ae",
    ),
    Path("BranchingProcessTest/Branching/RestartLineagePositivePart.lean"): (
        "ProbabilityTheory.BranchingRandomWalk.reserveSpineSlot_potential_le_cutoff_add_firstChildPositive",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpinePath_potential_eq_sum_edges",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpinePath_positivePart_le_cutoff_add_firstChildSum",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartSourceSlice_contains_live_spine",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartSourceMinPosition_le_live_spine",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartSourceMinPosition_positivePart_le",
    ),
    Path("BranchingProcessTest/Branching/RestartLineageSampledMark.lean"): (
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineFutureRoots_countable",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineFutureRoots_fiber_measurable",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineFutureRoots_depth",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineFutureRoots_injective",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineStep_measurable",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineStep_law",
        "ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineStep_independent",
        "ProbabilityTheory.BranchingRandomWalk.integral_selectedReserveSpineStep_observable",
        "ProbabilityTheory.BranchingRandomWalk.integral_selectedReserveSpineStep_firstRSelectedSlotPositivePotential",
    ),
    Path("BranchingProcessTest/Probability/BranchingRandomWalk/GeometricTrialFirstMomentAxioms.lean"): (
        "ProbabilityTheory.BranchingRandomWalk.iidGeometricFailurePositiveReward_integral",
        "ProbabilityTheory.BranchingRandomWalk.iidGeometricSplitCycle_positiveReward_le",
        "ProbabilityTheory.BranchingRandomWalk.iidGeometricFailureExponentialTransform",
    ),
    Path("BranchingProcessTest/Probability/BranchingRandomWalk/LowerTailExpectationAxioms.lean"): (
        "ProbabilityTheory.BranchingRandomWalk.neg_exp_neg_le_self",
        "ProbabilityTheory.BranchingRandomWalk.integral_ge_of_lower_bound_off_event_exp_neg",
        "ProbabilityTheory.BranchingRandomWalk.target_le_liminf_integral_div_log_of_polynomial_lower_tail",
    ),
    Path("BranchingProcessTest/Probability/BranchingRandomWalk/LeftTailAtAOne.lean"): (
        "ProbabilityTheory.BranchingRandomWalk.Analytic.measure_hasNoLargeDropEndpointBelow_le_exp_mul_spineProbability",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.measure_hasEndpointBelow_le_exp",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.measure_hasEndpointBelowByHorizon_le_sum_exp",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.eventually_horizontalTubeProbability_le_pow_fixedCover_uniformOffset",
    ),
    Path("BranchingProcessTest/Probability/BranchingRandomWalk/DrawdownSlicing.lean"): (
        "ProbabilityTheory.BranchingRandomWalk.Analytic.additivePath_le_threshold_add_delta_of_noLargeDrop",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.neg_delta_le_additivePath_of_noLargeDrop",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.iidSequenceLaw_measure_spatialBinPatternEvent_eq_pow",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.exists_spatialBinPatternEvent_of_noLargeDrop",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.card_monotoneSpatialBinPattern_le",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.measurableSet_monotoneSpatialBinPatternUnionEvent",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.iidSequenceLaw_measure_monotoneSpatialBinPatternUnionEvent_le",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.noLargeDropEndpointBelowEvent_subset_monotoneSpatialBinPatternUnionEvent",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.iidSequenceLaw_measure_monotoneSpatialBinPatternUnionEvent_le_exp",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_exp",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.eventually_integerDiffusiveBlockOscillationProbability_le_exp",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.eventually_finitePatternEntropyCondition_of_rate_gap",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.eventually_iidSequenceLaw_measure_monotoneSpatialBinPatternUnionEvent_le_exp_of_rate_gap",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.eventually_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_exp_of_rate_gap",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.eventually_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_ah_exp",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.exists_ah_diffusive_parameters",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.exists_uniform_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_ah_exp",
    ),
    Path("BranchingProcessTest/Probability/BranchingRandomWalk/DrawdownNormalization.lean"): (
        "ProbabilityTheory.BranchingRandomWalk.Analytic.measurableSet_noLargeDropEndpointBelowEvent",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.noLargeDropEndpointBelowEvent_preimage_div",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_eq_map_div",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.eventually_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_ah_exp_of_centeredSecondMoment",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.exists_uniform_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_ah_exp_of_centeredSecondMoment",
    ),
    Path("BranchingProcessTest/Probability/BranchingRandomWalk/SelectedPopulationDrawdown.lean"): (
        "ProbabilityTheory.BranchingRandomWalk.Analytic.firstNSelectedPopulation_measurable",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.measurableSet_firstNSelectedNoLargeDropEndpointBelow",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.firstNSelectedPopulation_depth",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.firstNSelectedPopulation_surviveAlong",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.firstNSelectedNoLargeDropEndpointBelow_subset_roots",
        "ProbabilityTheory.BranchingRandomWalk.Analytic.measure_firstNSelectedNoLargeDropEndpointBelow_le",
    ),
    Path("BranchingProcessTest/SmallDeviation/Mogulskii/Alpha2Target.lean"): (
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.centralCoreTargetMass_lower",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.ofReal_centralCoreTarget_le_rademacherCoreReturnProbability",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.ofReal_centralCoreTarget_le_rademacherTubeEndpointProbability",
    ),
    Path("BranchingProcessTest/SmallDeviation/Mogulskii/Alpha2EndpointBands.lean"): (
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.centralEndpointBandTargetMass_lower",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.eventually_lowerBound_le_centralEndpointBandTargetMass_of_diffusiveRatio",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.eventually_forall_sevenCentralEndpointWindowTargetMass_lower",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.ofReal_centralEndpointWindowTargetMassSum_le_endpointWindowBlockEvent",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.eventually_forall_sevenRademacherEndpointWindowBlockEvent_ge_of_diffusiveRatio",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.eventually_forall_sevenRademacherNormalizedEndpointWindowProbability_ge_of_diffusiveRatio",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.eventually_forall_integer_sevenRademacherNormalizedEndpointWindowProbability_ge_of_diffusiveRatio",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.eventually_forall_sevenCenteredUnitVarianceEndpointWindowProbability_ge_of_spectralBands",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.iidSequenceLaw_map_div_endpointWindowBlockEvent_eq_normalizedAlong",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.one_div_constant_mul_log_toReal_le_liminf_scaledLog_horizontalTubeProbability_of_endpointWindowBlocks",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.one_div_constant_mul_log_toReal_le_liminf_scaledLog_horizontalTubeProbability_of_spectralEndpointWindows",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.neg_half_pi_sq_le_liminf_scaledLog_horizontalTubeProbability_of_floorEndpointWindows",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.tendsto_scaledLog_horizontalTubeProbability_of_centeredUnitSecondMoment",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.returnKernel_apply_univ_lower_of_endpointWindowEvents",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.horizontalTubeProbability_ge_pow_endpointWindows",
    ),
    Path("BranchingProcessTest/Mogulskii/Stable/Discrete/PathClassRegimes.lean"): (
        "ProbabilityTheory.cdf_gaussianReal_zero_lt_one",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_index_two",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_index_two_of_brownian",
    ),
    Path("BranchingProcessTest/Mogulskii/SourceAlignment.lean"): (
        "MeasureTheory.CadlagPath.measurable_terminalLeftPath",
        "ProbabilityTheory.RandomWalk.measurable_sourceNormalizedStepCadlagPathIcc",
        "ProbabilityTheory.RandomWalk.sourceNormalizedStepCadlagPathIcc_apply_top",
        "ProbabilityTheory.RandomWalk.sourceNormalizedStepCadlagPathIcc_range_eq_scaledDisplacement",
        "ProbabilityTheory.RandomWalk.sourceNormalizedStepCadlagPathIcc_mem_rangeInOpenInterval_iff",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.tendsto_scaledLog_sourceNormalizedStepCorridor_eq_energyRate",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.sourceNormalizedStepCorridor_admissibleStepCorridor_rate",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_sourceDiscretestepCorridorRates",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_sourceStableInputs",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_source_index_lt_one",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_source_index_one",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_source_index_gt_one",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_source_index_two",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_sourceDiscretestepCorridorRates",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_sourceStableInputs",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.canonicalMogulskiiScale",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_source_index_two_of_brownian_explicit",
        "ProbabilityTheory.IsStableLevyProcess.unitIntervalPathLaw",
        "ProbabilityTheory.IsStableLevyProcess.isStableClockProcessLaw_unitIntervalPathLaw",
        "MeasureTheory.Measure.innerMeasure_mono",
        "MeasureTheory.Measure.measure_le_innerMeasure_of_nullMeasurableSet_subset",
        "ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability.tendsto_inner_outer_log_probability_ratio_of_FiniteCorridorUnionApproximation",
        "ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability.exists_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation",
        "ProbabilityTheory.HasStableProcessEscapeRate.approximableSet_innerOuterRate",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_discretestepCorridorRates",
        "ProbabilityTheory.HasStableProcessEscapeRate.eq_neg_pi_sq_div_eight",
        "ProbabilityTheory.HasStableProcessEscapeRate.fullWidthCoefficient_eq_neg_pi_sq_div_two",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.exists_brownian_escapeRate_eq_neg_pi_sq_div_eight",
    ),
    Path("BranchingProcessTest/Analysis/SlowDiagonal.lean"): (
        "Filter.exists_tendsto_slowDiagonal",
        "Asymptotics.exists_tendsto_slowDiagonal_mul_tendsto_zero",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.exists_slowDiagonal_within_stableScale",
    ),
    Path("BranchingProcessTest/Analysis/RegularVariationSlowScale.lean"): (
        "Asymptotics.IsRegularlyVaryingAtTop.exists_tendsto_slowScale",
        "Asymptotics.IsRegularlyVaryingAtTop.exists_tendsto_slowScale_of_eventually",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsStableMogulskiiScale.exists_tendsto_slowStableScaleTime_multiplier",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsStableMogulskiiScale.exists_tendsto_slowStableScaleTime_multiplier_of_eventually",
    ),
    Path("BranchingProcessTest/Order/DyadicGrid.lean"): (
        "DyadicGrid.isRefinement_succ",
        "DyadicGrid.point_lift",
        "DyadicGrid.countable_unitPoints",
        "DyadicGrid.dense_unitPoints",
    ),
    Path("BranchingProcessTest/RandomWalk/StoppingTimeBlockExcursion.lean"): (
        "ProbabilityTheory.RandomWalk.measure_stoppingTimeCell_inter_blockPrefixExceedance_eq_mul",
        "ProbabilityTheory.RandomWalk.measure_blockPrefixExceedanceAfter_le",
        "ProbabilityTheory.iidSequenceLaw_measure_stoppingTimeCell_inter_blockEvent_eq_mul",
        "ProbabilityTheory.iidSequenceLaw_measure_boundedStoppingTime_iidBlockEventAfter_eq_mul",
        "ProbabilityTheory.RandomWalk.firstPrefixExceedanceTime_isStoppingTime",
        "ProbabilityTheory.RandomWalk.measure_inter_boundedStoppingTime_blockPrefixExceedanceAfter_eq_mul",
        "ProbabilityTheory.RandomWalk.measure_firstPrefixExceedance_and_postCrossingBlockPrefixExceedance_eq_mul",
    ),
    Path("BranchingProcessTest/Probability/Sequence/IID/StoppingTime.lean"): (
        "ProbabilityTheory.iidSequenceLaw_measure_stoppingTimeCell_inter_blockEvent_eq_mul",
        "ProbabilityTheory.iidSequenceLaw_measure_boundedStoppingTime_iidBlockEventAfter_eq_mul",
        "ProbabilityTheory.iidSequenceLaw_measure_iidBlockEventAfter_le",
    ),
    Path("BranchingProcessTest/Probability/Sequence/IID/Filtration.lean"): (
        "ProbabilityTheory.iIndepFun.indep_coordinatePrefixFiltration_of_le",
    ),
    Path("BranchingProcessTest/Probability/Distributions/Moments/TruncatedRegularVariation.lean"): (
        "ProbabilityTheory.tendsto_rescaledSecondTailRatio_of_slowVariation",
        "ProbabilityTheory.tendsto_secondTailRatio_of_slowlyVarying_truncatedSecondMoment",
    ),
    Path("BranchingProcessTest/RandomWalk/AdjacentBlockExcursions.lean"): (
        "ProbabilityTheory.RandomWalk.measure_inter_adjacentBlockPrefixExceedance_eq_mul",
        "ProbabilityTheory.RandomWalk.measure_inter_adjacentBlockPrefixExceedance_eq_mul_of_lengths",
        "ProbabilityTheory.RandomWalk.measure_blockPrefixExceedance_translate_eq",
        "ProbabilityTheory.RandomWalk.measure_inter_adjacentBlockPrefixExceedance_le_mul_of_bounds",
        "ProbabilityTheory.RandomWalk.measure_inter_adjacentBlockPrefixExceedance_le_mul_of_bounds_of_lengths",
        "ProbabilityTheory.RandomWalk.measure_inter_adjacentBlockPrefixExceedance_le_sq_of_bound",
        "ProbabilityTheory.RandomWalk.measure_iUnion_adjacentBlockPrefixExceedance_le_of_commonBound",
        "ProbabilityTheory.RandomWalk.measure_iUnion_adjacentBlockPrefixExceedance_le_of_bounds",
        "ProbabilityTheory.RandomWalk.eventually_measure_iUnion_adjacentBlockPrefixExceedance_le_of_eventually_bounds",
        "ProbabilityTheory.RandomWalk.eventually_measure_inter_adjacentBlockPrefixExceedance_le_sq_of_oneBlockBound",
        "ProbabilityTheory.RandomWalk.measure_inter_adjacentBlockPrefixExceedance_le_sq_of_truncation_second_bounded",
    ),
    Path("BranchingProcessTest/RandomWalk/NormalizedBlockTail.lean"): (
        "ProbabilityTheory.RandomWalk.measure_blockPrefixExceedance_le_of_normalizedTruncationBounds",
    ),
    Path("BranchingProcessTest/RandomWalk/StepPathOscillationPartition.lean"): (
        "ProbabilityTheory.RandomWalk.normalizedStepCadlagPathIcc_oscillationBoundedOnStepPartition",
        "ProbabilityTheory.RandomWalk.exists_pos_uniform_admitsOscillationPartition_normalizedStepPath",
    ),
    Path("BranchingProcessTest/RandomWalk/FixedStepPathTightness.lean"): (
        "ProbabilityTheory.RandomWalk.isTightMeasureSet_singleton_normalizedStepPathLaw",
        "ProbabilityTheory.RandomWalk.isTightMeasureSet_normalizedStepPathLaw_image_of_finite",
    ),
    Path("BranchingProcessTest/SkorokhodEvaluation.lean"): (
        "Skorokhod.continuousAt_apply_of_continuousAt",
    ),
    Path("BranchingProcessTest/SkorokhodContinuityTimes.lean"): (
        "MeasureTheory.CadlagPath.measurableSet_rationalSideSeparation",
        "MeasureTheory.CadlagPath.rationalSideSeparation_iff_not_continuousAt",
        "MeasureTheory.CadlagPath.ae_ae_continuousAt_of_cadlag",
        "MeasureTheory.CadlagPath.dense_ae_continuityTimes_of_cadlag",
    ),
    Path("BranchingProcessTest/SkorokhodBorelGeneration.lean"): (
        "IsCadlag.countable_discontinuitySet",
        "Skorokhod.measurable_apply",
        "Skorokhod.continuousAt_integralAlongTimeChange",
        "Skorokhod.instSeparableSpaceCadlagPath",
        "Skorokhod.instIsCompletelyMetrizableSpaceCadlagPath",
        "Skorokhod.measurable_rationalEvaluation",
        "Skorokhod.measurableEmbedding_rationalEvaluation",
        "Skorokhod.borel_eq_comap_rationalEvaluation",
    ),
    Path("BranchingProcessTest/Skorokhod/FiniteDimensionalDense.lean"): (
        "MeasureTheory.CadlagPath.measurableEmbedding_denseEvaluation",
        "MeasureTheory.CadlagPath.measure_map_finiteEvaluation_eq_of_gridEvaluation_eq",
        "MeasureTheory.CadlagPath.measure_eq_of_map_finiteDenseEvaluation_eq",
        "ProbabilityTheory.CadlagPath.ProbabilityMeasure.tendsto_of_tight_of_finiteGridEvaluation",
    ),
    Path("BranchingProcessTest/Stable/RandomWalkFiniteDimensional.lean"): (
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.tendstoInDistribution_endpoints_of_stableClock",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.tendstoInDistribution_endpoints_of_stableNorming",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.tendstoInDistribution_normalizedStepPath_finiteGrid_floor_of_stableDomain",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.tendstoInDistribution_normalizedStepPath_finiteGrid_floor_of_zeroCenter",
    ),
    Path("BranchingProcessTest/Stable/RandomWalkPathLimit.lean"): (
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.tendsto_normalizedStepPathLaw_of_stableDomain_of_tight",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.tendsto_normalizedStepPathLaw_of_zeroCenter_stableDomain_of_tight",
    ),
    Path("BranchingProcessTest/Stable/RandomWalkPathLimitSource.lean"): (
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.tendsto_normalizedStepPathLaw_of_index_lt_one",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.tendsto_normalizedStepPathLaw_of_index_one",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.tendsto_normalizedStepPathLaw_of_index_gt_one",
    ),
    Path("BranchingProcessTest/SkorokhodLinearBreakpoint.lean"): (
        "Skorokhod.TimeChange.linearBreakpoint",
        "Skorokhod.TimeChange.linearBreakpoint_distortion_le_abs",
    ),
    Path("BranchingProcessTest/SkorokhodFinitePartitionTimeChange.lean"): (
        "Skorokhod.TimeChange.FinitePartition.ofMatchingPartitions",
        "Skorokhod.TimeChange.FinitePartition.ofMatchingPartitions_distortion_le",
        "Skorokhod.TimeChange.FinitePartition.act_ofMatchingPartitions_stepPath",
        "Skorokhod.TimeChange.FinitePartition.j1EDist_stepPath_le_ofMatchingPartitions",
    ),
    Path("BranchingProcessTest/SkorokhodOscillationPartition.lean"): (
        "Skorokhod.OscillationPartition.isCadlag_stepFunction",
        "IsCadlag.updateTop",
        "Skorokhod.OscillationPartition.ofFinitePoints",
        "Skorokhod.OscillationPartition.stepPath",
        "Skorokhod.OscillationPartition.stepApproximation",
        "Skorokhod.OscillationPartition.index_eq_of_cell",
        "Skorokhod.OscillationPartition.index_monotone",
        "Skorokhod.OscillationPartition.pullback",
        "Skorokhod.OscillationPartition.size_mul_mesh_le_one",
        "Skorokhod.OscillationPartition.dist_stepApproximation_le",
        "Skorokhod.OscillationPartition.uniformEDist_stepApproximation_le",
        "Skorokhod.OscillationPartition.j1EDist_stepApproximation_le",
        "Skorokhod.OscillationBoundedOnPartition.pullback",
        "Skorokhod.isOpen_admitsOscillationPartition",
        "Skorokhod.measurableSet_admitsOscillationPartition",
    ),
    Path("BranchingProcessTest/SkorokhodOscillationPartitionExistence.lean"): (
        "Skorokhod.IsCadlag.exists_oscillation_partition",
        "Skorokhod.CadlagPath.exists_admits_oscillation_partition",
        "Skorokhod.uniformEDist_ne_top",
        "Skorokhod.j1EDist_ne_top",
        "Skorokhod.OscillationPartition.uniformEDist_stepApproximation_le",
        "Skorokhod.OscillationPartition.j1EDist_stepApproximation_le",
    ),
    Path("BranchingProcessTest/SkorokhodCompactness.lean"): (
        "Skorokhod.OscillationPartition.edist_stepPath_le",
        "Skorokhod.OscillationPartition.continuous_stepPath",
        "Skorokhod.OscillationPartition.isCompact_stepPath_image",
        "Skorokhod.zeroPath",
        "Skorokhod.j1EDist_eq_uniformEDist_zero",
        "Skorokhod.isBounded_pathRange_of_isCompact",
        "Skorokhod.exists_uniform_admitsOscillationPartition_of_isCompact",
    ),
    Path("BranchingProcessTest/SkorokhodPathTightness.lean"): (
        "Skorokhod.isClosed_rangeIn",
        "Skorokhod.measurableSet_admitsOscillationPartitionSequence",
        "MeasureTheory.isTightMeasureSet_of_compactRange_and_oscillationPartitions",
        "MeasureTheory.isTightMeasureSet_range_of_eventually_compactRange_and_oscillationPartitions",
    ),
    Path("BranchingProcessTest/MeasureTheory/SequenceTightness.lean"): (
        "MeasureTheory.isTightMeasureSet_image_Iio_of_singletons",
        "MeasureTheory.isTightMeasureSet_range_of_eventually_uniform_compact_mass_bound",
    ),
    Path("BranchingProcessTest/SkorokhodMovingStepPath.lean"): (
        "Skorokhod.IsSeparatedPartitionPoints.strictMono",
        "Skorokhod.isClosed_setOf_isSeparatedPartitionPoints",
        "Skorokhod.isCompact_setOf_isSeparatedPartitionPoints",
        "Skorokhod.j1EDist_stepPath_le_ofMatchingPartitions_value",
        "Skorokhod.isCompact_setOf_stepPathParameters",
        "Skorokhod.stepPathOfParameters",
        "Skorokhod.j1EDist_stepPathOfParameters_le",
        "Skorokhod.continuous_stepPathOfParameters",
        "Skorokhod.isCompact_stepPathOfParameters_image",
        "Skorokhod.OscillationPartition.stepApproximation_eq_ofPoints_stepPath",
        "Skorokhod.compactRangeMovingPartitionStepPathFamily",
        "Skorokhod.isCompact_compactRangeMovingPartitionStepPathFamily",
        "Skorokhod.OscillationPartition.stepApproximation_mem_compactRangeMovingPartitionStepPathFamily",
        "Skorokhod.totallyBounded_of_uniform_admitsOscillationPartition",
        "Skorokhod.isCompact_iff_isComplete_rangeBounded_uniformAdmitsOscillationPartition",
        "Skorokhod.isCompact_closure_iff_isComplete_closure_rangeBounded_uniformAdmitsOscillationPartition",
        "Skorokhod.j1EDist_forgetRange",
        "Skorokhod.isometry_forgetRange",
        "Skorokhod.exists_isCompact_superset_of_uniform_admitsOscillationPartition",
    ),
    Path("BranchingProcessTest/CadlagLocalOscillation.lean"): (
        "IsCadlag.exists_left_oscillation_radius",
        "IsCadlag.exists_right_oscillation_radius",
    ),
    Path("BranchingProcessTest/RandomWalk/FiniteDimensionalIndependentBlocks.lean"): (
        "ProbabilityTheory.RandomWalk.iIndepFun_variableConsecutiveBlockCoordinates",
        "ProbabilityTheory.RandomWalk.iIndepFun_variableConsecutiveBlockSums",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.FiniteDimensional.tendstoInDistribution_consecutiveBlockSums",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.FiniteDimensional.tendstoInDistribution_consecutiveBlockEndpoints",
    ),
    Path("BranchingProcessTest/RandomWalk/BlockEndpointComparison.lean"): (
        "MeasureTheory.measure_mul_le_card_mul_of_finite_cover",
        "ProbabilityTheory.RandomWalk.iidSequenceLaw_measure_inter_prefix_nextBlock",
        "ProbabilityTheory.RandomWalk.measurableSet_inOpenPartialSumCorridorEndsIn",
        "ProbabilityTheory.RandomWalk.iidSequenceLaw_measure_mul_le_card_mul_of_finite_block_cover",
        "Asymptotics.eventually_one_sub_le_log_ratio_of_mul_bound",
    ),
    Path("BranchingProcessTest/RandomWalk/TruncationMoments.lean"): (
        "ProbabilityTheory.RandomWalk.integrable_truncatedIncrement_pow",
        "ProbabilityTheory.RandomWalk.integrable_centeredTruncatedIncrement_pow_four",
        "ProbabilityTheory.RandomWalk.integral_partialSum_pow_four_centeredTruncated_le",
        "ProbabilityTheory.RandomWalk.maximal_ineq_pow_four_blockSum_centeredTruncated_bounded",
        "ProbabilityTheory.RandomWalk.measure_exists_block_exists_abs_ge_le_of_truncation_bounded",
    ),
    Path("BranchingProcessTest/RandomWalk/TruncationSecondMoment.lean"): (
        "ProbabilityTheory.RandomWalk.integral_truncatedIncrement_sq_eq_truncatedSecondMoment",
        "ProbabilityTheory.RandomWalk.maximal_ineq_sq_blockSum_centeredTruncated_bounded",
        "ProbabilityTheory.RandomWalk.measure_exists_block_exists_abs_ge_le_of_truncation_second_bounded",
        "ProbabilityTheory.RandomWalk.measure_exists_block_exists_abs_ge_le_of_shiftedTruncation_second_bounded",
    ),
    Path("BranchingProcessTest/Analysis/RegularVariationInverse.lean"): (
        "Asymptotics.IsRegularlyVaryingAtTop.tendstoUniformlyOn_ratio_of_eventuallyMonotone",
        "Asymptotics.IsRegularlyVaryingAtTop.tendsto_div_of_tendsto_value_ratio",
        "Asymptotics.IsRegularlyVaryingAtTop.tendsto_div_of_tendsto_squareQuotient_ratio",
        "ProbabilityTheory.truncatedSecondMoment_isRegularlyVarying_of_stableSlowVariation",
        "ProbabilityTheory.stableScaleTime_tendsto_atTop_of_stableSlowVariation",
        "ProbabilityTheory.IsStableNorming.tendsto_floorBlock_normalization_div_scale",
    ),
    Path("BranchingProcessTest/Mogulskii/Stable/Discrete/UpperEndpoint.lean"): (
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.eventually_horizontalTubeProbability_le_pow_stableBlock_endpointMass",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.horizontalTubeProbability_ge_pow_stableEndpointBands",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.horizontalTubeProbability_ge_pow_stableEndpointBands_of_quotientBlockCount",
    ),
    Path("BranchingProcessTest/Mogulskii/Stable/CorridorUpper.lean"): (
        "ProbabilityTheory.RandomWalk.limsup_horizontalTubeProbability_le_of_normalizedStepBlockPathLimit",
        "ProbabilityTheory.RandomWalk.exists_normalizedStepCadlagPathIcc_eq_scaledDisplacement",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.blockOscillationLTEvent_subset_normalizedStepBlockRangeOscillation",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.iidSequenceLaw_measure_blockOscillationLT_le_normalizedStepBlockPathLaw",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.limsup_normalizedStepBlockRangeOscillation_le_stableProcessTube",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.limsup_iidSequenceLaw_blockOscillationLT_le_stableProcessTube",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.eventually_openHorizontalTubeProbability_le_pow_of_blockPathLimit",
        "ProbabilityTheory.HasStableProcessEscapeRate.tendsto_inv_rpow_mul_log_stableProcessTube",
        "ProbabilityTheory.HasStableProcessEscapeRate.eventually_tubeProbability_lt_exp",
        "ProbabilityTheory.HasStableProcessEscapeRate.eventually_tube_lt_of_exp_rate",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.limsup_stableSmallDeviationRate_mul_log_openHorizontalTubeProbability_le_of_blockPathLimit",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.limsup_stableSmallDeviationRate_mul_log_openHorizontalTubeProbability_le_of_escapeRate",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.limsup_stableSmallDeviationRate_mul_log_openHorizontalTubeProbability_le",
        "Skorokhod.rangeInClosedInterval_subset_oscillationInOpenTube",
        "Skorokhod.rangeOscillationLe_subset_oscillationInOpenTube",
    ),
    Path("BranchingProcessTest/Mogulskii/Stable/CorridorLower.lean"): (
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.eventually_openHorizontalTubeProbability_ge_exp_of_stableEscapeRate",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.stableEscapeRate_liminf_lower",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.stableEscapeRate_eventually_positive_and_log_cobounded",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.tendsto_stableSmallDeviationRate_mul_log_openHorizontalTubeProbability_of_escapeRate",
    ),
    Path("BranchingProcessTest/Mogulskii/Discrete/Horizontal.lean"): (
        "ProbabilityTheory.RandomWalk.iidSequenceLaw_measure_forall_consecutiveBlockEvent",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.iidSequenceLaw_measure_forall_blockOscillationLT",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.openHorizontalTubeProbability_le_pow_blockOscillationLT_source",
    ),
    Path("BranchingProcessTest/Mogulskii/Stable/Discrete/UpperEndpointSource.lean"): (
        "ProbabilityTheory.IsStrictlyAlphaStable.measure_Icc_lt_one_of_lt_two",
        "ProbabilityTheory.IsStrictlyAlphaStable.measure_map_rpow_Icc_lt_one_of_lt_two",
        "ProbabilityTheory.IsStrictlyAlphaStable.measure_Ioi_pos_indexTwo",
        "ProbabilityTheory.IsStrictlyAlphaStable.measure_Icc_lt_one_indexTwo",
        "ProbabilityTheory.IsStrictlyAlphaStable.measure_map_rpow_Icc_lt_one_indexTwo",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.eventually_horizontalTubeProbability_le_pow_of_strictStableDomain",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.eventually_horizontalTubeProbability_le_pow_of_strictStableDomain_indexTwo",
    ),
    Path("BranchingProcessTest/Mogulskii/Stable/Discrete/EndpointBandTransfer.lean"): (
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.iidSequenceLaw_normalizedEndpointBand_eq",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.eventually_forall_normalizedEndpointBandProbability_ge_of_pathLawLimit",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.eventually_horizontalTubeProbability_ge_pow_of_pathLawLimit",
    ),
    Path("BranchingProcessTest/Mogulskii/Stable/Discrete/SourceLower.lean"): (
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.eventually_horizontalTubeProbability_ge_pow_of_stableDomain",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.eventually_horizontalTubeProbability_ge_pow_of_index_lt_one",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.eventually_horizontalTubeProbability_ge_pow_of_index_one",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.eventually_horizontalTubeProbability_ge_pow_of_index_gt_one",
    ),
    Path("BranchingProcessTest/Analysis/RegularVariationIntegral.lean"): (
        "Asymptotics.IsRegularlyVaryingAtTop.tendsto_intervalIntegral_div_mul_of_monotone",
        "Asymptotics.IsRegularlyVaryingAtTop.tendsto_intervalIntegral_div_mul_of_antitone",
        "Asymptotics.IsRegularlyVaryingAtTop.tendsto_integral_Ioi_div_mul_of_antitone",
    ),
    Path("BranchingProcessTest/Branching/RestartLineage.lean"): (
        "ProbabilityTheory.BranchingRandomWalk.firstSelectedSlot_measurable",
        "ProbabilityTheory.BranchingRandomWalk.firstSelectedSlot_mem",
        "ProbabilityTheory.BranchingRandomWalk.splitBy_measurable",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.fixedSubtree_measurable_at",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.firstChildRootAt_root",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.firstChildRootAt_depth",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.sigma_isStoppingTime",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.all_sigma_isStoppingTime",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.first_success_within_isStoppingTime",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.successfulWithin_measurable",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.failureWithin_measurable",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.integral_selectedSubtree_abs_on_candidateFailure",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.integral_selectedSubtree_abs_on_candidateFailure_le",
        "ProbabilityTheory.BranchingRandomWalk.growthTrialSuccess_measurable",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.growthTrialSuccessAt_selectedRoot_measurable",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.firstChildRootAt_fiber_measurable",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.firstChildRootAt_selected",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.firstGrowthCandidateTest_measurable",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.firstGrowthCandidate_observable",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.firstGrowthCompletion_isStoppingTime",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.firstGrowthCompletion_eq_tau_add_trialLength",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.firstGrowthCandidatesWithin_measurable",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.integral_selectedSubtree_abs_on_firstGrowthFailure_le",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.sigma_eq_tau_add_one",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.integral_reserveRoot_abs_on_candidateFailure_le",
        "ProbabilityTheory.BranchingRandomWalk.lookahead_time_not_stopping",
        "ProbabilityTheory.BranchingRandomWalk.lookahead_completion_isStoppingTime",
        "ProbabilityTheory.BranchingRandomWalk.delayed_lookahead_completion_not_stopping",
        "ProbabilityTheory.BranchingRandomWalk.selectedPopulationSplitCompletion_eq_raw_add_one",
        "ProbabilityTheory.BranchingRandomWalk.selectedPopulationSplitCompletion_isStoppingTime",
        "ProbabilityTheory.BranchingRandomWalk.selectedPopulationRawSplitTime_not_stopping_of_probability",
        "ProbabilityTheory.BranchingRandomWalk.selectedPopulation_firstSplit_parent_card_eq_one",
        "ProbabilityTheory.BranchingRandomWalk.selectedPopulation_firstSplit_has_sibling_pair",
        "ProbabilityTheory.BranchingRandomWalk.secondSelectedSlot_measurable",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.secondChildRootAt_selected",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.secondChildRootAt_sigma_selected",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.secondChildRootAt_ne_firstChildRootAt",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.secondChildRootAt_sigma_ne_firstChildRootAt",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.secondChildRootAt_sigma_fiber_measurable",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.sigma_secondChildSubtree_splitCompletion_isStoppingTime",
        "ProbabilityTheory.BranchingRandomWalk.selectedPopulationFirstSplitRoots_fiber_measurable",
        "ProbabilityTheory.BranchingRandomWalk.selectedPopulationFirstSplitRoots_depth",
        "ProbabilityTheory.BranchingRandomWalk.selectedPopulationFirstSplitRoots_injective_of_finite",
        "ProbabilityTheory.BranchingRandomWalk.selectedChildrenAtFirstSplit_measurable",
        "ProbabilityTheory.BranchingRandomWalk.stopped_selectedSubtreeStepFieldVector_event_factorization_on_finite",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.stopped_selectedSubtreeStepFieldVector_event_factorization_on_finite",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.sigmaSiblingRoots",
        "ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.sigma_sibling_subtree_vector_factorization_on_finite",
        "ProbabilityTheory.BranchingRandomWalk.selectedPopulation_firstSplit_subtree_vector_factorization",
    ),
    Path("BranchingProcessTest/Branching/RestartedCoupling.lean"): (
        "ProbabilityTheory.BranchingRandomWalk.Coupling.RootIndexed.rankInstalledField_law",
        "ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.rankInstalledField_totalizedSelectedPopulation_measurable_law",
        "ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.rankInstalledField_causalPopulation_measurable_law",
        "ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.causalPopulationCoupling",
        "ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.restartedRealPositionCoupling",
        "ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.restartedRealPositionCoupledInjection_ae",
        "ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.restartedRealPositionCoupledInjectionOnRoots_ae",
    ),
    Path("BranchingProcessTest/RandomWalk/NormalizedStepEndpoint.lean"): (
        "ProbabilityTheory.RandomWalk.measure_centeredSkorokhodCorridorEndsIn_le_liminf_strictTubeEndsIn_of_functionalLimit",
        "ProbabilityTheory.RandomWalk.limsup_weakTubeEndsIn_le_measure_centeredSkorokhodCorridorEndsIn_of_functionalLimit",
    ),
    Path("BranchingProcessTest/Stable/FixedTimeContinuity.lean"): (
        "ProbabilityTheory.IsStableLevyProcess.ae_leftLim_eq_eval",
    ),
    Path("BranchingProcessTest/Stable/NormingTail.lean"): (
        "ProbabilityTheory.IsStableNorming.tendsto_nat_mul_twoSidedTail_of_regularlyVarying",
        "ProbabilityTheory.IsStableNorming.tendsto_nat_mul_twoSidedTail_mul_of_regularlyVarying",
        "ProbabilityTheory.IsStableNorming.tendsto_nat_mul_truncatedSecondMoment_mul_div_sq",
        "ProbabilityTheory.IsStableNorming.tendstoUniformlyOn_nat_mul_twoSidedTail_mul_of_regularlyVarying",
    ),
    Path("BranchingProcessTest/Stable/RandomWalkBlockTail.lean"): (
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_measure_blockPrefixExceedance_le_of_stableNorming",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_measure_blockPrefixExceedance_le_of_stableNorming_unitMargins",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_measure_adjacentBlockPrefixExceedance_le_of_stableNorming",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_measure_adjacentVariableBlockPrefixExceedance_le_of_stableNorming",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_measure_iUnion_adjacentBlockPrefixExceedance_le_of_stableNorming",
    ),
    Path("BranchingProcessTest/Stable/RandomWalkStoppingTimeBlockTail.lean"): (
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_measure_blockPrefixExceedanceAfter_le_of_stableNorming",
    ),
    Path("BranchingProcessTest/Stable/TruncationBiasAboveOne.lean"): (
        "ProbabilityTheory.integrableOn_twoSidedTail_of_integrable_abs",
        "ProbabilityTheory.integral_indicator_abs_eq_radius_mul_tail_add_tailIntegral",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.IsStableNorming.tendsto_nat_mul_discardedAbsFirstMoment_div_normalization_of_regularlyVaryingTail",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_truncatedIncrementBias_le_of_stableNorming_of_index_gt_one",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_measure_blockPrefixExceedance_le_of_stableNorming_of_index_gt_one",
    ),
    Path("BranchingProcessTest/Stable/RandomWalkTruncationCentering.lean"): (
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.IsStableNorming.tendsto_nat_mul_cappedAbsFirstMoment_div_normalization_of_regularlyVaryingTail",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_truncatedIncrementBias_le_of_stableNorming_of_index_lt_one",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_measure_blockPrefixExceedance_le_of_stableNorming_of_index_lt_one",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.abs_truncatedIncrementMean_div_le_sineIntegral_add_truncatedMoment_tail",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.IsStableNorming.eventually_nat_mul_abs_truncatedIncrementMean_div_le_of_index_one",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_truncatedIncrementBias_le_of_stableNorming_of_index_one",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_measure_blockPrefixExceedance_le_of_stableNorming_of_index_one",
    ),
    Path("BranchingProcessTest/Stable/RandomWalkRange.lean"): (
        "ProbabilityTheory.RandomWalk.not_mem_rangeIn_closedInterval_subset_blockPrefixExceedance",
        "ProbabilityTheory.RandomWalk.normalizedStepCadlagPathIcc_mem_rangeIn_closedInterval_iff_partialSumBounds",
        "ProbabilityTheory.RandomWalk.measure_normalizedStepPathLaw_rangeIn_closedInterval_compl_le_of_blockPrefixExceedance",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_measure_blockPrefixExceedance_le_of_stableNorming",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_measure_normalizedStepPathLaw_rangeExit_le_of_stableNorming",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.exists_eventually_compactRange_bound_of_index_lt_one",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.exists_eventually_compactRange_bound_of_index_one",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.exists_eventually_compactRange_bound_of_index_gt_one",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.exists_eventually_compactRange_bound_of_index_lt_one_ennreal",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.exists_eventually_compactRange_bound_of_index_one_ennreal",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.exists_eventually_compactRange_bound_of_index_gt_one_ennreal",
    ),
    Path("BranchingProcessTest/Mogulskii/RelativeTerminalLeft.lean"): (
        "Skorokhod.terminalLeftPath_eq_self_of_mem_space",
        "Skorokhod.terminalLeftPath_idempotent",
        "ProbabilityTheory.IsStableClockProcessLaw.spatialScale",
        "ProbabilityTheory.HasStableProcessEscapeRate.spatialScale",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.existsUnique_inner_outer_log_probability_ratio_of_hasRelativeVanishingEnergyGapApproximation_of_sourceDiscretestepCorridorRates",
    ),
    Path("BranchingProcessTest/Mogulskii/SourceOnlyRates.lean"): (
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.exists_source_relative_pathClass_rates_of_rawSource",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.exists_source_continuousBoundary_inner_outer_rates_of_rawSource",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.exists_source_continuousBoundary_probability_rate_of_rawSource",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.exists_source_continuousBoundary_probability_rate_of_rawSource_of_iid",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.sourceIidRelativePathClassRate_of_rawSource",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourceIidRelativePathClassRate.probabilityRate",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.rawNormalSourceRateData_of_rawSource",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.RawNormalSourceRateData.relativePathClassRate",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.rawNormalSourceRateData_of_centered_unitVariance",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.sourceScaledInnerOuterLogRate_of_centered_unitVariance",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.HasSourceFiniteVarianceScaledRelativeRate.probabilityRate",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.rawNormalContinuousBoundaryRateData_of_centered_unitVariance",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.rawNormalContinuousBoundaryProbabilityRate_of_rawSource",
        "ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredUnitVariance_sourceRelativeContinuousBoundaryProbabilityRate",
        "ProbabilityTheory.RandomWalk.sourceNormalizedStepCadlagPathIcc_mem_relativeContinuousBoundaryCorridorSet_iff",
        "ProbabilityTheory.RandomWalk.measurableSet_sourceNormalizedStepCadlagPathIcc_preimage_relativeContinuousBoundaryCorridorSet",
    ),
    Path("BranchingProcessTest/Probability/RandomWalk/StableProcessExistence.lean"): (
        "ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.exists_stableLevyProcess_of_tightSource",
    ),
}

AXIOM_PRINT = re.compile(
    r"(?m)^[ \t]*#print[ \t]+axioms[ \t\r\n]+([A-Za-z0-9_'.]+)"
)


def working_tree_tests() -> list[Path]:
    result = subprocess.run(
        [
            "git",
            "ls-files",
            "--cached",
            "--others",
            "--exclude-standard",
            "-z",
            "--",
            "BranchingProcessTest",
        ],
        check=True,
        stdout=subprocess.PIPE,
    )
    return sorted(
        {
            Path(name.decode())
            for name in result.stdout.split(b"\0")
            if name.endswith(b".lean")
        }
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output-dir",
        type=Path,
        help="save combined stdout and stderr per test for later CI checks",
    )
    args = parser.parse_args()

    tests = working_tree_tests()
    if not tests:
        print("No BranchingProcessTest Lean files found in the working tree.", file=sys.stderr)
        return 1

    for index, test in enumerate(tests, start=1):
        print(f"[{index}/{len(tests)}] lake env lean {test}", flush=True)
        result = subprocess.run(
            ["lake", "env", "lean", str(test)],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        if args.output_dir is not None:
            log_path = args.output_dir / f"{test}.log"
            log_path.parent.mkdir(parents=True, exist_ok=True)
            log_path.write_text(result.stdout)
        if result.stdout:
            print(result.stdout, end="", flush=True)
        if result.returncode:
            print(f"Lean test failed: {test}", file=sys.stderr)
            return result.returncode
        # Explicit entries keep a reviewed inventory for the main theorem
        # chains. For every other test, audit every declaration whose
        # transitive axioms the source asks Lean to print. This prevents a new
        # `#print axioms` test from compiling without actually checking its
        # result.
        expected = AXIOM_EXPECTATIONS.get(test)
        if expected is None:
            expected = tuple(AXIOM_PRINT.findall(test.read_text()))
        if expected:
            if args.output_dir is not None:
                axiom_log = args.output_dir / f"{test}.log"
            else:
                temporary = tempfile.NamedTemporaryFile(
                    mode="w", encoding="utf-8", suffix=".log", delete=False
                )
                axiom_log = Path(temporary.name)
                temporary.close()
                axiom_log.write_text(result.stdout)
            try:
                checked = subprocess.run(
                    [
                        sys.executable,
                        "scripts/check-lean-axioms.py",
                        str(axiom_log),
                        "--expected",
                        *expected,
                    ],
                    text=True,
                )
            finally:
                if args.output_dir is None:
                    axiom_log.unlink(missing_ok=True)
            if checked.returncode:
                print(f"Axiom check failed: {test}", file=sys.stderr)
                return checked.returncode

    print(f"All {len(tests)} working-tree Lean tests compiled successfully.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
