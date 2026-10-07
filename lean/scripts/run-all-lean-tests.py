#!/usr/bin/env python3
"""Compile every tracked Lean test under BranchingProcessTest."""

import argparse
from pathlib import Path
import subprocess
import sys
import tempfile


AXIOM_EXPECTATIONS = {
    Path("BranchingProcessTest/DomainOfAttraction/NormalAttraction.lean"): (
        "ProbabilityTheory.IsInDomainOfAttractionAlong.gaussian_defect_data",
        "ProbabilityTheory.isStableNorming_two_of_integrable_sq",
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
        "Skorokhod.measurableSet_rationalSideSeparation",
        "Skorokhod.rationalSideSeparation_iff_not_continuousAt",
        "Skorokhod.ae_ae_continuousAt_of_cadlag",
        "Skorokhod.dense_ae_continuityTimes_of_cadlag",
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
        "Skorokhod.measurableEmbedding_denseEvaluation",
        "Skorokhod.measure_map_finiteEvaluation_eq_of_gridEvaluation_eq",
        "Skorokhod.measure_eq_of_map_finiteDenseEvaluation_eq",
        "Skorokhod.ProbabilityMeasure.tendsto_of_tight_of_finiteGridEvaluation",
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
        "ProbabilityTheory.Process.Path.isTightMeasureSet_of_compactRange_and_oscillationPartitions",
        "ProbabilityTheory.Process.Path.isTightMeasureSet_range_of_eventually_compactRange_and_oscillationPartitions",
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
        "ProbabilityTheory.BranchingRandomWalk.selectedPopulationFirstSplitRoots_fiber_measurable",
        "ProbabilityTheory.BranchingRandomWalk.selectedPopulationFirstSplitRoots_depth",
        "ProbabilityTheory.BranchingRandomWalk.selectedPopulationFirstSplitRoots_injective_of_finite",
        "ProbabilityTheory.BranchingRandomWalk.selectedChildrenAtFirstSplit_measurable",
        "ProbabilityTheory.BranchingRandomWalk.stopped_selectedSubtreeStepFieldVector_event_factorization_on_finite",
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
}


def tracked_tests() -> list[Path]:
    result = subprocess.run(
        ["git", "ls-files", "-z", "--", "BranchingProcessTest"],
        check=True,
        stdout=subprocess.PIPE,
    )
    return sorted(
        Path(name.decode())
        for name in result.stdout.split(b"\0")
        if name.endswith(b".lean")
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output-dir",
        type=Path,
        help="save combined stdout and stderr per test for later CI checks",
    )
    args = parser.parse_args()

    tests = tracked_tests()
    if not tests:
        print("No tracked BranchingProcessTest Lean files found.", file=sys.stderr)
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
        expected = AXIOM_EXPECTATIONS.get(test)
        if expected is not None:
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

    print(f"All {len(tests)} tracked Lean tests compiled successfully.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
