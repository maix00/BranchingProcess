/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.Basic
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.Completion
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.Success
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.Law
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.Geometric
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.Roots
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.FreshField
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.FreshPool
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.Iteration
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.Coupling

/-!
# Split schedules for selected branching populations

Observable threshold schedules and their successful fixed-duration trials.
-/
