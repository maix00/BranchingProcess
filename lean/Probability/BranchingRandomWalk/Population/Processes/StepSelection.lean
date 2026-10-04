/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Processes.StepSelection.Basic
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.Concurrent
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.Filter
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.FirstN
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.PreserveFirst
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.RootIndexed
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.Scheduled
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule

/-!
# Populations selected from branching steps

Generic causal finite populations obtained from a finite selection rule at
each branching step.
-/
