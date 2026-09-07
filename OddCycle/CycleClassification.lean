import OddCycle.OrientationQuotient
import OddCycle.CircularRunDynamics
import OddCycle.ExceptionalCycleArithmetic
import OddCycle.CircularWords
import OddCycle.CycleRunStates
import OddCycle.ShortOrientation
import OddCycle.CompletionFrontier
import OddCycle.CycleFrontier
import OddCycle.CyclePathRealization
import OddCycle.CyclePathMoves
import OddCycle.CircularRunEncoding
import OddCycle.CycleDirectedPaths
import OddCycle.CycleArcBlocks
import OddCycle.CircularBitDynamics
import OddCycle.FiniteGraphSymmetry
import OddCycle.BinaryCycleGraph
import OddCycle.OrientationRealization
import OddCycle.CircularBlockMoves
import OddCycle.EdgeBitFlips
import OddCycle.CycleLocalMoves
import OddCycle.OperationalCycleClassification
import OddCycle.ExceptionalCycleClass
import OddCycle.ExceptionalCycleCommunication
import OddCycle.ExceptionalCycleCount
import OddCycle.TerminalRecurrence
import OddCycle.CycleRecurrenceClassification
import OddCycle.OINormalization

import OddCycle.ClassClassification
import OddCycle.CompletionKernel
import OddCycle.CycleSharpness
import OddCycle.NineJobCycle
import OddCycle.CycleContinuousTime
import OddCycle.LinearCycleClassifier

/-!
The cycle classification for the original queue events: recurrent classes,
exceptional closure, communication and orientation count, positive-position
completion kernels and absorption, normalized OI laws on short classes, and
the sharp universal canonical-product-form boundary. The symmetric residual
is proved for all larger exceptional cycles, with C9/w=2 as an explicit instance.
The continuous-time path construction proves nonexplosion and measure-one
recurrence/absorption, and an executable classifier has a linear word-RAM cost bound.
See CYCLE_CLASSIFICATION.md for declarations and probability conventions.
-/
