import CFG.Basic.Model
import CFG.Basic.Fiber
import CFG.Analysis.NormalizedWeights
import CFG.LinearAlgebra.RestrictedRank
import CFG.LinearAlgebra.RightInverseCertificate
import CFG.LinearAlgebra.AffineProjection
import CFG.LinearAlgebra.DiscreteSchur
import CFG.LinearAlgebra.DiscreteSchurProperties
import CFG.LinearAlgebra.SurjectivePseudoinverse
import CFG.LinearAlgebra.WeightedFlattening
import CFG.LinearAlgebra.FrobeniusCertificate
import CFG.Calculus.ObservedDerivative
import CFG.Calculus.LocalFiberChart
import CFG.Calculus.RankProjection
import CFG.Calculus.FiniteFiberAtlas
import CFG.Calculus.FiniteImageFiberAtlas
import CFG.Calculus.QuantitativeConstants
import CFG.Calculus.UniformRadius
import CFG.Calculus.InverseFamily
import CFG.Calculus.PseudoinverseDerivative
import CFG.Covering.FiniteCover
import CFG.Covering.BoxGrid
import CFG.Covering.FiniteDimensionalBall
import CFG.Covering.ImageFiberAtlas
import CFG.Covering.LinearTube
import CFG.Covering.DiagonalTubeCover
import CFG.Covering.CompactFiber
import CFG.Probability.ConditionalSupport
import CFG.Probability.FiniteMask
import CFG.Transport.TotalVariation
import CFG.Smoothing.KernelTranslation
import CFG.Smoothing.KernelTranslationFiniteDim
import CFG.Statistics.NormalizedEnergyScore
import CFG.Statistics.VUStatistic
import CFG.Statistics.MMSEAlgebra
import CFG.Statistics.ConditionalExpectationRisk
import CFG.Statistics.RankInterval
import CFG.Statistics.ExchangeableRank
import CFG.Statistics.ProductNoTies
import CFG.Statistics.IIDNoTies
import CFG.Statistics.IIDExchangeable
import CFG.External.EntropyScale
import CFG.Topology.CompactEmbedding
import CFG.Examples.ScopeCounterexamples
import CFG.Examples.RightInverseToy
import CFG.Audit.AxiomAudit

/-!
# Conditional Fiber Geometry

The production root imports only modules whose declarations compile without
placeholders. Planned statements live under `specs/`, not in this import tree.
-/
