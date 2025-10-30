import Carleson.Antichain.AntichainOperator
import Carleson.Antichain.AntichainTileCount
import Carleson.Antichain.Basic
import Carleson.Antichain.TileCorrelation
import Carleson.Calculations
import Carleson.Classical.Approximation
import Carleson.Classical.Basic
import Carleson.Classical.CarlesonHunt
import Carleson.Classical.CarlesonOnTheRealLine
import Carleson.Classical.CarlesonOperatorReal
import Carleson.Classical.ClassicalCarleson
import Carleson.Classical.ControlApproximationEffect
import Carleson.Classical.DirichletKernel
import Carleson.Classical.Helper
import Carleson.Classical.HilbertKernel
import Carleson.Classical.HilbertStrongType
import Carleson.Classical.SpectralProjectionBound
import Carleson.Classical.VanDerCorput
import Carleson.Defs
import Carleson.Discrete.Defs
import Carleson.Discrete.ExceptionalSet
import Carleson.Discrete.ForestComplement
import Carleson.Discrete.ForestUnion
import Carleson.Discrete.MainTheorem
import Carleson.Discrete.SumEstimates
import Carleson.DoublingMeasure
import Carleson.FinitaryCarleson
import Carleson.Forest
import Carleson.ForestOperator.AlmostOrthogonality
import Carleson.ForestOperator.Forests
import Carleson.ForestOperator.L2Estimate
import Carleson.ForestOperator.LargeSeparation
import Carleson.ForestOperator.PointwiseEstimate
import Carleson.ForestOperator.QuantativeEstimate
import Carleson.ForestOperator.RemainingTiles
import Carleson.GridStructure
import Carleson.HolderVanDerCorput
import Carleson.MetricCarleson.Basic
import Carleson.MetricCarleson.Linearized
import Carleson.MetricCarleson.Main
import Carleson.MetricCarleson.Truncation
import Carleson.MinLayerTiles
import Carleson.Operators
import Carleson.ProofData
import Carleson.Psi
import Carleson.TileExistence
import Carleson.TileStructure
import Carleson.ToMathlib.Analysis.Convex.SpecificFunctions.Basic
import Carleson.ToMathlib.Analysis.Convolution
import Carleson.ToMathlib.Analysis.Normed.Group.Basic
import Carleson.ToMathlib.Analysis.SpecialFunctions.Pow.Deriv
import Carleson.ToMathlib.Annulus
import Carleson.ToMathlib.BoundedCompactSupport
import Carleson.ToMathlib.BoundedFiniteSupport
import Carleson.ToMathlib.CoveredByBalls
import Carleson.ToMathlib.Data.ENNReal
import Carleson.ToMathlib.Data.NNReal
import Carleson.ToMathlib.Data.Real.ConjExponents
import Carleson.ToMathlib.ENorm
import Carleson.ToMathlib.HardyLittlewood
import Carleson.ToMathlib.Interval
import Carleson.ToMathlib.Lorentz
import Carleson.ToMathlib.MeasureTheory.Function.AEEqFun
import Carleson.ToMathlib.MeasureTheory.Function.L1Integrable
import Carleson.ToMathlib.MeasureTheory.Function.LocallyIntegrable
import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.Basic
import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Carleson.ToMathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Carleson.ToMathlib.MeasureTheory.Function.LpSpace.Indicator
import Carleson.ToMathlib.MeasureTheory.Function.SimpleFunc
import Carleson.ToMathlib.MeasureTheory.Integral.Average
import Carleson.ToMathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Carleson.ToMathlib.MeasureTheory.Integral.IntegrableOn
import Carleson.ToMathlib.MeasureTheory.Integral.Lebesgue
import Carleson.ToMathlib.MeasureTheory.Integral.MeanInequalities
import Carleson.ToMathlib.MeasureTheory.Integral.Periodic
import Carleson.ToMathlib.MeasureTheory.Measure.ENNReal
import Carleson.ToMathlib.MeasureTheory.Measure.Haar.Unique
import Carleson.ToMathlib.MeasureTheory.Measure.IsDoubling
import Carleson.ToMathlib.MeasureTheory.Measure.NNReal
import Carleson.ToMathlib.MeasureTheory.Measure.Prod
import Carleson.ToMathlib.MinLayer
import Carleson.ToMathlib.Misc
import Carleson.ToMathlib.Order.Chain
import Carleson.ToMathlib.Order.LiminfLimsup
import Carleson.ToMathlib.RealInterpolation.InterpolatedExponents
import Carleson.ToMathlib.RealInterpolation.LorentzInterpolation
import Carleson.ToMathlib.RealInterpolation.Main
import Carleson.ToMathlib.RealInterpolation.Minkowski
import Carleson.ToMathlib.RealInterpolation.Misc
import Carleson.ToMathlib.Topology.Instances.AddCircle.Defs
import Carleson.ToMathlib.Topology.Order.Basic
import Carleson.ToMathlib.WeakType
import Carleson.TwoSidedCarleson.Basic
import Carleson.TwoSidedCarleson.MainTheorem
import Carleson.TwoSidedCarleson.NontangentialOperator
import Carleson.TwoSidedCarleson.RestrictedWeakType
import Carleson.TwoSidedCarleson.WeakCalderonZygmund
import BlueprintGen

attribute [blueprint
  "real line ball"
  (statement := /-- For $x\in R$ and $R>0$, the ball $B(x,R)$ is the interval $(x-R,x+R)$ -/)
  (proof := /--
  Let $x'\in B(x,R)$. By definition of the ball, $|x'-x|<R$. It follows that $x'-x<R$ and $x-x'<R$. It
  follows $x'<x+R$ and $x'>x-R$. This implies $x'\in (x-R,x+R)$. Conversely, let $x'\in (x-R,x+R)$.
  Then $x'<x+R$ and $x'>x-R$. It follows that $x'-x<R$ and $x-x'<R$. It follows that $|x'-x|<R$, hence
  $x'\in B(x,R)$. This proves the lemma.
  -/)
  (latexEnv := "lemma")] Real.ball_eq_Ioo

attribute [blueprint
  (statement := /--
  Let $f:\R \to \C$ be $2\pi$-periodic and continuously differentiable, and let
  $n \in \Z \setminus \{0\}$. Then $$\begin{equation}
      \widehat{f}_n = \frac{1}{i n} \widehat{f'}_n.
  \end{equation}$$
  -/)
  (proof := /-- This is part of the Lean library. -/)
  (latexEnv := "lemma")] fourierCoeffOn_of_hasDerivAt

attribute [blueprint
  (statement := /--
  Let $f:\R \to \C$ such that $$\begin{equation}
      \sum_{n\in \Z} |\widehat{f}_n| < \infty.
  \end{equation}$$ Then $$\begin{equation}
      \sup_{x\in [0,2\pi]} |f(x) - S_Nf(x)| \rightarrow 0
  \end{equation}$$ as $N \rightarrow \infty$.
  -/)
  (proof := /-- This is part of the Lean library. -/)
  (latexEnv := "lemma")] hasSum_fourier_series_of_summable
