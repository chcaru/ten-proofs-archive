# ConnesRigidity feedback-work inventory

The following Lean files were present in `src/latest/ConnesRigidity/` before
the feedback work began on 2026-07-27. They are intentionally left untouched:

- `ArithmeticCocycle.lean`
- `CharacteristicKernel.lean`
- `CharacteristicSubgroup.lean`
- `CocycleExtension.lean`
- `CrossedClosure.lean`
- `CrossedMultipliers.lean`
- `ExternalResults.lean`
- `FactorIsomorphism.lean`
- `GroupVonNeumannAlgebra.lean`
- `Groups.lean`
- `ICC.lean`
- `LiftedCocycle.lean`
- `Main.lean`
- `MultiplicationAlgebra.lean`
- `PropertyT.lean`
- `Statements.lean`
- `SymplecticData.lean`
- `TorusCochain.lean`

New standalone files:

- `FeedbackReduction.lean`: the one-sided logical reduction, including its
  concrete specialization to the constructed nonsplit group.
- `FeedbackKazhdan.lean`: monotonicity of Kazhdan pairs under weaker constants
  and larger test sets.
- `FeedbackCounting.lean`: four-point parity, the quarter-support estimate,
  and the exact `1/4 - 1/7 = 3/28` finite union bound.
- `FeedbackBooleanQuadratic.lean`: partitions a binary cube into affine
  four-point squares and derives the quarter-support and `3/28` conclusions
  from a nonzero mixed second derivative.
- `FeedbackBooleanPolynomial.lean`: algebraic normal forms for binary
  polynomials of degree at most two and the unconditional theorem that every
  nonzero such polynomial has support density at least `1/4`, including the
  affine and constant cases.
- `Feedback.lean`: an aggregate import for the new modules.
