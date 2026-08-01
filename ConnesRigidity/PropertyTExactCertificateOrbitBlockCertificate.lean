


import ConnesRigidity.PropertyTExactCertificateOrbitAverage
import ConnesRigidity.PropertyTExactCertificateOrbitAlgebra
import ConnesRigidity.PropertyTExactCertificateOrbitBasis
import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices
import ConnesRigidity.PropertyTExactCertificateOrbitBlockWeights
import ConnesRigidity.PropertyTExactCertificateOrbitSymmetryAverage
import ConnesRigidity.PropertyTExactCertificateOrbitValidation












namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open scoped BigOperators

private theorem orbitAdjoint_mul
    {G : Type*} [Group G]
    (left right : RationalGroupRing G) :
    RationalGroupRing.adjoint (left * right) =
      RationalGroupRing.adjoint right * RationalGroupRing.adjoint left := by
  classical
  have hsingle (g : G) (r : ℚ) (value : RationalGroupRing G) :
      RationalGroupRing.adjoint (MonoidAlgebra.single g r * value) =
        RationalGroupRing.adjoint value *
          RationalGroupRing.adjoint (MonoidAlgebra.single g r) := by
    induction value using MonoidAlgebra.induction with
    | zero => simp
    | single_add h s value _hh _hs ih =>
        simp [mul_add, add_mul, RationalGroupRing.adjoint_add, ih,
          MonoidAlgebra.single_mul_single,
          RationalGroupRing.adjoint_single, mul_comm]
  induction left using MonoidAlgebra.induction with
  | zero => simp
  | single_add g r value _hg _hr ih =>
      simp [add_mul, RationalGroupRing.adjoint_add, ih, mul_add, hsingle]

private theorem orbitAdjoint_adjoint
    {G : Type*} [Group G] (value : RationalGroupRing G) :
    RationalGroupRing.adjoint (RationalGroupRing.adjoint value) = value := by
  ext g
  simp


theorem orbitPositiveSumOfSquares_adjoint
    {G : Type*} [Group G]
    {value : RationalGroupRing G}
    (hvalue : RationalGroupRing.IsPositiveSumOfSquares value) :
    RationalGroupRing.adjoint value = value := by
  obtain ⟨squares, _hweights, rfl⟩ := hvalue
  clear _hweights
  induction squares with
  | nil => simp
  | cons square squares ih =>
      simp [RationalGroupRing.adjoint_smul, orbitAdjoint_mul,
        orbitAdjoint_adjoint, ih]





noncomputable def orbitBlockAtom
    (block : Fin 28)
    (column : Fin (blockDimension block.val)) :
    RationalGroupRing constructedGammaZeroGroup :=
  ∑ index : Fin 424,
    (scaledInverseEntryInt
      (blockRowStart block.val + column.val) index.val : ℚ) •
      reducedGroupAtom orbitBasis index



noncomputable def orbitBlockCandidate :
    RationalGroupRing constructedGammaZeroGroup :=
  (((congruenceInverseScale : Int) : ℚ) ^ 2)⁻¹ •
    ∑ block : Fin 28,
      OrbitPositivity.matrixAtomExpansion (orbitBlockAtom block)
        (blockGram block.val)



noncomputable def orbitAveragedCertificate :
    RationalGroupRing constructedGammaZeroGroup :=
  groupRingSymmetryAverage (Finset.univ : Finset (Fin 64))
    orbitSymmetry orbitBlockCandidate



theorem orbitBlockExpansion_isPositiveSumOfSquares (block : Fin 28) :
    RationalGroupRing.IsPositiveSumOfSquares
      (OrbitPositivity.matrixAtomExpansion (orbitBlockAtom block)
        (blockGram block.val)) := by
  apply blockGram_isPositiveSumOfSquares block.val (orbitBlockAtom block)
  · intro row column
    exact orbitBlockFactorIdentityChecks block row column
  · intro row column
    exact orbitBlockResidualSymmetryChecks block row column
  · intro row
    exact orbitBlockResidualDominanceChecks block row



theorem orbitBlockCandidate_isPositiveSumOfSquares :
    RationalGroupRing.IsPositiveSumOfSquares orbitBlockCandidate := by
  unfold orbitBlockCandidate
  apply RationalGroupRing.IsPositiveSumOfSquares.smul
    ((((congruenceInverseScale : Int) : ℚ) ^ 2)⁻¹)
  · positivity
  · apply RationalGroupRing.IsPositiveSumOfSquares.sum Finset.univ
    intro block _
    exact orbitBlockExpansion_isPositiveSumOfSquares block




theorem orbitAveragedCertificate_isPositiveSumOfSquares :
    RationalGroupRing.IsPositiveSumOfSquares orbitAveragedCertificate := by
  unfold orbitAveragedCertificate
  exact groupRingSymmetryAverage_isPositiveSumOfSquares
    (Finset.univ : Finset (Fin 64)) orbitSymmetry
    orbitBlockCandidate_isPositiveSumOfSquares



theorem orbitAveragedCertificate_adjoint :
    RationalGroupRing.adjoint orbitAveragedCertificate =
      orbitAveragedCertificate :=
  orbitPositiveSumOfSquares_adjoint
    orbitAveragedCertificate_isPositiveSumOfSquares



theorem orbitAveragedCertificate_groupRingMap (symmetry : Fin 64) :
    groupRingMap (orbitSymmetry symmetry) orbitAveragedCertificate =
      orbitAveragedCertificate := by
  unfold orbitAveragedCertificate
  exact groupRingOrbitAverage_invariant orbitBlockCandidate symmetry

end ConnesRigidity.AffineSymplecticOrbitCertificate
