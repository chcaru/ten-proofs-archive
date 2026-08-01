
import ConnesRigidity.PropertyTExactCertificateData

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

abbrev GroupRing :=
  RationalGroupRing IntegralSymplecticCocycleInput.GammaZero

noncomputable def atom (i : ℕ) : GroupRing :=
  MonoidAlgebra.single (basisElement i) 1

noncomputable def reducedAtom (i : ℕ) : GroupRing :=
  atom (i + 1) - atom 0

def basisIndex (i : ℕ) : Fin 425 :=
  Fin.ofNat 425 i

noncomputable def factorVector (row : List ℤ) : GroupRing :=
  RationalGroupRing.basisVector certificateBasis fun i ↦
    (fullFactorCoefficient row i : ℚ)

structure Edge where
  left : ℕ
  right : ℕ
  weightNumerator : ℕ
deriving DecidableEq

def edgeOfData (row : List ℤ) : Edge where
  left := (row.getD 0 0).toNat
  right := (row.getD 1 0).toNat
  weightNumerator := (row.getD 2 0).toNat

noncomputable def negativeEdges : List Edge :=
  negativeEdgeData.map edgeOfData

noncomputable def positiveEdges : List Edge :=
  positiveEdgeData.map edgeOfData

def edgeWeight (edge : Edge) : ℚ :=
  (4 * edge.weightNumerator : ℚ) / 2000000000000

def negativeEdgeEntries (edge : Edge) : List (Fin 425 × ℤ) :=
  [(basisIndex edge.left, -1), (basisIndex edge.right, 1)]

def positiveEdgeEntries (edge : Edge) : List (Fin 425 × ℤ) :=
  [(basisIndex 0, -2), (basisIndex edge.left, 1),
    (basisIndex edge.right, 1)]

def diagonalEntries (i : ℕ) : List (Fin 425 × ℤ) :=
  [(basisIndex 0, -1), (basisIndex (i + 1), 1)]

noncomputable def sparseVector
    (entries : List (Fin 425 × ℤ)) : GroupRing :=
  RationalGroupRing.sparseBasisVector certificateBasis
    (entries.map fun entry ↦ (entry.1, (entry.2 : ℚ)))

noncomputable def negativeEdgeVector (edge : Edge) : GroupRing :=
  sparseVector (negativeEdgeEntries edge)

noncomputable def positiveEdgeVector (edge : Edge) : GroupRing :=
  sparseVector (positiveEdgeEntries edge)

noncomputable def factorSquares : List (ℚ × GroupRing) :=
  factorData.map fun row ↦
    ((8 : ℚ) / 2000000000000, factorVector row)

noncomputable def negativeEdgeSquares : List (ℚ × GroupRing) :=
  negativeEdges.map fun edge ↦
    (edgeWeight edge, negativeEdgeVector edge)

noncomputable def positiveEdgeSquares : List (ℚ × GroupRing) :=
  positiveEdges.filterMap fun edge ↦
    if edge.left = 0 ∨ edge.right = 0 then none
    else some (edgeWeight edge, positiveEdgeVector edge)

noncomputable def diagonalSquares : List (ℚ × GroupRing) :=
  diagonalWeightData.mapIdx fun i weight ↦
    ((4 * weight.toNat : ℚ) / 2000000000000,
      sparseVector (diagonalEntries i))

noncomputable def squares : List (ℚ × GroupRing) :=
  factorSquares ++ negativeEdgeSquares ++ positiveEdgeSquares ++ diagonalSquares

noncomputable def integerOuterTerms
    (weight : ℤ) (entries : List (Fin 425 × ℤ)) :
    List (IntegerTableTerm 73033) :=
  entries.flatMap fun left ↦
    entries.map fun right ↦
      { key := tableIndex left.1 right.1
        numerator := weight * left.2 * right.2 }

noncomputable def factorTermRow
    (i : Fin 425) : List (IntegerTableTerm 73033) :=
  let productRow := (productIndexDataRow i).toList
  let gramRow := (coefficientFullGramDataRow i).toList
  List.zipWith
    (fun productIndex gramCoefficient ↦
      { key := Fin.ofNat 73033 productIndex.toNat
        numerator := 8 * gramCoefficient })
    productRow gramRow

noncomputable def factorTerms : List (IntegerTableTerm 73033) :=
  (List.finRange 425).flatMap factorTermRow

noncomputable def negativeEdgeTermRow (edge : Edge) :
    List (IntegerTableTerm 73033) :=
  integerOuterTerms (4 * edge.weightNumerator)
    (negativeEdgeEntries edge)

noncomputable def negativeEdgeTerms : List (IntegerTableTerm 73033) :=
  negativeEdges.flatMap negativeEdgeTermRow

noncomputable def positiveEdgeTermRow (edge : Edge) :
    List (IntegerTableTerm 73033) :=
  if edge.left = 0 ∨ edge.right = 0 then []
  else
    integerOuterTerms (4 * edge.weightNumerator)
      (positiveEdgeEntries edge)

noncomputable def positiveEdgeTerms : List (IntegerTableTerm 73033) :=
  positiveEdges.flatMap positiveEdgeTermRow

noncomputable def diagonalTerms : List (IntegerTableTerm 73033) :=
  (diagonalWeightData.mapIdx fun i weight ↦
    integerOuterTerms (4 * (weight.toNat : ℤ))
      (diagonalEntries i)).flatten

noncomputable def certificateTerms : List (IntegerTableTerm 73033) :=
  factorTerms ++ negativeEdgeTerms ++ positiveEdgeTerms ++ diagonalTerms

def customaryLaplacianEntries : List (Fin 425 × ℤ) :=
  (basisIndex 0, 24) ::
    (List.range 24).map fun i ↦ (basisIndex (i + 1), -1)

noncomputable def targetTerms : List (IntegerTableTerm 73033) :=
  integerOuterTerms 8000000000000 customaryLaplacianEntries ++
    customaryLaplacianEntries.map fun entry ↦
      { key := tableIndex (basisIndex 0) entry.1
        numerator := -80000000000 * entry.2 }

end AffineSymplecticCertificate

end ConnesRigidity
