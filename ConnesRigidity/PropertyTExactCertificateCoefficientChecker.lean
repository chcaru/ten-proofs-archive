
import ConnesRigidity.GroupRingCertificateAlgebra
import Init.Data.Int.Bitwise

namespace ConnesRigidity

namespace AffineSymplecticCertificate

def coefficientTerm (key : Nat) (numerator : Int) :
    IntegerTableTerm 73033 where
  key := Fin.ofNat 73033 key
  numerator := numerator

def rangeSortIntegerTerms {N : Nat} :
    Nat → Nat → List (IntegerTableTerm N) → List (IntegerTableTerm N)
  | _, _, [] => []
  | 0, _, terms => terms
  | bit + 1, lower, terms =>
      let middle := lower + 2 ^ bit
      let parts := terms.partition fun term =>
        decide (term.key.val < middle)
      rangeSortIntegerTerms bit lower parts.1 ++
        rangeSortIntegerTerms bit middle parts.2

def kernelNormalizeIntegerTerms {N : Nat}
    (terms : List (IntegerTableTerm N)) : List (IntegerTableTerm N) :=
  collapseIntegerTerms (rangeSortIntegerTerms 17 0 terms)

def coefficientCheckStep
    (state : Array Int × Nat) (term : IntegerTableTerm 73033) :
    Array Int × Nat :=
  let block := term.key.val / 1000
  let offset := term.key.val % 1000
  (state.1.modify block fun encoded =>
      encoded + Int.shiftLeft term.numerator (64 * offset),
    state.2 + term.numerator.natAbs)

def coefficientCheckData
    (terms : List (IntegerTableTerm 73033)) : Array Int × Nat :=
  terms.foldl coefficientCheckStep
    (Array.replicate 74 (0 : Int), 0)

def encodeCoefficientBlocks
    (terms : List (IntegerTableTerm 73033)) : Array Int :=
  (coefficientCheckData terms).1

theorem coefficientCheckData_fst
    (terms : List (IntegerTableTerm 73033)) :
    (coefficientCheckData terms).1 = encodeCoefficientBlocks terms := by
  rfl

def addCoefficientEncodingRowsList :
    Nat → List Int → List Int → List Int
  | 0, _, _ => []
  | length + 1, left :: lefts, right :: rights =>
      (left + right) ::
        addCoefficientEncodingRowsList length lefts rights
  | length + 1, left :: lefts, [] =>
      left :: addCoefficientEncodingRowsList length lefts []
  | length + 1, [], right :: rights =>
      right :: addCoefficientEncodingRowsList length [] rights
  | length + 1, [], [] =>
      0 :: addCoefficientEncodingRowsList length [] []

def addCoefficientEncodingRows
    (left right : Array Int) : Array Int :=
  (addCoefficientEncodingRowsList 74
    left.toList right.toList).toArray

def sumCoefficientEncodingRows (rows : List (Array Int)) : Array Int :=
  rows.foldl addCoefficientEncodingRows
    (Array.replicate 74 0)

end AffineSymplecticCertificate

end ConnesRigidity
