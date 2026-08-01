


import ConnesRigidity.PropertyTExactCertificateCoefficientBase










namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000


def sparseRadixNumeratorSum
    (terms : List (IntegerTableTerm 73033)) : Int :=
  terms.foldl (fun total term => total + term.numerator) 0








def sparseRadixNormalize :
    Nat → Nat → List (IntegerTableTerm 73033) →
      List (IntegerTableTerm 73033)
  | _, _, [] => []
  | 0, lower, terms@(_ :: _) =>
      let numerator := sparseRadixNumeratorSum terms
      if numerator = 0 then []
      else [coefficientTerm lower numerator]
  | depth + 1, lower, terms@(_ :: _) =>
      let middle := lower + 2 ^ depth
      let parts := terms.partition fun term =>
        decide (term.key.val < middle)
      sparseRadixNormalize depth lower parts.1 ++
        sparseRadixNormalize depth middle parts.2


def sparseTermsOfIntPairs :
    List Int → List (IntegerTableTerm 73033)
  | key :: numerator :: rest =>
      coefficientTerm key.toNat numerator ::
        sparseTermsOfIntPairs rest
  | _ => []







inductive SparseCoefficientTrie where
  | zero
  | leaf (coefficient : Int)
  | branch (left right : SparseCoefficientTrie)
deriving DecidableEq

def SparseCoefficientTrie.mkLeaf
    (coefficient : Int) : SparseCoefficientTrie :=
  if coefficient = 0 then .zero else .leaf coefficient

def SparseCoefficientTrie.mkBranch
    (left right : SparseCoefficientTrie) : SparseCoefficientTrie :=
  match left, right with
  | .zero, .zero => .zero
  | _, _ => .branch left right


def SparseCoefficientTrie.addAt :
    Nat → Nat → SparseCoefficientTrie → Nat → Int →
      SparseCoefficientTrie
  | 0, _, .zero, _, coefficient => .mkLeaf coefficient
  | 0, _, .leaf old, _, coefficient => .mkLeaf (old + coefficient)
  | 0, _, .branch _ _, _, _ => .zero
  | depth + 1, lower, .zero, key, coefficient =>
      let middle := lower + 2 ^ depth
      if key < middle then
        .mkBranch
          (addAt depth lower .zero key coefficient) .zero
      else
        .mkBranch .zero
          (addAt depth middle .zero key coefficient)
  | depth + 1, lower, .branch left right, key, coefficient =>
      let middle := lower + 2 ^ depth
      if key < middle then
        .mkBranch
          (addAt depth lower left key coefficient) right
      else
        .mkBranch left
          (addAt depth middle right key coefficient)
  | _ + 1, _, .leaf _, _, _ => .zero


def SparseCoefficientTrie.toTerms :
    Nat → Nat → SparseCoefficientTrie →
      List (IntegerTableTerm 73033)
  | _, _, .zero => []
  | 0, lower, .leaf coefficient =>
      [coefficientTerm lower coefficient]
  | 0, _, .branch _ _ => []
  | depth + 1, lower, .branch left right =>
      let middle := lower + 2 ^ depth
      toTerms depth lower left ++
        toTerms depth middle right
  | _ + 1, _, .leaf _ => []


def sparseTrieNormalize
    (terms : List (IntegerTableTerm 73033)) :
    List (IntegerTableTerm 73033) :=
  let tree : SparseCoefficientTrie :=
    terms.foldl
      (fun tree term =>
        SparseCoefficientTrie.addAt
          17 0 tree term.key.val term.numerator)
      SparseCoefficientTrie.zero
  SparseCoefficientTrie.toTerms 17 0 tree


inductive SparseCoefficientQuadTrie where
  | zero
  | leaf (coefficient : Int)
  | branch
      (first second third fourth : SparseCoefficientQuadTrie)
deriving DecidableEq

def SparseCoefficientQuadTrie.mkLeaf
    (coefficient : Int) : SparseCoefficientQuadTrie :=
  if coefficient = 0 then .zero else .leaf coefficient

def SparseCoefficientQuadTrie.mkBranch
    (first second third fourth : SparseCoefficientQuadTrie) :
    SparseCoefficientQuadTrie :=
  match first, second, third, fourth with
  | .zero, .zero, .zero, .zero => .zero
  | _, _, _, _ => .branch first second third fourth


def SparseCoefficientQuadTrie.addAt :
    Nat → Nat → SparseCoefficientQuadTrie → Nat → Int →
      SparseCoefficientQuadTrie
  | 0, _, .zero, _, coefficient => .mkLeaf coefficient
  | 0, _, .leaf old, _, coefficient => .mkLeaf (old + coefficient)
  | 0, _, .branch _ _ _ _, _, _ => .zero
  | depth + 1, lower, tree, key, coefficient =>
      let span := 4 ^ depth
      let firstEnd := lower + span
      let secondEnd := firstEnd + span
      let thirdEnd := secondEnd + span
      let children :=
        match tree with
        | .branch first second third fourth =>
            (first, second, third, fourth)
        | _ => (.zero, .zero, .zero, .zero)
      if key < firstEnd then
        .mkBranch
          (addAt depth lower children.1 key coefficient)
          children.2.1 children.2.2.1 children.2.2.2
      else if key < secondEnd then
        .mkBranch children.1
          (addAt depth firstEnd children.2.1 key coefficient)
          children.2.2.1 children.2.2.2
      else if key < thirdEnd then
        .mkBranch children.1 children.2.1
          (addAt depth secondEnd children.2.2.1 key coefficient)
          children.2.2.2
      else
        .mkBranch children.1 children.2.1 children.2.2.1
          (addAt depth thirdEnd children.2.2.2 key coefficient)


def SparseCoefficientQuadTrie.toTerms :
    Nat → Nat → SparseCoefficientQuadTrie →
      List (IntegerTableTerm 73033)
  | _, _, .zero => []
  | 0, lower, .leaf coefficient =>
      [coefficientTerm lower coefficient]
  | 0, _, .branch _ _ _ _ => []
  | depth + 1, lower, .branch first second third fourth =>
      let span := 4 ^ depth
      let firstEnd := lower + span
      let secondEnd := firstEnd + span
      let thirdEnd := secondEnd + span
      toTerms depth lower first ++
        toTerms depth firstEnd second ++
        toTerms depth secondEnd third ++
        toTerms depth thirdEnd fourth
  | _ + 1, _, .leaf _ => []


def sparseQuadTrieNormalize
    (terms : List (IntegerTableTerm 73033)) :
    List (IntegerTableTerm 73033) :=
  let tree : SparseCoefficientQuadTrie :=
    terms.foldl
      (fun tree term =>
        SparseCoefficientQuadTrie.addAt
          9 0 tree term.key.val term.numerator)
      SparseCoefficientQuadTrie.zero
  SparseCoefficientQuadTrie.toTerms 9 0 tree

end AffineSymplecticCertificate

end ConnesRigidity
