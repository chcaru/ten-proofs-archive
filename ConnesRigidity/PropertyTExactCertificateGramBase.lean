
import ConnesRigidity.PropertyTExactCertificateGramData
import ConnesRigidity.PropertyTExactCertificateGramColumnData

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

noncomputable section

def factorCoefficientBound : Int := 13000000

def fullGramCoefficientBound : Int := 200000000000000

def fixedIntRow : Nat → List Int → List Int
  | 0, _ => []
  | n + 1, [] => 0 :: fixedIntRow n []
  | n + 1, entry :: entries =>
      entry :: fixedIntRow n entries

def factorCoefficientRowOf (row : List Int) : List Int :=
  (-row.sum) :: fixedIntRow 424 row

def factorCoefficientRow (r : Nat) : List Int :=
  factorCoefficientRowOf (factorRow r)

def factorRowEncodingIsValid (r : ℕ) : Bool :=
  let row := factorCoefficientRow r
  decide
    (encodedFactorRows.getD r 0 = encodeGramRow row) &&
    row.all fun coefficient ↦
      decide
        (-factorCoefficientBound ≤ coefficient ∧
          coefficient ≤ factorCoefficientBound)

def fullGramCoefficientRow (i : Nat) : List Int :=
  fixedIntRow 425 (fullGramData.getD i [])

def factorColumnChunkMatchesRows (start : Nat) :
    List (List Int) → List (List Int) → Bool
  | [], columns => columns.all List.isEmpty
  | row :: rows, columns =>
      decide
          (((factorCoefficientRowOf row).drop start).take columns.length =
            columns.map (·.headD 0)) &&
        factorColumnChunkMatchesRows start rows (columns.map List.tail)

def factorColumnChunkIsValid (chunk : Nat) : Bool :=
  decide
      ((factorColumnChunk chunk).length =
        min 32 (425 - 32 * chunk)) &&
    factorColumnChunkMatchesRows (32 * chunk) factorData
      (factorColumnChunk chunk)

def encodedFullGramColumnCombinationAux :
    Nat → List Int → List Int → Int → Int
  | 0, _, _, result => result
  | n + 1, [], [], result =>
      encodedFullGramColumnCombinationAux n [] [] result
  | n + 1, [], _ :: encodings, result =>
      encodedFullGramColumnCombinationAux n [] encodings result
  | n + 1, _ :: coefficients, [], result =>
      encodedFullGramColumnCombinationAux n coefficients [] result
  | n + 1, coefficient :: coefficients, encoded :: encodings, result =>
      encodedFullGramColumnCombinationAux n coefficients encodings
        (result + coefficient * encoded)

def encodedFullGramColumnCombination (i : Nat) : Int :=
  encodedFullGramColumnCombinationAux 424 (factorColumn i)
    encodedFactorRows 0

def fullGramRowEncodingIsValid (i : ℕ) : Bool :=
  let rawRow := (coefficientFullGramDataRow i).toList
  let row := fixedIntRow 425 rawRow
  decide (rawRow.length = 425) &&
    (decide
      (encodeGramRow row = encodedFullGramColumnCombination i) &&
      row.all fun coefficient ↦
        decide
          (-fullGramCoefficientBound ≤ coefficient ∧
            coefficient ≤ fullGramCoefficientBound))

end

end AffineSymplecticCertificate

end ConnesRigidity
