


import ConnesRigidity.PropertyTExactCertificateCoefficientBase
import Init.Data.Int.Bitwise









namespace ConnesRigidity

namespace AffineSymplecticCertificate

def coefficientLaneCheckData
    (laneWidth laneCount : Nat)
    (terms : List (IntegerTableTerm 73033)) :
    List (List Int) × Nat :=
  terms.foldl
    (fun state term =>
      let block := term.key.val / 1000
      let withinBlock := term.key.val % 1000
      let lane := withinBlock / laneWidth
      let digit := withinBlock % laneWidth
      (state.1.modify block fun row =>
          row.modify lane fun encoded =>
            encoded +
              Int.shiftLeft term.numerator (64 * digit),
        state.2 + term.numerator.natAbs))
    (List.replicate 74 (List.replicate laneCount 0), 0)

@[irreducible] noncomputable def benchmarkFactorRow260Terms :
    List (IntegerTableTerm 73033) :=
  coefficientFactorTermRowData productIndexDataRow260
    coefficientFullGramDataRow260

@[irreducible] noncomputable def benchmarkFactorRows260To264Terms :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow260
      coefficientFullGramDataRow260,
    coefficientFactorTermRowData productIndexDataRow261
      coefficientFullGramDataRow261,
    coefficientFactorTermRowData productIndexDataRow262
      coefficientFullGramDataRow262,
    coefficientFactorTermRowData productIndexDataRow263
      coefficientFullGramDataRow263,
    coefficientFactorTermRowData productIndexDataRow264
      coefficientFullGramDataRow264]

end AffineSymplecticCertificate

end ConnesRigidity
