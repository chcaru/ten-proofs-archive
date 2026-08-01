
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgeBase
import Init.Data.Int.Bitwise

namespace ConnesRigidity

namespace AffineSymplecticCertificate

def benchmarkEdgeCoefficientCheckData
    (terms : List (IntegerTableTerm 73033)) : Array Int × Nat :=
  terms.foldl
    (fun state term =>
      let block := term.key.val / 1000
      let offset := term.key.val % 1000
      (state.1.modify block fun encoded =>
          encoded + Int.shiftLeft term.numerator (64 * offset),
        state.2 + term.numerator.natAbs))
    (Array.replicate 74 (0 : Int), 0)

end AffineSymplecticCertificate

end ConnesRigidity
