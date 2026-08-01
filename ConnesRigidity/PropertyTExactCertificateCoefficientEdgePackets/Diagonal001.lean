
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgeBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Diagonal001.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

@[irreducible] noncomputable def coefficientDiagonalPacketRows001 :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Diagonal001.Entry000.data

noncomputable def coefficientDiagonalPacketTerms001 :
    List (IntegerTableTerm 73033) :=
  coefficientDiagonalPacketsTerms coefficientDiagonalPacketRows001

end AffineSymplecticCertificate

end ConnesRigidity
