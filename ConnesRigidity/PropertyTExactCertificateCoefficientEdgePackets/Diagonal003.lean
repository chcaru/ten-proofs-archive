
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgeBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Diagonal003.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

@[irreducible] noncomputable def coefficientDiagonalPacketRows003 :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Diagonal003.Entry000.data

noncomputable def coefficientDiagonalPacketTerms003 :
    List (IntegerTableTerm 73033) :=
  coefficientDiagonalPacketsTerms coefficientDiagonalPacketRows003

end AffineSymplecticCertificate

end ConnesRigidity
