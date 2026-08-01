
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgeBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Diagonal005.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

@[irreducible] noncomputable def coefficientDiagonalPacketRows005 :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Diagonal005.Entry000.data

noncomputable def coefficientDiagonalPacketTerms005 :
    List (IntegerTableTerm 73033) :=
  coefficientDiagonalPacketsTerms coefficientDiagonalPacketRows005

end AffineSymplecticCertificate

end ConnesRigidity
