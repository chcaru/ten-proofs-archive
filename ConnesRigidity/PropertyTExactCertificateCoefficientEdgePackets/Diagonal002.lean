
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgeBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Diagonal002.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

@[irreducible] noncomputable def coefficientDiagonalPacketRows002 :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Diagonal002.Entry000.data

noncomputable def coefficientDiagonalPacketTerms002 :
    List (IntegerTableTerm 73033) :=
  coefficientDiagonalPacketsTerms coefficientDiagonalPacketRows002

end AffineSymplecticCertificate

end ConnesRigidity
