
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgeBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Negative095.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

@[irreducible] noncomputable def coefficientNegativePacketRows095 :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Negative095.Entry000.data

noncomputable def coefficientNegativePacketTerms095 :
    List (IntegerTableTerm 73033) :=
  coefficientNegativePacketsTerms coefficientNegativePacketRows095

end AffineSymplecticCertificate

end ConnesRigidity
