
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgeBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Negative128.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

@[irreducible] noncomputable def coefficientNegativePacketRows128 :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Negative128.Entry000.data

noncomputable def coefficientNegativePacketTerms128 :
    List (IntegerTableTerm 73033) :=
  coefficientNegativePacketsTerms coefficientNegativePacketRows128

end AffineSymplecticCertificate

end ConnesRigidity
