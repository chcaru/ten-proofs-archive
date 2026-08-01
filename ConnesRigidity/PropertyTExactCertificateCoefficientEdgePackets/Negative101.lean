
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgeBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Negative101.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

@[irreducible] noncomputable def coefficientNegativePacketRows101 :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Negative101.Entry000.data

noncomputable def coefficientNegativePacketTerms101 :
    List (IntegerTableTerm 73033) :=
  coefficientNegativePacketsTerms coefficientNegativePacketRows101

end AffineSymplecticCertificate

end ConnesRigidity
