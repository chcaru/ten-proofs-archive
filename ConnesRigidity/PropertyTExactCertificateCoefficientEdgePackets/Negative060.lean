
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgeBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Negative060.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

@[irreducible] noncomputable def coefficientNegativePacketRows060 :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Negative060.Entry000.data

noncomputable def coefficientNegativePacketTerms060 :
    List (IntegerTableTerm 73033) :=
  coefficientNegativePacketsTerms coefficientNegativePacketRows060

end AffineSymplecticCertificate

end ConnesRigidity
