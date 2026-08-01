
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgeBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Negative010.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

@[irreducible] noncomputable def coefficientNegativePacketRows010 :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Negative010.Entry000.data

noncomputable def coefficientNegativePacketTerms010 :
    List (IntegerTableTerm 73033) :=
  coefficientNegativePacketsTerms coefficientNegativePacketRows010

end AffineSymplecticCertificate

end ConnesRigidity
