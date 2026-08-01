
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgeBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Positive046.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

@[irreducible] noncomputable def coefficientPositivePacketRows046 :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Positive046.Entry000.data

noncomputable def coefficientPositivePacketTerms046 :
    List (IntegerTableTerm 73033) :=
  coefficientPositivePacketsTerms coefficientPositivePacketRows046

end AffineSymplecticCertificate

end ConnesRigidity
