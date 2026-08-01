
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgeBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Positive110.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

@[irreducible] noncomputable def coefficientPositivePacketRows110 :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Positive110.Entry000.data

noncomputable def coefficientPositivePacketTerms110 :
    List (IntegerTableTerm 73033) :=
  coefficientPositivePacketsTerms coefficientPositivePacketRows110

end AffineSymplecticCertificate

end ConnesRigidity
