
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgeBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Positive070.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

@[irreducible] noncomputable def coefficientPositivePacketRows070 :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Positive070.Entry000.data

noncomputable def coefficientPositivePacketTerms070 :
    List (IntegerTableTerm 73033) :=
  coefficientPositivePacketsTerms coefficientPositivePacketRows070

end AffineSymplecticCertificate

end ConnesRigidity
